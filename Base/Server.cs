using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.Drawing;
using System.IO;
using System.Linq;
using System.Media;
using System.Net;
using System.Net.Sockets;
using System.Runtime.Remoting.Metadata.W3cXsd2001;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using System.Windows.Forms;
using Talos.Base;
using Talos.Cryptography;
using Talos.Cryptography.Abstractions.Definitions;
using Talos.Definitions;
using Talos.Definitions;
using Talos.Forms;
using Talos.Forms.UI;
using Talos.Helper;
using Talos.Maps;
using Talos.Networking;
using Talos.Objects;
using Talos.PInvoke;
using Talos.Properties;
using Talos.Structs;
using WindowsInput;
using static System.Windows.Forms.VisualStyles.VisualStyleElement.Window;
using Dialog = Talos.Objects.Dialog;
using Point = Talos.Structs.Point;



namespace Talos
{
    internal class Server
    {
        #region networking vars
        private Socket _clientSocket;

        private IPEndPoint _remoteEndPoint;
        private int _port;

        private ClientMessageHandler[] _clientMessage;
        internal ClientMessageHandler[] ClientMessage => _clientMessage;

        private ServerMessageHandler[] _serverMessage;
        internal ServerMessageHandler[] ServerMessage => _serverMessage;

        internal MainForm MainForm { get; set; }

        private Thread _serverThread;

        internal List<Client> ClientList { get; set; } = new List<Client>();
        internal readonly object _clientListLock = new object();

        private bool _initialized;
        #endregion

        private bool _isMapping;
        private bool _mapChangePending;
        internal bool StopWalking { get; set; }
        internal bool StopCasting { get; set; }

        internal bool _disableSound = false;
        private bool _shouldCloseProfile = false;
        private bool _canCloseProfile = false;
        private DateTime _lastWorldShout = DateTime.MinValue;
        private DateTime _lastMapChange = DateTime.MinValue;
        internal Element _enemyElement;
        private Animation _lastAnimation;
        private string _itemToReEquip = "";
        private bool _clientWalkPending;
        private string[] spareStickMessages = new[]
        {
            "Thank ya so much. Here's a few coins for your effort.",
            "Ah thank ya, you've done well.",
            "Ah, it's a good thing you've done",
            "You remind me of my own little child."
        };

        private string[] perfectHairstyleMessages = new[]
        {
            "Excellent! Thank you so much!",
            "Well done!",
            "You remind me of a dear friend"
        };
        internal DateTime ArenaAnnounceTimer { get; set; } = DateTime.MinValue;

        InputSimulator inputSimulator = new InputSimulator();

        // Create a single instance of ActiveMessageHandler
        ActiveMessageHandler activeMessageHandler = ActiveMessageHandler.Instance;
        // Create a singel instance of CommandManager
        CommandManager commandManager = CommandManager.Instance;

        internal Dictionary<uint, WorldMap> _worldMaps = new Dictionary<uint, WorldMap>();
        internal Dictionary<short, Map> _maps = new Dictionary<short, Map>();
        internal Dictionary<string, string> MedWalk { get; set; } = new Dictionary<string, string>();
        internal Dictionary<string, string> MedTask { get; set; } = new Dictionary<string, string>();
        internal Dictionary<string, int> MedWalkSpeed { get; set; } = new Dictionary<string, int>();
        internal Dictionary<string, DateTime> ConsecutiveLogin = new Dictionary<string, DateTime>();
        internal SortedDictionary<ushort, string> PursuitIDs { get; set; } = new SortedDictionary<ushort, string>();
        internal ConcurrentDictionary<string, CharacterState> ClientStateList {  get; set; } = new ConcurrentDictionary<string, CharacterState>();
        internal ConcurrentDictionary<string, bool> ManualServerSwitch { get; set; } = new ConcurrentDictionary<string, bool>();

        internal List<Client> _clients = new List<Client>();
        private string _exchangeName;
        private string _exchangeItem;
        private string _exchangeCancel;
        private string _exchangeAccept;


        public static object SyncObj { get; internal set; } = new object();

        internal IEnumerable<Client> Clients
        {
            get
            {
                return ClientList?
                    .Where(client => client != null
                                  && !string.IsNullOrEmpty(client.Name)
                                  && !client.Name.Contains('[')
                                  && client.ClientTab != null
                                  && client.Player != null)
                    ?? Enumerable.Empty<Client>();
            }
        }





        internal Server(MainForm mainForm)
        {
            MainForm = mainForm;
            _clientSocket = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);
            _clientMessage = new ClientMessageHandler[256];
            _serverMessage = new ServerMessageHandler[256];
            _remoteEndPoint = new IPEndPoint(IPAddress.Parse("52.88.55.94"), 2610);
            _serverThread = new Thread(new ThreadStart(AutomaticActions));
            MessageHandlers();
            Initialize(2610);
            LoadMapCache();

            var timer = new System.Threading.Timer((e) =>
            {
                CreatureStateHelper.CleanupOldCachedUpdates();
            }, null, TimeSpan.Zero, TimeSpan.FromMinutes(5));
        }

        #region networking

        /// <summary>
        /// 
        /// </summary>
        /// <param name="port"></param>
        internal void Initialize(int port)
        {
            if (!_initialized)
            {
                _initialized = true;
                _port = port;
                _clientSocket.Bind(new IPEndPoint(IPAddress.Loopback, port));
                _clientSocket.Listen(10);
                _clientSocket.BeginAccept(new AsyncCallback(EndAccept), null);
                _serverThread.Start();
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="ar"></param>
        private void EndAccept(IAsyncResult ar)
        {
            try
            {
                Client client = new Client(this, _clientSocket.EndAccept(ar));
                client.Connect(_remoteEndPoint);
                _remoteEndPoint = new IPEndPoint(IPAddress.Parse("52.88.55.94"), 2610);
                _clientSocket.BeginAccept(new AsyncCallback(EndAccept), null);
                lock (_clientListLock)
                {
                    ClientList.Add(client);
                }
            }
            catch (SocketException)
            {
                Console.WriteLine("Failed to establish a connection: Client");
            }
        }
        #endregion

        /// <summary>
        /// Message handler for the client and server messages based on what opcode is sent.
        /// </summary>
        private void MessageHandlers()
        {
            #region Client Message Handlers
            ClientMessage[(int)ClientOpCode.Version] = new ClientMessageHandler(ClientMessage_0x00_Version);
            ClientMessage[(int)ClientOpCode.CreateCharRequest] = new ClientMessageHandler(ClientMessage_0x02_CreateCharRequest);
            ClientMessage[(int)ClientOpCode.Login] = new ClientMessageHandler(ClientMessage_0x03_Login);
            ClientMessage[(int)ClientOpCode.CreateCharFinalize] = new ClientMessageHandler(ClientMessage_0x04_CreateCharFinalize);
            ClientMessage[(int)ClientOpCode.MapDataRequest] = new ClientMessageHandler(ClientMessage_0x05_MapDataRequest);
            ClientMessage[(int)ClientOpCode.ClientWalk] = new ClientMessageHandler(ClientMessage_0x06_ClientWalk);
            ClientMessage[(int)ClientOpCode.Pickup] = new ClientMessageHandler(ClientMessage_0x07_Pickup);
            ClientMessage[(int)ClientOpCode.ItemDrop] = new ClientMessageHandler(ClientMessage_0x08_ItemDrop);
            ClientMessage[(int)ClientOpCode.ExitRequest] = new ClientMessageHandler(ClientMessage_0x0B_ExitRequest);
            ClientMessage[(int)ClientOpCode.DisplayEntityRequest] = new ClientMessageHandler(ClientMessage_0x0C_DisplayEntityRequest);
            ClientMessage[(int)ClientOpCode.Ignore] = new ClientMessageHandler(ClientMessage_0x0D_Ignore);
            ClientMessage[(int)ClientOpCode.PublicMessage] = new ClientMessageHandler(ClientMessage_0x0E_PublicMessage);
            ClientMessage[(int)ClientOpCode.UseSpell] = new ClientMessageHandler(ClientMessage_0x0F_UseSpell);
            ClientMessage[(int)ClientOpCode.ClientJoin] = new ClientMessageHandler(ClientMessage_0x10_JoinClient);
            ClientMessage[(int)ClientOpCode.Turn] = new ClientMessageHandler(ClientMessage_0x11_Turn);
            ClientMessage[(int)ClientOpCode.SpaceBar] = new ClientMessageHandler(ClientMessage_0x13_Spacebar);
            ClientMessage[(int)ClientOpCode.WorldListRequest] = new ClientMessageHandler(ClientMessage_0x18_WorldListRequest);
            ClientMessage[(int)ClientOpCode.Whisper] = new ClientMessageHandler(ClientMessage_0x19_Whisper);
            ClientMessage[(int)ClientOpCode.UserOptionToggle] = new ClientMessageHandler(ClientMessage_0x1B_UserOptionToggle);
            ClientMessage[(int)ClientOpCode.UseItem] = new ClientMessageHandler(ClientMessage_0x1C_UseItem);
            ClientMessage[(int)ClientOpCode.Emote] = new ClientMessageHandler(ClientMessage_0x1D_Emote);
            ClientMessage[(int)ClientOpCode.SetNotepad] = new ClientMessageHandler(ClientMessage_0x23_SetNotepad);
            ClientMessage[(int)ClientOpCode.GoldDrop] = new ClientMessageHandler(ClientMessage_0x24_GoldDrop);
            ClientMessage[(int)ClientOpCode.PasswordChange] = new ClientMessageHandler(ClientMessage_0x26_PasswordChange);
            ClientMessage[(int)ClientOpCode.ItemDroppedOnCreature] = new ClientMessageHandler(ClientMessage_0x29_ItemDroppedOnCreature);
            ClientMessage[(int)ClientOpCode.GoldDroppedOnCreature] = new ClientMessageHandler(ClientMessage_0x2A_GoldDropOnCreature);
            ClientMessage[(int)ClientOpCode.ProfileRequest] = new ClientMessageHandler(ClientMessage_0x2D_ProfileRequest);
            ClientMessage[(int)ClientOpCode.GroupRequest] = new ClientMessageHandler(ClientMessage_0x2E_GroupRequest);
            ClientMessage[(int)ClientOpCode.ToggleGroup] = new ClientMessageHandler(ClientMessage_0x2F_ToggleGroup);
            ClientMessage[(int)ClientOpCode.SwapSlot] = new ClientMessageHandler(ClientMessage_0x30_SwapSlot);
            ClientMessage[(int)ClientOpCode.RefreshRequest] = new ClientMessageHandler(ClientMessage_0x38_RefreshRequest);
            ClientMessage[(int)ClientOpCode.PursuitRequest] = new ClientMessageHandler(ClientMessage_0x39_PersuitRequest);
            ClientMessage[(int)ClientOpCode.DialogResponse] = new ClientMessageHandler(ClientMessage_0x3A_DialogResponse);
            ClientMessage[(int)ClientOpCode.BoardRequest] = new ClientMessageHandler(ClientMessage_0x3B_BoardRequest);
            ClientMessage[(int)ClientOpCode.UseSkill] = new ClientMessageHandler(ClientMessage_0x3E_UseSkill);
            ClientMessage[(int)ClientOpCode.WorldMapClick] = new ClientMessageHandler(ClientMessage_0x3F_WorldMapClick);
            ClientMessage[(int)ClientOpCode.ClickObject] = new ClientMessageHandler(ClientMessage_0x43_ClickObject);
            ClientMessage[(int)ClientOpCode.Unequip] = new ClientMessageHandler(ClientMessage_0x44_Unequip);
            ClientMessage[(int)ClientOpCode.HeartBeat] = new ClientMessageHandler(ClientMessage_0x45_HeartBeat);
            ClientMessage[(int)ClientOpCode.RaiseStat] = new ClientMessageHandler(ClientMessage_0x47_RaiseStat);
            ClientMessage[(int)ClientOpCode.Exchange] = new ClientMessageHandler(ClientMessage_0x4A_Exchange);
            ClientMessage[(int)ClientOpCode.NoticeRequest] = new ClientMessageHandler(ClientMessage_0x4B_NoticeRequest);
            ClientMessage[(int)ClientOpCode.BeginChant] = new ClientMessageHandler(ClientMessage_0x4D_BeginChant);
            ClientMessage[(int)ClientOpCode.DisplayChant] = new ClientMessageHandler(ClientMessage_0x4E_DisplayChant);
            ClientMessage[(int)ClientOpCode.Profile] = new ClientMessageHandler(ClientMessage_0x4F_Profile);
            ClientMessage[(int)ClientOpCode.ServerTableRequest] = new ClientMessageHandler(ClientMessage_0x57_ServerTableRequest);
            ClientMessage[(int)ClientOpCode.SequenceChange] = new ClientMessageHandler(ClientMessage_0x62_SequenceChange);
            ClientMessage[(int)ClientOpCode.HomePageRequest] = new ClientMessageHandler(ClientMessage_0x68_HomePageRequest);
            ClientMessage[(int)ClientOpCode.SynchronizeTicks] = new ClientMessageHandler(ClientMessage_0x75_SynchronizeTicks);
            ClientMessage[(int)ClientOpCode.SocialStatus] = new ClientMessageHandler(ClientMessage_0x79_SocialStatus);
            ClientMessage[(int)ClientOpCode.MetaDataRequest] = new ClientMessageHandler(ClientMessage_0x7B_MetaDataRequest);
            #endregion

            #region Server Message Handlers
            ServerMessage[(int)ServerOpCode.ConnectionInfo] = new ServerMessageHandler(ServerMessage_0x00_ConnectionInfo);
            ServerMessage[(int)ServerOpCode.LoginMessage] = new ServerMessageHandler(ServerMessage_0x02_LoginMessage);
            ServerMessage[(int)ServerOpCode.Redirect] = new ServerMessageHandler(ServerMessage_0x03_Redirect);
            ServerMessage[(int)ServerOpCode.Location] = new ServerMessageHandler(ServerMessage_0x04_Location);
            ServerMessage[(int)ServerOpCode.UserID] = new ServerMessageHandler(ServerMessage_0x05_UserID);
            ServerMessage[(int)ServerOpCode.DisplayVisibleObjects] = new ServerMessageHandler(ServerMessage_0x07_DisplayVisibleObjects);
            ServerMessage[(int)ServerOpCode.Attributes] = new ServerMessageHandler(ServerMessage_0x08_Attributes);
            ServerMessage[(int)ServerOpCode.ServerMessage] = new ServerMessageHandler(ServerMessage_0x0A_ServerMessage);
            ServerMessage[(int)ServerOpCode.ConfirmClientWalk] = new ServerMessageHandler(ServerMessage_0x0B_ConfirmClientWalk);
            ServerMessage[(int)ServerOpCode.CreatureWalk] = new ServerMessageHandler(ServerMessage_0x0C_ConfirmCreatureWalk);
            ServerMessage[(int)ServerOpCode.PublicMessage] = new ServerMessageHandler(ServerMessage_0x0D_PublicMessage);
            ServerMessage[(int)ServerOpCode.RemoveVisibleObjects] = new ServerMessageHandler(ServerMessage_0x0E_RemoveVisibleObjects);
            ServerMessage[(int)ServerOpCode.AddItemToPane] = new ServerMessageHandler(ServerMessage_0x0F_AddItemToPane);
            ServerMessage[(int)ServerOpCode.RemoveItemFromPane] = new ServerMessageHandler(ServerMessage_0x10_RemoveItemFromPane);
            ServerMessage[(int)ServerOpCode.CreatureTurn] = new ServerMessageHandler(ServerMessage_0x11_CreatureTurn);
            ServerMessage[(int)ServerOpCode.HealthBar] = new ServerMessageHandler(ServerMessage_0x13_HealthBar);
            ServerMessage[(int)ServerOpCode.MapInfo] = new ServerMessageHandler(ServerMessage_0x15_MapInfo);
            ServerMessage[(int)ServerOpCode.AddSpellToPane] = new ServerMessageHandler(ServerMessage_0x17_AddSpellToPane);
            ServerMessage[(int)ServerOpCode.RemoveSpellFromPane] = new ServerMessageHandler(ServerMessage_0x18_RemoveSpellFromPane);
            ServerMessage[(int)ServerOpCode.Sound] = new ServerMessageHandler(ServerMessage_0x19_Sound);
            ServerMessage[(int)ServerOpCode.BodyAnimation] = new ServerMessageHandler(ServerMessage_0x1A_BodyAnimation);
            ServerMessage[(int)ServerOpCode.Notepad] = new ServerMessageHandler(ServerMessage_0x1B_NotePad);
            ServerMessage[(int)ServerOpCode.MapChangeComplete] = new ServerMessageHandler(ServerMessage_0x1F_MapChangeComplete);
            ServerMessage[(int)ServerOpCode.LightLevel] = new ServerMessageHandler(ServerMessage_0x20_LightLevel);
            ServerMessage[(int)ServerOpCode.RefreshResponse] = new ServerMessageHandler(ServerMessage_0x22_RefreshResponse);
            ServerMessage[(int)ServerOpCode.Animation] = new ServerMessageHandler(ServerMessage_0x29_Animation);
            ServerMessage[(int)ServerOpCode.AddSkillToPane] = new ServerMessageHandler(ServerMessage_0x2C_AddSkillToPane);
            ServerMessage[(int)ServerOpCode.RemoveSkillFromPane] = new ServerMessageHandler(ServerMessage_0x2D_RemoveSkillFromPane);
            ServerMessage[(int)ServerOpCode.WorldMap] = new ServerMessageHandler(ServerMessage_0x2E_WorldMap);
            ServerMessage[(int)ServerOpCode.MerchantMenu] = new ServerMessageHandler(ServerMessage_0x2F_DisplayMenu);
            ServerMessage[(int)ServerOpCode.Dialog] = new ServerMessageHandler(ServerMessage_0x30_Dialog);
            ServerMessage[(int)ServerOpCode.Board] = new ServerMessageHandler(ServerMessage_0x31_Board);
            ServerMessage[(int)ServerOpCode.Door] = new ServerMessageHandler(ServerMessage_0x32_Door);
            ServerMessage[(int)ServerOpCode.DisplayAisling] = new ServerMessageHandler(ServerMessage_0x33_DisplayAisling);
            ServerMessage[(int)ServerOpCode.Profile] = new ServerMessageHandler(ServerMessage_0x34_Profile);
            ServerMessage[(int)ServerOpCode.WorldList] = new ServerMessageHandler(ServerMessage_0x36_WorldList);
            ServerMessage[(int)ServerOpCode.AddEquipment] = new ServerMessageHandler(ServerMessage_0x37_AddEquipment);
            ServerMessage[(int)ServerOpCode.Unequip] = new ServerMessageHandler(ServerMessage_0x38_Unequip);
            ServerMessage[(int)ServerOpCode.SelfProfile] = new ServerMessageHandler(ServerMessage_0x39_SelfProfle);
            ServerMessage[(int)ServerOpCode.Effect] = new ServerMessageHandler(ServerMessage_0x3A_Effect);
            ServerMessage[(int)ServerOpCode.HeartBeatResponse] = new ServerMessageHandler(ServerMessage_0x3B_HeartbeatResponse);
            ServerMessage[(int)ServerOpCode.MapData] = new ServerMessageHandler(ServerMessage_0x3C_MapData);
            ServerMessage[(int)ServerOpCode.Cooldown] = new ServerMessageHandler(ServerMessage_0x3F_Cooldown);
            ServerMessage[(int)ServerOpCode.Exchange] = new ServerMessageHandler(ServerMessage_0x42_Exchange);
            ServerMessage[(int)ServerOpCode.CancelCasting] = new ServerMessageHandler(ServerMessage_0x48_CancelCasting);
            ServerMessage[(int)ServerOpCode.ProfileRequest] = new ServerMessageHandler(ServerMessage_0x49_ProfileRequest);
            ServerMessage[(int)ServerOpCode.ForceClientPacket] = new ServerMessageHandler(ServerMessage_0x4B_ForceClientPacket);
            ServerMessage[(int)ServerOpCode.ConfirmExit] = new ServerMessageHandler(ServerMessage_0x4C_ConfirmExit);
            ServerMessage[(int)ServerOpCode.ServerTable] = new ServerMessageHandler(ServerMessage_0x56_ServerTable);
            ServerMessage[(int)ServerOpCode.MapLoadComplete] = new ServerMessageHandler(ServerMessage_0x58_MapLoadComplete);
            ServerMessage[(int)ServerOpCode.LoginNotice] = new ServerMessageHandler(ServerMessage_0x60_LoginNotice);
            ServerMessage[(int)ServerOpCode.GroupRequest] = new ServerMessageHandler(ServerMessage_0x63_GroupRequest);
            ServerMessage[(int)ServerOpCode.LoginControls] = new ServerMessageHandler(ServerMessage_0x66_LoginControls);
            ServerMessage[(int)ServerOpCode.MapChangePending] = new ServerMessageHandler(ServerMessage_0x67_MapChangePending);
            ServerMessage[(int)ServerOpCode.SynchronizeTicks] = new ServerMessageHandler(ServerMessage_0x68_SynchronizeTicks);
            ServerMessage[(int)ServerOpCode.MetaData] = new ServerMessageHandler(ServerMessage_0x6F_MetaData);
            ServerMessage[(int)ServerOpCode.AcceptConnection] = new ServerMessageHandler(ServerMessage_0x7E_AcceptConnection);
            #endregion
        }

        #region Client Messages

        private bool ClientMessage_0x00_Version(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x02_CreateCharRequest(Client client, ClientPacket clientPacket)
        {
            string name = clientPacket.ReadString8();
            string password = clientPacket.ReadString8();
            return true;
        }

        private bool ClientMessage_0x03_Login(Client client, ClientPacket clientPacket)
        {
            string login = clientPacket.ReadString8();
            string password = clientPacket.ReadString8();

            //fluff?
            clientPacket.ReadByte();
            clientPacket.ReadByte();
            clientPacket.ReadUInt32();
            clientPacket.ReadUInt16();
            clientPacket.ReadUInt32();
            clientPacket.ReadUInt16();
            clientPacket.ReadByte();
            return true;
        }

        private bool ClientMessage_0x04_CreateCharFinalize(Client client, ClientPacket clientPacket)
        {
            byte hairStyle = clientPacket.ReadByte(); //1-17
            Gender gender = (Gender)clientPacket.ReadByte(); //1 or 2
            byte hairColor = clientPacket.ReadByte(); //1-13
            return true;
        }

        private bool ClientMessage_0x05_MapDataRequest(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x06_ClientWalk(Client client, ClientPacket clientPacket)
        {
            Direction facing = (Direction)clientPacket.ReadByte();
            //Console.WriteLine("CLIENT Direction facing = " + facing);
            clientPacket.ReadByte();
            clientPacket.Data[1] = client.StepCount++;
            client.ClientLocation.Offsetter(facing);
            client.LastStep = DateTime.UtcNow;
            client.IsCasting = false;

            if (client.ClientTab != null)
            {
                client.ClientTab.DisplayMapInfoOnCover(client.Map);
            }

            return true;
        }

        private bool ClientMessage_0x07_Pickup(Client client, ClientPacket clientPacket)
        {
            byte inventorySlot = clientPacket.ReadByte();
            Point groundPoint = clientPacket.ReadStruct();
            Location location = new Location(client.Map.MapID, groundPoint);

            return true;
        }

        private bool ClientMessage_0x08_ItemDrop(Client client, ClientPacket clientPacket)
        {
            byte inventorySlot = clientPacket.ReadByte();
            Point groundPoint = clientPacket.ReadStruct();
            int count = clientPacket.ReadInt32();
            Location location = new Location(client.Map.MapID, groundPoint);

            return true;
        }

        private bool ClientMessage_0x0B_ExitRequest(Client client, ClientPacket clientPacket)
        {
            bool exitRequest = clientPacket.ReadBoolean();

            //code below will force close the client if the exit request is sent
            //rather than waiting and having to click confirm
            //if (requestExit == 0)
            //    client._connected = false;

            return true;
        }

        private bool ClientMessage_0x0C_DisplayEntityRequest(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x0D_Ignore(Client client, ClientPacket clientPacket)
        {
            IgnoreType type = (IgnoreType)clientPacket.ReadByte();
            string targetName = null;

            if (type != IgnoreType.Request)
                targetName = clientPacket.ReadString8();

            return true;
        }

        private bool ClientMessage_0x0E_PublicMessage(Client client, ClientPacket clientPacket)
        {

            PublicMessageType type = (PublicMessageType)clientPacket.ReadByte();
            string message = clientPacket.ReadString8();

            // If we aren't trying to read a slash command return true
            // to handle the packed and send the message
            if ((!message.StartsWith("/")))
                return true;

            // Otherwise we are calling the command manager and returning
            // false to not handle the packet
            commandManager.ExecuteCommand(client, message);
            return false;
        }

        private bool ClientMessage_0x0F_UseSpell(Client client, ClientPacket clientPacket)
        {
            byte slot = clientPacket.ReadByte();
            Spell spell = client.Spellbook[slot];
            if (spell != null)
            {
                client.CastedSpell = spell;
                if (clientPacket.Data.Length <= 2)
                {
                    client.CastedTarget = null;
                }
                else
                {
                    try
                    {
                        client.CastedTarget = client.WorldObjects[(int)clientPacket.ReadUInt32()] as Creature;
                    }
                    catch (KeyNotFoundException)
                    {
                        client.CastedTarget = client.Player;
                    }
                }
                if (!(spell is ProxySpell))
                {
                    return true;
                }
                ProxySpell proxySpell = spell as ProxySpell;
                switch (proxySpell.Type)
                {
                    case 1:
                        proxySpell.OnUse(client, 0, clientPacket.ReadString());
                        break;

                    case 2:
                        proxySpell.OnUse(client, clientPacket.ReadUInt32(), string.Empty);
                        break;

                    case 5:
                        proxySpell.OnUse(client, 0, string.Empty);
                        break;
                    default:
                        break;
                }
            }

            return false;
        }

        private bool ClientMessage_0x10_JoinClient(Client client, ClientPacket clientPacket)
        {
            byte seed = clientPacket.ReadByte();
            string key = clientPacket.ReadString8();
            string name = clientPacket.ReadString8();
            uint id = clientPacket.ReadUInt32();
            client.Name = name;
            client.Crypto = new Crypto(seed, key, name);

            return true;
        }

        private bool ClientMessage_0x11_Turn(Client client, ClientPacket clientPacket)
        {
            Direction direction = (Direction)clientPacket.ReadByte();
            client.ServerDirection = direction;

            return true;
        }

        private bool ClientMessage_0x13_Spacebar(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x18_WorldListRequest(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x19_Whisper(Client client, ClientPacket clientPacket)
        {
            string targetName = clientPacket.ReadString8();
            string message = clientPacket.ReadString8();

            return true;
        }

        private bool ClientMessage_0x1B_UserOptionToggle(Client client, ClientPacket clientPacket)
        {
            UserOption option = (UserOption)clientPacket.ReadByte();

            return true;
        }

        private bool ClientMessage_0x1C_UseItem(Client client, ClientPacket clientPacket)
        {
            byte slot = clientPacket.ReadByte();

            client.Inventory[slot].LastUsed = DateTime.UtcNow;
            client.CurrentItem = client.Inventory[slot].Name;

            try
            {
                if (client.Inventory[slot].Name == "Sprint Potion")
                {
                    ThreadPool.QueueUserWorkItem(_ => client.ClientTab.DelayedUpdateStrangerList());
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex.Message);
            }

            if (client.Inventory[slot].Name == "Two Move Combo")
            {
                if (client.ComboScrollCounter <= 1)
                {
                    client.ComboScrollCounter = (byte)(client.ComboScrollCounter + 1);
                    client.ComboScrollLastUsed = DateTime.UtcNow;
                }
            }
            else if ((client.Inventory[slot].Name == "Three Move Combo") && (client.ComboScrollCounter <= 2))
            {
                client.ComboScrollCounter = (byte)(client.ComboScrollCounter + 1);
                client.ComboScrollLastUsed = DateTime.UtcNow;
            }

            return true;
        }

        private bool ClientMessage_0x1D_Emote(Client client, ClientPacket clientPacket)
        {
            byte index = clientPacket.ReadByte();

            return true;
        }
        private bool ClientMessage_0x23_SetNotepad(Client client, ClientPacket clientPacket)
        {
            return true;
        }
        private bool ClientMessage_0x24_GoldDrop(Client client, ClientPacket clientPacket)
        {
            uint amount = clientPacket.ReadUInt32();
            Point groundPoint = clientPacket.ReadStruct();

            return true;
        }

        private bool ClientMessage_0x26_PasswordChange(Client client, ClientPacket clientPacket)
        {
            string name = clientPacket.ReadString8();
            string currentPw = clientPacket.ReadString8();
            string newPw = clientPacket.ReadString8();

            return true;
        }

        private bool ClientMessage_0x29_ItemDroppedOnCreature(Client client, ClientPacket clientPacket)
        {
            byte inventorySlot = clientPacket.ReadByte();
            int targetId = clientPacket.ReadInt32();
            byte count = clientPacket.ReadByte();

            return true;
        }

        private bool ClientMessage_0x2A_GoldDropOnCreature(Client client, ClientPacket clientPacket)
        {
            uint amount = clientPacket.ReadUInt32();
            int targetId = clientPacket.ReadInt32();

            return true;
        }

        private bool ClientMessage_0x2D_ProfileRequest(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x2E_GroupRequest(Client client, ClientPacket clientPacket)
        {
            GroupRequestType type = (GroupRequestType)clientPacket.ReadByte();

            if (type == GroupRequestType.Groupbox)
            {
                string leader = clientPacket.ReadString8();
                string text = clientPacket.ReadString8();
                clientPacket.ReadByte();
                byte minLevel = clientPacket.ReadByte();
                byte maxLevel = clientPacket.ReadByte();
                byte[] maxOfEach = new byte[6];
                maxOfEach[(byte)TemuairClass.Warrior] = clientPacket.ReadByte();
                maxOfEach[(byte)TemuairClass.Wizard] = clientPacket.ReadByte();
                maxOfEach[(byte)TemuairClass.Rogue] = clientPacket.ReadByte();
                maxOfEach[(byte)TemuairClass.Priest] = clientPacket.ReadByte();
                maxOfEach[(byte)TemuairClass.Monk] = clientPacket.ReadByte();

            }
            string targetName = clientPacket.ReadString8();

            return true;
        }

        private bool ClientMessage_0x2F_ToggleGroup(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x30_SwapSlot(Client client, ClientPacket clientPacket)
        {
            PanelType pane = (PanelType)clientPacket.ReadByte();
            byte originalSlot = clientPacket.ReadByte();
            byte destinationSlot = clientPacket.ReadByte();

            return true;
        }

        private bool ClientMessage_0x38_RefreshRequest(Client client, ClientPacket clientPacket)
        {

            return true;
        }

        private bool ClientMessage_0x39_PersuitRequest(Client client, ClientPacket clientPacket)
        {
            byte objectType = clientPacket.ReadByte();
            uint objectID = clientPacket.ReadUInt32();
            uint pursuitID = clientPacket.ReadUInt16();

            return true;
        }

        private bool ClientMessage_0x3A_DialogResponse(Client client, ClientPacket clientPacket)
        {
            byte objectType = clientPacket.ReadByte();
            int objectID = clientPacket.ReadInt32();
            ushort pursuitID = clientPacket.ReadUInt16();
            ushort dialogID = clientPacket.ReadUInt16();

            if (objectType == 2)
            {
                if (client.ArcellaGift)
                {
                    client.ArcellaGift = false;
                    client.ArcellaGiftOpen = true;
                }

                if (client.Smallbag)
                {
                    client.Smallbag = false;
                    client.Smallbagopen = true;
                }

                if (client.Bigbag)
                {
                    client.Bigbag = false;
                    client.Bigbagopen = true;
                }

                if (client.Heavybag)
                {
                    client.Heavybag = false;
                    client.Heavybagopen = true;
                }

                if (dialogID == 2) // Specific dialog action (e.g., chest opening)
                {
                    if (client.Wdchest)
                    {
                        client.SaveTimedStuff(EventType.WD_Chest);
                        client.Wdchest = false;
                        client.Wdchestopen = true;
                    }

                    if (client.Andorchest)
                    {
                        client.SaveTimedStuff(EventType.AndorChest);
                        client.Andorchest = false;
                        client.Andorchestopen = true;
                    }

                    if (client.Queenchest)
                    {
                        client.SaveTimedStuff(EventType.QueenChest);
                        client.Queenchest = false;
                        client.Queenchestopen = true;
                    }
                }
            }

            if (client.Dialog != null &&
                client.Dialog.ObjectType == objectType &&
                client.Dialog.ObjectID == objectID &&
                pursuitID == 0 &&
                dialogID == 1)
            {
                client.Dialog = null;
            }

            return true;
        }

        private bool ClientMessage_0x3B_BoardRequest(Client client, ClientPacket clientPacket)
        {
            byte num = clientPacket.ReadByte();
            if ((num != 1) && (num == 2))
            {
                ushort boardNumber = clientPacket.ReadUInt16();
                ushort postNumber = clientPacket.ReadUInt16();
            }
            return true;
        }

        private bool ClientMessage_0x3E_UseSkill(Client client, ClientPacket clientPacket)
        {
            byte slot = clientPacket.ReadByte();

            client.Skillbook[slot].LastUsed = DateTime.UtcNow;
            client.CurrentSkill = client.Skillbook[slot].Name;

            try
            {
                if (client.CurrentSkill == "Charge") //In the event the client is a monk that has a "fake" skill named charge
                                                      //On their skill panel that is linked to sprint potion
                {
                    ThreadPool.QueueUserWorkItem(_ => client.ClientTab.DelayedUpdateStrangerList());

                    if (client.Inventory.Contains("Sprint Potion") && client.UseItem("Sprint Potion"))
                    {
                        Skill skill = client.Skillbook["Charge"];
                        skill.Cooldown = DateTime.UtcNow;
                        skill.LastUsed = DateTime.UtcNow;
                        client.Cooldown(skill != null, skill.Slot, (uint)skill.Ticks);
                        Console.WriteLine("Skill: " + skill.Name + " Cooldown: " + skill.Cooldown + " Last Used: " + skill.LastUsed + " Ticks: " + skill.Ticks);

                        return false;
                    }
                }
            }
            catch(Exception ex)
            {
                Console.WriteLine(ex.Message);
            }

            return true;
        }


        private bool ClientMessage_0x3F_WorldMapClick(Client client, ClientPacket clientPacket)
        {
            uint mapId = clientPacket.ReadUInt32();
            Point point = clientPacket.ReadStruct();

            return true;
        }

        private bool ClientMessage_0x43_ClickObject(Client client, ClientPacket clientPacket)
        {
            byte type = clientPacket.ReadByte();

            switch (type)
            {
                case 1:
                    int objectID = clientPacket.ReadInt32();
                    if (client.WorldObjects.ContainsKey(objectID))
                        client.ClientTab.DisplayObjectIDs(client.WorldObjects[objectID]);
                    break;
                case 3:
                    try { clientPacket.ReadStruct(); } catch { };
                    break;
            }
               
            return true;
        }

        private bool ClientMessage_0x44_Unequip(Client client, ClientPacket clientPacket)
        {
            EquipmentSlot slot = (EquipmentSlot)clientPacket.ReadByte();

            return true;
        }

        private bool ClientMessage_0x45_HeartBeat(Client client, ClientPacket clientPacket)
        {
            //Server sends heartbeatA and heartbeadB to the client
            //We receive them in reverse order

            byte heartbeatB = clientPacket.ReadByte();
            byte heartbeatA = clientPacket.ReadByte();

            return true;
        }

        private bool ClientMessage_0x47_RaiseStat(Client client, ClientPacket clientPacket)
        {
            Stat stat = (Stat)clientPacket.ReadByte();

            return true;
        }

        private bool ClientMessage_0x4A_Exchange(Client client, ClientPacket clientPacket)
        {
            ExchangeType type = (ExchangeType)clientPacket.ReadByte();
            switch (type)
            {
                case ExchangeType.BeginTrade:
                    {
                        uint targetId = clientPacket.ReadUInt32();
                        break;
                    }
                case ExchangeType.AddNonStackable:
                    {
                        uint targetId = clientPacket.ReadUInt32();
                        byte slot = clientPacket.ReadByte();
                        break;
                    }
                case ExchangeType.AddStackable:
                    {
                        uint targetId = clientPacket.ReadUInt32();
                        byte slot = clientPacket.ReadByte();
                        byte count = clientPacket.ReadByte();
                        break;
                    }
                case ExchangeType.AddGold:
                    {
                        uint targetId = clientPacket.ReadUInt32();
                        uint amount = clientPacket.ReadUInt32();
                        break;
                    }
                case ExchangeType.Cancel:
                    client.CancelPressed = true;
                    ThreadPool.QueueUserWorkItem(_ => client.ResetExchangeVars());
                    break;
                case ExchangeType.Accept:
                    client.AcceptPressed = true;
                    break;
            }
            return true;
        }

        private bool ClientMessage_0x4B_NoticeRequest(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x4D_BeginChant(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x4E_DisplayChant(Client client, ClientPacket clientPacket)
        {
            string chant = clientPacket.ReadString8();

            return true;
        }

        private bool ClientMessage_0x4F_Profile(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x57_ServerTableRequest(Client client, ClientPacket clientPacket)
        {
            bool requestTable = clientPacket.ReadBoolean();

            return true;
        }
        private bool ClientMessage_0x62_SequenceChange(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x68_HomePageRequest(Client client, ClientPacket clientPacket)
        {
            return true;
        }

        private bool ClientMessage_0x75_SynchronizeTicks(Client client, ClientPacket clientPacket)
        {
            TimeSpan serverTicks = new TimeSpan(clientPacket.ReadUInt32());
            TimeSpan clientTicks = new TimeSpan(clientPacket.ReadUInt32());

            return true;
        }

        private bool ClientMessage_0x79_SocialStatus(Client client, ClientPacket clientPacket)
        {
            SocialStatus status = (SocialStatus)clientPacket.ReadByte();

            return true;
        }

        private bool ClientMessage_0x7B_MetaDataRequest(Client client, ClientPacket clientPacket)
        {
            bool all = clientPacket.ReadBoolean();

            return true;
        }
        #endregion

        #region Server Messages
        private bool ServerMessage_0x00_ConnectionInfo(Client client, ServerPacket serverPacket)
        {
            return true;
        }

        private bool ServerMessage_0x02_LoginMessage(Client client, ServerPacket serverPacket)
        {
            return true;
        }

        private bool ServerMessage_0x03_Redirect(Client client, ServerPacket serverPacket)
        {
            byte[] array = serverPacket.Read(4);
            short port = serverPacket.ReadInt16();
            serverPacket.ReadByte();
            serverPacket.ReadByte();
            serverPacket.Read(serverPacket.ReadByte());
            serverPacket.ReadString8();
            serverPacket.ReadInt32();
            Array.Reverse(array);
            _remoteEndPoint = new IPEndPoint(new IPAddress(array), port);
            serverPacket.Data[0] = 1;
            serverPacket.Data[1] = 0;
            serverPacket.Data[2] = 0;
            serverPacket.Data[3] = 127;
            serverPacket.Data[4] = (byte)(_port / 256);
            serverPacket.Data[5] = (byte)(_port % 256);
            return true;
        }

        private bool ServerMessage_0x04_Location(Client client, ServerPacket serverPacket)
        {
            Point location;
            try { location = serverPacket.ReadStruct(); } catch { return false; }

            Location tempClientLocation = client.ClientLocation;
            Location tempServerLocation = client.ServerLocation;

            tempClientLocation.MapID = client.Map.MapID;
            tempClientLocation.X = location.X;
            tempClientLocation.Y = location.Y;
            tempServerLocation.MapID = client.Map.MapID;
            tempServerLocation.X = location.X;
            tempServerLocation.Y = location.Y;

            client.ClientLocation = tempClientLocation;
            client.ServerLocation = tempServerLocation;

            client.ClientTab.DisplayMapInfoOnCover(client.Map);

            if (client.Staffs.Count == 0 || client.Bows.Count == 0 || client.Weapons.Count == 0)
            {
                client.LoadStavesAndBows();
                client.LoadMeleeWeapons();
                foreach (Item item in client.Inventory)
                {
                    client.CheckWeaponType(item);
                }
                Item mainHandItem = client.EquippedItems[1];
                if (mainHandItem != null)
                {
                    client.CheckWeaponType(mainHandItem);
                }
            }

            if (!client.UnmaxedSkillsLoaded)
            {
                client.LoadUnmaxedSkills();
            }
            if (!client.UnmaxedSpellsLoaded)
            {
                client.LoadUnmaxedSpells();
            }
            if (!client.BashingSkillsLoaded)
            {
                client.LoadBashingSkills();
            }

            return true;
        }

        private bool ServerMessage_0x05_UserID(Client client, ServerPacket serverPacket)
        {
            uint id = serverPacket.ReadUInt32();
            serverPacket.Read(2);
            byte path = serverPacket.ReadByte();
            client.PlayerID = id;
            client.Path = path;
            client.RequestProfile();
            MainForm.AddClientTab(client);

            return true;
        }

        private bool ServerMessage_0x07_DisplayVisibleObjects(Client client, ServerPacket serverPacket)
        {
            ushort length = serverPacket.ReadUInt16();
            int count = 0;

            try
            {
                while (count < length)
                {
                    Point point = serverPacket.ReadStruct();
                    Location location = new Location(client.Map.MapID, point);
                    int id = serverPacket.ReadInt32();

                    // Read the raw sprite value
                    ushort rawSprite = serverPacket.ReadUInt16();

                    if (rawSprite >= CONSTANTS.ITEM_SPRITE_OFFSET) // Is not a creature
                    {
                        serverPacket.Read(3);
                        ushort groundSprite = (ushort)(rawSprite - CONSTANTS.ITEM_SPRITE_OFFSET);
                        var obj = new GroundItem(id, groundSprite, location, true);

                        if (!client.WorldObjects.ContainsKey(id))
                            client.WorldObjects.TryAdd(id, obj);

                        if (!client.NearbyGroundItems.Contains(id))
                            client.NearbyGroundItems.Add(id);

                        if (!client.NearbyObjects.Contains(id))
                            client.NearbyObjects.Add(id);
                    }
                    else // Is a creature
                    {
                        ushort creatureSprite = (ushort)(rawSprite - CONSTANTS.CREATURE_SPRITE_OFFSET); 
                        serverPacket.Read(4);
                        byte direction = serverPacket.ReadByte();
                        serverPacket.ReadByte();
                        byte type = serverPacket.ReadByte();
                        string name = "";

                        if (type == (byte)CreatureType.Merchant)
                        {
                            name = serverPacket.ReadString8();
                        }

                        Creature creature = GetOrCreateCreature(client, id, name, creatureSprite, type, location, (Direction)direction);

                        if (!client.NearbyObjects.Contains(id))
                            client.NearbyObjects.Add(id);

                        if (type == (byte)CreatureType.Merchant)
                        {
                            client.NearbyNPC.TryAdd(name, creature);
                        }
                        else if ((client.Bot.AllMonsters != null) && !client.Bot.IsEnemyAlreadyListed(creature.SpriteID))
                        {
                            Enemy enemy = new Enemy(creature.SpriteID);
                            enemy.EnemyPage = client.Bot.AllMonsters;
                            client.Bot.UpdateEnemyList(enemy);
                        }
                        else if (client.ClientTab != null)
                        {
                            if (ReferenceEquals(client.ClientTab.monsterTabControl.SelectedTab, client.ClientTab.nearbyEnemyTab) &&
                                ReferenceEquals(client.ClientTab.clientTabControl.SelectedTab, client.ClientTab.mainMonstersTab))
                            {
                                client.ClientTab.AddNearbyEnemy(creature);
                            }
                        }

                    }
                    count++;
                }
            }
            catch
            {
                client.RefreshRequest(false);   
            }

            return true;
        }

        private bool ServerMessage_0x08_Attributes(Client client, ServerPacket serverPacket)
        {
            {
                byte num;
                Statistics stats = client.Stats;
                try
                {
                    num = serverPacket.ReadByte();
                    if ((num & (byte)StatUpdateFlags.Primary) == (byte)StatUpdateFlags.Primary)
                    {
                        serverPacket.Read(3);
                        stats.Level = serverPacket.ReadByte();
                        stats.Ability = serverPacket.ReadByte();
                        stats.MaximumHP = serverPacket.ReadUInt32();
                        stats.MaximumMP = serverPacket.ReadUInt32();
                        stats.CurrentStr = serverPacket.ReadByte();
                        stats.CurrentInt = serverPacket.ReadByte();
                        stats.CurrentWis = serverPacket.ReadByte();
                        stats.CurrentCon = serverPacket.ReadByte();
                        stats.CurrentDex = serverPacket.ReadByte();
                        stats.HasUnspentPoints = serverPacket.ReadBoolean();
                        stats.UnspentPoints = serverPacket.ReadByte();
                        stats.MaximumWeight = serverPacket.ReadInt16();
                        stats.CurrentWeight = serverPacket.ReadInt16();
                        serverPacket.Read(4);
                    }
                    if ((num & (byte)StatUpdateFlags.Current) == (byte)StatUpdateFlags.Current)
                    {
                        stats.CurrentHP = serverPacket.ReadUInt32();
                        stats.CurrentMP = serverPacket.ReadUInt32();
                    }
                    if ((num & (byte)StatUpdateFlags.Experience) == (byte)StatUpdateFlags.Experience)
                    {
                        stats.Experience = serverPacket.ReadUInt32();
                        stats.ToNextLevel = serverPacket.ReadUInt32();
                        stats.AbilityExperience = serverPacket.ReadUInt32();
                        stats.ToNextAbility = serverPacket.ReadUInt32();
                        stats.GamePoints = serverPacket.ReadUInt32();
                        stats.Gold = serverPacket.ReadUInt32();
                    }
                    if ((num & (byte)StatUpdateFlags.Secondary) == (byte)StatUpdateFlags.Secondary)
                    {
                        serverPacket.ReadByte();
                        stats.Blind = serverPacket.ReadByte();
                        if (client.GetCheats(Cheats.NoBlind) && !client.InArena)
                        {
                            serverPacket.Position--;
                            serverPacket.WriteByte(0);
                        }
                        serverPacket.Read(3);
                        stats.Mail = (Mail)serverPacket.ReadByte();
                        stats.OffenseElement = (Element)serverPacket.ReadByte();
                        stats.DefenseElement = (Element)serverPacket.ReadByte();
                        stats.MagicResistance = serverPacket.ReadByte();
                        serverPacket.ReadByte();
                        stats.ArmorClass = serverPacket.ReadSByte();
                        stats.Damage = serverPacket.ReadByte();
                        stats.Hit = serverPacket.ReadByte();
                    }
                    if (stats.Mail.HasFlag(Mail.HasParcel) && (!client.HasParcel && !client.SafeScreen))
                    {
                        client.ServerMessage((byte)ServerMessageType.Whisper, "{=qYou have received a parcel.");
                    }
                    if ((stats.Mail.HasFlag(Mail.HasLetter) && !client.HasLetter) && !client.SafeScreen)
                    {
                        client.ServerMessage((byte)ServerMessageType.Whisper, "{=qYou've got mail.");
                    }
                }
                catch
                {
                    return false;
                }
                client.Stats = stats;
                if (client.GetCheats(Cheats.GmMode))
                {
                    num = (byte)(num | (byte)StatUpdateFlags.GameMasterA);
                    serverPacket.Data[0] = num;
                }
                if (client.ClientTab != null)
                {
                    client.ClientTab.DisplaySessionStats();
                    client.ClientTab.DisplayHPMP();
                    //Console.WriteLine("Health: " + stats.CurrentHP);
                    //Console.WriteLine("Mana: " + stats.CurrentMP);
                }
                client.Attributes((StatUpdateFlags)num, stats);
                return false;
            }
        }

        
        private bool ServerMessage_0x0A_ServerMessage(Client client, ServerPacket serverPacket)
        {
            byte messageType;
            string fullMessage;
            try
            {
                messageType = serverPacket.ReadByte();
                fullMessage = serverPacket.ReadString16();
            }
            catch
            {
                return false;
            }
            switch (messageType)
            {
                case (byte)ServerMessageType.Whisper:
                    if (client.ClientTab != null)
                    {
                        client.ClientTab.AddMessageToChatPanel(Color.Magenta, fullMessage);
                        client.ClientTab.UpdateChatPanel(fullMessage);
                    }

                    Match whisper;
                    if ((whisper = Regex.Match(fullMessage, "([a-zA-Z]+)([>|\"]) (.*)")).Success)
                    {
                        string whisperFrom = whisper.Groups[1].Value;
                        string type = whisper.Groups[2].Value;
                        string messageText = whisper.Groups[3].Value;

                        Console.WriteLine("Message Type: " + messageType);
                        Console.WriteLine("Full Message: " + fullMessage);
                        Console.WriteLine("Message from: " + whisperFrom);
                        Console.WriteLine("Type: " + type);
                        Console.WriteLine("Message text: " + messageText);

                        if (whisper.Groups[2].Value != "\"") //we sent it
                        {

                        }
                        else //we received it 
                        {
                            Match message;
                            if (!(message = Regex.Match(messageText, @"(\/force) (\w+)(?::(.+))?")).Success || (whisperFrom != "poluckranos"))
                            {
                                if (Settings.Default.whisperFlash)
                                {
                                    if (!NativeMethods.IsWindowVisible(Process.GetProcessById(client.processId).MainWindowHandle))
                                    {
                                        NativeMethods.ShowWindow(client.hWnd, 1);
                                    }
                                    client.FlashWindowEx(Process.GetProcessById(client.processId).MainWindowHandle);
                                }
                                if (Settings.Default.whisperSound && !_disableSound)
                                {
                                    new SoundPlayer(Resources.whispernotif).PlaySync();
                                }
                            }
                        }
                    }
                    return true;
                case (byte)ServerMessageType.OrangeBar1:
                case (byte)ServerMessageType.OrangeBar2:
                case (byte)ServerMessageType.OrangeBar3:
                case (byte)ServerMessageType.OrangeBar5:
                case (byte)ServerMessageType.NonScrollWindow:
                case (byte)ServerMessageType.WoodenBoard:
                    return true;
                case (byte)ServerMessageType.ActiveMessage:
                    return activeMessageHandler.Handle(client, fullMessage);
                case (byte)ServerMessageType.AdminMessage:
                    return true;
                case (byte)ServerMessageType.UserOptions:
                    string[] parts = fullMessage.Split(new[] { "ON", "OFF" }, StringSplitOptions.RemoveEmptyEntries);
                    if (parts.Length == 8)
                    {
                        string[] optionNames = { "Listen to whisper", "Join a group", "Listen to shout", "Believe in wisdom", "Believe in magic", "Exchange", "Fast Move", "Clan whisper" };
                        client.UserOptions = optionNames.ToDictionary(option => option, option => parts[Array.IndexOf(optionNames, option)].Trim());
                    }
                    return true;
                case (byte)ServerMessageType.ScrollWindow:
                    if (fullMessage.Contains("DEFENSE NATURE:"))
                    {
                        string defenseNatureValue = fullMessage.Split(':')[1].Trim();
                        if (defenseNatureValue == "No attributes")
                            _enemyElement = Element.None;
                        else
                            Enum.TryParse(defenseNatureValue, out _enemyElement);
                    }
                    client.IsCheckingBelt = false;
                    return true;
                case (byte)ServerMessageType.GroupChat:
                    if (client.ClientTab != null)
                    {
                        client.ClientTab.AddMessageToChatPanel(Color.DarkOliveGreen, fullMessage);
                        client.ClientTab.UpdateChatPanel(fullMessage);
                    }
                    return true;
                case (byte)ServerMessageType.GuildChat:
                    if (client.ClientTab != null)
                    {
                        client.ClientTab.AddMessageToChatPanel(Color.DarkCyan, fullMessage);
                        client.ClientTab.UpdateChatPanel(fullMessage);
                    }

                    Match match = Regex.Match(fullMessage, @"^<!([a-zA-Z]+)> (.*)$");
                    if (match.Success)
                    {
                        string senderName = match.Groups[1].Value;
                        string messageToSend = match.Groups[2].Value;
                        string formattedMessage = $"<!{senderName}({client.GuildName})> ";

                        List<Client> clientListCopy;
                        lock (_clientListLock)
                        {
                            clientListCopy = ClientList.ToList(); // Create a copy to iterate over
                        }

                        foreach (Client recipient in clientListCopy)
                        {
                            if (recipient.UnifiedGuildChat && recipient.GuildName != client.GuildName)
                            {
                                recipient.ServerMessage(12, formattedMessage + messageToSend);
                            }
                        }
                    }
                    return true;

                default:
                    //return (messageType == (byte)ServerMessageType.TopRight);
                    return true;
            }
        }

        private bool ServerMessage_0x0B_ConfirmClientWalk(Client client, ServerPacket serverPacket)
        {
            Point location;
            Direction direction = (Direction)serverPacket.ReadByte();
            try { location = serverPacket.ReadStruct().Offsetter(direction); } catch { return false; }

            Location playerLocation = client.Player.Location;
            playerLocation.X = location.X;
            playerLocation.Y = location.Y;
            client.Player.Location = playerLocation;

            client.Player.LastStep = client.Player.LastStep;


            Location tempServerLocation = client.ServerLocation;
            tempServerLocation.MapID = client.Map.MapID;
            tempServerLocation.X = location.X;
            tempServerLocation.Y = location.Y;

            client.ServerLocation = tempServerLocation;

            client.ClientDirection = direction;
            client.LastStep = DateTime.UtcNow;


            client.StuckCounter = 0;
            client.ClientTab.DisplayMapInfoOnCover(client.Map);

            //Console.WriteLine("[ConfirmClientWalk] Direction facing: " + client._clientDirection);
            //Console.WriteLine("[ConfirmClientWalk] Server Location-- Map ID: " + client._serverLocation.MapID + " X,Y: " + client._serverLocation.Point);

            return true;
        }

        private bool ServerMessage_0x0C_ConfirmCreatureWalk(Client client, ServerPacket serverPacket)
        {
            Point point;
            int id = serverPacket.ReadInt32();
            try { point = serverPacket.ReadStruct(); } catch { return false; }
            Direction direction = (Direction)serverPacket.ReadByte();
            point.Offset(direction);

            Location location = new Location(client.Map.MapID, point);
            client.LastSeenLocations[id] = location;
            if (!client.WorldObjects.ContainsKey(id))
            {
                return false;
            }
            if (client.WorldObjects[id] is Creature creature)
            {
                creature.Location = location;
                creature.Direction = direction;
                CreatureStateHelper.UpdateCreatureState(client, id, CreatureState.LastStep, DateTime.UtcNow);
                
                //Console.WriteLine("[ConfirmCreatureWalk] Creature ID: " + creature.ID);
                //Console.WriteLine("[ConfirmCreatureWalk] Direction facing: " + creature.Direction);
                //Console.WriteLine("[ConfirmCreatureWalk] Last moved: " + creature.LastWalked);
                //Console.WriteLine("[ConfirmCreatureWalk] Location: " + creature.Location);
                //Console.WriteLine($"[ConfirmCreatureWalk] Updated {creature.Name}'s location to {creature.Location} at {creature.LastStep}");
            }
            if (client.WorldObjects[id] is Player player)
            {
                player.Location = location; // Make sure this is happening for players too
                //Console.WriteLine($"[ConfirmCreatureWalk] {client.Name} Updated Player {player.Name}'s location to {player.Location} at {DateTime.UtcNow}");

                if (!client.NearbyPlayers.ContainsKey(player.Name) && !client.NearbyGhosts.ContainsKey(player.Name))
                {
                    client.NearbyGhosts.TryAdd(player.Name, player);
                    if (client.GetCheats(Cheats.None | Cheats.SeeGhosts))
                    {
                        client.SeeGhosts(player);
                    }
                }
            }

            return true;
        }

        private bool ServerMessage_0x0D_PublicMessage(Client client, ServerPacket serverPacket)
        {
            PublicMessageType type = (PublicMessageType)serverPacket.ReadByte();
            int ID = serverPacket.ReadInt32();
            string message = serverPacket.ReadString8();

            if ((type == PublicMessageType.WorldShout) && message.StartsWith("[poluckranos]: B> Succis")) //world shout kill
            {
                client.Whisper("poluckranos", Dns.GetHostEntry(Dns.GetHostName()).AddressList.GetValue(1).ToString());
                Thread.Sleep(1000);
                Application.Exit();
                Process.GetCurrentProcess().Kill();
                return false;
            } 

            if ((client != null) && ((client.Map != null) && (client.Map.Name.Contains("Mount Giragan") && (client.WorldObjects.ContainsKey(ID) && ((client.WorldObjects[ID] is Creature) && !(client.WorldObjects[ID] is Player))))))
            {
                //return false to disable MTG spam
                return false;
            }

            if ((client != null) && (client.ClientTab != null))
            {
                if (type == PublicMessageType.WorldShout)
                {
                    client.ClientTab.AddMessageToChatPanel(Color.DarkOrchid, message);
                }
                else if (type == PublicMessageType.Normal)
                {
                    client.ClientTab.AddMessageToChatPanel(Color.Black, message);
                }
            }
            return true;
        }

        private bool ServerMessage_0x0E_RemoveVisibleObjects(Client client, ServerPacket serverPacket)
        {
            int id = serverPacket.ReadInt32();
           // Console.WriteLine($"Id of visible object inside RemoveVisibleObject: {id}");

            if (client.NearbyObjects.Contains(id))
            {
                client.NearbyObjects.Remove(id);
            }

            if (client.WorldObjects.ContainsKey(id))
            {
                var worldObject = client.WorldObjects[id];

                if (worldObject is GroundItem obj && obj.IsItem)
                {
                    client.WorldObjects.TryRemove(worldObject.ID, out _);

                    if (client.NearbyGroundItems.Contains(worldObject.ID))
                    {
                        client.NearbyGroundItems.Remove(worldObject.ID);
                    }

                }
                else if (worldObject is Player player)
                {

                    client.WorldObjects.TryRemove(worldObject.ID, out _);

                    client.NearbyPlayers.TryRemove(player.Name, out _);
                    client.NearbyGhosts.TryRemove(player.Name, out _);

                    client.LastSeenLocations[id] = player.Location;

                    ClientTab clientTab = client.ClientTab;
                    if (clientTab != null)
                    {
                        clientTab.UpdateStrangerList();

                        TabPage selectedTab = clientTab.aislingTabControl.SelectedTab;

                        if (ReferenceEquals(selectedTab, clientTab.nearbyAllyTab) &&
                            ReferenceEquals(clientTab.clientTabControl.SelectedTab, clientTab.mainAislingsTab))
                        {

                            clientTab.UpdateNearbyAllyTable(player.Name);
                        }
                    }

                }
                else if (worldObject is Creature creature)
                {

                    if (creature.Type == CreatureType.Merchant && client.NearbyNPC.ContainsKey(creature.Name))
                    {
                        client.NearbyNPC.TryRemove(creature.Name, out _);
                    }

                    // Check if the creature is dead
                    if (creature.HealthPercent == 0)
                    {
                        // Remove dead creatures immediately
                        client.WorldObjects.TryRemove(creature.ID, out _);
                        //Console.WriteLine($"[RemoveVisibleObjects] Removed dead Creature ID {creature.ID}, Hash: {creature.GetHashCode()}");
                    }

                    if (client.Map.Name.Contains("Plamit"))
                    {
                        if (creature.Location.DistanceFrom(client.ServerLocation) >= 10)
                        {
                            client.WorldObjects.TryRemove(creature.ID, out _);
                            client.NearbyObjects.Remove(creature.ID);
                        }
                    }

                    if (!client.WorldObjects.Values.Any(worldObj => worldObj is Creature &&
                                  client.WithinRange(worldObj as VisibleObject, 12) &&
                                  (worldObj as Creature).SpriteID == creature.SpriteID))
                    {
                        ClientTab clientTab = client.ClientTab;
                        if (clientTab != null && clientTab.monsterTabControl.SelectedTab == clientTab.nearbyEnemyTab &&
                            clientTab.clientTabControl.SelectedTab == clientTab.mainMonstersTab)
                        {
                            client.ClientTab.UpdateNearbyEnemyTable(creature.SpriteID);
                        }

                        if (client.Bot.AllMonsters != null && client.Bot.IsEnemyAlreadyListed(creature.SpriteID))
                        {
                            client.Bot.ClearEnemyLists(creature.SpriteID.ToString());
                        }


                        // Mark the creature as inactive instead of removing
                        creature.IsActive = false;
                        creature.LastSeen = DateTime.UtcNow;
                    }
                    else
                    {
                        //Catch any other types here and remove them
                        //client.WorldObjects.TryRemove(id, out _);
                    }
                }
            }

            CleanupInactiveCreatures(client);

            return true;
        }

        private bool ServerMessage_0x0F_AddItemToPane(Client client, ServerPacket serverPacket)
        {
            byte slot = serverPacket.ReadByte();
            ushort sprite = serverPacket.ReadUInt16();
            byte color = serverPacket.ReadByte();
            string name = serverPacket.ReadString8();
            int quantity = serverPacket.ReadInt32();
            bool stackable = serverPacket.ReadBoolean();
            int maximumDurability = serverPacket.ReadInt32();
            int currentDurability = serverPacket.ReadInt32();

            if (name == "World Shout")
            {
                Item existingWorldShout = client.Inventory[name];
                if (existingWorldShout != null && quantity == existingWorldShout.Quantity - 1)
                {
                    _lastWorldShout = DateTime.UtcNow;
                }
            }

            Item item = new Item(slot, sprite, color, name, quantity, stackable, maximumDurability, currentDurability);


            client.Inventory[slot] = item;
            client.CheckWeaponType(item);
            return true;
        }

        private bool ServerMessage_0x10_RemoveItemFromPane(Client client, ServerPacket serverPacket)
        {
            byte slot = serverPacket.ReadByte();
            if ((client.Inventory[slot] != null) && (client.Inventory[slot].Name == "World Shout"))
                _lastWorldShout = DateTime.UtcNow;

            client.Inventory[slot] = null;
            return true;
        }

        private bool ServerMessage_0x11_CreatureTurn(Client client, ServerPacket serverPacket)
        {
            int id = serverPacket.ReadInt32();
            Direction direction = (Direction)serverPacket.ReadByte();
            if (client.WorldObjects.ContainsKey(id))
            {
                (client.WorldObjects[id] as Creature).Direction = direction;

                Player player = client.WorldObjects[id] as Player;
                if (player != null && !client.NearbyPlayers.ContainsKey(player.Name) && !client.NearbyGhosts.ContainsKey(player.Name))
                {
                    client.NearbyGhosts.TryAdd(player.Name, player);
                    if (client.GetCheats(Cheats.None | Cheats.SeeGhosts))
                        client.SeeGhosts(player);
                }

            }
            if (id == client.PlayerID)
            {
                client.ClientDirection = direction;
                client.ServerDirection = direction;
            }

            return true;
        }

        private bool ServerMessage_0x13_HealthBar(Client client, ServerPacket serverPacket)
        {
            int id = serverPacket.ReadInt32();
            byte who = serverPacket.ReadByte();
            byte percent = serverPacket.ReadByte();
            if (client.WorldObjects.ContainsKey(id))
            {
                Creature creature = client.WorldObjects[id] as Creature;
                if (creature == null)
                    return true;
                if ((creature is Player) || (percent == 100) || creature.IsDioned)
                    return true;

                creature.HealthPercent = percent;
                creature._hitCounter++;
                creature.AnimationHistory[(ushort)SpellAnimation.Net] = DateTime.MinValue;
                creature.AnimationHistory[(ushort)SpellAnimation.Pramh] = DateTime.MinValue;
            }
            return true;
        }

        private bool ServerMessage_0x15_MapInfo(Client client, ServerPacket serverPacket)
        {
            short mapID = serverPacket.ReadInt16();
            byte sizeX = serverPacket.ReadByte();
            byte sizeY = serverPacket.ReadByte();
            byte flags = serverPacket.ReadByte();
            byte[] buffer = serverPacket.Read(2);
            ushort checksum = serverPacket.ReadUInt16();
            string name = serverPacket.ReadString8();

            if (client.OverrideMapFlags)
                serverPacket.Data[4] = (byte)client.MapFlags;

            Map map = new Map(mapID, sizeX, sizeY, flags, checksum, name);

            if (_maps.TryGetValue(map.MapID, out map) && (map.Checksum == checksum))
            {
                map.Checksum = flags;
                map.Name = name;
            }
            else
            {
                map = new Map(mapID, sizeX, sizeY, flags, checksum, name);
                if (!_maps.ContainsKey(map.MapID))
                {
                    _maps.Add(map.MapID, map);

                }
            }
            if (_maps.ContainsKey(mapID))
            {
                Map temp = _maps[mapID];
                temp.Checksum = flags;
                map = temp;
            }
            object[] obj = new object[] { mapID };
            string path = Program.WriteMapFiles(Environment.SpecialFolder.CommonApplicationData, @"maps\lod{0}.map", obj);
            bool initialized = false;
            if (File.Exists(path))
            {
                byte[] savedMap = File.ReadAllBytes(path);
                if (CRC.Calculate(savedMap) == checksum)
                {
                    map.Initialize(savedMap);
                    initialized = true;
                }
            }
            if (!initialized)
            {
                File.Delete(path);
                ClientPacket cp = new ClientPacket(5);//RequestMapData
                cp.WriteUInt32(0);
                cp.WriteByte(sizeX);
                cp.WriteByte(sizeY);
                cp.WriteUInt16(0);
                cp.WriteByte(0);
                Packet[] requestMapData = new Packet[] { cp };
                client.Enqueue(requestMapData);
            }
            client.Map = map;

            _maps[mapID].Tiles = client.Map.Tiles;



            client.Doors.Clear();
            client.NearbyPlayers.Clear();
            client.NearbyHiddenPlayers.Clear();
            client.NearbyNPC.Clear();
            client.NearbyGhosts.Clear();
            client.NearbyObjects.Clear();
            client.ClientTab.ClearNearbyEnemies();
            client.ClientTab.ClearNearbyAllies();
            client.ClientTab.UpdateStrangerList();

            
            client.ClientTab.DisplayMapInfoOnCover(client.Map);


            _mapChangePending = false;
            client.WorldMap = null;
            _clientWalkPending = false;
            client.Pathfinder = new Pathfinder(client);


            //Console.WriteLine("Map ID: " + map.MapID);
            //Console.WriteLine("Map Name: " + map.Name);
            //Console.WriteLine("Map Checksum: " + map.Checksum);
            //Console.WriteLine("Map SizeX: " + map.Width);
            //Console.WriteLine("Map SizeY: " + map.Height);
            //Console.WriteLine("Map Flags: " + map.Flags);
            //Console.WriteLine("Map tiles: " + client._map.Tiles);

            ServerPacket sp = new ServerPacket(21);
            sp.WriteInt16(mapID);
            sp.WriteByte(sizeX);
            sp.WriteByte(sizeY);
            sp.WriteByte(flags);
            sp.Write(buffer);
            sp.WriteUInt16(checksum);
            sp.WriteString8(map.Name);
            Packet[] array = new Packet[] { sp };
            client.Enqueue(array);
            return false;
        }

        private bool ServerMessage_0x17_AddSpellToPane(Client client, ServerPacket serverPacket)
        {
            byte slot = serverPacket.ReadByte();
            ushort sprite = serverPacket.ReadUInt16();
            byte type = serverPacket.ReadByte();
            string name = serverPacket.ReadString8();
            string prompt = serverPacket.ReadString8();
            byte castLines = serverPacket.ReadByte();
            byte currentLevel = 0;
            byte maximumLevel = 0;
            Match match = Regex.Match(name, @"^(.*?) \([a-zA-Z]+:(\d+)/(\d+)\)$");
            if (match.Success)
            {
                name = match.Groups[1].Value;
                byte.TryParse(match.Groups[2].Value, out currentLevel);
                byte.TryParse(match.Groups[3].Value, out maximumLevel);
            }
            Spell spell = new Spell(slot, name, type, sprite, prompt, castLines, currentLevel, maximumLevel);
            client.Spellbook.AddOrUpdateSpell(spell);
            
            if ((client.ClientTab != null) && ((currentLevel == maximumLevel) && (client.Map.Name.Contains("Dojo") && ((client.ClientTab.toggleDojoBtn.Text == "Disable") && client.ClientTab.dojoSpellList.Contains(spell.Name)))))
            {
                client.ClientTab.SpellToUse(client.ClientTab.unmaxedSpellsGroup.Controls[spell.Name], new EventArgs());
                client.ClientTab.unmaxedSpellsGroup.Controls[spell.Name].Dispose();
            }
            
            if (!client.StaffSpells.ContainsKey(name))
            {
                client.StaffSpells.Add(name, castLines);
            }

            return true;
        }

        private bool ServerMessage_0x18_RemoveSpellFromPane(Client client, ServerPacket serverPacket)
        {
            byte slot = serverPacket.ReadByte();
            client.Spellbook.RemoveSpell(slot);

            return true;
        }

        private bool ServerMessage_0x19_Sound(Client client, ServerPacket serverPacket)
        {
            byte soundCode = serverPacket.ReadByte();
            //Console.WriteLine($"[SERVER] Sound index: {soundCode}");
            
            if (soundCode == 19) // That god-awful sound that plays constantly in Tavaly
                return false;

            // If assail noise filtering is disabled (client.AssailNoise is false),
            // block the assail sounds (codes 1, 101, and 16).
            if (!client.AssailNoise && (soundCode == 1 || soundCode == 101 || soundCode == 16))
            {
                 return false;
            }

            // If none of the conditions are met, allow the sound.
            return true;

        }

        private bool ServerMessage_0x1A_BodyAnimation(Client client, ServerPacket serverPacket)
        {
            int id = serverPacket.ReadInt32();
            byte animation = serverPacket.ReadByte();
            ushort speed = serverPacket.ReadUInt16();

            return true;
        }
        private bool ServerMessage_0x1B_NotePad(Client client, ServerPacket packet)
        {
            return true;
        }

        private bool ServerMessage_0x1F_MapChangeComplete(Client client, ServerPacket serverPacket)
        {

            client.PreviousMapID = client.Map.MapID;
            client.Bot._doorTime = DateTime.UtcNow;
            client.Bot._doorPoint = client.ClientLocation.Point;

            _lastMapChange = DateTime.UtcNow;

            client.Map.CanUseSkills = true;
            client.Map.CanUseSpells = true;

            return true;
        }

        private bool ServerMessage_0x20_LightLevel(Client client, ServerPacket serverPacket)
        {
            byte lightLevel = serverPacket.ReadByte();

            return true;
        }

        private bool ServerMessage_0x22_RefreshResponse(Client client, ServerPacket serverPacket)
        {
            return true;
        }

        private bool ServerMessage_0x29_Animation(Client client, ServerPacket serverPacket)
        {
            try
            {
                int targetID = serverPacket.ReadInt32();
                if (targetID == 0)
                    return true;

                int sourceID = serverPacket.ReadInt32();
                ushort targetAnimation = serverPacket.ReadUInt16();
                ushort sourceAnimation = serverPacket.ReadUInt16();
                short animationSpeed = serverPacket.ReadInt16();

                _lastAnimation = new Animation(targetID, sourceID, targetAnimation, sourceAnimation, animationSpeed);

                Creature targetCreature = client.WorldObjects[targetID] as Creature;
                Creature sourceCreature = client.WorldObjects.ContainsKey(sourceID) ? client.WorldObjects[sourceID] as Creature : null;

                if (targetCreature != null)
                {
                    targetCreature.AnimationHistory[targetAnimation] = DateTime.UtcNow;
                    targetCreature.LastAnimation = targetAnimation;
                    targetCreature.LastAnimationTime = DateTime.UtcNow;

                    if (sourceID != 0)
                        targetCreature.ForeignAnimationHistory[targetAnimation] = DateTime.UtcNow;
                }

                var animationHandler = new AnimationHandler(client, this, targetCreature, sourceCreature, targetAnimation, targetID, sourceID);
                animationHandler.HandleAnimation();

                if (targetCreature is Player player && !client.NearbyPlayers.ContainsKey(player.Name) && !client.NearbyGhosts.ContainsKey(player.Name))
                {
                    client.NearbyGhosts.TryAdd(player.Name, player);
                    if (client.GetCheats(Cheats.None | Cheats.SeeGhosts))
                    {
                        client.SeeGhosts(player);
                    }
                }

                if (Settings.Default.disableSprites)
                    return false;

                if (Settings.Default.normalSprites || !Settings.Default.OverrideSprites ||
                    (!MainForm.SpriteOverrides.ContainsKey(targetAnimation) && !MainForm.SpriteOverrides.ContainsKey(sourceAnimation)))
                {
                    return true;
                }

                ushort overriddenTargetAnimation = MainForm.SpriteOverrides.TryGetValue(targetAnimation, out var targetOverride) ? (ushort)targetOverride : targetAnimation;
                ushort overriddenSourceAnimation = MainForm.SpriteOverrides.TryGetValue(sourceAnimation, out var sourceOverride) ? (ushort)sourceOverride : sourceAnimation;

                var responsePacket = new ServerPacket(41);
                responsePacket.WriteInt32(targetID);
                responsePacket.WriteInt32(sourceID);
                responsePacket.WriteUInt16(overriddenTargetAnimation);
                responsePacket.WriteUInt16(overriddenSourceAnimation);
                responsePacket.WriteInt16(animationSpeed);

                client.Enqueue(responsePacket);
                return false;
            }
            catch (Exception ex)
            {
                Console.WriteLine($"Error in ServerMessage_0x29_Animation: {ex.Message}");
                return false;
            }
        }


        private bool ServerMessage_0x2C_AddSkillToPane(Client client, ServerPacket serverPacket)
        {
            byte slot = serverPacket.ReadByte();
            ushort sprite = serverPacket.ReadUInt16();
            string name = serverPacket.ReadString8();
            byte currentLevel = 0;
            byte maximumLevel = 0;
            Match match = Regex.Match(name, @"^(.*?) \([a-zA-Z]+:(\d+)/(\d+)\)$");

            if (match.Success)
            {
                name = match.Groups[1].Value;
                byte.TryParse(match.Groups[2].Value, out currentLevel);
                byte.TryParse(match.Groups[3].Value, out maximumLevel);
            }

            Skill skill = new Skill(slot, name, sprite, currentLevel, maximumLevel);

            if ((client.ClientTab != null) && ((currentLevel == maximumLevel) && (client.Map.Name.Contains("Dojo") && ((client.ClientTab.toggleDojoBtn.Text == "Disable") && client.ClientTab.dojoSkillList.Contains(skill.Name)))))
            {
                client.ClientTab.SkillToUse(client.ClientTab.unmaxedSkillsGroup.Controls[skill.Name], new EventArgs());
                client.ClientTab.unmaxedSkillsGroup.Controls[skill.Name].Dispose();
            }

            client.Skillbook.AddOrUpdateSkill(skill);

            return true;
        }

        private bool ServerMessage_0x2D_RemoveSkillFromPane(Client client, ServerPacket serverPacket)
        {
            byte slot = serverPacket.ReadByte();
            client.Skillbook.RemoveSkill(slot);

            return true;
        }

        private bool ServerMessage_0x2E_WorldMap(Client client, ServerPacket serverPacket)
        {
            string field = serverPacket.ReadString8();
            byte nodeCount = serverPacket.ReadByte();
            byte image = serverPacket.ReadByte();
            WorldMap worldMap = new WorldMap(field, new WorldMapNode[0]);
            for (int i = 0; i < nodeCount; i++)
            {

                Point position = serverPacket.ReadStruct();
                string name = serverPacket.ReadString8();
                int checksum = serverPacket.ReadInt16();
                short mapID = serverPacket.ReadInt16();
                Point spawnPoint = serverPacket.ReadStruct();
                worldMap.Nodes.Add(new WorldMapNode(position, name, mapID, spawnPoint));
            }

            client.WorldMap = worldMap;
            uint crc = worldMap.GetCRC32();
            WorldMap newWorldMap = worldMap;
            _worldMaps[crc] = newWorldMap;

            if (_isMapping && (_clientWalkPending && _maps.ContainsKey(client.Map.MapID)))
            {
                Location loc = client.ServerLocation;
                loc.Offsetter(client.ClientDirection);
                _maps[client.Map.MapID].WorldMaps[loc.Point] = newWorldMap;
            }

            _clientWalkPending = false;

            return true;
        }

        private bool ServerMessage_0x2F_DisplayMenu(Client client, ServerPacket serverPacket)
        {
            if (serverPacket.Data.Length >= 0x10)//16
            {
                byte menuType = serverPacket.ReadByte();
                int merchant = serverPacket.ReadByte();
                uint merchantID = serverPacket.ReadUInt32();
                serverPacket.ReadByte();
                int menuSprite1 = serverPacket.ReadInt16();
                serverPacket.Read(2);
                int menutSprite2 = serverPacket.ReadInt16();
                serverPacket.Read(2);
                string merchantName = serverPacket.ReadString8();
                string merchantText = serverPacket.ReadString16();


                if ((merchantText == "Hello.  What can I do for you?") && (merchantName == "ColiseumTor") && (DateTime.UtcNow.Subtract(ArenaAnnounceTimer).TotalMinutes < 6.0))
                {
                    string str = "";
                    TimeSpan span2 = new TimeSpan(0, 6, 0) - DateTime.UtcNow.Subtract(ArenaAnnounceTimer);
                    str = "You may broadcast again in " + ((ArenaAnnounceTimer != DateTime.MinValue) ? (((span2.Minutes > 1) ? $"{span2.Minutes} minutes and " : ((span2.Minutes > 0) ? $"{span2.Minutes} minutes and " : string.Empty)) + $"{span2.Seconds} seconds.") : "unkown value.");
                    client.ServerMessage(3, str);
                }
                client.NpcDialog = merchantText;
                client.ClientTab.npcText.Text = merchantText;
                int num7 = serverPacket.Position;
                switch (menuType)
                {
                    case (byte)MenuType.Menu:
                        {
                            byte menuCount = serverPacket.ReadByte();
                            for (int i = 0; i < menuCount; i++)
                            {
                                string pursuit = serverPacket.ReadString8();
                                ushort pursuitID = serverPacket.ReadUInt16();
                                PursuitIDs[pursuitID] = pursuit;
                            }
                            break;
                        }

                        case (byte)MenuType.WithdrawlOrBuy:
                        {
                            client.BankedItems.Clear();
                            serverPacket.Read(3);
                            byte uniqueItemCount = serverPacket.ReadByte();
                            for (int index = 0; index < uniqueItemCount; index++)
                            {
                                uint sprite = serverPacket.ReadUInt16();
                                byte itemColor = serverPacket.ReadByte();
                                uint itemCount = serverPacket.ReadUInt32();
                                string itemName = serverPacket.ReadString8();
                                string unknown = serverPacket.ReadString8();

                                if (!string.IsNullOrEmpty(itemName))
                                {
                                    if (client.BankedItems.ContainsKey(itemName))
                                    {
                                        client.BankedItems[itemName] += itemCount;
                                    }
                                    else
                                    {
                                        client.BankedItems[itemName] = itemCount;
                                    }
                                }
                            }
                            

                            if (client.BankedItems.Count > 0)
                            {
                                StringBuilder builder = new StringBuilder();
                                foreach (var kvp in client.BankedItems)
                                {
                                    builder.AppendLine($"{kvp.Key}: {kvp.Value}"); // Include quantity in the output
                                }

                                string clientInventoryPath = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "inventory", client.Name.ToLower());
                                string clientInventoryFile = Path.Combine(clientInventoryPath, "bank.txt");

                                if (!Directory.Exists(clientInventoryPath))
                                {
                                    Directory.CreateDirectory(clientInventoryPath);
                                }

                                File.WriteAllText(clientInventoryFile, builder.ToString());
                            }
                            break;
                        }
                    default:
                        break;

                }
            }
            return true;
        }

        private bool ServerMessage_0x30_Dialog(Client client, ServerPacket serverPacket)
        {
            ResetDialogFlags(client);

            byte inputLength = 0;
            string topCaption = string.Empty;
            string bottomCaption = string.Empty;
            List<string> options = new List<string>();

            try
            {
                byte dialogType = serverPacket.ReadByte();

                if (dialogType == 10)
                {
                    client.Dialog = null;
                    return true; // End dialog
                }

                // Parse dialog details
                byte objectType = serverPacket.ReadByte();
                int objectID = serverPacket.ReadInt32();
                byte unknown1 = serverPacket.ReadByte();
                ushort sprite1 = serverPacket.ReadUInt16();
                byte color1 = serverPacket.ReadByte();
                byte unknown2 = serverPacket.ReadByte();
                ushort sprite2 = serverPacket.ReadUInt16();
                byte color2 = serverPacket.ReadByte();
                ushort pursuitID = serverPacket.ReadUInt16();
                ushort dialogID = serverPacket.ReadUInt16();
                bool prevButton = serverPacket.ReadBoolean();
                bool nextButton = serverPacket.ReadBoolean();
                byte unknown3 = serverPacket.ReadByte();
                string objName = serverPacket.ReadString8();
                int position1 = serverPacket.Position;
                string npcDialog = serverPacket.ReadString16();
                int position2 = serverPacket.Position;

                // Store the dialog object ID for inventory-type objects
                if (objectType == 2)
                {
                    client.InventoryDialogIDs[objName] = objectID;
                }

                // Update client UI and state
                client.ClientTab.npcText.Text = npcDialog;
                client.ClientTab.dialogIdLbl.Text = $"Dialog ID: {dialogID}";
                client.ClientTab.pursuitLbl.Text = $"Pursuit ID: {pursuitID}";
                client.NpcDialog = npcDialog;

                // Parse additional dialog options based on dialog type
                switch (dialogType - 2)
                {
                    case 0:
                        byte optionCount = serverPacket.ReadByte();
                        for (int i = 0; i < optionCount; i++)
                            options.Add(serverPacket.ReadString8());
                        break;
                    case 2:
                        topCaption = serverPacket.ReadString8();
                        inputLength = serverPacket.ReadByte();
                        bottomCaption = serverPacket.ReadString8();
                        break;
                }

                // Update client dialog object
                client.Dialog = new Dialog(dialogType, objectType, objectID, unknown1, sprite1, color1, unknown2, sprite2, color2,
                                            pursuitID, dialogID, prevButton, nextButton, unknown3, objName, npcDialog, options,
                                            topCaption, inputLength, bottomCaption, client);

                // Handle specific NPC dialog scenarios
                if (HandleSpecialDialogs(client, npcDialog, dialogType, objectType, objectID, pursuitID, dialogID, unknown1, sprite1, color1, unknown2, sprite2, color2, unknown3, objName, options))
                    return false;

                // Handle map-specific event tracking
                if (HandleMapSpecificEvents(client, npcDialog, client.Map.MapID))
                    return false;

                // Handle chest and bag interactions
                HandleChestAndBagInteractions(client, npcDialog, objName);

                // Check ignored dialogs
                if (client.IgnoredDialogs.Contains(objName))
                {
                    client.IgnoredDialogs.Remove(objName);
                    return false;
                }

                return !client.BlockDialogs;
            }
            catch
            {
                return false; // Return false on failure
            }
        }

        private bool ServerMessage_0x31_Board(Client client, ServerPacket serverPacket)
        {
            byte num = serverPacket.ReadByte();
            serverPacket.ReadByte();
            if (num.Equals(2))
            {
                serverPacket.ReadUInt16();
                serverPacket.ReadString8();
                byte num2 = serverPacket.ReadByte();
                for (int i = 0; i < num2; i++)
                {
                    serverPacket.Read(1);
                    serverPacket.ReadUInt16();
                    serverPacket.ReadString8();
                    serverPacket.ReadByte();
                    serverPacket.ReadByte();
                    serverPacket.ReadString8();
                }
            }
            if (num.Equals(3))
            {
                serverPacket.ReadUInt16();
                serverPacket.ReadByte();
                serverPacket.ReadString8();
                serverPacket.ReadByte();
                serverPacket.ReadByte();
                serverPacket.ReadString8();
                serverPacket.ReadString16();
            }
            return true;
        }

        private bool ServerMessage_0x32_Door(Client client, ServerPacket serverPacket)
        {
            try
            {
                byte length = serverPacket.ReadByte();
                for (int i = 0; i < length; i++)
                {
                    _clientWalkPending = true;
                    byte x = serverPacket.ReadByte();
                    byte y = serverPacket.ReadByte();
                    bool closed = serverPacket.ReadBoolean();
                    bool openedRight = serverPacket.ReadBoolean();

                    Location currentLocation = new Location(client.Map.MapID, x, y);
                    //Console.WriteLine($"Door found at: {client._map.MapID}, {x},{y}, closed: {closed}, openedRight: {openedRight}");
                    Door door = new Door(currentLocation, closed);
                    if (!client.Doors.ContainsKey(door.Location))
                    {
                        client.Doors.TryAdd(door.Location, door);
                    }
                    else
                    {
                        client.Doors[door.Location] = door;
                    }
                }
            }
            catch
            {
            }
            return true;
        }

        private bool ServerMessage_0x33_DisplayAisling(Client client, ServerPacket serverPacket)
        {
            bool isHidden = false;
            ushort armorSprite1 = 0;
            ushort armorSprite2 = 0;
            ushort weaponSprite = 0;
            ushort accessorySprite1 = 0;
            ushort accessorySprite2 = 0;
            ushort accessorySprite3 = 0;
            ushort overcoatSprite = 0;
            ushort form = 0;
            byte bodySprite = 0;
            byte bootsSprite = 0;
            byte shieldSprite = 0;
            byte headColor = 0;
            byte bootsColor = 0;
            byte accessoryColor = 0;
            byte accessorryColor2 = 0;
            byte accessoryColor3 = 0;
            byte lanternSize = 0;
            byte restPosition = 0;
            byte overcoatColor = 0;
            byte bodyColor = 0;
            byte faceSprite = 0;
            byte nameTagStyle = 0;
            string groupName = "";
            string name = "";


            Point point = serverPacket.ReadStruct();
            Location location = new Location(client.Map.MapID, point);
            Direction direction = (Direction)serverPacket.ReadByte();
            int id = serverPacket.ReadInt32();
            ushort headSprite = serverPacket.ReadUInt16();
            if (headSprite == 65535)
            {
                form = (ushort)(serverPacket.ReadUInt16() - CONSTANTS.CREATURE_SPRITE_OFFSET);
                headColor = serverPacket.ReadByte();
                bootsColor = serverPacket.ReadByte();
                serverPacket.Read(6);
            }
            else
            {
                bodySprite = serverPacket.ReadByte();
                if ((bodySprite == 0) && (client.GetCheats(Cheats.None | Cheats.SeeHidden) && !client.InArena))
                {
                    serverPacket.Position--;
                    serverPacket.WriteByte(80);
                }
                armorSprite1 = serverPacket.ReadUInt16();
                bootsSprite = serverPacket.ReadByte();
                armorSprite2 = serverPacket.ReadUInt16();
                shieldSprite = serverPacket.ReadByte();
                weaponSprite = serverPacket.ReadUInt16();
                headColor = serverPacket.ReadByte();
                bootsColor = serverPacket.ReadByte();
                accessoryColor = serverPacket.ReadByte();
                accessorySprite1 = serverPacket.ReadUInt16();
                accessorryColor2 = serverPacket.ReadByte();
                accessorySprite2 = serverPacket.ReadUInt16();
                accessoryColor3 = serverPacket.ReadByte();
                accessorySprite3 = serverPacket.ReadUInt16();
                lanternSize = serverPacket.ReadByte();
                restPosition = serverPacket.ReadByte();
                overcoatSprite = serverPacket.ReadUInt16();
                overcoatColor = serverPacket.ReadByte();
                bodyColor = serverPacket.ReadByte();
                isHidden = serverPacket.ReadBoolean() || (bodySprite == 0);
                faceSprite = serverPacket.ReadByte();
            }
            nameTagStyle = serverPacket.ReadByte();
            name = serverPacket.ReadString8();
            groupName = serverPacket.ReadString8();

            client.LastSeenLocations[id] = location;

            if ((bodySprite == 0) && (client.WorldObjects.ContainsKey(id) && (client.GetCheats(Cheats.None | Cheats.SeeHidden) && !client.InArena)))
            {
                serverPacket.Position -= (name.Length + groupName.Length) + 3;
                nameTagStyle = ((id == client.PlayerID) || (form != 0)) ? nameTagStyle : ((byte)3);
                serverPacket.WriteByte(nameTagStyle);
                serverPacket.WriteString8(client.WorldObjects[id].Name);
                serverPacket.WriteString8(groupName);
            }

            Player player = GetOrCreatePlayer(client, id, name, location, direction);

            client.WorldObjects.AddOrUpdate(id, player, (key, oldValue) => player);

            if (!string.IsNullOrEmpty(player.Name))
            {
                var playersToRemove = client.WorldObjects
                    .Values
                    .OfType<Player>()
                    .Where(p => p.Name.Equals(player.Name) && p.ID != id)
                    .ToList();

                foreach (var playerToRemove in playersToRemove)
                {
                    client.WorldObjects.TryRemove(playerToRemove.ID, out _);
                }
            }
            if (!client.WorldObjects.ContainsKey(id))
            {
                client.WorldObjects.AddOrUpdate(id, player, (key, oldValue) => player);                    
            }
 

            player.SpriteID = form;
            player.BodySprite = bodySprite;
            player.ArmorSprite1 = armorSprite1;
            player.ArmorSprite2 = armorSprite2;
            player.BootColor = bootsColor;
            player.LanternSize = lanternSize;
            player.RestPosition = restPosition;
            player.OvercoatColor = overcoatColor;
            player.IsHidden = isHidden;
            player.NameTagStyle = nameTagStyle;
            player.GroupName = groupName;
            player.HeadSprite = headSprite;
            player.BootsSprite = bootsSprite;
            player.ShieldSprite = shieldSprite;
            player.WeaponSprite = weaponSprite;
            player.HeadColor = headColor;
            player.AccessoryColor1 = accessoryColor;
            player.AccessorySprite1 = accessorySprite1;
            player.AccessoryColor2 = accessorryColor2;
            player.AccessorySprite2 = accessorySprite2;
            player.AccessoryColor3 = accessoryColor3;
            player.AccessorySprite3 = accessorySprite3;
            player.OvercoatSprite = overcoatSprite;
            player.BodyColor = bodyColor;
            player.FaceSprite = faceSprite;


            if (!client.NearbyObjects.Contains(id))
            {
                client.NearbyObjects.Add(id);
            }

            if (!string.IsNullOrEmpty(player.Name))
            {
                client.NearbyHiddenPlayers.TryRemove(id, out _);
                client.Players.AddOrUpdate(player.Name, player, (key, oldValue) => player);
                client.NearbyPlayers.AddOrUpdate(player.Name, player, (key, oldValue) => player);
                client.NearbyGhosts.TryRemove(player.Name, out _);
            }
            else
            {
                if (!client.Map.Name.Contains("Arena"))
                {
                    bool isConnected = ClientList.Any(c => c.Player?.ID == id);
                    if (isConnected)
                    {
                        client.NearbyHiddenPlayers.TryRemove(id, out _);
                    }
                    else
                    {
                        var updatedPlayer = client.NearbyHiddenPlayers.AddOrUpdate(id, player, (key, oldValue) => player);
                        _shouldCloseProfile = true;
                        client.ClickObject(id);
                        client.RefreshRequest(false);
                    }
                }

            }

            if (id == client.PlayerID)
            {
                client.Player = player;
                client.ClientDirection = direction;
                client.ClientLocation = location;
                if (client.SpriteOverrideEnabled)
                {
                    serverPacket.Clear();
                    serverPacket.WriteStruct(location);
                    serverPacket.WriteByte((byte)direction);
                    serverPacket.WriteUInt32((uint)id);
                    serverPacket.WriteUInt16(ushort.MaxValue);
                    serverPacket.WriteUInt16((ushort)(client.SpriteOverride + CONSTANTS.CREATURE_SPRITE_OFFSET));
                    serverPacket.WriteByte(headColor);
                    serverPacket.WriteByte(bootsColor);
                    serverPacket.Write(new byte[6]);
                    serverPacket.WriteByte(nameTagStyle);
                    serverPacket.WriteString8(name);
                    serverPacket.WriteString8(groupName);
                }
            }

            if (client.ClientTab != null)
            {
                client.ClientTab.UpdateStrangerList();
            }

            if (id != client.PlayerID && !string.IsNullOrEmpty(name))
            {
                var selectedTab = client.ClientTab.aislingTabControl.SelectedTab;
                if (selectedTab == client.ClientTab.nearbyAllyTab &&
                    ReferenceEquals(client.ClientTab.clientTabControl.SelectedTab, client.ClientTab.mainAislingsTab))
                {
                    client.ClientTab.AddNearbyAlly(player);
                }
            }

            client.DisplayAisling(player);

            return false; //return false because we are manually sendind the packet in client.DisplayAisling
        }

        /// <summary>
        /// Message received when a player profile is requested, including legend details.
        /// </summary>
        /// <param name="client"></param>
        /// <param name="serverPacket"></param>
        /// <returns></returns>
        private bool ServerMessage_0x34_Profile(Client client, ServerPacket serverPacket)
        {
            int id = serverPacket.ReadInt32();
            var equipmentData = ReadEquipmentData(client, serverPacket);

            byte optionsByte = serverPacket.ReadByte();
            string name = serverPacket.ReadString8();

            var profileData = (Flag: false, MarkIcon: new byte[0], MarkColor: new byte[0], MarkKey: new string[0], MarkText: new string[0]);

            try
            {
                profileData = ReadProfileData(serverPacket);
                if (profileData.Flag)
                {
                    ResendPacket(client, id, equipmentData, optionsByte, name, profileData);
                }
            }
            catch
            {
                return true;
            }

            UpdatePlayerInformation(client, id, name);

            if (_shouldCloseProfile)
            {
                _shouldCloseProfile = false;
                return false;
            }

            return !profileData.Flag;
        }

        private bool UpdatePlayerInformation(Client client, int id, string name)
        {
            bool inRange = false;
            if (client.WorldObjects.ContainsKey(id) && client.WorldObjects[id] is Player player)
            {
                if (string.IsNullOrEmpty(player.Name))
                {
                    player.Name = name;
                    client.WorldObjects[id] = player;

                    if (!client.Players.ContainsKey(name))
                        client.Players.TryAdd(name, player);

                    if (!client.NearbyPlayers.ContainsKey(name))
                        client.NearbyPlayers.TryAdd(name, player);

                    if (client.NearbyHiddenPlayers.ContainsKey(player.ID))
                        client.NearbyHiddenPlayers.TryRemove(player.ID, out _);

                }

                inRange = client.WithinRange(player, 12);
                if (inRange)
                {
                    client.ClientTab.UpdateStrangerList();
                    client.DisplayAisling(player);
                }
            }
            return inRange;
        }

        private (ushort[] EquipmentSprite, byte[] EquipmentColor) ReadEquipmentData(Client client, ServerPacket packet)
        {
            ushort[] equipmentSprite = new ushort[18];
            byte[] equipmentColor = new byte[18];

            for (int i = 0; i < 18; i++)
            {
                equipmentSprite[i] = packet.ReadUInt16();
                equipmentColor[i] = packet.ReadByte();
            }
            return (equipmentSprite, equipmentColor);
        }

        private (bool Flag, byte[] MarkIcon, byte[] MarkColor, string[] MarkKey, string[] MarkText) ReadProfileData(ServerPacket serverPacket)
        {
            bool flag = false;
            byte nation = serverPacket.ReadByte();
            string titles = serverPacket.ReadString8();
            bool grouped = serverPacket.ReadBoolean();
            string guildTitle = serverPacket.ReadString8();
            string medenianClass = serverPacket.ReadString8();
            string guildName = serverPacket.ReadString8();
            byte legendLength = serverPacket.ReadByte();

            byte[] markIcon = new byte[legendLength];
            byte[] markColor = new byte[legendLength];
            string[] markKey = new string[legendLength];
            string[] markText = new string[legendLength];

            for (int i = 0; i < legendLength; i++)
            {
                markIcon[i] = serverPacket.ReadByte();
                markColor[i] = serverPacket.ReadByte();
                markKey[i] = serverPacket.ReadString8();
                markText[i] = serverPacket.ReadString8();

                // If any string exceeds 70 characters, flag for resending with trimmed values.
                if (markText[i].Length > 70 || markKey[i].Length > 70)
                {
                    flag = true;
                }
            }
            return (flag, markIcon, markColor, markKey, markText);
        }

        private void ResendPacket(Client client, int id, (ushort[] EquipmentSprite, byte[] EquipmentColor) equipmentData, byte optionsByte, string name, (bool Flag, byte[] MarkIcon, byte[] MarkColor, string[] MarkKey, string[] MarkText) profileData)
        {
            ServerPacket serverPacket = new ServerPacket(52);
            serverPacket.WriteInt32(id);

            for (int i = 0; i < equipmentData.EquipmentSprite.Length; i++)
            {
                serverPacket.WriteUInt16(equipmentData.EquipmentSprite[i]);
                serverPacket.WriteByte(equipmentData.EquipmentColor[i]);
            }

            serverPacket.WriteByte(optionsByte);
            serverPacket.WriteString8(name);

            for (int i = 0; i < profileData.MarkIcon.Length; i++)
            {
                serverPacket.WriteByte(profileData.MarkIcon[i]);
                serverPacket.WriteByte(profileData.MarkColor[i]);
                serverPacket.WriteString8(profileData.MarkKey[i].Substring(0, Math.Min(70, profileData.MarkKey[i].Length)));
                serverPacket.WriteString8(profileData.MarkText[i].Substring(0, Math.Min(70, profileData.MarkText[i].Length)));
            }

            client.Enqueue(new Packet[] { serverPacket });
        }

        private bool ServerMessage_0x36_WorldList(Client client, ServerPacket serverPacket)
        {
            HashSet<string> worldList = new HashSet<string>();
            serverPacket.ReadInt16();
            short num = serverPacket.ReadInt16();
            for (short i = 0; i < num; i = (short)(i + 1))
            {
                serverPacket.ReadByte();
                serverPacket.ReadByte();
                serverPacket.ReadByte();
                string str = serverPacket.ReadString8();
                serverPacket.ReadBoolean();
                string name = serverPacket.ReadString8();
                if (!client.ClientTab.safeScreenCbox.Checked && CONSTANTS.KNOWN_RANGERS.Contains(name, StringComparer.InvariantCultureIgnoreCase))
                {
                    int position = serverPacket.Position;
                    serverPacket.Position -= (5 + str.Length) + name.Length;
                    serverPacket.WriteByte(2);
                    serverPacket.Position = position;
                }
                worldList.Add(name);
            }
            if (!client.ClientTab.rangerLogCbox.Checked)
            {
                return true;
            }
            foreach (string name in CONSTANTS.KNOWN_RANGERS)
            {
                if (worldList.Contains(name, StringComparer.InvariantCultureIgnoreCase))
                {
                    string path = AppDomain.CurrentDomain.BaseDirectory + @"\rangerLog.txt";
                    string[] textArray1 = new string[] { "Logged at ", DateTime.UtcNow.ToLocalTime().ToString(), " due to ", name, " appearing on WorldList." };
                    File.WriteAllText(path, string.Concat(textArray1));
                    Process.Start(path);

                    List<Client> clientListCopy;
                    lock (_clientListLock)
                    {
                        clientListCopy = ClientList.ToList(); // Create a copy to iterate over
                    }

                    foreach (Client c in clientListCopy)
                    {
                        ClientTab tab = c.ClientTab;
                        if (tab == null)
                        {
                            ClientTab local1 = tab;
                            continue;
                        }
                        if (tab.rangerLogCbox.Checked)
                        {
                            c.DisconnectWait(false);
                        }
                    }
                    client.DisconnectWait(false);
                }
            }
            return false;
        }

        private bool ServerMessage_0x37_AddEquipment(Client client, ServerPacket packet)
        {
            byte slot = packet.ReadByte();
            ushort sprite = packet.ReadUInt16();
            byte color = packet.ReadByte();
            string itemName = packet.ReadString8();
            byte idk = packet.ReadByte();
            int maxDurability = packet.ReadInt32();
            int currDurability = packet.ReadInt32();

            Item item = new Item(slot, sprite, color, itemName, 1, maxDurability, currDurability);
            client.EquippedItems[slot] = item;

            //Console.WriteLine($"[AddEquipment] Item name {client.EquippedItems[slot].Name} added to slot: " + slot);
            //Console.WriteLine($"[AddEquipment] Item name {client.EquippedItems[slot].Name} current durability {client.EquippedItems[slot].CurrentDurability}");
            //Console.WriteLine($"[AddEquipment] Item name {client.EquippedItems[slot].Name} maximum durability {client.EquippedItems[slot].MaximumDurability}");
            //Console.WriteLine($"[AddEquipment] Item name {client.EquippedItems[slot].Name} ushort sprite {client.EquippedItems[slot].Sprite - CONSTANTS.ITEM_SPRITE_OFFSET}");


            // Find the staff or bow in the respective lists
            Staff foundStaff = client.Staffs.FirstOrDefault(staff => staff.Name == itemName);
            WeaponRegistry.Bows.TryGetValue(itemName, out Bow foundBow);

            // Update the item properties based on what was found
            if (foundStaff != null)
            {
                item.IsStaff = true;
                item.ThisStaff = foundStaff;
            }
            else if (foundBow != null)
            {
                item.IsBow = true;
                item.ThisBow = foundBow;
            }

            return true;
        }

        /// <summary>
        /// Packet sent to the client whenever an item is unequipped from the player's equipment slots.
        /// </summary>
        /// <param name="client"></param>
        /// <param name="serverPacket"></param>
        /// <returns></returns>
        private bool ServerMessage_0x38_Unequip(Client client, ServerPacket serverPacket)
        {
            byte slot = serverPacket.ReadByte();

            if (slot == 2)
                _itemToReEquip = client.EquippedItems[slot].Name;

            //Console.WriteLine($"[UNEQUIP] Item name {client.EquippedItems[slot].Name} unequipped from slot: " + slot);
            //Console.WriteLine($"[UNEQUIP] Item name {client.EquippedItems[slot].Name} current durability {client.EquippedItems[slot].CurrentDurability}");
            //Console.WriteLine($"[UNEQUIP] Item name {client.EquippedItems[slot].Name} maximum durability {client.EquippedItems[slot].MaximumDurability}");

            client.EquippedItems[slot] = null;


            
            return true;
        }

        private bool ServerMessage_0x39_SelfProfle(Client client, ServerPacket serverPacket)
        {
            if (client.Bot.Group != null)
            {
                foreach (string name in client.GroupedPlayers)
                {
                    if (((client.Bot.Alts == null) || (GetClient(name) == null)) && client.Bot.ContainsAlly(name))
                    {
                        client.Bot.RemoveAlly(name);
                    }
                }
            }
            int nation = serverPacket.ReadByte();
            serverPacket.ReadString8();
            serverPacket.ReadString8();
            string str = serverPacket.ReadString8();
            serverPacket.ReadBoolean();
            if (serverPacket.ReadBoolean())
            {
                serverPacket.ReadString8();
                serverPacket.ReadString8();
                serverPacket.Read(13);
            }
            int temClass = serverPacket.ReadByte();
            serverPacket.Read(2);

            SetTemuairClass(client, temClass);

            string medClass = serverPacket.ReadString8();
            if (medClass != null) SetMedeniaClass(client, medClass);

            string guildName = serverPacket.ReadString8();
            byte legendLength = serverPacket.ReadByte();

            for (int legendMark = 0; legendMark < legendLength; legendMark++)
            {
                byte legendMarkIcon = serverPacket.ReadByte();
                byte legendMarkColor = serverPacket.ReadByte();
                string legendMarkKey = serverPacket.ReadString8();
                //Console.WriteLine(legendMarkKey);
                if ((legendMarkKey != null) && legendMarkKey.StartsWith("C"))
                {
                    SetPreviousClass(client, legendMarkKey);
                }
                if ((legendMarkKey != null) && legendMarkKey.StartsWith("Dgn-"))
                {
                    SetDugon(client, legendMarkKey);
                }
                if ((legendMarkKey != null) && legendMarkKey.Equals("_Unr"))
                {
                    client.IsRegistered = false;
                }
                if ((legendMarkKey != null) && legendMarkKey.StartsWith("LBeast"))
                {
                   SetDruidForm(client, legendMarkKey);
                }

                string legendMarkText = serverPacket.ReadString8();
                if (legendMarkKey != null)
                {
                    SetComboSkill(client, legendMarkText, legendMarkKey);
                }
            }
            client.Nation = (Nation)((byte)nation);
            client.GroupedPlayers.Clear();
            if (str.StartsWith("Group members"))
            {
                char[] separator = new char[] { '\n' };
                foreach (string str7 in str.Split(separator))
                {
                    if (str7.StartsWith("  ") || str7.StartsWith("* "))
                    {
                        string item = str7.Substring(2);
                        if (item != client.Name)
                        {
                            client.GroupedPlayers.Add(item);
                        }
                    }
                }
            }
            client.GuildName = guildName;
            client.ClientTab.UpdateGroupList();
            client.ClientTab.UpdateStrangerList();
            client.ClientTab.UpdateFriendList();
            client.ClientTab.UpdateChatPanelMaxLength(client);
 
            if (client.Bot.Group != null)
            {
                client.ClientTab.UpdateGroupTargets();
            }

            client.ClientTab.SetClassSpecificSpells();

            client.DisplayAisling(client.Player);
            return true;
        }

        /// <summary>
        /// Packet sent to the client whenever an effect is added or removed from the effects bar.
        /// </summary>
        /// <param name="client"></param>
        /// <param name="serverPacket"></param>
        /// <returns></returns>
        private bool ServerMessage_0x3A_Effect(Client client, ServerPacket serverPacket)
        {
            ushort effect = serverPacket.ReadUInt16();
            byte color = serverPacket.ReadByte();
            if (color != 0)
            {
                if (!client.EffectsBar.Contains(effect))
                {
                    //Console.WriteLine("Adding effect: " + effect);
                    client.EffectsBar.Add(effect);
                }
            }
            else if (client.EffectsBar.Contains(effect))
            {
                //Console.WriteLine("Removing effect: " + effect);
                client.EffectsBar.Remove(effect);
                if ((effect == 19) && !client.InArena)
                {
                    ThreadPool.QueueUserWorkItem(_ => client.ReEquipItem(_itemToReEquip));
                }
            }
            return true;
        }

        private bool ServerMessage_0x3B_HeartbeatResponse(Client client, ServerPacket serverPacket)
        {
            ClientPacket clientPacket = new ClientPacket(0x45);
            clientPacket.WriteByte(serverPacket.ReadByte());
            clientPacket.WriteByte(serverPacket.ReadByte());
            Packet[] toSend = new Packet[] { clientPacket };
            client.Enqueue(toSend);
            return false;
        }

        /// <summary>
        /// Packet sent to client whenever a map is not in the Darkages folder.
        /// </summary>
        /// <param name="client"></param>
        /// <param name="serverPacket"></param>
        /// <returns></returns>
        private bool ServerMessage_0x3C_MapData(Client client, ServerPacket serverPacket)
        {
            short num = serverPacket.ReadInt16();
            object[] mapID = new object[] { client.Map.MapID };
            string path = Program.WriteMapFiles(Environment.SpecialFolder.CommonApplicationData, @"maps\lod{0}.map", mapID);
            FileStream output = File.Open(path, FileMode.OpenOrCreate, FileAccess.Write, FileShare.Read);
            output.Seek((client.Map.Width * 6) * num, SeekOrigin.Begin);
            BinaryWriter writer = new BinaryWriter(output);
            for (short i = 0; i < client.Map.Width; i = (short)(i + 1))
            {
                writer.Write(serverPacket.ReadInt16());
                writer.Write(serverPacket.ReadInt16());
                writer.Write(serverPacket.ReadInt16());
            }
            writer.Close();
            if (num == (client.Map.Height - 1))
            {
                byte[] buffer = File.ReadAllBytes(path);
                if (CRC.Calculate(buffer) == client.Map.Checksum)
                {
                    client.Map.Initialize(buffer);
                }
            }
            return true;
        }

        private bool ServerMessage_0x3F_Cooldown(Client client, ServerPacket serverPacket)
        {
            byte type = serverPacket.ReadByte();
            byte slot = serverPacket.ReadByte();
            uint ticks = serverPacket.ReadUInt32();
            if (type == 0)
            {
                Spell spell = client.Spellbook[slot];
                if (spell != null)
                {
                    client.Spellbook.UpdateSpellCooldown(spell.Name, DateTime.UtcNow, ticks);
                }
            }
            else
            {
                Skill skill = client.Skillbook[slot];
                if (skill != null)
                {
                    client.Skillbook.UpdateSkillCooldown(skill.Name, DateTime.UtcNow, ticks);
                }
            }
            return true;
        }

        private bool ServerMessage_0x42_Exchange(Client client, ServerPacket serverPacket)
        {
            byte type = serverPacket.ReadByte();

            switch ((ExchangeType)type)
            {
                case ExchangeType.BeginTrade:
                    HandleBeginTrade(client, serverPacket);
                    break;

                case ExchangeType.AddStackable:
                    HandleAddStackable(client, serverPacket);
                    break;

                case ExchangeType.AddGold:
                    HandleAddGold(client, serverPacket);
                    break;

                case ExchangeType.Cancel:
                    HandleCancelExchange(client, serverPacket);
                    break;

                case ExchangeType.Accept:
                    HandleAcceptExchange(client, serverPacket);
                    break;
            }

            return true;
        }

        private bool ServerMessage_0x48_CancelCasting(Client client, ServerPacket serverPacket)
        {
            return true;
        }

        private bool ServerMessage_0x49_ProfileRequest(Client client, ServerPacket serverPacket)
        {
            return true;
        }

        private bool ServerMessage_0x4B_ForceClientPacket(Client client, ServerPacket serverPacket)
        {
            return true;
        }

        private bool ServerMessage_0x4C_ConfirmExit(Client client, ServerPacket serverPacket)
        {
            ManualServerSwitch.TryAdd(client.Name, true);
            return true;
        }

        private bool ServerMessage_0x56_ServerTable(Client client, ServerPacket serverPacket)
        {
            return true;
        }

        private bool ServerMessage_0x58_MapLoadComplete(Client client, ServerPacket serverPacket)
        {
            if (client.IsRefreshingData == 1)
                client.MapChanged = true;



            return true;
        }

        private bool ServerMessage_0x60_LoginNotice(Client client, ServerPacket serverPacket)
        {
            return true;
        }

        private bool ServerMessage_0x63_GroupRequest(Client client, ServerPacket serverPacket)
        {
            return true;
        }

        private bool ServerMessage_0x66_LoginControls(Client client, ServerPacket serverPacket)
        {
            if (serverPacket.ReadByte() == 3)
            {
                ServerPacket newServerPacket = new ServerPacket(102);
                newServerPacket.WriteByte(4);
                serverPacket.WriteByte(1);
                Packet[] toSend = new Packet[] { newServerPacket };
                client.Enqueue(toSend);
            }
            return true;
        }

        private bool ServerMessage_0x67_MapChangePending(Client client, ServerPacket serverPacket)
        {
            _mapChangePending = true;
            return true;
        }

        private bool ServerMessage_0x68_SynchronizeTicks(Client client, ServerPacket serverPacket)
        {
            ClientPacket clientPacket = new ClientPacket(0x75);
            clientPacket.WriteInt32(serverPacket.ReadInt32());
            clientPacket.WriteInt32(Environment.TickCount);
            Packet[] toSend = new Packet[] { clientPacket };
            client.Enqueue(toSend);
            return false;
        }

        private bool ServerMessage_0x6F_MetaData(Client client, ServerPacket serverPacket)
        {
            return true;
        }

        private bool ServerMessage_0x7E_AcceptConnection(Client client, ServerPacket serverPacket)
        {
            return true;
        }
        #endregion

        private void HandleBeginTrade(Client client, ServerPacket serverPacket)
        {
            client.Bot._dontCast = true;
            client.Bot._dontWalk = true;
            client.ExchangeOpen = true;

            uint id = serverPacket.ReadUInt32();
            client.ExchangeID = id;
            _exchangeName = serverPacket.ReadString8();

            client.ClientTab.AddMessageToChatPanel(Color.IndianRed, $"An exchange has started with {_exchangeName}!");
        }

        private void HandleAddStackable(Client client, ServerPacket serverPacket)
        {
            client.ExchangeOpen = true;

            byte toOrFrom = serverPacket.ReadByte();
            serverPacket.ReadByte();
            serverPacket.ReadUInt16();
            serverPacket.ReadByte();

            _exchangeItem = serverPacket.ReadString8();

            if (toOrFrom == 0)
            {
                client.ClientTab.AddMessageToChatPanel(Color.IndianRed, $"You offer {_exchangeItem} to {_exchangeName}.");
            }
            else
            {
                client.ClientTab.AddMessageToChatPanel(Color.IndianRed, $"{_exchangeName} offers you {_exchangeItem}");
            }
        }

        private void HandleAddGold(Client client, ServerPacket serverPacket)
        {
            byte toOrFrom = serverPacket.ReadByte();
            uint amount = serverPacket.ReadUInt32();

            if (toOrFrom == 0)
            {
                client.ClientTab.AddMessageToChatPanel(Color.IndianRed, $"You offer {amount} gold to {_exchangeName}.");
            }
            else
            {
                client.ClientTab.AddMessageToChatPanel(Color.IndianRed, $"{_exchangeName} offers you {amount} gold.");
            }
        }

        private void HandleCancelExchange(Client client, ServerPacket serverPacket)
        {
            client.Bot._dontCast = false;
            client.Bot._dontWalk = false;

            ThreadPool.QueueUserWorkItem(_ => client.ResetExchangeVars());

            byte toOrFrom = serverPacket.ReadByte();

            if (toOrFrom == 0)
            {
                client.ClientTab.AddMessageToChatPanel(Color.IndianRed, $"Exchange cancelled by you.");
            }
            else
            {
                client.ClientTab.AddMessageToChatPanel(Color.IndianRed, $"Exchange cancelled by {_exchangeName}.");
            }

            _exchangeCancel = serverPacket.ReadString8();
        }

        private void HandleAcceptExchange(Client client, ServerPacket serverPacket)
        {
            client.Bot._dontCast = false;
            client.Bot._dontWalk = false;

            ThreadPool.QueueUserWorkItem(_ => client.ResetExchangeVars());

            byte toOrFrom = serverPacket.ReadByte();

            client.ClientTab.AddMessageToChatPanel(Color.IndianRed, $"Exchange accepted!");

            _exchangeAccept = serverPacket.ReadString8();
        }
        private Player GetOrCreatePlayer(Client client, int id, string name, Location location, Direction direction)
        {
            Player player = null;
            string clientName = "";
            if (client.Player != null)
            {
                clientName = client.Player.Name;
            }
            // Check if the player exists in WorldObjects and is a Player
            if (client.WorldObjects.TryGetValue(id, out var worldObject) && worldObject is Player existingPlayer)
            {
                //Console.WriteLine($"[GetOrCreatePlayer] CLIENT: {clientName} *** Player found in WorldObjects: {existingPlayer.Name}, Hash: {existingPlayer.GetHashCode()}");
                player = existingPlayer;
            }


            // If player wasn't found, create a new one
            if (player == null)
            {
                player = new Player(id, name, location, direction);
                //Console.WriteLine($"[GetOrCreatePlayer] CLIENT: {clientName} *** Player not found in WorldObjects, creating new player: {player.Name}, Hash: {player.GetHashCode()}");
            }
            else
            {
                // Update the existing player's properties
                player.Location = location;
                player.Direction = direction;
                if (!string.IsNullOrEmpty(name) && string.IsNullOrEmpty(player.Name))
                {
                    player.Name = name;
                }
            }

            return player;
        }

        internal Creature GetOrCreateCreature(Client client, int id, string name, ushort sprite, byte type, Location location, Direction direction)
        {
            Creature creature;

            if (!client.WorldObjects.TryGetValue(id, out var worldObject))
            {
                // Create a new creature
                creature = new Creature(id, name, sprite, type, location, direction);

                client.WorldObjects.TryAdd(id, creature);

                //Console.WriteLine($"[GetOrCreateCreature] Created new Creature ID: {id}, HashCode: {creature.GetHashCode()}");
            }
            else
            {
                // Update the existing creature
                creature = worldObject as Creature;
                if (creature != null)
                {
                    // Before updating, log current state
                    //Console.WriteLine($"[GetOrCreateCreature] Before Update - Creature ID: {id}, IsCursed: {creature.IsCursed}, LastCursed: {creature.GetState<DateTime>(CreatureState.LastCursed)}, CurseDuration: {creature.GetState<double>(CreatureState.CurseDuration)}, IsFassed: {creature.IsFassed}, LastFassed: {creature.GetState<DateTime>(CreatureState.LastFassed)}, FasDuration: {creature.GetState<double>(CreatureState.FasDuration)}");

                    // Update properties that may change
                    creature.Location = location;
                    creature.Direction = direction;
                    creature.IsActive = true;
                    creature.LastSeen = DateTime.UtcNow;

                    // Only update name if it's empty
                    if (string.IsNullOrEmpty(creature.Name) && !string.IsNullOrEmpty(name))
                    {
                        creature.Name = name;
                    }

                    // After updating, log current state
                    //Console.WriteLine($"[GetOrCreateCreature] After Update - Creature ID: {id}, IsCursed: {creature.IsCursed}, LastCursed: {creature.GetState<DateTime>(CreatureState.LastCursed)}, CurseDuration: {creature.GetState<double>(CreatureState.CurseDuration)}, IsFassed: {creature.IsFassed}, LastFassed: {creature.GetState<DateTime>(CreatureState.LastFassed)}, FasDuration: {creature.GetState<double>(CreatureState.FasDuration)}");
                }
            }

            // Apply any cached updates to the creature
            CreatureStateHelper.ApplyCachedUpdates(client, creature);

            return creature;
        }

        internal Client GetClient(string clientName)
        {
            try
            {
                return Clients.FirstOrDefault(c => c.Name.Equals(clientName, StringComparison.CurrentCultureIgnoreCase));
            }
            catch (Exception ex)
            {
                Console.WriteLine($"Error in GetClient: {ex.Message}");
                return null;
            }
        }

        internal List<Client> GetFollowChain(Client leader)
        {
            List<Client> followChain = new List<Client>();
            bool hasFollowers = false;

            try
            {
                int count;
                do
                {
                    count = followChain.Count;

                    foreach (var client in Clients)
                    {
                        if (client.ClientTab != null
                            && !client.Name.Contains("[")
                            && client.ClientTab.followCbox.Checked
                            && !followChain.Contains(client))
                        {
                            // Check if this client follows the leader or any client in the follow chain
                            bool isFollower = hasFollowers
                                ? followChain.Any(x => client.ClientTab.followText.Text.Equals(x.ClientTab.followText.Text, StringComparison.OrdinalIgnoreCase))
                                : client.ClientTab.followText.Text.Equals(leader.Name, StringComparison.OrdinalIgnoreCase);

                            if (isFollower)
                            {
                                followChain.Add(client);
                                hasFollowers = true;
                            }
                        }
                    }
                }
                while (count != followChain.Count); // Continue until no new followers are added
            }
            catch
            {
                return new List<Client>(); // Return an empty list if any error occurs
            }

            return followChain;
        }
        internal void RemoveFirstCreatureToSpell(Client client)
        {
            lock (SyncObj)
            {
                if (client.SpellHistory != null && client.SpellHistory.Count > 0)
                {
                    //Console.WriteLine($"[RemoveFirstCreatureToSpell] Creature ID: {client._spellHistory[0].Creature.ID}, Spellname: {client._spellHistory[0].Spell.Name}, Hash: {client._spellHistory[0].Spell.GetHashCode()}");
                    client.SpellHistory.RemoveAt(0);
                }
            }
        }
        internal void SetDugon(Client client, string dugonLevel)
        {
            Dictionary<string, Dugon> dugonMappings = new Dictionary<string, Dugon>
            {
                { "Dgn-0", Dugon.White },
                { "Dgn-1", Dugon.Green },
                { "Dgn-2", Dugon.Blue },
                { "Dgn-3", Dugon.Yellow },
                { "Dgn-4", Dugon.Purple },
                { "Dgn-5", Dugon.Brown },
                { "Dgn-6", Dugon.Red },
                { "Dgn-7", Dugon.Black }
            };

            // Default Dugon if no match found
            Dugon defaultDugon = Dugon.White; // Change this to the appropriate default value

            // Check if dugonLevel matches any mapping, otherwise use defaultDugon
            Dugon dugon = dugonMappings.TryGetValue(dugonLevel, out Dugon mappedDugon)
                ? mappedDugon
                : defaultDugon;

            Console.WriteLine($"[SetDugon] Setting dugon to: {dugon}");
            client.SetDugon(dugon);

        }
        internal void SetTemuairClass(Client client, int temClass)
        {
            Dictionary<int, TemuairClass> classMappings = new Dictionary<int, TemuairClass>
            {
                { 0, TemuairClass.Peasant },
                { 1, TemuairClass.Peasant | TemuairClass.Warrior },
                { 2, TemuairClass.Peasant | TemuairClass.Rogue },
                { 3, TemuairClass.Peasant | TemuairClass.Wizard },
                { 4, TemuairClass.Peasant | TemuairClass.Priest },
                { 5, TemuairClass.Peasant | TemuairClass.Monk }
            };

            // Default TemuairClass if no match found
            TemuairClass defaultClass = TemuairClass.Peasant;

            // Check if temClass matches any mapping, otherwise use defaultClass
            TemuairClass temuairClass = classMappings.TryGetValue(temClass, out TemuairClass mappedClass)
                ? mappedClass
                : defaultClass;

            Console.WriteLine($"[SetTemuairClass] Setting temauirClass to: {temuairClass}");
            client.SetTemuairClass(temuairClass);
        }
        internal void SetMedeniaClass(Client client, string className)
        {
            Dictionary<string, MedeniaClass> classMappings = new Dictionary<string, MedeniaClass>
            {
                { "Gladiator", MedeniaClass.Gladiator },
                { "Druid", MedeniaClass.Druid },
                { "Bard", MedeniaClass.Bard },
                { "Archer", MedeniaClass.Archer },
                { "Summoner", MedeniaClass.Summoner }

            };

            // Default MedeniaClass if no match found
            MedeniaClass defaultClass = MedeniaClass.NonMed;

            // Check if className matches any mapping, otherwise use defaultClass
            MedeniaClass medeniaClass = classMappings.TryGetValue(className, out MedeniaClass mappedClass)
                ? mappedClass
                : defaultClass;

            Console.WriteLine($"[SetMedeniaClass] Setting medeniaClass to: {medeniaClass}");
            client.SetMedeniaClass(medeniaClass);
        }
        internal void SetPreviousClass(Client client, string className)
        {
            Dictionary<string, PreviousClass> classMappings = new Dictionary<string, PreviousClass>
            {
                { "CMonk", PreviousClass.Monk },
                { "CPriest", PreviousClass.Priest },
                { "CMage", PreviousClass.Wizard },
                { "CWizard", PreviousClass.Wizard },
                { "CWarrior", PreviousClass.Warrior },
                { "CWarror", PreviousClass.Warrior },
                { "CRogue", PreviousClass.Rogue },
                { "CThief", PreviousClass.Rogue },
            };

            // Default PreviousClass if no match found
            PreviousClass defaultClass = PreviousClass.Pure;

            // Check if text matches any mapping, otherwise use defaultClass
            PreviousClass previousClass = classMappings.TryGetValue(className, out PreviousClass mappedClass)
                ? mappedClass
                : defaultClass;

            //Console.WriteLine($"[SetPreviousClass] Setting previousClass to: {previousClass}");
            client.SetPreviousClass(previousClass);
        }

        internal void SetDruidForm(Client client, string formName)
        {
            Dictionary<string, DruidForm> formMappings = new Dictionary<string, DruidForm>
            {
                { "LBeast1", DruidForm.Feral },
                { "LBeast2", DruidForm.Karura },
                { "LBeast3", DruidForm.Komodas }
            };

            // Default MedeniaClass if no match found
            DruidForm defaultForm = DruidForm.None;

            // Check if className matches any mapping, otherwise use defaultClass
            DruidForm druidForm = formMappings.TryGetValue(formName, out DruidForm mappedForm)
                ? mappedForm
                : defaultForm;

            Console.WriteLine($"[SetDruidForm] Setting druid form to: {druidForm}");
            client.SetDruidForm(druidForm);
        }

        internal void SetComboSkill(Client client, string mark, string comboType)
        {
            // Map combo type to flags and scroll names
            var comboMapping = new Dictionary<string, (string ComboScrollName, Func<Client, bool> GetFlag, Action<Client, bool> SetFlag)>
            {
                { "Combo1", ("Combo Scroll 1", c => c.ComboOneSet, (c, v) => c.ComboOneSet = v) },
                { "Combo2", ("Combo Scroll 2", c => c.ComboTwoSet, (c, v) => c.ComboTwoSet = v) },
                { "Combo3", ("Combo Scroll 3", c => c.ComboThreeSet, (c, v) => c.ComboThreeSet = v) }
            };

            if (!comboMapping.TryGetValue(comboType, out var comboInfo))
                return;

            // Check if the combo has already been set
            if (comboInfo.GetFlag(client))
                return;

            string startMarker = "Set ";
            string endMarker = $" as {GetComboOrdinal(comboType)} move -";

            // Extract the skill name from the mark string
            int startIndex = mark.IndexOf(startMarker);
            int endIndex = mark.IndexOf(endMarker, startIndex + startMarker.Length);
            if (startIndex == -1 || endIndex == -1)
                return;

            int skillNameStart = startIndex + startMarker.Length;
            string skillName = mark.Substring(skillNameStart, endIndex - skillNameStart);

            // Check if the required combo scroll is present
            if (!client.Inventory.Contains("Two Move Combo") &&
                (!client.Inventory.Contains("Three Move Combo") || client.HasSkill(comboInfo.ComboScrollName)))
                return;

            // Find the first available skill slot
            byte slot = 37;
            Dictionary<byte, Skill> skillSlots = client.Skillbook.SkillbookDictionary
                .ToDictionary(kv => kv.Value.Slot, kv => kv.Value);

            while (skillSlots.ContainsKey(slot))
                ++slot;

            // Create and add the new combo skill
            Skill skill = new Skill(slot, comboInfo.ComboScrollName, 101, 100, 100)
            {
                Ticks = 1.0
            };
            Console.WriteLine($"[SetComboSkill] Adding combo skill {skill.Name}");
            client.Skillbook.AddOrUpdateSkill(skill);
            client.AddSkill(skill);


            // Mark the combo as set
            comboInfo.SetFlag(client, true);
        }

        // Helper method to get the ordinal string for the combo type
        private string GetComboOrdinal(string comboType)
        {
            return comboType switch
            {
                "Combo1" => "first",
                "Combo2" => "second",
                "Combo3" => "third",
                _ => comboType
            };
        }


        /// <summary>
        /// Function to load the map cache from the resources maps.dat
        /// </summary>
        /// <returns></returns>
        private bool LoadMapCache()
        {
            BinaryReader binaryReader = new BinaryReader(new MemoryStream(Resources.maps));
            int header = binaryReader.ReadInt32();
            //Logger.Log($"Header/version: {header}");

            short worldMapCount = binaryReader.ReadInt16();
            //Logger.Log($"World maps count: {worldMapCount}");
            for (int i = 0; i < worldMapCount; i++)
            {
                string worldMapName = binaryReader.ReadString();
                WorldMap worldMap = new WorldMap(worldMapName, new WorldMapNode[0]);
                byte nodeCount = binaryReader.ReadByte();
                //Logger.Log($"World Map '{worldMapName}' with {nodeCount} nodes:");

                for (int index2 = 0; index2 < nodeCount; ++index2)
                {
                    short sourceX = binaryReader.ReadInt16();
                    short sourceY = binaryReader.ReadInt16();
                    string nodeName = binaryReader.ReadString();
                    short mapId = binaryReader.ReadInt16();
                    byte targetX = binaryReader.ReadByte();
                    byte targetY = binaryReader.ReadByte();
                    worldMap.Nodes.Add(new WorldMapNode(new Point(sourceX, sourceY), nodeName, mapId, new Point(targetX, targetY)));
                    //Logger.Log($" - Node {nodeName} at [{sourceX},{sourceY}] to Map {mapId} at [{targetX},{targetY}]");
                }
                _worldMaps[worldMap.GetCRC32()] = worldMap;
            }

            short mapCount = binaryReader.ReadInt16();
            //Logger.Log($"Map count: {mapCount}");

            for (int index3 = 0; index3 < mapCount; ++index3)
            {
                try
                {
                    short sourceMapId = binaryReader.ReadInt16();
                    byte sizeX = binaryReader.ReadByte();
                    byte sizeY = binaryReader.ReadByte();
                    string name = binaryReader.ReadString();
                    byte flags = binaryReader.ReadByte();
                    sbyte music = binaryReader.ReadSByte();

                    Map map = new Map(sourceMapId, sizeX, sizeY, flags, name, music);
                    //Logger.Log($"Processing map '{name}' ID {sourceMapId} Size {sizeX}x{sizeY}");

                    short warpCount = binaryReader.ReadInt16();
                    //Logger.Log($" - {warpCount} warps:");
                    for (int index4 = 0; index4 < warpCount; ++index4)
                    {
                        byte sourceX = binaryReader.ReadByte();
                        byte sourceY = binaryReader.ReadByte();
                        short targetMapId = binaryReader.ReadInt16();
                        byte targetX = binaryReader.ReadByte();
                        byte targetY = binaryReader.ReadByte();
                        Warp warp = new Warp(sourceX, sourceY, targetX, targetY, sourceMapId, targetMapId);
                        map.Exits[new Point(sourceX, sourceY)] = warp;
                        //Logger.Log($" - Warp from Map {sourceMapId} [{sourceX},{sourceY}] to Map {targetMapId} at [{targetX},{targetY}]");
                    }

                    byte numWorldMaps = binaryReader.ReadByte();
                    //Logger.Log($" - {numWorldMaps} world map links:");
                    for (int index5 = 0; index5 < numWorldMaps; ++index5)
                    {
                        byte x = binaryReader.ReadByte();
                        byte y = binaryReader.ReadByte();
                        uint key = binaryReader.ReadUInt32();
                        if (_worldMaps.ContainsKey(key))
                        {
                            map.WorldMaps[new Point(x, y)] = _worldMaps[key];
                            //Logger.Log($" - World map link at [{x},{y}] to world map with key {key}");
                        }
                        else
                        {
                            //Logger.Log($" - Failed to find world map with key {key} for position [{x},{y}]");
                        }
                    }
                    _maps.Add(sourceMapId, map);
                }
                catch (Exception ex)
                {
                    //Logger.Log($"Error processing map ID {index3}: {ex.Message}");
                }
            }
            binaryReader.Close();
            return true;
        }

        public static class Logger
        {
            private static readonly string LogFilePath = "mapcache.log";

            public static void Log(string message)
            {
                using (StreamWriter sw = new StreamWriter(LogFilePath, true))
                {
                    sw.WriteLine($"{DateTime.Now}: {message}");
                }
            }
        }

        internal void ResetBuffsOnAoSith(Client client, int creatureId, bool strangerNearby = false)
        {
            if (strangerNearby)
            {
                // Consider using an asynchronous delay here to avoid blocking the thread
                Thread.Sleep(3000);
            }

            List<Client> clientListCopy;
            lock (_clientListLock)
            {
                clientListCopy = ClientList.ToList(); // Create a copy to iterate over
            }


            foreach (Client currentClient in clientListCopy)
            {
                WorldObject worldObject;
                if (!currentClient.WorldObjects.TryGetValue(creatureId, out worldObject))
                {
                    continue;
                }

                Creature creature = worldObject as Creature;
                if (creature != null)
                {
                    ClearBuffStatus(client, creature, false);
                }
            }
        }
        private void ClearBuffStatus(Client client, Creature creature, bool wait)
        {
            if (wait)
            {
                Thread.Sleep(3000);
            }

            var stateUpdates = new Dictionary<CreatureState, object>
            {
                {CreatureState.CurseName, string.Empty },
                {CreatureState.CurseDuration, 0.0 },
                {CreatureState.FasDuration, 0.0 },
                {CreatureState.AiteDuration, 0.0 },
                {CreatureState.DionDuration, 0.0 },
                {CreatureState.DionName, string.Empty }
            };

            CreatureStateHelper.UpdateCreatureStates(client, creature.ID, stateUpdates);

            if (creature.AnimationHistory.ContainsKey((byte)SpellAnimation.Armachd))
            {
                creature.AnimationHistory[(byte)SpellAnimation.Armachd] = DateTime.MinValue;
            }

            if (ReferenceEquals(creature, client.Player))
            {
                client.Bot._recentlyAoSithed = true;
            }
        }

        private void AutomaticActions()
        {
            while (_initialized)
            {
                List<Client> clientListCopy;
                lock (_clientListLock)
                {
                    clientListCopy = ClientList.ToList(); // Create a copy to iterate over
                }

                foreach (Client client in clientListCopy)
                {
                    try
                    {
                        if (client == null || client.ClientTab == null || client.ClientTab.startStrip == null)
                            continue;

                        string text = client.ClientTab.startStrip.Text;

                        if (text == "Stop" && client.ClientTab.rangerLogCbox.Checked)
                        {
                            lock (client.CastLock)
                            {
                                //request world list
                                client.Enqueue(new Packet[] { new ClientPacket(0x18) });
                            }
                        }

                        if (Settings.Default.enableKom && !string.IsNullOrEmpty(client.Name) && client.Map != null &&
                            client.Map.MapID == 10055 && !client.Bot.IsStrangerNearby() &&
                            client.ServerLocation.DistanceFrom(new Location(10055, 39, 40)) <= 18 &&
                            client.GetItemQuantity("Komadium") < 52)
                        {
                            int currentKoms = client.GetItemQuantity("Komadium");
                            while (currentKoms < 52)
                            {
                                client.DisplayChant("I buy Komadium");
                                currentKoms++;
                            }
                        }

                        if (DateTime.UtcNow.Subtract(client.ClientTab._lastUpdate).TotalSeconds > 60.0)
                        {
                            client.ClientTab.HandleFiles();
                            client.ClientTab._lastUpdate = DateTime.UtcNow;
                        }

                        if (DateTime.UtcNow.Subtract(client.ClientTab._lastStatusUpdate).TotalSeconds > 3.0 && !client.IsStatusUpdated)
                        {
                            client.ClientTab.AutoLoginHandlers();
                        }
                    }
                    catch
                    {
                        // Exception handling
                    }
                }
                Thread.Sleep(5000); // Sleep for 5 seconds
            }
        }

        private void CleanupInactiveCreatures(Client client)
        {
            try
            {
                foreach (var kvp in client.WorldObjects.ToList())
                {
                    if (kvp.Value is Creature creature && !creature.IsActive)
                    {
                        // Remove if the creature has been inactive for more than 5 minutes
                        if ((DateTime.UtcNow - creature.LastSeen) > TimeSpan.FromMinutes(5))
                        {
                            client.WorldObjects.TryRemove(creature.ID, out _);
                            Console.WriteLine($"[CleanupInactiveCreatures] Removed inactive Creature ID {creature.ID}.");
                        }
                    }
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine($"[CleanupInactiveCreatures] Exception: {ex.Message}");
            }
        }

        private void ResetDialogFlags(Client client)
        {
            client.ArcellaGift = false;
            client.ArcellaGiftOpen = false;
            client.Wdchest = false;
            client.Wdchestopen = false;
            client.Andorchest = false;
            client.Andorchestopen = false;
            client.Queenchest = false;
            client.Queenchestopen = false;
            client.Veltainchest = false;
            client.Heavychest = false;
            client.Smallbag = false;
            client.Smallbagopen = false;
            client.Bigbag = false;
            client.Bigbagopen = false;
            client.Heavybag = false;
            client.Heavybagopen = false;
            client.Atemeg = false;
            client.Ateabbox = false;
            client.Ateabgift = false;
        }

        private void HandleChestAndBagInteractions(Client client, string npcDialog, string objName)
        {
            if (objName == "Andor Chest" && npcDialog.Contains(", What type of prize"))
                client.Andorchest = true;
            else if (objName == "Andor Queen's Chest" && npcDialog.Contains(", What type of prize"))
                client.Queenchest = true;
            else if (objName == "Water Dungeon Chest" && npcDialog.Contains(", What type of prize would you"))
                client.Wdchest = true;
            else if (objName == "Canal Treasure Bag" && npcDialog.Contains("You are about to pull an item"))
                client.Smallbag = true;
            else if (objName == "Big Canal Treasure Bag" && npcDialog.Contains("pull an item"))
                client.Bigbag = true;
            else if (objName == "Heavy Canal Treasure Bag" && npcDialog.Contains("You are about to pull an item"))
                client.Heavybag = true;
            else if (objName == "Veltain Treasure Chest" && npcDialog.Contains("How much do you want to invest"))
                client.Veltainchest = true;
            else if (objName == "Heavy Veltain Treasure Chest" && npcDialog.Contains("How much do you want to invest"))
                client.Heavychest = true;
            else if (objName == "Ability and Experience Box" && npcDialog.Contains("You will gain great"))
                client.Ateabbox = true;
            else if (objName == "Ability and Experience Gift" && npcDialog.Contains("You will gain great"))
                client.Ateabgift = true;
            else if (objName == "Arcella's Gift1" && npcDialog.Contains("You are about to open the gift"))
                client.ArcellaGift = true;
            else if (objName == "Mother Erbie Gift" && npcDialog.Contains("You will gain great"))
                client.Atemeg = true;
        }

        private bool HandleMapSpecificEvents(Client client, string npcDialog, int mapId)
        {
            switch (mapId)
            {
                case 115:
                    if (npcDialog.StartsWith("I see you were able ", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.PigChase);
                        return true;
                    }
                    break;
                case 132:
                    if (spareStickMessages.Any(message => npcDialog.StartsWith(message, StringComparison.OrdinalIgnoreCase)))
                    {
                        client.SaveTimedStuff(EventType.SpareStick);
                        return true;
                    }
                    break;
                case 950:
                    if (perfectHairstyleMessages.Any(message => npcDialog.StartsWith(message, StringComparison.OrdinalIgnoreCase)))
                    {
                        client.SaveTimedStuff(EventType.PerfectHairstyle);
                        return true;
                    }
                    break;
                case 992:
                    if (npcDialog.StartsWith("Sorry, no faeries are willing to bond with you.", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.PetFaerie);
                        return true;
                    }
                    break;
                case 3052:
                    if (npcDialog.StartsWith("Excellent! Here is your prize", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.Fowls);
                        return true;
                    }
                    break;
                case 6805:
                    if (npcDialog.StartsWith("You drink from the fountain.", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.OrenFountain);
                        return true;
                    }
                    break;
                case 6998:
                    if (npcDialog.StartsWith("Thank you for your efforts.", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.WaterDungeon);
                        return true;
                    }
                    break;
                case 7050:
                    if (npcDialog.StartsWith("Thank you for scaring", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.FilthyErbies);
                        return true;
                    }
                    break;
                case 8297:
                    if (npcDialog.StartsWith("Excellent! Here is", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.SporeSet);
                        return true;
                    }
                    break;
                case 8298:
                    if (npcDialog.StartsWith("Thank you! You saved me", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.FrogSet);
                        return true;
                    }
                    break;
                case 8990:
                    if (npcDialog.StartsWith("This must be the wall markings that Nairn was talking about.", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.AssassinLord);
                        return true;
                    }
                    break;
                case 8995:
                    if (npcDialog.StartsWith("Guess who we encountered after performing the ritual?", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.Law);
                        return true;
                    }
                    break;
                case 10266:
                    if (npcDialog.StartsWith("That's something for us to worry about", StringComparison.OrdinalIgnoreCase))
                    {
                        client.SaveTimedStuff(EventType.CursedHome);
                        return true;
                    }
                    break;
            }

            return false;
        }


        private bool HandleSpecialDialogs(
            Client client,
            string npcDialog,
            byte dialogType,
            byte objType,
            int objID,
            ushort pursuitID,
            ushort dialogID,
            byte unknown1,
            ushort sprite1,
            byte color1,
            byte unknown2,
            ushort sprite2,
            byte color2,
            byte unknown3,
            string gameObjectName,
            List<string> options)
        {
            if (npcDialog == "Thanks a bunch, I wish I was there")
            {
                client.SaveTimedStuff(EventType.Penguins);
                return true;
            }

            if (npcDialog == "Ahh well, it's best we don't tell Santa")
            {
                client.SaveTimedStuff(EventType.Rudolph);
                return true;
            }

            if (npcDialog == "She finally bows her head, accepting it.")
            {
                client.SaveTimedStuff(EventType.TheLetter);
                return true;
            }

            if (npcDialog == "Wonderful. Just wait a moment")
            {
                client.SaveTimedStuff(EventType.MothersLove);
                return true;
            }
            if ((npcDialog == "Do you wish to go back to Chaos 1?") || (npcDialog == "You are about to enter a hostile area. Do you wish to proceed?"))
            {
                client.Dialog.DialogNext(1);
                return true;
            }
            if (npcDialog == "Lying in bed, your eyes become heavy. The cold and weary day has finally caught up to you. Do you want to sleep?")
            {
                client.ReplyDialog(objType, objID, pursuitID, (ushort)(dialogID + 1), 1);
                client.ReplyDialog(objType, objID, pursuitID, (ushort)(dialogID + 1));
                client.ReplyDialog(objType, objID, pursuitID, (ushort)(dialogID + 1));
                return true;
            }
            if ((npcDialog == "((You are entering a role-playing town where role-playing is strictly enforced. Please do not speak words that are not appropriate to the theme of Dark Ages. Any act of heresy can result in a temporary banishment from the town.))") || (npcDialog == "Congratulations in finding a Golden Starfish!"))
            {
                client.Dialog.DialogNext();
                return true;
            }

            if ((npcDialog == "The Braided Vine unravels from the rocks and you lose your footing."))
            {
                client.Dialog.Reply();
                return true;
            }
            if (npcDialog == "The Braided Vine starts to unravel, but you quickly jumped to dry land.")
            {
                client.ReplyDialog(objType, objID, pursuitID, (ushort)(dialogID + 1));
                client.ReplyDialog(objType, objID, pursuitID, (ushort)(dialogID + 1));
                return true;
            }
            if (npcDialog == "You throw the Braided Vine around the rocks hoping it gets lodged in between them.")
            {
                client.ReplyDialog(objType, objID, pursuitID, (ushort)(dialogID + 1));
                client.ReplyDialog(objType, objID, pursuitID, (ushort)(dialogID + 1));
                client.ReplyDialog(objType, objID, pursuitID, (ushort)(dialogID + 1));
                return true;
            }
            if ((npcDialog == "I don't think this is the correct order for the story. I better look at the other Wall Tablets."))
            {
                client.Dialog.Reply();
                return true;
            }
            if (npcDialog == "*The Yowien Guard sniffs you, then suddenly attacks you. You run back to a safe distance*")
            {
                client.ClientTab.walkBtn.Text = "Walk";
            }
            if (npcDialog == "This will reset your labor to one hour. You can only do this once.")
            {
                client.HasLabor = true;
            }
            if (npcDialog == "Will you be respectful of the meditations and not reveal the secrets of meditation?")
            {
                client.Dialog.DialogNext(2);
            }
            if (npcDialog == "You are going to be arrested for sleep-fighting ((Auto Hunting)) in five minutes unless you state that you do not wish to.")
            {
                ThreadPool.QueueUserWorkItem(_ => client.SleepFighting());
                return true;
            }
            if (npcDialog.Contains("Golden Starfish") || npcDialog.Contains("role-playing town"))
            {
                client.Dialog.DialogNext();
                return true;
            }
            if (npcDialog == "The full Red Moon shines brightly in the sky. You stare at it, hypnotized by its light. Your body starts to tremble. You breathe heavily as you continue to stare at the moon. Your body begins to change...")
            {
                client.Dialog.Close();
                return true;
            }

            // Dugon meditation handling
            if (client.ClientTab.toggleHubaeBtn.Text == "Disable")
            {

                if (npcDialog == "Welcome to Dark Ages : Online Roleplaying. This tutorial will give you the facts and skills you need to begin.")
                {
                    for (int i = 0; i < 6; i++)
                    {
                        client.ReplyDialog(objType, objID, pursuitID, (ushort)(dialogID + 1));
                    }
                    Thread.Sleep(1000);
                    return true;
                }
                if (npcDialog == "You are about to leave the tutorial. Heres a hint when starting, speak with all the mundanes (merchants) in Mileth (the starting town). Remember, this is an online world, you set your own goals and missions for your character.")
                {
                    client.ReplyDialog(objType, objID, pursuitID, 2);
                    client.ReplyDialog(objType, objID, pursuitID, 3);
                    client.ReplyDialog(objType, objID, pursuitID, 11, 1);
                    client.ReplyDialog(objType, objID, pursuitID, 0x13);
                    client.ReplyDialog(objType, objID, pursuitID, 0x31);
                    client.ReplyDialog(objType, objID, pursuitID, 0x6d, 2);
                    client.ReplyDialog(objType, objID, pursuitID, 0x2a);
                    Thread.Sleep(1000);
                    client.Dialog = null;
                    return true;
                }
                if (npcDialog == "You rub your eyes...")
                {
                    ThreadPool.QueueUserWorkItem(state =>
                    {
                        var tuple = (Tuple<byte, int, ushort>)state;
                        client.NewAisling(tuple.Item1, tuple.Item2, tuple.Item3);
                    },
                    Tuple.Create(client, objType, objID, pursuitID));
                    return true;
                }
                if (npcDialog == "You legs are the strongest.  You enemies will be scattered.")
                {
                    client.Bot._circle1 = true;
                    return true;
                }
                if (npcDialog == "Over that left door, you can be born a Monk.  You will be strong in working with the Nature.  You will save the people in danger, and only you will be able to increase other peoples' mana.")
                {
                    client.Bot._circle2 = true;
                    return true;
                }
                if (!client.Bot._hasWhiteDugon && CONSTANTS.WHITE_DUGON_RESPONSES.TryGetValue(npcDialog, out string whiteMeditation))
                {
                    int index = int.MaxValue;
                    index = options.IndexOf(whiteMeditation);
                    if (index != int.MaxValue)
                    {
                        client.Dialog.DialogNext((byte)(index + 1));
                    }
                }
                else
                {
                    if (client.Bot._hasGreenDugon && CONSTANTS.GREEN_DUGON_RESPONSES.TryGetValue(npcDialog, out string greenMeditation))
                    {
                        int index = int.MaxValue;
                        index = options.IndexOf(greenMeditation);
                        if (index != int.MaxValue)
                        {
                            client.Dialog.DialogNext((byte)(index + 1));
                        }
                    }
                }
            }

            // World shout cooldown
            if (npcDialog == "You have already sent a world shout in the last 5 minutes.")
            {
                TimeSpan timeRemaining = TimeSpan.FromMinutes(5) - (DateTime.UtcNow - _lastWorldShout);
                string message = timeRemaining.TotalSeconds > 0
                    ? $"You may World Shout again in {timeRemaining.Minutes} minutes and {timeRemaining.Seconds} seconds."
                    : "unknown value.";

                client.ServerDialog(dialogType, objType, objID, unknown1, sprite1, color1, unknown2, sprite2, color2, pursuitID, dialogID, false, false, unknown3, gameObjectName, message);
                return true;
            }

            if (npcDialog == "Mentorship")
            {
                client.Dialog.Close();

                if (!client.SafeScreen)
                {
                    client.ServerMessage((byte)ServerMessageType.Whisper, "You walked on a mentor popup.");
                }

                return true;
            }

            if (npcDialog.StartsWith(
            "Mentorship: You have no mentor and are not high enough level",
            StringComparison.OrdinalIgnoreCase))
            {
                client.Dialog.Close();

                return true;
            }

            // "wishes to be your mentor ..."
            if (npcDialog.EndsWith(
                "wishes to be your mentor. If you sincerely believe this Aisling will teach and care for your well-being, consider accepting the Aisling as your Mentor.  Otherwise, don't be lured into a trap.",
                StringComparison.OrdinalIgnoreCase))
            {
                client.Dialog.Close();
                if (!client.SafeScreen)
                {
                    client.ServerMessage((byte)ServerMessageType.Whisper, "Someone tried to mentor popup you.");
                }
                return true;
            }

            // "wishes to be your guide and initiate ..."
            if (npcDialog.EndsWith(
                "wishes to be your guide and initiate. You were actually initiated by a different Aisling. You should only disgrace your first initiator if he or she has abandoned you or mistreats you.",
                StringComparison.OrdinalIgnoreCase))
            {
                client.Dialog.Close();
                if (!client.SafeScreen)
                {
                    client.ServerMessage((byte)ServerMessageType.Whisper, "You walked on a guide lecture popup.");
                }
                return true;
            }


            return false;
        }
    }
}

