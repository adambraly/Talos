using Newtonsoft.Json;
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using Talos.AStar;
using Talos.Cryptography;
using Talos.Definitions;
using Talos.Definitions;
using Talos.Forms;
using Talos.Helper;
using Talos.Maps;
using Talos.Networking;
using Talos.Objects;
using Talos.PInvoke;
using Talos.Properties;
using Talos.Structs;
using Talos.Utility;
using static System.Net.Mime.MediaTypeNames;
using GroundItem = Talos.Objects.GroundItem;
using Timer = Talos.Utility.Timer;



namespace Talos.Base
{
    internal class Client
    {
        #region Process Memory
        internal int processId;
        internal IntPtr hWnd;

        internal byte[] PROCESS_DATA;

        internal int BASE_ADDRESS = 6281332;

        internal byte[] ADDRESS_BUFFER = new byte[5] { 232, 47, 88, 2, 0 };

        private bool IsOSCompatible => Environment.OSVersion.Version.Major >= 5;
        #endregion

        #region Networking Vars
        private Socket _clientSocket;
        private Socket _serverSocket;

        private Queue<Packet> _sendQueue;
        private Queue<Packet> _receiveQueue;

        private byte _serverOrdinal;
        private byte _clientOrdinal;
        private byte[] _clientBuffer = new byte[4096];
        private byte[] _serverBuffer = new byte[4096];

        private List<byte> _fullClientBuffer = new List<byte>();
        private List<byte> _fullServerBuffer = new List<byte>();

        private Thread _clientLoopThread = null;
        private Thread _autoAscendLoopThread = null;

        private bool _connected = false;
        private bool clientReceiving = false;
        private bool serverReceiving = false;

        internal Crypto Crypto { get; set; }
        internal Server Server { get; set; }

        private DateTime _lastPacketSent = DateTime.UtcNow;
        private readonly TimeSpan _minSendInterval = TimeSpan.FromMilliseconds(50);
        #endregion

        private Location _routeDestination;
        private Location _lastDestination;
        private Stack<Location> _pathStack = new Stack<Location>();
        private Stack<Location> _routeStack = new Stack<Location>();
        private Cheats _cheats;
        private DateTime _lastClickedWorldMap = DateTime.MinValue;
        private DateTime _lastAssail;
        private int _customSpellLineCounter;
        private static int _walkCallCount = 0;
        private static HashSet<string> AoSuainHashSet = new HashSet<string>(new string[3] { "ao suain", "ao pramh", "Leafhopper Chirp" }, StringComparer.CurrentCultureIgnoreCase);
        internal int IsRefreshingData;
        internal bool comboFour;
        internal bool comboThree;
        internal bool comboTwo;
        internal bool comboOne;
        internal string lastGMChecked;
        internal bool GMDetect;
        internal bool forcegroup;
        internal readonly object BashLock = new object();
        internal readonly object CastLock = new object();
        internal Player Player { get; set; }
        internal Creature CastedTarget { get; set; }
        internal Map Map { get; set; }
        internal WorldMap WorldMap { get; set; }
        internal Spell CastedSpell { get; set; }
        internal Spell LastSpell { get; set; }
        internal Pathfinder Pathfinder { get; set; }
        internal RouteFinder RouteFinder { get; set; }
        internal Bot Bot { get; set; }
        internal BotBase BotBase { get; set; }
        internal Thread WalkThread { get; set; }
        internal ClientTab ClientTab { get; set; }
        internal Statistics Stats { get; set; }
        internal Dialog Dialog { get; set; }
        internal Inventory Inventory { get; set; } = new Inventory(60);
        internal Item[] EquippedItems { get; set; } = new Item[20];
        internal Spellbook Spellbook { get; set; } = new Spellbook();
        internal Skillbook Skillbook { get; set; } = new Skillbook();
        internal BindingList<int> WorldObjectBindingList { get; set; } = new BindingList<int>();
        internal BindingList<int> CreatureBindingList { get; set; } = new BindingList<int>();
        internal BindingList<string> StrangerBindingList { get; set; } = new BindingList<string>();
        internal BindingList<string> FriendBindingList { get; set; } = new BindingList<string>();
        internal BindingList<string> GroupBindingList { get; set; } = new BindingList<string>();
        internal List<SpellEntry> SpellHistory { get; set; } = new List<SpellEntry>();
        internal Dictionary<string, uint> BankedItems { get; set; } = new Dictionary<string, uint>();
        internal List<Staff> Staffs { get; set; } = new List<Staff>();
        internal List<MeleeWeapon> Weapons { get; set; } = new List<MeleeWeapon>();
        internal List<Bow> Bows { get; set; } = new List<Bow>();
        internal List<string> IgnoredDialogs { get; set; } = new List<string>();
        internal Dictionary<string, string> UserOptions { get; set; } = new Dictionary<string, string>();
        internal Dictionary<string, byte> StaffSpells { get; set; } = new Dictionary<string, byte>();
        internal Dictionary<string, DateTime> DictLastSeen { get; set; } = new Dictionary<string, DateTime>();
        internal Dictionary<string, int> InventoryDialogIDs { get; set; } = new Dictionary<string, int>();

        internal ConcurrentDictionary<int, Location> LastSeenLocations { get; set; } = new ConcurrentDictionary<int, Location>();
        internal ConcurrentDictionary<int, WorldObject> WorldObjects { get; private set; } = new ConcurrentDictionary<int, WorldObject>();
        internal ConcurrentDictionary<int, Player> NearbyHiddenPlayers { get; private set; } = new ConcurrentDictionary<int, Player>();
        internal ConcurrentDictionary<string, Player> NearbyPlayers { get; private set; } = new ConcurrentDictionary<string, Player>(StringComparer.OrdinalIgnoreCase);
        internal ConcurrentDictionary<string, Player> NearbyGhosts { get; private set; } = new ConcurrentDictionary<string, Player>(StringComparer.OrdinalIgnoreCase);
        internal ConcurrentDictionary<string, Creature> NearbyNPC { get; private set; } = new ConcurrentDictionary<string, Creature>();
        internal ConcurrentDictionary<string, int> ObjectID { get; private set; } = new ConcurrentDictionary<string, int>();
        internal ConcurrentDictionary<string, Player> Players { get; private set; } = new ConcurrentDictionary<string, Player>();
        internal ConcurrentDictionary<Location, Door> Doors { get; private set; } = new ConcurrentDictionary<Location, Door> { };
        internal HashSet<int> NearbyObjects { get; private set; } = new HashSet<int>();
        internal HashSet<int> NearbyGroundItems { get; private set; } = new HashSet<int>();
        internal HashSet<ushort> EffectsBar { get; set; } = new HashSet<ushort>();
        internal HashSet<string> GroupedPlayers { get; set; } = new HashSet<string> { };
        internal DateTime ComboScrollLastUsed { get; set; } = DateTime.MinValue;
        internal Location ClientLocation { get; set; }
        internal Location ServerLocation { get; set; }
        internal DateTime LastStep { get; set; } = DateTime.MinValue;
        internal DateTime LastTurned { get; set; } = DateTime.MinValue;
        internal Nation Nation { get; set; }
        internal Direction ClientDirection { get; set; }
        internal Direction ServerDirection { get; set; }
        internal MapFlags MapFlags { get; set; }
        internal TemuairClass TemuairClassFlag { get; set; }
        internal MedeniaClass MedeniaClassFlag { get; set; }
        internal DruidForm DruidFormFlag { get; set; }
        internal PreviousClass PreviousClassFlag { get; set; }
        internal Dugon DugonFlag { get; set; }
        internal string NpcDialog { get; set; }
        internal string CurrentSkill { get; set; } = "";
        internal string CurrentItem { get; set; } = "";
        internal string OffenseElement { get; set; } = "";
        internal string Action { get; set; } = "Current Action: ";
        internal string Name { get; set; }
        internal string GuildName { get; set; }
        internal bool BlockDialogs { get; set; } = false;
        internal bool SafeScreen { get; set; }
        internal bool IsCasting { get; set; }
        internal bool IsWalking { get; set; }
        internal bool IsBashing { get; set; }
        internal bool MapChanged { get; set; }
        internal bool HasLabor { get; set; }
        internal bool FullLabor { get; set; }
        internal bool OverrideMapFlags { get; set; }
        internal bool IsRegistered { get; set; } = true;
        internal bool IsCheckingBelt { get; set; }
        internal bool InventoryFull { get; set; }
        internal bool RecentlyDied { get; set; }
        internal bool ShouldEquipBow { get; set; }
        internal bool TrainingGroundsMember { get; set; }
        internal bool HasWalked { get; set; }
        internal bool CancelPressed { get; set; }
        internal bool AcceptPressed { get; set; }
        internal bool ExchangeOpen { get; set; }
        internal bool ExchangeClosing { get; set; }
        internal bool OkToBubble { get; set; } = false;
        internal bool ConfirmBubble { get; set; }
        internal bool IsStatusUpdated { get; set; }
        internal bool RecentlyCrashered { get; set; }
        internal bool BashingSkillsLoaded { get; set; } = false;
        internal bool UnmaxedSpellsLoaded { get; set; } = false;
        internal bool UnmaxedSkillsLoaded { get; set; } = false;
        internal bool ComboOneSet { get; set; } = false;
        internal bool ComboTwoSet { get; set; } = false;
        internal bool ComboThreeSet { get; set; } = false;
        internal bool DeformNearStrangers { get; set; } = false;
        internal bool Stopped { get; set; } = false;
        internal bool NeedsToRepairHammer { get; set; } = false;
        internal bool AssailNoise { get; set; } = true;
        internal bool Ladder { get; set; }
        internal bool ChestToggle { get; set; } = false;
        internal bool RaffleToggle { get; set; } = false;
        internal bool AscendTaskDone { get; set; }
        internal bool SuccHairDropped { get; set; }
        internal bool WarBagDeposited { get; set; }
        internal bool Depositing { get; set; }
        internal bool SpriteOverrideEnabled { get; set; }
        internal bool UnifiedGuildChat { get; set; }
        internal bool DialogOn { get; set; }
        internal int SpellCounter { get; set; }
        internal int Identifier { get; set; }
        internal int StuckCounter { get; set; }
        public int AlreadyCastMessageCount { get; set; } = 0;
        public int CurrentWaypoint { get; internal set; }
        internal uint ExchangeID { get; set; }
        internal uint PlayerID { get; set; }
        internal double WalkSpeed { get; set; } = 150;
        internal ushort SpriteOverride { get; set; } = 1;
        internal short PreviousMapID { get; set; }
        internal byte ComboScrollCounter { get; set; }
        internal byte Path { get; set; }
        internal byte StepCount { get; set; }
        internal System.Windows.Forms.Timer SpellTimer { get; set; }
        internal bool InArena
        {
            get
            {
                string mapName = Map?.Name;

                if (mapName == "Balanced Arena" || mapName == "Coliseum Circuit")
                {
                    return false;
                }

                if (mapName?.Contains("Arena") == true || mapName?.Contains("Loures Battle Ring") == true)
                {
                    return true;
                }

                return mapName?.Contains("Coliseum") == true;
            }
        }
        internal uint BaseHP { get; set; }
        internal uint BaseMP { get; set; }
        internal uint HealthPct
        {
            get
            {
                if (Stats.CurrentHP * 100 / Stats.MaximumHP <= 100)
                {
                    return (Stats.CurrentHP * 100 / Stats.MaximumHP);
                }
                return 100;
            }
        }
        internal uint ManaPct
        {
            get
            {
                if (Stats.CurrentMP * 100 / Stats.MaximumMP <= 100)
                {
                    return (Stats.CurrentMP * 100 / Stats.MaximumMP);
                }
                return 100;
            }
        }
        internal uint MaximumHP { get { return Stats.MaximumHP; } set { Stats.MaximumHP = value; } }
        internal uint MaximumMP { get { return Stats.MaximumMP; } set { Stats.MaximumMP = value; } }
        internal uint CurrentHP { get { return Stats.CurrentHP; } set { Stats.CurrentHP = value; } }
        internal uint CurrentMP { get { return Stats.CurrentMP; } set { Stats.CurrentMP = value; } }
        internal Element AttackElement { get { return Stats.OffenseElement; } set { Stats.OffenseElement = value; } }
        internal Element DefenseElement { get { return Stats.DefenseElement; } set { Stats.DefenseElement = value; } }
        internal byte UnspentPoints { get { return Stats.UnspentPoints; } set { Stats.UnspentPoints = value; } }
        internal uint Experience => Stats.Experience;
        internal uint AbilityExperience => Stats.AbilityExperience;
        internal uint Gold => Stats.Gold;
        internal byte Ability => Stats.Ability;
        internal byte Level => Stats.Level;
        internal uint ToNextLevel => Stats.ToNextLevel;
        internal bool HasLetter => Stats.Mail.HasFlag(Mail.HasLetter);
        internal bool HasParcel => Stats.Mail.HasFlag(Mail.HasParcel);
        internal bool IsSkulled => Player != null && (EffectsBar.Contains((ushort)Definitions.EffectsBar.Skull) || EffectsBar.Contains((ushort)Definitions.EffectsBar.WormSkull) && Player.IsSkulled);

        public bool ArcellaGift { get; internal set; }
        public bool ArcellaGiftOpen { get; internal set; }
        public bool Wdchest { get; internal set; }
        public bool Wdchestopen { get; internal set; }
        public bool Andorchest { get; internal set; }
        public bool Andorchestopen { get; internal set; }
        public bool Queenchest { get; internal set; }
        public bool Queenchestopen { get; internal set; }
        public bool Veltainchest { get; internal set; }
        public bool Heavychest { get; internal set; }
        public bool Smallbag { get; internal set; }
        public bool Smallbagopen { get; internal set; }
        public bool Bigbag { get; internal set; }
        public bool Bigbagopen { get; internal set; }
        public bool Heavybag { get; internal set; }
        public bool Heavybagopen { get; internal set; }
        public bool Atemeg { get; internal set; }
        public bool Ateabbox { get; internal set; }
        public bool Ateabgift { get; internal set; }
        public bool RequestingLabor { get; internal set; }
        public bool WaitingOnLabor { get; internal set; }
        public bool WaitingToRelaborAfterLaborFix { get; internal set; }
        public bool ategsf { get; internal set; }
        public bool ateclover { get; internal set; }

        internal Client(Server server, Socket socket)
        {
            Identifier = RandomUtils.Random(int.MaxValue);
            Server = server;
            Crypto = new Crypto(0, "UrkcnItnI");
            _clientSocket = socket;
            _serverSocket = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);
            _sendQueue = new Queue<Packet>();
            _receiveQueue = new Queue<Packet>();
            SpellTimer = new System.Windows.Forms.Timer
            {
                Interval = 1000
            };
            SpellTimer.Tick += SpellTimerTick;
            RouteFinder = new RouteFinder(Server, this);
            Stats = new Statistics();
            Bot = new Bot(this, server);
        }
        internal void SpellTimerTick(object sender, EventArgs e)
        {
            SpellCounter = 0;
        }
        internal void Remove()
        {
            ClientTab.RemoveClient();
            ClientTab = null;
        }

        internal bool HasEffect(EffectsBar effectID) => EffectsBar.Contains((ushort)effectID);
        internal void ClearEffect(EffectsBar effectID) => EffectsBar.Remove((ushort)effectID);
        internal bool GetMapFlags(MapFlags flagID) => MapFlags.HasFlag(flagID);
        internal void SetMapFlags(MapFlags flagID) => MapFlags |= flagID;
        internal void SetTemuairClass(TemuairClass temClass) => TemuairClassFlag |= temClass;
        internal void SetMedeniaClass(MedeniaClass medClass) => MedeniaClassFlag |= medClass;
        internal void SetPreviousClass(PreviousClass previousClass) => PreviousClassFlag |= previousClass;
        internal void SetDruidForm (DruidForm druidForm) => DruidFormFlag |= druidForm;
        internal void SetDugon(Dugon color) => DugonFlag |= color;
        internal bool GetCheats(Cheats value) => _cheats.HasFlag(value);
        internal void EnableCheats(Cheats value) => _cheats |= value;
        internal void DisableCheats(Cheats value) => _cheats &= (Cheats)(byte)(~(uint)value);
        internal void SetStatUpdateFlags(StatUpdateFlags flags) => Attributes(flags, Stats);
        internal bool HasItem(string itemName) => Inventory.Contains(itemName);
        internal bool HasSkill(string skillName) => Skillbook[skillName] != null;
        internal bool HasSpell(string spellName) => Spellbook[spellName] != null;
        internal int CalculateHealAmount(string spellName)
        {
            int num = (Stats.CurrentWis >= 99) ? Stats.CurrentWis : 99;
            uint fnvHash = HashingUtils.CalculateFNV(spellName);

            switch (fnvHash)
            {
                case 301833330: //Spirit Essence
                    return 2000000;

                case 2360874113: //beag ioc
                    return 1056 - (255 - num) * 6;

                case 2431366422: //ioc
                case 1586538930: //ioc comlha
                    return 8800 - (255 - num) * 50;

                case 2358017708: //mor ioc comlha:
                case 1812078524: //mor ioc
                    return 26400 - (255 - num) * 150;

                case 1544215329: //ard ioc comlha
                case 4118165127: //ard ioc
                    return 52800 - (255 - num) * 300;

                case 3783935686: //nuadhaich
                case 1649558369: //Nuadhiach Le Cheile
                    return 88000 - (255 - num) * 500;

                case 1445356977: //Leigheas
                    return 264000 - (255 - num) * 1000;

                case 4167026527: //Cold Blood
                    return 500 * Ability;

                default:
                    return 0;
            }
        }
        internal int GetItemQuantity(string itemName)
        {
            int quantity = 0;
            foreach (Item item in Inventory)
            {
                if (item != null && item.Name.Equals(itemName, StringComparison.CurrentCultureIgnoreCase))
                {
                    quantity += item.Quantity;
                }
            }
            return quantity;
        }
        internal bool CanUseItem(Item item)
        {
            if (!EffectsBar.Contains((ushort)Definitions.EffectsBar.Pramh) || !EffectsBar.Contains((ushort)Definitions.EffectsBar.Suain))
                return true;

            return false;
        }
        internal bool CanUseSkill(Skill skill)
        {
            if (skill == null) 
            { 
                return false; 
            }

            if (!skill.CanUse)
            {
                //Console.WriteLine($"[DEBUG] Skill {skill.Name} cannot be used because it is on cooldown.");
                return false;
            }

            if (!Map.CanUseSkills)
            {
                //Console.WriteLine($"[DEBUG] Skills cannot be used on this map (Map.CanUseSkills is false).");
                return false;
            }

            if (EffectsBar.Contains((ushort)Definitions.EffectsBar.Pramh))
            {
                //Console.WriteLine($"[DEBUG] Cannot use skill {skill.Name} because Pramh effect is active.");
                return false;
            }

            if (EffectsBar.Contains((ushort)Definitions.EffectsBar.Suain))
            {
                //Console.WriteLine($"[DEBUG] Cannot use skill {skill.Name} because Suain effect is active.");
                return false;
            }

            return true;
        }



        internal bool CanUseSpell(Spell spell, Creature creature = null)
        {
            if (spell.CanUse && Map.CanUseSpells)
            {
                if (EffectsBar.Contains((ushort)Definitions.EffectsBar.Pramh) || EffectsBar.Contains((ushort)Definitions.EffectsBar.Suain))
                    return AoSuainHashSet.Contains(spell.Name);

                return true; // If neither Pramh nor Suain is active, always return true
            }
            return false;
        }
        internal bool NumberedSkill(string skillName)
        {
            for (int i = 20; i > 0; i--)
            {
                if (UseSkill($"{skillName} {i}"))
                    return true;
            }
            return false;
        }

        internal bool NumberedSpell(string spellName, Creature target = null, bool autoStaff = true, bool wait = true)
        {
            for (int i = 20; i > 0; --i)
            {
                if (UseSpell(spellName + " " + i.ToString(), target, autoStaff, wait))
                    return true;
            }
            return false;
        }

        internal void UseHammer()
        {
            Bot._dontWalk = true;
            Bot._dontCast = true;
            Bot._dontBash = true;

            var repairItem = Inventory.FirstOrDefault(i => i.Name.Equals("Equipment Repair", StringComparison.OrdinalIgnoreCase));

            if (repairItem == null)
            {
                ServerMessage((byte)ServerMessageType.OrangeBar1, "You do not have any Equipment Repair hammers!");
                ClientTab.equipmentrepairCbox.Checked = false;
                Bot._dontWalk = false;
                Bot._dontCast = false;
                Bot._dontBash = false;
            }
            else
            {
                if (!UseItem("Equipment Repair"))
                    return;

                Utility.Timer hammer = Utility.Timer.FromSeconds(5);

                while (Dialog == null)
                {
                    if (hammer.IsTimeExpired || Player.IsSuained || Player.IsAsleep)
                        return;
                    Thread.Sleep(25);
                }

                ReplyDialog(Dialog.ObjectType, Dialog.ObjectID, Dialog.PursuitID, (ushort)(Dialog.DialogID + 1U));
                NeedsToRepairHammer = false;
                Bot._hammerTimer = DateTime.UtcNow;
                Bot._dontWalk = false;
                Bot._dontCast = false;
                Bot._dontBash = false;
            }
        }
        internal List<GroundItem> GetNearbyGroundItems(int distance = 12, params ushort[] sprites)
        {
            var spriteSet = new HashSet<ushort>(sprites);
            var nearbyGroundItems = new List<GroundItem>();

            if (Monitor.TryEnter(Server.SyncObj, 150))
            {
                try
                {
                    foreach (var nearbyGroundItem in NearbyGroundItems)
                    {

                        if (WorldObjects[nearbyGroundItem] is GroundItem groundItem
                            && WithinRange(groundItem, distance)
                            && spriteSet.Contains(groundItem.SpriteID))
                        {
                            nearbyGroundItems.Add(groundItem);
                        }
                    }
                }
                finally
                {
                    Monitor.Exit(Server.SyncObj);
                }
            }

            return nearbyGroundItems;
        }
        internal List<GroundItem> GetNearbyGroundItems(int distance = 12)
        {
            if (!Monitor.TryEnter(Server.SyncObj, 1000))
            {
                return new List<GroundItem>();
            }
            try
            {
                return WorldObjects.Values
                    .OfType<GroundItem>()
                    .Where(obj => obj.GetType() == typeof(Objects.GroundItem))
                    .Where(obj => ServerLocation.DistanceFrom(obj.Location) <= distance)
                    .ToList();
            }
            finally
            {
                Monitor.Exit(Server.SyncObj);
            }
        }
        internal Player GetNearbyPlayer(string name)
        {
            if (Monitor.TryEnter(Server.SyncObj, 300))
            {
                try
                {
                    return (!NearbyPlayers.ContainsKey(name)) ? null : NearbyPlayers[name];
                }
                finally
                {
                    Monitor.Exit(Server.SyncObj);
                }
            }
            return null;
        }
        internal List<Player> GetNearbyPlayers()
        {
            List<Player> nearbyPlayers = new List<Player>();
            if (Monitor.TryEnter(Server.SyncObj, 150))
            {
                try
                {
                    nearbyPlayers = NearbyPlayers.Values
                        .Where(p => !string.IsNullOrEmpty(p.Name))
                        .ToList();
                }
                finally
                {
                    Monitor.Exit(Server.SyncObj);
                }
            }
            //foreach (var p in nearbyPlayers)
            //{
            //    Console.WriteLine("NearbyPlayer: " + p.Name);
            //}
            return nearbyPlayers;
        }
        internal List<Player> GetNearbyGroupedPlayers()
        {

            if (!Monitor.TryEnter(Server.SyncObj, 1000))
            {
                return new List<Player>();
            }
            try
            {
                return NearbyPlayers.Values
                    .Where(player => GroupedPlayers.Contains(player.Name))
                    .ToList();
            }
            finally
            {
                Monitor.Exit(Server.SyncObj);
            }
        }
        internal Creature GetNearbyNPC(string name)
        {
            if (Monitor.TryEnter(Server.SyncObj, 300))
            {
                try
                {
                    return (!NearbyNPC.ContainsKey(name)) ? null : NearbyNPC[name];
                }
                finally
                {
                    Monitor.Exit(Server.SyncObj);
                }
            }
            return null;
        }
        internal List<Creature> GetNearbyNPCs()
        {
            if (Monitor.TryEnter(Server.SyncObj, 150))
            {
                try
                {
                    return NearbyNPC.Values.ToList();
                }
                finally
                {
                    Monitor.Exit(Server.SyncObj);
                }
            }

            // Return an empty list if unable to acquire lock
            return new List<Creature>();
        }
        internal List<WorldObject> GetNearbyObjects()
        {
            return WorldObjects.Values.Where(wo => NearbyObjects.Contains(wo.ID)).ToList();
        }
        internal List<Location> GetWarpPoints(Location location)
        {
            if (!Server._maps.TryGetValue(location.MapID, out Map value))
            {
                return new List<Location>();
            }

            var exits = value.Exits
                .Where(item => !location.Point.Equals(item.Key))
                .Select(item => new Location(location.MapID, item.Key))
                .ToList();

            exits.AddRange(value.WorldMaps
                .Where(item => !location.Point.Equals(item.Key))
                .Select(item => new Location(location.MapID, item.Key)));

            return exits;
        }

        internal HashSet<Location> GetAllWarpPoints()
        {
            HashSet<Location> allWarpPoints = new HashSet<Location>();

            if (Server._maps.TryGetValue(Map.MapID, out Map map))
            {
                foreach (var exit in map.Exits)
                {
                    allWarpPoints.Add(new Location(Map.MapID, exit.Key));
                }

                foreach (var worldMap in map.WorldMaps)
                {
                    allWarpPoints.Add(new Location(Map.MapID, worldMap.Key));
                }
            }

            return allWarpPoints;
        }




        internal List<Creature> GetNearbyValidCreatures(int distance = 12)
        {
            var whiteList = new HashSet<ushort>();
            List<Creature> creatureList = new List<Creature>();
            if (!Monitor.TryEnter(Server.SyncObj, 1000))
            {
                return creatureList;
            }

            try
            {
                var validCreatures = GetNearbyObjects().OfType<Creature>().Where(creature => IsValidCreature(creature, distance));
                creatureList.AddRange(validCreatures);

                if (creatureList.Count == 0) return creatureList;

                if (CONSTANTS.WHITELIST_BY_MAP_ID.ContainsKey((ushort)Map.MapID) ||
                    CONSTANTS.WHITELIST_BY_MAP_NAME.Any(kv => Map.Name.StartsWith(kv.Key)))
                {
                    whiteList = GetWhiteLists();
                    creatureList = creatureList.Where(creature => IsCreatureAllowed(creature, whiteList)).ToList();
                }

                return creatureList;
            }
            finally
            {
                Monitor.Exit(Server.SyncObj);
            }
        }
        private HashSet<ushort> GetWhiteLists()
        {
            var whiteList = new HashSet<ushort>();
            if (CONSTANTS.WHITELIST_BY_MAP_ID.TryGetValue((ushort)Map.MapID, out var whiteListByMapID))
            {
                whiteList.UnionWith(whiteListByMapID);
            }

            var whiteListByMapName = CONSTANTS.WHITELIST_BY_MAP_NAME.FirstOrDefault(kv => Map.Name.StartsWith(kv.Key)).Value;
            if (whiteListByMapName != null)
            {
                whiteList.UnionWith(whiteListByMapName);
            }

            return whiteList;
        }
        private bool IsValidCreature(Creature creature, int distance)
        {
            int mapID = Map.MapID;

            // Allow sprite 492 only on map 6999
            if (creature.SpriteID == 492 && mapID == 6999)
            {
                return creature.Type < CreatureType.Merchant && creature.SpriteID > 0 && creature.SpriteID <= 1000 && WithinRange(creature, distance);
            }

            return creature.Type < CreatureType.Merchant && creature.SpriteID > 0 && creature.SpriteID <= 1000 &&
                !CONSTANTS.INVISIBLE_SPRITES.Contains(creature.SpriteID) &&
                !CONSTANTS.UNDESIRABLE_SPRITES.Contains(creature.SpriteID) && WithinRange(creature, distance);
        }
        internal List<Creature> GetAllNearbyMonsters(int distance = 12)
        {
            List<Creature> list = new List<Creature>();
            if (Monitor.TryEnter(Server.SyncObj, 1000))
            {
                try
                {
                    foreach (Creature creature in GetNearbyObjects().OfType<Creature>())
                    {
                        if (IsValidCreature(creature, distance))
                        {
                            list.Add(creature);
                        }
                    }
                    return list;
                }
                finally
                {
                    Monitor.Exit(Server.SyncObj);
                }
            }
            return list;
        }
        internal List<Location> GetAdjacentPoints(Creature creature)
        {
            return new List<Location>
            {
                new Location(creature.Location.MapID, (short)(creature.Location.X - 1), creature.Location.Y),
                new Location(creature.Location.MapID, creature.Location.X, (short)(creature.Location.Y + 1)),
                new Location(creature.Location.MapID, creature.Location.X, (short)(creature.Location.Y - 1)),
                new Location(creature.Location.MapID, (short)(creature.Location.X + 1), creature.Location.Y)
            };
        }
        private Location GetValidLocationNearTarget(Location targetLocation, short followDistance)
        {
            List<Location> potentialLocations = new List<Location>();

            // Check exactly followDistance tiles away in each direction (Up, Down, Left, Right)
            short[] dx = { followDistance, (short)-followDistance, 0, 0 };
            short[] dy = { 0, 0, followDistance, (short)-followDistance };

            //Console.WriteLine($"Checking cardinal directions around target: {targetLocation}, followDistance: {followDistance}");

            // Try to find valid locations in the cardinal directions
            for (int i = 0; i < 4; i++)
            {
                Location potentialLocation = new Location(
                    targetLocation.MapID,
                    (short)(targetLocation.X + dx[i]),
                    (short)(targetLocation.Y + dy[i])
                );


                //Console.WriteLine($"Checking cardinal direction location: {potentialLocation}");

                // Check if the location is valid and walkable
                if (IsWalkable(potentialLocation))
                {
                    //Console.WriteLine($"Location {potentialLocation} is walkable.");
                    potentialLocations.Add(potentialLocation);
                }
                else
                {
                    //Console.WriteLine($"Location {potentialLocation} is NOT walkable.");
                }
            }

            // Return the first valid location found in the cardinal directions
            if (potentialLocations.Any())
            {
                //Console.WriteLine($"Returning valid cardinal direction location: {potentialLocations.First()}");
                return potentialLocations.First();
            }

            // As a fallback, calculate diagonal movements exactly followDistance away
            //Console.WriteLine($"No valid cardinal locations found. Checking diagonals...");

            for (short xOffset = (short)-followDistance; xOffset <= followDistance; xOffset++)
            {
                for (short yOffset = (short)-followDistance; yOffset <= followDistance; yOffset++)
                {
                    if (Math.Abs(xOffset) == followDistance || Math.Abs(yOffset) == followDistance)
                    {
                        Location diagonalLocation = new Location(
                            targetLocation.MapID,
                            (short)(targetLocation.X + xOffset),
                            (short)(targetLocation.Y + yOffset)
                        );


                        //Console.WriteLine($"Checking diagonal location: {diagonalLocation}");

                        // Check if the diagonal location is walkable
                        if (IsWalkable(diagonalLocation))
                        {
                            //Console.WriteLine($"Diagonal location {diagonalLocation} is walkable.");
                            potentialLocations.Add(diagonalLocation);
                        }
                        else
                        {
                            //Console.WriteLine($"Diagonal location {diagonalLocation} is NOT walkable.");
                        }
                    }
                }
            }

            // If valid diagonal locations were found, return the first one
            if (potentialLocations.Any())
            {
                //Console.WriteLine($"Returning valid diagonal location: {potentialLocations.First()}");
                return potentialLocations.First();
            }

            // If no valid locations were found, return the original target location
            //Console.WriteLine($"No valid locations found. Returning original target location: {targetLocation}");
            return targetLocation;
        }
        internal List<Location> BoroArea1(Creature creature)
        {
            if (HasEffect(Definitions.EffectsBar.Hide))
            {
                return new List<Location>();
            }
            return new List<Location>
            {
                new Location(creature.Location.MapID, new Point((short)(creature.Location.X - 2), creature.Location.Y)),
                new Location(creature.Location.MapID, new Point((short)(creature.Location.X - 1), (short)(creature.Location.Y + 1))),
                new Location(creature.Location.MapID, new Point((short)(creature.Location.X - 1), creature.Location.Y)),
                new Location(creature.Location.MapID, new Point((short)(creature.Location.X - 1), (short)(creature.Location.Y - 1))),
                new Location(creature.Location.MapID, new Point(creature.Location.X, (short)(creature.Location.Y + 2))),
                new Location(creature.Location.MapID, new Point(creature.Location.X, (short)(creature.Location.Y + 1))),
                new Location(creature.Location.MapID, new Point(creature.Location.X, (short)(creature.Location.Y - 1))),
                new Location(creature.Location.MapID, new Point(creature.Location.X, (short)(creature.Location.Y - 2))),
                new Location(creature.Location.MapID, new Point((short)(creature.Location.X + 1), (short)(creature.Location.Y + 1))),
                new Location(creature.Location.MapID, new Point((short)(creature.Location.X + 1), creature.Location.Y)),
                new Location(creature.Location.MapID, new Point((short)(creature.Location.X + 1), (short)(creature.Location.Y - 1))),
                new Location(creature.Location.MapID, new Point((short)(creature.Location.X + 2), creature.Location.Y))
            };
        }
        internal List<Creature> GetAllNearbyMonsters(int distance = 12, params ushort[] creatureArray)
        {
            var creatureList = new List<Creature>();
            var hashSet = new HashSet<ushort>(creatureArray);

            lock (Server.SyncObj)
            {
                foreach (var creature in GetNearbyObjects().OfType<Creature>())
                {
                    // Allow sprite 492 only on map 6999
                    if (creature.SpriteID == 492 && Map.MapID != 6999)
                    {
                        continue;
                    }

                    if ((creature.Type == CreatureType.Normal || creature.Type == CreatureType.WalkThrough)
                        && WithinRange(creature, distance)
                        && creature.SpriteID > 0 && creature.SpriteID <= 1000
                        && !CONSTANTS.INVISIBLE_SPRITES.Contains(creature.SpriteID)
                        && !CONSTANTS.UNDESIRABLE_SPRITES.Contains(creature.SpriteID)
                        && hashSet.Contains(creature.SpriteID))
                    {
                        creatureList.Add(creature);
                    }
                }
            }

            return creatureList;
        }


        internal void UseExperienceGem(byte choice)
        {
            Bot._dontWalk = true;
            if (!UseItem("Experience Gem"))
            {
                ServerMessage(1, "You do not have any experience gems.");
                ClientTab.autoGemCbox.Checked = false;
                return;
            }
            while (Dialog == null)
            {
                Thread.Sleep(25);
            }
            byte type = Dialog.ObjectType;
            int objID = Dialog.ObjectID;
            ushort pursuitID = Dialog.PursuitID;
            ushort dialogID = Dialog.DialogID;
            Dialog.DialogNext();
            ReplyDialog(type, objID, pursuitID, (ushort)(dialogID + 1));
            ReplyDialog(type, objID, pursuitID, (ushort)(dialogID + 1), choice);
            ReplyDialog(type, objID, pursuitID, (ushort)(dialogID + 1));
            ReplyDialog(type, objID, pursuitID, (ushort)(dialogID + 1));
            ReplyDialog(type, objID, pursuitID, (ushort)(dialogID + 1));
            Thread.Sleep(1000);
            while (Dialog == null)
            {
                Thread.Sleep(25);
            }
            type = Dialog.ObjectType;
            objID = Dialog.ObjectID;
            pursuitID = Dialog.PursuitID;
            dialogID = Dialog.DialogID;
            ReplyDialog(type, objID, pursuitID, (ushort)(dialogID + 1));
            ReplyDialog(type, objID, pursuitID, (ushort)(dialogID + 1), 2);
            ReplyDialog(type, objID, pursuitID, dialogID);
            Bot._lastUsedGem = DateTime.UtcNow;
            Bot._dontWalk = false;
        }
        private bool IsValidSpell(Client client, string spellName, Creature creature)
        {
            // Guard clause: Reject spell if Suain effect is active and spell is not allowed
            // Maybe we should check if pramh'd too?
            if (ShouldRejectSpellDueToSuain(client, spellName))
            {
                return false;
            }

            // Guard clause: Make sure we aren't in Dojo
            if (!Map.Name.Contains("Training Dojo"))
            {
                // Reject spell based on spell name
                // Check whether this is needed. We already check for spell == null in the parent method
                //if (ShouldRejectSpellDueToSpellName(spellName))
                //{
                //    return false;
                //}

                // Check if the creature already has the given spell
                if (DoesCreatureHaveSpellAlready(spellName, creature, client))
                {
                    return false;
                }
            }
            //Console.WriteLine($"[IsValidSpell] Spell {spellName} on Creature ID: {creature?.ID} is valid.");
            return true;
        }
        internal bool ReadyToSpell(string spell)
        {
            try
            {
                uint num = HashingUtils.CalculateFNV(spell);
                switch (num)
                {
                    case 420187390: // beag fas nadur
                    case 2476745328: // fas nadur
                    case 1149628551: // mor fas nadur
                    case 107956092: // ard fas nadur
                        if (!CastedTarget.IsFassed) return true;
                        return false;

                    case 2848971440: // beag cradh
                    case 1154413499: // cradh
                    case 1281358573: // mor cradh
                    case 2118188214: // ard cradh
                    case 1928539694: // Dark Seal
                    case 219207967: // Darker Seal
                    case 4252225073: // Demon Seal
                    case 928817768: // Demise
                        if (!CastedTarget.IsCursed) return true;
                        return false;

                    case 2112563240: // beag naomh aite
                    case 291448073: // naomh aite
                    case 2761324515: // mor naomh aite
                    case 443271170: // ard naomh aite
                        if (!CastedTarget.IsAited) return true;
                        return false;

                    case 195270534: // Wake Scroll
                        if (spell == "Wake Scroll")
                        {
                            foreach (Player player in GetNearbyGroupedPlayers())
                            {
                                player.AnimationHistory[(ushort)SpellAnimation.Mesmerize] = DateTime.MinValue;
                                player.AnimationHistory[(ushort)SpellAnimation.Pramh] = DateTime.MinValue;
                            }
                        }
                        return false;

                    case 810175405: // ao suain
                    case 894297607: // Leafhopper Chirp
                        CastedTarget.AnimationHistory[(ushort)SpellAnimation.Suain] = DateTime.MinValue;
                        return false;

                    case 1046347411: // suain
                        if (CastedTarget.IsSuained)
                        {
                            Console.WriteLine("ReadyToSpell: Creature is already suained, returning false");
                            return false;
                        }
                        else
                        {
                            Console.WriteLine("ReadyToSpell: Creature is not suained, can cast Pramh, returning true");
                            return true;
                        }

                    case 2030226177: // armachd
                        if (!CastedTarget.HasArmachd) return true;
                        return false;

                    case 3219892635: // beag pramh
                    case 2647647615: // pramh
                    case 2592944103: // Mesmerize
                        if (CastedTarget.IsAsleep)
                        {
                            Console.WriteLine("ReadyToSpell: Creature is already asleep, returning false");
                            return false;
                        }
                        else
                        {
                            Console.WriteLine("ReadyToSpell: Creature is not asleep, can cast Pramh, returning true");
                            return true;
                        }

                    case 2756163491: // Fungus Beetle Extract
                        foreach (Player player in GetNearbyGroupedPlayers())
                        {
                            player.AnimationHistory[(ushort)SpellAnimation.PinkPoison] = DateTime.MinValue;
                            player.AnimationHistory[(ushort)SpellAnimation.GreenBubblePoison] = DateTime.MinValue;
                            player.AnimationHistory[(ushort)SpellAnimation.MedeniaPoison] = DateTime.MinValue;
                        }
                        return false;

                    case 674409180: // Lyliac Plant
                    case 2793184655: // Lyliac Vineyard
                        Bot._needFasSpiorad = true;
                        return false;

                    case 2996522388: //ao puinsein
                        {
                            CastedTarget.AnimationHistory[(ushort)SpellAnimation.PinkPoison] = DateTime.MinValue;
                            CastedTarget.AnimationHistory[(ushort)SpellAnimation.GreenBubblePoison] = DateTime.MinValue;
                            CastedTarget.AnimationHistory[(ushort)SpellAnimation.MedeniaPoison] = DateTime.MinValue;
                        }
                        return false;

                    case 3134427575: // Frost Arrow 1
                    case 3151205194: // Frost Arrow 2
                    case 3167982813: // Frost Arrow 3
                    case 3050539480: // Frost Arrow 4
                    case 3067317099: // Frost Arrow 5
                    case 3084094718: // Frost Arrow 6
                    case 3100872337: // Frost Arrow 7
                    case 2983429004: // Frost Arrow 8
                    case 3000206623: // Frost Arrow 9
                    case 2718832517: // Frost Arrow 10
                    case 2702054898: // Frost Arrow 11
                        if (CastedTarget.IsFrozen)
                        {
                            Console.WriteLine("ReadyToSpell: Creature is already asleep, returning false");
                            return false;
                        }
                        else
                        {
                            Console.WriteLine("ReadyToSpell: Creature is not asleep, can cast Frost Arrow, returning true");
                            return true;
                        }
                    case 2292268700: // Cursed Tune 1
                    case 2342601557: // Cursed Tune 2
                    case 2325823938: // Cursed Tune 3
                    case 2241935843: // Cursed Tune 4
                    case 2225158224: // Cursed Tune 5
                    case 2275491081: // Cursed Tune 6
                    case 2258713462: // Cursed Tune 7
                    case 2443267271: // Cursed Tune 8
                    case 2426489652: // Cursed Tune 9
                    case 3252005060: // Cursed Tune 10
                    case 3268782679: // Cursed Tune 11
                    case 3285560298: // Cursed Tune 12
                        if (CastedTarget.HasCursedTunes)
                        {
                            Console.WriteLine("ReadyToSpell: Creature already has CT, returning false");
                            return false;
                        }
                        else
                        {
                            Console.WriteLine("ReadyToSpell: Creature does not have CT, can cast CT, returning true");
                            return true;
                        }


                    default:
                        return true;
                }
            }
            catch
            {
                return true;
            }
        }
        private bool ShouldRejectSpellDueToSuain(Client client, string spellName)
        {
            return (EffectsBar.Contains((ushort)Definitions.EffectsBar.Suain) &&
                   (client == null || !IsAllowedSuainSpell(spellName)));
        }
        private bool IsAllowedSuainSpell(string spellName)
        {
            return spellName.Equals("ao suain", StringComparison.CurrentCultureIgnoreCase) ||
                   spellName.Equals("Leafhopper Chirp", StringComparison.CurrentCultureIgnoreCase);
        }
        private bool ShouldRejectSpellDueToSpellName(string spellName)
        {
            uint spellHash = HashingUtils.CalculateFNV(spellName);

            switch (spellHash)
            {
                case 107956092: // ard fas nadur
                case 219207967: // Darker Seal
                case 4252225073: //Demon Seal
                case 291448073: // naomh aite
                case 420187390: // beag fas nadur
                case 443271170: // ard naomh aite
                case 810175405: // ao suain
                case 928817768: // Demise

                case 3777649476: // beag pramh
                case 1046347411: // pramh

                case 2848971440: // beag cradh
                case 1149628551: // cradh
                case 2118188214: // ard cradh


                case 1154413499: // mor fas nadur
                case 1928539694: // Dark Seal
                case 2112563240: // beag naomh aite

                case 2454795333: // fas nadur
                case 2579487986: // Mesmerize
                case 2647647615: // pramh
                case 2761324515: // mor naomh aite

                case 3000206623: // Frost Arrow 9
                case 3050539480: // Frost Arrow 4
                case 3067317099: // Frost Arrow 5
                case 3084094718: // Frost Arrow 6
                case 3100872337: // Frost Arrow 7
                case 3134427575: // Frost Arrow 1
                case 3151205194: // Frost Arrow 2
                case 3635920463: // fas spiorad

                    return false;
                default:
                    return true;
            }
        }
        private bool DoesCreatureHaveSpellAlready(string spellName, Creature creature, Client client)
        {
            if (creature == null)
            {
                return false;
            }

            switch (spellName)
            {
                case "suain":
                    //Console.WriteLine($"[DoesCreatureHaveSpellAlready] Checking {spellName} for Creature ID: {creature.ID}, Creature Name: {creature.Name}, Hash: {creature.GetHashCode()}, Currently Suained: {creature.IsSuained}");
                    return creature.IsSuained;
                case "beag cradh":
                case "cradh":
                case "mor cradh":
                case "ard cradh":
                case "Dark Seal":
                case "Darker Seal":
                case "Demise":
                case "Demon Seal":
                    //Console.WriteLine($"[DoesCreatureHaveSpellAlready] Checking {spellName} for Creature ID: {creature.ID}, Creature Name: {creature.Name}, Hash: {creature.GetHashCode()} Currently Cursed: {creature.IsCursed}");
                    return creature.IsCursed;

                case "Frost Arrow 1":
                case "Frost Arrow 2":
                case "Frost Arrow 3":
                case "Frost Arrow 4":
                case "Frost Arrow 5":
                case "Frost Arrow 6":
                case "Frost Arrow 7":
                case "Frost Arrow 8":
                case "Frost Arrow 9":
                case "Frost Arrow 10":
                    return creature.IsFrozen;
                case "beag pramh":
                case "pramh":
                case "Mesmerize":
                    //Console.WriteLine($"[DoesCreatureHaveSpellAlready] Checking {spellName} for Creature ID: {creature.ID}, Hash: {creature.GetHashCode()}, Currently Asleep: {creature.IsAsleep}");
                    return creature.IsAsleep;
                case "fas spiorad":
                    return !Bot._needFasSpiorad && !Bot._manaLessThanEightyPct;
                case "beag fas nadur":
                case "fas nadur":
                case "mor fas nadur":
                case "ard fas nadur":
                    //Console.WriteLine($"[DoesCreatureHaveSpellAlready] Checking {spellName} for Creature ID: {creature.ID}, Currently Fassed: {creature.IsFassed}");
                    return creature.IsFassed;
                case "ao suain":
                    return creature.IsSuained;
                case "beag naomh aite":
                case "naomh aite":
                case "mor naomh aite":
                case "ard naomh aite":
                    return creature.IsAited;
                default:
                    return false;
            }
        }
        
        internal bool WaitForSpellChant()
        {
            Timer timer = Timer.FromMilliseconds(1500);
            while (CastedSpell != null)
            {
                if (timer.IsTimeExpired)
                {
                    CastedSpell = null;
                    LastSpell = null;
                    return false;
                }
                Thread.Sleep(5);
            }
            return true;
        }
        
        internal void SeeGhosts(Player player)
        {
            player.NakedPlayer();
            player.HeadColor = 1;
            player.BodySprite = 48;
            DisplayAisling(player);
            DisplayEntityRequest(player.ID);
        }
        private void UpdateClientActionText(string text)
        {
            if (ClientTab.InvokeRequired)
            {
                ClientTab.Invoke(new Action(() => ClientTab.currentAction.Text = text));
            }
            else
            {
                ClientTab.currentAction.Text = text;
            }
        }
        private bool UseOptimalStaff(Spell spell, out byte castLines)
        {
            bool swappingWeapons = false;
            castLines = spell.CastLines;

            Item obj = EquippedItems[1];
            Bow bow = (obj != null && obj.IsBow) ? EquippedItems[1].ThisBow : new Bow();
            Staff staff = (obj != null && obj.IsStaff) ? EquippedItems[1].ThisStaff : new Staff();
            MeleeWeapon meleeWeapon = (obj != null && obj.IsMeleeWeapon) ? EquippedItems[1].ThisWeapon : new MeleeWeapon();

            bool hasArcherSpells = CONSTANTS.ARCHER_SPELLS.Any(spellName => spell.Name.Contains(spellName) || spell.Name.Equals(spellName, StringComparison.InvariantCultureIgnoreCase));
            DateTime utcNow = DateTime.UtcNow;
            if (hasArcherSpells && int.TryParse(Skillbook.SkillbookDictionary.Keys.FirstOrDefault((string string_0) => string_0.Contains("Archery ")).Replace("Archery ", ""), out int currentArcherySkill))
            {
                var equippedBow = EquippedItems[1]?.ThisBow;
                var bestBow = Inventory
                    .Where(i => i.IsBow
                             && i.ThisBow.CanUse(Ability, currentArcherySkill)
                             && (equippedBow == null || i.ThisBow.AbilityRequired > equippedBow.AbilityRequired))
                    .Select(i => i.ThisBow)
                    .OrderByDescending(b => b.AbilityRequired)
                    .FirstOrDefault();

                if (bestBow != null)
                {
                    string bowName = bestBow.Name;
                    if (equippedBow?.Name.Equals(bowName, StringComparison.CurrentCultureIgnoreCase) == true)
                    {
                        return true;
                    }

                    RemoveShield();
                    //Console.WriteLine($"Equipping {bowName} to cast {spell.Name}");
                    UseItem(bowName);

                    while (EquippedItems[1]?.Name?.Equals(bowName, StringComparison.CurrentCultureIgnoreCase) != true)
                    {
                        double elapsedSeconds = DateTime.UtcNow.Subtract(utcNow).TotalSeconds;

                        if (elapsedSeconds <= 2.0)
                        {
                            UpdateClientActionText($"{Action} Swapping to {bestBow.Name}");
                            // Thread.Sleep(5);
                            continue;
                        }

                        return false;
                    }
                }
            }
            else
            {
                Item bestStaff = null;

                var candidates = Inventory
                    .Where(item => item.IsStaff &&
                                   item.ThisStaff.CanUse(Ability, Level, ToNextLevel, TemuairClassFlag) &&
                                   item.ThisStaff.CastLines.TryGetValue(spell.Name, out byte lines) &&
                                   lines < spell.CastLines)
                    .ToList();

                if (candidates.Count == 0)
                {
                    //Console.WriteLine("No usable staff with better CastLines.");
                }
                else if (candidates.Count == 1)
                {
                    bestStaff = candidates[0];
                    //Console.WriteLine($"Only one candidate with better CastLines: {bestStaff}");
                }
                else
                {
                    bestStaff = candidates
                        .OrderByDescending(item => item.ThisStaff.AbilityRequired)
                        .ThenByDescending(item => item.ThisStaff.InsightRequired)
                        .ThenByDescending(item => item.ThisStaff.MasterRequired)
                        .First();

                    //Console.WriteLine($"Multiple candidates found. Selected best staff: {bestStaff}");
                }

                if (bestStaff != null)
                {
                    staff = bestStaff.ThisStaff;
                    swappingWeapons = true;
                }

                if (staff.Name == new Staff().Name)
                {
                    if (Spellbook[spell.Name].CastLines <= Staffs[0].CastLines[spell.Name])
                    {
                        return true;
                    }
                    staff = Staffs[0];
                }

                if (swappingWeapons)
                {
                    RemoveShield();

                    if (staff.Name != "Barehand")
                    {
                        //Console.WriteLine($"Equipping {staff.Name} to cast {spell.Name}");
                        UseItem(staff.Name);
                    }

                    while (Spellbook[spell.Name]?.CastLines != staff.CastLines[spell.Name])
                    {
                        double elapsedSeconds = DateTime.UtcNow.Subtract(utcNow).TotalSeconds;

                        // Ensure the swap operation doesn't exceed 2 seconds
                        if (elapsedSeconds <= 2.0)
                        {
                            UpdateClientActionText($"{Action} Swapping to {staff.Name}");

                            // Thread.Sleep(5);
                            continue;
                        }

                        return false;
                    }

                    Thread.Sleep(100);
                }
            }
            castLines = Spellbook[spell.Name].CastLines;
            return true;
        }
        internal void NewAisling(byte objType, int objID, ushort pursuitID)
        {
            ReplyDialog(objType, objID, pursuitID, 52);
            Thread.Sleep(500);
            ReplyDialog(objType, objID, pursuitID, 66);
            Thread.Sleep(500);
            ReplyDialog(objType, objID, pursuitID, 69);
            Thread.Sleep(500);
            ReplyDialog(objType, objID, pursuitID, 72);
            Thread.Sleep(500);
            ReplyDialog(objType, objID, pursuitID, 75);
            //this.client.Tasks.Stop();
            Thread.Sleep(3000);
            //this.client.Tasks.Start();
        }
        internal void LoadMeleeWeapons()
        {
            Weapons.AddRange(WeaponRegistry.MeleeWeapons.Values);

            foreach (Item i in Inventory)
            {
                if (WeaponRegistry.MeleeWeapons.TryGetValue(i.Name, out MeleeWeapon matchingWeapon))
                {
                    i.IsMeleeWeapon = true;
                    i.ThisWeapon = matchingWeapon;
                }
            }
        }
        internal void LoadStavesAndBows()
        {
            Dictionary<string, byte> minusOneLine = new Dictionary<string, byte>(StaffSpells);
            Dictionary<string, byte> minusTwoLines = new Dictionary<string, byte>(StaffSpells);
            Dictionary<string, byte> masterOneLine = new Dictionary<string, byte>(StaffSpells);
            Dictionary<string, byte> oneLine = new Dictionary<string, byte>(StaffSpells);
            Dictionary<string, byte> masterPriest = new Dictionary<string, byte>(StaffSpells);
            Dictionary<string, byte> cradhZeroLine = new Dictionary<string, byte>(StaffSpells);
            Dictionary<string, byte> fourLinesBecome2Lines = new Dictionary<string, byte>(StaffSpells);
            Dictionary<string, byte> cradhOneLine = new Dictionary<string, byte>(StaffSpells);

            foreach (var key in minusOneLine.Keys.ToList())
            {
                minusOneLine[key] = minusOneLine[key] <= 1 ? (byte)0 : (byte)(minusOneLine[key] - 1);
            }

            foreach (var key in minusTwoLines.Keys.ToList())
            {
                minusTwoLines[key] = minusTwoLines[key] <= 2 ? (byte)0 : (byte)(minusTwoLines[key] - 2);
            }

            foreach (var key in masterOneLine.Keys.ToList())
            {
                masterOneLine[key] = 1;
            }

            foreach (var key in oneLine.Keys.ToList())
            {
                oneLine[key] = oneLine[key] > 0 ? (byte)1 : (byte)0;
            }

            foreach (var key in masterPriest.Keys.ToList())
            {
                byte currentValue = masterPriest[key];
                masterPriest[key] = currentValue <= 3 ? (byte)0 : (byte)(currentValue - 3);

                if (key == "cradh" || key == "mor cradh" || key == "ard cradh")
                {
                    masterPriest[key] = 1;
                }
            }

            // -- cradhZeroLine: Force 0 for specific keys
            string[] zeroKeys = {
                "beag cradh", "cradh", "mor cradh", "ard cradh",
                "Dark Seal", "Darker Seal", "Demise", "Demon Seal"
            };
            foreach (var key in cradhZeroLine.Keys.ToList())
            {
                if (zeroKeys.Contains(key))
                {
                    cradhZeroLine[key] = 0;
                }
            }

            // -- fourLinesBecome2Lines: If exactly 4, become 2
            foreach (var key in fourLinesBecome2Lines.Keys.ToList())
            {
                if (fourLinesBecome2Lines[key] == 4)
                {
                    fourLinesBecome2Lines[key] = 2;
                }
            }

            // -- cradhOneLine: Force 1 for specific cradh-keys
            string[] cradhKeys = { "beag cradh", "cradh", "mor cradh", "ard cradh" };
            foreach (var key in cradhOneLine.Keys.ToList())
            {
                if (cradhKeys.Contains(key))
                {
                    cradhOneLine[key] = 1;
                }
            }

            Bows.AddRange(WeaponRegistry.Bows.Values);
            Staffs.AddRange(WeaponRegistry.BuildStaffs(
                StaffSpells, minusOneLine, minusTwoLines, masterOneLine, oneLine,
                masterPriest, cradhZeroLine, fourLinesBecome2Lines, cradhOneLine));
            // Add Arsaid Aon weapons?
        }
        internal void CheckWeaponType(Item item)
        {
            if (Staffs.Any(Staff => Staff.Name == item.Name))
            {
                item.IsStaff = true;
                item.ThisStaff = Staffs.First(Staff => Staff.Name == item.Name);
            }
            if (WeaponRegistry.Bows.TryGetValue(item.Name, out Bow bow))
            {
                item.IsBow = true;
                item.ThisBow = bow;
            }
            if (WeaponRegistry.MeleeWeapons.TryGetValue(item.Name, out MeleeWeapon meleeWeapon))
            {
                item.IsMeleeWeapon = true;
                item.ThisWeapon = meleeWeapon;
            }
        }

        internal string EquipBow()
        {
            var candidateBow = Inventory
                .Select(item => item.Name)
                .Distinct()
                .Where(name => WeaponRegistry.Bows.ContainsKey(name))
                .Select(name => WeaponRegistry.Bows[name])
                .Where(bow => bow.AbilityRequired <= (int)Ability)
                .OrderByDescending(bow => bow.AbilityRequired)
                .FirstOrDefault();

            if (candidateBow == null)
                return string.Empty;

            UseItem(candidateBow.Name);
            return candidateBow.Name;
        }

        private string EquipBestWeapon(
            IReadOnlyDictionary<string, (int AbilityRequired, int LevelRequired)> weaponCriteria,
            Func<string, bool> isCurrentlyEquipped,
            Func<string, bool> equipWeapon,
            int currentAbility,
            int currentLevel)
        {
            // Find the best matching weapon
            var bestWeapon = weaponCriteria
                .Where(w => currentAbility >= w.Value.AbilityRequired && currentLevel >= w.Value.LevelRequired)
                .OrderByDescending(w => (w.Value.AbilityRequired, w.Value.LevelRequired))
                .Select(w => w.Key)
                .FirstOrDefault();

            if (bestWeapon == null)
                return string.Empty;

            // Check if the weapon is already equipped
            if (isCurrentlyEquipped(bestWeapon))
                return bestWeapon;

            // Equip the weapon
            equipWeapon(bestWeapon);
            return bestWeapon;
        }

        internal string EquipMonk()
        {
            return EquipBestWeapon(
                CONSTANTS.MONK_WEAPONS,
                weaponName => EquippedItems[1]?.Name == weaponName,
                weaponName => UseItem(weaponName),
                currentAbility: Ability,
                currentLevel: Level
            );
        }

        internal string EquipGlad()
        {
            return EquipBestWeapon(
                CONSTANTS.GLAD_WEAPONS,
                weaponName => EquippedItems[1]?.Name == weaponName,
                weaponName => UseItem(weaponName),
                currentAbility: Ability,
                currentLevel: Level
            );
        }

        internal string EquipArcher()
        {
            return EquipBestWeapon(
                CONSTANTS.ARCHER_WEAPONS,
                weaponName => EquippedItems[1]?.Name == weaponName,
                weaponName => UseItem(weaponName),
                currentAbility: Ability,
                currentLevel: Level
            );
        }




        private string[] LoadSavedChants(string spellName)
        {
            string[] chants = new string[10];
            string spellBookPath = System.IO.Path.Combine(Settings.Default.DarkAgesPath.Replace("Darkages.exe", ""), Name, "SpellBook.cfg");

            if (!File.Exists(spellBookPath))
            {
                return chants;
            }

            string[] lines = File.ReadAllLines(spellBookPath);
            bool foundSpell = false;
            foreach (string line in lines)
            {
                if (line.Equals(spellName, StringComparison.CurrentCultureIgnoreCase))
                {
                    foundSpell = true;
                    continue;
                }

                if (foundSpell)
                {
                    if (line.StartsWith("Spell"))
                    {
                        int index = int.Parse(line.Substring("Spell".Length, line.IndexOf(':') - "Spell".Length));
                        chants[index] = line.Substring(line.IndexOf(':') + 1);
                        if (index == chants.Length - 1) // Stop if we've read all chants
                        {
                            break;
                        }
                    }
                    else
                    {
                        break; // Exit loop if line doesn't start with "Spell" prefix
                    }
                }
            }

            return chants;
        }
        private string ParseCustomSpellLines()
        {
            string[] array = Regex.Split(ClientTab.customLinesBox.Text, "\r\n");
            _customSpellLineCounter++;
            if (_customSpellLineCounter > array.Count() - 1)
            {
                _customSpellLineCounter = 0;
            }
            return array[_customSpellLineCounter];
        }
        internal bool TryUseAnySpell(string[] spellNames, Creature target, bool autoStaffSwitch, bool keepSpellAfterUse)
        {
            foreach (string spellName in spellNames)
            {
                // Check if the spell exists in the Spellbook
                if (Spellbook[spellName] != null)
                {
                    // If the spell exists, attempt to use it
                    if (UseSpell(spellName, target, autoStaffSwitch, keepSpellAfterUse))
                    {
                        return true;
                    }
                    break;
                }
            }
            return false;
        }
        internal void SleepFighting()
        {
            Thread.Sleep(3000);
            Dialog?.DialogNext(2);
        }
        internal void ReEquipItem(string itemName)
        {
            while (!Inventory.Contains(itemName))
            {
                Thread.Sleep(100);
            }
            UseItem(itemName);
        }
        internal bool EquipDarkNeck()
        {
            return EquipNecklace("Dark", CONSTANTS.DARK_NECKS);
        }
        internal bool EquipLightNeck()
        {
            return EquipNecklace("Light", CONSTANTS.LIGHT_NCEKS);
        }
        private bool EquipNecklace(string elementName, IReadOnlyDictionary<string, (int Ability, int Level)> necklaceList)
        {
            lock (BashLock)
            {
                if (necklaceList.ContainsKey(EquippedItems[6].Name))
                {
                    OffenseElement = elementName;
                    return true;
                }
                var bestNecklace = Inventory
                    .Where(item => necklaceList.ContainsKey(item.Name)) // Item exists in the list
                    .Where(item => necklaceList[item.Name].Ability <= Ability && necklaceList[item.Name].Level <= Level) // Usability check
                    .OrderByDescending(item => necklaceList[item.Name].Level)   // Prioritize higher levels
                    .ThenByDescending(item => necklaceList[item.Name].Ability)  // Break ties with ability
                    .FirstOrDefault();

                if (bestNecklace == null)
                    return false; // No usable necklace found

                UseItem(bestNecklace.Name);

                // Verify if the necklace is equipped
                Utility.Timer timer = Utility.Timer.FromMilliseconds(1500);
                while (!timer.IsTimeExpired)
                {
                    if (EquippedItems[6] != null && EquippedItems[6].Name == bestNecklace.Name)
                    {
                        OffenseElement = elementName;
                        return true;
                    }
                    Thread.Sleep(50);
                }

                return false;
            }
        }
        private bool IsCreatureAllowed(Creature creature, HashSet<ushort> whiteList)
        {

            int mapID = Map.MapID;

            // Allow sprite 492 only on map 6999
            if (creature.SpriteID == 492 && mapID == 6999)
            {
                return true;
            }

            if ((creature.Type == CreatureType.WalkThrough && !Map.Name.Contains("Shinewood")) || CONSTANTS.INVISIBLE_SPRITES.Contains(creature.SpriteID) || CONSTANTS.UNDESIRABLE_SPRITES.Contains(creature.SpriteID) || CONSTANTS.RED_BOROS.Contains(creature.SpriteID) || CONSTANTS.GREEN_BOROS.Contains(creature.SpriteID))
            {
                return false;
            }

            var blackListByMapName = CONSTANTS.BLACKLIST_BY_MAP_NAME.FirstOrDefault(kv => Map.Name.StartsWith(kv.Key)).Value;
            if (blackListByMapName != null && blackListByMapName.Contains(creature.SpriteID))
            {
                return false;
            }

            return whiteList.Contains(creature.SpriteID);
        }
        internal void ResetExchangeVars()
        {
            ExchangeClosing = true;
            Thread.Sleep(1500);
            ExchangeOpen = false;
            ExchangeClosing = false;
        }
        internal void LoadUnmaxedSkills()
        {
            short num = 15;
            short num2 = 20;
            foreach (KeyValuePair<string, Skill> entry in Skillbook)
            {
                Skill skill = entry.Value;
                if (skill != null && !CONSTANTS.DOJOBLACKLIST_1.Contains(skill.Name) && !skill.Name.Contains("Lore") && !skill.Name.Contains("Inner Beast") && !skill.Name.Contains("Item") && !skill.Name.Contains("Archery") && !skill.Name.Contains("Thrust Attack") && skill.CurrentLevel < skill.MaxLevel)
                {
                    ClientTab.RenderUnmaxedSkills(skill.Name, skill.Sprite, new System.Drawing.Point(num, num2));
                    num = (short)(num + 40);
                    if (num >= 480)
                    {
                        num = 15;
                        num2 = (short)(num2 + 40);
                    }
                }
            }
            UnmaxedSkillsLoaded = true;
        }
        internal void LoadBashingSkills()
        {
            short num = 15;
            short num2 = 20;
            foreach (KeyValuePair<string, Skill> entry in Skillbook)
            {
                Skill skill = entry.Value;
                if (skill != null && !CONSTANTS.DOJOBLACKLIST_2.Contains(skill.Name) && !skill.Name.Contains("Lore") && !skill.Name.Contains("Inner Beast") && !skill.Name.Contains("Item") && !skill.Name.Contains("Archery") && !skill.Name.Contains("Thrust Attack") && !skill.Name.Contains("Arrow Shot") && skill != null)
                {
                    ClientTab.RenderBashingSkills(skill.Name, skill.Sprite, new System.Drawing.Point(num, num2));
                    num = (short)(num + 40);
                    if (num >= 650)
                    {
                        num = 15;
                        num2 = (short)(num2 + 40);
                    }
                }
            }
            var itemMappings = new Dictionary<string, ushort>
            {
                { "Two Move Combo", 108 },
                { "Three Move Combo", 108 },
                { "Sprint Potion", 101 }
            };

            // Iterate through the inventory
            foreach (var item in Inventory)
            {
                if (item != null && itemMappings.TryGetValue(item.Name, out ushort value))
                {
                    ClientTab.RenderBashingSkills(item.Name, value, new System.Drawing.Point(num, num2));

                    // Update coordinates
                    num += 40;
                    if (num >= 650)
                    {
                        num = 15;
                        num2 += 40;
                    }
                }
            }

            BashingSkillsLoaded = true;
        }
        internal void LoadUnmaxedSpells()
        {
            short num = 15;
            short num2 = 20;
            foreach (Spell spell in Spellbook.Where((Spell sp) => sp != null))
            {
                if (!CONSTANTS.DOJOBLACKLIST_1.Contains(spell.Name) && !spell.Name.Contains("Lore") && !spell.Name.Contains("Inner Beast") && !spell.Name.Contains("Item") && !spell.Name.Contains("Archery") && !spell.Name.Contains("Thrust Attack") && spell.CurrentLevel < spell.MaximumLevel)
                {
                    ClientTab.RenderUnmaxedSpells(spell.Name, spell.Sprite, new System.Drawing.Point(num, num2));
                    num = (short)(num + 40);
                    if (num >= 480)
                    {
                        num = 15;
                        num2 = (short)(num2 + 40);
                    }
                }
            }
            UnmaxedSpellsLoaded = true;
        }
        internal void EscapeKey()
        {
            NativeMethods.PostMessage(Process.GetProcessById(processId).MainWindowHandle, 256, 27, MakeLParam(1, NativeMethods.MapVirtualKey(27, 0)));
            NativeMethods.PostMessage(Process.GetProcessById(processId).MainWindowHandle, 257, 27, MakeLParam(1, NativeMethods.MapVirtualKey(27, 0)));
        }
        internal void EnterKey()
        {
            NativeMethods.PostMessage(Process.GetProcessById(processId).MainWindowHandle, 256, 13, MakeLParam(1, NativeMethods.MapVirtualKey(13, 0)));
            NativeMethods.PostMessage(Process.GetProcessById(processId).MainWindowHandle, 257, 13, MakeLParam(1, NativeMethods.MapVirtualKey(13, 0)));
        }
        internal int MakeLParam(int LoWord, int HiWord)
        {
            return (HiWord << 16) | (LoWord & 0xFFFF);
        }


        internal bool Pathfind(Location destination, short distance = 1, bool shouldBlock = true, bool avoidWarps = true)
        {

            if (NearbyHiddenPlayers.Count > 0 || IsCasting)
            {
                //Console.WriteLine($"[Pathfind] [{this.Name}] Cannot walk because NearbyHiddenPlayers count is {NearbyHiddenPlayers.Count} or is casting {IsCasting}");
                if (!IsWalking)
                {
                    //Console.WriteLine($"[Pathfind] [{this.Name}] Not currently walking.");
                    return false;
                }
                IsCasting = false;
            }

            bool isWall = Map.IsWall(ClientLocation);
            bool isStuck = GetNearbyObjects().OfType<Creature>()
                .Any(creature => creature != Player && creature.Type != CreatureType.WalkThrough && creature.Location == ClientLocation);

            //Console.WriteLine($"[Pathfind] [{this.Name}] value of isStuck = " + isStuck);

            if ((isWall || isStuck) && (HasWalked || ClientLocation.X == 0 && ClientLocation.Y == 0 || ServerLocation.X == 0 && ServerLocation.Y == 0))
            {
                //Console.WriteLine($"[Pathfind] [{this.Name}] isWall or isStuck, refreshing. Setting _hasWalked to false and returning false");
                RefreshRequest();
                HasWalked = false;
                return false;
            }

            // Avoid recalculating path if already near the target
            /*if (distance > 0 && ClientLocation.DistanceFrom(destination) <= distance)
            {
                return false;
            }*/


            if (ClientLocation == destination)
            {
                if (HasWalked || DateTime.UtcNow.Subtract(LastStep).TotalSeconds > 2.0)
                {
                    if (StuckCounter == 0)
                    {
                        //Console.WriteLine($"[Pathfind] [{this.Name}] Refreshing client due to timeout or refresh needed.");
                        RefreshRequest();
                    }
                    HasWalked = false;
                }
                return true;
            }

            double elapsedMilliseconds = DateTime.UtcNow.Subtract(LastStep).TotalMilliseconds;
            double waitThreshold = (Bot.IsStrangerNearby() && !ClientTab.chkSpeedStrangers.Checked) || Bot._rangerNear
                ? 420.0
                : WalkSpeed;

            // Continue looping until elapsed time meets or exceeds the threshold
            while (elapsedMilliseconds < waitThreshold)
            {
                Thread.Sleep(10);
                elapsedMilliseconds = DateTime.UtcNow.Subtract(LastStep).TotalMilliseconds;
            }


            // Only recalculate the path if necessary
            if (destination != _lastDestination || _pathStack.Count == 0)
            {
                //Console.WriteLine($"[Pathfind] [{this.Name}] New destination or empty path stack. Calculating new path.");
                _lastDestination = destination;
                _pathStack = Pathfinder.FindPath(ClientLocation, destination, avoidWarps, distance);

            }

            // Handle cases where path is empty
            if (_pathStack.Count == 0 && ClientLocation != ServerLocation && HasWalked)
            {
                _pathStack = Pathfinder.FindPath(ServerLocation, destination, avoidWarps, distance   );
                if (_pathStack.Count == 0) return false;

                //Console.WriteLine($"[Pathfind] [{this.Name}] Location difference detected, requesting refresh.");
                RefreshRequest();
                HasWalked = false;
                return false;
            }

            if (_pathStack.Count == 0)
            {
                //Console.WriteLine($"[Pathfind] [{this.Name}] Path stack is empty, no further movement possible.");
                return false;
            }

            // Clone _pathStack before iterating to prevent modification while looping.
            // List<Location> pathList = _pathStack.ToList();

            List<Creature> nearbyCreatures = GetNearbyObjects()
                .OfType<Creature>()
                .Where(c => c.Type != CreatureType.WalkThrough && c != Player && c.Location.DistanceFrom(ServerLocation) <= 11)
                .ToList();

            foreach (Location loc in _pathStack.ToList())
            {
                Door door = Doors.Values.FirstOrDefault(d => d.Location.Equals(loc));
                if (door != null && door.Closed && !door.RecentlyClicked)
                {
                    ClickObject(loc);
                    door.LastClicked = DateTime.UtcNow;
                }

                if (nearbyCreatures.Any(creature =>
                    Location.NotEquals(loc, destination) &&
                    Location.Equals(creature.Location, loc) ||
                    (!HasEffect(Definitions.EffectsBar.Hide) && CONSTANTS.GREEN_BOROS.Contains(creature.SpriteID) && BoroArea1(creature).Contains(loc))))
                {
                    _pathStack = Pathfinder.FindPath(ClientLocation, destination, avoidWarps, distance);
                    return false;
                }
            }

            Location nextPosition = _pathStack.Peek();

            if (nextPosition.Equals(ClientLocation))
            {
                _pathStack.Pop();
                if (_pathStack.Count == 0)
                {
                    //Console.WriteLine($"[Pathfind] [{this.Name}] Path complete. Destination reached.");
                    return true;
                }
                nextPosition = _pathStack.Peek();
            }


            if (nextPosition.DistanceFrom(ClientLocation) != 1)
            {
                //Console.WriteLine($"[Pathfind] [{this.Name}] Unexpected distance to next position {nextPosition}, recalculating path.");
                if (nextPosition.DistanceFrom(ClientLocation) > 2 && HasWalked)
                {
                    if (StuckCounter == 0)
                    {
                        //Console.WriteLine($"[Pathfind] [{this.Name}] Refreshing client due to unexpected position distance.");
                        RefreshRequest();
                    }
                    HasWalked = false;
                }
                _pathStack = Pathfinder.FindPath(ClientLocation, destination, avoidWarps, distance);
                return false;
            }

            Direction directionToWalk = nextPosition.GetDirection(ClientLocation);
           
            if (shouldBlock)
            {
                lock (CastLock)
                {
                    if (!HasEffect(Definitions.EffectsBar.Pramh) &&
                        !HasEffect(Definitions.EffectsBar.Suain) &&
                        (!HasEffect(Definitions.EffectsBar.Skull) || ClientTab.ascendBtn.Text == "Ascending"))
                    {
                        Walk(directionToWalk);
                    }
                }
            }
            else if (!HasEffect(Definitions.EffectsBar.Pramh) &&
                    !HasEffect(Definitions.EffectsBar.Suain) &&
                    (!HasEffect(Definitions.EffectsBar.Skull) || ClientTab.ascendBtn.Text == "Ascending"))
            {
                Walk(directionToWalk);
            }

            return true;
        }
        internal bool Routefind(Location destination, short distance = 0, bool mapOnly = false, bool shouldBlock = true, bool avoidWarps = true)
        {
            try
            {
                //Console.WriteLine($"[RouteFind] [{Name}] Starting RouteFind to {destination}");
                if (Server.StopWalking)
                {
                    //Console.WriteLine($"[RouteFind] [{Name}] Not supposed to walk.");
                    return false;
                }

                Location currentLocation = new Location((short)(Map?.MapID), ClientLocation.X, ClientLocation.Y);
                //Console.WriteLine($"[RouteFind] [{this.Name}] Current location: {currentLocation}");
                Location adjustedDestination;
                //adjust for followdistance?
                if (ClientTab != null && ClientTab.followCbox.Checked)
                {
                    adjustedDestination = GetValidLocationNearTarget(destination, (short)ClientTab.followDistanceNum.Value);
                }
                else
                {
                    adjustedDestination = destination;
                }

                if (Location.Equals(currentLocation, adjustedDestination))
                {
                    if (Location.Equals(adjustedDestination, new Location(395, 6, 6))) //Path Temple 1
                    {
                        Bot._circle1 = true;
                    }
                    else if (Location.Equals(adjustedDestination, new Location(344, 6, 6))) //Path Temple 6
                    {
                        Bot._circle2 = true;
                    }
                    //Console.WriteLine($"[RouteFind] [{this.Name}] Already at destination.");
                    _routeStack.Clear();
                    return false;
                }

                if (_routeStack.Count == 1 && adjustedDestination.MapID == Map.MapID && mapOnly)
                {
                    _routeStack.Clear();
                    return false;
                }

                if (_routeStack.Count == 0 || Location.NotEquals(_routeDestination, adjustedDestination))
                {
                    Console.WriteLine($"[RouteFind] [{this.Name}] Finding new route.");
                    _routeDestination = adjustedDestination;
                    _routeStack = RouteFinder.FindRoute(currentLocation, adjustedDestination);
                }

                if (Map.Name.Contains("Plamit"))
                {
                    _routeStack = RouteFinder.FindRoute(currentLocation, adjustedDestination);
                }

                if (_routeStack.Count == 0)
                {
                    Console.WriteLine($"[RouteFind] [{this.Name}] Route not found, initializing new RouteFinder.");
                    RouteFinder = new RouteFinder(Server, this);
                    _routeDestination = adjustedDestination;
                    _lastClickedWorldMap = DateTime.MinValue;
                    _routeStack = RouteFinder.FindRoute(currentLocation, adjustedDestination);
                    return false;
                }

                // Clone _routeStack before iterating
                List<Location> routeList = _routeStack.ToList();
                routeList.Reverse();

                Location nextLocation = _routeStack.Peek();

                //if (routeStack.Count != 1)
                //{
                //Console.WriteLine("***routeStack.Count != 1");
                //    distance = 0;
                //}

                if (_routeStack.Count > 1)
                {
                    Location tempNext = _routeStack.Peek();
                    if (Location.Equals(tempNext, ServerLocation))
                    {
                        _routeStack.Pop();
                        if (_routeStack.Count > 0)
                        {
                            nextLocation = _routeStack.Peek();
                        }
                    }
                }

                if (WorldMap != null)
                {
                     //Console.WriteLine($"[RouteFind] [{this.Name}] World map is not null, processing world map navigation.");
                     List<Location> list = RouteFinder.FindRoute(currentLocation, adjustedDestination).Reverse().ToList();
                    if (DateTime.UtcNow.Subtract(_lastClickedWorldMap).TotalSeconds < 1.0)
                    {
                        return false;
                    }
                    foreach (Location location in routeList)
                    {
                        //Console.WriteLine($"[RouteFind] [{this.Name}] Checking world map node for location {location}");

                        foreach (WorldMapNode node in WorldMap.Nodes)
                        {
                            //Console.WriteLine($"[RouteFind] [{this.Name}] Checking node {node.Location}");
                            if (node.MapID == location.MapID)
                            {
                                //Console.WriteLine($"[RouteFind] [{this.Name}] Need to click world map");
                                _lastClickedWorldMap = DateTime.UtcNow;
                                ClickWorldMap(node.MapID, node.Location);
                                return true;
                            }
                        }
                    }
                    foreach (WorldMapNode node in WorldMap.Nodes)
                    {
                        //Console.WriteLine($"[RouteFind] [{this.Name}] [2]Checking node {node.Location}");

                        if (node.MapID == nextLocation.MapID)
                        {
                            //Console.WriteLine($"[RouteFind] [{this.Name}] [2]Need to click world map");
                            _lastClickedWorldMap = DateTime.UtcNow;
                            ClickWorldMap(node.MapID, node.Location);
                            return true;
                        }
                    }
                    return false;
                }

                if (nextLocation.MapID != Map.MapID)
                {
                    if (!Server._maps.TryGetValue(Map.MapID, out Map value))
                    {
                        //Console.WriteLine($"[RouteFind] [{this.Name}] Map not found in server maps. Clearing routeStack.");
                        _routeStack.Clear();
                        return false;
                    }
                    if (value.WorldMaps.TryGetValue(ClientLocation.Point, out WorldMap _worldMapNodeList))
                    {
                        if (!value.WorldMaps.TryGetValue(ServerLocation.Point, out _worldMapNodeList))
                        {
                            //Console.WriteLine($"[RouteFind] [{this.Name}] Need to refresh");
                            RefreshRequest();
                            return false;
                        }
                        foreach (WorldMapNode worldMapNode in _worldMapNodeList.Nodes)
                        {
                            if (worldMapNode.MapID == nextLocation.MapID)
                            {
                                //Console.WriteLine($"[RouteFind] [{this.Name}] maps are equal");
                                return false;
                            }
                        }
                    }
                    if (value.Exits.TryGetValue(ClientLocation.Point, out Warp warp) && warp.TargetMapID == nextLocation.MapID)
                    {
                        //Console.WriteLine($"[RouteFind] [{this.Name}] Warping with NPC");
                        WarpWithNPC(nextLocation);
                        RefreshRequest();
                        return true;
                    }
                    _routeStack.Clear();
                    return false;
                }
                //Console.WriteLine($"[RouteFind] [{this.Name}] About to call TryWalkLocation with distance value of: {distance}");
                if (!Pathfind(nextLocation, distance, shouldBlock, avoidWarps = true))
                {
                    if (Map.Name.Contains("Threshold"))
                    {
                        //Console.WriteLine($"[RouteFind] [{this.Name}] Threshold map detected, attempting to walk south.");
                        Walk(Direction.South);
                        Thread.Sleep(1000);
                        return true;
                    }
                    //Console.WriteLine($"[RouteFind] [{this.Name}] TryWalkToLocation failed, returning false.");
                    return false;
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine($"[RouteFind] [{Name}] Exception in RouteFind. Refreshing.");
                Console.WriteLine(ex.ToString());
                Console.WriteLine("***");
                RefreshRequest();
                return false;
            }
            if (_routeStack.Count <= 0)
            {
                //Console.WriteLine($"[RouteFind] [{Name}] Route stack empty, returning false.");
                return false;
            }

            return true;
        }
        private bool IsWalkable(Location location)
        {
            // Check if the location is walkable (not blocked)
            if (Map.Tiles.TryGetValue(location.Point, out Tile tile))
            {
                return !tile.IsWall;
            }
            return false;
        }
        private void WarpWithNPC(Location nextLocation)
        {
            if (ClientTab != null)
            {
                try
                {
                    if (Location.Equals(ClientLocation, new Location(5220, 0, 6)) && nextLocation.MapID == 5210 && Dialog != null)
                    {
                        Dialog.DialogNext(2);
                    }
                    if (Location.Equals(ClientLocation, new Location(6926, 8, 9)) && nextLocation.MapID == 10028)
                    {
                        Creature creature = GetNearbyNPC("Quard");
                        RequestNamedPursuit(creature, "Express Ship", true);
                        ReplyDialog(1, creature.ID, 0, 2, 1);
                        ReplyDialog(1, creature.ID, 0, 2);

                        if (!string.IsNullOrEmpty(ClientTab?.walkMapCombox.Text) && ClientTab?.walkBtn.Text == "Stop" && ClientTab?.startStrip.Text == "Stop")
                        {
                            Server.MedWalk[Name] = ClientTab?.walkMapCombox.Text;
                        }
                        if (!string.IsNullOrEmpty(ClientTab?.followText.Text) && ClientTab?.followCbox.Checked == true && ClientTab?.startStrip.Text == "Stop")
                        {
                            Server.MedTask[Name] = ClientTab?.followText.Text;
                        }
                        if (((!string.IsNullOrEmpty(ClientTab?.walkMapCombox.Text) && ClientTab?.walkBtn.Text == "Stop") || (!string.IsNullOrEmpty(ClientTab?.followText.Text) && ClientTab?.followCbox.Checked == true)) && ClientTab?.startStrip.Text == "Stop")
                        {
                            Server.MedWalkSpeed[Name] = (int)(ClientTab?.walkSpeedSldr.Value);
                        }
                        if (ClientTab?.toggleBugBtn.Text == "Disable" && ClientTab?.startStrip.Text == "Stop")
                        {
                            Server.MedTask[Name] = "bugEvent";
                            Server.MedWalkSpeed[Name] = (int)(ClientTab?.walkSpeedSldr.Value);
                        }
                        if (ClientTab.toggleSeaonalDblBtn.Text == "Disable" && ClientTab?.startStrip.Text == "Stop")
                        {
                            Server.MedTask[Name] = "vDayEvent";
                            Server.MedWalkSpeed[Name] = (int)(ClientTab?.walkSpeedSldr.Value);
                        }
                    }
                    else if (Location.Equals(ClientLocation, new Location(706, 11, 13)) && nextLocation.MapID == 6591)
                    {
                        PublicMessage(3, "Enter Sewer Maze");
                    }
                    else if (Location.Equals(ClientLocation, new Location(10000, 29, 31)) && nextLocation.MapID == 10999)
                    {
                        Creature creature = GetNearbyNPC("Lenoa");
                        RequestNamedPursuit(creature, "Caravan to Noam", true);
                        ReplyDialog(1, creature.ID, 0, 2);
                        ReplyDialog(1, creature.ID, 0, 2, 1);
                        ReplyDialog(1, creature.ID, 0, 2);
                    }
                    else if (Location.Equals(ClientLocation, new Location(10055, 46, 23)) && nextLocation.MapID == 10999)
                    {
                        Creature creature = GetNearbyNPC("Habab");
                        RequestNamedPursuit(creature, "Caravan to Asilon or Hwarone", true);
                        ReplyDialog(1, creature.ID, 0, 2);
                        ReplyDialog(1, creature.ID, 0, 2, 1);
                        ReplyDialog(1, creature.ID, 0, 2);
                    }
                    else if (Location.Equals(ClientLocation, new Location(10265, 87, 47)) && nextLocation.MapID == 10998)
                    {
                        Creature creature = GetNearbyNPC("Mank");
                        RequestNamedPursuit(creature, "Caravan to Noam", true);
                        ReplyDialog(1, creature.ID, 0, 2);
                        ReplyDialog(1, creature.ID, 0, 2, 1);
                        ReplyDialog(1, creature.ID, 0, 2);
                    }
                    else if (Location.Equals(ClientLocation, new Location(10055, 46, 24)) && nextLocation.MapID == 1960)
                    {
                        Creature creature = GetNearbyNPC("Habab");
                        RequestNamedPursuit(creature, "Carpet Merchant", true);
                        ReplyDialog(1, creature.ID, 0, 2);
                        ReplyDialog(1, creature.ID, 0, 2, 1);
                        ReplyDialog(1, creature.ID, 0, 2, 1);
                        ReplyDialog(1, creature.ID, 0, 2);

                        if (!string.IsNullOrEmpty(ClientTab?.walkMapCombox.Text) && ClientTab?.walkBtn.Text == "Stop" && ClientTab?.startStrip.Text == "Stop")
                        {
                            Server.MedWalk[Name] = ClientTab?.walkMapCombox.Text;
                        }
                        if (!string.IsNullOrEmpty(ClientTab?.followText.Text) && ClientTab?.followCbox.Checked == true && ClientTab?.startStrip.Text == "Stop")
                        {
                            Server.MedTask[Name] = ClientTab?.followText.Text;
                        }
                        if (((!string.IsNullOrEmpty(ClientTab?.walkMapCombox.Text) && ClientTab?.walkBtn.Text == "Stop") || (!string.IsNullOrEmpty(ClientTab?.followText.Text) && ClientTab?.followCbox.Checked == true)) && ClientTab?.startStrip.Text == "Stop")
                        {
                            Server.MedWalkSpeed[Name] = (int)(ClientTab?.walkSpeedSldr.Value);
                        }
                        if (ClientTab?.toggleBugBtn.Text == "Disable" && ClientTab?.startStrip.Text == "Stop")
                        {
                            Server.MedTask[Name] = "bugEvent";
                            Server.MedWalkSpeed[Name] = (int)(ClientTab?.walkSpeedSldr.Value);
                        }
                        if (ClientTab?.toggleSeaonalDblBtn.Text == "Disable" && ClientTab?.startStrip.Text == "Stop")
                        {
                            Server.MedTask[Name] = "vDayEvent";
                            Server.MedWalkSpeed[Name] = (int)(ClientTab?.walkSpeedSldr.Value);
                        }
                    }
                    else if (Location.Equals(ClientLocation, new Location(3634, 16, 6)) && nextLocation.MapID == 8420)
                    {
                        Creature creature = GetNearbyNPC("Fallen Soldier");
                        RequestNamedPursuit(creature, "ChadulEntry", true);
                        ReplyDialog(1, creature.ID, 0, 2, 1);
                    }
                    else if (Location.Equals(ClientLocation, new Location(8318, 50, 95)) && nextLocation.MapID == 8345)
                    {
                        Creature creature = GetNearbyNPC("Ashlee");
                        ClickObject(creature.ID);
                        ReplyDialog(1, creature.ID, 0, 2);
                    }
                    else if (Location.Equals(ClientLocation, new Location(8355, 32, 5)) && nextLocation.MapID == 8356)
                    {
                        Creature creature = GetNearbyNPC("Norrie");
                        PublicMessage(0, "let me through");
                        while (Dialog == null)
                        {
                            Thread.Sleep(25);
                        }
                        if (!Dialog.Message.Contains("Sorry, I forgot..."))
                        {
                            ReplyDialog(1, creature.ID, 0, 2, 1);
                            ReplyDialog(1, creature.ID, 0, 2, 1);
                            Thread.Sleep(1000);
                            PublicMessage(0, "let me through");
                        }
                        ReplyDialog(1, creature.ID, 0, 2);
                        ReplyDialog(1, creature.ID, 0, 2);
                        ReplyDialog(1, creature.ID, 0, 2);
                        Thread.Sleep(1000);
                    }
                    else if (Location.Equals(ClientLocation, new Location(8361, 32, 7)) && nextLocation.MapID == 8362)
                    {
                        Creature creature = GetNearbyNPC("Yowien Guard");
                        if (creature != null && Inventory.Contains("Yowien Costume"))
                        {
                            UseSkill("Assail");
                            UseItem("Yowien Costume");
                            UseItem("Yowien Headgear");
                            Thread.Sleep(1000);
                        }
                        PublicMessage(0, "graauuloow");
                        DateTime utcNow = DateTime.UtcNow;
                        while (Dialog == null)
                        {
                            if (!(DateTime.UtcNow.Subtract(utcNow).TotalSeconds <= 2.0))
                            {
                                return;
                            }
                            Thread.Sleep(25);
                        }
                        if (Dialog.Message == "*The Yowien Guard sniffs you, then suddenly attacks you. You run back to a safe distance*")
                        {
                            Thread.Sleep(1000);
                        }
                        else
                        {
                            ReplyDialog(1, creature.ID, 0, 2);
                            ReplyDialog(1, creature.ID, 0, 2);
                            ReplyDialog(1, creature.ID, 0, 2);
                            ReplyDialog(1, creature.ID, 0, 2);
                            ReplyDialog(1, creature.ID, 0, 2);
                            Thread.Sleep(1000);
                        }
                    }
                    else if (Map.MapID == 3052 && ClientLocation.X == 44 && ClientLocation.Y >= 18 && ClientLocation.Y <= 25)
                    {
                        Creature creature = GetNearbyNPC("Celesta");
                        RequestNamedPursuit(creature, "Enter Balanced Arena", true);
                        ReplyDialog(1, creature.ID, 0, 2);
                        while (Dialog == null)
                        {
                            Thread.Sleep(10);
                        }
                        Thread.Sleep(1000);
                        if (Dialog != null && Dialog.Message.Contains("Lumen Amulet"))
                        {
                            ServerMessage(0, "Deposit your lumen, then re-enable bot. damn nub");
                            Bot.StopAsync();
                        }
                    }
                    else if (Map.MapID == 393 && ClientLocation.DistanceFrom(new Location(393, 7, 6)) <= 1)
                    {
                        Creature npc = GetNearbyNPC("Aoife");
                        PursuitRequest(1, npc.ID, 1171);
                        if (WaitForDialog())
                        {
                            ReplyDialog(Dialog.ObjectType, Dialog.ObjectID, Dialog.PursuitID, 1);
                            ReplyDialog(Dialog.ObjectType, Dialog.ObjectID, Dialog.PursuitID, (ushort)((Player.BodySprite == 16) ? 6 : 3));
                            ReplyDialog(Dialog.ObjectType, Dialog.ObjectID, Dialog.PursuitID, 8, 1);
                            ReplyDialog(Dialog.ObjectType, Dialog.ObjectID, Dialog.PursuitID, 15, 1);
                            Thread.Sleep(1000);
                        }
                    }
                    else if (Location.Equals(ClientLocation, new Location(503, 41, 59)) && nextLocation.MapID == 3014)
                    {
                        Creature npc = GetNearbyNPC("Keane");
                        RequestNamedPursuit(npc, "Suomi Help", true);
                        ReplyDialog(1, npc.ID, 0, 2, 1);
                        ReplyDialog(1, npc.ID, 0, 2);
                    }

                }
                catch (Exception ex)
                {
                    Console.WriteLine($"[WarpWithNPC] Exception occurred: {ex.ToString()}");
                }
            }
        }
       
        internal bool WaitForDialog()
        {
            DateTime utcNow = DateTime.UtcNow;
            while (true)
            {
                if (Dialog == null)
                {
                    if (!(DateTime.UtcNow.Subtract(utcNow).TotalSeconds <= 3.0))
                    {
                        break;
                    }
                    Thread.Sleep(10);
                    continue;
                }
                return true;
            }
            return false;
        }
        internal bool RouteFindByMapID(short mapID)
        {
            return Routefind(new Location(mapID, 0, 0), 0, true);
        }
        internal bool WithinRange(VisibleObject obj, int range = 12)
        {
            return NearbyObjects.Contains(obj.ID) && ServerLocation.DistanceFrom(obj.Location) <= range;
        }
        internal bool IsLocationSurrounded(Location location)
        {
            //Console.WriteLine($"[IsLocationSurrounded] Checking if location {location} is surrounded.");

            if (Player == null) return false;

            // Early return if the player is too close to the location.
            if (Player.Location.DistanceFrom(location) <= 1)
            {
                return false;
            }

            // Gather all relevant creatures' locations within the same map to avoid repeated enumeration.
            var creatureLocations = GetNearbyObjects()
                .OfType<Creature>()
                .Where(creature => (creature.Type == CreatureType.Aisling || creature.Type == CreatureType.Merchant || creature.Type == CreatureType.Normal) && !creature.Location.Equals(location))
                .Select(creature => creature.Location)
                .ToHashSet(); // Using HashSet for O(1) lookups.

            // Get obstacle locations within the same map once to avoid repeated calls.
            var obstacleLocations = GetWarpPoints(location).Where(obstacle => obstacle.MapID == location.MapID).ToHashSet(); // Using HashSet for O(1) lookups.

            // Define adjacent locations based on cardinal directions.
            var adjacentLocations = new[]
            {
                location.Offsetter(Direction.North),
                location.Offsetter(Direction.West),
                location.Offsetter(Direction.South),
                location.Offsetter(Direction.East)
            };

            // Check each adjacent location for being surrounded conditions.
            foreach (var loc in adjacentLocations)
            {
                bool isOccupiedOrBound = creatureLocations.Contains(loc) || obstacleLocations.Contains(loc) || Map.IsWall(loc);

                // If any adjacent location is not occupied or within bounds, the location is not surrounded.
                if (!isOccupiedOrBound)
                {
                    return false;
                }
            }

            // All adjacent locations are occupied or within bounds, so the location is surrounded.
            return true;
        }

        internal bool IsWalledIn(Location loc)
        {
            var nearbyPoints = new HashSet<Location>(
                GetNearbyObjects()
                    .OfType<Creature>()
                    .Where(c => (c.Type == CreatureType.Aisling ||
                                 c.Type == CreatureType.Merchant ||
                                 c.Type == CreatureType.Normal) &&
                                 c != Player)
                    .Select(c => c.Location)
            );

            var warpPoints = new HashSet<Location>(GetWarpPoints(loc));

            int wallsCount = 0;
            foreach (Direction dir in Enum.GetValues(typeof(Direction)))
            {
                Location adjacentPoint = loc.Offsetter(dir);

                if (nearbyPoints.Contains(adjacentPoint) ||
                    warpPoints.Contains(adjacentPoint) ||
                    Map.IsWall(adjacentPoint))
                {
                    wallsCount++;
                }

                // Early exit if fully surrounded
                if (wallsCount >= 4)
                    return true;
            }

            return false;
        }

        internal Element WhichtoUse(Element element)
        {
            var counterElementMap = new Dictionary<Element, Element>
            {
                { Element.Fire, Element.Water },
                { Element.Water, Element.Earth },
                { Element.Wind, Element.Fire },
                { Element.Earth, Element.Wind },
                { Element.Holy, Element.Darkness },
                { Element.Darkness, Element.Holy },
                { Element.Wood, Element.Wind },
                { Element.Metal, Element.Water },
                { Element.Nature, Element.Fire }
            };

            return counterElementMap.TryGetValue(element, out Element counterElement)
                ? counterElement
                : Element.Any;
        }

        public void SaveTimedStuff(EventType eventType)
        {
            string baseDir = AppDomain.CurrentDomain.BaseDirectory;
            string directoryPath = System.IO.Path.Combine(baseDir, "TimedEvents", Name.ToLower());

            Directory.CreateDirectory(directoryPath);

            string filePath = System.IO.Path.Combine(directoryPath, "timedstuff.json");

            Dictionary<string, DateTime> eventDictionary;
            if (File.Exists(filePath))
            {
                string existingJson = File.ReadAllText(filePath);
                eventDictionary = JsonConvert.DeserializeObject<Dictionary<string, DateTime>>(existingJson)
                                  ?? new Dictionary<string, DateTime>();
            }
            else
            {
                eventDictionary = new Dictionary<string, DateTime>();
            }

            eventDictionary[eventType.ToString()] = DateTime.UtcNow;

            string updatedJson = JsonConvert.SerializeObject(eventDictionary, Formatting.Indented);
            File.WriteAllText(filePath, updatedJson);
        }




        #region ClientPacket methods

        internal void Pickup(byte inventorySlot, Location location)
        {
            ClientPacket clientPacket = new ClientPacket(7);
            clientPacket.WriteByte(inventorySlot);
            clientPacket.WriteStruct(location.Point);
            Enqueue(clientPacket);
        }
        internal void Drop(byte inventorySlot, Location location, int count = 1)
        {
            ClientPacket clientPacket = new ClientPacket(8);
            clientPacket.WriteByte(inventorySlot);
            clientPacket.WriteStruct(location.Point);
            clientPacket.WriteInt32(count);
            Enqueue(clientPacket);
        }
        internal void DisplayEntityRequest(int id)
        {
            ClientPacket clientPacket = new ClientPacket(12);
            clientPacket.WriteInt32(id);
            Enqueue(clientPacket);
        }
        internal void PublicMessage(byte type, string message)
        {
            ClientPacket clientPacket = new ClientPacket(14);
            clientPacket.WriteByte(type);
            clientPacket.WriteString8(message);
            Enqueue(clientPacket);
        }
        internal void Turn(Direction direction)
        {
            LastTurned = DateTime.UtcNow;
            ClientPacket clientPacket = new ClientPacket(17);
            clientPacket.WriteByte((byte)direction);
            Enqueue(clientPacket);
            ServerDirection = direction;
        }

        internal void Assail()
        {
            TimeSpan sinceLastAssail = DateTime.UtcNow.Subtract(_lastAssail);

            if (sinceLastAssail.TotalMilliseconds > 250.0)
            {
                ClientPacket clientPacket = new ClientPacket(19);
                clientPacket.WriteByte(0);
                Enqueue(clientPacket);

                _lastAssail = DateTime.UtcNow;
            }

        }

        internal void Whisper(string targetName, string message)
        {
            ClientPacket clientPacket = new ClientPacket(25);
            clientPacket.WriteString8(targetName);
            clientPacket.WriteString8(message);
            Enqueue(clientPacket);
        }

        internal bool UseItem(int slot)
        {
            ClientPacket clientPacket = new ClientPacket(28);
            clientPacket.WriteByte((byte)slot);
            clientPacket.WriteByte(0);
            clientPacket.WriteByte(clientPacket.Opcode);
            clientPacket.Write(new byte[7]);
            Enqueue(clientPacket);
            return true;
        }
        internal bool UseItemIgnoreCase(Client client, string itemName)
        {
            if (client.Inventory.Any(item => item.Name.Equals(itemName, StringComparison.OrdinalIgnoreCase)))
            {
                return client.UseItem(itemName);
            }
            return false;
        }
        internal bool UseItem(string itemName)
        {
            Item item = Inventory.FirstOrDefault((Item item2) => item2.Name.Equals(itemName, StringComparison.CurrentCultureIgnoreCase));
            if (item == null)
            {
                ServerMessage(0, $"Item {itemName} not found in inventory");
                return false;
            }

            if (!EffectsBar.Contains((ushort)Definitions.EffectsBar.Pramh) && !EffectsBar.Contains((ushort)Definitions.EffectsBar.Suain) && !Server.StopCasting)
            {
                ClientPacket clientPacket = new ClientPacket(28);
                clientPacket.WriteByte(item.Slot);
                item.LastUsed = DateTime.UtcNow;
                CurrentItem = itemName;
                if (itemName == "Sprint Potion")
                {
                    Task.Run(() =>
                    {
                        ClientTab.DelayedUpdateStrangerList();
                    });
                }

                UpdateClientActionText($"{Action} Using {itemName}");
                ReadyToSpell(itemName);
                Enqueue(clientPacket);
                if (itemName == "Two Move Combo")
                {
                    if (ComboScrollCounter <= 1u)
                    {
                        ComboScrollCounter++;
                        ComboScrollLastUsed = DateTime.UtcNow;
                    }
                }
                else if (itemName == "Three Move Combo")
                {
                    if (ComboScrollCounter <= 2u)
                    {
                        ComboScrollCounter++;
                        ComboScrollLastUsed = DateTime.UtcNow;
                    }
                }

                return true;
            }
            return false;
        }
        internal void RequestProfile()
        {
            Enqueue(new ClientPacket(45));
        }
        internal void RequestGroup(string playerName)
        {
            ClientPacket clientPacket = new ClientPacket(46);
            clientPacket.WriteByte(2);
            clientPacket.WriteString8(playerName);
            Enqueue(clientPacket);
        }
        internal void RequestGroupForced(string playerName)
        {
            ClientPacket clientPacket = new ClientPacket(46);
            clientPacket.WriteByte(3);
            clientPacket.WriteString8(playerName);
            Enqueue(clientPacket);
        }
        internal void RefreshRequest(bool waitForCompletion = true)
        {
            if (Interlocked.CompareExchange(ref IsRefreshingData, 1, 0) == 0)
            {
                Enqueue(new ClientPacket(56));
                Bot._lastRefresh = DateTime.UtcNow;
            }

            var expirationTime = DateTime.UtcNow.AddMilliseconds(1500);

            if (waitForCompletion)
            {
                try
                {
                    while (DateTime.UtcNow < expirationTime)
                    {
                        if (MapChanged || IsRefreshingData == 0)
                        {
                            MapChanged = false;
                            //Console.WriteLine("[REFRESH] Can now refresh");
                            break;
                        }

                        //Console.WriteLine("[REFRESH] Waiting for refresh completion");
                        Thread.Sleep(10);
                    }
                }
                catch (ThreadInterruptedException ex)
                {
                    Console.WriteLine($"[REFRESH] Thread interrupted: {ex.Message}");
                }
                finally
                {
                    IsRefreshingData = 0;
                }
            }
            else
                IsRefreshingData = 0;
        }

        internal bool RequestNamedPursuit(Creature merchant, string pursuitName, bool wait)
        {
            if (merchant == null)
                return false;

            // If the pursuit name is not already in the server’s pursuits, force a dialog trigger.
            if (!Server.PursuitIDs.Values.Contains(pursuitName))
            {
                if (!EnsureDialogForMerchant(merchant))
                    return false;
            }

            // Reset dialog before requesting a new pursuit.
            Dialog = null;

            // Look up the pursuit key from Server.Pursuits.
            ushort pursuitKey = Server.PursuitIDs
                .FirstOrDefault(p => string.Equals(p.Value, pursuitName))
                .Key;

            PursuitRequest(1, merchant.ID, pursuitKey);

            if (wait)
            {
                // Wait for the Dialog to appear with a 2-second timeout.
                if (!WaitForDialog(TimeSpan.FromSeconds(2)))
                    return false;
            }

            return true;
        }

        private bool EnsureDialogForMerchant(Creature merchant)
        {
            bool reClickPerformed = false;
            ClickObject(merchant.ID);
            Timer timer = Timer.FromSeconds(2);

            // Wait until a Dialog appears.
            while (Dialog == null)
            {
                if (timer.IsTimeExpired)
                {
                    if (reClickPerformed)
                        return false;
                    ClickObject(merchant.ID);
                    reClickPerformed = true;
                    timer = Timer.FromSeconds(2); // Reset timer after re-click.
                }
                Thread.Sleep(10);
            }
            Dialog.Close();
            return true;
        }

        private bool WaitForDialog(TimeSpan timeout)
        {
            Timer timer = Timer.FromSeconds((int)timeout.TotalSeconds);
            while (Dialog == null)
            {
                if (timer.IsTimeExpired)
                    return false;
                Thread.Sleep(10);
            }
            return true;
        }


        internal void PursuitRequest(byte objType, int objID, ushort pursuitID, params object[] args)
        {
            ClientPacket clientPacket = new ClientPacket(57);
            clientPacket.WriteByte(objType);
            clientPacket.WriteInt32(objID);
            clientPacket.WriteUInt16(pursuitID);
            clientPacket.WriteArray(args);
            Enqueue(clientPacket);
        }
        internal void WithdrawMoney(int objID, int quantity)
        {
            ClientPacket clientPacket = new ClientPacket(57);
            clientPacket.WriteByte(1);
            clientPacket.WriteInt32(objID);
            clientPacket.WriteUInt16(85);
            clientPacket.WriteString8(quantity.ToString());
            Enqueue(clientPacket);
        }
        internal void DepositMoney(int objID, int quantity)
        {
            ClientPacket clientPacket = new ClientPacket(57);
            clientPacket.WriteByte(1);
            clientPacket.WriteInt32(objID);
            clientPacket.WriteInt16(82);
            clientPacket.WriteString8(quantity.ToString());
            Enqueue(clientPacket);
        }
        internal void WithdrawItem(int npcID, string item, int quantity = 0)
        {
            ClientPacket clientPacket = new ClientPacket(57);
            clientPacket.WriteByte(1);
            clientPacket.WriteInt32(npcID);
            clientPacket.WriteInt16(quantity > 0 ? (short)87 : (short)86);
            clientPacket.WriteString8(item);
            if (quantity > 0)
                clientPacket.WriteString8(quantity.ToString());
            Enqueue(clientPacket);
        }
        internal void DepositItem(int npcID, string item, int quantity = 1)
        {
            byte num = 0;
            if (!Inventory.Contains(item))
                ServerMessage((byte)ServerMessageType.ActiveMessage, "You don't own that item.");
            else
                num = Inventory[item].Slot;
            ClientPacket clientPacket = new ClientPacket(57);
            clientPacket.WriteByte(1);
            clientPacket.WriteInt32(npcID);
            clientPacket.WriteInt16(quantity > 1 ? (short)84 : (short)83);
            if (quantity > 1)
                clientPacket.WriteByte(1);
            clientPacket.WriteByte(num);
            if (quantity > 1)
                clientPacket.WriteString8(quantity.ToString());
            Enqueue(clientPacket);
        }
        internal void ReplyDialog(byte objType, int objId, ushort pursuitId, ushort pursuitIndex)
        {
            ClientPacket clientPacket = new ClientPacket(58);
            clientPacket.WriteByte(objType);
            clientPacket.WriteInt32(objId);
            clientPacket.WriteUInt16(pursuitId);
            clientPacket.WriteUInt16(pursuitIndex);
            Enqueue(clientPacket);
        }
        internal void ReplyDialog(byte objType, int objId, ushort pursuitId, ushort pursuitIndex, byte optionToClick)
        {
            ClientPacket clientPacket = new ClientPacket(58);
            clientPacket.WriteByte(objType);
            clientPacket.WriteInt32(objId);
            clientPacket.WriteUInt16(pursuitId);
            clientPacket.WriteUInt16(pursuitIndex);
            clientPacket.WriteByte(1);
            clientPacket.WriteByte(optionToClick);
            Enqueue(clientPacket);
        }
        internal void ReplyDialog(byte objType, int objId, ushort pursuitId, ushort pursuitIndex, string response)
        {
            ClientPacket clientPacket = new ClientPacket(58);
            clientPacket.WriteByte(objType);
            clientPacket.WriteInt32(objId);
            clientPacket.WriteUInt16(pursuitId);
            clientPacket.WriteUInt16(pursuitIndex);
            clientPacket.WriteByte(2);
            clientPacket.WriteString8(response);
            Enqueue(clientPacket);
        }
        internal bool UseSkill(string skillName)
        {
            Skill skill = Skillbook[skillName];

            if (skill == null)
            {
                //Console.WriteLine($"[UseSkill] You do not have skill {skillName}");
                return false;
            }

            if (!CanUseSkill(skill))
            {
                //Console.WriteLine($"[UseSkill] Skill '{skillName}' cannot be used. Check conditions in CanUseSkill.");
                return false;
            }

            ClientPacket clientPacket = new ClientPacket(62);
            clientPacket.WriteByte(skill.Slot);
            skill.LastUsed = DateTime.UtcNow;
            if (CurrentSkill != skillName)
            {
                CurrentSkill = skillName;
                if (skillName == "Charge")
                {
                    ThreadPool.QueueUserWorkItem(_ => ClientTab.DelayedUpdateStrangerList());
                }
            }
            Console.WriteLine($"[UseSkill] Using skill {skillName}");
            Enqueue(clientPacket);

            return true;
        }

       /* internal bool UseSkill(string skillName)
        {
            Console.WriteLine($"[Debug] Attempting to use skill: {skillName}");

            Skill skill = Skillbook.SkillbookDictionary.ContainsKey(skillName) ? Skillbook[skillName] : null;

            if (skill == null)
            {
                Console.WriteLine($"[Error] Skill '{skillName}' not found in Skillbook.");
                return false;
            }

            if (!CanUseSkill(skill))
            {
                Console.WriteLine($"[Debug] Skill '{skillName}' cannot be used. Check conditions in CanUseSkill.");
                return false;
            }

            lock (SkillQueueLock)
            {
                try
                {
                    ClientPacket clientPacket = new ClientPacket(62);
                    clientPacket.WriteByte(skill.Slot);
                    skill.LastUsed = DateTime.UtcNow;

                    if (_currentSkill != skillName)
                    {
                        _currentSkill = skillName;

                        if (skillName == "Charge")
                        {
                            Console.WriteLine($"[Debug] Skill 'Charge' detected. Triggering DelayedUpdateStrangerList.");
                            ThreadPool.QueueUserWorkItem(_ => ClientTab.DelayedUpdateStrangerList());
                        }
                    }

                    SkillQueue.Enqueue((skillName, clientPacket));
                    Console.WriteLine($"[Debug] Skill '{skillName}' queued successfully (Slot: {skill.Slot}).");
                }
                catch (Exception ex)
                {
                    Console.WriteLine($"[Error] Exception while queuing skill '{skillName}': {ex.Message}");
                    return false;
                }
            }

            ProcessSkillQueue();

            return true;
        }

        private void ProcessSkillQueue()
        {
            lock (SkillQueueLock)
            {
                try
                {
                    if (SkillQueue.Count == 0)
                    {
                        Console.WriteLine("[Debug] SkillQueue is empty. Nothing to process.");
                        return;
                    }

                    DateTime now = DateTime.UtcNow;

                    if (now - LastPacketSentTime < PacketCooldown)
                    {
                        Console.WriteLine($"[Debug] Packet cooldown in effect. Next packet allowed in {(PacketCooldown - (now - LastPacketSentTime)).TotalMilliseconds} ms.");
                        return;
                    }

                    var (skillName, packet) = SkillQueue.Dequeue();
                    Enqueue(packet);
                    LastPacketSentTime = now;

                    Console.WriteLine($"[Debug] Skill '{skillName}' sent successfully at {now:O}.");
                }
                catch (Exception ex)
                {
                    Console.WriteLine($"[Error] Exception while processing skill queue: {ex.Message}");
                }
            }
        }*/


        internal void ClickWorldMap(short mapId, Point point)
        {
            ClientPacket clientPacket = new ClientPacket(63);
            clientPacket.WriteInt32(mapId);
            clientPacket.WriteStruct(point);
            Enqueue(clientPacket);
        }
        internal void RemoveWeapon()
        {
            ClientPacket clientPacket = new ClientPacket(68);
            clientPacket.WriteByte(1);
            Enqueue(clientPacket);
        }
        internal void RemoveShield()
        {
            ClientPacket clientPacket = new ClientPacket(68);
            clientPacket.WriteByte(3);
            Enqueue(clientPacket);
        }
        internal void RemoveStaff()
        {
            // Check if the item in slot 1 is a staff and exists in the staff list
            var staffInSlot = EquippedItems[1];
            if (staffInSlot == null || !Staffs.Any(staff => staff.Name == staffInSlot.Name))
                return;

            // Create and enqueue the client packet for removing the staff
            var clientPacket = new ClientPacket(68);
            clientPacket.WriteByte(1);
            Enqueue(clientPacket);

            // Update cast lines for spells based on the first staff's cast lines
            var castLines = Staffs.First().CastLines;

            foreach (var spell in Spellbook.Where(spell => spell != null && castLines.ContainsKey(spell.Name)))
            {
                spell.CastLines = castLines[spell.Name];
            }
        }

        internal bool UseSpell(string spellName, Creature target = null, bool staffSwitch = true, bool wait = true)
        {
            if (Server.StopCasting)
            {
                IsCasting = false;
                return false;
            }

            if (Spellbook[spellName] == null)
            {
                //ServerMessage(0, $"Spell {spellName} not found in spellbook");
                //Console.WriteLine($"Spell {spellName} not found in spellbook");
                return false;
            }

            if (this.Bot.IsAllyAffectedByPramhOrAsleep(this.Player))
            {
                ServerMessage((byte)ServerMessageType.TopRight, $"Nothing, you're asleep");
                return false;
            }

            if (target != null)
            {
                int test = ClientLocation.DistanceFrom(target.Location);
                ServerMessage((byte)ServerMessageType.TopRight, $"Casting on {target.ID}, {test} spaces");
                DisplayTextOverTarget(2, target.ID, $"[Spell Target]");
            }


            Spell spell = Spellbook[spellName];
            byte castLines = spell.CastLines;


            lock (BashLock)
            {

                if (spell == null || !CanUseSpell(spell, target) || ((spellName == "Hide" || spellName == "White Bat Form") && Server.StopCasting))
                {
                    //Console.WriteLine($"[UseSpell] Aborted casting {spellName} on Creature ID: {target?.ID}. Reason: Validation failed.");
                    IsCasting = false;
                    return false;
                }

                if (staffSwitch)
                {
                    if (!UseOptimalStaff(spell, out castLines))
                    {
                        //Console.WriteLine("Error in Client.cs UseSpell: staffSwitch was true but CheckWeaponCastLines returned false");
                        return false;
                    }
                }

                CastedTarget = (target ?? Player);

                if (ReadyToSpell(spell.Name))
                {
                    var existingEntry = SpellHistory.FirstOrDefault(cts => cts.Creature.ID == CastedTarget.ID && cts.Spell.Name == spell.Name);

                    if (existingEntry != null)
                    {
                        if (existingEntry.CooldownEndTime > DateTime.UtcNow)
                        {
                            //Console.WriteLine($"[Debug] Skipped adding {CastedTarget.ID} to _spellHistory due to cooldown.");
                        }
                        else
                        {
                            // Update cooldown end time for re-casting
                            existingEntry.CooldownEndTime = DateTime.UtcNow.AddSeconds(1);
                        }
                    }
                    else
                    {
                        var newEntry = new SpellEntry(spell, CastedTarget)
                        {
                            CooldownEndTime = DateTime.UtcNow.AddSeconds(1)
                        };
                        SpellHistory.Add(newEntry);

                    }
                }

                if (LastSpell != spell)
                {
                    UpdateClientActionText($"{Action} Casting {spellName}");
                }

                ClientPacket clientPacket = new ClientPacket(15);
                clientPacket.WriteByte(spell.Slot);

                if (target != null && (NearbyObjects.Contains(target.ID) || target is Player))
                {
                    clientPacket.WriteInt32(target.ID);
                    clientPacket.WriteStruct(target.Location);
                }

                if (castLines > 0)
                {
                    if (IsWalking)
                    {
                        IsCasting = false;
                        return false;
                    }
                    string[] chantArray = LoadSavedChants(spellName);
                    lock (CastLock)
                    {
                        IsCasting = true;
                        ClientPacket chantPacket = new ClientPacket(77); // Begin to chant
                        chantPacket.WriteByte(castLines);
                        Enqueue(chantPacket);
                        for (int i = 0; i < castLines; i++)
                        {
                            if (ClientTab.hideLinesCbox.Checked)
                            {
                                DisplayChant(" ");
                            }
                            else if (!string.IsNullOrWhiteSpace(ClientTab.customLinesBox.Text) && !Bot._rangerNear)
                            {
                                DisplayChant(ParseCustomSpellLines());
                            }
                            else if (!string.IsNullOrWhiteSpace(chantArray[i]))
                            {
                                DisplayChant(chantArray[i]);
                            }
                            DateTime utcNow = DateTime.UtcNow;
                            Client client = (target != null) ? Server.GetClient(target.Name) : this;
                            while (DateTime.UtcNow.Subtract(utcNow).TotalMilliseconds < 1000.0)
                            {
                                if (!IsValidSpell(client, spell.Name, target))
                                {
                                    IsCasting = false;
                                    return false;
                                }
                                Thread.Sleep(10);
                            }
                            if (!IsCasting || !CanUseSpell(spell, target))
                            {
                                IsCasting = false;
                                return false;
                            }
                        }
                        if (ClientTab != null && ClientTab.hideLinesCbox.Checked)
                        {
                            DisplayChant(" ");
                        }
                        else
                        {
                            if (spell.Name == "fas spiorad" && !Bot._needFasSpiorad && !Bot._manaLessThanEightyPct)
                            {
                                IsCasting = false;
                                return false;
                            }
                            DisplayChant(spell.Name);
                        }
                    }
                }
                if (spell.Name == "fas spiorad" && ClientTab.safeFSCbox.Checked)
                {
                    if (!int.TryParse(ClientTab.safeFSTbox.Text, out int result))
                    {
                        if (Stats.CurrentHP < Stats.MaximumMP * 0.5)
                        {
                            IsCasting = false;
                            return false;
                        }
                    }
                    else if (Stats.CurrentHP < result)
                    {
                        IsCasting = false;
                        return false;
                    }
                }
                //Console.WriteLine($"[UseSpell] Casting {spellName} on Creature ID: {target?.ID}, Name: {target?.Name}");

                Enqueue(clientPacket);
                SpellCounter++;
                Bot._spellTimer = DateTime.UtcNow;
                spell.LastUsed = DateTime.UtcNow;
                IsCasting = false;
                CastedSpell = (wait ? spell : null);
                if (spell.Name != "Gem Polishing" || spell.Name.Contains("Prayer"))
                {
                    LastSpell = spell;
                }
                return !wait || WaitForSpellChant();
            }
        }

        internal void DisplayChant(string chant)
        {
            ClientPacket clientPacket = new ClientPacket(78);
            clientPacket.WriteString8(chant);
            Enqueue(clientPacket);
        }
        internal void ClickObject(int objectId)
        {
            ClientPacket clientPacket = new ClientPacket(67);
            clientPacket.WriteByte(1);
            clientPacket.WriteInt32(objectId);
            Enqueue(clientPacket);
        }
        internal void ClickObject(Location location)
        {
            Point point = new Point(location.X, location.Y);
            Console.WriteLine($"[ClickObject] Clicking object at {point}");
            ClientPacket clientPacket = new ClientPacket(67);
            clientPacket.WriteByte(3);
            clientPacket.WriteStruct(point);
            clientPacket.WriteByte(1);
            Enqueue(clientPacket);
        }
        internal void RaiseStrStat()
        {
            ClientPacket clientPacket = new ClientPacket(71);
            clientPacket.WriteByte(1);
            Enqueue(clientPacket);
        }


        #endregion

        #region SereverPacket methods
        internal void EnableMapZoom()
        {
            ServerPacket serverPacket = new ServerPacket(5);
            serverPacket.WriteUInt32(PlayerID);
            serverPacket.WriteUInt16(0);
            serverPacket.WriteByte((byte)(GetCheats(Cheats.ZoomableMap) ? 2 : Path));
            serverPacket.WriteUInt16(0);
            Enqueue(serverPacket);
        }
        internal void Attributes(StatUpdateFlags value, Statistics stats)
        {
            ServerPacket serverPacket = new ServerPacket(8);
            if (GetCheats(Cheats.GmMode))
            {
                value |= StatUpdateFlags.GameMasterA;
            }
            if (stats.Mail != 0)
            {
                value |= (StatUpdateFlags.UnreadMail | StatUpdateFlags.Secondary);
            }
            serverPacket.WriteByte((byte)value);
            if (value.HasFlag(StatUpdateFlags.Primary))
            {
                serverPacket.Write(new byte[3]);
                serverPacket.WriteByte(stats.Level);
                serverPacket.WriteByte(stats.Ability);
                serverPacket.WriteUInt32(stats.MaximumHP);
                serverPacket.WriteUInt32(stats.MaximumMP);
                serverPacket.WriteByte(stats.CurrentStr);
                serverPacket.WriteByte(stats.CurrentInt);
                serverPacket.WriteByte(stats.CurrentWis);
                serverPacket.WriteByte(stats.CurrentCon);
                serverPacket.WriteByte(stats.CurrentDex);
                serverPacket.WriteBoolean(stats.HasUnspentPoints);
                serverPacket.WriteByte(stats.UnspentPoints);
                serverPacket.WriteInt16(stats.MaximumWeight);
                serverPacket.WriteInt16(stats.CurrentWeight);
                serverPacket.Write(new byte[4]);
            }
            if (value.HasFlag(StatUpdateFlags.Current))
            {
                serverPacket.WriteUInt32(stats.CurrentHP);
                serverPacket.WriteUInt32(stats.CurrentMP);
            }
            if (value.HasFlag(StatUpdateFlags.Experience))
            {
                serverPacket.WriteUInt32(stats.Experience);
                serverPacket.WriteUInt32(stats.ToNextLevel);
                serverPacket.WriteUInt32(stats.AbilityExperience);
                serverPacket.WriteUInt32(stats.ToNextAbility);
                serverPacket.WriteUInt32(stats.GamePoints);
                serverPacket.WriteUInt32(stats.Gold);
            }
            if (value.HasFlag(StatUpdateFlags.Secondary))
            {
                serverPacket.Write(new byte[1]);
                if (GetCheats(Cheats.NoBlind) && !InArena)
                {
                    serverPacket.WriteByte(0);
                }
                else
                {
                    serverPacket.WriteByte(stats.Blind);
                }
                serverPacket.Write(new byte[4]);
                serverPacket.WriteByte((byte)stats.OffenseElement);
                serverPacket.WriteByte((byte)stats.DefenseElement);
                serverPacket.WriteByte(stats.MagicResistance);
                serverPacket.Write(new byte[1]);
                serverPacket.WriteSByte(stats.ArmorClass);
                serverPacket.WriteByte(stats.Damage);
                serverPacket.WriteByte(stats.Hit);
            }
            Enqueue(serverPacket);
        }
        internal void ServerMessage(byte type, string message)
        {
            if (!SafeScreen)
            {
                ServerPacket serverPacket = new ServerPacket(10);
                serverPacket.WriteByte(type);
                serverPacket.WriteString16(message);
                Enqueue(serverPacket);
            }
        }
        internal void DisplayTextOverTarget(byte type, int id, string message)
        {
            ServerPacket serverPacket = new ServerPacket(13);
            serverPacket.WriteByte(type);
            serverPacket.WriteInt32(id);
            serverPacket.WriteString8(message);
            Enqueue(serverPacket);
        }
        internal void RemoveObject(int objId)
        {
            ServerPacket serverPacket = new ServerPacket(14);
            serverPacket.WriteUInt32((uint)objId);
            Enqueue(serverPacket);
        }
        internal void SendAnimation(ushort animation, short speed)
        {
            ServerPacket serverPacket = new ServerPacket(41);
            serverPacket.WriteUInt32(PlayerID);
            serverPacket.WriteUInt32(PlayerID);
            serverPacket.WriteUInt16(animation);
            serverPacket.WriteUInt16(animation);
            serverPacket.WriteInt16(speed);
            Enqueue(serverPacket);

        }
        internal void SendAnimation(ushort animation, short speed, Point point)
        {
            ServerPacket serverPacket = new ServerPacket(41);
            serverPacket.WriteUInt32(0u);
            serverPacket.WriteUInt16(animation);
            serverPacket.WriteInt16(speed);
            serverPacket.WriteStruct(point);
            Enqueue(serverPacket);

        }
        internal void AddSkill(Skill skill)
        {
            ServerPacket serverPacket = new ServerPacket(44);
            serverPacket.WriteByte(skill.Slot);
            serverPacket.WriteUInt16(skill.Sprite);
            serverPacket.WriteString8(skill.Name);
            Enqueue(serverPacket);
        }
        internal void ServerDialog(byte dialogType, byte objectType, int objectID, byte unknown1, ushort sprite1, byte color1, byte unknown2, ushort sprite2, byte color2,
            ushort pursuitID, ushort dialogID, bool previousButton, bool nextButton, byte unknown3, string objectName, string message)
        {
            ServerPacket serverPacket = new ServerPacket(48);
            serverPacket.WriteByte(dialogType);
            serverPacket.WriteByte(objectType);
            serverPacket.WriteInt32(objectID);
            serverPacket.WriteByte(unknown1);
            serverPacket.WriteUInt16(sprite1);
            serverPacket.WriteByte(color1);
            serverPacket.WriteByte(unknown2);
            serverPacket.WriteUInt16(sprite2);
            serverPacket.WriteByte(color2);
            serverPacket.WriteUInt16(pursuitID);
            serverPacket.WriteUInt16(dialogID);
            serverPacket.WriteBoolean(previousButton);
            serverPacket.WriteBoolean(nextButton);
            serverPacket.WriteByte(unknown3);
            serverPacket.WriteString8(objectName);
            serverPacket.WriteString16(message);
            Enqueue(serverPacket);
        }
        internal void DisplayAisling(Player player)
        {
            _ = player.Location;
            ushort spriteID = player.SpriteID;
            if (player == Player && SpriteOverrideEnabled)
            {
                spriteID = SpriteOverride;
            }
            ServerPacket serverPacket = new ServerPacket(51);
            serverPacket.WriteStruct(player.Location);
            serverPacket.WriteByte((byte)player.Direction);
            serverPacket.WriteInt32(player.ID);
            if (spriteID == 0)
            {
                serverPacket.WriteUInt16(player.HeadSprite);
                if (player.BodySprite == 0 && GetCheats(Cheats.SeeHidden) && !InArena)
                {
                    serverPacket.WriteByte(80);
                }
                else
                {
                    serverPacket.WriteByte(player.BodySprite);
                }
                serverPacket.WriteUInt16(player.ArmorSprite1);
                serverPacket.WriteByte(player.BootsSprite);
                serverPacket.WriteUInt16(player.ArmorSprite2);
                serverPacket.WriteByte(player.ShieldSprite);
                serverPacket.WriteUInt16(player.WeaponSprite);
                serverPacket.WriteByte(player.HeadColor);
                serverPacket.WriteByte(player.BootColor);
                serverPacket.WriteByte(player.AccessoryColor1);
                serverPacket.WriteUInt16(player.AccessorySprite1);
                serverPacket.WriteByte(player.AccessoryColor2);
                serverPacket.WriteUInt16(player.AccessorySprite2);
                serverPacket.WriteByte(player.AccessoryColor3);
                serverPacket.WriteUInt16(player.AccessorySprite3);
                serverPacket.WriteByte(player.LanternSize);
                serverPacket.WriteByte(player.RestPosition);
                serverPacket.WriteUInt16(player.OvercoatSprite);
                serverPacket.WriteByte(player.OvercoatColor);
                serverPacket.WriteByte(player.BodyColor);
                serverPacket.WriteBoolean(player.IsHidden);
                serverPacket.WriteByte(player.FaceSprite);
            }
            else
            {
                serverPacket.WriteUInt16(ushort.MaxValue);
                serverPacket.WriteUInt16((ushort)(spriteID + 16384));
                serverPacket.WriteByte(player.HeadColor);
                serverPacket.WriteByte(player.BootColor);
                serverPacket.WriteUInt16(0);
                serverPacket.WriteUInt32(0u);
            }
            serverPacket.WriteByte(player.NameTagStyle);

            if (player.BodySprite == 0 && !GetCheats(Cheats.SeeHidden))
            {
                Map map = Map;
                if (map != null && map.Name?.Contains("Arena") == false && !InArena)
                    serverPacket.WriteString8(string.Empty);
                else
                    serverPacket.WriteString8(player.Name);
            }
            else
            {
                serverPacket.WriteString8(player.Name);
            }
            serverPacket.WriteString8(player.GroupName);
            Enqueue(serverPacket);
        }
        internal void Walk(Direction dir)
        {
            if (Dialog == null || !Server.StopWalking || dir != Direction.Invalid || IsRefreshingData == 1)
            {
                _walkCallCount++;
                LastStep = DateTime.UtcNow;

                if (ServerDirection != dir)
                {
                    Turn(dir);
                }

                HasWalked = true;

                ClientPacket clientPacket = new ClientPacket(6); // walk
                clientPacket.WriteByte((byte)dir);
                clientPacket.WriteByte(StepCount++);
                Enqueue(clientPacket);

                ServerPacket serverPacket = new ServerPacket(12); // creaturewalk
                serverPacket.WriteUInt32(PlayerID);
                serverPacket.WriteStruct(ClientLocation);
                serverPacket.WriteByte((byte)dir);

                Enqueue(serverPacket);

                ClientLocation = ClientLocation.Offsetter(dir);
                LastStep = DateTime.UtcNow;

                UpdateClientActionText($"{Action} Walking {dir}");
            }
            else
            {
                IsWalking = false;
                Thread.Sleep(100);
            }
        }
        internal void Cooldown(bool isSkill, byte slot, uint ticks)
        {
            ServerPacket serverPacket = new ServerPacket(63);
            serverPacket.WriteBoolean(isSkill);
            serverPacket.WriteByte(slot);
            serverPacket.WriteUInt32(ticks);
            Enqueue(serverPacket);
        }
        #endregion

        private void AutoAscendLoop()
        {
            // Create an instance of the AutoAscendManager
            var autoAscendManager = new AutoAscendManager(this, Server);

            while (_connected)
            {
                try
                {
                    autoAscendManager.AutoAscendTask();
                }
                catch (Exception ex)
                {
                    Console.WriteLine($"Error in AutoAscendLoop: {ex.Message}");
                }

                Thread.Sleep(100);
            }
        }

        #region Networking
        /// <summary>
        /// Establishes a connection and begins receiving data. Begins a new _clientLoopThread
        /// and starts it.
        /// </summary>
        /// <param name="endPoint">The remote endpoint to connect to.</param>
        internal void Connect(EndPoint endPoint)
        {
            _serverSocket.Connect(endPoint);
            _connected = true;
            _clientSocket.BeginReceive(_clientBuffer, 0, _clientBuffer.Length, SocketFlags.None, new AsyncCallback(ClientEndReceive), this);
            _serverSocket.BeginReceive(_serverBuffer, 0, _serverBuffer.Length, SocketFlags.None, new AsyncCallback(ServerEndReceive), this);
            _clientLoopThread = new Thread(ClientLoop);
            _clientLoopThread.Start();
            _autoAscendLoopThread = new Thread(AutoAscendLoop);
            _autoAscendLoopThread.Start();
        }

        /// <summary>
        /// Main client loop that handles sending and receiving packets.
        /// </summary>
        private void ClientLoop()
        {
            Thread.GetDomain().UnhandledException += Program.ExceptionHandler;
            _connected = true;

            while (_connected)
            {
                try
                {
                    ProcessSendQueue();
                    ProcessReceiveQueue();
                }
                catch (Exception ex)
                {
                    Console.WriteLine($"[ClientLoop] Exception: {ex}");
                    _connected = false;
                }

                Thread.Sleep(5);
            }

            HandleDisconnect();
            RestoreWindow();
            CleanupClient();
        }

        private void ProcessSendQueue()
        {
            lock (_sendQueue)
            {
                while (_sendQueue.Count > 0)
                {
                    Packet packet = _sendQueue.Dequeue();
                    HandlePacketSending(packet);
                }
            }
        }

        private void HandlePacketSending(Packet packet)
        {
            Socket socket;
            byte[] array;

            if (packet is ClientPacket clientPacket)
            {
                LogClientPacket(clientPacket);
                PrepareClientPacketForSending(clientPacket);
                socket = _serverSocket;
            }
            else if (packet is ServerPacket serverPacket)
            {
                LogServerPacket(serverPacket);
                PrepareServerPacketForSending(serverPacket);
                socket = _clientSocket;
            }
            else
            {
                return;
            }

            array = packet.CreatePacket();

            try
            {
                socket.BeginSend(array, 0, array.Length, SocketFlags.None, EndSend, socket);
            }
            catch (Exception ex)
            {
                LogException(ex);
            }
        }

        private void PrepareClientPacketForSending(ClientPacket clientPacket)
        {
            if (clientPacket.IsDialog) clientPacket.EncryptDialog();
            if (clientPacket.Opcode == 98) _serverOrdinal = clientPacket.Sequence;
            if (clientPacket.ShouldEncrypt)
            {
                clientPacket.Sequence = _serverOrdinal++;
                clientPacket.Encrypt(Crypto);
            }
        }

        private void PrepareServerPacketForSending(ServerPacket serverPacket)
        {
            if (serverPacket.ShouldEncrypt)
            {
                serverPacket.Sequence = _clientOrdinal++;
                serverPacket.Encrypt(Crypto);
            }
        }

        private void LogClientPacket(ClientPacket clientPacket)
        {
            //Console.WriteLine($"[DEBUG] ({Name}) Sending ClientPacket. Opcode: {clientPacket.Opcode} ({clientPacket.ToString()}), Length: {clientPacket.Data.Length}");

            ClientPacket clientPacketToLog = clientPacket.Copy();
            if (clientPacketToLog != null && ClientTab != null && !ClientTab.IsDisposed)
            {
                ClientTab.LogPackets(clientPacketToLog);
            }
        }

        private void LogServerPacket(ServerPacket serverPacket)
        {
            //Console.WriteLine($"[DEBUG] ({Name}) Received ServerPacket. Opcode: {serverPacket.Opcode} ({serverPacket.ToString()}), Length: {serverPacket.Data.Length}");

            ServerPacket serverPacketToLog = serverPacket.Copy();
            if (serverPacketToLog != null && ClientTab != null && !ClientTab.IsDisposed)
            {
                ClientTab.LogPackets(serverPacketToLog);
            }
        }

        private void LogException(Exception ex)
        {
            string basePath = AppDomain.CurrentDomain.BaseDirectory;

            string logsFolder = System.IO.Path.Combine(basePath, "Logs");
            if (!Directory.Exists(logsFolder))
            {
                Directory.CreateDirectory(logsFolder);
            }

            string crashLogsFolder = System.IO.Path.Combine(logsFolder, "CrashLogs");
            if (!Directory.Exists(crashLogsFolder))
            {
                Directory.CreateDirectory(crashLogsFolder);
            }

            string filename = $"{DateTime.Now:MM-dd-HH-yyyy_hh-mm-ss_tt}.log";
            string filepath = System.IO.Path.Combine(crashLogsFolder, filename);

            File.WriteAllText(filepath, ex.ToString());
        }


        private void ProcessReceiveQueue()
        {
            lock (_receiveQueue)
            {
                while (_receiveQueue.Count > 0)
                {
                    Packet packet = _receiveQueue.Dequeue();
                    HandlePacketReceiving(packet);
                }
            }
        }

        private void HandlePacketReceiving(Packet packet)
        {
            if (packet.ShouldEncrypt) packet.Decrypt(Crypto);
            bool shouldEnqueue = true;

            if (packet is ClientPacket clientPacket)
            {
                shouldEnqueue = HandleClientPacket(clientPacket);
            }
            else if (packet is ServerPacket serverPacket)
            {
                shouldEnqueue = HandleServerPacket(serverPacket);
            }

            if (shouldEnqueue)
            {
                Enqueue(packet);
            }
        }

        private bool HandleClientPacket(ClientPacket clientPacket)
        {
            if (clientPacket.IsDialog) clientPacket.DecryptDialog();

            ClientMessageHandler clientHandler = Server.ClientMessage[clientPacket.Opcode];
            return TryHandleClientPacket(clientHandler, clientPacket);
        }

        private bool HandleServerPacket(ServerPacket serverPacket)
        {
            ServerMessageHandler serverHandler = Server.ServerMessage[serverPacket.Opcode];
            //Console.WriteLine($"[DEBUG] ({Name}) Received ServerPacket. Opcode: {serverPacket.Opcode} ({serverPacket.ToString()}), Length: {serverPacket.Data.Length}");
            return TryHandleServerPacket(serverHandler, serverPacket);
        }

        private bool TryHandleClientPacket(ClientMessageHandler handler, ClientPacket packet)
        {
            bool result = true;

            if (handler != null)
            {
                lock (Server.SyncObj)
                {
                    try
                    {
                        result = handler(this, packet);
                    }
                    catch
                    {
                        result = false;
                    }
                }
            }

            return result;
        }

        private bool TryHandleServerPacket(ServerMessageHandler handler, ServerPacket packet)
        {
            bool result = true;

            if (handler != null)
            {
                lock (Server.SyncObj)
                {
                    try
                    {
                        result = handler(this, packet);
                    }
                    catch
                    {
                        result = false;
                    }
                }
            }

            return result;
        }


        private void HandleDisconnect()
        {
            try
            {
                _clientSocket.Disconnect(false);
                _serverSocket.Disconnect(false);
            }
            catch
            {
            }
        }

        private void RestoreWindow()
        {
            try
            {
                NativeMethods.SetForegroundWindow((int)hWnd);
                NativeMethods.ShowWindow(hWnd, 1u);
                FlashWindowEx(Process.GetProcessById(processId).MainWindowHandle);
            }
            catch
            {
            }
        }

        private void CleanupClient()
        {
            Thread.Sleep(500);
            lock (Server._clientListLock)
            {
                Server.ClientList.Remove(this);
            }
            Thread.Sleep(100);
            Server.MainForm.RemoveClientTab(this);
        }


        internal bool FlashWindowEx(IntPtr hWnd)
        {
            if (IsOSCompatible)
            {
                Interop.FLASHWINFO flashwinfo = NativeMethods.fInfo(hWnd, 15u, uint.MaxValue, 0u);
                return NativeMethods.FlashWindowEx(ref flashwinfo);
            }
            return false;
        }

        internal void CheckNetStat()
        {
            try
            {
                if (TryGetPortFromRemoteEndPoint(_clientSocket.RemoteEndPoint.ToString(), out int port))
                {
                    string netStatData = GetNetStatData();

                    if (TryGetProcessIdForPort(netStatData, port, out int procID))
                    {
                        processId = procID;
                        hWnd = Process.GetProcessById(processId).MainWindowHandle;

                        NativeMethods.SetWindowText(hWnd, Name);
                    }
                }
            }
            catch
            {
                DisconnectWait();
            }
        }

        private bool TryGetPortFromRemoteEndPoint(string remoteEndPoint, out int port)
        {
            return int.TryParse(remoteEndPoint.Replace("127.0.0.1:", ""), out port);
        }

        private string GetNetStatData()
        {
            string netStatData = string.Empty;

            using (Process process = new Process())
            {
                process.StartInfo.FileName = "cmd.exe";
                process.StartInfo.UseShellExecute = false;
                process.StartInfo.RedirectStandardOutput = true;
                process.StartInfo.CreateNoWindow = true;
                process.StartInfo.Arguments = "/c netstat -a -n -o";
                process.OutputDataReceived += (sender, e) =>
                {
                    if (!string.IsNullOrEmpty(e.Data))
                    {
                        netStatData += e.Data + Environment.NewLine;
                    }
                };

                process.Start();
                process.BeginOutputReadLine();
                process.WaitForExit();
            }

            return netStatData;
        }

        private bool TryGetProcessIdForPort(string netStatData, int port, out int processId)
        {
            processId = 0;
            string pattern = $@"TCP\s+127.0.0.1:{port}\s+127.0.0.1:2610\s+ESTABLISHED\s+([0-9]+)";

            var match = Regex.Match(netStatData, pattern);
            if (match.Success && int.TryParse(match.Groups[1].Value, out int procID))
            {
                processId = procID;
                return true;
            }

            return false;
        }


        /// <summary>
        /// Asynchronously finalizes the sending of a packet.
        /// </summary>
        /// <param name="ar">Result of the async operation.</param>
        private void EndSend(IAsyncResult ar)
        {
            ((Socket)ar.AsyncState).EndSend(ar);
        }

        /// <summary>
        /// Asynchronously receives data from the client, and processes the information.
        /// </summary>
        /// <param name="ar">Result of the async operation.</param>
        private void ClientEndReceive(IAsyncResult ar)
        {
            try
            {
                int length = _clientSocket.EndReceive(ar);
                //Console.WriteLine($"[Client] {Name} Data received: {length} bytes.");

                if (length == 0)
                {
                    //Console.WriteLine($"[Client] {Name} Zero bytes received. Buffer content for inspection:");
                    //Console.WriteLine($"[Client] {Name} Raw buffer: {BitConverter.ToString(_clientBuffer)}");

                    //Console.WriteLine($"[Client] {Name} Zero bytes received, disconnecting...");
                    DisconnectWait();
                }
                else
                {
                    byte[] data = new byte[length];
                    Buffer.BlockCopy(_clientBuffer, 0, data, 0, length);
                    //Console.WriteLine($"[Client] {Name} Raw data received: {BitConverter.ToString(data)}");

                    _fullClientBuffer.AddRange(data);

                    //Console.WriteLine($"[Client] {Name} Full buffer size: {_fullClientBuffer.Count} bytes.");

                    while (_fullClientBuffer.Count > 3)
                    {
                        int count = (_fullClientBuffer[1] << 8) + _fullClientBuffer[2] + 3;
                        //Console.WriteLine($"[Client] {Name} Packet size detected: {count} bytes.");

                        if (count > _fullClientBuffer.Count)
                        {
                            //Console.WriteLine($"[Client] {Name} Incomplete packet, waiting for more data...");
                            break;
                        }

                        List<byte> range = _fullClientBuffer.GetRange(0, count);
                        _fullClientBuffer.RemoveRange(0, count);
                        //Console.WriteLine($"[Client] {Name} Processed packet of size: {range.Count} bytes. Remaining buffer size: {_fullClientBuffer.Count} bytes.");

                        ClientPacket clientPacket = new ClientPacket(range.ToArray());

                        //Console.WriteLine($"[Client] {Name} Processed packet Opcode: {clientPacket.Opcode} ({clientPacket.ToString()}), Length: {clientPacket.Data.Length}");

                        lock (_receiveQueue)
                        {
                            _receiveQueue.Enqueue(clientPacket);
                        }
                    }
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine($"[Client] {Name} Exception in EndReceive: {ex}");
                DisconnectWait();
            }
            finally
            {
                clientReceiving = false;

                if (_connected && !clientReceiving)
                {
                    try
                    {
                        clientReceiving = true;
                        _clientSocket.BeginReceive(_clientBuffer, 0, _clientBuffer.Length, SocketFlags.None, ClientEndReceive, null);
                    }
                    catch (SocketException ex)
                    {
                        Console.WriteLine($"[Client] {Name} SocketException in BeginReceive: {ex.SocketErrorCode} - {ex.Message}");
                        DisconnectWait();
                    }
                    catch (ObjectDisposedException ex)
                    {
                        Console.WriteLine($"[Client] {Name} ObjectDisposedException in BeginReceive: {ex.Message}");
                        // Socket already disposed, nothing more to do
                    }
                }
            }

        }

        /// <summary>
        /// Asynchronously receives data from the client, and processes the information.
        /// </summary>
        /// <param name="ar">Result of the async operation.</param>
        private void ServerEndReceive(IAsyncResult ar)
        {
            try
            {
                int length = _serverSocket.EndReceive(ar);
                //Console.WriteLine($"[Server] {Name} Data received: {length} bytes.");

                if (length == 0)
                {
                    //Console.WriteLine($"[Server] {Name} Zero bytes received. Buffer content for inspection:");
                    //Console.WriteLine($"[Server] {Name} Raw buffer: {BitConverter.ToString(_serverBuffer)}");

                    //Console.WriteLine($"[Server] {Name} Zero bytes received, disconnecting...");
                    DisconnectWait();
                }
                else
                {
                    byte[] data = new byte[length];
                    Buffer.BlockCopy(_serverBuffer, 0, data, 0, length);
                    //Console.WriteLine($"[Server] {Name} Raw data received: {BitConverter.ToString(data)}");

                    _fullServerBuffer.AddRange(data);

                    //Console.WriteLine($"[Server] {Name} Full buffer size: {_fullServerBuffer.Count} bytes.");

                    while (_fullServerBuffer.Count > 3)
                    {
                        int count = (_fullServerBuffer[1] << 8) + _fullServerBuffer[2] + 3;
                        //Console.WriteLine($"[Server] {Name} Packet size detected: {count} bytes.");

                        if (count > _fullServerBuffer.Count)
                        {
                            //Console.WriteLine($"[Server] {Name} Incomplete packet, waiting for more data...");
                            break;
                        }

                        List<byte> range = _fullServerBuffer.GetRange(0, count);
                        _fullServerBuffer.RemoveRange(0, count);
                        //Console.WriteLine($"[Server] {Name} Processed packet of size: {range.Count} bytes. Remaining buffer size: {_fullServerBuffer.Count} bytes.");

                        ServerPacket serverPacket = new ServerPacket(range.ToArray());

                        //Console.WriteLine($"[Server] {Name} Processed packet Opcode: {serverPacket.Opcode} ({serverPacket.ToString()}), Length: {serverPacket.Data.Length}");

                        lock (_receiveQueue)
                        {
                            _receiveQueue.Enqueue(serverPacket);
                        }
                    }
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine($"[Server] {Name} Exception in EndReceive: {ex}");
                DisconnectWait();
            }
            finally
            {
                // Reset the receiving flag and start receiving again.
                serverReceiving = false;

                if (_connected && !serverReceiving)
                {
                    try
                    {
                        serverReceiving = true;
                        _serverSocket.BeginReceive(_serverBuffer, 0, _serverBuffer.Length, SocketFlags.None, ServerEndReceive, null);
                    }
                    catch (SocketException ex)
                    {
                        Console.WriteLine($"[Server] {Name} SocketException in BeginReceive: {ex.SocketErrorCode} - {ex.Message}");
                        DisconnectWait();
                    }
                    catch (ObjectDisposedException ex)
                    {
                        Console.WriteLine($"[Server] {Name} ObjectDisposedException in BeginReceive: {ex.Message}");
                        // Socket already disposed, nothing more to do
                    }
                }
            }

        }

        /// <summary>
        /// Enqueues a packet to be sent to the server.
        /// </summary>
        /// <param name="packetArray">The packet array to be sent</param> 
        internal void Enqueue(params Packet[] packetArray)
        {
            if (Thread.CurrentThread.ManagedThreadId == Program.MainForm.ThreadID)
                ThreadPool.QueueUserWorkItem(delegate { Enqueue(packetArray); });
            else
            {
                lock (_sendQueue)
                {
                    Packet[] array = packetArray;
                    foreach (Packet packet in array)
                    {
                        _sendQueue.Enqueue(packet);
                    }
                }
            }
        }

        /// <summary>
        /// Disconnect from the server.
        /// </summary>
        /// <param name="wait">True or false depending on whether we are disconnecting</param>
        internal void DisconnectWait(bool wait = false)
        {
            _connected = false;
            if (wait)
            {
                _clientLoopThread.Join(1000);
                if (_clientLoopThread.IsAlive)
                {
                    _clientLoopThread.Abort();
                }
            }
        }


        #endregion

    }
}


