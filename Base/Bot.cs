using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Media;
using System.Runtime.InteropServices;
using System.Threading;
using System.Threading.Tasks;
using System.Windows.Forms;
using Talos.Bashing;
using Talos.Definitions;
using Talos.Definitions;
using Talos.Extensions;
using Talos.Forms;
using Talos.Forms.UI;
using Talos.Helper;
using Talos.Maps;
using Talos.Objects;
using Talos.Properties;
using Talos.Structs;
using Talos.Utility;
using static System.Windows.Forms.VisualStyles.VisualStyleElement;
using static System.Windows.Forms.VisualStyles.VisualStyleElement.Window;

namespace Talos.Base
{
    internal class Bot : BotBase
    {
        private const int LONG_SLEEP_MS = 150000;
        private const int RESCUE_SLEEP_MS = 100;
        private const int MERCHANT_WAIT_MS = 2500;
        private const short SPECIAL_MAP_ID = 5271;
        private const short DOJO_MAP_ID = 3071;
        private static object _lock { get; set; } = new object();
        private Dictionary<int, bool> routeFindPerformed = new Dictionary<int, bool>();
        private int _dropCounter;
        private int currentWaypointIndex = 0;
        private DateTime _sprintPotionLastUsed = DateTime.MinValue;
        internal Creature creature;
        internal Creature target;
        internal BashingBase BashingBase;
        CommandManager commandManager = CommandManager.Instance;
        private readonly BugManager _bugManager;

        private bool _autoStaffSwitch;
        private bool _fasSpiorad;
        private bool _isSilenced;
        private bool bashClassSet;
        private DateTime _lastHidden = DateTime.MinValue;
        internal bool _needFasSpiorad = true;
        internal bool _manaLessThanEightyPct = true;
        internal bool _rangerNear = false;
        internal bool _shouldAlertItemCap;
        internal bool _recentlyAoSithed;
        internal bool[] itemDurabilityAlerts = new bool[5];

        internal bool _dontWalk;
        internal bool _dontCast;
        internal bool _dontBash;
        private int? _leaderID;
        internal bool _hasRescue;

        internal byte _fowlCount;
        internal bool _receivedDblBonus = false;
        internal int currentWay;

        internal DateTime _lastEXP = DateTime.MinValue;
        internal DateTime _lastDisenchanterCast = DateTime.MinValue;
        internal DateTime LastGrimeScentCast = DateTime.MinValue;
        internal DateTime _skullTime = DateTime.MinValue;
        internal DateTime _lastRefresh = DateTime.MinValue;
        internal DateTime _lastVineCast = DateTime.MinValue;
        internal DateTime _botChecks = DateTime.MinValue;
        internal DateTime _lastExpBonusAppliedTime = DateTime.MinValue;
        internal DateTime _spellTimer = DateTime.MinValue;
        internal DateTime _lastUsedGem = DateTime.MinValue;
        private DateTime _lastAoPoison = DateTime.MinValue;
        private DateTime _lastWakeScroll = DateTime.MinValue;
        private DateTime _lastUsedFungusBeetle = DateTime.MinValue;
        private DateTime _lastUsedBeetleAid = DateTime.MinValue;
        private DateTime _lastUsedVanishElixir = DateTime.MinValue;
        internal TimeSpan _expBonusElapsedTime = TimeSpan.Zero;
        internal DateTime _lastUnstick = DateTime.MinValue;

        internal List<Ally> _allyList = new List<Ally>();
        internal List<Enemy> _enemyList = new List<Enemy>();
        internal List<Player> _playersExistingOver250ms = new List<Player>();
        internal List<Player> _skulledPlayers = new List<Player>();
        internal List<String> GMdetectedonline = new List<string>();
        internal List<Creature> _nearbyValidCreatures = new List<Creature>();
        internal List<Location> ways = new List<Location>();

        internal List<Player> NearbyAllies { get; set; } = new List<Player>();
        internal HashSet<string> _allyListName = new HashSet<string>(StringComparer.CurrentCultureIgnoreCase);
        internal HashSet<ushort> _enemyListID = new HashSet<ushort>();



        internal System.Windows.Forms.Label currentAction;
        private Location _lastBubbleLocation;
        private Location _pcDeathSpot = new Location(3052, 27, 19);
        private string _bubbleType;

        private SoundPlayer soundPlayer = new SoundPlayer();
        private bool _swappingNecklace;
        private DateTime _lastUsedMonsterCall = DateTime.MinValue;
        internal bool _hasWhiteDugon;
        internal bool _hasGreenDugon;
        private List<Player> _nearbyPlayers;
        internal bool _circle1;
        internal bool _circle2;
        internal DateTime _doorTime;
        internal Point _doorPoint;
        private bool _together;
        private DateTime _followerTimer;
        internal DateTime _lastMushroomBonusAppliedTime;
        internal DateTime _lastSkillBonusAppliedTime;

        internal TimeSpan _mushroomBonusElapsedTime;

        internal bool InsectNetRepair = false;
        internal DateTime _hammerTimer = DateTime.MinValue;
        internal bool _spikeGameToggle;
        private DateTime _animationTimer = DateTime.MinValue;
        private bool generaterandom;
        private bool equipattempted;
        private DateTime neckSwap;
        private bool autoForm;
        private DateTime LastPointInSync = DateTime.MinValue;
        private DateTime LastDirectionInSync = DateTime.MinValue;
        private bool bashWffUsed;
        private DateTime assailUse = DateTime.MinValue;
        private DateTime skillUse = DateTime.MinValue;
        private bool hasrepaired;
        private bool _hasDeposited;
        internal bool toldUsAboutPotofGold;
        internal bool madeLepNet;
        private DateTime _lastUsedHealingPotion;
        private Creature nonMainTarget;
        private Task dojoSpellTask;
        private Location dojoPoint;
        private DateTime _lastLootTime = DateTime.MinValue;
        private const int LootIntervalMs = 500; // adjust as needed
        private DateTime _lastDropTime = DateTime.MinValue;
        private const int DropIntervalMs = 5000; // adjust as needed

        internal bool HasInsectNet { get; set; }
        public bool RecentlyUsedGlowingStone { get; set; } = false;
        public bool RecentlyUsedDragonScale { get; set; } = false;
        public bool RecentlyUsedFungusExtract { get; set; } = false;
        internal AllyPage Alts { get; set; }
        internal AllyPage Group { get; set; }
        internal EnemyPage AllMonsters { get; set; }



        internal Bot(Client client, Server server) : base(client, server)
        {
            _bugManager = new BugManager(Client);

            AddTask(BotLoop);
            AddTask(SoundLoop);
            AddTask(WalkLoop);
            AddTask(MultiLoop);
            AddTask(AnimationLoop);
            AddTask(DojoLoop);
        }

        private async Task AnimationLoop(CancellationToken token)
        {
            while (!token.IsCancellationRequested)
            {
                try
                {
                    if (Client.Map == null || !Client.Map.IsLoaded)
                    {
                        await Task.Delay(1000, token); // Wait for map to load
                        continue;
                    }

                    // Ensure we are checking a valid MapID in the blacklist
                    if (!Pathfinder.BlackList.TryGetValue(Client.Map.MapID, out Location[] blacklistTiles))
                    {
                        await Task.Delay(1000, token); // If no blacklist for this map, just wait and retry
                        continue;
                    }

                    // Iterate through blacklisted tiles
                    foreach (var loc in blacklistTiles)
                    {
                        if (Client.Map.Tiles.ContainsKey(loc.Point))
                        {
                            // Confirm that the unwalkable tile exists in the map
                            // Console.WriteLine($"Confirmed unwalkable tile at ({loc.X}, {loc.Y}) exists in Map.Tiles");

                            // Send animation packet if needed (Modify with your actual animation logic)
                            Client.SendAnimation(96, 100, loc.Point);
                        }
                        else
                        {
                            // Report missing tiles
                            Console.WriteLine($"WARNING: Expected unwalkable tile ({loc.X}, {loc.Y}) is missing from Map.Tiles!");
                        }
                    }

                    // Sleep to prevent excessive looping and CPU usage
                    await Task.Delay(2000, token);
                }
                catch (OperationCanceledException)
                {
                    break;
                }
                catch (Exception ex)
                {
                    Console.WriteLine($"[AnimationLoop] Exception occurred: {ex}");
                }
            }
        }


        private async Task MultiLoop(CancellationToken token)
        {
            try
            {
                while (!token.IsCancellationRequested)
                {
                    if (Client.Name == "Brightness")
                    //    Console.WriteLine("MultiLoop Pulse");
                        
                    // Block if Client or ClientTab is null
                    if (Client == null || Client.ClientTab == null)
                        continue;

                    Client.InventoryFull = Client.Inventory.IsFull;

                    // Block if conditions for ranger or exchange are not met
                    if ((_rangerNear && Client.ClientTab.rangerStopCbox.Checked) || Client.ExchangeOpen)
                    {
                        await Task.Delay(100, token);
                        continue;
                    }

                    //CheckScrollTimers();
                    BashLoop();
                    HolidayEvents();
                    // ItemFinding();
                    VeltainChests();
                    Raffles();
                    TaskLoop();
                    // TavalyWallHacks();
                    MonsterForm();
                    DuraLoop();

                    // Sleep before the next iteration
                    await Task.Delay(100, token);
                }
               
            }
            catch (OperationCanceledException)
            {
                Console.WriteLine($"[MultiLoop] OperationCanceledException");

            }
            catch (Exception ex)
            {
                Console.WriteLine($"[MultiLoop] Exception occurred: {ex}");
            }
        }

        #region DojoLoop
        private bool IsDojoEnabled() => string.Equals(Client.ClientTab.toggleDojoBtn.Text, "Disable");
        private void ExecuteRescue()
        {
            Client.UseSkill("Rescue");
            Thread.Sleep(RESCUE_SLEEP_MS);
        }
        internal async Task DojoLoop(CancellationToken token)
        {
            try
            {
                while (!token.IsCancellationRequested)
                {
                    // Exit if Dojo is not enabled
                    if (!IsDojoEnabled())
                        return;

                    bool isRangerNear = IsRangerNearBy();

                    if (isRangerNear)
                    {
                        await Task.Delay(LONG_SLEEP_MS, token);
                    }

                    if (Client.ClientTab.rescueCbox.Checked)
                    {
                        ExecuteRescue();
                        return;
                    }

                    // If we are not on a dojo map and regeneration is not checked, perform map transition logic.
                    if (!CONSTANTS.DOJO_MAPS.ContainsKey(Client.Map.MapID) && !Client.ClientTab.regenCaHere.Checked)
                    {
                        HandleMapTransition(isRangerNear);
                    }
                    else
                    {
                        // run the DoTrainingDojo task
                        await Task.Run(() => DoTrainingDojo(token), token);
                    }
                }
           
            }
            catch (OperationCanceledException)
            {

            }
            catch (Exception ex)
            {
                Console.WriteLine($"[DojoLoop] Exception occurred: {ex}");
            }

        }

        private void HandleMapTransition(bool isRangerNear)
        {
            if (Client.Map.MapID == SPECIAL_MAP_ID)
            {
                // Wait until we can get the merchant "Mionope"
                Creature merchant = null;
                while (merchant == null)
                {
                    merchant = Client.GetNearbyNPC("Mionope");
                    Client.Pathfind(new Location(5271, 2, 2), shouldBlock: false, avoidWarps: false);
                }
                Client.ClickObject(merchant.ID);
                Thread.Sleep(MERCHANT_WAIT_MS);
            }

            if (Client.Map.MapID != DOJO_MAP_ID && !isRangerNear)
            {
                Client.Routefind(new Location(DOJO_MAP_ID, 0, 0));
            }
            else
            {
                EnterDojo(isRangerNear);
            }
        }

        private void EnterDojo(bool isRangerNear)
        {
            Location entryPoint = new Location(DOJO_MAP_ID, 4, 5);
            if (Client.ServerLocation.DistanceFrom(entryPoint) > 5)
            {
                Client.Pathfind(entryPoint);
            }
            else
            {
                if (isRangerNear)
                    Thread.Sleep(MERCHANT_WAIT_MS);

                Creature merchant = Client.GetNearbyNPC("Niomope");
                if (merchant == null)
                    return;

                if (Client.RequestNamedPursuit(merchant, "Enter Training Dojo", false))
                {
                    Client.ReplyDialog(1, merchant.ID, 0, 2, 1);
                }
                if (Client.ClientTab.dojoAutoStaffCbox.Checked)
                {
                    Client.RemoveWeapon();
                    Client.RemoveShield();
                }
                Thread.Sleep(MERCHANT_WAIT_MS);
            }
        }

        private async Task DoTrainingDojo(CancellationToken token)
        {
            if (Client.ClientTab.chkDachaidh.Checked)
            {
                DojoDachaidh();
                return;
            }
            if (Client.ClientTab.regenCaHere.Checked)
            {
                DojoCounterRegen();
                return;
            }
            if (Client.ClientTab.flowerCbox.Checked && !string.IsNullOrEmpty(Client.ClientTab.flowerText.Text))
            {
                DojoFlower();
                return;
            }
            if (!UpdateDojoTarget())
                return;

            // Use extra spacing if needed
            if (Client.ClientTab.dojo2SpaceCbox.Checked)
            {
                HandleDojo2Space();
                return;
            }
            else if (nonMainTarget.Location.DistanceFrom(Client.ServerLocation) != 1 && !_rangerNear)
            {
                Client.Pathfind(nonMainTarget.Location);
                return;
            }

            // Face the target if not already in the correct direction
            Direction desiredDirection = nonMainTarget.Location.GetDirection(Client.ServerLocation);
            if (desiredDirection != Client.ServerDirection)
            {
                Client.Turn(desiredDirection);
            }
            else
            {
                // Start the dojo spells task if it’s not running.
                if (dojoSpellTask == null || dojoSpellTask.IsCompleted)
                {
                    dojoSpellTask = Task.Run(() => DojoSpells(token), token);
                }
                DojoSkills();
                DojoCounterRegen();
                await Task.Delay(50, token);
            }
        }

        private void HandleDojo2Space()
        {
            // Calculate candidate points around the target
            List<Location> candidates = new List<Location>
            {
                new Location(Client.ServerLocation.MapID, (short)(nonMainTarget.Location.X + 2), nonMainTarget.Location.Y),
                new Location(Client.ServerLocation.MapID, (short)(nonMainTarget.Location.X - 2), nonMainTarget.Location.Y),
                new Location(Client.ServerLocation.MapID, nonMainTarget.Location.X, (short)(nonMainTarget.Location.Y + 2)),
                new Location(Client.ServerLocation.MapID, nonMainTarget.Location.X, (short)(nonMainTarget.Location.Y - 2))
            };

            // Select the valid candidate (not walled and no nearby monsters)
            var targetPoint = candidates
                .Where(p => !Client.IsWalledIn(p) && !Client.GetAllNearbyMonsters().Any(c => c.Type == 0 && c.Location == p))
                .OrderBy(p => p.DistanceFrom(Client.ServerLocation))
                .FirstOrDefault();

            if (targetPoint.DistanceFrom(Client.ServerLocation) != 0 && !_rangerNear)
            {
                Client.Pathfind(targetPoint, 0);
            }
        }

        private bool UpdateDojoTarget()
        {
            // If nonMainTarget is valid, keep it; otherwise, try to select a new target.
            if (nonMainTarget != null &&
                nonMainTarget.Location.MapID == Client.Map.MapID &&
                Client.WithinRange(nonMainTarget) &&
                !Client.IsWalledIn(nonMainTarget.Location))
            {
                return true;
            }

            nonMainTarget = Client.GetAllNearbyMonsters(12, CONSTANTS.DOJO_MAPS[Client.Map.MapID])
                .Where(c => !Client.IsWalledIn(c.Location))
                .OrderBy(c => c.Location.DistanceFrom(Client.ServerLocation))
                .FirstOrDefault();

            return nonMainTarget != null;
        }


        private async Task DojoSpells(CancellationToken token)
        {
            if (Client == null || Client.ClientTab == null)
                return;

            token.ThrowIfCancellationRequested();

            try
            {
                // Example: process lists of dojo spells and skills
                bool waitForBowEquip = false;
                List<string> disarmSkills = Client.ClientTab.dojoSkillList
                    .Where(skill => CONSTANTS.REQUIRE_DISARM.Any(dis => skill.Contains(dis)))
                    .ToList();
                List<string> stabSkills = Client.ClientTab.dojoSkillList
                    .Where(skill => CONSTANTS.STABS.Contains(skill))
                    .ToList();
                bool hasArrowShot = Client.ClientTab.dojoSkillList.Any(skill => skill.Contains("Arrow Shot"));

                if (Client.ClientTab.dojoSpellList.Count == 0)
                    Client.ClientTab.dojoSpellList.Add("filler");

                foreach (string dojoSpell in Client.ClientTab.dojoSpellList)
                {
                    token.ThrowIfCancellationRequested();

                    foreach (string skill in disarmSkills.Where(s => Client.CanUseSkill(Client.Skillbook[s])))
                    {
                        token.ThrowIfCancellationRequested();

                        if (skill.Contains("Claw Slash"))
                        {
                            if (!Client.UseItem("Blackstar Night Claw") &&
                                !Client.UseItem("Yowien's Fist") &&
                                !Client.UseItem("Yowien's Fist1") &&
                                !Client.UseItem("Yowien's Claw") &&
                                !Client.UseItem("Yowien's Claw1"))
                            {
                                Client.UseItem("Tilian Claw");
                            }
                        }
                        else
                        {
                            Client.RemoveWeapon();
                            Client.RemoveShield();
                        }
                        if (Client.UseSkill(skill))
                        {
                            Client.RemoveWeapon();
                            Client.RemoveShield();
                            while (Client.EquippedItems[1] != null || Client.EquippedItems[3] != null)
                            {
                                await Task.Delay(5, token);
                            }
                            await Task.Delay(5, token);
                        }
                    }
                    foreach (string skill in stabSkills.Where(s => Client.CanUseSkill(Client.Skillbook[s])))
                    {
                        token.ThrowIfCancellationRequested();

                        string currentWeapon = Client.EquippedItems[1]?.Name;
                        if ((currentWeapon == null || !CONSTANTS.BOWS.Concat(CONSTANTS.DAGGERS).Any(e => currentWeapon.Contains(e))) &&
                            string.IsNullOrEmpty(Client.EquipBow()))
                        {
                            foreach (Item item in Client.Inventory)
                            {
                                token.ThrowIfCancellationRequested();

                                if (CONSTANTS.DAGGERS.Any(d => item.Name.Contains(d)))
                                {
                                    Client.UseItem(item.Name);
                                    break;
                                }
                            }
                        }
                        Client.UseSkill(skill);
                    }
                    // Check and wait for bow equip if necessary
                    string equippedWeapon = Client.EquippedItems[1]?.Name;
                    if (hasArrowShot && (equippedWeapon == null || !CONSTANTS.BOWS.Any(b => equippedWeapon.Contains(b))) &&
                        !string.IsNullOrEmpty(Client.EquipBow()))
                    {
                        waitForBowEquip = true;
                    }
                    DateTime startWait = DateTime.UtcNow;
                    while (waitForBowEquip &&
                          (equippedWeapon == null || !CONSTANTS.BOWS.Concat(CONSTANTS.DAGGERS).Any(e => equippedWeapon.Contains(e))) &&
                          DateTime.UtcNow.Subtract(startWait).TotalMilliseconds <= 500)
                    {
                        await Task.Delay(5, token);
                    }
                    waitForBowEquip = false;
                    await Task.Delay(5, token);
                    if (!string.Equals(dojoSpell, "filler"))
                    {
                        if (_needFasSpiorad)
                        {
                            Client.UseSpell("fas spiorad", staffSwitch: Client.ClientTab.dojoAutoStaffCbox.Checked, wait: false);
                        }
                        else
                        {
                            ManageSpellHistory();
                            if (!string.Equals(dojoSpell, "creag neart") && !string.Equals(dojoSpell, "Salvation"))
                            {
                                Client.UseSpell(dojoSpell, nonMainTarget, Client.ClientTab.dojoAutoStaffCbox.Checked, false);
                            }
                            else
                            {
                                Client.UseSpell(dojoSpell, (Creature)Client.Player, Client.ClientTab.dojoAutoStaffCbox.Checked, false);
                            }
                        }
                    }
                }
                await Task.Delay(5, token);
            }
 catch (OperationCanceledException)
    {
        // Handle cancellation if needed.
    }
    catch (Exception ex)
    {
        Console.WriteLine($"[DojoSpellsAsync] Exception occurred: {ex}");
    }
        }


        private void DojoSkills()
        {
            if (Client == null || Client.ClientTab == null)
                return;

            try
            {
                // Bonus spells every 5+ seconds
                if (!Client.HasEffect(EffectsBar.SpellSkillBonus1) &&
                    (DateTime.UtcNow - _lastSkillBonusAppliedTime).TotalSeconds > 5 &&
                    Client.ClientTab.dojoBonusCbox.Checked)
                {
                    bool usedBonus = false;

                    // Attempt to use the quadruple bonus if it's in the inventory.
                    if (Client.Inventory.Contains("Skill/Spell Quadruple Bonus"))
                    {
                        usedBonus = Client.UseItem("Skill/Spell Quadruple Bonus");
                    }

                    // If not used, try the triple bonus.
                    if (!usedBonus && Client.Inventory.Contains("Skill/Spell Triple Bonus"))
                    {
                        usedBonus = Client.UseItem("Skill/Spell Triple Bonus");
                    }

                    // If neither bonus was used, fall back to the leveling bonus.
                    if (!usedBonus && Client.Inventory.Contains("Skill/Spell Leveling Bonus"))
                    {
                        Client.UseItem("Skill/Spell Leveling Bonus");
                    }

                    _lastSkillBonusAppliedTime = DateTime.UtcNow;
                }

                List<string> crasherSkills = Client.ClientTab.dojoSkillList
                    .Where(skill => CONSTANTS.CRASHERS.Contains(skill))
                    .ToList();
                if (crasherSkills.Any() && !Client.HasEffect(EffectsBar.Poison))
                {
                    Client.DisplayChant("Poison Please");
                }
                if (Client.HealthPct <= 1)
                {
                    foreach (string skill in crasherSkills)
                        Client.UseSkill(skill);
                }
                else
                {
                    foreach (string skill in crasherSkills)
                    {
                        if (Client.CanUseSkill(Client.Skillbook[skill]) && Client.UseSkill("Auto Hemloch"))
                        {
                            foreach (string s in crasherSkills)
                                Client.UseSkill(s);
                            break;
                        }
                    }
                }

                foreach (string skill in Client.ClientTab.dojoSkillList
                    .Where(s => !CONSTANTS.CRASHERS.Contains(s) &&
                                !CONSTANTS.REQUIRE_DISARM.Any(r => s.Contains(r)) &&
                                !CONSTANTS.STABS.Contains(s))
                    .ToList())
                {
                    Client.UseSkill(skill);
                }
            }
            catch
            {
                // Handle exceptions as needed
            }
        }

        private void DojoFlower()
        {
            Client targetClient = Server.GetClient(Client.ClientTab.flowerText.Text);
            if (targetClient == null)
                return;

            // Regenerate a valid point if current dojoPoint is not walkable or too close to boundaries
            while (!Client.Map.IsWalkable(Client, dojoPoint) ||
                   dojoPoint.X < 6 ||
                   dojoPoint.Y < 6 ||
                   (targetClient.Map.Name.Contains("Training Dojo") &&
                    targetClient.Player.Location.DistanceFrom(dojoPoint) > 9))
            {
                dojoPoint = new Location(targetClient.Map.MapID, (short)RandomUtils.Random(1, Client.Map.Width - 1),
                                       (short)RandomUtils.Random(1, Client.Map.Height - 1));
            }

            if (Client.Map.MapID != targetClient.Map.MapID)
            {
                Creature merchant = Client.GetNearbyNPC("Pionome");
                if (merchant == null)
                    return;
                Client.ClickObject(merchant.ID);
                while (Client.Dialog == null)
                    Thread.Sleep(25);
                byte gameObjectType = Client.Dialog.ObjectType;
                int gameObjectId = Client.Dialog.ObjectID;
                ushort pursuitId = Client.Dialog.PursuitID;
                ushort dialogId = Client.Dialog.DialogID;
                if (byte.TryParse(targetClient.Map.Name.Replace("Training Dojo ", ""), out byte option))
                {
                    Client.ReplyDialog(gameObjectType, gameObjectId, pursuitId, (ushort)(dialogId + 1), 2);
                    Client.ReplyDialog(gameObjectType, gameObjectId, pursuitId, (ushort)(dialogId + 1), option);
                }
                Thread.Sleep(2000);
            }
            else
            {
                if (Client.ServerLocation.DistanceFrom(dojoPoint) > 2 && Client.Pathfind(dojoPoint))
                    return;
                if (_needFasSpiorad)
                {
                    Client.UseSpell("fas spiorad", staffSwitch: Client.ClientTab.dojoAutoStaffCbox.Checked, wait: false);
                }
                else
                {
                    Client.UseSpell("Lyliac Plant", (Creature)targetClient.Player, Client.ClientTab.dojoAutoStaffCbox.Checked, false);
                    _needFasSpiorad = true;
                }
            }
        }


        private void DojoDachaidh()
        {
            ManageSpellHistory();
            Client.UseSpell("dachaidh");
        }

        private void DojoCounterRegen()
        {
            var nearbyCreatures = Client.GetNearbyObjects().OfType<Creature>()
                .Where(obj => !(obj is Player player && player.IsHidden) && !obj.IsPoisoned)
                .ToList();

            if (Client.ClientTab.dojoRegenerationCbox.Checked)
            {
                foreach (Creature cr in nearbyCreatures.Where(c =>
                     !c.AnimationHistory.ContainsKey(187) ||
                     (DateTime.UtcNow - c.AnimationHistory[187]).TotalSeconds > 4))
                {
                    ManageSpellHistory();
                    Client.NumberedSpell("Regeneration", cr, wait: false);
                }
            }
            if (Client.ClientTab.dojoCounterAttackCbox.Checked)
            {
                foreach (Creature cr in nearbyCreatures
                             .Where(c => c is Player &&
                                  (!c.AnimationHistory.ContainsKey(184) ||
                                   (DateTime.UtcNow - c.AnimationHistory[184]).TotalSeconds > 22))
                             .OrderBy(_ => RandomUtils.Random()))
                {
                    ManageSpellHistory();
                    Client.NumberedSpell("Counter Attack", cr, wait: false);
                }
            }
        }


        #endregion

        private void VeltainChests()
        {
            if (!Client.ChestToggle || Client.InventoryFull)
                return;

            if (Client.Inventory.Contains("Treasure Chest"))
            {
                foreach (var item in Client.Inventory.Where(i => i.Sprite == 36001))
                {
                    Client.UseItem(item.Slot);
                    Thread.Sleep(500);

                    foreach (var inventoryDialogId in Client.InventoryDialogIDs)
                    {
                        if (inventoryDialogId.Key == "Veltain Treasure Chest")
                        {
                            Client.ReplyDialog(2, inventoryDialogId.Value, 0, 2);
                            Client.ReplyDialog(2, inventoryDialogId.Value, 0, 2);
                            Client.ReplyDialog(2, inventoryDialogId.Value, 0, 2, "1");
                        }
                    }
                }
            }
            else
            {
                Client.ServerMessage((byte)ServerMessageType.Whisper, "No chests found.");
                Client.ChestToggle = false;
            }
        }

        #region Raffles
        private void Raffles()
        {
            if (Client.Map == null || Client == null)
                return;

            if (Client.Map.Name == "Balanced Arena")
            {
                Client.RaffleToggle = true;
            }
            else if (Client.RaffleToggle)
            {
                Client.ServerMessage((byte)ServerMessageType.ActiveMessage, "Must be in Balanced Arena: Raffle opening is now toggled off.");
                Client.RaffleToggle = false;
                return;
            }

            if (!Client.RaffleToggle || Client.InventoryFull)
                return;

            ProcessRaffleItems("LA Raffle", "LA Raffle(x5)");
            ProcessRaffleItems("LN Raffle", "LN Raffle(x5)");

            if (!Client.Inventory.Contains("LA Raffle") &&
                !Client.Inventory.Contains("LN Raffle") &&
                Client.Map.Name != "Balanced Arena")
            {
                Client.ServerMessage((byte)ServerMessageType.ActiveMessage, "No raffles found.");
                Client.RaffleToggle = false;
            }
        }

        private void ProcessRaffleItems(string singleRaffleName, string bundleRaffleName)
        {
            if (Client.Inventory.Contains(bundleRaffleName))
            {
                int singleRaffleCount = Client.Inventory.CountOf(singleRaffleName);
                int bundleRaffleCount = Client.Inventory.CountOf(bundleRaffleName);
                int totalRaffles = singleRaffleCount + (bundleRaffleCount * 5);

                if (totalRaffles > 100)
                {
                    int bundlesToUse = (100 - singleRaffleCount) / 5;
                    var bundles = Client.Inventory.Where(item => item.Name == bundleRaffleName).Take(bundlesToUse);

                    foreach (var bundle in bundles)
                    {
                        Client.UseItem(bundle.Slot);
                    }
                }
                else
                {
                    foreach (var bundle in Client.Inventory.Where(item => item.Name == bundleRaffleName))
                    {
                        Client.UseItem(bundle.Slot);
                    }

                    Thread.Sleep(5000);
                }
            }

            while (Client.Inventory.Contains(singleRaffleName))
            {
                Client.UseItem(singleRaffleName);
                var timer = Utility.Timer.FromSeconds(5);

                while (Client.Dialog == null)
                {
                    if (timer.IsTimeExpired)
                        return;

                    Thread.Sleep(10);
                }

                Client.Dialog.DialogNext();
                Thread.Sleep(500);
            }
        }
        #endregion


        private void DuraLoop()
        {

        }

        #region BashLoop
        private void BashLoop()
        {
            try
            {
                // Grab a local reference to ensure we’re working with the same ClientTab instance
                var tab = Client?.ClientTab;
                if (tab == null || !tab.IsBashingActive)
                    return;


                if (!bashClassSet)
                {
                    SetBashClass();
                }

                if (!Client?.ClientTab?.IsBashingActive ?? true)
                {
                    return;
                }

                if (_skulledPlayers.Count > 0 && Client.ClientTab.autoRedCbox.Checked)
                {
                    return;
                }

                if (!Client.ClientTab.oneLineWalkCbox.Checked)
                    Client.ClientTab.oneLineWalkCbox.Checked = true;

                BashingBase.EnableProtection =
                    (Client.ClientTab?.Protect1Cbx?.Checked ?? false) ||
                    (Client.ClientTab?.Protect2Cbx?.Checked ?? false);

                BashingBase.ProtectName1 = (Client.ClientTab?.Protect1Cbx?.Checked ?? false)
                    ? Client.ClientTab?.Protected1Tbx?.Text
                    : null;

                BashingBase.ProtectName2 = (Client.ClientTab?.Protect2Cbx?.Checked ?? false)
                    ? Client.ClientTab?.Protected2Tbx?.Text
                    : null;

                BashingBase.AssistBasherEnabled = Client.ClientTab?.assistBasherChk?.Checked ?? false;
                BashingBase.AssistBasherName = Client.ClientTab?.leadBasherTxt?.Text;
                BashingBase.AssistBasherStray = (int)(Client.ClientTab?.numAssitantStray?.Value ?? 0);

                bool result = BashingBase.DoBashing();

                if (!result)
                {
                    WayPointWalking(true);
                }

            }
            catch (Exception ex)
            {
                Console.WriteLine($"[DEBUG] Exception caught in HandleBashingCycle: {ex.Message}");
                LogException("HandleBashingCycle", ex);
            }

        }

        private void HandleRandomWaypoints()
        {
            Console.WriteLine("[DEBUG] Entering HandleRandomWaypoints method...");
            if (!Client.ClientTab.chkRandomWaypoints.Checked)
            {
                Console.WriteLine("[DEBUG] Random waypoints not checked, exiting method...");
                return;
            }

            if (!generaterandom)
            {
                Console.WriteLine("[DEBUG] Generating new random waypoints...");
                GenerateRandomWaypoints();
                generaterandom = true;
            }
            else
            {
                Console.WriteLine("[DEBUG] Navigating to next random waypoint...");
                if (!NavigateToNextWaypoint())
                {
                    Console.WriteLine("[DEBUG] Navigation failed, forcing new random generation next time...");
                    generaterandom = false; // Regenerate if navigation fails
                }
            }
            Console.WriteLine("[DEBUG] Exiting HandleRandomWaypoints method...");
        }

        private bool NavigateToNextWaypoint()
        {
            Console.WriteLine("[DEBUG] Entering NavigateToNextWaypoint method...");
            // Ensure there are waypoints to navigate
            if (!Client.Bot.ways.Any())
            {
                Console.WriteLine("[DEBUG] No waypoints available, exiting with false...");
                return false;
            }

            // Reset index if out of bounds
            if (currentWaypointIndex >= Client.Bot.ways.Count)
            {
                Console.WriteLine("[DEBUG] Waypoint index out of bounds, resetting to 0...");
                currentWaypointIndex = 0; // Wrap around
            }

            // Get the next waypoint
            var nextWaypoint = Client.Bot.ways[currentWaypointIndex];
            //Console.WriteLine($"[NavigateToNextWaypoint] Attempting to navigate to waypoint: {nextWaypoint}");

            // Check if pathfinding is valid
            var path = Client.Pathfinder.FindPath(Client.ServerLocation, nextWaypoint);
            if (path.Count > 0)
            {
                Console.WriteLine("[DEBUG] Valid path found, pathfinding to next waypoint...");
                // Path exists; attempt to move
                Client.Pathfind(nextWaypoint);

                // Verify if we've reached the waypoint
                if (Client.ClientLocation == nextWaypoint)
                {
                    Console.WriteLine("[DEBUG] Successfully reached waypoint, moving to next...");
                    currentWaypointIndex++; // Move to the next waypoint
                }
                return true;
            }
            else
            {
                Console.WriteLine("[DEBUG] No valid path found, skipping this waypoint...");
                currentWaypointIndex++;
            }

            Console.WriteLine("[DEBUG] Exiting NavigateToNextWaypoint with false...");
            return false;
        }

        private void GenerateRandomWaypoints()
        {
            Console.WriteLine("[DEBUG] Entering GenerateRandomWaypoints method...");
            Client.ClientTab.WayForm.waypointsLBox.Items.Clear();
            Client.Bot.ways.Clear();

            foreach (var map in Server._maps.Values.Where(m => m.MapID == Client.Map.MapID))
            {
                int waypointsToGenerate = MathUtils.Clamp((map.Height + map.Width) / 8, 5, 12);

                for (int i = 0; i < waypointsToGenerate; i++)
                {
                    Location location;
                    do
                    {
                        location = new Location(map.MapID,
                            (short)RandomUtils.Random(1, Client.Map.Width - 2),
                            (short)RandomUtils.Random(1, Client.Map.Height - 2));
                    }
                    while (Client.Map.IsWall(location) || Client.Pathfinder.FindPath(Client.ServerLocation, location).Count == 0);

                    if (!Client.Bot.ways.Contains(location))
                    {
                        Client.Bot.ways.Add(location);
                        Client.ClientTab.WayForm.waypointsLBox.Items.Add($"({location.X}, {location.Y}) {map.Name}: {map.MapID}");
                    }
                }
            }
            Console.WriteLine("[DEBUG] Exiting GenerateRandomWaypoints method...");
        }


        private void SetBashClass()
        {
            // Needs to work for lowbies too
            BashingBase = null; // Clear any previously set base

            if (Client.PreviousClassFlag == PreviousClass.Pure &&
                Client.TemuairClassFlag == TemuairClass.Warrior &&
                Client.MedeniaClassFlag == (MedeniaClass.Gladiator))
            {
                BashingBase = new PureWarriorBashing(this);
                Console.WriteLine("Activated: PureWarriorBashing (Warrior + Gladiator).");
            }
            else if (Client.MedeniaClassFlag == MedeniaClass.Druid)
            {
                if (Client.DruidFormFlag == DruidForm.Feral)
                {
                    BashingBase = new FeralBashing(this);
                    Console.WriteLine("Activated: FeralBashing (Druid Feral).");
                }
                else if (Client.DruidFormFlag == DruidForm.Karura)
                {
                    BashingBase = new KaruraBashing(this);
                    Console.WriteLine("Activated: KaruraBashing (Druid Karura).");
                }
            }
            else if (Client.PreviousClassFlag == PreviousClass.Monk &&
                     Client.MedeniaClassFlag == MedeniaClass.Gladiator)
            {
                BashingBase = new MonkWarriorBashing(this);
                Console.WriteLine("Activated: MonkWarriorBashing (PreviousClass Monk + Gladiator).");
            }
            else if (Client.MedeniaClassFlag == MedeniaClass.Archer)
            {
                BashingBase = new RogueBashing(this);
                Console.WriteLine("Activated: RogueBashing (Archer).");
            }

            bashClassSet = (BashingBase != null);
        }


        private void LogException(string methodName, Exception ex)
        {
            Console.WriteLine($"[DEBUG] Logging exception from {methodName}: {ex.Message}");

            string basePath = AppDomain.CurrentDomain.BaseDirectory;

            string logsFolder = Path.Combine(basePath, "Logs");
            if (!Directory.Exists(logsFolder))
            {
                Directory.CreateDirectory(logsFolder);
            }

            string crashLogsFolder = Path.Combine(logsFolder, "BashCrashLogs");
            if (!Directory.Exists(crashLogsFolder))
            {
                Directory.CreateDirectory(crashLogsFolder);
            }

            string fileName = $"{DateTime.Now:MM-dd-HH-yyyy_hh-mm-ss_tt}.log";
            string filePath = Path.Combine(crashLogsFolder, fileName);

            File.WriteAllText(filePath, ex.ToString());
        }


        internal bool EnsureWeaponEquipped()
        {
            equipattempted = false;
            //Console.WriteLine("[DEBUG] Entering EnsureWeaponEquipped method...");
            string equippedWeapName = Client.EquippedItems[1]?.Name;
            bool hasValidWeapon = equippedWeapName != null && WeaponRegistry.MeleeWeapons.ContainsKey(equippedWeapName);

            if (hasValidWeapon)
            {
                return true;
            }

            if (!equipattempted)
            {
                //Console.WriteLine("[DEBUG] No valid weapon found. Attempting to equip one for current class...");
                if (!Client.SafeScreen)
                    Client.ServerMessage((byte)ServerMessageType.TopRight, "Equipping Weapon");

                string weaponToEquip = EquipWeaponForClass(Client.TemuairClassFlag);
                WaitForWeaponToEquip(weaponToEquip);
                equipattempted = true;
            }
            else
            {
                //Console.WriteLine("[DEBUG] Second attempt at equipping weapon failed; stopping bashing...");
                ShowWeaponErrorAndStop();
            }

            //Console.WriteLine("[DEBUG] Exiting EnsureWeaponEquipped method with false...");
            return false;
        }

        private string EquipWeaponForClass(TemuairClass classFlag)
        {
            // Minimal debug to avoid clutter; add if needed
            return classFlag switch
            {
                TemuairClass.Warrior => Client.EquipGlad(),
                TemuairClass.Rogue => Client.EquipArcher(),
                TemuairClass.Monk => Client.EquipMonk(),
                _ => string.Empty
            };
        }

        private void WaitForWeaponToEquip(string weaponToEquip)
        {
            Console.WriteLine("[DEBUG] Entering WaitForWeaponToEquip method...");
            var timer = Utility.Timer.FromMilliseconds(1500);
            while (!timer.IsTimeExpired && Client.EquippedItems[1]?.Name != weaponToEquip)
            {
                Thread.Sleep(100);
            }
            Console.WriteLine("[DEBUG] Exiting WaitForWeaponToEquip method...");
        }

        private void ShowWeaponErrorAndStop()
        {
            Console.WriteLine("[DEBUG] Entering ShowWeaponErrorAndStop method...");
            MessageBox.Show("A supported weapon is not equipped. Bashing stopped.");
            if (Client.ClientTab?.btnBashingNew.Text == "Stop Bashing")
            {
                Client.ClientTab.btnBashingNew.Text = "Start Bashing";
            }
            Console.WriteLine("[DEBUG] Exiting ShowWeaponErrorAndStop method...");
        }

        internal void SwapNecklace(string element)
        {
            Console.WriteLine($"[DEBUG] Entering SwapNecklace method for element: {element}...");
            autoForm = true;
            RemoveDruidForm();

            if (element == "Light")
                Client.EquipLightNeck();
            else if (element == "Dark")
                Client.EquipDarkNeck();

            neckSwap = DateTime.UtcNow;
            EnterDruidForm();
            autoForm = false;
            Console.WriteLine("[DEBUG] Exiting SwapNecklace method...");
        }

        private void EnterDruidForm()
        {
            if (!Client.ClientTab.druidFormCbox.Checked)
            {
                return;
            }

            if (Client.TemuairClassFlag == TemuairClass.Monk &&
                Client.MedeniaClassFlag == MedeniaClass.Druid &&
                !Client.HasEffect(EffectsBar.FeralForm) &&
                !Client.HasEffect(EffectsBar.KaruraForm) &&
                !Client.HasEffect(EffectsBar.KomodasForm))
            {
                Console.WriteLine("[DEBUG] Attempting to enter a druid form...");
                foreach (var spell in CONSTANTS.DRUID_FORMS)
                {
                    if (Client.UseSpell(spell, null, _autoStaffSwitch))
                        break;
                }
            }

            Thread.Sleep(80);
        }

        private void RemoveDruidForm()
        {
            if (!Client.ClientTab.druidFormCbox.Checked)
            {
                return;
            }

            if (Client.TemuairClassFlag == TemuairClass.Monk &&
                Client.MedeniaClassFlag == MedeniaClass.Druid &&
                (Client.HasEffect(EffectsBar.FeralForm) ||
                 Client.HasEffect(EffectsBar.KaruraForm) ||
                 Client.HasEffect(EffectsBar.KomodasForm)))
            {
                Console.WriteLine("[DEBUG] Attempting to remove druid form...");
                foreach (var spell in CONSTANTS.DRUID_FORMS)
                {
                    if (Client.UseSpell(spell, null, _autoStaffSwitch))
                        break;
                }
            }

            Thread.Sleep(80);
        }



        #endregion


        #region TaskLoop
        private void TaskLoop()
        {
            Ascending();
            TryUsingHealingPotion();
        }

        /// <summary>
        /// Checks if the client should use a healing potion and attempts to use one if needed.
        /// </summary>
        public void TryUsingHealingPotion()
        {
            if (ShouldUseHealingPotion())
            {
                TimeSpan timeSinceLastHeal = DateTime.UtcNow - _lastUsedHealingPotion;

                if (timeSinceLastHeal.TotalSeconds > 1.0 && CanUseHealingPotion())
                {
                    if (UseHealingPotion())
                    {
                        _lastUsedHealingPotion = DateTime.UtcNow;
                    }
                }
            }
        }

        /// <summary>
        /// Determines whether healing potion logic should be executed.
        /// </summary>
        private bool ShouldUseHealingPotion()
        {
            if (Client == null || Client.ClientTab == null)
            {
                return false;
            }

            return Client.ClientTab.chkExkuranum.Checked &&
                   !Client.Player.NeedsHeal &&
                   Client.HealthPct <= Client.ClientTab.numExHeal.Value;
        }

        /// <summary>
        /// Checks whether the client is in a state that allows potion use.
        /// </summary>
        private bool CanUseHealingPotion()
        {
            return !Client.IsSkulled && !Client.HasEffect(EffectsBar.Pramh);
        }

        /// <summary>
        /// Tries to use a healing potion from the available options.
        /// </summary>
        /// <returns>True if a potion was successfully used, otherwise false.</returns>
        private bool UseHealingPotion()
        {
            string[] potions = { "Exkuranum", "hydele deum", "Brown Potion", "ard ioc deum" };

            foreach (string potion in potions)
            {
                if (Client.UseItemIgnoreCase(Client, potion))
                {
                    return true;
                }
            }

            return false;
        }

        private void Ascending()
        {
            if (Client == null || Client.ClientTab == null)
                return;

            if (Client.ClientTab.ascendBtn.Text != "Ascending")
                return;

            if (!DepositWarBagIfNeeded()) return;
            if (!RetrieveWarBagIfNeeded()) return;
            if (!DropSuccubusHair()) return;
            if (!HandleKillerOrDieOption()) return;
            if (!HandleGhostWalk()) return;
            if (!AscendHpIfNeeded()) return;
            if (!AscendMpIfNeeded()) return;

            Thread.Sleep(100);
        }


        private bool DepositWarBagIfNeeded()
        {
            // Check if the task is already done
            if (Client.WarBagDeposited)
                return true;

            if (!Client.Inventory.Contains("Warranty Bag") || Client.AscendTaskDone)
                return false;

            if (hasrepaired)
                hasrepaired = false;

            if (Client.Map.MapID == 135) // Mileth Storage
            {
                Location current = Client.ServerLocation;
                if (current.DistanceFrom(new Location(135, 6, 6)) <= 3)
                {
                    Creature npc = Client.GetNearbyNPCs()
                        .OrderBy(n => n.Location.DistanceFrom(Client.ServerLocation))
                        .FirstOrDefault();

                    if (npc != null)
                    {
                        if (npc.Location.DistanceFrom(Client.ServerLocation) <= 12)
                        {
                            if (!hasrepaired)
                            {
                                Client.PursuitRequest(1, npc.ID, 92);
                                Thread.Sleep(1000);
                                Client.WithdrawItem(npc.ID, "Succubus's Hair", 1);
                                Thread.Sleep(1000);

                                int komCount = 52 - Client.Inventory.CountOf("Komadium");
                                if (komCount > 0 && komCount <= 51)
                                {
                                    Client.WithdrawItem(npc.ID, "Komadium", komCount);
                                    Thread.Sleep(1000);
                                }

                                int exkuraCount = 30 - Client.Inventory.CountOf("Exkuranum");
                                if (exkuraCount > 0 && exkuraCount <= 30)
                                {
                                    Client.WithdrawItem(npc.ID, "Exkuranum", exkuraCount);
                                    Thread.Sleep(1000);
                                }

                                int scrollCount = 30 - Client.Inventory.CountOf("Rucesion Song");
                                if (scrollCount > 0 && scrollCount <= 30)
                                {
                                    Client.WithdrawItem(npc.ID, "Rucesion Song", scrollCount);
                                    Thread.Sleep(1000);
                                }

                                int hemCount = 30 - Client.Inventory.CountOf("Hemloch");
                                if (hemCount > 0 && hemCount <= 30)
                                {
                                    Client.WithdrawItem(npc.ID, "Hemloch", hemCount);
                                    Thread.Sleep(1000);
                                }
                            }

                            // Deposit each war bag we find in inventory
                            foreach (Item obj in Client.Inventory)
                            {
                                if (obj.Name.Equals("Warranty Bag"))
                                {
                                    Client.DepositItem(npc.ID, "Warranty Bag");
                                    Thread.Sleep(1000);
                                }
                            }

                            // Wait up to 5 seconds for the bag to disappear
                            DateTime start = DateTime.UtcNow;
                            while (Client.Inventory.Contains("Warranty Bag"))
                            {
                                Thread.Sleep(10);
                                var timeSpan = DateTime.UtcNow.Subtract(start);
                                if (timeSpan.TotalSeconds > 5.0)
                                {
                                    Client.ClientTab.Invoke(new Action(() => Client.ClientTab.ascendBtn.Text = "Ascend"));
                                    MessageDialog.Show(Server.MainForm, "Could not deposit warranty bag. Error");
                                    break;
                                }
                            }

                            Client.WarBagDeposited = true;
                            Client.AscendTaskDone = false;
                            hasrepaired = true;

                            return true;
                        }
                    }
                    // Merchant not found or too far
                    Client.ServerMessage((byte)ServerMessageType.Whisper, "You need a merchant nearby to use this command.");
                    return false;
                }
            }

            // Route to Mileth storage
            Client.Routefind(new Location(135, 6, 6), 2);
            return false;
        }
        private bool DropSuccubusHair()
        {
            Client.SuccHairDropped = true;

            if (Client.SuccHairDropped)
                return true;

            // We are ghost walking
            if (Client.Map.MapID == 435 ||
               Client.Map.MapID == 3085 ||
               Client.Map.MapID == 3086 ||
               Client.Map.MapID == 3087)
                return false;


            if (Client.EffectsBar.Contains((ushort)EffectsBar.Skull) || Client.AscendTaskDone)
                return false;

            // If we don’t have succubus hair, withdraw from Mileth
            if (!Client.Inventory.Contains("Succubus's Hair"))
            {
                if (Client.Map.MapID == 135) // Mileth Storage
                {
                    Location current = Client.ServerLocation;
                    if (current.DistanceFrom(new Location(135, 6, 6)) <= 3)
                    {
                        Creature creature = Client.GetNearbyNPCs()
                            .OrderBy(n => n.Location.DistanceFrom(Client.ServerLocation))
                            .FirstOrDefault();

                        if (creature != null &&
                            creature.Location.DistanceFrom(Client.ServerLocation) <= 12)
                        {
                            Client.PursuitRequest(1, creature.ID, 92);
                            Thread.Sleep(1000);
                            Client.WithdrawItem(creature.ID, "Succubus's Hair", 1);
                            Client.Dialog?.Reply();

                            DateTime start = DateTime.UtcNow;
                            while (!Client.Inventory.Contains("Succubus's Hair"))
                            {
                                Thread.Sleep(10);
                                var timeSpan = DateTime.UtcNow.Subtract(start);
                                if (timeSpan.TotalSeconds > 5.0)
                                {
                                    Client.ClientTab.ascendBtn.Text = "Ascend";
                                    MessageDialog.Show(Server.MainForm,
                                        "Succubus Hair retreival failed.");
                                    break;
                                }
                            }

                            return false;
                        }

                        Client.ServerMessage((byte)ServerMessageType.Whisper, "You need a merchant nearby to use this command.");
                        return false;
                    }
                }
                Client.Routefind(new Location(135, 6, 6), 3);
                return false;
            }

            if (Client.Map.MapID == 500 && CONSTANTS.MILETH_ALTAR_SPOTS.Keys.Contains(Client.ServerLocation))
            {
                // Drop the succubus hair
                Client.Drop(
                    Client.Inventory["Succubus's Hair"].Slot,
                    CONSTANTS.MILETH_ALTAR_SPOTS[Client.ServerLocation]
                );
                Thread.Sleep(1500);
                Client.Dialog?.Reply();
                Thread.Sleep(100);

                if (!Client.EffectsBar.Contains((ushort)EffectsBar.Skull))
                {
                    Client.RefreshRequest();
                    return true;
                }

                var ascendNames = Server.MainForm.AutoAscendDataList
                    .Where(d => d.ContainsKey("Name"))
                    .Select(d => d["Name"].ToString());

                if (ascendNames.Contains(Client.Name) && Client.HasItem("Rucesion Song"))
                    Client.UseItem("Rucesion Song");

                Thread.Sleep(150);
                Client.SuccHairDropped = true;
                return true;
            }


            // Route to a random unoccupied altar spot
            var nextPoint = CONSTANTS.MILETH_ALTAR_SPOTS
                .OrderBy(_ => RandomUtils.Random())
                .FirstOrDefault(kvp =>
                    !Client.GetNearbyPlayers().Any(p => p.Location == kvp.Key)
                ).Key;

            Client.Routefind(new Location(500, nextPoint.X, nextPoint.Y));
            return false;

        }
        private bool HandleKillerOrDieOption()
        {
            // We are ghost walking
            if (Client.Map.MapID == 435 ||
                Client.Map.MapID == 3085 ||
                Client.Map.MapID == 3086 ||
                Client.Map.MapID == 3087)
                return true;

            // Check if "Killer" option is enabled
            if (Client.ClientTab.useKillerCbx.Checked)
            {
                string killerName = Client.ClientTab.killerNameTbx.Text;
                Client killer = Server.GetClient(killerName);

                if (killer == null)
                {
                    SystemSounds.Beep.Play();
                    Thread.Sleep(1000);
                    Client.ServerMessage((byte)ServerMessageType.Whisper, "Killer not found.");
                    return false;
                }

                Location killerLocation = killer.ServerLocation;

                if (Client.Map.MapID == killerLocation.MapID)
                {
                    Location current = Client.ServerLocation;
                    if (current.DistanceFrom(killerLocation) <= 6)
                    {
                        // Attack logic
                        if (Client.CurrentHP > 1U && !Client.UseSkill("Auto Hemloch"))
                        {
                            if (Client.Inventory.Contains("Hemloch"))
                                Client.UseItem("Hemloch");
                            Thread.Sleep(2000);
                        }

                        foreach (Client c in Server.ClientList)
                        {
                            if (c.Name == killerName)
                            {
                                if (c.HasSpell("mor strioch pian gar"))
                                {
                                    if (c.ManaPct < 50)
                                    {
                                        c.UseSpell("fas spiorad", null, true, false);
                                    }
                                    c.UseSpell("mor strioch pian gar", null, true, false);
                                }
                            }
                        }

                        return true; // Task completed
                    }
                }

                Client.Routefind(killerLocation); // Route to the killer
                return false;
            }

            // Check if "Die at PC" option is enabled
            if (Client.ClientTab.deathOptionCbx.Checked)
            {
                if (Client.ServerLocation.DistanceFrom(_pcDeathSpot) <= 2)
                    return true; // Task completed

                Client.Routefind(_pcDeathSpot, 2); // Route to the PC death spot
                return false;
            }

            // Neither option is enabled
            return true;
        }


        private bool HandleGhostWalk()
        {
            bool ascendHP = Client.ClientTab.ascendOptionCbx.Text == "HP";

            if (Client.Map.MapID == 435)
            {
                if (Client.ServerLocation.X < 6)
                    Client.Pathfind(new Location(435, 4, 20), 0);
                else
                    Client.Pathfind(new Location(435, 6, 23), 0);
                return true;
            }
            else if (Client.Map.MapID == 3085)
            {
                if (ascendHP)
                    Client.Pathfind(new Location(3085, 10, 14), 0);
                else
                    Client.Pathfind(new Location(3085, 10, 5), 0);
                return true;
            }


            return true;

        }
        private bool AscendHpIfNeeded()
        {
            if (Client.Map.MapID != 3086)
                return false;

            Location altarSpot = new Location(3086, 5, 2);
            Location current = Client.ServerLocation;

            if (current.DistanceFrom(altarSpot) > 2)
            {
                Client.Pathfind(altarSpot);
                return false;
            }

            // If within range
            Client.RefreshRequest();
            current = Client.ServerLocation;
            if (current.DistanceFrom(altarSpot) > 2)
                return false;

            Thread.Sleep(2500);
            commandManager.ExecuteCommand(Client, "/hp all");

            // If WarBag not deposited, set ascendBtn back and possibly complete ascending
            if (!Client.WarBagDeposited)
            {
                Client.ClientTab.Invoke(new Action(() => Client.ClientTab.ascendBtn.Text = "Ascend"));

                var ascendNames = Server.MainForm.AutoAscendDataList
                    .Where(d => d.ContainsKey("Name"))
                    .Select(d => d["Name"].ToString())
                    .ToList();

                if (ascendNames.Contains(Client.Name))
                    Server.ClientStateList[Client.Name] = CharacterState.AscendingComplete;
            }

            Client.AscendTaskDone = true;
            return true;
        }
        private bool AscendMpIfNeeded()
        {
            if (Client.Map.MapID != 3087)
                return false;

            Location altarSpot = new Location(3087, 5, 2);
            Location current = Client.ServerLocation;

            if (current.DistanceFrom(altarSpot) > 2)
            {
                Client.Pathfind(altarSpot);
                return false;
            }

            Client.RefreshRequest();
            current = Client.ServerLocation;
            if (current.DistanceFrom(altarSpot) > 2)
                return false;

            Thread.Sleep(2500);
            commandManager.ExecuteCommand(Client, "/mp all");

            if (!Client.WarBagDeposited)
            {
                Client.ClientTab.Invoke(new Action(() => Client.ClientTab.ascendBtn.Text = "Ascend"));

                var ascendNames = Server.MainForm.AutoAscendDataList
                    .Where(d => d.ContainsKey("Name"))
                    .Select(d => d["Name"].ToString());

                if (ascendNames.Contains(Client.Name))
                    Server.ClientStateList[Client.Name] = CharacterState.AscendingComplete;
            }

            Client.AscendTaskDone = true;
            return true;
        }
        private bool RetrieveWarBagIfNeeded()
        {
            // Original check: if WarBagDeposited && AscendTaskDone
            if (!Client.WarBagDeposited || !Client.AscendTaskDone)
                return false;

            // If we get here, we need to retrieve the bag
            if (Client.Map.MapID == 167) // Abel storage
            {
                Location current = Client.ServerLocation;
                if (current.DistanceFrom(new Location(167, 3, 8)) <= 2)
                {
                    Creature creature = Client.GetNearbyNPCs()
                        .OrderBy(n => n.Location.DistanceFrom(Client.ServerLocation))
                        .FirstOrDefault();

                    if (creature != null && creature.Location.DistanceFrom(Client.ServerLocation) <= 12)
                    {
                        Client.PublicMessage((byte)PublicMessageType.Chant, "Give my Warranty Bag back");
                        Client.Dialog?.Reply();

                        DateTime start = DateTime.UtcNow;
                        while (!Client.Inventory.Contains("Warranty Bag"))
                        {
                            Client.PublicMessage((byte)PublicMessageType.Chant, "Give my Warranty Bag back");
                            Thread.Sleep(500);

                            var timeSpan = DateTime.UtcNow.Subtract(start);
                            if (timeSpan.TotalSeconds > 5.0)
                            {
                                Client.ClientTab.Invoke(new Action(() => Client.ClientTab.ascendBtn.Text = "Ascend"));
                                MessageDialog.Show(Server.MainForm, "Couldn't retrieve warranty bag. Error");
                                break;
                            }
                        }

                        // Once done, set ascendBtn to Ascend
                        Client.ClientTab.Invoke(new Action(() => Client.ClientTab.ascendBtn.Text = "Ascend"));

                        var ascendNames = Server.MainForm.AutoAscendDataList
                            .Where(d => d.ContainsKey("Name"))
                            .Select(d => d["Name"].ToString());

                        if (ascendNames.Contains(Client.Name))
                            Server.ClientStateList[Client.Name] = CharacterState.AscendingComplete;

                        // We are done
                        return true;
                    }

                    Client.ServerMessage((byte)ServerMessageType.Whisper,
                        "You need a merchant nearby to use this command.");
                    return false;
                }
            }
            // Otherwise route to Abel storage
            Client.Routefind(new Location(167, 3, 8), 1);
            return false;
        }

        #endregion



        private void CheckScrollTimers()
        {
            if (Client.ComboScrollCounter > 0)
            {
                TimeSpan remainingTime = GetScrollRemainingTime();
                if (remainingTime < TimeSpan.FromSeconds(1))
                {
                    Client.ComboScrollCounter = 0;
                }
                else if (!Client.SafeScreen)
                {
                    Client.ServerMessage((byte)ServerMessageType.TopRight, $"Scroll in: {remainingTime:m\\:ss}");
                }
            }
            else if (Client.MedeniaClassFlag == MedeniaClass.Druid && !Client.SafeScreen)
            {
                Client.ServerMessage((byte)ServerMessageType.TopRight, "Scroll Ready.");
            }
        }

        private TimeSpan GetScrollRemainingTime()
        {
            int scrollMinutes = (Client.ComboScrollCounter == (Client.PreviousClassFlag == PreviousClass.Pure ? 3 : 2)) ? 2 : 1;
            TimeSpan totalScrollTime = new TimeSpan(0, scrollMinutes, 2);
            return totalScrollTime - (DateTime.UtcNow - Client.ComboScrollLastUsed);
        }


        private void HolidayEvents()
        {
            ConsecutiveLogin();
            RetrieveDoubles();
            _bugManager.BugLoop();
        }

        private void ConsecutiveLogin()
        {
            if (Client.ClientTab != null && Client.ClientTab.btnConLogin.Text == "Stop")
            {
                // Check if the client is at the correct map and within range
                if (Client.Map.MapID == 3052 && Client.ServerLocation.DistanceFrom(new Location(3052, 48, 17)) <= 6)
                {
                    // Interact with the NPC
                    var creature = Client.GetNearbyNPC("Celesta");
                    if (creature == null || !Client.RequestNamedPursuit(creature, "Avid Daydreamer", true))
                    {
                        return; // Exit if NPC interaction fails
                    }

                    // Reply to dialog options
                    Client.ReplyDialog(1, creature.ID, 0, 2);
                    Client.Dialog.Reply();

                    // Update consecutive login data
                    string clientName = Client.Name.ToUpper();
                    var consecutiveLogin = Client.Server.ConsecutiveLogin;
                    consecutiveLogin[clientName] = DateTime.UtcNow; // Add or update login time

                    // Save the updated data
                    Thread.Sleep(1000); // Maintain original behavior with the delay
                    Client.Server.MainForm.SaveLoginCon();

                    // Update the button text
                    Client.ClientTab.btnConLogin.Text = "Start";
                }
                else
                {
                    // Route the client to the required location
                    Client.Routefind(new Location(3052, 46, 20), 0, false, true, true);
                }
            }

        }
        private void RetrieveDoubles()
        {
            {
                int targetMapID = 3271;
                Location targetLocation = new Location(3271, 43, 58);
                string npcName = "Frosty3";



                // Logic to retrieve doubles
                if (Client.ClientTab != null && Client.ClientTab.toggleSeaonalDblBtn.Text == "Disable")
                {

                    // Adjust based on the calendar month
                    switch (DateTime.Now.Month)
                    {
                        case 12: // December
                            targetMapID = 3271;
                            targetLocation = new Location(3271, 43, 58);
                            npcName = "Frosty3";
                            break;

                        case 2: // February
                            targetMapID = 3271;
                            targetLocation = new Location(3271, 43, 58);
                            //targetMapID = 3043;
                            //targetLocation = new Location(3043, 20, 24);
                            npcName = "Aidan";
                            break;

                        default:
                            Console.WriteLine("[HolidayEvents] Cannot retrieve doubles during this month.");
                            Client.ServerMessage((byte)ServerMessageType.Whisper, "Cannot retrieve doubles during this month.");
                            Client.ClientTab.toggleSeaonalDblBtn.Text = "Enable";
                            return;
                    }

                    if (!_receivedDblBonus)
                    {
                        // Check if we are on the target map and close to the target location
                        if (Client.Map.MapID == targetMapID && Client.ServerLocation.DistanceFrom(targetLocation) <= 2)
                        {
                            Creature creature = Client.GetNearbyNPC(npcName);
                            if (creature != null)
                            {
                                Console.WriteLine($"[HolidayEvents] Retrieved NPC Name: {creature.Name}, ID: {creature.ID}");
                                Console.WriteLine($"[HolidayEvents] Clicking creature");
                                Client.ClickObject(creature.ID);
                            }
                            else
                            {
                                Console.WriteLine($"[HolidayEvents] Creature was null");
                                return;
                            }
                            Thread.Sleep(1000);
                            Console.WriteLine($"[HolidayEvents] Hitting escape key");
                            Client.EscapeKey();
                            Console.WriteLine($"[HolidayEvents] Setting boolean to true");
                            _receivedDblBonus = true;
                            Console.WriteLine($"[HolidayEvents] Sleeping for 1 s");
                            Thread.Sleep(1000);
                        }
                        else // We need to walk to the target location
                        {
                            Console.WriteLine($"[HolidayEvents] Routing to target location: {targetLocation}");
                            Client.Routefind(targetLocation, 0, false, true, true);
                            return;
                        }
                    }
                    else
                    {
                        // Move to the next stage based on the map and location
                        if (Client.Map.MapID != 6925)
                        {
                            Console.WriteLine($"[HolidayEvents] Routing to Loures Harbor");
                            Client.Routefind(new Location(6925, 41, 4), 0, false, true, true);
                        }
                        else
                        {
                            if (Client.ServerLocation.DistanceFrom(new Location(6925, 41, 4)) <= 2)
                            {
                                Console.WriteLine($"[HolidayEvents] We are done!");
                                Client.ClientTab.toggleSeaonalDblBtn.Text = "Enable";
                                SystemSounds.Beep.Play();
                                Client.FlashWindowEx(Process.GetProcessById(Client.processId).MainWindowHandle);
                            }
                            else
                            {
                                Console.WriteLine($"[HolidayEvents] Moving closer to (41, 4)");
                                Client.Routefind(new Location(6925, 41, 4), 0, false, true, true);
                            }
                        }
                    }
                }
            }
        }

        private void TavalyWallHacks()
        {
            if (Client.ClientTab.chkTavWallStranger.Checked && IsStrangerNearby() && Client.ClientTab.chkTavWallHacks.Checked && !Client.Map.IsWall(Client.ServerLocation))
            {
                Client.ClientTab.chkTavWallHacks.Checked = false;
                Client.RefreshRequest();
            }
            if (Client.ClientTab.chkTavWallStranger.Checked && !IsStrangerNearby() && !Client.ClientTab.chkTavWallHacks.Checked)
            {
                Client.ClientTab.chkTavWallHacks.Checked = true;
                Client.RefreshRequest();
            }
        }

        private void MonsterForm()
        {
            if (Client != null && Client.ClientTab != null)
            {
                bool strangerNear = IsStrangerNearby();
                bool deformChecked = (bool)(Client?.ClientTab?.deformCbox.Checked);
                ushort desiredFormNum = (ushort)Client?.ClientTab?.formNum.Value;

                if (Client.ClientTab.formCbox.Checked)
                {
                    if (deformChecked && strangerNear)
                    {
                        // Only set if the state needs to change
                        if (Client.ClientTab.formCbox.Checked)
                        {
                            Client.ClientTab.SetMonsterForm(false, desiredFormNum);
                        }
                    }
                }
                else if (!Client.ClientTab.formCbox.Checked && deformChecked)
                {
                    if (!strangerNear)
                    {


                        Client.ClientTab.SetMonsterForm(true, desiredFormNum);
                    }
                }
            }

        }



        internal bool IsStrangerNearby()
        {
            return Client.GetNearbyPlayers().Any(player => IsNotInFriendList(player));
        }

        private bool IsNotInFriendList(Player player)
        {
            var clientTab = Client.ClientTab;

            if (clientTab != null || Client.ClientTab != null)
            {
                return !clientTab.friendList.Items.OfType<string>().Any(friend => string.Equals(friend, player.Name, StringComparison.OrdinalIgnoreCase));
            }
            else
            {
                return true;
            }
        }

        private async Task WalkLoop(CancellationToken token)
        {

            while (!token.IsCancellationRequested)
            {
                //Console.WriteLine("[WalkLoop] Pulse");
                _rangerNear = IsRangerNearBy();
                if (!Client.ExchangeOpen && Client.ClientTab != null)
                {
                    HandleDialog();
                    HandleDumbMTGWarp();
                    WalkActions();
                }

                await Task.Delay(100, token); // Add a small sleep to avoid flooding the CPU default: 100
            }

        }

        private void WalkActions()
        {
            //var start = DateTime.UtcNow;
            //Console.WriteLine($"WalkActions started at {start:HH:mm:ss.fff}");
            var clientTab = Client.ClientTab;
            if (clientTab == null || Client.ClientTab == null)
            {
                return;
            }

            _nearbyPlayers = Client.GetNearbyPlayers();
            _nearbyValidCreatures = Client.GetNearbyValidCreatures(12);
            var shouldWalk = !_dontWalk &&
                (!clientTab.rangerStopCbox.Checked || !_rangerNear);

            if (shouldWalk)
            {
                HandleWalkingCommand();
            }

            //var end = DateTime.UtcNow;
            //Console.WriteLine($"WalkActions ended at {end:HH:mm:ss.fff}, Duration: {(end - start).TotalMilliseconds} ms");
        }

        private void HandleWalkingCommand()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null || Client.ClientTab == null)
            {
                return;
            }

            string comboBoxText = clientTab.walkMapCombox.Text;
            bool followChecked = clientTab.followCbox.Checked;
            string followName = clientTab.followText.Text;

            if (followChecked && !string.IsNullOrEmpty(followName))
            {
                FollowWalking(followName);
            }
            else if (clientTab.walkBtn.Text == "Stop")
            {
                RefreshLastStep();

                if (comboBoxText == "SW Lure")
                {
                    SWLure();
                    return;
                }
                else if (comboBoxText == "WayPoints")
                {
                    WayPointWalking();
                    return;
                }

                // Determine the route target from comboBoxText
                if (TryGetRouteTarget(comboBoxText, out short mapID, out Location destination))
                {
                    // Handle extra map actions if needed
                    HandleExtraMapActions(destination);

                    // Update the walk button or directly route
                    if (mapID > 0)
                    {
                        Client.RouteFindByMapID(mapID);
                    }
                    else if (destination != default)
                    {
                        UpdateWalkButton(destination);
                    }
                }
                else
                {
                    UpdateWalkButton(destination);
                }

            }
        }
        private void HandleExtraMapActions(Location destination)
        {

            if (Client.Map == null)
                return;

            // Extracting for readability
            var currentMapID = Client.Map.MapID;
            var currentLocation = Client.ServerLocation;

            // First, handle specific cases triggered by the current map ID
            if (HandleMapSpecificActions(currentMapID, currentLocation))
            {
                return; // If handled, stop
            }

            // Next, handle cases based on the destination map ID
            if (HandleDestinationSpecificActions(destination))
            {
                return;
            }
        }
        private bool HandleMapSpecificActions(int currentMapID, Location currentLocation)
        {
            switch (currentMapID)
            {
                case 6525: // Oren Island Ruins0
                    return HandleOrenIslandRuins0(currentLocation);

                default:
                    return false; // Not handled here
            }
        }

        private bool HandleDestinationSpecificActions(Location destination)
        {
            switch (destination.MapID)
            {
                case 424: // Rucesion Black Market
                    return HandleBlackMarket();

                case 3012: // Loures Castle Way
                    return HandleLouresCastleWay();

                case 3938: // Loures Storage 12, to wait outside Canals
                    return HandleLouresStore12();

                case 3950: // Gladiator Arena Entrance
                    return HandleGladiatorArenaEntrance();

                case 6534: // Oren Ruins 2-1 to wait ouside 2-5
                    return HandleOrenRuinsWalkTo2dash5();

                case 6537: // Oren Ruins 2-4 to wait ouside 2-11
                    return HandleOrenRuinsWalkTo2dash11();

                case 6538: // Oren Ruins 3-1 to wait ouside 3-5
                    return HandleOrenRuinsWalkTo3dash5();

                case 6541: // Oren Ruins 3-4 to wait ouside 3-11
                    return HandleOrenRuinsWalkTo3dash11();

                case 10265: // Hwarone City, to wait outside Fire Canyon
                    return HandleFireCanyon();

                default:
                    return false; // Not handled here
            }
        }

        // Below are the helper methods for each map or destination.
        // Each returns true if it handled the action (meaning it performed
        // some routing or updated the UI and then returned early).
        private bool HandleOrenIslandRuins0(Location currentLocation)
        {
            if (currentLocation.AbsoluteXY(32, 23) > 2)
            {
                Client.Routefind(new Location(6525, 32, 23), 0, false, true, true);
                return true;
            }
            else
            {
                Client.PublicMessage(3, "Welcome Aisling");
                Thread.Sleep(500);
                return true;
            }
        }
        private bool HandleLouresStore12()
        {
            if (Client.Map.MapID == 3938)
            {
                if (Client.ClientLocation.AbsoluteXY(7, 13) > 2)
                {
                    Client.Pathfind(new Location(3938, 7, 13), 0, true, false);
                    return true;
                }
                else
                {
                    Client.ClientTab.walkBtn.Text = "Walk";
                    return true;
                }
            }
            else
                return false;
        }
        private bool HandleGladiatorArenaEntrance()
        {
            if (Client.Map.MapID == 3950)
            {
                if (Client.ClientLocation.AbsoluteXY(13, 12) > 2)
                {
                    Client.Pathfind(new Location(3950, 13, 12), 0, true, false);
                    return true;
                }
                else
                {
                    Client.ClientTab.walkBtn.Text = "Walk";
                    return true;
                }
            }
            else
                return false;
        }
        private bool HandleLouresCastleWay()
        {
            if (Client.Map.MapID == 3012)
            {
                if (Client.ClientLocation.AbsoluteXY(15, 0) > 2)
                {
                    Client.Pathfind(new Location(3012, 15, 0), 0, true, false);
                    return true;
                }
                else
                {
                    Client.ClientTab.walkBtn.Text = "Walk";
                    return true;
                }
            }
            else
                return false;
        }
        private bool HandleFireCanyon()
        {
            if (Client.Map.MapID == 10265)
            {
                if (Client.ClientLocation.AbsoluteXY(93, 48) > 2)
                {
                    // Actually puts us in Hwarone City Entrance
                    Client.Pathfind(new Location(10265, 93, 48), 0, true, false);
                    return true;
                }
                else
                {
                    Client.ClientTab.walkBtn.Text = "Walk";
                    return true;
                }
            }
            else
                return false;
        }
        private bool HandleBlackMarket()
        {
            if (Client.Map.MapID == 424)
            {
                if (Client.ClientLocation.AbsoluteXY(6, 6) > 2)
                {
                    Client.Pathfind(new Location(424, 6, 6), 0, true, false);
                    return true;
                }
                else
                {
                    Client.ClientTab.walkBtn.Text = "Walk";
                    return true;
                }
            }
            else
                return false;
        }

        #region Oren Ruins walking
        // The Oren Ruins related methods are more complex. Each of these methods is specific
        // to a destination and handles the logic to move through the annoying Nobis rooms
        private bool HandleOrenRuinsWalkTo3dash11()
        {
            // Handle sub-routes within specific maps
            if (HandleSubRouteLogicFor3dash11(Client.Map.MapID, Client.ClientLocation))
            {
                return true;
            }

            // Handle main routing logic
            var ruinsMapIDs = new HashSet<int> { 6924, 6701, 6700, 6530, 6531, 6533, 6537, 6535, 6538, 6539, 6540, 6541 };
            if (ruinsMapIDs.Contains(Client.Map.MapID))
            {
                return TryRouteOrPathfind(new Location(6541, 73, 4), 3);
            }

            // Handle Oren Island City
            if (Client.Map.MapID == 6228)
            {
                return TryRouteOrPathfind(new Location(6525, 62, 146), 4);
            }

            // Default to Oren Island City
            if (Client.Map.MapID != 6228)
            {
                return TryRouteOrPathfind(new Location(6228, 59, 169), 4);
            }

            return false;
        }
        private bool HandleSubRouteLogicFor3dash11(int mapID, Location clientLocation)
        {
            switch (mapID)
            {
                case 6530:
                    return Client.Pathfind(new Location(6530, 10, 0), 0, true, false);

                case 6537:
                    return Client.Pathfind(new Location(6537, 0, 4), 0, true, false);

                case 6539:
                    return Client.Pathfind(new Location(6539, 53, 74), 0, true, true);

                case 6538:
                    return Client.Pathfind(new Location(6538, 74, 16), 0, true, false);

                case 6540 when clientLocation.X < 4:
                    return Client.Pathfind(new Location(6540, 3, 0), 0, true, false);

                case 6540:
                    return Client.Pathfind(new Location(6540, 35, 0), 0, true, false);

                case 6541 when clientLocation.X < 28 && clientLocation.Y > 63:
                    return Client.Pathfind(new Location(6541, 23, 74), 0, true, false);

                case 6541 when IsCloseTo(new Location(6541, 73, 4), 3):
                    Client.ClientTab.walkBtn.Text = "Walk";
                    return true;

                default:
                    return false;
            }
        }
        private bool HandleOrenRuinsWalkTo3dash5()
        {
            // Handle sub-routes within specific maps
            if (HandleSubRouteLogicFor3dash5(Client.Map.MapID, Client.ClientLocation))
            {
                return true;
            }

            // Handle main routing logic
            var ruinsMapIDs = new HashSet<int> { 6924, 6701, 6700, 6530, 6531, 6533, 6537, 6535, 6538, 6539, 6540 };
            if (ruinsMapIDs.Contains(Client.Map.MapID))
            {
                return TryRouteOrPathfind(new Location(6538, 58, 73), 3);
            }

            // Handle Oren Island City
            if (Client.Map.MapID == 6228)
            {
                return TryRouteOrPathfind(new Location(6525, 62, 146), 4);
            }

            // Default to Oren Island City
            if (Client.Map.MapID != 6228)
            {
                return TryRouteOrPathfind(new Location(6228, 59, 169), 4);
            }

            return false;
        }
        private bool HandleSubRouteLogicFor3dash5(int mapID, Location clientLocation)
        {
            switch (mapID)
            {
                case 6530:
                    return Client.Pathfind(new Location(6530, 10, 0), 0, true, false);

                case 6537:
                    return Client.Pathfind(new Location(6537, 0, 4), 0, true, false);

                case 6539 when clientLocation.Y < 8:
                    return Client.Pathfind(new Location(6539, 1, 8), 1, true, false);

                case 6539:
                    return Client.Pathfind(new Location(6539, 4, 74), 0, true, true);

                case 6538 when clientLocation.Y < 50:
                    return Client.Pathfind(new Location(6538, 74, 47), 0, true, false);

                case 6540:
                    return Client.Pathfind(new Location(6540, 0, 67), 0, true, false);

                case 6538 when IsCloseTo(new Location(6538, 58, 73), 3):
                    Client.ClientTab.walkBtn.Text = "Walk";
                    return true;

                default:
                    return false;
            }
        }
        private bool HandleOrenRuinsWalkTo2dash5()
        {
            // Handle sub-routes within specific maps
            if (HandleSubRouteLogicFor2dash5(Client.Map.MapID, Client.ClientLocation))
            {
                return true;
            }

            // Handle main routing logic
            var ruinsMapIDs = new HashSet<int> { 6924, 6701, 6700, 6530, 6531, 6533, 6534, 6535 };
            if (ruinsMapIDs.Contains(Client.Map.MapID))
            {
                return TryRouteOrPathfind(new Location(6534, 1, 36), 3);
            }

            // Handle Oren Island City
            if (Client.Map.MapID == 6228)
            {
                return TryRouteOrPathfind(new Location(6525, 62, 146), 4);
            }

            // Default to Oren Island City
            if (Client.Map.MapID != 6228)
            {
                return TryRouteOrPathfind(new Location(6228, 59, 169), 4);
            }

            return false;
        }
        private bool HandleSubRouteLogicFor2dash5(int mapID, Location clientLocation)
        {
            switch (mapID)
            {
                case 6530:
                    return Client.Pathfind(new Location(6530, 10, 0), 0, true, false);

                case 6537:
                    return Client.Pathfind(new Location(6537, 0, 4), 0, true, false);

                case 6535:
                    return Client.Pathfind(new Location(6535, 20, 74), 0, true, false);

                case 6534 when IsCloseTo(new Location(6534, 1, 36), 3):
                    Client.ClientTab.walkBtn.Text = "Walk";
                    return true;

                default:
                    return false;
            }
        }
        private bool HandleOrenRuinsWalkTo2dash11()
        {
            // Handle sub-routes within specific maps
            if (HandleSubRouteLogicFor2dash11(Client.Map.MapID, Client.ClientLocation))
            {
                return true;
            }

            // Handle main routing logic
            var ruinsMapIDs = new HashSet<int> { 6924, 6701, 6700, 6530, 6531, 6533, 6534, 6535, 6536, 6537 };
            if (ruinsMapIDs.Contains(Client.Map.MapID))
            {
                return TryRouteOrPathfind(new Location(6537, 65, 1));
            }

            // Handle Oren Island City
            if (Client.Map.MapID == 6228)
            {
                return TryRouteOrPathfind(new Location(6525, 62, 146), 4);
            }

            // Default to Oren Island City
            if (Client.Map.MapID != 6228)
            {
                return TryRouteOrPathfind(new Location(6228, 59, 169), 4);
            }

            return false;
        }
        private bool HandleSubRouteLogicFor2dash11(int mapID, Location clientLocation)
        {
            switch (mapID)
            {
                case 6537 when clientLocation.X < 31 && clientLocation.Y < 43:
                    return Client.Pathfind(new Location(6537, 0, 31), 0, true, false);

                case 6535 when clientLocation.X > 68 && clientLocation.Y < 56:
                    return Client.Pathfind(new Location(6535, 74, 49), 0, true, false);

                case 6537 when clientLocation.X < 43 && clientLocation.Y > 43:
                    return Client.Pathfind(new Location(6537, 14, 74), 0, true, false);

                case 6536 when clientLocation.X < 25 && clientLocation.Y < 24:
                    return Client.Pathfind(new Location(6536, 0, 15), 0, true, false);

                case 6534 when clientLocation.X > 45:
                    return Client.Pathfind(new Location(6534, 74, 28), 0, true, false);

                case 6536 when (clientLocation.X > 25 || clientLocation.Y > 26) && clientLocation.X < 69:
                    return Client.Pathfind(new Location(6536, 72, 4), 0, true, false);

                case 6536 when clientLocation.X > 68:
                    return Client.Pathfind(new Location(6536, 69, 0), 0, true, false);

                case 6537 when IsCloseTo(new Location(6537, 65, 1), 3):
                    Client.ClientTab.walkBtn.Text = "Walk";
                    return true;

                default:
                    return false;
            }
        }
        #endregion

        private bool TryRouteOrPathfind(Location target, short distance = 0)
        {
            return TryRouteFind(target) || Client.Pathfind(target, distance, true, false);
        }
        // Utility methods to reduce repeated code
        private bool TryRouteFind(Location loc, short distance = 0, bool mapOnly = false, bool shouldBlock = true, bool avoidWarps = true)
        {
            return Client.Routefind(loc, distance, mapOnly, shouldBlock, avoidWarps);
        }

        private bool IsCloseTo(Location target, int threshold)
        {
            Location serverLocation = Client.ServerLocation;
            return (serverLocation.DistanceFrom(target) <= threshold);
        }



        /// <summary>
        /// Attempts to interpret the user input as either a map ID or a named destination.
        /// Returns true if a valid route target was found.
        /// </summary>
        private bool TryGetRouteTarget(string input, out short mapID, out Location destination)
        {
            mapID = 0;
            destination = default;

            // Try parsing as Map ID
            if (short.TryParse(input, out short parsedMapID))
            {
                mapID = parsedMapID;
                destination = new Location(mapID, 0, 0);
                return true;
            }

            // If not a map ID, try getting a named destination
            destination = GetDestinationBasedOnComboBoxText(input);
            return (destination != default);
        }


        private Location GetDestinationBasedOnComboBoxText(string text)
        {
            uint fnvHash = HashingUtils.CalculateFNV(text);
            return CONSTANTS.DESTINATION_MAP.TryGetValue(fnvHash, out var loc) ? loc : default;
        }

        private void FollowWalking(string followName)
        {
            try
            {
                if (Client == null || Client.ClientTab == null)
                    return;

                // Is follow enabled? Do we have a follow name?
                if (!Client.ClientTab.followCbox.Checked || string.IsNullOrEmpty(Client.ClientTab.followText.Text))
                    return;

                bool overlapped = Client.GetNearbyObjects()
                    .OfType<Creature>()
                    .Any(creature => creature.Location == Client.ClientLocation
                                     && creature.ID != Client.Player?.ID);

                if (overlapped)
                {
                    Console.WriteLine($"[FollowWalking] [{Client.Name}] Overlapped by creature - attempting random unstick.");
                    if (!TryFollowUnstuck()) // If random unstick fails, we return and try again next cycle
                    {
                        return;
                    }
                }

                // Identify the leader (bot or player)
                Client botClientToFollow = Server.GetClient(followName);
                Player leader = botClientToFollow?.Player
                    ?? Client.WorldObjects.Values.OfType<Player>()
                       .FirstOrDefault(p => p.Name.Equals(followName, StringComparison.CurrentCultureIgnoreCase));

                List<Player> nearbyPlayers = Client.GetNearbyPlayers();

                // Only nullify leader if we don't have a bot client AND the player is not nearby.
                if (botClientToFollow == null &&
                    !nearbyPlayers.Any(p => p.Name.Equals(followName, StringComparison.CurrentCultureIgnoreCase)))
                {
                    leader = null;
                }

                var leaderClient = botClientToFollow;

                if (Client != null && (Client.ClientTab.IsBashingActive || !Client.Stopped))
                {
                    RefreshLastStep();
                }


                // If the leader is null, fallback to last known location
                if (leader == null)
                {
                    if (_leaderID.HasValue && Client.LastSeenLocations.TryGetValue(_leaderID.Value, out Location lastSeenLocation))
                    {
                        // Use last seen location
                        Client.IsWalking = Client.Pathfind(lastSeenLocation)
                            && !Client.ClientTab.oneLineWalkCbox.Checked
                            && !Server.StopWalking;
                    }
                    else
                    {
                        Client.IsWalking = false;
                    }
                    return;
                }

                // If we found a leader, store their ID
                _leaderID = leader.ID;
                Location leaderLocation = leader.Location;
                int distance = leaderLocation.DistanceFrom(Client.ClientLocation);


                if (botClientToFollow != null
                    && botClientToFollow.Bot != null
                    && botClientToFollow.Bot.currentWay < botClientToFollow.Bot.ways.Count)
                {
                    Location leadersCurrentWaypoint = botClientToFollow.Bot.ways[botClientToFollow.Bot.currentWay];
                    if (leadersCurrentWaypoint == Client.ServerLocation)
                    {
                        Console.WriteLine($"[FollowWalking] [{Client.Name}] My location matches leader's current waypoint => random step + return");

                        if (botClientToFollow?.ClientTab?.walkMapCombox.Text == "WayPoints" &&
                            botClientToFollow.ClientTab.walkBtn.Text == "Stop" &&
                            botClientToFollow.Stopped)
                        {
                            // Call your method to move to an adjacent walkable location
                            MoveToNearbyLocation();
                            return;
                        }
                    }
                }

                if (leaderClient?.ClientTab?.IsBashingActive == true
                    && !Client.HasEffect(EffectsBar.BeagSuain)
                    && !Client.HasEffect(EffectsBar.Pramh)
                    && !Client.HasEffect(EffectsBar.Suain)
                    && Client.GetAllNearbyMonsters(0).Any())
                {
                    Console.WriteLine($"[FollowWalking] Shake loose logic => random direction + short sleep + refresh");
                    var direction = GetRandomDirection();
                    Client.Walk(direction);
                    Thread.Sleep(300);
                    Client.RefreshRequest(false);
                }


                if (!UnStucker(leader))
                {
                    short followDistance = (leaderLocation.MapID == Client.Map.MapID)
                        ? (short)Client.ClientTab.followDistanceNum.Value
                        : (short)0;

                    // Lockstep logic
                    if (Client.ClientTab.lockstepCbox.Checked && leaderLocation.MapID == Client.Map.MapID)
                    {
                        if (distance > followDistance)
                        {
                            if (Client.IsCasting)
                                Client.IsCasting = false;

                            Client.ConfirmBubble = false;
                            Client.IsWalking = Client.Pathfind(leaderLocation, followDistance, true, true)
                                && !Client.ClientTab.oneLineWalkCbox.Checked
                                && !Server.StopWalking;
                        }
                    }
                    else if (distance > followDistance)
                    {
                        if (Client.IsCasting)
                            Client.IsCasting = false;

                        Client.ConfirmBubble = false;
                        Client.IsWalking = Client.Pathfind(leaderLocation, followDistance, true, true)
                            && Client.ClientTab != null && !Client.ClientTab.oneLineWalkCbox.Checked
                            && !Server.StopWalking;
                    }
                    else
                    {
                        Client.IsWalking = false;
                    }

                    if (Client.OkToBubble)
                    {
                        if (leaderClient != null)
                        {
                            TimeSpan t1 = DateTime.UtcNow - leaderClient.LastStep;
                            if (t1.TotalMilliseconds <= 1000.0)
                                return;

                            TimeSpan t2 = DateTime.UtcNow - Client.LastStep;
                            if (t2.TotalMilliseconds <= 500.0)
                                return;

                        }

                        if (Client.ServerLocation != Client.ClientLocation)
                        {
                            Client.ConfirmBubble = false;
                            Client.RefreshRequest(true);
                        }
                        else
                        {
                            // If map is Lost Ruins or Assassin Dungeon or if any valid creature is close
                            if (Client.Map.Name.Contains("Lost Ruins")
                                || Client.Map.Name.Contains("Assassin Dungeon")
                                || _nearbyValidCreatures.Any(m => Client.ServerLocation.DistanceFrom(m.Location) <= 6))
                            {
                                Client.ConfirmBubble = true;
                            }
                        }
                    }
                }

                // If the leader is on a different map, attempt to follow via LastSeenLocations
                if (leaderLocation.MapID != Client.Map.MapID)
                {
                    if (_leaderID.HasValue &&
                        Client.LastSeenLocations.TryGetValue(_leaderID.Value, out Location lastSeenLocation))
                    {
                        if (lastSeenLocation.MapID == Client.Map.MapID)
                        {
                            Client.IsWalking = Client.Pathfind(lastSeenLocation)
                                && !Client.ClientTab.oneLineWalkCbox.Checked
                                && !Server.StopWalking;
                        }
                        else
                        {
                            Client.IsWalking = false;
                        }
                    }
                    else
                    {
                        Client.IsWalking = false;
                    }
                    return;
                }
            }
            catch (Exception ex)
            {
                Client.IsWalking = false;
                Console.WriteLine($"[FollowWalking] Exception occurred {ex.Message}");
            }
        }

        private Direction GetRandomDirection()
        {
            Direction direction;
            do
            {
                direction = RandomUtils.RandomEnumValue<Direction>();
            } while (direction == Direction.Invalid);
            return direction;
        }


        private bool TryFollowUnstuck()
        {
            // Randomly shuffle directions
            var dirs = Enum.GetValues(typeof(Direction))
                           .Cast<Direction>()
                           .OrderBy(_ => RandomUtils.Random())
                           .ToList();

            foreach (var dir in dirs)
            {
                // The tile in that direction
                var nextLoc = Client.ClientLocation.Offsetter(dir);
                // Check if walkable
                if (Client.Map.IsWalkable(Client, nextLoc))
                {
                    // Perform the walk
                    Client.Walk(dir);
                    return true; // success
                }
            }
            return false; // no walkable direction found
        }

        private bool UnStucker(Player leader)
        {
            if (Server.StopWalking)
            {
                return false;
            }

            if (DateTime.UtcNow.Subtract(leader.LastStep).TotalSeconds > 5.0
                && leader.Location.MapID == Client.Map.MapID
                && (DateTime.UtcNow.Subtract(_lastEXP).TotalSeconds > 5.0
                || DateTime.UtcNow.Subtract(_doorTime).TotalSeconds < 10.0))
            {
                // Get nearby object points (creatures with type Merchant or Aisling)
                HashSet<Location> objectPoints = (from c in Client.GetNearbyObjects().OfType<Creature>()
                                                  where c != null &&
                                                        c.Type == CreatureType.Merchant ||
                                                        c.Type == CreatureType.Aisling
                                                  select c.Location).ToHashSet<Location>();

                // Get warp points
                List<Location> warps = Client.GetWarpPoints(leader.Location);

                // Build a list of all reachable (non-wall) tiles on the leader's current map, excluding warp tiles,
                // object-occupied tiles, and the leader's own current position.
                List<Location> list = (from kvp in Server._maps[leader.Location.MapID].Tiles
                                       where !kvp.Value.IsWall
                                             && !warps.Contains(new Location(leader.Location.MapID, kvp.Key))
                                             && !objectPoints.Contains(new Location(leader.Location.MapID, kvp.Key))
                                             && kvp.Key != leader.Location.Point
                                       select new Location(leader.Location.MapID, kvp.Key)).ToList();

                // Determine the flood fill threshold based on the number of available locations.
                // This threshold helps decide if the area around the leader is sufficiently navigable.
                // It is calculated as 1% of the total reachable tiles but constrained between 5 and 25
                // to maintain a reasonable minimum and maximum threshold.  
                int val = list.Count / 100;
                int num = Math.Max(5, Math.Min(val, 25));

                // Perform a flood fill algorithm starting from the leader's location to identify the
                // connected region of accessible tiles. The flood fill is limited to a maximum of 26 tiles
                // to prevent excessive computation and ensure performance remains optimal.
                // The result is compared against the threshold to determine if the navigable area meets
                // the required criteria for safe movement. If the count of connected tiles is less than
                // or equal to the threshold, it indicates limited navigable space
                bool flag = list.FloodFill(leader.Location).Take(26).Count() <= num;

                if (flag)
                {
                    Console.WriteLine($"[UnStucker] flag was triggered");

                    // Select a random location from the list
                    Random random = new Random();
                    Location location = list.OrderBy(_ => random.Next()).FirstOrDefault();

                    // Perform the route find operation
                    if (Client.Routefind(location, 0, true, true))
                    {
                        Thread.Sleep(1500);
                    }
                }

                return flag;
            }

            return false;
        }



        private void MoveToNearbyLocation()
        {
            // Move to nearby location logic
            Location serverLoc = Client.ServerLocation;
            List<Location> potentialLocations = new List<Location>
            {
                new Location(serverLoc.MapID, serverLoc.X, (short)(serverLoc.Y - 1)),
                new Location(serverLoc.MapID, (short)(serverLoc.X + 1), serverLoc.Y),
                new Location(serverLoc.MapID, serverLoc.X, (short)(serverLoc.Y + 1)),
                new Location(serverLoc.MapID, (short)(serverLoc.X - 1), serverLoc.Y)
            };

            List<Creature> nearbyCreatures = Client.GetNearbyObjects().OfType<Creature>().ToList();

            foreach (var location in potentialLocations)
            {
                if (!Client.Map.IsWall(location)
                    && nearbyCreatures.All(c => c.Location != location)
                    && Client.Routefind(location, 0, true, true))
                {
                    break;
                }
            }

            Thread.Sleep(2500);
        }

        internal void RefreshLastStep()
        {
            bool lastStepF5 = Client.ClientTab.chkLastStepF5.Checked;
            bool exceededStepTime = DateTime.UtcNow.Subtract(Client.LastStep).TotalSeconds > (double)Client.ClientTab.numLastStepTime.Value;

            if (lastStepF5 && exceededStepTime)
            {
                Client.RefreshRequest(true);
            }
        }

        private void WayPointWalking(bool skip = false)
        {
            try
            {
                // 1) Basic checks
                if (ways.Count == 0) return;
                if (Server.ClientStateList.ContainsKey(Client.Name)
                    && Server.ClientStateList[Client.Name] == CharacterState.WaitForSpells)
                    return;

                // If we still have waypoints left
                if (currentWay < ways.Count)
                {
                    Client.WalkSpeed = Client.ClientTab.walkSpeedSldr.Value;

                    // Skip waypoint if there's a monster on top
                    if (skip)
                    {
                        bool anyCreatureOnTop = Client.GetNearbyObjects()
                            .OfType<Creature>()
                            .Any(z => z.Type != CreatureType.WalkThrough
                                      && z.Location.Point == ways[currentWay].Point);

                        if (anyCreatureOnTop)
                        {
                            currentWay++;
                            return;
                        }
                    }

                    // 3) Door Time logic: If you were near a door recently, clamp speed
                    if ((DateTime.UtcNow - _doorTime).TotalSeconds < 2.5
                        && Client.ClientLocation.Point.DistanceFrom(_doorPoint) < 6)
                    {
                        if (Client.WalkSpeed > 350.0)
                            Client.WalkSpeed = 350.0;
                    }
                    else
                    {
                        // 4) Monster-based slowdown logic
                        //    (a) Get nearby creatures not matching certain filters
                        List<Creature> nearbyMobs = Client.GetNearbyValidCreatures()
                            .Where(e => e.Location != Client.ServerLocation)
                            .ToList();

                        // If "ignoreWalledInCbox" is checked, remove walled-in
                        if (Client.ClientTab.ignoreWalledInCbox.Checked)
                        {
                            nearbyMobs = nearbyMobs
                                .Where(z => !Client.IsWalledIn(z.Location))
                                .ToList();
                        }

                        // If "chkIgnoreDionWaypoints" is checked, remove "dioned" mobs
                        if (Client.ClientTab.chkIgnoreDionWaypoints.Checked)
                        {
                            nearbyMobs = nearbyMobs
                                .Where(z => !z.IsDioned)
                                .ToList();
                        }

                        // 5) Slowing conditions (condition1..3) if not bashing
                        //    E.g. if (# of mobs in proximityUpDwn1 >= mobSizeUpDwn1) => slow
                        //    The old code does each "conditionX" in order; if matched => set walkspeed
                        WayForm waysForm = Client.ClientTab.WayForm;
                        if (waysForm.condition1.Checked && !Client.ClientTab.IsBashingActive)
                        {
                            int count = nearbyMobs.Count(c =>
                                Client.WithinRange(c, (int)waysForm.proximityUpDwn1.Value));
                            if (count >= waysForm.mobSizeUpDwn1.Value)
                            {
                                Client.WalkSpeed = (double)waysForm.walkSlowUpDwn1.Value;
                            }
                        }
                        if (waysForm.condition2.Checked && !Client.ClientTab.IsBashingActive)
                        {
                            int count = nearbyMobs.Count(c =>
                                Client.WithinRange(c, (int)waysForm.proximityUpDwn2.Value));
                            if (count >= waysForm.mobSizeUpDwn2.Value)
                            {
                                Client.WalkSpeed = (double)waysForm.walkSlowUpDwn2.Value;
                            }
                        }
                        if (waysForm.condition3.Checked && !Client.ClientTab.IsBashingActive)
                        {
                            int count = nearbyMobs.Count(c =>
                                Client.WithinRange(c, (int)waysForm.proximityUpDwn3.Value));
                            if (count >= waysForm.mobSizeUpDwn3.Value)
                            {
                                Client.WalkSpeed = (double)waysForm.walkSlowUpDwn3.Value;
                            }
                        }

                        // 6) "condition4" logic: if many mobs => STOP
                        if (waysForm.condition4.Checked)
                        {
                            int count = nearbyMobs.Count(c =>
                                Client.WithinRange(c, (int)waysForm.proximityUpDwn4.Value));
                            if (count >= waysForm.mobSizeUpDwn4.Value)
                            {
                                // old code sets "stopped" or triggers backtracking
                                Client.Stopped = true;
                                if (BackTracking()) return;

                                // Possibly handle "okToBubble" logic for certain dungeons
                                if (Client.Map.Name.Contains("Lost Ruins")
                                    || Client.Map.Name.Contains("Assassin Dungeon")
                                    || (_nearbyValidCreatures.Count > 0 && _nearbyValidCreatures.Any(x => x.Location.DistanceFrom(Client.ServerLocation) <= 6)))
                                {
                                    Client.OkToBubble = true;
                                    foreach (Client follower in Server.GetFollowChain(Client))
                                        follower.OkToBubble = true;
                                }

                                Client.IsWalking = false;
                                return;
                            }
                        }

                        // If condition4 not triggered => we resume normal
                        Client.Stopped = false;
                        foreach (Client follower in Server.GetFollowChain(Client))
                            follower.OkToBubble = false;
                        Client.OkToBubble = false;

                        // 7) Check for BackTracking
                        if (BackTracking()) return;

                        // 8) Make sure followers are not pramh / suain, etc.
                        foreach (Client follower in Server.GetFollowChain(Client))
                        {
                            if (follower.HasEffect(EffectsBar.Pramh)
                                || follower.HasEffect(EffectsBar.Suain)
                                || follower.HasEffect(EffectsBar.BeagSuain)
                                || follower.HasEffect(EffectsBar.Skull)
                                || follower.Player.IsSkulled)
                            {
                                return;
                            }
                        }

                        // 9) If override item pickup is checked, handle item pickup
                        if (Client.ClientTab.toggleOverrideCbox.Checked
                            && Client.ClientTab.overrideList.Items.Count > 0)
                        {
                            try
                            {
                                List<ushort> itemsToPickup = new();
                                foreach (var item in Client.ClientTab.overrideList.Items.OfType<string>())
                                {
                                    if (ushort.TryParse(item, out ushort num))
                                        itemsToPickup.Add(num);
                                }

                                // If we only have itemID=140? old code's logic => skip if inventory full
                                if ((itemsToPickup.Count != 1 || itemsToPickup[0] != 140)
                                    && Client.InventoryFull)
                                    return;

                                List<GroundItem> groundItems = Client.GetNearbyGroundItems(12, itemsToPickup.ToArray());
                                // Filter out unreachable or too distant items
                                groundItems = groundItems
                                    .Where(g =>
                                    {
                                        int pathCount = Client.Pathfinder.FindPath(Client.ClientLocation, g.Location).Count;
                                        return pathCount > 0 && pathCount <= (int)Client.ClientTab.overrideDistanceNum.Value;
                                    })
                                    .OrderBy(g => g.Location.DistanceFrom(Client.ClientLocation))
                                    .ToList();

                                if (groundItems.Count > 0)
                                {
                                    GroundItem closest = groundItems[0];
                                    int dist = Client.ClientLocation.DistanceFrom(closest.Location);

                                    if (dist > 2)
                                    {
                                        // pathfind up to distance=2
                                        Client.IsWalking = Client.Pathfind(closest.Location, 2)
                                                           && !Client.ClientTab.oneLineWalkCbox.Checked
                                                           && !Server.StopWalking;
                                        return;
                                    }

                                    // If we are close enough
                                    if (Monitor.TryEnter(Client.CastLock, 200))
                                    {
                                        try
                                        {
                                            Client.Pickup(0, closest.Location);
                                        }
                                        finally
                                        {
                                            Monitor.Exit(Client.CastLock);
                                        }
                                    }
                                    Client.IsWalking = false;
                                    return;
                                }
                            }
                            catch
                            {
                                Client.IsWalking = false;
                            }
                        }
                    } // end of "else" from doorTime check

                    // 10) Routefind to the next waypoint if needed
                    // old code logic:
                    WayForm wform = Client.ClientTab.WayForm;
                    Location currentLocation = ways[currentWay];
                    // If we're already within range => check map ID etc.
                    if (Client.ClientLocation.DistanceFrom(currentLocation)
                        <= (int)wform.distanceUpDwn.Value)
                    {
                        // same map => see if server point is also close
                        if (Client.Map.MapID == currentLocation.MapID)
                        {
                            if (Client.ServerLocation.DistanceFrom(currentLocation)
                                > (int)wform.distanceUpDwn.Value)
                            {
                                // do a quick refresh
                                Client.RefreshRequest();
                            }
                            else
                            {
                                // move to next waypoint
                                currentWay++;
                            }
                        }
                    }
                    else
                    {
                        // Attempt the routefind
                        bool routeOk = Client.Routefind(currentLocation, (short)wform.distanceUpDwn.Value);
                        // Possibly respect "oneLineWalkCbox" or "Server.StopWalking"
                        Client.IsWalking = routeOk && !Client.ClientTab.oneLineWalkCbox.Checked
                                                   && !Server.StopWalking;
                    }

                }
                else
                {
                    // If we've passed the last waypoint, reset
                    currentWay = 0;
                }
            }
            catch (ThreadAbortException)
            {
                Console.WriteLine($"[Waypoints] [{Client.Name}] Thread aborted: ");
            }
            catch (Exception ex)
            {
                string basePath = AppDomain.CurrentDomain.BaseDirectory;

                string logsFolder = Path.Combine(basePath, "Logs");
                if (!Directory.Exists(logsFolder))
                {
                    Directory.CreateDirectory(logsFolder);
                }

                string crashLogsFolder = Path.Combine(logsFolder, "PathfinderCrashLogs");
                if (!Directory.Exists(crashLogsFolder))
                {
                    Directory.CreateDirectory(crashLogsFolder);
                }

                string fileName = $"{DateTime.Now:MM-dd-HH-yyyy_hh-mm-ss_tt}.log";
                string filePath = Path.Combine(crashLogsFolder, fileName);

                File.WriteAllText(filePath, ex.ToString());
            }

        }



        private bool BackTracking()
        {
            try
            {
                // Get list of clients that are following this client and have their 'startStrip' set to 'Stop'
                var clientList = Server.Clients
                    .Where(x => x?.ClientTab?.startStrip.Text == "Stop"
                                && x.ClientTab.followCbox.Checked
                                && x.ClientTab.followText.Text.Equals(Client.Name, StringComparison.OrdinalIgnoreCase))
                    .ToList();

                bool wasTogether = _together;
                _together = true;
                Client clientToFollow = null;

                // Check if any client is on a different map or too far away
                foreach (var client in clientList)
                {
                    if (client.Map.MapID != Client.Map.MapID || client.ServerLocation.DistanceFrom(Client.ServerLocation) > 9)
                    {
                        clientToFollow = client;
                        _together = false;
                        break;
                    }
                }

                // If the clients were together and are now apart, start the timer
                if (wasTogether && !_together)
                {
                    _followerTimer = DateTime.UtcNow;
                }
                // If the clients have been apart for more than 5 seconds, backtrack to the client
                else if (!_together && DateTime.UtcNow.Subtract(_followerTimer).TotalSeconds > 5.0)
                {
                    Client.WalkSpeed = Client.ClientTab.walkSpeedSldr.Value;
                    if (clientToFollow != null)
                    {
                        Client.IsWalking = Client.Routefind(clientToFollow.ServerLocation, 3, shouldBlock: false);
                    }
                    return true;
                }

                return false;
            }
            catch
            {
                _together = true;
                return false;
            }
        }

        private void SWLure()
        {
            throw new NotImplementedException();
        }




        private void UpdateWalkButton(Location targetLocation)
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return;
            }

            if (!clientTab.walkMapCombox.Text.Contains("Nobis") && ShouldProceedWithNavigation(targetLocation))
            {
                UpdateButtonStateBasedOnProximity(targetLocation);
            }
        }

        private bool ShouldProceedWithNavigation(Location targetLocation)
        {
            bool isRouteAvailable = Client.Routefind(targetLocation, 3, false, true, true);
            return !isRouteAvailable && Client.Map.MapID == targetLocation.MapID;
        }

        private void UpdateButtonStateBasedOnProximity(Location targetLocation)
        {
            Location currentLocation = Client.ServerLocation;
            int proximityThreshold = 4;
            if (currentLocation.DistanceFrom(targetLocation) <= proximityThreshold)
            {
                Client.ClientTab.walkBtn.Text = "Walk";
            }
        }

        private void HandleDumbMTGWarp()
        {
            if (Client.Map == null)
            {
                return;
            }

            //The warp into Mt. Giragan 1 is stupid and sometimes drops you in the warp to the world server
            if (Client.Map.MapID.Equals(2120)) //Giragan
            {
                Location location = Client.ServerLocation;
                if (location.X.Equals(39) && (location.Y.Equals(8) || location.Y.Equals(7)))
                {
                    Client.Walk(Direction.West);
                    Thread.Sleep(800);
                }
            }
        }

        private void HandleDialog()
        {
            if (Client.NpcDialog != null && Client.NpcDialog.Equals("You see strange dark fog upstream. Curiosity overcomes you and you take a small raft up the river through the black mist."))
            {
                Client.EnterKey();
                Client.NpcDialog = "";
            }
        }
        private async Task SoundLoop(CancellationToken token)
        {
            if (Client.ClientTab == null || Client == null)
            {
                return;
            }
            try
            {
                while (!token.IsCancellationRequested)
                {
                    //Console.WriteLine("[SoundLoop] Pulse");
                    if (Server._disableSound)
                    {
                        await Task.Delay(250);
                        return;
                    }

                    if (Client.ClientTab == null || Client == null)
                    {
                        return;
                    }

                    if (Client.RecentlyDied)
                    {
                        //soundPlayer.Stream = Resources.warning;
                        soundPlayer.PlaySync();
                        Client.RecentlyDied = false;
                    }

                    if (Client.ClientTab.alertSkulledCbox.Checked && Client.IsSkulled)
                    {
                        soundPlayer.Stream = Resources.skull;
                        soundPlayer.PlaySync();
                    }

                    if (Client.ClientTab.alertRangerCbox.Checked && IsRangerNearBy())
                    {
                        soundPlayer.Stream = Resources.ranger;
                        soundPlayer.PlaySync();
                    }

                    if (Client.ClientTab.alertStrangerCbox.Checked && IsStrangerNearby())
                    {
                        soundPlayer.Stream = Resources.detection;
                        soundPlayer.PlaySync();
                    }

                    if (Client.ClientTab.alertItemCapCbox.Checked && _shouldAlertItemCap)
                    {
                        soundPlayer.Stream = Resources.itemCap;
                        soundPlayer.PlaySync();
                        _shouldAlertItemCap = false;
                    }

                    if (Client.ClientTab.alertDuraCbox.Checked && itemDurabilityAlerts.Contains(true))
                    {
                        for (int i = 0; i < itemDurabilityAlerts.Length; i++)
                        {
                            if (itemDurabilityAlerts[i])
                            {
                                soundPlayer.Stream = Resources.durability;
                                soundPlayer.PlaySync();
                                itemDurabilityAlerts[i] = false; // Set the current alert as handled
                                break; // Exit the loop after handling the first alert
                            }
                        }
                        await Task.Delay(2000);
                    }

                    if (Client.ClientTab.alertEXPCbox.Checked && Client.Experience >= 4290000000U)
                    {
                        soundPlayer.Stream = Resources.expmaxed;
                        soundPlayer.PlaySync();
                    }


                    await Task.Delay(2000);  // Delay before the next iteration to prevent high CPU usage
                }
            }
            catch(OperationCanceledException)
            {

            }
            catch (Exception ex)
            {
                Console.WriteLine($"[SoundLoop] Exception caught: {ex.Message}");
            }
        }

        private async Task BotLoop(CancellationToken token)
        {
            try
            {
                while (!token.IsCancellationRequested)
                {

                        //Console.WriteLine("[BotLoop] Pulse - _shouldThreadStop: " + _shouldThreadStop);

                        try
                        {
                        if (Client.InArena)
                        {
                            await Task.Delay(1000);
                            continue;
                        }

                        if (currentAction == null)
                        {
                            currentAction = Client.ClientTab.currentAction;
                        }

                        _rangerNear = IsRangerNearBy();

                        if (CheckForStopConditions())
                        {
                            await Task.Delay(100);
                            continue;
                        }

                        ProcessPlayersAndCreatures();
                        ProcessCreatureText();

                        if (Client.CurrentHP <= 1U && Client.IsSkulled)
                        {
                            //Console.WriteLine("[BotLoop] Client HP <= 1 and is skulled, handling skull status");
                            HandleSkullStatus();
                            continue;
                        }

                        if (ShouldRequestRefresh())
                        {
                            Client.RefreshRequest(false);
                            _lastRefresh = DateTime.UtcNow;
                            continue;
                        }

                        if (AutoRedConditionsMet())
                        {
                            //Console.WriteLine("[BotLoop] AutoRed conditions met");
                            if (GetSkulledPlayers().Count > 0)
                            {
                                Console.WriteLine("[BotLoop] Skulledplayers > 0, calling RedSkulledPlayers");
                                RedSkulledPlayers();
                            }
                            else
                            {
                                _dontWalk = false;
                            }
                        }

                        if (IsStrangerNearby())
                        {
                            FilterStrangerPlayers();
                        }

                        double botCheckSeconds = DateTime.UtcNow.Subtract(_botChecks).TotalSeconds;

                        if (botCheckSeconds < 2.5)
                        {
                            continue;
                        }

                        ManageSpellHistory();
                        UpdateVineTimer();
                        PerformActions();

                    }
                    catch (Exception ex)
                    {
                        Console.WriteLine($"[BotLoop] Exception caught in inner try: {ex.Message}");
                    }
                }

                //Console.WriteLine("Exiting BotLoop, _shouldThreadStop: " + _shouldThreadStop);
            }
            catch (OperationCanceledException)
            {
                
            }
            catch (Exception ex)
            {
                Console.WriteLine($"[BotLoop] Exception caught in outer try: {ex.Message}");
            }
        }

        private void UpdateVineTimer()
        {
            if (Client.HasSpell("Lyliac Vineyard") && !Client.Spellbook["Lyliac Vineyard"].CanUse)
            {
                _lastVineCast = DateTime.UtcNow;
            }
        }

        private bool ProcessCreatureText()
        {
            if (Client == null || Client.ClientTab == null)
                return false;

            if (!Client.ClientTab.chkSpellStatus.Checked)
                return false;

            foreach (Creature creature in _nearbyValidCreatures)
            {
                // Retrieve the creature's states
                bool isCursed = creature.GetState<bool>(CreatureState.IsCursed);
                bool isFassed = creature.GetState<bool>(CreatureState.IsFassed);

                // Determine the text to display based on the creature's states
                string displayText = string.Empty;

                if (isCursed && isFassed)
                {
                    // Creature is both cursed and fassed
                    displayText = "[C/F]";
                }
                else if (isCursed)
                {
                    // Creature is only cursed
                    displayText = "[C]";
                }
                else if (isFassed)
                {
                    // Creature is only fassed
                    displayText = "[F]";
                }

                // Display the text if applicable
                if (!string.IsNullOrEmpty(displayText))
                {
                    Client.DisplayTextOverTarget(2, creature.ID, displayText);
                }
            }

            return true;
        }

        internal bool IsRangerNearBy()
        {
            if (!Settings.Default.paranoiaMode)
            {
                return Client.GetNearbyPlayers().Any(new Func<Player, bool>(RangerListContains));
            }
            return IsStrangerNearby();
        }
        private bool RangerListContains(Player player)
        {
            return CONSTANTS.KNOWN_RANGERS.Contains(player.Name, StringComparer.OrdinalIgnoreCase);
        }
        private bool CheckForStopConditions()
        {

            return (Client.ClientTab != null && Client.InventoryFull && Client.ClientTab?.toggleFarmBtn.Text == "Farming") ||
                   (Client.ClientTab != null && Client.Bot._hasDeposited && Client.ClientTab?.toggleFarmBtn.Text == "Farming") ||
                   Client.ExchangeOpen || Client.ClientTab == null || Client.Dialog != null || _dontCast;
        }
        private void ProcessPlayersAndCreatures()
        {
            NearbyAllies = Client.GetNearbyGroupedPlayers();
            _nearbyValidCreatures = Client.GetNearbyValidCreatures(11);
            var nearbyPlayers = Client.GetNearbyPlayers();
            _playersExistingOver250ms = nearbyPlayers?
                .Where(p => (DateTime.UtcNow - p.Creation).TotalMilliseconds > 250)
                .ToList();
            _skulledPlayers.Clear();
        }
        private void HandleSkullStatus()
        {
            currentAction.Text = Client.Action + "Nothing, you're dead";
            _skullTime = (_skullTime == DateTime.MinValue) ? DateTime.UtcNow : _skullTime;
            LogIfSkulled();
            LogIfSkulledAndSurrounded();
            if (!Client.SafeScreen)
            {
                Client.ServerMessage((byte)ServerMessageType.TopRight, "Skulled for: " + DateTime.UtcNow.Subtract(_skullTime).Seconds.ToString() + " seconds.");
            }
        }
        private void LogIfSkulled()
        {
            bool isOptionsSkullCboxChecked = Client.ClientTab?.optionsSkullCbox.Checked == true;

            if (isOptionsSkullCboxChecked && DateTime.UtcNow.Subtract(_skullTime).TotalSeconds > 6.0)
            {
                string text = AppDomain.CurrentDomain.BaseDirectory + "\\skull.txt";
                File.WriteAllText(text, string.Concat(new string[]
                {
                    DateTime.UtcNow.ToLocalTime().ToString(),
                    "\n",
                    Client.Map.Name,
                    ": (",
                    Client.ServerLocation.ToString(),
                    ")"
                }));
                Process.Start(text);
                Client.DisconnectWait(false);
            }
        }
        private void LogIfSkulledAndSurrounded()
        {
            bool isOptionsSkullSurrboxChecked = Client.ClientTab?.optionsSkullSurrbox.Checked == true;
            if (isOptionsSkullSurrboxChecked && DateTime.UtcNow.Subtract(_skullTime).TotalSeconds > 4.0 && Client.IsLocationSurrounded(Client.ServerLocation))
            {
                string text2 = AppDomain.CurrentDomain.BaseDirectory + "\\skull.txt";
                File.WriteAllText(text2, string.Concat(new string[]
                {
                    DateTime.UtcNow.ToLocalTime().ToString(),
                    "\n",
                    Client.Map.Name,
                    ": (",
                    Client.ServerLocation.ToString(),
                    ")"
                }));
                Process.Start(text2);
                Client.DisconnectWait(false);
            }
        }
        private bool ShouldRequestRefresh()
        {
            return DateTime.UtcNow.Subtract(Client.LastStep).TotalSeconds > 20.0 &&
                   DateTime.UtcNow.Subtract(_lastEXP).TotalSeconds > 20.0 &&
                   DateTime.UtcNow.Subtract(_lastRefresh).TotalSeconds > 30.0;
        }

        private bool AutoRedConditionsMet()
        {
            return Client.ClientTab != null && _playersExistingOver250ms != null && Client.ClientTab?.autoRedCbox.Checked == true;
        }
        private List<Player> GetSkulledPlayers()
        {
            if (_playersExistingOver250ms.Any(p => p.IsSkulled))
            {
                _playersExistingOver250ms.RemoveAll(p => p.IsSkulled);
                foreach (Player player in Client.GetNearbyPlayers().Where(IsSkulledFriendOrGroupMember))
                {
                    _skulledPlayers.Add(player);
                }
                return _skulledPlayers = _skulledPlayers.OrderBy(DistanceFromPlayer).ToList();
            }
            return new List<Player>();
        }

        private bool RedSkulledPlayers()
        {
            if (Client == null || Client.ClientTab == null)
                return false;

            Console.WriteLine("[BotLoop] RedSkulledPlayers called");

            if (_skulledPlayers.Count > 0 && Client.ClientTab?.autoRedCbox.Checked == true)
            {
                Console.WriteLine("[BotLoop] Players needing red > 0 and autoRed checked");

                Player player = _skulledPlayers[0];
                Console.WriteLine($"[BotLoop] Target player: {player?.Name}, HealthPercent: {player?.HealthPercent}");

                var inventory = Client.Inventory;
                bool canUseBeetleAid = inventory.Contains("Beetle Aid") && Client.IsRegistered &&
                                       DateTime.UtcNow.Subtract(_lastUsedBeetleAid).TotalMinutes > 2.0;
                bool canUsePotions = inventory.Contains("Komadium") || inventory.Contains("beothaich deum");

                Console.WriteLine($"[BotLoop] Can use Beetle Aid: {canUseBeetleAid}, Can use potions: {canUsePotions}");

                if (canUseBeetleAid || canUsePotions)
                {
                    _dontWalk = true;
                    Direction direction = player.Location.Point.GetDirection(Client.ServerLocation.Point);
                    Console.WriteLine($"[BotLoop] Calculated direction to player: {direction}");

                    if (Client.ServerLocation.DistanceFrom(player.Location) > 1)
                    {
                        Console.WriteLine("[BotLoop] Server distance from player > 1");

                        if (Client.ClientLocation.DistanceFrom(player.Location) == 1)
                        {
                            Console.WriteLine("[BotLoop] Client distance from player = 1, requesting refresh");
                            Client.RefreshRequest(true);
                        }

                        Console.WriteLine("[BotLoop] Pathfinding to player location");
                        Client.Pathfind(player.Location, 1, true, true);
                    }
                    else if (direction != Client.ServerDirection)
                    {
                        Console.WriteLine("[BotLoop] Turning to face player");
                        Client.Turn(direction);
                    }
                    else
                    {
                        if (canUseBeetleAid && Client.UseItem("Beetle Aid"))
                        {
                            _lastUsedBeetleAid = DateTime.UtcNow;
                            Console.WriteLine("[BotLoop] Used Beetle Aid, updated lastUsedBeetleAid");
                            player.AnimationHistory[(ushort)SpellAnimation.Skull] = DateTime.UtcNow.AddSeconds(-2);
                        }
                        else if (canUsePotions && (Client.UseItem("Komadium") || Client.UseItem("beothaich deum")))
                        {
                            Console.WriteLine("[BotLoop] Used other item (Komadium or beothaich deum)");
                            player.AnimationHistory[(ushort)SpellAnimation.Skull] = DateTime.UtcNow.AddSeconds(-2);
                            Thread.Sleep(1000); // Consider async/await pattern if possible
                        }

                        Console.WriteLine("[BotLoop] Using Transferblood skill");
                        Client.UseSkill("Transferblood");

                        return false;
                    }
                }
                if (player == null || !Client.GetNearbyPlayers().Contains(player) || player.HealthPercent > 30 || DateTime.UtcNow.Subtract(player.AnimationHistory[(ushort)SpellAnimation.Skull]).TotalSeconds > 5.0)
                {
                    Console.WriteLine("[BotLoop] Conditions for ending red-skull action met, resetting player and dontWalk flag");
                    player = null;
                    _dontWalk = false;

                    return false;
                }
            }

            Console.WriteLine("[BotLoop] RedSkulledPlayers method returning true");
            return true;
        }


        private bool IsSkulledFriendOrGroupMember(Player player)
        {
            return Client.GroupBindingList.Concat(Client.FriendBindingList).Contains(player.Name, StringComparer.CurrentCultureIgnoreCase) && player.IsSkulled;
        }

        private int DistanceFromPlayer(Player player)
        {
            return Client.ServerLocation.DistanceFrom(player.Location);
        }

        private void FilterStrangerPlayers()
        {
            var duplicateOrHiddenPlayers = new List<Player>();
            foreach (var player in _playersExistingOver250ms)
            {
                foreach (var otherPlayer in _playersExistingOver250ms)
                {
                    if (player != otherPlayer && (player.Location.Equals(otherPlayer.Location) || otherPlayer.IsHidden) && !duplicateOrHiddenPlayers.Contains(player))
                    {
                        duplicateOrHiddenPlayers.Add(player);
                    }
                }
                foreach (var creature in _nearbyValidCreatures)
                {
                    if (creature != null && player.Location.Equals(creature.Location) && !duplicateOrHiddenPlayers.Contains(player))
                    {
                        duplicateOrHiddenPlayers.Add(player);
                    }
                }
            }
            _playersExistingOver250ms = _playersExistingOver250ms.Except(duplicateOrHiddenPlayers).ToList();
        }

        private bool PerformActions()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null || Client.ClientTab == null)
            {
                return false;
            }

            _autoStaffSwitch = clientTab.autoStaffCbox.Checked;
            _fasSpiorad = Client.HasEffect(EffectsBar.FasSpiorad) || (Client.HasSpell("fas spiorad") && DateTime.UtcNow.Subtract(Client.Spellbook["fas spiorad"].LastUsed).TotalSeconds < 1.5);
            _isSilenced = Client.HasEffect(EffectsBar.Silenced);

            Loot();
            AoSuain();
            WakeScroll();
            AutoGem();
            UpdatePlayersListBasedOnStrangers();
            CheckFasSpioradRequirement();

            try
            {
                if (CastDefensiveSpells())
                {
                    CastOffensiveSpells();
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine($"Exception in PerformSpellActions: {ex.Message}");
            }

            Client currentClient = Client;
            byte? castLinesCountNullable;

            if (currentClient == null)
            {
                castLinesCountNullable = null;
            }
            else
            {
                Spell castedSpell = currentClient.LastSpell;
                castLinesCountNullable = (castedSpell != null) ? new byte?(castedSpell.CastLines) : null;
            }

            byte? castLinesCount = castLinesCountNullable;
            int? castLines = (castLinesCount != null) ? new int?(castLinesCount.GetValueOrDefault()) : null;

            if (castLines.GetValueOrDefault() <= 0 & castLines != null)
            {
                // Throttle 0 line spells if a stranger is nearby
                if (IsStrangerNearby())
                    Thread.Sleep(330);
            }


            return true;
        }
        private bool CastDefensiveSpells()
        {
            FasSpiorad();
            Heal();
            Hide();
            BubbleBlock();
            DispellAllySuain();
            DispellPlayerCurse();
            BeagCradh();
            DispellAllyCurse();
            BeagCradhAllies();
            AoPoison();
            Dion();
            Aite();
            Fas();
            AiteAllies();
            FasAllies();
            DragonScale();
            Armachd();
            ArmachdAllies();


            Other(); //Deireas Faileas, Monk Forms, Asgall, Perfect Defense,
                     //Aegis Spehre, ao beag suain, Muscle Stim, Nerve Stim, Mist, Mana Ward
                     //Vanish Elixir, Regens, Mantid Scent, Repair hammer
            Comlhas();
            Lyliac();
            return true;
        }

        private void Lyliac()
        {
            if (Client == null || Client.ClientTab == null)
            {
                return;
            }

            HandleLyliac();
            HandleVineyard();
        }

        public bool HandleLyliac()
        {
            foreach (Ally ally in ReturnAllyList())
            {
                if (!ally.Page.miscLyliacCbox.Checked)
                    continue;

                bool casted = TryCastLyliacPlantForAlly(ally);

                if (casted)
                {
                    return true;
                }
            }
            return false;
        }

        private bool TryCastLyliacPlantForAlly(Ally ally)
        {
            if (!IsAlly(ally, out Player player, out Client alt))
                return false;

            if (!int.TryParse(ally.Page.miscLyliacTbox.Text, out int threshold))
                return false;

            // If we have an alt client, check its MP
            if (alt != null)
            {
                if (alt.CurrentMP < threshold)
                {
                    Client.UseSpell("Lyliac Plant", player, _autoStaffSwitch);
                    alt.Bot._needFasSpiorad = false;
                    return true;
                }
            }
            // Otherwise, check user's last animation time
            else
            {
                if (player.AnimationHistory.TryGetValue(84, out DateTime animStart))
                {
                    TimeSpan elapsed = DateTime.UtcNow - animStart;
                    if (elapsed.TotalMilliseconds <= threshold)
                        return false;
                }

                Client.UseSpell("Lyliac Plant", player, _autoStaffSwitch);
                return true;
            }

            return false;
        }


        public void HandleVineyard()
        {

            if (!int.TryParse(Client.ClientTab?.vineText.Text, out int vineDelay))
                return;

            if (!Client.ClientTab?.vineyardCbox.Checked == true
                || !Client.HasSpell("Lyliac Vineyard")
                || !Client.Spellbook["Lyliac Vineyard"].CanUse)
                return;

            bool shouldCast = ShouldCastVineyard(vineDelay, Client.ClientTab?.vineCombox.Text);

            if (shouldCast)
            {
                Client.UseSpell("Lyliac Vineyard", staffSwitch: _autoStaffSwitch);
            }

            return;
        }

        private bool ShouldCastVineyard(int vineDelay, string comboText)
        {
            // If the combo box is not "Delay", use group MP-based logic
            if (comboText != "Delay")
            {
                return Server.Clients.Any(c =>
                    c != null
                    && !string.IsNullOrEmpty(c.Name)
                    && !c.Name.Contains("[")
                    && Client.GroupedPlayers.Any(g => g.Equals(c.Name, StringComparison.OrdinalIgnoreCase))
                    && c.CurrentMP < vineDelay);
            }
            else
            {
                TimeSpan timeSince = DateTime.UtcNow - _lastVineCast;
                return timeSince.TotalMilliseconds > vineDelay;
            }
        }


        private bool Comlhas()
        {
            if (Group == null) { return false; }

            if (Group.allyMDCRbtn.Checked)
            {
                var playerToDion = NearbyAllies.FirstOrDefault(p => !p.IsDioned);

                if (playerToDion != null)
                {
                    Console.WriteLine($"[Comlhas] PlayerToDion: {playerToDion?.Name}, Hash: {playerToDion.GetHashCode()}, has dion: {playerToDion.IsDioned}");
                    Client.UseSpell("mor dion comlha", null, _autoStaffSwitch, false);
                    return false;
                }
            }

            if (Group.allyMDCSpamRbtn.Checked)
            {
                if (Client.UseSpell("mor dion comlha", null, _autoStaffSwitch, false))
                {
                    return false;
                }
            }
            else if (Group.allyMICSpamRbtn.Checked)
            {
                if (!Client.UseSpell("Nuadhiach Le Cheile", null, _autoStaffSwitch, false) &&
                    !Client.UseSpell("ard ioc comlha", null, _autoStaffSwitch, false) &&
                    !Client.UseSpell("mor ioc comlha", null, _autoStaffSwitch, false))
                {
                    Client.UseSpell("ioc comlha", null, _autoStaffSwitch, false);
                }

                return false;
            }

            return true;
        }

        private bool Other()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                //Exit early if clienttab is null e.g., switching servers
                return false;
            }

            if (clientTab.deireasFaileasCbox.Checked && !Client.HasEffect(EffectsBar.DeireasFaileas))
            {
                Client.UseSpell("deireas faileas", null, _autoStaffSwitch, true);
                return false;
            }

            if (clientTab.dragonsFireCbox.Checked && Client.IsRegistered && !Client.HasEffect(EffectsBar.DragonsFire))
            {
                Client.UseItem("Dragon's Fire");
            }

            if (clientTab.druidFormCbox.Checked && !Client.HasEffect(EffectsBar.FeralForm) && !Client.HasEffect(EffectsBar.KaruraForm) && !Client.HasEffect(EffectsBar.KomodasForm) && !_swappingNecklace)
            {
                if (!Client.UseSpell("Feral Form", null, _autoStaffSwitch, true) && !Client.UseSpell("Wild Feral form", null, _autoStaffSwitch, true) && !Client.UseSpell("Fierce Feral Form", null, _autoStaffSwitch, true) && !Client.UseSpell("Master Feral Form", null, _autoStaffSwitch, true) && !Client.UseSpell("Karura Form", null, _autoStaffSwitch, true) && !Client.UseSpell("Wild Karura Form", null, _autoStaffSwitch, true) && !Client.UseSpell("Fierce Karura Form", null, _autoStaffSwitch, true) && !Client.UseSpell("Master Karura Form", null, _autoStaffSwitch, true) && !Client.UseSpell("Komodas Form", null, _autoStaffSwitch, true) && !Client.UseSpell("Wild Komodas Form", null, _autoStaffSwitch, true) && !Client.UseSpell("Fierce Komodas Form", null, _autoStaffSwitch, true))
                {
                    Client.UseSpell("Master Komodas Form", null, _autoStaffSwitch, true);
                }
                Thread.Sleep(1000);
            }

            if (clientTab.asgallCbox.Checked && !Client.HasEffect(EffectsBar.AsgallFaileas))
            {
                Client.UseSpell("asgall faileas", null, true, true);
            }

            if (clientTab.perfectDefenseCbox.Checked && !Client.HasEffect(EffectsBar.PerfectDefense))
            {
                Client.UseSkill("Perfect Defense");
            }

            if (clientTab.aegisSphereCbox.Checked && !Client.HasEffect(EffectsBar.Armachd))
            {
                Client.UseSpell("Aegis Sphere", null, false, true);
            }

            if (clientTab.aoSuainCbox.Checked && Client.HasEffect(EffectsBar.BeagSuain))
            {
                Client.UseSkill("ao beag suain");
            }

            if (clientTab.muscleStimulantCbox.Checked && Client.IsRegistered && !Client.HasEffect(EffectsBar.FasDeireas))
            {
                Client.UseItem("Muscle Stimulant");
            }

            if (clientTab.nerveStimulantCbox.Checked && Client.IsRegistered && !Client.HasEffect(EffectsBar.Beannaich))
            {
                Client.UseItem("Nerve Stimulant");
            }

            if (clientTab.disenchanterCbox.Checked && DateTime.UtcNow.Subtract(_lastDisenchanterCast).TotalMinutes > 6.0)
            {
                Client.UseSpell("Disenchanter", null, _autoStaffSwitch, true);
                Thread.Sleep(1000);
                return false;
            }

            if (clientTab.monsterCallCbox.Checked && Client.IsRegistered && DateTime.UtcNow.Subtract(_lastUsedMonsterCall).TotalSeconds > 2.0 && Client.UseItem("Monster Call"))
            {
                _lastUsedMonsterCall = DateTime.UtcNow;
            }

            if (clientTab.mistCbox.Checked && !Client.HasEffect(EffectsBar.Mist))
            {
                Client.UseSpell("Mist", null, _autoStaffSwitch, true);
            }

            if (clientTab.manaWardCbox.Checked)
            {
                Client.UseSpell("Mana Ward", null, false, false);
            }

            if (clientTab.vanishingElixirCbox.Checked && Client.IsRegistered)
            {
                foreach (Player ally in NearbyAllies)
                {
                    if (ally != Client.Player && !ally.IsHidden && DateTime.UtcNow.Subtract(_lastUsedVanishElixir).TotalSeconds > 2.0)
                    {
                        _lastUsedVanishElixir = DateTime.UtcNow;
                        Client.UseItem("Vanishing Elixir");
                        Console.WriteLine("[Other] Used Vanishing Elixir");
                    }
                }
            }

            if (clientTab.autoDoubleCbox.Checked && !Client.HasEffect(EffectsBar.BonusExperience) && Client.IsRegistered && Client.CurrentMP > 100)
            {
                // Mapping of combobox text to the item names
                var itemMappings = new Dictionary<string, string>
                {
                    { "Kruna 50%", "50 Percent EXP/AP Bonus" },
                    { "Kruna 100%", "Double EXP/AP Bonus" },
                    { "Xmas 50%", "XMas Bonus Exp-Ap" },
                    { "Star 100%", "Double Bonus Exp-Ap" },
                    { "Vday 100%", "VDay Bonus Exp-Ap" }
                };

                // Check for special case where additional logic is needed
                if (clientTab.doublesCombox.Text == "Xmas 100%")
                {
                    var itemText = Client.HasItem("Christmas Double Exp-Ap") ? "Christmas Double Exp-Ap" : "XMas Double Exp-Ap";
                    clientTab.UseDouble(itemText);
                }
                else if (itemMappings.TryGetValue(clientTab.doublesCombox.Text, out var itemText))
                {
                    clientTab.UseDouble(itemText);
                }

                clientTab.UpdateExpBonusTimer();
            }

            if (clientTab.autoMushroomCbox.Checked && !Client.HasEffect(EffectsBar.BonusMushroom) && Client.IsRegistered && Client.CurrentMP > 100)
            {
                var itemMappings = new Dictionary<string, string>
                {
                    { "Double", "Double Experience Mushroom" },
                    { "50 Percent", "50 Percent Experience Mushroom" },
                    { "Greatest", "Greatest Experience Mushroom" },
                    { "Greater", "Greater Experience Mushroom" },
                    { "Great", "Great Experience Mushroom" },
                    { "Experience Mushroom", "Experience Mushroom" }
                };

                if (clientTab.mushroomCombox.Text == "Best Available")
                {
                    var mushrooom = clientTab.FindBestMushroomInInventory(Client);
                    clientTab.UseMushroom(mushrooom);
                }
                else if (itemMappings.TryGetValue(clientTab.mushroomCombox.Text, out var mushroom))
                {
                    clientTab.UseMushroom(mushroom);
                }


                clientTab.UpdateMushroomBonusTimer();
            }



            if (clientTab.regenerationCbox.Checked && (!Client.HasEffect(EffectsBar.Regeneration) || !Client.HasEffect(EffectsBar.IncreasedRegeneration)))
            {
                if (Client.HasSpell("Increased Regeneration") && !Client.HasEffect(EffectsBar.IncreasedRegeneration))
                {
                    Client.UseSpell("Increased Regeneration", Client.Player, _autoStaffSwitch, true);
                    return false;
                }
                if (Client.Spellbook.Any(spell => spell.Name != "Increased Regeneration" && spell.Name.Contains("Regeneration"))
                   && !Client.HasEffect(EffectsBar.Regeneration))
                {
                    TryCastAnyRank("Regeneration", Client.Player, _autoStaffSwitch, true);
                    return false;
                }
            }
            foreach (Ally currentAlly in ReturnAllyList())
            {
                if (_playersExistingOver250ms.Count > 0)
                {
                    foreach (Player player in _playersExistingOver250ms)
                    {
                        if (player != null && currentAlly != null && currentAlly.Page != null && currentAlly.Page.dbRegenCbox != null &&
                            player.Name.Equals(currentAlly.Name, StringComparison.OrdinalIgnoreCase) && player != Client.Player && currentAlly.Page.dbRegenCbox.Checked)
                        {
                            Client client = Client.Server.GetClient(currentAlly.Name);
                            if (client != null)
                            {
                                if (!client.HasEffect(EffectsBar.IncreasedRegeneration) && Client.UseSpell("Increased Regeneration", client.Player, _autoStaffSwitch, true))
                                {
                                    return false;
                                }
                                if (Client.Spellbook.Any(s => s.Name != "Increased Regeneration" && s.Name.Contains("Regeneration"))
                                    && !client.HasEffect(EffectsBar.Regeneration)
                                    && TryCastAnyRank("Regeneration", client.Player, _autoStaffSwitch, true))
                                {
                                    return false;
                                }
                            }
                            else
                            {
                                // Fallback to using spells on the player directly if the client for the ally wasn't found
                                if ((!player.AnimationHistory.ContainsKey((ushort)SpellAnimation.IncreasedRegeneration) || DateTime.UtcNow.Subtract(player.AnimationHistory[(ushort)SpellAnimation.IncreasedRegeneration]).TotalSeconds > 1.5) && Client.UseSpell("Increased Regeneration", player, _autoStaffSwitch, true))
                                {
                                    return false;
                                }
                                if (Client.Spellbook.Any(s => s.Name != "Increased Regeneration" && s.Name.Contains("Regeneration"))
                                    && (!player.AnimationHistory.ContainsKey((ushort)SpellAnimation.Regeneration)
                                        || DateTime.UtcNow.Subtract(player.AnimationHistory[(ushort)SpellAnimation.Regeneration]).TotalSeconds > 1.5)
                                    && TryCastAnyRank("Regeneration", player, _autoStaffSwitch, true))
                                {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }

            if (clientTab.mantidScentCbox.Checked && Client.IsRegistered && !Client.HasEffect(EffectsBar.MantidScent))
            {
                if (Client.UseItem("Mantid Scent") || Client.UseItem("Potent Mantid Scent"))
                {
                    return true;
                }

                clientTab.mantidScentCbox.Checked = false;
                Client.ServerMessage((byte)ServerMessageType.Whisper, "You do not own Mantid Scent");
                return false;
            }

            if (clientTab.equipmentrepairCbox.Checked && Client.NeedsToRepairHammer && DateTime.UtcNow.Subtract(_hammerTimer).TotalMinutes > 40.0)
            {
                Client.UseHammer();
            }

            return false;
        }

        private bool DispellAllySuain()
        {

            foreach (Ally ally in ReturnAllyList())
            {
                if (ally.Page == null) { break; }

                bool isDispelSuainChecked = ally.Page.dispelSuainCbox.Checked;

                if (isDispelSuainChecked && TryGetSuainedAlly(ally, out Player player, out Client client))
                {

                    Client.UseSpell("ao suain", player, _autoStaffSwitch, true);
                    //Console.WriteLine($"[DispellAllySuain] Player {player.Name}, Hash: {player.GetHashCode()}. IsSuained: {player.IsSuained}");

                    return false;

                }
            }

            return true;
        }

        private bool TryGetSuainedAlly(Ally ally, out Player player, out Client client)
        {
            if (IsAlly(ally, out player, out client))
            {
                //Console.WriteLine($"[TryGetSuainedAlly] Player.ID: {player.ID}, Hash: {player.GetHashCode()}, Player {player.Name} IsSuained: {player.IsSuained}");
                return player.IsSuained;
            }

            return false;
        }

        private bool FasSpiorad()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            if (_needFasSpiorad)
            {
                uint currentMP = Client.CurrentMP;
                DateTime startTime = DateTime.UtcNow;

                while (_needFasSpiorad)
                {
                    int fasSpioradThreshold;

                    bool isFasSpioradChecked = clientTab.fasSpioradCbox.Checked;
                    bool isThresholdParsed = int.TryParse(clientTab.fasSpioradText.Text.Trim(), out fasSpioradThreshold);
                    bool isBelowThreshold = Client.CurrentMP <= fasSpioradThreshold;

                    if (isFasSpioradChecked && isThresholdParsed && isBelowThreshold)
                    {
                        Client.UseSpell("fas spiorad", null, _autoStaffSwitch, false);
                    }

                    bool hasManaReachedHalf = Client.CurrentMP >= Client.Stats.MaximumMP / 2U;
                    bool hasManaIncreasedByFivePercent = Client.CurrentMP - currentMP >= Client.Stats.MaximumMP / 20U;
                    bool isDurationExceeded = DateTime.UtcNow.Subtract(startTime).TotalSeconds > 20.0;

                    if (hasManaReachedHalf || hasManaIncreasedByFivePercent || isDurationExceeded)
                    {
                        _needFasSpiorad = false;
                    }

                    Thread.Sleep(10);
                }
            }

            return true;
        }

        private bool BeagCradh()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            bool isBeagCradhChecked = clientTab.beagCradhCbox.Checked;
            bool isPlayerCursed = (bool)(Client.Player?.IsCursed);

            if (isBeagCradhChecked && !isPlayerCursed)
            {
                Client.UseSpell("beag cradh", Client.Player, _autoStaffSwitch, false);
                return false;
            }

            return true;
        }

        private bool BeagCradhAllies()
        {

            foreach (Ally ally in ReturnAllyList())
            {
                bool isBeagCradhChecked = ally.Page.dbBCCbox.Checked;

                if (isBeagCradhChecked && IsAlly(ally, out Player player, out Client client) && !player.IsCursed)
                {
                    Client.UseSpell("beag cradh", player, _autoStaffSwitch, false);
                    return false;
                }
            }

            return true;
        }

        private bool WakeScroll()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            if (!clientTab.wakeScrollCbox.Checked || !Client.IsRegistered)
                return false;

            var alliesToClear = NearbyAllies
                .Where(player => IsAllyAffectedByPramhOrAsleep(player))
                .ToList();

            if (alliesToClear.Count == 0)
                return false;

            if (!Client.UseItem("Wake Scroll"))
                return false;

            foreach (var player in alliesToClear)
            {
                Server.GetClient(player.Name)?.ClearEffect(EffectsBar.Pramh);
            }

            return true;
        }

        internal bool IsAllyAffectedByPramhOrAsleep(Player player)
        {
            if (!player.IsAsleep)
            {
                Client client = Server.GetClient(player.Name);
                return client != null && client.HasEffect(EffectsBar.Pramh);
            }
            return true;
        }

        private bool AoPoison()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            // Process allies first
            AoPoisonForAllies();

            if (!clientTab.aoPoisonCbox.Checked)
                return true;

            // Check that the player is affected by poison
            if (!Client.HasEffect(EffectsBar.Poison) || !Client.Player.IsPoisoned)
                return true;

            var currentTime = DateTime.UtcNow;
            bool canUseFungusExtract = (currentTime - _lastUsedFungusBeetle).TotalSeconds > 1.0;

            // Use Fungus Beetle Extract if conditions are met
            if (clientTab.fungusExtractCbox.Checked &&
                Client.IsRegistered &&
                Client.HasItem("Fungus Beetle Extract") &&
                canUseFungusExtract)
            {
                UseFungusBeetleExtract();
                _lastUsedFungusBeetle = currentTime;
            }
            else
            {
                Client.UseSpell("ao puinsein", Client.Player, _autoStaffSwitch, false);
            }

            return true;
        }

        private void AoPoisonForAllies()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return;
            }

            foreach (Ally ally in ReturnAllyList())
            {
                if (!ally.Page.dispelPoisonCbox.Checked)
                    continue;

                // Resolve the ally into a Player and, if available, a Client.
                if (!IsAlly(ally, out Player allyPlayer, out Client allyClient))
                    continue;

                // Determine if the ally is poisoned by checking both the Player and Client (if available).
                bool allyIsPoisoned = allyPlayer.IsPoisoned || (allyClient != null && allyClient.HasEffect(EffectsBar.Poison));
                if (!allyIsPoisoned)
                    continue;

                // Check if we can use Fungus Beetle Extract based on the cooldown.
                bool canUseFungusExtract = DateTime.UtcNow.Subtract(_lastUsedFungusBeetle).TotalSeconds > 1.0;
                if (clientTab.fungusExtractCbox.Checked && Client.IsRegistered && Client.HasItem("Fungus Beetle Extract") && canUseFungusExtract)
                {
                    UseFungusBeetleExtract();
                    _lastUsedFungusBeetle = DateTime.UtcNow;
                }
                else
                {
                    Client.UseSpell("ao puinsein", allyPlayer, _autoStaffSwitch, false);
                }
            }
        }


        private void UseFungusBeetleExtract()
        {
            for (int j = 0; j < 6; j++)
            {
                Client.UseItem("Fungus Beetle Extract");
            }
            _lastUsedFungusBeetle = DateTime.UtcNow;
        }

        private bool Aite()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            bool isAiteChecked = clientTab.aiteCbox.Checked;
            bool isPlayerAited = Client.Player.IsAited;
            double aiteDuration = Client.Player.GetState<double>(CreatureState.AiteDuration);
            string aiteSpell = clientTab.aiteCombox.Text;

            if (isAiteChecked && !Client.HasEffect(EffectsBar.NaomhAite) && (!isPlayerAited || aiteDuration != 2.0))
            {
                Client.UseSpell(aiteSpell, Client.Player, _autoStaffSwitch, false);
                return false;
            }

            return true;
        }

        private bool AiteAllies()
        {
            foreach (Ally ally in ReturnAllyList())
            {
                bool isAiteChecked = ally.Page.dbAiteCbox.Checked;
                string spellName = ally.Page.dbAiteCombox.Text;

                if (isAiteChecked && IsAlly(ally, out Player player, out Client client) && !player.IsAited)
                {
                    Client.UseSpell(spellName, player, _autoStaffSwitch, false);
                    return true;
                }
            }
            return false;
        }

        private bool FasAllies()
        {
            foreach (Ally ally in ReturnAllyList())
            {
                bool isFasChecked = ally.Page.dbFasCbox.Checked;
                string spellName = ally.Page.dbFasCombox.Text;

                if (isFasChecked && IsAlly(ally, out Player player, out Client client) && !player.IsFassed)
                {
                    Client.UseSpell(spellName, player, _autoStaffSwitch, false);
                    return true;
                }
            }
            return false;
        }

        private bool Fas()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            bool isFasChecked = clientTab.fasCbox.Checked;
            bool isPlayerFassed = Client.Player.IsFassed;
            double fasDuration = Client.Player.GetState<double>(CreatureState.FasDuration);
            string fasSpell = clientTab.fasCombox.Text;

            if (isFasChecked && !Client.HasEffect(EffectsBar.FasNadur) && (!isPlayerFassed || fasDuration != 2.0))
            {
                Client.UseSpell(fasSpell, Client.Player, _autoStaffSwitch, false);
                return false;
            }

            return true;
        }

        private bool DragonScale()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            bool isDragonScaleChecked = clientTab.dragonScaleCbox.Checked;

            if (isDragonScaleChecked && Client.IsRegistered && !Client.HasEffect(EffectsBar.Armachd))
            {
                if (!RecentlyUsedDragonScale)
                {
                    RecentlyUsedDragonScale = true;

                    //Console.WriteLine("[DragonScale] Using Dragon's Scale");

                    Client.UseItem("Dragon's Scale");

                    Task.Delay(TimeSpan.FromSeconds(1)).ContinueWith(_ => RecentlyUsedDragonScale = false);

                    return false;
                }

            }

            return true;
        }

        private bool Dion()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            bool isDionChecked = clientTab.dionCbox.Checked;

            if (!isDionChecked || Client.HasEffect(EffectsBar.Dion))
            {
                return false;
            }

            string dionWhen = clientTab.dionWhenCombox.Text;
            bool shouldUseSpell = false;

            switch (dionWhen)
            {
                case "Always":
                    shouldUseSpell = true;
                    break;
                case "In Danger":
                    shouldUseSpell = _nearbyValidCreatures.Count > 0;
                    break;
                case "Taking Damage":
                    shouldUseSpell = Client.CurrentHP < Client.MaximumHP;
                    break;
                case "At Percent":
                    shouldUseSpell = Client.CurrentHP * 100U / Client.MaximumHP < Client.ClientTab.dionPctNum.Value;
                    break;
                case "Green Not Nearby":
                    shouldUseSpell = !_nearbyValidCreatures.Any(c => c.SpriteID == 87);
                    break;
            }

            if (shouldUseSpell || (clientTab.aoSithCbox.Checked && _recentlyAoSithed))
            {
                UseDionOrStone();
                return false; // Spell used, exit the method
            }

            // Reset Ao Sith flag if Dion effect is present
            if (Client.HasEffect(EffectsBar.Dion))
            {
                _recentlyAoSithed = false;
            }

            return true; // No spell used, continue execution
        }

        private bool Armachd()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            bool isArmachdChecked = clientTab.armachdCbox.Checked;

            if (isArmachdChecked && !Client.HasEffect(EffectsBar.Armachd))
            {
                Client.UseSpell("armachd", Client.Player, _autoStaffSwitch, false);
                return false;
            }

            return true;
        }

        private bool ArmachdAllies()
        {
            foreach (Ally ally in ReturnAllyList())
            {
                bool isArmChecked = ally.Page.dbArmachdCbox.Checked;

                if (isArmChecked && IsAlly(ally, out Player player, out Client allyClient) && !player.HasArmachd)
                {
                    if (!allyClient.HasEffect(EffectsBar.Armachd))
                    {
                        Client.UseSpell("armachd", player, _autoStaffSwitch, false);
                        return true;
                    }

                }
            }


            return false;
        }

        private bool UseDionOrStone()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            string dionSpell = clientTab.dionCombox.Text;

            if (dionSpell == "Glowing Stone" && !RecentlyUsedGlowingStone)
            {
                RecentlyUsedGlowingStone = true;

                Client.UseItem("Glowing Stone");

                Task.Delay(TimeSpan.FromSeconds(1)).ContinueWith(_ => RecentlyUsedGlowingStone = false);
            }
            else if (dionSpell != "Glowing Stone")
            {
                Client.UseSpell(dionSpell, null, _autoStaffSwitch, false);
            }

            return true;
        }

        private bool DispellPlayerCurse()
        {
            var clientTab = Client.ClientTab;
            Player player = Client.Player;

            if (clientTab == null || player == null)
            {
                return false;
            }

            var isDispelCurseChecked = clientTab.aoCurseCbox.Checked;

            var cursesToDispel = new HashSet<string> { "cradh", "mor cradh", "ard cradh" };

            var curseName = player.GetState<string>(CreatureState.CurseName);
            var curseDuration = player.GetState<double>(CreatureState.CurseDuration);

            if (isDispelCurseChecked && cursesToDispel.Contains(curseName))
            {
                Client.UseSpell("ao " + curseName, player, _autoStaffSwitch, true);

                var stateUpdates = new Dictionary<CreatureState, object>
                {
                    { CreatureState.CurseDuration, 0.0 },
                    { CreatureState.CurseName, string.Empty }
                };
                CreatureStateHelper.UpdateCreatureStates(Client, player.ID, stateUpdates);

                // Console.WriteLine($"[DispellPlayerCurse] Curse '{curseName}' dispelled from {player.Name}. Resetting curse data.");

                return true;
            }

            return false;
        }
        private bool DispellAllyCurse()
        {

            foreach (Ally ally in ReturnAllyList())
            {
                bool isDispelCurseChecked = ally.Page.dispelCurseCbox.Checked;

                if (isDispelCurseChecked && TryGetCursedAlly(ally, out Player player, out Client client))
                {

                    var cursesToDispel = new HashSet<string> { "cradh", "mor cradh", "ard cradh" };
                    var curseName = player.GetState<string>(CreatureState.CurseName);
                    var curseDuration = player.GetState<double>(CreatureState.CurseDuration);

                    if (cursesToDispel.Contains(curseName))
                    {
                        Client.UseSpell("ao " + curseName, player, _autoStaffSwitch, true);

                        var stateUpdates = new Dictionary<CreatureState, object>
                        {
                            { CreatureState.CurseDuration, 0.0 },
                            { CreatureState.CurseName, string.Empty }
                        };
                        CreatureStateHelper.UpdateCreatureStates(client, player.ID, stateUpdates);

                        //Console.WriteLine($"[DispellAllyCurse] Curse data reset on {player.Name}, Hash: {player.GetHashCode()}. Curse: {curseName}, CurseDuration: {curseDuration}, IsCursed: {player.IsCursed}");

                        return false;

                    }
                }
            }
            return true;
        }

        private bool TryGetCursedAlly(Ally ally, out Player player, out Client client)
        {
            if (IsAlly(ally, out player, out client))
            {
                //Console.WriteLine($"[TryGetCursedAlly] Player.ID: {player.ID}, Hash: {player.GetHashCode()}, Player {player.Name} is cursed: {player.IsCursed}");
                return player.IsCursed;
            }
            return false;
        }

        internal bool IsAlly(Ally ally, out Player player, out Client client)
        {
            player = Client.GetNearbyPlayer(ally.Name);
            client = Server.GetClient(ally.Name);

            if (player == null || client == Client)
                return false;

            player = client?.Player ?? player;
            return true;
        }

        private bool Heal()
        {
            if (Client.HasEffect(EffectsBar.FasSpiorad) || Client.ClientTab == null)
            {
                return false;
            }

            int loopPercentThreshold = 20;

            while (loopPercentThreshold <= 100 && !_needFasSpiorad)
            {
                foreach (Player player in Client.GetNearbyPlayers())
                {
                    if (ContainsAlly(player.Name) || player == Client.Player)
                    {
                        Ally ally = ReturnAllyList().FirstOrDefault(a =>
                                            string.Equals(a.Name?.ToLowerInvariant(), player.Name?.ToLowerInvariant(), StringComparison.OrdinalIgnoreCase));
                        AllyPage allyPage = ally?.Page;
                        Client allyClient = Server.GetClient(player.Name);


                        if (allyClient == null) continue;
                        if ((allyPage == null && allyClient != Client) ||
                               (allyClient == Client && !Client.ClientTab.healCbox.Checked) ||
                               (allyClient != Client && !allyPage.dbIocCbox.Checked))
                        {
                            continue;
                        }

                        if (ShouldExcludePlayer(player)) continue;

                        string healSpell = player == allyClient.Player
                            ? allyClient.ClientTab.healCombox.Text
                            : allyPage.dbIocCombox.Text;


                        if (loopPercentThreshold == 20 && player != Client.Player &&
                            (Client.HasSpell("Nuadhiach Le Cheile") ||
                             Client.HasSpell("ard ioc comlha") ||
                             Client.HasSpell("mor ioc comlha")))
                        {
                            // Refresh heal states for all nearby grouped players
                            foreach (var p in Client.GetNearbyGroupedPlayers())
                            {
                                Client allyC = Server.GetClient(p.Name); // Check if the player is a bot-controlled Client
                                int healAtPercent = (int)(p == Client.Player ? Client.ClientTab.healPctNum.Value : 20); // Default to 20% for non-Client

                                RefreshPlayerHealStates(p, allyC, healAtPercent);
                            }

                            // Calculate how many allies are in need of healing
                            int alliesInNeed = Client.GetNearbyGroupedPlayers()
                                                     .Count(p => p != Client.Player && IsAllyInNeed(p));

                            //Console.WriteLine("ALLIES IN NEED: " + alliesInNeed);

                            // Determine if we should cast an AoE heal spell
                            if (alliesInNeed > 2)
                            {
                                healSpell = Client.HasSpell("Nuadhiach Le Cheile")
                                             ? "Nuadhiach Le Cheile"
                                             : Client.HasSpell("ard ioc comlha")
                                                 ? "ard ioc comlha"
                                                 : "mor ioc comhla";

                                Console.WriteLine($"Cast group heal spell: {healSpell}");

                                // Cast the AoE heal spell
                                if (Client.UseSpell(healSpell, null, _autoStaffSwitch, false))
                                {
                                    //Console.WriteLine($"[Debug] Successfully cast AoE heal spell: {healSpell}");
                                }
                            }
                        }


                        if (!Client.GetNearbyPlayers().Any(player => ShouldExcludePlayer(player)) || player == Client.Player || healSpell.Contains("comlha"))
                        {
                            //Console.WriteLine($"[Debug] Evaluating healing for player: {player.Name}");
                            //Console.WriteLine($"[Debug] HealSpell: {healSpell}, PlayerIsSelf: {player == Client.Player}, ContainsComlha: {healSpell.Contains("comlha")}");

                            int healAtPercent = (int)(player == Client.Player
                                ? Client.ClientTab.healPctNum.Value
                                : allyPage.dbIocNumPct.Value);

                            healAtPercent = healAtPercent > loopPercentThreshold ? loopPercentThreshold : healAtPercent;

                            //Console.WriteLine($"[Debug] HealAtPercent: {healAtPercent}, LoopThreshold: {loopPercentThreshold}");

                            uint currentHealthPct = allyClient != null
                                ? allyClient.HealthPct
                                : player.HealthPercent;

                            bool shouldHeal = player.NeedsHeal || currentHealthPct <= healAtPercent;

                            //Console.WriteLine($"[Debug] {player.Name} NeedsHeal: {player.NeedsHeal}, ShouldHeal: {shouldHeal}, CurrentHP: {allyClient?.Stats.CurrentHP}, MaximumHP: {allyClient?.Stats.MaximumHP}");

                            if (shouldHeal)
                            {

                                uint healAmount = (uint)Client.CalculateHealAmount(healSpell);
                                //Console.WriteLine($"[Debug] Calculated Heal Amount: {healAmount} for player: {player.Name}");

                                List<Player> playersHealed = new List<Player>();

                                if (!(healSpell == "Nuadhiach Le Cheile") && !(healSpell == "ard ioc comlha") && !(healSpell == "mor ioc comlha"))
                                {
                                    if (Client.UseSpell(healSpell, player, _autoStaffSwitch, false))
                                    {
                                        //Console.WriteLine($"[Debug] Cast single-target heal spell: {healSpell} on {player.Name}");
                                        playersHealed.Add(player);
                                        Thread.Sleep(200);
                                        RefreshPlayerHealStates(player, allyClient, healAtPercent);
                                    }
                                }
                                else if (Client.UseSpell(healSpell, null, _autoStaffSwitch, false))
                                {
                                    var AoETargets = Client.GetNearbyGroupedPlayers();
                                    playersHealed.AddRange(AoETargets);

                                    Console.WriteLine($"[Debug] Cast AoE heal spell: {healSpell}");

                                    // Refresh each player's state if you have an accurate Client for them
                                    foreach (var p2 in AoETargets)
                                    {
                                        var p2Client = Server.GetClient(p2.Name);
                                        Thread.Sleep(200);
                                        RefreshPlayerHealStates(p2, p2Client, healAtPercent);
                                    }
                                }
                                foreach (Player p in playersHealed)
                                {

                                    if (allyClient?.Player?.Name == player.Name)
                                    {

                                        uint newHealth = Math.Min(allyClient.Stats.CurrentHP + healAmount, allyClient.Stats.MaximumHP);
                                        allyClient.Stats.CurrentHP = newHealth;

                                        //Console.WriteLine($"[Heal] {allyClient.Name} healed for {healAmount} HP. New HP: {allyClient.CurrentHP} / {allyClient.MaximumHP}");

                                        // Update health percentage and needs heal status
                                        p.HealthPercent = (byte)allyClient.HealthPct;
                                        p.NeedsHeal = p.HealthPercent < healAtPercent;

                                        //Console.WriteLine($"[Debug] Updated Player: {p.Name}, New Health Percent: {p.HealthPercent}, NeedsHeal: {p.NeedsHeal}");
                                    }
                                    else
                                    {
                                        // We don't have access to the actual health value, so we'll just update it based on a health percentage
                                        // Calculate the new health percentage based on loopPercentThreshold, ensuring it does not exceed 100%
                                        byte newHealthPercent = (byte)Math.Min(p.HealthPercent + 20, 100);

                                        // Update health percentage and needs heal status
                                        p.HealthPercent = newHealthPercent;
                                        p.NeedsHeal = p.HealthPercent <= healAtPercent;

                                        //Console.WriteLine($"[Debug] Updated Nearby Player: {p.Name}, New Health Percent: {p.HealthPercent}, NeedsHeal: {p.NeedsHeal}");
                                    }

                                }
                            }
                        }
                    }
                }

                loopPercentThreshold += 20;
            }
            return true;
        }

        private void RefreshPlayerHealStates(Player player, Client allyClient, int healAtPercent)
        {
            // If the player is also a bot-controlled Client
            if (allyClient != null)
            {
                // The Client.HealthPct is generally more accurate because the bot is actually logged in as that character
                uint clientPct = allyClient.HealthPct;
                byte playerPct = player.HealthPercent; // packet-based healthbar

                // Check for a mismatch
                if (clientPct != playerPct)
                {
                    Console.WriteLine(
                    //$"[Debug] Discrepancy for {player.Name}: " +
                    //$"Client side = {clientPct}%, Player object = {playerPct}%"
                    );
                    // Take some action? — override the Player object's HP with the client’s more accurate HP?
                    // Because the client is more up-to-date, we’ll trust the client’s data?
                    player.HealthPercent = (byte)clientPct;
                }

                // Recompute whether they still need a heal based on the new player.HealthPercent
                player.NeedsHeal = player.HealthPercent < healAtPercent;
            }
            else
            {
                // Fallback for non-bot players:
                // We only have the overhead-bar / packet-based HP to go by.
                // So just rely on player.HealthPercent as is.
                player.NeedsHeal = player.HealthPercent < healAtPercent;
            }

            //Console.WriteLine($"[Debug] Refreshed {player.Name} -> HealthPercent: {player.HealthPercent}, NeedsHeal: {player.NeedsHeal}");
        }


        private bool IsAllyInNeed(Player player)
        {
            return player.HealthPercent < 20 || player.NeedsHeal;
        }

        internal bool ShouldExcludePlayer(Player player)
        {
            // Checks if playerToCheck is not in friend list, is not the reference player,
            // and is either at the same location as reference player or is hidden
            return !Client.ClientTab.friendList.Items.OfType<string>().Contains(player.Name, StringComparer.CurrentCultureIgnoreCase) && player != Client.Player && (Equals(player.Location, Client.Player.Location) || player.IsHidden);
        }

        private bool BubbleBlock()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            // UI Settings
            bool isBubbleBlockChecked = clientTab.bubbleBlockCbox.Checked;
            bool isSpamBubbleChecked = clientTab.spamBubbleCbox.Checked;
            bool isFollowChecked = clientTab.followCbox.Checked;
            string walkMap = clientTab.walkMapCombox.Text;

            // Spell availability
            bool hasBubbleBlock = Client.HasSpell("Bubble Block");
            bool hasBubbleShield = Client.HasSpell("Bubble Shield");

            // Cooldown checks
            bool canCastBubbleBlock = hasBubbleBlock && Client.CanUseSpell(Client.Spellbook["Bubble Block"], null);
            bool canCastBubbleShield = hasBubbleShield && Client.CanUseSpell(Client.Spellbook["Bubble Shield"], null);

            // Movement check (assumes _lastBubbleLocation is maintained elsewhere)
            bool hasMoved = !Location.Equals(_lastBubbleLocation, Client.ServerLocation);

            // --- Mode 1: Spam Mode ---
            if (isSpamBubbleChecked)
            {
                bool castedSomething = false;
                // Spam mode ignores movement; try to cast each available spell.
                if (canCastBubbleBlock)
                {
                    castedSomething |= Client.UseSpell("Bubble Block", null, _autoStaffSwitch, true);
                }
                if (canCastBubbleShield)
                {
                    castedSomething |= Client.UseSpell("Bubble Shield", null, _autoStaffSwitch, true);
                }
                return !castedSomething;
            }
            // --- Mode 2: Normal Mode ---
            else if (isBubbleBlockChecked && Client.OkToBubble)
            {
                // Only proceed if we're in Select Location, WayPoints, or Follow mode with confirmation.
                if (walkMap == "WayPoints" || (isFollowChecked && Client.ConfirmBubble))
                {
                    // Fresh Cast: if we've moved or no bubble is active, choose based on availability,
                    // preferring Bubble Shield for greater protection.
                    if (hasMoved || string.IsNullOrEmpty(_bubbleType))
                    {
                        if (canCastBubbleShield)
                        {
                            if (Client.UseSpell("Bubble Shield", null, _autoStaffSwitch, true))
                            {
                                _lastBubbleLocation = Client.ServerLocation;
                                _bubbleType = "SHIELD";
                                return false;
                            }
                        }
                        else if (canCastBubbleBlock)
                        {
                            if (Client.UseSpell("Bubble Block", null, _autoStaffSwitch, true))
                            {
                                _lastBubbleLocation = Client.ServerLocation;
                                _bubbleType = "BLOCK";
                                return false;
                            }
                        }
                    }
                    else
                    {
                        // Refresh/Rotate: When standing still and a bubble is active,
                        // try to alternate the bubble spell.
                        string currentSpell = _bubbleType == "BLOCK" ? "Bubble Block" : "Bubble Shield";
                        string alternateSpell = _bubbleType == "BLOCK" ? "Bubble Shield" : "Bubble Block";
                        bool canCastCurrent = (_bubbleType == "BLOCK") ? canCastBubbleBlock : canCastBubbleShield;
                        bool hasAlternate = (_bubbleType == "BLOCK") ? hasBubbleShield : hasBubbleBlock;
                        bool canCastAlternate = (_bubbleType == "BLOCK") ? canCastBubbleShield : canCastBubbleBlock;

                        // If the alternate spell is available, cast it.
                        if (hasAlternate && canCastAlternate)
                        {
                            if (Client.UseSpell(alternateSpell, null, _autoStaffSwitch, false))
                            {
                                _lastBubbleLocation = Client.ServerLocation;
                                _bubbleType = _bubbleType == "BLOCK" ? "SHIELD" : "BLOCK";
                                return false;
                            }
                        }
                        // Otherwise, refresh the current bubble.
                        else if (canCastCurrent && Client.UseSpell(currentSpell, null, _autoStaffSwitch, false))
                        {
                            _lastBubbleLocation = Client.ServerLocation;
                            return false;
                        }
                    }
                }
            }
            return true;
        }






        private bool Hide()
        {
            if (CastHide())
            {
                _dontBash = true;
                return false;
            }

            return true;
        }
        private bool CastHide()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }

            bool isHideChecked = clientTab.hideCbox.Checked;
            bool canUseSpells = Client.Map.CanUseSpells;

            if (isHideChecked && canUseSpells)
            {
                string spellName = "";
                if (Client.HasSpell("Hide"))
                {
                    spellName = "Hide";
                }
                else if (Client.HasSpell("White Bat Stance"))
                {
                    spellName = "White Bat Stance";
                }
                if (!Client.HasEffect(EffectsBar.Hide) || DateTime.UtcNow.Subtract(_lastHidden).TotalSeconds > 50.0)
                {
                    Client.UseSkill("Assail");
                    Client.UseSpell(spellName, null, true, true);
                    _lastHidden = DateTime.UtcNow;
                }
                return true;
            }
            return false;
        }

        private bool CastOffensiveSpells()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return false;
            }
            _nearbyValidCreatures = Client.GetNearbyValidCreatures(11);

            if (_nearbyValidCreatures.Count > 0)
            {
                _nearbyValidCreatures = _nearbyValidCreatures.OrderBy(c => RandomUtils.Random()).ToList();
            }

            // If a stranger is nearby, limit the nearby creatures to only those that have existed for 2 seconds
            // This is to prevent the bot from attacking a creature that has just spawned and appear more huamn-like
            if (IsStrangerNearby())
            {
                if (_nearbyValidCreatures.Count > 0)
                {
                    _nearbyValidCreatures.RemoveAll(c => DateTime.UtcNow.Subtract(c.Creation).TotalSeconds < 2.0);
                }
                RemoveDuplicateCreatures();
            }

            if (AllMonsters != null)
            {
                if (HandleAllMonstersSpells())
                {
                    return true;
                }
            }
            else
            {
                if (HandleEnemyListSpells())
                {
                    return true;
                }
            }

            if (AllMonsters != null)
            {
                if (CastAttackSpells(AllMonsters, _nearbyValidCreatures))
                {
                    return true;
                }
            }
            else
            {
                if (CastAttackSpellsForEnemies())
                {
                    return true;
                }
            }

            _dontBash = false;
            return false;
        }

        private void RemoveDuplicateCreatures()
        {
            var duplicates = _nearbyValidCreatures
                .GroupBy(c => c.Location)
                .SelectMany(g => g.Skip(1))
                .ToList();

            foreach (var duplicate in duplicates)
            {
                _nearbyValidCreatures.Remove(duplicate);
            }
        }

        private bool HandleAllMonstersSpells()
        {
            if (AllMonsters.ignoreCbox.Checked)
            {
                _nearbyValidCreatures.RemoveAll(creature => AllMonsters.ignoreLbox.Items.Contains(creature.SpriteID.ToString()));
            }

            List<Creature> priorityCreatures = new List<Creature>();
            List<Creature> nonPriorityCreatures = new List<Creature>();

            if (AllMonsters.priorityCbox.Checked)
            {
                foreach (var creature in _nearbyValidCreatures)
                {
                    if (AllMonsters.priorityLbox.Items.Contains(creature.SpriteID.ToString()))
                    {
                        priorityCreatures.Add(creature);
                    }
                    else if (!AllMonsters.priorityOnlyCbox.Checked)
                    {
                        nonPriorityCreatures.Add(creature);
                    }
                }
            }
            else
            {
                nonPriorityCreatures = new List<Creature>(_nearbyValidCreatures);
            }

            if (AllMonsters.spellAllRbtn.Checked)
            {
                creature = null;
                if (ExecuteEngagementStrategy(AllMonsters, priorityCreatures, nonPriorityCreatures))
                {
                    return true;
                }
            }
            else
            {
                if (SpellCreaturesOneAtATime(AllMonsters, priorityCreatures, nonPriorityCreatures))
                {
                    return true;
                }
            }

            return false;
        }

        private bool HandleEnemyListSpells()
        {
            foreach (Enemy enemy in ReturnEnemyList())
            {
                var creatureList = Client.GetAllNearbyMonsters(11, new ushort[] { enemy.SpriteID })
                    .Where(c => c.SpriteID.ToString() == enemy.SpriteID.ToString())
                    .ToList();

                if (creatureList.Count > 0)
                {
                    if (enemy.EnemyPage.spellAllRbtn.Checked)
                    {
                        creature = null;
                        if (DecideAndExecuteEngagementStrategy(enemy.EnemyPage, creatureList))
                        {
                            _dontBash = true;
                            return true;
                        }
                    }
                    else if (SpellOneAtATime(enemy.EnemyPage, creatureList))
                    {
                        _dontBash = true;
                        return true;
                    }
                }
            }

            return false;
        }

        private bool ExecuteEngagementStrategy(dynamic config, List<Creature> priority, List<Creature> nonPriority)
        {
            if (priority.Count > 0 && DecideAndExecuteEngagementStrategy(config, priority))
            {
                _dontBash = true;
                return true;
            }
            if (nonPriority.Count > 0 && DecideAndExecuteEngagementStrategy(config, nonPriority))
            {
                _dontBash = true;
                return true;
            }
            return false;
        }

        private bool SpellCreaturesOneAtATime(dynamic config, List<Creature> priority, List<Creature> nonPriority)
        {
            if (priority.Count > 0 && SpellOneAtATime(config, priority))
            {
                _dontBash = true;
                return true;
            }
            if (!priority.Contains(creature) && nonPriority.Count > 0 && SpellOneAtATime(config, nonPriority))
            {
                _dontBash = true;
                return true;
            }
            return false;
        }

        private bool CastAttackSpells(dynamic config, List<Creature> creatures)
        {
            if (config.priorityCbox.Checked)
            {
                List<Creature> priorityCreatures = new List<Creature>();
                List<Creature> nonPriorityCreatures = new List<Creature>();

                foreach (var creature in creatures)
                {
                    if (config.priorityLbox.Items.Contains(creature.SpriteID.ToString()))
                    {
                        priorityCreatures.Add(creature);
                    }
                    else if (!config.priorityOnlyCbox.Checked)
                    {
                        nonPriorityCreatures.Add(creature);
                    }
                }

                if (CastAttackSpell(config, priorityCreatures) || CastAttackSpell(config, nonPriorityCreatures))
                {
                    return true;
                }
            }
            else if (CastAttackSpell(config, creatures))
            {
                return true;
            }

            return false;
        }

        private bool CastAttackSpellsForEnemies()
        {
            foreach (Enemy enemy in ReturnEnemyList())
            {
                var creaturesToAttack = Client.GetAllNearbyMonsters(11, new ushort[] { enemy.SpriteID })
                    .Where(c => c.SpriteID.ToString() == enemy.SpriteID.ToString())
                    .ToList();

                if (CastAttackSpell(enemy.EnemyPage, creaturesToAttack))
                {
                    return true;
                }
            }

            return false;
        }


        private bool CastAttackSpell(EnemyPage enemyPage, List<Creature> creatureList)
        {
            if (!enemyPage.targetCbox.Checked || creatureList.Count == 0)
            {
                return false;
            }

            // Handle single-target spells
            if (enemyPage.spellOneRbtn.Checked)
            {
                if (!creatureList.Contains(creature))
                {
                    creature = creatureList.OrderBy(c => c.Location.DistanceFrom(Client.ClientLocation)).FirstOrDefault();
                }
                if (creature == null)
                {
                    return false;
                }
                creatureList = new List<Creature> { creature };
            }

            // Handle PND spells if applicable
            if (AllMonsters != null && AllMonsters.mpndDioned.Checked)
            {
                bool proceedWithPND = true;

                if (!enemyPage.attackCboxOne.Checked && !enemyPage.attackCboxTwo.Checked)
                {
                    if (!_nearbyValidCreatures.Any(c => c.IsDioned))
                    {
                        proceedWithPND = false;
                    }
                }
                else if (!_nearbyValidCreatures.All(c => c.CanPND))
                {
                    proceedWithPND = false;
                }

                if (proceedWithPND)
                {
                    Creature creatureTarget = _nearbyValidCreatures
                        .Where(c => c.CanPND)
                        .OrderBy(c => c.Location.DistanceFrom(Client.ClientLocation))
                        .FirstOrDefault();

                    if (creatureTarget != null)
                    {
                        return Client.TryUseAnySpell(
                            new[] { "ard pian na dion", "mor pian na dion", "pian na dion" },
                            creatureTarget,
                            _autoStaffSwitch,
                            false);
                    }
                }
            }

            // Handle attack spells when not silenced
            if (!_isSilenced)
            {
                // Attack Combo Box Two
                if (enemyPage.attackCboxTwo.Checked)
                {
                    Creature target = SelectAttackTarget(enemyPage, creatureList, enemyPage.attackComboxTwo.Text);
                    if (target != null)
                    {
                        string spellName = enemyPage.attackComboxTwo.Text.Trim();

                        switch (spellName)
                        {
                            case "Supernova Shot":
                                return Client.UseSpell("Supernova Shot", target, _autoStaffSwitch, false);

                            case "Shock Arrow":
                                return Client.UseSpell("Shock Arrow", target, _autoStaffSwitch, false) &&
                                       Client.UseSpell("Shock Arrow", target, _autoStaffSwitch, false);

                            case "Volley":
                                return Client.UseSpell("Volley", target, _autoStaffSwitch, true);

                            case "MSPG":
                                if (enemyPage.mspgPct.Checked && Client.ManaPct < 80)
                                {
                                    _manaLessThanEightyPct = true;
                                    Client.UseSpell("fas spiorad", null, _autoStaffSwitch, false);
                                    return true;
                                }
                                return Client.UseSpell("mor strioch pian gar", Client.Player, _autoStaffSwitch, true);

                            case "Unholy Explosion":
                                return Client.UseSpell("Unholy Explosion", target, _autoStaffSwitch, false);

                            case "Cursed Tune":
                                return TryCastAnyRank("Cursed Tune", target, _autoStaffSwitch, false);

                            case "M/DSG":
                                return Client.UseSpell("mor deo searg gar", Client.Player, _autoStaffSwitch, false) ||
                                       Client.UseSpell("deo searg gar", Client.Player, _autoStaffSwitch, false);
                        }
                    }
                }

                // Attack Combo Box One
                if (enemyPage.attackCboxOne.Checked)
                {
                    Creature target = SelectAttackTarget(enemyPage, creatureList, enemyPage.attackComboxOne.Text);
                    if (target != null)
                    {
                        string spellName = enemyPage.attackComboxOne.Text.Trim();

                        switch (spellName)
                        {
                            case "lamh":
                                return Client.TryUseAnySpell(
                                    new[] { "beag athar lamh", "beag srad lamh", "athar lamh", "srad lamh", "Howl" },
                                    null,
                                    _autoStaffSwitch,
                                    false);

                            case "A/DS":
                                return Client.TryUseAnySpell(
                                    new[] { "ard deo searg", "deo searg" },
                                    target,
                                    _autoStaffSwitch,
                                    false);

                            case "A/M/PND":
                                return Client.TryUseAnySpell(
                                    new[] { "ard pian na dion", "mor pian na dion", "pian na dion" },
                                    target,
                                    _autoStaffSwitch,
                                    false);

                            case "Frost Arrow":
                                return TryCastAnyRank("Frost Arrow", target, _autoStaffSwitch, false);

                            default:
                                return Client.UseSpell(spellName, target, _autoStaffSwitch, false) ||
                                       TryCastAnyRank(spellName, target, _autoStaffSwitch, false);
                        }
                    }
                }
            }

            // Handle spells when silenced
            if (_isSilenced)
            {
                if (enemyPage.mpndSilenced.Checked)
                {
                    Creature mpndTarget = SelectAttackTarget(enemyPage, creatureList, "A/M/PND");
                    return Client.TryUseAnySpell(
                        new[] { "ard pian na dion", "mor pian na dion", "pian na dion" },
                        mpndTarget,
                        _autoStaffSwitch,
                        false);
                }

                if (enemyPage.mspgSilenced.Checked && SelectAttackTarget(enemyPage, creatureList, "MSPG") != null)
                {
                    if (enemyPage.mspgPct.Checked && Client.ManaPct < 80)
                    {
                        _manaLessThanEightyPct = true;
                        return Client.UseSpell("fas spiorad", null, _autoStaffSwitch, false);
                    }
                    Client.UseSpell("mor strioch pian gar", Client.Player, _autoStaffSwitch, true);
                    return true;
                }
            }

            return false;
        }


        private bool TryCastAnyRank(string spellNAme, Creature creatureTarget = null, bool autoStaffSwitch = true, bool keepSpellAfterUse = true)
        {
            for (int i = 20; i > 0; i--)
            {
                if (Client.UseSpell(spellNAme + " " + i.ToString(), creatureTarget, autoStaffSwitch, keepSpellAfterUse))
                {
                    return true;
                }
            }
            return false;
        }


        private bool SpellOneAtATime(EnemyPage enemyPage, List<Creature> creatureList)
        {
            foreach (var creature in creatureList.OrderBy(c => c.Location.DistanceFrom(Client.ClientLocation)))
            {

                if (!creatureList.Contains(this.creature))
                {
                    this.creature = creatureList.OrderBy(c => c.Location.DistanceFrom(Client.ClientLocation)).FirstOrDefault<Creature>();
                }
                if (creature == null)
                {
                    continue;
                }
                this.creature = creature;

                if (enemyPage.pramhFirstRbtn.Checked && enemyPage.spellsControlCbox.Checked && !creature.IsAsleep)
                {
                    Client.UseSpell(enemyPage.spellsControlCombox.Text, creature, _autoStaffSwitch, false);
                    return true;
                }
                if (enemyPage.spellFirstRbtn.Checked && ((enemyPage.spellsFasCbox.Checked && !creature.IsFassed) || (enemyPage.spellsCurseCbox.Checked && !creature.IsCursed)))
                {
                    if (CastFasOrCurse(enemyPage, creature))
                    {
                        return true;
                    }
                }
                else if (enemyPage.pramhFirstRbtn.Checked && (!enemyPage.spellsControlCbox.Checked || creature.IsAsleep) && ((enemyPage.spellsFasCbox.Checked && !creature.IsFassed) || (enemyPage.spellsCurseCbox.Checked && !creature.IsCursed)))
                {
                    if (CastFasOrCurse(enemyPage, creature))
                    {
                        return true;
                    }
                }
                else if (enemyPage.spellFirstRbtn.Checked && (!enemyPage.spellsFasCbox.Checked || creature.IsFassed) && (!enemyPage.spellsCurseCbox.Checked || creature.IsCursed) && enemyPage.spellsControlCbox.Checked && !creature.IsAsleep)
                {
                    Client.UseSpell(enemyPage.spellsControlCombox.Text, creature, _autoStaffSwitch, false);
                    return true;
                }
            }

            // If the method reaches this point, it means no spells were cast successfully on any of the creatures
            return false;
        }

        private bool CastFasOrCurse(EnemyPage enemyPage, Creature creature)
        {
            if (enemyPage.fasFirstRbtn.Checked && enemyPage.spellsFasCbox.Checked && !creature.IsFassed)
            {
                _dontBash = true;
                Client.UseSpell(enemyPage.spellsFasCombox.Text, creature, _autoStaffSwitch, false);
                return true;
            }
            if (enemyPage.curseFirstRbtn.Checked && enemyPage.spellsCurseCbox.Checked && !creature.IsCursed)
            {
                _dontBash = true;
                Client.UseSpell(enemyPage.spellsCurseCombox.Text, creature, _autoStaffSwitch, false);
                return true;
            }
            if ((!enemyPage.fasFirstRbtn.Checked || !enemyPage.spellsFasCbox.Checked || creature.IsFassed) && enemyPage.spellsCurseCbox.Checked && !creature.IsCursed)
            {
                _dontBash = true;
                Client.UseSpell(enemyPage.spellsCurseCombox.Text, creature, _autoStaffSwitch, false);
                return true;
            }
            if ((!enemyPage.curseFirstRbtn.Checked || !enemyPage.spellsCurseCbox.Checked || creature.IsCursed) && enemyPage.spellsFasCbox.Checked && !creature.IsFassed)
            {
                _dontBash = true;
                Client.UseSpell(enemyPage.spellsFasCombox.Text, creature, _autoStaffSwitch, false);
                return true;
            }
            return false;
        }


        private bool DecideAndExecuteEngagementStrategy(EnemyPage enemyPage, List<Creature> creatureList)
        {
            if (enemyPage.pramhFirstRbtn.Checked)
            {
                if (enemyPage.spellsControlCbox.Checked)
                    if (ExecutePramhStrategy(enemyPage, creatureList))
                    {
                        return true;
                    }
                if (enemyPage.spellsFasCbox.Checked || enemyPage.spellsCurseCbox.Checked)
                    if (ExecuteDebuffStrategy(enemyPage, creatureList))
                    {
                        return true;
                    }
            }
            else if (enemyPage.spellFirstRbtn.Checked)
            {
                if (enemyPage.spellsFasCbox.Checked || enemyPage.spellsCurseCbox.Checked)
                    if (ExecuteDebuffStrategy(enemyPage, creatureList))
                    {
                        return true;
                    }
                if (enemyPage.spellsControlCbox.Checked)
                    if (ExecutePramhStrategy(enemyPage, creatureList))
                    {
                        return true;
                    }
            }
            return false;
        }

        private bool ExecuteDebuffStrategy(EnemyPage enemyPage, List<Creature> creatureList)
        {
            List<Creature> eligibleCreatures = creatureList.Where(c => !c.IsFassed || !c.IsCursed).ToList();

            if (eligibleCreatures.Any() && (enemyPage.spellsFasCbox.Checked || enemyPage.spellsCurseCbox.Checked))
            {
                if (enemyPage.fasFirstRbtn.Checked)
                {
                    return ExecuteFasFirstStrategy(enemyPage, eligibleCreatures);
                }
                else if (enemyPage.curseFirstRbtn.Checked)
                {
                    return ExecuteCurseFirstStrategy(enemyPage, eligibleCreatures);
                }
            }

            return false;
        }

        private bool ExecuteFasFirstStrategy(EnemyPage enemyPage, List<Creature> eligibleCreatures)
        {
            // Try casting Fas first, then Curse if applicable
            if (enemyPage.spellsFasCbox.Checked && CastFasIfApplicable(enemyPage, eligibleCreatures))
            {
                _dontBash = true;
                return true;
            }

            if (enemyPage.spellsCurseCbox.Checked && CastCurseIfApplicable(enemyPage, eligibleCreatures))
            {
                _dontBash = true;
                return true;
            }

            return false;
        }

        private bool ExecuteCurseFirstStrategy(EnemyPage enemyPage, List<Creature> eligibleCreatures)
        {
            // Try casting Curse first, then Fas if applicable
            if (enemyPage.spellsCurseCbox.Checked && CastCurseIfApplicable(enemyPage, eligibleCreatures))
            {
                _dontBash = true;
                return true;
            }

            if (enemyPage.spellsFasCbox.Checked && CastFasIfApplicable(enemyPage, eligibleCreatures))
            {
                _dontBash = true;
                return true;
            }

            return false;
        }

        private bool CastCurseIfApplicable(EnemyPage enemyPage, List<Creature> creatures)
        {
            lock (_lock)
            {
                //Console.WriteLine($"[CastCurseIfApplicable] Total creatures: {creatures.Count}");

                // Filter creatures that are not cursed
                var eligibleCreatures = creatures.Where(c => !c.IsCursed);

                //Console.WriteLine($"[CastCurseIfApplicable] Eligible creatures (not cursed): {eligibleCreatures.Count()}");

                // Select the nearest eligible creature if specified, otherwise select any eligible creature
                //Creature targetCreature = enemyPage.NearestFirstCbx.Checked
                //    ? eligibleCreatures.OrderBy(creature => creature.Location.DistanceFrom(Client.ServerLocation)).FirstOrDefault()
                //    : eligibleCreatures.FirstOrDefault();

                Creature targetCreature;

                if (enemyPage.NearestFirstCbx.Checked && !enemyPage.FarthestFirstCbx.Checked)
                {
                    // Select the nearest eligible creature
                    targetCreature = eligibleCreatures
                        .OrderBy(creature => creature.Location.DistanceFrom(Client.ServerLocation))
                        .FirstOrDefault();
                }
                else if (enemyPage.FarthestFirstCbx.Checked && !enemyPage.NearestFirstCbx.Checked)
                {
                    // Select the farthest eligible creature
                    targetCreature = eligibleCreatures
                        .OrderByDescending(creature => creature.Location.DistanceFrom(Client.ServerLocation))
                        .FirstOrDefault();
                }
                else
                {
                    // If neither checkbox is checked or both are checked, select any eligible creature
                    targetCreature = eligibleCreatures.FirstOrDefault();
                }

                // If a target is found and casting curses is enabled, cast the curse spell
                if (targetCreature != null && enemyPage.spellsCurseCbox.Checked)
                {
                    //Console.WriteLine($"[CastCurseIfApplicable] Targeting creature ID: {targetCreature.ID}, Name: {targetCreature.Name}, LastCursed: {targetCreature.LastCursed}, IsCursed: {targetCreature.IsCursed}");
                    Client.UseSpell(enemyPage.spellsCurseCombox.Text, targetCreature, _autoStaffSwitch, false);
                    _dontBash = true; // Indicate that an action was taken
                    return true;
                }

                return false; // No action was taken

            }
        }

        private bool CastFasIfApplicable(EnemyPage enemyPage, List<Creature> creatures)
        {
            lock (_lock)
            {
                //Console.WriteLine($"[CastFasIfApplicable] Total creatures: {creatures.Count}");

                // Filter creatures that are not fassed
                var eligibleCreatures = creatures.Where(c => !c.IsFassed);

                //Console.WriteLine($"[CastFasIfApplicable] Eligible creatures (not fassed): {eligibleCreatures.Count()}");

                // Select the nearest eligible creature if specified, otherwise select any eligible creature
                //Creature targetCreature = enemyPage.NearestFirstCbx.Checked
                //    ? eligibleCreatures.OrderBy(creature => creature.Location.DistanceFrom(Client.ServerLocation)).FirstOrDefault()
                //    : eligibleCreatures.FirstOrDefault();

                Creature targetCreature;

                if (enemyPage.NearestFirstCbx.Checked && !enemyPage.FarthestFirstCbx.Checked)
                {
                    // Select the nearest eligible creature
                    targetCreature = eligibleCreatures
                        .OrderBy(creature => creature.Location.DistanceFrom(Client.ServerLocation))
                        .FirstOrDefault();
                }
                else if (enemyPage.FarthestFirstCbx.Checked && !enemyPage.NearestFirstCbx.Checked)
                {
                    // Select the farthest eligible creature
                    targetCreature = eligibleCreatures
                        .OrderByDescending(creature => creature.Location.DistanceFrom(Client.ServerLocation))
                        .FirstOrDefault();
                }
                else
                {
                    // If neither checkbox is checked or both are checked, select any eligible creature
                    targetCreature = eligibleCreatures.FirstOrDefault();
                }
                // If a target is found and casting the 'fas' spell is enabled, cast the spell
                if (targetCreature != null && enemyPage.spellsFasCbox.Checked)
                {
                    //Console.WriteLine($"[CastFasIfApplicable] Targeting creature ID: {targetCreature.ID}, Name: {targetCreature.Name}, LastFassed: {targetCreature.LastFassed}, IsFassed: {targetCreature.IsFassed}");
                    Client.UseSpell(enemyPage.spellsFasCombox.Text, targetCreature, _autoStaffSwitch, false);
                    _dontBash = true; // Indicate that an action was taken
                    return true;
                }

                return false; // No action was taken
            }

        }

        private Creature SelectAttackTarget(EnemyPage enemyPage, List<Creature> creatureList, string spellName = "")
        {
            List<Creature> attackList;

            bool flag = enemyPage.attackCboxTwo.Checked && enemyPage.targetCbox.Checked &&
                        (enemyPage.attackComboxTwo.Text == "MSPG" || enemyPage.attackComboxTwo.Text == "M/DSG");

            bool checkCursed = enemyPage.targetCursedCbox.Checked;
            bool checkFassed = enemyPage.targetFassedCbox.Checked;

            // Build the attack list based on cursed and fassed filters
            attackList = BuildAttackList(creatureList, checkCursed, checkFassed, flag);

            if (attackList.Count == 0)
            {
                return null;
            }

            // Apply additional filters based on spellName
            attackList = FilterAttackListBySpell(attackList, spellName, enemyPage);

            if (attackList.Count == 0)
            {
                return null;
            }

            // If the current creature is still in the attack list, return it
            if (creature != null && attackList.Contains(creature))
            {
                return creature;
            }

            // Decide on the target selection method
            if (ShouldSelectClusterTarget(enemyPage, flag))
            {
                return SelectClusterTarget(enemyPage, attackList);
            }
            else
            {
                // Select the nearest creature from the attack list
                return attackList.OrderBy(c => c.Location.DistanceFrom(Client.ServerLocation)).FirstOrDefault();
            }
        }

        private List<Creature> BuildAttackList(List<Creature> creatureList, bool checkCursed, bool checkFassed, bool flag)
        {
            List<Creature> attackList = new List<Creature>();

            if (!checkCursed && !checkFassed)
            {
                attackList = new List<Creature>(creatureList);
            }
            else
            {
                foreach (Creature creature in creatureList)
                {
                    bool addCreature = (!checkCursed || creature.IsCursed) && (!checkFassed || creature.IsFassed);

                    if (addCreature)
                    {
                        attackList.Add(creature);
                    }
                    else if (flag && creature.Location.DistanceFrom(Client.ServerLocation) <= GetFurthestClient())
                    {
                        attackList.Clear();
                        break;
                    }
                }
            }

            return attackList;
        }

        private List<Creature> FilterAttackListBySpell(List<Creature> attackList, string spellName, EnemyPage enemyPage)
        {
            if (spellName == "Frost Arrow")
            {
                attackList = attackList.Where(c => !c.IsFrozen).ToList();
            }
            else if (spellName == "Cursed Tune")
            {
                attackList = attackList.Where(c => !c.IsPoisoned).ToList();
            }
            else if (spellName != "lamh" && spellName != "Shock Arrow" && spellName != "Volley")
            {
                if (spellName != "A/M/PND")
                {
                    attackList = attackList.Where(c => !c.IsDioned).ToList();
                }

                if (enemyPage.expectedHitsNum.Value > 0m)
                {
                    attackList = attackList.Where(creature => CalculateHitCounter(creature, enemyPage)).ToList();
                }
            }

            return attackList;
        }

        private bool ShouldSelectClusterTarget(EnemyPage enemyPage, bool flag)
        {
            return enemyPage.targetCombox.Text.Contains("Cluster") && !flag && (!_isSilenced || !enemyPage.mpndSilenced.Checked);
        }

        private Creature SelectClusterTarget(EnemyPage enemyPage, List<Creature> attackList)
        {
            int maxDistance = GetMaxClusterDistance(enemyPage.targetCombox.Text);

            Dictionary<Creature, int> clusterTargets = new Dictionary<Creature, int>();

            List<Creature> nearbyCreatures = Client.GetAllNearbyMonsters(12)
                                                   .Concat(_playersExistingOver250ms)
                                                   .ToList();

            List<Creature> validCreatures = Client.GetNearbyValidCreatures(12);

            List<Creature> borosCreatures = validCreatures
                .Where(c => CONSTANTS.GREEN_BOROS.Contains(c.SpriteID) || CONSTANTS.RED_BOROS.Contains(c.SpriteID))
                .ToList();

            if (!nearbyCreatures.Contains(Client.Player))
            {
                nearbyCreatures.Add(Client.Player);
            }

            foreach (Creature c in nearbyCreatures)
            {
                int count = attackList.Count(creature => IsWithinClusterRange(c.Location, creature.Location, maxDistance));

                if (!IsCreatureNearBoros(c, borosCreatures, maxDistance))
                {
                    clusterTargets[c] = count;
                }
            }

            // Remove unsuitable targets
            var unsuitableCreatures = clusterTargets.Keys
                .Where(c => (c.Type == CreatureType.Aisling ||
                            (c.Type == CreatureType.WalkThrough && !validCreatures.Contains(c)) ||
                            c.IsDioned) && clusterTargets[c] <= 1)
                .ToList();

            foreach (var c in unsuitableCreatures)
            {
                clusterTargets.Remove(c);
            }

            if (clusterTargets.Count == 0)
            {
                return null;
            }

            // Select the best target
            return clusterTargets
                .OrderByDescending(kvp => kvp.Value)
                .ThenBy(kvp => kvp.Key.Creation)
                .First()
                .Key;
        }

        private int GetMaxClusterDistance(string clusterText)
        {
            return clusterText switch
            {
                "Cluster 29" => 3,
                "Cluster 13" => 2,
                _ => 1,
            };
        }

        private bool IsWithinClusterRange(Location loc1, Location loc2, int maxDistance)
        {
            return loc1.DistanceFrom(loc2) <= maxDistance ||
                   (maxDistance > 1 && IsDiagonallyAdjacent(loc1.Point, loc2.Point, maxDistance));
        }

        private bool IsCreatureNearBoros(Creature c, List<Creature> borosCreatures, int maxDistance)
        {
            foreach (var borosCreature in borosCreatures)
            {
                if (c == borosCreature)
                {
                    return true;
                }

                foreach (Location adjLoc in Client.GetAdjacentPoints(borosCreature))
                {
                    if (IsWithinClusterRange(c.Location, adjLoc, maxDistance))
                    {
                        return true;
                    }
                }
            }

            return false;
        }


        private bool IsDiagonallyAdjacent(Point location, Point otherLocation, int maxDistance)
        {
            int adjustedDistance = maxDistance - 1;
            int deltaX = Math.Abs(location.X - otherLocation.X);
            int deltaY = Math.Abs(location.Y - otherLocation.Y);

            return deltaX == adjustedDistance && deltaY == adjustedDistance;
        }

        internal bool CalculateHitCounter(Creature creature, EnemyPage enemyPage)
        {
            if (creature.HealthPercent == 0
                && creature.AnimationHistory.Count != 0
                && creature.LastAnimation != (byte)SpellAnimation.Miss
                && DateTime.UtcNow.Subtract(creature.LastAnimationTime).TotalSeconds <= 1.5)
            {
                return creature._hitCounter < enemyPage.expectedHitsNum.Value;
            }
            if (creature.HealthPercent != 0
                && creature._hitCounter > enemyPage.expectedHitsNum.Value)
            {
                creature._hitCounter = (int)enemyPage.expectedHitsNum.Value - 1;
            }
            return true;
        }

        private int GetFurthestClient()
        {
            int result;
            try
            {
                List<Client> nearbyClients = Client.GetNearbyPlayers()
                    .Select(player => Server.GetClient(player?.Name))
                    .Where(client => client != null)
                    .ToList();

                if (nearbyClients.Any())
                {
                    Client furthestClient = nearbyClients
                        .OrderByDescending(client => CalculateDistanceFromBaseClient(client))
                        .First();

                    result = 11 - furthestClient.ServerLocation.DistanceFrom(Client.ServerLocation);
                }
            }
            catch (Exception ex)
            {
                // Handle exception if needed
                Console.WriteLine($"Error in GetFurthestClient: {ex.Message}");
            }

            return 11; // Default value if no nearby clients or an exception occurs
        }

        private int CalculateDistanceFromBaseClient(Client client)
        {
            return client.ServerLocation.DistanceFrom(Client.ServerLocation);
        }

        private bool ExecutePramhStrategy(EnemyPage enemyPage, List<Creature> creatures)
        {
            List<Creature> creatureList = FilterCreaturesByControlStatus(enemyPage, creatures);
            if (CONSTANTS.GREEN_BOROS.Contains(enemyPage.Enemy.SpriteID))
            {
                List<Creature> greenBorosInRange = Client.GetAllNearbyMonsters(8, CONSTANTS.GREEN_BOROS.ToArray());
                foreach (Creature creature in greenBorosInRange.ToList<Creature>())
                {
                    foreach (Location location in Client.GetWarpPoints(new Location(Client.Map.MapID, 0, 0)))
                    {
                        if (creature.Location.DistanceFrom(location) <= 3)
                        {
                            greenBorosInRange.Remove(creature);
                        }
                    }
                }
                creatureList.AddRange(greenBorosInRange);
            }
            Creature targetCreature = creatureList.FirstOrDefault<Creature>();
            if (targetCreature != null && creatureList.Any() && enemyPage.spellsControlCbox.Checked && !targetCreature.IsAsleep)
            {
                Console.WriteLine($"[ExecutePramhStrategy] Targeting creature ID: {targetCreature.ID}, Hash: {targetCreature.GetHashCode()}, Name: {targetCreature.Name}, LastPramhd: {DateTime.UtcNow}");
                Client.UseSpell(enemyPage.spellsControlCombox.Text, creatureList.FirstOrDefault<Creature>(), _autoStaffSwitch, false);
                return true;
            }
            return false;
        }

        private List<Creature> SelectCreaturesForPramh(EnemyPage enemyPage, List<Creature> creatures)
        {
            List<Creature> selectedCreatures = FilterCreaturesByControlStatus(enemyPage, creatures);

            if (CONSTANTS.GREEN_BOROS.Contains(enemyPage.Enemy.SpriteID))
            {
                var additionalCreatures = Client.GetAllNearbyMonsters(8, CONSTANTS.GREEN_BOROS.ToArray())
                    .Where(creature => !Client.GetWarpPoints(new Location(Client.Map.MapID, 0, 0))
                    .Any(location => creature.Location.DistanceFrom(location) <= 3))
                    .ToList();

                selectedCreatures.AddRange(additionalCreatures);
            }

            return selectedCreatures;
        }

        private List<Creature> FilterCreaturesByControlStatus(EnemyPage enemyPage, List<Creature> creatureListIn)
        {
            bool isSuainSelected = enemyPage.spellsControlCombox.Text.Equals("suain", StringComparison.OrdinalIgnoreCase);

            return creatureListIn.Where(creature =>
                isSuainSelected ? !creature.IsSuained : !creature.IsAsleep || enemyPage.spellsControlCombox.Text != "suain"
            ).ToList();
        }

        private void AoSuain()
        {

            // Check if Ao Suain is enabled and the Suain effect is present before attempting to cast spells.
            if (!(Client?.ClientTab?.aoSuainCbox.Checked ?? false) || !Client.HasEffect(EffectsBar.Suain))
            {
                return;
                
            }
            Console.WriteLine("[AoSuain] Attempting to cast 'ao suain' to clear the Suain effect.");
            // Attempt to cast "Leafhopper Chirp" first. If it fails, attempt to cast "ao suain".
            // Only clear the Suain effect if one of the spells is successfully cast.
            if (Client.UseSpell("Leafhopper Chirp", null, false, false) || Client.UseSpell("ao suain", Client.Player, false, true))
            {
                Client.ClearEffect(EffectsBar.Suain);
            }
        }

        private void AutoGem()
        {
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return;
            }

            bool shouldUseGem = clientTab.autoGemCbox.Checked &&
                                Client.Experience > 4250000000U &&
                                DateTime.UtcNow.Subtract(_lastUsedGem).TotalMinutes > 5.0;

            if (!shouldUseGem)
            {
                return;
            }

            // Determine the gem type based on the selected text, then use the gem.
            byte choice = clientTab.expGemsCombox.Text == "Ascend HP" ? (byte)1 : (byte)2;
            Client.UseExperienceGem(choice);
        }

        private void UpdatePlayersListBasedOnStrangers()
        {
            _playersExistingOver250ms = !IsStrangerNearby() ? _playersExistingOver250ms : _playersExistingOver250ms.Where(p => DateTime.UtcNow.Subtract(p.Creation).TotalSeconds > 2.0).ToList();
        }

        private void CheckFasSpioradRequirement()
        {
            int requiredMp;
            var clientTab = Client.ClientTab;
            if (clientTab == null)
            {
                return;
            }

            if (clientTab.fasSpioradCbox.Checked && int.TryParse(clientTab.fasSpioradText.Text.Trim(), out requiredMp) && Client.ManaPct < requiredMp)
            {
                _needFasSpiorad = true;
            }
        }

        private void ManageSpellHistory()
        {
            Utility.Timer timer = Utility.Timer.FromSeconds(1);

            while (Client.SpellHistory.Count >= 3 || Client.SpellCounter >= 3)
            {
                if (timer.IsTimeExpired)
                    Client.SpellHistory.Clear();
                Thread.Sleep(10);
            }

            if (DateTime.UtcNow.Subtract(_spellTimer).TotalSeconds <= 1.0)
                return;

            Client.SpellHistory.Clear();

        }



        internal bool ContainsAlly(string name)
        {
            lock (_lock)
            {
                return _allyListName.Contains(name, StringComparer.CurrentCultureIgnoreCase);
            }
        }

        internal bool IsEnemyAlreadyListed(ushort sprite)
        {

            lock (_lock)
            {
                return _enemyListID.Contains(sprite);
            }
        }

        internal void AddAlly(Ally ally)
        {
            lock (_lock)
            {
                ally.Name = ally.Name.Trim().ToLowerInvariant(); // Normalize to lowercase
                _allyList.Add(ally);
                _allyListName.Add(ally.Name);
                //Console.WriteLine($"[Debug] Adding normalized Ally Name: {ally.Name}");
            }
        }

        internal void UpdateEnemyList(Enemy enemy)
        {
            lock (_lock)
            {
                _enemyList.Add(enemy);
                _enemyListID.Add(enemy.SpriteID);
            }
        }

        internal void RemoveAlly(string name)
        {
            if (Monitor.TryEnter(_lock, 1000))
            {
                try
                {
                    foreach (Ally ally in _allyList)
                    {
                        if (ally.Name == name)
                        {
                            _allyList.Remove(ally);
                            _allyListName.Remove(ally.Name);
                            break;
                        }
                    }
                }
                finally
                {
                    Monitor.Exit(_lock);
                }
            }
        }

        internal List<Ally> ReturnAllyList()
        {
            lock (_lock)
            {
                //Console.WriteLine($"[Debug] Ally List: {string.Join(", ", _allyList.Select(a => a.Name))}");
                return new List<Ally>(_allyList);
            }
        }

        internal List<Enemy> ReturnEnemyList()
        {
            lock (_lock)
            {
                return new List<Enemy>(_enemyList);
            }
        }

        internal void ClearEnemyLists(string name)
        {
            if (ushort.TryParse(name, out ushort spriteId))
            {
                List<Enemy> enemiesToRemove = new List<Enemy>();

                foreach (Enemy enemy in _enemyList)
                {
                    if (enemy.SpriteID == spriteId)
                    {
                        enemiesToRemove.Add(enemy);
                    }
                }

                if (enemiesToRemove.Any())
                {
                    if (Monitor.TryEnter(_lock, 1000))
                    {
                        try
                        {
                            foreach (Enemy enemy in enemiesToRemove)
                            {
                                _enemyList.Remove(enemy);
                                _enemyListID.Remove(enemy.SpriteID);
                            }
                        }
                        finally
                        {
                            Monitor.Exit(_lock);
                        }
                    }
                }
            }
        }



        private void Loot()
        {
            var clientTab = Client.ClientTab;

            if (clientTab == null || Client.ClientTab == null)
            {
                return;
            }

            bool isPickupGoldChecked = clientTab.pickupGoldCbox.Checked;
            bool isPickupItemsChecked = clientTab.pickupItemsCbox.Checked;
            bool isDropTrashChecked = clientTab.dropTrashCbox.Checked;

            if (!isPickupGoldChecked && !isPickupItemsChecked && !isDropTrashChecked)
                return;

            try
            {
                if (!IsStrangerNearby())
                {
                    var lootArea = new Structs.Rectangle(new Point(Client.ServerLocation.X - 2, Client.ServerLocation.Y - 2), new Size(5, 5));
                    List<Objects.GroundItem> nearbyObjects = Client.GetNearbyGroundItems(4);

                    if (nearbyObjects.Count > 0)
                    {
                        ProcessLoot(nearbyObjects, lootArea);
                    }

                    HandleTrashItems();
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine($"Error in Loot: {ex.Message}");
            }
        }

        private void ProcessLoot(List<Objects.GroundItem> nearbyObjects, Rectangle lootArea)
        {
            if (DateTime.UtcNow.Subtract(_lastLootTime).TotalMilliseconds < LootIntervalMs)
                return;

            bool isPickupGoldChecked = Client.ClientTab.pickupGoldCbox.Checked;
            bool isPickupItemsChecked = Client.ClientTab.pickupItemsCbox.Checked;

            if (isPickupGoldChecked)
            {
                foreach (var obj in nearbyObjects.Where(obj => IsGold(obj, lootArea)))
                {
                    Client.Pickup(0, obj.Location);

                }
            }

            if (isPickupItemsChecked)
            {
                foreach (var obj in nearbyObjects.Where(obj => IsLootableItem(obj, lootArea)))
                {
                    Client.Pickup(0, obj.Location);
                }
            }

            _lastLootTime = DateTime.UtcNow;
        }

        private bool IsGold(Objects.GroundItem obj, Rectangle lootArea)
        {
            return lootArea.ContainsPoint(obj.Location.Point) && obj.SpriteID == 140 && DateTime.UtcNow.Subtract(obj.Creation).TotalSeconds > 2.0;
        }

        private bool IsLootableItem(Objects.GroundItem obj, Rectangle lootArea)
        {
            return lootArea.ContainsPoint(obj.Location.Point) && obj.SpriteID != 140 && DateTime.UtcNow.Subtract(obj.Creation).TotalSeconds > 2.0;
        }

        private void HandleTrashItems()
        {
            if (DateTime.UtcNow.Subtract(_lastDropTime).TotalMilliseconds < DropIntervalMs)
                return;

            if (Client.ClientTab.dropTrashCbox.Checked)
            {

                foreach (Item item in Client.Inventory.ToList())
                {
                    if (Client.ClientTab._trashToDrop.Contains(item.Name, StringComparer.CurrentCultureIgnoreCase))
                    {
                        Client.Drop(item.Slot, Client.ServerLocation, item.Quantity);
                    }
                }

            }

            _lastDropTime = DateTime.UtcNow;
        }


    }


}
