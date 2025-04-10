﻿using System;
using System.Collections.Generic;
using System.Linq;
using Talos.Base;
using Talos.Objects;

namespace Talos.Bashing
{
    internal sealed class FeralBashing : BashingBase
    {
        // Standard skills
        private Skill ClawFist => Client.Skillbook["Claw Fist"];
        private Skill RagingAttack => Client.Skillbook["Raging Attack"];
        private Skill FuriousBash => Client.Skillbook["Furious Bash"];
        private Skill MantisKick => Client.Skillbook["Mantis Kick"];
        private Skill HighKick => Client.Skillbook["High Kick"];
        private Skill Kick => Client.Skillbook["Kick"];

        // Numbered skills: try direct lookup first, then fall back to the numbered lookup.
        private Skill MassStrike => Client.Skillbook["Mass Strike"] ?? Client.Skillbook.GetNumberedSkill("Mass Strike");
        private Skill DoubleRake => Client.Skillbook["Double Rake"] ?? Client.Skillbook.GetNumberedSkill("Double Rake");
        private Skill Pounce => Client.Skillbook["Pouncet"] ?? Client.Skillbook.GetNumberedSkill("Pounce");


        // Crasher skills
        private Skill AutoHemloch => Client.Skillbook["Auto Hemloch"];
        private Skill AnimalFeast => Client.Skillbook["Animal Feast"];
        private Skill Crasher => Client.Skillbook["Crasher"];
        private Skill WhirlwindAttack => Client.Skillbook["Whirlwind Attack"];

        public FeralBashing(Bot bot)
            : base(bot)
        {
        }

        /// <summary>
        /// Tries to use the best possible skill(s) on the given target.
        /// </summary>
        /// <param name="target">The creature we're fighting.</param>
        internal override void UseSkills(Creature target)
        {
            var now = DateTime.UtcNow;
            bool canUseSkill = (now - LastUsedSkill) > TimeSpan.FromMilliseconds(SkillIntervalMs);
            bool canAssail = (now - LastAssailed) > TimeSpan.FromMilliseconds(1000.0);

            if (canUseSkill && DoActionForSurroundingCreatures())
            {
                LastUsedSkill = now;
                return;
            }

            int distanceToTarget = Client.ClientLocation.DistanceFrom(target.Location);
            if (distanceToTarget > 5)
                return;

            if (distanceToTarget == 1)
            {
                if (target.IsAsgalled && canUseSkill && CanUseCrashers())
                {
                    if (DoCrashers())
                    {
                        LastUsedSkill = now;
                    }
                }

                if (target.IsAsgalled && !Client.Player.IsDioned && !BashAsgall)
                    return;

                if (canAssail && (BashAsgall || !target.IsAsgalled))
                {
                    if (ClawFist != null)
                        Client.UseSkill(ClawFist.Name);
                    UseAssails();
                    LastAssailed = now;
                }

                if (canUseSkill && DoActionForRange1(target))
                    LastUsedSkill = now;
            }
            else // Range is <= 5 but not 1
            {

                if (target.IsAsgalled && !Client.Player.IsDioned && !BashAsgall)
                    return;

                if (canUseSkill && DoActionForRangeLessThan5(target))
                    LastUsedSkill = now;
            }
        }

        /// <summary>
        /// Checks surrounding creatures for an AOE opportunity.
        /// </summary>
        /// <returns>True if an AOE attack was performed; otherwise false.</returns>
        private bool DoActionForSurroundingCreatures()
        {
            var nearby = GetSurroundingCreatures(KillableTargets)
                         .Where(ShouldUseSkillsOnTarget)
                         .ToList();

            if (nearby.Count >= 3 || (nearby.Count == 2 && nearby.Any(mob => mob.HealthPercent >= 80)))
            {
                if (RagingAttack != null && Client.UseSkill(RagingAttack.Name))
                    return true;

                if (FuriousBash != null && Client.UseSkill(FuriousBash.Name))
                    return true;

                if (CanUseCrashers() && WhirlwindAttack != null && Client.UseSkill(WhirlwindAttack.Name))
                {
                    Client.Player.NeedsHeal = true;
                    return true;
                }
            }

            return false;
        }
       

        /// <summary>
        /// Logic for range < 5 but not 1 tile (i.e., 2-5).
        /// Must be aligned to X or Y & facing direction for "Pounce."
        /// </summary>
        private bool DoActionForRangeLessThan5(Creature target)
        {
            bool axisAligned = (target.Location.X == Client.ClientLocation.X ||
                               target.Location.Y == Client.ClientLocation.Y);
            bool directionMatch = (target.Location.GetDirection(Client.ClientLocation) == Client.ClientDirection);

            if (!ShouldUseSkillsOnTarget(target))
                return false;

            return axisAligned && directionMatch &&
                (Pounce != null && Client.UseSkill(Pounce.Name));
        }

        /// <summary>
        /// Attempts to use a melee-range skill based on the target's health.
        /// </summary>
        /// <param name="target">The target in melee range.</param>
        /// <returns>True if a skill was successfully used; otherwise false.</returns>
        private bool DoActionForRange1(Creature target)
        {
            if (!MeetsKillCriteria(target) || !ShouldUseSkillsOnTarget(target))
                return false;

            byte hp = target.HealthPercent;

            // For high-health targets (>=80%), try a combo using Wolf Fang Fist with Sprint Potion or Pounce.
            if (hp >= 80 && (TryComboWithSleepSkill("Sprint Potion", true) ||
                 (Pounce != null && TryComboWithSleepSkill(Pounce.Name))))
            {
                return true;
            }

            // For targets with higher health (>=60%), try Double Rake or Raging Attack.
            if (hp >= 60 &&
                (DoubleRake != null && Client.UseSkill(DoubleRake.Name)) ||
                (RagingAttack != null && Client.UseSkill(RagingAttack.Name)))
            {
                return true;
            }

            // Try to crasher
            if (hp >= 40 && CanUseCrashers())
            {
                // If OnlyCrasherAsgall is false, or the target is Asgalled
                if (!OnlyCrasherAsgall || target.IsAsgalled)
                {
                    if (DoCrashers())
                    {
                        return true;
                    }
                }
            }

            // For moderate targets (>=40%), try Mass strike
            if (hp >= 40 && 
                (MassStrike != null && Client.UseSkill(MassStrike.Name)))
                return true;


            // For targets with lower health (>=40%), try Pounce
            if (hp >= 40 &&
                (Pounce != null && Client.UseSkill(Pounce.Name)))
                return true;

            // For very low-health targets (<=20%), try Mantis Kick, High Kick, or Kick
            if (hp <= 20 &&
                ((MantisKick != null && Client.UseSkill(MantisKick.Name)) ||
                    (HighKick != null && Client.UseSkill(HighKick.Name)) ||
                    (Kick != null && Client.UseSkill(Kick.Name))))
            {

                return true;
            }

            return false;
        }

        /// <summary>
        /// Executes risky skill sequences such as Sacrifice/Mad Soul or the crasher combo.
        /// </summary>
        /// <returns>True if a risky combo was successfully used, otherwise false.</returns>
        private bool DoCrashers()
        {
            if (!UseCrashers)
                return false;

            bool hasHemloch = Client.Inventory.Contains("Hemloch");
            bool autoHemlochAvailable = (AutoHemloch?.CanUse ?? false);
            bool canHemloch = autoHemlochAvailable || Client.Player.HealthPercent <= 5 || hasHemloch;

            bool canAnimalFeast = (AnimalFeast?.CanUse ?? false);
            bool canCrasher = (Crasher?.CanUse ?? false);

            if (!canHemloch || !(canAnimalFeast || canCrasher))
                return false;


            if (AutoHemloch != null && autoHemlochAvailable)
            {
                Client.UseSkill(AutoHemloch.Name);
            }
            else if (hasHemloch)
            {
                Client.UseItem("Hemloch");
            }

            if (AnimalFeast != null)
                Client.UseSkill(AnimalFeast.Name);
            if (Crasher != null)
                Client.UseSkill(Crasher.Name);
            if (WhirlwindAttack != null)
                Client.UseSkill(WhirlwindAttack.Name);

            if (Client.HasItem("Damage Scroll"))
                Client.UseItem("Damage Scroll");

            Client.Player.NeedsHeal = true;
            return true;

        }
    }

}
