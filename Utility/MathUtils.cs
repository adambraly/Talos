﻿namespace Talos.Utility
{
    internal class MathUtils
    {
        internal static int Clamp(int value, int min, int max)
        {
            if (value < min) return min;
            if (value > max) return max;
            return value;
        }

    }
}
