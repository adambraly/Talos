﻿namespace Talos.Forms.UI
{
    internal class Ally
    {
        internal string Name { get; set; }
        internal AllyPage Page { get; set; }
        internal Ally(string name)
        {
            Name = name;
        }
        public override string ToString()
        {
            return Name;
        }   

    }
}
