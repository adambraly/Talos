﻿using System.Drawing;
using System.Globalization;

namespace Talos.Structs
{
    internal struct Rect
    {
        internal int _left;

        internal int _top;

        internal int _right;

        internal int _bottom;

        internal int X
        {
            get
            {
                return _left;
            }
            set
            {
                _right -= _left - value;
                _left = value;
            }
        }

        internal int Y
        {
            get
            {
                return _top;
            }
            set
            {
                _bottom -= _top - value;
                _top = value;
            }
        }

        internal int Height
        {
            get
            {
                return _bottom - _top;
            }
            set
            {
                _bottom = value + _top;
            }
        }

        internal int Width
        {
            get
            {
                return _right - _left;
            }
            set
            {
                _right = value + _left;
            }
        }

        internal System.Drawing.Point Point
        {
            get
            {
                return new System.Drawing.Point(_left, _top);
            }
            set
            {
                X = value.X;
                Y = value.Y;
            }
        }

        internal System.Drawing.Size Size
        {
            get
            {
                return new System.Drawing.Size(Width, Height);
            }
            set
            {
                Width = value.Width;
                Height = value.Height;
            }
        }

        internal Rect(int left, int top, int right, int bottom)
        {
            _left = left;
            _top = top;
            _right = right;
            _bottom = bottom;
        }

        internal Rect(System.Drawing.Rectangle rect) : this(rect.Left, rect.Top, rect.Right, rect.Bottom) { }


        public override string ToString()
        {
            return string.Format(CultureInfo.CurrentCulture, "{{Left={0},Top={1},Right={2},Bottom={3}}}", _left, _top, _right, _bottom);
        }
    }
}
