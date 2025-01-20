﻿using System.IO;
using Talos.Capricorn.IO;

namespace Talos.Capricorn.Drawing
{
    /// <summary>
    /// MPF Image Class
    /// </summary>
    public class MPFImage
    {
        public int expectedFrames;
        public int width;
        public int height;
        public MPFFrame[] frames;
        public uint expectedDataSize;
        public byte walkStart;
        public byte walkLength;
        public uint ffUnknown;
        public bool isNewFormat;
        public bool isFFFormat;
        public byte idleStart;
        public byte idleLength;
        public byte idleSpeed;
        public byte walkSpeed;
        public byte attack1Start;
        public byte attack1Length;
        public byte attack2Start;
        public byte attack2Length;
        public byte attack3Start;
        public byte attack3Length;
        public string palette;

        /// <summary>
        /// Gets or sets the frame at the specified index.
        /// </summary>
        /// <param name="index">Zero-based index of the frame.</param>
        /// <returns>MPF frame data.</returns>
        public MPFFrame this[int index]
        {
            get { return frames[index]; }
            set { frames[index] = value; }
        }

        public string Palette
        {
            get { return palette; }
        }

        /// <summary>
        /// Gets whether the MPF is flagged using the FF header.
        /// </summary>
        public bool IsFFFormat
        {
            get { return isFFFormat; }
        }

        /// <summary>
        /// Gets whether the MPF is using the newer header format.
        /// </summary>
        public bool IsNewFormat
        {
            get { return isNewFormat; }
        }

        /// <summary>
        /// Gets the value of the FF Header unknown value.
        /// </summary>
        public uint FFUnknown
        {
            get { return ffUnknown; }
        }

        /// <summary>
        /// Gets the expected size of the data, excluding the header, in bytes.
        /// </summary>
        public uint ExpectedDataSize
        {
            get { return expectedDataSize; }
        }

        /// <summary>
        /// Gets the frames of the image.
        /// </summary>
        public MPFFrame[] Frames
        {
            get { return frames; }
        }

        /// <summary>
        /// Gets the height of the frames' containing canvas, in pixels.
        /// </summary>
        public int Height
        {
            get { return height; }
        }

        /// <summary>
        /// Gets the width of the frames' containing canvas, in pixels.
        /// </summary>
        public int Width
        {
            get { return width; }
        }

        /// <summary>
        /// Gets the numbers of frames expected in the image.
        /// </summary>
        public int ExpectedFrames
        {
            get { return expectedFrames; }
        }

        /// <summary>
        /// Loads a MPF file from disk.
        /// </summary>
        /// <param name="file">MPF image file to load.</param>
        /// <returns>MPF image object.</returns>
        public static MPFImage FromFile(string file)
        {
            // Create File Stream
            FileStream stream = new FileStream(file,
                FileMode.Open, FileAccess.Read, FileShare.Read);

            // Load MPF from File Stream
            return LoadMPF(stream);
        }

        /// <summary>
        /// Loads a MPF image file from raw data bytes.
        /// </summary>
        /// <param name="data">Raw data to use.</param>
        /// <returns>MPF image.</returns>
        public static MPFImage FromRawData(byte[] data)
        {
            // Create Memory Stream
            MemoryStream stream = new MemoryStream(data);

            // Load HPF from Memory Stream
            return LoadMPF(stream);
        }

        /// <summary>
        /// Loads a MPF image file from an archive (case-sensitive).
        /// </summary>
        /// <param name="file">MPF image to load.</param>
        /// <param name="archive">Data archive to load from.</param>
        /// <returns>MPF image.</returns>
        public static MPFImage FromArchive(string file, DATArchive archive)
        {
            // Check if File Exists
            if (!archive.Contains(file))
                return null;

            // Extract and Create File
            return FromRawData(archive.ExtractFile(file));
        }

        /// <summary>
        /// Loads a MPF image file from an archive.
        /// </summary>
        /// <param name="file">MPF image to load.</param>
        /// <param name="ignoreCase">Ignore case (noncase-sensitive).</param>
        /// <param name="archive">Data archive to load from.</param>
        /// <returns>MPF image.</returns>
        public static MPFImage FromArchive(string file, bool ignoreCase, DATArchive archive)
        {
            // Check if File Exists
            if (!archive.Contains(file, ignoreCase))
                return null;

            // Extract and Create File
            return FromRawData(archive.ExtractFile(file, ignoreCase));
        }

        /// <summary>
        /// Internal function that loads a MPF image from a given data stream.
        /// </summary>
        /// <param name="stream">Data stream.</param>
        /// <returns>MPF image.</returns>
        private static MPFImage LoadMPF(Stream stream)
        {
            // Create Binary Reader
            stream.Seek(0, SeekOrigin.Begin);
            BinaryReader reader = new BinaryReader(stream);

            // Create MPF File
            MPFImage mpf = new MPFImage();

            #region Check for FF Header Type
            if (reader.ReadUInt32() == 0xFFFFFFFF)
            {
                mpf.isFFFormat = true;
                mpf.ffUnknown = reader.ReadUInt32();
            }
            else
                reader.BaseStream.Seek(-4, SeekOrigin.Current);

            #endregion

            // Get Frame Count
            mpf.expectedFrames = reader.ReadByte();

            // Allocate Frames
            mpf.frames = new MPFFrame[mpf.expectedFrames];

            #region Read MPF Header
            mpf.width = reader.ReadUInt16();
            mpf.height = reader.ReadUInt16();

            mpf.expectedDataSize = reader.ReadUInt32();

            mpf.walkStart = reader.ReadByte();
            mpf.walkLength = reader.ReadByte();

            // If 0xFFFF, then New Format
            mpf.isNewFormat = (reader.ReadUInt16() == 0xFFFF);

            // Get Extended Header Info
            if (mpf.isNewFormat)
            {
                mpf.idleStart = reader.ReadByte();
                mpf.idleLength = reader.ReadByte();
                mpf.idleSpeed = reader.ReadByte();
                mpf.walkSpeed = reader.ReadByte();
                mpf.attack1Start = reader.ReadByte();
                mpf.attack1Length = reader.ReadByte();
                mpf.attack2Start = reader.ReadByte();
                mpf.attack2Length = reader.ReadByte();
                mpf.attack3Start = reader.ReadByte();
                mpf.attack3Length = reader.ReadByte();
            }
            else
            {
                reader.BaseStream.Seek(-2L, SeekOrigin.Current);
                mpf.attack1Start = reader.ReadByte();
                mpf.attack1Length = reader.ReadByte();
                mpf.idleStart = reader.ReadByte();
                mpf.idleLength = reader.ReadByte();
                mpf.idleSpeed = reader.ReadByte();
                mpf.walkSpeed = reader.ReadByte();
            }
            #endregion

            // Get Data Start Address
            long dataStart = reader.BaseStream.Length - mpf.expectedDataSize;

            #region Read Frame Headers
            for (int i = 0; i < mpf.expectedFrames; i++)
            {
                #region Read Variables
                int left = reader.ReadUInt16();
                int top = reader.ReadUInt16();
                int right = reader.ReadUInt16();
                int bottom = reader.ReadUInt16();

                int width = right - left;
                int height = bottom - top;

                int xOffset = reader.ReadUInt16();
                int yOffset = reader.ReadUInt16();

                // Reverse Bytes
                //xOffset = ((xOffset % 256) << 8) + (xOffset / 256);
                //yOffset = ((yOffset % 256) << 8) + (yOffset / 256);

                long startAddress = reader.ReadUInt32();

                if (left == 0xFFFF && right == 0xFFFF)
                {
                    mpf.palette = string.Format("mns{0:D3}.pal", startAddress);
                    mpf.expectedFrames--;
                }
                else mpf.palette = "mns000.pal";
                #endregion

                byte[] frameData = null;

                if (height > 0 && width > 0)
                {
                    // Save Current Position
                    long position = reader.BaseStream.Position;

                    #region Read Raw Frame Data
                    reader.BaseStream.Seek(dataStart + startAddress, SeekOrigin.Begin);

                    frameData = reader.ReadBytes(height * width);

                    reader.BaseStream.Seek(position, SeekOrigin.Begin);
                    #endregion
                }

                // Create Frame
                mpf.frames[i] = new MPFFrame(left, top, width, height, xOffset, yOffset, frameData);

            } reader.Close();
            #endregion

            // Return MPF
            return mpf;
        }

        /// <summary>
        /// Gets the string representation of the object.
        /// </summary>
        /// <returns></returns>
        public override string ToString()
        {
            return "{Frames = " + expectedFrames.ToString() + ", Width = " +
                width.ToString() + ", Height = " +
                height.ToString() + ", Unknown = 0x}";
        }
    }

    /// <summary>
    /// MPF Image Frame Class
    /// </summary>
    public class MPFFrame
    {
        private int left;
        private int top;
        private int width;
        private int height;
        private byte[] rawData;
        private int xOffset;
        private int yOffset;

        /// <summary>
        /// Gets whether the frame is renderable or not.
        /// </summary>
        public bool IsValid
        {
            get
            {
                if (rawData == null || rawData.Length < 1)
                    return false;
                else if (width < 1 || height < 1)
                    return false;
                else if (width * height != rawData.Length)
                    return false;
                else
                    return true;
            }
        }

        /// <summary>
        /// Gets the Y positional offset of the frame.
        /// </summary>
        public int OffsetY
        {
            get { return yOffset; }
        }

        /// <summary>
        /// Gets the X positional offset of the frame.
        /// </summary>
        public int OffsetX
        {
            get { return xOffset; }
        }

        /// <summary>
        /// Gets the raw byte data for the frame's image.
        /// </summary>
        public byte[] RawData
        {
            get { return rawData; }
        }

        /// <summary>
        /// Gets the height of the frame image, in pixels.
        /// </summary>
        public int Height
        {
            get { return height; }
        }

        /// <summary>
        /// Gets the width of the frame image, in pixels.
        /// </summary>
        public int Width
        {
            get { return width; }
        }

        /// <summary>
        /// Gets or sets the Y position of the frame's location within the canvas.
        /// </summary>
        public int Top
        {
            get { return top; }
            set { top = value; }
        }

        /// <summary>
        /// Gets or sets the X position of the frame's location within the canvas.
        /// </summary>
        public int Left
        {
            get { return left; }
            set { left = value; }
        }

        /// <summary>
        /// Creates a frame with the specified values.
        /// </summary>
        /// <param name="left">X position of the frame within the canvas.</param>
        /// <param name="top">Y position of the frame within the canvas.</param>
        /// <param name="width">Width of the frame, in pixels.</param>
        /// <param name="height">Height of the frame, in pixels.</param>
        /// <param name="unknown">Unknown value.</param>
        /// <param name="rawData">Raw data bytes of the frame.</param>
        public MPFFrame(int left, int top, int width, int height, int xOffset, int yOffset, byte[] rawData)
        {
            this.left = left;
            this.top = top;
            this.width = width;
            this.height = height;
            this.xOffset = xOffset;
            this.yOffset = yOffset;
            this.rawData = rawData;
        }

        /// <summary>
        /// Gets the string representation of the object.
        /// </summary>
        /// <returns></returns>
        public override string ToString()
        {
            return "{X = " + left.ToString() + ", Y = " +
                top.ToString() + ", Width = " +
                width.ToString() + ", Height = " +
                height.ToString() + ", Offset = (" +
                xOffset.ToString() + ", " + yOffset.ToString() + ")}";
        }
    }
}