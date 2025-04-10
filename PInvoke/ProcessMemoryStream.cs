﻿using System;
using System.IO;
using System.Runtime.InteropServices;
using System.Text;
using Talos.Definitions;

namespace Talos.PInvoke
{
    internal sealed class ProcMemoryStream : Stream, IDisposable
    {
        private readonly ProcessAccessFlags _accessType;

        private bool _disposed;

        private IntPtr _pocessHandle;

        public override long Position { get; set; }

        public int ProcessId { get; set; }

        public override bool CanSeek => true;

        public override bool CanRead => (_accessType & ProcessAccessFlags.VmRead) > ProcessAccessFlags.None;

        public override bool CanWrite => (_accessType & (ProcessAccessFlags.VmOperation | ProcessAccessFlags.VmWrite)) > ProcessAccessFlags.None;

        public override long Length => throw new NotSupportedException("Length is not supported.");


        public ProcMemoryStream(int processId, ProcessAccessFlags access)
        {
            ProcessId = processId;
            _accessType = access;
            _pocessHandle = NativeMethods.OpenProcess(access, false, processId);
            if (_pocessHandle == IntPtr.Zero)
                throw new ArgumentException("Unable to open the process.");
        }

        ~ProcMemoryStream() { Dispose(false); }

        public override void Flush() => throw new NotSupportedException("Flush is not supported.");

        public override int Read(byte[] buffer, int offset, int count)
        {
            if (_disposed)
                throw new ObjectDisposedException("ProcessMemoryStream");
            if (_pocessHandle == IntPtr.Zero)
                throw new InvalidOperationException("Process is not open.");
            IntPtr intPtr = Marshal.AllocHGlobal(count);
            if (intPtr == IntPtr.Zero)
                throw new InvalidOperationException("Unable to allocate memory.");
            int bytesRead;
            NativeMethods.ReadProcessMemory(_pocessHandle, (IntPtr)Position, intPtr, count, out bytesRead);
            Position += bytesRead;
            Marshal.Copy(intPtr, buffer, offset, count);
            Marshal.FreeHGlobal(intPtr);
            return bytesRead;
        }

        public override long Seek(long offset, SeekOrigin origin)
        {
            if (_disposed)
                throw new ObjectDisposedException("ProcessMemoryStream");
            return origin switch
            {
                SeekOrigin.Begin => Position = offset,
                SeekOrigin.Current => Position += offset,
                SeekOrigin.End => throw new NotSupportedException("SeekOrigin.End not supported.")
            };
        }

        public override void SetLength(long value) => throw new NotSupportedException("Cannot set the length for this stream.");

        public override void Write(byte[] buffer, int offset, int count)
        {
            if (_disposed)
                throw new ObjectDisposedException("ProcessMemoryStream");
            if (_pocessHandle == IntPtr.Zero)
                throw new InvalidOperationException("Process is not open.");
            IntPtr intPtr = Marshal.AllocHGlobal(count);
            if (intPtr == IntPtr.Zero)
                throw new InvalidOperationException("Unable to allocate memory.");
            Marshal.Copy(buffer, offset, intPtr, count);
            int bytesWritten;
            NativeMethods.WriteProcessMemory(_pocessHandle, (IntPtr)Position, intPtr, count, out bytesWritten);
            Position += bytesWritten;
            Marshal.FreeHGlobal(intPtr);
        }

        public override void WriteByte(byte value) => Write(new byte[] { value }, 0, 1);

        public void WriteString(string value)
        {
            byte[] bytes = Encoding.ASCII.GetBytes(value);
            Write(bytes, 0, bytes.Length);
        }

        public override void Close()
        {
            if (_disposed)
                throw new ObjectDisposedException("ProcessMemoryStream");
            if (_pocessHandle != IntPtr.Zero)
            {
                NativeMethods.CloseHandle(_pocessHandle);
                _pocessHandle = IntPtr.Zero;
            }
            base.Close();
        }

        protected override void Dispose(bool disposing)
        {
            if (!_disposed)
            {
                if (_pocessHandle != IntPtr.Zero)
                {
                    NativeMethods.CloseHandle(_pocessHandle);
                    _pocessHandle = IntPtr.Zero;
                }
                base.Dispose(disposing);
            }
            _disposed = true;
        }

    }
}
