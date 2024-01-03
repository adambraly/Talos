using System.Runtime.CompilerServices;

public class KhanArchive
{
	public DATArchive AD
	{
		get;
		set;
	}

	public DATArchive EH
	{
		get;
		set;
	}

	public DATArchive IM
	{
		get;
		set;
	}

	public DATArchive NS
	{
		get;
		set;
	}

	public DATArchive TZ
	{
		get;
		set;
	}

	public KhanArchive(string path, bool male)
	{
		string str = male ? "m" : "w";
		AD = DATArchive.FromFile(path + "\\khan" + str + "ad.dat");
		EH = DATArchive.FromFile(path + "\\khan" + str + "eh.dat");
		IM = DATArchive.FromFile(path + "\\khan" + str + "im.dat");
		NS = DATArchive.FromFile(path + "\\khan" + str + "ns.dat");
		TZ = DATArchive.FromFile(path + "\\khan" + str + "tz.dat");
	}
}
