/*  
 * Given a file with one integer per line, implement a solution that finds
 * the Kth smallest number.
 * Create a new file where line K has that number and the first K files
 * have the Kth smallest numbers.  
 */

include "Io.dfy"

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok, env.files
{
  var n := HostConstants.NumCommandLineArgs(env);
  if n != 4 {
    print "Usage: dotnet copy_list.dll <number> <sourcefile> <destinationfile>\n";
    return;
  }

  var num_arg := HostConstants.GetCommandLineArg(1 as uint64, env);
  var src_file_arg := HostConstants.GetCommandLineArg(2 as uint64, env);
  var dst_file_arg := HostConstants.GetCommandLineArg(3 as uint64, env);

  var src_file := ConvertByteArrayToCharArray(src_file_arg[..]);
  var dst_file := ConvertByteArrayToCharArray(dst_file_arg[..]);

  // Check if source file exists
  var src_exists := FileStream.FileExists(src_file, env);
  if !src_exists {
    print "Error: Source file does not exist.\n";
    return;
  }

  // Check if destination file exists
  var dst_exists := FileStream.FileExists(dst_file, env);
  if dst_exists {
    print "Error: Destination file already exists.\n";
    return;
  }

  // Open source file
  var src_file_stream_ok, src_file_stream := FileStream.Open(src_file, env);
  if !src_file_stream_ok {
    print "Error: Could not open source file.\n";
    return;
  }

  // Determine source file length
  var success_len, src_len := FileStream.FileLength(src_file, env);
  if !success_len {
    print "Error: Unable to determine source file length.\n";
    return;
  }

  // // If source file is empty, return
  // if src_len == 0 {
  //   print "Destination file not changed: Source file is empty.\n";
  //   return;
  // }

  // Read source file
  var src_buffer := new byte[src_len];
  var ok_read := src_file_stream.Read(0 as nat32, src_buffer, 0, src_len);
  if !ok_read {
    print "Error: Unable to read from source file.\n";
    return;
  }

  // Convert src_buffer to array<int>
  var src_array := ConvertByteArrayToIntArray(src_buffer);

  print "Source file contents: ";
  for i := 0 to src_array.Length {
    print src_array[i];
    print " ";
  }

}





// Method to convert a array<byte> to a array<int>
method ConvertByteArrayToIntArray(a:array<byte>) returns (b: array<int32>)
  ensures b.Length == a.Length
{
  
  b := new int32[a.Length];

  for i := 0 to a.Length {
    b[i] := a[i] as int32 - 48;
  }

   

}


// Method to convert a seq<char> to an array<char>
method ConvertByteArrayToCharArray(s:seq<char>) returns (a: array<char>)
  ensures a.Length == |s|
{
  a := new char[|s|];
  for i := 0 to |s| {
    a[i] := s[i];
  }
  return a;
}

