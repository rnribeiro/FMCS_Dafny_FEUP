/*  
 * Given a file with one integer per line, implement a solution that finds
 * the Kth smallest number.
 * Create a new file where line K has that number and the first K files
 * have the Kth smallest numbers.  
 */

/* 
 * Building command:
 * 
 * dafny build find_k_smallest.dfy IoNative.cs --unicode-char:false
 */

/* 
 * Running commands (examples):
 *
 * ./find_k_smallest.exe 5 SourceFile DestFile
 * (or)
 * dotnet find_k_smallest.dll 5 SourceFile DestFile
 */

include "Io.dfy"

function IsInteger(chars: array<char>): bool
  reads chars
{
  // Check each character in the array
  forall i :: 0 <= i < chars.Length ==> '0' <= chars[i] <= '9'
}

method CharArrayToInt(arr: array<char>) returns (n: int)
  requires IsInteger(arr)
{
  var k := 0;
  var mult := 1;
  var i := arr.Length - 1;

  while (i >= 0)
  {
    k := k + (arr[i] as int  - '0' as int) * mult;
    mult := mult * 10;
    i := i - 1;
  }

  return k;
}

method ByteArrayToIntArray(a:array<byte>) returns (b: array<int32>)
  //ensures forall i :: 0 <= i < b.Length ==> 0 <= b[i] < 256
  ensures b.Length == a.Length
{
  b := new int32[a.Length];

  for i := 0 to a.Length
  {
    b[i] := a[i] as int32 - 48;
  }
}

method IntArrayToByteArray(a:array<int32>) returns (b: array<byte>)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] < 256
  ensures b.Length == a.Length
{
  b := new byte[a.Length];

  for i := 0 to a.Length
  {
    b[i] := a[i] as byte;
  }
}

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok, env.files
{
  // - First step -
  // Read the command line

  // Check the number of arguments
  var numArgs := HostConstants.NumCommandLineArgs(env);

  // If number of arguments is different than 4, print error message
  if numArgs != 4
  {
    print "Error: Wrong number of arguments!\nUsage: number sourceFile destFile";
    return;
  }

  // Verify argument 1 - number
  // (first verification will only verify if it is a number)
  // (later it will verify if the number is between the correct range)

  var argNumber := HostConstants.GetCommandLineArg(1, env);

  if !IsInteger(argNumber)
  {
    print "Error: Wrong argument type! Argument 1 must be of type int!\nUsage: number sourceFile destFile";
    return;
  }

  // Convert the number variable (char array) into 
  var number: int := CharArrayToInt(argNumber);

  // Verify argument 2 - source file

  var sourceFile := HostConstants.GetCommandLineArg(2, env);

  // Verify if source file exists

  var sourceFileExists := FileStream.FileExists(sourceFile, env);

  if !sourceFileExists
  {
    print "Error: Source file does not exist!";
    return;
  }

  // Verify argument 3 - destination file

  var destFile := HostConstants.GetCommandLineArg(3, env);

  // Verify if destination file already exists

  var destFileExists := FileStream.FileExists(destFile, env);

  if destFileExists
  {
    print "Error: Destination file already exists!";
    return;
  }

  // - Second step -
  // Open, read from and close the source file

  // Open source file

  var ok: bool;
  var sourceFileStream: FileStream?;

  ok, sourceFileStream := FileStream.Open(sourceFile, env);

  if !ok
  {
    print "Error: Could not open source file!";
    return;
  }

  // Get the length of the source file
  
  var len: int32;

  ok, len := FileStream.FileLength(sourceFile, env);

  if !ok {
    print "Error: Could not get the length of the source file!";
    return;
  }

  // Create a buffer to read the file content

  var buffer := new byte[len];

  // Read the content of the source file into the buffer

  ok := sourceFileStream.Read(0, buffer, 0, len);

  if !ok {
    print "Error: Could not read from source file!";
    return;
  }

  // Convert the byte array to an int array

  var numbers := ByteArrayToIntArray(buffer);

  // Close the source file

  ok := sourceFileStream.Close();

  if !ok {
    print "Error: Could not close source file!";
    return;
  }

  // - Third step -
  // Apply method from Challenge 2

  //------------------------------

  // - Forth and final step -
  // Create, write to and close destination file

  // Create/open destination file

  var destFileStream: FileStream?;

  ok, destFileStream := FileStream.Open(destFile, env);

  if !ok
  {
    print "Error: Could not create destination file!";
    return;
  }

  // Convert the int array to a byte array

  var numbersByteArray := IntArrayToByteArray(numbers);

  // Write the byte array to the destination file

  ok := destFileStream.Write(0, numbersByteArray, 0, len);

  if !ok
  {
    print "Error: Could not write to destination file!";
    return;
  }

  // Close the destination file

  ok := destFileStream.Close();

  if !ok {
    print "Error: Could not close destination file!";
    return;
  }
}
