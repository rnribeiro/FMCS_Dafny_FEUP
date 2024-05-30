/*  
 * Given a file with one integer per line, implement a solution that finds
 * the Kth smallest number.
 * Create a new file where line K has that number and the first K files
 * have the Kth smallest numbers.  
 */

include "Io.dfy"
include "../Challenge 2/Find.dfy"

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok, env.files
  ensures env.files == old(env.files)
  ensures env.Valid()
{
  // - First step -
  // Read the command line

  // Check the number of arguments
  var numArgs := HostConstants.NumCommandLineArgs(env);

  // If number of arguments is different than 4, print error message
  if numArgs != 4 {
    print "Error: Wrong number of arguments!\nUsage: dotnet find_k_smallest.dll <number> <sourcefile> <destinationfile>\n";
    return;
  }

  // Get command line arguments
  var argNumber := HostConstants.GetCommandLineArg(1, env);
  var sourceFile := HostConstants.GetCommandLineArg(2, env);
  var destFile := HostConstants.GetCommandLineArg(3, env);

  // Convert command line arguments to appropriate types
  if !IsInteger(argNumber) {
    print "Error: Wrong argument type! Argument 1 must be of type int!\nUsage: number sourceFile destFile\n";
    return;
  }
  var K := ConvertCharArrayToInt(argNumber);

  // Verify if source file exists
  var sourceFileExists := FileStream.FileExists(sourceFile, env);
  if !sourceFileExists {
    print "Error: Source file does not exist!\n";
    return;
  }

  // Verify argument 3 - destination file
  // Check if destination file exists, if so, terminate
  var destFileExists := FileStream.FileExists(destFile, env);
  if destFileExists {
    print "Error: Destination file already exists.\n";
    return;
  }

  // - Second step -
  // Open, read from and close the source file
  // Open source file

  var ok: bool;
  var sourceFileStream: FileStream?;
  ok, sourceFileStream := FileStream.Open(sourceFile, env);
  if !ok {
    print "Error: Could not open source file!\n";
    return;
  }

  // Determine source file length, if not possible, terminate
  var success_len, src_len := FileStream.FileLength(sourceFile, env);
  if !success_len {
    print "Error: Unable to determine source file length.\n";
    return;
  }
  // Check if source file is empty, if so, terminate
  if src_len == 0 {
    print "Error: Source file is empty.\n";
    return;
  }

  // Read source file, if not possible, terminate
  var src_buffer := new byte[src_len];
  ok := sourceFileStream.Read(0 as nat32, src_buffer, 0, src_len);
  if !ok {
    print "Error: Unable to read from source file.\n";
    return;
  }

  // Check if the number is within the range of the array
  if src_buffer.Length == 0 {
    print "Error: Source file is empty.\n";
    return;
  }

  // Convert src_buffer to array<int>
  var numbers := ConvertByteArrayToIntArray(src_buffer);

  // Close source file
  ok := sourceFileStream.Close();
  if !ok {
    print "Error: Unable to close source file.\n";
    return;
  }

  // // - Third step -
  // // Apply method from Challenge 2

  // var l, s := FindKthSmallest(numbers, K);


  // - Forth and final step -
  // Create, write to and close destination file

  var destFileStream: FileStream?;
  ok, destFileStream := FileStream.Open(destFile, env);
  // Create and open destination file
  if !ok {
    print "Error: Could not create destination file!\n";
    return;
  }

  // Convert src_array to array<byte>
  var numbersByteArray := ConvertIntArrayToByteArray(numbers);

  // Ensure numbersByteArray.Length is within the range of int32
  if numbersByteArray.Length > 0x7FFFFFFF  {
    print "Error: Destination file size is too large.\n";
    return;
  }
  if numbersByteArray.Length == 0 {
    print "Error: Empty output.\n";
    return;
  }

  // Write to destination file
  ok := destFileStream.Write(0, numbersByteArray, 0, numbersByteArray.Length as int32);
  if !ok {
    print "Error: Could not write to destination file!\n";
    return;
  }

  // Close the destination file
  ok := destFileStream.Close();
  if !ok {
    print "Error: Could not close destination file!\n";
    return;
  }

  print "File copy successful.\n";
}



// Predicate to check if a array<char> contains only integers (ASCII encoded)
// And, if the array contains only one element, it must be a digit
predicate IsInteger(chars: array<char>)
  reads chars
{
  (forall i: int :: 0 <= i < chars.Length ==> '0' <= chars[i] <= '9')
  &&
  (chars.Length == 1 ==> 0 < chars[0] as int - 48 <= 9)
}



/*
Method to convert a array<char> to an integer
The input array<char> contains ASCII encoded integers
The output integer is the actual integer
Example: 
    a = ['1', '2', '3'] outputs b = 123
    ASCII code for '1', '2', '3' are 49, 50, 51, respectively
*/
method ConvertCharArrayToInt(a: array<char>) returns (b: int)
  requires IsInteger(a)
{
  var temp: seq<int> := [];
  // Convert K char array to int
  for i := 0 to a.Length {
    temp := temp + [a[i] as int - 48];
  }

  b := ConvertDigitsSeqToInt(temp);
}


/*
Method to convert a seq<int> to an integer
The input seq<int> contains digits of a number
The output integer is the actual integer
Example: 
    a = [1, 2, 3] outputs b = 123
*/
method ConvertDigitsSeqToInt(s: seq<int>) returns (b: int)
{
  // Initialize num to 0
  var num := 0;
  // Loop through temp's digits to form the number
  for i := 0 to |s| {
    // Example: temp = [1, 2, 3]
    // num = 0
    // num = 0 * 10 + 1 = 1
    // num = 1 * 10 + 2 = 12
    // num = 12 * 10 + 3 = 123
    num := num * 10 + s[i];
  }
  b := num;
}


/* 
Method to convert a array<byte> to a array<int>
The input array<byte> contains ASCII encoded integers
The output array<int> contains the actual integers
The method converts the ASCII encoded integers to actual integers ignoring any other characters
Example1: 
    a = [49, 13, 10, 50, 13, 10, 51, 13, 10] outputs b = [1, 2, 3] 
    ASCII code for '1', '2', '3' are 49, 50, 51, respectively;
    ASCII code for '\r' and '\n' are 13 and 10, respectively
Example2: 
    a = [49, 13, 10, 50, 13, 10, 51] outputs b = [1, 2, 3]
*/
method ConvertByteArrayToIntArray(a:array<byte>) returns (b: array<int>)
{
  var temp: seq<int> := [];
  var result: seq<int> := [];

  // Loop through the array<byte>
  for i := 0 to a.Length {
    // Convert ASCII code to integer
    var number := a[i] as int - 48;
    // Check if the character is a digit
    if number >= 0 && number <= 9 {
      // Accumulate the digits to form the number
      temp := temp + [number];
    } else {
      // If the character is not a digit and temp is not empty,
      // convert temp to an integer and add it to result
      if |temp| > 0 {
        var num := ConvertDigitsSeqToInt(temp);
        // Add the number to result
        result := result + [num];
        // Reset temp
        temp := [];
      }
    }
  }

  // If temp is not empty at the end of the loop, convert temp to an integer and add it to result
  if |temp| > 0 {
    var num := ConvertDigitsSeqToInt(temp);
    result := result + [num];
    temp := [];
  }

  // Convert seq<int> to array<int>
  b := ConvertIntSeqToIntArray(result);

  return b;
}

/*
Method to convert an integer into a sequence of ASCII encoded integers (bytes)
The method converts the integer to ASCII encoded integers
Example: a = 123 outputs b = [49, 50, 51]
ASCII code for '1', '2', '3' are 49, 50, 51, respectively
*/
method ConvertIntToByteSeq(a: int) returns (b: seq<byte>)
{
  var digits: seq<byte> := [];
  var num := a;
  // Convert the number to ASCII encoded integers
  // Example: num = 123
  // digits = []
  // digits = [123 % 10 + 48] + [] = [51] + [] = [51] (= ['3'])
  // num = 123 / 10 = 12
  // digits = [12 % 10 + 48] + [51] = [50] + [51] = [50, 51] (= ['2', '3'])
  // num = 12 / 10 = 1
  // digits = [1 % 10 + 48] + [50, 51] = [49] + [50, 51] = [49, 50, 51] (= ['1', '2', '3'])
  while num > 0 {
    digits := [(num % 10) as byte + 48 as byte] + digits; // Convert digit to ASCII
    num := num / 10;
  }

  return digits;
}

// Method to convert a array<int> to a array<byte>
// The method converts the integers to ASCII encoded integers
// Example: a = [1, 2, 3] outputs b = [49, 13, 10, 50, 13, 10, 51]
method ConvertIntArrayToByteArray(a: array<int>) returns (b: array<byte>)
{
  var temp: seq<byte> := [];

  // Loop through the array<int>
  for i := 0 to a.Length {
    var num := a[i];
    // If the number is 0, add 0 to temp
    if num == 0 {
      temp := temp + [48 as byte]; // ASCII code for '0'
    } else {
      var digits := ConvertIntToByteSeq(num);
      // Add the digits to temp
      temp := temp + digits;
      // Add '\r' and '\n' to temp if the number is not the last number
      if i != a.Length - 1 {
        temp := temp + [13 as byte] + [10 as byte]; // ASCII code for '\r' and '\n'
      }
    }
  }

  // Convert seq<byte> to array<byte>
  b := ConvertByteSeqToByteArray(temp);

  return b;
}

// Method to convert a seq<byte> to an array<byte>
method ConvertByteSeqToByteArray(s: seq<byte>) returns (a: array<byte>)
  ensures a.Length == |s|
{
  a := new byte[|s|];
  for i := 0 to |s| {
    a[i] := s[i];
  }

  return a;
}

// Method to convert a seq<int> to an array<int>
method ConvertIntSeqToIntArray(s:seq<int>) returns (a: array<int>)
  ensures a.Length == |s|
{
  a := new int[|s|];
  for i := 0 to |s| {
    a[i] := s[i];
  }
  return a;
}