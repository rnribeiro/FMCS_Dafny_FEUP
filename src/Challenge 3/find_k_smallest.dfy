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
    print "Usage: dotnet find_k_smallest.dll <number> <sourcefile> <destinationfile>\n";
    return;
  }

  // Get command line arguments
  var num_arg := HostConstants.GetCommandLineArg(1 as uint64, env);
  var src_file_arg := HostConstants.GetCommandLineArg(2 as uint64, env);
  var dst_file_arg := HostConstants.GetCommandLineArg(3 as uint64, env);

  // Convert command line arguments to appropriate types
  var K_char_array := ConvertCharSeqToCharArray(num_arg[..]);
  if !ValidKArgArray(K_char_array) {
    print "Error: Invalid <number> argument.\n";
    return;
  }
  var K := ConvertCharArrayToInt(K_char_array);

  var src_file := ConvertCharSeqToCharArray(src_file_arg[..]);
  var dst_file := ConvertCharSeqToCharArray(dst_file_arg[..]);

  // Check if source file exists, if not, terminate
  var src_exists := FileStream.FileExists(src_file, env);
  if !src_exists {
    print "Error: Source file does not exist.\n";
    return;
  }

  // Check if destination file exists, if so, terminate
  var dst_exists := FileStream.FileExists(dst_file, env);
  if dst_exists {
    print "Error: Destination file already exists.\n";
    return;
  }

  // Open source file, if not possible, terminate
  var src_file_stream_ok, src_file_stream := FileStream.Open(src_file, env);
  if !src_file_stream_ok {
    print "Error: Could not open source file.\n";
    return;
  }

  // Determine source file length, if not possible, terminate
  var success_len, src_len := FileStream.FileLength(src_file, env);
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
  var ok_read := src_file_stream.Read(0 as nat32, src_buffer, 0, src_len);
  if !ok_read {
    print "Error: Unable to read from source file.\n";
    return;
  }
  // Check if the number is within the range of the array
  if src_buffer.Length == 0 {
    print "Error: Source file is empty.\n";
    return;
  }

  // Convert src_buffer to array<int>
  var src_array := ConvertByteArrayToIntArray(src_buffer);

  // Close source file
  var ok_src_close := src_file_stream.Close();
  if !ok_src_close {
    print "Error: Unable to close source file.\n";
    return;
  }


  /*
    TODO: Call the method to find the Kth smallest number and reorder the array accordingly
  */

  // Output array to destination file

  // Convert src_array to array<byte>
  var dst_buffer := ConvertIntArrayToByteArray(src_array);

  // Open destination file
  var dst_file_stream_ok, dst_file_stream := FileStream.Open(dst_file, env);
  if !dst_file_stream_ok {
    print "Error: Could not open destination file.\n";
    return;
  }

  // Ensure dst_buffer.Length is within the range of int32
  if dst_buffer.Length > 0x7FFFFFFF  {
    print "Error: Destination file size is too large.\n";
    return;
  }
  if dst_buffer.Length == 0 {
    print "Error: Empty output.\n";
    return;
  }

  // Write to destination file
  var ok_write := dst_file_stream.Write(0 as nat32, dst_buffer, 0, dst_buffer.Length as int32);
  if !ok_write {
    print "Error: Unable to write to destination file.\n";
    return;
  }

  // Close destination file
  var ok_dst_close := dst_file_stream.Close();
  if !ok_dst_close {
    print "Error: Unable to close destination file.\n";
    return;
  }

  print "File copy successful.\n";
}

predicate ValidKArgArray(a: array<char>)
reads a
{
  (forall i: int :: 0 <= i < a.Length ==> '0' <= a[i] <= '9')
  &&
  (a.Length == 1 ==> 0 < a[0] as int - 48 <= 9) 
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
requires ValidKArgArray(a)
{
    var temp: seq<int> := [];
    // Convert K char array to int
    for i := 0 to a.Length {
      temp := temp + [a[i] as int - 48];
    }
    var K_int := 0;
    for i := 0 to |temp| {
      K_int := K_int * 10 + temp[i];
    }
    b := K_int;
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
        // Initialize num to 0
        var num := 0;
        // Loop through temp's digits to form the number
        // Example: temp = [1, 2, 3]
        // num = 0
        // num = 0 * 10 + 1 = 1
        // num = 1 * 10 + 2 = 12
        // num = 12 * 10 + 3 = 123
        for j := 0 to |temp| {
          num := num * 10 + temp[j];
        }
        // Add the number to result
        result := result + [num];
        // Reset temp
        temp := [];
      }
    }
  }

  // If temp is not empty at the end of the loop, convert temp to an integer and add it to result
  if |temp| > 0 {
    var num := 0;
    for j := 0 to |temp| {
      num := num * 10 + temp[j];
    }
    result := result + [num];
    temp := [];
  }

  // Convert seq<int> to array<int>
  b := ConvertIntSeqToIntArray(result);

  return b;
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
      // Convert the number to ASCII encoded integers
      var digits: seq<byte> := [];
      // Loop through the digits of the number
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

// Method to convert a seq<char> to an array<char>
method ConvertCharSeqToCharArray(s:seq<char>) returns (a: array<char>)
  ensures a.Length == |s|
{
  a := new char[|s|];
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