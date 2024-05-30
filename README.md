# FMCS 2nd Project

## Group Members
- Pedro Barbeira
- Ricardo Ribeiro
- Tiago Marques

## Project Achievements

### Challenge 1

We were able to implement the Partition algorithm as per the requirements. The file is [Partition.dfy](./src/Challenge%201/Partition.dfy). In [main.dfy](./src/Challenge%201/main.dfy) we have a simple test of this algorithm.

We were able to prove that the algorithm terminates, that it only affects the segment between ```s``` and ```l```, not elements are added or removed and that the three regions required are created (<X, ==X, <X)


### Challenge 2

We were able to follow the [verified implementation developed by Roland Backhouse](./src/Challenge%202/Find.pdf), but we were not able to verify it. We have the file [Find.dfy](./src/Challenge%202/Find.dfy) with the implementation of ```FindKSmallest``` and [main.dfy](./src/Challenge%202/main.dfy) with a manual execution of the algorithm which demonstrates a possible execution.

We believe the problem lies in the contract specification of [Partition.dfy](./src/Challenge%201/Partition.dfy) because we are not able to prove that either the range between ```s``` and ```l``` decreases or that ```done``` is set to ```false```.

### Challenge 3

We were able to read the list from the source file and to convert it to an array of integers.
We would then call the ```FindKSmallest``` function with the array and the value of ```k``` as arguments but left it commented out because we were not able to verify the implementation. 
After, we convert the array back to ASCII bytes and write it to the destination file.

Therefore, as of now, the code only copies the list from the source file to the destination file as it is.

We were able to ensure that at the end of the execution the envrionment remains valid, that the writting to the destination file only happens in case the destination file does not already exist and the proper error handling is performed.