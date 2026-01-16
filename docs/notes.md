# Coding conventions
## Intrinsics vs functions/procedures
As much as possible I've kept away from intrinsics, favouring smaller functions and procedures with possibly type checks etc. Rule of thumb is if it is something that I would want to enter at the command line then it is an intrinsic or if it needs to be accessed from another file. Another rule of thumb is if giving a name to a repeatedly used bit of code that is somewhat opaque makes life easier then it might become an intrinsic. Even for small things like GetPrime(P) which simply returns the prime divisor of P they are an intrinsic because although it is unlikely I would need it myself across the file it is a very quick and readable way of obtaining it when writing code. 
## File structure
Functions and procedures go at the start so it is easy to see what is only accessible locally in that file.
