---- MODULE Name ----
EXTENDS Nat, Bit

VARIABLE A
VARIABLES A,B,C

CONSTANT  c
CONSTANTS c, f(_, _), -_, [] _, <> _, _ -| _, _??_
RECURSIVE r(_,_,_)

HIDE MODULE Number

USE ONLY Nat.N DEFS x

[] X == ~X
f(x,y) == x + y
abc == A

===========