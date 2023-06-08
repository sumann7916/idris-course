module Main
namespace Numbers

pred: (n: Nat)-> Nat
pred Z = Z
pred (S k) = k

minusTwo: (n: Nat)-> Nat
minusTwo Z = Z
minusTwo (S Z) = Z
minusTwo (S(S k)) = k

minusThree: (n: Nat)-> Nat
minusThree Z = Z
minusThree (S Z) = Z
minusThree (S(S Z)) = Z
minusThree (S(S(S k))) = k

evenb: (n: Nat)-> Bool
evenb Z         =True
evenb (S Z)     =False
evenb(S(S k))   = evenb k

oddb: (n:Nat)-> Bool
oddb n = not (evenb n)

testOddb1: oddb 3 = True
testOddb1= Refl

testOddb2: oddb 4 = False
testOddb2= Refl