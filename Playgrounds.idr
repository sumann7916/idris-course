namespace Playgrounds

plus: (n: Nat)-> (m:Nat)-> Nat
plus Z m = m 
plus (S k) m = S (Main.plus k m)


mult: (n, m : Nat)-> Nat
mult Z _ = Z
mult (S k ) m = Main.plus m (Main.mult k m)

testMult1 : (Main.mult 3 3) = 9
testMult1 = Refl

minus: (n, m: Nat)-> Nat
minus Z _ = Z
minus n Z = n
minus (S k) (S j) = Main.minus k j 

exp: (base, power: Nat)-> Nat
exp base Z = S Z
exp base (S p) = Main.mult base (Main.exp base p)

factorial: (n: Nat)-> Nat
factorial Z = S Z
factorial (S k) = Main.mult(S k) (factorial k)