namespace Playgrounds

andb: (b1: Bool) -> (b2: Bool) -> Bool
andb True b2 = b2
andb False _ = False

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


(==): (n, m : Nat)-> Bool
(==) Z      Z       = True
(==) Z      (S k)   = False
(==) (S k)  Z       = False
(==) (S k)  (S j)   = Main.(==) k j

lte:(n, m : Nat)-> Bool
lte Z m = True
lte n Z = False
lte (S k) (S j) = lte k j

testLte1 : lte 2 2 = True
testLte1 = Refl

testLte2: lte 2 4 = True
testLte2 = Refl

testLte3: lte 4 2 = False
testLte3 = Refl

blt_nat: (n, m : Nat)-> Bool
blt_nat n m = andb (lte n m)  (not(lte m n))

test_blt_nat_1 : blt_nat 2 2 = False
test_blt_nat_1 = Refl

test_blt_nat_2: blt_nat 2 4 = True
test_blt_nat_2 = Refl

test_blt_nat_3: blt_nat 4 2 = False
test_blt_nat_3 = Refl