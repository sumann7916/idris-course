namespace Booleans

not: (b: Bool) -> Bool
not True = False
not False = True

andb: (b1: Bool) -> (b2: Bool) -> Bool
andb True b2 = b2
andb False _ = False


orb: (b1: Bool) -> (b2: Bool) -> Bool
orb True _ = True
orb False b2 = b2

testOrb1: orb True False = True
testOrb1 = Refl

testOrb2: orb False False = False
testOrb2 = Refl

testOrb3: orb False True = True
testOrb3 = Refl

testOrb4: orb True True = True
testOrb4 = Refl

nandb: (b1: Bool) -> (b2: Bool) -> Bool
nandb True True = False
nandb True False = True
nandb False _ = True

test_nandb1: nandb True False = True
test_nandb1 = Refl

test_nandb2: nandb True True = False
test_nandb2 = Refl

test_nandb3: nandb False False = True
test_nandb3 = Refl

test_nandb4: nandb False True = True
test_nandb4 = Refl


andb3 : Bool -> Bool -> Bool -> Bool
andb3 True True True = True
andb3 False False False = False
andb3 _ _ _ = False

test_andb31: (andb3 True True True) = True
test_andb31 = Refl

test_andb32 : (andb3 False True True) = False
test_andb32 = Refl

test_andb33 : (andb3 True False True) = False
test_andb33 = Refl

test_andb34 : (andb3 True True False) = False
test_andb34 = Refl