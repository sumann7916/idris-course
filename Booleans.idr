namespace Booleans

data CustomBool: Type where
    True: CustomBool
    False: CustomBool

not: (b: CustomBool) -> CustomBool
not True = False
not False = True

andb: (b1: CustomBool) -> (b2: CustomBool) -> CustomBool
andb True b2 = b2
andb False _ = False

orb: (b1: CustomBool) -> (b2: CustomBool) -> CustomBool
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

nandb: (b1: CustomBool) -> (b2: CustomBool) -> CustomBool
nandb True True = False
nandb True False = True
nandb False _ = True

test_nandb1: nandb True False = True
test_nandb1 = Refl