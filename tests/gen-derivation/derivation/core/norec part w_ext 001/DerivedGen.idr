module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX (Maybe String)

%runElab derive "X" [Generic, Meta, Show]

export
checkedGen : Fuel -> (Fuel -> Gen String) => Gen X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]