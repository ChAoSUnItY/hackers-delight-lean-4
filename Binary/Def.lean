import Init.Data.Nat
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Defs
import Mathlib.Data.Vector.Zip

abbrev Bit := Bool

inductive Binary : Nat → Type where
  | nil : Binary 0
  | cons : Bit → {n : ℕ} → Binary n → Binary (n + 1)
  deriving Repr

infixr:67 " ::b " => Binary.cons
