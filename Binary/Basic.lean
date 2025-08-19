import Init.Data.Nat
import Binary.Def

namespace Binary

variable {n : ℕ} {a b : Bit} {as bs : Binary n}

public section

-- Helper functions that creates commonly used binary values
def zeros : (n : ℕ) → Binary n
  | 0 => .nil
  | .succ n => false ::b zeros n

@[simp]
theorem zeros_nil : zeros 0 = nil :=
  by rfl

@[simp]
theorem zeros_cons : zeros n.succ = false ::b zeros n :=
  by rfl

def ones : (n : ℕ) → Binary n
  | 0 => .nil
  | .succ n => true ::b ones n

@[simp]
theorem ones_nil : ones 0 = nil :=
  by rfl
@[simp]
theorem ones_cons : ones n.succ = true ::b ones n :=
  by rfl

def one : (n : ℕ) → Binary n
  | 0 => .nil
  | .succ n => true ::b zeros n

@[simp]
theorem one_nil : one 0 = nil :=
  by rfl

@[simp]
theorem one_cons : one n.succ = true ::b zeros n :=
  by rfl

-- Unary operations

-- Bitwise negation, false bits are flipped to true and vice versa
def bneg {n : ℕ} : Binary n → Binary n
  | .nil => .nil
  | false ::b as => true ::b bneg as
  | true ::b as => false ::b bneg as

@[simp]
theorem bneg_nil : bneg nil = nil :=
  by rfl

@[simp]
theorem bneg_cons_true : bneg (true ::b as) = false ::b bneg as :=
  by rfl

@[simp]
theorem bneg_cons_false : bneg (false ::b as) = true ::b bneg as :=
  by rfl

@[simp]
theorem bneg_cons : bneg (a ::b as) = (!a) ::b bneg as :=
  by cases a <;> simp

def inc {n} : Binary n → Binary n
  | .nil => .nil
  | false ::b as => true ::b as
  | true ::b as => false ::b inc as


@[simp]
theorem inc_nil : inc nil = nil :=
  by rfl

@[simp]
theorem inc_cons_true : inc (true ::b as) = false ::b inc as :=
  by rfl

@[simp]
theorem inc_cons_false : inc (false ::b as) = true ::b as :=
  by rfl

@[simp]
def dec {n : ℕ} : Binary n → Binary n
  | .nil => .nil
  | false ::b as => true ::b dec as
  | true ::b as => false ::b as

@[simp]
theorem dec_nil : dec nil = nil :=
  by rfl

@[simp]
theorem dec_cons_true : dec (true ::b as) = false ::b as :=
  by rfl

@[simp]
theorem dec_cons_false : dec (false ::b as) = true ::b dec as :=
  by rfl

-- Numerical negation, performs 2's complement in this case
def nneg (as : Binary n) : Binary n
  := inc (bneg as)

@[simp]
theorem nneg_nil : nneg nil = nil :=
  by rfl

@[simp]
theorem nneg_cons_true : nneg (true ::b as) = true ::b (bneg as) := by
  rw [nneg.eq_def]
  simp

@[simp]
theorem nneg_cons_false : nneg (false ::b as) = false ::b inc (bneg as) := by
  rw [nneg.eq_def]
  simp

-- Binary operations
/-- XNOR is equals to ≡ described in Hacker's Delight -/
def xnor {n : ℕ} : Binary n → Binary n → Binary n
  | .nil, .nil => .nil
  | a ::b as, b ::b bs => (a == b) ::b (xnor as bs)

@[simp]
theorem xnor_nil : xnor nil nil = nil :=
  by rfl

@[simp]
theorem xnor_cons : xnor (a ::b as) (b ::b bs) = (a == b) ::b (xnor as bs) :=
  by rfl

def or {n : ℕ} : Binary n → Binary n → Binary n
  | .nil, .nil => .nil
  | a ::b as, b ::b bs => (a ∨ b) ::b (or as bs)

@[simp]
theorem or_nil : or nil nil = nil :=
  by rfl

@[simp]
theorem or_cons : or (a ::b as) (b ::b bs) = (a ∨ b) ::b (or as bs) :=
  by rfl

def and {n : ℕ} : Binary n → Binary n → Binary n
  | .nil, .nil => .nil
  | a ::b as, b ::b bs => (a ∧ b) ::b (and as bs)

@[simp]
theorem and_nil : and nil nil = nil :=
  by rfl

@[simp]
theorem and_cons : and (a ::b as) (b ::b bs) = (a ∧ b) ::b (and as bs) :=
  by rfl

def xor {n} : Binary n → Binary n → Binary n
  | .nil, .nil => .nil
  | a ::b as, b ::b bs => (a ^^ b) ::b (xor as bs)

@[simp]
theorem xor_nil : xor nil nil = nil :=
  by rfl

@[simp]
theorem xor_cons : xor (a ::b as) (b ::b bs) = (a ^^ b) ::b (xor as bs) :=
  by rfl

@[simp]
def rca {n : ℕ} : (as bs : Binary n) → (c : Bit) → Binary n
  | .nil, .nil, _ => .nil
  | (a ::b as), (b ::b bs), c => (a ^^ b ^^ c) ::b rca as bs ((a ∧ b) ∨ (c ∧ (a ^^ b)))

-- Operators
--
-- To avoid some parsing issues, and some context issues caused by operator definition,
-- we choose to adapt imperative porogramming languages' tradition, which is C in this
-- case.
--
-- TODO: Maybe unify style?

notation:100 "~" rhs:100 => Binary.bneg rhs

notation:100 "-" rhs:100 => Binary.nneg rhs

notation:65 lhs:65 " + " rhs:66 => Binary.rca lhs rhs false

notation:65 lhs:65 " - " rhs:66 => Binary.rca lhs (-rhs) false

notation:30 lhs:31 " || " rhs:30 => Binary.or lhs rhs

notation:35 lhs:36 " && " rhs:35 => Binary.and lhs rhs

notation:40 lhs:41 " ⊕ " rhs:40 => Binary.xor lhs rhs

notation:41 lhs:41 " ⊙ " rhs:40 => Binary.xnor lhs rhs

end
end Binary
