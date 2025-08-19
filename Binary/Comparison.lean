import Binary.Def
import Binary.Basic
import Binary.Lemmas
import Binary.AddLemmas

namespace Binary.Comparison

variable {n : ℕ} {as bs : Binary (n + 1)}

public section

-- This namespace contains inequality relations defined by comparison predicates.

-- Computes most significant bit as bool
-- This is same as right shifting an binary n - 1 times and take the only bit
-- as boolean result
@[simp]
def msb_to_bool : ∀ {n}, Binary (n + 1) → Bool
  | 0, .cons a .nil => a
  | .succ _, .cons _ as => msb_to_bool as

-- As mentioned in chapter 2-12, we can produce unsigned "less than or equal" comparison
-- predicate from expression:
--
-- (¬x | y) & ((x ⊕ y) | ¬(y - x))
@[simp]
def unsigned_ble (as bs : Binary (n + 1)) : Bool :=
  msb_to_bool ((~as || bs) && ((as ⊕ bs) || ~(bs - as)))

-- We can define ≤ᵘ with previous unsigned_ble, and make it into a
-- proposition as our comparison predicate later used in some theorems
@[simp]
def unsigned_le (as bs : Binary (n + 1)) : Prop :=
  unsigned_ble as bs = true

-- As seen in page 26, x <ᵘ y = ¬(y ≤ᵘ x)
@[simp]
def unsigned_lt (as bs : Binary (n + 1)) : Prop :=
  unsigned_ble bs as = false

-- As seen in page 26, x ≥ᵘ y = y ≤ᵘ x
@[simp]
def unsigned_ge (as bs : Binary (n + 1)) : Prop :=
  unsigned_ble bs as = true

-- As seen in page 26, x >ᵘ y = ¬(x ≤ᵘ y)
@[simp]
def unsigned_gt (as bs : Binary (n + 1)) : Prop :=
  unsigned_ble as bs = false

infix:50 " ≤ᵘ " => Comparison.unsigned_le
infix:50 " <ᵘ " => Comparison.unsigned_lt
infix:50 " ≥ᵘ " => Comparison.unsigned_ge
infix:50 " >ᵘ " => Comparison.unsigned_gt

theorem unsigned_ge_eq_symm_unsigned_le : (as ≥ᵘ bs) = (bs ≤ᵘ as) := by
  rfl

theorem unsigned_le_eq_symm_unsigned_ge : (as ≤ᵘ bs) = (bs ≥ᵘ as) := by
  rfl

theorem unsigned_gt_eq_symm_unsigned_ge : (as >ᵘ bs) = (bs <ᵘ as) := by
  rfl

theorem unsigned_lt_eq_symm_unsigned_gt : (as <ᵘ bs) = (bs >ᵘ as) := by
  rfl

theorem or_unsigned_ge_right : (as || bs) ≥ᵘ bs := by
  induction n with
  | zero =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases as'
    cases bs'
    cases a <;> cases b <;> simp
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases a <;> cases b <;> simp_all <;> (try rw [AddLemmas.rca_carry_trans_inc_right])
      <;> rw [← Lemmas.nneg_eq_bneg_inc, ih]

theorem or_unsigned_ge_left : (as || bs) ≥ᵘ as := by
  induction n with
  | zero =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases as'
    cases bs'
    cases a <;> cases b <;> simp
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases a <;> cases b <;> simp_all <;> (try rw [AddLemmas.rca_carry_trans_inc_right])
      <;> rw [← Lemmas.nneg_eq_bneg_inc, ih]

theorem and_unsigned_le_right : (as && bs) ≤ᵘ bs := by
  induction n with
  | zero =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases as'
    cases bs'
    cases a <;> cases b <;> simp
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases a <;> cases b <;> simp_all <;> (try rw [AddLemmas.rca_carry_trans_inc_right])
      <;> rw [← Lemmas.nneg_eq_bneg_inc, ih]

theorem and_unsigned_le_left : (as && bs) ≤ᵘ as := by
  induction n with
  | zero =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases as'
    cases bs'
    cases a <;> cases b <;> simp
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases a <;> cases b <;> simp_all <;> (try rw [AddLemmas.rca_carry_trans_inc_right])
      <;> rw [← Lemmas.nneg_eq_bneg_inc, ih]

end
end Binary.Comparison
