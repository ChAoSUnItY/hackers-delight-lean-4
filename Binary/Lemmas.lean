import Binary.Def
import Binary.Basic

-- Here are some important theorems but yet not so critical, this namespace is meant
-- to put some common lemmas together without spilling everywhere. If not introduced
-- or not meant to be in any major part of lemmas, we would put here to keep clean.

namespace Binary.Lemmas

variable {n : ℕ} {a b c c' : Bit} {as' bs' : Binary n.succ} {as bs cs : Binary n}

public section

-- A gernerl tactic to simplify out base case of 2 binaries induction
syntax "simp_nil" term : tactic
macro_rules
| `(tactic| simp_nil $as $bs $cs) => `(tactic| cases ($as); cases ($bs); cases ($cs); simp)
| `(tactic| simp_nil $as $bs) => `(tactic| cases ($as); cases ($bs); simp)
| `(tactic| simp_nil $as) => `(tactic| cases ($as); simp)

-- Simple tactic when proving theorem that is only expanded by structure of
-- Binary
syntax "induction_fast" term : tactic
macro_rules
| `(tactic| induction_fast $as $bs $cs) => `(tactic|
  induction n with
  | zero => simp_nil ($as) ($bs) ($cs)
  | succ _ ih =>
    cases ($as) with | cons a _
    cases ($bs) with | cons b _
    cases ($cs) with | cons c _
    cases a <;> cases b <;> cases c <;> simp <;> rw [ih]
  )
| `(tactic| induction_fast $as $bs) => `(tactic|
  induction n with
  | zero => simp_nil ($as) ($bs)
  | succ _ ih =>
    cases ($as) with | cons a _
    cases ($bs) with | cons b _
    cases a <;> cases b <;> simp <;> rw [ih]
  )
| `(tactic| induction_fast $as) => `(tactic|
  induction n with
  | zero => simp_nil ($as)
  | succ _ ih => cases ($as) with | cons a _; cases a <;> simp <;> rw [ih]
  )

-- bitwise negation properties

-- negates an all-flase-bit binary gives an all-true-bit binary
@[simp]
theorem bneg_ones_eq_zeros : (~ (ones n)) = zeros n := by
  induction n with
  | zero => rfl
  | succ =>
    simp
    congr

@[simp]
theorem bneg_zeros_eq_ones : (~ (zeros n)) = ones n := by
  induction n with
  | zero => rfl
  | succ =>
    simp
    congr

-- apply negates twice on binary gives the exact binary passed in
@[simp]
theorem of_bneg_bneg : (~ (~ as)) = as := by
  induction n with
  | zero => simp_nil as
  | succ n' ih =>
    cases as with | cons a as'
    simp
    exact ih

-- increment / decrement properties

@[simp]
theorem inc_ones_eq_zero : inc (ones n) = zeros n := by
  induction n with
  | zero => rfl
  | succ =>
    simp
    congr

@[simp]
theorem of_inc_dec : inc (dec as) = as := by
  induction as with
  | nil => rfl
  | cons a _ => cases a <;> simp; congr

@[simp]
theorem of_dec_inc : dec (inc as) = as := by
  induction as with
  | nil => rfl
  | cons a _ => cases a <;> simp; congr

theorem inc_dec_swap : inc (dec as) = dec (inc as) := by
  induction as with
  | nil => rfl
  | cons a _ => cases a <;> simp

theorem inc_inj : inc as = inc bs ↔ as = bs := by
  constructor
  · intro h
    apply congrArg dec at h
    repeat rw [of_dec_inc] at h
    exact h
  · intro h
    rw [h]

theorem dec_inj : dec as = dec bs ↔ as = bs := by
  constructor
  · intro h
    apply congrArg inc at h
    repeat rw [of_inc_dec] at h
    exact h
  · intro h
    rw [h]

-- numerical negation properties

@[simp]
theorem of_nneg_nneg : -(- as) = as := by
  induction as with
  | nil => rfl
  | cons a _ => cases a <;> simp ; congr

theorem nneg_eq_bneg_inc : -as = inc (~as) := by
  rfl

-- bitwise or properties

@[simp]
theorem or_identity : (as || as) = as := by
  induction_fast as

@[simp]
theorem or_zeros_eq_self : (as || zeros n) = as := by
  induction_fast as

@[simp]
theorem zeros_or_eq_self : (as || zeros n) = as := by
  induction_fast as

@[simp]
theorem or_ones_eq_ones : (as || ones n) = ones n := by
  induction_fast as

@[simp]
theorem ones_or_eq_ones : (ones n || as) = ones n := by
  induction_fast as

theorem or_comm : (as || bs) = (bs || as) := by
  induction_fast as bs

theorem or_assoc : (as || (bs || cs)) = ((as || bs) || cs) := by
  induction_fast as bs cs

@[simp]
theorem neg_or_self_eq_ones : (~as || as) = ones n := by
  induction_fast as

@[simp]
theorem self_or_neg_eq_ones : (as || ~as) = ones n := by
  induction_fast as

-- bitwise and properties

@[simp]
theorem and_identity : (as && as) = as := by
  induction_fast as

@[simp]
theorem and_zeros_eq_zeros : (as && zeros n) = zeros n := by
  induction_fast as

@[simp]
theorem zeros_and_eq_zeros : (zeros n && as) = zeros n := by
  induction_fast as

@[simp]
theorem and_ones_eq_self : (as && ones n) = as := by
  induction_fast as

@[simp]
theorem ones_and_eq_self : (ones n && as) = as := by
  induction_fast as

theorem and_comm : (as && bs) = (bs && as) := by
  induction_fast as bs

theorem and_assoc : (as && (bs && cs)) = ((as && bs) && cs) := by
  induction n with
  | zero => simp_nil as bs cs
  | succ _ ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases cs with | cons c cs'
    cases a <;> cases b <;> cases c <;> simp <;> rw [ih, and_comm]

-- bitwise xor properties

@[simp]
theorem xor_zeros_eq_self : (as ⊕ zeros n) = as := by
  induction_fast as

@[simp]
theorem zeros_xor_eq_self : (zeros n ⊕ as) = as := by
  induction_fast as

@[simp]
theorem xor_self_eq_zeros : (as ⊕ as) = zeros n := by
  induction_fast as

theorem xor_comm : (as ⊕ bs) = (bs ⊕ as) := by
  induction_fast as bs

theorem xor_assoc : (as ⊕ (bs ⊕ cs)) = ((as ⊕ bs) ⊕ cs) := by
  induction n with
  | zero => simp_nil as bs cs
  | succ _ ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases cs with | cons c cs'
    cases a <;> cases b <;> cases c <;> simp <;> rw [ih, xor_comm]

end
end Binary.Lemmas
