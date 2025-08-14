import Binary.Def
import Binary.Basic

-- Here are some important theorems but yet not so critical, this namespace is meant
-- to put some common lemmas together without spilling everywhere. If not introduced
-- or not meant to be in any major part of lemmas, we would put here to keep clean.

namespace Binary.Lemmas

variable {n : ℕ} {a b c c' : Bit} {as' bs' : Binary n.succ} {as bs cs : Binary n}

public section

open Binary.Lemmas

-- bitwise negation properties

-- negates an all-flase-bit binary gives an all-true-bit binary
@[simp]
theorem bneg_ones_eq_zeros : bneg (ones n) = zeros n := by
  induction n with
  | zero => rfl
  | succ =>
    simp
    congr

@[simp]
theorem bneg_zeros_eq_ones : bneg (zeros n) = ones n := by
  induction n with
  | zero => rfl
  | succ =>
    simp
    congr

-- apply negates twice on binary gives the exact binary passed in
@[simp]
theorem of_bneg : bneg (bneg as) = as := by
  induction n with
  | zero => cases as; simp
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

@[simp]
theorem inc_dec_swap : inc (dec as) = dec (inc as) := by
  induction as with
  | nil => rfl
  | cons a _ => cases a <;> simp

-- numerical negation properties

@[simp]
theorem of_nneg_nneg : nneg (nneg as) = as := by
  induction as with
  | nil => rfl
  | cons a _ => cases a <;> simp ; congr

end
end Binary.Lemmas
