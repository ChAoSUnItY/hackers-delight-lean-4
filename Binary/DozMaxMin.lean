import Init.Data.Nat
import Binary.Def
import Binary.Basic
import Binary.Lemmas
import Binary.AddLemmas
import Binary.DeMorganLemmas
import Binary.Comparison

-- Here, we formalize functions and theorems defined in chapter 2-19 "Doz, Max, Min".

namespace Binary.DozMaxMin

variable {n : ℕ} {as bs : Binary (n + 1)}

public section

@[simp]
def dozu (as bs : Binary (n + 1)) : Binary (n + 1) :=
  match Comparison.unsigned_ble as bs with
  | false => as - bs
  | true => zeros (n + 1)

@[simp]
def maxu (as bs : Binary (n + 1)) : Binary (n + 1) :=
  bs + dozu as bs

-- by definition, maxu(x, y) must produce either x or y as result
theorem maxu_eq (as bs : Binary (n + 1)) : (maxu as bs = as) ∨ (maxu as bs = bs) := by
  simp [-Comparison.unsigned_ble]
  by_cases h : Comparison.unsigned_ble as bs
  · rw [h]
    simp
    rw [← zeros_cons, AddLemmas.add_zero_eq_id]
    exact Or.inr rfl
  · rw [Bool.not_eq_true] at h
    rw [h]
    simp
    rw [
      AddLemmas.add_comm,
      ← AddLemmas.add_assoc,
      AddLemmas.nneg_self_add_eq_zeros,
      AddLemmas.add_zero_eq_id
    ]
    exact Or.symm (Or.inr rfl)

@[simp]
def minu (as bs : Binary (n + 1)) : Binary (n + 1) :=
  as - dozu as bs

-- by definition, minu(x, y) must produce either x or y as result
theorem minu_eq (as bs : Binary (n + 1)) : (minu as bs = as) ∨ (minu as bs = bs) := by
  simp [-Comparison.unsigned_ble]
  by_cases h : Comparison.unsigned_ble as bs
  · rw [h]
    simp
    rw [← zeros_cons, AddLemmas.add_zero_eq_id]
    exact Or.symm (Or.inr rfl)
  · rw [Bool.not_eq_true] at h
    rw [h]
    simp
    rw [
      DeMorganLemmas.nneg_distrib,
      Lemmas.of_nneg_nneg,
      AddLemmas.add_assoc,
      AddLemmas.add_nneg_self_eq_zeros,
      AddLemmas.zero_add_eq_id
    ]
    exact Or.inr rfl

end
end Binary.DozMaxMin
