/-
  PACLearning.Defs
  Core definitions for PAC learning theory.
-/
import Mathlib

open Finset

/-- A boolean hypothesis maps `n` input features to a boolean prediction. -/
abbrev BooleanHypothesis (n : ℕ) := Fin n → Bool

section EmpiricalRisk

variable {n : ℕ}

/-- Empirical risk of hypothesis `h` on `m` samples `(x, y)`:
    the fraction of samples where `h(xᵢ) ≠ yᵢ`. -/
noncomputable def EmpiricalRisk (m : ℕ) (h : BooleanHypothesis n)
    (x : Fin m → Fin n) (y : Fin m → Bool) : ℝ :=
  ((Finset.univ.filter fun i : Fin m => h (x i) ≠ y i).card : ℝ) / (m : ℝ)

theorem EmpiricalRisk_nonneg (m : ℕ) (h : BooleanHypothesis n)
    (x : Fin m → Fin n) (y : Fin m → Bool) :
    0 ≤ EmpiricalRisk m h x y := by
  unfold EmpiricalRisk
  positivity

theorem EmpiricalRisk_le_one {m : ℕ} (hm : 0 < m) (h : BooleanHypothesis n)
    (x : Fin m → Fin n) (y : Fin m → Bool) :
    EmpiricalRisk m h x y ≤ 1 := by
  exact div_le_one_of_le₀ ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by simp ) ) ( by positivity )

end EmpiricalRisk

/-- True risk of a hypothesis: an abstract probability of misclassification, in [0,1].
    Since the true distribution is unknown, we model this as a bundled real number
    with proof that it lies in the unit interval. -/
structure TrueRisk where
  /-- The risk value -/
  risk : ℝ
  /-- Risk is non-negative -/
  risk_nonneg : 0 ≤ risk
  /-- Risk is at most 1 -/
  risk_le_one : risk ≤ 1

/-- A finite hypothesis class with positive cardinality. -/
class HypothesisClass (H : Type*) extends Fintype H where
  /-- The hypothesis class is non-empty -/
  card_pos : 0 < Fintype.card H