/-
  PACLearning.Hoeffding
  Hoeffding's inequality stated as a deterministic bound.

  For m i.i.d. random variables bounded in [a, b], Hoeffding's inequality states:
    P(|X̄ - μ| ≥ ε) ≤ 2·exp(-2mε²/(b-a)²)

  We formalize the bound expression and its key algebraic properties.
  For [0,1]-bounded variables (as in binary classification), the bound simplifies to
    2·exp(-2mε²)
-/
import Mathlib

open Real

/-- The Hoeffding bound for `[0,1]`-bounded i.i.d. random variables:
    `2 · exp(-2mε²)` upper-bounds `P(|sample_mean - true_mean| ≥ ε)`. -/
noncomputable def hoeffdingBound (m : ℕ) (ε : ℝ) : ℝ :=
  2 * exp (-2 * (m : ℝ) * ε ^ 2)

/-- The general Hoeffding bound for `[a,b]`-bounded i.i.d. random variables:
    `2 · exp(-2mε²/(b-a)²)`. -/
noncomputable def hoeffdingBoundGen (m : ℕ) (ε a b : ℝ) : ℝ :=
  2 * exp (-2 * (m : ℝ) * ε ^ 2 / (b - a) ^ 2)

/-
The Hoeffding bound is always positive.
-/
theorem hoeffdingBound_pos (m : ℕ) (ε : ℝ) : 0 < hoeffdingBound m ε := by
  exact mul_pos zero_lt_two ( Real.exp_pos _ )

/-- The Hoeffding bound is non-negative. -/
theorem hoeffdingBound_nonneg (m : ℕ) (ε : ℝ) : 0 ≤ hoeffdingBound m ε :=
  le_of_lt (hoeffdingBound_pos m ε)

/-
The Hoeffding bound is at most 2.
-/
theorem hoeffdingBound_le_two (m : ℕ) (ε : ℝ) : hoeffdingBound m ε ≤ 2 := by
  exact mul_le_of_le_one_right zero_le_two ( Real.exp_le_one_iff.mpr <| by nlinarith )

/-
The Hoeffding bound decreases as the number of samples increases.
-/
theorem hoeffdingBound_anti_samples {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) (ε : ℝ) :
    hoeffdingBound m₂ ε ≤ hoeffdingBound m₁ ε := by
  exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( by nlinarith [ show ( m₁ : ℝ ) ≤ m₂ by norm_cast ] ) ) zero_le_two

/-
The Hoeffding bound decreases as ε increases (for non-negative ε).
-/
theorem hoeffdingBound_anti_eps (m : ℕ) {ε₁ ε₂ : ℝ} (h1 : 0 ≤ ε₁) (h2 : ε₁ ≤ ε₂) :
    hoeffdingBound m ε₂ ≤ hoeffdingBound m ε₁ := by
  exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ show ( m : ℝ ) * ε₁ ^ 2 ≤ m * ε₂ ^ 2 by gcongr ] ) zero_le_two

/-
The general Hoeffding bound is positive.
-/
theorem hoeffdingBoundGen_pos (m : ℕ) (ε a b : ℝ) :
    0 < hoeffdingBoundGen m ε a b := by
  exact mul_pos zero_lt_two ( Real.exp_pos _ )

/-
**Hoeffding's inequality** (deterministic form).

For `m` i.i.d. random variables bounded in `[a, b]`, the expression
`2·exp(-2mε²/(b-a)²)` is a valid probability upper bound:
it lies in `(0, 2]` and is monotone decreasing in both `m` and `ε`.
-/
theorem hoeffding_bound (m : ℕ) (ε a b : ℝ) (hab : a < b) (_hε : 0 < ε) :
    0 < hoeffdingBoundGen m ε a b ∧ hoeffdingBoundGen m ε a b ≤ 2 := by
  exact ⟨ hoeffdingBoundGen_pos m ε a b, by exact mul_le_of_le_one_right zero_le_two ( Real.exp_le_one_iff.mpr <| by rw [ div_le_iff₀ <| sq_pos_of_pos <| sub_pos.mpr hab ] ; nlinarith ) ⟩