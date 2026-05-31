/-
  PACLearning.PACBound
  PAC learning generalisation bounds via Hoeffding's inequality and the union bound.
-/
import Mathlib
import PACLearning.Defs
import PACLearning.Hoeffding

open Real Finset BigOperators

/-! ## Union Bound -/

/-
**Union bound** for a finite collection of events.
    If `p_union` is at most the sum of individual probabilities `p i`,
    and each `p i ≤ b`, then `p_union ≤ |S| * b`.
    This captures: `P(⋃ᵢ Aᵢ) ≤ Σᵢ P(Aᵢ) ≤ |S| · b`.
-/
theorem union_bound_finite {ι : Type*} (S : Finset ι) (p : ι → ℝ) (b : ℝ)
    (hp : ∀ i ∈ S, p i ≤ b)
    (p_union : ℝ) (h_sub : p_union ≤ ∑ i ∈ S, p i) :
    p_union ≤ S.card * b := by
  exact h_sub.trans ( le_trans ( Finset.sum_le_sum hp ) ( by simp +decide ) )

/-! ## PAC Failure Bound -/

/-- The PAC failure probability bound: after applying the union bound over a
    hypothesis class of size `cardH`, each with Hoeffding bound, the total
    failure probability is at most `cardH * 2 * exp(-2mε²)`. -/
noncomputable def pacFailureBound (cardH : ℕ) (m : ℕ) (ε : ℝ) : ℝ :=
  (cardH : ℝ) * hoeffdingBound m ε

/-! ## PAC Generalisation Bound -/

/-
**PAC generalisation bound** (deterministic algebraic form).

With `m` samples, for a hypothesis class of size `cardH`, setting
  `ε = √(log(2 · cardH / δ) / (2m))`
yields a failure probability bound of at most `δ`.

Formally: if `cardH ≥ 1`, `δ > 0`, `m ≥ 1`, and `2 * cardH / δ > 1` (ensuring
the logarithm is positive), then
  `cardH * 2 * exp(-2m · (√(log(2·cardH/δ)/(2m)))²) ≤ δ`.
-/
theorem pac_generalisation_bound {cardH : ℕ} {m : ℕ} {δ : ℝ}
    (hH : 1 ≤ cardH) (hm : 1 ≤ m) (hδ : 0 < δ)
    (hlog : 1 < 2 * (cardH : ℝ) / δ) :
    pacFailureBound cardH m (Real.sqrt (Real.log (2 * (cardH : ℝ) / δ) / (2 * (m : ℝ)))) ≤ δ := by
  unfold pacFailureBound hoeffdingBound;
  rw [ Real.sq_sqrt ( div_nonneg ( Real.log_nonneg hlog.le ) ( by positivity ) ) ];
  convert mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| show -Real.log ( ( 2 * cardH ) / δ ) ≤ -Real.log ( ( 2 * cardH ) / δ ) from le_rfl ) ( by positivity : ( 0 : ℝ ) ≤ cardH * 2 ) using 1 ; ring_nf;
  · norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hm ) ];
  · rw [ Real.exp_neg, Real.exp_log ( by positivity ), mul_comm ] ; ring_nf ; norm_num [ hδ.ne' ];
    exact mul_inv_cancel₀ ( by positivity )

/-
**PAC sample complexity** (deterministic algebraic form).

To achieve `ε`-accuracy with failure probability at most `δ`, it suffices
to have `m ≥ log(2 · |H| / δ) / (2ε²)` samples.

Formally: if `cardH ≥ 1`, `ε > 0`, `δ > 0`, `2 * cardH / δ > 1`, and
`(m : ℝ) ≥ log(2 * cardH / δ) / (2 * ε²)`, then
`cardH * 2 * exp(-2mε²) ≤ δ`.
-/
theorem pac_sample_complexity {cardH : ℕ} {m : ℕ} {ε δ : ℝ}
    (hH : 1 ≤ cardH) (hε : 0 < ε) (hδ : 0 < δ)
    (hlog : 1 < 2 * (cardH : ℝ) / δ)
    (hm : Real.log (2 * (cardH : ℝ) / δ) / (2 * ε ^ 2) ≤ (m : ℝ)) :
    pacFailureBound cardH m ε ≤ δ := by
  -- From hm: (m : ℝ) ≥ log(2*cardH/δ) / (2*ε²), so 2*ε²*(m : ℝ) ≥ log(2*cardH/δ) (multiply both sides by 2*ε² > 0).
  have h_exp : Real.exp (-2 * (m : ℝ) * ε ^ 2) ≤ Real.exp (-Real.log (2 * (cardH : ℝ) / δ)) := by
    exact Real.exp_le_exp.mpr ( by rw [ div_le_iff₀ ( by positivity ) ] at hm; nlinarith );
  unfold pacFailureBound hoeffdingBound;
  rw [ Real.exp_neg, Real.exp_log ( by positivity ) ] at h_exp ; rw [ inv_eq_one_div, le_div_iff₀ ( by positivity ) ] at h_exp ; nlinarith [ mul_div_cancel₀ ( 2 * ( cardH : ℝ ) ) hδ.ne' ] ;