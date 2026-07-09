# pac-learning-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](PACLearning)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20480664.svg)](https://doi.org/10.5281/zenodo.20480664)

**pac-learning-lean: Formal PAC Learning Bounds in Lean 4**

Lean 4 formal proofs for finite-class PAC learning bounds. The development
models boolean hypotheses over finite domains, empirical risk, true risk values
in `[0,1]`, Hoeffding-style exponential bounds, a finite union bound, and the
standard finite-hypothesis-class sample-complexity inequality

```text
m >= log(2 |H| / delta) / (2 epsilon^2).
```

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`).

## Setting

The library works with a finite hypothesis class and binary classification.
For `n` features, a hypothesis is represented as

```lean
abbrev BooleanHypothesis (n : ℕ) := Fin n -> Bool
```

The empirical risk of a hypothesis on `m` labelled samples is the fraction of
sample points where the predicted label differs from the observed label.
Hoeffding's inequality is represented by the deterministic bound expression
`2 * exp (-2 * m * epsilon^2)`, and the PAC failure probability after a union
bound over a class of size `cardH` is `cardH * hoeffdingBound m epsilon`.

The main sample-complexity theorem proves that, under the stated positivity and
logarithm hypotheses,

```lean
Real.log (2 * (cardH : ℝ) / δ) / (2 * ε ^ 2) <= (m : ℝ)
```

implies `pacFailureBound cardH m ε <= δ`.

## Theorem Inventory

| Module | Name | Statement |
| --- | --- | --- |
| `PACLearning.Defs` | `EmpiricalRisk_nonneg` | `0 ≤ EmpiricalRisk m h x y` |
| `PACLearning.Defs` | `EmpiricalRisk_le_one` | `EmpiricalRisk m h x y ≤ 1` when `0 < m` |
| `PACLearning.Hoeffding` | `hoeffdingBound_pos` | `0 < hoeffdingBound m ε` |
| `PACLearning.Hoeffding` | `hoeffdingBound_nonneg` | `0 ≤ hoeffdingBound m ε` |
| `PACLearning.Hoeffding` | `hoeffdingBound_le_two` | `hoeffdingBound m ε ≤ 2` |
| `PACLearning.Hoeffding` | `hoeffdingBound_anti_samples` | `hoeffdingBound m₂ ε ≤ hoeffdingBound m₁ ε` when `m₁ ≤ m₂` |
| `PACLearning.Hoeffding` | `hoeffdingBound_anti_eps` | `hoeffdingBound m ε₂ ≤ hoeffdingBound m ε₁` when `0 ≤ ε₁` and `ε₁ ≤ ε₂` |
| `PACLearning.Hoeffding` | `hoeffdingBoundGen_pos` | `0 < hoeffdingBoundGen m ε a b` |
| `PACLearning.Hoeffding` | `hoeffding_bound` | `0 < hoeffdingBoundGen m ε a b ∧ hoeffdingBoundGen m ε a b ≤ 2` when `a < b` and `0 < ε` |
| `PACLearning.PACBound` | `union_bound_finite` | `p_union ≤ S.card * b` from `p_union ≤ ∑ i ∈ S, p i` and pointwise `p i ≤ b` |
| `PACLearning.PACBound` | `pac_generalisation_bound` | `pacFailureBound cardH m (sqrt (log (2 * cardH / δ) / (2 * m))) ≤ δ` under the stated hypotheses |
| `PACLearning.PACBound` | `pac_sample_complexity` | `pacFailureBound cardH m ε ≤ δ` if `m ≥ log(2 * cardH / δ) / (2 * ε^2)` under the stated hypotheses |

## Modules

- `PACLearning.Defs`: boolean hypotheses, empirical risk, true risk, and finite hypothesis classes.
- `PACLearning.Hoeffding`: Hoeffding bound expressions and monotonicity properties.
- `PACLearning.PACBound`: finite union bound, PAC failure bound, generalisation bound, and sample complexity bound.

## Build

```bash
lake build
rg "sorry|admit" PACLearning/
```

The library targets Lean 4.28.0 and Mathlib v4.28.0.

## Author

Ben Cassie
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
