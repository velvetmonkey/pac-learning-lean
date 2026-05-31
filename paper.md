# pac-learning-lean: Formal PAC Learning Bounds in Lean 4

Ben Cassie  
ORCID: 0009-0004-1899-7627  
2026-05-31

## Abstract

`pac-learning-lean` is a Lean 4 / Mathlib library formalising finite-class PAC learning bounds in a deterministic algebraic form. The library defines boolean hypotheses on finite domains, empirical risk, true risk values in `[0,1]`, Hoeffding bound expressions, monotonicity facts for those bounds, a finite union bound, a PAC failure bound, and the standard sample complexity implication `m >= log(2|H|/delta)/(2 epsilon^2)`. The proof method combines Hoeffding's exponential bound with the union bound and elementary logarithmic algebra. The development is machine-checked in Lean 4 with zero `sorry`, zero `admit`, and standard Lean/Mathlib axioms only.

## 1. Introduction

PAC learning gives finite-sample guarantees for learning from random examples. In the finite-hypothesis-class setting, a standard argument bounds the probability that any hypothesis has a large empirical-to-true-risk deviation. Hoeffding's inequality controls one hypothesis, and the union bound lifts the estimate to the entire class.

The Lean repository formalises the deterministic algebraic part of this argument. It does not construct a probability space of samples or prove Hoeffding's inequality from measure theory. Instead, it defines the Hoeffding expression used as a probability upper bound and verifies the finite-class algebra that yields the usual sample complexity formula.

## 2. Mathematical Setting

`PACLearning/Defs.lean` defines

```text
BooleanHypothesis n = Fin n -> Bool.
```

For `m` labelled samples, empirical risk is the fraction of indices where the hypothesis prediction differs from the label. Theorems `EmpiricalRisk_nonneg` and `EmpiricalRisk_le_one` prove that this empirical risk lies in `[0,1]` when `m > 0`. `TrueRisk` bundles a real risk value with proofs that it lies in `[0,1]`, and `HypothesisClass` packages a finite nonempty class.

`Hoeffding.lean` defines

```text
hoeffdingBound m epsilon =
  2 * exp (-2 * m * epsilon^2)
```

and the general bounded-interval version `hoeffdingBoundGen`.

## 3. Main Theorems

The Hoeffding module proves `hoeffdingBound_pos`, `hoeffdingBound_nonneg`, `hoeffdingBound_le_two`, monotonicity in sample size through `hoeffdingBound_anti_samples`, monotonicity in the accuracy parameter through `hoeffdingBound_anti_eps`, and `hoeffding_bound`, which states that the general bound lies in `(0,2]` when `a < b` and `epsilon > 0`.

`PACBound.lean` proves the finite union bound:

```text
union_bound_finite:
  p_union <= sum_{i in S} p_i
  and p_i <= b
  imply p_union <= |S| * b.
```

It defines

```text
pacFailureBound cardH m epsilon =
  cardH * hoeffdingBound m epsilon.
```

The theorem `pac_generalisation_bound` proves that choosing

```text
epsilon = sqrt(log(2 * cardH / delta) / (2 * m))
```

makes the finite-class failure bound at most `delta`. The theorem `pac_sample_complexity` proves the sample-complexity implication:

```text
log(2 * cardH / delta) / (2 * epsilon^2) <= m
------------------------------------------------
pacFailureBound cardH m epsilon <= delta.
```

## 4. Proof Sketch

The proof starts with the bound for a single hypothesis, represented by `hoeffdingBound`. The finite union bound says that the probability of any bad event is at most the sum of the individual probabilities, and if each bad event is bounded by the same `b`, then the total is at most `|H| * b`.

The main algebra substitutes the Hoeffding expression and rearranges exponentials and logarithms. The condition

```text
m >= log(2 * |H| / delta) / (2 * epsilon^2)
```

implies `exp(-2m epsilon^2) <= exp(-log(2|H|/delta))`. After simplifying `exp(-log x) = 1/x`, the factor `|H| * 2` cancels with `2|H|/delta`, leaving the desired bound `delta`.

## 5. Relation to Sibling Libraries

`pac-learning-lean` is closest to the online and stochastic members of the suite. `online-learning-lean` formalises adversarial regret bounds for FTRL, while `sgd-lean`, DOI `10.5281/zenodo.20475583`, studies bounded-noise first-order convergence. `mirror-descent-lean`, DOI `10.5281/zenodo.20475033`, supplies a related Bregman proof pattern. The present repository contributes the finite-class statistical-learning calculation based on Hoeffding and the union bound.

## 6. Conclusion

`pac-learning-lean` provides a Lean 4 formalisation of the finite-hypothesis PAC sample complexity algebra. It defines empirical and true risk interfaces, Hoeffding bound expressions, finite union bound reasoning, and the standard `log(2|H|/delta)/(2 epsilon^2)` sample bound. Future work could connect this algebraic layer to Mathlib probability spaces, independent samples, measurable hypotheses, and full proofs of concentration inequalities.

## References

Valiant, L. G. (1984). *A theory of the learnable*. Communications of the ACM, 27(11), 1134-1142.

Hoeffding, W. (1963). *Probability inequalities for sums of bounded random variables*. Journal of the American Statistical Association, 58(301), 13-30.

Shalev-Shwartz, S. and Ben-David, S. (2014). *Understanding Machine Learning: From Theory to Algorithms*. Cambridge University Press.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *sgd-lean: Formal Proofs of Bounded-Noise SGD Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20475583>

Cassie, B. (2026). *mirror-descent-lean: Formal Proofs of Mirror Descent and Bregman Divergence Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20475033>
