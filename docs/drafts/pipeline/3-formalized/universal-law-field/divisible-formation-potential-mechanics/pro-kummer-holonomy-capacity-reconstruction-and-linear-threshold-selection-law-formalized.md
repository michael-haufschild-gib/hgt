# ULF-DFPM-2 — Lean certification record

**Card:** `pro-kummer-holonomy-capacity-reconstruction-and-linear-threshold-selection-law.md`
**Status:** every theorem of the card is Lean-certified, unconditional and axiom-clean.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| (PKH.1) | the depth-`n` Kummer holonomy | `kummerHolonomy`, `kummerHolonomy_ne_zero`, `kummerHolonomy_zero` |
| (PKH.13) | charge conservation | `kummerHolonomy_add` |
| Thm 2.1, one depth | `h_n(q) = h_n(q') ⟺ n ∣ q − q'` | `kummerHolonomy_eq_one_iff`, `kummerHolonomy_eq_iff` |
| Thm 2.1, (PKH.4) | a finite packet determines `q` mod `lcm F` | `forall_mem_kummerHolonomy_eq_iff` |
| Thm 2.1, full tower | the whole tower determines `q` | `eq_of_forall_kummerHolonomy_eq` |
| Cor 2.2, (PKH.2) | the observer orbit has exact period `n / gcd(n, |q|)` | `kummerPeriod`, `kummerHolonomy_pow`, `kummerHolonomy_pow_eq_one_iff` |
| Cor 2.2, (PKH.3) | the marked logarithmic lift is unbounded | `tendsto_abs_markedLift_atTop` |
| §3 | the squared chord | `chordSq`, `chordSq_nonneg`, `chordSq_zero`, `norm_one_sub_exp_sq`, `chordSq_eq_sin_sq` |
| Thm 3.1, (PKH.6) | the two-sided inverse-square chord bounds | `chordSq_bounds` |
| (PKH.5) | the weighted action and its comparison profile | `proKummerTerm`, `capacityProfile` |
| Thm 3.1, (PKH.7) | finiteness ⟺ square-summable capacity | `summable_proKummerTerm_iff` |
| Cor 3.2, (PKH.8) | the polynomial threshold at `a = 1` | `summable_proKummerTerm_rpow` |
| Thm 4.1, (PKH.10) | bounded-action selection | `summable_proKummerTerm_iff_eq_zero` |
| Thm 4.1, truncation | uniformly bounded truncations already force `q = 0` | `eq_zero_of_sum_range_le` |
| (PKH.11)–(PKH.12) | the contour holonomy | `exp_contour_div_eq_kummerHolonomy` |
| Cor 5.1 | finite action ⟺ vanishing charge integral | `summable_proKummerTerm_iff_contour_eq_zero` |
| §6, linear capacity | the harmonic comparison profile diverges | `not_summable_linearCapacityProfile`, `summable_linear_proKummerTerm_iff_eq_zero` |
| §6 (1)–(4) | RH ⟺ finite ⟺ zero ⟺ uniformly bounded truncated action | `riemannHypothesis_tfae_proKummer` |
| §6, zeros | a strict-right zeta zero has divergent linear action | `not_summable_linear_proKummerTerm_of_zetaZero` |

## Modules

| Module | Public declarations |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/ProKummerHolonomyCapacity.lean` | 21 |
| `formal/GaloisForLFunctions/RHTower/ProKummerLinearThresholdSelection.lean` | 4 |

Both wired into `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower` and
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Proof notes

* The extended action `∑ w_n |1 − h_n(q)|² ∈ [0, ∞]` is formalized as `Summable` of a nonnegative
  real family, which is equivalent to finiteness of the `ℝ≥0∞` sum and keeps the two-sided
  comparison inside `ℝ`.  The finitely many depths below `2|q|`, where the chord bounds are not
  available, are removed by `summable_nat_add_iff` at shift `2|q|`, exactly as the card's
  "finitely many initial terms do not affect convergence".
* The card's "exact period `n/gcd(n,q)`" is proved as `addOrderOf` in `ZMod n`, so minimality is
  part of the statement: `h_n(q)^k = 1 ↔ n / gcd(n, |q|) ∣ k`.
* The chord identity `|1 − e^{ix}|² = 4 sin²(x/2)` is derived from `Complex.exp_mul_I` and the
  double-angle formula; the Jordan inequality `2y/π ≤ sin y` on `[0, π/2]` is mathlib's
  `Real.mul_le_sin`.
* The polynomial threshold reduces to `Real.summable_nat_rpow` after rewriting
  `n^a / n^2 = n^{a−2}`.

## Verification

* `lake env lean` on both modules: 0 errors, 0 warnings.
* `#print axioms` over the 25 public declarations: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, and no added hypotheses.

## Not claimed

The pre-target source construction of the weights and a uniform finite-action bound for the literal
arithmetic source — the card's `[SOURCE CAPACITY GENESIS OPEN]` gate — are future work.  §6 is an
equivalence, not an RH proof.
