# ULF-FIELD-2 — Lean certification record

**Card:** `critical-locus-hessian-classification-and-crystalline-transversality-law.md`
**Status:** every proved theorem of the card (Θ1, Θ2(i)–(v), Θ3.1, Θ3.2) is Lean-certified,
unconditional and axiom-clean. Θ4 is open research and has been split out.

## Modules

| Module | Role |
|---|---|
| `formal/GaloisForLFunctions/RHTower/CriticalLocusQuadrupleEvenness.lean` | Θ1 |
| `formal/GaloisForLFunctions/RHTower/CrystallineShadowTransversality.lean` | Θ3.1 kernel, Θ3.2 |
| `formal/GaloisForLFunctions/RHTower/CriticalLocusHessianClassification.lean` | Θ2(i)–(v), Θ3.1 packaging |
| `formal/GaloisForLFunctions/RHTower/CriticalLocusConeFullness.lean` | Θ4 Step A (cone fullness) |

All four are imported by `GaloisForLFunctions.RHTower`.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| Θ1 | multiset evenness of the splitting quadruple | `criticalQuadruple_neg` |
| Θ1 | every function of the configuration is even in the displacement | `apply_criticalQuadruple_neg` |
| Θ1 | universal criticality: the scalar quadruple functional has vanishing derivative at `t = 0` | `deriv_criticalQuadrupleSum_zero` |
| Θ1 | exact first derivative at the corpus `XiC` | `hasDerivAt_criticalQuadrupleSum_XiC`, `deriv_criticalQuadrupleSum_XiC` |
| Θ2 | second central jet at `XiC` | `iteratedDeriv_two_criticalQuadrupleSum_XiC` |
| Θ2(i) | exact separation, no cross terms | `multiQuadruple_map_sum`, `multiQuadruple_relative_separation`, `relativeQuadrupleValue` |
| Θ2(ii) | the weight `2(F''(1/2+iγ)+F''(1/2−iγ))`, real form `4 Re F''(1/2+iγ)` | `iteratedDeriv_two_criticalQuadrupleSum`, `iteratedDeriv_two_criticalQuadrupleSum_re` (with the conjugation bridge `hasDerivAt_conj_of_eventually_conj`, `analyticAt_conj_point`, `iteratedDeriv_two_conj_eq`) |
| Θ2(iii) | per-zero necessity | `re_iteratedDeriv_two_nonpos_of_detector`, `weight_nonpos_of_detector` |
| Θ2(iv) | diagonal Hessian and second-order determination | `iteratedDeriv_two_multiSplitting`, `secondOrder_jets_eq_iff_weights_eq` |
| Θ2(v) | composite criteria | `deriv_deriv_comp_of_first_derivs_zero`, `composite_detector_necessity` |
| Θ3.1 | kernel identity `4cos(γx)(cosh(tx)−1)` | `quadrupleExp_eq`, `quadrupleExp_sub_undisplaced` |
| Θ3.1 | integral packaging `⟨Δν,h⟩ = ∫ h·4cos(γx)(cosh(tx)−1)` | `lineTestTransform`, `relativeQuadrupleValue_lineTestTransform`, `multiSplitting_shadow_integral` |
| Θ3.2 | the shadow density is somewhere strictly positive, hence not atomic | `shadowDensity`, `shadowDensity_zero`, `shadowDensity_pos_of_ne_zero`, `shadowDensity_ne_zero_fun` |
| Θ4 Step A | every nonzero direction sees a strictly negative configuration move | `criticalLocus_move_cone_fullness`, `pair_sum_eq_two_re`, `quad_sum_eq_four_re` |

## Verification (2026-08-21)

* `#print axioms` on all 41 public declarations of the four modules: only `propext`,
  `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`.
* Every declaration name recorded in the card's Lean-status section was checked against the tree
  and found present.

## Θ4 — split out

The 2026-08-09 proof of Θ4 was refuted by the 2026-08-13 hostile re-audit (placement drift off the
line; Jacobian propagation from a discrete support). The repaired route retains one open point.
Θ4 now lives in `0-backlog/critical-locus-finite-evaluation-blindness.md`, which additionally
records two new reductions found on 2026-08-21:

* a **bounded-rounding assembly** — `N` independent k-slide IFT blocks give radius `Nr` while an
  integer cone combination cancels the base with error bounded independently of `N`, so exact
  hitting follows from *repeatable* moves positively spanning `ℝ^k`;
* an **elementary proof of second-derivative cone fullness** — `Re G'' ≥ 0` on the line makes
  `γ ↦ Re G(1/2+iγ)` concave, and a concave function on `ℝ` with limits `0` at both ends is
  identically zero; with linear independence modulo constants this replaces the strip
  Phragmén–Lindelöf and harmonic-minimum-principle argument of Step A.
