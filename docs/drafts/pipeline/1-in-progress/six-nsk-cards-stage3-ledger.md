# Six NSK cards → stage 3: formalization ledger

Working ledger for the goal "formalize unconditionally in Lean every proven theorem of the six
`2-fully-proven/not_new_scientific_knowledge` cards listed below, then promote them to stage 3".

## Cards in scope

| # | Card | Lean state at ledger open (2026-08-19) |
|---|---|---|
| C1 | `hardy-critical-line-moment-anchor` | VanDerCorput, DigammaSeries/Uniform, HardyZ*, SmoothAFEGaussian* done; smooth AFE keystone, moments C/F, mean E, assembly open |
| C2 | `hardy-cyclicity-maximal-ht-field-blindness` | only `HTGeometry/CayleySchur.lean`; H²(D)/inner-outer/Beurling/model space/DA-independence missing |
| C3 | `f1-inversion-single-prime-stieltjes-collapse` | `HTGeometry/SymmetricBlockAlgebraicIndependence.lean` has `beurlingBlock`, esymm generation, esymm alg-independence |
| C4 | `faithful-krein-index-escape-stratification` | finite Krein inertia + measured-index blindness exist; analytic canonical product, N_κ topology, Fredholm families missing |
| C5 | `dyadic-squarefree-euler-fock-source-factorization` | one-prime factor formalized; global unitary + rank-two connection identity open |
| C6 | `horizontal-singleton-zero-fibers` | pointwise theorems in `RHTower/HorizontalSingletonZeroFiber.lean`; finite charging law + liminf passage open |

## Log

- 2026-08-19 — ledger opened; corpus reconnaissance done.

## 2026-08-19 session 1

### C6 `horizontal-singleton-zero-fibers` — card content DONE
New: `formal/GaloisForLFunctions/RHTower/HorizontalSingletonFiberCharging.lean` (wired into
`RHTower.lean`, olean built, axioms clean).  Contains `xiZeroCount`/`xiCriticalZeroCount`/
`xiOffLineZeroCount`/`xiSimpleCriticalZeroCount`/`xiSingletonFiberCount`,
`two_mul_xiSimpleCriticalZeroCount_le` (inequality (1)),
`xiSimpleCriticalRatio_sub_le_xiSingletonFiberRatio` (normalized form),
`le_liminf_xiSingletonFiberRatio` (inequality (2)),
`prattRoblesZaharescuZeindler_singleton_density` (the 0.116158438 corollary as an implication).
REMAINING: unconditional Lean providers for the two cited PRZZ proportions — external literature,
same lane as C1.

### C5 `dyadic-squarefree-euler-fock-source-factorization` — card content DONE
Seven new modules (all wired, oleans built, axioms clean):
`EulerSquarefreeDyadicStateFactorization`, `...LogTransport`, `...LogMoments`,
`...FisherTangent`, `...FisherDefect`, `...Tower`, `...AnalyticTelescope`.
Covers (1)-(35) of the card.  The card's three unchecked gates (prime-Gamma completion,
Sonin graph convergence, RH) are the declared successor programme, not theorems of the card.

### C4 `faithful-krein-index-escape-stratification` — substrate located (card Lean section is STALE)
Existing and directly reusable:
- `HTGeometry/MovingCanonicalSurgery.lean` — `movingCanonicalSurgeryProduct`,
  `movingCanonicalSurgeryCarrier_exact_negativeSquares`, `movingCanonicalSurgeryProduct_exactOrderOneDivisor`
- `HTGeometry/MovingEvenCanonicalSurgery.lean` — the functional-equation-even version
- `HTGeometry/MovingCanonicalSurgeryFieldInvariance.lean` — differential-field invariance under the
  rational surgery gauge, and `no_movingCanonicalSurgeryCount_selector_of_differentialAdjoin`
- `HTGeometry/MovingCanonicalFullTranslationFreeness.lean`, `FamilyPowerGauge.lean`
  (`not_familyDifferentiallyAlgebraicOn_translates_pow`), `MovingDivisorEntireFreeness.lean`
- `HTGeometry/HerglotzFiniteAtomicExactNegativeSquares.lean` — `CarrierHasExactlyNegativeSquares`
- `RHTower/CompactOpenKolchinWardChargeEscape.lean` — the Xi-side analogue of the escape family with
  full compact-open + all-jets convergence (`escapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly`)
STILL TO BUILD for C4: (a) the normalized remote-pair gauge `A_(r,T)` and its all-derivative
compact-open convergence to 1; (b) exact index `k+r` for the multiplied carrier; (c) `P_N` equality
at every power level; (d) lower semicontinuity of the negative-square index; (e) the
continuous-Fredholm impossibility theorem.

### C1/C2/C3 — not started this session
- C1 `hardy-critical-line-moment-anchor`: substrate VanDerCorput/HardyZ*/SmoothAFEGaussian* present.
- C2 `hardy-cyclicity-maximal-ht-field-blindness`: needs analytic `H^2(D)`, inner-outer, Beurling.
- C3 `f1-inversion-single-prime-stieltjes-collapse`: `HTGeometry/SymmetricBlockAlgebraicIndependence.lean`
  has `beurlingBlock` + esymm generation; the corank-2 floor needs Gelfond--Schneider (not in mathlib).

### C4 progress (2026-08-19, same session)
New modules (all compile clean, wired into `HTGeometry.lean`):
- `HTGeometry/FaithfulIndexFredholmObstruction.lean` — `NegIndexAtMost`, `HasCoerciveComplement`
  (the gap form of "self-adjoint Fredholm at 0 with finite negative spectral subspace"),
  `finrank_le_of_trivial_meet_of_sup_eq_top`, `negIndexAtMost_of_coerciveComplement` (index
  stability), `no_faithful_continuous_index_of_unbounded_witness` (the obstruction).
- `HTGeometry/RemotePairEscapeGauge.lean` — `remotePairFactor`, `remotePairGauge` = `A_(r,T)`,
  explicit quadratic form, Schwarz reality, zeros, `neg_logDeriv_remotePairGauge = multiPairCarrier`,
  `tendstoLocallyUniformly_finset_prod`, `remotePairGauge_tendstoLocallyUniformly`,
  `remotePairGauge_mul_iteratedDeriv_tendstoLocallyUniformly` (all-derivative escape).
- `HTGeometry/KreinIndexEscapeStratification.lean` — `differentialAdjoin_range_pow_baseGauge_eq`
  (equation (4) at EVERY power level, fully general — also serves card C2 item 3),
  `multiPairCarrier_append`, `escapeCarrier`, `escapeCarrier_exact_negativeSquares` (index k+r),
  `exists_coercive_bound_on_subspace`, `eventually_negOn_subspace_of_entrywise_tendsto` and
  `eventually_carrier_negativeSquares_witness` (lower semicontinuity (12)),
  `no_continuous_faithful_krein_index` (the card's continuous-Fredholm obstruction).
- `HTGeometry/KreinEscapeAnalyticFamily.lean` — `kreinEscapeCarrier`,
  `kreinEscapeCarrier_exact_negativeSquares`, `kreinEscapeProduct = A_(r,T)·F_(θ,k)`,
  `neg_logDeriv_kreinEscapeProduct_eq`, `kreinEscapeProduct_iteratedDeriv_tendstoLocallyUniformly`.

STILL OPEN for C4: (i) exact order one and Schwarz reality of the gauged product; (ii) the
translation-orbit differential independence and the concrete `P_N` equality — needs the gauge
realized in `RatFunc ℂ` / `upperEndMeroField` like `movingCanonicalSurgeryGaugeRatFunc`;
(iii) the functional-equation-even version (10)–(11).

### C4 COMPLETE (2026-08-19)
All of statements 1–5, (6), the FE-even strengthening (10)–(11), the lower semicontinuity law (12)
and the continuous-Fredholm obstruction (13) are formalized unconditionally; see the card's
"Lean status update (2026-08-19)" section for the exact declaration list.  Six modules:
`RemotePairEscapeGauge`, `FaithfulIndexFredholmObstruction`, `KreinIndexEscapeStratification`,
`KreinEscapeAnalyticFamily`, `KreinEscapePowerFieldInvariance` (+ the pre-existing
`MovingCanonicalSurgery` stack).  All axioms clean.

### Next: C2 `hardy-cyclicity-maximal-ht-field-blindness`
Item 3 (`P_N(G_B) = P_N(O)` at every power level) is already covered by
`differentialAdjoin_range_pow_baseGauge_eq`.
Item 4 needs an analytic `H²(D)`: coefficient model `ℓ²(ℕ)`, polynomial density, multiplication by
a bounded analytic function, multiplication by a finite Blaschke product as an isometry with closed
range `B·H²`, and `dim(H² ⊖ B·H²) = deg B`.  NOTE: `[O] = H²(D)` does NOT need Beurling — `O` and
`O⁻¹` bounded analytic makes multiplication by `O` a bounded operator with bounded inverse, so it
carries the dense set of polynomials to a dense set.
Item 1 needs `|σ| < 1` from the Herglotz/Cayley construction (corpus `CayleySchur.lean`).
Item 2 needs the parent Herglotz full-translation freeness (corpus
`HerglotzFullTranslationFreeness.lean`) transported through the rational substitution `φ`, the
Cayley map and `exp`.
