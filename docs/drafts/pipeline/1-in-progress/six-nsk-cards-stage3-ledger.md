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
