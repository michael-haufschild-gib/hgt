# Internal claim trace audit

This file is not part of the manuscript. It records internal theorem support for
headline mathematical claims. The manuscript does not mention the formal corpus
and claims no novelty or significance from it.

## Primary modules

- `formal/GaloisForLFunctions/RHTower/HighExponentShellZeroFree.lean`
- `formal/GaloisForLFunctions/RHTower/HighExponentShellHypertranscendence.lean`
- `formal/GaloisForLFunctions/RHTower/HighExponentShellManuscriptCapstone.lean`

## Claim map

| Manuscript claim | Supporting declaration | Module |
|---|---|---|
| \(a_m\) is the difference of consecutive \(m\)-free indicators | `shellIndicator_apply` | `HighExponentShellZeroFree.lean` |
| \(a_m(n)\in\{0,1\}\) | `shellIndicator_eq_zero_or_one` | same |
| Exact support characterization | `shellIndicator_eq_one_iff` | same |
| Pairwise-disjoint shell supports | `shellIndicator_eq_zero_of_ne` | same |
| Finite coefficient telescope | `sum_range_shellIndicator` | `HighExponentShellHypertranscendence.lean` |
| Pointwise infinite fusion to zeta minus the unit coefficient | `tsum_complexShellIndicator` | same |
| \(m\)-free Dirichlet-series factorization | `LSeries_shellIndicator` | `HighExponentShellZeroFree.lean` |
| Prime-two head lower bound \(29/100\) | `le_norm_shellHead` | same |
| Tail upper bound with \(512/5\) and sixth-power tail | `norm_riemannZeta_diff_sub_shellHead_le` | same |
| \(\zeta(ms)-\zeta((m+1)s)\ne0\), \(m\ge12\), \(\Re s>1/2\) | `riemannZeta_natCast_mul_sub_succ_mul_ne_zero` | same |
| \(H_m\ne0\) in the strict right half-plane | `shellMultiplier_ne_zero` | same |
| \(H_m\) analytic in the strict right half-plane | `analyticAt_shellMultiplier` | same |
| Multiplication by \(H_m\) preserves analytic order | `analyticOrderAt_mul_shellMultiplier` | same |
| \(S_m^\#\) and zeta have equal vanishing order | `analyticOrderAt_riemannZeta_mul_shellMultiplier` | same |
| \(S_m^\#=0\) iff \(\zeta=0\) in the strict right half-plane | `riemannZeta_mul_shellMultiplier_eq_zero_iff` | same |
| Nonzero shell coefficient has \(\Omega(n)\ge m\) | `shellIndicator_cardFactors_lower` | `HighExponentShellHypertranscendence.lean` |
| Equality \(\Omega(n)=m\) forces \(n=p^m\) | `shellIndicator_eq_prime_pow_of_cardFactors_eq` | same |
| Selected-prime derivative vanishes below grade \(m-1\) | `primeDeriv_rotatedShellJet_eq_zero_of_cardFactors_lt` | same |
| Selected-prime derivative is a pure point mass at grade \(m-1\) | `primeDeriv_rotatedShellJet_eq_pointMass_of_cardFactors_eq` | same |
| Lowest-layer determinant coefficient cannot be changed by higher layers | `arithmeticFunction_det_apply_eq_of_cardFactors_lowerLayer_fintype` | same |
| Universal \(\Omega\)-leading finite-jet independence | `omegaLeadingJets_algebraicIndependent` | same |
| Shell jet rectangles algebraically independent | `highExponentShellJets_algebraicIndependent` | same |
| Unified zeta/shell jet rectangles algebraically independent | `zetaShellJets_algebraicIndependent` | same |
| Arbitrary finite shell families differentially independent in source fraction field | `highExponentShellArithmetic_differentialIndependent_fintype` | same |
| Arbitrary finite zeta/shell families differentially independent in source fraction field | `zetaShellArithmetic_differentialIndependent_fintype` | same |
| Faithful transfer to meromorphic germs over the actual rational coordinate | `zetaShellUpperEndCarrier_differentialIndependent` | same |
| Countable zeta-plus-shell differential independence over \(\mathbb C(s)\), for every shell \(m\ge2\) | `zetaPositiveShellUpperEnd_differentialIndependent` | same |
| Every shell \(m\ge2\) remains independent after adjoining zeta differential field | `positiveShellUpperEndCarrier_relativeDifferentialIndependent` | same |
| Relative multiplier carrier is \(S_m/\zeta\) | `relativeShellMultiplierUpperEndCarrier` and `zeta_mul_relativeShellMultiplierUpperEndCarrier` | same |
| \((H_m)_{m\ge2}\) jointly differentially independent over \(\mathbb C(s)\langle\zeta\rangle\) | `relativeShellMultiplierUpperEndCarrier_differentialIndependent_two` | same |
| Zero-free subfamily \(m\ge12\) inherits relative independence | `relativeShellMultiplierUpperEndCarrier_differentialIndependent` | same |
| RH iff one high shell is zero-free in the open right critical half-strip | `riemannHypothesis_iff_shellCriticalStripZeroFree` and `riemannHypothesis_iff_exists_shellCriticalStripZeroFree` | `HighExponentShellManuscriptCapstone.lean` |
| RH iff every high shell is zero-free there | `riemannHypothesis_iff_forall_shellCriticalStripZeroFree` | same |
| RH iff the common frame zero set there is empty | `riemannHypothesis_iff_shellFrameCommonZeroFree` | same |
| Bundled publication theorem | `positiveHypertranscendentalRiemannDivisorFrame` | same |

## Derived manuscript corollaries

- Exact finite-jet transcendence degree follows immediately from algebraic
  independence of the selected jets.
- Analytic infinite fusion on \(\Re s>1\) follows from
  `tsum_complexShellIndicator`, bounded \(0/1\) coefficients, and absolute
  convergence of \(\sum_{n\ge2}n^{-\sigma}\).
- RH equivalences now have direct capstone declarations; their proof uses
  `riemannZeta_mul_shellMultiplier_eq_zero_iff`,
  `riemannZeta_ne_zero_of_one_le_re`, and `rh_iff_xi_ne_zero_right`.

The analytic fusion identity is the only manuscript corollary retained as a
direct composition of coefficientwise fusion and absolute convergence; every RH
equivalence has a dedicated capstone declaration.

## Scope alignment

- Main paper does not mention the formal corpus.
- No RH assumption occurs in either primary module.
- No numerical zero verification is used.
- Threshold \(12\) is presented as sufficient, not optimal.
- Divisor equality is stated away from the zeta pole.
- Differential independence is measured over the actual rational coordinate
  field, then over the differential field generated by zeta.
- Relative normalization uses a nonzero meromorphic field element; it does not
  assert pointwise division at a zeta zero.
- Paper explicitly says that common-zero exclusion still needs an analytic
  inequality and that the theorem does not prove RH.

## Verification record

Audit date: 2026-07-27.

- Final foreground build:
  `lake build GaloisForLFunctions.RHTower.HighExponentShellManuscriptCapstone`
  completed successfully (`8821/8821` jobs).
- Axiom audit of the bundled publication theorem, relative differential-independence
  theorem, universal \(\Omega\)-leading theorem, zero-free analytic theorem, and common-zero
  RH equivalence returned exactly `propext`, `Classical.choice`, and `Quot.sound`.
  No `sorryAx` or project-specific axiom occurs.
- Project lint initially detected that the two new RHTower modules were not reachable from
  the RHTower umbrella. Both imports were added; the repeated lint no longer reports either
  module.
- The repeated repository-wide lint still exits nonzero because ten unrelated, pre-existing
  untracked HTGeometry modules are absent from the already-modified HTGeometry umbrella.
  They were not edited or claimed by this work. No proof-debt error was reported for either
  paper module.
- Manuscript source contains no mention of formalization, proof software, or machine
  verification.
- All citations and cross-references resolve; the TeX log has no warning, overflow, underflow,
  or undefined-reference diagnostic.
- The final 12-page PDF was rasterized at 120 dpi and every page was inspected.
- Final process audit found no active Lean, Lake, or task lint process.
