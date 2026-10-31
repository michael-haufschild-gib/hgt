# HilbertianExplicitFormulas

Namespace `GaloisForLFunctions.HilbertianExplicitFormulas`; umbrella `HilbertianExplicitFormulas.lean`; 8 modules.
All results unconditional; RH appears only inside equivalences.

## 1. Motivation

On the zero divisor there are two quadratic functionals. The Weil form W(F) = Σ m F(z_ρ)·conj F(z̄_ρ) pairs a
zero with its line reflection (z_ρ = −i(ρ − ½)); the same-point (Hilbert) form S(F) = Σ m |F(z_ρ)|² pairs a
zero with itself. Explicit formulas compute holomorphic weights, hence W; RH is S = W. The programme determines
exactly what explicit formulas can and cannot see, finds integer-valued (quantized) same-point carriers that
read off-line zeros with margin 2, and proves the first exact same-point identity with a prime side.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Weil weight | `weilWeight F` | F·F#, F#(z) = conj F(z̄) |
| Finite forms | `samePointForm`, `explicitStatistic`, `lineReflectionDefect` | Σm|F|², Σm h(z), ½Σm|F(z) − F(z̄)|² |
| Reflection configuration | `ReflectionConfiguration`, `IsCritical`, `total`, `lineMass`, `offLineMass` | finite divisor closed under s ↦ 1 − s̄ and conjugation |
| Collision charge | `collisionCharge`, `horizontalMult`, `partnerMult` | O = Σ m_ρ(H_ρ − m_ρ): ordered pairs on a common horizontal |
| Pencil / Cesàro | `cesaroMeanSquare`, `CesaroBounded` | (1/N)Σ_n |Σ m c^n|² |
| Clocks | `holomorphicClock`, `ordinateClock`, `aliasCharge`, `NonResonant` | e^{λ(s−½)}; e^{2it Im s} |
| Resolvent norms | `samePointResolvent`, `explicitResolvent`, `resolventDefect`, `depthMoment` | S(s) = Σm/|s−ρ|², E(s) = ΣmRe 1/(s−ρ), D(s), M_{2k} |
| Xi resolvent | `xiSamePointResolvent`, `xiResolventDepth`, `xiResolventDepthTerm` | same objects on the multiplicity-exact Xi divisor |
| Theta reading | `xiResolventSourceKernel`, `xiResolventThetaReading`, `xiResolventThetaSamePoint` | smooth kernel = |4−z|^{−2} on the strip; finite theta readings |
| Curve data | `curveOrdinate`, `curveCollisionCharge` | F_q analogues (ordinate β/|β|) |
| Signed divisor | `signedSamePointForm`, `isolatingPolynomial` | real multiplicities |

External: `RHTower.xiWeilPolarization`, `RHTower.xiWeilEvaluationLp`, `RHTower.xiWeilLineConjLinearIsometry`,
`RHTower.lineReflect`, `ArithmeticCastelnuovoSeveri.CurveDatum`, `goldenDatum`, `circleReflect`.

## 3. Language

- **Same-point**: weight evaluated at one zero via z and z̄ (holomorphic × antiholomorphic). **Reflection-paired**:
  holomorphic weight pairing z with z̄.
- **Line-calibrated**: correct on every critical configuration (h = |F|² on ℝ).
- **Quantum**: least positive value of a carrier on configurations with an off-line point (here 2).
- **Depth**: d = β − ½; **depth moments** M_{2k} = Σ m d^{2k}.
- **Effective**: all multiplicities ≥ 0.

## 4. Mechanisms

1. Identity theorem from the real line: an entire weight equal to |F|² on ℝ is F·F#. Pair identity
   |a|² + |b|² − (ab̄ + bā) = |a − b|².
2. Reflection symmetrization over ρ ↦ ρ* turns signed depth sums into nonnegative depth terms.
3. Line reflection preserves ordinates ⇒ every off-line point has a horizontal partner ⇒ O ≥ 2; swap involution ⇒ O even.
4. Dominant-mode lemma: positive multiplicities and one clock of modulus > 1 ⇒ unbounded Cesàro mean square.
   Four-fold symmetry realizes every sign of Re λ·d ± Im λ·γ.
5. Parseval with clock classes: unimodular pencil mean square → Σ over coincidence classes = Σm² + O + aliasing.
6. Resolvent pair identity |s−ρ*|² − |s−ρ|² = (2σ−1)(2β−1); Cauchy-kernel partial fractions for vertical integrals.
7. Absolute summability of S right of the strip via the real reciprocal field; explicit side opened by
   ξ'/ξ = Γ-factor − Σ Λ(n)n^{−s}.
8. Smooth kernel equal to the Cauchy kernel on the strip + finite theta-prefix readings with compact cutoffs.
9. Circle transport w = e^{iz} for F_q; Lagrange isolation for signed divisors.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Calibration rigidity: line-calibrated entire weight = F·F# | `eq_weilWeight_of_calibrated` | proved |
| Pair error = |F(z) − F(z̄)|²; correct everywhere ⇒ F constant | `samePoint_sub_explicit_pair`, `const_of_explicit_eq_samePoint_everywhere` | proved |
| Finite S − W = defect; equality ⇔ all pairs blind | `samePointForm_sub_explicitStatistic`, `explicitStatistic_eq_samePointForm_iff` | proved |
| Xi divisor: explicit = Weil polarization; ‖v‖² − explicit = ½‖v − Jv‖² | `tsum_explicit_eq_xiWeilPolarization`, `norm_sq_sub_explicit_eq_half_reflectionDefect` | proved |
| Quantum law: critical ⇔ O = 0 ⇔ O < 2; O even | `isCritical_tfae`, `even_collisionCharge` | proved |
| Census: N ≤ N₀ + O; O ≤ cN ⇒ N₀ ≥ (1−c)N | `total_le_lineMass_add_collisionCharge`, `one_sub_mul_total_le_lineMass` | proved |
| Holomorphic clocks: bounded ⇔ read nothing; real λ: ⇔ O < 2 | `cesaroBounded_holomorphicClock_iff`, `cesaroBounded_holomorphicClock_real_iff` | proved |
| Ordinate clock reads O (non-resonant) | `tendsto_cesaro_ordinateClock`, `tendsto_cesaro_ordinateClock_sub_diag_of_nonResonant` | proved |
| Resolvent formula (σ−½)S = E + D, D ≥ 0, D = 0 ⇔ critical; sandwich | `sub_mul_samePointResolvent_eq`, `resolventDefect_eq_zero_iff`, `sub_width_mul_samePointResolvent_le` | proved |
| ∫D dt = π Σ_k M_{2k}u^{−2k} | `integral_resolventDefect_vertical` | proved |
| Full Xi: (σ−½)S − Re ξ'/ξ = D ≥ 0 (Re s > 1); prime/archimedean form | `sub_mul_xiSamePointResolvent_sub_logDeriv`, `xiResolventDepth_eq_samePoint_sub_arch_add_prime` | proved |
| D(4) as theta–prime expression | `xiResolventDepth_four_eq_thetaPrime`, `xiResolventThetaSamePoint_eq` | proved |
| F_q: unitary ⇔ O = 0 ⇔ O < 2 ⇔ bounded Lefschetz pencil; golden datum O = 2 | `unitary_tfae`, `cesaroBounded_lefschetz_iff_curveCollisionCharge_lt_two`, `goldenDatum_curveCollisionCharge` | proved |
| Circle-calibrated explicit sums = Rosati pairing | `explicit_eq_rosatiPairing` | proved |
| Same-point positivity ⇔ effectivity | `signedSamePointForm_nonneg_iff`, `exists_signedSamePointForm_neg` | proved |
| O(T) < 2 for ξ; census O ≤ cN with c < ¼ | — | open (RH / census) |

## 6. Tools

**Developed**
- Calibration rigidity on finite configurations, the Xi divisor and curve data.
- Clock calculus: dominant modes, classification, ordinate Parseval with aliasing.
- Collision-charge quantum law and census reduction.
- Resolvent Hilbertian formula (finite and full Xi), depth-moment generating series.
- Theta-prefix computation of the same-point resolvent at s = 4.

**To build**
- Non-holomorphic producer: an arithmetic identity for a same-point sum with quantized error.
- Prime-side control of the depth D(s) at σ near ½ (currently only Re s > 1).
- Source-realizable unimodular clocks reading O with finite loss.
- Census bound O(T) ≤ cN(T), c < ¼, from same-point carriers.

## 7. Open questions

1. Is there any source-realizable family whose Cesàro mean square reads the collision charge?
2. Can D(s) be bounded from the prime side as σ → ½⁺ (depth moments from resolvent data)?
3. Which non-holomorphic operation (Laplacian, two-variable kernel, divisor conjugation) yields a same-point
   identity with an arithmetic side?
4. Does the theta–prime expression for D(4) extend to a family in s with controllable sign of each term?

## 8. Traps

| Trap | Fact |
|---|---|
| A better test function lets the explicit formula compute S | Line calibration pins every holomorphic weight to F·F# |
| Explicit formula correct at one off-line pair is progress | It forces F blind at that pair |
| Mean squares of explicit formulas are same-point sums | Only for unimodular clocks; holomorphic clocks diverge off the line |
| Complex frequency avoids growth | Im λ ≠ 0 grows already on critical configurations with a non-real point |
| O = o(N) gives RH | It gives censuses; RH needs O < 2 |
| Same-point positivity holds for every L-function quotient | Any pole makes it indefinite |
| Computing S (theta readings) bounds the defect | It computes the same-point side only; the comparison D is the problem |

## 9. Context

**Uses** (import counts): RHTower 7, ConjugateDiagonalGeometry 1, ArithmeticElectrostatics 1, ArithmeticCastelnuovoSeveri 1.

**Used by**: none (umbrella only).

| Neighbour | Relation |
|---|---|
| RHTower (XiWeilLineConjHilbert, WindowRelation, pencil growth, ξ'/ξ positivity) | Xi evaluation space, line conjugation, horizontal collisions, log-derivative split |
| ConjugateDiagonalGeometry | Finite theta readings recover compact currents; used to compute S(4) |
| ArithmeticElectrostatics | External field is a prime sum; real reciprocal field summability |
| ArithmeticCastelnuovoSeveri | Curve data, circle reflection, golden datum for the F_q calibration |

## 10. Big picture

The programme separates the RH problem into two sides with a precise boundary. Everything an explicit formula
can compute is the Weil form; the same-point form differs from it by the line-reflection defect, pair by pair,
and no holomorphic test removes that defect. On the same-point side the defect is quantized: off-line zeros
contribute an even integer collision charge, at least 2, and over F_q this charge is exactly Weil's theorem in
disguise. Holomorphic clocks see the quantum only as an infinite excess; it is finite only on the
antiholomorphic side.

For the RH effort this means the decisive input cannot be a cleverer explicit formula; it must be a
non-holomorphic identity that reaches the same-point side. The resolvent identity shows such identities exist
and have a prime side right of the strip, with a nonnegative depth term that vanishes exactly under RH. The
open problem is to control that depth term near the critical line, or to find a source-realizable carrier that
reads the quantum with finite loss.
