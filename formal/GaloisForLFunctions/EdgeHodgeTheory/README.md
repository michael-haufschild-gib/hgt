# Edge Hodge Theory of the Scaling Surface (EHT)

Namespace `GaloisForLFunctions.EdgeHodgeTheory`; umbrella `EdgeHodgeTheory.lean`. Everything is
unconditional. Theorems named `riemannHypothesis_iff_*` are equivalences, `riemannHypothesis_of_*`
implications into RH; neither is a proof of RH.

## 1. Motivation

Renormalized intersection theory (RIT) and adelic Krein geometry (AKG) put the Frobenius-graph
geometry on the scaling surface of `ℤ` and locate the missing sign: RH is the renormalized Hodge
index, positivity of the pairing of scaling correspondences on the pole-orthogonal hyperplane
`v₁^⊥`. Every reformulation inside that geometry — Castelnuovo–Severi at rational scales, the
Künneth square, every Hadamard power, the glued test index, the heat homotopy — reproduces RH
exactly. Every estimate stops at the same place.

The place has a name. The pairing is only ever computed at **finite resolution**: atoms of a
profile `φ` at overlap `c` on the horizon `{1, …, N}`, giving the complete Weil matrix
`W_{φ,c,N}`. As the resolution grows the family passes from a **universal regime**, where
positivity is proved without zero information, to an **RH regime**, where positivity is
equivalent to RH. Between them is the **detection edge**: the resolution at which the family
first sees the zeros, `τ(c) log N ≈ 1` with `τ` the Fourier tail of the profile.

The obstruction at the edge is logical. A positivity statement proved without zero information
holds for every datum that shares the information, including data with off-line zeros, so it is
valid only where those data are not yet seen. No refinement of estimates crosses the edge, and
signature calculus cannot either, because every index reformulation reproduces RH exactly. What
can cross is a statement that holds at the edge **by structure**. EHT is the theory of the
degenerating family `W_{φ,c,N}` and of the three kinds of statement that hold by structure:
identities, inherited polarizations and integer invariants.

The model is Hodge theory of degenerations. In a degenerating family of polarized Hodge
structures positivity survives in the limit by structure — the nilpotent-orbit and `SL₂`-orbit
theorems polarize the limiting mixed structure by representation theory, without estimates. The
scaling surface carries the analogous ingredients: a limit structure at fixed overlap (the
Ramanujan-graded completed conductor energies), one-parameter degenerations (overlap, horizon,
heat) with integer invariants (Hodge defect, Krein–Langer index, collision charge), and a
hyperbolic plane (boost and conformal successor) on which the affine group acts through
`SL(2, ℝ)`. EHT asks which of these structures survive across the edge, proves what they give, and
proves where they cannot give more.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Resolution | `(φ, c, N)` | profile `φ ∈ C²`, supported in `[0, 1]`, `∫φ ≠ 0`; overlap `c`; horizon `N` |
| Complete Weil matrix | `RenormalizedArithmeticPotentialTheory.completeWeilMatrix φ c N` | Weil's form on the atoms `φ((u − log n)/w)`, `w = c/N`, `1 ≤ n ≤ N`, atom-mass normalized |
| Complete Weil energy | `RenormalizedArithmeticPotentialTheory.completeWeilEnergy` | its quadratic form on `ℝ^{1..N}` |
| Pole class | `normalizedRamanujanHorizonVector 1 N` | the ground conductor `v₁`, `(log N)^{−1/2}`-normalized; boost, Markov and harmonic hyperplanes are `v₁^⊥` |
| Hodge defect at resolution | (EHT) | negative index of `W_{φ,c,N}` on `v₁^⊥`; total index `≤` defect `+ 1` |
| Edge | (EHT) | `e_φ(N) = inf {c ≥ 1 : W_{φ,c,N} not PSD}`, `e_φ^⊥(N)` the same on `v₁^⊥`; values in `[1, ∞]` |
| Universal regime / RH regime | (EHT) | schedules `c_N` with eventual positivity proved unconditionally / equivalent to RH |
| Edge exponent | (EHT) | `α_φ = liminf log e_φ(N) / log log N` |
| Completed conductor energies | `RenormalizedArithmeticPotentialTheory.CompletedShell.completedConductorEnergy φ c m` | `E_m(c) = (2/(M φ(m))) Σ_{(a,m)=1} (m/a) ∫_{ac/m}^∞ |φ̂(2πt)|² dt` |
| Limit structure | (EHT) | the Ramanujan-graded form `Σ_m E_m(c) y_m²`: the fixed-overlap limit of `W_{φ,c,N}` |
| Fourier tail, critical overlap | `TransMetzlerWeilPositivity.sincTail`, `sincCriticalOverlap` | `τ(c) = ∫_{ξ>c} |φ̂|²`; least `c ≥ 1` with `τ(c) log N ≤ 1` |
| Visible window | `TransMetzlerWeilPositivity.nonneg_of_sincCritical_multiple` | at overlap `K c*_N` the family controls every test of support radius `½ log K + O(1)` |
| Flows | (EHT) | overlap flow `c ↦ W_{φ,c,N}`; horizon flow `N`; heat flow `t ↦ K_t` |
| Krein–Langer index | `HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel` | `κ(K_ζ)` = zeros right of the line, the ceiling of every receiver |
| Heat Hodge defect | `AdelicKreinGeometry.heatDilationKernel`, `RenormalizedIntersectionTheory.boostPolarIndex_heat_eq_sum_collisionPairs` | nonreal right zeros of `H_t`; drops by one per collision |
| Collision charge | `ConjugateDiagonalGeometry.fredholmIndex_integerThetaCollisionOperator_eq_charge` | Fredholm index of a Wiener–Hopf operator from integer theta prefixes |
| Collided and reflection pairings | `ArithmeticPolarization`, `ConjugateDiagonalGeometry.heckeDefect_eq_second_difference` | `(ρ, ρ̄)` and `(ρ, 1 − ρ)`; Frobenius at infinity identifies them |
| Profile classes | `HeckeKreinToeplitz.atomicReceivers_quasiAnalytic_boundary`, `SpacingScaleHarmonicAnalysis.TheDenjoyCarlemanProfiles` | `C²`, Gevrey `s > 1`, log-Denjoy–Carleman; the quasi-analytic boundary `s = 1` |
| Curve data | `ArithmeticCastelnuovoSeveri.CurveDatum` | the calibration over `𝔽_q`: Frobenius eigenvalues, quantized exponents |

## 3. Language

- **Resolution family**: `(c, N) ↦ W_{φ,c,N}` for a fixed profile, read as a degenerating family.
- **Universal regime**: resolutions at which positivity is a theorem; it cannot depend on where the
  zeros are.
- **RH regime**: resolutions at which positivity is RH (the receivers of TM, SSHA, RAPT).
- **Detection edge**: the boundary between them. For ζ under RH the family is positive at every
  resolution and the edge is `∞`; the edge as a function of resolution is what an off-line zero
  would produce, and its location is a property of the profile.
- **Edge-valid statement**: one that holds at every resolution, edge included: an identity, an
  inherited polarization, or an integer invariant. An estimate against the ground energy is not
  edge-valid.
- **Limit structure**: the fixed-overlap limit of the family in Ramanujan coordinates.
- **Inherited polarization**: positivity of the finite-resolution form deduced from positivity
  of its limit structure, with a loss that is a fixed fraction of the limit's gap.
- **Ground energy and quantum**: `E₁(c)`, of order `τ(c)`, and `1/log N`, the energy scale at which
  zeros enter the normalized form. The edge is where they balance.
- **Crossing**: a resolution or time at which a nondegenerate path of forms becomes degenerate;
  integers change only there.
- **Frobenius at infinity**: an arithmetic correspondence acting as complex conjugation on the zero
  divisor.

## 4. Mechanisms

**The edge logic.**
1. An estimate is a statement `∀ Z ∈ 𝒞, W_r(Z) ≥ 0` over the class `𝒞` of data sharing its input.
   Its universal regime is contained in the positivity region of every member of `𝒞`, so it lies
   below the edge of every off-line member. Positivity across the edge needs a statement whose
   class contains no off-line datum: a selective structure.

**Identities.**
2. Repayment: the shells repay every conductor exactly, so each completed conductor energy is a
   positive Fourier integral. The limit structure is polarized by an identity at every overlap.
3. Shell identity: on `ℓ = 0` the archimedean Weil state is Weil's dilation form plus the exact
   squares of the half-line shells (AKG). An identity at RH-complete resolution would be RH.

**Inherited polarization.**
4. At fixed overlap the Ramanujan vectors are quasimodes with eigenvalues `E_m(c)`; the low
   spectrum lives on the low conductors, and the form inherits a fixed fraction of the limit's
   gap at every horizon beyond one. Along growing overlap the limit degenerates (`E_m(c) → 0`), and
   inheritance holds exactly as long as the ground energy dominates the quantum.

**Integers.**
5. The negative index is lower semicontinuous and, at nondegenerate points, locally constant;
   along a path of nondegenerate forms it is constant, and it changes only at crossings, by at most
   the nullity there.
6. Every finite-resolution Hodge defect is bounded by the Krein–Langer index `κ(K_ζ)`; RH-complete
   schedules attain it. The index is conserved along every flow in this sense.
7. Along the heat flow the defect drops by one per collided pair and vanishes for `t ≥ 1/8`.

**Profile covariance.**
8. The RH regime starts where the profile's synthesis error, squared and weighted by `log N`,
   vanishes: `c_N⁴/log N → ∞` for every `C²` profile, `(log log N)^{α}`, `α > s`, in Gevrey class
   `s`, `L(log L)²`, `L = log log N`, for log-Denjoy–Carleman profiles. Below Gevrey class `1` no
   compactly supported profile exists: the edge cannot be pushed past the quasi-analytic boundary.

**Selection.**
9. Finite prime flips are seen at fixed overlap, the Liouville twin below touching; ζ is positive
   through the universal regime. The edge separates ζ from these twins.

## 5. Questions

1. What is the limiting structure of `W_{φ,c,N}` as the resolution grows, and is it polarized on
   `v₁^⊥` by an `SL₂`-type mechanism?
2. Why is the edge at `τ(c) log N ≈ 1`, and what changes in the form exactly there?
3. Is there a monotone or conserved quantity along the resolution flow that controls the Hodge
   defect (an analogue of a `c`-theorem)?
4. What is Frobenius at infinity: the correspondence acting as conjugation on the divisor?
5. Does Weil's dilation form on `ℓ = 0` admit a shell identity, and is it the edge limit of the
   universal-regime decompositions?
6. Is `κ(φ_c) − 1` an index computed by deformation to a model?

## 6. Pillar theorems

| Pillar | Statement | Lean | Status |
|---|---|---|---|
| Edge dichotomy | RH ⇔ the edge is `∞` at every horizon; otherwise the edge of the tilted spline lies in `[(log N)^{α*}, 2(log N)^{¼+}]` infinitely often | | target |
| Edge ceiling law | every `C²` profile has its edge below `(log N)^{¼+}`, every Gevrey-`s` profile below `(log log N)^{s+}`, the sinc profile below `ω(1)·c*_N`; nothing below the quasi-analytic boundary | | target |
| Limit structure | at fixed overlap the family converges to the Ramanujan-graded form `Σ E_m(c) y_m²`, polarized by the repayment identity; the limit degenerates along the overlap flow | | target |
| Integers along flows | index locally constant at nondegenerate points; constant along nondegenerate paths; jumps bounded by nullity | | target |
| Deformation to a model | a nondegenerate path from a form to a positive model exists iff the form is positive; index-by-deformation is the sign | | target |
| Krein–Langer ceiling along flows | every resolution's Hodge defect `≤ κ(K_ζ)`; RH-complete schedules reach it | | target |
| Edge selectivity | finite flip twins have bounded edge; ζ's edge grows at least like `(log N)^{α*}` | | target |
| No softening at resolution | the Künneth square family has the same edge; Hadamard powers have no smaller edge | | target |
| Frobenius at infinity | conjugation and reflection agree on a configuration iff it is critical; over `𝔽_q` this is `ᾱ = q/α`; a conjugation correspondence is RH | | target |
| Calibration over `𝔽_q` | the resolution flow of a curve is trivial: a violation is seen within `2g` scales; the golden datum fails | | target |

## 7. Tools

**To develop.**
- Resolution families of Hermitian forms: Hodge defect on a hyperplane, edge, universal and RH
  regimes, edge exponents; compression and comparison of edges.
- Krein-space spectral flow: semicontinuity, local constancy, crossing bounds, path invariance.
- Limit structures: Ramanujan-graded limits, their polarization by repayment, degeneration rates.
- Arithmetic sum-of-squares certificates indexed by conductors and successor shells.
- Denjoy–Carleman calculus of profiles and their edges.
- Integer Fredholm readings as edge detectors.
- Renormalized determinants and counterterms along the flows.

## 8. Open research topics

1. The exact edge exponent of the tilted spline in `[α*, ¼]` and its intrinsic value predicted by
   `τ(c) log N ≈ 1`.
2. Inheritance of the limit's polarization on `v₁^⊥` past the universal regime.
3. A signed estimate on the subthreshold conductor block `m ≲ c` at floor scale.
4. A shell identity for Weil's dilation form on `ℓ = 0`.
5. A crossing-free homotopy of the glued state to an index-one model for a structural reason.
6. Frobenius at infinity as a correspondence over `ℤ`.

## 9. Traps

| Trap | Fact |
|---|---|
| Positivity at fixed overlap is progress toward RH | It holds unconditionally with a gap; it is the universal regime |
| A sharper estimate eventually crosses the edge | An estimate valid for a class with an off-line member stops below that member's edge |
| The limit structure polarizes the edge | It degenerates along the overlap flow and does not depend on the zeros |
| A crossing-free homotopy to a positive model is an independent proof | It exists iff the endpoint is positive |
| Smoother profiles soften the problem | They move the RH regime down to `L(log L)²`; positivity there is still RH, and the quasi-analytic boundary stops the descent |
| Künneth or Hadamard powers soften the sign | They are positive iff RH, at every resolution |
| Over `𝔽_q` one also needs a resolution flow | The flow is trivial: detection happens within `2g` scales |

## 10. Context

EHT sits at the edge between the two halves of the RH map: the estimate routes of class C1 (HF,
SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD), which grow unconditional positivity with resolution,
and the identity and index routes (SC, WD, RIT, AKG, HKT), which reproduce RH exactly. Its
objects are the walls `Σ-1` (positivity on `v₁^⊥` across the edge), `Σ-4` (the exact edge of the
tilted spline), `Σ-5` (a shell identity for the dilation form) and `Σ-10` (no heat-index jump).

| Neighbour | Interface |
|---|---|
| RenormalizedIntersectionTheory | renormalized Hodge index, pole hyperplane, Hodge index at growing overlap, heat homotopy |
| AdelicKreinGeometry | archimedean glue, shell identity, pole–successor states, Borel model |
| CriticalArithmeticCorrelationTheory | positivity at fixed, iterated-logarithmic and power-of-log overlap (the universal regime) |
| RenormalizedArithmeticPotentialTheory | complete Weil matrix, completed conductor energies, low spectrum on low conductors, RH at logarithmic overlap |
| TransMetzlerWeilPositivity | receivers, critical overlap, visible window, flip and Liouville selectivity |
| SpacingScaleHarmonicAnalysis, HeckeKreinToeplitz | Gevrey receivers, the quasi-analytic boundary, Krein–Langer ceiling |
| EffectiveArithmeticHodgeTheory | atomic indices converge to `κ(K_ζ)` |
| ConjugateDiagonalGeometry, ArithmeticPolarization | collision Fredholm index, Hecke defect, collided polarization |
| ArithmeticCastelnuovoSeveri | curve data, Frobenius span, golden datum |

## 11. Success criteria

1. **Edge validity**: its positivity statements hold uniformly across the edge; they are identities,
   inherited polarizations or index computations, never estimates against the ground energy.
2. **Calibration**: over `𝔽_q` the flow is trivial and the theory reproduces Weil's Hodge index with
   quantized exponents; on the golden datum it fails where the Hodge index fails.
3. **Archimedean source of the square**: the single global square comes from the archimedean
   place; the density of extremal-weight exponents for two primes is used, not avoided.
4. **No-softening compatibility**: the sign is given at degree one, or an index ceiling for the
   Künneth square.
5. **Integrality**: indices and charges are integers, so precision `< 1` suffices along homotopies.
6. **Selectivity**: the inherited structure exists for ζ and fails for flip twins and
   maximal-margin twins; it is built from integers and adeles, never from zero copies.
7. **Profile covariance**: the edge location as a function of the profile's regularity class is a
   theorem.

The field is developed when every question of §5 has a Lean theorem that answers it — an
equivalence, a classification or a no-go — and every tool of §7 is used by a pillar. It succeeds
when a positivity statement on `v₁^⊥` is proved at an RH-complete resolution by an edge-valid
mechanism.

## 12. What counts as a contribution

- A Lean theorem, unconditional, in this folder, wired into the umbrella.
- It is a statement about the degenerating family — its edge, its limit, its flows, its integers,
  its selectivity — or a tool another pillar uses.
- It says which kind of statement it is: identity, inherited polarization, integer invariant,
  estimate (then: in which regime), equivalence with RH, or no-go.
- New objects are built from integers, adeles and Weil's data, never from zero copies.
