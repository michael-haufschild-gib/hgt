# Arithmetic Orientation Geometry (`GaloisForLFunctions.ArithmeticOrientationGeometry`)

**One question.** Weil obtained the sign of the explicit formula for a curve from the geometry of
the Frobenius graph on `C × C`: the Castelnuovo–Severi inequality on the plane spanned by the graph
and the diagonal is the Hasse–Weil bound. The scaling flow of `ℤ` has graphs, Lefschetz numbers
and an adjunction formula of the same shape, but no proof that its graphs satisfy that inequality.
What geometry could supply it, which arithmetic structures can orient the scaling correspondence,
and which provably cannot?

Arithmetic Orientation Geometry (AOG) is the geometry of the **scaling correspondence**. Its basic
object is a cycle together with its orbit under the scales, and its basic invariant is the
**orbit correlation** `c_x(g) = δ(ψ_g x, x)`: the primitive part of the Lefschetz number, the term
that the Hasse–Weil bound controls. A cycle is **oriented** when this correlation stays inside its
Hasse–Weil envelope, `|c_x(g)| ≤ c_x(0)`, at every scale. The programme studies when that happens,
what orientation of one cycle forces, what a correspondence must satisfy to orient its graph, and
which inputs fail for a stated reason on every impure model.

Everything in the programme is unconditional. The Riemann hypothesis appears only inside exact
equivalences or as the conclusion of implications whose premise is named; no premise is asserted.

---

## Place in the research

The programme separates geometric identities from the arithmetic estimate that
would orient a correspondence. The canonical width receivers are equivalent
at their stated quantifiers, so translating between them supplies no smaller
width. Likewise, Lefschetz, adjunction and Rosati identities hold on impure
model data. Their common algebra identifies the required sign but cannot
force it by itself.

The positive foundations are more specific: orientation of a cycle can be
classified by the zeros its orbit sees; its index counts distinct adverse
zeros; its growth rate reads their maximal depth. The archimedean place orients
suitable finite orbit segments. A second index formula measures the global
defect through heat collisions. Each result localizes an arithmetic task while
retaining its unbounded-scale quantifiers. The purpose of AOG is to find a
source-derived geometric input for that task, or establish a sharp obstruction
for a precisely stated class of inputs.

| Programme | Interface |
|---|---|
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Supplies the polar surface, the scaling surface of `ℤ`, the λ-ring, Hecke cycles, the arithmetic Lefschetz number and the Lefschetz–adjunction identity. AOG abstracts them to every scaling datum and studies orbits instead of single cycles. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Supplies sign- and integer-valued invariants of sources: frustration indices, readings and their trichotomy, the critical Wiener algebra and its hulls, the width functor. AOT orients **sources**; AOG orients **correspondences**. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Its two-bump tests are the Weil planes of AOG. A bounded orbit correlation has no top pole (`eq_zero_of_norm_tsum_exp_le`), every two-point minor holding forces the critical line (`exists_minor_fails_of_top`), and the negativity rate of the minors is the maximal depth (`NegativityRateEqualsMaximalDepth`). |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Its envelope law for translated pairings (`translated_pairing_envelope_law`) is the prime-side form of the self-upgrade of orientation. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Its three selectivity classes of conservation laws isolate Bézout-selective laws, the class in that framework that uses the successor structure of `ℤ`. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md), [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md), [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Supply supersolutions, shared allocation and frustration: the second mechanism class of §4. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md), [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Supply signed-flux identities in damping and aperture and the doubly exponential ceiling: the third mechanism class. |
| [Arithmetic Local Divisor Geometry](../ArithmeticLocalDivisorGeometry/README.md) | Retains local multiplicities, exact factor transitions and heat normalization; its collision budgets connect to the second index formula below. |
| [Signed Successor Arithmetic](../SignedSuccessorArithmetic/README.md) and [Arithmetic Defect Rigidity](../ArithmeticDefectRigidity/README.md) | Test additive and cofactor compatibility of the actual Möbius source, with signed estimates still required beyond identities. |
| [Dilution–Crystallization Pincer](../DilutionCrystallizationPincer/README.md) | Supplies the localization of a rate excess to collapsed clusters at doubly exponential height. |

`RHTower`, `Zeta23` and `PNTPlus` supply the explicit formula, zero configurations, the Weil
criterion and sieve bounds.

---

## 1. Why

### 1.1 Weil's argument, read on orbits

Over `𝔽_q` the Frobenius `F` acts on cycles of `C × C`, fixes one fibre class `V`, multiplies the
other by `q`, and its graph `Γ_m = (F^m × id)_* Δ` satisfies

* **Lefschetz:** `Γ_m · Δ = N_m = q^m + 1 − tr(F^m | H¹)`;
* **adjunction:** `Γ_m² = q^m Δ²`;
* **pullback:** `Γ_k · Γ_l = q^l N_{k−l}`;
* **Hodge index** on the plane spanned by `H, V, Γ_m, Δ`, which is the Hasse–Weil bound.

The first three are identities. Only the fourth is a sign. AOG separates the two layers on an
arbitrary **scaling datum**: an additive group of scales acting on a polar surface by isometries
that weight the fibre classes by `e^{± s/2}`. On every scaling datum the three identities hold
(§3.1), so they cannot produce the sign, and the sign becomes a property of orbits: the defect must
be nonnegative on the span of the orbit of a cycle. That property is the positive-definiteness of
one function on the scale group, the orbit correlation.

### 1.2 What changes over `ℤ`

Over `ℚ` the scale group is `ℝ`, the action is logarithmic translation of tests, the Lefschetz
number is the prime comb, and the orbit correlation of a test `f` is Weil's pairing of `f` with its
translates. RH is the statement that every cycle is oriented (§3.1, item 5). Three differences from
the curve case organize the programme:

* **Infinite genus.** A curve has finitely many eigenvalues; the orbit correlation of a curve is a
  finite exponential sum and its orientation is decided by a finite window. Over `ℤ` it is an
  infinite exponential sum and no finite window decides (`Square-Root Threshold`, finite-radius
  mimicry).
* **An archimedean place.** The collar is a positive Dirichlet form, and at each aperture it pays
  everything above a frequency horizon (Arithmetic Castelnuovo–Severi, item 14). Curves and
  lattices have defect `0` or `∞` at every degree; `ζ` has a finite defect at every degree.
* **Additive structure.** `ℤ` has consecutive integers and Bézout relations; Beurling systems do
  not. This supplies one concrete way to distinguish `ζ` from the golden Beurling datum;
  the selectivity classification applies to the specified incidence laws.

### 1.3 What an orientation principle is

An **orientation principle** is a theorem that proves the orbit Hodge index of a class of cycles
from arithmetic input that is stated independently of the sign of the form. The programme's
requirements for such a principle concern its input and quantitative reach:

* *selectivity* — it fails, for a stated reason, on the golden datum, the shifted pair
  `ζ(s − a)ζ(s + a)`, parity twins, cluster configurations and planted Euler factors, and reduces
  to Weil's argument over `𝔽_q`;
* *orientation* — its reading distinguishes the relevant impure data; reflection-odd
  channels and calibrated magnitude readings are two possible mechanisms;
* *cofinality* — it retains the uniformity in scale, aperture, height and rank required
  by the chosen receiver;
* *supra-Nyquist* — it reads information beyond the square-root threshold;
* *rate* — it supplies a quantitative gain, with a fixed zero-free strip as an initial
  global target;
* *source input* — its arithmetic premise is proved from the source; a zero-indexed
  identity or receiver alone does not supply that premise;
* *exactness* — it keeps the Gamma factor, both polar terms and every prime power.

---

## 2. What: objects and language

### 2.1 The dictionary

| Weil's proof over `𝔽_q` | Scaling datum | Over `ℤ` | Lean |
|---|---|---|---|
| Frobenius `F^m` | scale `g ∈ G`, `ψ_g` isometry | translation by `t = log a` | `ScalingDatum`, `zetaScalingDatum` |
| degree `q^m` | `e^{s(g)}` | `a` | `ScalingDatum.scale` |
| graph `Γ_m` | Hecke graph `T_g x = e^{s(g)/2} ψ_g x` | Hecke cycle | `heckeGraph` |
| `N_m = Γ_m · Δ` | Lefschetz number `L(x, g)` | prime comb at `log a` | `lefschetz`, `pair_heckeGraph_diag` |
| `tr(F^m \| H¹)` | orbit correlation `c_x(g)` | `Re W(f(· − t), f)` | `orbitCorr`, `lefschetz_eq` |
| adjunction `Γ_m² = q^m Δ²` | `Γ_g² = e^{s(g)} x²` | archimedean collar | `pair_heckeGraph_self` |
| pullback `Γ_k·Γ_l = q^l N_{k−l}` | `Γ_g·Γ_h = e^{s(h)} L(x, g − h)` | Hecke pullback | `pair_heckeGraph` |
| Weil's decomposition of `N_m` | Lefschetz–adjunction identity | same | `lefschetz_sub_half_selfPair_eq` |
| Hodge index on `⟨H, V, Γ, Δ⟩` | Hasse–Weil at `(x, g)` | two-bump minor | `hasseWeilAt_iff_castelnuovoSeveri_weilPlane` |
| ring of correspondences | finitely supported measures on `G` | Hecke algebra of `ℝ_{>0}` | `Correspondence`, `conv`, `corr_conv` |
| Rosati involution | `ξ′(g) = ξ(−g)` | `k ↦ k̃` | `rosati`, `defect_corr_corr` |
| `π π′ = q` | `T_g T_g′ = e^{s(g)}` | same | `heckeGraph_rosati` |
| positivity of `Tr(ξ ξ′)` | Rosati positivity at `x` | Weil positivity on the orbit of `f` | `rosatiPositive_iff_orbitHodgeIndex` |

### 2.2 Objects

| Object | Meaning | Lean |
|---|---|---|
| Scaling datum | polar surface, scale group `G`, logarithmic scale `s : G →+ ℝ`, isometric action with `ψ_g H = e^{s/2}H`, `ψ_g V = e^{−s/2}V` | `ScalingDatum` |
| Orbit correlation | `c_x(g) = δ(ψ_g x, x)`, even in `g` | `orbitCorr`, `orbitCorr_neg` |
| Lefschetz number | `L(x, g) = T_g x · x = (e^s + 1)(x·H)(x·V) − e^{s/2} c_x(g)` | `lefschetz`, `lefschetz_eq` |
| Weil plane | span of `H, V, ψ_g x, x` | `defect_weilPlane_self` |
| Hasse–Weil at `(x, g)` | `|c_x(g)| ≤ c_x(0)` | `HasseWeilAt` |
| Orbit combination | `Σ_{g ∈ S} c_g ψ_g x` | `orbitComb` |
| Orbit Hodge index | defect `≥ 0` on the orbit span: `c_x` positive definite | `OrbitHodgeIndex` |
| Correspondence | `ξ : G →₀ ℝ`, acting by `ξ · x = Σ ξ(g) ψ_g x` | `Correspondence`, `corr` |
| Trace at a cycle | `τ_x(ξ) = δ(ξ · x, x)` | `traceAt` |
| Rosati positivity | `τ_x(ξ ⋆ ξ′) ≥ 0` for all `ξ` | `RosatiPositive` |

### 2.3 Words

* **Oriented cycle.** A cycle whose orbit has the Hodge index; equivalently (on tempered zero
  configurations) whose orbit correlation is bounded.
* **Orientation index.** The number of negative squares of the defect on the orbit span of a cycle.
* **Orientation rate.** The exponential growth rate of `c_x`; the Hasse–Weil envelope is rate `0`.
* **Selective.** A property is selective when it fails, for a stated reason, on every model of the
  battery (§9).
* **Soft structure.** Identities that hold on every scaling datum, or on every model of the battery:
  Lefschetz, adjunction, pullback, λ-ring, functional equation, Euler product, integrality.
* **Scale-stable family.** A subspace of tests containing every translate of its members; it
  **jointly sees** `ρ` when some member is nonzero at `γ_ρ` and some member is nonzero at `γ̄_ρ`.
* **Damped energy.** `E_x(ε) = sup_{t ≥ 0} e^{−εt}|c_x(t)| ∈ [0, ∞]`.

---

## 3. How: the pillar theorems

### 3.1 Scaling data and Weil planes (`ScalingDataAndWeilPlanes`)

1. **Isometry calculus.** The defect is invariant under every scale (`defect_act`), its adjoint is
   the inverse scale (`defect_act_left`), and two orbit points meet through the difference of their
   scales (`defect_act_act`); the orbit correlation is even (`orbitCorr_neg`).
2. **Lefschetz trace formula and the Lefschetz–adjunction identity on every scaling datum.**
   `L(x, g) = (e^{s} + 1)(x·H)(x·V) − e^{s/2} c_x(g)` (`lefschetz_eq`) and, with `σ = e^{s/2}`,
   `L(x, g) − ((σ² + 1)/2) x² = ((σ − 1)²/2) δ(x, x) + (σ/2) δ(ψ_g x − x, ψ_g x − x)`
   (`lefschetz_sub_half_selfPair_eq`). The coboundary has defect `2δ(x, x) − 2c_x(g)`
   (`defect_coboundary_self`).
3. **Weil planes.** The defect on `⟨ψ_g x, x⟩` is `(r² + t²) δ(x, x) + 2rt c_x(g)`
   (`defect_weilPlane_self`); the pole plane is in its radical (`defect_add_pole`). Hence three
   statements coincide: `|c_x(g)| ≤ c_x(0)`; the Castelnuovo–Severi inequality
   `y² ≤ 2(y·H)(y·V)` on the Weil plane (`hasseWeilAt_iff_castelnuovoSeveri_weilPlane`); and the
   Lefschetz bound `|L(x, g) − (e^s + 1)(x·H)(x·V)| ≤ e^{s/2} δ(x, x)`
   (`hasseWeilAt_iff_lefschetz_bound`). For `x = Δ` of a curve this is `|N_m − q^m − 1| ≤ 2g q^{m/2}`.
4. **Orbit Toeplitz law.** `δ(Σ c_g ψ_g x, Σ c_h ψ_h x) = Σ_{g,h} c_g c_h c_x(g − h)`
   (`defect_orbitComb_self`); the orbit Hodge index gives Hasse–Weil at every scale
   (`hasseWeilAt_of_orbitHodgeIndex`).
5. **Global form.** Hodge index ⟺ every orbit has the Hodge index ⟺ every cycle is Hasse–Weil at
   every scale ⟺ every cycle is Hasse–Weil at scale `0` (`hodgeIndex_tfae`). For `ℤ`
   (`zetaScalingDatum`, with `zetaScalingDatum_lefschetz_log` identifying the arithmetic Lefschetz
   number): RH ⟺ every cycle is Hasse–Weil along its whole orbit
   (`riemannHypothesis_iff_forall_hasseWeilAt`). Globally the statement at all scales adds nothing
   to the statement at scale `0`; per cycle it does, and that is where the programme works.

### 3.2 The correspondence algebra (`TheCorrespondenceAlgebra`)

6. **Action and convolution.** Correspondences act linearly, and convolution is composition
   (`corr_conv`).
7. **Rosati adjoint and trace.** `δ(ξ · x, η · x) = τ_x(ξ ⋆ η′)` (`defect_corr_corr`), with
   `τ_x([g]) = c_x(g)` (`traceAt_single`) and `τ_x(ξ) = Σ ξ(g) c_x(g)` (`traceAt_eq_sum`).
8. **Weil's positivity is the orbit Hodge index.** Rosati positivity of the trace at `x` is the
   orbit Hodge index of `x` (`rosatiPositive_iff_orbitHodgeIndex`): the positivity in Weil's second
   proof, read at a diagonal cycle, is the same statement as the positivity in his first.
9. **Hecke graphs.** Pullback `Γ_g · Γ_h = e^{s(h)} L(x, g − h)` (`pair_heckeGraph`), adjunction
   `Γ_g² = e^{s(g)} x²` (`pair_heckeGraph_self`), Lefschetz `Γ_g · x = L(x, g)`
   (`pair_heckeGraph_diag`), and Weil's relation `T_g T_g′ = e^{s(g)}` (`heckeGraph_rosati`).

### 3.3 The scaling datum of a configuration (`TheScalingDatumOfAConfiguration`)

10. **Every tempered zero configuration is a scaling datum** (`configSurface`,
    `configScalingDatum`): the pairing of the scaling surface with Weil's pairing replaced by the
    zero-side form `Re W_Z`, the scales acting by logarithmic translation. The zeros of `ζ`, of a
    curve, of the golden datum and of cluster models are instances of one theory. Its defect is the
    zero-side form (`configSurface_defect`); configurations on the line have the Hodge index
    (`configSurface_hodgeIndex_of_onLine`).
11. **Translation law and orbit correlation.** Translating the two tests by `s, t` multiplies the
    summand at `ρ` by `e^{(s − t)(ρ − ½)}` (`Wsummand_scaleShift`); the orbit correlation is the
    exponential sum `c_f(t) = Re Σ_ρ e^{t(ρ − ½)} m_ρ h_f(γ_ρ) conj h_f(γ̄_ρ)`
    (`configScalingDatum_orbitCorr_eq`).
12. **For `ζ` the explicit formula identifies the zero-side datum with the scaling datum of `ℤ`**
    (`configWeil_zeta_eq_weilPair`, `configSurface_zeta_eq`).

### 3.4 The orientation of a cycle (`TheOrientationOfACycle`)

13. **The orientation theorem** (`orientation_tfae`). On a tempered configuration symmetric under
    the functional equation, for every cycle: Hasse–Weil at every scale ⟺ orbit Hodge index ⟺ the
    transform of the cycle vanishes at one point of every off-line reflection pair
    (`BlindOffLine`). Blindness orients on every tempered configuration
    (`orbitHodgeIndex_of_blindOffLine`): every orbit combination has transform `P(z) h_f(z)`
    (`paperFT_orbitTest`), so only on-line terms `m |h(γ)|² ≥ 0` survive. The converse is the
    **self-upgrade** (`blindOffLine_of_hasseWeil`): Hasse–Weil at every scale bounds an exponential
    sum, which then has no top pole (Square-Root Threshold); the orbit correlation of a real test
    is real on symmetric configurations (`W_real_of_fes`).
14. **The oriented locus** (`blindOffLine_orbitTest`) is stable under correspondences: it is a
    union of correspondence-stable subspaces, one for each choice of a point in every off-line pair.
15. **One generic orbit decides** (`onLine_iff_hasseWeil_of_generic`). Real tests whose transform
    vanishes at no zero exist on every configuration (`exists_realSpectrallyGeneric`, by dilating
    a bump off a countable set). For `ζ` (`zeta_orientation_iff`,
    `riemannHypothesis_iff_hasseWeil_of_generic`, `exists_orbit_deciding_riemannHypothesis`): a
    cycle of `ℤ` is oriented iff it is blind to the off-line zeros of `ζ`, and RH holds iff one
    real spectrally generic test satisfies `|W(f, f(· − t))| ≤ W(f, f)` for every `t`.

### 3.5 Euler factors and payment (`EulerFactorsAndPayment`)

16. **Tail law** (`receiverBounded_roughMoebius_iff`, `paidIdeal_roughMoebius_eq`,
    `obstructionHull_roughMoebius_eq`). For every finite set `P` of primes, deleting the Euler
    factors at `P` from the damped Möbius receiver changes neither payment, nor the repairing ideal,
    nor the obstruction hull: one factor is removed by the convolution identity
    `μ_ε^{(P)} = (δ₁ − p^{−ε}δ_p) ⋆ μ_ε^{(P ∪ {p})}` (`roughMoebius_eq_localFactor_conv`) and local
    factors are units.
17. **Absolute convergence decides, and only there** (`isWienerUnit_moebius_of_half_lt`,
    `not_criticalWiener_moebius`). For `ε > ½`, `μ_ε` is a unit of `𝒲_{1/2}` with inverse `d^{−ε}`;
    for `ε ≤ ½` it is not even in the algebra (`Σ |μ(d)| d^{−ε−½} ≥ Σ_p 1/p`).

### 3.6 The archimedean place orients orbit segments (`TheArchimedeanPlaceOrientsOrbitSegments`)

18. **Unconditional orientation of orbit segments** (`orbitSegment_defect_nonneg_of_lowBlind`,
    `hasseWeilAt_of_lowBlind`). If `f` is supported in `[−a, a]` and its transform vanishes at the
    pole and on the low-frequency grid of aperture `a + T/2`, the defect of `ζ` is nonnegative on
    every combination of the translates `f(· − s)`, `0 ≤ s ≤ T`, and `f` is Hasse–Weil at every
    scale `|t| ≤ T`. The number of linear conditions grows doubly exponentially in `T`.

### 3.7 The orientation rate (`TheOrientationRateIsTheDepthOfTheDeepestSeenZero`)

19. **The orientation rate theorem** (`orbitCorr_rate_iff_blindAbove`). On a symmetric tempered
    configuration, for `σ ≥ 0`, the orbit correlation of a cycle satisfies `|c_f(t)| ≤ K e^{σt}` iff
    the cycle sees no zero deeper than `σ` (`BlindAbove`). The upper rate holds on every tempered
    configuration (`orbitCorr_le_of_blindAbove`); the lower rate is the top-pole argument
    (`blindAbove_of_orbitCorr_le`). The exponent of a cycle is the depth of the deepest zero it
    sees; `σ = 0` is the orientation theorem.
20. **For `ζ` one generic orbit reads the zero width**
    (`zeta_orbitCorr_rate_iff_zetaZeroWidth_le`): `|W(f, f(· − t))| ≤ K e^{σt}` iff
    `zetaZeroWidth ≤ σ`. Its first improvement below `σ = ½` is a zero-free strip.

### 3.8 The selectivity battery (`TheSelectivityBatteryOfOrientation`)

21. **Curves.** Curve configurations are symmetric under the functional equation
    (`fesSymmetric_curveConfig`); unitary curves orient every cycle
    (`unitaryCurve_orbitHodgeIndex`).
22. **Soft structure does not orient** (`golden_soft_structure_and_disorientation`). The golden datum
    `1 − 5X + 5X²` has a Beurling system with nonnegative prime counts, an integral zeta series and
    the functional equation; its configuration is a scaling datum, so every identity of §3.1–3.2
    holds; every zero has depth `log φ/log 5` (`abs_re_sub_half_goldenConfig`); and the orbit of a
    generic real test is not oriented, with orientation rate exactly `log φ/log 5`
    (`golden_not_oriented`, `golden_orbitCorr_rate_iff`).
23. **Orientation is blind to multiplicity** (`orientation_congr_carrier`,
    `orientationRate_congr_carrier`): configurations with the same zeros orient the same cycles at
    the same rates.

### 3.9 Sections on the orbit of a cycle (`SectionsOnTheOrbitOfACycle`)

24. **The orbit surface.** The span of `H, V` and the orbit of `x` carries the restricted polar
    structure (`orbitSurface`); it is scale-stable when the scales act on the fibres by scalars
    (`FibreCompatible`, `map_act_orbitSpan_le`). Each of its classes is a pole-plane class plus the
    action of a correspondence (`exists_eq_corr_of_mem_orbitSpan`), so its Hodge index is the orbit
    Hodge index of `x` (`orbitSurface_defect_nonneg_iff`).
25. **Riemann–Roch on an orbit is orientation** (`orbitSurface_riemannRoch_iff`,
    `configOrbitSurface_riemannRoch_iff_blind`): an ample section cone of nonnegative degree on the
    orbit surface of `x` satisfies Riemann–Roch iff it contains the open positive cone and `x` is
    oriented — on a configuration, iff `x` is blind to the off-line zeros.

### 3.10 Eventual Hasse–Weil is Hasse–Weil (`EventualHasseWeilIsHasseWeil`)

26. **The tensor-power trick on orbits** (`blindAbove_of_eventually_le`,
    `hasseWeilAt_of_eventually_bounded`). On a symmetric tempered configuration, if the orbit
    correlation of `x` is bounded, by any constant, at all sufficiently large scales, then `x`
    satisfies the sharp Hasse–Weil bound at every scale; more generally an eventual bound
    `K e^{σt}` gives blindness above depth `σ`. Over `𝔽_q` this is the classical fact that bounds on
    `N_m` for large `m`, with any constant, imply the sharp bound for every `m`.
27. **For `ζ`** (`riemannHypothesis_iff_eventually_bounded_of_generic`): for a spectrally generic real
    test, RH holds iff `W(f, f(· − t))` stays bounded as `t → ∞`.

### 3.11 The orientation index of a cycle (`TheOrientationIndexOfACycle`)

28. **The seen configuration** (`seenConfig`). The zeros a test sees — those at which its transform
    vanishes at neither point of the reflection pair — form a tempered configuration on which the
    test is spectrally generic, and on the orbit of the test the Weil form of `Z` equals that of the
    seen configuration (`W_translate_seenConfig`).
29. **The orientation index law** (`orientationIndex_law`, `orientationIndex_eq_zero_iff`). For shifts
    dense in `[0, ∞)`, the negative index of the Weil Gram matrices of translates of a real test
    reaches `n` iff the test sees at least `n` zeros right of the line. The orientation index of a
    cycle is the number of right zeros it sees; no functional-equation symmetry is needed. For `ζ`
    with the Weil form computed from primes, Gamma factor and pole: `zeta_orientationIndex_law`.
30. **The signature of an orbit surface** (`zeta_orbit_signature_law`). The intersection Gram matrix
    of the pole plane and translates of a real test has one positive square plus one for every
    right zero of `ζ` the test sees. On an orbit, the continuum signed form of `ζ` — archimedean
    collar, prime atoms and pole — has exactly as many negative squares as the cycle sees right
    zeros: this is the continuum frustration count of the orbit.

### 3.12 Correctors and the Lefschetz trace (`CorrectorsAndTheLefschetzTrace`)

31. **Lefschetz trace of a correspondence** (`lefschetzTrace_eq`):
    `L(x, ξ) = poleTrace(ξ)·(x · H)(x · V) − Σ_g ξ(g) e^{s(g)/2} c_x(g)`.
32. **Conservation law for correctors** (`lefschetzTrace_of_corrector`,
    `lefschetzTrace_of_corrector_add_pole`). A corrector — a correspondence with vanishing pole
    trace — has Lefschetz trace equal to minus its primitive trace, independent of the fibre
    degrees of the cycle: relative compensation turns the Lefschetz trace into absolute energy read
    only by the defect. Its sign under the orbit Hodge index is `traceAt_rosati_nonneg`.

### 3.13 A second index formula: heat collisions (`TheIndexExit`)

Let `D` be the global Hodge defect, the number of distinct right zeros. If
`D` is finite, let `E=Σ_{Re ρ>½}(m_ρ−1)` be their multiplicity excess. For all
sufficiently small positive de Bruijn–Newman heat times,

`collisionMassAfter(t) = 2(D+E)`.

If the off-line divisor is infinite, the future collision mass diverges as
`t↓0`. Thus a uniform finite bound on heat counts, future collision mass or
horizontal collision charges is equivalent to finitely many off-line zeros,
not to RH. It implies a zero-free strip `Θ<1`; it still permits finite
exceptions. Conjugation makes the finite distinct-right-zero count even, so
`D<2` is exactly RH. See [TheIndexExit.lean](TheIndexExit.lean).

The second formula connects orientation to a dynamical count and exposes the
multiplicity excess discarded by the Hodge index. Since both terms on its
right are nonnegative, nonnegativity of collision mass supplies no upper
bound. A useful producer must bound that mass uniformly towards heat zero,
and reach the appropriate integer threshold.

### 3.14 The shifted pair and the cluster models (`TheShiftedPairAndTheClusterModels`)

33. **A generic orbit reads the depth of every zero** (`generic_orbitCorr_rate_iff`,
    `generic_not_oriented`): on a symmetric tempered configuration the orbit correlation of a
    spectrally generic test grows at most like `e^{σt}` iff every zero has depth at most `σ`.
34. **The shifted pair of a curve** (`curveShiftedPair`). `ζ_C(s − a)ζ_C(s + a)` is again a curve
    datum, with eigenvalues `q^{±a}β_i`: conjugation- and functional-equation-closed, tempered, a
    scaling datum. Its Frobenius traces are those of the curve times `q^{am} + q^{−am}`
    (`powerSum_curveShiftedPair`), the analogue of the weights `Λ(n)(n^a + n^{−a})` of
    `ζ(s − a)ζ(s + a)`; it is impure for `a ≠ 0` (`curveShiftedPair_not_pure`). For a curve satisfying
    RH every zero has depth exactly `a` (`abs_re_sub_half_shiftedPairConfig`), a generic orbit has
    orientation rate exactly `a` (`shiftedPair_orbitCorr_rate_iff`) and is not oriented
    (`shiftedPair_not_oriented`).
35. **Height averages do not see a cluster; one generic orbit does**
    (`fesSymmetric_clusterConfig`, `cluster_orbitCorr_rate_iff`,
    `cluster_heightAverages_blind_orbit_not`). On a cluster with symmetric depth profile and
    `r · TV(d) · sinh(2δr) ≤ 1`, every windowed Weil form at resolution `r` is nonnegative, for tests
    of every aperture, while a generic orbit is not oriented and its orientation rate is the
    maximal depth.

### 3.15 Scale-stable families (`TheOrientationOfScaleStableFamilies`)

36. **Joint seeing is seeing** (`jointlySees_iff`, `jointlyBlind_iff_forall_blind`). If `f₁` misses
    `γ̄_ρ` and `f₂` misses `γ_ρ`, then `f₁ + f₂` sees `ρ`; a family is jointly blind iff every member
    is blind.
37. **The orientation of a family** (`scaleStable_nonneg_iff_jointlyBlind`,
    `zeta_scaleStable_nonneg_iff_jointlyBlind`). On a symmetric tempered configuration the Weil form
    is nonnegative on a scale-stable family iff the family is jointly blind: at every off-line pair
    all members vanish at the same point. For `ζ` the form is computed from primes, Gamma factor
    and pole.
38. **The oriented subspaces** (`orientedSubspace`, `scaleStable_nonneg_iff_le_orientedSubspace`). A
    choice of one point in every off-line pair defines a scale-stable, jointly blind subspace; the
    oriented scale-stable families are exactly their subfamilies.
39. **The index of a family** (`negIndex_family_le`, `exists_mem_sees`, `scaleStable_index_law`). On
    every tempered configuration the negative index of the Weil form on a scale-stable family is the
    number of right zeros it jointly sees; the bound holds for every finite family of members, and it
    is attained on the orbit of one generic member. This is the frustration count beyond single
    orbits.
40. **Riemann–Roch on the surface of a family** (`familySurface_riemannRoch_iff`): an ample section
    cone of nonnegative degree satisfies Riemann–Roch iff it contains the open positive cone and the
    family is jointly blind. The span of finitely many orbits jointly sees `ρ` iff some test is
    nonzero at `γ_ρ` and some test is nonzero at `γ̄_ρ` (`jointlySees_orbitFamily_iff`): orientation is
    not additive.

### 3.16 The theta `h⁰` of `Spec ℤ` (`TheThetaH0OfSpecZ`)

41. **An arithmetic `h⁰` with an independent Riemann–Roch** (`arithH0`, `arithH0_riemannRoch`). For
    the Arakelov divisor of degree `d`, `h⁰(d) = log Σ_{n ∈ ℤ} e^{−πn²e^{−2d}}`, and
    `h⁰(d) − h⁰(−d) = d` by Poisson summation (`thetaSum_inv`). No positivity of any form is used.
42. **Effectivity, vanishing, asymptotics** (`arithH0_pos`, `arithH0_strictMono`,
    `tendsto_arithH0_atBot`, `tendsto_arithH0_sub_atTop`): `h⁰ > 0` is strictly increasing,
    `h⁰ → 0` as `d → −∞`, and `h⁰(d) − d → 0` as `d → ∞`.
43. **`Λ(s)` is the generating function of `h⁰`** (`completedRiemannZeta_eq_mellin_arithH0`): for
    `Re s > 1`, `π^{−s/2}Γ(s/2)ζ(s)` is half the Mellin transform at `s/2` of `e^{h⁰} − 1` in
    `t = e^{−2d}`.
44. **The pole plane** (`poleH0_riemannRoch`). On every polar surface, `D = aH + bV` and
    `D^∨ = a⁻¹H + b⁻¹V` satisfy `h⁰(D) − h⁰(D^∨) = log(D²/2)`. This Riemann–Roch is that of the base:
    it gives the functional equation and holds on every datum that has one. The Hodge index needs
    Riemann–Roch on the surface, for classes with a test component.

### 3.17 Correctors in the damping parameter (`CorrectorsInTheDampingParameter`)

45. **Damping automorphisms** (`damp_conv`, `damp_damp`, `damp_zero_left`, `rosati_damp`,
    `traceAt_damp`). Weighting by the character `e^{−εs(g)}` is an automorphism of the
    correspondence algebra, additive in `ε`, and it conjugates the Rosati involution to the
    opposite damping: `(α_ε ξ)′ = α_{−ε}(ξ′)`. The damped trace pairs `ξ` with the one-sided damped
    correlation `e^{−εs(g)} c_x(g)`.
46. **Damped correctors exist on every pair of scales** (`isCorrector_damp_twoPoint`,
    `lefschetzTrace_damp_of_corrector`): `c(h)[g] − c(g)[h]`, `c(k) = e^{−εs(k)}(e^{s(k)} + 1)`, has
    vanishing damped pole trace, and its damped Lefschetz trace is minus its primitive trace.
47. **Relative to absolute without loss** (`dampedEnergy_lt_top_iff_blindAbove`, `dampedEnergy_tfae`,
    `riemannHypothesis_iff_forall_damped_bounded`). On a symmetric tempered configuration `E_x(ε)` is
    finite iff `x` is blind above depth `ε`, and the following are equivalent: `x` is oriented;
    `E_x(0) < ∞`; `E_x(ε) < ∞` for every `ε > 0` with no control of the constants as `ε ↓ 0`;
    `E_x(ε) = c_x(0)` for every `ε ≥ 0`. For `ζ` and one generic test this is RH.

### 3.18 Quantitative readings on curve orbits (`QuantitativeReadingsOnCurveOrbits`)

48. **The tower reads the Frobenius traces** (`curve_orbitCorr_tower`): for a test supported in an
    interval shorter than `log q`, `c_f(ν log q) = log q · ‖f‖² · Re Σ_i β_i^ν`.
49. **Turán's reading** (`exists_orbitCorr_ge_turan`, `exists_not_hasseWeilAt_window`). If
    `|β_i| ≥ Z₀ > 0` for some `i`, every window `M < ν ≤ M + 2g` contains a scale with
    `|c_f(ν log q)| ≥ log q · ‖f‖² · Z₀^ν / C(2g, M)`, `C(N, M) = 2eN(6(N + 1)(M + 2N + 2))^N`; if
    `Z₀ ≥ 1` and `2g · C(2g, M) < Z₀^{M+1}`, the Hasse–Weil bound fails in that window.
50. **Violations recur in every late window** (`eventually_exists_not_hasseWeilAt`,
    `golden_eventually_exists_not_hasseWeilAt`): an impure curve violates the bound in every window
    of `2g` consecutive tower scales beyond some point; the golden datum in every late pair of
    consecutive powers of `5`. The precision cost is governed by the number `2g` of terms of the
    exponential sum.

### 3.19 Inherited pillars

The following corpus theorems are the foundations of AOG in other languages; AOG states and uses
them in the language of orbits.

* **Bounded orbit correlations have no top pole** (Square-Root Threshold,
  `eq_zero_of_norm_tsum_exp_le`), and **every two-point minor holding forces the line**
  (`exists_minor_fails_of_top`, `weil_nonneg_iff_onLine`): on a tempered configuration, Hasse–Weil
  along the orbit of a modulated bump forces its off-line weights to vanish.
* **The negativity rate of a Weil plane is the maximal depth** (`NegativityRateEqualsMaximalDepth`).
* **The Hodge defect counts the right zeros** and **lives on one Hecke orbit**
  (Arithmetic Castelnuovo–Severi, `zeta_hodgeDefect_iff`, `cyclic_pontryagin_law`).
* **The arithmetic Lefschetz–adjunction identity and the envelope cone**
  (`arithLefschetz_eq_selfPair_add_defect_add_adamsVar`, `lefschetzEnvelopeCone_riemannRoch_tfae`).

---

## 4. Mechanisms

AOG reads every candidate orientation mechanism as a way to prove the orbit Hodge index.

* **Positivity of correspondences.** Prove `τ_x(ξ ⋆ ξ′) ≥ 0` from a geometric property of the
  graphs. Over `𝔽_q` the property is the Hodge index of `C × C`, supplied by Riemann–Roch. On a
  scaling datum the identities of §3.1–3.2 hold without it.
* **Contraction with a supersolution.** Write the defect on the orbit span as a Dirichlet form with
  a positive part (the archimedean collar) and signed atoms (the primes), and prove nonnegativity
  from a positive supersolution (Allegretto–Piepenbrink, Beurling–Deny).
* **Signed-flux conservation.** Find a functional of the orbit whose derivative along a flow is a
  boundary flux of forced sign.
* **Self-upgrade.** On a configuration, orientation of one cycle is equivalent to boundedness of
  its orbit correlation, which is a growth statement; positivity follows from a rate.
* **Compute, then bound.** Every positivity statement of the programme is one term of an exact
  identity: Lefschetz, adjunction, Toeplitz, Rosati.

---

## 5. Traps

| Trap | What is true instead |
|---|---|
| Lefschetz, adjunction and pullback orient the graph | They hold on every scaling datum, including the golden curve datum, which violates Hasse–Weil. |
| Hasse–Weil at all scales is stronger than at scale `0` | Globally they are equivalent (`hodgeIndex_tfae`); the distinction is per cycle. |
| Weil's second proof avoids the Hodge index | Rosati positivity at `x` is the orbit Hodge index of `x` (`rosatiPositive_iff_orbitHodgeIndex`). |
| A cycle oriented on a finite scale window is oriented | Finite windows admit off-line mimics (Square-Root Threshold). |
| The orientation of a cycle is a sign condition | On a configuration it is a growth condition: bounded orbit correlation. |
| Positivity of the prime atoms orients | Positive prime counts hold on the golden datum and bound only `tr F^m ≤ q^{m/2} + q^{−m/2}`. |
| A sieve upper bound is half an orientation | It bounds counts by a constant multiple of the main term, never deviations at the square-root scale; impure Beurling data satisfy it. |
| One generic cycle suffices, so orientation is easy to test | One spectrally generic cycle carries the whole defect, but proving its orientation is RH. |
| Euler-product structure decides repair | It decides only where the product converges absolutely (`ε > ½`); every finite set of Euler factors is invisible to payment below. |
| The archimedean place orients a cycle | It orients every finite orbit segment of a sufficiently blind cycle, at a cost growing doubly exponentially with the length, never a whole orbit. |
| Orientation is additive | Two cycles blind at opposite points of an off-line pair span a family that sees it (`jointlySees_orbitFamily_iff`); the oriented locus is a union of oriented subspaces, one for each choice. |
| An arithmetic `h⁰` with an independent Riemann–Roch would orient | The theta `h⁰` of `Spec ℤ` has one (`arithH0_riemannRoch`); it yields the functional equation. Orientation needs Riemann–Roch on the surface. |
| Damped bounds lose the absolute energy as `ε ↓ 0` | On an orbit, finiteness of the damped energy at every `ε > 0`, with arbitrary constants, gives `E_x(ε) = c_x(0)` (`dampedEnergy_tfae`). |
| Height averages read clusters | Windowed forms are blind to small-variation clusters; one generic orbit reads the maximal depth (`cluster_heightAverages_blind_orbit_not`). |

---

## 6. Questions the programme aims to answer

1. **Arithmetic sections.** What is an arithmetic section of a cycle on the scaling surface, and
   why would it satisfy Riemann–Roch from an independent source law? The structural
   criterion is established (§3.9): on the
   orbit surface of a cycle, an ample section cone of nonnegative degree satisfies Riemann–Roch iff
   the cycle is oriented. Sections with Riemann–Roch exist exactly over the oriented locus, and
   an independent arithmetic proof of this criterion remains open. Logical equivalence
   to the sign does not preclude an independent geometric proof. Beyond single orbits the
   criterion holds for every scale-stable family (§3.15). An `h⁰` defined from arithmetic with a
   Riemann–Roch proved without the sign exists on the base (§3.16); there it is the functional
   equation.
2. **Frustration against subsidy.** Why would prime-sum frustrations cost less than the archimedean
   subsidy uniformly in aperture? Answered on orbits (§3.4, §3.6, §3.11): on the orbit of a cycle
   the continuum signed form has exactly as many negative squares as the cycle sees right zeros;
   the subsidy pays every frustration along the orbit iff the cycle is blind to the off-line zeros,
   and along every finite segment for a sufficiently low-blind cycle. Uniformly in aperture for all
   cycles it is RH. Beyond orbits (§3.15) the negative index of a scale-stable family is the number
   of right zeros it jointly sees. Arithmetic Orientation Theory supplies the frustration counts
   (prime sums, matched samples) on finite samples.
3. **Anti-collapse.** Which arithmetic invariant prevents `log γ` off-line multiplicity from
   collapsing into a unit window at doubly exponential height? Answered for orientation (§3.8):
   none is needed. Which cycles are oriented, and at which rate, depends only on the set of zeros,
   never on multiplicities. An anti-collapse principle enters only mass floors, where multiplicity
   is mass (Arithmetic Continuation and Critical Energy, the cluster dichotomy); for orientation the
   problem is depth, not collapse.
4. **Relative to absolute.** What conserved quantity converts relative compensation into absolute
   energy at every fixed small damping? On the scale flow (§3.12) the Lefschetz trace of correctors:
   a correspondence with vanishing pole trace has Lefschetz trace equal to minus its primitive trace,
   exactly and independently of the fibre degrees. Damping acts on correspondences by automorphisms,
   and damped correctors exist at every damping (§3.17). On orbits the conversion is lossless: the
   damped energy `E_x(ε)` is finite iff `x` is blind above depth `ε`, and finiteness at every `ε > 0`,
   with constants arbitrary as `ε ↓ 0`, gives `E_x(ε) = c_x(0)` (`dampedEnergy_tfae`). The identities
   do not supply the finiteness; that is the orientation. In the damping picture of the source the
   corresponding identities are those of Arithmetic Continuation and Critical Energy and Arithmetic
   Compensation Theory.
5. **Euler products and repair.** When is the repairing ideal of the damped Möbius source the whole
   critical Wiener algebra, and can Euler-product structure on the Bohr polydisk decide it?
   Answered (§3.5): the ideal is the whole algebra iff the receiver is paid (Arithmetic Orientation
   Theory), which holds above the zero width. Euler-product structure decides it exactly where the
   product converges absolutely, `ε > ½`, where `μ_ε` is a unit; for `0 < ε ≤ ½` every finite set of
   Euler factors is invisible to payment, to the ideal and to the hull, and the full product is not
   in the algebra. Repair below half damping must use cancellation across infinitely many primes.
6. **The Frobenius graph.** Is there an arithmetic correspondence on the scaling surface playing the
   role of the Frobenius graph? Answered for the identities (§3.1–3.2): the Hecke graphs `T_g x`
   have Lefschetz, pullback, adjunction and `ππ′ = q`, and Hasse–Weil for `(x, g)` is exactly
   Castelnuovo–Severi on their Weil plane. The positivity is decided per orbit (§3.4): a cycle is
   oriented iff it is blind to the off-line zeros, and one generic orbit decides RH. Open: a
   geometric proof of the positivity.
7. **Orientation-faithful readings.** Which readings are orientation-faithful for the actual `ζ`
   source, and what does each cost? Partial (§3.4, §3.6): the orbit correlation of one spectrally
   generic real test is faithful for the actual `ζ` — it is bounded by its value at `0` iff RH. The
   archimedean place certifies it on every finite segment `[0, T]` for cycles blind to the grid
   `D_{a + T/2}`, at a doubly exponential number of linear conditions, and on no infinite one. Over
   `𝔽_q` the reading is explicit (§3.18): every late window of `2g` tower scales detects an impure
   eigenvalue with precision `Z₀^ν / C(2g, M)`, a cost exponential only in the genus. Generic orbits
   read the depth of every battery model (§3.14), including clusters that height averages miss.

## 7. Tools the programme builds

Built:

- *Scaling data*: isometry calculus, orbit correlations, Lefschetz numbers, the Lefschetz–adjunction
  identity, Weil planes and the three forms of Hasse–Weil, orbit Toeplitz law, global equivalences.
- *The correspondence algebra*: action, convolution, Rosati involution, traces at cycles, Rosati
  positivity, Hecke graphs with pullback, adjunction and `ππ′ = q`.
- *Configuration scaling data*: every tempered zero configuration as a scaling datum, the
  translation law, the orbit correlation as an exponential sum over zeros, the explicit-formula
  identification for `ζ`.
- *The orientation theorem*: blindness, self-upgrade, the oriented locus, real generic tests, the
  one-orbit criterion for RH.
- *Euler factors on the Bohr polydisk*: rough Möbius weights, the one-factor convolution identity,
  the tail law of payment, the absolute-convergence dichotomy at `ε = ½`.
- *Archimedean orientation*: recentred orbit combinations and the orientation of orbit segments
  of low-blind cycles.
- *Orientation rates*: blindness above a depth, the upper and lower rate laws, the zero width as the
  rate of a generic orbit.
- *The battery*: curve configurations, unitary curves, the golden curve, multiplicity-blindness.
- *Orbit surfaces*: restriction of polar surfaces, fibre compatibility, orbit spans as
  correspondence images, Riemann–Roch on an orbit.
- *Orientation index*: seen configurations and the orbit Pontryagin law for arbitrary cycles.
- *Self-improvement*: eventual bounds on orbit correlations upgrade to the sharp bound.
- *Corrector theory on the scale flow*: Lefschetz, pole and primitive traces; correctors and their
  conservation law.
- *Families beyond single orbits*: joint seeing, scale-stable families, oriented subspaces, the index
  of a family, surfaces of families and their Riemann–Roch.
- *Arakelov `h⁰` of the base*: the theta `h⁰` of `Spec ℤ`, its Riemann–Roch, effectivity and vanishing,
  `Λ(s)` as its generating function, the pole-plane `h⁰`.
- *Damping*: damping automorphisms of the correspondence algebra, damped correctors, the damped orbit
  energy and its lossless cofinal limit.
- *Quantitative readings*: the tower identity for curve orbits, Turán's reading with explicit
  precision, recurrence of violations in every late window.
- *Battery models*: the shifted pair of a curve, symmetric clusters, the generic depth law.

To be built:

- an arithmetic `h⁰` on the surface, for classes with a test component, with a Riemann–Roch proved
  without the sign; exact index laws for families that are not scale-stable; quantitative readings
  over `ℤ`, where the orbit correlation has infinitely many terms; the shifted pair over `ℤ` as a
  zero-side datum. Arithmetic anti-concentration is not needed for orientation (§3.8); it remains a
  tool for mass floors.

## 8. Research boundaries and open questions

1. **The shifted pair over `ℤ` and parity twins.** The shifted pair of a curve and symmetric
   clusters are in the battery (§3.14). The zeros `ρ ± a` of `ζ(s − a)ζ(s + a)` leave the strip
   `0 ≤ Re ≤ 1` unless the zero width is below `½ − a`, so its zero-side datum needs another
   normalization; the parity twins remain to be placed.
2. **Orientation index on the lattice of scales.** ACS already classifies finite and
   well-founded prime-tower visibility, exhibits the Wolff obstruction at a non-attained
   top, and proves two-prime completeness. The remaining single-tower question concerns
   arbitrary cycles beyond those visible classes, especially exclusion of Wolff-type
   accumulation for the actual divisor. State which tower and visibility hypothesis a
   proposed index formula uses.
3. **Infinite Euler data.** Which properties of the infinitely many local factors of `μ_ε`
   (equidistribution of `p^{it}`, sign patterns, densities) can repair it below half damping, now that
   every finite set of factors is invisible?
4. **Cheaper archimedean orientation.** Lower the doubly exponential cost of orienting an orbit
   segment of length `T`, or prove it necessary.
5. **Bézout-selective orientation.** Which laws driven by `gcd(n, n + 1) = 1` and `pa − qb = 1`
   carry a signed estimate on orbits, and which of them fail on Beurling systems?
6. **A source bound on the collision index.** The exact heat-count identity and equivalence
   of finite bounds are established (§3.13). Produce an independent bound uniform as heat
   tends to zero, first to exclude infinitely many exceptions, then below the first
   nonzero quantum. Multiplicity and the distinction between horizontal and heat charge
   must remain explicit.
7. **Mechanism equivalence.** Are the three mechanism classes of §4 equivalent on scaling data, and
   which fails first on each battery model?

---

## 9. Success criteria and contributions

**The programme succeeds** when it proves the orbit Hodge index of a cofinal class of cycles from
an input that passes the selectivity battery, or when it proves that no input from a stated class
of arithmetic data can — in either case reducing over `𝔽_q` to Weil's argument.

**A contribution must**

* be an unconditional Lean theorem in this folder, wired into the umbrella;
* be stated in the language of scaling data, orbits, Weil planes and correspondences;
* state what it gives on the golden datum and on the shifted pair, and over `𝔽_q`;
* give an identity wherever Weil's step is an identity, and record the positive survivor of every
  no-go;
* name the mechanism class it belongs to.

**The selectivity battery.** A theorem that claims to orient must fail, for a stated reason, on:
the golden datum `1 − 5X + 5X²` (integral, functional equation, positive prime counts, impure);
the shifted pair `ζ(s − a)ζ(s + a)`; parity twins; cluster configurations with `ζ`-type local
counts; planted Euler factors; finite-window mimics.

## 10. Principles

1. **Identities first, sign last.** Separate what holds on every scaling datum from what does not.
2. **Work per orbit.** Global positivity is one statement; the information is in which cycles are
   oriented.
3. **Calibrate over `𝔽_q`.**
4. **Selectivity is a theorem.** Every positivity claim carries its failure on the battery.
5. **Do not mistake a reformulation for a reduction.**
6. **Search the corpus first**: `scripts/formal_tools.py research "<query>"`.

---

## Source entry points

| Module | Content |
|---|---|
| `ScalingDataAndWeilPlanes` | scaling data, orbit correlation, Lefschetz trace formula, Lefschetz–adjunction identity, Weil planes, orbit Toeplitz law, orbit Hodge index, global equivalences, the scaling datum of `ℤ` |
| `TheCorrespondenceAlgebra` | correspondences, convolution, Rosati involution, traces at cycles, Rosati positivity, Hecke graphs, pullback, adjunction, `ππ′ = q` |
| `TheScalingDatumOfAConfiguration` | configuration surfaces and scaling data, translation law, orbit correlation as an exponential sum, explicit-formula identification for `ζ` |
| `TheOrientationOfACycle` | blindness, the orientation theorem, self-upgrade, oriented locus, real generic tests, one-orbit RH criterion |
| `EulerFactorsAndPayment` | rough Möbius weights, tail law of payment, ideal and hull, absolute-convergence dichotomy |
| `TheArchimedeanPlaceOrientsOrbitSegments` | recentred orbit combinations, orientation of orbit segments of low-blind cycles |
| `TheOrientationRateIsTheDepthOfTheDeepestSeenZero` | blindness above a depth, upper and lower rate laws, the zero width as the rate of a generic orbit |
| `TheSelectivityBatteryOfOrientation` | functional-equation symmetry of curve configurations, unitary curves, the golden curve, multiplicity-blindness |
| `SectionsOnTheOrbitOfACycle` | restricted polar surfaces, orbit surfaces, fibre compatibility, Riemann–Roch on an orbit |
| `EventualHasseWeilIsHasseWeil` | eventual rate bounds, the tensor-power trick on orbits, RH from eventual boundedness of one orbit |
| `TheOrientationIndexOfACycle` | seen zeros and seen configurations, the orientation index law, the signature of an orbit surface |
| `TheIndexExit` | Hodge defect versus future heat collision mass, multiplicity excess, equivalent finite-count bounds, quasi-RH consequence and even index quantization |
| `CorrectorsAndTheLefschetzTrace` | Lefschetz, pole and primitive traces of correspondences, correctors and the conservation law |
| `TheShiftedPairAndTheClusterModels` | generic depth law, the shifted pair of a curve, symmetric clusters versus height averages |
| `TheOrientationOfScaleStableFamilies` | joint seeing, orientation and index of scale-stable families, oriented subspaces, surfaces of families |
| `TheThetaH0OfSpecZ` | theta sum, arithmetic `h⁰` of `Spec ℤ`, Riemann–Roch, vanishing and asymptotics, `Λ` as generating function, pole-plane `h⁰` |
| `CorrectorsInTheDampingParameter` | damping automorphisms, damped correctors, damped orbit energy, lossless cofinal limit |
| `QuantitativeReadingsOnCurveOrbits` | tower identity for curve orbits, Turán's reading, explicit violating windows, recurrence of violations |
