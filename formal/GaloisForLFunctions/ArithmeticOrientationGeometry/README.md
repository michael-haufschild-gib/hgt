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

The review of the open walls (`docs/reports/review-2410/hard-obstacles-summary.md`, §2.3) found six
facts that constrain any proof:

1. **Reformulation is exhausted.** All receivers that read the zero width are isomorphic; changing
   language changes no producer.
2. **Present inputs stop at rate `1/2`.** At lag `t` the prime and polar measures both have density
   of order `e^{t/2}`; restricted positivity is paid by archimedean gains absent on the RH-complete
   cone.
3. **Soft structure is shared by impure models.** Functional equation, Euler product, Witt
   integrality, positive prime counts, local zero counts and many sign patterns are realized by
   models that violate RH.
4. **Sub-Nyquist sign information is blind.**
5. **Every route stops at the square-root threshold** `½ log T`.
6. **The obstruction is localized but not small**: a finite low-frequency sector of doubly
   exponential dimension at each aperture, a Bohr-polydisk hull, frustration on prime-sum edges,
   collapsed clusters at doubly exponential height.

From these the review proposed that the missing input is an **orientation principle**: a mechanism
producing the sign of the prime–pole interaction at the critical scale from arithmetic alone, as
Castelnuovo–Severi positivity on `C × C` produces the Hasse–Weil bound. AOG is the programme that
makes this proposal precise. It does not assume that such a principle exists. It states what one
would have to prove, proves everything that can be proved about it unconditionally, and records
the models that defeat each candidate.

| Programme | Interface |
|---|---|
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Supplies the polar surface, the scaling surface of `ℤ`, the λ-ring, Hecke cycles, the arithmetic Lefschetz number and the Lefschetz–adjunction identity. AOG abstracts them to every scaling datum and studies orbits instead of single cycles. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Supplies sign- and integer-valued invariants of sources: frustration indices, readings and their trichotomy, the critical Wiener algebra and its hulls, the width functor. AOT orients **sources**; AOG orients **correspondences**. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Its two-bump tests are the Weil planes of AOG. A bounded orbit correlation has no top pole (`eq_zero_of_norm_tsum_exp_le`), every two-point minor holding forces the critical line (`exists_minor_fails_of_top`), and the negativity rate of the minors is the maximal depth (`NegativityRateEqualsMaximalDepth`). |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Its envelope law for translated pairings (`translated_pairing_envelope_law`) is the prime-side form of the self-upgrade of orientation. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Its three selectivity classes of conservation laws place the Bézout-selective laws, the only class that uses the successor structure of `ℤ`. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md), [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md), [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Supply supersolutions, shared allocation and frustration: the second mechanism class of §4. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md), [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Supply signed-flux identities in damping and aperture and the doubly exponential ceiling: the third mechanism class. |
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
  not. Only laws that use this can separate `ζ` from the golden Beurling datum.

### 1.3 What an orientation principle is

An **orientation principle** is a theorem that proves the orbit Hodge index of a class of cycles
from arithmetic input that is stated independently of the sign of the form. The programme's
criteria for such a principle are those of the review:

* *selectivity* — it fails, for a stated reason, on the golden datum, the shifted pair
  `ζ(s − a)ζ(s + a)`, parity twins, cluster configurations and planted Euler factors, and reduces
  to Weil's argument over `𝔽_q`;
* *orientation* — it uses reflection-odd data; magnitude-only data cannot decide;
* *cofinality* — it holds uniformly in scale, aperture, height and rank;
* *supra-Nyquist* — it reads information beyond the square-root threshold;
* *rate* — its first output beyond present technology is at least a fixed zero-free strip;
* *pre-divisor* — it uses no zero-indexed object;
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
  battery (§8).
* **Soft structure.** Identities that hold on every scaling datum, or on every model of the battery:
  Lefschetz, adjunction, pullback, λ-ring, functional equation, Euler product, integrality.

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
    real test satisfies `|W(f, f(· − t))| ≤ W(f, f)` for every `t`.

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

### 3.7 Inherited pillars

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

---

## 6. Questions the programme aims to answer

1. **Arithmetic sections.** What is an arithmetic section of a cycle on the scaling surface, and
   why would it satisfy Riemann–Roch without reference to the Weil sign? Known: for every ample
   Hecke-stable cone Riemann–Roch is equivalent to the defect floor (Arithmetic Castelnuovo–Severi,
   universal floor law); a section theory must therefore carry its sign from an independent input.
2. **Frustration against subsidy.** Why would prime-sum frustrations cost less than the archimedean
   subsidy uniformly in aperture?
3. **Anti-collapse.** Which arithmetic invariant prevents `log γ` off-line multiplicity from
   collapsing into a unit window at doubly exponential height?
4. **Relative to absolute.** What conserved quantity converts relative compensation into absolute
   energy at every fixed small damping?
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
   `D_{a + T/2}`, at a doubly exponential number of linear conditions, and on no infinite one.

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

To be built:

- orientation index and rate of a cycle, and the orientation of the battery models;
- the selectivity battery for orientation mechanisms;
- an Arakelov-type intersection theory with arithmetic `h⁰`; signed spectral graph theory in the
  continuum; corrector theory across scales; arithmetic anti-concentration; quantitative
  supra-Nyquist readings.

## 8. Open research topics

1. **The orientation of the battery.** Compute the orbit correlation, orientation index and rate of
   the diagonal for unitary curves, the golden datum, shifted pairs and cluster configurations.
2. **Orbit Pontryagin law for arbitrary cycles.** The orientation index of a cycle should be the
   number of right zeros it sees; Arithmetic Castelnuovo–Severi proves this for spectrally generic
   cycles.
3. **Infinite Euler data.** Which properties of the infinitely many local factors of `μ_ε`
   (equidistribution of `p^{it}`, sign patterns, densities) can repair it below half damping, now that
   every finite set of factors is invisible?
4. **Cheaper archimedean orientation.** Lower the doubly exponential cost of orienting an orbit
   segment of length `T`, or prove it necessary.
5. **Bézout-selective orientation.** Which laws driven by `gcd(n, n + 1) = 1` and `pa − qb = 1`
   carry a signed estimate on orbits, and which of them fail on Beurling systems?
6. **Mechanism equivalence.** Are the three mechanism classes of §4 equivalent on scaling data, and
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
