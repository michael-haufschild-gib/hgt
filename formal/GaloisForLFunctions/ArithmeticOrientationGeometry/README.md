# Arithmetic Orientation Geometry (AOG)

Namespace `GaloisForLFunctions.ArithmeticOrientationGeometry`; umbrella `ArithmeticOrientationGeometry.lean`.

**Question.** Weil got the sign of the explicit formula for a curve from the geometry of the
Frobenius graph: Castelnuovo–Severi on the plane of graph and diagonal is the Hasse–Weil bound. The
scaling flow of `ℤ` has graphs, Lefschetz numbers and adjunction of the same shape, but no proof that
its graphs satisfy that inequality. What geometry could supply it, which arithmetic structures can
orient the scaling correspondence, and which provably cannot?

AOG is the geometry of the **scaling correspondence**. Basic object: a cycle with its orbit under the
scales. Basic invariant: the **orbit correlation** `c_x(g) = δ(ψ_g x, x)`, the primitive part of the
Lefschetz number. A cycle is **oriented** when `|c_x(g)| ≤ c_x(0)` at every scale. Everything is
unconditional; RH appears only inside equivalences.

---

## 1. Place in the research

AOG separates geometric identities (Lefschetz, adjunction, Rosati — true on impure models) from the
arithmetic estimate that would orient a correspondence. Positive foundations: orientation of a cycle
is classified by the zeros its orbit sees; its index counts the adverse zeros it sees; its growth
rate reads their maximal depth; the archimedean place orients finite orbit segments; heat collisions
give a second index formula; one explicit orbit (the cubic spline) decides RH. AOT orients
**sources**; AOG orients **correspondences**.

| Programme | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | Polar/scaling surface, λ-ring, Hecke cycles, Lefschetz–adjunction; AOG abstracts to every scaling datum and works per orbit |
| ArithmeticOrientationTheory | Frustration, readings, Wiener algebra, width functor |
| SquareRootThreshold | Two-bump tests = Weil planes; bounded orbit correlation has no top pole (`eq_zero_of_norm_tsum_exp_le`); negativity rate = maximal depth |
| BiScaleUncertainty | Translated-pairing envelope law (`translated_pairing_envelope_law`) = prime-side self-upgrade |
| TransHorizonIncidenceMechanics | Bézout-selective conservation laws |
| ACT, AIP, SAEI | Supersolutions, shared allocation, frustration (mechanism class 2) |
| ACCE, ACompT | Signed-flux identities, ceiling (mechanism class 3) |
| ArithmeticLocalDivisorGeometry | Local multiplicities, heat normalization; collision budgets ↔ second index formula |
| SignedSuccessorArithmetic, ArithmeticDefectRigidity | Additive and cofactor compatibility of the actual Möbius source |
| DilutionCrystallizationPincer | Rate excess localized to collapsed clusters at doubly exponential height |

---

## 2. Why

**Weil on orbits.** Over `𝔽_q`: Lefschetz `Γ_m·Δ = N_m`; adjunction `Γ_m² = q^mΔ²`; pullback
`Γ_k·Γ_l = q^l N_{k−l}`; Hodge index on `⟨H, V, Γ_m, Δ⟩` = Hasse–Weil. Three identities, one sign. On an
arbitrary **scaling datum** (scale group acting isometrically on a polar surface, weighting fibres by
`e^{±s/2}`) all three identities hold, so they cannot produce the sign; the sign becomes positive
definiteness of one function on the scale group, the orbit correlation.

**Over `ℤ`.** Scale group `ℝ`, action = log translation, Lefschetz number = prime comb, orbit
correlation = Weil pairing of `f` with its translates. RH ⇔ every cycle oriented. Differences from
curves: infinite genus (no finite window decides); an archimedean place (positive collar paying above
a frequency horizon; finite defect at every degree); additive structure (consecutive integers, Bézout
relations — absent in Beurling systems).

**Orientation principle** = proof of the orbit Hodge index for a class of cycles from arithmetic input
stated without the sign. Requirements: selectivity (fails on the battery for a stated reason, reduces
to Weil over `𝔽_q`), orientation (reads impure data), cofinality, supra-Nyquist information, a
quantitative rate (first target: a fixed zero-free strip), source input proved from the source,
exactness (Gamma factor, both poles, every prime power).

---

## 3. Objects and language

| Weil over `𝔽_q` | Scaling datum | Over `ℤ` | Lean |
|---|---|---|---|
| Frobenius `F^m` | scale `g`, isometry `ψ_g` | translation by `log a` | `ScalingDatum`, `zetaScalingDatum` |
| graph `Γ_m` | Hecke graph `T_g x = e^{s/2}ψ_g x` | Hecke cycle | `heckeGraph` |
| `N_m` | Lefschetz number | prime comb | `lefschetz`, `lefschetz_eq` |
| `tr(F^m|H¹)` | orbit correlation `c_x(g)` | `Re W(f(·−t), f)` | `orbitCorr` |
| Hodge index on Weil plane | Hasse–Weil at `(x,g)` | two-bump minor | `HasseWeilAt`, `hasseWeilAt_iff_castelnuovoSeveri_weilPlane` |
| correspondences | finitely supported measures on `G` | Hecke algebra of `ℝ_{>0}` | `Correspondence`, `conv`, `corr_conv` |
| Rosati | `ξ'(g) = ξ(−g)` | `k ↦ k̃` | `rosati`, `RosatiPositive`, `traceAt` |

Further: orbit combination `orbitComb`, `OrbitHodgeIndex`; configuration surfaces `configSurface`,
`configScalingDatum` (every tempered zero configuration is a scaling datum); blindness `BlindOffLine`,
`BlindAbove`, `OffLineGeneric`; seen configuration `seenConfig`; orbit/family surfaces `orbitSurface`,
`FibreCompatible`; families `orientedSubspace`; damping `ScalingDatum.damp`, `dampedEnergy`; theta `arithH0`;
spline cycle `splineCycle`.

**Words.** *Oriented*: orbit has the Hodge index (on configurations: bounded orbit correlation).
*Orientation index*: negative squares on the orbit span. *Orientation rate*: growth exponent of `c_x`.
*Sees ρ*: transform nonzero at both points of the reflection pair. *Scale-stable family*: closed under
translates; *jointly sees*: some member nonzero at `γ_ρ` and some at `γ̄_ρ`. *Soft structure*: identities
true on every battery model. *Damped energy* `E_x(ε) = sup_t e^{−εt}|c_x(t)|`.

---

## 4. Mechanisms

1. **Scaling-datum identities.** Lefschetz `L(x,g) = (e^s+1)(x·H)(x·V) − e^{s/2}c_x(g)`; Lefschetz–adjunction
   identity (`lefschetz_sub_half_selfPair_eq`); Weil-plane defect `(r²+t²)δ(x,x) + 2rt c_x(g)`; three forms of
   Hasse–Weil coincide (`hasseWeilAt_iff_lefschetz_bound`); orbit Toeplitz law (`defect_orbitComb_self`);
   globally all-scales = scale 0 (`hodgeIndex_tfae`); for `ℤ`: `riemannHypothesis_iff_forall_hasseWeilAt`.
2. **Correspondence algebra.** `δ(ξx, ηx) = τ_x(ξ⋆η')` (`defect_corr_corr`); Rosati positivity at `x` = orbit
   Hodge index (`rosatiPositive_iff_orbitHodgeIndex`) — Weil's two proofs coincide per cycle; Hecke graphs
   satisfy pullback, adjunction, `TT' = e^s` (`heckeGraph_rosati`).
3. **Configurations.** Translation multiplies the summand at ρ by `e^{(s−t)(ρ−½)}` (`Wsummand_scaleShift`);
   orbit correlation is an exponential sum over zeros (`configScalingDatum_orbitCorr_eq`); for ζ the explicit
   formula identifies it with the scaling datum of `ℤ` (`configSurface_zeta_eq`).
4. **Orientation theorem** (`orientation_tfae`): Hasse–Weil at every scale ⇔ orbit Hodge index ⇔ blind to one
   point of every off-line pair. Blindness orients (`orbitHodgeIndex_of_blindOffLine`); self-upgrade
   (`blindOffLine_of_hasseWeil`) via no top pole. Oriented locus = union of correspondence-stable subspaces.
   One generic orbit decides RH (`riemannHypothesis_iff_hasseWeil_of_generic`).
5. **Rates.** `|c_f(t)| ≤ Ke^{σt}` ⇔ blind above depth σ (`orbitCorr_rate_iff_blindAbove`); for ζ a generic orbit
   reads the zero width (`zeta_orbitCorr_rate_iff_zetaZeroWidth_le`). Eventual bounds with any constant upgrade
   to the sharp bound (tensor-power trick; `hasseWeilAt_of_eventually_bounded`,
   `riemannHypothesis_iff_eventually_bounded_of_generic`).
6. **The spline orbit decides.** The laws need genericity only at off-line zeros (`OffLineGeneric`); the cubic
   spline has transform `(sin z/z)⁴`, zero only on the real axis (`offLineGeneric_cubicSpline`). So one explicit
   orbit decides RH (`riemannHypothesis_iff_splineOrbit_hasseWeil`), reads the width
   (`zeta_splineOrbit_rate_iff_zetaZeroWidth_le`), and its prime-side Weil Gram negative index counts distinct
   right zeros (`zeta_splineOrbit_negIndex_law`); RH ⇔ all those Grams PSD, already on the two-prime Hecke orbit
   `k log p + l log q` (`riemannHypothesis_iff_splineTwoPrime_negIndex_eq_zero`) and the rational Hecke orbit
   (`riemannHypothesis_iff_splineRatHecke_negIndex_eq_zero`); RH ⇔ index ≤ 1 (`riemannHypothesis_iff_splineOrbit_negIndex_le_one`).
7. **Index laws.** Seen configuration (`W_translate_seenConfig`); orientation index = right zeros seen
   (`orientationIndex_law`, `zeta_orientationIndex_law`); orbit surface signature = 1 + right zeros seen
   (`zeta_orbit_signature_law`) — the continuum frustration count of an orbit. Families: joint seeing is
   seeing (`jointlySees_iff`); Weil form ≥ 0 on a scale-stable family ⇔ jointly blind
   (`zeta_scaleStable_nonneg_iff_jointlyBlind`); index = right zeros jointly seen (`scaleStable_index_law`);
   orientation is not additive (`jointlySees_orbitFamily_iff`).
8. **Sections.** Orbit surface classes = pole-plane + correspondence image (`exists_eq_corr_of_mem_orbitSpan`);
   RR on an orbit surface ⇔ open positive cone ⊆ cone ∧ cycle oriented (`orbitSurface_riemannRoch_iff`,
   `configOrbitSurface_riemannRoch_iff_blind`); same for families (`familySurface_riemannRoch_iff`).
9. **Theta `h⁰` of `Spec ℤ`.** `h⁰(d) = log Σ e^{−πn²e^{−2d}}`, `h⁰(d) − h⁰(−d) = d` by Poisson
   (`arithH0_riemannRoch`); `Λ(s)` is its Mellin generating function (`completedRiemannZeta_eq_mellin_arithH0`);
   pole-plane RR (`poleH0_riemannRoch`). This RR is the base's: it gives the functional equation, not the
   Hodge index.
10. **Euler factors and payment.** Deleting finitely many Euler factors from `μ_ε` changes neither payment,
    ideal nor hull (`receiverBounded_roughMoebius_iff`); `μ_ε` is a unit iff `ε > ½`, not in the algebra for
    `ε ≤ ½` (`isWienerUnit_moebius_of_half_lt`, `not_criticalWiener_moebius`).
11. **Archimedean orientation of segments.** Low-blind `f` (transform vanishing at the pole and on the
    low-frequency grid of aperture `a + T/2`) is Hasse–Weil for `|t| ≤ T` (`hasseWeilAt_of_lowBlind`); the
    number of conditions grows doubly exponentially in `T`.
12. **Correctors.** Lefschetz trace of a correspondence (`lefschetzTrace_eq`); correctors (zero pole trace)
    have Lefschetz trace = −primitive trace (`lefschetzTrace_of_corrector`). Damping `e^{−εs}` acts by
    automorphisms, conjugating Rosati to the opposite damping (`rosati_damp`); damped correctors exist on
    every pair of scales (`isCorrector_damp_twoPoint`); `E_x(ε) < ∞` ⇔ blind above ε; finiteness at every
    `ε > 0` with arbitrary constants gives `E_x(ε) = c_x(0)` (`dampedEnergy_tfae`,
    `riemannHypothesis_iff_forall_damped_bounded`).
13. **Heat-collision index** (`TheIndexExit`): for small de Bruijn–Newman times collision mass = `2(D + E)`
    (`D` distinct right zeros, `E` multiplicity excess); diverges if infinite. Uniform bounds ⇔ finitely many
    off-line zeros (⇒ strip `Θ < 1`); `D` even, so `D < 2` is RH.
14. **Battery.** Curves (`unitaryCurve_orbitHodgeIndex`); golden datum has all soft structure, rate exactly
    `log φ/log 5` (`golden_soft_structure_and_disorientation`, `golden_orbitCorr_rate_iff`); orientation blind
    to multiplicity (`orientation_congr_carrier`); curve shifted pair has rate `a` (`shiftedPair_orbitCorr_rate_iff`);
    symmetric clusters fool every windowed form but not a generic orbit (`cluster_heightAverages_blind_orbit_not`).
15. **Quantitative curve readings.** Tower identity `c_f(ν log q) = log q‖f‖² Re Σβ_i^ν` (`curve_orbitCorr_tower`);
    Turán: violations detected in every window of `2g` scales with explicit precision
    (`exists_not_hasseWeilAt_window`, `golden_eventually_exists_not_hasseWeilAt`).

Mechanism classes for orienting: (1) positivity of correspondences from graph geometry; (2) contraction
with a supersolution (collar + signed prime atoms); (3) signed-flux conservation; plus self-upgrade
(positivity from a rate) and compute-then-bound.

---

## 5. Pillar theorems

1. Weil planes and global equivalences (`hasseWeilAt_iff_castelnuovoSeveri_weilPlane`, `hodgeIndex_tfae`, `rosatiPositive_iff_orbitHodgeIndex`).
2. Orientation theorem (`orientation_tfae`, `riemannHypothesis_iff_hasseWeil_of_generic`).
3. Rate = depth of deepest seen zero (`orbitCorr_rate_iff_blindAbove`, `zeta_orbitCorr_rate_iff_zetaZeroWidth_le`).
4. Explicit deciding orbit (`riemannHypothesis_iff_splineOrbit_hasseWeil`, `riemannHypothesis_iff_splineTwoPrime_negIndex_eq_zero`).
5. Index laws (`orientationIndex_law`, `zeta_orbit_signature_law`, `scaleStable_index_law`).
6. RR on orbits ⇔ orientation (`orbitSurface_riemannRoch_iff`).
7. Lossless damping (`dampedEnergy_tfae`); eventual = sharp (`hasseWeilAt_of_eventually_bounded`).
8. Soft structure does not orient (`golden_soft_structure_and_disorientation`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Lefschetz/adjunction/pullback orient | Hold on every scaling datum incl. golden |
| All scales stronger than scale 0 | Globally equivalent; the distinction is per cycle |
| Weil's second proof avoids Hodge index | Rosati positivity at `x` = orbit Hodge index |
| Finite scale window orients | Finite windows admit off-line mimics |
| Orientation is a sign condition | On configurations it is a growth condition |
| Positive prime counts orient | True on golden datum |
| Sieve upper bound is half an orientation | Bounds counts by a constant multiple, never square-root deviations |
| One generic cycle (now: the spline) makes it easy | Proving its orientation is RH |
| Euler products decide repair | Only for `ε > ½`; finitely many factors invisible below |
| Archimedean place orients a cycle | Only finite segments, doubly exponential cost |
| Orientation is additive | Opposite blindness spans a seeing family |
| Theta `h⁰` RR orients | It gives the functional equation; surface RR is needed |
| Damped bounds lose energy as `ε ↓ 0` | Lossless on orbits; finiteness is the content |
| Height averages read clusters | Windowed forms are blind; a generic orbit reads depth |
| Collision-mass bound = RH | Equivalent to finitely many off-line zeros |

---

## 7. Open problems

1. **Arithmetic sections on the surface**: an `h⁰` for classes with a test component, RR proved without the
   sign (RR on an orbit ⇔ orientation is established; an independent proof is open).
2. **Shifted pair over `ℤ` and parity twins** in the zero-side datum (zeros `ρ ± a` leave the strip).
3. **Single-tower orientation index** for arbitrary cycles: exclude Wolff-type accumulation for the actual
   divisor (ACS has two-prime completeness; the spline already decides on two-prime orbits).
4. **Infinite Euler data**: which properties of infinitely many local factors (equidistribution of `p^{it}`,
   sign patterns) repair `μ_ε` below ½.
5. **Cheaper archimedean orientation** of length-`T` segments, or proof that doubly exponential cost is necessary.
6. **Bézout-selective orientation**: laws from `gcd(n,n+1) = 1`, `pa − qb = 1` with signed estimates on
   orbits that fail on Beurling systems.
7. **Source bound on the collision index**, uniform as heat time → 0, first finiteness, then below the first quantum.
8. **Mechanism equivalence** of the three classes on scaling data; which fails first on each battery model.
9. **Quantitative readings over `ℤ`** (infinitely many terms) analogous to Turán on curves; index laws for
   non-scale-stable families.

---

## 8. Tools to build

Surface $h^0$ with an RR proof independent of the sign; quantitative readings over `ℤ` analogous to Turán;
a source bound on the heat-collision index; Bézout-selective orbit laws.

---

## 9. Success criteria and principles

Success: the orbit Hodge index of a cofinal class of cycles from an input that passes the battery, or a
proof that no input of a stated class can — reducing over `𝔽_q` to Weil. A contribution is unconditional,
stated in scaling data/orbits/Weil planes/correspondences, says what it gives on the golden datum, the
shifted pair and over `𝔽_q`, gives identities where Weil's step is an identity, names its mechanism class,
and records the positive survivor of every no-go.

Battery: golden datum `1 − 5X + 5X²`; shifted pair; parity twins; cluster configurations with ζ-type
local counts; planted Euler factors; finite-window mimics.

Principles: identities first, sign last; work per orbit; calibrate over `𝔽_q`; selectivity is a theorem;
a reformulation is not a reduction.
