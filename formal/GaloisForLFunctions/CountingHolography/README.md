# Counting Holography (CTH)

Namespace `GaloisForLFunctions.CountingHolography`; umbrella `CountingHolography.lean`.

## 1. Motivation

On the massless topological AdS₄ black hole with horizon `PSL₂(ℤ)\ℍ` every zero of `ζ` is a damped mode
of the wave equation, and RH is one universal relaxation rate (`BlackHoleRingdown`). Arithmetic scattering
holography (`ArithmeticScatteringHolography`, ASH) asked whether a law of wave dynamics forces that rate,
on the exact function-field model where the horizon is a graph. None does. Flux, unitarity, causality,
positive commuting Hecke operators at every degree, KMS positivity and the functional equation at genus
two all hold on fake black holes with a slow resonance. What separates a true curve from a fake is a
**count law**: the number of open channels `K` of a probe obeys the parallelogram law

  `K(φ + ψ) + K(φ − ψ) = 2K(φ) + 2K(ψ)`,

the Born rule for counts. On a true elliptic curve `K` is the degree of `y − xF`; it is a count because it
is the number of points of a group, and it is quadratic because of the addition law. Hasse's theorem
follows (`ASH.hasse_of_countLaw`). A fake has honest counts, `|𝒬|`, which are not quadratic. Over `ℤ` the
Weil form of the integer probes is quadratic and is not known to be a count.

Counting holography takes the count, not the wave, as the physical object: the quantum numbers of
boundary sources on arithmetic quotients of AdS. A probe is a source. Its count is a boundary degeneracy:
an integer on the graph, a point count over a function field, a number of cusp images met by the source on
the horizon. The programme separates the two properties of a count law, finds which structure supplies
each, decides the first rung at genus two, proves the count law on true curves of every genus and produces
it from heights of the Jacobian at genus two, shows that a non-arithmetic Hecke group fails through the
count, reads the horizon's own counts (Farey points) and their rates for smooth and sharp sources, decides
the natural candidates for a count over `ℤ`, and states exactly what such a count must be.

**The answer in one line.** A count law is a **Born rule** (a quadratic form covariant under the delay)
plus a **count** (nonnegativity). The Born rule is the functional equation; the count is universal
damping. Every structure tested supplies the first half or a linear shadow of the second; over `ℤ` the
first half holds unconditionally, the natural counts of the horizon are linear and cannot be the law,
and the second half is RH.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Count law | `ASH.CountLaw` | the parallelogram law for `K : ℤ² → ℕ` on the probes `y − xπ` |
| Genus form | `genusForm` | `g y² − a x y + g Q x²`, the count law forced by the channel numbers `g`, `gQ`, `N + (g−1)(Q+1)` |
| Level `n` | `exists_levelCountLaw_iff` | the probes `y − xπⁿ` over `𝔽_{qⁿ}`, channel numbers `g`, `g qⁿ`, `N_n + (g − 1)(qⁿ + 1)` |
| Delay | `IsMode`, `cplx` | one double tick of the ringdown acting on a state space; its modes are the eigenvalues of the complexification |
| Born rule | `IsBornRule` | a quadratic form `S` with `Mᵀ S M = q S`: one tick multiplies every count by `q` |
| Covariant count | `IsCovariant` | `K(t x − y, q x) = q K(x, y)`: the delay `π(y − xπ) = qx − (tx − y)π` on probes |
| Rosati form | `ACP.rosatiDeg`, `AET.intRosatiDeg` | `Tr(P(F) P(F)′) = Σ P(α_i) P(q/α_i)` on the probe ring `ℤ[F]`: the height of a Jacobian |
| True hyperelliptic curve | `AET.hyperellipticDatum` | the curve datum of `y² = f(x)`, `f` squarefree of odd degree, with its actual point counts |
| Every hyperelliptic curve | `pointsAtInfinity`, `lRoots`, `rootProd` | `y² = f(x)`, `f` squarefree of any degree; one point at infinity in odd degree, `1 + χ(lc f)` in even degree; the reciprocal roots of `χ(Res(·, f))` |
| Bielliptic genus-two curve | `bielliptic_countLaw`, `mirror_coprime` | `y² = h(x²)`, `h = X³ + aX² + bX + c` separable, `c ≠ 0`; its quotients `y² = h(u)` and `y² = m(v)`, `m = X³ + bX² + acX + c²` |
| Echo state of a throat | `throatEcho` | the companion of `throatPoly`, modes multiplying to `(b − 1) q` |
| Oscillator bank | `bankDelay`, `bankKrein`, `kreinMatrix`, `wronskianMatrix` | `g` oscillators `z² − t_k z + q` on pairs of echoes; Krein squares and the Wronskian |
| Hermitian form of a repeated oscillator | `echoCoord`, `bornHermitian` | complex coordinates `(u₁ − t u₀/2) + i s u₀` of the echo states and the form `H` of a Born rule |
| Off-circle quadruple | `quadrupleDelay`, `hyperbolicForm` | the delay of `α, ᾱ, q/α, q/ᾱ` and its split Born rule |
| Genus-two delay, genus-two Born rules | `genusTwoDelay`, `genusTwoKrein`, `genusTwoKreinPair` | the two oscillators of `L_q`; `c₁ 𝒬_{t₁} ⊕ c₂ 𝒬_{t₂}` |
| Traces of genus two | `genusTwoTrace`, `traceOne`, `traceTwo` | `a_n = V_n(t₁) + V_n(t₂)`, `t₁ + t₂ = q − 2`, `t₁ t₂ = 1 − 3q` |
| Boundary algebra | `QuadraticAlgebra R (−q) t`, `probe`, `reState` | `R[π]/(π² − tπ + q)` with the partner involution `π* = t − π = q/π`; the probe `y − xπ`; the state `Re` |
| Oscillating mode | `oscillatingMode` | `t/2 + i √(q − t²/4)`, the embedding of the probe ring in `ℂ` |
| Integer probes over `ℤ` | `ASH.integerProbe`, `dilate` | `Q(a) = W(f_a, f_a)`, `f_a = Σ aₙ B(· − log n)`; Hecke at `p` moves `log n` to `log p n` |
| Tate limit of a count | `riemannHypothesis_iff_tateLimit_of_count` | `lim K(m a)/m²` along integer rays |
| Horocycle point, row depth | `horoPoint`, `rowDepth` | `x + iy` and `Im M_{c,d}(x + iy) = y / ((cx + d)² + c²y²)` |
| Shell count | `shellCount` | the number of cusp images of `SL₂(ℤ)` whose horoball shell `a ≤ Im < b` contains a point |
| Quarter disc, horoball profile | `quarterDisc`, `horoballSum`, `circleRemainder` | `Σ_{m ≥ 1} √(Y² − m²)`; `Σ_c φ(c) √((X/c)² − 1)`; the remainder `Σ √(Y² − m²) − πY²/4 + Y/2` |
| Hecke words and places | `heckeT`, `heckeS`, `place` | `γₙ = TⁿS` in `G₅ = ⟨S, T_φ⟩`; the real places `X ↦ φ`, `X ↦ ψ` of `ℤ[X]/(X² − X − 1)` |
| Hecke group `G_q` | `heckeLength`, `heckeInvariant`, `heckePoly` | `λ_q = 2cos(π/q)`; `λ_q² = 2 + 2cos(2π/q)`, the generator of the invariant traces; `P_q = D_q(X − 2) − 2` with the Dickson polynomial `D_q` |
| Farey kernel, weight, count | `fareyKernel`, `fareyWeight`, `fareyCount` | the profile over the horoball of one cusp image; its dependence on `c/C`; the totient-weighted sum |
| Calibration models | `goldenDatum`, ASH fakes, throats, `genusTwoL`, true hyperelliptic and bielliptic curves, the modular horizon, the Hecke groups `G_q` | |

## 3. Language

- **Open channel**: a cusp of a graph black hole, a point of a curve, a cusp image met by a source.
- **Count of a probe**: the number of points of `ℤ[π]/(φ)`, or the value of a count law at `φ`.
- **Born rule**: a quadratic count covariant under the delay. **Quadratic half** and **count half**: the
  two properties of a count law.
- **Partner law**: the modes come in pairs `α`, `q/α`; the functional equation of the mode polynomial.
- **Oscillating**: `t² < 4q`; **critical**: `t² = 4q`; **overdamped**: `t² > 4q`.
- **Orientation of a probe**: the sign of its Krein square; a fake has probes of both orientations.
- **Level**, **tower count law**: the count law over `𝔽_{qⁿ}`, at one level or all.
- **Crude count**: a bound `|N_n − qⁿ − 1| ≤ C qⁿᐟ²` at every level, with any constant.
- **Linear count**: a count additive in the source, like the cusp images met by a shell.
- **Shell**, **depth**: horoball regions between heights `a` and `b`.
- **Farey order** `C = y^{−1/2}`: the largest denominator of a cusp image a horocycle of height `y` meets.
- **Thermalization rate**: the rate at which a horocycle mean reaches its limit.
- **Sharp shell**: the indicator of a shell, a source with a jump, outside the smooth class.
- **Place**: a real embedding of the trace field of a group; the **count at a place** is the Krein square
  `y² − σ(tr γ) xy + x²` of the conjugate element.
- **Partner involution**: `π* = q/π`, the involution of the boundary algebra exchanging a mode with its
  functional-equation partner; a **state** is a normalized functional, positive if `ω(a* a) ≥ 0`.
- **Elliptic state map**: the one-tick map `(u₀, u₁) ↦ (u₁, t u₁ − q u₀)` of a black hole in its oscillating
  regime; its Wronskian is multiplied by `q` per tick (ASH `wronskian_step`).
- **Flux**: `𝓕 = (1 − 1/q) 𝒬`, the energy balance of the boundary data (ASH `kreinSquare_nonneg_iff`, `kreinFlux`).
- **Damping deficit**: `¼ − (1 − Re ρ)/2`, the shortfall of a zero below the universal rate (ASH `rateDeficit`).
- **Trivial mode**: a factor `x²` of the mode polynomial of a graph; integrality bounds the genus by the
  number of trivial modes (ASH `genus_le_trivial_zeros`).
- **Silent branch**: the incoming (plus) branch of a mode, absorbed by the core and absent from the
  reflected signal (ASH `plusBranch_isIncoming`).
- **Modular clock**: the common time of the Hecke trees, with tick `log p` at the prime `p` (ASH
  `TheOneClockOfTheModularHorizon`).
- **KMS midpoint**: the critical line as the fixed height of the KMS reflection; `¼` is the rate of the
  midpoint (ASH `kms_midpoint`, `quarter_iff_midpoint`).

## 4. Mechanisms

**Count laws.**
1. **Three numbers.** The parallelogram law on `ℤ²` determines `K` from `K(0,1)`, `K(1,0)`, `K(1,1)`
   (`countLaw_eq_form`). The channel numbers of a curve force the genus form (`countLaw_eq_genusForm`),
   half the Castelnuovo–Severi defect of `yΔ − xΓ_{Fⁿ}` (`toeplitz_twoTerm`). A count law exists iff
   `a² ≤ 4g²Q` (`exists_genusCountLaw_iff`).
2. **Tensor power.** A count law at every level, or a crude count with any constant, bounds every power
   sum, power-sum elimination puts every mode in the disc, the functional equation on the circle
   (`unitary_of_crude_trace_bound`, `towerCountLaw_iff_crude_bound`).
3. **Jacobian sum.** A sum of count laws is a count law and the channel numbers add. On `y² = h(x²)` the
   squares cover `u` exactly `1 + χ(u)` times (`sum_sq_eq`) and `u ↦ c/u` carries `χ(u h(u))` to `χ(m(v))`
   (`charSum_mirror`), so the points of the curve are the points of its two quotients
   (`card_points_bielliptic`); a common root `v` of `m`, `m′` would give the common root `c/v` of `h`, `h′`
   (`mirror_coprime`). The sum of Manin's two height counts is the genus-two count law
   (`bielliptic_countLaw`).

**Born rules.**

4. **Determinant.** A nondegenerate Born rule forces `(det M)² = q^d` (`det_sq_of_bornRule`).
5. **The quadratic half is the partner law.** If `Mv = αv`, then `Mᵀ(Sv) = (q/α)(Sv)`, and `Sv ≠ 0` for a
   nondegenerate `S` (`partner_of_bornRule`).
6. **The count half is universal damping.** For a positive `S` the real and imaginary parts of a mode
   vector rotate under `M` (`mulVec_re_im`) and the count of both is multiplied by `|α|²` and by `q`
   (`normSq_eq_of_bornRule`).
7. **Uniqueness at genus one.** Covariance at `1`, `π`, `1 − π` fixes a count law up to `K(1)`
   (`countLaw_covariant_eq`).
8. **Blocks.** Covariance forbids a Born rule to pair oscillators with different traces, and pairs two
   copies of one oscillator by `c 𝒬 + d J` (`block_eq_zero_of_ne`, `block_eq_of_eq_trace`).
9. **Complex coordinates.** On a damped oscillator `𝒬(u, v) = Re(φ(u) φ(v)̄)` and `J(u, v) = Im(φ(u) φ(v)̄)/s`,
   so the Born rules of `m` copies are Hermitian forms (`quad_eq_bornHermitian`), and a Born rule of any
   bank splits over its trace classes (`quad_eq_sum_classes`, `quad_class_eq_bornHermitian`).
10. **Conservation and levels.** A Born rule is multiplied by `qⁿ` after `n` ticks (`bornRule_pow`) and is a
   Born rule of every level (`bornRule_pow_delay`): the normalized count is a conserved Lyapunov functional.
11. **The Rosati form is the trace-form Born rule.** A mode and its partner multiply to `q`, so
    `Tr(F P (F P)′) = q Tr(P P′)` (`rosatiDeg_delay`); on `y − xFⁿ` it is twice the genus form
    (`rosatiDeg_twoTerm`, `genusForm_eq_kreinSum`).
12. **GNS.** In the boundary algebra `a* a = N(a)` (`star_mul_self_eq`) and `N(y − xπ) = 𝒬(x, y)`
    (`norm_probe`), so every state has the Krein square as its GNS form (`state_star_mul_self`); a
    `*`-representation on `ℂ` gives `N(a) = |ρ a|²` (`exists_starRep_iff`).

**The ring of probes.**

13. **Norm.** The count of `y − xπ` is `|𝒬(x, y)|` (ASH). For an oscillating mode the ring embeds in `ℂ`
    and `𝒬(x, y) = |y − xα|²` (`kreinSquare_eq_normSq`), the factor by which the probe scales areas
    (`det_mulMatrix`). For an overdamped mode `𝒬` factors over `ℝ` and takes both signs
    (`kreinSquare_eq_mul_of_real`, `exists_probe_neg_of_overdamped`).
14. **Places.** A unimodular element counts nonnegatively at a real place iff `σ(tr γ)² ≤ 4`, and the
    probes `1 ∓ π` detect every failure (`placeCount_nonneg_iff`). The words `TⁿS` of a Hecke group are
    universal words over `ℤ[X]` evaluated at the places of the trace field (`heckeWord_map`).
15. **Hecke instances.** `πⁿ = a_n π + b_n`; the counts of `1 ∓ πⁿ` are `qⁿ + 1 ∓ V_n`, and their sum is
    `2(qⁿ + 1)` on every black hole with `|t| ≤ q` (`conservation_at_every_level`).
16. **Linear counts are degenerate.** Additivity gives `K(2φ) = 2K(φ)`, the law `4K(φ)`
    (`eq_zero_of_additive_countLaw`); a count law constant along a line has a radical
    (`countLaw_through_linear_degenerate`).

17. **Units of nonsquare norm.** For monic squarefree `g`, `Res(g, ·)` is the norm of `F[X]/(g)`
    (`algebraMap_resultant`); a unit `1 + (g/P) w` takes a nonsquare value at a root of an irreducible
    factor `P` (`exists_nonsquare_unit`), and twisting by it kills the high degree sums
    (`degSumW_eq_zero_of_squarefree`) and gives the trivial root of even degree
    (`chiC_leadingCoeff_mem_lRoots`).

**Over `ℤ`.**

18. **Tate.** A nonnegative function with quadratic growth `Q` along a ray forces `Q ≥ 0`
    (`nonneg_of_tateLimit`); the floor of a nonnegative form has that growth (`tendsto_floor_div_sq`).
19. **Ratios.** The Gram entry of the atoms `m`, `n` is the spline correlation at `log(m/n)`
    (`atomGram_eq_ratio`), so dilation by `p` preserves the form (`hermQuad_extend`, `integerProbe_dilate`).

**The horizon.**

20. **Coprime windows.** Every window of `c` consecutive integers contains `φ(c)` integers prime to `c`
    (`card_coprime_Ico`); every point of the line lies in exactly `φ(c)` intervals `(d, d + c]` with `d`
    prime to `c` (`sum_indicator_coprime`).
21. **Unfolding.** On the segment `0 ≤ x ≤ 1` of a horocycle the pseudo-Eisenstein series is a finite sum
    over a box of rows (`pseudoEisenstein_horoPoint`); the rows of denominator `c` unfold to `φ(c)/c ∫ g`
    (`integral_sum_coprime`).
22. **Order.** The Farey kernel depends on `c² y` only (`fareyKernel_eq_weight`): the horocycle at height
    `C⁻²` reads the Farey points of order `C` with weight `w(c/C)` (`fareyCount_eq_order`).
23. **Three circles right of a zero-free half-plane.** On discs about `3 + it` that avoid the pole and
    stay right of `σ₀`, `ζ` has a logarithm, and the two-radius bound gives `|ζ| ≥ exp(−B (K log t)^θ)`,
    `θ < 1`; so a zero-free half-plane is a polynomial lower bound (`zeroFree_iff_zeta_lower_bound`).
24. **Möbius and the circle.** `φ = μ * id` turns the horoball profile of a sharp horoball into a Möbius
    sum of quarter-disc column sums (`horoballSum_eq_moebius`); each is within its radius of its area by
    sum–integral comparison for a decreasing profile (`quarterDisc_bounds`), and `Σ μ(d)/d²` is within
    `1/D` of `6/π²` (`RHTower.abs_sum_moebius_div_sq_sub_le`).

## 5. Questions the programme aims to answer, and the answers

**First rung: on the genus-two graph, does a parallelogram channel count exist exactly for `q ≤ 3`?** At
every level of the tower, yes; at one level, no. The count law at the first level exists exactly for
`q ≤ 19`, the genus-two Weil bound `(q − 2)² ≤ 16q` (`genusTwo_firstLevel_iff`); at every level exactly for
`q ≤ 3` (`genusTwo_tower_iff`). The Born rules on the echo states are exactly `c₁ 𝒬_{t₁} ⊕ c₂ 𝒬_{t₂}`
(`bornRule_genusTwo_eq`); a nondegenerate one exists for every `q` (`det_genusTwoKrein_ne_zero`), a
positive one exactly for `q ≤ 3` (`genusTwoKreinPair_positive_iff`, `exists_positive_bornRule_iff`).

**The question of §2.7: is there a bulk-defined count of open channels for integer sources, nonnegative,
integer-valued, with the parallelogram law up to bounded error and at bounded distance from `Q`?** The
question is RH, in both directions, and the three natural candidates are refuted.
- A count at bounded distance from `Q` forces RH, and no law is needed at finite size
  (`riemannHypothesis_of_count_at_bounded_distance`, `riemannHypothesis_iff_tateLimit_of_count`);
  under RH `⌊Q⌋` is at distance `< 1` and obeys the law up to `6` (`exists_near_count_of_riemannHypothesis`).
- The candidates — cusp images in horoball regions cut out by the source, echoes weighted by `φ(c)`,
  degrees of line bundles attached to the source — are linear in the source (`pseudoEisenstein_add`,
  `shellCount_add`). A nonzero linear count never obeys the law (`eq_zero_of_additive_countLaw`), and a
  count read through one linear count is degenerate (`countLaw_through_linear_degenerate`): it is the
  Krein square of a black hole only at the critical edge (`kreinSquare_through_linear_iff`). The
  quadratic invariant of a line bundle, its self-intersection, is the Castelnuovo–Severi defect, which is
  the Born rule again (`toeplitz_twoTerm`, ACS `hodgeIndexOnSpan_iff_unitary`).
- The survivor is exact: a count must be quadratic of full rank, covariant under Hecke
  (`integerProbe_dilate`, `tateLimit_dilate`), with leading term `Σ a_m a_n C(log(m/n))`
  (`atomGram_eq_ratio`), and defined without `Q`. So the physical reading of the sign stops at the
  horizon's natural counts; the horizon remains a language until a quadratic count exists.

**A32: Manin at higher genus through Jacobians; first case genus two.** At every genus the tower count law
is Hasse–Weil (`towerCountLaw_iff_unitary`). It holds on every hyperelliptic curve of every genus, of odd
or even degree, at every level (`hyperelliptic_countLaw_every`): the even-degree Riemann hypothesis is
proved here, by a unit of nonsquare norm, the trivial root at infinity and descent from the splitting field
(`riemannHypothesis_evenHyperelliptic`). So every genus-two curve `y² = f(x)`, `deg f ∈ {5, 6}`, whatever
its Jacobian, has the count law (`genusTwo_countLaw`). At genus two heights produce it alone on
every bielliptic curve `y² = h(x²)`: the Jacobian is isogenous to the product of the quotients
`y² = h(u)` and `y² = m(v)`, the sum of Manin's two height counts obeys the parallelogram law with the
channel numbers `2`, `2q`, `N_C + q + 1` (`bielliptic_countLaw`), and Hasse–Weil `(q + 1 − N_C)² ≤ 16q`
follows over every finite extension (`bielliptic_weil`, `bielliptic_weil_tower`), with no character-sum
bound. The Rosati form is the Born rule of the probe ring at every genus (`rosati_tfae`). On the genus-two
graph the count law exists at every level exactly for `q ≤ 3` (`genusTwo_tower_iff`).

**Q1. What is `K` on an integer source of the modular horizon?** Its leading term is `Q` itself: any count
with Tate limit `Q` gives RH and under RH `⌊Q⌋` is one (`riemannHypothesis_iff_tateLimit_of_count`). It is a
function of the ratios `m/n` (`atomGram_eq_ratio`), asymptotically Hecke invariant (`tateLimit_dilate`), the
restriction to `ℕ` of the GNS form of `r ↦ C(log r)` on `ℚ_{>0}` (APD `dotProduct_weilGram_eq_ratCorr`), and
not a linear count of the horizon.

**Can modular conjugation supply the partner involution?** The boost-commuting wedge reflection is
`-I₂`; the normalized `PSL₂(ℤ)` normalizer has integer entries, and its quotient action preserves
pseudo-Eisenstein series. Integer shifts are not closed under negation. In a standard-form von Neumann
algebra, `Z ∈ M` and `J Z J ∈ M` force `Z ∈ M ∩ M'`, `J Z J = Z*`, and natural-cone pairing
`‖Z Ω‖²` (`StandardForm.tomita_central_eq_star`). Partner representations of rational dilations are
central and unitary. A nontrivial graph realization exists exactly when `t² ≤ 4q`
(`exists_standardForm_partner_rep_iff_damped`); an integer Born-rule realization, exact or in Tate
limit, exists exactly when RH holds (`riemannHypothesis_iff_exists_standardForm_bornRule`,
`riemannHypothesis_iff_exists_standardForm_tateLimit`). See
[ModularConjugationIsNotThePartnerInvolution.lean](ModularConjugationIsNotThePartnerInvolution.lean).

**Q2. What is the physical origin of the parallelogram law on a branched graph?** The delay. A quadratic
count covariant under one tick is a Born rule; a nondegenerate one forces the partner law
(`partner_of_bornRule`), and at genus one it is unique, `K(1)·𝒬` (`countLaw_covariant_eq`), so a covariant
quadratic count of the probes that counts the trivial probe once exists iff the black hole is damped
(`exists_covariantCountLaw_iff`). A throat with `b ≠ 2` has flux and unitarity and no nondegenerate Born rule
(`throat_no_bornRule`); the genus-two graph has one for every `q`. At every genus the Born rules of a bank are
built from Krein squares and Wronskians (`bornRule_bank_blocks`): weighted sums for distinct traces
(`bornRule_bank_eq`), Hermitian forms on repeated oscillators (`bornRule_positive_iff_hermitian`), the direct
sum of the Hermitian forms of the trace classes in general (`bornRule_positive_iff_classes`), and a
hyperbolic form on four modes off the circle (`offCircle_quadruple`). The parallelogram law is the
functional equation read as a count; it is global because it is a statement about the delay on the whole
state space.

**Q3. Does integrality of the mode data force a count when trivial modes are infinite?** No, and not even
with a single trivial zero. For `4 ≤ q ≤ 19` the genus-two graph has integral mode data with the sharp law of
trivial zeros, the functional equation of genus two and the count law at the first level, and a slow
resonance (`firstCountLaw_does_not_force_damping`).

**Q4. Why is the form a boundary square exactly when the modes oscillate?** Because the count of an
oscillating black hole is the norm of a complex number. For `t² ≤ 4q` the probe ring embeds in `ℂ` through
the mode on the circle, and the count of `y − xπ` is `|y − xα|²`, the area scaling of the probe
(`probeCount_eq_normSq`, `det_mulMatrix`); `𝒬` is a boundary square iff `t² ≤ 4q` (`boundarySquare_iff`). It
is then the sum of the squares of two linear counts, the real and imaginary parts of the probe at its mode;
one linear count is not enough (`kreinSquare_through_linear_iff`). On repeated oscillators the boundary
square becomes a positive Hermitian form (`bornRule_positive_iff_hermitian`). In the language of operator
algebras: the boundary algebra with the partner involution has the Krein square as GNS form, and its GNS
representation on `ℂ` exists exactly when the modes oscillate (`exists_starRep_iff`).

**Q5. Does Hecke at a second place constrain a count?** Only through conservation. A place of degree `n`
fixes the counts of `1 ∓ πⁿ`, whose conservation holds on every black hole (`conservation_at_every_level`).
An overdamped fake keeps positive counts and conservation at every level and a covariant count, and
violates the law at `2 − π` (`hecke_conservation_without_law`).

**Q6. Why do long horocycles thermalize at `y^{3/4}`, and is the rate a consequence of a count?** The
horocycle mean of a source is a count:

  `∫₀¹ F_ψ(x + iy) dx = 2ψ(y) + 2 Σ_{c ≥ 1} φ(c) ∫ ψ(y / (c²(v² + y²))) dv`

(`horocycleMean_eq_fareySum`): the cusp images of denominator `c` are the `φ(c)` Farey fractions `d/c`, each
contributing the time spent in its horoball; for a shell this is the average number of cusp images met
(`pseudoEisenstein_shell`, `horocycleMean_shellCount`). The horocycle at height `C⁻²` reads the Farey points of
order `C` normalized by `C²` (`fareyCount_eq_order`). RH holds iff every smoothed Farey count has square-root
error, `Σ φ(c) w(c/C) = m C² + O(C^{1/2+ε})` (`riemannHypothesis_iff_squareRootFareyLaw`). So
`3/4 = (2 − 1/2)/2`, the area exponent minus the square-root fluctuation per unit of `−½ log y`; equivalently
`1 − Re ρ/2 = 1/2 + (1 − Re ρ)/2`, the horocycle exponent of a zero is `1/2` plus its ringdown damping rate,
so `y^{3/4}` and `e^{−t/4}` read the same pole `ρ/2`. A count law over `ℤ` gives the rate through RH; the
horizon's own count is linear, and the rate is its square-root law.

**Second physical question: does a long closed horocycle thermalize faster than `y^{1/2}` by any power?**
Exactly when `ζ` has a zero-free strip: for `0 < δ ≤ 1/4`, every zero with `Re ρ > 0` has `Re ρ ≤ 1 − 2δ`
iff every Farey count reaches its limit at rate `y^{1/2+δ−ε}` (`zeroFreeStrip_iff_fareyCount_rate`).
Unconditionally smooth profiles have rate `y^{1/2} exp(-√(-log y))`
(`horocycle_rate_stretched_exp`, `fareyCount_rate_stretched_exp`), hence `O(y^{1/2})`, every
logarithmic power saving, and `o(y^{1/2})` (`horocycle_rate_sqrt_exact`, `horocycle_rate_log_pow`,
`horocycle_div_sqrt_tendsto_zero`). Hardy's critical-line zero forbids any common exponent
`α > 3/4` (`not_horocycle_rate_gt_three_quarters`, `not_fareyCount_rate_gt_three_quarters`).

**Rates for sharp shells.** A shell `a ≤ Im < b` is a source with a jump. Its Farey kernel is explicit
(`fareyKernel_shell`), the mean number of cusp images met is `4y(H(X_a) − H(X_b))` with the horoball
profile `H(X) = Σ φ(c)√((X/c)² − 1)`, `X_a = (ay)^{-1/2}` (`horocycleMean_shell_eq`), and the horoball
profile is a Möbius sum of quarter discs, `H(X) = Σ_d μ(d) Σ_{m ≥ 1} √((X/d)² − m²)`
(`horoballSum_eq_moebius`). Unconditionally a sharp shell thermalizes at rate `y^{1/2}` to
`(6/π)(1/a − 1/b)`, with error at most `76(√(y/a) + √(y/b))` for `1 < a < b`, `0 < y ≤ 1/b`
(`shell_rate_sqrt`). Concavity gives `|E(Y)| ≤ 8√Y` (`abs_circleRemainder_le_sqrt`); bounded
harmonic Möbius sums then give `|H(X) − 3X²/(2π)| ≤ 19X` (`abs_horoballSum_sub_le_linear`).
The error splits into `Σ_{d ≤ X} μ(d) E(X/d)` and two Möbius main-term remainders
(`horoballSum_decomposition`). RH bounds the latter by `O_ε(X^{1/2+ε})`
(`moebius_harmonic_and_sq_tail_of_rh`). For **any fixed shell** `1 < a < b`, rate
`O_ε(y^{3/4−ε})` is equivalent to RH together with
`Σ_{d ≤ X} μ(d) E(X/d) = O_ε(X^{1/2+ε})`
(`single_shell_rh_rate_iff_rh_and_moebius_circle`, `horoball_rh_rate_iff_rh_and_moebius_circle`).
Thus one shell's RH rate implies every shell's; no single shell admits exponent `α > 3/4`
(`not_single_shell_rate_gt_three_quarters`). See
[ClosedHorocycleThermalizationAndSharpShells.lean](ClosedHorocycleThermalizationAndSharpShells.lean).

**Fail for non-arithmetic groups.** The count fails for the Hecke group `G₅ = ⟨S, T_φ⟩` at the second place
of its trace field. A unimodular element counts nonnegatively at a place iff the conjugate trace satisfies
`σ(tr γ)² ≤ 4` (`placeCount_nonneg_iff`); the second place of `γₙ = TⁿS` counts nonnegatively exactly for
`n ≤ 3`, for `γₙ` and `γₙ²` (`secondPlace_nonneg_iff`, `secondPlace_sq_nonneg_iff`); `γ₄` has the count
`4 − 2√5 < 0` at the probe `1 + π` (`fourth_word_negative`). The invariant traces `tr γₙ²` are irrational
(`trace_sq_irrational`), so the second place is a place of the invariant trace field; for `G₃ = SL₂(ℤ)`,
`G₄`, `G₆` the same words have integer invariant traces (`trace_sq_int_of_sq_int`) and no second place. At
the first place `G₅` has the dynamics of the arithmetic groups (`firstPlace_hyperbolic`). By Takeuchi's
criterion [C] a failing place is exactly non-arithmeticity. A non-congruence subgroup of `SL₂(ℤ)` has
integer traces and one place, and passes the test [C]: the count separates arithmetic from non-arithmetic
groups, not congruence from non-congruence ones.

The same holds for every non-arithmetic Hecke group. For `G_q`, `q ≥ 3`, the invariant traces
`tr γₙ² = n²λ_q² − 2` (`trace_sq_hecke`) lie in `ℚ(λ_q²)`; by Niven's theorem `λ_q²` is irrational unless
`q ∈ {3, 4, 6}` (`irrational_heckeInvariant`), where it is `1, 2, 3` and `ℚ(λ_q²)` has one place
(`heckeInvariant_arith`, `arithmetic_one_place`). `λ_q²` is a root of `P_q = D_q(X − 2) − 2`
(`heckePoly_aeval`), every root of `P_q` is `2 + 2 Re w` with `w^q = 1`, real in `[0, 4]`
(`real_of_heckePoly_root`), so for `q ∉ {3, 4, 6}` the minimal polynomial has a second real root
`r ∈ (0, 4]` (`exists_second_place`), and at the place `λ_q² ↦ r` the count of `γₙ²` is negative at
`1 − π` once `n² r > 4` (`hecke_count_fails`).

## 6. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| A count law is its three channel numbers | `countLaw_eq_form`, `countLaw_eq_genusForm`, `exists_genusCountLaw_iff` | unconditional |
| The count law at every genus | `exists_levelCountLaw_iff`, `towerCountLaw_iff_unitary`, `towerCountLaw_iff_crude_bound` | unconditional, every curve datum |
| The count law of a true curve at every genus | `hyperelliptic_countLaw`, `splitHyperelliptic_countLaw` | unconditional, odd-degree hyperelliptic curves |
| The Rosati height is the Born rule | `rosatiDeg_delay`, `rosatiDeg_twoTerm`, `rosati_tfae`, `hyperelliptic_naiveHeight` | unconditional |
| The Jacobian count at genus two | `mirror_coprime`, `card_points_bielliptic`, `bielliptic_countLaw`, `bielliptic_weil`, `bielliptic_weil_tower` | unconditional, bielliptic curves, odd characteristic |
| The count law of every hyperelliptic curve | `degSumW_eq_zero_of_squarefree`, `chiC_leadingCoeff_mem_lRoots`, `riemannHypothesis_evenHyperelliptic`, `abs_card_points_sub_le_hyperelliptic`, `hyperelliptic_countLaw_every`, `genusTwo_countLaw` | unconditional, every degree, odd characteristic |
| The golden fake fails through the count | `golden_counts_without_law` | unconditional |
| The genus-two rung | `genusTwo_firstLevel_iff`, `genusTwo_tower_iff`, `firstCountLaw_does_not_force_damping` | unconditional, `q ≥ 2` |
| The two halves of a Born rule | `det_sq_of_bornRule`, `partner_of_bornRule`, `normSq_eq_of_bornRule`, `bornRule_pow` | unconditional, every delay |
| The Born rule at genus one is unique | `countLaw_covariant_eq`, `exists_covariantCountLaw_iff`, `probeCount_covariant` | unconditional |
| No Born rule without the functional equation | `throat_no_bornRule` | unconditional |
| The Born rules of an oscillator bank | `bornRule_bank_blocks`, `bornRule_bank_eq`, `exists_positive_bornRule_bank_iff'`, `bornRule_positive_iff_hermitian`, `bornRule_positive_iff_classes`, `offCircle_quadruple` | unconditional |
| The Born rules at genus two | `bornRule_genusTwo_eq`, `genusTwoKreinPair_positive_iff`, `exists_positive_bornRule_iff`, `genusForm_eq_kreinSum` | unconditional, `q ≥ 2` |
| Boundary square is oscillation | `kreinSquare_eq_normSq`, `probeCount_eq_normSq`, `boundarySquare_iff` | unconditional |
| The boundary algebra | `norm_probe`, `state_star_mul_self`, `exists_positive_state_iff`, `exists_starRep_iff`, `exists_faithful_bank_iff`, `trace_transpose_mul_self_nonneg` | unconditional |
| Hecke supplies conservation, not the law | `conservation_at_every_level`, `hecke_conservation_without_law` | unconditional |
| Linear counts are degenerate | `eq_zero_of_additive_countLaw`, `countLaw_through_linear_degenerate`, `kreinSquare_through_linear_iff` | unconditional |
| The count door over `ℤ` | `riemannHypothesis_iff_tateLimit_of_count`, `riemannHypothesis_of_count_at_bounded_distance`, `exists_near_count_of_riemannHypothesis` | equivalence |
| The Born rule over `ℤ` | `atomGram_eq_ratio`, `integerProbe_dilate`, `tateLimit_dilate` | unconditional |
| The Farey reading of the horocycle | `card_coprime_Ico`, `horocycleMean_eq_fareySum`, `pseudoEisenstein_shell`, `pseudoEisenstein_add`, `shellCount_add` | unconditional |
| The horocycle rate is the square-root Farey law | `fareyCount_eq_order`, `fareyCount_rate`, `re_le_of_fareyCount_rate`, `riemannHypothesis_iff_squareRootFareyLaw` | unconditional rates; RH equivalence |
| Thermalization faster than the square root is a zero-free strip | `zeroFree_iff_zeta_lower_bound`, `zeroFreeStrip_iff_fareyCount_rate` | equivalences |
| The rate of a sharp shell | `fareyKernel_shell`, `horoballSum_eq_moebius`, `quarterDisc_bounds`, `horoballSum_decomposition`, `shell_rate` | unconditional, explicit constants |
| The count fails at the second place of `G₅` | `placeCount_nonneg_iff`, `heckeWord_map`, `secondPlace_nonneg_iff`, `trace_sq_irrational`, `fourth_word_negative`, `trace_sq_int_of_sq_int` | unconditional |
| Every non-arithmetic Hecke group fails through the count | `irrational_heckeInvariant`, `real_of_heckePoly_root`, `exists_second_place`, `hecke_count_fails`, `arithmetic_one_place` | unconditional, every `q ≥ 3` |

## 7. Tools the programme develops

- **A bulk construction of `K` on integer probes**: the exact specification. The Tate-limit door
  (`TheTateLimitOfACount`), the Born rule over `ℤ` (Hecke dilation), the leading term as a function of ratios,
  and the refutation of every linear count (`LinearCountsAreDegenerate`). The construction itself is RH.
- **A dictionary between heights on Jacobians and solutions on branched graphs**: the Rosati form on the probe
  ring is the trace-form Born rule; its two-term part is the count law of each level; height, sign, count
  law and damping are one condition (`TheRosatiHeightIsTheBornRule`); on the graph side the count law selects
  the equal-weight member of the family of Born rules (`genusForm_eq_kreinSum`). True curves of every genus
  satisfy all of it, with Stepanov's auxiliary polynomial as producer
  (`TheCountLawOfATrueCurveAtEveryGenus`), and every hyperelliptic curve of either parity satisfies the
  count law (`TheCountLawOfEveryHyperellipticCurve`). At genus two heights are the producer on bielliptic curves: the
  height of the Jacobian is the sum of Manin's heights on the two factors
  (`TheJacobianCountOfABiellipticGenusTwoCurve`).
- **A boundary operator algebra whose GNS form on sources is Krein**: the probe algebra `R[π]/(π² − tπ + q)`
  with the partner involution, whose GNS form is the Krein square for every state, with a positive state and
  a GNS representation exactly when damped, and a faithful state on a bank exactly when every oscillator is
  strictly damped (`TheBoundaryAlgebraOfABlackHole`); over `ℤ` the group algebra of `ℚ_{>0}` with
  `r ↦ C(log r)` (APD), restricted to the integer probes (`atomGram_eq_ratio`); on graphs the Born rules of a
  delay, hyperbolic on off-circle quadruples (`hyperbolicForm_bornRule`) and Hermitian on repeated oscillators.
- **Lyapunov functionals from counts**: `bornRule_pow` and `bornRule_pow_delay`; a positive Born rule puts
  every mode on the universal circle (`normSq_eq_of_bornRule`).
- **Horoball lattice-point counts attached to sources**: shell counts, coprime windows, Farey kernels,
  weights and counts (`TheFareyReadingOfTheHorocycle`, `TheHorocycleRateIsTheSquareRootFareyLaw`); for
  sharp sources the explicit kernel, the Möbius sum of quarter discs and the unconditional rate
  (`TheRateOfASharpShell`, `ClosedHorocycleThermalizationAndSharpShells`).
- **Counts at the places of a trace field**: the Krein square of the conjugate element, the universal words
  of a Hecke group over `ℤ[X]`, Niven's theorem for `λ_q²`, the Dickson polynomial whose roots are the real
  conjugates, places from roots of the minimal polynomial
  (`TheCountFailsAtTheSecondPlaceOfAHeckeTriangleGroup`).
- **Zero-free half-planes as rates**: the three-circles lower bound right of a zero-free half-plane
  (`ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip`).
- **The count-law calculus and self-improvement**: three-number determination, genus forms, levels, towers,
  crude counts (`TheCountLawAtEveryGenus`, `TheCountLawOfATrueCurveAtEveryGenus`).
- **Explicit genus two**: integer traces by Newton's recurrence, the two towers, the block delay
  (`TheGenusTwoRung`, `TheBornRuleAtGenusTwo`).

**Used from the corpus.** Curve data and the Toeplitz form (ACS), the Rosati form and naive heights (ACP,
AET), the hyperelliptic curve datum and Stepanov's theorem (AET, RHTower), black holes, fakes, throats, the
genus-two graph, the integer probes and Manin's height count (ASH), pseudo-Eisenstein series and Zagier's
theorem (BHR), the three-circles machinery (HTGeometry, RHTower), positive definiteness on `ℚ_{>0}` (APD),
the divisor swap, the Möbius form of `φ`, the harmonic bound and `Σ μ(d)/d² = 6/π²` (RHTower).

## 8. Traps

| Trap | Truth |
|---|---|
| A count law is a law of wave dynamics | It is a statement about the delay on the probe ring; fakes have all the dynamics |
| The parallelogram law needs positivity | The Krein square is quadratic on every black hole; the fake's count is `|𝒬|` |
| Positive counts at every level exclude a fake | Fakes have `qⁿ + 1 ∓ V_n > 0` and conservation at every level (`hecke_conservation_without_law`) |
| The count law at the first level is damping | Only at genus one; at genus two it holds for `q ≤ 19`, damping for `q ≤ 3` |
| A sharp count bound is needed | Any constant at every level self-improves (`towerCountLaw_iff_crude_bound`) |
| A covariant count is quadratic | `|𝒬|` is covariant on every black hole (`probeCount_covariant`) |
| The functional equation is a positivity | It is the existence of a nondegenerate Born rule; the genus-two graph has one at every `q` |
| Off-line modes destroy the Born rule | A quadruple off the circle keeps a hyperbolic Born rule; it loses only the count |
| Repeated eigenvalues give one Born rule | They give a Hermitian family, positive iff the Hermitian form is; a bank is the direct sum over its trace classes |
| Integrality of the mode data forces a count | Integral data with one trivial zero and the first law still have a slow mode |
| `C*`-positivity of the delay algebra is the count | The Hilbert involution is positive on every black hole (`trace_transpose_mul_self_nonneg`); the count is the positivity of the partner involution (`exists_positive_state_iff`) |
| Hecke positivity constrains counts | Hecke fixes only the counts of `1 ∓ πⁿ`, whose conservation always holds |
| Over `ℤ` the quadratic half is missing | It holds exactly: parallelogram and Hecke dilation (`integerProbe_dilate`); the count is missing |
| A count must obey the law at finite size | Only its Tate limit matters (`nonneg_of_tateLimit`) |
| The horizon's counts of cusp images can be the count law | They are linear in the source and never obey it (`eq_zero_of_additive_countLaw`) |
| The square of one linear count can be | It is degenerate, the Krein square only at the critical edge (`kreinSquare_through_linear_iff`) |
| Heights at genus two need a genus-two height pairing | On bielliptic curves the sum of two elliptic heights is the count (`bielliptic_countLaw`) |
| Non-arithmetic groups fail through their dynamics | `G_q` has a cusp, horocycles and hyperbolic words; it fails through the count at a second place (`hecke_count_fails`) |
| RH alone settles the sharp-shell rate | Every single shell's `O_ε(y^{3/4−ε})` rate is equivalent to RH plus Möbius–circle cancellation (`single_shell_rh_rate_iff_rh_and_moebius_circle`) |

## 9. Where it sits in the research, and the neighbouring programmes

| Neighbour | Interface |
|---|---|
| ArithmeticScatteringHolography | black holes, `CountLaw`, Krein square, probe ring, fakes, throats, genus-two graph, integer probes; the wave mechanisms CTH takes as given: exact d'Alembert and contour expansion, flux balance, Hecke as time shift, Krein translation invariance, Lax–Phillips semigroup, Manin's count with the poles of a height as channels above a place; CTH is the count half of ASH |
| BlackHoleRingdown | the modular horizon as a quotient of the Rindler wedge of AdS₄, resonant states, general `L²` data and metric; the equidistribution of horocycles as the spatial face of ringdown |
| BlackHoleRingdown (horocycles) | pseudo-Eisenstein series, horocycle means, Zagier's theorem; CTH reads them as Farey counts |
| ArithmeticCastelnuovoSeveri | curve data, Toeplitz form, power-sum elimination; the genus form is half its two-term defect |
| ArithmeticEffectivityTheory, ArithmeticCorrespondencePositivity | Tate limits, naive heights, the Rosati form, the hyperelliptic datum; the Rosati height is the Born rule |
| RHTower (Stepanov, Farey, three circles) | the producer of the count on true curves, Farey discrepancy, `1/ζ` bounds |
| ArithmeticPositiveDuality | positive definiteness on `ℚ_{>0}`, the GNS form of the integer probes |
| HeckeKreinToeplitz | integer windows carry the whole index |

**In the research.** The review's §2.7 asked for a bulk-defined count of open channels for integer sources.
CTH shows that this question is RH in both directions; splits the count law into a Born rule, which every
arithmetic structure supplies (the functional equation on graphs, Hecke dilation over `ℤ`, the Rosati form on
curves), and a count, which only true curves supply; proves the count on true curves of every genus and,
at genus two, from heights of the Jacobian; shows that every non-arithmetic Hecke group fails through
the count at a second place; gives the unconditional rate of sharp shells;
classifies the Born rules of oscillator banks; and refutes the natural counts of the horizon, which are
linear in the source. CTH is not an RH route. Its value is the exact separation of the two halves, the
calibration at every genus, and the precise shape of the missing object.

**The table of cases.**

| | Born rule (quadratic, covariant) | count (nonnegative) |
|---|---|---|
| true curve, every genus | yes: the Rosati form | yes (`hyperelliptic_countLaw_every` for every hyperelliptic curve; genus one by Manin's height, ASH) |
| bielliptic genus-two curve | yes: the sum of two Rosati forms | yes, from heights alone (`bielliptic_countLaw`) |
| fake | yes (`𝒬`) | `|𝒬|` is a count, not quadratic |
| throat, `b ≠ 2` | none | — |
| genus-two graph | yes, every `q` | exactly for `q ≤ 3` |
| off-circle quadruple | yes, hyperbolic | never |
| `ℤ` | yes (`integerProbe_parallelogram`, `integerProbe_dilate`) | unknown: RH |
| modular horizon, Farey and shell counts | linear, never quadratic | yes |
| Hecke group `G_q`, `q ∉ {3, 4, 6}`, second place | the Krein square of the conjugate | fails (`hecke_count_fails`; `G₅` at `γ₄ = T⁴S`) |

## 10. Success criteria

- **Recover Hasse from channels at all probes**: ASH (`hasse_of_countLaw`).
- **Hasse–Weil at every genus (A32)**: the count law at every level is Hasse–Weil (`towerCountLaw_iff_unitary`),
  any crude count self-improves to it (`towerCountLaw_iff_crude_bound`), on every odd-degree hyperelliptic
  curve the channel numbers extend to the count law at every level (`hyperelliptic_countLaw`), so do they on
  every hyperelliptic curve of even degree, hence on every genus-two curve (`hyperelliptic_countLaw_every`,
  `genusTwo_countLaw`), and on every bielliptic genus-two curve heights of the Jacobian produce it
  (`bielliptic_countLaw`, `bielliptic_weil_tower`).
- **Fail on fakes through the count, not through dynamics**: `golden_counts_without_law`,
  `hecke_conservation_without_law`, `exists_probe_neg_of_overdamped`, `offCircle_quadruple`.
- **Supply the partner law globally**: `partner_of_bornRule`, `throat_no_bornRule`.
- **Fail for non-arithmetic groups**: every non-arithmetic Hecke group `G_q` fails through the count at a second
  place of its invariant trace field (`hecke_count_fails`; explicitly for `G₅`, `fourth_word_negative`),
  while `SL₂(ℤ)`, `G₄`, `G₆` have one place (`arithmetic_one_place`); on graphs the fakes have every dynamical
  structure and no count law.
- **Explain the blindness of KMS, Schur, `C*` and Hecke-algebra positivity**: they are positivities of the
  energy, the flux or the linear Hecke action, and hold on fakes (ASH); `C*`-positivity is the positivity of
  the Hilbert involution, which holds on every black hole (`trace_transpose_mul_self_nonneg`), while the count
  is the positivity of the partner involution, which is damping (`exists_positive_state_iff`); the count law is a statement about the
  quadratic form on the probe ring, which Hecke reaches only through conservation
  (`conservation_at_every_level`), and which linear structures cannot reach (`eq_zero_of_additive_countLaw`).
- **Explain the two RH rates**: §5 Q6; for sharp shells, §5 *Rates for sharp shells*.
- **Consistent with raw echo spikes and GUE**: the count law is quadratic in the probe and diagonal in the
  modes; it constrains no spacing and no pointwise echo.

## 11. What a contribution must be

A theorem about counts, not a dictionary entry; it says which half of the count law it concerns; it states
what it does on the fakes, the throats and the genus-two graph; and over `ℤ` it says whether it reaches the
count or stops at the Born rule. A candidate count of integer sources must be quadratic of full rank and
Hecke covariant; a linear count is not a candidate.

**The programme would close RH** with a count of the integer probes, defined without the Weil form, whose Tate
limit is `Q` (`riemannHypothesis_iff_tateLimit_of_count`).

## 12. Open research topics

The questions, tools, calibrations and criteria of §2.10 are answered and built in §§5–10. The topics below
are the open problems those answers expose; the first is RH itself, which §2.10 names as the limit of the
programme ("a language until a count exists").

1. A quadratic count over `ℤ` with Tate limit `Q`, defined without `Q`. This is RH.
2. A height producer on a simple genus-two Jacobian. Every genus-two curve has the count law
   (`genusTwo_countLaw`, produced by counting); on bielliptic curves heights produce it
   (`bielliptic_countLaw`). Open: the height pairing of a simple Jacobian over `𝔽_q(T)` as a second producer.
3. The Farey reading of a non-arithmetic Hecke group: its cusp images are not Farey fractions, and the
   horocycle mean of a source is a sum over the cusps of `G_q` with no totient weights.
4. The RH rate for sharp shells: whether RH implies `Σ_{d ≤ X} μ(d) E(X/d) = O_ε(X^{1/2+ε})`
   for the quarter-disc remainder `E`. This is the exact remaining condition, independent of shell
   endpoints (`single_shell_rh_rate_iff_rh_and_moebius_circle`).
