# Arithmetic Holography of the Modular Horizon (AHMH)

Namespace `GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon`; umbrella
`ArithmeticHolographyOfTheModularHorizon.lean`; 17 modules.

## 1. Motivation

The zeros of `ζ` are physical. On the massless topological AdS₄ black hole with horizon `PSL₂(ℤ)\ℍ` (the
*modular horizon*) every zero `ρ` is a resonance of the wave equation in the mirror-even (Eisenstein)
channel, at spectral parameter `s = ρ/2` and ringdown rate `½ − Re s = (1 − Re ρ)/2`; the mirror-odd channel
is a cavity of Maass cusp forms with no resonances. RH is *universal damping*: every resonance decays at
rate `¼` (`BlackHoleRingdown.riemannHypothesis_iff_pulse_ringdown`). The archimedean place is a second
physical object: the archimedean Frobenius is `2π√(mn)` times the bulk propagator `G_{1/2}` of a scalar of
mass `m² = −¾` in Euclidean AdS₃ = `ℍ³`, quantized at `Δ = ½`, between two points of one geodesic
(`SurfaceOfSpecZ.archProfile_eq_hyperbolicGreen`). Its normal modes are `½ + 2k`, the distances of the trivial
zeros from the critical line.

In AdS₃ gravity a black hole's damping can be kinematics. The BTZ black hole is the modular `S`-image of
thermal AdS₃; its quasinormal frequencies are images of the real normal modes of the confined phase, and their
decay rates are fixed by the conformal weight alone. If the modular horizon were the modular image of a
confined system with real normal modes, universal damping would be kinematics of the same kind. That is the
programme's main conjecture (B117 of the review):

> **Modular confinement.** The mirror-even channel is the modular image of a unitary confined system built
> from the worldline modes and prime interactions; every resonance `ρ/2` is the image of a real normal mode.

AHMH makes the three objects and the maps between them precise, proves what each map can carry, and decides
the conjecture form by form.

**The answer in one line.** The modular map is *position rigid*: for every seed the resonances sit at the
zeros of `ξ(2s)`, fixed by the group, and the seed enters only through the residues `Λ_F(ρ/2)`. So confinement
holds collectively (unitary seeds see every resonance) and never kinematically (no seed, weight or spectrum
moves a resonance); the frequency form of B117 is a Hilbert–Pólya realization and is RH. Positivity cannot
enter through the back door either: a one-sided bound on the dual (black-hole) side is as strong as the rate
itself. The residue question B109 has a positive answer: pairs of Hecke–Maass eigenforms see every resonance, and
one cavity function — of odd tent fields, of Maass eigenforms, or of Hecke eigenforms — sees all of them, so the
horocycle rate of its energy is a complete receiver. The Krein structure of the channel lives on reflection pairs of resonances: the
Krein form of one resonance has infinite index of both signs, on the line or off it, while the reflection Krein
form `Λ(s) Λ̄(s*) + Λ(s*) Λ̄(s)` of the cavity has exactly one negative square at each off-line zero and none on
the line, so RH is the positivity of these forms. The receivers are sharp: the ringdown rate of every seed whose
completed transform decays like `e^{−π|t|}` is its zero-free region, and RH holds iff every two-mode state of the
cavity rings down at `y^{3/4−ε}` (Zagier's theorem for the cavity); one cuspidal function `g` of Hecke–Maass forms is a
sharp receiver on its own: RH ⟺ `|g|²` rings down at `y^{3/4−ε}`, and a zero-free strip ⟺ some rate `y^α`, `α > ½`.
Universal damping is thereby an exact statement about one cavity energy, and it is RH. A single eigenform is
not enough: the diagonal entry of a Hecke eigenform is `ζ(s)` times Shimura's weight-½ integral, so one Hecke
eigenform is blind to every zero `ρ` for which `ρ/2` is also a zero, and B109 for one eigenform already excludes
such halving pairs.

## 2. The holographic triangle

| Corner | Object | What it carries |
|---|---|---|
| **Horizon** `H` | `SL₂(ℤ)\`(Rindler wedge of AdS₄); horizon `PSL₂(ℤ)\ℍ` | mirror-even channel with scattering `Λ(2s−1)/Λ(2s)`, resonances `s = ρ/2`; odd cavity of Maass cusp forms |
| **Worldline** `W` | Euclidean AdS₃ = `ℍ³`, vertical geodesic `z_n = (0,0,n)`, scalar `m² = −¾`, `Δ = ½` (and `3/2`) | normal modes `½ + 2k`; propagator `2πG_{1/2}(d) = Σ_k e^{−(2k+½)d}` = archimedean Frobenius |
| **Confined dual** `C` | unitary systems with real spectrum: seeds, the `c = 2` Narain CFT, oscillator banks, the GNS space of the Born rule with its Hecke clock | positive spectral data; real normal modes |

| Edge | Map | Content |
|---|---|---|
| `C → H` | **modular map**: Poincaré sum; on horocycles, Rankin–Selberg unfolding | linear in the seed; position rigid |
| `W → H` | **one image**: a single `S`-reflection, the bounce `(1 − e^{−v})^{−1/2}` with transform `B(w, ½)` | kinematic Gamma lattice |
| image sum | echoes of denominator `c`, delay `2 log c`, weight `φ(c)/c` | the arithmetic resonances are poles of its Dirichlet series |
| `W → C` | **free part**: the worldline as a unitary system with spectrum `½ + 2k` | the archimedean term of the explicit formula |
| primes → `C` | **interactions at times `log n`**: the prime side of the explicit formula; `T_p` = translation by `log p` | the Weil form; its unitarity is RH |

## 3. Objects

| Object | Lean | Meaning |
|---|---|---|
| Seed | `IsSeed` | continuous, bounded, `SL₂(ℤ)`-invariant, `‖F(z)‖ ≤ C e^{−c Im z}` on `Im z ≥ 1` |
| Response | `response` | the horocycle mean `a_F(y) = ∫_0^1 F(x + iy) dx` |
| Completed transform | `seedTransform` | `Λ_F(s) = ∫_𝒟 F · E*(s − ½)`, `E*(u) = ξ(1+2u)E(½+u)/((1+2u)2u)` (`EisAuto.completedEisenstein`) |
| Response continuation | `responseContinuation` | `Λ_F(s) · 2s(2s − 1)/ξ(2s)` |
| Numerator and polar transforms | `numeratorTransform`, `polarNumerator`, `polarTransform` | `N_F(s) = ∫_𝒟 F N(s − ½)` with `E* = N/((1+2u)2u)`; `(2u − 1)N(u)` and its transform |
| Mass constant, lower transform | `massConstant`, `lowerTransform`, `dualProfile` | `c_F = (3/π)∫_𝒟 F`; the continuation of `∫_0^1 (a_F − c_F) y^{s−2} dy`; the remainder in Landau's variable |
| Cavity family | `IsCavityFamily` | continuous invariant `u_j` under one envelope `‖u_j(z)‖ ≤ e^{−κ Im z}` |
| Cusp family | `cuspFamily` | `v_j/M_j` for any sequence of Maass cusp forms `v_j` |
| Cavity function | `cavity` | `g_x = Σ_j x_j 2^{−j} u_j`, `x ∈ ℕ →ᵇ ℂ` |
| Pairing, pair form, pair entries | `pairing`, `pairForm`, `pairEntry` | `∫_𝒟 g conj(h) E*(s − ½)`; `B_s(x,x')`; `b_{jk}(s)` |
| Right resonances | `rightResonances` | `ρ/2` for the zeros `ρ` of `ζ` with `Re ρ > ½` |
| Height profile, odd cusp field | `IsHeightProfile`, `oddCuspField` | continuous `φ` vanishing below `2` and high up; `G_φ = φ(Im γz) sin(2π Re γz)` for `Im γz > ½` |
| Tent, tent energy | `tent`, `tentEnergy` | the tent of height `½` on `[j + 3, j + 4]`; `d_j(s) = ∫_𝒟 G_j² E*(s − ½)` |
| Maass form of the eigenbasis, tent datum | `maassForm`, `tentData` | the scalar cusp form of the `i`-th cuspidal eigenvector; the `L²` class of `G_j` |
| Reflection Krein matrix | `reflectionMatrix`, `tentReflectionKrein` | `v w* + w v*` with `v_a = d_{t_a}(ρ/2)`, `w_a = d_{t_a}((1 − ρ̄)/2)` |
| Ringdown constant, pole numerator | `seedRateConst`, `seedPoleNum`, `seedRegPart` | `c = P_F(1)/(2ξ(2))`; `P_F(s)/(2ξ(2s)) − cΓ(s)`; the regular Mellin transform of `a_F − c e^{−y}` |
| Two-mode energy | `twoModeEnergy` | `|u + c v|²` for cusp forms `u, v` and `c ∈ ℂ` |
| Odd cavity family | `oddFamily` | the normalized tent fields `G_j/M_j` |
| Horocycle profile | `horocycleProfile` | `W_s(y) = ∫_0^1 sin²(2πx) E*(s − ½; x, y) dx` |
| Resonance coefficient | `resonanceCoefficient` | `κ(u) = ξ(2u)/((2u − 1)2u)`, the surviving constant term at a resonance |
| Resonance Krein form, Krein Gram matrix | `resonanceKrein`, `kreinGram` | `𝒦_s(g, h) = ½(b_s(g, h) + conj b_s(h, g))`; its Gram matrix on tents |
| Pair Gamma factor | `pairGamma` | `2^{s−3}/Γ(s) Π Γ((s ± ν₁ ± ν₂)/2)` |
| Hecke representatives, adjugates | `HeckeCoset.A`, `HeckeCoset.Astar` | `α_∞ = (p 0; 0 1)`, `α_b = (1 b; 0 p)`; `α_∞^* = (1 0; 0 p)`, `α_b^* = (p −b; 0 1)` |
| Hecke bijection | `HeckeCoset.heckeEquiv`, `HeckeAdjoint.pslEquiv` | `(i, γ) ↦ (γ', k)` with `α_i^* γ = γ' α_k`, on `SL₂(ℤ)` and on `PSL₂(ℤ)` |
| Hecke form | `IsHeckeForm` | a cusp form of eigenvalue `λ` that is an eigenfunction of every `T_p` |
| `L²` image of a cusp space | `L2Image`, `toImage` | `S(λ) ≅` its class in `L²(𝒟)`, with the Petersson product |
| Hecke basis | `heckeBasis`, `heckeV` | a finite spanning set of Hecke forms of `S(λ)`; their enumeration over the spectrum |
| Shimura kernel and integral | `Shimura.kernel`, `RHTower.HalfWeight.rsFold 1 (Shimura.kernel g)` | `G(z) = g(4z) θ̄(z) y^{1/4}`; its fold against the weight-½ Eisenstein series of level `4` |
| Shimura series | `Shimura.zCoef`, `Shimura.melC` | `ρ_W(j²)(8πj²)^{3/4−w}`; `Mel_ν(μ) = 2^{μ−1}Γ(μ)Γ(μ+ν)Γ(μ−ν)/Γ(2μ)` |
| Normalized Hecke sequence | `HalvingPairs.tauOf` | `τ(n) = ρ(n)/ρ(1)`, real, multiplicative, `τ(n)² = Σ_{d∣n} τ((n/d)²)` |
| Diagonal identity | `HalvingPairs.lhsD`, `HalvingPairs.rhsD` | the two sides of `4ρ(1)(s−1)c(w)Mel_ν(s/2)P_u(s) = Γ_ℝ(2s)(2π)^{−s}G(s)N s (s−1)ζ(s) Sh_u(w)`, `w = s/2 + ¼` |
| Modular horizon, pulses | `BlackHoleRingdown.pulseField`, `pseudoEisenstein`, `horocycleMean` | the exact wave theory |
| Echo train | `BlackHoleRingdown.echoKernel`, `bounceKernel` | the scattering as a train of single-image bounces |
| Worldline | `SurfaceOfSpecZ.archProfile`, `hyperbolicGreen` | `Σ_k e^{−(2k+½)d}`, `G_s(d) = e^{−(s−1)d}/(4π sinh d)` |
| Narain seed | `ModularBootstrap.narainScalarHeat` | scalar heat trace of the `c = 2` Narain CFT |
| Boundary algebra, standard forms | `CountingHolography` | the partner involution; GNS form = Krein square |
| Krein square over `ℤ` | `ArithmeticScatteringHolography.physicalKrein` | `e^{−τ/2} W_ℤ(f, f)` |

## 4. Language

- **Seed**: an input of the modular map; **confined seed**: one whose profile is a Euclidean correlator of a
  unitary system.
- **Response**: the horocycle mean of the modular image; its **remainder**: response minus its limit.
- **Resonance position**: a pole of the continued response transform; **residue**: its coefficient, `Λ_F(ρ/2)`.
- **Position rigidity**: the positions do not depend on the seed. **Residue holography**: the seed enters only
  through the residues.
- **Kinematic tower**: poles fixed by Gamma factors (one image) or by a non-decaying seed profile;
  **arithmetic tower**: the zeros of `ξ(2s)`.
- **Seen**: a resonance is seen by a seed if its residue is nonzero; a **receiver** turns a decay rate into the
  vanishing of residues.
- **Cavity**: the mirror-odd (cuspidal) channel; **cavity function**: a uniformly convergent combination of
  cavity modes (cusp forms or odd cusp fields); **pair entry**: the residue form of two cavity modes.
- **Resonance Krein form**: the Hermitian part of the energy pairing at a resonance; its **Krein signature** on a
  tent is the sign of `Re d_j(s)`.
- **Universal damping**: rate `¼` for every resonance; **frequency holography**: a map from individual normal
  modes to individual resonances.

## 5. Mechanisms

**From the corpus.**
1. *Ringdown = width.* Pulse decay `e^{−δτ}` ⟺ every zero has `Re ρ ≤ 1 − 2δ`; rate `¼` ⟺ RH
   (`BlackHoleRingdown.zeroFreeStrip_iff_pulse_ringdown`, `riemannHypothesis_iff_pulse_ringdown`); the
   horocycle rate `y^{½+δ}` is the same exponent (`CountingHolography.zeroFreeStrip_iff_fareyCount_rate`).
2. *The scattering is an echo train.* `∫ e^{−wτ} K(τ) dτ = B(w,½) ζ(2w)/ζ(2w+1)`
   (`BlackHoleRingdown.integral_cexp_mul_echoKernel_eq_completed`): every echo is one kinematic bounce; the
   arithmetic sits in the delays `2 log c` and weights `φ(c)/c`.
3. *Worldline.* `archKernel/√(mn) = 2πG_{1/2}(d)`, `2πG_{1/2} = 2πG_{3/2} + 1/(2 cosh(d/2))` (`SurfaceOfSpecZ`).
4. *Graph companions.* A graph black hole has a standard-form realization of its partner involution iff
   `t² ≤ 4q` (`CountingHolography.exists_standardForm_partner_rep_iff_damped`).
5. *Operator no-gos over `ℤ`.* Internal, vacuum-fixing and half-sided realizations of the Born rule are
   excluded (`CountingHolography.partner_standardForm_trichotomy`); a standard-form realization with the Hecke
   clock exists iff RH (`CountingHolography.riemannHypothesis_iff_exists_standardForm_bornRule`).
6. *Narain seed.* The `c = 2` Narain target average carries every arithmetic resonance with full multiplicity
   (`ModularBootstrap.narainMellinMean_full_order`).

**Proved here.**
7. *Seeds form a `*`-algebra containing the cavity.* Sums, products, conjugates and `|F|²` of seeds are seeds;
   every Maass cusp form is a seed with envelope `e^{−π Im z}` (`IsSeed.add`, `IsSeed.mul`, `IsSeed.star`,
   `IsSeed.normSq`, `isSeed_of_mem_cuspSpace`, `cuspForm_decay`).
8. *Continuation and functional equation of every seed.* `Λ_F` is holomorphic on `ℂ ∖ {0, ½, 1}` and
   `Λ_F(1 − s) = Λ_F(s)` (`differentiableOn_seedTransform`, `seedTransform_one_sub`), by Cauchy domination with
   the uniform bound `|E*(u)| ≤ α Y^a + β` on `𝒟`.
9. *Unfolding.* `Λ_F(s) = ξ(2s)/(2s(2s − 1)) · ∫_0^∞ a_F(y) y^{s−2} dy` for `Re s > 1`, `Im s ≠ 0`
   (`seedTransform_eq_mellin`), from the row sum of `E` and Fubini on the strip; on all of `Re s > 1` the response
   transform is `N_F(s)/ξ(2s)` (`mellin_response_eq`).
10. *Position rigidity.* The response transform of every seed continues to `Λ_F · 2s(2s−1)/ξ(2s)`, holomorphic
    at every `s ∉ {0, ½, 1}` with `ξ(2s) ≠ 0` (`responseContinuation_eq_mellin`,
    `differentiableAt_responseContinuation`).
11. *Every-seed receiver.* `|a_F(y) − c| ≤ C y^α` on `(0, 1]` forces `Λ_F(s₀) = 0` at the zeros `s₀` of `ξ(2s)`
    with `Re s₀ > 1 − α`; a seen zero caps the rate at `y^{1 − Re ρ/2}` (`seedTransform_eq_zero_of_rate`,
    `seedTransform_half_eq_zero_of_rate`, `not_rate_of_seen`).
12. *The pair form.* `B_s` is sesquilinear and bounded by `K ‖x‖ ‖x'‖` (`exists_pairForm_bound`); polarization
    `4B(x,y) = Q(x+y) − Q(x−y) + iQ(x+iy) − iQ(x−iy)` (`polarization`); `Q_s` is continuous (`continuous_quad`).
13. *Blind sets are nowhere dense.* If a pair sees `s`, the zero set of `Q_s` has empty interior: vanishing on a
    ball forces `Q_s(h) = 0` along every line through its centre, hence everywhere, hence every pair entry
    vanishes (`interior_quad_zero_eq_empty`).
14. *Baire.* Seeing a countable set is generic (`dense_cavity_seeing`, `exists_cavity_seeing`); truncations show
    pairs are necessary (`quad_eq_zero_of_pairEntry_eq_zero`); so one cavity function sees a countable set iff
    every point is seen by a pair (`exists_cavity_seeing_iff`).
15. *Cuspidality.* The cavity function of cusp forms has vanishing horocycle means
    (`response_cavity_cuspFamily_eq_zero`).
16. *Pair entries are Rankin–Selberg series.* Polarized Parseval `∫_0^1 u conj(v) = Σ_n a_n(u) conj(a_n(v))`
    (`hasSum_response_mul_conj`), dominated convergence and the two-K Mellin product give
    `∫_𝒟 u conj(v) E*(s−½) = ξ(2s)/(2s(2s−1)) (2π)^{−s} G(s; ν_u, ν_v) Σ_n ρ_u(n) conj(ρ_v(n)) |n|^{−s}`
    (`hasSum_mellin_pairResponse`, `pairing_eq_rankinSelberg`).
17. *Momentum universality.* `Σ_{d | n} d^w ≠ 0` for `Re w ≠ 0` (multiplicativity and geometric sums at prime
    powers, `divisorPowerSum_ne_zero`). Hence the Rademacher image sum `Σ_c c_c(n) c^{−w} = σ_{1−w}(n)/ζ(w)` of
    every momentum channel has the full order `−ord_ρ ζ` at every `ρ` with `Re ρ ≠ 1`
    (`meromorphicOrderAt_rademacher`, `rademacher_image_sum`), and every Whittaker coefficient `n^u σ_{−2u}(n)` of
    the completed Eisenstein function is nonzero at every resonance (`modeCoefficient_ne_zero_of_resonance`).
18. *The dual side has no sign.* Against the Eisenstein numerator `N(u)` the transform `N_F(s) = 2s(2s−1)Λ_F(s)` is
    holomorphic off `s = 1` (`differentiableOn_numeratorTransform`), and `(2u − 1)N(u)` is entire with value `1`
    at `u = ½` (`polarNumerator_half`); so the response transform `N_F/ξ(2s)` is analytic at every real point
    except a simple pole at `s = 1` with residue `c_F = (3/π)∫_𝒟 F` (`polarRatio_one`, `xi_two`), and the lower
    transform `∫_0^1 (a_F − c_F) y^{s−2} dy` is analytic at every real point (`analyticAt_lowerTransform`,
    `integral_lower_eq`). With `y = e^{−v/(2α)}` a one-sided bound `a_F − c_F ≤ C y^α` is Landau's hypothesis
    (`RHTower.exists_differentiable_extension_of_le_exp`, `exists_lower_extension_of_oneSided`); multiplying by
    `ξ(2s)` and continuing on quarter planes kills `Λ_F` at every zero with `Re s > 1 − α`
    (`seedTransform_eq_zero_of_lower_extension`, `seedTransform_eq_zero_of_oneSided`,
    `seedTransform_eq_zero_of_oneSided_lower`). A seen resonance `ρ/2` forbids either sign beyond `y^{1−Re ρ/2}`
    (`not_oneSided_of_seen`).
19. *Odd cusp fields and their strip.* For a height profile `φ`, `φ(Im w) sin(2π Re w)` is well defined on
    `Γ\ℍ` because a matrix with `c ≠ 0` maps heights above `½` below `2`; the field is continuous, modular,
    mirror-odd and lies under `M e^{−π Im z}` (`oddCuspField_smul`, `oddCuspField_mirror`,
    `continuous_oddCuspField`, `exists_envelope_oddCuspField`). On `𝒟` it is its profile, and a periodic function
    vanishing below height `1` has the same integral over `𝒟` and the strip (`setIntegral_fd_eq_strip_of_high`), so
    `∫_𝒟 G_φ² E*(s − ½) = ∫_0^∞ φ² W_s dy/y²` (`pairing_oddCuspField`).
20. *Phase law.* At a resonance `ξ(2s) = 0`: `E*(u) = κ(u) Y^{½−u} + tail` (`completedEisenstein_eq_of_resonance`),
    `W_s(y) = ½κ y^{1−s} + O(1)` (`horocycleProfile_eq_of_resonance`, `exists_tail_bound`), and `κ ≠ 0` because
    `ξ(ρ − 1) = ξ(2 − ρ)` with `Re(2 − ρ) > 1` (`resonance_data`). On a far tent the phase of `y^{1−s}` turns by at
    most `|Im s|/(j + 3)` and its size beats the tail: `Re(e^{iθ} d_j(s)) ≥ |κ|/2048 · (j + 3)^{−1−Re s}` whenever
    `cos(θ + arg κ − Im s · log(j + 7/2)) ≥ ¾` (`exists_tent_phase`). So every resonance is seen by a tent
    (`exists_tent_seeing`), and `|d_j(s)| ≍ (j + 3)^{−1−Re s}` (`exists_tentEnergy_ge`, `exists_tentEnergy_le`).
21. *B109 for cavity functions.* Baire over the tent family: a dense set of coefficient vectors gives a
    cuspidal, mirror-odd cavity function whose energy sees every right resonance (`dense_odd_cavity_seeing`,
    `exists_odd_cavity_seeing_every_right_zero`), with zero horocycle means (`response_cavity_oddFamily`).
22. *Krein inertia of the cavity.* Tents of different index have disjoint supports, so the Krein Gram matrix is
    `diag(Re d_j(s))` (`kreinGram_eq_diagonal`); far up the cusp the Krein sign of `G_j` is the sign of
    `cos(arg κ − Im s · log(j + 7/2))` (`tent_krein_sign`); a zero with `Re ρ > 0` is not real
    (`im_ne_zero_of_zero`), and the phases `Im s · log(j + 7/2)` meet every arc (`exists_cos_ge`).
23. *Pairwise visibility.* `h ↦ ∫_𝒟 G_j h̄ E*` is the inner product with the class of `G_j E*`, bounded on `𝒟`
    because `G_j` vanishes there above height `j + 4`; `G_j` is mirror-odd, so it is the `L²` sum of its components
    on the cuspidal eigenbasis (`BlackHoleRingdown.OddSector.hasSum_odd`, `exists_inner_basis_ne_zero`). Seeing passes
    to an eigenform `v_i`, and through the class of `v_i Ē*` (bounded since `v_i ≪ e^{−π Im z}`) to a second one:
    `∫_𝒟 v_l v̄_i E*(ρ/2 − ½) ≠ 0` (`exists_maass_pair_seeing`). The eigenbasis is countable (discreteness of the
    cusp spectrum), so Baire gives a cavity function of Maass cusp forms seeing every right resonance
    (`exists_maass_cavity_seeing_every_right_zero`).
24. *Reflection Krein index law.* `v w* + w v* = ½(v + w)(v + w)* − ½(v − w)(v − w)*` has at most one negative
    square and none if `v = w` (`negIndex_reflectionMatrix_le_one`, `negIndex_reflectionMatrix_self`); `⟨x, v⟩ = 1`,
    `⟨x, w⟩ = −1` gives one (`one_le_negIndex_reflectionMatrix`). The reflection `ρ* = 1 − ρ̄` of a zero is a zero
    (`reflect_zero`) and fixes exactly the critical line (`reflect_eq_self_iff`); off the line the decay exponents
    `1 + Re(ρ/2) ≠ 1 + Re(ρ*/2)` of the tent energies forbid proportionality (`not_proportional_of_lt`,
    `exists_tent_independent`).
25. *The ringdown rate of a seed.* The polar transform `P_F = 4s(2s−1)(s−1)Λ_F` of every seed is entire, odd under
    `s ↦ 1 − s` and polynomially bounded on `−¼ ≤ Re s ≤ 5/4` (`polarTransform_one_sub`, `exists_polarTransform_poly`);
    by Phragmén–Lindelöf an `e^{−π|t|}` bound on `Re s = 5/4` holds on the strip (`exists_polarTransform_decay`). The
    Mellin transform of `a_F − c e^{−y}` is `N(w + 1)/w`, `N = P_F/(2ξ(2s)) − cΓ` (`mellin_eq_seedRegPart`); a zero-free
    half-plane with polynomial bounds for `1/ζ` makes it regular, and the contour shift gives `|a_F − c| ≤ C y^{1−Θ/2−ε}`
    (`norm_response_sub_le_of_zeroFree`, `response_rate_of_zeroFree`, `response_rate_of_riemannHypothesis`).
26. *Two-mode energies.* For cusp forms `u, v`, `P_{u v̄}` on `Re s = 5/4` is `2(s−1) ξ(2s) G(s; ν_u, ν_v) (2π)^{−s}`
    times an absolutely convergent Rankin–Selberg series; `Γ(s)` cancels in `ξ(2s)G` and the four Gamma factors decay
    like `e^{−π|t|}` (`xi_mul_pairGamma`, `exists_pairPolar_right`, `exists_pairPolar_decay`). The energy `|u + cv|²`
    is the Hermitian combination of four pair energies (`response_twoModeEnergy`, `seedTransform_twoModeEnergy`), so it
    rings down at the zero-free rate (`twoMode_rate_of_zeroFree`), and by polarization one of `c ∈ {1, −1, i}` sees
    every resonance seen by the pair (`exists_twoMode_seeing`, `re_le_of_twoMode_rate`).
27. *One sharp receiver.* The pair bound on `Re s = 5/4` has the exponent `4N_Γ + 3` for every pair
    (`pairPolar_right_bound`); normalizers `M_j = envelope · (1 + Σ_{m ≤ j}(D_{jm} + D_{mj}))` give `D_{jk} ≤ M_j M_k`
    (`pairD_le`), so the energy of `g_x = Σ x_j 2^{−j} v_j/M_j`, integrated term by term over its double series, obeys
    `|P_{|g_x|²}(5/4 + it)| ≤ 4‖x‖²(1 + |t|)^N e^{−π|t|}` (`cavity_polar_right`); with a Baire-generic `x` this is a
    sharp receiver (`exists_sharp_cavity_receiver`). The construction uses only that the sequence of cusp forms sees
    every right resonance in pairs (`sharp_receiver_of_pairs`).
28. *Hecke cosets.* Modulo `p` a matrix of determinant `p` has rank one, so its columns are proportional and so are
    its rows: `M = γ' α_k` with `k = ∞` iff the first column vanishes mod `p`, and `M = α_i^* γ` with `i = ∞` iff the
    second row does (`leftQuot_mul`, `leftIndex_mul`, `Astar_mul_rightQuot`, `rightIndex_Astar_mul`). Matching the
    two decompositions is a bijection `P¹(𝔽_p) × SL₂(ℤ) ≃ SL₂(ℤ) × P¹(𝔽_p)`, `α_i^* γ = γ' α_k`
    (`heckeEquiv`, `heckeEquiv_spec`), compatible with `γ ↦ −γ` and so defined on `PSL₂(ℤ)` (`pslEquiv`).
29. *Self-adjointness of `T_p`.* Substitute `z = α_i^* w` (`α_i α_i^* = p` is scalar, `GL₂⁺(ℝ)` preserves the
    hyperbolic measure) and unfold `ℍ = ⋃ γ𝒟`: `∫_𝒟 (T_p f) ḡ = ∫_𝒟 f(w) Σ_{γ, i} (1_𝒟 ḡ)(α_i^* γ w)`. By the Hecke
    bijection the inner sum is `Σ_k Σ_{γ'} (1_𝒟 ḡ)(γ' α_k w)`, and off the null set of points with a translate on
    `∂𝒟` exactly one `γ'` puts `α_k w` into `𝒟` (`eq_of_smul_mem_fd`, `tsum_sum_astar`). Hence
    `∫_𝒟 (T_p f) ḡ = ∫_𝒟 f (T_p g)‾` for bounded measurable invariant `f, g` (`integral_heckeH_mul_conj`).
30. *Hecke eigenforms.* On the `L²` image of `S(λ)` the Hecke operators are symmetric and commute, so the joint
    eigenspaces span it (`iSup_jointEigenspace_eq_top`): Hecke forms span every cusp space, finitely many suffice
    (`span_heckeForms`, `exists_finite_heckeForms`). The pair entry is additive and homogeneous in the first slot,
    conjugate-homogeneous in the second, so seeing passes from any pair of eigenforms to a pair from any spanning
    sets (`exists_pair_seeing_of_span`): pairs of Hecke–Maass forms see every resonance (`exists_hecke_pair_seeing`),
    and the enumerated Hecke basis gives a complete receiver and a sharp receiver of Hecke forms
    (`exists_hecke_cavity_seeing_every_right_zero`, `exists_sharp_hecke_receiver`).
31. *Shimura's integral of a level-one cusp form.* `G(z) = g(4z) θ̄(z) y^{1/4}` obeys `G(γz) = \overline{j(γ,z)} G(z)` on
    `Γ₀(4)` because `4γz = γ'(4z)` with `γ' ∈ SL₂(ℤ)` (`kernel_smul`); `4gz` is an `SL₂(ℤ)`-translate of `(ez+β)/δ`,
    `eδ = 4`, so every translate decays faster than any power on `𝒟` (`kernel_hdec`). The fold against the regularised
    weight-½ Eisenstein series is holomorphic on `Re w > ¼` (`differentiableAt_fold`); for `Re w > 7/4` the theta
    unfolding `∫_0^1 g(4z)θ̄(z)dx = Σ_j ρ_W(j²)e^{−8πj²y}W_ν(8πj²y)` and the Mellin transform of `K_ν e^{−t}` give
    `rsFold = 2ρ(w) Mel_ν(w−¼) Σ_j ρ_W(j²)(8πj²)^{3/4−w}` (`fold_eq`), with `ρ(w) = (4w−3)(4w−2)ζ(4w−1)`.
32. *The diagonal of a Hecke eigenform.* The eigenvalues are real (`conj_eigenvalue`), the Hecke sequence satisfies
    `τ(p^{2k+2}) = τ(p^{k+1})² − τ(p^k)²` (`double`), hence `τ(n)² = Σ_{d∣n} τ((n/d)²)` (`sq_eq_zeta_mul`) and
    `Σ τ(n)² n^{−s} = ζ(s) Σ τ(m²) m^{−s}` (`lseries_sq_eq`). In `s = 2w − ½` the factor `ζ(2s)` of `ξ(2s)` in `E*`
    and the factor `ζ(4w−1)` of `ρ(w)` coincide, so `Λ_u(s)` and `ζ(s) · Sh_u(w)` agree up to Gamma factors for
    `Re s > 3` (`identity_of_re`), and by analytic continuation on `Re s > 0` (`diagonal_identity`). `E*` is even in
    `x`, so the mirror form has the same diagonal (`pairing_comp_mirror`) and covers `ρ(1) = 0`. At every zero `s₀`
    of `ζ` in `Re s > 0` every Hecke form has `Λ_u(s₀) = 0` (`pairing_self_eq_zero_of_zeta`), and for `ρ(1) ≠ 0`
    `Λ_u(s₀) ≠ 0 ⟺ ζ(s₀) ≠ 0 ∧ Sh_u(s₀/2 + ¼) ≠ 0` (`pairing_self_ne_zero_iff_of_rho`).

## 6. Questions the programme answers

**Q1. Which confined system has the worldline modes `½ + 2k` as its free part and primes as interactions at
times `log n`?** The explicit formula fixes it: free part the worldline (spectrum `½ + 2k`, correlator
`2πG_{1/2}`), interactions the prime atoms `Λ(n) n^{−½}` at `± log n`, and a rank-two growing mode for the pole;
together the Weil form. Its Hilbert-space realization with the Hecke clock exists iff RH (mechanism 5), and
none lives inside the horizon's own operator algebra.

**Q2. Which modular map sends confined correlators to the mirror-even response?** The Poincaré sum, read on
horocycles as Rankin–Selberg unfolding (mechanism 9). It is linear and position rigid (mechanism 10): it maps
seeds to residues, never frequencies to frequencies.

**Q3. Which conformal weight fixes the lowest tower at rate `¼`?** None. For every seed the response has no
seed-dependent pole anywhere: its only poles are the zeros of `ξ(2s)` and the equidistribution pole at `s = 1`
(mechanisms 10, 18). The kinematic tower of a single image — the bounce `B(w, ½)`, poles at `s = ½ − k`, the
worldline modes `½ + 2k` in the variable `2s − 1` — is invisible in the response of every seed
(`differentiableAt_responseTransform_worldline`): the image sum cancels it, by the pole of `ζ` at `k = 0` and by
the trivial zeros for `k ≥ 1`. Seed-dependent towers would need seed profiles that do not decay in the cusp.
In `ρ = 2s`, RH says `Re ρ = ½ = Δ` of the worldline; this is the fixed line of the functional equation (the KMS
midpoint of ASH), not the kinematics of a weight.

**Q4. Why does arithmeticity make the confined side unitary?** It does not by itself. Arithmeticity gives the
functional equation (the Born rule) and the Euler product (one clock per prime); a non-arithmetic Hecke group
already fails at a second place (`CountingHolography.hecke_count_fails`). Unitarity of the companion is the
count half of the count law, and over `ℤ` that is RH.

**B117 (modular confinement), decided form by form.**
- *Collective form* — every resonance is a singularity of the modular image of a unitary confined system
  defined without the zeros: **true** (Narain, mechanism 6; pseudo-Eisenstein seeds of BHR).
- *Kinematic form* — a seed, its weight or its spectrum places the resonances: **false** for every seed
  (position rigidity).
- *Frequency form* — real normal modes of a companion map one-to-one to the resonances: a Hilbert–Pólya
  realization; **equivalent to RH** (mechanism 5).

**Can unitarity of a confined seed enter as a sign on the black-hole side?** Only at full strength. For a real
seed a one-sided bound on the remainder `a_F(y) − c_F` at rate `y^α`, from above or from below, already forces
`Λ_F(s₀) = 0` at every zero with `Re s₀ > 1 − α` (mechanism 18): a sign at rate `α` is the rate `α`. A seed that
sees a resonance `ρ/2` has a remainder of both signs beyond every `C y^{1 − Re ρ/2 + ε}` (`not_oneSided_of_seen`);
at a critical zero this is the universal scale `y^{3/4}`.

**B109 (one cavity mode sees every zero).** *True for cavity functions.* One cavity function sees a countable set
of resonances iff every point is seen by a pair of its modes (`exists_cavity_seeing_iff`), and in the odd cavity
every resonance is seen by a single tent field (`exists_tent_seeing`): high in the cusp `E*` at a resonance is its
constant term `κ y^{1−s}` up to a bounded tail, and `κ ≠ 0`. So there is a continuous, modular, mirror-odd function
`g`, with `|g| ≤ C e^{−π Im z}` and zero mean on every closed horocycle, such that a horocycle rate `y^α` of `|g|²`
forces `Re ρ ≤ 2 − 2α` at every zero (`exists_odd_cavity_receiver`): rate `y^{½+δ}` is a zero-free strip and
rate `y^{3/4}` leaves no zero right of the line. The cavity receiver is complete; no L-value enters.
*True for pairs of Hecke–Maass forms.* At every resonance `ρ/2`, `Re ρ > 0`, two cuspidal Laplace eigenforms have a
nonzero pair entry (`exists_maass_pair_seeing`): the tent field that sees the resonance is a superposition of
eigenforms, and the pair entry is continuous on `L²` in each slot. Since `T_p` is self-adjoint, Hecke eigenforms
span each eigenspace, and the two eigenforms can be taken to be Hecke eigenforms (`exists_hecke_pair_seeing`).
*Not for one eigenform without a statement about ζ.* The diagonal entry of a Hecke eigenform is `ζ(s)` times
Shimura's integral (`diagonal_identity`), so a single Hecke eigenform never sees a resonance `ρ/2` for which `ρ/2`
is itself a zero (`pairing_half_eq_zero`). B109 for one Hecke eigenform therefore implies that no zero `ρ` with
`Re ρ > ½` has `ζ(ρ/2) = 0` (`zeta_half_ne_zero_of_hecke_seeing`), a property of the zeros that RH gives (there
are no right zeros) and nothing else is known to give. Exactly: `u` sees `ρ/2` iff `ζ(ρ/2) ≠ 0` and Shimura's
integral of `u` does not vanish at `w = (ρ + 1)/4` (`pairing_self_ne_zero_iff_of_rho`). Pairs are the
unconditional form of B109. For Maass cusp forms the pair entry is the
continued Rankin–Selberg series `Σ ρ_u(n) conj(ρ_v(n)) |n|^{−s}` (`pairing_eq_rankinSelberg`), so this is
pairwise noncancellation of Rankin–Selberg functions at `ρ/2`. Hence one cavity function of Maass cusp forms, or of
Hecke–Maass forms, sees every right resonance and its energy is a complete receiver
(`exists_maass_cavity_seeing_every_right_zero`, `exists_hecke_cavity_seeing_every_right_zero`).

**Krein-space holography for the mirror-even channel.** *At one resonance* the Hermitian part `𝒦_s` of the energy
pairing has infinite index of both signs on the odd cavity, at every resonance `ρ/2`, critical or not
(`krein_index_tents`): the tents diagonalize it and their Krein signs rotate with `Im s · log(j + 7/2)`. Its index
does not single out the off-line zeros. *On a reflection pair* `s = ρ/2`, `s* = (1 − ρ̄)/2` — the image of the
functional-equation pairing of the zeros, fixing exactly the damping line `Re s = ¼` — the reflection Krein form
`𝒦_ρ(F, G) = Λ_F(s) Λ̄_G(s*) + Λ_F(s*) Λ̄_G(s)` on tent energies has at most one negative square, none for a
critical zero and exactly one for an off-line zero (`tentReflectionKrein_index`), and

  **RH ⟺ every reflection Krein form of the cavity is positive semidefinite**
  (`riemannHypothesis_iff_tentReflectionKrein`).

This is the horizon form of the orientation index law of the Weil form (`ArithmeticOrientationGeometry.orientationIndex_law`):
one negative square per off-line zero seen. The negative square is the mismatch of the decay exponents
`1 + Re s ≠ 1 + Re s*` of the tent energies, i.e. of the two ringdown rates of the pair; positivity of all
reflection forms is RH, not an input from wave dynamics (on the zero side the Krein square decays at the universal
rate on every configuration, `ArithmeticScatteringHolography.physicalKrein_eq`).

**Milestones.** M1 (worldline ↦ Gamma lattice): the bounce `B(w,½)` and the worldline tower `½ + 2k` (mechanisms
2–3), invisible in every response (`differentiableAt_responseTransform_worldline`). M2 (a damped graph black
hole as the image of an oscillator bank): mechanism 4. M3 (a Narain confined seed carrying the arithmetic poles):
mechanism 6. M4 (a positive universal decay rate) and M5 (rate `¼`) are exact statements about the cavity:

  **a zero-free strip `Re z > 1 − δ` ⟺ all two-mode energies ring down at a common rate `y^α`, `α > ½`**
  (`zeroFreeStrip_iff_twoMode_rate`),

  **RH ⟺ every two-mode energy rings down at `y^{3/4−ε}` for every `ε > 0`** (`riemannHypothesis_iff_twoMode_rate`).

and for one cuspidal function `g` of Maass forms, or of Hecke–Maass forms: RH ⟺ `|g|²` rings down at `y^{3/4−ε}` for
every `ε`, and a zero-free strip ⟺ `|g|²` rings down at some `y^α`, `α > ½` (`exists_sharp_cavity_receiver`,
`exists_sharp_hecke_receiver`).

They are the zero-free strip and RH themselves: the programme decides what they are, not whether they hold.

## 7. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Seeds form a `*`-algebra containing the cusp forms | `IsSeed.mul`, `IsSeed.star`, `IsSeed.normSq`, `isSeed_of_mem_cuspSpace` | unconditional |
| Continuation and functional equation of every seed | `differentiableOn_seedTransform`, `seedTransform_one_sub` | unconditional |
| Unfolding | `seedTransform_eq_mellin`, `two_mul_strip_eq`, `strip_eq_mellin` | unconditional |
| Position rigidity | `responseContinuation_eq_mellin`, `differentiableAt_responseContinuation` | unconditional |
| Every-seed receiver | `seedTransform_eq_zero_of_rate`, `seedTransform_half_eq_zero_of_rate`, `not_rate_of_seen` | unconditional |
| Blind sets are nowhere dense | `polarization`, `continuous_quad`, `interior_quad_zero_eq_empty` | unconditional |
| B109 reduced to pairs | `exists_cavity_seeing_iff`, `cavity_sees_every_right_zero_iff`, `cuspFunction_sees_every_right_zero_iff` | unconditional |
| Complete cavity receiver | `re_le_of_cavity_rate` | unconditional |
| Cavity functions are cuspidal | `response_cavity_cuspFamily_eq_zero`, `response_cavity_oddFamily` | unconditional |
| Odd cusp fields; odd pairings unfold to the strip | `oddCuspField_smul`, `oddCuspField_mirror`, `continuous_oddCuspField`, `setIntegral_fd_eq_strip_of_high`, `pairing_oddCuspField` | unconditional |
| `E*` at a resonance; phase law of the tent energies | `completedEisenstein_eq_of_resonance`, `horocycleProfile_eq_of_resonance`, `resonance_data`, `exists_tent_phase` | unconditional |
| Every resonance is seen by a tent | `exists_tent_seeing` | unconditional |
| B109 for cavity functions; complete cuspidal receiver | `dense_odd_cavity_seeing`, `exists_odd_cavity_seeing_every_right_zero`, `exists_odd_cavity_receiver` | unconditional |
| Krein inertia of the cavity: infinite index of both signs at every resonance | `kreinGram_eq_diagonal`, `tent_krein_sign`, `krein_index_tents` | unconditional |
| Size of the tent energies `|d_j(s)| ≍ (j + 3)^{−1−Re s}` | `exists_tent_phase`, `exists_tentEnergy_ge`, `exists_tentEnergy_le` | unconditional |
| Pairwise visibility of Maass cusp forms | `exists_inner_basis_ne_zero`, `exists_maass_pair_seeing` | unconditional |
| B109 for Maass cusp forms; complete receiver of Maass forms | `exists_maass_cavity_seeing_every_right_zero` | unconditional |
| Reflection Krein index law | `negIndex_reflectionMatrix_le_one`, `one_le_negIndex_reflectionMatrix_two`, `exists_tent_independent`, `tentReflectionKrein_index` | unconditional |
| RH ⟺ positivity of the reflection Krein forms | `riemannHypothesis_iff_tentReflectionKrein` | equivalence |
| The ringdown rate of a seed is its zero-free region | `exists_polarTransform_decay`, `norm_response_sub_le_of_zeroFree`, `response_rate_of_zeroFree`, `response_rate_of_riemannHypothesis` | unconditional implications |
| Pair energies decay like `e^{−π|t|}`; two-mode energies ring down at the zero-free rate | `exists_pairPolar_decay`, `twoMode_rate_of_zeroFree` | unconditional implication |
| Zagier's theorem for the cavity (M5); zero-free strip ⟺ universal two-mode rate (M4) | `riemannHypothesis_iff_twoMode_rate`, `zeroFreeStrip_iff_twoMode_rate` | equivalences |
| One sharp receiver: RH ⟺ rate `y^{3/4−ε}` of one cuspidal energy; zero-free strip ⟺ rate `y^α`, `α > ½` | `cavity_polar_right`, `sharp_receiver_of_pairs`, `exists_sharp_cavity_receiver`, `exists_sharp_hecke_receiver` | equivalences |
| Hecke cosets of determinant `p`; the Hecke bijection | `leftQuot_mul`, `leftIndex_mul`, `Astar_mul_rightQuot`, `rightIndex_Astar_mul`, `heckeEquiv_spec`, `pslEquiv` | unconditional |
| `T_p` is self-adjoint for the Petersson product | `tsum_sum_astar`, `integral_heckeH_mul_conj` | unconditional |
| Hecke eigenforms span every cusp space | `iSup_jointEigenspace_eq_top`, `span_heckeForms`, `exists_finite_heckeForms` | unconditional |
| Pairwise visibility of Hecke–Maass forms; B109 for Hecke forms | `exists_pair_seeing_of_span`, `exists_hecke_pair_seeing`, `exists_hecke_cavity_seeing_every_right_zero` | unconditional |
| Shimura's continuation for level-one cusp forms | `Shimura.kernel_smul`, `Shimura.kernel_hdec`, `Shimura.differentiableAt_fold`, `Shimura.fold_eq` | unconditional |
| The diagonal of a Hecke eigenform is `ζ(s)` times Shimura's integral | `HalvingPairs.conj_eigenvalue`, `HalvingPairs.sq_eq_zeta_mul`, `HalvingPairs.lseries_sq_eq`, `HalvingPairs.diagonal_identity` | unconditional |
| One Hecke eigenform is blind to halving pairs; B109 for one eigenform excludes them | `HalvingPairs.pairing_half_eq_zero`, `HalvingPairs.zeta_half_ne_zero_of_hecke_seeing`, `HalvingPairs.pairing_self_ne_zero_iff_of_rho` | unconditional |
| Pair entries are Rankin–Selberg series | `hasSum_response_mul_conj`, `hasSum_mellin_pairResponse`, `pairing_eq_rankinSelberg` | unconditional |
| One-sided bounds on the dual side are two-sided | `seedTransform_eq_zero_of_oneSided`, `seedTransform_eq_zero_of_oneSided_lower`, `not_oneSided_of_seen` | unconditional |
| Analytic structure of the response | `differentiableOn_numeratorTransform`, `polarNumerator_half`, `eisensteinNumerator_zero`, `analyticAt_lowerTransform`, `integral_lower_eq` | unconditional |
| The worldline tower is invisible | `differentiableAt_responseTransform_of_real`, `differentiableAt_responseTransform_worldline` | unconditional |
| Momentum universality | `divisorPowerSum_ne_zero`, `meromorphicOrderAt_rademacher`, `rademacher_image_sum`, `modeCoefficient_ne_zero_of_resonance` | unconditional |
| Ringdown = width; rate `¼` = RH | `BlackHoleRingdown.zeroFreeStrip_iff_pulse_ringdown`, `riemannHypothesis_iff_pulse_ringdown` | equivalences (BHR) |
| Born-rule realization with the Hecke clock = RH | `CountingHolography.riemannHypothesis_iff_exists_standardForm_bornRule` | equivalence (CTH) |
| Narain seed sees every resonance | `ModularBootstrap.narainMellinMean_full_order` | unconditional (ModularBootstrap) |

## 8. Tools

- **Arithmetic S-duality for Poincaré sums of seeds** (developed): the seed class, the completed transform with
  its functional equation and continuation, unfolding, position rigidity, the every-seed receiver; the numerator
  and polar transforms (regular at `s = ½`, residue `c_F` at `s = 1`) and the one-sided (Landau) receiver.
- **Rankin–Selberg noncancellation for one cavity mode** (developed): the pair form and its bound, polarization,
  Baire genericity of seeing, the converse by truncation, cuspidal cavity functions, pair entries as
  Rankin–Selberg series; odd cusp fields, the strip unfolding of their pairings, the constant term of `E*` at a
  resonance, the phase law and size of the tent energies, B109 for cavity functions, transfer of seeing to pairs of
  eigenforms through the odd spectral expansion, B109 for Maass cusp forms; the Hecke cosets of determinant `p`,
  self-adjointness of `T_p` by unfolding, Hecke eigenbases of the cusp spaces, B109 for Hecke–Maass forms;
  Shimura's weight-½ integral of a level-one cusp form with its continuation to `Re w > ¼`, and the factorization
  of the diagonal entry of a Hecke eigenform as `ζ(s)` times that integral.
- **Krein-space holography for the mirror-even channel** (developed): the resonance Krein form, its
  diagonalization by tents, the Krein sign law, infinite index of both signs at every resonance; the reflection
  Krein form of a resonance pair, its index law (one negative square exactly off the line) and RH as its
  positivity; on the zero side the Krein square `e^{−τ/2} W_ℤ(f, f)` (`ArithmeticScatteringHolography.physicalKrein_eq`)
  and the orientation index law (`ArithmeticOrientationGeometry.orientationIndex_law`).
- **Arithmetic S-duality, the rate side** (developed): the polar transform of a seed, its oddness and growth,
  Phragmén–Lindelöf from one line, the Mellin regular part and the contour shift for every seed; pair and two-mode
  energies; Zagier's theorem for the cavity; one sharp cuspidal receiver, for any sequence of cusp forms that sees
  in pairs, in particular for Hecke–Maass forms.
- **Rademacher expansions with arithmetic poles** (developed): the echo train of the constant channel (BHR) and,
  at momentum `n`, the Ramanujan image sum `σ_{1−w}(n)/ζ(w)` (`RHTower.LSeries_d4BMRamanujanNaturalCoefficient_eq_div_riemannZeta`)
  with its full pole order at every zero; nonvanishing of complex divisor sums off `Re w = 0`.

## 9. Traps

| Trap | Truth |
|---|---|
| BTZ-type kinematics fixes the arithmetic damping | For every seed the only resonances in the strip are the zeros of `ξ(2s)` |
| A unitary confined seed forces real resonance frequencies | Positivity of a seed controls residues, never positions |
| The modular map sends normal modes to resonances | It sends seeds to residues; the seed's spectrum is invisible to the positions |
| `Δ = ½` of the worldline explains the critical line | The line is the fixed line of the functional equation; the worldline weight is a second appearance of it |
| A Hilbert space of the confined side can be found inside the horizon algebra | Internal, vacuum-fixing and half-sided realizations are excluded (CTH) |
| One cavity mode must be an eigenform | The natural object is a cavity function; seeing is generic among them once pairs see |
| Some momentum channel might miss a resonance | Every channel has the full order at every zero; the channels differ only in the residues `σ_{1−ρ}(n)` |
| B109 needs a nonvanishing theorem for L-values | Not for pairs: a tent field sees every resonance through the constant term `κ y^{1−s}`, and seeing passes to pairs of eigenforms by `L²` continuity and to pairs of Hecke eigenforms by spanning; only the diagonal (one eigenform) needs more |
| One Hecke eigenform is a universal receiver if the L-values cooperate | Its diagonal carries the factor `ζ(s)`: it is blind at every `ρ/2` that is a zero, so one-eigenform B109 needs the absence of halving pairs |
| Laplace eigenforms might see a resonance that Hecke eigenforms miss | Hecke eigenforms span every cusp space (`T_p` is self-adjoint), and the pair entry is sesquilinear on cusp forms |
| The Krein form of one resonance detects off-line resonances | At every resonance, on the line or off, it has infinite index of both signs; the line is seen by the reflection pair `s ↔ ½ − s̄` |
| Positivity of the reflection Krein forms can come from the horizon | It is equivalent to RH; the negative square is the mismatch of two ringdown rates |
| A receiver needs a sign | Rates force residues to vanish with no positivity anywhere |
| Positivity on the dual side is a weaker input than a rate | A one-sided bound at rate `α` is equivalent in strength to the two-sided rate `α` (Landau) |

## 10. Where it sits

| Neighbour | Interface |
|---|---|
| BlackHoleRingdown | Eisenstein function and its completion, unfolding, cusp forms, Whittaker coefficients, echo train, receivers for cusp energies |
| ArithmeticScatteringHolography | graph black holes and fakes, Krein law, KMS midpoint, one clock per prime |
| ModularBootstrap (inside ASH) | the Narain confined seed and its pole detection |
| CountingHolography | Born rule + count, boundary algebra, standard-form trichotomy, Farey reading, second place |
| SurfaceOfSpecZ | the worldline: `ℍ³` Green function, `Δ = ½, 3/2` |
| ArithmeticOrientationGeometry | the Weil form along an orbit; negative index = right zeros seen |
| RHTower | `ξ`, the completed and numerator Eisenstein models, Landau's theorem with exponential bounds, Ramanujan Dirichlet series |

Imports: BlackHoleRingdown (receiver of cusp energies, Whittaker coefficients, the mirror and odd cusp profiles of
`TheCuspFormsExist`, the bounded Whittaker tail, the cusp spaces and Hecke operators of `HeckeCusp`), RHTower
(`FiniteOffLineLandau`, the Ramanujan and line-eigen modules of `ThetaCusp`, the row sum, `ZetaRealStrip`, the Hecke
matrices of `Gamma0MaassHeckeOperator`, the weight-½ theory of `HalfWeight*`: `θ`, the regularised Eisenstein series of
level `4M` and its fold `rsFold`), HTGeometry (strip unfolding, `HermitianInertia`, the fundamental domain as a
measurable fundamental domain of `PSL₂(ℤ)` and its finite volume). Used by:
MainTheorems.

AHMH is the holographic reading of these programmes. It shows that the physical dictionary is a residue
dictionary: every map of the triangle preserves the arithmetic positions, and what a physical system can
contribute is visibility. Universal damping therefore cannot come from the modular map, the worldline or any
confined seed; it is a property of the positions, which is RH.

## 11. Success criteria, and what a contribution must be

**Criteria from the review.** Define the confined side from the archimedean place and the primes alone: the Weil
form (Q1). Avoid the excluded realizations: CTH. Fail on graph black holes with `t² > 4q` through the companion:
the graph companion exists iff damped. Reproduce universal decay `e^{−t/4}`, the horocycle rate `y^{3/4−ε}` and the
Narain average: BHR, CTH, ModularBootstrap. The every-seed receiver gives the direction rate ⇒ width for all
these readings at once, two-sided or one-sided; the direction RH ⇒ `y^{3/4−ε}` is proved for cusp energies and
pseudo-Eisenstein seeds (BHR, CTH) and here for every seed whose completed transform decays like `e^{−π|t|}`, in
particular every two-mode cavity energy.

**A contribution must** be a theorem about a map of the triangle or about one of its corners that holds for every
seed or states exactly which seeds it needs; say whether it moves positions or residues; and either reach a
sub-RH statement or name the exact place where it becomes RH.

## 12. Open research topics

1. **B109 for one eigenform.** Decided up to two statements that exist only if RH fails. The obstruction is proved:
   one Hecke eigenform is blind to halving pairs (`pairing_half_eq_zero`), so one-eigenform B109 implies that no
   right zero `ρ` has `ζ(ρ/2) = 0`. What remains open is the converse: for every right zero `ρ` with `ζ(ρ/2) ≠ 0`,
   some Hecke eigenform whose Shimura integral does not vanish at `w = (ρ + 1)/4`, i.e. nonvanishing of
   `L(s, sym² u)` at `s = ρ/2` somewhere in the Hecke family; and the absence of halving pairs among the zeros.
2. **The rate itself.** A universal damping rate (M4, the zero-free strip) or the rate `¼` (M5, RH) for the energy of
   the sharp receiver `g`.
