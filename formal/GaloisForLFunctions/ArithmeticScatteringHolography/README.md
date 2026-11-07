# Arithmetic Scattering Holography (ASH)

Namespace `GaloisForLFunctions.ArithmeticScatteringHolography`; umbrella
`ArithmeticScatteringHolography.lean`; 33 modules.

## 1. Motivation

On the massless topological AdS₄ black hole with horizon `PSL₂(ℤ)\ℍ`, the zeros of `ζ` are resonances of the wave
equation: one damped mode per zero, at rate `D + (1-β)/2`. So RH reads *one universal relaxation rate*. That is a
theorem about an actual solution of an actual wave equation (`BlackHoleRingdown`), and it restates RH. The geometry
is locally pure AdS, so no gravitational dynamics is involved: this is scattering on an arithmetic quotient.

ASH asks whether the physical reading has content. Is there a *law of wave dynamics* (flux, unitarity, causality,
Hecke symmetry) that forces the universal rate, or is the rate the same statement in other words? The question can
be decided, because over a curve the system is exact and RH is known. There the horizon is a graph, the wave equation
is a recursion, and either a derivation exists or a fake system with the same dynamics exists.

**The answer.** The fake exists. Over every `q` there are tree lattices with the local geometry of the
function-field black hole, with flux, unitarity, causality and a commuting positive family of Hecke operators, and
with a resonance off the universal circle. So universal damping is not a law of wave dynamics. What the
obstruction leaves behind is a sharper object: the **Krein square**, which decays at exactly the universal rate on
every such system, true or fake, and is a dissipated energy exactly under RH.

The fakes carry a Hecke algebra at places of all degrees, with positivity, so that does not exclude them either. What excludes them is a **count law**: the
parallelogram law for the number of points of the probes `y - x π`. Its first instance is the conservation of channels, `#G + #G' = 2(q+1)`, which holds on every black hole. The
law at all probes is equivalent to universal damping. On a true curve the law is a theorem: the height on the twisted curve over `𝔽_q(T)` obeys the exact parallelogram law, and this reproves Hasse's theorem
from the conservation of channels at all probes, independently of Stepanov.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Black hole of `(q, G, D)` | `Channels`, `Vertex`, `waveOp`, `mass` | edge-indexed quotient of the `(q+1)`-regular tree: core, dead ends `D`, necks and pins, caps, rays labelled by the abelian group `G` |
| Trace | `Channels.trace`, `traceR` | `t = q + 1 - #G` |
| Wave equation | `IsWave` | `u(τ+1) + q u(τ-1) = A u(τ)` |
| Regular solution | `regSeq`, `Channels.regular` | the polynomial eigenfunction from the core |
| Jost function | `jost` | `j(X,Y) = (Y²-1)(X³-tX+Y)`, `λ = X+Y`, `XY = q` |
| Outgoing state | `IsOutgoing` | eigenfunction `c_P Y^k` on rays: a resonant state |
| Scattering | `radialScattering`, `zeroMeanField` | `(Y/X)σ` on zero-mean amplitudes, rank one onto the core |
| Pulse, echo train | `Channels.pulse`, `reflected`, `echo` | the exact field of one pulse, and what comes back |
| Ringdown signal | `lucas`, `ringSignal` | the echo train through the ground-mode probe |
| Krein square | `kreinSquare`, `normalizedKrein` | `𝒬(x,y) = y² - txy + qx²` on the state `(R_n, R_{n+1})` |
| Probe form | `probeNorm` | the degree form of a two-term causal probe |
| Hecke operators | `heckeOp`, `transl` | `T_Q = τ_Q⁻¹ A τ_Q`, one for each class `Q ∈ G` |
| Hecke at degree two | `heckeTwo`, `DeadLabel`, `deadTerm` | one operator for each `Q₀ ∈ G`, `w ∈ G'`, with `G'` the group of the twist, `#G + #G' = 2(q+1)` |
| Hecke polynomials | `chebOp`, `heckeDeg` | the propagator `P_d(A)`, with `P_d(X+Y) = X^d + Y^d`, and `P_d(T_Q)` |
| Shadow on the second group | `thetaTerm`, `thetaDiff` | the even function `g` on `G'`: `f` on dead ends, `((q+1) f(pin) - f(cap))/q` at zero |
| Translation of the second group | `thetaOp` | `Λ_w`: the second difference of the shadow |
| Cusp forms | `thetaField` | `ψ + ψ⁻¹` on dead ends, `1` on the pin, `1 - q` on the cap: compact support, eigenvalue `0` |
| Hecke family at even degree | `heckeFull` | `P_{2m}(T_Q) + (-q)^m Λ_w`, with `heckeTwo` at `m = 1` |
| Hecke at every class | `heckeClass` | `S(1,Q) = T_Q`, `S(2,Q) = T_{Q,0}`, `S(d+2,Q) = A S(d+1,Q) - q S(d,Q)` |
| Twisted curve | `twistCurve`, `xPair`, `height` | `h(T) Y² = h(X)` over `F(T)`; the height is the degree of `X` |
| Generic and Frobenius points | `genericPoint`, `frobeniusPoint` | `(T, 1)` and `(T^q, h^{(q-1)/2})` |
| Three biquadratic forms | `formA`, `formB`, `formC` | the quadratic with roots `X(P+Q)`, `X(P-Q)` |
| Ring of a black hole | `probeMatrix`, `probeLattice`, `probeCount` | `ℤ[π] = ℤ[x]/(x² - tx + q)`, the ideal `(y - xπ)`, and its index |
| Count law | `CountLaw` | the parallelogram law for a function `K` on probes |
| Tower of groups | `powA`, `powB`, `powV` | `π^n = a_n π + b_n` and the group `ℤ[π]/(1 - π^n)` |
| Lax–Phillips semigroup | `lpMatrix`, `shiftPair` | the companion `Z` of the denominator, on the state `(R_n, R_{n+1})` |
| Metric of the model space | `kreinHerm` | the Hermitian Krein form `q\|x\|² - t Re(x̄y) + \|y\|²` |
| Throat | `throatOp`, `throatMass`, `throatPoly` | a one-cusp tree lattice with two free edge indices `a, b` |
| Throat of every length | `chainOp`, `chainMass`, `thPoly`, `thDen` | a path with one cusp and free indices `c_j`, with its denominator |
| KMS correlator | `kmsCorrelator` | `G(z) = F(1 + iz)` on the strip `0 ≤ Re s ≤ 1` |
| Fake horizon | `fakeKernel`, `fakeXi` | the transform of `e^{-x²}(e cosh b + cosh 2x) > 0` |
| Integer probes over `ℤ` | `atomGram`, `integerProbe` | the Gram form of `B(· - log n)` on integer vectors |
| Damping rate | `dampingRate` | the mode at `a = X²` decays by `q^{-rate}` per tick; `rate = (1 - Re ρ)/2` |
| Curve datum of a black hole | `datumOfRoots` | the rank-two datum, geometric or not |
| Base change | `towerTrace` | `V_d = α^d + β^d`, the trace over `𝔽_{q^d}` |
| Packet on the modular horizon | `BlackHoleRingdown.wavePacket` | exact Eisenstein wave |
| Tree wave | `treeWave` | the packet at tree time `n`: `p^{n/2} 𝓕(τ + n log p)` |
| Physical Krein square over `ℤ` | `physicalKrein`, `kreinFlux` | `e^{-τ/2} W_Z(f_{τ/2}, f_{τ/2})` |
| Horocycle mean | `horoMean`, `Horofunction.sphere` | the constant term, and the horospheres of the tree |

The graph is a theorem of Takahashi when `G = E(𝔽_q)`, with vertices the rank-two bundles up to `O(∞)`. It makes sense for
every abelian `G` with `#{±P} + #D = q + 1`. Local regularity (`Channels.waveOp_one`) and the balance of the measure
make it a tree lattice quotient by Bass–Kulkarni [C].

## 3. Language

- **Ringdown, overtone, excitation factor**: the expansion of the reflected signal in damped modes.
- **Universal damping**: every non-ground mode at rate `¼`, that is `q^{-1/4}` per tick. Off the universal circle the
  oscillator is **overdamped**; on it, **underdamped**; at `t² = 4q`, **critically damped**.
- **Minus and plus branch**: the two time factors `X^τ`, `Y^τ` of one eigenfunction.
- **Open and trapped channels**: cusps, and the dead ends with the two-torsion points, the points of the twist.
- **Flux**: the boundary term of Green's identity on a truncated region (Maass–Selberg).
- **Krein square, Krein flux**: the form above and its loss per tick.
- **Probe**: a compactly supported causal input, a polynomial in `w = X⁻²`.
- **Bode integral**: the mean of `log|P|` on the universal circle, the mean of `log|ξ|` on the critical line.
- **Damping deficit**: `¼ - rate`.
- **Clock of a place**: the time unit in which the wave equation of a tree runs: `log p` at `p`.
- **Propagator**: `P_d(A)`, the solution at time `d` with the initial data of Chebyshev.
- **Shadow**: the part of a function that only the second group sees.
- **Count of a probe**: the number of points of `ℤ[π]/(y - xπ)`; **count law**: the parallelogram law for it.
- **Height**: the degree of the `X`-coordinate of a point of the twisted curve.
- **Krein signature**: the value `H(1, z) = 2 (Im z)²` of the metric on a mode; **neutral**: zero signature.
- **KMS strip**: `0 ≤ Re s ≤ 1` with reflection `s ↦ 1 - s`; **midpoint**: the critical line.

## 4. Mechanisms

**Exact solvability.**
1. The regular solution is polynomial in `λ` at every vertex (`waveOp_regular`), and its value on a ray decomposes in
   the Jost function (`regSeq_jost`). A nonzero outgoing eigenfunction exists exactly at a zero of `j`
   (`exists_outgoing_iff`): the ground states, or `X⁴ - tX² + q = 0`.
2. Zero-mean amplitudes never reach the core: `S = (Y/X)σ` there, with no resonance (`zeroMeanField_eigen`). The scattering
   matrix is `(Y/X)σ` plus rank one.
3. In the causal variable `S(w) = qw + q(q-1)h w²(1+qw)/((1-q²w)(1-tw+qw²))` (`scattering_eq_causal`).
4. A pulse has a closed-form field on the whole graph (`pulse_isWave`). Only the core equation uses the recurrence of the
   denominator; everything else is d'Alembert. The ringdown has no remainder (`coreSeq_eq_modes`), and the probe
   `1 - q²w` leaves one damped oscillator (`ringSignal_add_two`).

**Flux and energy.**
5. Green's identity has only the boundary term on the rays (`truncSum_greenDensity`).
6. A nonreal resonance is damped (`normSq_lt_of_outgoing`), its mass is a geometric sum (`mass_law`), and its core mass is
   the amplitude over the distance to the unitary circle (`core_mass_law`). Two resonant states pair as a Szegő
   kernel (`gram_law`).
7. Any two waves have a leapfrog energy changing only by flux (`energy_balance`).

**Hecke.**
8. `T_Q(P,k+1) = q(P+Q,k) + (P-Q,k+2)`. These commute with each other and with `A` for every `(q,G,D)`
   (`heckeOp_comm`, `heckeOp_comm_waveOp`). They are conjugates of `A` by a measure-preserving bijection
   (`heckeOp_eq_conj`), positive, with constants as eigenvector (`Channels.heckeOp_nonneg`, `Channels.heckeOp_one`).
9. On the core sector `T_Q = A` (`heckeOp_balanced`), so every resonance has `T_Q`-eigenvalue `λ`
   (`IsOutgoing.hecke_eigen`). On a character `T_Q` has eigenvalue `χ(-Q)X + χ(Q)Y` (`chi_hecke_eigen`), and that sector has no
   resonance.
10. **Rigidity.** Any linear operator commuting with `A` and acting in the cusps as a shift of depth by `d` acts on every resonant state by
    the scalar `X^d + Y^d` (`hecke_rigidity`). Such operators exist at every degree on every black hole (`chebOp`,
    `chebOp_comm_waveOp`, `chebOp_comm_heckeOp`, `chebOp_ray`).
11. **Degree two.** For odd groups `G`, `G'` with `#G + #G' = 2(q+1)`, the dead ends are the classes `±Q` of `G'`, and a place of degree
    two translates them by `±w` (`heckeTwo`). The operator has `q²+1` edges, nonnegative coefficients, and commutes with `A`, with
    `T_Q` and with the other places of degree two (`Channels.heckeTwo_one`, `Channels.heckeTwo_nonneg`, `Channels.heckeTwo_comm_waveOp`,
    `Channels.heckeTwo_comm_heckeOp`, `Channels.heckeTwo_comm`). It acts on a resonance by `X²+Y²` (`Channels.heckeTwo_resonance`).
12. **The propagator is positive.** The wave on a black hole is read from its value at the core: d'Alembert plus an echo on the rays (`chebOp_ray_succ`, `echoPart_succ`), and
    geometric sums over the core on the necks and dead ends (`gap_formula`, `deadTerm_odd`, `deadTerm_even`). The core sequence is solved by
    `1/((1 - q² z)(1 - t z + q z²))` (`even_closed`, `odd_closed`), whose pole at the constant function dominates for every `|t| ≤ q` (`propR_growth`). So for odd groups and `q ≥ 7`,
    every entry of `P_d(A)` is nonnegative for `d ≥ 3` (`chebOp_nonneg`). At `d = 2` the dead ends have the entry `1 - q`, which `heckeTwo` corrects.
13. **The cuspidal sector.** `A Λ_w = Λ_w A = 0` and the same for `T_Q` (`waveOp_thetaOp`, `thetaOp_waveOp`, `heckeOp_thetaOp`), and `Λ_w` acts on the shadow by a second difference
    (`thetaTerm_thetaOp`). So `T_{2Q,w} = P₂(T_Q) - q Λ_w` (`heckeTwo_eq`). On `θ_ψ`, `A` and `T_Q` act by `0` and `T_{Q₀,w}` by `-q(ψ(w)+ψ(-w))` (`heckeTwo_thetaField`), and these
    eigenvalues separate the cusp forms (`heckeTwo_separates`).
14. **The full family.** `P_{2m}(T_Q) + (-q)^m Λ_w` commutes with `A` and with itself (`heckeFull_comm_waveOp`, `heckeFull_comm`), has `q^{2m}+1` edges (`heckeFull_one`), is symmetric on
    compactly supported functions (`heckeFull_symmetric`), has the arithmetic eigenvalue on cusp forms (`heckeFull_thetaField`), and has nonnegative coefficients for `w ≠ 0`, `q ≥ 7`
    (`heckeFull_nonneg`). All of `heckeDeg`, `heckeTwo`, `Λ_w` are symmetric (`heckeDeg_symmetric`, `heckeTwo_symmetric`, `truncSum_thetaOp_green`).
15. **Every class.** `S(d, Q)` has class `Q` at degree `d`, for every `Q`. It is a polynomial in `A`, `T_Q` and `T_{Q,0}`, so the family commutes (`heckeClass_comm`); it has the Hecke shape in the cusps and `q^d + 1` edges (`heckeClass_ray`,
    `heckeClass_one`). Off the rays it is the propagator of the function with translated cusps (`heckeClass_off_ray`), so it is positive for `d ≥ 3` (`heckeClass_nonneg`), also with the correction `(-q)^m Λ_w`
    (`heckeClass_add_theta_nonneg`).
16. Over `ℤ`: `T_p 𝓕(τ) = 𝓕(τ + log p) + 𝓕(τ - log p)` on Eisenstein packets (`heckeOp_wavePacket`), and the rescaled
    packet solves the wave equation of the tree at `p` for every `p` (`treeWave_isWave`).

**Krein.**
17. `𝒬(y, ty - qx) = q 𝒬(x,y)` for every `t` (`kreinSquare_step`). `𝒬` is the Turán determinant of three echoes
    (`kreinSquare_eq_turan`). The Wronskian is multiplied by `q` (`wronskian_step`).
18. `𝒬(x,y) = deg(y - xF)`, half the Castelnuovo–Severi defect of the graph class
    (`kreinSquare_eq_endDeg`, `krein_eq_half_defect`). A two-term probe multiplies `𝒬` by the degree form
    (`kreinSquare_probe`).
19. A pulse has `𝒬 = q^{n+2} h'` with `h' > 0` (`kreinSquare_ringSignal`): positive on every black hole. A probe can make it
    negative exactly on a fake (`probe_krein_nonneg_iff`).
20. Over `ℤ`, translation is an isometry of the Weil form, so `𝒬_f(τ) = e^{-τ/2} W_Z(f,f)` on every tempered configuration
    (`physicalKrein_eq`). At every genus the form is the Toeplitz form of the traces (`curveKrein_step`).

**Counts.**
21. `𝒬(x,y)` is the norm of the probe, and `ℤ[π]/(y - xπ)` has `|𝒬(x,y)|` elements on every black hole (`det_probeMatrix`, `card_quotient_probeLattice`). The tower of a fake is a tower of
    groups of order `q^n + 1 - V_n` (`card_quotient_tower`).
22. A function with the parallelogram law and `K(1) = 1`, `K(π) = q`, `K(1 - π) = q + 1 - t` is `𝒬` (`CountLaw.eq_kreinSquare`), so such a `K ≥ 0` exists exactly under universal damping
    (`exists_countLaw_iff`, `Channels.universal_iff_countLaw`). The counts of the ring obey the first instance always (`first_conservation`), and the law exactly under universal damping
    (`probeCount_law_iff`). A fake with three cusps breaks it at the second probe (`fake_violates_second_probe`).

23. **The law holds on a true curve.** `X(P+Q)` and `X(P-Q)` are the roots of a quadratic whose coefficients are biquadratic forms in `X(P)`, `X(Q)` (`crossRelations`). These forms have no common zero, since a common zero would be a double
    root of the cubic (`forms_no_common_zero`), so they generate the unit ideal and lose no degree at infinity (`forms_bezout`, `forms_top`). With Gauss for the product of two linear forms (`pair_bezout`, `pair_top`), this gives the exact law
    `ht(P+Q) + ht(P-Q) = 2 ht(P) + 2 ht(Q)` (`height_parallelogram`). The function `K(x,y) = ht(y P₀ - x P₁)` has `K(0,1) = 1`, `K(1,0) = q`, and `X(P₀ - P₁) = N/(T^q - T)²` loses `1 - χ(h(c))` powers of `T - c` at each rational `c`
    (`xCoord_sub`, `reduced_coprime`), so `K(1,1) = #E(𝔽_q)` (`height_sub_eq`, `elliptic_has_countLaw`). Then `hasse_of_countLaw` is Hasse's theorem, by Manin's argument.

**The strip and the reflection.**
24. The functional equation is a KMS condition at `β = 1`, and the critical line is the midpoint of the strip (`kms_condition`, `kms_reflection`, `kms_midpoint`). A positive kernel gives KMS
    positivity (`kernel_positive`).
25. A throat has flux for all edge indices (`throat_green`), and its modes multiply to `(b-1)q` (`throat_resonance`, `throat_partner_law`), so the functional equation is the condition `b = 2`
    (`throat_functional_equation_iff`). In every length the denominator is monic with constant term `q^{m+2}(1 - c₀)` and the root `q²` (`thDen_monic_natDegree`, `thDen_eval_zero`, `thDen_eval_ground`), each root is a resonance (`chain_resonance`), and
    the functional equation is impossible from genus two on (`chain_no_functional_equation`): a path quotient has it only at genus at most one.

**The semigroup and the phase.**
26. The Hankel operator of the echo train has rank two (`hankel_det_eq_zero`, `recurrence_shift`), and its compression is the semigroup `Z` with `det Z = q` and spectrum the modes (`lpMatrix_det`,
    `lpMatrix_charpoly`, `lpMatrix_mode`). `Z` multiplies the metric of the model space by `q` for every `t` (`kreinHerm_step`, `kreinHerm_semigroup`); the metric is positive exactly under universal
    damping (`kreinHerm_nonneg_iff`), and a mode has signature `2 (Im z)²` (`kreinHerm_mode`). Two resonant states pair as a Szegő kernel (`gram_law`).
27. On a disc free of zeros of the causal symbol, log-modulus and phase determine each other (`kramers_kronig`, `causal_symbol_kramers_kronig`). The Bode integral is the term at frequency zero on the
    universal circle.

**Horocycles.**
28. The horospheres of a tree satisfy the wave equation with depth as time (`horosphere_isWave`). The mean over a closed
    horocycle obeys `H[T_p F](y) = p^{-½} H[F](py) + p^{½} H[F](y/p)` (`horoMean_heckeOp`).

## 5. Questions the programme answers

**Can universal damping on the function-field black hole be derived from wave dynamics, without Weil?** No
(`universal_damping_not_forced_one_cusp`, `_three_cusps`, `_many_cusps`). For every `q ≥ 5`, there are tree lattices with flux, unitarity, causality, commuting positive Hecke operators and
resonances off the circle. For `q ≥ 8` they carry commuting positive operators at all degrees, with the arithmetic eigenvalues on their cusp forms
(`universal_damping_not_forced_with_degree_two`, `universal_damping_not_forced_at_every_degree`, `universal_damping_not_forced_by_the_full_algebra`, `universal_damping_not_forced_at_every_class`). The physical reading is a
reformulation, unless new input is brought.

**Is there a law on the graph that excludes the fakes?** Yes: the count law (`Channels.universal_iff_countLaw`). It uses only `q` and the number of cusps, and its first instance is the
local count that defines the graph. A fake has counts, positive at every level of its tower, and they are not quadratic. So wave dynamics supplies one instance of the law, and the sharp rate is the law at all probes.

**Does the sharp rate over curves follow from such a law?** Yes, and on a true curve the law is proved here (`elliptic_has_countLaw`), with Hasse's theorem as a consequence (`hasse_of_countLaw`) and universal damping after it
(`elliptic_universal_damping_of_countLaw`). The proof does not use Stepanov's argument or any character sum bound. Its input beyond wave dynamics is the addition law of the curve, and that is exactly what a fake does not have: the parallelogram law comes
from `h` having no double root, and the count at `1 - π` from the Frobenius point.

**What quantity decays at exactly the universal rate, and what is the proof in the graph model?** The Krein square. The
proof is the algebraic identity above, for every `t` (`normalizedKrein_step`). The signal itself decays at the universal
rate only under universal damping (`ringSignal_rate_iff`, `horocycle_rate_iff`).

**What is the physical meaning of `¼`?** It is Liouville's value for an oscillator that is not overdamped. The state map has
determinant fixed by the functional equation, so a mode and its partner multiply to `q^{-n}` at double tick `n`, and to
`e^{-τ/2}` at modular time `τ` (`normalizedMode_mul_partner`, `modeFactor_mul_partner`). Their rates sum to `½`
(`dampingRate_add_partner`). `¼` is the isotropic case, half the contraction rate of the area. The reflection `a ↦ q/a` that
fixes it is not unitarity, which is `a ↦ q²/a`: it is the functional equation of the denominator. A throat shows that the two are independent: the flux law holds and the modes multiply to
`(b-1)q` (`throat_partner_law`), so without the functional equation there is no `¼`.

**Is `¼` the midpoint of a KMS strip in the Mellin variable?** Yes. With `G(z) = ξ(1 + iz)`, the functional equation is `G(z + i) = G(-z)`, a KMS condition at `β = 1` (`xi_kms_condition`), with the
critical line as fixed line at height `β/2` (`kms_midpoint`). A mode at `ρ` has rate `(1 - Re ρ)/2`, and `¼ = ½ · β/2` is the rate of the midpoint (`quarter_iff_midpoint`). KMS positivity holds
for `ξ` unconditionally, because Riemann's kernel is positive (`xi_kms_positive`). It does not locate the zeros: a positive even kernel with Gaussian decay has a transform with the same
KMS condition and positivity whose zeros are all at distance `b` from the line (`fake_horizon`).

**Why is the plus branch silent, and what does it say about reflection?** The same eigenfunction with time factor `Y^τ` is a
function of `τ + k` on each ray: a purely incoming wave absorbed by the core, the time reversal of the ringdown
(`plusBranch_isIncoming`, `plusBranch_constantTerm`). Reflection is reciprocal, `S(X,Y) S(Y,X) = 1`
(`scattering_mul_swap`), so the pole at `X` is a zero at `Y`. This holds wherever the resonance is.

**Does Hecke at a second place constrain the flux through the first?** No. On the sector that carries the resonances it is a
function of the wave group: `A` itself on the graph, time translation over `ℤ`. Any operator with the Hecke shape in the cusps, at any
degree, acts on a resonance by the scalar forced by dispersion (`hecke_rigidity`). Its independent content lies on the cusp forms, where it separates what `A` does not
(`heckeTwo_separates`), and they have no flux and no resonance. An exact symmetry that decides nothing.

**What is the bulk reading of the log-mean?** It is the Bode integral of the causal symbol on the universal line
(`causalSymbol_universalFrequency`), and it measures the total damping deficit: `2 log q Σ(¼ - rate)⁺` over a curve
(`bode_integral_every_genus`), the Green potential of the slow modes in Poisson form, and the density of the deficit in the
Abel limit (`bode_hasSum`, `bode_tendsto_iff_deficit_density`).

**Is there a flux law for the Krein square with a manifest boundary square as flux?** A flux law, always: `𝓕 = (1-1/q)𝒬` on
the graph, `½𝒬` over `ℤ`. A manifest square, exactly under RH (`flux_nonneg_iff`, `kreinSquare_eq_sum_sq`,
`kreinFlux_nonneg_iff`). If RH fails there is a test with `𝒬 < 0` at all times, rising to `0`
(`exists_antiDissipative_of_not_riemannHypothesis`). So the Thomson–Tait–Chetaev argument has content only once `𝓕 ≥ 0` is known,
and on the graph that fails on the fakes. The physical energy is a different object: positive off the ground mode, conserved, and
with no information about mode positions.

## 6. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Exact resonances of the black hole | `exists_outgoing_iff`, `jost_eq_zero_iff` | unconditional |
| Exact field of a pulse | `Channels.pulse_isWave`, `reflected_of_lt`, `echo_sub_ground` | unconditional |
| Edge theorem from flux | `Channels.norm_resonance_lt`, `normSq_lt_of_outgoing` | unconditional |
| Hecke algebra on every black hole | `heckeOp_comm`, `truncSum_heckeGreen`, `IsWave.hecke` | unconditional |
| Rigidity of Hecke on resonances | `hecke_rigidity`, `IsOutgoing.hecke_eigen`, `chebOp_eigen` | unconditional |
| Hecke at degree two on fakes | `Channels.heckeTwo_comm`, `Channels.heckeTwo_nonneg`, `universal_damping_not_forced_with_degree_two` | unconditional |
| The propagator is positive | `chebOp_nonneg`, `heckeDeg_nonneg`, `universal_damping_not_forced_at_every_degree` | unconditional, odd groups, `q ≥ 7` |
| Cusp forms and their Hecke eigenvalues | `thetaField_wave`, `heckeTwo_thetaField`, `heckeTwo_separates`, `heckeTwo_eq` | unconditional |
| Full Hecke family on fakes | `heckeFull_comm`, `heckeFull_nonneg`, `heckeFull_symmetric`, `universal_damping_not_forced_by_the_full_algebra` | unconditional |
| Count law | `CountLaw.eq_kreinSquare`, `exists_countLaw_iff`, `Channels.universal_iff_countLaw`, `probeCount_law_iff` | unconditional |
| Fake towers are groups | `card_quotient_probeLattice`, `card_quotient_tower` | unconditional |
| KMS strip and fake horizon | `kms_midpoint`, `xi_kms_positive`, `fake_horizon` | unconditional |
| Lax–Phillips semigroup and Krein signature | `hankel_det_eq_zero`, `lpMatrix_det`, `kreinHerm_step`, `kreinHerm_nonneg_iff`, `kreinHerm_mode` | unconditional |
| Kramers–Kronig for the causal symbol | `kramers_kronig`, `causal_symbol_kramers_kronig` | unconditional |
| Exact parallelogram law of heights | `crossRelations`, `forms_no_common_zero`, `height_parallelogram` | unconditional, odd characteristic |
| Count law on a true curve, and Hasse | `elliptic_has_countLaw`, `hasse_of_countLaw`, `elliptic_universal_damping_of_countLaw` | unconditional, odd characteristic |
| Hecke at every class on fakes | `heckeClass_comm`, `heckeClass_nonneg`, `heckeClass_resonance`, `universal_damping_not_forced_at_every_class` | unconditional, odd groups, `q ≥ 7` |
| Path quotients and the functional equation | `chain_green`, `chain_resonance`, `chain_no_functional_equation` | unconditional |
| Partner law is independent of flux | `throat_green`, `throat_partner_law`, `throat_functional_equation_iff` | unconditional |
| Integer probes over `ℤ` | `riemannHypothesis_iff_integerProbes`, `integerProbe_parallelogram`, `posSemidef_of_integer_nonneg` | equivalence |
| Universal damping is not forced | `exists_slow_resonance`, `universal_damping_not_forced_*` | unconditional |
| Hasse window | `universal_iff_window`, `universal_iff_product` | unconditional |
| Krein flux law | `kreinSquare_step`, `normalizedKrein_step`, `curveKrein_step`, `physicalKrein_eq` | unconditional |
| Krein square is the degree form | `kreinSquare_eq_endDeg`, `krein_eq_half_defect` | unconditional |
| Sign of the flux | `flux_nonneg_iff`, `toeplitz_nonneg_iff_unitary`, `kreinFlux_nonneg_iff` | equivalences |
| Sharp rate of the signal | `ringSignal_rate_iff`, `lucasMix_rate_iff`, `physicalCorrelator_rate_iff` | equivalences |
| Zagier on the graph | `horocycle_rate_iff` | equivalence |
| Physical positivities are blind | `schur_bound_iff`, `Channels.coreMoment_psd`, `ramanujan_for_every_black_hole` | unconditional |
| One clock over `ℤ` | `heckeOp_normalizedEisenstein`, `heckeOp_wavePacket`, `treeWave_isWave` | unconditional |
| Rank barrier | `ringSignal_silenced`, `infinite_excited_modes` | unconditional |
| Calibration on true curves | `ellipticChannels`, `elliptic_universal_damping`, `elliptic_universal_damping_of_countLaw` | by Stepanov, and independently by the count law |
| Tower | `abs_towerTrace_lt`, `towerTrace_overdamped`, `tower_bound_iff` | unconditional |

## 7. Tools

**Developed.**
- *Energy estimates that see Hecke*: `energy_balance` for any pair of waves, and one conserved energy per place and degree
  (`hecke_energy_balance`, `heckeDeg_energy_balance`).
- *A Lyapunov functional for the Eisenstein sector*: the Krein square, positive with the universal rate exactly under universal
  damping (`kreinSquare_eq_sum_sq`). Over curves it is the degree form, and Hasse's proof is the positivity of this Lyapunov
  functional on the integer lattice (`integer_kreinSquare_nonneg_iff`).
- *Sharp decay for smoothed resonant sums*: `lucasMix_rate_iff`, `physicalCorrelator_rate_iff`, a rate for each probe.
- *Causal, compactly supported probes*: `kreinSquare_probe`, `ringSignal_silenced`. A finite probe silences a curve; no probe
  silences the horizon (`infinite_excited_modes`).
- *Horocycle renormalization*: `horosphere_isWave`, `horoMean_heckeOp`.
- *Exact models*: `oddChannels`, `oddPairChannels`, `Channels.ofGroup`, `ellipticChannels`, `datumOfRoots`, `throatOp`, `chainOp`, `fakeXi`.
- *Height calculus*: the three forms, the Top calculus for degrees at infinity, and `eq_const_mul_of_cross`, on any curve over a rational function field.
- *Closed forms of the propagator*: `even_closed`, `odd_closed`, `root_formula`, with the coefficient calculus of `ThePropagatorCoefficients`.
- *Functional model*: the semigroup `lpMatrix`, the metric `kreinHerm`, and the Szegő pairing `gram_law`.
- *Integer positivity*: a real Hermitian matrix nonnegative on integer vectors is positive semidefinite (`posSemidef_of_integer_nonneg`).

## 8. Traps

| Trap | Truth |
|---|---|
| Unitarity forces the critical line | It forces the half-plane of the poles and the edge: `|S| = 1`, `|a| < q` on every black hole |
| Causality or passivity gives RH | Passivity is `|t| ≤ q + 1`, the edge (`schur_bound_iff`) |
| Physical energy is a Lyapunov functional for the rate | It is conserved and sees no mode position; the Krein form has the rate |
| Krein positivity follows from dissipation | Flux is `(1-1/q)𝒬`: its sign is the statement |
| Pulses detect the fake | A pulse has `𝒬 > 0` everywhere (`kreinSquare_ringSignal`); a two-term probe is needed |
| Hecke at a second place is an independent constraint | On the sector of the resonances it is `A`, or a time translation; it is independent only on the cusp forms, which have no resonance |
| Hecke positivity excludes fakes | The whole family is positive and commuting on the fakes (`heckeFull_nonneg`, `heckeDeg_nonneg`) |
| The propagator has signs because the tree does | On the tree `P_d(A)` has negative entries; on the quotient they are filled, for `d ≥ 3` |
| `P₂(A)` is Hecke of degree two | It has the entry `1 - q` on a dead end; the operator at a place is `P₂(T_Q) - q Λ_w`, with `w ≠ 0` |
| The fake has no point counts | `ℤ[π]/(1 - π^n)` is a group of order `q^n + 1 - V_n` at every level (`card_quotient_tower`); it is the count law that fails |
| Conservation of channels is the whole law | It is the first instance; a fake breaks the second (`fake_violates_second_probe`) |
| The count law is Hasse in other words | It has an independent proof, by the addition law of the curve (`height_parallelogram`), and Hasse follows |
| Long throats generalize the curve | Their partner product is `q^m (c₀ - 1)`, so they miss the functional equation from genus two on |
| KMS positivity places the zeros | It holds for `ξ` unconditionally, and on a fake horizon with no zero on the line (`fake_horizon`) |
| A slow mode is a resonance of negative norm | It is neutral: `H(1, z) = 0` on a real mode (`kreinHerm_mode`). Negative states are the combinations of two modes |
| Unitarity gives the functional equation | A throat has flux and unitarity for all `b`, and the functional equation only at `b = 2` |
| Ramanujan bound is universal damping | The `L²` spectrum has Ramanujan shape on every fake: resonances are not spectral data |
| Base change kills fakes | Channel counts stay positive at every level, and the oscillator stays overdamped |
| A polynomial probe works over `ℤ` | Every nonzero compact probe excites infinitely many modes (`infinite_excited_modes`) |
| Raw echoes decay universally over `ℤ` as over curves | Finite rank gives pointwise bounds; over `ℤ` spikes defeat them, independently of RH |
| Radial means `T_Q = A` | Only on the balanced sector; the dead ends and pins have type-constant functions outside it |

## 9. Where it sits

| Neighbour | Interface |
|---|---|
| BlackHoleRingdown | the modular horizon, packets, causal symbol; ASH is the field around that exact solution |
| ArithmeticCastelnuovoSeveri | `CurveDatum`, `endDeg`, graph defects, Hodge index on the span |
| ArithmeticInnerFunctionTheory | `lPoly`, `innerMass`, `innerField`, depth density |
| ArithmeticOrientationGeometry | scale isometry, orbit correlation, rate theorem: the Krein law over `ℤ` |
| RenormalizedIntersectionTheory | Mayer scattering, with the Lax–Phillips generator over `ℤ`; the Krein reflection `s ↦ ½ - s̄` and its negative states |
| RHTower | the Hasse bound by Stepanov, Eisenstein Hecke relations, compact test obstruction, Riemann's kernel `Φ > 0` |
| HeckeKreinToeplitz | integer windows carry the whole index: the source of the integer probes over `ℤ` |
| ArithmeticPositiveDuality | the Toeplitz form of the spline orbit |
| PrimeTorusTheory | the orbit at finite time; ASH has no statement about many primes at finite height |

**In the research.** ASH closes the physical door of the review: flux, unitarity and Hecke do not produce the sign. It does not
close RH and is not an RH route. Its value is the classification of what wave dynamics can and cannot see, the exact model on which any
future physical idea can be tested, and the Krein law as the single object that has the universal rate unconditionally.

**The fakes.** On the true curve `t` is the difference between trapped and open channels, and Hasse says that they are balanced to within `2√q`. A fake is the same formulas with `ℤ[π]` a real
quadratic order: its norm form is indefinite, its tower is a tower of honest groups, and it has the whole Hecke algebra. Three cases sum it up:

| | `K` is a count | `K` is quadratic |
|---|---|---|
| a curve | yes: the degree | yes (`height_parallelogram`) |
| a fake | yes: `K = \|𝒬\|` | no (`probeCount_law_iff`) |
| `ℤ` | not known | yes (`integerProbe_parallelogram`) |

So positivity is what happens when both hold, which is the argument of Cassels and of Weil. A wave system sees only the first instance of the law.

## 10. Success criteria, and what a contribution must be

**Criteria from the review.**
- Recovers the edge theorem from flux: done (`Channels.norm_resonance_lt`). The sharp rate over curves: impossible from flux, unitarity and Hecke. It is equivalent to the count law, whose first instance is the conservation of channels
  (`Channels.universal_iff_countLaw`), and the law on a true curve is proved from the addition law (`elliptic_has_countLaw`), which gives the rate (`elliptic_universal_damping_of_countLaw`).
- Fails for non-arithmetic `Γ`: the fakes are exact non-arithmetic examples.
- Explains why KMS, Schur and `C*` positivity are blind: they hold on the fakes (`ThePhysicalPositivitiesAreBlind`), and KMS positivity holds for `ξ` and for a fake horizon alike
  (`xi_kms_positive`, `fake_horizon`).
- Consistent with raw echo spikes: the statement with a universal rate is the quadratic one, and the amplitude statements are smoothed.
- No prediction contradicting GUE: the Krein form is diagonal in the modes, and holds for every arrangement of zeros on the line
  (`kreinFlux_nonneg_of_onLine`). It says nothing about spacing.

**A contribution must** be a theorem about the wave system and not a dictionary entry; state what it does on the fakes; state whether it is
blind to the position of a resonance; and over `ℤ` either carry through the rank barrier or say where it stops.

**The programme would close RH** with a nonnegative quantity defined without the Weil form and equal to it on the integer probes (`riemannHypothesis_of_count`). On a curve this quantity is the
degree. Over `ℤ` none is known, which is the door of the effective geometry programme.

## 11. Open research topics

1. Over `ℤ`: a count equal to the Krein square of the integer probes. By `riemannHypothesis_of_count` this is a proof of RH, so it is the open problem itself, not a task of this programme.
2. The true quotient `Γ\T` for a curve of genus two, with its branching, and the partner law as a statement about the lattice. By `chain_no_functional_equation` it cannot be a path.
3. The small fields: `P_d(A)` has a negative entry at `q = 2`, `h = 5`, `d = 3` (paper computation), where the curve has no place of degree three. Which entries of the family need a place to exist?
4. The cuspidal sectors of the adelic bulk: Maass forms, where Hecke is independent of the wave group and there are no resonances, as `thetaField` is on the graph.
5. The Bode integral at finite height over `ℤ`, with an exceptional set.
6. Characteristic two, where the height law needs the general Weierstrass form.

**Cited, not formalized.** Takahashi's identification of the graph with `Γ\T` for `G = E(𝔽_q)`, and Bass–Kulkarni for the existence of the lattice. They give the graph its geometric meaning. No theorem here uses them.
