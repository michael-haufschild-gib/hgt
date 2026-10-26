# Multiplicative Positivity Geometry (MPG)

**One question.** The only forcing mechanism in the corpus is multiplicative. Positivity of the
Euler log-coefficients `Λ(n) ≥ 0`, coupled across the harmonics of a height, forces `ζ(1+it) ≠ 0`.
Combined with growth input it forces the classical zero-free regions. What is the complete content
of that positivity: everything it permits, everything it forces and exactly what it can certify in
the strip?

MPG answers on the boundary line and measures the answer in the interior. Basic object: the
**boundary divisor** `D(u) = (pole order) − (zero order)` at `1 + iu`, viewed as a function on the
discrete group `(ℝ, +)`. Basic theorem: **for nonnegative log-coefficients, `D` is an even
positive-definite function.** De la Vallée Poussin, Mertens and Fejér inequalities are Gram forms of
this one function. Forcing questions become questions about integer-valued positive-definite
functions, and those can be answered completely.

The boundary has four forcing mechanisms: positive definiteness of `D` (Bochner), Baire regularity
of boundary limits (which excludes dense supports), Bessel's inequality for the Rankin–Selberg square
of a signed datum, and the decay-exponent law, which uses growth rates of `log |Z|` instead of
boundary limits. For families over a finite abelian group the
same theory lives on `G × ℝ`, and its only unforced configuration is a two-torsion exception.

Namespace `GaloisForLFunctions.MultiplicativePositivityGeometry`; umbrella
`MultiplicativePositivityGeometry.lean`. Everything is unconditional.

---

## 1. Place in the research

The route review records two exhaustion facts.

- Single-channel quadratic positivity can only certify blindness: every sharp-stable positive
  convolution ideal of the Meyer source lies inside the off-line-blind ideal
  (`isGreatest_meyerSharpPositiveIdeal`,
  [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md)).
- Coefficient positivity forces, but only on `Re s = 1`, and with growth input up to the
  Vinogradov–Korobov region.

MPG is the theory of the second fact. Its results show that multiplicative positivity is a
**complete boundary theory**: it classifies and realizes every boundary configuration and identifies
the minimal invariants that force `D_ζ = 1_{0}`. It is also a **closed interior method**: what it
certifies in the strip is an exact function of three numbers, its best case is strictly below any
fixed strip, and no choice of positive certificate improves it. The missing input for RH is
therefore located outside multiplicative positivity, in the growth input or in an interior object.

| Programme | Interface |
|---|---|
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Maximality theorem (the quadratic side); harmonic coupling module: `zetaRealLogDeriv`, `tendsto_zetaRealLogDeriv_boundary`, `fejerAutoCoeff`, the double-pole and periodic-pole models. MPG replaces its single cosine polynomial by the whole positive-definite function. |
| HTGeometry | `cosinePolynomial`, `cosinePolynomial_purchase_ratio_le_two`, `purchase_width_cap` (the universal cap MPG sharpens per degree); complex positive definiteness of atomic Fourier series; Bohr means. |
| RHTower | `dlvp_half`, `neg_re_logDeriv_riemannZeta_real_le` (the calibration input); classical dlVP, Littlewood and VK regions. |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md), ArithmeticOrientationTheory | Orientation is positive definiteness of the orbit correlation, a quadratic object. MPG is its multiplicative counterpart. The golden datum `1 − 5X + 5X²` has nonnegative point counts, so over `𝔽_q` multiplicative positivity is passed by an RH-violating datum. |
| BVI, TransHorizon, SquareRootThreshold, AOT width functor | Their receivers are width statements. MPG's growth law says which widths multiplicative positivity can reach, and so what input those routes must supply. |

---

## 2. Why

**The boundary is a limit of positive-definite functions.** For `σ = 1 + x > 1`,
`u ↦ Re(−ζ'/ζ)(σ + iu) = Σ_n Λ(n) n^{−σ} cos(u log n)` is a nonnegative combination of characters of
`ℝ`, hence positive definite (`zetaRealLogDeriv_isEvenPosDef`). Multiplying by `x` and letting
`x ↓ 0` produces the pole order at `1` and minus the zero orders on the line. Positive definiteness
survives pointwise limits, so the boundary divisor is positive definite.

**Positive-definite integer functions are rigid.** With `D(0) = 1` and integer values, the bound
`|D| ≤ D(0)` leaves `{−1, 0, 1}`. A three-point Gram form shows that the nonvanishing set is a
subgroup and `D` is a `±1` character on it. A boundary zero is therefore a `−1` of a character, and
a character has `D(2u) = D(u)² = 1`. Every boundary zero forces a pole at twice its height. For `ζ`
there are no such poles, so `ζ(1+it) ≠ 0`.

**In the interior there is no limit.** At `σ > 1` positivity still holds, but zeros in the strip
enter only through continuation and growth bounds. The method then reduces to one inequality
between three numbers: pole weight, zero weight and growth. MPG computes what that inequality can
give.

---

## 3. Objects and language

| Object | Definition | Lean |
|---|---|---|
| Positive-definite function | `φ : G → ℝ` on an additive group with `Σᵢⱼ cᵢ cⱼ φ(xᵢ − xⱼ) ≥ 0`; even when `φ(−u) = φ(u)` | `IsPosDef`, `IsEvenPosDef` |
| Cosine trace | `u ↦ Σᵢ wᵢ cos(λᵢ u)`, weights `wᵢ ≥ 0`, frequencies `λᵢ` | `cosineTrace` |
| Boundary datum | damped weights `w(x)`, `x > 0`, with `x · trace(w(x))(u) → D(u)` | `IsBoundaryDivisor lam w D` |
| Boundary divisor | the limit `D`; for an Euler product, pole order minus zero order at `1 + iu` | `zetaBoundaryDivisor` |
| Nonvanishing subgroup | `{u : D(u) ≠ 0}` for integer `D` with `D(0) = 1` | `nonvanishingSubgroup` |
| Profile | restriction `m ↦ D(m t₀)` to a progression, a positive-definite sequence on `ℤ` | `profileCoeff` |
| Twist | weights multiplied by `P(t₀ λᵢ)`, `P` a nonnegative cosine polynomial | `twistedWeight`, `twistWeight` |
| Progression datum | one-prime weights `h e^{−(hn+c)x}` on frequencies `hn + c` | `progressionWeight` |
| Certificate | nonnegative cosine polynomial, or almost-periodic polynomial `Σ_{u∈S} a(u) cos(ut)` | `cosinePolynomial`, `multiFrequency_purchase_le_two` |
| Purchase ratio | `a₁/a₀`: zero share bought per unit of pole | `cosinePolynomial_first_le_fejer` |
| Exclusion | `A/δ + G < B/(δ+η)` for some `δ > 0`: pole `A`, zero `B` at distance `η`, growth `G` | `exclusion_iff` |

The **four boundary invariants** of a datum:

- **(N)** nonnegative weights;
- **(Z)** an integer divisor;
- **(S)** a simple pole, `D(0) = 1`;
- **(I)** pole isolation, `D ≤ 0` off the origin.

The language keeps these distinctions explicit:

- test-space positivity (Weil, Hodge) vs height-space positivity (MPG);
- one Gram form (a harmonic inequality) vs positive definiteness (all Gram forms);
- boundary (a limit, positivity exact) vs interior (continuation plus growth);
- forced vs imported regions;
- certificate (the cosine polynomial) vs input (pole, zero and growth bounds).

---

## 4. Mechanisms

1. **Two-point Gram.** `|φ(h)| ≤ φ(0)`: a boundary zero has order at most the pole order at `1`
   (`abs_le_apply_zero`, `boundary_zero_order_le`).
2. **Three-point translation.** `φ(h) = ±φ(0)` forces `φ(h + u) = ±φ(u)` (`apply_add_of_eq`,
   `apply_add_of_eq_neg`). Combined with integrality this gives the subgroup-and-character structure
   (`intValued_mul`, `nonvanishingSubgroup`).
3. **Fejér progression vector.** The constant vector on `0, h, …, (N−1)h` gives
   `N φ(0) + 2 Σ_r (N − r − 1) φ((r+1)h) ≥ 0` (`progression_gram`, via `sum_range_sum_range_sub`).
4. **Closure.** Positive multiples and pointwise limits of positive-definite functions are
   positive definite (`isEvenPosDef_of_tendsto`). This passes positivity from `σ > 1` to the line.
5. **Discreteness.** A locally finite divisor has a non-dense, hence cyclic, nonvanishing subgroup
   (`nonvanishingSubgroup_cyclic`, from `AddSubgroup.dense_or_cyclic`).
6. **Product-to-sum twisting.** `cos(kt₀ log n) cos(u log n)` splits into the characters at
   `u ± kt₀`, so twisting shifts and averages divisors (`twist_mode`).
7. **Dual quadrature.** Weighting the roots of `z^{K+2} = −1` by `cos α − cos θ_j ≥ 0` kills all
   middle moments (`fejer_quadrature`).
8. **Geometric mean.** The optimal damping `δ* = √(Aη/G)` turns the exclusion inequality into
   AM–GM (`exclusion_at_geometric_mean`).
9. **Discrete Bohr mean.** Sampling along a non-resonant progression isolates the constant term
   of an almost-periodic polynomial (`abs_cosSum_le`).
10. **Følner sets without a basis.** The sets `{Σ n_z z : 0 ≤ n_z < N}` grow polynomially, so some
    step grows by at most `1 + ε`, and their Gram forms see every zero with weight about
    `|F_N|` (`folnerSet`, `exists_folner_step`, `card_shift_mem_ge`).

---

## 5. Pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| **P1 Boundary positivity** | The boundary divisor of nonnegative weights is even positive definite on `ℝ`. | `isEvenPosDef_cosineTrace`, `IsBoundaryDivisor.isEvenPosDef` |
| **P2 Simple-pole rigidity** | With (Z) and (S): `D ∈ {−1, 0, 1}`, `D(ku) = D(u)^{|k|}`, and a zero at `u` forces a pole at `2u`. | `boundary_values`, `boundary_mul_natAbs`, `boundary_zero_forces_double_pole` |
| **P3 Trichotomy** | A locally finite simple-pole integer divisor is `1_{0}`, `1_{cℤ}` or the alternating character on `cℤ`, and each type occurs. | `boundary_trichotomy`, `boundary_trichotomy_realized` |
| **P4 Total zero mass law** | Without off-origin poles, the zero masses at any finite set of positive heights add up to at most `D(0)/2`, sharp. With an integer divisor at most `D(0)/2` heights carry zeros, and a simple pole admits none. The progression law is the special case of one progression. | `total_zero_mass_le`, `card_zero_heights_le`, `eq_zero_of_simple_pole`, `doublePoleProfile_total_mass`, `boundary_progression_zero_mass_le` |
| **P5 ζ on the line** | `D_ζ = 1_{0}`; `ζ(1+iu) ≠ 0` from positive definiteness alone; prime phases at distinct heights are asymptotically orthonormal. | `zetaBoundaryDivisor_eq`, `riemannZeta_boundary_ne_zero_of_posDef`, `zeta_boundary_gram_tendsto` |
| **P6 Realization** | A finitely supported even profile is a boundary profile iff it is positive definite on `ℤ`, iff its cosine polynomial is nonnegative. Twisted von Mangoldt weights realize every such profile. | `boundary_profile_iff`, `profile_isEvenPosDef_iff`, `twisted_isBoundaryDivisor` |
| **P7 Completeness and minimality** | (N), (Z), (S), (I) force `D = 1_{0}`. Dropping any one admits a boundary zero, realized by an explicit datum. | `boundary_forcing_law`, `isolation_necessary`, `simplicity_necessary`, `integrality_necessary`, `nonnegativity_necessary` |
| **P8 Interior invisibility** | Data with bounded mass at the boundary have `D = 0`. `ζ(s) Φ(s + κ)` satisfies all four invariants and vanishes inside the strip. | `isBoundaryDivisor_zero_of_bounded`, `interior_zero_invisible` |
| **P9 Exact Fejér barrier** | A nonnegative cosine polynomial of degree `K` has `a₁ ≤ 2cos(π/(K+2)) a₀`, and the constant is attained. | `cosinePolynomial_first_le_fejer`, `fejer_barrier_attained`, `fejer_barrier_sharp` |
| **P10 Growth-to-forcing law** | Exclusion holds iff `√A + √(Gη) < √B`: the certified width is exactly `(√B − √A)²/G`. An input valid only for `δ ≤ δ₁` loses nothing once `Aη ≤ Gδ₁²`. | `exclusion_iff`, `exclusion_iff_lt_width`, `exclusion_iff_restricted` |
| **P11 Certificate caps** | Degree `K` certifies only `η < (1 − ρ_K^{−1/2})²/L`; degree one certifies nothing. Any finite multi-frequency certificate has `a(γ) ≤ 2a(0)`, so the universal cap `(3 − 2√2)/(2L)` binds them all. | `fejer_width_cap`, `degree_one_excludes_nothing`, `fejer_width_cap_lt_universal`, `multiFrequency_purchase_le_two`, `multiFrequency_width_cap` |
| **P12 Calibration** | The corpus dlVP input gives `β ≤ 1 − (2 − √3)²/((5/2) log γ + C)`, and no better region follows from it. | `xiZero_re_le_dlvp`, `dlvp_input_consistent` |
| **P13 Finite Bochner** | A finite configuration (heights arbitrary, poles allowed off the origin) is a boundary divisor iff it is positive definite iff its Bohr polynomial `D(0) + 2Σ D(z) cos(zt)` is `≥ 0`; it is realized by `Π_v ζ(s + iv)^{D(v)}`. | `finite_boundary_divisor_iff`, `finiteConfig_isEvenPosDef_iff`, `bohr_isBoundaryDivisor` |
| **P14 Integral realization** | Greedy rounding of the exponents preserves the boundary divisor, so every finite positive-definite configuration is the divisor of `Π_p (1 − p^{−s})^{−m(p)}`, `m(p) ∈ ℕ`. Exponents in `{0, 1, 2}` give half zeros: (Z) is a meromorphy condition, not integrality of the prime data. | `IsBoundaryDivisor.round`, `integral_boundary_profile_iff`, `integral_half_zero` |
| **P15 Zero capacity** | Integer `D`, pole order `k`, no off-origin pole: `D = kδ₀ − Σ m(z)(δ_z + δ_{−z})` with `2Σ m ≤ k`, each realized by `ζ^{k−2M} Π (ζ(s)²/(ζ(s+iz)ζ(s−iz)))^{m(z)}`. | `isolated_boundary_classification`, `capacity_isBoundaryDivisor` |
| **P16 Positivity margin** | Signed weights `≥ −εΛ`: the same classification with `2Σ m ≤ k + ε`; a simple pole forces `D = δ₀` iff `ε < 1`. | `margin_classification`, `simple_pole_margin_threshold` |
| **P17 Range** | `D` is a boundary divisor iff it is a pointwise limit of positive cosine polynomials. `1_ℚ` is positive definite and is not one. | `isBoundaryDivisor_iff_tendsto_posCosPoly`, `rationalIndicator_not_boundaryDivisor` |
| **P18 Families** | For a family over a finite abelian `G` the joint divisor is positive definite on `G × ℝ`; with (Z), (S), (I) it is `δ₀` or `δ₀ − δ_{(h,0)}` with `2h = 0`, and both occur. | `joint_boundary_classification`, `exceptional_isJointBoundaryDivisor` |
| **P19 Rankin–Selberg** | For signed log-coefficients `Λg`: `D_f(0)² + 2Σ_{u ∈ U} D_f(u)² ≤` pole order of `f ⊗ f`; simple poles of `f` and `f ⊗ f` force `D_f = δ₀`; equality for `ζ(s)/(ζ(s+i)ζ(s−i))`. | `rankinSelberg_bessel`, `rankinSelberg_forcing`, `rankinSelberg_bessel_sharp` |
| **P20 Abelian mass law** | On every abelian group a positive-definite `φ ≤ 0` off the origin has off-origin mass `≤ φ(0)`; zeros with `p ≠ −p` have order `≤ φ(0)/2`, self-conjugate ones `≤ φ(0)`. | `total_offOrigin_mass_le`, `zero_order_le_of_pair` |
| **P21 Decay law** | If `log |Z|` has growth exponent `≤ k` at the pole, `≤ 0` elsewhere and decay exponents `α_z` at the heights `z`, then `Σ α_z ≤ k/2`; no boundary limits are needed. A simple pole admits no decay faster than `x^{1/2}`. | `decay_mass_law`, `holder_barrier` |
| **P22 Beurling threshold** | A Beurling-type zeta `A(1+w)/w + (1+w)∫ r(v)e^{−wv}dv` with nonnegative log-coefficients and `∫|r|(1+v)^θ < ∞` has `nθ ≤ 1/2` for `n` boundary zero heights; a count error `O(t/log^γ t)` gives every `θ < γ − 1`, so `γ > 3/2` leaves no zero: `3/2 = 1 + ` half capacity. | `beurling_zero_count`, `moment_of_power_decay`, `norm_beurlingZetaModel_sub_le` |
| **P23 Protected points** | A zero at a point `p` of the family group `G × ℝ` gets a certified zero-free interval iff `2p ≠ 0`: order-two fibres have purchase ratio `1`, cyclic fibres of order `≥ 3` ratio `2`. `Z_0 = ζ`, `Z_h = 1/ζ(s + 1 − β)` (and `ζ(s)/ζ(s+1−β)` for `h = 0`) satisfy every boundary invariant with a real zero at any `β < 1`. | `siegel_isJointBoundaryDivisor`, `siegel_member_zero`, `cyclic_fibre_sum_nonneg`, `unpaired_real_zero_unexcluded` |
| **P24 Lattice realization** | The lattice of simple poles and the alternating character are boundary divisors of `Π_p (1 − p^{−s})^{−m(p)}`, `m(p) ∈ ℕ`: primes in windows `(e^{hk+a}, e^{hk+a}(1 + (k+1)^{−2})]` with exponent `⌊h/S_k⌋` reproduce the one-prime factor at the boundary (PNT with de la Vallée Poussin error). Every type of the trichotomy is realized by integral data. | `latticeRound_isBoundaryDivisor`, `integral_lattice`, `integral_alternating` |
| **P25 Family capacity** | For a family over a finite abelian `G`, an even configuration with pole order `k` at the origin, no other pole and finite symmetric support `S` is a joint boundary divisor iff `Σ_{p ∈ S} m(p) ≤ k`; realized by character-twisted ζ weights. A self-conjugate point (`2p = 0`) can carry the whole capacity `k`, a pair `±p` at most `k/2` each. | `family_isolated_iff`, `capFamily_isJointBoundaryDivisor` |
| **P26 Locally finite Bochner** | A locally finite `D` (finitely many points in every bounded set; poles and zeros anywhere, infinitely many) is a boundary divisor iff it is even and positive definite. Fejér truncations `D(v)(1 − |v|/N)⁺` stay positive definite (overlap of intervals), and their convolutions with `n^{−2}Σ_{k ≤ n²} cos(ku/n)` are positive cosine polynomials converging to `D` pointwise. | `locallyFinite_boundary_divisor_iff`, `IsEvenPosDef.mul_fejerFactor`, `tendsto_fejerPoly` |
| **P27 Regularity** | An integer boundary divisor with `D(0) = 1` is `δ₀`, a lattice indicator, an alternating lattice character or the constant `1`, without assuming local finiteness: a boundary divisor is a pointwise limit of continuous functions, so by Baire it cannot be `±1` on a dense subgroup and `0` on its dense translate. | `boundary_tetrachotomy`, `boundary_locallyFinite`, `not_tendsto_continuous_of_dense` |
| **P28 Arithmetic Bochner** | A locally finite even positive-definite `D` is the boundary divisor of one Dirichlet series `Σ Λ(n) g(log n) n^{−s}` with fixed `g ≥ 0`. The profile `g = Σ_N (e^{−a_N t} − e^{−a_{N−1} t}) P_N(t)` glues the Bohr polynomials of the Fejér truncations; each block is a difference of ζ-traces at two dampings, the diagonal is a Toeplitz average, and uniform continuity of `ζ'/ζ` on compacta of `Re s ≥ 1` minus `1` kills the rest. | `arithmetic_bochner`, `arithmetic_isBoundaryDivisor`, `tsum_block_eq`, `tendsto_toeplitz` |
| **P29 Integral Bochner** | A locally finite `D` is the boundary divisor of an Euler product `Π_p (1 − p^{−s})^{−m(p)}` with `m(p) ∈ ℕ` iff it is even and positive definite. Greedy rounding keeps the prime error below `log(n + 1)` for every profile; logarithmic growth of the P28 profile is absorbed by `Σ_{n not prime} (1 + log n)² Λ(n)/n < ∞`. | `integral_bochner`, `IsBoundaryDivisor.round_log` |
| **P30 σ-additivity and dense supports** | Countable sums of boundary divisors with summable pole orders `Σ_k D_k(0) < ∞` are boundary divisors. `Σ_n 2^{−n} 1_{(2π/(n+1)!)ℤ}` is a boundary divisor positive exactly on the dense subgroup `2πℚ`: boundary divisors need not be locally finite, but by P27 such supports never carry integer values with a simple pole. | `isBoundaryDivisor_tsum`, `ratLattice_isBoundaryDivisor`, `ratLattice_ne_zero_iff` |
| **P31 Summable Bochner and rank `r`** | On any abelian group an absolutely summable even positive-definite `φ` has `Σ φ(γ) cos θ(γ) ≥ 0` for every additive `θ` (Følner Gram forms). Hence every absolutely summable even positive-definite function on `ℝ`, dense supports included, is the boundary divisor of an integral Euler product; for heights `t ∈ ℝ^r` independent over `ℤ`, every summable positive-definite profile on `ℤ^r` is an integral boundary profile, while an integer profile with a unit pole is one only if its support has rank `≤ 1`. | `IsEvenPosDef.tsum_mul_cos_nonneg`, `summable_real_integral`, `rank_profile_integral`, `rank_profile_collapse` |

---

## 6. Answers to the programme questions

The review lists the questions a forcing theory must answer. MPG answers the ones that live in
multiplicative positivity.

**What separates ζ from systems that share its invariants?** On the boundary, exactly the four
invariants (P7). Each is necessary:

| Dropped | Realized datum | Boundary zero |
|---|---|---|
| (I) pole isolation | alternating one-prime factor `(1 + e^{−π(s−1)})/(1 − e^{−π(s−1)})` | at `1`, forced pole at `2` |
| (S) simplicity | `ζ(s)²/(ζ(s+i)ζ(s−i))` | at `±1` |
| (Z) integrality | `ζ(s)/√(ζ(s+i)ζ(s−i))` | half zeros at `±1` |
| (N) nonnegativity | `ζ(s)/(ζ(s+i)ζ(s−i))` | at `±1`; divisor not positive definite |

Off the boundary, boundary data separate nothing (P8): interior zeros and interior poles are equally
invisible. Separation in the strip needs an interior invariant: pole-freeness of the continuation,
the functional equation, or both. This is the open question Q2.

**What replaces the Fejér barrier in the interior?** The full answer for positive certificates
consists of four statements.

1. The law is exact: width `(√B − √A)²/G` (P10).
2. The certificate fixes `B/A`, and `B/A ≤ 2cos(π/(K+2)) < 2` at degree `K` (P9).
3. Coupling any finite set of frequencies, primes and heights does not raise `B/A` above `2`
   (P11).
4. Every certificate therefore stays below `(3 − 2√2)/(2L)` (P11).

No multi-channel structure supplies the missing margin. An interior gain must come from a smaller
growth term `G`, which is outside multiplicative positivity.

**How can quantization force vanishing?** On the boundary there are two routes. Integrality plus
`|D| ≤ D(0) = 1` makes `D` a character, and a character cannot have an isolated `−1` (P2).
Alternatively, the total zero mass is at most `D(0)/2 = 1/2`, while an integer zero has mass at least
`1` (P4). In the interior, the zero
order is not a limit of positive-definite data (P8). Interior quantization needs an object that is
not a boundary datum.

**Growth-to-forcing renormalization (the requested tool).** P10 is the one theorem: any input of the
form `A/δ + G ≥ B/(δ + η)` forces exactly `η ≥ (√B − √A)²/G`. Its sharp barrier is P10 read
backwards (`dlvp_input_consistent`). dlVP is the instance `(3, 4, (5/2) log γ + C)` (P12).

**What does integrality of the prime data permit?** Everything positivity permits (P14, P29). An Euler
product with nonnegative integer exponents over the rational primes realizes every finite
positive-definite configuration, including half zeros. The invariant (Z) is meromorphy at the
boundary.

**Is positivity the only boundary forcing mechanism?** No. A signed datum whose Rankin–Selberg
square has a simple pole has no boundary zeros or poles (P19): the square bounds the `ℓ²`-norm of the
divisor. For families, positive definiteness on `G × ℝ` forces everything except one zero at the
pole on a member of order two (P18); this is the exceptional real character, and excluding it
needs the real axis inside the strip.

Questions about flows, completions, selection, correspondences and shared budgets do not live in
multiplicative positivity. They belong to other programmes.

---

## 7. Traps

| Trap | Truth |
|---|---|
| One harmonic inequality is the whole positivity | It is one Gram form; positive definiteness is all of them (P1) |
| More channels buy more | Any finite multi-frequency certificate has `a(γ) ≤ 2a(0)` (P11) |
| Higher degree approaches the cap | Only in the limit: `2cos(π/(K+2)) < 2` at every degree (P9) |
| Boundary completeness reaches the interior | Boundary data cannot see interior zeros (P8) |
| Positive definiteness alone forces vanishing | Needs integrality: the `1 − cos θ` twist has half zeros (P7) |
| The trichotomy follows from positivity | Positive definiteness permits every subgroup indicator; regularity of boundary limits excludes dense ones, so the trichotomy plus the constant `1` holds for every boundary divisor (P27) |
| Twisted products are Beurling systems | Their prime weights are not integral; they calibrate positivity, not integrality |
| A better constant is a better method | The constant is fixed by the input `(A, B, G)` (P10); only a better input helps |
| Function-field positivity proves Hasse | The golden datum `1 − 5X + 5X²` has nonnegative counts and fails RH |

---

## 8. Tools

Built:

- real positive-definite calculus on additive groups (bounds, translation, subgroup and character
  extraction, progression identities, closure under limits);
- the boundary-datum interface and its calculus (scaling, sums, twists, invisibility);
- realization by ζ-twists and by one-prime progression factors;
- dual-quadrature certificates for nonnegative cosine polynomials;
- the exact growth-to-forcing law with its optimal witness;
- discrete Bohr means along non-resonant progressions.

To build:

- interior data: a positive-definite object attached to the strip;
- the VK and Littlewood inputs as range-limited inequalities, and a law for `δ`-dependent growth.

---

## 9. Open research topics

1. **Interior positivity.** Which positive-definite structure survives analytic continuation into
   `1/2 < σ < 1`? P8 shows it cannot be a boundary datum.
2. **Interior invariants.** Without the functional equation the answer is no: over-regular
   continuous Beurling systems keep (N) and (S) and have off-line zeros
   (`RHTower.overRegular_integers_do_not_constrain_zeros`), and `ζ(s)/ζ(s + 1 − β)` keeps all four
   boundary invariants with a real zero at `β` (P23). With Riemann's theta relation and integral
   masses only `ζ` remains (`HTGeometry.eq_integers_of_riemannThetaRelation`), so with the
   functional equation Q2 is RH itself.
3. **Integral realization.** Answered for locally finite configurations: an integral Euler product
   over the rational primes realizes exactly the even positive-definite ones (P29; P14 and P24 are
   special cases). Open: configurations that are not locally finite.
4. **`σ`-dependent growth.** Range-limited inputs are covered by `exclusion_iff_restricted`. The
   corpus VK step (`vk_dlvp_contradiction`) has the form `4/(δ+η) ≤ 3/δ + G`, but only at one `δ`
   inside the proof of `exists_riemannZeta_ne_zero_vinogradovKorobov_width`. Stated on a `δ`-range,
   it would give the VK region with its optimal constant and its barrier. Inputs with genuinely
   `δ`-dependent `G(δ)` remain open.
5. **Higher poles.** Answered: on locally finite configurations the boundary divisors are exactly
   the even positive-definite functions (P26; P13 and P15 are the finite cases). Beyond local
   finiteness the range is a cone closed under summable countable sums and contains dense supports
   (P30), while positive definiteness alone is not enough (P17). Open: an intrinsic description of
   the full range.

---

## 10. Success criteria and contribution standard

The programme succeeds when the complete content of multiplicative positivity is known. On the
boundary this is achieved (P1–P8). In the interior it is achieved for positive certificates with
constant growth input (P9–P12). It remains open for interior objects and `σ`-dependent input.

A contribution must:

1. be an unconditional Lean theorem, whose ζ inputs are limited to `Λ ≥ 0`, the residue, the Euler
   factorization and explicitly named growth bounds;
2. state a classification, a realization, an exact constant or a sharp barrier, not a new equivalent
   of RH;
3. be selective: distinguish ζ from a realized countermodel, or prove that no statement of its
   class can;
4. keep boundary and interior, forced and imported, certificate and input separate;
5. record the positive survivor of every no-go.

---

## 11. Modules

| Module | Content |
|---|---|
| `PositiveDefiniteFunctions` | Positive-definite functions on additive groups; integer classification; progression law; closure |
| `BoundaryPositivity` | Cosine traces, boundary data, boundary positivity |
| `SimplePoleClassification` | Values, zero forces pole, `δ₀` without poles, cyclic support, trichotomy, zero-mass bounds |
| `ZetaBoundaryDivisor` | The ζ datum; `D_ζ = 1_{0}`; nonvanishing on the line; Gram orthonormality |
| `ArithmeticRealization` | ζ-twists; the double-pole profile; sharpness of the progression law |
| `PositiveDefiniteProfiles` | Positive-definite profiles have nonnegative cosine polynomials |
| `ProfileCharacterization` | Boundary profile ⇔ positive definite ⇔ nonnegative cosine polynomial |
| `ProgressionModels` | One-prime boundary data; lattice and alternating divisors |
| `BoundaryCompleteness` | The four invariants: forcing law and minimality; the trichotomy realized |
| `BoundaryCalculus` | Scaling, sums, twists; bounded data invisible; interior zeros invisible |
| `TotalZeroMass` | Følner sets; total zero mass `≤ D(0)/2`; zero count; simple pole without zeros |
| `ExactFejerBarrier` | `a₁ ≤ 2cos(π/(K+2)) a₀`, quadrature certificate, extremal profile |
| `GrowthToForcing` | Interior positivity; the exact exclusion law; degree-`K` width caps |
| `MultiFrequencyCap` | `a(γ) ≤ 2a(0)` for every finite real spectrum; universal width cap |
| `ZeroFreeRegionCalibration` | The dlVP region as an instance of the law, with its barrier |
| `IntegralRealization` | Greedy rounding; integral Euler products realize every profile; half zeros |
| `FiniteBoundaryDivisors` | Bochner's theorem for finite configurations; almost-periodic twists |
| `BoundaryZeroCapacity` | Capacity `⌊k/2⌋`; classification of pole-isolated integer divisors |
| `PositivityMargin` | Signed data with `w ≥ −εΛ`; the threshold `ε < 1` |
| `BoundaryDivisorRange` | Range of the boundary map; `1_ℚ` is positive definite and not a divisor |
| `CharacterFamilies` | Joint divisors on `G × ℝ`; the two-torsion exception and its realization |
| `RankinSelbergBessel` | Bessel's inequality for the square; Rankin–Selberg forcing |
| `AbelianZeroMass` | The zero-mass law on every abelian group; paired and self-conjugate zeros |
| `DecayMassLaw` | The decay-exponent mass law; Hölder barrier |
| `BeurlingThreshold` | Count regularity gives boundary decay; Beurling's threshold and zero count |
| `SiegelException` | Protected points of the family group; the Siegel family at every depth |
| `IntegralLatticeRealization` | Lattice and alternating divisors from integer exponents at prime windows |
| `FamilyCapacity` | Exact capacity classification of isolated family configurations |
| `LocallyFiniteBochner` | Locally finite boundary divisors are exactly the positive-definite ones |
| `BoundaryRegularity` | Baire regularity of boundary limits; the simple-pole classification without local finiteness |
| `ArithmeticBochner` | Locally finite divisors of a single Dirichlet series `Σ Λ(n) g(log n) n^{−s}` |
| `IntegralLocallyFinite` | Integral Euler products realize every locally finite positive-definite divisor |
| `BoundarySummation` | Countable sums of boundary divisors; a boundary divisor supported on `2πℚ` |
| `SummableBochner` | Bochner positivity in `ℓ¹`; integral realization of summable configurations; rank-`r` profiles |
