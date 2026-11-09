# Arithmetic Lefschetz–Stepanov Theory (ALST)

Namespace `GaloisForLFunctions.ArithmeticLefschetzStepanovTheory`; umbrella
`ArithmeticLefschetzStepanovTheory.lean`; 43 modules. Specification: §2.9 of
[the review-0811 obstacles summary](../../../docs/reports/review-0811/obstacles-summary.md).

## 1. Motivation

Weil's theorem for a curve `C/𝔽_q` has a proof with two halves that never use a positivity of forms:

1. **Lefschetz.** The fixed points of `Fⁿ` are counted by a trace:
   `#C(𝔽_{qⁿ}) = Γ_{Fⁿ}·Δ = qⁿ + 1 − Σ αᵢⁿ`.
2. **Stepanov.** An auxiliary function vanishes to order `J` at every fixed point and has pole order
   `D` at one point; the product formula gives `#C(𝔽_{qⁿ})·J ≤ D`, hence
   `#C(𝔽_{qⁿ}) ≤ qⁿ + O(q^{n/2})` (Bombieri's form, even `n`).

Self-improvement turns the crude count into `|αᵢ| = √q`. Over `Spec ℤ` the corpus has the Lefschetz
half and the self-improvement: the smoothed Frobenius graphs meet with `c_B(log n) = Γ_1·Γ_n`; a
bound `|c_B(log n)| ≤ K` at every integer degree is RH, a lower bound at the square degrees already
suffices (`SurfaceOfSpecZ`); crude bounds on thick sets self-improve (`InfiniteRankWeilTheory`). The
missing half is Stepanov's. ALST is the theory of that half over `ℤ`, and of the point where the two
halves meet: the Lefschetz numbers of the Frobenius graphs are the degree of the auxiliary that
vanishes at their fixed points.

Stepanov's count rests on three exact facts over `𝔽_q`:

| | Fact over `𝔽_q` | Role in the count |
|---|---|---|
| (S1) | the Frobenius is a ring endomorphism fixing every rational point (`x^q = x`) | an auxiliary built from `g∘F` restricts to the points as a low-degree function |
| (S2) | the Frobenius is inseparable: `d(g^q) = 0` | vanishing at a point costs one condition and has order `p^μ` |
| (S3) | the product formula | zeros counted with order and degree are at most the pole order |

ALST locates each fact over `ℤ` and proves what it gives there:

- (S3) holds exactly: the closed points of every prime circle, counted with order and degree, are
  bounded by the length of the auxiliary.
- (S1) holds exactly on the **torsion of the prime torus**, where the Galois action of `ℚ(μ_m)` is
  the power map. The full affine fixed locus also allows zero coordinates.
  Every integral polynomial self-map preserving a finite prime orbit with two distinct primes
  is an Adams operation. Rational preservers of those finite orbits, and of the full prime
  orbit with arbitrary coordinate supports, are signed Adams operations over `ℝ` or `ℤ`.
  Their clocks are `t ↦ nt`, with `n∈ℤ`, and every nonidentity map fixes only `0`.
  This classification assumes no regularity of the clock. Stepanov's construction
  `h = Σ f_i ψ_q(g_i)` runs verbatim on the fixed locus: one polynomial identity `Σ f_i g_i = 0`
  kills `h` there.
- (S2) holds at every finite place `ℓ`: `ψ_ℓ(g) ≡ g^ℓ (mod ℓ)` and the derivatives of `ψ_ℓ(g)` are
  divisible by `ℓ`. Under `Σ (∂_j f_i) g_i = 0` alone, the derivative norm amplifier has
  threshold `ℓ^{φ(m)}`. If the global identity `Σ f_i g_i = 0` also holds, the derivative
  already vanishes exactly on the fixed torus, without a norm bound. The all-order Euler
  transfer identifies this cancellation through polynomial moments. This supplies no
  archimedean inseparability: exact order still costs degree, one order per unit of `log₂ N`.

The archimedean Frobenius exists only approximately (returns of the prime orbit). Exact vanishing
is available off the orbit (closed torsion points), at its one fixed point, and along the closed
points of the prime circles, which the orbit crosses at countably many heights; everywhere it is paid
in degree, at the circles at Chebyshev's price. On the orbit vanishing is cheap only approximately,
and the Rouché copy of an approximate zero is capped by the precision. Stepanov's count needs vanishing that is cheap **and**
exact; over `ℤ` no place supplies both.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Integer auxiliary | `F : MvPolynomial P ℤ` | `P`-smooth integer Dirichlet polynomial `A(s) = F((p^{-s})_{p∈P})` |
| Prime orbit | `orbitPoint P t`, `orbitValue F t`, `orbitFun F s` | `(p^{-it})_p`; `A(it)`; the entire function `A(s)` |
| Frequency, weight | `frequency α`, `weight α` | `λ_α = Σ α_p log p = log n_α`, `n_α = Π p^{α_p}` |
| Length, height, Lipschitz weight | `length F`, `height F`, `lipWeight F` | `N = max n_α`; `H = Σ|c_α|`; `L(F) = Σ |c_α| |α|` |
| Adams operation | `adams a` | `ψ_a F = F(u^a)`, a ring endomorphism |
| Torsion point, closed point | `torsionPoint μ b`, `primitiveRoots m ℂ` | `μ^b = (μ^{b_p})_p`; its conjugates `{μ'^b : μ'` primitive`}` |
| One-variable pullback | `pullback b F` | `F(X^b)`: values at torsion points are values at roots of unity |
| Uniform order | `iterDeriv`, `VanishesToOrder F ω J` | all partial derivatives of order `< J` vanish at `ω` |
| Circle factor | `circlePoly h p`, `circleProduct L` | `h(u_p)`; `Φ_m(u_p)^J` is vanishing to order `J` along the closed point of degree `φ(m)` of the circle of `p` |
| Orbit and power moments | `orbitMoment`, `powerMoment` (two primes), `orbitMomentF`, `powerMomentF` (any `P`), `firstMoment`, `firstPowerMoment` | `Σ c_α λ_α^k = (−1)^k A^{(k)}(0)`; `Σ c_α α^β` |
| Relation among logarithms | `logVec`, `LogRelation P d` | a nonzero integer homogeneous form of degree `d` vanishing at `(log p)_{p∈P}` |
| Siegel data | `pairing`, `auxOf`, `classSum`, `classMatrix` | `b·α`; auxiliary on a set `S`; class sums `C_r = Σ_{b·α≡r} c_α` |
| Closed-point auxiliary | `closedPointAux κ` | `Π_p (u_p − 1)^{κ(p)}`, vanishing to order `κ(p)` at the fixed point `p` |
| Fixed-point auxiliary | `fixedPointAux N`, `primeAux N` | `A_N = Π_{p≤N} (u_p − 1)^{⌊log_p N⌋}`: the fixed points of all `Γ_n`, `n ≤ N`, counted once per degree; the squarefree `Π_{p≤N}(u_p − 1)` |
| Stepanov auxiliary | `stepanovAux q f g` | `h = Σ f_i ψ_q(g_i)` |
| Corpus | `phase`, `IsReturn`, `order_le_of_rouche` (IRW); `pointCount_eq`, `riemannHypothesis_iff_bddBelow_squareDegrees` (SOSZ); `prod_pow_le_of_vanishesAlong` (EAHT) | returns, cap; point count, Stepanov side; Bézout of `𝔾_m(ℚ)` |

## 3. Language

- **Exact Frobenius**: a ring endomorphism of the auxiliaries with a fixed-point set on which it
  acts trivially. **Approximate Frobenius**: the flow at a return time, close to the identity on the
  whole torus.
- **Closed torsion point**: the Galois orbit of a torsion point; **closed point of a circle**: the
  hypersurface `u_p ∈ μ_m^{prim}`, of degree `φ(m)` and weight `log p`.
- **Integrality amplifier**: a mechanism turning smallness into exact vanishing (a nonzero algebraic
  integer has norm of modulus `≥ 1`).
- **Uniform order** at a point (all partial derivatives) versus **orbit order** (derivatives in `s`
  along the prime orbit only). Orbit order exceeds uniform order only through relations among the
  `log p`.
- **Frobenius orbit of a return**: the dilates `at`, `a < m` prime to `m`, of a return to a torsion
  point of order `m`; they are returns to its conjugates.
- **Cheap / exact**: a vanishing condition is cheap if its order is not paid in length, exact if it
  holds without approximation.

## 4. Mechanisms

1. **Galois = Adams on torsion.** `ψ_a F(μ^b) = F((μ^a)^b)`; on the `(q−1)`-torsion `ψ_q F = F`
   (`aeval_torsionPoint_adams`, `aeval_torsionPoint_adams_of_pow_eq`).
2. **The norm.** `Π_{μ prim} |G(μ)|` is the modulus of the norm of the cyclotomic integer `G(ζ_m)`:
   `0` or `≥ 1` (`one_le_prod_norm_aeval_primitiveRoots`); a closed point vanishes as a whole
   (`aeval_eq_zero_of_mem_primitiveRoots`).
3. **Lipschitz transfer.** On the unit polydisc `|F(u) − F(v)| ≤ L(F) max|u_p − v_p|`
   (`norm_aeval_sub_le`); dilates of a `δ`-return are `aδ`-returns to the conjugates
   (`norm_orbitPoint_mul_sub_le`).
4. **Transcendence separates moments.** For two primes an orbit moment is a binary form in
   `(log p, log q)` with integer power moments as coefficients (`orbitMoment_eq`); Gelfond–Schneider
   (`RHTower.log_ratio_transcendental`) separates them.
5. **Unisolvence.** Lagrange polynomials on the simplex: power moments of order `≤ D` determine a
   coefficient vector on `|α| ≤ D`, in two variables (`eq_zero_of_powerMoment_eq_zero`) and in
   `|P|` variables (`eq_zero_of_powerMomentF_eq_zero`); by the multinomial theorem an orbit moment
   is the moment form evaluated at `(log p)_p` (`orbitMomentF_eq`).
6. **Derivatives lower the degree; an integer polynomial with zero gradient is constant**
   (`totalDegree_pderiv_lt`, `eq_C_of_forall_pderiv_eq_zero`).
7. **Countability.** A nonzero integer auxiliary is a nonzero entire function (the smallest frequency
   dominates on the real axis, `exists_orbitFun_ne_zero`); there are countably many integer
   auxiliaries.
8. **Top-coefficient shift.** Multiplying by `h(u_p)` moves the top monomial up by `p^{deg h}` with
   coefficient `lc(h)·c_top` (`pow_natDegree_mul_length_le`).
9. **Class sums.** `F(μ^b) = Σ_r C_r μ^r`; equal class sums kill the closed point
   (`aeval_torsionPoint_eq_zero_of_classSum`).
10. **Jensen with an integral centre.** `|A(it + w)| ≤ H N^{|w|}` at every height
    (`norm_orbitFun_shift_le`); integrality gives centres with `|A| ≥ 1/2`.
11. **Stepanov's construction on the torsion.** `h = Σ f_i ψ_q(g_i)` with `Σ f_i g_i = 0` vanishes on
    the `(q−1)`-torsion (`aeval_stepanov_eq_zero`). For `D=X_j∂_j`, its exact jets at any Adams
    fixed point satisfy
    `D^n h = Σ_{a+b=n} binom(n,a) q^b(1−q)^a D^b(Σ_i D^a(f_i)g_i)`
    (`aeval_euler_pow_stepanov`). Both global first-order syzygies therefore force the ordinary
    derivative exactly (`aeval_pderiv_stepanov_eq_zero_of_syzygies`). With only the derivative
    syzygy, `∂_j h=ℓR` on the fixed torus and the norm threshold is `ℓ^{φ(m)}`
    (`pderiv_stepanov_eq_zero_of_lt`). Pointwise grid identities cannot replace polynomial syzygies.

    More generally, if `Σ_i E_L(f_i)g_i=0` as polynomials for every coordinate Euler word
    `L` of length below `r`, every mixed Euler jet of `h` below `r` vanishes at every Adams
    fixed point. On the fixed torus these give ordinary uniform multiplicity `r`
    (`vanishesToOrder_stepanov_of_syzygies`). Leibniz transfers each derivative between the
    two factors; no norm estimate enters. A nonzero auxiliary still has length at least `2^r`.

    The exact polynomial image is stronger: these global syzygies produce precisely
    `(u_p^q−u_p : p∈P)^r` over `ℤ`
    (`mem_adamsFixedIdeal_pow_iff_stepanov_syzygies`). Thus they impose multiplicity on the
    full affine fixed locus, including zero coordinates. For `q≥2` and nonempty prime support
    with least prime `p`, the sharp nonzero length is `p^(qr)`; the entire minimal filtered
    piece is `ℤ·(u_p^q−u_p)^r` (`minimal_stepanov_image_iff`). Integral Newton coordinates
    preserve arithmetic length and retain exactly quotient order at least `r`.
    Torsion vanishing alone costs `p^((q−1)r)`. This comparison concerns the polynomial
    auxiliary before any division by a monomial.

12. **Orbit preservation forces Adams operations.** For any finite prime set with two distinct
    primes, every complex polynomial self-map carrying the prime orbit into itself has the
    unique form `X_p↦p^(−ib)X_p^n`, with `n∈ℕ`, `b∈ℝ`
    (`preservesPrimeOrbit_iff`, `translatedAdams_eq_iff`). Constant-modulus finite spectra force
    monomials. Divisibility removes hidden period-lattice terms from the clock; the determinant
    trick and Baker independence force a common integer exponent. Over `ℤ`, common torsion
    rigidity removes the translation (`integer_endomorphism_is_adams`). The fixed orbit points
    satisfy `(n−1)t+b=0`, so any map fixing two distinct orbit points is the identity
    (`preservesPrimeOrbit_two_fixed_points`). Orbit-preserving polynomial replacements for Adams
    operations therefore cannot supply many fixed orbit points in this auxiliary algebra.

13. **Rational denominators leave only Laurent Adams maps.** On a finite prime set with two
    distinct primes, every rational self-map defined on and preserving the whole prime orbit
    has unique coordinates `p^(−ib)X_p^n`, now with `n∈ℤ`
    (`rationalPreservesPrimeOrbit_iff`, `laurentAdamsRelation_parameters_unique`).
    Locally normalized logarithms have a continuous defect in a countable period set.
    Integer logarithmic residues then force equal numerator and denominator zero divisors;
    order-one entire-quotient rigidity forces characters. Bohr coefficients and the signed
    prime-logarithm lattice force the integer exponent. Real or integer coefficients force
    `b=0` (`real_rational_preserver_is_laurentAdams`, `integer_rational_preserver_is_laurentAdams`).
    Fixed times still satisfy `(n−1)t+b=0`, so two distinct fixed orbit points force the identity
    (`rational_preserver_two_fixed_points`).

    The classification also holds in the full prime-variable algebra, with no common finite
    invariant prime set (`globalRationalPreservesPrimeOrbit_iff`). Three output primes and
    six exponentials force an algebraic clock slope; Baker independence on one coordinate's
    finite frequency support makes it an integer (`global_prime_frequency_dilation_is_int`).
    Every rational coordinate therefore reduces to its own prime power, even if its given
    numerator and denominator use other primes. Uniqueness, the fixed-point law, and real/integer
    descent persist (`globalLaurentAdamsRelation_parameters_unique`,
    `global_rational_preserver_two_fixed_points`, `global_real_rational_preserver_is_laurentAdams`,
    `global_integer_rational_preserver_is_laurentAdams`).

## 5. Questions and answers

| # | Question (§2.9) | Answer | Lean |
|---|---|---|---|
| Q1 | What is the degree-`n` Frobenius of `Spec ℤ` as a correspondence, and what are its fixed points? | As a correspondence it is the Hecke graph `Γ_n` of `x ↦ nx`; its fixed points are the closed orbits of length `log n` (the prime `p` with weight `log p` if `n = pᵏ`), the cusp and the archimedean fixed point (jets): `Γ_1·Γ_n = Λ(n) + 1 + 1/(n²−1)` (SOSZ). Its **exact** form as a ring endomorphism of the integer auxiliaries is the Adams operation `ψ_a`: on torsion points it is the Galois action of `ℚ(μ_m)`, fixing the `(q−1)`-torsion pointwise (`x^q = x` in characteristic zero); on the prime orbit it is the dilation `t ↦ at`, whose only fixed point is `t = 0` — two primes have no common torsion return. The orbit returns to every torsion point at arbitrarily large heights. | `aeval_torsionPoint_adams`, `aeval_torsionPoint_adams_of_pow_eq`, `orbitValue_adams`, `eq_zero_of_torsion_return`, `exists_torsion_return`; `SurfaceOfSpecZ.pointCount_eq` |
| Q2 | What is the Lefschetz identity for `Γ_1·Γ_n` with its main term? | Fixed-point form: `Γ_1·Γ_n = Λ(n) + 1 + 1/(n²−1)` — prime fixed points of index `log p`, the cusp, the archimedean index (the even Lefschetz trace of the dilation of `ℝ`); main term `n + 1`, the `𝔽₁`-line. **Lefschetz = Stepanov**: the prime Lefschetz numbers of all `Γ_n`, `2 ≤ n ≤ N`, add up to the degree of the minimal integer auxiliary vanishing at their fixed points, `Σ_{2≤n≤N}(Γ_1·Γ_n − 1 − 1/(n²−1)) = ψ(N) = log N(A_N)`, `N(A_N) = lcm(1,…,N)`, as `deg(x^{qⁿ} − x) = qⁿ` counts the points of degree dividing `n`; on the orbit `A_N(s) = Π_{p≤N}(p^{-s} − 1)^{⌊log_p N⌋}`. The **main term** of the summed identity is `N`, and the arithmetic Stepanov bound is the upper bound `log N(A_N) ≤ N + C√N(log N)²`, equivalent to RH (also with the squarefree auxiliary of degree `θ(N)`). | `log_length_fixedPointAux_eq_sum_lefschetz`, `length_fixedPointAux`, `log_length_fixedPointAux`, `orbitFun_fixedPointAux`, `lcmUpto_le_length_of_dvd`, `riemannHypothesis_iff_log_length_fixedPointAux_le`, `riemannHypothesis_iff_log_length_primeAux_le`; `SurfaceOfSpecZ.pointCount_eq`, `archLevyDensity_eq_even_trace` |
| Q3 | Which auxiliary integer Dirichlet polynomials vanish at all fixed points, to what order, of what degree? | **Closed points of the circles** (exact fixed points on the orbit): vanishing to order `J` along the closed point of degree `φ(m)` of the circle of `p` is divisibility by `Φ_m(p^{-s})^J`, and then `Π p^{φ(m)J} ≤ N` — sharp, attained by `Φ_m(p^{-s})^J`. **Closed torsion points of the torus**: `m − 1` integer conditions with coefficients in `{−1,0,1}` each; Siegel gives auxiliaries of height `\|S\|^{M/(\|S\|−M)}`. **All `(q−1)`-torsion points at once**: Stepanov's `h = Σ f_i ψ_q(g_i)` with the single identity `Σ f_i g_i = 0`; ordinary order at least two if the additional polynomial identities `Σ (∂_j f_i) g_i = 0` hold for every coordinate, without a norm bound. **Order at any point** (uniform): at most the total degree, so order `J` needs length `2^J`. **The common fixed point `s = 0`**: for any `P`, orbit order `J` forces a term `n_α ≥ 2^J` unless the `log p` satisfy a nonzero integer homogeneous relation of degree `< J`; for two primes there is none (Gelfond–Schneider), and the bound is sharp at `(2^{-s} − 1)^J`; real coefficients reach order `≍ (log N)²/(2 log p log q)`. | `stepanov_count_closedPoints`, `length_circlePoly`, `orbitFun_circlePoly_mul`, `exists_siegel_auxiliary`, `aeval_stepanov_eq_zero`, `aeval_pderiv_stepanov_eq`, `two_pow_le_length_of_vanishesToOrder`, `exists_two_pow_le_or_relation`, `exists_two_pow_le_of_orbitMoment_eq_zero`, `orbitMoment_binomial_eq_zero` |
| Q4 | When does integrality force a `δ`-small auxiliary to vanish exactly at a return of the prime orbit? | **Never at a generic return**: the heights at which some nonzero integer auxiliary on `P` vanishes are countable, and every return window contains heights outside them. **On the torus, at torsion returns**: if `A` is small along the Frobenius orbit `{at}` of a `δ`-return to `μ^b`, `Π_a(\|A(iat)\| + aδL) < 1`, then `F` vanishes exactly on the closed point; precision `δ ≤ 1/(4mL)` suffices, with no factorial; the threshold `1` is sharp. Contrapositively, integer auxiliaries are not small along Frobenius orbits: at sign returns `\|A(it)\| ≥ 1 − δL`. **At `s = 0`**: integrality makes orders `0` and `1` exact (`\|A'(0)\| < 1/H` forces `A'(0) = 0`); a vanishing orbit moment of order `d` is a block of vanishing integer power moments or a relation of degree `d` among the `log p`, so for two primes every order is exact (Gelfond–Schneider). **On progressions**: small integer auxiliaries are divisible (EAHT). | `countable_setOf_exists_orbitValue_eq_zero`, `exists_return_forall_orbitValue_ne_zero`, `eq_zero_of_small_on_frobeniusOrbit`, `eq_zero_of_frobeniusOrbit_le_half`, `norm_amplifier_threshold_sharp`, `one_le_prod_frobeniusOrbit`, `one_sub_le_norm_orbitValue`, `firstMoment_eq_zero_of_lt`, `firstPowerMoment_eq_zero`, `powerMomentF_eq_zero_or_relation`, `powerMoment_eq_zero_of_orbitMoment_eq_zero`; `EffectiveArithmeticHodgeTheory.vanishesAlong_of_small` |

## 6. Tools

| # | Tool (§2.9) | Built | Module |
|---|---|---|---|
| T1 | Siegel lemmas for Dirichlet polynomials on smooth numbers | nonzero integer auxiliary on any exponent set `S` vanishing on prescribed closed torsion points of orders `m_i`, height `\|S\|^{M/(\|S\|−M)}`, `M = Σ(m_i − 1)`; at every `δ`-return to them `\|A\| ≤ δ L(F)` | `SiegelAuxiliariesOnTheTorsion` |
| T2 | zero estimates in many logarithms, uniform in their number | `\|A(it + w)\| ≤ H N^{\|w\|}` at every height; at a sign return (or some Frobenius dilate of a torsion return) where `F` does not vanish, the zeros of `A(it + ·)` in `\|w\| ≤ r` number at most `(log 2H + 2r log N)/log 2`, independent of `\|P\|` and of the number of terms | `TheZeroEstimateAtTheReturns` |
| T3 | integrality amplifier | the norm amplifier on closed torsion points, at every uniform order; its orbit form at Frobenius orbits of returns; its `ℓ`-adic form on Stepanov's auxiliary, threshold `ℓ^{φ(m)}`; its price: order `J` needs length `2^J` | `TheFrobeniusOfTheTorsionIsGalois`, `StepanovsConstructionOnTheTorsion`, `ExactVanishingCostsTheDegree` |
| T4 | Lefschetz fixed-point form of Frobenius-graph intersections | the summed fixed-point formula as a Stepanov degree: `Σ_{n≤N}` prime Lefschetz numbers `= log N(A_N)`, with `A_N` minimal among auxiliaries vanishing at the same fixed points to the same orders; closed-point auxiliaries `Π_p(u_p − 1)^{κ(p)}` have length exactly `Π_p p^{κ(p)}`; length is multiplicative on circle factors | `TheLefschetzNumbersAreStepanovDegrees` (on `SurfaceOfSpecZ.pointCount_eq`) |
| T5 | Stepanov counting `#fixed·J ≤ deg A` | `Σ_{(p,m,J)} φ(m) J log p ≤ log N` over closed points of the prime circles; sharp; for the fixed points of the Frobenius graphs of degree `≤ N` the count is `ψ(N) ≤ log N(F)` | `TheStepanovCountOfTheClosedPoints`, `TheLefschetzNumbersAreStepanovDegrees` |

## 7. Criteria and milestones

| Item (§2.9) | Answer | Lean |
|---|---|---|
| C1 reproduce Stepanov–Bombieri over `𝔽_q` as the finite-rank case | Stepanov's construction runs verbatim on the torsion of the prime torus with the Adams operation as Frobenius; reduced modulo `ℓ` it is the construction over `𝔽_ℓ`, inseparability included, and the archimedean threshold of the `ℓ`-adic amplifier is then void. The count over `𝔽_q` is in the corpus for hyperelliptic curves and character sums | `aeval_stepanov_eq_zero`, `map_adams_eq_pow`, `map_pderiv_adams_eq_zero`, `pderiv_stepanov_eq_zero_of_lt`; `RHTower.Stepanov.stepanov_count`, `ArithmeticKreinLangerTheory.stepanov_order_hyperelliptic` |
| C2 crude bound with a constant at every integer degree, or on the squares | the main conjecture, in two equivalent exact forms: `c_B(log n²) ≥ −K`, and the Stepanov degree bound `log N(A_N) ≤ N + C√N(log N)²`; each is equivalent to RH | `riemannHypothesis_iff_log_length_fixedPointAux_le`; `SurfaceOfSpecZ.riemannHypothesis_iff_bddBelow_squareDegrees` |
| C3 use the Euler product and the FE; fail on one-offs, `cosh` models, the heat family | The Stepanov degree bound is formulated through the fixed points of the Frobenius graphs, i.e. through the Euler product of `ζ`; `cosh` models and the heat family have no Euler product and no fixed points. It **fails on the integer-norm one-off** (an Euler product over integer norms, continued past `½`, zeros `3/5 ± i`, no FE) for every constant, and **holds on the real one-off** (zero `3/5`): it uses more than the Euler product and is blind exactly to real zeros, like the Stepanov side over `𝔽_q`. The integrality mechanisms of §4 do not involve the coefficients of `ζ`; they hold for every Euler product over the rational primes, so they are tools, not the separating input | `one_off_violates_stepanov_bound`, `real_one_off_satisfies_stepanov_bound`, `riemannHypothesis_iff_log_length_primeAux_le` |
| C4 beat the precision cap by exact vanishing | on the torus: the norm amplifier gives exact vanishing on closed torsion points at precision `δ ≍ 1/(mL)`, independent of the order. On the orbit exact vanishing is confined to countably many heights, and exact order costs length `2^J` at every torus point and at the fixed point `0` | `eq_zero_of_frobeniusOrbit_le_half`, `countable_setOf_exists_orbitValue_eq_zero`, `two_pow_le_length_of_vanishesToOrder`, `exists_two_pow_le_or_relation` |
| M1 Lefschetz identity on the smoothed graphs | the fixed-point formula and its summed form `ψ(N) = log N(A_N)` | `log_length_fixedPointAux_eq_sum_lefschetz`; `SurfaceOfSpecZ.smoothedPrime_add_smoothedArchPole_eq_orbitCorr` |
| M2 amplifier at returns of `k` fixed primes, order `J ≫ k log N` | answered negatively, with the exact price: integer auxiliaries reach exact order `J` at a point only with length `2^J`, so `J ≤ log N/log 2`; at the fixed point `0` the same holds for two primes, and for `k` primes unless the `log p` satisfy a homogeneous relation of degree `< J`; real coefficients reach order `≍ (log N)²` but only approximately | `two_pow_le_length_of_small`, `exists_two_pow_le_of_orbitMoment_eq_zero`, `exists_two_pow_le_or_relation` |
| M3 amplifier with `k → ∞` at the rate the squares need | the torus amplifier needs precision `1/(mL)` independent of `k`; the height of a `δ`-return of `k` primes is the constant-precision first-return problem B97 | `eq_zero_of_frobeniusOrbit_le_half`, `exists_torsion_return` |
| M4 `\|c_B(log k²)\| ≤ k^{2σ}`, `σ < ½` | a zero-free strip: quasi-RH | `SurfaceOfSpecZ.zetaZeroWidth_le_iff_crude_integerDegrees` |
| M5 constant `K` | RH | `riemannHypothesis_iff_log_length_fixedPointAux_le` |

## 8. Pillar theorems

| Theorem | Lean |
|---|---|
| The norm bound and the closed-point law | `one_le_prod_norm_aeval_primitiveRoots`, `aeval_eq_zero_of_mem_primitiveRoots`, `norm_amplifier`, `norm_amplifier_threshold_sharp` |
| Galois = Adams on torsion; `x^q = x` on the `(q−1)`-torsion | `aeval_torsionPoint_adams`, `aeval_torsionPoint_adams_of_pow_eq` |
| The Frobenius on the orbit is the dilation; no common torsion return | `orbitValue_adams`, `eq_zero_of_torsion_return` |
| All polynomial orbit preservers are translated Adams; integral endomorphisms are exactly Adams; two fixed orbit points force identity | `preservesPrimeOrbit_iff`, `integer_endomorphism_is_adams`, `preservesPrimeOrbit_two_fixed_points` |
| Rational orbit preservers are uniquely translated Laurent Adams, both on finite prime sets with at least two primes and on the full prime algebra; real/integer coefficients remove translation | `rationalPreservesPrimeOrbit_iff`, `globalRationalPreservesPrimeOrbit_iff`, `globalLaurentAdamsRelation_parameters_unique`, `global_real_rational_preserver_is_laurentAdams`, `global_integer_rational_preserver_is_laurentAdams` |
| Torsion returns exist at every height | `exists_torsion_return` |
| Norm amplifier on the torus and on Frobenius orbits of returns | `torus_norm_amplifier`, `vanishesToOrder_of_small`, `eq_zero_of_small_on_frobeniusOrbit`, `one_le_prod_frobeniusOrbit`, `eq_zero_of_frobeniusOrbit_le_half` |
| No exact vanishing at generic returns | `countable_setOf_exists_orbitValue_eq_zero`, `exists_return_forall_orbitValue_ne_zero` |
| Repulsion at sign returns | `one_sub_le_norm_orbitValue` |
| Bézout at the common fixed point (two primes), sharp | `exists_le_of_orbitMoment_eq_zero`, `exists_two_pow_le_of_orbitMoment_eq_zero`, `orbitMoment_binomial_eq_zero` |
| Integrality at `s = 0` through order two, any `P` | `firstMoment_eq_zero_of_lt`, `firstPowerMoment_eq_zero` |
| The excess order at `s = 0` is a relation among the logarithms, any `P` | `orbitMomentF_eq`, `powerMomentF_eq_zero_or_relation`, `eq_zero_of_powerMomentF_eq_zero`, `exists_large_or_relation`, `exists_two_pow_le_or_relation` |
| Exact order costs the degree, any point, any `P` | `le_totalDegree_of_vanishesToOrder`, `two_pow_le_length_of_vanishesToOrder`, `two_pow_le_length_of_small` |
| Stepanov count of the closed points of the prime circles, sharp | `stepanov_count_closedPoints`, `prod_pow_mul_length_le`, `length_circlePoly` |
| Siegel's lemma on smooth numbers | `exists_siegel_auxiliary`, `norm_orbitValue_le_of_siegel` |
| Lefschetz = Stepanov: the prime Lefschetz numbers of degree `≤ N` are the degree `ψ(N)` of the minimal fixed-point auxiliary; length is multiplicative on circle factors | `log_length_fixedPointAux_eq_sum_lefschetz`, `length_fixedPointAux`, `length_circleProduct`, `prod_pow_le_length_of_dvd`, `orbitFun_fixedPointAux` |
| The arithmetic Stepanov bound in exact form is RH | `riemannHypothesis_iff_log_length_fixedPointAux_le`, `riemannHypothesis_iff_log_length_primeAux_le` |
| Calibration: the bound fails on the integer-norm one-off, holds on the real one-off | `one_off_violates_stepanov_bound`, `real_one_off_satisfies_stepanov_bound` |
| Stepanov's construction on the torsion; inseparability at `ℓ`; the `ℓ`-adic amplifier | `aeval_stepanov_eq_zero`, `map_adams_eq_pow`, `map_pderiv_adams_eq_zero`, `aeval_pderiv_stepanov_eq`, `pderiv_stepanov_eq_zero_of_lt` |
| Zero estimate at returns, uniform in the number of logarithms | `norm_orbitFun_shift_le`, `zeroCount_le_of_half_le`, `zeroCount_le_of_sign_return`, `exists_dilate_zeroCount_le` |

All are unconditional.

## 9. Traps

| Trap | Truth |
|---|---|
| Rational coordinates can introduce new primes and thereby preserve the full prime orbit while fixing many of its points | even without a finite invariant prime set, every rational map defined on the whole orbit and preserving it is translated Laurent Adams; any nonidentity one fixes at most one orbit point |
| Returns are fixed points of a Frobenius | at a return the flow is close to the identity on the whole torus; the only exact fixed points common to all primes are torsion points (off the orbit) and `t = 0`; each prime has its own, the closed points of its circle |
| Integrality turns forced near-vanishing at returns into zeros | only countably many heights carry a zero of any nonzero integer auxiliary; every return window avoids them |
| The norm amplifier lifts the precision cap on the orbit | it gives exact vanishing at the torsion point, off the orbit; the orbit passes at distance `δ` and the zero copied to it is a Rouché copy, capped as before |
| High order at a point is cheap with integer coefficients | uniform order is at most the total degree, so order `J` costs length `2^J`; for two primes the same holds for orbit order at `0` |
| Real-coefficient auxiliaries are as good as integer ones | they reach orbit order `≍ (log N)²` at `0` but only approximately at returns; integer ones are exact and pay `log₂ N` per order |
| Vanishing at the exact fixed points of `ℤ` can be cheap | along a closed point of degree `φ(m)` on the circle of `p` it costs `p^{φ(m)}` per order, exactly; the count is Chebyshev's |
| `ℓ`-adic Frobenius congruences give a Stepanov count | on the torsion they give Stepanov's multiplicity `ℓ`-adically, with an archimedean threshold `ℓ` per conjugate that the auxiliary does not meet; on integers they give factorial auxiliaries, whose prime counts are fixed by Stirling's formula and see no zero |
| An integrality mechanism on the prime torus can separate `ζ` from fakes | the integrality mechanisms do not involve the coefficients of `ζ` and hold for every Euler product over the rational primes; what separates is the Stepanov degree bound itself, which fails on the integer-norm one-off |
| The Stepanov degree bound is a two-sided statement | it is an upper bound only; the real one-off satisfies it, as the Stepanov side over `𝔽_q` misses a real eigenvalue `> √q` |
| Torsion returns place the zero-estimate centres where needed | they sit at heights fixed by simultaneous approximation of `log p`; their height is the first-return problem |

## 10. What the field reduces the Stepanov step to

The agenda of §2.9 — Q1–Q4, T1–T5, criteria C1–C4, milestones M1–M3 — is answered and built (§5–§7).
The statements below are not open topics of the programme but the classical problems it reduces the
Stepanov step to, each with its strength fixed by a theorem; no unconditional argument in the corpus
or the literature decides them.

| Statement | Proved relation | Boundary |
|---|---|---|
| **The Stepanov degree bound** `log N(A_N) ≤ N + C√N(log N)²` (equivalently `c_B(log n²) ≥ −K`) | equivalent to RH (`riemannHypothesis_iff_log_length_fixedPointAux_le`; SOSZ) | fails on the integer-norm one-off, holds on the real one-off (`one_off_violates_stepanov_bound`, `real_one_off_satisfies_stepanov_bound`); the Stepanov side alone is blind exactly to real zeros (SOSZ) |
| **A coupling of the torsion Frobenius to the prime orbit**: an identity relating values of integer auxiliaries at torsion points to their zeros on the orbit, with error below the Rouché cap | would give exact vanishing at returns with cheap order | exact vanishing on the orbit is impossible at generic heights (`countable_setOf_exists_orbitValue_eq_zero`); exact order costs `log₂ N` per order at every point (`two_pow_le_length_of_vanishesToOrder`); approximate copies are capped (`order_le_of_rouche`); the derivative-syzygy norm amplifier has threshold `ℓ` per conjugate (`pderiv_stepanov_eq_zero_of_lt`); combined polynomial syzygies already force exact derivative vanishing (`aeval_pderiv_stepanov_eq_zero_of_syzygies`), still paid in degree — the coupling must be inseparable at the archimedean place |
| **Relations among `log p`** for three or more primes | an integer auxiliary of orbit order `J` at `0` has a term `≥ 2^J` unless `LogRelation P d` for some `d < J` (`exists_two_pow_le_or_relation`); for two primes `LogRelation` never holds (`exists_two_pow_le_of_orbitMoment_eq_zero`, Gelfond–Schneider) | algebraic independence of logarithms of primes (a consequence of Schanuel's conjecture) [C] |
| **Heights of torsion returns** (M3) | the amplifier needs precision `1/(mL)` independent of `k` | the first `δ`-return of `k` primes is B97 (`TailArithmeticOfThePrimeOrbit`, `PrimeTorusTheory`) |

## 11. Context

| Programme | Interface |
|---|---|
| SurfaceOfSpecZ | integer-degree Hasse–Weil, point count and its indices (used by `TheLefschetzNumbersAreStepanovDegrees`), Stepanov side at the squares, smoothed kernels |
| ArithmeticPositiveDuality | the integer-norm one-off and its prime oscillation (the calibration of C3) |
| InfiniteRankWeilTheory | self-improvement on thick sets, returns, freezing, forced vanishing, the precision cap |
| EffectiveArithmeticHodgeTheory | Bézout and Riemann–Roch of `𝔾_m(ℚ)` along progressions (the closed point `m = 1`), divisibility of small integer auxiliaries |
| ArithmeticKreinLangerTheory, ArithmeticOfSquareRootPrecision | factorial (`ℓ`-adic) auxiliaries, their producers and obstructions; Chebyshev ledger |
| RHTower | Gelfond–Schneider, Baker, Stepanov over `𝔽_q`, Jensen zero counts, countability of zeros |
| HTGeometry | Kronecker density and recurrence, prime-log independence, norms of cyclotomic integers |
| PrimeTorusTheory, TailArithmeticOfThePrimeOrbit | torsion avoidance at large heights, returns, precision law |
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | scaling surface, Hecke and Adams operations, Lefschetz identities, curve data |

## 12. Success criteria and contributions

ALST succeeds when Q1–Q4 have theorem-level answers, T1–T5 exist in their strongest unconditional
form in the programme, each criterion is met or shown impossible for a named mechanism with its
strongest positive survivor, the main conjecture has an exact form calibrated on the fakes, and the
Stepanov step is reduced to precise statements whose strength is fixed by theorems. That state is
reached (§5–§7, §10).

A **contribution** must be unconditional; say which of (S1), (S2), (S3) it realizes over `ℤ` and at
which place; say whether its vanishing is exact or approximate and at which points (orbit, torus,
circle, progression); price its order in length; and say whether it separates `ζ` from the
integer-norm one-off. A proposed Frobenius over `ℤ` must name its fixed points and show that it is
a ring endomorphism of the auxiliaries.

## 13. Big picture

Over `𝔽_q` Stepanov's count works because one operation is three things at once: a ring
endomorphism, the identity on the points, and inseparable. Over `ℤ` the three come apart. The ring
endomorphism exists (the Adams operations) and is the identity exactly on the torsion of the prime
torus, where it is the Galois action and the norm turns smallness into exact vanishing — a genuine
characteristic-zero Frobenius with an integrality amplifier. But the torsion is off the prime orbit,
which meets it only at its single fixed point, and inseparability is absent at the archimedean place:
every exact order costs a unit of `log₂ N` at every point of the torus, and at the fixed point
of the orbit unless the `log p` satisfy an algebraic relation (never for two primes). On the orbit
itself integer auxiliaries vanish at only countably many heights; at the returns integrality is a
repulsion, not a source of zeros. What the product formula counts with exact vanishing — the closed
points of the prime circles — it counts at Chebyshev's price.

Arbitrary rational denominators and coordinatewise introduction of new primes do not change
the fixed-point obstruction. On the full prime orbit, every globally defined orbit-preserving
rational map has coordinates `p^(−ib)X_p^n`, with one integer exponent and one real translation.
Real or integer coefficients remove the translation. Denominators add negative exponents,
while fixed times remain `(n−1)t+b=0`; two distinct fixed orbit points force the identity.

On the complete order-`q` torsion locus the price is more rigid: for an allowed prime set with
least prime `p`, multiplicity `r` costs length `p^(qr)`, and every integer auxiliary at that
threshold is exactly `c(u_p^q − 1)^r` (`minimal_torsion_auxiliary_iff`). Minimal auxiliaries use
only the least prime; adding more prime coordinates creates no additional minimizers. Fourier
extraction detects the remainder after removing this single binomial.

The entire torsion kernel has integral Newton coordinates:
`B_a = ∏_p u_p^(a_p mod q)(u_p^q−1)^(a_p div q)` form a basis over `ℤ`.
Full multiplicity `r` retains exactly the indices with `Σ_p floor(a_p/q) ≥ r`;
length at most `N` retains exactly those with `weight(a) ≤ N`
(`filtered_torsion_kernel_iff_unique_expansion`). Synthesis preserves length
exactly. Consequently, complex vanishing to order `r` on the full grid is
precisely membership in the ordinary power `J_q^r` over `ℤ`, where
`J_q = (u_p^q−1 : p∈P)` (`fullTorsionMultiplicity_iff_mem_gridIdeal_pow`).
There is no denominator obstruction to integral descent on this grid.

Integral torsion interpolation has an exact length cost. Removing Newton
coordinates of quotient order at least `r` gives the unique reduced
representative modulo `J_q^r`, and it minimizes length in its class. For
nonempty prime support and `r>0`, every integral class has a representative
of length at most `N` exactly when
`N ≥ (∏_p p^(q−1)) p_max^(q(r−1))`
(`universal_torsion_interpolation_iff_cutoff`). The least prime controls the
first nonzero vanishing auxiliary; the largest prime controls the last
necessary interpolation coordinate. Order zero has cutoff `0`; empty prime
support at positive order has cutoff `1`.

The two halves of Weil's proof meet exactly at the fixed points: the prime Lefschetz numbers of the
Frobenius graphs of degree `≤ N` are the degree of the minimal integer auxiliary vanishing at their
fixed points, `ψ(N) = log lcm(1,…,N)`, the analogue of `deg(x^{qⁿ} − x) = qⁿ`. RH is then the
Stepanov degree bound `log N(A_N) ≤ N + O(√N log²N)` — an upper bound on the degree of one explicit
integer auxiliary — which the integer-norm one-off violates and the real one-off satisfies.

So each ingredient of Stepanov's method available over `ℤ` — the exact Frobenius, integrality, the
product formula, `ℓ`-adic inseparability — is located and priced, and none of them yields cheap exact
vanishing on the prime orbit, which is what the arithmetic Stepanov bound (RH) would need. A proof
along this line needs an identity coupling the exact torsion Frobenius to zeros on the orbit
that behaves inseparably at the archimedean place — the one ingredient of Stepanov's method that
characteristic zero lacks — and that uses the coefficients of `ζ`, since every mechanism built here
holds for all Euler products over the rational primes.
