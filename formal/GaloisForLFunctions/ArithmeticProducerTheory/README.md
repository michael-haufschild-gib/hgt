# Theory of Arithmetic Producers (TAP)

Namespace `GaloisForLFunctions.ArithmeticProducerTheory`; umbrella `ArithmeticProducerTheory.lean`.
Specification: §2.9 of the [review-2011 obstacles summary](../../../docs/reports/review-2011/obstacles-summary.md).
Every statement with a Lean name is a theorem, of this folder unless a neighbour is named. Every
theorem is unconditional; RH and zero-free strips appear only inside implications and equivalences.
Statements under "Open" are not theorems.

## 1. Motivation

The corpus has turned almost every route to RH into an exact statement about `Θ`, the supremum of
the real parts of the zeros of `ζ`. A quantity that reads `Θ` exactly is a **meter**. A meter has
no slack: a bound for it is as hard as the statement it reads. A proof needs a **producer**: a
construction made from integers and primes without reference to zeros, and a comparison of two
sizes of that construction which forces a one-sided bound for a signed remainder, at an exponent
that a proved one-sided ⇒ strip implication converts into a zero-free region.

Producers are known in few places.

| Where | Construction | Comparison | What pays |
|---|---|---|---|
| Curves over `𝔽_q` (Stepanov, Bombieri) | auxiliary `Σ f_i g_i^q` | degree ≥ multiplicity × number of fixed points | inseparability: `d(g^q) = 0` |
| Curves over `𝔽_q` (Weil) | Frobenius correspondence | Castelnuovo positivity | the Hodge index of the surface |
| Kummer and Fermat curves (Jacobi) | Jacobi sums | conjugation pairing = polarization pairing | complex conjugation of `ℚ(ζ_m)` |
| `ℤ` (Chebyshev) | binomial coefficients | carries at the primes ≤ entropy | the real place |
| `ℤ` (Gelfond, Schnirelman, Nair) | `lcm(1,…,n+1) · ∫₀¹ P` for `P ∈ ℤ[X]` | a positive integer is `≥ 1` | the real place: the sup norm of `P` |
| `ℤ` (Selberg) | squared weights `(Σ_{d∣n} λ_d)²` | the indicator of the primes is at most the square | a factor `2` |
| `ℤ` (Hadamard, de la Vallée Poussin, mean values) | `ζ` on `Re s ≥ 1` | positivity of a trigonometric polynomial | stops at a strip of width zero |
| `ℤ[ω]` (the detector strip) | a detector with cubic probes over `ℚ(ω)` | principal signal against a Gram bound | stops at `Re s = 20999/24000` |

TAP is the theory of such comparisons over `ℤ`: which exist, what they cost, at which place the
cost is paid, and which twins they separate. Its aim is a producer that meets the four criteria of
§12, or the proof that a named class of constructions contains none, together with the strongest
positive statement the obstruction leaves.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Prime torus and Adams operations | `MvPolynomial.expand a` on `R[X_σ]` | coordinates `X_p`; `ψ_a : X_p ↦ X_p^a`; on a Dirichlet polynomial `[n] ↦ [n^a]`; in characteristic `p`, `ψ_p` is the Frobenius |
| Order of an operator | `HasOrderLE k D` | Grothendieck order: iterated commutators with multiplications vanish |
| Local operator | `IsLocal D` | `(Df)(c)` vanishes when `f` vanishes to high order at `c` |
| Diagonal operator | `diag s` | `X^n ↦ s(n) X^n`; the Euler derivation `X∂` is `s(n) = n` |
| Digit operators | `digitOp a i k`, `quotOp a i K` | `s(n) =` the `k`-th digit of `n_i` in base `a`; the quotient by `a^K` |
| Hasse–Euler operator | `hasseEuler i m` | `X^m ∂^m/m!`, symbol `binom(n, m)` |
| Compatible derivation | `IsCompatible a c D` | `D ∘ ψ_a = c · ψ_a ∘ D`; `c` is the **Frobenius scalar** |
| Point and fibre ideals | `pointIdeal c`, `fibreIdeal a c` | functions vanishing at `c`; functions vanishing on the fibre `{w : w^a = c^a}` of `ψ_a` |
| Carry of a derivation | `derivationCarry L m n` | `(m+n)L(m+n) − mL(m) − nL(n)` for completely additive `L` |
| Entropy carry | `entropyCarry x y` | the carry of `x ↦ x log x`: `(x+y)log(x+y) − x log x − y log y` |
| Sections of degree `≤ d` on `k` primes | `simplexPoints k w d` | exponent vectors with `Σ α_i w_i ≤ d`; for `w_i = log p_i` the integers `Π p_i^{α_i} ≤ e^d` |
| Smooth integers | `RHTower.Sieve.smoothUpTo S N` | the integers of `[1, N]` whose prime factors lie in `S` |
| Dilation kernel, gain | `dilationGain t a λ s` | `K f(x) = Σ_j a_j f(λ_j x)`, `ρ(s) = Σ_j a_j λ_j^s` |
| Barycentric stencil | `IsBarycentric t a λ` | positive weights of sum `1`, barycentre `1`, at least two scales |
| Gap of the prime error | `primeErrorGap t a λ x` | `V(x) − Σ_j a_j V(λ_j x)`, `V = θ − x` |
| Zero abscissa | `RHTower.zetaZeroAbscissa` | `Θ` |
| Kummer points, Jacobi sums | `puncturedKummerPoints`, `jacobiSum` | `z^{n+1} = c · x(1−x)^a` over a finite field |
| Symmetric Frobenius | `SymmetricFrobenius G V`, `IsEigen χ v` | a Frobenius on a complex space with a pairing it scales by `q`, a conjugation and a symmetry group `G`, all commuting; the `χ`-eigenspace of `G` |

## 3. Language

- **Producer.** A *construction* (an integer, a polynomial, a section), a *reading* (its arithmetic
  size, linear in `Λ` by unique factorization), a *price* (a second size computed by another
  mechanism), a *comparison* (reading ≤ price), and a *landing* (a proved one-sided ⇒ strip
  implication applied to the resulting bound).
- **Slack.** Price minus reading. *Comparison slack* is lost in the inequality between the two sizes;
  *reading slack* is lost when the reading is replaced by the remainder one wants.
- **Meter.** A remainder whose one-sided growth exponents are exactly `Θ`.
- **Gain, contraction, neutral exponent.** A kernel contracts at `s` if `ρ(s) < 1`; `s` is neutral
  if `ρ(s) = 1`. A one-sided bound passes through a kernel exactly at contracting exponents.
- **Priced.** A reading is priced if its value is known in closed form to `O(log)`.
- **Circular.** A price is circular if it is computed from `ψ`, from `M`, or from the zeros.
- **Free multiplicity.** Vanishing order obtained below the cost of that many simple zeros.
- **Fat point, fibre.** In characteristic `p` the fibre of the Frobenius over a point is the point
  with multiplicity `p`. Where `a` is invertible the fibre of `ψ_a` is `a` distinct points.
- **Carry.** The failure of a multiplicative derivation to be additive.
- **Axiom level, twin.** The list of properties of `ζ` an argument uses; a twin shares the list and
  violates the conclusion. An argument is **selective** if one of its steps fails for the twin.

## 4. Mechanisms

1. **Locality and Frobenius-linearity exclude each other.** Stepanov's method needs an operator that
   measures vanishing at a point and is linear over the image of the Frobenius. A differential
   operator of finite order on `R[X_σ]` which is linear over `ψ_a(R[X_σ])`, with `a` regular in `R`,
   is a multiplication (`HasOrderLE.eq_mul_of_expand_linear`); `∂_i` is `ψ_a`-linear iff `a = 0` in `R`
   (`pderiv_expand_linear_iff`). Over an infinite domain the pointwise-local operators are the
   differential operators (`isLocal_iff_hasOrderLE`), so a local `ψ_a`-linear operator is a
   multiplication (`IsLocal.eq_mul_of_expand_linear`).
2. **The Frobenius scalar is the degree.** `D ∘ ψ_a = c · ψ_a ∘ D` holds iff `D` is an Euler
   derivation `Σ r_i X_i ∂_i` with `c r_i = a r_i` (`isCompatible_iff`); over a domain `c = a`
   (`IsCompatible.scalar_eq`). At a prime `p | a` the scalar is small; at the real place it is
   `a > 1`. By the product formula the gain at the finite places equals the loss at `∞`.
3. **The Frobenius-linear operators over `ℤ` are the digit operators.** `digitOp a i k` is
   `ψ_{a^{k+1}}`-linear over every ring (`digitOp_expand_mul`), the Euler derivation is
   `Σ_k a^k · digitOp_k + a^K · quotOp_K` (`euler_eq_sum_digitOp`), and in characteristic `p` the
   digit operator is the Hasse–Euler operator `binom(X∂, p^k)` (`digitOp_eq_hasseEuler`, Lucas).
   Where `a` is regular it has no finite order (`not_hasOrderLE_digitOp`).
4. **The fibre replaces the fat point.** The `ψ_a`-periodic diagonal operators annihilate `f` at `c`
   iff `f` lies in the fibre ideal `(X_i^a − c_i^a)` (`mem_fibreIdeal_iff`, `fibreIdeal_eq_span`); in
   characteristic `p` this ideal is `((X_i − c_i)^p)` (`fibreIdeal_eq_span_pow_of_charP`). Over `𝔽_q`
   one condition buys multiplicity `p`; over `ℤ` the same conditions buy `a` simple zeros at `a`
   distinct points, and the count of zeros against degree gains nothing.
5. **The balance of carries.** At `p` the Fermat quotient has an integral carry
   (`prime_dvd_add_pow_sub`). At the real place the power maps `x ↦ x^a` approach the identity and
   their generator is `x ↦ x log x`, whose carry is the entropy (`hasDerivAt_powerCarry`), between
   `0` and `(x+y) log 2` (`entropyCarry_nonneg`, `entropyCarry_le`). The carries of `m + n` at the
   finite places, weighted by `log p`, equal `log binom(m+n, m)` (Kummer) and
   `E(m,n) − log(m+n+1) ≤ log binom(m+n, m) ≤ E(m,n)`
   (`log_choose_le_entropyCarry`, `entropyCarry_sub_log_le_log_choose`; in one statement
   `abs_sum_factorization_choose_sub_entropyCarry_le`). This is the product formula for the
   binomial coefficient, read as a balance between the carries at the finite places and the carry
   at the real place. It is Chebyshev's comparison; its slack is logarithmic.
6. **Rigidity of the archimedean derivation.** A completely additive `L` whose carry is bounded
   below by `−K(m+n)` is `c · log` (`eq_mul_log_of_carry_ge`, `carry_bddBelow_iff`); for every other
   weighting of the primes the carry is unbounded in both directions on the linear scale
   (`exists_carry_lt_and_gt`). With mechanism 2: among the derivations compatible with the Adams
   operations, one free weight per prime, the only one with an entropy is `d/ds`.
7. **Riemann–Roch on a finite prime torus.** The number `N(d)` of sections of degree `≤ d` on `k`
   primes satisfies `d^k ≤ k! · Π w_i · N(d) ≤ (d + Σ w_i)^k` (`card_simplexPoints_bounds`): the
   leading constant is `1/(Γ(k+1) Π log p_i)`. Sections with all coordinates positive are the
   sections of degree `d − Σ w_i` (`card_filter_pos_simplexPoints`): the canonical degree is
   `Σ log p_i`. On the graph of `ψ_a` product sections stay distinct while `d₁ < a · w_i`
   (`graph_injOn`), and on the diagonal the product count exceeds the sum count as soon as
   `k! Π w_i (d₁ + d₂ + Σ w_i)^k < (d₁ d₂)^k` (`card_image_add_lt_card_product`). The threshold
   grows with `k` like the canonical degree. For distinct primes the sections of degree `≤ log X`
   are the integers `≤ X` composed of these primes (`card_smoothUpTo_eq_card_simplexPoints`), so
   `(log X)^k ≤ k! · Π log p · Ψ(X; S) ≤ (log X + Σ log p)^k` for every set `S` of `k` primes
   (`card_smoothUpTo_finset_bounds`): this is the number of unknowns of a Siegel lemma on
   `S`-smooth integers. On a set containing every prime `≤ N` the count is `N`
   (`card_smoothUpTo_of_full`), and the product of the counts at `X` and `Y` never exceeds the
   count at `XY` (`card_smoothUpTo_mul_le`). On all primes the dimension count that produces the
   auxiliary section on a curve is therefore marginal, and the kernel of a restriction is spanned
   by differences of two sections with the same restriction.
8. **Two pairings, and multiplicity one.** For `z^{n+1} = c · x(1−x)^a` the Jacobi sums satisfy `conj J(χ,φ) = J(χ⁻¹,φ⁻¹)`
   and `J(χ,φ) J(χ⁻¹,φ⁻¹) = q`, hence `|σ J|² = q` at every embedding `σ` of the value ring
   (`norm_map_jacobiSum_sq`) and the Hasse–Weil bound (`abs_card_puncturedKummerPoints_sub_le`). No
   positivity is used; the archimedean places of `ℚ(ζ_m)` enter through complex conjugation.
   The mechanism is a statement of multiplicity one. Let a Frobenius scale a pairing by `q` and
   commute with a conjugation. On an eigenvector not orthogonal to its conjugate, `α ᾱ = q`
   (`SymmetricFrobenius.mul_conj_eq_of_pair_bar_ne_zero`). If a finite symmetry group commutes
   with the three structures and its `χ`-eigenspace is a line outside the kernel of the pairing,
   the Frobenius acts on the line by such an `α`
   (`SymmetricFrobenius.exists_eigenvalue_mul_conj_eq`): the pairing couples `χ` with `χ⁻¹`,
   conjugation sends `χ` to `χ̄ = χ⁻¹`, and both land on the same line. Both hypotheses are
   needed. The Frobenius `diag(r, r⁻¹)` with the hyperbolic pairing and coordinatewise
   conjugation satisfies the axioms at multiplicity two (`exists_frobenius_not_pure`), and at
   multiplicity one under the non-compact symmetry `ℝˣ` acting by `diag(t, t⁻¹)`, whose character
   `t ↦ t` is not unitary (`exists_frobenius_not_pure_of_scaling`). For `ζ` the compact symmetry,
   the Dirichlet characters, has infinite multiplicity, and the scaling group acts on the line of
   a zero `ρ` by `t ↦ t^(ρ − 1/2)`, unitary iff `Re ρ = ½`.
9. **Purity as an equality case.** If `x_j y_j = q` for all `j` and `Σ (x_j² + y_j²) ≤ 2 q · #`, then
   every `x_j² = q` (`sq_eq_of_mul_eq_of_sum_sq_le`). For Jacobi sums the product is the functional
   equation and the sum is Parseval (`sum_norm_sq_jacobiSum`, `norm_jacobiSum_sq_of_meanValue`). The
   comparison of a functional equation with a second moment has zero slack over `𝔽_q`; over `ℤ` its
   slack is the error term of the mean value.
10. **One-sided transfer along a positive kernel.** If `f ≤ g + K f`, `g ≤ A x^s` and `ρ(s) < 1`,
    then `f ≤ A/(1 − ρ(s)) · x^s` (`le_rpow_of_le_add_dilate`); the constant is attained
    (`transfer_constant_attained`). At a neutral exponent `x^s` solves the homogeneous equation
    (`rpow_eq_sum_dilate_of_gain_eq_one`), and a neutral mode is removed only by an `o(·)` a priori
    bound (`le_rpow_of_le_add_dilate_of_isLittleO`). A barycentric stencil contracts on all of
    `(0, 1)` (`dilationGain_lt_one_of_barycentric`). Instances in the corpus: the halving
    kernel, with the constant `1/(1 − 2^{−b})` (ExclusionOfTheCriticalState
    `error_le_of_terminalOddHalf_le`), and the midpoint kernel on the scales `⅔` and `4⁄3`, whose
    finite Green series is ExceptionalLayerTheory `finite_midpoint_green`.
11. **Every contracting stencil of the prime error is a meter.** For a positive stencil with
    `ρ(1) ≤ 1` and `ρ < 1` on `(½, 1)`, and either sign `σ`, the bounds `σ · gap ≤ C x^s` hold for
    all `s ∈ (b, 1)` iff `Θ ≤ b`, for every `b ≥ ½` (`primeErrorGap_upper_spectrum_iff`). The a priori input is the
    prime number theorem alone. In particular every Jensen gap `θ(x) − Σ a_j θ(λ_j x)` on a
    barycentric stencil reads `Θ` from either side (`thetaJensenGap_upper_spectrum_iff`).

## 5. The producers, with their slack

| Producer | Reading | Price | Comparison slack | Reading slack | Paid at |
|---|---|---|---|---|---|
| Stepanov over `𝔽_q` | zeros with multiplicity | degree of the auxiliary | `O(g√q)` | none | the finite place, by inseparability |
| Stepanov on the prime torus (ALST) | vanishing at torsion | length `lcm(1,…,N) = e^{ψ(N)}` | none | circular | the real place |
| Jacobi sums (mechanism 8) | `|J|²` | `q` | none | none | conjugation of `ℚ(ζ_m)` |
| Second moment (mechanism 9) | `Σ |J|²` | Parseval | none over `𝔽_q` | none | the functional equation |
| Chebyshev (mechanism 5) | carries `· log p` | entropy | `≤ log(m+n+1)` | linear: a `K`-term majorant overshoots by the mass at `K`-rough quotients (RHTower `ChebyshevMajorant.sum_mul_log_factorial_ge`) | the real place |
| Polynomial integrals (ArithmeticEffectivityTheory `log_inv_integral_le_psi`) | `log(1/∫₀¹ P) ≤ ψ(n+1)` | sup norm of `P` on `(0, 1)` | none: the integrals in degree `≤ n` are exactly `lcm(1,…,n+1)⁻¹ ℤ` (ArithmeticOfSquareRootPrecision `nairLattice_eq`) | linear: every nonzero `P` of degree `≤ n` exceeds `e^{−0.87n}` on `(0, 1)` (ArithmeticKreinLangerTheory `exists_Ioo_gt_univariate_chebyshev_cap`) | the real place |
| Factorial stencils with multiplicity (ArithmeticKreinLangerTheory) | multiplicities `· log p` | size of the auxiliary | — | `εx` for every `ε > 0`: `θ(x) ≤ (1+ε)x + C log² x` (`theta_le_one_add_eps_of_vanishing_order`); the normalized slopes have infimum `1`, not attained (`isGLB_producerSlopeSet`, `one_notMem_producerSlopeSet`) | the real place |
| Selberg sieve (RHTower/Sieve `card_prime_Ioc_le`) | primes in `(a, b]` | `2(b−a)/log Y` and a remainder | — | the factor `2` | — |
| Positive stencil (mechanism 11) | gap of `θ` | none known | — | none: it is a meter | — |

The Chebyshev row locates the loss of every divisibility producer: the comparison is exact up to
a logarithm, and all of the loss occurs when the alternating priced stencil is replaced by a
positive one. A stencil on the powers of one base whose reading is known to a power saving has a
symbol vanishing at every zero of `ζ` to the right of that power (ZeroConfigurationGeometry
`dilationSymbol_eq_zero_of_zeta_eq_zero`). The symbol `1 − ρ(s)` of a positive contracting stencil
has no zero there, since `|ρ(s)| ≤ ρ(Re s) < 1`, and its reading is a meter.

The ledgers are exact: a nonzero polynomial over a field has degree at least the sum of its
prescribed vanishing orders, and a nonzero integer divisible by `p^{m_p}` has logarithm at least
`Σ m_p log p` (ArithmeticKreinLangerTheory `sum_le_natDegree_of_vanishing`,
`sum_mul_log_le_log_of_dvd`). Divisibility does not see parity at square-root precision: the
logarithm of the least common multiple of the odd parity class differs from `θ(x)` by at most
`2√x log x` (`abs_log_lcm_oddPoints_sub_theta_le`, same programme). What a producer over `ℤ` lacks
is multiplicity below its price (mechanisms 1 to 4).

One producer over `ℤ` in the corpus passes the classical region: `ζ` has no zero with
`Re s > 20999/24000` (MetaplecticMobiusDescent/Detector
`riemannZeta_ne_zero_of_sub_seven_eighths_lt_re`). Its comparison is a principal signal against a
Gram bound. In the exponent model of RHTower `QuasiRHDetectorScaleBudget` the boundary is `7/8`
for every split of the two low scales (`fixed_slot_boundary`), and `7/8` is the minimum over the
total slot length, attained only at `1/6` (`retunedBoundary_sharp_minimum`). These are identities
between the exponents of the bounds used, not lower bounds. Since `Θ ≤ 20999/24000`
(ZeroForcingCalculus `zetaZeroAbscissa_le_sub_seven_eighths`), mechanism 11 gives every contracting
stencil gap of the prime error a bound `σ · gap ≤ C x^s`, for either sign, at each exponent
`s ∈ (20999/24000, 1)`. The slack of this producer has not been analysed in the terms of the
table.

## 6. Questions

| # | Question | Answer |
|---|---|---|
| Q1 | What replaces inseparability at the real place? | Nothing local (mechanism 1). The Frobenius-linear operators over `ℤ` are the digit operators; they see the fibre of `ψ_a`, `a` distinct points, in place of the fat point (mechanisms 3, 4). Infinitesimally the replacement is `d/ds`: it is the only compatible derivation with an entropy, and its Frobenius scalar is `a`, expanding (mechanisms 2, 6). |
| Q2 | What is the analogue of a divisor of bounded degree on `Spec ℤ × Spec ℤ`, with a Riemann–Roch count whose constants include the `Γ` factor? | A weighted simplex of exponents, that is the integers composed of `k` primes; the count has leading constant `1/(Γ(k+1) Π log p_i)`, canonical degree `Σ log p_i` and a duality (mechanism 7). On all primes the count is marginal (`card_smoothUpTo_mul_le`). On one factor with its archimedean weight the count is the theta Riemann–Roch `h⁰(a, d) − h⁰∨(a, −d) = d` (ArithmeticEffectivityTheory `thetaH0_riemannRoch`). Open: the second term on the full square. |
| Q3 | Which comparisons of sizes survive the product formula? | Carries against entropy, with logarithmic slack, and only for the weights `c · log p` (mechanisms 5, 6). A functional equation against a second moment, with the slack of the mean value (mechanism 9). Degree against multiplicity does not: the Frobenius scalar is paid at `∞` (mechanism 2). |
| Q4 | Is there a positivity-free proof of the curve case in which the archimedean place of a number field appears? | Yes, for the Kummer family, and the proof is exactly multiplicity one under a compact symmetry (mechanism 8). At multiplicity two, or under a non-compact symmetry, the same axioms admit a Frobenius that is not pure. A curve without complex multiplication needs a further structure. |
| Q5 | Is every producer with a priced reading a transfer? Which classes have sublinear slack? | In the stencil class: priced stencils are blind at the zeros, positive stencils are meters, and the passage between them costs the rough mass (§5). Factorial stencils with multiplicity reach every slope above `1` and never `1` (ArithmeticKreinLangerTheory `isGLB_producerSlopeSet`, `one_notMem_producerSlopeSet`). |
| Q6 | What does each axiom level reach? | An integer count with error tending to a constant is compatible with a zero at every depth in `(½, ⅔)` (RHTower `overRegular_integers_do_not_constrain_zeros`); integer norms with an Euler product allow the one-off (ALST). The level that excludes them is the balance `Λ ∗ 1 = log` (HodgeTheoryOfAFixedPart `sum_divisors_eq_log_iff`), equivalently the entropy of the weights (mechanism 6). |
| Q7 | What do quadratic readings reach? | Selberg's formula is a quadratic priced reading (RHTower `selberg_symmetry_formula`), exact on `Λ` and off by a linear term on the Liouville twin (RigidArithmeticOfCuts, the Selberg ledger). The sieve built on the same square bounds the primes of an interval with the factor `2` (RHTower/Sieve `card_prime_Ioc_le`). Open: any saving for `Λ` itself. |
| Q8 | Which one-sided transfers between meters hold at the same exponent? | All those along a positive kernel, exactly at its contracting exponents, with the constant `1/(1 − ρ(s))` (mechanisms 10, 11). |

## 7. Tools

| Tool | Where it lives |
|---|---|
| T1 Auxiliary sections with explicit heights | counts and duality: `simplexPoints`; the unknowns of a Siegel lemma on smooth integers: `card_smoothUpTo_finset_bounds` (mechanism 7); Siegel auxiliaries on torsion: ALST `exists_siegel_auxiliary`; smooth populations at factorial price: RestrictedFactorizationCalculus; small sections of a metrized rational lattice, with their height: CountingHolography/Sections `sectionHeight_bounds`; integer polynomials with a small integral: ArithmeticEffectivityTheory `log_inv_integral_le_psi` |
| T2 A `δ`-structure with an archimedean component | the carry calculus of mechanisms 5 and 6, with the balance `abs_sum_factorization_choose_sub_entropyCarry_le`; the finite components are the Fermat quotients of the ghost ring (AbsoluteGeometryOfSpecZ) |
| T3 Sieve-ordered Schur elimination | the cooperative reduction (inverse and Schur corrections of a form with nonpositive couplings are sign-definite, GreenCalculusOfThePrimeFreeWindow `inv_mulVec_nonneg_of_offDiag_nonpos`, `mul_inv_mul_transpose_apply_nonneg`), the pole plane (`withPoles`) and the overlap law `riemannHypothesis_iff_forall_weilSchur_nonneg`; elimination on a sublattice of the comb: SignedArithmeticCorrespondences |
| T4 A twin suite | ScaleSignedIncidenceCriticality `TheTwinTestSuite`; for weights, `exists_carry_lt_and_gt` |
| T5 One-sided transfer kernels | mechanisms 10 and 11; the halving kernel (ExclusionOfTheCriticalState `error_le_of_terminalOddHalf_le`) and the Green series of the prime midpoint (ExceptionalLayerTheory `finite_midpoint_green`) |

## 8. Pillar theorems

| # | Theorem | Lean |
|---|---|---|
| 1 | A local Frobenius-linear operator is a multiplication | `HasOrderLE.eq_mul_of_expand_linear`, `IsLocal.eq_mul_of_expand_linear` |
| 2 | The Frobenius scalar of a compatible derivation is the degree | `isCompatible_iff`, `IsCompatible.scalar_eq` |
| 3 | The digit operators lift the Hasse derivatives; the fibre replaces the fat point | `digitOp_expand_mul`, `digitOp_eq_hasseEuler`, `mem_fibreIdeal_iff`, `fibreIdeal_eq_span_pow_of_charP` |
| 4 | The balance of carries and the rigidity of `log` | `entropyCarry_sub_log_le_log_choose`, `log_choose_le_entropyCarry`, `carry_bddBelow_iff` |
| 5 | Riemann–Roch and duality on a finite prime torus; its sections are the smooth integers; on all primes the count is marginal | `card_simplexPoints_bounds`, `card_filter_pos_simplexPoints`, `card_smoothUpTo_finset_bounds`, `card_smoothUpTo_mul_le` |
| 6 | Hasse–Weil for the Kummer family from the two pairings | `abs_card_puncturedKummerPoints_sub_le`, `norm_map_jacobiSum_sq` |
| 7 | Purity is the equality case of a mean-value comparison | `norm_jacobiSum_sq_of_meanValue` |
| 8 | Purity without positivity is multiplicity one under a compact symmetry; both hypotheses are needed | `SymmetricFrobenius.exists_eigenvalue_mul_conj_eq`, `exists_frobenius_not_pure`, `exists_frobenius_not_pure_of_scaling` |
| 9 | One-sided transfer with the exact constant and the exact range | `le_rpow_of_le_add_dilate`, `transfer_constant_attained`, `rpow_eq_sum_dilate_of_gain_eq_one` |
| 10 | Every contracting stencil of the prime error is a one-sided meter | `primeErrorGap_upper_spectrum_iff`, `thetaJensenGap_upper_spectrum_iff` |

## 9. Traps

| Trap | Truth |
|---|---|
| A tight inequality is a producer | An identity read through `Λ` is a meter; a producer needs slack that is not circular |
| A derivative can be made Frobenius-linear over `ℤ` | Only multiplications are local and `ψ_a`-linear where `a` is regular |
| The digit operators give multiplicity | They give `a` simple zeros on a fibre; the count against degree is unchanged |
| `ℓ`-adic inseparability is free | The Frobenius scalar is `a` at every place; what is gained at `ℓ` is paid at `∞` |
| Chebyshev's comparison is lossy | It is exact up to `log(m+n+1)`; the loss is in the reading |
| The weights `log p` are a normalization | They are forced: no other weighting has a carry bounded on the linear scale |
| A priced stencil can be made positive | Its symbol vanishes at the zeros; a positive contracting stencil has none |
| A one-sided bound passes through any averaging | Only at contracting exponents; at a neutral exponent the kernel has a homogeneous solution |
| Bombieri's count works on the arithmetic square | On `k` primes it starts at degree of the order of the canonical degree; on all primes product and sum of the counts agree |
| Purity of Jacobi sums is a positivity argument | It is an identity between two pairings; its analogue for `ζ` is `ρ̄ = 1 − ρ` |
| A functional equation and a real structure force purity | Only at multiplicity one under a compact symmetry; `diag(r, r⁻¹)` satisfies both otherwise |
| A better integer polynomial reaches slope `1` | Every nonzero integer polynomial of degree `≤ n` exceeds `e^{−0.87n}` somewhere on `(0, 1)` |
| A factorial stencil can be tuned to slope `1` | The slopes have infimum `1` and do not attain it |
| The Stepanov degree bound on the torus is a producer | Its price is `e^{ψ(N)}` (ALST) |
| An integer count of high precision forces the zeros | Over-regular Beurling integers carry zeros off the line |

## 10. Open

1. **A one-sided bound for one positive stencil.** For any barycentric stencil and either sign,
   `σ · (θ(x) − Σ a_j θ(λ_j x)) ≤ C x^s` with `s < 1` gives `Θ ≤ s`. The detector strip gives these
   bounds for `s > 20999/24000` (§5). A bound at a smaller exponent is open, and no comparison is
   known whose reading is such a gap.
2. **A joint `δ`-structure.** The balance of carries is the product formula for the binomial
   coefficient (mechanism 5). Open: one operator on integer auxiliaries whose component at `p` is
   the Fermat quotient and whose component at `∞` is `n log n`, and a comparison of this kind for
   an auxiliary that is not a ratio of factorials.
3. **The second term on the arithmetic square.** On all primes the Riemann–Roch count is marginal;
   the number of distinct products below the leading order is the analogue of the genus term.
4. **Sieve order.** The cooperative reduction is proved for the dyadic middle of a window. In
   the order of the small primes the stage floors are those of multiples of `d ≥ 2`
   (SignedArithmeticCorrespondences); the transport of the degrees through the stages is open.
5. **Quadratic readings.** A saving for `Λ` from a priced reading of `Λ ∗ Λ`.
6. **Curves without complex multiplication.** At the axiom level of mechanism 8 the question is
   closed: at multiplicity two the axioms admit a Frobenius that is not pure. Open: a structure
   that is not a positivity and not inseparability, and that excludes the split datum for a curve
   without complex multiplication.

## 11. Context

| Programme | Relation |
|---|---|
| ArithmeticLefschetzStepanovTheory | Stepanov's method on the prime torus; the fixed-point auxiliary has length `e^{ψ(N)}`; TAP explains why no operator repairs it (mechanisms 1 to 4) |
| AbsoluteGeometryOfSpecZ, SurfaceOfSpecZ | ghost ring, Frobenius graphs, contacts; TAP adds the archimedean component of the `δ`-structure |
| GreenCalculusOfThePrimeFreeWindow, SignedArithmeticCorrespondences | positivity producers by elimination; they host T3 |
| ScaleSignedIncidenceCriticality | the twin test suite |
| ExclusionOfTheCriticalState, ExceptionalLayerTheory | halving and midpoint identities; instances of mechanism 10; the landing of mechanism 11 uses their both-signs theorem |
| ZeroConfigurationGeometry, ArithmeticOfSquareRootPrecision, RHTower (Chebyshev majorants) | priced stencils: symbols vanish at the zeros, rough slack, Möbius inversion of the factorial; the lattice of the integrals of integer polynomials |
| ArithmeticCastelnuovoSeveri, CountingHolography | Hodge index and Stepanov over finite fields: the calibration targets; CountingHolography/Sections hosts the small sections with heights of T1 |
| TensorPowerProgramme | purity of Jacobi sums |
| ArithmeticKreinLangerTheory | the language of producer, receiver and ledger; the exact ledgers over a field and over `ℤ`; the integer Chebyshev ceiling; the slopes of factorial stencils; parity-blindness of divisibility. TAP supplies what lies under the ledger: operators, carries, counts and transfers |
| ArithmeticEffectivityTheory | Stepanov's method over `ℤ` through `lcm · ∫ P`; the theta Riemann–Roch on `Spec ℤ` |
| RHTower/Sieve | Selberg's sieve for the primes of an interval; the smooth integers `smoothUpTo` of mechanism 7 |
| MetaplecticMobiusDescent/Detector, RHTower (detector budget) | the producer over `ℤ` that passes the classical region, and the exponent budget of its comparison |

TAP sits between the programmes that state what an input must deliver and the programmes that read
`Θ` exactly. It adds no route. For a route it answers: where is the slack, at which place is it
paid, and which twin do the axioms admit.

## 12. Success criteria and contributions

**A producer must meet** (§2.9):
1. **Calibration.** Inside the theory it reproves the Riemann hypothesis for curves and Riemann–Roch
   with exact constants.
2. **Selection.** It does not apply to any twin.
3. **Non-circularity.** Its price is not computed from `ψ`, `M` or the zeros.
4. **Output.** A one-sided bound for one meter, landing in a proved implication.

**The programme succeeds** when each producer class has its slack, its place and its twin fixed by
theorems, and either a producer meeting the four criteria exists or the open items of §10 are
closed in the negative with their positive survivors.

**A contribution must** be unconditional; name construction, reading, price and comparison; say
whether its slack is comparison slack or reading slack and at which place it is paid; state the
twin at its axiom level; and answer a question, sharpen a pillar, or add a tool that another module
uses. A restatement of a corpus equivalence is not a contribution.
