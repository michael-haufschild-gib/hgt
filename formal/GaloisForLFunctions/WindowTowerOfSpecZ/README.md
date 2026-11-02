# The Window Tower of Spec ℤ (WTZ)

Namespace `GaloisForLFunctions.WindowTowerOfSpecZ`; umbrella `WindowTowerOfSpecZ.lean`; 7 modules.
Every theorem is unconditional. Theorems named `riemannHypothesis_iff_*` are proved equivalences,
not proofs of RH.

## 1. Motivation

Weil's criterion has become a statement about **windows**: RH holds iff Weil's form `Q` is
nonnegative on every test supported in `[−A, 0]`, for every length `A`. One window is a finite
problem: it reads only the prime powers `n ≤ e^A`, its negative index is finite, and its form is
archimedean jumps, one fold per active prime power, a canonical class and a pole plane (CWS). RH is
not a property of one window. It is **uniformity in `A`**: a law valid along the whole tower
`A ↦ W_A` as the length grows and the integers enter one at a time.

Three proved laws fix the shape of what is missing (CWS, ACS, LST): the window `h¹` has no
finite-dimensional realization; its effective rank grows like `2e^A`; counts pay everything except
the primitive part `½Q`. Over `𝔽_q` this situation is resolved by towers of growing rank with
control theorems (base change along `𝔽_{q^m}`, Iwasawa theory), not by one variety. WTZ is the
theory of the window tower of `Spec ℤ` as such: the algebra acting on a window, the transitions
between windows and their control, the Tate pieces and the one non-Tate piece, the lattice carrying
the sections, the growth law in `A`, and the place where selection has to happen.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Window module | `windowSupported A` | real functions vanishing off `[−A, 0]`; `F_A ⊆ F_B` for `A ≤ B` |
| Window shift | `windowShift t` | `(T_t H)(u) = 1_{u≤0} H(u − t)`: the fold by `t`, cut at the right end |
| Window representation | `windowRep A`, `windowRepFun` | `ρ_A(f)H = Σ_{n≤e^A} f(n)n^{−1/2}T_{log n}H`, a ring map from arithmetic functions to `End(F_A)` |
| Truncation ideal, window algebra | `truncIdeal N` | `I_N = {f : f = 0 on [1,N]}`; window algebra `D_N = 𝒜/I_N`, `N = ⌊e^A⌋` |
| Basis functions | `single n c` | `c·δ_n`, the fold `T_n` as an element of the algebra |
| Position, Tate twist, Tate flow | `positionOp`, `tateTwist c`, `tateTwistHom c` | `(MH)(u) = uH(u)`; `f ↦ f·n^{−c}`, a ring automorphism, implemented by `e^{cu}` |
| Window zeta, Möbius, von Mangoldt operators | `windowRep A ζ`, `windowRep A μ`, `windowRep A Λ` | `Z = Σ T_n`, its inverse, its logarithmic derivative |
| Euler datum, Tate family | `tateFamily F G k` | `F * G = 1`; `J^F_k = twist_{−k}(F) * G` |
| Jordan family | `jordanFun k` (ADT `jordanTotient`) | `J_k = J^ζ_k`, `J_k(m) = Σ_{d∣m}μ(m/d)d^k = #primitive vectors of (ℤ/m)^k` |
| Tate function | `tateFunction A H k` | `τ_H(k) = ⟨ρ_A(J_k)H, H⟩`, an exponential polynomial in the dimension `k` |
| Flip datum, shifted datum | `flipDatum p`, `shiftedDatum ε` | `ζ(s)(1 − p^{−s})²`; `ζ(s)ζ(s − ε)` |
| Atoms, atomic embedding | `atom N φ m`, `atomicEmbedding N φ g`, `IsAtomProfile` | `b_m(u) = φ(u + log N − log m)` at `log(m/N)`; `ι(g) = Σ_{m≤N} g(m)m^{−1/2}b_m` |
| Centred pole plane | `centredCosh A`, `centredSinh A` | `2cosh((u + A/2)/2)`, `2sinh((u + A/2)/2)` |
| Sharp window floor | `sharpWindowFloor A` | `deg K_A + 2 sinh(A/2) − A` |
| Dilation, Adams lift | `dilate r`, RHTower `mPart e` | `(D_rH)(u) = H(u/r)`; `ψ^e f(n^e) = f(n)`, zero off `e`-th powers |
| Adjoint shift | `adjointShift A t` | `(T_t^*H)(u) = 1_{u≥−A}H(u + t)`, the shift toward the left end |

From CWS: `IsWindowTest`, `windowLevel = ⌊e^A⌋`, `foldEnergy`, `canonicalDensity`, `halfChebyshev`,
`canonicalDegree`, `windowIndex`, `windowGenus`, `exists_flip_twin_of_window`.

## 3. Language

- **Tower**: `A ↦ (F_A, ρ_A, Q|_{W_A})`; **level** `N = ⌊e^A⌋`; **stage** `n`: `log n ≤ A < log(n+1)`.
- **Transition**: the truncation `D_{N+1} → D_N` on algebras, the inclusion `F_A ⊆ F_B` on modules.
- **Small extension**: a surjection of local algebras whose kernel is killed by the maximal ideal
  `m = I_1 = {f : f(1) = 0}`. **Socle element**: an element killed by `m`.
- **Loewy length**: the least `k` with `m^k = 0`. **Cotangent space**: `m/(m² + I_N)`.
- **Tate flow**: the one-parameter group of twists `f ↦ f·n^{−c}`; its generator is the degree
  derivation `f ↦ f·log`, i.e. the commutator with the position.
- **Tate piece**: a value of a Tate family at a positive integer dimension. **Non-Tate piece**: the
  derivative at dimension `0`. **Tate positive**: all Tate pieces are `≥ 0`.
- **Atomic lattice**: the integers `m ≤ e^A`, embedded as atoms.
- **Soft**: true for data with off-line zeros (shifted products, flip twins, Epstein lattices).
  **Selective**: fails on such data.

## 4. Mechanisms

**A. The window algebra.** Compressions of translations by nonnegative amounts to an interval
compose exactly and vanish past its length: `T_sT_t = T_{s+t}`, `T_t = 0` on `F_A` for `t > A`. So
the Hecke shifts `n^{−1/2}T_{log n}` turn Dirichlet convolution into composition, and `ρ_A` is a ring
homomorphism whose kernel is exactly `I_{⌊e^A⌋}`: **the window algebra is the Dirichlet ring
truncated at the level**. The degree derivation is the commutator with the position,
`Mρ_A(f) − ρ_A(f)M = ρ_A(f·log)`; Tate twists are conjugations by `e^{cu}`. Hence
`ρ_A(Λ) = [M, Z]Z^{−1}`, `Z = ρ_A(ζ)`, equivalently `Z M Z^{−1} = M − ρ_A(Λ)` (the window zeta
operator conjugates the position into position minus von Mangoldt), and

`Q(H) = Ω(0)‖H‖² + J_∞(H) − 2⟨ρ_A(Λ)H, H⟩ + ½⟨c,H⟩² − ½⟨s,H⟩²`.

**B. The tower and its control.** The modules nest equivariantly (`ρ_B = ρ_A` on `F_A`). The
algebras form an inverse system of local Artinian rings with limit the full Dirichlet ring. Each
transition is a small extension with one-dimensional kernel spanned by the new fold `δ_{N+1}`
(`I_M·m ⊆ I_{2M+1}`); on windows shorter than `log 2n` the new fold `T_n` composes to zero with every
element of `m`. The maximal ideal satisfies `m^k ⊆ I_{2^k−1}`, sharply: any `k` folds compose to zero
on windows shorter than `k log 2`, and `T₂^{k−1}` survives on longer ones. The cotangent space has the
primes `≤ e^A` as a basis: the primes generate every window algebra; prime powers and composites
are products.

**C. Tate pieces and the non-Tate piece.** For an Euler datum `(F, G)` the Tate family
`J^F_k = twist_{−k}(F) * G` is a cocycle of the Tate flow, `J^F_{k+l} = twist_{−k}(J^F_l) * J^F_k`,
with `J^F_0 = 1`. For `ζ` it is Jordan's totient; on a window it is the group commutator
`ρ_A(J_k) = e^{kM}Ze^{−kM}Z^{−1}`. Its values at `k = β + 1` are the point counts
`φ(m)#ℙ^β(ℤ/m)` (the Tate pieces of the degeneration, AHD), its value at `k = 0` is `1`, and its
derivative at `k = 0` is `Λ`. With the Tate function `τ_H(k) = ⟨ρ_A(J_k)H, H⟩`:

`Q(H) = Ω(0)τ_H(0) − 2τ_H′(0) + J_∞(H) + ½⟨c,H⟩² − ½⟨s,H⟩²`.

Weil's window form is the first-order jet at dimension zero of a function whose values at the
positive integers are counts. Along the powers of a prime the Tate pieces form a Hensel tower,
`J_k(p^{a+1}) = p^kJ_k(p^a)` (`p^k` is the fibre of reduction `(ℤ/p^{a+1})^k → (ℤ/p^a)^k`), while the
non-Tate piece `log p` is the same at every stage. At the first prime `τ_H(k) = ‖H‖² + (2^k − 1)2^{−1/2}∫H(u)H(u + log 2)`:
the signed fold count of `T₂` is the coefficient of `#ℙ^{k−1}(𝔽₂)`.

**D. The atomic lattice.** Atoms of width `< log((N+1)/N)` at the points `log(m/N)`, `m ≤ N`, are
moved by the window shifts as the integers are multiplied: `T_{log n}b_m = b_{nm}` (`0` past the
level). The atomic embedding `ι` intertwines `ρ_A` with multiplication in `D_N`: the integers of
the window are a free module of rank one over the window algebra. With `⟨ι g, ι h⟩ = ‖φ‖²Σ g(k)h(k)/k`,
Weil's arithmetic term on the lattice is multiplication by `Λ`, `−2‖φ‖²Σ_k (Λ*g)(k)g(k)/k`, and the pole
plane reads the window Dirichlet polynomial `Σ g(m)m^{−s}` at `s = 0` and `s = 1`.

**E. The pole plane and the floor.** The pole term `2Ĥ(0)Ĥ(1)` is translation invariant; centred at
the window it is `½⟨c_A,H⟩² − ½⟨s_A,H⟩²` with `‖s_A‖² = 4 sinh(A/2) − 2A`. Its exact capacity
`2 sinh(A/2) − A` replaces the cruder `2A sinh²(A/2)`, giving the sharp floor
`Q ≥ −(deg K_A + 2 sinh(A/2) − A)‖H‖²` and, with `ψ_{1/2}(x) ≤ 2√x log x`, the explicit bound
`≤ −Ω(0) + (4A + 1)e^{A/2}`: window negativity grows at most like `Ae^{A/2}` (the trivial strip).

**F. Symmetries of the tower.** Dilation by `e` maps the window of length `A` onto the window of
length `eA` and intertwines the window representation with the Adams lift `ψ^e`, up to the Tate
twist `(e − 1)/2`: `ρ_{eA}(ψ^e f)D_e = D_eρ_A(f n^{−(e−1)/2})`. The tower is self-similar on `e`-th
powers; Weil's form is not, because the longer window also sees the integers that are not `e`-th
powers and the Gamma factor is not dilation invariant. Over a curve the corresponding base change
`𝔽_q ⇝ 𝔽_{q^e}` is an exact symmetry. The window involution `σ_A` conjugates every shift into its
adjoint, so Serre duality is the Rosati involution of the window algebra, and Weil's arithmetic term
is the Rosati symmetrization of `ρ_A(Λ)`.

**G. Selection.** Tate pieces at a prime have the sign of the weight: `J^F_k(p) = F(p)(p^k − 1)` and
`λ_F(p) = F(p) log p`. A flip twin has a negative Tate piece at its prime from the stage where the
flip becomes visible. The shifted datum `ζ(s)ζ(s − ε)`, with zeros `ρ + ε` off the line, is Tate
positive in every positive dimension. Counts at integer dimensions do not select.

## 5. Questions the programme answers

| Question (obstacles §2.7) | Answer |
|---|---|
| What are the restriction maps `W_A → W_{A'}` and their control theorem? | Equivariant inclusions of window modules over the truncations `D_{⌊e^{A'}⌋} → D_{⌊e^A⌋}` (`windowRepFun_of_le`, `ker_windowRep`). Each stage is a small extension with kernel the new fold (`sub_single_mem_truncIdeal_succ`, `mul_mem_truncIdeal`); the new fold is a socle element until stage `2n` (`windowRep_single_mul_eq_zero`); Loewy length `⌊log₂ N⌋ + 1` (`windowRep_kills_pow_iff`); cotangent space = primes (`mem_sq_sup_truncIdeal_iff`, `single_prime_not_mem`); inverse limit = Dirichlet ring (`existsUnique_limit`, `iInf_truncIdeal`). |
| What is the count attached to a fold `T_n`; what does `sym₂` count? | `T_n` is `δ_n`; in the Tate function its coefficient is `J_k(n)n^{−1/2}`, a count of primitive vectors of `(ℤ/n)^k` (`tateFunction_eq`, `jordanTotient_eq_card_primVec`). At the first prime the signed fold count `anti₂ − sym₂` is the coefficient of `#ℙ^{k−1}(𝔽₂) = 2^k − 1` (`tateFunction_firstPrime`). It enters Weil's form only through the derivative at `k = 0` (`weilQuad_eq_tateJet`): no integer dimension makes it a count. |
| Is there a scheme over `ℤ` whose `ℤ/m`-points give the twisted counts and whose "conductor-one" part is the window form? | The punctured affine spaces `𝔸^k∖0` (primitive vectors), with the dimension as parameter: `J_k(m) = φ(m)#ℙ^{k−1}(ℤ/m)` are the Tate pieces (`jordanTotient_eq_card_projPoints`); `∂_kJ_k(m)|₀ = Λ(m)` (`hasDerivAt_jordanTotient_zero`) makes Weil's arithmetic window term the derivative at dimension zero (`hasDerivAt_tateFunction`). |
| What lattice of rank `≈ 2e^A` carries the sections; with what metric? | The atomic lattice: the integers `m ≤ e^A`, a free rank-one module over the window algebra (`windowRepFun_atomicEmbedding`), of rank `⌊e^A⌋`; the window genus `≥ (2 − η)e^A` (CWS) is twice this rank to main order. Metric `‖φ‖²Σ g(k)h(k)/k` (`integral_atomicEmbedding_mul`); arithmetic term = multiplication by `Λ` (`integral_windowRep_atomicEmbedding`); pole = values at `s = 0, 1` (`poleA_atomicEmbedding`, `poleB_atomicEmbedding`); the Gamma factor enters as the Lévy kernel between atoms. |
| What growth law does the tower obey? | Negativity `≤ (deg K_A + 2 sinh(A/2) − A)‖H‖² ≤ (−Ω(0) + (4A+1)e^{A/2})‖H‖²` (`weilQuad_ge_neg_sharpWindowFloor`, `sharpWindowFloor_le`). Its exponent lies between the zero width and `½`, with RH iff it is `0` (ACCE `UnconditionalEqualityOfPolarAndFullGroundEnergyRates`, SRT `NegativityRateEqualsMaximalDepth`). |
| Is there a Frobenius / base change for the tower; what is Serre duality on it? | Adams lifts are dilations `A ↦ eA` up to a Tate twist (`windowRepFun_mPart_dilate`, `windowShift_dilate`); Serre duality `σ_A` is the Rosati involution (`windowInvolution_windowShift`, `integral_windowRepFun_mul_eq`). |
| Which axiom fails for the fakes? | Flip twins fail Tate positivity at their prime (`flipDatum_tateFamily_prime_neg`); shifted products `ζ(s)ζ(s−ε)` satisfy it (`shiftedDatum_tateFamily_nonneg`); every algebraic structure of the tower holds for every Euler datum. Selection is the sign of the derivative at dimension zero against the archimedean data, along the whole tower — Weil's form itself. |

## 6. Tools

**Developed.**
- Window shifts and the window representation of the Dirichlet ring; nesting along the tower.
- Truncation ideals, basis functions `δ_n`, small-extension, socle and Loewy calculus; cotangent
  spaces; inverse limits of compatible window classes.
- The Tate flow: twist automorphisms, the degree derivation as a commutator, Tate families of Euler
  data as cocycles, Tate operators as group commutators; Tate pieces at primes.
- The Jordan family as an analytic family in the dimension; Tate functions of window tests.
- Atoms and the atomic embedding; orthogonality, regular representation, pole moments of atomic tests.
- Centred pole plane; exact capacity by Cauchy–Schwarz; sharp floor and pencil; `ψ_{1/2}` bound by
  telescoping `Σ n^{−1/2} ≤ 2√N`.
- Dilations of windows and Adams lifts; adjoint shifts and the Rosati involution.

**Used from the corpus.** CWS (window tests, folds, canonical class, floor, index, genus, flip twins);
AHD/ADT (`jordanTotient`, `natCard_projPoints_mul_totient`, `natCard_primVec_eq_jordanTotient`); RHTower
`WeilMarkovPoleCapacity` (Markov form, `levyJump`, pole pairings); SpacingScaleHarmonicAnalysis
(`weilQuad`, Cauchy–Schwarz); RHTower `mPart` (power dilation); mathlib `ArithmeticFunction`. The coefficientwise Jordan derivative is
the window form of RHTower `hasDerivAt_suzukiShiftedCoefficient`.

**To develop.** Schur complements along the socle filtration (positivity transfer across a small
extension); Poincaré inequalities for the censored jump process with potential
`archWindowKilling − k_A` (AOT, CWS); dilation continuity of window forms (critical lengths);
Wiener–Hopf factorization of the window symbol; positivity principles for exponential polynomials
in the dimension.

## 7. Open research topics

1. **The derivative at dimension zero.** `τ_H` is an exponential polynomial in `k` whose values at the
   positive integers are counts and whose value at `0` is `‖H‖²`. RH is the statement that
   `Ω(0)τ_H(0) − 2τ_H′(0) + J_∞(H) + pole ≥ 0` on every window. Which positivity of the family
   `k ↦ ρ_A(J_k)` (commutators of `Z` with the Tate flow) survives differentiation at `0`?
2. **Positivity across a small extension.** The new fold is a socle element of `D_{N+1}`. Find a Schur
   complement or capacity statement transferring window positivity from level `N` to `N + 1`, paying
   the new fold by its end masses.
3. **Analytic control by stages.** AOT's aperture transport gives the ground energy's spectral jumps
   between apertures. Open: their stage-resolved form — how much of a jump occurs where `n` enters,
   whether the archimedean exit charge `W(d) ≈ ½log(1/d)` pays each new fold at its entrance, and
   the critical lengths `A_k = inf{A : ι(A) ≥ k}`.
4. **Window capacity.** A Poincaré inequality for the interior jumps against `archWindowKilling − k_A`
   uniform in `A` (RH; shared with CWS §7).
5. **The exponent.** Close the gap between the zero width and the negativity exponent without
   no-clustering hypotheses.

## 8. Pillar theorems

| Theorem | Lean |
|---|---|
| Window shifts compose and die past the length | `windowShift_add`, `windowShift_eq_zero`, `windowShift_zero` |
| The window representation is a ring map; its kernel is the truncation | `windowRep`, `windowRepFun_mul`, `windowRep_eq_zero_iff`, `ker_windowRep` |
| Nesting along the tower | `windowRepFun_of_le` |
| Degree derivation = commutator with the position; Tate twists = conjugations | `position_comm_windowRep`, `windowRepFun_twist`, `tateTwistHom`, `tateTwist_tateTwist` |
| Von Mangoldt operator = logarithmic derivative of the window zeta operator | `windowRep_vonMangoldt_mul_zeta`, `windowRep_vonMangoldt_eq`, `windowRep_moebius_mul_zeta` |
| Weil's window form in the window algebra | `weilQuad_eq_windowRep` |
| One new fold per stage; socle law; small extensions | `sub_single_mem_truncIdeal_succ`, `mul_mem_truncIdeal`, `mul_mem_truncIdeal_succ`, `windowRep_single_mul_eq_zero` |
| Sharp Loewy length | `pow_truncIdeal_one_le`, `single_two_pow`, `windowRep_kills_pow_iff` |
| Cotangent space = primes | `mem_sq_sup_truncIdeal_iff`, `single_prime_not_mem` |
| Inverse limit = Dirichlet ring | `iInf_truncIdeal`, `existsUnique_limit` |
| Jordan family: `J_0 = 1`, `∂J|₀ = Λ`, Tate pieces = point counts | `jordanFun_zero`, `jordanFun_eq`, `hasDerivAt_jordanTotient_zero`, `jordanTotient_eq_card_projPoints`, `jordanTotient_eq_card_primVec`, `windowRepFun_jordan_nonneg` |
| Weil's form = 1-jet of the Tate function at dimension zero | `tateFunction_zero`, `hasDerivAt_tateFunction`, `tateFunction_succ`, `tateFunction_firstPrime`, `weilQuad_eq_tateJet` |
| Tate cocycle, commutator and conjugation forms | `tateFamily_add`, `tateFamily_zeta`, `windowRepFun_jordan_eq_commutator`, `windowRep_zeta_conj_position` |
| Hensel tower of Tate pieces | `jordanTotient_prime_pow_succ`, `hasDerivAt_jordanTotient_prime_pow` |
| Tate pieces at primes; flip twins; softness | `tateFamily_prime`, `logDeriv_prime`, `tateFamily_prime_mul_log`, `flipDatum_tateFamily_prime_neg`, `shiftedDatum_tateFamily_nonneg` |
| Atomic lattice = regular representation | `windowShift_atom_of_le`, `windowShift_atom_of_lt`, `windowRepFun_atomicEmbedding`, `integral_atomicEmbedding_mul`, `integral_windowRep_atomicEmbedding`, `poleA_atomicEmbedding`, `poleB_atomicEmbedding` |
| Adams lifts = dilations; Serre duality = Rosati involution | `windowShift_dilate`, `windowRepFun_mPart_dilate`, `windowInvolution_windowShift`, `integral_windowShift_mul_eq`, `integral_windowRepFun_mul_eq` |
| Exact pole capacity; sharp floor and pencil; exponent `½` | `pole_eq_centred`, `integral_centredSinh_sq`, `centredSinhPairing_sq_le`, `pole_ge`, `weilQuad_ge_neg_sharpWindowFloor`, `pencil_nonneg_sharp`, `halfChebyshev_le`, `sharpWindowFloor_le` |

## 9. Traps

| Trap | Truth |
|---|---|
| The window algebra is the semilocal algebra of the Euler factors at `p ≤ e^A` | It is the Dirichlet ring truncated at `n ≤ e^A`; composites are products, truncation is by size |
| The tower is a direct limit of finite objects carrying `h¹` | The algebras are finite-dimensional; the modules are not, and no window has a finite-dimensional realization (CWS) |
| A new prime power is a large perturbation of the window | Algebraically it is a socle element; it composes to zero with every fold until stage `2n` |
| Weil's arithmetic term is a count | It is the derivative at dimension zero of counts; at every positive integer dimension the family is a count, and that positivity is soft |
| Counting coefficients select `ζ` | `ζ(s)ζ(s − ε)` is Tate positive with zeros off the line |
| The pole plane costs `Ae^A` on a window | Its exact capacity is `2 sinh(A/2) − A`, exponent `½` |
| Atoms diagonalize Weil's form | They diagonalize the norm and turn the arithmetic into multiplication by `Λ`; the Lévy kernel couples all atoms |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| `CohomologyOfWindowsOfSpecZ` (CWS) | one window at a time: datum, folds, canonical class, floor, index, genus, Tate law, selection. WTZ is its tower: algebra, transitions, control, Tate pieces, lattice, growth |
| `ArithmeticHodgeTheoryOfDegenerations`, `ArithmeticDegenerationTheory` | Jordan totient and the projective-space count law; WTZ puts the Tate pieces and Weil's form on one family and differentiates it |
| `ArithmeticContinuationAndCriticalEnergy`, `SquareRootThreshold` | ground-energy rates and the two-bump negativity rate; WTZ supplies the explicit floor whose exponent they are |
| `LatticeSectionTheory`, `ArithmeticOrientationTheory` | Künneth Riemann–Roch, exterior jumps, the archimedean killing potential `archWindowKilling`, aperture transport and the spectral jumps of the ground energy (`TransportInApertureAndTheCeilingLyapunovIdentity`): the analytic control of the tower, beside WTZ's algebraic control |
| `ArithmeticCastelnuovoSeveri`, `ArithmeticOrientationGeometry` | Hecke action, scaling surface, orbit rates, curve towers as base changes; the window algebra is the Hecke action compressed to a window, Adams lifts its base change |
| HTGeometry / RHTower power dilation | `mPart`, `powerDilationRingHom`: the Adams lifts used for the tower's self-similarity |
| RHTower Suzuki / shifted Euler coefficients | the coefficientwise derivative `∂_ω c_ω(n)|₀ = 2Λ(n)` |

WTZ sits between the degeneration (which isolates `H¹` as the one non-Tate piece) and any producer
of positivity: it states exactly what a producer must act on — a module over a finite local algebra
at every length, compatible along small extensions — and exactly where counts stop: at the
derivative in the dimension.

## 11. Success criteria and criteria for contributions

The programme succeeds when the questions of §5 have theorems as answers (done) and when positivity
of the window `h¹` is produced, or its carriers classified, uniformly along the tower through one of:
a positivity of the Tate family that survives the derivative at `k = 0`; a transfer of positivity
across each small extension; a Poincaré inequality for the censored jump process at every length.

A contribution must:
1. be a law along the tower (in `A`, in the level `N`, or across a stage), or a statement on one
   window that the tower structure turns into such a law;
2. say which part of the window it controls: the algebra (arithmetic), the archimedean jumps, the
   pole plane, the atomic lattice;
3. say what it does on fakes (flip twins, shifted products, Epstein data, golden curve);
4. be an identity or a structural inequality, not an estimate losing a factor growing with `A`;
5. be unconditional; equivalences with RH are labelled as such.

## 12. Big picture

A window of length `A` is a module over a finite local algebra, the Dirichlet ring truncated at
`e^A`; the tower is a chain of small extensions, one new fold per integer, generated by the primes,
with the Dirichlet ring as limit, self-similar under dilation through the Adams lifts and with Serre
duality as its Rosati involution. The integers of the window, as atoms, are the regular
representation of that algebra. The Tate flow acts on it by automorphisms; the commutators of the
window zeta operator with the flow are the Jordan counts, the point counts of punctured affine space
over residue rings that the degeneration produces as Tate pieces. Weil's window form is the
derivative of this family at dimension zero, plus the Gamma factor and the pole plane, whose exact
capacity bounds window negativity by `Ae^{A/2}`. Counts in positive dimension are positive for `ζ`
and for fakes alike; what remains is a positivity that survives the derivative at dimension zero,
uniformly along the tower.
