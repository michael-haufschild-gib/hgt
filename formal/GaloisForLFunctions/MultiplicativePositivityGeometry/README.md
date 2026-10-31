# MultiplicativePositivityGeometry (MPG)

Namespace `GaloisForLFunctions.MultiplicativePositivityGeometry`; umbrella `MultiplicativePositivityGeometry.lean`; 38
modules. All results unconditional. ζ inputs: `Λ ≥ 0`, the residue at 1, local analytic factorization, ζ ≠ 0 on
`Re s ≥ 1` (for continuity of `−ζ'/ζ` up to the line), PNT error term (window realization), Dirichlet's theorem in
Mathlib's form (progressions), `RHTower.dlvp_half` (calibration).

## 1. Motivation

The only forcing mechanism in the corpus that actually excludes zeros is multiplicative: nonnegative Euler
log-coefficients, coupled across heights, force `ζ(1+it) ≠ 0` and, with a growth input, the classical zero-free
regions. MPG determines the complete content of that positivity: everything it forces, everything it permits, and
exactly what it can certify inside the strip.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Positive-definite function | `IsPosDef`, `IsEvenPosDef` | real Gram forms `Σcᵢcⱼφ(xᵢ−xⱼ) ≥ 0` on an additive group |
| Cosine trace | `cosineTrace` | `Σ wᵢ cos(λᵢu)`, `w ≥ 0` |
| Boundary datum / divisor | `IsBoundaryDivisor` | damped nonnegative weights `w(x)` with `x·trace → D(u)` as `x ↓ 0` |
| ζ boundary divisor | `zetaBoundaryDivisor`, `zetaBoundaryWeight`, `logFrequency` | pole order − zero order of ζ at `1+iu`; weights `Λ(n)n^{−1−x}` on `log n` |
| Signed datum | `IsSignedBoundaryDivisor` | absolutely summable signed weights with boundary limit |
| Nonvanishing subgroup | `nonvanishingSubgroup` | `{D ≠ 0}` for integer PD `D`, `D(0) = 1` |
| Twist | `twistedWeight`/`twistedDivisor`, `twistWeight`/`twistDivisor` | weights × `P(t₀λ)`, `P ≥ 0` cosine polynomial; divisor `Σ(a_k/2)(D(u+kt₀)+D(u−kt₀))` |
| Profile | `profileCoeff` | `m ↦ D(mt₀)` on `ℤ`, cosine polynomial `d₀ + 2Σd_m cos mθ` |
| Finite configuration, Bohr polynomial | `IsFiniteConfig`, `bohrPoly`, `apPoly`, `apWeight` | even `D` on `{0} ∪ ±Z`; `P_D(t) = D(0) + 2Σ D(z)cos(zt)` |
| Capacity configuration | `capacityDivisor`, `capFamDivisor` | `kδ₀ − Σ m(z)(δ_z + δ_{−z})` |
| One-prime factor | `progressionWeight`, `progressionDivisor` | geometric Euler factor; divisor `cos(cu)` on `(2π/h)ℤ` |
| Integral Euler product | `intWeight`, `roundMult`, `latticeMult` | `Π_p(1−p^{−s})^{−m(p)}`, `m(p) ∈ ℕ` |
| Positive cosine polynomial | `IsPosCosPoly`, `IsFamPosCosPoly` | finite nonnegative cosine sums (also over `G × ℝ`) |
| Joint (family) datum | `IsJointBoundaryDivisor`, `jointTrace`, `jointMode` | family over finite abelian `G`; divisor on `G × ℝ` |
| Exclusion inequality | `exclusion_iff` | `A/δ + G < B/(δ+η)`: pole `A`, zero weight `B` at distance `η`, growth `G` |
| Fejér nodes / extremal | `fejerNode`, `fejerWeight`, `fejerExtremal` | roots of `z^{K+2} = −1`; `b_j = sin((j+1)π/(K+2))` |
| Følner sets | `folnerSet`, `abFolnerSet` | `{Σ n_s s : 0 ≤ n_s < N}`, polynomial growth |
| Beurling model | `beurlingZetaModel`, `countLaplace` | `A(1+w)/w + (1+w)∫r(v)e^{−wv}dv` |

## 3. Language

- **Four boundary invariants:** (N) nonnegative weights; (Z) integer divisor; (S) simple pole `D(0) = 1`; (I) pole
  isolation `D ≤ 0` off 0.
- **Boundary vs interior:** the boundary divisor is a limit and is exact; interior zeros enter only through
  continuation and growth bounds.
- **Certificate vs input:** a nonnegative cosine/almost-periodic polynomial is a certificate; pole weight, zero weight
  and growth `(A, B, G)` are inputs. Purchase ratio = `a₁/a₀` (zero weight per unit pole weight).
- **Height-space positivity** (MPG: PD in `u`) is distinct from test-space positivity (Weil, Hodge).
- **Capacity:** total zero multiplicity a pole of order `k` can carry; counted in self-conjugate units on `G × ℝ`.
- **Margin `ε`:** log-coefficients `≥ −εΛ`.

## 4. Mechanisms

**A. Positive definiteness of the boundary**
1. Cosine traces of nonnegative weights are PD; PD survives pointwise limits and positive scaling ⇒ every boundary
   divisor is even PD.
2. Two-point Gram `|φ(h)| ≤ φ(0)`; three-point Gram gives translation laws when `φ(h) = ±φ(0)`.
3. Integer PD with `φ(0) = 1`: values `{−1,0,1}`, nonvanishing set a subgroup, `φ` a `±1` character on it.
4. Fejér progression vector: Gram along `0,h,…,(N−1)h` ⇒ progression mass `≤ φ(0)/2`.
5. Følner Gram forms over `{Σ n_z z}`: polynomial growth gives a slow step where every shift is seen by
   `(1−ε)|F_N|` pairs ⇒ zero-mass laws without commensurability, on any abelian group.

**B. Realization**
6. Twist = convolution: product-to-sum turns a cosine twist into shifted copies of the divisor; with base `D_ζ = δ₀`
   every nonnegative Bohr polynomial is realized by ζ-quotients.
7. Rounding: greedy integer exponents keep the running prime error `≤ log(n+1)`; Abel summation bounds the defect
   series uniformly on `Re s = 1+x`; prime powers carry bounded mass ⇒ same divisor.
8. Fejér truncation (interval overlaps) + Dirichlet-mean approximate identity `Q_n` ⇒ locally finite PD `D` is a
   pointwise limit of positive cosine polynomials; range theorem turns limits into weights.
9. Exponential partition `φ_N = e^{−a_N t} − e^{−a_{N−1}t}` makes blocks differences of ζ-traces; uniform continuity
   of `Re(−ζ'/ζ)` off `(0,0)` + Toeplitz ⇒ one Dirichlet series realizes `D`.
10. Character orthogonality on finite `G` turns family weights into fibrewise shifted ζ-traces.
11. Prime windows `(e^{λ_k}, e^{λ_k}(1+1/(k+1)²)]` with PNT error reproduce non-logarithmic frequencies.

**C. Rigidity / obstruction**
12. Baire: a pointwise limit of continuous functions cannot jump by 1 between two dense sets ⇒ regularity forbids
    dense nonvanishing subgroups.
13. Rankin–Selberg: Gram of `cos(u log n)` under the prime measure tends to `diag(1,½,…)` ⇒ Bessel inequality.

**D. Interior**
14. Dual quadrature on roots of `z^{K+2} = −1` gives the extremal Fejér certificate.
15. Geometric-mean damping `δ* = √(Aη/G)` turns exclusion into AM–GM.
16. Off-resonance sampling of `(1 − cos γt)P(t)` ⇒ multi-frequency purchase cap.
17. Cyclic fibre: restricting a PD trace to `⟨(g,0)⟩` gives `Σ_k T(kg) ≥ 0`; at order two only `|T(h)| ≤ T(0)`.
18. Decay-exponent law: one-sided growth rates of `log|Z|` replace boundary limits.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Every boundary divisor is even PD | `IsBoundaryDivisor.isEvenPosDef` | proved |
| Integer PD, `D(0)=1`: zero at `u` ⇒ pole at `2u`; no pole ⇒ `D = δ₀`; locally finite ⇒ `δ₀`, `1_{cℤ}`, or alternating on `cℤ` | `boundary_zero_forces_double_pole`, `boundary_eq_delta_of_no_pole`, `boundary_trichotomy` | proved |
| Integer boundary divisor with `D(0)=1` is `δ₀`, `1_{cℤ}`, alternating, or constant 1 (no local finiteness) | `boundary_tetrachotomy` | proved |
| `D_ζ = δ₀`, hence `ζ(1+iu) ≠ 0` from PD alone; prime phases at distinct heights asymptotically orthonormal | `zetaBoundaryDivisor_eq`, `riemannZeta_boundary_ne_zero_of_posDef`, `zeta_boundary_gram_tendsto` | proved |
| (N)+(Z)+(S)+(I) ⇒ `D = δ₀`; each invariant necessary (realized countermodels) | `boundary_forcing_law`, `isolation_necessary`, `simplicity_necessary`, `integrality_necessary`, `nonnegativity_necessary` | proved |
| Interior zeros invisible: `ζ(s)Φ(s+κ)` has all four invariants and vanishes at `1−κ+iπ/ℓ` | `interior_zero_invisible` | proved |
| Total zero mass `Σ_{z>0} −D(z) ≤ D(0)/2` (PD, `D ≤ 0` off 0, any heights); sharp; on any abelian group `Σ_{p≠0} −φ(p) ≤ φ(0)` | `total_zero_mass_le`, `doublePoleProfile_total_mass`, `total_offOrigin_mass_le` | proved |
| Pole-isolated integer PD with `D(0)=k` ⇔ `kδ₀ − Σm(z)(δ_z+δ_{−z})`, `2Σm ≤ k` | `isolated_boundary_classification` | proved |
| Margin: integer, isolated, `w ≥ −εΛ` ⇔ capacity with `2Σm ≤ k+ε`; simple pole forces `δ₀` iff `ε < 1` | `margin_classification`, `simple_pole_margin_threshold` | proved |
| Finite profile / finite configuration: PD ⇔ Bohr polynomial ≥ 0 ⇔ boundary divisor ⇔ integral Euler product | `boundary_profile_iff`, `finite_boundary_divisor_iff`, `integral_boundary_profile_iff` | proved |
| Range: boundary divisor ⇔ pointwise limit of positive cosine polynomials; `1_ℚ` PD but not a divisor | `isBoundaryDivisor_iff_tendsto_posCosPoly`, `rationalIndicator_not_boundaryDivisor` | proved |
| Locally finite Bochner: divisor ⇔ even PD ⇔ divisor of one series `ΣΛ(n)g(log n)n^{−s}` ⇔ divisor of an integral Euler product | `locallyFinite_boundary_divisor_iff`, `arithmetic_bochner`, `integral_bochner` | proved |
| Summable PD on any `Γ` pushed by `h : Γ →+ ℝ` is realized (integrally); every summable even PD on `ℝ` is an integral divisor; σ-additivity; dense supports occur | `summable_isBoundaryDivisor`, `summable_integral`, `summable_real_integral`, `isBoundaryDivisor_tsum`, `ratLattice_ne_zero_iff` | proved |
| Rank collapse: integer rank-`r` profile with unit pole has rank-≤1 support | `rank_profile_collapse` | proved |
| Convolution law; primes of one residue class realize the summable cone | `IsBoundaryDivisor.twist_bohr`, `class_isBoundaryDivisor`, `progression_realizes` | proved |
| Rankin–Selberg Bessel `D_f(0)² + 2ΣD_f(u)² ≤ R`; simple poles of `f` and `f⊗f` force `D_f = δ₀`; sharp | `rankinSelberg_bessel`, `rankinSelberg_forcing`, `rankinSelberg_bessel_sharp` | proved |
| Families: joint forcing law `δ₀` or `δ₀ − δ_{(h,0)}`, `2h = 0`, exception realized; capacity exact; summable/locally finite family Bochner; integer family classification | `joint_boundary_classification`, `family_isolated_iff`, `family_summable_bochner`, `family_locallyFinite_bochner`, `joint_integer_classification` | proved |
| Siegel exception: order-two member `1/ζ(s+1−β)` keeps all invariants and vanishes at real `β`; unpaired zero never excluded | `siegel_isJointBoundaryDivisor`, `siegel_member_zero`, `unpaired_real_zero_unexcluded` | proved |
| Exact Fejér barrier `a₁ ≤ 2cos(π/(K+2))a₀`, attained | `cosinePolynomial_first_le_fejer`, `fejer_barrier_attained`, `fejer_barrier_sharp` | proved |
| Multi-frequency cap `a(γ) ≤ 2a(0)` for any finite almost-periodic certificate | `multiFrequency_purchase_le_two`, `multiFrequency_width_cap` | proved |
| Growth-to-forcing: exclusion ⇔ `√A + √(Gη) < √B` ⇔ `η < (√B−√A)²/G`; degree-K width cap `< (3−2√2)/(2L)`; degree one excludes nothing | `exclusion_iff`, `exclusion_iff_lt_width`, `fejer_width_cap`, `fejer_width_cap_lt_universal`, `degree_one_excludes_nothing` | proved |
| dlVP region `β ≤ 1 − (2−√3)²/((5/2)log γ + C)` as the instance `(3,4,G)`, optimal for that input | `xiZero_re_le_dlvp`, `dlvp_input_consistent` | proved |
| Decay-exponent mass law `Σα_z ≤ k/2`; Hölder barrier 1/2; Beurling count `nθ ≤ 1/2` | `decay_mass_law`, `holder_barrier`, `beurling_zero_count` | proved |

## 6. Tools

**Developed**
- PD calculus: `IsEvenPosDef.comp_addMonoidHom`, `.smul`, `.mul_fejerFactor`, `.mul_fejerFactor_comp`,
  `.restrict_zero`, `.sum_finset_mul_nonneg`, `isEvenPosDef_of_tendsto`, `IsEvenPosDef.tsum_mul_cos_nonneg`,
  `tsum_nonneg_of_gram`.
- Boundary calculus: `IsBoundaryDivisor.smul`, `.sum`, `.twist`, `.twist_bohr`, `.round`, `.round_log`,
  `isBoundaryDivisor_zero_of_bounded`, `isBoundaryDivisor_tsum`.
- Følner machinery: `folnerSet`, `abFolnerSet`, `exists_folner_step`, `exists_abFolner_step`, `card_shift_mem_ge`.
- Approximation: `dirichletMean`, `abs_dirichletMean_le`, `convPoly_eq`, `famPoly_eq`, `tendsto_toeplitz`,
  `exists_posCosPoly_of_isBoundaryDivisor`, `isBoundaryDivisor_of_tendsto_posCosPoly`,
  `isJointBoundaryDivisor_of_tendsto_famPosCosPoly`.
- Baire tools: `exists_open_near_continuous`, `not_tendsto_continuous_of_dense`.
- ζ up to the line: `zetaX`, `continuousAt_zetaX`, `exists_modulus_zetaX`.
- Interior: `exclusion_iff_quadratic`, `exclusion_at_geometric_mean`, `exclusion_iff_restricted`, `fejer_quadrature`,
  `abs_cosSum_le`, `cyclic_fibre_sum_nonneg`.
- Countermodels: `doublePoleProfile`, `halfZeroCoeff`, `signedCoeff`, `lattice_isBoundaryDivisor`,
  `alternating_isBoundaryDivisor`, `const_isBoundaryDivisor`, `ratLattice`, Siegel family `siegelWeight`.

**To build**
- A positive-definite object attached to the open strip `½ < σ < 1` (not a boundary datum).
- Littlewood and Vinogradov–Korobov inputs stated as range-limited exclusion inputs (`exclusion_iff_restricted`
  shape) with `δ`-dependent growth `G(δ)`.
- Full range of the boundary map for non-locally-finite, non-summable configurations.

## 7. Open questions

1. Which PD structure survives continuation into the strip? `interior_zero_invisible` and the Siegel family show it
   cannot be a boundary datum, nor any of the four invariants.
2. Growth law with `δ`-dependent `G(δ)`: what width does the VK input certify when stated on its natural range?
3. Characterize boundary divisors that are neither locally finite nor summable (dense supports, non-summable
   orders). PD alone is insufficient (`1_ℚ`); is first-Baire-class PD sufficient?
4. Integral realization beyond the summable and locally finite cones.
5. Families: is there a joint invariant beyond PD on `G × ℝ` that separates the two-torsion exception from ζ?
6. Beurling: the count bound `nθ ≤ 1/2` is attained by the half-zero datum; is the integer-count Beurling threshold
   `γ = 3/2` attained by an actual generalized-prime system?

## 8. Traps

| Trap | Fact |
|---|---|
| One harmonic inequality is the whole positivity | It is one Gram form; PD is all of them |
| More frequencies/primes/harmonics buy more | Every finite certificate has `a(γ) ≤ 2a(0)` (`multiFrequency_purchase_le_two`) |
| Higher degree reaches ratio 2 | `2cos(π/(K+2)) < 2` at every `K`; `K = 1` excludes nothing |
| Boundary completeness reaches the interior | `interior_zero_invisible`: all four invariants, interior zero |
| PD alone forces vanishing | Needs integrality: half zeros `D(±1) = −½` are realized (`integrality_necessary`) |
| (Z) is integrality of prime data | It is meromorphic continuation; integer exponents in `{0,1,2}` give half zeros (`integral_half_zero`) |
| PD ⇒ boundary divisor | False: `1_ℚ`; the extra condition is regularity (first Baire class) |
| Boundary divisors are locally finite | False: `ratLattice` has support `2πℚ` |
| Double poles behave like simple poles | `ζ²/(ζ(s+it₀)ζ(s−it₀))` carries a zero at `t₀`; mass `D(0)/2` is sharp |
| Multiplicative positivity excludes Siegel zeros | Order-two fibres have purchase ratio 1; `ζ(s)/ζ(s+1−β)` keeps all invariants |
| A better constant is a better method | The width is fixed by `(A,B,G)`; only better input helps (`dlvp_input_consistent`) |
| Nonnegativity can be weakened freely | Threshold `ε < 1` exactly; one copy of `Λ` buys one boundary zero |

## 9. Context

| Uses | # imports | Interface |
|---|---|---|
| RHTower | 8 | `dlvp_half`, PNT error, residue/differentiability of `−ζ'/ζ`, prime-power sums, Gauss sums |
| ArithmeticCastelnuovoSeveri | 2 | boundary orders, `tendsto_zetaRealLogDeriv_boundary`, `fejerAutoCoeff`, `periodicPoleZeta` |
| HTGeometry | 1 | `cosinePolynomial`, `purchase_width_cap` |
| ArithmeticPositiveDuality | 1 | `extendByZero`, `signCharacter_isEvenPosDef` |

| Used by | # files | Imports |
|---|---|---|
| ArithmeticPositiveDuality | 5 | PositiveDefiniteFunctions, ZetaBoundaryDivisor, ArithmeticRealization, GrowthToForcing |
| BiarithmeticGaugeGeometry | 3 | TotalZeroMass, SummableBochner |
| StripBochnerWeilForcing | 2 | BoundaryPositivity, GrowthToForcing |
| ArithmeticCorrespondencePositivity | 2 | TotalZeroMass, BoundaryPositivity |
| RenormalizedBiarithmeticGeometry | 1 | ExactFejerBarrier |
| MainTheorems | 1 | umbrella |

| Neighbour | Relation |
|---|---|
| ArithmeticCastelnuovoSeveri | quadratic (Hodge) side certifies blindness; MPG is the coefficient-positivity side that forces |
| ArithmeticPositiveDuality | integer PD = sign characters; MPG supplies the boundary PD functions and the purchase barrier |
| StripBochnerWeilForcing | attempts the interior PD object that MPG proves cannot be a boundary datum |
| BVI, THIM, SquareRootThreshold | their receivers are width statements; the growth law fixes which widths positivity reaches |
| RHTower zero-free regions | dlVP/Littlewood/VK are instances of the growth-to-forcing law |

## 10. Big picture

MPG closes the book on what nonnegative Euler coefficients can do. On the line `Re s = 1` the answer is exact and
complete: positivity is equivalent to positive definiteness of the boundary divisor, every positive-definite
configuration with mild regularity is realized by an honest Euler product over the rational primes, and the four
invariants together force exactly `ζ(1+it) ≠ 0` and nothing more. Integrality of prime data, choice of progression,
number of channels and degree of the certificate add nothing.

For RH this is a clean negative compass. Multiplicative positivity cannot see the interior: realized Euler products
satisfy every boundary invariant and vanish inside the strip, and a real zero on a self-conjugate member is never
excluded. Every interior gain must therefore come from the growth input or from a new interior object, not from a
cleverer positive certificate. The dlVP–VK line of zero-free regions is one inequality between pole weight, zero
weight and growth; any RH route that leans only on coefficient positivity is bounded by the universal width cap.
