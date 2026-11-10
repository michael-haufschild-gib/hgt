# Sign-free purity mechanisms: the Frobenius shadow and the separation shadow over ℤ

- **ID:** sign-free-purity-mechanisms
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0911/fable.md` §6, questions (S1) and (S2)
- **Lean:** `formal/GaloisForLFunctions/SignFreePurityMechanisms/` (umbrella
  `SignFreePurityMechanisms.lean`, imported by `MainTheorems.lean`), namespace
  `GaloisForLFunctions.SignFreePurityMechanisms`
- **Statement:** ℤ carries the Frobenius and the separation mechanism as structure and as
  receivers, with exact costs. Neither is a producer.

## Questions

- **(S1)** Is there a ring with commuting endomorphisms `F_n`, `F_mF_n=F_{mn}`, whose fixed-point
  counts are `N(n)=Λ(n)+1+1/(n²−1)`, on which vanishing to order `m` at the fixed points of the
  degrees of a window costs less than `m` times the window's Chebyshev count?
- **(S2)** Is there a sign-free prime-side quantity that bounds the fibre multiplicity of the
  height map on the zeros?

Notation: `ψ_nF=F(Xⁿ)` on `ℤ[X]`; `θ(S)=Σ_{p∈S}log p`; `δ_p a=(a−a^p)/p`; `c(u)` the cubic-spline
trace `2 Re S(u)`.

## (S1) The Frobenius

**T1 (no literal count).** For `n≥2` not a prime power, `1<N(n)<2`. No family of sets has
cardinalities `N(n)`.
*Proof.* `Λ(n)=0` and `0<1/(n²−1)<1`; `6` is not a prime power. ∎
`specPointCount_mem_Ioo`, `not_exists_card_eq_specPointCount`.

**T2 (logarithmic count).** For `n≥2`, `Λ(n)=log Φ_n(1)`. Over `𝔽_p`,
`Φ_{p^k}=(X−1)^{p^k−p^{k−1}}`, `k≥1`.
*Proof.* `Φ_{p^k}(1)=p`, `Φ_n(1)=1` otherwise; in characteristic `p`,
`Φ_{p^k m}=Φ_m^{p^k−p^{k−1}}` for `p∤m`. ∎
`vonMangoldt_eq_log_eval_one_cyclotomic`, `cyclotomic_prime_pow_zmod`.

**T3 (where the power map fixes a fibre).** For a prime `p` and `n≥1`: `xⁿ=x` for every
`x∈𝔽_p` ⇔ `p−1 ∣ n−1`. For `n≥2` this happens at no more than `d(n−1)` primes.
*Proof.* (⇐) Fermat. (⇒) A generator `g` of `𝔽_p^×` has `g^{n−1}=1`. The map `p↦p−1` is
injective into the divisors of `n−1`. ∎
`forall_pow_eq_self_iff`, `ncard_fixed_fibres_le`.

**T4 (where the power map is a Frobenius).** For a prime `q` and `n≥1`:
`(X+1)ⁿ=Xⁿ+1` over `𝔽_q` ⇔ `n` is a power of `q`. For `n≥2`,
`Λ(n)=Σ_{q prime, x↦xⁿ additive in characteristic q} log q`.
*Proof.* Write `n=q^v m`, `q∤m`. Then `(X+1)ⁿ=(X^{q^v}+1)^m`, whose coefficient at `X^{q^v}` is
`m`, while `Xⁿ+1` has coefficient `0` there unless `m=1`. For `n≥2` at most one prime qualifies. ∎
`isFrobeniusAt_iff`, `eq_of_isFrobeniusAt`, `vonMangoldt_eq_finsum_log_isFrobeniusAt`.

**T5 (the derivative at `p`).** The identity is the only ring endomorphism of ℤ, and it is a
Frobenius lift at every prime. For `p ∣ a`, `a≠0`: `ord_p(δ_p a)+1=ord_p(a)`. For every `m`:
`p ∣ δ_p^j a` for all `j<m` ⇔ `p^m ∣ a`. `δ_p a=0` ⇔ `a^p=a` ⇒ `a∈{0,1,−1}`.
*Proof.* `δ_p(pb)=b(1−p^{p−1}b^{p−1})`, and the second factor is a unit modulo `p`; hence
`p^m ∣ δ_p(pb)` ⇔ `p^m ∣ b`. Induct on `m`. If `a^p=a≠0` then `a^{p−1}=1`. ∎
`ringHom_int_eq_id`, `natCast_dvd_sub_pow`, `padicValInt_fermatQuotient_add_one`,
`forall_dvd_iterate_fermatQuotient_iff`, `fermatQuotient_eq_zero_iff`,
`eq_zero_or_eq_one_or_eq_neg_one_of_pow_eq_self`.

**T6 (the product formula leaves no slack).** If `a≠0` vanishes to `δ_p`-order `m` at every
prime of a finite set `S`, then `m·θ(S)≤log|a|`, with equality for `a=Π_{p∈S}p^m`.
*Proof.* By T5, `Π_{p∈S}p^m ∣ a`. ∎
`mul_sum_log_le_log_abs`, `log_prod_pow_eq`.

**T7 (no archimedean zero derivative).** A ring endomorphism `φ` of `ℤ[X]` with `(φX)′=0` is
`F↦F(a)` for an integer `a`.
*Proof.* `φX` is a constant `a`, and `φ` is determined by `φX`. ∎
`exists_eq_C_eval_of_derivative_eq_zero`.

**T8 (Stepanov's identity modulo `n`, all orders).** For `A,B∈ℤ[X]`, all `n,k`:
`(A·ψ_nB)^{(k)}≡A^{(k)}·ψ_nB (mod n)`.
*Proof.* `(ψ_nB)′=nX^{n−1}ψ_n(B′)`; induct on `k`. ∎
`C_dvd_iterate_derivative_mul_expand_sub`.

**T9 (inseparability at a set of primes costs its primorial).** Let `F∈ℤ[X]` be monic.
(a) If `F′≡0 (mod p)` for every `p∈S`, then `Π_{p∈S}p ∣ deg F`; for `deg F≥1`,
`θ(S)≤log deg F`. (b) If `F` is a `p^{k_p}`-th power modulo each `p∈S`, then
`Π_{p∈S}p^{k_p} ∣ deg F`. (c) `ψ_{p^k m}F≡(ψ_mF)^{p^k} (mod p)`, and every root of `ψ_{p^k m}F`
modulo `p` has multiplicity `≥p^k`. (d) With `n=Π_{p∈S}p^{⌈log_p m⌉}`, every root of `ψ_nF`
modulo a prime of `S` has multiplicity `≥m`, and `log n≤θ(S)+|S|·log m`.
*Proof.* (a) The coefficient of `X^{d−1}` in `F′` is `d`. (b) Degrees of powers; distinct prime
powers are coprime. (c) `ψ_pG=G^p` over `𝔽_p`. (d) `p^{⌈log_p m⌉}≤pm`. ∎
`prod_dvd_natDegree_of_map_derivative_eq_zero`, `sum_log_le_log_natDegree`,
`prod_pow_dvd_natDegree`, `map_expand_pow_mul`, `pow_le_rootMultiplicity_map_expand`,
`le_rootMultiplicity_map_expand_prod`, `log_prod_pow_clog_le`.

## (S2) Separation

**T10 (separation principle).** A self-map of a set preserving a function injective on the set
is the identity. Hence: for `L/K` Galois and `v` on `L` invariant under `Gal(L/K)`, a polynomial
over `K` on whose roots `v` is injective has its roots in `K`; this applies to the spectral norm
of a normed field; a real polynomial whose complex roots have pairwise distinct absolute values
has only real roots.
`fixed_of_injOn`, `mem_range_algebraMap_of_injOn`, `mem_range_algebraMap_of_spectralNorm_injOn`,
`im_eq_zero_of_norm_injOn`.

**T11 (archimedean Newton polygon).** Let `a_0,…,a_n∈ℂ` be nonzero with
`|a_{j+1}|²≥9|a_j||a_{j+2}|`, `ρ_j=|a_j|/|a_{j+1}|`, `P=Σa_jz^j`.
(a) For `3ρ_i≤|z|≤ρ_{i+1}/3` (no upper bound if `i=n−1`),
`|P(z)−a_{i+1}z^{i+1}|<|a_{i+1}z^{i+1}|`.
(b) `P` has `i+1` zeros, with multiplicity, in `|z|<3ρ_i`.
(c) Distinct zeros of `P` have distinct absolute values.
(d) Of three zeros of increasing absolute value, the largest exceeds nine times the smallest.
(e) If the `a_j` are real, all zeros of `P` are real.
*Proof.* (a) With `t_j=|a_j||z|^j`: `t_{j+1}≥3t_j` for `j≤i` and `t_{j+1}≤t_j/3` for `j≥i+1`,
since `ρ_j≤ρ_i` for `j≤i` and `ρ_j≥9ρ_i` for `j>i`. A sequence decaying by `3` has
`s_1+⋯+s_m≤(s_0−s_m)/2`, so the other terms sum to at most `t_{i+1}−(t_0+t_n)/2`.
(b) Rouché against `a_{i+1}z^{i+1}` on `|z|=3ρ_i`. (c) By (a) every zero lies in some annulus
`3ρ_{i−1}≤|z|<3ρ_i`; by (b) the two discs carry multiplicities `i` and `i+1`, so the annulus
carries one zero. (d) The annulus index is strictly increasing in `|z|`, so the indices of the
three zeros differ by at least two, and `ρ_{i+1}≥9ρ_i`. (e) (c) and T10. ∎
`HasCoeffGaps.norm_gapPoly_sub_lt`, `HasCoeffGaps.zeroSumBall_gapPoly`,
`HasCoeffGaps.eq_of_mem_annulus`, `HasCoeffGaps.injOn_norm_zeros`,
`HasCoeffGaps.nine_mul_norm_lt`, `im_eq_zero_of_coeff_gaps`.

**T12 (ζ has no coefficient gaps).** There are ordinates `0<τ₁<τ₂<τ₃≤2τ₁` of zeros of `Ξ`. No
polynomial with the gaps of T11 vanishes at `τ₁², τ₂², τ₃²`.
*Proof.* Some dyadic range carries at least three ordinates of critical zeros
(`RHTower.exists_many_critical_ordinates_dyadic`). `τ₃²≤4τ₁²<9τ₁²` contradicts T11 (d). ∎
`exists_three_critical_ordinates`, `exists_critical_ordinates_not_hasCoeffGaps`.

**T13 (the height separates iff the prime traces are bounded).** The reflection `ρ↦1−ρ̄`
preserves the nontrivial zeros and their height. If the height is injective on the zeros, every
zero is on the line. For `σ≥0`: any two zeros at one height have real parts within `2σ`
⇔ zero width `≤σ` ⇔ `∃K ∀p: |c(log p)|≤Kp^σ`. At `σ=0`: the height is injective on the zeros
⇔ `∃K ∀p: |c(log p)|≤K` ⇔ RH.
*Proof.* T10 for the reflection; `Re ρ−Re(1−ρ̄)=2(Re ρ−½)`; the two-sided prime criterion
(`CollectiveDiophantineGeometry.zeroWidth_iff_twoSided_primes`). ∎
`re_eq_half_of_injOn_im`, `fibre_spread_le_iff_zetaZeroWidth_le`,
`fibre_spread_le_iff_twoSided_primes`, `injOn_im_iff_twoSided_primes`,
`injOn_im_iff_riemannHypothesis`.

**T14 (ultrametric Newton polygon, sides of length one).** Let `v` be a nonarchimedean absolute
value on a field `L` and `f=Σ_{k≤n}a_kX^k` with `a_k≠0` and `v(a_j)v(a_{j+2})<v(a_{j+1})²`;
`ρ_j=v(a_j)/v(a_{j+1})`.
(a) A root `z` of `f` in `L` has `v(z)=ρ_i` for some `i<n`.
(b) If `z` is a root, `f/(X−z)` has no zero on the sphere `v(w)=v(z)`.
(c) The roots of `f` in `L` are simple and `v` is injective on them.
(d) If `K` is a complete ultrametric field and `f∈K[X]` satisfies the hypothesis for the norm
of `K`, then `f` splits over `K` and its `n` roots have pairwise distinct norms. In a Galois
extension of `K` this is T10 with its hypothesis supplied by (c) for the spectral norm.
(e) Every partial sum of `Σ_k p^{k²}X^k` splits over `ℚ_p`.
*Proof.* Let `r=v(z)>0` and `t_k=v(a_k)r^k`. The sequence `t` is positive and strictly
log-concave, so after a step that does not increase it decreases strictly, and before a step
that does not decrease it increases strictly.
(a) If one term `a_kz^k` were strictly largest, `v(f(z))` would be its size. So the largest size
is attained at two indices `i<l`. From `t_{i+1}≤t_i`, `t_l<t_i` for `l≥i+2`; hence `l=i+1` and
`t_i=t_{i+1}`.
(b) Let `r=ρ_j` and `g=f/(X−z)=Σb_kX^k`: `b_k=a_{k+1}+zb_{k+1}`, `a_0=−zb_0`. From the top,
`v(b_k)=v(a_{k+1})` for `k≥j`, because `v(zb_{k+1})=r·v(a_{k+2})<v(a_{k+1})` is
`t_{k+2}<t_{k+1}`. From the bottom, `v(b_k)·r=v(a_k)` for `k<j`, because `zb_{k+1}=b_k−a_{k+1}`
and `v(b_k)<v(a_{k+1})` is `t_k<t_{k+1}`. On the sphere the terms of `g` have sizes `t_k/r`
for `k<j` and `t_{k+1}/r` for `k≥j`; the term `k=j` is strictly largest since
`t_k<t_j=t_{j+1}` for `k<j` and `t_l<t_{j+1}` for `l≥j+2`.
(c) `f(w)=(w−z)g(w)` and `f′(z)=g(z)`.
(d) In an algebraic closure of `K` the spectral norm is a nonarchimedean absolute value
extending the norm, because `K` is complete. A conjugate `y` of a root `x` is a root of `f`
with the minimal polynomial of `x`, hence with the spectral norm of `x`; by (c) `y=x`. The
minimal polynomial of `x` is then a power of `X−x`, and `x` is a simple root of `f`, so its
degree is one. No separability of `K` is used.
(e) `k²+(k+2)²=2(k+1)²+2`. ∎
`HasSimpleSlopes.exists_slope_of_isRoot`, `HasSimpleSlopes.eval_divByMonic_ne_zero`,
`HasSimpleSlopes.derivative_eval_ne_zero`, `HasSimpleSlopes.injOn_isRoot`, `injOn_norm_isRoot`,
`injOn_spectralNorm_rootSet`, `mem_range_algebraMap_of_strict_logConcave`,
`mem_range_of_isRoot_of_isAlgClosed`, `splits_of_strict_logConcave`,
`card_roots_of_strict_logConcave`, `padicTheta_splits`, `padicTheta_roots`.

## Answers

**(S1): no.**
- The counts are not cardinalities (T1). Their prime part is a logarithmic count: the order of
  the intersection of the primitive `n`-torsion with the fixed point `1` (T2), equivalently the
  weighted number of primes at which `x↦xⁿ` is a Frobenius (T4). Fixing a fibre pointwise is a
  different and rarer event (T3).
- The Frobenius exists one prime at a time. On ℤ it is the identity, its derivative at `p` is
  the Fermat quotient, and the order it measures is the `p`-adic order (T5). The constants of
  the derivative are `0, ±1`: nothing plays the part of the `q`-th powers in Stepanov's
  auxiliary.
- The cost is exact. Order `m` at every prime of `S` costs `m·θ(S)`, with equality (T6): on the
  diagonal Stepanov's inequality "zeros × order ≤ degree" is the product formula.
- On `ℤ[X]`, Stepanov's identity holds modulo `n` (T8), not archimedeanly (T7). Multiplicity `m`
  modulo every prime of `S` is cheap, `θ(S)+|S|log m` (T9 d), but one operator inseparable at
  every prime of `S` has degree divisible by the primorial of `S` (T9 a, b): it pays the
  Chebyshev count it is meant to bound, and the multiplicity it buys is modulo `p`.

**(S2): yes as a receiver, no as a producer.**
- The mechanism is T10. For ζ the invariant is the height, and the sign-free prime-side quantity
  is the absolute cubic-spline trace: its boundedness at the primes is fibre multiplicity one,
  and its growth exponent is half the horizontal spread of the fibres (T13).
- A producer of separation from coefficient data exists in both worlds. Over a complete
  ultrametric field any strict log-concavity of the coefficient norms suffices and the
  polynomial splits over the base field (T14): no hypothesis on the roots remains. Over ℂ gaps
  of factor `9` replace the strict inequality (T11); they force lacunary roots (T11 d), so this
  producer does not apply to ζ (T12).

## Lean modules

| Module | Theorems |
|---|---|
| `ThePointCountOfSpecZIsLogarithmic` | T1, T2 |
| `ThePowerMapIsAFrobeniusAtOnePrime` | T3, T4 |
| `TheFermatQuotientIsTheDerivativeAtAPrime` | T5, T6 |
| `SimultaneousInseparabilityCostsThePrimorial` | T7, T8, T9 |
| `SeparationForcesRationality` | T10 |
| `CoefficientGapsSeparateTheRoots` | T11 |
| `TheZerosOfZetaHaveNoCoefficientGaps` | T12 |
| `TheHeightSeparatesTheZerosIffThePrimeTracesAreBounded` | T13 |
| `TheUltrametricNewtonPolygonSeparatesTheRoots` | T14 |

Each module passes `lake --old env lean` without errors or warnings; every listed capstone
depends on `propext`, `Classical.choice`, `Quot.sound` only.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3

## Not done
- The Riemann hypothesis for the Carlitz–Goss zeta function in the corpus's language. T14 (d) is
  its Newton-polygon step; the coefficient valuations of the Goss polynomials are not computed.
