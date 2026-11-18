# Binary carries and distinct prime divisors of central binomial coefficients

- **ID:** bpf-binary-carry-cancellation-resolution
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** docs/reports/review-1811/obstacles-summary.md §2.6
- **Statement:** Binary carries, adjacent quotient-interval pairings, growing quotient bands, and smooth-integer division trees cannot produce an $O_\varepsilon(X^{3/2+\varepsilon})$ cancellation law for distinct ordinary prime divisors of $\binom{2\lfloor k/2\rfloor}{\lfloor k/2\rfloor}$ with positivity and spectral methods excluded; the discrete binary-carry mean is an exact positive-offset tent function bounded below by $X/3$ across both adjacent quotient intervals, smooth division trees cancel only the middle dyadic octave while top-octave carries alias $2r-1$ with $2r$, moving-cutoff quotient bands admit a uniform summable $O((X/(2Q+2))^{15/8})$ bound with single-band RH equivalence, outer-cutoff bands near $\sqrt{X}$ admit no asymptotic gain over trivial summation by Bertrand's postulate, sub-square-root integer-norm prime edits ($c_0<1/2$, dyadic count first total $o(X^{3/2})$) still violate $O(X^{b+1})$ across $[1/2,\beta)$, and for actual primes all distinct-prime binomial carry and smooth dyadic first totals are unconditionally $O(X^{15/8})$ exact.

## Gates
- [x] 0 → 1  in-progress: exact formulation across binary carries, smooth division trees, and quotient bands
- [x] 1 → 2  fully-proven: complete dependency-closed paper proofs of all four structural theorems and corollaries
- [x] 2 → 3  formalized: Lean 4 modules in `GaloisForLFunctions/ExceptionalLayerTheory/`, wired into `ExceptionalLayerTheory.lean`

## Lean 4 Formalization
- `formal/GaloisForLFunctions/ExceptionalLayerTheory/BinaryCarryTentAndAdjacentQuotientIntervals.lean`
  - `discreteQuotientMean_binaryCarryProfile_eq_piecewise`
  - `discreteQuotientMean_binaryCarryProfile_eq_half_sub_tent`
  - `discreteQuotientMean_binaryCarryProfile_adjacent_intervals`
  - `ordinaryLastClassTotal_two_eq_half_prefix_sub_tent`
  - `mangoldt_binaryCarry_first_total_le_three_halves`
  - `ordinaryLastClassTotal_bound_excludes_zero_and_bounds_zeroReSup`
  - `binomialDistinctPrimeTotal_bound_excludes_zero_and_bounds_zeroReSup`
- `formal/GaloisForLFunctions/ExceptionalLayerTheory/DivisionTreesOfDyadicSmoothCounts.lean`
  - `smoothIntegerCount_eq_half_add_odd`
  - `two_mul_smoothIntegerCount_sub_eq_alternating`
  - `two_mul_smoothIntegerCount_sub_eq_middle_octave_cancel`
  - `alternatingSmoothSum_eq_sum_odd_roots`
  - `alternatingSmoothSum_two`
  - `alternatingSmoothSum_buchstab`
  - `sum_range_two_mul_smooth_dyadic_eq`
  - `smooth_complement_uniquely_selects_primes`
  - `centralBinom_carry_top_octave_aliasing`
- `formal/GaloisForLFunctions/ExceptionalLayerTheory/GrowingQuotientBandsInBinomialCarries.lean`
  - `sum_movingOddQuotientBand_eq_ordinaryLastClassTotal`
  - `movingQuotientSlice_eq_interior_add_boundary_strip`
  - `abs_movingQuotientSlice_le_of_prefix`
  - `exists_movingOddQuotientBand_uniform_and_summable`
  - `exists_movingOddQuotientBand_fifteen_eighths_exact`
  - `movingQuotientSliceTrivial_lower_bound`
  - `movingQuotientSlice_bound_excludes_zero_and_bounds_zeroReSup`
  - `riemannHypothesis_iff_one_movingQuotientSlice`
  - `exists_outerQuotientPairBand_sub_seven_eighths`
  - `exists_outerQuotientPairBand_seven_eighths_exact`
  - `outerQuotientPairBand_abs_eq_trivial_of_primeFree`
  - `eventually_exists_sqrt_band_near_trivial`
- `formal/GaloisForLFunctions/ExceptionalLayerTheory/PrimeEditObstructionForBinomialCarries.lean`
  - `editedLastClassTotal_bound_excludes_fake_zero`
  - `editedLastClassTotal_frequently_large_at_fake_zero`
  - `exists_isEdit_strict_line_carry_obstruction`
  - `exists_sub_sqrt_count_edit_with_carry_obstruction`
  - `exists_ordinaryLastClassTotal_sub_seven_eighths`
  - `exists_binomialDistinctPrime_and_smooth_sub_seven_eighths`
  - `exists_binomialDistinctPrime_and_smooth_fifteen_eighths_exact`
- `formal/GaloisForLFunctions/ExceptionalLayerTheory/CompleteResolutionOfBinomialCarryPrimeCancellation.lean`
  - `complete_adjacent_quotient_and_tent_resolution`
  - `complete_smooth_division_tree_resolution`
  - `complete_growing_quotient_band_resolution`
  - `complete_prime_edit_barrier_and_unconditional_corollaries`

## Mathematical Summary

1. **Exact tent law and non-cancellation of adjacent quotient intervals:**
   For $A(u)=\mathbf{1}_{2\mid u+1}$ and $m\ge 1$, $B_m(X):=\sum_{k<X}A(\lfloor k/m\rfloor)$ equals $Qm$ when $2\mid\lfloor X/m\rfloor$ and $X-(Q+1)m$ when $2\nmid\lfloor X/m\rfloor$ ($Q=\lfloor\lfloor X/m\rfloor/2\rfloor$), equivalently $\frac{X}{2}-\frac{1}{2}\min(X\bmod 2m,2m-X\bmod 2m)$. For $Q\ge 1$, every $m$ in either $\lfloor X/m\rfloor=2Q$ or $\lfloor X/m\rfloor=2Q+1$ satisfies $\frac{Q}{2Q+1}X\le B_m(X)\le\frac{X}{2}$ ($\ge X/3>0$). While von Mangoldt weights $\Lambda(m)-1$ cancel $\zeta$-zeros to $O(X^{3/2})$ unconditionally, any $O(X^{b+1})$ bound ($1/2\le b<1$) on `binomialDistinctPrimeTotal j X` excludes all $\zeta$-zeros in $\Re s>b$ and forces $\Theta\le b$.

2. **Smooth-integer division trees and top-octave parity aliasing:**
   For all $n\ge 0$ and $y\ge 2$, $2\Psi(n,y)-\Psi(2n,y)=\sum_{j\le 2n,P^+(j)\le y}(-1)^j=\Psi(\lfloor n/2\rfloor,y)-(\Psi_{\mathrm{odd}}(2n,y)-\Psi_{\mathrm{odd}}(n,y))$, decomposing over odd $y$-smooth roots $u\le M$ with weight $\lfloor\log_2(M/u)\rfloor-1$ and satisfying $\Phi(M,y)=\Phi(M,z)+\sum_{z<p\le y}\Phi(\lfloor M/p\rfloor,p)$ ($2\le z\le y$) with $\Phi(M,2)=\lfloor\log_2 M\rfloor-1$. While $\Psi(x,y)+\sum_{m\in(y,B]}g(m)\lfloor x/m\rfloor=x$ ($B<(y+1)^2$) uniquely forces $g=\mathbf{1}_{\text{prime}}$, the central-binomial carry aliases $2r-1$ and $2r$ identically ($\lfloor 2n/(2r-1)\rfloor\bmod 2=\lfloor 2n/(2r)\rfloor\bmod 2=\mathbf{1}_{r\le n}$) whenever $N<2r-1$ and $n\le N$.

3. **Growing quotient-band trichotomy:**
   Moving-cutoff slices $S_d(X)=\sum_{m\le\lfloor X/(d+1)\rfloor}m w(m)+\sum_{\lfloor X/(d+1)\rfloor<m\le\lfloor X/d\rfloor}(X-dm)w(m)$ partition `ordinaryLastClassTotal 2 X` across $d=2Q+1$, satisfy $|S_d(X)|\le C_\beta(X/(d+1))^{1+\beta}$ ($\beta>20999/24000$, exact $15/8$) summably over all odd bands ($\sum_{Q<X}|S_{2Q+1}(X)|\le C_{\mathrm{sum}}X^{15/8}$), beat the unsigned benchmark $\ge X^2/(64(d+1)^2\log X)$ on wide bands, and satisfy single-slice equivalence with `RiemannHypothesis` for every $d\ge 1$. Outer-cutoff paired bands satisfy $|\mathcal{T}_{\mathrm{out}}(Q,X)|\le C_\beta X(X/(2Q))^\beta$ (exact $7/8$), whereas near $\sqrt{X}$ Bertrand's postulate produces short bands above $\sqrt{X}$ of width $\le 13$ with $(1-\varepsilon)\mathcal{T}_{\mathrm{out}}^{\mathrm{triv}}(Q,X)\le|\mathcal{T}_{\mathrm{out}}(Q,X)|$.

4. **Prime-edit selectivity barrier and unconditional $O(X^{15/8})$ corollaries:**
   Across $\sigma\in(1/2,14/15)$, two-sided prime edits with strict fake zeros on $\Re s=\sigma$ force $|\mathrm{editedLastClassTotal}(e,q,X)|>KX^{b+1}$ infinitely often for all $b\in[1/2,\sigma)$; on $\beta\in(1/2,27001/48000)$, signed grouped edits achieve sub-square-root norm-count remainder $c_0<1/2$ (so $\sum_{k<X}|2N_B(\lfloor k/2\rfloor)-N_B(2\lfloor k/2\rfloor)|\le C_{\mathrm{dyad}}X^{c_0+1}$ with $c_0+1<3/2$) while still forcing $\Omega(X^{b+1})$ blow-up in `editedLastClassTotal`. For actual primes, `ordinaryLastClassTotal q X`, `binomialDistinctPrimeTotal j X`, the central binomial distinct-prime first total, and `smoothDyadicFirstTotal X` are all unconditionally $O(X^{15/8})$ exact.

## No-go closure
- **Obstruction mechanism:** Logarithmic differentiation of $G(s)=(s-1)\zeta(s)\exp(L(e,s)+\mathrm{editRem}(e,s))$ cancels $-\zeta'/\zeta$ identically against the edited generator weight, leaving a simple pole $G'/G$ at every zero $\rho_0\ne 1$ of $G$, independent of divisibility, unique factorization, or sub-square-root norm-count remainders.
- **Strongest positive survivor:** All four master theorems above are unconditionally proved and formalized in Lean 4.
