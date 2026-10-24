# Kloosterman reciprocity in the balanced cross-scale Gram: minor arcs below the diagonal, the archimedean place on it

- **ID:** fable-2410-A
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2410/fable.md §2.3 A · BVI README §3.13, §7.4, §7.8.1
- **Statement:** For the Möbius row and the centred prime row `c' = (Λ−1)𝟙_{(Q,2Q]}`, the
  single-modulus statistic `Λ_p(c')` of the cross-scale dual norm satisfies
  `|Λ_p(c')| ≤ 24 (1+log 2Q)⁴ (p²/Q) Q^{−δ/4}` at every prime `Q^δ ≤ p ≤ Q^{1−δ}` (cross-scale
  exponent `θ ≤ 2−2δ`), and `|Λ_d(c')| ≤ C (d²/Q) e^{−c√log Q}` at every modulus `Q ≤ K d ≤ 2KQ`
  (the diagonal). Both unconditional.

## Goal
Opening A asks for a Gram improvement at balanced scales from Kloosterman reciprocity that is not
a short-window power saving, and whether every Gram improvement is the strip.

Answer.
1. The Kloosterman-fraction form `𝔅(p,n) = (π²/4) Σ_k B₂(k/p) csc²(πk n̄/p)` is the image under
   `n ↦ n̄` of a form diagonal in the additive characters of `n`. By the spectral law
   (`abs_kernelStatistic_le_fourier`) `Λ_p(c')` is controlled by the twists
   `S_r(ζ) = Σ_n (c'(n)/nʳ) ζⁿ` at the nontrivial `p`-th roots `ζ`; no sum in both `n` and `n̄`
   occurs. The binding input is the minor-arc estimate for `Σ μ(n)ζⁿ`, `Σ Λ(n)ζⁿ` at the exact
   denominator `p` (Vinogradov's bilinear method: additive, Beurling-selective), not Weil's bound.
2. Below the diagonal both actual rows have a power saving in the dual norm and in the cross-scale
   remainder, for arbitrary bounded small-scale coefficients. This is a theorem, so it is a Gram
   improvement that is not equivalent to the strip. It is parity-blind (Type I/II), consistent with
   BVI's parity-blindness of the cross-scale form. Generic Type-II rows stop at `θ = 6/5`, sharp
   cutoffs at `4/3`; the actual rows pass every `θ < 2`.
3. On the diagonal the low frequencies are archimedean: the statistic is a functional of the
   long-window partial sums `C(x) = Σ_{Q<n≤x} c'(n)` (any modulus, prime or composite). The
   de la Vallée Poussin / PNT saving is unconditional; a power saving there follows from
   `M(x) ≪ x^{1−η}` (Θ < 1), and the cross-scale form carries nothing beyond the long-window
   oscillation.
4. Ceiling: the receiver's cross-scale obstruction lives on the band `Q ≤ P^{1+o(1)}`, where it is
   the zero-free region. Summing the diagonal saving into the receiver at fixed damping `ε < 1/2`
   needs a power saving there, i.e. Θ < 1 (BVI §3.15), the opening's stated first rung.

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized: all four modules check with `lake --old env lean`, headline `#print axioms`
  = `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.BezoutValuationIncidence`
- [ ] 3 → 4 publication-ready

## Lean theorems (module : declarations)
- `BezoutValuationIncidence/MinorArcMoebiusSumsAtPrimeRootsOfUnity` — the minor-arc law.
  `norm_sum_moebius_mul_pow_le` (`|Σ_{n≤N} μ(n)ζⁿ| ≤ 2U + U W_p + (log₂N+1)√(typeIIBlockBound p U N)`,
  `1 ≤ U < p`), `rootHarmonicSum_le` (`W_p ≤ p(1+log p)`), `moebius_eq_vinogradov_decomposition`,
  `norm_sum_conv_conv_zeta_le` (Type I), `norm_sq_typeII_block_le`, `norm_sum_typeIIShort_le`
  (Type II), `sum_Ioc_root_mul_pow_le` (residue-class equidistribution of a geometric orbit).
- `BezoutValuationIncidence/TheDualNormIsMinorArcBelowTheDiagonal` — the Möbius row below the
  diagonal. `abs_kernelStatistic_moebiusWindowRow_le_minorArc`, `exists_minorArc_cutoff`,
  `abs_kernelStatistic_moebiusWindowRow_le_rpow` (`23 (1+log 2Q)³ (p²/Q) Q^{−δ/4}`),
  `eventually_abs_kernelStatistic_moebiusWindowRow_le` (`(p²/Q) Q^{−δ/8}`),
  `dualNorm_moebiusWindowRow_le_rpow`, `abs_rowBilinear_moebiusWindowRow_sub_main_le_rpow`
  (cross-scale remainder), `norm_sum_window_div_pow_le_of_twisted`.
- `BezoutValuationIncidence/TheDiagonalDualNormIsArchimedean` — the diagonal law.
  `abs_kernelStatisticAll_le_archimedean` (any row, any modulus, harmonic cut `J`),
  `norm_sum_window_div_pow_le_archimedean`, `exists_balanced_kernelStatisticAll_le` (rows with
  zero-free-region partial sums), `exists_balanced_kernelStatisticAll_moebiusWindowRow_le`
  (`C (d²/Q) e^{−√log Q/24}`).
- `BezoutValuationIncidence/TheCentredPrimeRowIsMinorArcBelowTheDiagonal` — the prime row and the
  synthesis. `norm_sum_vonMangoldt_mul_pow_le` (Vaughan, `U = V < p`),
  `abs_kernelStatistic_centredPrimeBlock_le_rpow` (`24 (1+log 2Q)⁴ (p²/Q) Q^{−δ/4}`),
  `dualNorm_centredPrimeBlock_le_rpow`, `exists_balanced_kernelStatisticAll_centredPrimeBlock_le`,
  `crossScale_dichotomy_moebius_and_centredPrime` (headline).

## Paper proof
Minor-arc law (p prime, ζ^p = 1, ζ ≠ 1, 1 ≤ U < p):
- `μ = 2μ_U − μ_U∗μ_U∗1 + (μ − μ_U)∗g`, `g = δ − 1∗μ_U` vanishing on `[1,U]`.
- Type I: `p ∤ d₁d₂`; geometric sums `≤ 2/|ζ^{d₁d₂}−1|`; `d₂ ↦ ζ^{d₁d₂}` injective into the
  nontrivial roots: `≤ U W_p`.
- Type II on `d ∈ (D,2D]`, `D = 2^i U`: Cauchy–Schwarz in `k`,
  `|T_D|² ≤ (Σ_{k≤N/D} g²)·D(D/p+1)(N/D + W_p)`; the block vanishes unless `N/D > U`.
- `Λ`: Vaughan with `U = V`; the `log m` weight removed by Abel summation; `|Λ| ≤ 1 + log N`.
- `U = ⌊Q^{δ/2}⌋` and Abel summation against `n^{-2}`, `n^{-3}`.
Diagonal law: Abel summation of `S_r(η^j)` against `C(x)`, `‖S_r(w)‖ ≤ A(2 + Q|w−1|)/(Q+1)^r`;
`|η^j−1| ≤ j|η−1|`, `Σ|η−1|^{−2} = (d²−1)/12`, `Σ 2|η−1|^{−1} ≤ d(1+log d)`, `|η−1| ≥ 4/d`;
harmonics cut at `J = ⌈e^{cs/2}⌉`, `s = √log Q`.

## Boundary of this formalization
Below the diagonal the power saving is proved at prime moduli (the opening's small-scale prime
row). At composite moduli the spectral bound over all nontrivial `d`-th roots includes roots of
small order, which need the divisor-weighted spectral form. On the diagonal all moduli are covered.

## Log
- 2026-10-24 — created, paper proof, formalized (four BVI modules), axiom audit clean.
