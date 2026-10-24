# Kloosterman reciprocity in the balanced cross-scale Gram: minor arcs below the diagonal, the archimedean place on it

- **ID:** fable-2410-A
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-2410/fable.md §2.3 A · BVI README §3.13, §7.4, §7.8.1
- **Statement:** The dual norm `Σ_{p∈S} |Λ_p(c')|/p` of the Möbius window row `c' = μ·1_{(Q,2Q]}`
  has an unconditional power saving at every cross-scale exponent `θ = 2 log P/log Q < 2`; on the
  diagonal `θ = 2` it is bounded by the long-window partial-sum oscillation of `c'` (the archimedean
  place), which gives the de la Vallée Poussin saving unconditionally and a power saving from `Θ < 1`.

## Goal
Opening A asks for a Gram improvement at balanced scales from Kloosterman reciprocity that is not a
short-window power saving, and asks whether every Gram improvement is the strip.

Answer:
1. The Kloosterman-fraction form `𝔅(p,n) = (π²/4) Σ_k B₂(k/p) csc²(πk n̄/p)` is the image of a form
   that is *diagonal in additive characters of `n`*: `𝔅(p,n) − m_p = (p²/2π²) Σ_{p∤jk} cos(2πjkn/p)/(jk)²`
   (corpus: `sum_mul_residuePotential_sub_gcd_eq_spectral`, `abs_kernelStatistic_le_fourier`). The
   kernel statistic is a combination, with absolutely summable weights, of the additive twists
   `S₂(ζ) = Σ_n (c'(n)/n²) ζⁿ` at nontrivial `p`-th roots `ζ`. No complete sum in `n` and `n̄`
   appears, so Weil's bound is never the binding input: the binding input is the *minor-arc*
   estimate for `Σ μ(n) ζⁿ` (Vinogradov's bilinear method — additive, Beurling-selective).
2. **Below the diagonal** (`Q^δ ≤ p ≤ Q^{1−δ}`): Vinogradov's Type I/II method at the prime
   denominator `p` gives `|Σ_{n≤N} μ(n)ζⁿ| ≪ (N p^{−1/2} + N U^{−1/2} + (Np)^{1/2} + Up) log³N`, hence
   `|Λ_p(c')| ≤ (p²/Q) Q^{−δ/8}` for all large `Q`, uniformly in `p`: a power saving in the open
   regime `1 < θ < 2`, for arbitrary bounded small-scale rows. This is a Gram improvement that is a
   theorem, hence not equivalent to the strip. It is parity-blind (Type I/II), consistent with
   BVI's parity-blindness of the cross-scale form.
3. **On the diagonal** (`p ≍ Q`): all low frequencies `jk/p` are archimedean. Abel summation in the
   spectral form gives, for every row `c'` on `(Q,2Q]` with partial-sum oscillation `A`, every
   modulus `d` and every `J ≥ 1`,
   `|Λ_d(c')| ≤ (A/(Q+1)²)[π²d²/36 + Q d(1+log d)(1+log J)/2 + O(d³/Q)] + (d²/(12J)) Σ|c'|/n²`.
   For Möbius, the de la Vallée Poussin rate makes this `(d²/Q) e^{−c√log Q}` on `d ≍ Q`. The
   diagonal saving is the long-window Mertens oscillation; a power saving there follows from `Θ < 1`.
4. Ceiling: the obstruction of the receiver's cross-scale Gram is localized on the band
   `Q ≤ P^{1+o(1)}` and is archimedean there.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Paper proof of the minor-arc law (p prime, ζ^p = 1, ζ ≠ 1, 1 ≤ U < p, `W_p = Σ_{η∈T_p} 2/|η−1| ≤ p(1+log p)`):
- `μ = 2μ_U − μ_U∗μ_U∗1 + (μ − μ_U)∗g`, `g = δ − 1∗μ_U` (`typeIIShort U`), `g = 0` on `[1,U]`, `|g| ≤ 1+τ`.
- `2μ_U`: at most `2U`.
- Type I: `Σ_{d₁,d₂≤U} μμ Σ_m ζ^{d₁d₂m}`; `p ∤ d₁d₂`, geometric sums `≤ 2/|ζ^{d₁d₂}−1|`; for fixed
  `d₁`, `d₂ ↦ ζ^{d₁d₂}` is injective into `T_p`: total `≤ U W_p`.
- Type II on dyadic blocks `d ∈ (D,2D]`, `D = 2^i U`: Cauchy–Schwarz in `k`,
  `|T_D|² ≤ (Σ_{k≤N/D} g²)·Σ_{d,d'} min(N/D, 2/|ζ^{d−d'}−1|) ≤ E(N/D)·D(D/p+1)(N/D + W_p)`;
  each residue class of `d'` meets `(D,2D]` at most `D/p+1` times. Blocks with `DU ≥ N` vanish.
- Abel summation against `n^{−2}`, `n^{−3}` on `(Q,2Q]` and the spectral bound
  `abs_kernelStatistic_le_fourier`.
Diagonal law: Abel summation of `S₂(η^j)`, `|η^j − 1| ≤ j|η−1|`, `Σ|η−1|^{−2} = (d²−1)/12`,
`Σ|η−1|^{−1} ≤ d(1+log d)/2`, truncation of the harmonic series at `J`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Weil/Kuznetsov at `θ = 2`: the kernel is diagonal in additive
  characters with weights `1/(jk)²`; the low frequencies carry the mass and are archimedean.
- **Strongest positive survivor:** items 2 and 3 above.
- **New insight:** the cross-scale obstruction is the archimedean place on the diagonal band.
- **Status:** paper proof above; Lean in progress.

## Log
- 2026-10-24 — created in 1-in-progress
