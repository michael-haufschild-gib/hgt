# Kloosterman reciprocity in the balanced cross-scale Gram: minor arcs below the diagonal, the archimedean place on it

- **ID:** fable-2410-A
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-2410/fable.md §2.3 A · BVI README §3.13, §7.4, §7.8.1
- **Statement:** The dual-norm statistic `Λ_p(c')` of the Möbius row and of the centred prime row on
  `(Q,2Q]` has an unconditional power saving `(log Q)^4 Q^{-δ/4}` at every prime `Q^δ ≤ p ≤ Q^{1-δ}`
  (cross-scale exponent `θ ≤ 2 − 2δ`); on the diagonal `Q ≤ K d ≤ 2KQ` it is bounded by the
  long-window partial sums of the row, which gives `C (d²/Q) e^{-c√log Q}` at every modulus.

## Goal
Opening A asks for a Gram improvement at balanced scales from Kloosterman reciprocity that is not
a short-window power saving, and whether every Gram improvement is the strip.

Answer.
1. The Kloosterman-fraction form `𝔅(p,n) = (π²/4) Σ_k B₂(k/p) csc²(πk n̄/p)` is the image under
   `n ↦ n̄` of a form diagonal in the additive characters of `n`: by the spectral law
   (`abs_kernelStatistic_le_fourier`) `Λ_p(c')` is controlled by the twists
   `S_r(ζ) = Σ_n (c'(n)/nʳ) ζⁿ` at the nontrivial `p`-th roots `ζ`. No sum in both `n` and `n̄`
   occurs; the binding input is the minor-arc estimate for `Σ μ(n) ζⁿ`, `Σ Λ(n) ζⁿ` at the exact
   denominator `p` (Vinogradov's bilinear method, additive, Beurling-selective), not Weil's bound.
2. Below the diagonal the dual norm has a power saving for both actual rows, for arbitrary bounded
   small-scale coefficients. This is a theorem, so it is a Gram improvement that is not
   equivalent to the strip; it is parity-blind (Type I/II), in line with BVI's parity-blindness of
   the cross-scale form. Generic Type-II rows stop at `θ = 6/5`, sharp cutoffs at `4/3`.
3. On the diagonal the low frequencies are archimedean. The statistic is a functional of the
   long-window partial sums `C(x) = Σ_{Q<n≤x} c'(n)`: the de la Vallée Poussin / PNT saving is
   unconditional, a power saving there follows from `M(x) ≪ x^{1-η}` (Θ < 1), and nothing in the
   cross-scale form goes beyond the long-window Mertens oscillation.
4. Ceiling: the receiver's cross-scale obstruction lives on the band `Q ≤ P^{1+o(1)}` and is the
   zero-free region there. Summing the diagonal saving into the receiver at a fixed damping
   `ε < 1/2` needs a power saving, i.e. Θ < 1 (BVI 3.15), the opening's stated first rung.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Paper proof
Minor-arc law (p prime, ζ^p = 1, ζ ≠ 1, 1 ≤ U < p, `W_p = Σ_{η∈T_p} 2/|η−1| ≤ p(1+log p)`):
- `μ = 2μ_U − μ_U∗μ_U∗1 + (μ − μ_U)∗g`, `g = δ − 1∗μ_U` vanishing on `[1,U]`, `|g| ≤ 1+τ`.
- Type I: `p ∤ d₁d₂`; geometric sums `≤ 2/|ζ^{d₁d₂}−1|`; `d₂ ↦ ζ^{d₁d₂}` injective into `T_p`:
  `≤ U W_p`.
- Type II on `d ∈ (D,2D]`, `D = 2^i U`: Cauchy–Schwarz in `k`,
  `|T_D|² ≤ (Σ_{k≤N/D} g²) · D(D/p+1)(N/D + W_p)` (each residue class meets `(D,2D]` at most
  `D/p+1` times); the block vanishes unless `N/D > U`.
- Total: `|Σ_{n≤N} μ(n)ζⁿ| ≤ 2U + U W_p + (log₂N+1)√(2(1+H_N³)(N²/p + N²/U + N²W_p/(Up) + N W_p))`.
- `Λ`: Vaughan with `U = V`, the `log m` weight removed by Abel summation, long coefficients
  `|Λ| ≤ 1 + log N`.
- `U = ⌊Q^{δ/2}⌋` and Abel summation against `n^{-2}`, `n^{-3}` give the power saving.
Diagonal law: Abel summation of `S_r(η^j)` against `C(x)`: `‖S_r(w)‖ ≤ A(2 + Q|w−1|)/(Q+1)^r`;
`|η^j − 1| ≤ j|η−1|`, `Σ|η−1|^{−2} = (d²−1)/12`, `Σ 2|η−1|^{−1} ≤ d(1+log d)`, `|η−1| ≥ 4/d`;
harmonics cut at `J = ⌈e^{cs/2}⌉`, `s = √log Q`.

## Log
- 2026-10-24 — created; paper proof complete; Lean modules in BezoutValuationIncidence:
  `MinorArcMoebiusSumsAtPrimeRootsOfUnity`, `TheDualNormIsMinorArcBelowTheDiagonal`,
  `TheDiagonalDualNormIsArchimedean`, `TheCentredPrimeRowIsMinorArcBelowTheDiagonal`.
