# Family continuation: the walk of review-1011 §13

- **ID:** family-continuation-walk
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [review-1011 fable §13](../../../reports/review-1011/fable.md) · cards [metaplectic-mobius-descent](metaplectic-mobius-descent.md), [quasi-rh-fixed-strip-improvement](quasi-rh-fixed-strip-improvement.md)
- **Statement:** Leg A (a half-plane by continuing the reciprocals of a family across its rightmost zeros) and leg B (from a half-plane to the line) close to RH.

## Goal

Walk the stages W0–W8 of §13 by conjecture and proof. Every Lean theorem is unconditional; a
statement that needs the external half-plane carries it inside an equivalence. Lean:
`formal/GaloisForLFunctions/FamilyContinuationTheory/`.

Notation of the external source (cached text `logs/review-2410-current-audit/quasi-rh-seven-eighths.txt`):
probe `I_η = Σ_m B_m A_m`, `B_m` the completed cubic theta row twisted by `η χ_•(m)`,
`A_m = Y^{-1} Σ_s c_σ(s) W₁(q_s/Y)(q_s/Y)^{-1/2+iv} q_s^{-1/2} g_{χ_s}(s,−m)` the additive polynomial,
`χ_s` the sextic residue symbol; low estimate `|I| ≤ ‖B‖‖A‖`; `Σ_m|A_m|² ≪ (Q/Y)(1+P^{1/6}+P²/Y)`, `P=Y²/Q`.

## Conjecture ledger

| # | Conjecture | Status | Lesson |
|---|---|---|---|
| C1 | (B★ of §5.5) The Möbius weights of the Gram form save a power at the exceptional (sixth-power) frequencies | REFUTED on paper | The weights `μ(d)` invert the coprimality of two columns: a sieve with density `1/ζ_K(2)`. At a sixth-power frequency `k` the complete correlation of two coprime columns is the reciprocity factor, with no dependence on `k`: `F(s₁,s₂;k)=χ_{s₁}(−1)\bar χ_{s₁}(s₂)χ_{s₂}(s₁)`. The exceptional part of `Σ_m w(m)|A_m|²` is `(Q/Y³)·#{k=a⁶, q_k ≲ P}·|Σ_s c_σ(s)W₁(…)|²`: a nonnegative main term for nonnegative columns. It is the dual of an incomplete character sum (row ball `Q` shorter than the conductor `Y²` of a pair). Survivor: the two-column correlation theorem (Lean, below) |
| C2 | The exponent `1/6` is `1/n` for averaging symbols of order `n`; a cyclotomic field with more roots of unity lowers it | REFUTED on paper (second half) | The count of `n`-th power frequencies is `P^{1/n}`. The conversion of Möbius needs `μ·g(χ)` to be an explicit multiple of a cubic Gauss sum; the duplication formula `g(χ)g(χρ)=\barχ(4)g(χ²)g(ρ)` gives this exactly for `χ` cubic and `ρ` quadratic. Order six is forced by "quadratic (explicit Gauss sum) × cubic (theta coefficients known)" |
| C3 | Centering the columns (zero plain sum) removes the exceptional term and keeps the signal | REFUTED on paper | The principal row is `(Σ_s c_σ(s)W₁(…))·(Mellin integral of 1/L)`: the factor `R(A,s)` of the probe makes the cross reciprocity trivial and the column sum factors out. Signal and exceptional energy are both carried by the plain column sum |
| C4 | The Cauchy–Schwarz step of the low estimate can be replaced by an exact evaluation of the row sum after reflection (the reflected row carries the scalar `ζ(m)`, a product of normalized sextic and quadratic Gauss sums of the row) | REFUTED by exponents `[D]` | The exact row sum is a sum of sextic Gauss sums of `m` twisted by a character of modulus `μ s`; with the trivial bound it loses `Z^{0.49}` against Cauchy–Schwarz at the published scales, and the saving of the sextic Kubota series (`Q^{-1/3}` for the principal twist) does not cover it. Mean squares over rows are stronger than pointwise evaluations here |
| C5 | A column with zero plain sum on a ray class removes the exceptional term for free: the fixed character `χ_s(b*)/ξ(s)` is nonprincipal modulo the primes of `S` | REFUTED on paper | The `S`-part of the frequency restores the principal character: the exceptional frequencies are `a⁶e` with `e` supported on `C` and `S`, and for one class of `S`-exponents the fixed part is principal. A positive proportion of the exceptional frequencies carries the main term |
| C6 | Cauchy–Schwarz in the dual variable `μ` of the reflected row, or restricted to the span of the reflected rows (dimension `D=Q²/Z<Q`), beats Cauchy–Schwarz in the row | REFUTED on paper | The matrix of quadratic symbols `(μ/m)` has norm `√max(D,Q)` in both directions (quadratic large sieve); the additive polynomial is not generic for that span: its main part is aligned with the reflected rows, and this alignment is the signal |
| C7 | Split the additive polynomial into its main term and a remainder without exceptional energy; evaluate the pairing of the reflected rows with the main term exactly | OPEN, no first step | The main term of a sum of sextic Gauss sums twisted by `\bar χ_s(m)` is governed by the sextic theta function, whose coefficients are not known; the scalar `ζ(m)` of the reflected row is multiplicative in `m`, the theta coefficients are not |

## Lean

| Module | Result |
|---|---|
| `FamilyContinuationTheory/TwistedColumnsCorrelateThroughOneResidue` | `sum_column_mul_conj_column_of_coprime`: the correlation of two additive columns of coprime moduli is one term; `sum_weight_mul_column_mul_conj_column`: the weighted second moment is a multiplicative form in the frequency; `sum_exceptional_correlation`: no cancellation among the frequencies on which both characters are `1` |
| `FamilyContinuationTheory/ContinuationFromACommonSignal` | `exists_differentiableOn_eq_of_signal_le`: a kernel whose signal is `O(Z^b)` extends to `Re s>b`; `ne_zero_of_signal_le`; `ne_zero_of_common_signal`: a direct bound `Z^{a₁}` and a comparison `Z^{a₂}` with the signal give the half-plane `Re s>max a₁ a₂`; `le_of_improving_bounds` and `ne_zero_of_family_common_signal`: the supremum step and the family form (Proposition 2.1 of the external source as a native theorem) |
| `FamilyContinuationTheory/TheTwoLegsGiveTheRiemannHypothesis` | `isSignalKernel_zetaKernel`: `exp((s−c)²)/((s−1)ζ(s))` is a signal kernel; `riemannZeta_ne_zero_of_signal_le`, `xiZeroHalfPlaneBound_of_signal_le`, `xiZeroHalfPlaneBound_of_common_signal`: leg A for `ζ` ends in the corpus predicate `XiZeroHalfPlaneBound`; `riemannHypothesis_of_signal_le_of_jasDressedPSD_one`: a signal bound with exponent in `[½,1)` and `JasDressedPSD 1` give RH |

**The two open inputs as Lean propositions.** (A) `∃ c b K Z₀, ½ ≤ b ∧ b < 1 ∧ 0 < Z₀ ∧ ∀ Z ≥ Z₀, ‖signal (zetaKernel c) 2 Z‖ ≤ K * Z ^ b`; (B) `JasDressedPSD 1`. The external theorem supplies (A) with every `b > 7/8`.

## Stage notes

- **W2.** Answer to (B★): No. The boundary of the published geometry is not moved by the signs of
  the source. The term `P^{1/6}` is the multiplicity of the sixth-power frequencies in the dual of
  an incomplete sum; it is absent in the balanced geometry (`P=1`, boundary `11/12`) and is the
  price of the asymmetry that gives `7/8`.
- **Boundary formula** `[D]`: with `x+y+L=1`, low exponent `(5x+y)/12`, principal shift
  `c=x/3−5/6+L/6`: boundary `11/12−L/4`; `L=0` gives `11/12`, `L=1/6` gives `7/8`, and `L=1` would
  give `2/3`. Inside this probe family leg A has a floor above `½`.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Log
- 2026-11-10 — created; C1–C5 analysed against the cached text (§5.1, §6.1, §12, §15.2); three modules compiled (single-file check, no output) and wired through `FamilyContinuationTheory` into `MainTheorems`.
