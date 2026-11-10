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
- 2026-11-10 — created; C1–C3 analysed against the cached text (§6.1, §12, §15.2).
