# The window receivers of a curve

- **ID:** window-receivers-of-a-curve
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0511 §2.1, A11.
- **Statement:** for a curve datum with distinct normalized eigenvalues `R`: purity is decided on the
  window of size `#R`; for a pure datum the Hardy interval is `{1}` on all large windows; point
  evaluation is form-bounded on windows `n ≤ #R` and unbounded on larger ones.
- **Lean:** `GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheWindowReceiversOfACurve.lean`;
  standard axioms only.

## Proof

Write `T(e) = Σ_{k,l} e_k e_l Re Σ_i β_i^{|k−l|}` and `F_e(z) = Σ_k e_k z^k`.

1. **Hermitian form.** For complex `a`, `Σ a_k ā_l τ_{|k−l|} = Σ_i P(β_i) conj P(β_i*)`, `z* = 1/z̄`, and its real
   part is `T(Re a) + T(Im a)`.
2. **Purity.** If `|z| ≠ 1` for `z ∈ R`, then `z* ≠ z` and `z* ∈ R`. Take `P` of degree `< #R` by Lagrange:
   `P(z) = 1`, `P(z*) = −1`, zero on the rest of `R`. The Hermitian energy is `−#{i : β_i ∈ {z, z*}} < 0`.
3. **Explicit formula.** `τ_j = s^j + s^{−j} − N_j s^{−j}` gives `T = H − P`, with
   `H(e) = 2F_e(s)F_e(1/s) + (2g−2)Σe_k²` and `P(e) = Σ_{k≠l} e_k e_l N_{|k−l|} s^{−|k−l|}`.
4. **Collapse.** With `B = ∏_{z∈R}(X−z)`, the tests `B(1 ± X^j)` lie in the radical of `T`, and
   `H = 2c(2 ± Y_j) + O(1)`, where `c = B(s)B(1/s) ≠ 0`, `Y_j = s^j + s^{−j}`, uniformly in `j`. For large `j` they
   take both signs, and `H − tP = (1−t)H` on the radical forces `t = 1`.
5. **Chain.** For `n ≤ #R`, Lagrange interpolation on `R` and Cauchy–Schwarz give
   `|F_e(z₀)|² ≤ (Σ_{z∈R} |ℓ_z(z₀)|²) T(e)`. For `n > #R`, `B` itself has `T = 0` and `B(z₀) ≠ 0` off `R`.

## Contrast

Over `ℤ` no finite window decides the sign: every bounded aperture admits off-line mimics of every width.
