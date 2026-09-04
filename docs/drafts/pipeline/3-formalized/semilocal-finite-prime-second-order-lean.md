# The finite-`S` second-order assembly of the semilocal Jacobi data

**Stage:** 3 (formalized), 2026-09-04.  Closes MUST-178.  Two new modules
(`SemilocalQuadraticPathSecondOrder`, `SemilocalFinitePrimeSecondOrder`), wired into `RHTower.lean`,
axioms `[propext, Classical.choice, Quot.sound]`, lint clean.  Continues the one-prime
(`semilocal-one-prime-second-order-lean.md`) and two-prime (`semilocal-two-mode-bilinear-response-lean.md`,
`semilocal-boost-entry-bound-lean.md`) second-order theory.

**Setting.**  Rapidities `δ_a` and amplitudes `v_a` (`a : Fin k`), ray `ε = t v`.  The degree-two part
of the product weight `∏_a (1 + 2tv_a cos(δ_a s) + t²v_a²(1 + 2cos(2δ_a s)))` is
`1 + tA(s) + t²B(s)` with `A = Σ_a 2v_a cos(δ_a s)` and `B = ½A² + Σ_a v_a² cos(2δ_a s)`
(the pair terms are the `½A²`), so the Gram matrix is the quadratic path
`1 + tM₁ + t²M₂`, `M₁ = Σ_a v_a T(δ_a)`,
`M₂ = ½ Σ_{a,b} v_a v_b (T(δ_a+δ_b) + T(δ_a−δ_b)) + ½ Σ_a v_a² T(2δ_a)` (`rayGram_eq`).

**Generic engine** (`SemilocalQuadraticPathSecondOrder`): for any families `M₁ m, M₂ m`,
`(log det(1 + tM₁ + t²M₂))''(0) = 2 tr M₂ − tr M₁²` (`deriv_deriv_log_quadDet`) and through the Hankel
quotient `(a_n²)''(0) = r_n²(ΔΔ(2tr M₂ − tr M₁²) + (ΔΔ tr M₁)²)` (`deriv_deriv_quadSquaredRadius`).

**Theorem 1 — the quadratic form** (`rayLogJet_eq`, `deriv_deriv_log_rayDet`):

    (log D_n)''(0) along the ray = Σ_{a,b} v_a v_b B_{ab}(n) + Σ_a v_a² J_{2δ_a}(n),

`B_{ab} = J_{δ_a+δ_b} + J_{δ_a−δ_b} − tr(T(δ_a)T(δ_b))` the bilinear jets (diagonal included,
`J_0 = 2(n+1)`).

**Theorem 2 — the assembly** (`deriv_deriv_raySquaredRadius`, `deriv_deriv_raySquaredRadius_assembly`):

    (a_n²)''(0) = Σ_{a,b} v_a v_b · [bilinear squared-radius jet]_{ab} + Σ_a v_a² · [harmonic jet at 2δ_a]
               = Σ_a v_a² · [one-prime second-order jet]_a + Σ_{a≠b} v_a v_b · [bilinear squared-radius jet]_{ab},

using the **diagonal identity** `bilinearSquaredRadiusJet δ δ n + squaredRadiusJetOf J_{2δ} n =
onePrimeSecondOrderJet δ n` (`bilinearSquaredRadiusJet_diag_add_harmonic`).  So the second-order
response of the finite-`S` semilocal Jacobi matrix is *exactly* the sum of the owned one-prime jets and
the owned pairwise beat jets — no genuinely three-body term at second order — and every piece
carries its explicit boost-bound estimate (`abs_onePrimeSecondOrder_le`,
`abs_bilinearSquaredRadiusJet_sub_beat_le`): one-prime `O(q_a)` at first order, pairwise
`O(√(q_aq_b))·[beat jet]` at second order, one-prime self `O(q_a²)`, uniformly for `n ≪ min p`.

**Theorem 3 — the finite product against its truncation** (`abs_prod_sub_quadratic_le`): for `|t| ≤ 1`,

    |∏_{a∈s}(1 + tx_a + t²y_a) − (1 + tΣx + t²(Σy + ½((Σx)² − Σx²)))| ≤ |t|³ · ∏(1 + w_a) · (1 + Σ w_a)³,
    w_a = |x_a| + |y_a|,

proved by finset induction with the invariants `|X_s| ≤ W_s`, `|Y_s| ≤ W_s + W_s²`; together with
`abs_eulerFactor_sub_quadratic_le` (`60ε³` per factor) this controls the true Euler product to third
order at the weight level.

**Numerics** (`computations/routej-semilocal-scale/finite_prime_second_order.py`, `.log`;
`S = {101, 211, 307}`): the quadratic form against second differences of the true three-prime Euler
product to `10⁻⁷`, the radius-level formula to `10⁻⁶`; at the actual amplitudes the second-order term
is dominated by the pairwise beat part (e.g. `n = 50`: first `−4.8·10⁻⁴`, second `+2.2·10⁻³`, cross
part `2.2·10⁻³`, exact `1.7·10⁻³`), and first + second order reproduces the exact deviation to
`10⁻⁵`.

| module | content |
|---|---|
| `SemilocalQuadraticPathSecondOrder` | `quadPath`, `quadDet`, `quadLogJet`, `quadSlope`, `deriv_deriv_log_quadDet`; `quadPrevDet`, `quadSquaredRadius`, `quadRadiusSlope`, `quadSecondOrderJet`, **`deriv_deriv_quadSquaredRadius`** |
| `SemilocalFinitePrimeSecondOrder` | `rayFirst`, `raySecond`, `rayGram`, `rayM₁`, `rayM₂`, **`rayGram_eq`**; `cosineDiagonalMoment_zero`, `trace_rayM₁`, `trace_rayM₂`, `trace_rayM₁_mul_rayM₁`, **`rayLogJet_eq`**, `deriv_deriv_log_rayDet`, `raySquaredRadius`, **`deriv_deriv_raySquaredRadius`**, `bilinearSquaredRadiusJet_diag_add_harmonic`, **`deriv_deriv_raySquaredRadius_assembly`**, **`abs_prod_sub_quadratic_le`** |

**Left open (routine):** the determinant-level transfer of the third-order weight agreement to the
Hankel quotient (Lipschitz `det` near the identity), which turns the exact second-order structure into a
Taylor formula with explicit remainder for the true Euler product.
