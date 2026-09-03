# Meixner–Pollaczek generating function of the archimedean semilocal Jacobi polynomials (Lean)

**Stage:** 3 (formalized).  **Module:**
`formal/GaloisForLFunctions/RHTower/SemilocalJacobiMeixnerPollaczekGeneratingFunction.lean`
(namespace `RHTower.MeixnerPollaczek`, wired into `RHTower.lean` after
`SemilocalCosineModeFirstOrderResponse`; axioms `[propext, Classical.choice, Quot.sound]`; lint clean).

**Statement.**  Let `p_n` be the corpus's orthonormal archimedean Jacobi polynomials
(`semilocalArchimedeanJacobiPolynomial`, recursively defined through `r_n = √((n+½)(n+1))`) and
`c_n = √((2n)!)/(2^n n!)` (`semilocalArchimedeanJacobiNormalization`).  For every `s ∈ ℝ`:

- `hasSum_mpGeneratingFunction`: for complex `‖w‖ < 1`,
  `Σ_n c_n p_n(s) w^n = (1 − iw)^{−1/4 + is/2} (1 + iw)^{−1/4 − is/2}` (`mpGeneratingFunction`).
- `mpGeneratingFunction_ofReal` / `hasSum_mpGeneratingFunction_real`: for real `|w| < 1` the sum is
  `(1 + w²)^{−1/4} exp(s · arctan w)`.
- Intermediate theorems: `mpGeneratingFunction_ode` (`(1 + w²)G′ = (s − w/2)G` on the disc),
  `mpDerivative_recurrence` (`G^{(n+2)}(0) = s G^{(n+1)}(0) − (n+1)(n+½) G^{(n)}(0)`),
  `mpCoefficient_recurrence` (`(n+2) c_{n+2}p_{n+2} = s c_{n+1}p_{n+1} − (n+½) c_n p_n`),
  `mpDerivative_eq_factorial_mul_coefficient` (`G^{(n)}(0) = n! c_n p_n(s)`).

So the corpus's polynomials are the Meixner–Pollaczek polynomials `P_n^{(1/4)}(s/2; π/2)` exactly
(`c_n p_n = P_n^{(1/4)}`), which is the first brick of MUST-148 (the boost generating function, the
diagonal cosine moments and the Route J profile `Φ`).

**Method.**  Cauchy's Taylor theorem on the unit disc (`Complex.hasSum_taylorSeries_on_ball`),
the first-order equation differentiated `n+1` times at `0` with only the coordinate Leibniz rule
(`iteratedDeriv_id_mul_zero_succ_of_contDiffAt` from `PRecursiveDFinite`), and the corpus identities
`(n+1) c_{n+1} = r_n c_n`, `c_{n+1} r_n = (n+½) c_n`.

**Next bricks (MUST-148).**  (i) Characteristic function of the Gamma measure at complex rapidity,
`∫ e^{zs} dμ = (cos z)^{−1/2}` on the strip `|Re z| ≤ π/4` (corpus majorant
`integrable_exp_pi_div_four_abs_mul_semilocalArchimedeanGammaDensity`); (ii) the boost row
`∫ G_s(w) e^{its} dμ = (cosh t)^{−1/2}(1 − iw tanh t)^{−1/2}`; (iii) the two-variable boost generating
function; (iv) the diagonal `m_n(t) = (cosh t)^{−1/2} P_n^{(0,−1/2)}(1 − 2 tanh² t)`.

**Update 2026-09-03.**  Bricks (i)–(iv) are done: see
`3-formalized/semilocal-boost-diagonal-closed-form-lean.md` (seven modules; main theorem
`cosineDiagonalMoment_eq`).  Only the Mehler–Heine limit (MUST-149) separates the Route J profile
from a Lean theorem.
