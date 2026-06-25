/-
# Hurwitz N=2 — wiring the Laurent kernel to discharge the row relations

Discharges the `hrow`/`h0`/`h1`/`hc` hypotheses of `HurwitzN2Theorem.hurwitz_n2` using the committed
`linear_laurent_top` (the cpow Laurent kernel), `psi_regroup` (the `Ψb = ∑_k c_k E_k` regroup),
`tailFactored_zero_eq` (`R_0(0) = ζ(s,−n)`), and the positive-ray restriction `z = log t`.
-/
import GaloisForLFunctions.Hurwitz.N2Theorem
import GaloisForLFunctions.Hurwitz.N2Laurent
import GaloisForLFunctions.Hurwitz.N2TailValue
import GaloisForLFunctions.Hurwitz.N2PsiRegroup
import GaloisForLFunctions.Hurwitz.N2TailAnalytic

open Complex HurwitzN2Tail HurwitzN2Main

namespace HurwitzN2Final

/-- **The singular exponential on the positive real ray is a `cpow`.** For `t > 0`,
`e^{w·(Real.log t)} = (t:ℂ)^w`. So at `z = log t` the block's `e^{−(s+k)z}` becomes `(t:ℂ)^{−(s+k)}`, the
form `linear_laurent_top` consumes. -/
theorem exp_mul_ofReal_log_eq_cpow (w : ℂ) {t : ℝ} (ht : 0 < t) :
    Complex.exp (w * ((Real.log t : ℝ) : ℂ)) = (t : ℂ) ^ w := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  rw [Complex.cpow_def_of_ne_zero htc, ← Complex.ofReal_log ht.le, mul_comm]

/-- `e^{log t} = t` on the positive ray (the base coordinate `x = e^z`). -/
theorem exp_ofReal_log {t : ℝ} (ht : 0 < t) :
    Complex.exp ((Real.log t : ℝ) : ℂ) = (t : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log ht]

/-- The regrouped coefficient `c_k(x) = ∑_j (q_{kj}+q_{jk})(−n+x)·tailFactored s j n x + l_k(−n+x)` is
continuous at `x = 0` (polynomials + the analytic tail). -/
theorem coeff_continuousAt {s : ℂ} (hs : 1 < s.re) (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ)
    (l : Fin 3 → Polynomial ℂ) (k : Fin 3) :
    ContinuousAt (fun x : ℂ =>
      (∑ j : Fin 3, ((q k j + q j k).eval (-(n : ℂ) + x)) * tailFactored s (j : ℕ) n x)
        + (l k).eval (-(n : ℂ) + x)) 0 := by
  have htail : ∀ j : Fin 3, ContinuousAt (fun x : ℂ => tailFactored s (j : ℕ) n x) 0 :=
    fun j => ((tailFactored_analytic hs (j : ℕ) n).continuousOn).continuousAt
      (IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) (by norm_num))
  apply ContinuousAt.add
  · apply continuousAt_finset_sum
    intro j _
    exact (((Polynomial.continuous _).comp (by fun_prop)).continuousAt).mul (htail j)
  · exact ((Polynomial.continuous _).comp (by fun_prop)).continuousAt

end HurwitzN2Final
