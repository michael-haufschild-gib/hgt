import GaloisForLFunctions.RHTower.Sieve.HalaszMontgomeryDual
import GaloisForLFunctions.RHTower.Sieve.KernelDoubleIntegral

/-!
# The integral Halász–Montgomery bound

Combining the duality step, the expansion of the dual coefficients and the continuous Schur test:

```text
   ∫_E ‖A‖²  ≤  M · ∑_n ‖a_n‖² ,     M ≥ the row and column masses of the kernel.
```

The exposé's smoothing weight `2 − n/N` is not used: the dyadic route to the kernel bound does not
need it, so the kernel here is the plain `∑_{n < N} exp(i v log(n+1))`.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The logarithmic-phase kernel of a Dirichlet polynomial of length `N`. -/
noncomputable def plainKernel (N : ℕ) (v : ℝ) : ℂ :=
  ∑ n : Fin N, Complex.exp (((v * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)

theorem continuous_phase (L : ℝ) :
    Continuous fun s : ℝ => Complex.exp (((s * L : ℝ) : ℂ) * Complex.I) :=
  Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul continuous_const)

theorem continuous_plainKernel (N : ℕ) : Continuous (plainKernel N) :=
  continuous_finsetSum _ fun _ _ => continuous_phase _

/-- **The sum of the squared dual coefficients is the kernel double integral.** -/
theorem sum_normSq_dualCoeff_eq {N : ℕ} (a : Fin N → ℂ) {T : ℝ} {E : Set ℝ}
    (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T) :
    ((∑ n : Fin N, ‖dualCoeff N a E n‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∫ t in E, ∫ u in E, plainKernel N (t - u)
          * (starRingEnd ℂ) (dirPoly N a t) * dirPoly N a u := by
  classical
  have hcA : Continuous (dirPoly N a) := continuous_dirPoly N a
  have hcconj : Continuous fun t : ℝ => (starRingEnd ℂ) (dirPoly N a t) :=
    Complex.continuous_conj.comp hcA
  have hint : ∀ g : ℝ → ℂ, Continuous g → IntegrableOn g E := fun g hg =>
    (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set hEs
  set d : Fin N → ℂ := fun n =>
    ∫ u in E, Complex.exp (((-u * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
      * dirPoly N a u with hd
  -- the inner integral
  have hinner : ∀ t : ℝ, (∫ u in E, plainKernel N (t - u)
        * (starRingEnd ℂ) (dirPoly N a t) * dirPoly N a u)
      = ∑ n : Fin N, (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
          * (starRingEnd ℂ) (dirPoly N a t)) * d n := by
    intro t
    have hsplit : ∀ u : ℝ, plainKernel N (t - u)
          * (starRingEnd ℂ) (dirPoly N a t) * dirPoly N a u
        = ∑ n : Fin N, (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
            * (starRingEnd ℂ) (dirPoly N a t))
            * (Complex.exp (((-u * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
              * dirPoly N a u) := by
      intro u
      rw [plainKernel, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hprod : Complex.exp ((((t - u) * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
          = Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((-u * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hprod]
      ring
    rw [MeasureTheory.setIntegral_congr_fun hEm fun u _ => hsplit u]
    have hswap := MeasureTheory.integral_finsetSum
      (μ := volume.restrict E) (s := (Finset.univ : Finset (Fin N)))
      (f := fun n u => (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
          * (starRingEnd ℂ) (dirPoly N a t))
          * (Complex.exp (((-u * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) * dirPoly N a u))
      (fun n _ => hint _ (continuous_const.mul
        (((continuous_phase (Real.log ((n : ℕ) + 1))).comp continuous_neg).mul hcA)))
    rw [hswap, hd]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.setIntegral_congr_fun hEm fun t _ => hinner t]
  -- the outer integral
  have hswap2 := MeasureTheory.integral_finsetSum
    (μ := volume.restrict E) (s := (Finset.univ : Finset (Fin N)))
    (f := fun n t => (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
        * (starRingEnd ℂ) (dirPoly N a t)) * d n)
    (fun n _ => hint _ (((continuous_phase (Real.log ((n : ℕ) + 1))).mul hcconj).mul
      continuous_const))
  rw [hswap2, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  -- each term is `c n * conj (c n)`
  have hconj_e : ∀ s : ℝ,
      (starRingEnd ℂ) (Complex.exp (((s * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I))
        = Complex.exp (((-s * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
    intro s
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hdconj : d n = (starRingEnd ℂ) (dualCoeff N a E n) := by
    rw [hd, dualCoeff, ← integral_conj]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [map_mul, hconj_e u, Complex.conj_conj]
  have hc : (∫ t in E, Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
      * (starRingEnd ℂ) (dirPoly N a t)) = dualCoeff N a E n := rfl
  rw [MeasureTheory.integral_mul_const, hc, hdconj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- **The integral Halász–Montgomery bound.**  A Dirichlet polynomial's mean square over a set is
bounded by the kernel's row/column mass times the coefficient energy. -/
theorem setIntegral_normSq_dirPoly_le_HM {N : ℕ} (a : Fin N → ℂ) {T M : ℝ} {E : Set ℝ}
    (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T)
    (hrow : ∀ t ∈ E, (∫ u in E, ‖plainKernel N (t - u)‖) ≤ M)
    (hcol : ∀ u ∈ E, (∫ t in E, ‖plainKernel N (t - u)‖) ≤ M) (hM0 : 0 ≤ M) :
    (∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ)) ≤ M * ∑ n : Fin N, ‖a n‖ ^ (2 : ℕ) := by
  classical
  have hI0 : (0 : ℝ) ≤ ∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ) :=
    MeasureTheory.setIntegral_nonneg hEm fun t _ => sq_nonneg _
  have hE0 : (0 : ℝ) ≤ ∑ n : Fin N, ‖a n‖ ^ (2 : ℕ) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 := setIntegral_normSq_dirPoly_sq_le a hEm hEs
  -- the dual energy is the norm of the double integral
  have hdual : (∑ n : Fin N, ‖dualCoeff N a E n‖ ^ (2 : ℕ))
      = ‖∫ t in E, ∫ u in E, plainKernel N (t - u)
          * (starRingEnd ℂ) (dirPoly N a t) * dirPoly N a u‖ := by
    have hid := sum_normSq_dualCoeff_eq a hEm hEs
    have hnn : (0 : ℝ) ≤ ∑ n : Fin N, ‖dualCoeff N a E n‖ ^ (2 : ℕ) :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [← hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  have h3 := setIntegral_double_kernel_le (A := dirPoly N a) (K := plainKernel N)
    (continuous_dirPoly N a) (continuous_plainKernel N) hEs hEm hrow hcol
  rw [← hdual] at h3
  -- `I² ≤ (∑‖a‖²)·M·I`
  have hsq : (∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ)) ^ (2 : ℕ)
      ≤ (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) * (M * ∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ)) := by
    refine h1.trans (mul_le_mul_of_nonneg_left h3 hE0)
  rcases eq_or_lt_of_le hI0 with heq | hpos
  · rw [← heq]
    positivity
  · nlinarith [hsq, hpos]

end RHTower.Sieve
