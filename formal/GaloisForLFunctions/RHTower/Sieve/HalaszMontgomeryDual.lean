import GaloisForLFunctions.RHTower.Sieve.DirichletPoly

/-!
# The duality step of the integral Halász–Montgomery bound

Soundararajan's exposé, proof of Lemma 2.6, step `(17)`: for a measurable set `E`,

```text
   (∫_E ‖A‖²)²  ≤  (∑_n ‖a_n‖²) · ∑_n ‖∫_E n^{it}·conj(A(t)) dt‖² .
```

This is the step that makes the smallness of `E` usable: the right-hand side is a double integral
over `E × E` against a kernel, whereas every covering argument from `∫_E` to a separated sum throws
the smallness away.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The `n`-th dual coefficient of a Dirichlet polynomial over a set. -/
noncomputable def dualCoeff (N : ℕ) (a : Fin N → ℂ) (E : Set ℝ) (n : Fin N) : ℂ :=
  ∫ t in E, Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
    * (starRingEnd ℂ) (dirPoly N a t)

/-- **The duality identity.**  The mean square over `E` is the pairing of the coefficients with the
dual coefficients. -/
theorem setIntegral_normSq_dirPoly_eq_dual {N : ℕ} (a : Fin N → ℂ) {T : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T) :
    ((∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ) = ∑ n : Fin N, a n * dualCoeff N a E n := by
  classical
  have hcA : Continuous (dirPoly N a) := continuous_dirPoly N a
  have hcconj : Continuous fun t : ℝ => (starRingEnd ℂ) (dirPoly N a t) :=
    Complex.continuous_conj.comp hcA
  have hcsq : Continuous fun t : ℝ => ‖dirPoly N a t‖ ^ (2 : ℕ) := (hcA.norm).pow 2
  have hint : IntegrableOn (fun t : ℝ => ‖dirPoly N a t‖ ^ (2 : ℕ)) E :=
    (hcsq.integrableOn_Icc).mono_set hEs
  -- move to the complex integral of `A · conj A`
  have hpt : ∀ t : ℝ, ((‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = dirPoly N a t * (starRingEnd ℂ) (dirPoly N a t) := by
    intro t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hstep1 : ((∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∫ t in E, dirPoly N a t * (starRingEnd ℂ) (dirPoly N a t) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun hE fun t _ => hpt t
  rw [hstep1]
  -- expand the first factor and swap
  have hexp : ∀ t : ℝ, dirPoly N a t * (starRingEnd ℂ) (dirPoly N a t)
      = ∑ n : Fin N, a n * (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
          * (starRingEnd ℂ) (dirPoly N a t)) := by
    intro t
    rw [dirPoly, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [setIntegral_congr_fun hE fun t _ => hexp t]
  have hintn : ∀ n : Fin N, IntegrableOn
      (fun t : ℝ => a n * (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
        * (starRingEnd ℂ) (dirPoly N a t))) E := by
    intro n
    have hc : Continuous fun t : ℝ => a n
        * (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
          * (starRingEnd ℂ) (dirPoly N a t)) := by
      refine continuous_const.mul (Continuous.mul ?_ hcconj)
      exact Complex.continuous_exp.comp
        (((Complex.continuous_ofReal.comp
          (continuous_id.mul continuous_const)).mul continuous_const))
    exact (hc.integrableOn_Icc).mono_set hEs
  rw [MeasureTheory.integral_finsetSum _ fun n _ => hintn n]
  exact Finset.sum_congr rfl fun n _ => by
    rw [dualCoeff, MeasureTheory.integral_const_mul]

/-- **The duality bound `(17)`.** -/
theorem setIntegral_normSq_dirPoly_sq_le {N : ℕ} (a : Fin N → ℂ) {T : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T) :
    (∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ)) ^ (2 : ℕ)
      ≤ (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) * ∑ n : Fin N, ‖dualCoeff N a E n‖ ^ (2 : ℕ) := by
  classical
  have hid := setIntegral_normSq_dirPoly_eq_dual a hE hEs
  have habs : |∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ)|
      ≤ ∑ n : Fin N, ‖a n‖ * ‖dualCoeff N a E n‖ := by
    have h1 : ‖((∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ)‖
        ≤ ∑ n : Fin N, ‖a n * dualCoeff N a E n‖ := by
      rw [hid]
      exact norm_sum_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    simpa only [norm_mul] using h1
  have hcs : (∑ n : Fin N, ‖a n‖ * ‖dualCoeff N a E n‖) ^ (2 : ℕ)
      ≤ (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) * ∑ n : Fin N, ‖dualCoeff N a E n‖ ^ (2 : ℕ) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hnn : (0 : ℝ) ≤ ∑ n : Fin N, ‖a n‖ * ‖dualCoeff N a E n‖ :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hsq : (∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ)) ^ (2 : ℕ)
      ≤ (∑ n : Fin N, ‖a n‖ * ‖dualCoeff N a E n‖) ^ (2 : ℕ) := by
    have := abs_nonneg (∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ))
    nlinarith [habs, sq_abs (∫ t in E, ‖dirPoly N a t‖ ^ (2 : ℕ))]
  linarith [hsq, hcs]

/-! ## The dual coefficients as a double integral -/

/-- The smoothed logarithmic-phase kernel of a weight `w`. -/
noncomputable def logKernel (N : ℕ) (w : Fin N → ℝ) (v : ℝ) : ℂ :=
  ∑ n : Fin N, (w n : ℂ) * Complex.exp (((v * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)

/-- **One dual coefficient, squared, as a double integral.** -/
theorem normSq_dualCoeff_eq {N : ℕ} (a : Fin N → ℂ) (E : Set ℝ) (n : Fin N) :
    ((‖dualCoeff N a E n‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∫ t in E, ∫ u in E,
          Complex.exp ((((t - u) * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
            * (starRingEnd ℂ) (dirPoly N a t) * dirPoly N a u := by
  classical
  have hmulconj : ((‖dualCoeff N a E n‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = dualCoeff N a E n * (starRingEnd ℂ) (dualCoeff N a E n) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hmulconj, dualCoeff]
  set L : ℝ := Real.log ((n : ℕ) + 1) with hL
  have hconj_e : ∀ s : ℝ,
      (starRingEnd ℂ) (Complex.exp (((s * L : ℝ) : ℂ) * Complex.I))
        = Complex.exp (((-s * L : ℝ) : ℂ) * Complex.I) := by
    intro s
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hconjInt : (starRingEnd ℂ)
        (∫ t in E, Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)
          * (starRingEnd ℂ) (dirPoly N a t))
      = ∫ u in E, Complex.exp (((-u * L : ℝ) : ℂ) * Complex.I) * dirPoly N a u := by
    rw [← integral_conj]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [map_mul, hconj_e u, Complex.conj_conj]
  rw [hconjInt]
  have hpull : (∫ t in E, Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)
          * (starRingEnd ℂ) (dirPoly N a t))
        * (∫ u in E, Complex.exp (((-u * L : ℝ) : ℂ) * Complex.I) * dirPoly N a u)
      = ∫ t in E, ∫ u in E,
          (Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (dirPoly N a t))
            * (Complex.exp (((-u * L : ℝ) : ℂ) * Complex.I) * dirPoly N a u) := by
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [MeasureTheory.integral_const_mul]
  rw [hpull]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [show (Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (dirPoly N a t))
        * (Complex.exp (((-u * L : ℝ) : ℂ) * Complex.I) * dirPoly N a u)
      = (Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((-u * L : ℝ) : ℂ) * Complex.I))
        * (starRingEnd ℂ) (dirPoly N a t) * dirPoly N a u by ring,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

end RHTower.Sieve
