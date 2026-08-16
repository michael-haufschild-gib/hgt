import GaloisForLFunctions.RHTower.HeatQuadraticForm

/-!
# Orthogonality of the Fourier modes on the phase window

The `L²` norm of a trigonometric polynomial on `(-π, π]` is the `ℓ²` norm of its coefficients.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

theorem integrableOn_exp_int_mul (m : ℤ) :
    IntegrableOn (fun θ : ℝ => Complex.exp (I * (m : ℂ) * (θ : ℂ)))
      (Ioc (-Real.pi) Real.pi) :=
  Continuous.integrableOn_Ioc (by fun_prop)

/-- **Orthogonality.**  The window `L²` norm of a trigonometric polynomial. -/
theorem integral_trigPoly_normSq (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ θ in Ioc (-Real.pi) Real.pi,
        (∑ n ∈ s, a n * Complex.exp (I * (n : ℂ) * (θ : ℂ)))
          * (starRingEnd ℂ) (∑ n ∈ s, a n * Complex.exp (I * (n : ℂ) * (θ : ℂ))))
      = 2 * Real.pi * ∑ n ∈ s, ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
  have hexpand : ∀ θ : ℝ,
      (∑ n ∈ s, a n * Complex.exp (I * (n : ℂ) * (θ : ℂ)))
        * (starRingEnd ℂ) (∑ n ∈ s, a n * Complex.exp (I * (n : ℂ) * (θ : ℂ)))
      = ∑ n ∈ s, ∑ m ∈ s, (a n * (starRingEnd ℂ) (a m))
          * Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ)) := by
    intro θ
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, conj_exp_I_mul_real]
    have hmul : Complex.exp (I * (n : ℂ) * (θ : ℂ)) * Complex.exp (I * ((-m : ℤ) : ℂ) * (θ : ℂ))
        = Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc a n * Complex.exp (I * (n : ℂ) * (θ : ℂ))
          * ((starRingEnd ℂ) (a m) * Complex.exp (I * ((-m : ℤ) : ℂ) * (θ : ℂ)))
        = (a n * (starRingEnd ℂ) (a m))
            * (Complex.exp (I * (n : ℂ) * (θ : ℂ))
              * Complex.exp (I * ((-m : ℤ) : ℂ) * (θ : ℂ))) := by ring
      _ = (a n * (starRingEnd ℂ) (a m))
            * Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ)) := by rw [hmul]
  rw [setIntegral_congr_fun measurableSet_Ioc fun θ _ => hexpand θ,
    MeasureTheory.integral_finsetSum _ (fun n _ => MeasureTheory.integrable_finsetSum _
      fun m _ => ((integrableOn_exp_int_mul (n - m)).const_mul _))]
  have hinner : ∀ n ∈ s, (∫ θ in Ioc (-Real.pi) Real.pi, ∑ m ∈ s,
      (a n * (starRingEnd ℂ) (a m)) * Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ)))
      = 2 * Real.pi * ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
    intro n hn
    rw [MeasureTheory.integral_finsetSum _ (fun m _ =>
      ((integrableOn_exp_int_mul (n - m)).const_mul _))]
    have hterm : ∀ m ∈ s, (∫ θ in Ioc (-Real.pi) Real.pi,
        (a n * (starRingEnd ℂ) (a m)) * Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ)))
        = if m = n then 2 * Real.pi * ((‖a n‖ ^ 2 : ℝ) : ℂ) else 0 := by
      intro m _
      rw [MeasureTheory.integral_const_mul, setIntegral_exp_int_mul]
      by_cases hmn : m = n
      · subst hmn
        rw [if_pos rfl, if_pos (by ring)]
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      · have hne : (n - m : ℤ) ≠ 0 := by
          intro hcon
          exact hmn (by omega)
        rw [if_neg hne, if_neg hmn, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s n]
    rw [if_pos hn]
  rw [Finset.sum_congr rfl hinner, Finset.mul_sum]

end RHTower
