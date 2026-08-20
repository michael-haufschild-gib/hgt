import GaloisForLFunctions.HTGeometry.ExponentialWindowIntegral

/-!
# The twisted mean value of a Dirichlet polynomial

Expanding `A(σ+it)·conj B(σ+it)·e^{iL₀t}` term by term turns the window integral into a double sum
of exponential window integrals at the shifted frequencies `log n − log m + L₀`.  The diagonal is
now `log n − log m + L₀ = 0`, i.e. `n·e^{L₀} = m`, which for a twist by `(h/k)^{it}` is the
classical condition `nk = mh`.

This is the exact identity every twisted second moment starts from; no estimate is made here.
-/

open Complex intervalIntegral MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The `n`-th term of a Dirichlet polynomial on the line `Re s = σ`, as a function of height. -/
def cdterm (a : ℕ → ℂ) (σ t : ℝ) (n : ℕ) : ℂ :=
  a n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-(Real.log n) * t : ℝ) : ℂ) * I)

/-- A Dirichlet polynomial on the line `Re s = σ`, as a function of height. -/
def cdpoly (a : ℕ → ℂ) (s : Finset ℕ) (σ t : ℝ) : ℂ := ∑ n ∈ s, cdterm a σ t n

theorem conj_cdterm (b : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (cdterm b σ t n)
      = (starRingEnd ℂ) (b n) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)
        * Complex.exp ((((Real.log n) * t : ℝ) : ℂ) * I) := by
  unfold cdterm
  rw [map_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem cdterm_mul_conj (a b : ℕ → ℂ) (σ t : ℝ) (m n : ℕ) :
    cdterm a σ t m * (starRingEnd ℂ) (cdterm b σ t n)
      = (a m * (starRingEnd ℂ) (b n))
        * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)
        * Complex.exp ((((Real.log n - Real.log m) * t : ℝ) : ℂ) * I) := by
  rw [conj_cdterm]
  unfold cdterm
  rw [← Complex.exp_add]
  push_cast
  ring_nf
  rw [← Complex.exp_add]
  ring_nf

theorem continuous_cdterm_mul_conj_twist (a b : ℕ → ℂ) (σ L₀ : ℝ) (m n : ℕ) :
    Continuous fun t : ℝ =>
      (a m * (starRingEnd ℂ) (b n))
        * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)
        * Complex.exp (((((Real.log n - Real.log m + L₀) * t : ℝ)) : ℂ) * I) := by
  refine continuous_const.mul ?_
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)

/-- **The twisted mean value identity.**  No estimate: an exact double sum of exponential window
integrals at the shifted frequencies. -/
theorem twisted_meanValue (a b : ℕ → ℂ) (s : Finset ℕ) (σ L₀ T U : ℝ) :
    (∫ t in T..(T + U), cdpoly a s σ t * (starRingEnd ℂ) (cdpoly b s σ t)
        * Complex.exp ((((L₀ * t : ℝ)) : ℂ) * I))
      = ∑ m ∈ s, ∑ n ∈ s, (a m * (starRingEnd ℂ) (b n))
          * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)
          * expInt (Real.log n - Real.log m + L₀) T U := by
  classical
  have hpoint : ∀ t : ℝ,
      cdpoly a s σ t * (starRingEnd ℂ) (cdpoly b s σ t)
          * Complex.exp ((((L₀ * t : ℝ)) : ℂ) * I)
        = ∑ m ∈ s, ∑ n ∈ s, (a m * (starRingEnd ℂ) (b n))
            * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)
            * Complex.exp (((((Real.log n - Real.log m + L₀) * t : ℝ)) : ℂ) * I) := by
    intro t
    unfold cdpoly
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [cdterm_mul_conj, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t)]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_const_mul]
      rfl
    · intro n _
      exact (continuous_cdterm_mul_conj_twist a b σ L₀ m n).intervalIntegrable _ _
  · intro m _
    refine IntervalIntegrable.sum _ ?_
    intro n _
    exact (continuous_cdterm_mul_conj_twist a b σ L₀ m n).intervalIntegrable _ _

end GaloisForLFunctions.HTGeometry

end
