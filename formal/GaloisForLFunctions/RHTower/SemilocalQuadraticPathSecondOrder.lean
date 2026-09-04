import GaloisForLFunctions.RHTower.SemilocalTwoModeRadiusResponse

/-!
# Second-order calculus of a quadratic determinant path

For families of matrices `M₁ m, M₂ m` (`m ∈ ℕ`, size `m+1`) and the path
`A_m(t) = 1 + t M₁ m + t² M₂ m`:

`(log det A_m)''(0) = 2 tr M₂ m − tr((M₁ m)²)`,

and through the Hankel quotient `a_n² = r_n² Δ_{n−1}Δ_{n+1}/Δ_n²`,

`(a_n²)''(0) = r_n² ( ΔΔ(2 tr M₂ − tr M₁²)(n) + (ΔΔ tr M₁ (n))² )`.

This is the generic engine behind the one-prime and finite-`S` second-order responses: any
second-order weight perturbation `1 + tA + t²B` feeds in through `M₁ = T(A)`, `M₂ = T(B)`.
-/

open Matrix Real Filter Topology Finset
open scoped BigOperators

namespace RHTower
namespace CosineModeResponse

open GaloisForLFunctions.HilbertMetric FirstEulerCriticalJet

section generic

variable (M₁ M₂ : ∀ m : ℕ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)

/-- `A_m(t) = 1 + t M₁ + t² M₂`. -/
noncomputable def quadPath (m : ℕ) (t : ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  1 + t • M₁ m + (t ^ 2) • M₂ m

noncomputable def quadDet (m : ℕ) (t : ℝ) : ℝ := (quadPath M₁ M₂ m t).det

/-- `(log det A_m)''(0)`. -/
noncomputable def quadLogJet (m : ℕ) : ℝ := 2 * Matrix.trace (M₂ m) - Matrix.trace (M₁ m * M₁ m)

/-- `tr(A_m(t)⁻¹ (M₁ + 2t M₂))`. -/
noncomputable def quadSlope (m : ℕ) (t : ℝ) : ℝ :=
  Matrix.trace ((quadPath M₁ M₂ m t)⁻¹ * (M₁ m + (2 * t) • M₂ m))

theorem quadPath_zero (m : ℕ) : quadPath M₁ M₂ m 0 = 1 := by
  unfold quadPath
  simp

theorem hasDerivAt_quadPath_entry (m : ℕ) (t : ℝ) (i j : Fin (m + 1)) :
    HasDerivAt (fun ε => quadPath M₁ M₂ m ε i j) ((M₁ m + (2 * t) • M₂ m) i j) t := by
  have hfun : (fun ε => quadPath M₁ M₂ m ε i j) =
      fun ε => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i j + ε * M₁ m i j + ε ^ 2 * M₂ m i j := by
    funext ε
    simp only [quadPath, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hfun]
  have h := (((hasDerivAt_id t).mul_const (M₁ m i j)).const_add
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i j)).add
    (((hasDerivAt_id t).pow 2).mul_const (M₂ m i j))
  refine h.congr_deriv ?_
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem hasDerivAt_quadDet (m : ℕ) (t : ℝ) :
    HasDerivAt (fun ε => quadDet M₁ M₂ m ε)
      (detFirstJet (quadPath M₁ M₂ m t) (M₁ m + (2 * t) • M₂ m)) t :=
  hasDerivAt_matrixDet (fun ε => quadPath M₁ M₂ m ε) _ t
    (fun i j => hasDerivAt_quadPath_entry M₁ M₂ m t i j)

theorem hasDerivAt_quadDet' (m : ℕ) (t : ℝ) (hdet : (quadPath M₁ M₂ m t).det ≠ 0) :
    HasDerivAt (fun ε => quadDet M₁ M₂ m ε) (quadDet M₁ M₂ m t * quadSlope M₁ M₂ m t) t := by
  refine (hasDerivAt_quadDet M₁ M₂ m t).congr_deriv ?_
  rw [detFirstJet_eq_det_mul_trace_inv_mul _ _ hdet]
  rfl

theorem deriv_log_quadDet (m : ℕ) (t : ℝ) (hdet : (quadPath M₁ M₂ m t).det ≠ 0) :
    deriv (fun ε => Real.log (quadDet M₁ M₂ m ε)) t = quadSlope M₁ M₂ m t := by
  have h := hasDerivAt_quadDet M₁ M₂ m t
  have h0 : quadDet M₁ M₂ m t ≠ 0 := hdet
  have hlog := h.log h0
  rw [hlog.deriv, detFirstJet_eq_det_mul_trace_inv_mul _ _ hdet]
  unfold quadSlope quadDet
  field_simp

theorem quadSlope_zero (m : ℕ) : quadSlope M₁ M₂ m 0 = Matrix.trace (M₁ m) := by
  unfold quadSlope
  rw [quadPath_zero]
  simp

theorem hasDerivAt_quadSlope (m : ℕ) :
    HasDerivAt (quadSlope M₁ M₂ m) (quadLogJet M₁ M₂ m) 0 := by
  have hfun : quadSlope M₁ M₂ m = fun t => ∑ i, ∑ k, (quadPath M₁ M₂ m t)⁻¹ i k *
      (M₁ m + (2 * t) • M₂ m) k i := by
    funext t
    unfold quadSlope
    simp [Matrix.trace, Matrix.mul_apply]
  rw [hfun]
  have hinv : ∀ i j, HasDerivAt (fun t : ℝ => (quadPath M₁ M₂ m t)⁻¹ i j) (-(M₁ m i j)) 0 := by
    intro i j
    have h := hasDerivAt_matrix_inv (fun t => quadPath M₁ M₂ m t) (M₁ m) 0
      (fun i j => by
        have := hasDerivAt_quadPath_entry M₁ M₂ m 0 i j
        simpa using this) (by rw [quadPath_zero]; simp) i j
    rw [quadPath_zero] at h
    simpa using h
  have hN : ∀ k i, HasDerivAt (fun t : ℝ => (M₁ m + (2 * t) • M₂ m) k i) (2 * M₂ m k i) 0 := by
    intro k i
    have hfun' : (fun t : ℝ => (M₁ m + (2 * t) • M₂ m) k i) = fun t => M₁ m k i + (2 * t) * M₂ m k i := by
      funext t
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hfun']
    have := ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (M₂ m k i)
    refine (this.const_add (M₁ m k i)).congr_deriv ?_
    simp
  have hterm : ∀ i k : Fin (m + 1), HasDerivAt
      (fun t : ℝ => (quadPath M₁ M₂ m t)⁻¹ i k * (M₁ m + (2 * t) • M₂ m) k i)
      (-(M₁ m i k) * M₁ m k i + (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i k * (2 * M₂ m k i)) 0 := by
    intro i k
    refine ((hinv i k).fun_mul (hN k i)).congr_deriv ?_
    rw [quadPath_zero]
    simp
  have hrow : ∀ i : Fin (m + 1), HasDerivAt
      (fun t : ℝ => ∑ k, (quadPath M₁ M₂ m t)⁻¹ i k * (M₁ m + (2 * t) • M₂ m) k i)
      (∑ k, (-(M₁ m i k) * M₁ m k i + (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i k * (2 * M₂ m k i))) 0 :=
    fun i => HasDerivAt.fun_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin (m + 1))))
      (fun k _ => hterm i k)
  have h := HasDerivAt.fun_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin (m + 1)))) (fun i _ => hrow i)
  refine h.congr_deriv ?_
  unfold quadLogJet
  have hval : (∑ i, ∑ k, (-(M₁ m i k) * M₁ m k i +
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i k * (2 * M₂ m k i))) =
      -Matrix.trace (M₁ m * M₁ m) + 2 * Matrix.trace (M₂ m) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, neg_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  rw [hval]
  ring

theorem continuous_quadDet (m : ℕ) : Continuous (fun t : ℝ => (quadPath M₁ M₂ m t).det) := by
  apply Continuous.matrix_det
  unfold quadPath
  exact (continuous_const.add (continuous_id.smul continuous_const)).add
    ((continuous_id.pow 2).smul continuous_const)

/-- **`(log det A_m)''(0) = 2 tr M₂ − tr M₁²`.** -/
theorem deriv_deriv_log_quadDet (m : ℕ) :
    deriv (deriv (fun ε => Real.log (quadDet M₁ M₂ m ε))) 0 = quadLogJet M₁ M₂ m := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (quadPath M₁ M₂ m t).det ≠ 0 :=
    (continuous_quadDet M₁ M₂ m).continuousAt.eventually_ne (by rw [quadPath_zero]; simp)
  have heq : deriv (fun ε => Real.log (quadDet M₁ M₂ m ε)) =ᶠ[𝓝 0] quadSlope M₁ M₂ m := by
    filter_upwards [hev] with t h
    exact deriv_log_quadDet M₁ M₂ m t h
  exact ((hasDerivAt_quadSlope M₁ M₂ m).congr_of_eventuallyEq heq).deriv

/-! ## The Hankel quotient -/

noncomputable def quadPrevDet : ℕ → ℝ → ℝ
  | 0, _ => 1
  | m + 1, t => quadDet M₁ M₂ m t

noncomputable def quadPrevSlope : ℕ → ℝ → ℝ
  | 0, _ => 0
  | m + 1, t => quadSlope M₁ M₂ m t

theorem hasDerivAt_quadPrevDet (n : ℕ) (t : ℝ)
    (hall : ∀ m ≤ n + 1, (quadPath M₁ M₂ m t).det ≠ 0) :
    HasDerivAt (fun ε => quadPrevDet M₁ M₂ n ε)
      (quadPrevDet M₁ M₂ n t * quadPrevSlope M₁ M₂ n t) t := by
  cases n with
  | zero =>
      change HasDerivAt (fun _ : ℝ => (1 : ℝ)) ((1 : ℝ) * 0) t
      rw [mul_zero]
      exact hasDerivAt_const _ _
  | succ m => exact hasDerivAt_quadDet' M₁ M₂ m t (hall m (by omega))

theorem hasDerivAt_quadPrevSlope (n : ℕ) :
    HasDerivAt (quadPrevSlope M₁ M₂ n) (prevJet (quadLogJet M₁ M₂) n) 0 := by
  cases n with
  | zero =>
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0
      exact hasDerivAt_const _ _
  | succ m =>
      change HasDerivAt (quadSlope M₁ M₂ m) (quadLogJet M₁ M₂ m) 0
      exact hasDerivAt_quadSlope M₁ M₂ m

theorem quadPrevSlope_zero (n : ℕ) :
    quadPrevSlope M₁ M₂ n 0 = prevJet (fun m => Matrix.trace (M₁ m)) n := by
  cases n with
  | zero => rfl
  | succ m => exact quadSlope_zero M₁ M₂ m

theorem quadDet_zero (m : ℕ) : quadDet M₁ M₂ m 0 = 1 := by
  unfold quadDet
  rw [quadPath_zero]
  simp

theorem quadPrevDet_zero (n : ℕ) : quadPrevDet M₁ M₂ n 0 = 1 := by
  cases n with
  | zero => rfl
  | succ m => exact quadDet_zero M₁ M₂ m

/-- `r_n² Δ_{n−1} Δ_{n+1} / Δ_n²`. -/
noncomputable def quadSquaredRadius (n : ℕ) (t : ℝ) : ℝ :=
  archimedeanSquaredRadius n *
    (quadPrevDet M₁ M₂ n t * quadDet M₁ M₂ (n + 1) t / quadDet M₁ M₂ n t ^ 2)

noncomputable def quadRadiusSlope (n : ℕ) (t : ℝ) : ℝ :=
  quadPrevSlope M₁ M₂ n t + quadSlope M₁ M₂ (n + 1) t - 2 * quadSlope M₁ M₂ n t

theorem quadRadiusSlope_zero (n : ℕ) :
    quadRadiusSlope M₁ M₂ n 0 = prevJet (fun m => Matrix.trace (M₁ m)) n +
      Matrix.trace (M₁ (n + 1)) - 2 * Matrix.trace (M₁ n) := by
  unfold quadRadiusSlope
  rw [quadPrevSlope_zero, quadSlope_zero, quadSlope_zero]

theorem hasDerivAt_quadRadiusSlope (n : ℕ) :
    HasDerivAt (quadRadiusSlope M₁ M₂ n)
      (prevJet (quadLogJet M₁ M₂) n + quadLogJet M₁ M₂ (n + 1) - 2 * quadLogJet M₁ M₂ n) 0 := by
  unfold quadRadiusSlope
  exact ((hasDerivAt_quadPrevSlope M₁ M₂ n).add (hasDerivAt_quadSlope M₁ M₂ (n + 1))).sub
    ((hasDerivAt_quadSlope M₁ M₂ n).const_mul 2)

theorem hasDerivAt_quadSquaredRadius (n : ℕ) (t : ℝ)
    (hall : ∀ m ≤ n + 1, (quadPath M₁ M₂ m t).det ≠ 0) :
    HasDerivAt (fun ε => quadSquaredRadius M₁ M₂ n ε)
      (quadSquaredRadius M₁ M₂ n t * quadRadiusSlope M₁ M₂ n t) t := by
  have hP := hasDerivAt_quadPrevDet M₁ M₂ n t hall
  have hN := hasDerivAt_quadDet' M₁ M₂ (n + 1) t (hall (n + 1) le_rfl)
  have hD := hasDerivAt_quadDet' M₁ M₂ n t (hall n (by omega))
  have hD0 : quadDet M₁ M₂ n t ≠ 0 := hall n (by omega)
  have hquot := ((hP.mul hN).div (hD.pow 2) (pow_ne_zero 2 hD0)).const_mul
    (archimedeanSquaredRadius n)
  have hquot' : HasDerivAt (fun ε => quadSquaredRadius M₁ M₂ n ε) _ t := hquot
  refine hquot'.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply]
  unfold quadSquaredRadius quadRadiusSlope
  field_simp
  ring

theorem quadSquaredRadius_zero (n : ℕ) :
    quadSquaredRadius M₁ M₂ n 0 = archimedeanSquaredRadius n := by
  unfold quadSquaredRadius
  rw [quadPrevDet_zero, quadDet_zero, quadDet_zero]
  simp

/-- `(a_n²)''(0) = r_n² (ΔΔ(2 tr M₂ − tr M₁²) + (ΔΔ tr M₁)²)`. -/
noncomputable def quadSecondOrderJet (n : ℕ) : ℝ :=
  archimedeanSquaredRadius n *
    ((prevJet (quadLogJet M₁ M₂) n + quadLogJet M₁ M₂ (n + 1) - 2 * quadLogJet M₁ M₂ n) +
      (prevJet (fun m => Matrix.trace (M₁ m)) n + Matrix.trace (M₁ (n + 1)) -
        2 * Matrix.trace (M₁ n)) ^ 2)

/-- **The second derivative of the quadratic-path squared radius.** -/
theorem deriv_deriv_quadSquaredRadius (n : ℕ) :
    deriv (deriv (fun ε => quadSquaredRadius M₁ M₂ n ε)) 0 = quadSecondOrderJet M₁ M₂ n := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ m ∈ Finset.range (n + 2), (quadPath M₁ M₂ m t).det ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro m _
    exact (continuous_quadDet M₁ M₂ m).continuousAt.eventually_ne (by rw [quadPath_zero]; simp)
  have heq : deriv (fun ε => quadSquaredRadius M₁ M₂ n ε) =ᶠ[𝓝 0]
      fun t => quadSquaredRadius M₁ M₂ n t * quadRadiusSlope M₁ M₂ n t := by
    filter_upwards [hev] with t h
    exact (hasDerivAt_quadSquaredRadius M₁ M₂ n t
      (fun m hm => h m (Finset.mem_range.mpr (by omega)))).deriv
  have hall0 : ∀ m ≤ n + 1, (quadPath M₁ M₂ m 0).det ≠ 0 := fun m _ => by
    rw [quadPath_zero]; simp
  have hA := hasDerivAt_quadSquaredRadius M₁ M₂ n 0 hall0
  have hG := hasDerivAt_quadRadiusSlope M₁ M₂ n
  have hprod := hA.fun_mul hG
  rw [(hprod.congr_of_eventuallyEq heq).deriv, quadSquaredRadius_zero, quadRadiusSlope_zero]
  unfold quadSecondOrderJet
  ring

end generic

end CosineModeResponse
end RHTower
