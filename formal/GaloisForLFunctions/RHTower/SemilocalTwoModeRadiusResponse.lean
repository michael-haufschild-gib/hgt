import GaloisForLFunctions.RHTower.SemilocalTwoModeBilinearResponse

/-!
# The bilinear response of the Jacobi radii to two cosine modes

Through the Hankel quotient `a_n² = r_n² Δ_{n−1} Δ_{n+1} / Δ_n²` the bilinear determinant jets
`B_m = ∂₁∂₂ log D_m` transfer to the squared radii:

`∂₁∂₂ a_n²(ε₁, ε₂)|₀ = r_n² (B_{n−1} + B_{n+1} − 2 B_n) + [ε₁]a_n² · [ε₂]a_n² / r_n²`,

i.e. the bilinear squared-radius jet is the squared-radius jet of the bilinear determinant jet
(sum mode + beat mode − truncation defect) plus the product of the two first-order jets.
-/

open Matrix Real MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower
namespace CosineModeResponse

open GaloisForLFunctions.HilbertMetric
open FirstEulerCriticalJet

/-! ## Determinant paths at `ε₁ = 0` and their inner derivatives -/

theorem twoModeDeterminant_eq (δ₁ δ₂ : ℝ) (m : ℕ) (ε₁ ε₂ : ℝ) :
    twoModeDeterminant δ₁ δ₂ m ε₁ ε₂ = (twoModeMatrix δ₁ δ₂ m ε₁ ε₂).det := by
  unfold twoModeDeterminant
  rw [twoModeGram_eq]

theorem twoModeDeterminant_zero_left (δ₁ δ₂ : ℝ) (m : ℕ) (ε₂ : ℝ) :
    twoModeDeterminant δ₁ δ₂ m 0 ε₂ = cosineModeDeterminantPath δ₂ m ε₂ := by
  rw [twoModeDeterminant_eq, twoModeMatrix_zero_left]
  unfold cosineModeDeterminantPath
  rw [cosineModeGram_eq]

/-- `g_m(ε₂) = tr((1 + ε₂ T₂)⁻¹ (T₁ + ε₂ T₁₂))`, the inner derivative of `log D_m` at `(0, ε₂)`. -/
noncomputable def bilinearTraceFunction (δ₁ δ₂ : ℝ) (m : ℕ) (ε₂ : ℝ) : ℝ :=
  Matrix.trace ((1 + ε₂ • cosineModeTangent δ₂ m)⁻¹ *
    (cosineModeTangent δ₁ m +
      ε₂ • (cosineModeTangent (δ₁ + δ₂) m + cosineModeTangent (δ₁ - δ₂) m)))

theorem hasDerivAt_bilinearTraceFunction (δ₁ δ₂ : ℝ) (m : ℕ) :
    HasDerivAt (bilinearTraceFunction δ₁ δ₂ m) (bilinearDeterminantJet δ₁ δ₂ m) 0 := by
  have h := hasDerivAt_traceInvMul m (cosineModeTangent δ₁ m) (cosineModeTangent δ₂ m)
    (cosineModeTangent (δ₁ + δ₂) m + cosineModeTangent (δ₁ - δ₂) m)
  refine h.congr_deriv ?_
  unfold bilinearDeterminantJet
  rw [Matrix.trace_add, Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.trace_add,
    trace_cosineModeTangent, trace_cosineModeTangent]
  unfold cosineModeDeterminantJet
  ring

theorem bilinearTraceFunction_zero (δ₁ δ₂ : ℝ) (m : ℕ) :
    bilinearTraceFunction δ₁ δ₂ m 0 = cosineModeDeterminantJet δ₁ m := by
  unfold bilinearTraceFunction
  simp [trace_cosineModeTangent, cosineModeDeterminantJet]

theorem hasDerivAt_twoModeDeterminant_left (δ₁ δ₂ : ℝ) (m : ℕ) (ε₂ : ℝ)
    (hdet : (1 + ε₂ • cosineModeTangent δ₂ m).det ≠ 0) :
    HasDerivAt (fun ε₁ => twoModeDeterminant δ₁ δ₂ m ε₁ ε₂)
      (twoModeDeterminant δ₁ δ₂ m 0 ε₂ * bilinearTraceFunction δ₁ δ₂ m ε₂) 0 := by
  have h := hasDerivAt_det_twoModeMatrix δ₁ δ₂ m ε₂
  have hfun : (fun ε₁ => twoModeDeterminant δ₁ δ₂ m ε₁ ε₂) =
      fun ε₁ => (twoModeMatrix δ₁ δ₂ m ε₁ ε₂).det := by
    funext ε₁
    exact twoModeDeterminant_eq δ₁ δ₂ m ε₁ ε₂
  rw [hfun]
  refine h.congr_deriv ?_
  rw [detFirstJet_eq_det_mul_trace_inv_mul _ _ hdet, twoModeDeterminant_eq, twoModeMatrix_zero_left]
  rfl

/-! ## The formal predecessor -/

/-- `Δ_{n−1}` with `Δ_{−1} = 1`. -/
noncomputable def twoModePrevDeterminant (δ₁ δ₂ : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | m + 1, ε₁, ε₂ => twoModeDeterminant δ₁ δ₂ m ε₁ ε₂

/-- `g_{n−1}` with `g_{−1} = 0`. -/
noncomputable def prevTraceFunction (δ₁ δ₂ : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | m + 1, ε₂ => bilinearTraceFunction δ₁ δ₂ m ε₂

theorem twoModePrevDeterminant_zero_left (δ₁ δ₂ : ℝ) (n : ℕ) (ε₂ : ℝ) :
    twoModePrevDeterminant δ₁ δ₂ n 0 ε₂ =
      previousDeterminantPathOf (cosineModeDeterminantPath δ₂) n ε₂ := by
  cases n with
  | zero => rfl
  | succ m => exact twoModeDeterminant_zero_left δ₁ δ₂ m ε₂

theorem hasDerivAt_prevTraceFunction (δ₁ δ₂ : ℝ) (n : ℕ) :
    HasDerivAt (prevTraceFunction δ₁ δ₂ n) (prevJet (bilinearDeterminantJet δ₁ δ₂) n) 0 := by
  cases n with
  | zero =>
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0
      exact hasDerivAt_const _ _
  | succ m =>
      change HasDerivAt (bilinearTraceFunction δ₁ δ₂ m) (bilinearDeterminantJet δ₁ δ₂ m) 0
      exact hasDerivAt_bilinearTraceFunction δ₁ δ₂ m

theorem prevTraceFunction_zero (δ₁ δ₂ : ℝ) (n : ℕ) :
    prevTraceFunction δ₁ δ₂ n 0 = prevJet (cosineModeDeterminantJet δ₁) n := by
  cases n with
  | zero => rfl
  | succ m => exact bilinearTraceFunction_zero δ₁ δ₂ m

theorem hasDerivAt_twoModePrevDeterminant_left (δ₁ δ₂ : ℝ) (n : ℕ) (ε₂ : ℝ)
    (hall : ∀ m ≤ n + 1, (1 + ε₂ • cosineModeTangent δ₂ m).det ≠ 0) :
    HasDerivAt (fun ε₁ => twoModePrevDeterminant δ₁ δ₂ n ε₁ ε₂)
      (twoModePrevDeterminant δ₁ δ₂ n 0 ε₂ * prevTraceFunction δ₁ δ₂ n ε₂) 0 := by
  cases n with
  | zero =>
      change HasDerivAt (fun _ : ℝ => (1 : ℝ)) ((1 : ℝ) * 0) 0
      rw [mul_zero]
      exact hasDerivAt_const _ _
  | succ m =>
      exact hasDerivAt_twoModeDeterminant_left δ₁ δ₂ m ε₂ (hall m (by omega))

theorem twoModePrevDeterminant_zero_left_ne (δ₁ δ₂ : ℝ) (n : ℕ) (ε₂ : ℝ)
    (hall : ∀ m ≤ n + 1, (1 + ε₂ • cosineModeTangent δ₂ m).det ≠ 0) :
    twoModePrevDeterminant δ₁ δ₂ n 0 ε₂ ≠ 0 := by
  cases n with
  | zero => exact one_ne_zero
  | succ m =>
      change twoModeDeterminant δ₁ δ₂ m 0 ε₂ ≠ 0
      rw [twoModeDeterminant_eq, twoModeMatrix_zero_left]
      exact hall m (by omega)

/-! ## The squared radius -/

/-- The two-mode squared Jacobi radius `r_n² Δ_{n−1} Δ_{n+1} / Δ_n²`. -/
noncomputable def twoModeSquaredRadius (δ₁ δ₂ : ℝ) (n : ℕ) (ε₁ ε₂ : ℝ) : ℝ :=
  archimedeanSquaredRadius n *
    (twoModePrevDeterminant δ₁ δ₂ n ε₁ ε₂ * twoModeDeterminant δ₁ δ₂ (n + 1) ε₁ ε₂ /
      twoModeDeterminant δ₁ δ₂ n ε₁ ε₂ ^ (2 : ℕ))

theorem twoModeSquaredRadius_zero_left (δ₁ δ₂ : ℝ) (n : ℕ) (ε₂ : ℝ) :
    twoModeSquaredRadius δ₁ δ₂ n 0 ε₂ =
      squaredJacobiRadiusPathOf (cosineModeDeterminantPath δ₂) n ε₂ := by
  unfold twoModeSquaredRadius squaredJacobiRadiusPathOf
  rw [twoModePrevDeterminant_zero_left, twoModeDeterminant_zero_left, twoModeDeterminant_zero_left]

theorem twoModeSquaredRadius_zero_zero (δ₁ δ₂ : ℝ) (n : ℕ) :
    twoModeSquaredRadius δ₁ δ₂ n 0 0 = archimedeanSquaredRadius n := by
  rw [twoModeSquaredRadius_zero_left]
  unfold squaredJacobiRadiusPathOf
  have hprev : previousDeterminantPathOf (cosineModeDeterminantPath δ₂) n 0 = 1 := by
    cases n with
    | zero => rfl
    | succ m => exact cosineModeDeterminantPath_zero δ₂ m
  rw [hprev, cosineModeDeterminantPath_zero, cosineModeDeterminantPath_zero]
  simp

/-- The inner slope `g_{n−1} + g_{n+1} − 2 g_n` at `(0, ε₂)`. -/
noncomputable def innerRadiusSlope (δ₁ δ₂ : ℝ) (n : ℕ) (ε₂ : ℝ) : ℝ :=
  prevTraceFunction δ₁ δ₂ n ε₂ + bilinearTraceFunction δ₁ δ₂ (n + 1) ε₂ -
    2 * bilinearTraceFunction δ₁ δ₂ n ε₂

theorem innerRadiusSlope_zero (δ₁ δ₂ : ℝ) (n : ℕ) :
    innerRadiusSlope δ₁ δ₂ n 0 = prevJet (cosineModeDeterminantJet δ₁) n +
      cosineModeDeterminantJet δ₁ (n + 1) - 2 * cosineModeDeterminantJet δ₁ n := by
  unfold innerRadiusSlope
  rw [prevTraceFunction_zero, bilinearTraceFunction_zero, bilinearTraceFunction_zero]

theorem hasDerivAt_innerRadiusSlope (δ₁ δ₂ : ℝ) (n : ℕ) :
    HasDerivAt (innerRadiusSlope δ₁ δ₂ n)
      (prevJet (bilinearDeterminantJet δ₁ δ₂) n + bilinearDeterminantJet δ₁ δ₂ (n + 1) -
        2 * bilinearDeterminantJet δ₁ δ₂ n) 0 := by
  unfold innerRadiusSlope
  exact ((hasDerivAt_prevTraceFunction δ₁ δ₂ n).add (hasDerivAt_bilinearTraceFunction δ₁ δ₂ (n + 1))).sub
    ((hasDerivAt_bilinearTraceFunction δ₁ δ₂ n).const_mul 2)

/-- The inner derivative of the squared radius at `(0, ε₂)`. -/
theorem deriv_twoModeSquaredRadius_left (δ₁ δ₂ : ℝ) (n : ℕ) (ε₂ : ℝ)
    (hall : ∀ m ≤ n + 1, (1 + ε₂ • cosineModeTangent δ₂ m).det ≠ 0) :
    deriv (fun ε₁ => twoModeSquaredRadius δ₁ δ₂ n ε₁ ε₂) 0 =
      twoModeSquaredRadius δ₁ δ₂ n 0 ε₂ * innerRadiusSlope δ₁ δ₂ n ε₂ := by
  have hP := hasDerivAt_twoModePrevDeterminant_left δ₁ δ₂ n ε₂ hall
  have hN := hasDerivAt_twoModeDeterminant_left δ₁ δ₂ (n + 1) ε₂ (hall (n + 1) le_rfl)
  have hD := hasDerivAt_twoModeDeterminant_left δ₁ δ₂ n ε₂ (hall n (by omega))
  have hD0 : twoModeDeterminant δ₁ δ₂ n 0 ε₂ ≠ 0 := by
    rw [twoModeDeterminant_eq, twoModeMatrix_zero_left]
    exact hall n (by omega)
  have hquot := ((hP.mul hN).div (hD.pow 2) (pow_ne_zero 2 hD0)).const_mul
    (archimedeanSquaredRadius n)
  have hquot' : HasDerivAt (fun ε₁ => twoModeSquaredRadius δ₁ δ₂ n ε₁ ε₂) _ 0 := hquot
  rw [hquot'.deriv]
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply]
  unfold twoModeSquaredRadius innerRadiusSlope
  field_simp
  ring

/-- The bilinear squared-radius jet: `r_n²(B_{n−1} + B_{n+1} − 2B_n) + [ε₁]a_n² [ε₂]a_n² / r_n²`. -/
noncomputable def bilinearSquaredRadiusJet (δ₁ δ₂ : ℝ) (n : ℕ) : ℝ :=
  squaredRadiusJetOf (bilinearDeterminantJet δ₁ δ₂) n +
    squaredRadiusJetOf (cosineModeDeterminantJet δ₁) n *
      squaredRadiusJetOf (cosineModeDeterminantJet δ₂) n / archimedeanSquaredRadius n

/-- **The bilinear response of the squared Jacobi radius.** -/
theorem deriv_deriv_twoModeSquaredRadius (δ₁ δ₂ : ℝ) (n : ℕ) :
    deriv (fun ε₂ => deriv (fun ε₁ => twoModeSquaredRadius δ₁ δ₂ n ε₁ ε₂) 0) 0 =
      bilinearSquaredRadiusJet δ₁ δ₂ n := by
  have hev : ∀ᶠ ε₂ in 𝓝 (0 : ℝ), ∀ m ∈ Finset.range (n + 2),
      (1 + ε₂ • cosineModeTangent δ₂ m).det ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro m _
    exact (Continuous.matrix_det (continuous_const.add
      (continuous_id.smul continuous_const))).continuousAt.eventually_ne (by simp)
  have heq : (fun ε₂ => deriv (fun ε₁ => twoModeSquaredRadius δ₁ δ₂ n ε₁ ε₂) 0) =ᶠ[𝓝 0]
      fun ε₂ => twoModeSquaredRadius δ₁ δ₂ n 0 ε₂ * innerRadiusSlope δ₁ δ₂ n ε₂ := by
    filter_upwards [hev] with ε₂ h
    exact deriv_twoModeSquaredRadius_left δ₁ δ₂ n ε₂
      (fun m hm => h m (Finset.mem_range.mpr (by omega)))
  have hA : HasDerivAt (fun ε₂ => twoModeSquaredRadius δ₁ δ₂ n 0 ε₂)
      (squaredRadiusJetOf (cosineModeDeterminantJet δ₂) n) 0 := by
    have h := hasDerivAt_squaredJacobiRadiusPathOf_jet (cosineModeDeterminantPath δ₂)
      (cosineModeDeterminantJet δ₂) (cosineModeDeterminantPath_zero δ₂)
      (hasDerivAt_cosineModeDeterminantPath δ₂) n
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun ε₂ => ?_)
    exact twoModeSquaredRadius_zero_left δ₁ δ₂ n ε₂
  have hG := hasDerivAt_innerRadiusSlope δ₁ δ₂ n
  have hprod := hA.fun_mul hG
  have hD := hprod.congr_of_eventuallyEq heq
  rw [hD.deriv, innerRadiusSlope_zero, twoModeSquaredRadius_zero_zero]
  unfold bilinearSquaredRadiusJet squaredRadiusJetOf
  have hr := (archimedeanSquaredRadius_pos n).ne'
  field_simp
  ring

end CosineModeResponse
end RHTower
