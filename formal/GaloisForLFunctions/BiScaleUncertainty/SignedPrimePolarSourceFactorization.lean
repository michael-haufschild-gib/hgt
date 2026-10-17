import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalSource

open MeasureTheory Set
open scoped CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

/-- The reflected factorial ramp is an actual compact continuous source. -/
def factorialSourceLeft (n : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => sourceFactorialRamp (n+1) (-u),
    (continuous_sourceFactorialRamp (n+1)).comp continuous_neg⟩,
    (hasCompactSupport_sourceFactorialRamp (by omega : 1 ≤ n+1)).comp_homeomorph (Homeomorph.neg ℝ)⟩

/-- The narrow exponential tent is the second actual source. -/
def factorialSourceRight (n : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨exponentialTentSource (sourceFactorialWidth (n+1)), continuous_exponentialTentSource _⟩,
    hasCompactSupport_exponentialTentSource _⟩

def factorialSourceScale (n : ℕ) : ℝ := Real.sqrt (Real.sqrt (n+1 : ℕ))

theorem factorialSourceScale_pos (n : ℕ) : 0 < factorialSourceScale n := by
  unfold factorialSourceScale
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem factorialSourceScale_sq (n : ℕ) : (factorialSourceScale n)^2 = Real.sqrt (n+1 : ℕ) :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

def factorialSourcePlus (n : ℕ) : C_c(ℝ, ℝ) :=
  factorialSourceScale n • factorialSourceLeft n+(factorialSourceScale n)⁻¹ • factorialSourceRight n

def factorialSourceMinus (n : ℕ) : C_c(ℝ, ℝ) :=
  factorialSourceScale n • factorialSourceLeft n-(factorialSourceScale n)⁻¹ • factorialSourceRight n

/-- A signed contrast of two genuine source autocorrelations. -/
def factorialSourceContrast (n : ℕ) (x : ℝ) : ℝ :=
  (autocorr (factorialSourcePlus n) x-autocorr (factorialSourceMinus n) x)/2

theorem sourceFactorialCausal_eq_integral (N : ℕ) (x : ℝ) :
    sourceFactorialCausal N x =
      ∫ t : ℝ, sourceFactorialRamp N (x-t)*exponentialTentSource (sourceFactorialWidth N) t := by
  have he : sourceFactorialCausal N x =
      ∫ t in Icc 0 (2*sourceFactorialWidth N),
        sourceFactorialRamp N (x-t)*exponentialTentSource (sourceFactorialWidth N) t := by
    apply integral_congr_ae
    filter_upwards [] with t
    unfold exponentialTentSource
    ring
  rw [he]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  simp [exponentialTentSource, exponentialTentDensity_zero_of_not_mem _ ht]

theorem factorialSource_mixed_forward (n : ℕ) (x : ℝ) :
    (∫ u : ℝ, factorialSourceLeft n u*factorialSourceRight n (u+x)) = sourceFactorialCausal (n+1) x := by
  rw [sourceFactorialCausal_eq_integral,
    ← integral_add_right_eq_self (fun u => factorialSourceLeft n u*factorialSourceRight n (u+x)) (-x)]
  apply integral_congr_ae
  filter_upwards [] with u
  change sourceFactorialRamp (n+1) (-(u+ -x))*exponentialTentSource _ (u+ -x+x) = _
  congr 1 <;> congr 1 <;> ring

theorem factorialSource_mixed_reverse (n : ℕ) (x : ℝ) :
    (∫ u : ℝ, factorialSourceRight n u*factorialSourceLeft n (u+x)) = sourceFactorialCausal (n+1) (-x) := by
  rw [sourceFactorialCausal_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with u
  change exponentialTentSource _ u*sourceFactorialRamp (n+1) (-(u+x)) = _
  rw [show -(u+x) = -x-u by ring]
  ring

private theorem integrable_mixed_shift (f g : C_c(ℝ, ℝ)) (x : ℝ) :
    Integrable (fun u => f u*g (u+x)) :=
  (f.continuous.mul (g.continuous.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
    (f.hasCompactSupport.mul_right)

theorem factorialSourceContrast_eq (n : ℕ) (x : ℝ) :
    factorialSourceContrast n x = sourceFactorialCausal (n+1) x+sourceFactorialCausal (n+1) (-x) := by
  have hiP : Integrable (fun u => factorialSourcePlus n u*factorialSourcePlus n (u+x)) :=
    integrable_mul_shift (g := (factorialSourcePlus n : ℝ → ℝ))
      (factorialSourcePlus n).continuous (factorialSourcePlus n).hasCompactSupport x
  have hiM : Integrable (fun u => factorialSourceMinus n u*factorialSourceMinus n (u+x)) :=
    integrable_mul_shift (g := (factorialSourceMinus n : ℝ → ℝ))
      (factorialSourceMinus n).continuous (factorialSourceMinus n).hasCompactSupport x
  unfold factorialSourceContrast autocorr
  rw [← integral_sub hiP hiM, ← integral_div]
  calc
    _ = ∫ u : ℝ, factorialSourceLeft n u*factorialSourceRight n (u+x)+
        factorialSourceRight n u*factorialSourceLeft n (u+x) := by
      apply integral_congr_ae
      filter_upwards [] with u
      change (((factorialSourceScale n*factorialSourceLeft n u+(factorialSourceScale n)⁻¹*factorialSourceRight n u)*
          (factorialSourceScale n*factorialSourceLeft n (u+x)+(factorialSourceScale n)⁻¹*factorialSourceRight n (u+x))-
        (factorialSourceScale n*factorialSourceLeft n u-(factorialSourceScale n)⁻¹*factorialSourceRight n u)*
          (factorialSourceScale n*factorialSourceLeft n (u+x)-(factorialSourceScale n)⁻¹*factorialSourceRight n (u+x)))/2) = _
      have hs := (factorialSourceScale_pos n).ne'
      field_simp
      ring
    _ = _ := by
      rw [integral_add (integrable_mixed_shift _ _ x) (integrable_mixed_shift _ _ x),
        factorialSource_mixed_forward, factorialSource_mixed_reverse]

theorem factorialSourceContrast_eq_of_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    factorialSourceContrast n x = sourceFactorialCausal (n+1) x := by
  rw [factorialSourceContrast_eq,
    sourceFactorialCausal_zero_of_nonpos (x := -x) (by omega : 1 ≤ n+1) (by linarith), add_zero]

theorem factorialSource_disjoint (n : ℕ) (u : ℝ) :
    factorialSourceLeft n u*factorialSourceRight n u = 0 := by
  by_cases hu : 0 ≤ u
  · change sourceFactorialRamp (n+1) (-u)*_ = 0
    rw [sourceFactorialRamp_zero_of_nonpos (by omega : 1 ≤ n+1) (by linarith), zero_mul]
  · have hh : u ∉ Icc 0 (2*sourceFactorialWidth (n+1)) := fun h => hu h.1
    change _*exponentialTentSource _ u = 0
    simp [exponentialTentSource, exponentialTentDensity_zero_of_not_mem _ hh]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
