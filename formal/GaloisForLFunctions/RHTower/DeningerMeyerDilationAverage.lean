import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogMellin
import GaloisForLFunctions.RHTower.DeningerMeyerRadialEndpoints
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!+# All-weight averages of genuine Schwartz dilates

Every Schwartz seminorm of a dilation costs an exponential weight in the
logarithmic parameter. An actual Meyer source absorbs every such cost,
so its dilation average remains Schwartz in the original physical radius.
-/

open Complex MeasureTheory Filter Set Topology SchwartzMap
open scoped ContDiff

namespace RHTower
noncomputable section

theorem deningerMeyer_expWeight_integrable
    (h : DeningerMeyerStrongLogTarget) (r : ℝ) :
    Integrable (fun t : ℝ => Real.exp (r*t)*‖h.val t‖) := by
  have hi := (integrable_deningerMeyerStrongLogMellinJet h.property 0 (r : ℂ)).norm
  simpa only [norm_deningerMeyerStrongLogMellinJet, pow_zero, one_mul, Complex.ofReal_re] using hi

def deningerMeyerDilationKernel (h : DeningerMeyerStrongLogTarget)
    (f : 𝓢(ℝ, ℂ)) (n : ℕ) (x t : ℝ) : ℂ :=
  h.val t * (Real.exp (-(n : ℝ)*t) : ℂ) *
    iteratedDeriv n (f : ℝ → ℂ) (Real.exp (-t)*x)

private theorem kernel_continuous (h : DeningerMeyerStrongLogTarget)
    (f : 𝓢(ℝ, ℂ)) (n : ℕ) (x : ℝ) :
    Continuous (deningerMeyerDilationKernel h f n x) := by
  have hf := f.smooth'.continuous_iteratedDeriv n (by exact_mod_cast le_top)
  exact (h.property.smooth.continuous.mul (by fun_prop)).mul (hf.comp (by fun_prop))

theorem deningerMeyerDilationKernel_weighted_bound
    (h : DeningerMeyerStrongLogTarget) (f : 𝓢(ℝ, ℂ)) (k n : ℕ) (x t : ℝ) :
    ‖x‖^k * ‖deningerMeyerDilationKernel h f n x t‖ ≤
      SchwartzMap.seminorm ℂ k n f * Real.exp (((k : ℝ)-n)*t) * ‖h.val t‖ := by
  have hf := SchwartzMap.le_seminorm' ℂ k n f (Real.exp (-t)*x)
  have hscale : ‖Real.exp (-t)*x‖^k = Real.exp (-(k : ℝ)*t)*‖x‖^k := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [← Real.norm_eq_abs, hscale] at hf
  have he : Real.exp (((k : ℝ)-n)*t)*Real.exp (-(k : ℝ)*t) =
      Real.exp (-(n : ℝ)*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hf (Real.exp_nonneg (((k : ℝ)-n)*t))) (norm_nonneg (h.val t))
  rw [deningerMeyerDilationKernel, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs (Real.exp (-(n : ℝ)*t)), abs_of_pos (Real.exp_pos _)]
  calc ‖x‖^k * (‖h.val t‖*Real.exp (-(n : ℝ)*t)*
        ‖iteratedDeriv n (f : ℝ → ℂ) (Real.exp (-t)*x)‖)
      = (Real.exp (((k : ℝ)-n)*t)*
          (Real.exp (-(k : ℝ)*t)*‖x‖^k*
            ‖iteratedDeriv n (f : ℝ → ℂ) (Real.exp (-t)*x)‖))*‖h.val t‖ := by
        rw [← he]
        ring
    _ ≤ _ := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

theorem deningerMeyerDilationKernel_integrable
    (h : DeningerMeyerStrongLogTarget) (f : 𝓢(ℝ, ℂ)) (n : ℕ) (x : ℝ) :
    Integrable (deningerMeyerDilationKernel h f n x) := by
  apply ((deningerMeyer_expWeight_integrable h (-(n : ℝ))).const_mul
    (SchwartzMap.seminorm ℂ 0 n f)).mono' (kernel_continuous h f n x).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [pow_zero, one_mul, Nat.cast_zero, zero_sub, mul_assoc] using
      deningerMeyerDilationKernel_weighted_bound h f 0 n x t

private theorem kernel_hasDerivAt (h : DeningerMeyerStrongLogTarget)
    (f : 𝓢(ℝ, ℂ)) (n : ℕ) (x t : ℝ) :
    HasDerivAt (fun y => deningerMeyerDilationKernel h f n y t)
      (deningerMeyerDilationKernel h f (n+1) x t) x := by
  have hd := (f.smooth'.differentiable_iteratedDeriv n
    (by exact_mod_cast lt_top_iff_ne_top.mpr (ENat.coe_ne_top n))
    (Real.exp (-t)*x)).hasDerivAt.scomp x ((hasDerivAt_id x).const_mul (Real.exp (-t)))
  have hp := hd.const_mul (h.val t*(Real.exp (-(n : ℝ)*t) : ℂ))
  apply hp.congr_deriv
  simp only [Complex.real_smul, ← iteratedDeriv_succ, mul_one]
  change h.val t * (Real.exp (-(n : ℝ)*t) : ℂ) *
      ((Real.exp (-t) : ℂ)*iteratedDeriv (n+1) (f : ℝ → ℂ) (Real.exp (-t)*x)) = _
  have hexp : (Real.exp (-(n : ℝ)*t) : ℂ)*(Real.exp (-t) : ℂ) =
      (Real.exp (-((n+1 : ℕ) : ℝ)*t) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring
  dsimp [deningerMeyerDilationKernel]
  rw [← mul_assoc, mul_assoc (h.val t), hexp]

theorem deningerMeyerDilationIntegral_hasDerivAt
    (h : DeningerMeyerStrongLogTarget) (f : 𝓢(ℝ, ℂ)) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => ∫ t, deningerMeyerDilationKernel h f n y t)
      (∫ t, deningerMeyerDilationKernel h f (n+1) x t) x := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (F := fun x t => deningerMeyerDilationKernel h f n x t)
    (F' := fun x t => deningerMeyerDilationKernel h f (n+1) x t)
    (bound := fun t => SchwartzMap.seminorm ℂ 0 (n+1) f *
      (Real.exp (-(n+1 : ℝ)*t)*‖h.val t‖))
    (Filter.univ_mem)
    (Eventually.of_forall fun y => (kernel_continuous h f n y).aestronglyMeasurable)
    (deningerMeyerDilationKernel_integrable h f n x)
    (kernel_continuous h f (n+1) x).aestronglyMeasurable
    (Eventually.of_forall fun t y _ => by
      simpa only [pow_zero, one_mul, Nat.cast_zero, zero_sub, Nat.cast_add, Nat.cast_one,
        mul_assoc] using deningerMeyerDilationKernel_weighted_bound h f 0 (n+1) y t)
    ((deningerMeyer_expWeight_integrable h (-(n+1 : ℝ))).const_mul _)
    (Eventually.of_forall fun t y _ => kernel_hasDerivAt h f n y t)).2

def deningerMeyerDilationAverageProfile (h : DeningerMeyerStrongLogTarget)
    (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ∫ t, deningerMeyerDilationKernel h f 0 x t

theorem iteratedDeriv_deningerMeyerDilationAverageProfile
    (h : DeningerMeyerStrongLogTarget) (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    iteratedDeriv n (deningerMeyerDilationAverageProfile h f) =
      fun x => ∫ t, deningerMeyerDilationKernel h f n x t := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      exact funext fun x => (deningerMeyerDilationIntegral_hasDerivAt h f n x).deriv

def deningerMeyerDilationAverage (h : DeningerMeyerStrongLogTarget)
    (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) where
  toFun := deningerMeyerDilationAverageProfile h f
  smooth' := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro n _
    rw [iteratedDeriv_deningerMeyerDilationAverageProfile]
    exact fun x => (deningerMeyerDilationIntegral_hasDerivAt h f n x).differentiableAt
  decay' k n := by
    let major := fun t => SchwartzMap.seminorm ℂ k n f *
      (Real.exp (((k : ℝ)-n)*t)*‖h.val t‖)
    have hi : Integrable major := (deningerMeyer_expWeight_integrable h _).const_mul _
    refine ⟨∫ t, major t, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_deningerMeyerDilationAverageProfile]
    have hn := norm_integral_le_of_norm_le hi
      (Eventually.of_forall fun t => ?_)
      (f := fun t => (‖x‖^k : ℝ) • deningerMeyerDilationKernel h f n x t)
    · simpa only [integral_smul, norm_smul, Real.norm_eq_abs, abs_pow, abs_abs] using hn
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) k)]
      simpa only [major, mul_assoc] using deningerMeyerDilationKernel_weighted_bound h f k n x t

end
end RHTower
