import GaloisForLFunctions.RHTower.MellinApertureIndependence
import GaloisForLFunctions.RHTower.SoninExtendedDilation
import GaloisForLFunctions.RHTower.SoninDilationContinuity

/-!
# The Mellin transform of a dilate, and the dilation-difference multiplier

`rayDilate v f (t) = √v · f(v t)` almost everywhere, so its right Mellin transform is
`v^{s-1/2}` times that of `f`.  Subtracting a constant multiple of `f` therefore multiplies the
transform by the entire factor `v^{s-1/2} - v^{ρ-1/2}`, which vanishes at `ρ` and is not
identically zero as soon as `v ≠ 1`.  This is the elementary substitute for Burnol's bump
multiplier `θ(s)` in the proof of Lemma 7.5: it gains one order of vanishing at a prescribed point
while shrinking the aperture by the factor `v`.

## Main results

* `soninMellinIntegral_rayDilate`
* `dilationDifferenceMultiplier`, `dilationDifferenceMultiplier_self`,
  `dilationDifferenceMultiplier_ne_zero`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

noncomputable section

theorem soninMellinIntegral_rayDilate {v : ℝ} (hv : 0 < v) (f : SoninL2) (z : ℂ) :
    soninMellinIntegral (rayDilate v f) z
      = ((v : ℝ) : ℂ) ^ (z - 1 / 2) * soninMellinIntegral f z := by
  have hvc : ((v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv
  rw [soninMellinIntegral_eq_mellin, soninMellinIntegral_eq_mellin]
  have hae : ((rayDilate v f : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] fun t : ℝ => ((Real.sqrt v : ℝ) : ℂ) * (f : ℝ → ℂ) (v * t) := rayDilate_ae hv f
  have hcongr : mellin ((rayDilate v f : SoninL2) : ℝ → ℂ) (1 - z)
      = mellin (fun t : ℝ => ((Real.sqrt v : ℝ) : ℂ) * (f : ℝ → ℂ) (v * t)) (1 - z) := by
    rw [mellin, mellin]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [hae] with t ht _
    rw [ht]
  rw [hcongr]
  have hsmul : mellin (fun t : ℝ => ((Real.sqrt v : ℝ) : ℂ) * (f : ℝ → ℂ) (v * t)) (1 - z)
      = ((Real.sqrt v : ℝ) : ℂ) * mellin (fun t : ℝ => (f : ℝ → ℂ) (v * t)) (1 - z) := by
    rw [mellin, mellin, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [smul_eq_mul]
    ring
  rw [hsmul, mellin_comp_mul_left (f : ℝ → ℂ) (1 - z) hv]
  have hsqrt : ((Real.sqrt v : ℝ) : ℂ) = ((v : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ← Complex.ofReal_cpow hv.le]
  rw [hsqrt, smul_eq_mul, ← mul_assoc, ← Complex.cpow_add _ _ hvc]
  congr 2
  push_cast
  ring

/-- The entire multiplier `v^{s-1/2} - v^{ρ-1/2}`. -/
def dilationDifferenceMultiplier (v : ℝ) (ρ : ℂ) : ℂ → ℂ := fun s =>
  ((v : ℝ) : ℂ) ^ (s - 1 / 2) - ((v : ℝ) : ℂ) ^ (ρ - 1 / 2)

theorem differentiable_dilationDifferenceMultiplier {v : ℝ} (hv : 0 < v) (ρ : ℂ) :
    Differentiable ℂ (dilationDifferenceMultiplier v ρ) := by
  have hvc : ((v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv
  have hcpow : Differentiable ℂ fun s : ℂ => ((v : ℝ) : ℂ) ^ (s - 1 / 2) := by
    have h : (fun s : ℂ => ((v : ℝ) : ℂ) ^ (s - 1 / 2))
        = fun s : ℂ => Complex.exp (Complex.log ((v : ℝ) : ℂ) * (s - 1 / 2)) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero hvc]
    rw [h]
    exact Complex.differentiable_exp.comp ((differentiable_const _).mul
      (differentiable_id.sub (differentiable_const _)))
  exact hcpow.sub (differentiable_const _)

@[simp] theorem dilationDifferenceMultiplier_self (v : ℝ) (ρ : ℂ) :
    dilationDifferenceMultiplier v ρ ρ = 0 := by
  rw [dilationDifferenceMultiplier]
  ring

/-- The multiplier is not identically zero: it is nonzero one unit to the right of `ρ`. -/
theorem dilationDifferenceMultiplier_ne_zero {v : ℝ} (hv : 0 < v) (hv1 : v ≠ 1) (ρ : ℂ) :
    dilationDifferenceMultiplier v ρ (ρ + 1) ≠ 0 := by
  have hvc : ((v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv
  have hstep : ((v : ℝ) : ℂ) ^ ((ρ + 1) - 1 / 2)
      = ((v : ℝ) : ℂ) ^ (ρ - 1 / 2) * ((v : ℝ) : ℂ) := by
    have h1 : ((ρ + 1) - 1 / 2 : ℂ) = (ρ - 1 / 2) + 1 := by ring
    rw [h1, Complex.cpow_add _ _ hvc, Complex.cpow_one]
  rw [dilationDifferenceMultiplier, hstep]
  have hne : ((v : ℝ) : ℂ) ^ (ρ - 1 / 2) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hvc)
  have hv1' : ((v : ℝ) : ℂ) - 1 ≠ 0 := by
    intro h
    have : ((v : ℝ) : ℂ) = 1 := by linear_combination h
    exact hv1 (by exact_mod_cast this)
  intro hzero
  refine hv1' ?_
  have : ((v : ℝ) : ℂ) ^ (ρ - 1 / 2) * (((v : ℝ) : ℂ) - 1) = 0 := by
    linear_combination hzero
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hne
  · exact h

end

end RHTower
