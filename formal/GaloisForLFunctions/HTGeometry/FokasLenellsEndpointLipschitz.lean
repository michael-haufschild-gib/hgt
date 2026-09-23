import GaloisForLFunctions.HTGeometry.FokasLenellsSpectralComparison

/-!
# Global spectral Lipschitz bounds for both scattering endpoints

One integrable first moment controls the inhomogeneous frequency difference.
The existing variable-coefficient Grönwall theorem gives a comparison bound
independent of interval length. Passing to both infinite endpoints preserves
that bound. The determinant-one endpoint inverse has the same entrywise
Lipschitz constant because its adjugate is linear in dimension two.
-/

open Complex Matrix MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Orientation preserves the homogeneous comparison density and the first-moment source. -/
theorem uniformizedOrbitDerivative_joint_bound (f g h : SchwartzMap ℝ ℂ)
    (z w : ℝ) (v : SpectralVector) (b : Bool) (x : ℝ) :
    ‖uniformizedOrbitDerivative f g h z v b x-uniformizedOrbitDerivative f g h w v b x‖ ≤
      orientedEffectiveDensity f g h b x*‖uniformizedOrbit f g h z v b x-uniformizedOrbit f g h w v b x‖+
      2*|x| *|z-w| *orientedEffectiveDensity f g h b x*‖uniformizedOrbit f g h w v b x‖ := by
  cases b
  · exact uniformizedInteractionRate_joint_bound f g h z w x _ _
  · simpa only [uniformizedOrbitDerivative,uniformizedOrbit,orientedEffectiveDensity,↓reduceIte,
      neg_sub_neg,norm_sub_rev,abs_neg] using uniformizedInteractionRate_joint_bound f g h z w (-x)
      (uniformizedInteractionSolution f g h z v (-x)) (uniformizedInteractionSolution f g h w v (-x))

/-- A single finite first-moment budget controls frequency changes on both infinite half-lines. -/
def uniformizedFrequencyBudget (f g h : SchwartzMap ℝ ℂ) : ℝ :=
  2*Real.exp (effectiveMass f g h)^(2 : ℕ)*effectiveMoment f g h 1

theorem uniformizedFrequencyBudget_nonneg (f g h : SchwartzMap ℝ ℂ) :
    0 ≤ uniformizedFrequencyBudget f g h := by
  unfold uniformizedFrequencyBudget
  exact mul_nonneg (by positivity) (effectiveMoment_nonneg f g h 1)

/-- Integrable-coefficient Grönwall yields a spectral Lipschitz bound uniform in spatial distance. -/
theorem uniformizedOrbit_parameter_bound (f g h : SchwartzMap ℝ ℂ) (z w : ℝ)
    (v : SpectralVector) (b : Bool) (x : ℝ) :
    ‖uniformizedOrbit f g h z v b |x|-uniformizedOrbit f g h w v b |x|‖ ≤
      uniformizedFrequencyBudget f g h*‖v‖*|z-w| := by
  let S := fun y => ‖uniformizedOrbit f g h z v b y-uniformizedOrbit f g h w v b y‖
  let k := orientedEffectiveDensity f g h b
  let m := fun y : ℝ => |y| *k y
  let A := 2*|z-w| *‖v‖*Real.exp (effectiveMass f g h)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hS : Continuous S := ((uniformizedOrbit_continuous f g h z v b).sub
    (uniformizedOrbit_continuous f g h w v b)).norm
  have hk : Continuous k := orientedEffectiveDensity_continuous f g h b
  have hm : Continuous m := continuous_abs.mul hk
  have hder : ∀ y : ℝ, 0 ≤ y →
      ‖uniformizedOrbitDerivative f g h z v b y-uniformizedOrbitDerivative f g h w v b y‖ ≤ k y*S y+A*m y := by
    intro y hy
    have hw := uniformizedOrbit_bound f g h w v b y
    rw [abs_of_nonneg hy] at hw
    have h0 := uniformizedOrbitDerivative_joint_bound f g h z w v b y
    have hn := orientedEffectiveDensity_nonneg f g h b y
    calc
      _ ≤ k y*S y+2*|y| *|z-w| *k y*‖uniformizedOrbit f g h w v b y‖ := h0
      _ ≤ k y*S y+2*|y| *|z-w| *k y*(‖v‖*Real.exp (effectiveMass f g h)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hw (by dsimp [k]; positivity))
      _ = _ := by dsimp [A,m]; ring
  have hD := ((uniformizedOrbitDerivative_continuous f g h z v b).sub
    (uniformizedOrbitDerivative_continuous f g h w v b)).norm
  have hmajor : Continuous (fun y => k y*S y+A*m y) := (hk.mul hS).add (continuous_const.mul hm)
  have hG := le_mul_exp_of_le_add_integral_of_mass_le (A := 0) (B := |x|)
    (C := A*effectiveMoment f g h 1) (M := effectiveMass f g h)
    (abs_nonneg x) hS.continuousOn hk.continuousOn
    (fun y _ => orientedEffectiveDensity_nonneg f g h b y)
    (mul_nonneg hA (effectiveMoment_nonneg f g h 1))
  have hbound : ∀ y ∈ Icc (0:ℝ) |x|, S y ≤ A*effectiveMoment f g h 1+∫ s in (0:ℝ)..y, k s*S s := by
    intro y hy
    have he : uniformizedOrbit f g h z v b y-uniformizedOrbit f g h w v b y =
        ∫ s in (0:ℝ)..y, uniformizedOrbitDerivative f g h z v b s-uniformizedOrbitDerivative f g h w v b s := by
      rw [uniformizedOrbit_integral,uniformizedOrbit_integral,intervalIntegral.integral_sub
        ((uniformizedOrbitDerivative_continuous f g h z v b).intervalIntegrable 0 y)
        ((uniformizedOrbitDerivative_continuous f g h w v b).intervalIntegrable 0 y)]
      abel
    have hmom : (∫ s in (0:ℝ)..y, m s) ≤ effectiveMoment f g h 1 := by
      rw [intervalIntegral.integral_of_le hy.1,← orientedEffectiveDensity_moment_integral f g h b 1]
      simp only [pow_one]
      exact setIntegral_le_integral (by simpa only [pow_one] using orientedEffectiveDensity_moment_integrable f g h b 1)
        (Eventually.of_forall fun s => mul_nonneg (abs_nonneg s) (orientedEffectiveDensity_nonneg f g h b s))
    calc
      S y = ‖∫ s in (0:ℝ)..y, uniformizedOrbitDerivative f g h z v b s-uniformizedOrbitDerivative f g h w v b s‖ := congrArg norm he
      _ ≤ ∫ s in (0:ℝ)..y, ‖uniformizedOrbitDerivative f g h z v b s-uniformizedOrbitDerivative f g h w v b s‖ :=
        intervalIntegral.norm_integral_le_integral_norm hy.1
      _ ≤ ∫ s in (0:ℝ)..y, (k s*S s+A*m s) :=
        intervalIntegral.integral_mono_on hy.1 (hD.intervalIntegrable 0 y) (hmajor.intervalIntegrable 0 y)
          (fun s hs => hder s hs.1)
      _ = (∫ s in (0:ℝ)..y, k s*S s)+A*(∫ s in (0:ℝ)..y, m s) := by
        have hkS : IntervalIntegrable (fun s => k s*S s) volume 0 y := (hk.mul hS).intervalIntegrable 0 y
        have hAm : IntervalIntegrable (fun s => A*m s) volume 0 y := (continuous_const.mul hm).intervalIntegrable 0 y
        rw [intervalIntegral.integral_add hkS hAm,intervalIntegral.integral_const_mul]
      _ ≤ (∫ s in (0:ℝ)..y, k s*S s)+A*effectiveMoment f g h 1 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hmom hA)
      _ = _ := add_comm _ _
  have hmass : ∀ y ∈ Icc (0:ℝ) |x|, (∫ s in (0:ℝ)..y, k s) ≤ effectiveMass f g h := by
    intro y hy
    rw [intervalIntegral.integral_of_le hy.1,← orientedEffectiveDensity_integral f g h b]
    exact setIntegral_le_integral (orientedEffectiveDensity_integrable f g h b)
      (Eventually.of_forall (orientedEffectiveDensity_nonneg f g h b))
  have hb := hG hbound hmass |x| ⟨abs_nonneg x,le_rfl⟩
  calc
    _ ≤ A*effectiveMoment f g h 1*Real.exp (effectiveMass f g h) := hb
    _ = _ := by dsimp [A,uniformizedFrequencyBudget]; ring

/-- Both infinite endpoint vectors inherit the same global frequency bound. -/
theorem uniformizedAsymptoticVector_parameter_bound (f g h : SchwartzMap ℝ ℂ)
    (z w : ℝ) (v : SpectralVector) (b : Bool) :
    ‖uniformizedAsymptoticVector f g h z v b-uniformizedAsymptoticVector f g h w v b‖ ≤
      uniformizedFrequencyBudget f g h*‖v‖*|z-w| := by
  apply le_of_tendsto (((uniformizedOrbit_tendsto f g h z v b).sub (uniformizedOrbit_tendsto f g h w v b)).norm)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  simpa only [abs_of_nonneg hx] using uniformizedOrbit_parameter_bound f g h z w v b x

/-- Each endpoint matrix entry is globally Lipschitz on the entire real spectral line. -/
theorem uniformizedAsymptoticMatrix_entry_parameter_bound (f g h : SchwartzMap ℝ ℂ)
    (z w : ℝ) (b : Bool) (i j : Fin 2) :
    ‖uniformizedAsymptoticMatrix f g h z b i j-uniformizedAsymptoticMatrix f g h w b i j‖ ≤
      uniformizedFrequencyBudget f g h*|z-w| := by
  have h0 := uniformizedAsymptoticVector_parameter_bound f g h z w (1,0) b
  have h1 := uniformizedAsymptoticVector_parameter_bound f g h z w (0,1) b
  simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,norm_one,norm_zero,
    max_eq_left (show (0:ℝ) ≤ 1 by positivity),max_eq_right (show (0:ℝ) ≤ 1 by positivity),mul_one] at h0 h1
  fin_cases i <;> fin_cases j
  · exact (max_le_iff.mp h0).1
  · exact (max_le_iff.mp h1).1
  · exact (max_le_iff.mp h0).2
  · exact (max_le_iff.mp h1).2

/-- The determinant-one inverse in dimension two preserves the endpoint entrywise Lipschitz constant. -/
theorem uniformizedAsymptoticMatrix_inverse_entry_parameter_bound (f g h : SchwartzMap ℝ ℂ)
    (z w : ℝ) (b : Bool) (i j : Fin 2) :
    ‖(uniformizedAsymptoticMatrix f g h z b)⁻¹ i j-(uniformizedAsymptoticMatrix f g h w b)⁻¹ i j‖ ≤
      uniformizedFrequencyBudget f g h*|z-w| := by
  rw [Matrix.inv_def,Matrix.inv_def,uniformizedAsymptoticMatrix_det,uniformizedAsymptoticMatrix_det]
  simp only [Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · exact uniformizedAsymptoticMatrix_entry_parameter_bound f g h z w b 1 1
  · change ‖-uniformizedAsymptoticMatrix f g h z b 0 1-(-uniformizedAsymptoticMatrix f g h w b 0 1)‖ ≤ _
    rw [neg_sub_neg,norm_sub_rev]
    exact uniformizedAsymptoticMatrix_entry_parameter_bound f g h z w b 0 1
  · change ‖-uniformizedAsymptoticMatrix f g h z b 1 0-(-uniformizedAsymptoticMatrix f g h w b 1 0)‖ ≤ _
    rw [neg_sub_neg,norm_sub_rev]
    exact uniformizedAsymptoticMatrix_entry_parameter_bound f g h z w b 1 0
  · exact uniformizedAsymptoticMatrix_entry_parameter_bound f g h z w b 0 0

end
end GaloisForLFunctions.HTGeometry.FokasLenells
