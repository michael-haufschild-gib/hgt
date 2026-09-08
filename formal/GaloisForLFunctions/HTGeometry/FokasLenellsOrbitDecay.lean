import GaloisForLFunctions.HTGeometry.FokasLenellsOscillatoryOrbit

/-!
# Reciprocal spectral decay of the constructed off-diagonal endpoint entries

The oscillatory source gains one spectral power by integration by parts.
The corpus's integral Gronwall theorem preserves this gain through diagonal
transport. Passing to the already constructed infinite endpoint limits
proves frequency decay for both off-diagonal entries of both asymptotic
matrices. All spectra and both orientations are covered unconditionally.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The zero initial off-diagonal coordinate satisfies a scalar transport equation with the oscillatory source. -/
theorem offOrbit_integral (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    offOrbit f g h z left upper x =
      (∫ s in (0:ℝ)..x, offOrbitDiagonal f g h left upper s*offOrbit f g h z left upper s)+
        offOrbitSource f g h z left upper x := by
  have hp : Continuous (FDNLS.staggerPhase (offOrbitFrequency z left upper)) := by
    unfold FDNLS.staggerPhase
    fun_prop
  have h1 := ((offOrbitDiagonal f g h left upper).continuous.mul
    (offOrbit_continuous f g h z left upper)).intervalIntegrable (μ := volume) 0 x
  have h2 := (hp.mul (offOrbitAmplitude_continuous f g h z left upper)).intervalIntegrable (μ := volume) 0 x
  change IntervalIntegrable (fun s => offOrbitDiagonal f g h left upper s*offOrbit f g h z left upper s) volume 0 x at h1
  change IntervalIntegrable (fun s => FDNLS.staggerPhase (offOrbitFrequency z left upper) s*offOrbitAmplitude f g h z left upper s) volume 0 x at h2
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => offOrbit_hasDerivAt f g h z left upper s)
    ((offOrbitRate_continuous f g h z left upper).intervalIntegrable 0 x)
  rw [offOrbit_initial, sub_zero] at hi
  simp only [offOrbitRate_eq] at hi
  simp only [offOrbitAmplitude] at h2
  rw [intervalIntegral.integral_add h1 h2] at hi
  exact hi.symm

def offOrbitDecayConstant (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) : ℝ :=
  (offOrbitAmplitudeBudget f g h left upper/2)*Real.exp (effectiveMass f g h)

theorem offOrbitDecayConstant_nonneg (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) :
    0 ≤ offOrbitDecayConstant f g h left upper := by
  unfold offOrbitDecayConstant
  exact mul_nonneg (div_nonneg (offOrbitAmplitudeBudget_nonneg f g h left upper) (by positivity)) (Real.exp_pos _).le

/-- Gronwall propagates the source's frequency gain through the remaining diagonal transport. -/
theorem offOrbit_frequency_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    |z| *‖offOrbit f g h z left upper |x|‖ ≤ offOrbitDecayConstant f g h left upper := by
  have hS := (offOrbit_continuous f g h z left upper).norm.const_mul |z|
  have hk := (offOrbitDiagonal f g h left upper).continuous.norm
  have hc : 0 ≤ offOrbitAmplitudeBudget f g h left upper/2 :=
    div_nonneg (offOrbitAmplitudeBudget_nonneg f g h left upper) (by positivity)
  apply le_mul_exp_of_le_add_integral_of_mass_le (A := 0) (B := |x|)
    (S := fun s => |z| *‖offOrbit f g h z left upper s‖)
    (k := fun s => ‖offOrbitDiagonal f g h left upper s‖)
    (abs_nonneg x) hS.continuousOn hk.continuousOn (fun _ _ => norm_nonneg _) hc
  · intro y hy
    have hs := offOrbitSource_frequency_bound f g h z left upper y
    rw [abs_of_nonneg hy.1] at hs
    have hcSource : |z| *‖offOrbitSource f g h z left upper y‖ ≤ offOrbitAmplitudeBudget f g h left upper/2 := by
      linarith
    have hi : ‖∫ s in (0:ℝ)..y, offOrbitDiagonal f g h left upper s*offOrbit f g h z left upper s‖ ≤
        ∫ s in (0:ℝ)..y, ‖offOrbitDiagonal f g h left upper s‖*‖offOrbit f g h z left upper s‖ := by
      simpa only [norm_mul] using intervalIntegral.norm_integral_le_integral_norm
        (f := fun s => offOrbitDiagonal f g h left upper s*offOrbit f g h z left upper s) hy.1
    calc
      _ = |z| *‖(∫ s in (0:ℝ)..y, offOrbitDiagonal f g h left upper s*offOrbit f g h z left upper s)+
          offOrbitSource f g h z left upper y‖ := by rw [offOrbit_integral]
      _ ≤ |z| *(‖∫ s in (0:ℝ)..y, offOrbitDiagonal f g h left upper s*offOrbit f g h z left upper s‖+
          ‖offOrbitSource f g h z left upper y‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg z)
      _ ≤ |z| *(∫ s in (0:ℝ)..y, ‖offOrbitDiagonal f g h left upper s‖*‖offOrbit f g h z left upper s‖)+
          offOrbitAmplitudeBudget f g h left upper/2 := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_left hi (abs_nonneg z)) hcSource
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul]
        rw [add_comm]
        congr 1
        apply intervalIntegral.integral_congr
        intro s _
        ring
  · intro y hy
    calc
      (∫ s in (0:ℝ)..y, ‖offOrbitDiagonal f g h left upper s‖) ≤
          ∫ s in (0:ℝ)..y, orientedEffectiveDensity f g h left s :=
        intervalIntegral.integral_mono_on hy.1 (hk.intervalIntegrable 0 y)
          ((orientedEffectiveDensity_continuous f g h left).intervalIntegrable 0 y)
          (fun s _ => offOrbitDiagonal_le_density f g h left upper s)
      _ ≤ effectiveMass f g h := by
        rw [intervalIntegral.integral_of_le hy.1, ← orientedEffectiveDensity_integral f g h left]
        exact setIntegral_le_integral (orientedEffectiveDensity_integrable f g h left)
          (Eventually.of_forall (orientedEffectiveDensity_nonneg f g h left))
  · exact ⟨abs_nonneg x,le_rfl⟩

/-- The off-diagonal entries have a global reciprocal envelope, including zero frequency. -/
theorem offOrbit_reciprocal_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    ‖offOrbit f g h z left upper |x|‖ ≤
      (Real.exp (effectiveMass f g h)+offOrbitDecayConstant f g h left upper)/(1+|z|) := by
  apply (le_div_iff₀ (by positivity)).mpr
  have h0 := (offOrbit_coordinates_bound f g h z left upper x).1
  have h1 := offOrbit_frequency_bound f g h z left upper x
  nlinarith

def offOrbitEndpoint (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) : ℂ :=
  uniformizedAsymptoticMatrix f g h z left (if upper then 0 else 1) (if upper then 1 else 0)

theorem offOrbit_tendsto_endpoint (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Tendsto (offOrbit f g h z left upper) atTop (𝓝 (offOrbitEndpoint f g h z left upper)) := by
  cases upper
  · exact (uniformizedOrbit_tendsto f g h z (1,0) left).snd_nhds
  · exact (uniformizedOrbit_tendsto f g h z (0,1) left).fst_nhds

/-- Infinite endpoint normalization preserves the frequency decay. -/
theorem offOrbitEndpoint_frequency_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    |z| *‖offOrbitEndpoint f g h z left upper‖ ≤ offOrbitDecayConstant f g h left upper := by
  apply le_of_tendsto ((offOrbit_tendsto_endpoint f g h z left upper).norm.const_mul |z|)
  exact eventually_atTop.2 ⟨0,fun x hx => by simpa only [abs_of_nonneg hx] using offOrbit_frequency_bound f g h z left upper x⟩

end
end GaloisForLFunctions.HTGeometry.FokasLenells
