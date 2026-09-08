import GaloisForLFunctions.HTGeometry.FokasLenellsCorrectedDecay
import GaloisForLFunctions.HTGeometry.FokasLenellsScatteringDecay

/-!
# Second-order spectral decay of genuine scattering data

The corrected endpoint is λ off + c(0) rowDiagonal. Both λ and c(0)
reverse sign on the opposite oriented half-line. Thus the leading endpoint
terms cancel exactly in the actual scattering matrix. The remaining
corrected endpoints give a second spectral power, uniformly for every
Schwartz input and both reflection numerators.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rowDiagonalEndpoint (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) : ℂ :=
  uniformizedAsymptoticMatrix f g h z left (if upper then 0 else 1) (if upper then 0 else 1)

theorem rowDiagonalOrbit_tendsto (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Tendsto (diagonalOrbit f g h z left (!upper)) atTop (𝓝 (rowDiagonalEndpoint f g h z left upper)) := by
  cases upper
  · exact (uniformizedOrbit_tendsto f g h z (0,1) left).snd_nhds
  · exact (uniformizedOrbit_tendsto f g h z (1,0) left).fst_nhds

def correctedOffEndpoint (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) : ℂ :=
  -(I*(offOrbitFrequency z left upper : ℂ))*offOrbitEndpoint f g h z left upper+
    offOrbitCoefficient f g h left upper 0*rowDiagonalEndpoint f g h z left upper

/-- The decaying Schwartz endpoint term disappears from the corrected orbit at infinity. -/
theorem correctedOffOrbit_tendsto_endpoint (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Tendsto (correctedOffOrbit f g h z left upper) atTop (𝓝 (correctedOffEndpoint f g h z left upper)) := by
  have hc := (offOrbitCoefficient f g h left upper).tendsto_cocompact.mono_left atTop_le_cocompact
  have hd := rowDiagonalOrbit_tendsto f g h z left (!upper)
  simp only [Bool.not_not] at hd
  have hcd : Tendsto (fun x => offOrbitCoefficient f g h left upper x*diagonalOrbit f g h z left upper x) atTop (𝓝 0) := by
    simpa only [zero_mul] using hc.mul hd
  have hp : Tendsto (fun x => FDNLS.staggerPhase (offOrbitFrequency z left upper) x*
      (offOrbitCoefficient f g h left upper x*diagonalOrbit f g h z left upper x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun x => ?_) (by simpa only [norm_zero] using hcd.norm)
    rw [norm_mul,FDNLS.norm_staggerPhase,one_mul]
  have h1 := (offOrbit_tendsto_endpoint f g h z left upper).const_mul (-(I*(offOrbitFrequency z left upper : ℂ)))
  have h2 := (rowDiagonalOrbit_tendsto f g h z left upper).const_mul (offOrbitCoefficient f g h left upper 0)
  change Tendsto (fun x => -(I*(offOrbitFrequency z left upper : ℂ))*offOrbit f g h z left upper x+
    offOrbitCoefficient f g h left upper 0*diagonalOrbit f g h z left (!upper) x-
    FDNLS.staggerPhase (offOrbitFrequency z left upper) x*
      (offOrbitCoefficient f g h left upper x*diagonalOrbit f g h z left upper x)) atTop
    (𝓝 (-(I*(offOrbitFrequency z left upper : ℂ))*offOrbitEndpoint f g h z left upper+
      offOrbitCoefficient f g h left upper 0*rowDiagonalEndpoint f g h z left upper))
  simpa only [sub_zero] using (h1.add h2).sub hp

/-- The corrected infinite endpoints retain their proved spectral-power bound. -/
theorem correctedOffEndpoint_frequency_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    |z| *‖correctedOffEndpoint f g h z left upper‖ ≤ correctedOffDecayConstant f g h left upper := by
  apply le_of_tendsto ((correctedOffOrbit_tendsto_endpoint f g h z left upper).norm.const_mul |z|)
  exact eventually_atTop.2 ⟨0,fun x hx => by
    simpa only [abs_of_nonneg hx] using correctedOffOrbit_frequency_bound f g h z left upper x⟩

theorem offOrbitFrequency_left (z : ℝ) (upper : Bool) :
    offOrbitFrequency z true upper = -offOrbitFrequency z false upper := by
  cases upper <;> simp [offOrbitFrequency]

theorem offOrbitCoefficient_left_zero (f g h : SchwartzMap ℝ ℂ) (upper : Bool) :
    offOrbitCoefficient f g h true upper 0 = -offOrbitCoefficient f g h false upper 0 := by
  simp [offOrbitCoefficient,orientedSchwartzEntry_apply]

/-- The two leading endpoint terms cancel exactly in the actual off-diagonal scattering entry. -/
theorem uniformizedOffDiagonal_corrected_eq (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (upper : Bool) :
    -(I*(offOrbitFrequency z false upper : ℂ))*uniformizedOffDiagonal f g h z upper =
      correctedOffEndpoint f g h z false upper*rowDiagonalEndpoint f g h z true upper+
        rowDiagonalEndpoint f g h z false upper*correctedOffEndpoint f g h z true upper := by
  rw [uniformizedOffDiagonal_eq]
  simp only [correctedOffEndpoint,offOrbitFrequency_left,offOrbitCoefficient_left_zero,Complex.ofReal_neg]
  unfold rowDiagonalEndpoint
  ring

def uniformizedSecondDecay (f g h : SchwartzMap ℝ ℂ) (upper : Bool) : ℝ :=
  ((correctedOffDecayConstant f g h false upper+correctedOffDecayConstant f g h true upper)*
    (effectiveDisplacement f g h+1))/2

theorem uniformizedSecondDecay_nonneg (f g h : SchwartzMap ℝ ℂ) (upper : Bool) :
    0 ≤ uniformizedSecondDecay f g h upper := by
  unfold uniformizedSecondDecay
  positivity [correctedOffDecayConstant_nonneg f g h false upper,correctedOffDecayConstant_nonneg f g h true upper,
    effectiveDisplacement_nonneg f g h]

/-- Every genuine reflection numerator gains two spectral powers, without assumptions on the Schwartz profile. -/
theorem uniformizedOffDiagonal_second_frequency_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (upper : Bool) :
    |z|^2*‖uniformizedOffDiagonal f g h z upper‖ ≤ uniformizedSecondDecay f g h upper := by
  have he := congrArg norm (uniformizedOffDiagonal_corrected_eq f g h z upper)
  simp only [norm_mul,norm_neg,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,offOrbitFrequency_abs] at he
  have h1 := correctedOffEndpoint_frequency_bound f g h z false upper
  have h2 := correctedOffEndpoint_frequency_bound f g h z true upper
  have hd1 := uniformizedAsymptoticMatrix_entry_bound f g h z false (if upper then 0 else 1) (if upper then 0 else 1)
  have hd2 := uniformizedAsymptoticMatrix_entry_bound f g h z true (if upper then 0 else 1) (if upper then 0 else 1)
  change ‖rowDiagonalEndpoint f g h z false upper‖ ≤ _ at hd1
  change ‖rowDiagonalEndpoint f g h z true upper‖ ≤ _ at hd2
  have hpos : 0 ≤ effectiveDisplacement f g h+1 := by linarith [effectiveDisplacement_nonneg f g h]
  have hb : |z| *(2*|z| *‖uniformizedOffDiagonal f g h z upper‖) ≤
      (correctedOffDecayConstant f g h false upper+correctedOffDecayConstant f g h true upper)*(effectiveDisplacement f g h+1) := by
    rw [he]
    calc
      _ ≤ |z| *(‖correctedOffEndpoint f g h z false upper‖*‖rowDiagonalEndpoint f g h z true upper‖+
          ‖rowDiagonalEndpoint f g h z false upper‖*‖correctedOffEndpoint f g h z true upper‖) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg z)
        simpa only [norm_mul] using norm_add_le (correctedOffEndpoint f g h z false upper*rowDiagonalEndpoint f g h z true upper)
          (rowDiagonalEndpoint f g h z false upper*correctedOffEndpoint f g h z true upper)
      _ = (|z| *‖correctedOffEndpoint f g h z false upper‖)*‖rowDiagonalEndpoint f g h z true upper‖+
          ‖rowDiagonalEndpoint f g h z false upper‖*(|z| *‖correctedOffEndpoint f g h z true upper‖) := by ring
      _ ≤ correctedOffDecayConstant f g h false upper*(effectiveDisplacement f g h+1)+
          (effectiveDisplacement f g h+1)*correctedOffDecayConstant f g h true upper :=
        add_le_add (mul_le_mul h1 hd2 (norm_nonneg _) (correctedOffDecayConstant_nonneg f g h false upper))
          (mul_le_mul hd1 h2 (by positivity) hpos)
      _ = _ := by ring
  unfold uniformizedSecondDecay
  nlinarith

/-- A globally nonsingular quadratic envelope includes both zero and large frequencies. -/
theorem uniformizedOffDiagonal_quadratic_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (upper : Bool) :
    ‖uniformizedOffDiagonal f g h z upper‖ ≤
      (4*effectiveDisplacement f g h*(1+effectiveDisplacement f g h)+
        uniformizedSecondDecay f g h upper)/(1+z^2) := by
  apply (le_div_iff₀ (by positivity)).mpr
  have h0 := uniformizedOffDiagonal_bound f g h z upper
  have h2 := uniformizedOffDiagonal_second_frequency_bound f g h z upper
  rw [sq_abs] at h2
  nlinarith

end
end GaloisForLFunctions.HTGeometry.FokasLenells
