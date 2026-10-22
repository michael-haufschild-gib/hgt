import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5RegularizedAction
/-! Smooth removal of the actual inverse-source/denominator-clock quotient at
zero. The denominator clock has a strictly positive smooth factor on all real
arguments. This identifies the actual quotient and its endpoint value; no
claim about its fourth jet or global monotonicity is made here. -/
namespace RHTower.ThetaCuspDefect
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
local notation "c" => thetaCuspLogCurvature
local notation "e" => completedCurvatureEven
local notation "Eb" => curvaturePrimitiveFactor
local notation "y" => completedFirstDenominator
local notation "k" => denominatorClockRate
local notation "psi" => denominatorClockProfile

private theorem y_factor (u t : ℝ) : y u t=t*(Eb u t+e u t) := by
  unfold completedFirstDenominator
  rw [completedDecayEvenPrimitive_factor u t]
  ring
private theorem y_smooth (u : ℝ) : ContDiff ℝ ∞ (y u) := by
  have he : y u=fun t => t*(Eb u t+e u t) := funext (y_factor u)
  rw [he]
  exact contDiff_id.mul ((curvaturePrimitiveFactor_smooth u).add (completedCurvatureEven_smooth u))

/-- Positive smooth factor of the actual denominator clock's simple zero. -/
def denominatorClockSmoothFactor (u t : ℝ) : ℝ :=
  k u*(Eb u t+e u t)*(∫ r in (0:ℝ)..1, Real.cosh (r*(k u*y u t)))

theorem denominatorClockSmoothFactor_smooth (u : ℝ) : ContDiff ℝ ∞ (denominatorClockSmoothFactor u) := by
  have hY := y_smooth u
  have hI : ContDiff ℝ ∞ (fun z : ℝ × ℝ => Real.cosh (z.2*(k u*y u z.1))) := by
    fun_prop
  have hA := contDiff_unitIntervalParameterIntegral hI
  exact (contDiff_const.mul ((curvaturePrimitiveFactor_smooth u).add
    (completedCurvatureEven_smooth u))).mul hA

theorem denominatorClockSmoothFactor_pos (u t : ℝ) : 0 < denominatorClockSmoothFactor u t := by
  unfold denominatorClockSmoothFactor
  apply mul_pos (mul_pos (denominatorClockRate_pos u)
    (add_pos (curvaturePrimitiveFactor_pos u t) (completedCurvatureEven_pos u t)))
  apply intervalIntegral.integral_pos (by norm_num)
    ((Real.continuous_cosh.comp (continuous_id.mul_const (k u*y u t))).continuousOn)
  · intro r _; exact (Real.cosh_pos _).le
  · exact ⟨0,⟨le_rfl,by norm_num⟩,Real.cosh_pos _⟩

theorem denominatorClockSmoothFactor_zero (u : ℝ) : denominatorClockSmoothFactor u 0=2*k u*c u := by
  simp [denominatorClockSmoothFactor,curvaturePrimitiveFactor_zero,completedCurvatureEven,
    completedFirstDenominator,completedDecayEvenPrimitive_zero]
  ring

theorem denominatorClockProfile_factor (u t : ℝ) : psi u t=t*denominatorClockSmoothFactor u t := by
  let z := k u*y u t
  have hd (r : ℝ) : HasDerivAt (fun s : ℝ => Real.sinh (s*z)) (z*Real.cosh (r*z)) r := by
    convert! ((hasDerivAt_id r).mul_const z).sinh using 1
    dsimp only [id_eq]
    ring
  have hc : Continuous (fun r : ℝ => z*Real.cosh (r*z)) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hc.intervalIntegrable 0 1)
  simp only [one_mul,zero_mul,Real.sinh_zero,sub_zero,intervalIntegral.integral_const_mul] at hh
  unfold denominatorClockProfile denominatorClockSmoothFactor
  rw [←hh]
  dsimp only [z]
  rw [y_factor u t]
  ring

/-- Smooth actual inverse-source/clock quotient, including its removable endpoint. -/
def intrinsicClockRegularRatio (u t : ℝ) : ℝ :=
  intrinsicInverseSmoothFactor u t/denominatorClockSmoothFactor u t

theorem intrinsicClockRegularRatio_smooth (u : ℝ) : ContDiff ℝ ∞ (intrinsicClockRegularRatio u) :=
  (intrinsicInverseSmoothFactor_smooth u).div (denominatorClockSmoothFactor_smooth u)
    (fun t => (denominatorClockSmoothFactor_pos u t).ne')

theorem intrinsicClockRegularRatio_eq {u t : ℝ} (ht : 0 < t) :
    intrinsicActionInverseSource u t/psi u t=intrinsicClockRegularRatio u t := by
  rw [intrinsicActionInverseSource_factor ht.le,denominatorClockProfile_factor u t]
  unfold intrinsicClockRegularRatio
  field_simp [ht.ne']

theorem intrinsicClockRegularRatio_zero (u : ℝ) :
    intrinsicClockRegularRatio u 0=3*(c u)^((8:ℝ)/5)/(k u*c u) := by
  rw [intrinsicClockRegularRatio,intrinsicInverseSmoothFactor_zero,denominatorClockSmoothFactor_zero]
  ring

end
end RHTower.ThetaCuspDefect
