import GaloisForLFunctions.HTGeometry.FiniteTorusPhaseEnsembleLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.Correlation

/-! # Signed macroscopic detunings on a window from a prescribed origin -/

open Finset Complex MeasureTheory
open scoped ComplexConjugate symmDiff Interval
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The character of a real phase in radians. -/
def wave (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)

private theorem wave_add (x y : ℝ) : wave (x+y)=wave x*wave y := by
  simp only [wave,Complex.ofReal_add,add_mul,Complex.exp_add]

private theorem wave_neg (x : ℝ) : conj (wave x)=wave (-x) := by
  simp [wave,←Complex.exp_conj]

/-- Average of one signed detuning on the affine time window. Its midpoint
phase carries the origin dependence, even for the zero detuning. -/
theorem mean_wave (a w d : ℝ) :
    (∫ x in (0:ℝ)..1, wave ((a+w*x)*d))=wave ((a+w/2)*d)*(Real.sinc (w*d/2):ℂ) := by
  have he (x : ℝ) : wave ((a+w*x)*d)=wave ((a+w/2)*d)*wave ((w*d/2)*(2*x-1)) := by
    rw [←wave_add]
    congr 1
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  exact congrArg (wave ((a+w/2)*d)*·) (interval_exp_centered_eq_sinc _)

/-- The signed finite window sum on index pairs surviving the support cutoff. -/
def windowSum (F : Finset (Finset I)) (m : Finset I → ℂ) (E : I → ℝ) (r : ℕ) (a w : ℝ) : ℝ :=
  ∑ S ∈ F, ∑ T ∈ F.filter (fun T => r<(S ∆ T).card),
    let d := (∑ i ∈ T, E i)-(∑ i ∈ S, E i)
    (m S*conj (m T)*wave ((a+w/2)*d)).re*Real.sinc (w*d/2)

private theorem term_mean (c : ℂ) (a w d : ℝ) :
    (∫ x in (0:ℝ)..1, (c*wave ((a+w*x)*d)).re)=
      (c*wave ((a+w/2)*d)).re*Real.sinc (w*d/2) := by
  have hi : IntervalIntegrable (fun x : ℝ => c*wave ((a+w*x)*d)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold wave
    fun_prop
  change (∫ x in (0:ℝ)..1, RCLike.re (c*wave ((a+w*x)*d)))=_
  rw [intervalIntegral.intervalIntegral_re hi,intervalIntegral.integral_const_mul,mean_wave,←mul_assoc]
  simp

/-- The signed pair sum is the exact uniform-time average of the
correlation, with no contribution from any discarded support. -/
theorem window_mean (F : Finset (Finset I)) (m : Finset I → ℂ) (E : I → ℝ) (r : ℕ) (a w : ℝ) :
    (∫ x in (0:ℝ)..1, farCorrelation F
      (fun S => m S*wave (-(a+w*x)*(∑ i ∈ S, E i))) r)=windowSum F m E r a w := by
  let Δ (S T : Finset I) := (∑ i ∈ T, E i)-(∑ i ∈ S, E i)
  let b (S T : Finset I) := m S*conj (m T)
  have he (x : ℝ) (S T : Finset I) :
      (m S*wave (-(a+w*x)*(∑ i ∈ S, E i)))*conj (m T*wave (-(a+w*x)*(∑ i ∈ T, E i))) =
        b S T*wave ((a+w*x)*Δ S T) := by
    rw [map_mul,wave_neg]
    dsimp only [b,Δ]
    rw [show (a+w*x)*((∑ i ∈ T, E i)-(∑ i ∈ S, E i))=
      -(a+w*x)*(∑ i ∈ S, E i)+ -(-(a+w*x)*(∑ i ∈ T, E i)) by ring,wave_add]
    ring
  have hi (S T : Finset I) : IntervalIntegrable
      (fun x => (b S T*wave ((a+w*x)*Δ S T)).re) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold wave
    fun_prop
  simp only [farCorrelation,he,windowSum]
  rw [intervalIntegral.integral_finsetSum (fun S _ => show IntervalIntegrable
    (fun x => ∑ T ∈ F.filter (fun T => r<(S ∆ T).card), (b S T*wave ((a+w*x)*Δ S T)).re)
      volume 0 1 by apply Continuous.intervalIntegrable; unfold wave; fun_prop)]
  apply sum_congr rfl
  intro S _
  rw [intervalIntegral.integral_finsetSum (fun T _ => hi S T)]
  exact sum_congr rfl fun T _ => term_mean _ _ _ _

#print axioms window_mean
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
