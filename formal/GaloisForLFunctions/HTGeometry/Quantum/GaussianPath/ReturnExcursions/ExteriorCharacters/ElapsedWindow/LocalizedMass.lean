import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.ElapsedWindow.Kernel

/-! # Window mass forced by one interior interval of fits -/

open Finset Filter Set MeasureTheory
open scoped symmDiff Interval
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Squaring the character makes its contribution outside the observed
interval nonnegative. Removing all small differences then costs at most
one Hamming-ball contribution per subset on the entire window. -/
theorem localized_floor (F : Finset (Finset I)) (m : Finset I → ℂ) (hm : ∀ S∈F, ‖m S‖≤1)
    (E : I → ℝ) (r : ℕ) (a w l u b : ℝ) (hl : 0≤l) (hlu : l≤u) (hu : u≤1)
    (h : ∀ x∈Icc l u, b≤‖∑ S ∈ F, m S*wave (-(a+w*x)*(∑ i ∈ S, E i))‖^2) :
    (u-l)*b-(F.card:ℝ)*(2^r*(3/2)^Fintype.card I) ≤ windowSum F m E r a w := by
  let P (x : ℝ) (S : Finset I) := m S*wave (-(a+w*x)*(∑ i ∈ S, E i))
  let f (x : ℝ) := ‖∑ S ∈ F, P x S‖^2
  let C : ℝ := (F.card:ℝ)*(2^r*(3/2)^Fintype.card I)
  let g (x : ℝ) := farCorrelation F (P x) r
  have hf : Continuous f := by dsimp only [f,P,wave]; fun_prop
  have hg : Continuous g := by dsimp only [g,farCorrelation,P,wave]; fun_prop
  have hsub := intervalIntegral.integral_mono_interval hl hlu hu
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖∑ S ∈ F, P x S‖)) (hf.intervalIntegrable (μ:=volume) 0 1)
  have hobs := intervalIntegral.integral_mono_on hlu (intervalIntegrable_const (μ:=volume) (c:=b))
    (hf.intervalIntegrable (μ:=volume) l u) h
  have hbudget (x : ℝ) : f x≤g x+C := by
    apply sub_le_iff_le_add.mp
    apply far_correlation_floor
    intro S hS
    simpa only [P,wave,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one] using hm S hS
  have hall := intervalIntegral.integral_mono (show (0:ℝ)≤1 by norm_num) (hf.intervalIntegrable (μ:=volume) 0 1)
    ((hg.add continuous_const).intervalIntegrable (μ:=volume) 0 1) hbudget
  rw [intervalIntegral.integral_const,smul_eq_mul] at hobs
  change (∫ x in (0:ℝ)..1, f x)≤∫ x in (0:ℝ)..1, g x+C at hall
  rw [intervalIntegral.integral_add (hg.intervalIntegrable (μ:=volume) 0 1) intervalIntegrable_const,
    intervalIntegral.integral_const,sub_zero,one_smul] at hall
  change _≤(∫ x in (0:ℝ)..1, farCorrelation F (P x) r)+C at hall
  rw [show (∫ x in (0:ℝ)..1, farCorrelation F (P x) r)=windowSum F m E r a w from window_mean ..] at hall
  exact sub_le_iff_le_add.mpr (hobs.trans (hsub.trans hall))

#print axioms localized_floor
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
