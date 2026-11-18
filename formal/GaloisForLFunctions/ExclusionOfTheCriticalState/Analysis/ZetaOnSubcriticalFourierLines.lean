import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RHTower.HardyZ
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Zeta on subcritical Fourier lines

On a fixed line of real part σ between zero and one half, convexity costs
strictly less than one power of frequency in a squared Fourier integral.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Squared zeta in cycles-per-unit coordinates on a fixed vertical line. -/
theorem squared_zeta_on_positive_line {σ : ℝ} (hσ : 0 < σ) (hhalf : σ ≤ 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ,
      ‖riemannZeta ((σ:ℂ) + ((2*Real.pi*ξ:ℝ):ℂ)*I)‖^2 ≤
        C*(1+|ξ|^(1-σ/2)) := by
  let z := fun t : ℝ => (σ:ℂ)+(t:ℂ)*I
  let r := 1-σ/2
  have hr : 0 ≤ r := by dsimp only [r]; linarith only [hhalf]
  have hc : Continuous (fun t => riemannZeta (z t)) := by
    apply continuous_iff_continuousAt.2
    intro t
    have hn : z t ≠ 1 := fun he => by
      have h := congrArg Complex.re he
      simp [z] at h
      linarith only [h,hhalf]
    exact (differentiableAt_riemannZeta hn).continuousAt.comp (by dsimp only [z]; fun_prop)
  obtain ⟨B,hB⟩ := (isCompact_Icc (α := ℝ) (a := -8) (b := 8)).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨A,hA,ha⟩ := _root_.RHTower.exists_norm_riemannZeta_le_convexity
    (η := σ/2) (by positivity) (by linarith only [hhalf])
  have hbound (t : ℝ) (ht : 8 ≤ t) : ‖riemannZeta (z t)‖^2 ≤ A^2*t^r := by
    have h := ha σ t (by linarith only [hσ]) (by linarith only [hhalf,hσ]) ht
    rw [show (1+σ/2-σ)/2 = r/2 by dsimp only [r]; ring] at h
    have hp := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow,← Real.rpow_mul_natCast (by linarith only [ht] : 0 ≤ t),
      show r/2*((2:ℕ):ℝ) = r by norm_num] at hp
    exact hp
  have hconj (t : ℝ) : ‖riemannZeta (z (-t))‖ = ‖riemannZeta (z t)‖ := by
    have he : z (-t) = conj (z t) := by simp [z]
    rw [he,_root_.RHTower.riemannZeta_conj_of_re_pos (by simpa [z] using hσ)
      (fun he => by have h := congrArg Complex.re he; simp [z] at h; linarith only [h,hhalf]),Complex.norm_conj]
  let D := A^2*(2*Real.pi)^r
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
  refine ⟨D+(max B 0)^2,add_nonneg hD (sq_nonneg _),fun ξ => ?_⟩
  let t := 2*Real.pi*ξ
  have ht : |t| = (2*Real.pi)*|ξ| := by rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
  have hξ : 0 ≤ |ξ|^r := Real.rpow_nonneg (abs_nonneg _) _
  change ‖riemannZeta (z t)‖^2 ≤ (D+(max B 0)^2)*(1+|ξ|^r)
  by_cases hbig : 8 ≤ |t|
  · have he : ‖riemannZeta (z t)‖ = ‖riemannZeta (z |t|)‖ := by
      rcases le_or_gt 0 t with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h,hconj]
    rw [he]
    apply (hbound |t| hbig).trans
    rw [ht,Real.mul_rpow (by positivity) (abs_nonneg _),← mul_assoc]
    change D*|ξ|^r ≤ _
    exact mul_le_mul (le_add_of_nonneg_right (sq_nonneg _)) (le_add_of_nonneg_left zero_le_one)
      hξ (add_nonneg hD (sq_nonneg _))
  · have hm := abs_le.1 (le_of_lt (lt_of_not_ge hbig))
    have h := pow_le_pow_left₀ (norm_nonneg _) ((hB t hm).trans (le_max_left B 0)) 2
    apply h.trans
    calc (max B 0)^2 ≤ D+(max B 0)^2 := le_add_of_nonneg_left hD
      _ ≤ _ := le_mul_of_one_le_right (add_nonneg hD (sq_nonneg _)) (le_add_of_nonneg_right hξ)

#print axioms squared_zeta_on_positive_line
end GaloisForLFunctions.ExclusionOfTheCriticalState
