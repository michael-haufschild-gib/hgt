import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Fourier.Dirichlet
import GaloisForLFunctions.HTGeometry.OscillatoryIntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Oscillatory tails of the literal Dirichlet kernel

On the positive half-period the reciprocal sine is positive and decreasing.
Its derivative mass cancels the upper boundary term in integration by parts,
giving a tail estimate with one inverse power of the Fourier frequency.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Period

private theorem sine_half_pos (x : Ioc (0 : ℝ) (1 / 2)) :
    0 < Real.sin (π * x.val) := by
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos x.property.1)
  nlinarith [x.property.2, Real.pi_pos]

private theorem cosine_half_nonneg (x : Ioc (0 : ℝ) (1 / 2)) :
    0 ≤ Real.cos (π * x.val) := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> nlinarith [x.property.1, x.property.2, Real.pi_pos]

/-- The exact kernel tail is controlled by its initial reciprocal-sine amplitude. -/
theorem norm_dirichlet_tail_le (N : ℕ) (a : Ioc (0 : ℝ) (1 / 2))
    (b : Icc a.val (1 / 2)) :
    ‖∫ t in a.val..b.val, dirichlet N t‖ ≤
      2 / (((2 * (N : ℝ) + 1) * π) * Real.sin (π * a.val)) := by
  let L : ℝ := (2 * (N : ℝ) + 1) * π
  let g : ℝ → ℝ := fun t => 1 / Real.sin (π * t)
  let g' : ℝ → ℝ := fun t => -(Real.cos (π * t) * π) / Real.sin (π * t) ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hab : a.val ≤ b.val := b.property.1
  have hhalf (x : ℝ) (hx : x ∈ uIcc a.val b.val) : x ∈ Ioc (0 : ℝ) (1 / 2) := by
    rw [uIcc_of_le hab] at hx
    exact ⟨a.property.1.trans_le hx.1, hx.2.trans b.property.2⟩
  have hs (x : ℝ) (hx : x ∈ uIcc a.val b.val) : 0 < Real.sin (π * x) :=
    sine_half_pos ⟨x, hhalf x hx⟩
  have hgderiv (x : ℝ) (hx : x ∈ uIcc a.val b.val) : HasDerivAt g (g' x) x := by
    dsimp [g, g']
    convert! (((hasDerivAt_id x).const_mul π).sin).inv (hs x hx).ne' using 1 <;>
      simp [one_div]
    rfl
  have hg'cont : ContinuousOn g' (uIcc a.val b.val) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact pow_ne_zero 2 (hs x hx).ne'
  have hg'I : IntervalIntegrable g' volume a.val b.val := hg'cont.intervalIntegrable
  have hg'C : IntervalIntegrable (fun x => (g' x : ℂ)) volume a.val b.val :=
    (Complex.continuous_ofReal.comp_continuousOn hg'cont).intervalIntegrable
  have hderivC (x : ℝ) (hx : x ∈ uIcc a.val b.val) :
      HasDerivAt (fun x => (g x : ℂ)) (g' x : ℂ) x := (hgderiv x hx).ofReal_comp
  have hgp (x : ℝ) (hx : x ∈ uIcc a.val b.val) : g' x ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (mul_nonneg (cosine_half_nonneg ⟨x, hhalf x hx⟩) Real.pi_pos.le)
    · exact sq_nonneg _
  have hmass : (∫ x in a.val..b.val, ‖(g' x : ℂ)‖) = g a.val - g b.val := by
    calc
      _ = ∫ x in a.val..b.val, -g' x := by
        apply intervalIntegral.integral_congr
        intro x hx
        change ‖(g' x : ℂ)‖ = -g' x
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (hgp x hx)]
      _ = -(g b.val - g a.val) := by
        rw [intervalIntegral.integral_neg,
          intervalIntegral.integral_eq_sub_of_hasDerivAt hgderiv hg'I]
      _ = _ := by ring
  have hga : ‖(g a.val : ℂ)‖ = g a.val := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    exact one_div_pos.mpr (sine_half_pos a)
  have hgb : ‖(g b.val : ℂ)‖ = g b.val := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    exact one_div_pos.mpr (sine_half_pos ⟨b.val, a.property.1.trans_le hab, b.property.2⟩)
  have hosc := norm_integral_oscillatory_le hL hab hderivC hg'C
  rw [hga, hgb, hmass] at hosc
  let f : ℝ → ℂ := fun t => (g t : ℂ) * Complex.exp ((t * L : ℝ) * Complex.I)
  have hfI : IntervalIntegrable f volume a.val b.val := by
    apply ContinuousOn.intervalIntegrable
    exact (Complex.continuous_ofReal.comp_continuousOn
      (HasDerivAt.continuousOn hgderiv)).mul (by fun_prop)
  have hkernel (t : ℝ) (ht : t ∈ uIcc a.val b.val) :
      dirichlet N t = ((f t).im : ℂ) := by
    have he : (f t).im = g t * Real.sin (t * L) := by
      simp [f, Complex.exp_im]
    rw [he]
    apply mul_right_cancel₀ (show (Real.sin (π * t) : ℂ) ≠ 0 by
      exact_mod_cast (hs t ht).ne')
    rw [dirichlet_sin, ← Complex.ofReal_mul]
    congr 1
    have hang : ang N t + π * t = t * L := by dsimp [ang, L]; ring
    rw [hang]
    dsimp [g]
    rw [mul_right_comm, div_mul_cancel₀ _ (hs t ht).ne', one_mul]
  calc
    ‖∫ t in a.val..b.val, dirichlet N t‖ = ‖((∫ t in a.val..b.val, f t).im : ℂ)‖ := by
      rw [intervalIntegral.integral_congr hkernel, intervalIntegral.integral_ofReal,
        show (∫ t in a.val..b.val, (f t).im) = (∫ t in a.val..b.val, f t).im from
          Complex.imCLM.intervalIntegral_comp_comm hfI]
    _ ≤ ‖∫ t in a.val..b.val, f t‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Complex.abs_im_le_norm _
    _ ≤ (g b.val + g a.val + (g a.val - g b.val)) / L := hosc
    _ = 2 / (((2 * (N : ℝ) + 1) * π) * Real.sin (π * a.val)) := by
      dsimp [g, L]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring

end GaloisForLFunctions.HTGeometry.FourierLLogL.Period
