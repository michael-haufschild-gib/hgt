import GaloisForLFunctions.CountingHolography.Sections.CriticalZerosSeparateThePrimeProfileFromFactorialKernels
import Mathlib.Analysis.Complex.Liouville

/-! # Derivatives at critical zeros of factorial comparisons

The Mellin error multiplied by the scale to the power s has a uniform
bound on each closed substrip. Cauchy's inequality then constrains the
value of the factorial frequency polynomial at every critical zero.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Complex MeasureTheory Filter Finset Set Topology Zeta23
open ArithmeticOrientationGeometry

private def residual {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (X : ℝ) (s : ℂ) :=
  Complex.exp ((Real.log X:ℝ)*s) *
    (mellin squarePrimeWeight s + NymanMellin.freqPoly c a s * riemannZeta s / s)

private theorem norm_scale {X : ℝ} (hX : 0 < X) (s : ℂ) :
    ‖Complex.exp ((Real.log X:ℝ)*s)‖ = X^s.re := by
  rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Real.rpow_def_of_pos hX]

private theorem residual_bound {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    {X B : ℝ} (hX : 0 < X)
    (hE : IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0))
    (hcap : ∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B)
    (hmass : (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X)
    {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    s.re*‖residual c a X s‖ ≤ B := by
  have h := mellin_difference_initial_interval_bound hs hs'.le (inv_pos.mpr hX)
    (mellinConvergent_squarePrimeWeight s) (NymanMellin.mellinConvergent_nymanCombination c a ha hs hs')
    hE hcap (by simpa only [div_eq_mul_inv] using hmass)
  rw [NymanMellin.mellin_nymanCombination c a ha hs hs',sub_neg_eq_add,Real.inv_rpow hX.le,
    ← div_eq_mul_inv] at h
  have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hX s.re)).mp ((le_div_iff₀ hs).mp h)
  rw [residual,norm_mul,norm_scale hX]
  linarith only [hh]

private theorem freq_differentiable {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) :
    Differentiable ℂ (NymanMellin.freqPoly c a) := by
  rw [NymanMellin.freqPoly_eq_expSum c a ha]
  fun_prop

/-- The normalized Mellin error has derivative bounded by sixteen times
the common height and mass budget, uniformly along the half line Re s = 1/2. -/
private theorem residual_deriv_bound {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (ha : ∀ j, 0 < a j) {X B : ℝ} (hX : 0 < X)
    (hE : IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0))
    (hcap : ∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B)
    (hmass : (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X)
    {ρ : ℂ} (hρ : ρ.re=1/2) : ‖deriv (residual c a X) ρ‖ ≤ 16*B := by
  let U := {s : ℂ | 0 < s.re ∧ s.re < 1}
  have hball {s : ℂ} (hs : s ∈ Metric.closedBall ρ (1/4:ℝ)) : 1/4 ≤ s.re ∧ s.re ≤ 3/4 := by
    have hd := (Complex.abs_re_le_norm (s-ρ)).trans (by simpa only [← dist_eq_norm] using hs)
    rw [Complex.sub_re,hρ,abs_le] at hd
    constructor <;> linarith only [hd.1,hd.2]
  have hu : Metric.closedBall ρ (1/4:ℝ) ⊆ U := fun s hs => by
    obtain ⟨h₁,h₂⟩ := hball hs
    exact ⟨by linarith only [h₁],by linarith only [h₂]⟩
  have hr : DifferentiableOn ℂ (residual c a X) U := by
    intro s hs
    have hs₀ : s ≠ 0 := fun e => hs.1.ne' (by rw [e]; rfl)
    have hs₁ : s ≠ 1 := fun e => hs.2.ne (by rw [e]; rfl)
    have he : Differentiable ℂ (fun t : ℂ => Complex.exp ((Real.log X:ℝ)*t)) := by fun_prop
    exact ((he s).mul ((differentiable_mellin_squarePrimeWeight s).add
      ((((freq_differentiable c a ha s).mul (differentiableAt_riemannZeta hs₁)).div
        (differentiableAt_id) hs₀)))).differentiableWithinAt
  have hb (s : ℂ) (hs : s ∈ Metric.sphere ρ (1/4:ℝ)) : ‖residual c a X s‖ ≤ 4*B := by
    have hd := Metric.sphere_subset_closedBall hs
    have h := residual_bound c a ha hX hE hcap hmass (hu hd).1 (hu hd).2
    linarith only [h,mul_le_mul_of_nonneg_right (hball hd).1 (norm_nonneg (residual c a X s))]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1/4)
    (hr.diffContOnCl_ball hu) hb
  linarith only [h]

/-- A critical zero fixes the first-order interpolation target of the
factorial frequency polynomial, including the derivative of zeta. -/
theorem factorial_frequency_at_critical_zero {ρ : ℂ} (hζ : riemannZeta ρ=0) (hρ : ρ.re=1/2)
    {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    {X B : ℝ} (hX : 0 < X)
    (hE : IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0))
    (hcap : ∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B)
    (hmass : (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X) :
    X^(1/2:ℝ)*‖(Real.log X:ℂ)*mellin squarePrimeWeight ρ + deriv (mellin squarePrimeWeight) ρ +
      NymanMellin.freqPoly c a ρ * deriv riemannZeta ρ / ρ‖ ≤ 16*B := by
  have h₀ : ρ ≠ 0 := by intro e; rw [e,Complex.zero_re] at hρ; norm_num at hρ
  have h₁ : ρ ≠ 1 := by intro e; rw [e,Complex.one_re] at hρ; norm_num at hρ
  have hd := (((hasDerivAt_id ρ).const_mul ((Real.log X:ℝ):ℂ)).cexp).mul
    ((differentiable_mellin_squarePrimeWeight ρ).hasDerivAt.add
      ((((freq_differentiable c a ha ρ).hasDerivAt.mul (differentiableAt_riemannZeta h₁).hasDerivAt).div
        (hasDerivAt_id ρ) h₀))
  change HasDerivAt (residual c a X) _ ρ at hd
  have he : deriv (residual c a X) ρ = Complex.exp ((Real.log X:ℝ)*ρ) *
      ((Real.log X:ℂ)*mellin squarePrimeWeight ρ+deriv (mellin squarePrimeWeight) ρ+
        NymanMellin.freqPoly c a ρ*deriv riemannZeta ρ/ρ) := by
    rw [hd.deriv]
    simp only [id_eq,hζ,mul_zero,zero_div,add_zero,zero_add,sub_zero,zero_mul,mul_one]
    field_simp
    ring
  have h := residual_deriv_bound c a ha hX hE hcap hmass hρ
  rwa [he,norm_mul,norm_scale hX,hρ] at h

#print axioms factorial_frequency_at_critical_zero

end GaloisForLFunctions.CountingHolography.Sections
