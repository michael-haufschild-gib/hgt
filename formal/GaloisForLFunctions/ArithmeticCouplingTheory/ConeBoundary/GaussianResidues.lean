import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.ActualResidueGeometry

/-!
# Gaussian damping of the actual spline residues

A fixed positive Gaussian multiplier preserves nonzero off-line residues
and gives quadratic exponential decay in the ordinate. Absolute convergence
survives positive clock shifts and radial removal of an allowed growth rate.
-/

open Complex
open Zeta23
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
open ConeCoupling

/-- Gaussian damping of the actual centered zero. -/
def gaussianDamping (τ : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  Complex.exp ((τ:ℂ)*(zeroOffset ρ)^2)

def gaussianSplineWeight (τ : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  gaussianDamping τ ρ*wt ρ

def gaussianMixedResidue (τ a b : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  gaussianDamping τ ρ*mixedResidue a b ρ

lemma norm_gaussianDamping (τ : ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖gaussianDamping τ ρ‖ =
      Real.exp (τ*((zeroOffset ρ).re^2-(ρ:ℂ).im^2)) := by
  rw [gaussianDamping,Complex.norm_exp,Complex.re_ofReal_mul,pow_two,Complex.mul_re,
    zeroOffset_im]
  congr 1
  ring

lemma norm_gaussianDamping_le {τ : ℝ} (hτ : 0 ≤ τ) (ρ : zetaZeroConfig.carrier) :
    ‖gaussianDamping τ ρ‖ ≤ Real.exp (τ/4)*Real.exp (-τ*(ρ:ℂ).im^2) := by
  have hs := zetaZeroConfig.strip ρ.val ρ.property
  have hδ : (zeroOffset ρ).re^2 ≤ 1/4 := by
    rw [zeroOffset_re]
    nlinarith only [hs.1,hs.2,mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  rw [norm_gaussianDamping,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hδ hτ]

lemma norm_gaussianDamping_le_constant {τ : ℝ} (hτ : 0 ≤ τ) (ρ : zetaZeroConfig.carrier) :
    ‖gaussianDamping τ ρ‖ ≤ Real.exp (τ/4) := by
  have he : Real.exp (-τ*(ρ:ℂ).im^2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hτ (sq_nonneg (ρ:ℂ).im)])
  exact (norm_gaussianDamping_le hτ ρ).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (Real.exp_pos (τ/4)).le)

lemma summable_norm_gaussianSplineWeight {τ : ℝ} (hτ : 0 ≤ τ) :
    Summable fun ρ : zetaZeroConfig.carrier => ‖gaussianSplineWeight τ ρ‖ := by
  refine (summable_norm_wt.mul_left (Real.exp (τ/4))).of_nonneg_of_le
    (fun ρ => norm_nonneg _) fun ρ => ?_
  rw [gaussianSplineWeight,norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_gaussianDamping_le_constant hτ ρ) (norm_nonneg _)

lemma summable_norm_gaussianMixedResidue {τ a b : ℝ}
    (hτ : 0 ≤ τ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable fun ρ : zetaZeroConfig.carrier => ‖gaussianMixedResidue τ a b ρ‖ := by
  refine ((summable_norm_mixedResidue ha hb).mul_left (Real.exp (τ/4))).of_nonneg_of_le
    (fun ρ => norm_nonneg _) fun ρ => ?_
  rw [gaussianMixedResidue,norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_gaussianDamping_le_constant hτ ρ) (norm_nonneg _)

/-- A Gaussian turns the polynomially weighted actual residues into a quadratic exponential tail. -/
lemma gaussianMixedResidue_tail_pointwise {τ T a b : ℝ} (hτ : 0 ≤ τ) (hT : 0 ≤ T)
    (ρ : zetaZeroConfig.carrier) (hγ : T ≤ |(ρ:ℂ).im|) :
    ‖gaussianMixedResidue τ a b ρ‖ ≤
      Real.exp (τ/4-τ*T^2)*‖mixedResidue a b ρ‖ := by
  have hsq : T^2 ≤ (ρ:ℂ).im^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hT hγ 2
  have he : Real.exp (-τ*(ρ:ℂ).im^2) ≤ Real.exp (-τ*T^2) :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hsq hτ])
  have hd := (norm_gaussianDamping_le hτ ρ).trans
    (mul_le_mul_of_nonneg_left he (Real.exp_pos (τ/4)).le)
  rw [← Real.exp_add] at hd
  rw [gaussianMixedResidue,norm_mul]
  simpa only [sub_eq_add_neg,neg_mul] using mul_le_mul_of_nonneg_right hd (norm_nonneg (mixedResidue a b ρ))

/-- A right-of-line zero retains a nonzero mixed residue after Gaussian damping. -/
lemma gaussianMixedResidue_ne_zero (τ : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ρ : zetaZeroConfig.carrier) (hρ : 0 < (zeroOffset ρ).re) :
    gaussianMixedResidue τ a b ρ ≠ 0 := by
  have hw : wt ρ ≠ 0 := ArithmeticKreinLangerTheory.Wsummand_ne_zero_of_rightZero
    ⟨ρ.property,by rw [zeroOffset_re] at hρ; linarith only [hρ]⟩
  have hclock (c : ℝ) (hc : 0 < c) : mult c ρ ≠ 1 := by
    have hn : 1 < ‖mult c ρ‖ := by
      rw [norm_mult]
      exact Real.one_lt_exp_iff.mpr (mul_pos hc (by simpa only [zeroOffset_re] using hρ))
    intro he
    rw [he,norm_one] at hn
    exact (lt_irrefl 1) hn
  exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr (hclock a ha)) (sub_ne_zero.mpr (hclock b hb))) hw)

lemma summable_gaussianMixedResidue_moment {τ : ℝ} (hτ : 0 ≤ τ)
    (a b : ℝ) (m n : ℕ) : Summable fun ρ : zetaZeroConfig.carrier =>
      gaussianMixedResidue τ a b ρ*mult a ρ^m*mult b ρ^n := by
  have hs := (summable_mixedResidue_moment a b m n).norm.mul_left (Real.exp (τ/4))
  apply Summable.of_norm
  refine hs.of_nonneg_of_le (fun ρ => norm_nonneg _) fun ρ => ?_
  have he : gaussianMixedResidue τ a b ρ*mult a ρ^m*mult b ρ^n =
      gaussianDamping τ ρ*(mixedResidue a b ρ*mult a ρ^m*mult b ρ^n) := by
    unfold gaussianMixedResidue
    ring
  rw [he,norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_gaussianDamping_le_constant hτ ρ) (norm_nonneg _)

/-- Removing an allowed exponential growth rate translates the two clocks radially. -/
def shiftedClock (σ a : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  Complex.exp ((a:ℂ)*(zeroOffset ρ-(σ:ℂ)))

lemma norm_shiftedClock (σ a : ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖shiftedClock σ a ρ‖ = Real.exp (a*((zeroOffset ρ).re-σ)) := by
  rw [shiftedClock,Complex.norm_exp,Complex.re_ofReal_mul,Complex.sub_re,Complex.ofReal_re]

lemma norm_shiftedClock_le {σ a : ℝ} (hσ : 0 ≤ σ) (ha : 0 ≤ a)
    (ρ : zetaZeroConfig.carrier) : ‖shiftedClock σ a ρ‖ ≤ Real.exp (a/2) := by
  rw [norm_shiftedClock]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (zeroOffset_re_le_half ρ) ha
  nlinarith only [hh,mul_nonneg ha hσ]

lemma summable_shifted_gaussian_moment {τ σ a b : ℝ}
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m n : ℕ) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      gaussianMixedResidue τ a b ρ*shiftedClock σ a ρ^m*shiftedClock σ b ρ^n := by
  apply Summable.of_norm
  have hs := (summable_norm_gaussianMixedResidue hτ ha hb).mul_right
    ((Real.exp (a/2))^m*(Real.exp (b/2))^n)
  refine hs.of_nonneg_of_le (fun ρ => norm_nonneg _) fun ρ => ?_
  rw [norm_mul,norm_mul,norm_pow,norm_pow]
  have hA := pow_le_pow_left₀ (norm_nonneg _) (norm_shiftedClock_le hσ ha ρ) m
  have hB := pow_le_pow_left₀ (norm_nonneg _) (norm_shiftedClock_le hσ hb ρ) n
  have hh := mul_le_mul hA hB (pow_nonneg (norm_nonneg _) n)
    (pow_nonneg (Real.exp_pos _).le m)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (norm_nonneg (gaussianMixedResidue τ a b ρ))

#print axioms summable_norm_gaussianSplineWeight
#print axioms gaussianMixedResidue_ne_zero
#print axioms summable_gaussianMixedResidue_moment
#print axioms gaussianMixedResidue_tail_pointwise
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
