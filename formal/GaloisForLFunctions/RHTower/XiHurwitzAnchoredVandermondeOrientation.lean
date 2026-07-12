import GaloisForLFunctions.RHTower.XiHurwitzConstraintOrientation

/-!
# One anchored Hurwitz Vandermonde reality chamber proves RH

The full positive Vandermonde chamber is stronger than necessary.  Fix one actual Xi zero on the
critical line.  Its Hurwitz monodromy character is real.  The two-node Vandermonde determinant
between an arbitrary Xi zero and this anchor is exactly the difference of their characters.
Consequently, mere reality of every anchored two-node separator forces every Xi character to be
real, hence every Xi zero to lie on the critical line.
-/

open Complex Set Function
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open HurwitzOrbit

/-- The two-node Vandermonde separator on the negative Hurwitz characters of two Xi zeros. -/
def xiHurwitzPairVandermondeDet (ρ τ : XiDivisorSupport) : ℂ :=
  (Matrix.vandermonde ![-xiHurwitzMonodromyCharacter ρ,
    -xiHurwitzMonodromyCharacter τ]).det

/-- The two-node separator is the oriented character difference. -/
theorem xiHurwitzPairVandermondeDet_eq_sub (ρ τ : XiDivisorSupport) :
    xiHurwitzPairVandermondeDet ρ τ =
      xiHurwitzMonodromyCharacter ρ - xiHurwitzMonodromyCharacter τ := by
  rw [xiHurwitzPairVandermondeDet, Matrix.det_fin_two]
  simp [Matrix.vandermonde_apply]
  ring

/-- Differential-freeness supplies a nonzero two-node separator for distinct Xi divisor points. -/
theorem xiHurwitzPairVandermondeDet_ne_zero_of_ne
    {ρ τ : XiDivisorSupport} (hne : ρ ≠ τ) :
    xiHurwitzPairVandermondeDet ρ τ ≠ 0 := by
  rw [xiHurwitzPairVandermondeDet_eq_sub]
  exact sub_ne_zero.mpr fun hchar => hne (xiHurwitzMonodromyCharacter_injective hchar)

/-- Reality chamber for every two-node Hurwitz separator relative to one fixed Xi-zero anchor. -/
def XiHurwitzAnchoredPairVandermondeReal (τ : XiDivisorSupport) : Prop :=
  ∀ ρ : XiDivisorSupport, (xiHurwitzPairVandermondeDet ρ τ).im = 0

/-- A critical-line anchor has real Hurwitz monodromy character. -/
theorem xiHurwitzMonodromyCharacter_im_eq_zero_of_re_eq_half
    {τ : XiDivisorSupport} (hτ : (τ : ℂ).re = 1 / 2) :
    (xiHurwitzMonodromyCharacter τ).im = 0 := by
  have hneg := (openCriticalStrip_monoScalar_negativeReal_iff
    (xi_divisor_support_re_mem_open_unit τ)).mpr hτ
  simpa only [xiHurwitzMonodromyCharacter] using hneg.1

/-- Under RH, all anchored pair separators are real. -/
theorem xiHurwitzAnchoredPairVandermondeReal_of_rh
    (hRH : RiemannHypothesis) (τ : XiDivisorSupport) :
    XiHurwitzAnchoredPairVandermondeReal τ := by
  intro ρ
  have hchamber := riemannHypothesis_iff_xiHurwitzNegativeCharacterChamber.mp hRH
  rw [xiHurwitzPairVandermondeDet_eq_sub, Complex.sub_im,
    (hchamber ρ).1, (hchamber τ).1, sub_zero]

/-- **Anchored two-node orientation criterion.**  Given one actual Xi zero on the critical line,
RH is equivalent to reality—not positivity—of every two-node Hurwitz Vandermonde separator from
that anchor. -/
theorem riemannHypothesis_iff_xiHurwitzAnchoredPairVandermondeReal
    (τ : XiDivisorSupport) (hτ : (τ : ℂ).re = 1 / 2) :
    RiemannHypothesis ↔ XiHurwitzAnchoredPairVandermondeReal τ := by
  constructor
  · intro hRH
    exact xiHurwitzAnchoredPairVandermondeReal_of_rh hRH τ
  · intro hreal
    apply riemannHypothesis_iff_xiHurwitzNegativeCharacterChamber.mpr
    intro ρ
    have hτim := xiHurwitzMonodromyCharacter_im_eq_zero_of_re_eq_half hτ
    have hdet := hreal ρ
    rw [xiHurwitzPairVandermondeDet_eq_sub, Complex.sub_im, hτim, sub_zero] at hdet
    have hmonoIm : (monoScalar (ρ : ℂ)).im = 0 := by
      simpa only [xiHurwitzMonodromyCharacter] using hdet
    have hρhalf : (ρ : ℂ).re = 1 / 2 := by
      apply (openCriticalStrip_monoScalar_conj_fixed_iff
        (xi_divisor_support_re_mem_open_unit ρ)).mp
      exact Complex.conj_eq_iff_im.mpr hmonoIm
    exact (openCriticalStrip_monoScalar_negativeReal_iff
      (xi_divisor_support_re_mem_open_unit ρ)).mpr hρhalf

/-- Source-facing implication with the critical-line anchor existentially packaged. -/
theorem riemannHypothesis_of_exists_xiHurwitzAnchor_pairVandermondeReal
    (h : ∃ τ : XiDivisorSupport,
      (τ : ℂ).re = 1 / 2 ∧ XiHurwitzAnchoredPairVandermondeReal τ) :
    RiemannHypothesis := by
  obtain ⟨τ, hτ, hreal⟩ := h
  exact (riemannHypothesis_iff_xiHurwitzAnchoredPairVandermondeReal τ hτ).mpr hreal

/-- Under RH, a height-ordered anchored pair separator lies in the positive real chamber. -/
theorem xiHurwitzPairVandermondeDet_pos_real_of_rh
    (hRH : RiemannHypothesis) {ρ τ : XiDivisorSupport}
    (hheight : (ρ : ℂ).im < (τ : ℂ).im) :
    ∃ d : ℝ, 0 < d ∧ xiHurwitzPairVandermondeDet ρ τ = (d : ℂ) := by
  let rρ : ℝ := xiHurwitzMonodromyRadius ρ
  let rτ : ℝ := xiHurwitzMonodromyRadius τ
  have hr : rρ < rτ := by
    dsimp only [rρ, rτ, xiHurwitzMonodromyRadius]
    rw [Real.exp_lt_exp]
    exact mul_lt_mul_of_pos_left hheight (mul_pos (by norm_num) Real.pi_pos)
  refine ⟨rτ - rρ, sub_pos.mpr hr, ?_⟩
  rw [xiHurwitzPairVandermondeDet_eq_sub,
    (riemannHypothesis_iff_xiHurwitzMonodromyCharacter_eq_neg_height.mp hRH) ρ,
    (riemannHypothesis_iff_xiHurwitzMonodromyCharacter_eq_neg_height.mp hRH) τ]
  dsimp only [rρ, rτ, xiHurwitzMonodromyRadius]
  push_cast
  ring

end

end RHTower
