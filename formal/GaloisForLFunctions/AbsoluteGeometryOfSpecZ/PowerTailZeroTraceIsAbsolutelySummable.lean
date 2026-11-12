import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailZetaMultiplierBound
import GaloisForLFunctions.ZeroConfigurationGeometry.TheRightSubstripsHaveSubunitMoments

/-!
# Absolute summability of the contact zero amplitudes

A sufficiently narrow band below the power boundary has a density
deficit stronger than the growth of its zeta multiplier. Thus the actual
contact residues are absolutely summable, with all multiplicities.
-/

noncomputable section

open Complex
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ZeroConfigurationGeometry

/-- Contact residue amplitude in the right band below the power boundary. -/
def powerTailRightZeroAmplitude (a σ : ℝ) (q : XiZeroCopy) : ℂ := by
  classical
  exact if σ ≤ (q.1 : ℂ).re ∧ (q.1 : ℂ).re ≤ 1 - a then
    -riemannZeta ((q.1 : ℂ) + (a : ℂ)) / ((q.1 : ℂ) - (a : ℂ)) else 0

/-- A density moment stronger than the zeta multiplier makes the complete
band of contact amplitudes absolutely summable. -/
theorem summable_norm_powerTailRightZeroAmplitude
    {a σ : ℝ} (hσ : 1 / 2 < σ) (hp0 : 0 < σ + a) (hp1 : σ + a < 1)
    (hp : 1 - min ((σ - 1 / 2) / 2) (1 / 4) / 3 < σ + a) :
    Summable (fun q => ‖powerTailRightZeroAmplitude a σ q‖) := by
  classical
  let p := σ + a
  let C := 22 + 1 / (1 - p)
  have hC : 0 ≤ C := by dsimp only [C, p]; positivity
  let w : XiZeroCopy → ℝ := fun q =>
    if σ ≤ (q.1 : ℂ).re then |xiCopyOrdinate q| ^ (-p) else 0
  have hw (q : XiZeroCopy) : 0 ≤ w q := by
    dsimp only [w]
    split_ifs <;> positivity
  have hws : Summable w := by
    change Summable ({q : XiZeroCopy | σ ≤ (q.1 : ℂ).re}.indicator
      (fun q => |xiCopyOrdinate q| ^ (-p)))
    exact summable_subtype_iff_indicator.mp (summable_rightSubstrip_ordinate_rpow hσ hp)
  apply (hws.mul_left C).of_nonneg_of_le (fun q => norm_nonneg _)
  intro q
  by_cases hq : σ ≤ (q.1 : ℂ).re ∧ (q.1 : ℂ).re ≤ 1 - a
  · have hγ : 0 < |xiCopyOrdinate q| := by
      have hh := four_lt_abs_xiCopyOrdinate q
      linarith only [hh]
    have hγ1 : 1 ≤ |xiCopyOrdinate q| := by
      have hh := four_lt_abs_xiCopyOrdinate q
      linarith only [hh]
    have hnum : ‖riemannZeta ((q.1 : ℂ) + (a : ℂ))‖ ≤
        C * |xiCopyOrdinate q| ^ (1 - p) := by
      apply norm_zeta_le_ordinate_power_in_closed_strip hp0 hp1
      · simp only [Complex.add_re, Complex.ofReal_re]
        linarith only [hq.1]
      · simp only [Complex.add_re, Complex.ofReal_re]
        linarith only [hq.2]
      · simpa only [Complex.add_im, Complex.ofReal_im, add_zero, xiCopyOrdinate] using hγ1
    have hden : |xiCopyOrdinate q| ≤ ‖(q.1 : ℂ) - (a : ℂ)‖ := by
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, xiCopyOrdinate] using
        Complex.abs_im_le_norm ((q.1 : ℂ) - (a : ℂ))
    have hmul : |xiCopyOrdinate q| ^ (-p) * |xiCopyOrdinate q| =
        |xiCopyOrdinate q| ^ (1 - p) := by
      have hh := (Real.rpow_add hγ (-p) 1).symm
      simpa only [Real.rpow_one, show -p + 1 = 1 - p by ring] using hh
    have he : (C * |xiCopyOrdinate q| ^ (1 - p)) / |xiCopyOrdinate q| =
        C * |xiCopyOrdinate q| ^ (-p) := by
      apply (div_eq_iff hγ.ne').mpr
      rw [mul_assoc, hmul]
    rw [powerTailRightZeroAmplitude, if_pos hq, norm_div, norm_neg,
      show w q = |xiCopyOrdinate q| ^ (-p) from if_pos hq.1]
    calc
      _ ≤ (C * |xiCopyOrdinate q| ^ (1 - p)) / ‖(q.1 : ℂ) - (a : ℂ)‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (C * |xiCopyOrdinate q| ^ (1 - p)) / |xiCopyOrdinate q| :=
        div_le_div_of_nonneg_left (by positivity) hγ hden
      _ = _ := he
  · rw [powerTailRightZeroAmplitude, if_neg hq, norm_zero]
    exact mul_nonneg hC (hw q)

/-- Every subcritical power boundary has a nonempty-width right band
whose actual contact residues are absolutely summable. -/
theorem exists_summable_powerTailRightZeroAmplitude
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 - a ∧
      Summable (fun q => ‖powerTailRightZeroAmplitude a σ q‖) := by
  let σ := 1 - a - (1 / 2 - a) / 100
  have hσ : 1 / 2 < σ := by dsimp only [σ]; linarith only [ha2]
  have hσβ : σ < 1 - a := by dsimp only [σ]; linarith only [ha2]
  refine ⟨σ, hσ, hσβ, summable_norm_powerTailRightZeroAmplitude hσ
    (by linarith only [hσ, ha]) (by linarith only [hσβ]) ?_⟩
  have hmin : min ((σ - 1 / 2) / 2) (1 / 4) = (σ - 1 / 2) / 2 :=
    min_eq_left (by dsimp only [σ]; linarith only [ha])
  rw [hmin]
  dsimp only [σ]
  linarith only [ha2]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
