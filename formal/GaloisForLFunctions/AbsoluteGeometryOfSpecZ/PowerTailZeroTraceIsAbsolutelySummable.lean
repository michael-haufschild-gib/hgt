import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailZetaMultiplierBound
import GaloisForLFunctions.ZeroConfigurationGeometry.TheRightSubstripsHaveSubunitMoments

/-!
# Absolute summability of the contact zero amplitudes

A sufficiently narrow band below the power boundary has a density
deficit stronger than the growth of its zeta multiplier. Thus the actual
contact residues are absolutely summable, with all multiplicities.
-/

noncomputable section

open Complex Filter Topology
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
  have hgap : 0 < 1 - p := sub_pos.mpr hp1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
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
      have hh := norm_zeta_le_ordinate_power_in_closed_strip hp0 hp1
        (s := (q.1 : ℂ) + (a : ℂ))
        (by simp only [Complex.add_re, Complex.ofReal_re]; linarith only [hq.1])
        (by simp only [Complex.add_re, Complex.ofReal_re]; linarith only [hq.2])
        (by simpa only [Complex.add_im, Complex.ofReal_im, add_zero, xiCopyOrdinate] using hγ1)
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero, xiCopyOrdinate] using hh
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

/-- Logarithmic phase of a contact residue, normalized at the power boundary. -/
def powerTailRightZeroWave (a σ u : ℝ) (q : XiZeroCopy) : ℂ :=
  powerTailRightZeroAmplitude a σ q *
    Complex.exp (((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) * (u : ℂ))

/-- Nonnegative logarithmic lags are dominated by the residue amplitudes. -/
theorem norm_powerTailRightZeroWave_le {a σ u : ℝ} (hu : 0 ≤ u)
    (q : XiZeroCopy) :
    ‖powerTailRightZeroWave a σ u q‖ ≤ ‖powerTailRightZeroAmplitude a σ q‖ := by
  classical
  by_cases hq : σ ≤ (q.1 : ℂ).re ∧ (q.1 : ℂ).re ≤ 1 - a
  · rw [powerTailRightZeroWave, norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq.2) hu
  · simp only [powerTailRightZeroWave, powerTailRightZeroAmplitude, hq,
      if_false, zero_mul, norm_zero, le_refl]

/-- Every mode away from the boundary vanishes as the logarithmic lag grows. -/
theorem tendsto_powerTailRightZeroWave_zero {a σ : ℝ}
    (q : XiZeroCopy) (hne : (q.1 : ℂ).re ≠ 1 - a) :
    Tendsto (fun u => powerTailRightZeroWave a σ u q) atTop (𝓝 0) := by
  classical
  by_cases hq : σ ≤ (q.1 : ℂ).re ∧ (q.1 : ℂ).re ≤ 1 - a
  · have hp : 0 < (1 - a) - (q.1 : ℂ).re :=
      sub_pos.mpr (lt_of_le_of_ne hq.2 hne)
    have hl := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hp tendsto_id))
    have he : Tendsto (fun u : ℝ =>
        Complex.exp (((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) * (u : ℂ))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine hl.congr fun u => ?_
      change Real.exp (-(((1 - a) - (q.1 : ℂ).re) * u)) = _
      rw [Complex.norm_exp]
      apply congrArg Real.exp
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      ring
    simpa only [powerTailRightZeroWave, mul_zero] using
      he.const_mul (powerTailRightZeroAmplitude a σ q)
  · simpa only [powerTailRightZeroWave, powerTailRightZeroAmplitude, hq,
      if_false, zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))

/-- An absolutely summable contact trace retains exactly its boundary
layer. No common gap below that layer is needed. -/
theorem tendsto_powerTailRightZeroTrace_sub_boundary {a σ : ℝ}
    (hs : Summable (fun q => ‖powerTailRightZeroAmplitude a σ q‖)) :
    Tendsto (fun u : ℝ =>
      (∑' q : XiZeroCopy, powerTailRightZeroWave a σ u q) -
        ∑' q : XiZeroCopy, if (q.1 : ℂ).re = 1 - a then powerTailRightZeroWave a σ u q else 0)
      atTop (𝓝 0) := by
  classical
  let boundary := fun (u : ℝ) (q : XiZeroCopy) =>
    if (q.1 : ℂ).re = 1 - a then powerTailRightZeroWave a σ u q else 0
  have hterm (u : ℝ) (hu : 0 ≤ u) : Summable (powerTailRightZeroWave a σ u) :=
    Summable.of_norm_bounded hs (norm_powerTailRightZeroWave_le hu)
  have hboundary (u : ℝ) (hu : 0 ≤ u) : Summable (boundary u) := by
    refine Summable.of_norm_bounded hs fun q => ?_
    dsimp only [boundary]
    split_ifs
    · exact norm_powerTailRightZeroWave_le hu q
    · simpa only [norm_zero] using norm_nonneg (powerTailRightZeroAmplitude a σ q)
  have hpt (q : XiZeroCopy) :
      Tendsto (fun u : ℝ => powerTailRightZeroWave a σ u q - boundary u q) atTop (𝓝 0) := by
    by_cases hq : (q.1 : ℂ).re = 1 - a
    · simpa only [boundary, hq, if_true, sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    · simpa only [boundary, hq, if_false, sub_zero] using
        tendsto_powerTailRightZeroWave_zero q hq
  have hdom : ∀ᶠ u : ℝ in atTop, ∀ q : XiZeroCopy,
      ‖powerTailRightZeroWave a σ u q - boundary u q‖ ≤
        ‖powerTailRightZeroAmplitude a σ q‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu q
    dsimp only [boundary]
    split_ifs
    · simpa only [sub_self, norm_zero] using norm_nonneg (powerTailRightZeroAmplitude a σ q)
    · simpa only [sub_zero] using norm_powerTailRightZeroWave_le hu q
  have hh := tendsto_tsum_of_dominated_convergence hs hpt hdom
  simp only [tsum_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  exact (hterm u hu).tsum_sub (hboundary u hu)

/-- Every subcritical power parameter has a right band with summable
contact amplitudes and a vanishing contribution below the boundary. -/
theorem exists_powerTailRightZeroTrace_boundary_decomposition
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 - a ∧
      Summable (fun q => ‖powerTailRightZeroAmplitude a σ q‖) ∧
      Tendsto (fun u : ℝ =>
        (∑' q : XiZeroCopy, powerTailRightZeroWave a σ u q) -
          ∑' q : XiZeroCopy, if (q.1 : ℂ).re = 1 - a then powerTailRightZeroWave a σ u q else 0)
        atTop (𝓝 0) := by
  obtain ⟨σ, hσ, hσβ, hs⟩ := exists_summable_powerTailRightZeroAmplitude ha ha2
  exact ⟨σ, hσ, hσβ, hs, tendsto_powerTailRightZeroTrace_sub_boundary hs⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
