import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheShortRatioEnergyOfLongMoebiusPolynomials

/-!
# Reading the zero width from short integer ratios

The triangular sum at length T^θ uses only integer ratios at logarithmic
distance less than 1/T. Its logarithm divided by 2θ log T recovers the
zero width when θ is taken large and then the height cutoff is taken
large for that θ. This quantifier order requires no fixed-θ limit.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
open Filter MeasureTheory Topology
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg)
noncomputable section

/-- A finite real-valued reading of the zero width. Adding one keeps its
logarithm nonnegative even when the whole band energy is small. -/
def shortRatioWidthReading (θ T : ℝ) : ℝ :=
  Real.log (1+shortRatioForm ⌊T^θ⌋₊ T)/(2*θ*Real.log T)

private theorem form_nonneg (N : ℕ) {T : ℝ} (ht : 0<T) : 0≤ shortRatioForm N T := by
  rw [shortRatioForm_eq_bandEnergy _ ht]
  exact integral_nonneg fun _ => sq_nonneg _

/-- Below the zero width, the form divided by any fixed height power
and the proposed length power tends to infinity at every sufficiently
large fixed length exponent. -/
theorem all_heights_exceed_short_ratio_slope {β : ℝ} (hβ : 0≤β) (hw : β<zetaZeroWidth)
    {K : ℝ} (hK : 0≤K) :
    ∀ᶠ θ : ℝ in atTop, Tendsto (fun T : ℝ => shortRatioForm ⌊T^θ⌋₊ T/T^(K+2*β*θ)) atTop atTop := by
  classical
  have hn : ¬∀ a : ℝ, 0<a → ∃ θ : ℝ, a≤θ ∧ ∃ C : ℝ, 0≤C ∧
      ∃ᶠ T : ℝ in atTop, bandEnergy ⌊T^θ⌋₊ T⁻¹≤C*T^(K+2*β*θ) :=
    fun hg => hw.not_ge ((shortRatioGrowth_iff_zero_width hβ).mp ⟨K,hK,hg⟩)
  obtain ⟨a,ha⟩ := not_forall.mp hn
  filter_upwards [eventually_ge_atTop a] with θ hθ
  apply tendsto_atTop.mpr
  intro b
  let C := max 0 b
  have hnf : ¬∃ᶠ T : ℝ in atTop, bandEnergy ⌊T^θ⌋₊ T⁻¹≤C*T^(K+2*β*θ) :=
    fun hf => ha (fun _ => ⟨θ,hθ,C,le_max_left _ _,hf⟩)
  have hev : ∀ᶠ T : ℝ in atTop, ¬bandEnergy ⌊T^θ⌋₊ T⁻¹≤C*T^(K+2*β*θ) := Classical.not_not.mp hnf
  filter_upwards [hev,eventually_gt_atTop (0 : ℝ)] with T hT ht
  change b ≤ shortRatioForm ⌊T^θ⌋₊ T/T^(K+2*β*θ)
  rw [shortRatioForm_eq_bandEnergy _ ht,le_div_iff₀ (Real.rpow_pos_of_pos ht _)]
  exact (mul_le_mul_of_nonneg_right (le_max_right 0 b) (Real.rpow_nonneg ht.le _)).trans
    (le_of_lt (lt_of_not_ge hT))

private theorem reading_upper {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ θ : ℝ in atTop, ∀ᶠ T : ℝ in atTop, shortRatioWidthReading θ T≤zetaZeroWidth+ε := by
  have hw := zetaZeroWidth_nonneg
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_ge_atTop (1/ε)] with θ hθ hs
  have hθε : 1≤θ*ε := (div_le_iff₀ hε).mp hs
  obtain ⟨C,_,hb⟩ := short_ratio_energy_at_polynomial_length hθ zero_lt_one
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_ge_atTop (1+C)] with T hT hC
  have ht := zero_lt_one.trans hT
  have hp : 1≤T^(1+2*zetaZeroWidth*θ) := Real.one_le_rpow hT.le (by positivity)
  have hform := form_nonneg ⌊T^θ⌋₊ ht
  have hpow : 1+shortRatioForm ⌊T^θ⌋₊ T≤T^(2+2*zetaZeroWidth*θ) := by
    rw [shortRatioForm_eq_bandEnergy _ ht]
    calc
      _ ≤ (1+C)*T^(1+2*zetaZeroWidth*θ) := by
        rw [add_mul,one_mul]
        exact add_le_add hp (hb T hT.le)
      _ ≤ T*T^(1+2*zetaZeroWidth*θ) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht.le _)
      _ = _ := by
        rw [show 2+2*zetaZeroWidth*θ=1+(1+2*zetaZeroWidth*θ) by ring,
          Real.rpow_add ht 1 (1+2*zetaZeroWidth*θ),Real.rpow_one]
  have hl := Real.log_le_log (by linarith only [hform] : 0<1+shortRatioForm ⌊T^θ⌋₊ T) hpow
  rw [Real.log_rpow ht] at hl
  apply (div_le_iff₀ (show 0<2*θ*Real.log T from mul_pos (by positivity) (Real.log_pos hT))).mpr
  calc
    _ ≤ (2+2*zetaZeroWidth*θ)*Real.log T := hl
    _ ≤ ((zetaZeroWidth+ε)*(2*θ))*Real.log T := mul_le_mul_of_nonneg_right
      (by nlinarith only [hθε]) (Real.log_pos hT).le
    _ = _ := by ring

private theorem reading_lower {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ θ : ℝ in atTop, ∀ᶠ T : ℝ in atTop, zetaZeroWidth-ε≤ shortRatioWidthReading θ T := by
  by_cases h : zetaZeroWidth≤ε
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact (sub_nonpos.mpr h).trans (div_nonneg
      (Real.log_nonneg (le_add_of_nonneg_right (form_nonneg _ (zero_lt_one.trans hT))))
      (mul_nonneg (by positivity) (Real.log_pos hT).le))
  · let β := zetaZeroWidth-ε
    have hβ : 0≤β := sub_nonneg.mpr (le_of_not_ge h)
    have hw : β<zetaZeroWidth := sub_lt_self _ hε
    filter_upwards [eventually_gt_atTop (0 : ℝ),all_heights_exceed_short_ratio_slope hβ hw (K:=0) le_rfl] with θ hθ hb
    filter_upwards [eventually_gt_atTop (1 : ℝ),hb.eventually_ge_atTop 1] with T hT hl
    have ht := zero_lt_one.trans hT
    change 1 ≤ shortRatioForm ⌊T^θ⌋₊ T/T^(0+2*β*θ) at hl
    rw [zero_add,le_div_iff₀ (Real.rpow_pos_of_pos ht _),one_mul] at hl
    have hh := Real.log_le_log (Real.rpow_pos_of_pos ht (2*β*θ))
      (hl.trans (le_add_of_nonneg_left zero_le_one))
    rw [Real.log_rpow ht] at hh
    apply (le_div_iff₀ (show 0<2*θ*Real.log T from mul_pos (by positivity) (Real.log_pos hT))).mpr
    calc
      _ = (2*β*θ)*Real.log T := by dsimp only [β]; ring
      _ ≤ _ := hh

/-- At all sufficiently large power lengths, every sufficiently large
height reads the zero width to the prescribed accuracy. The inner height
threshold may depend on the length exponent. -/
theorem shortRatioWidthReading_converges (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ θ : ℝ in atTop, ∀ᶠ T : ℝ in atTop, |shortRatioWidthReading θ T-zetaZeroWidth|<ε := by
  filter_upwards [reading_upper (half_pos hε),reading_lower (half_pos hε)] with θ hu hl
  filter_upwards [hu,hl] with T h₁ h₂
  exact abs_lt.mpr ⟨by linarith only [h₂,hε],by linarith only [h₁,hε]⟩

#print axioms all_heights_exceed_short_ratio_slope
#print axioms shortRatioWidthReading_converges
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
