import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.LineClosure
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.OccupationGaps

/-! # Intermediate readings of physical line omissions

An arc joins any two nonzero directions inside the heat range while its
interior remains outside. A reciprocal tail multiplied by a scalar that
vanishes exactly at the endpoints makes the entire interior admissible.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def omissionArc (u w h : H) (t : ℝ) : H :=
  ((1-t:ℝ):ℂ) • u+(t:ℂ) • w+((t*(1-t):ℝ):ℂ) • h

theorem omissionArc_zero (u w h : H) : omissionArc u w h 0 = u := by simp [omissionArc]
theorem omissionArc_one (u w h : H) : omissionArc u w h 1 = w := by simp [omissionArc]

theorem continuous_omissionArc (u w h : H) : Continuous (omissionArc u w h) := by
  have h₁ : Continuous (fun t : ℝ => ((1-t:ℝ):ℂ)) := Complex.continuous_ofReal.comp (continuous_const.sub (continuous_id : Continuous (id : ℝ → ℝ)))
  have h₂ : Continuous (fun t : ℝ => ((t*(1-t):ℝ):ℂ)) := Complex.continuous_ofReal.comp (continuous_id.mul (continuous_const.sub (continuous_id : Continuous (id : ℝ → ℝ))))
  exact ((h₁.smul continuous_const).add (Complex.continuous_ofReal.smul continuous_const)).add (h₂.smul continuous_const)

/-- The interior of the arc is disjoint from a given subspace containing both endpoints. -/
theorem omissionArc_notMem (R : Submodule ℂ H) {u w h : H} (hu : u ∈ R) (hw : w ∈ R)
    (hh : h ∉ R) {t : ℝ} (ht : t ∈ Ioo 0 1) : omissionArc u w h t ∉ R := by
  intro hm
  have ha := R.add_mem (R.smul_mem ((1-t:ℝ):ℂ) hu) (R.smul_mem (t:ℂ) hw)
  exact hh ((R.smul_mem_iff (Complex.ofReal_ne_zero.mpr (mul_pos ht.1 (sub_pos.mpr ht.2)).ne')).mp
    ((R.add_mem_iff_right ha).mp hm))

/-- Every strict intermediate reading of the endpoints is attained by an interior wave. -/
theorem omissionArc_intermediate (R : Submodule ℂ H) {u w h : H} (hu : u ∈ R) (hw : w ∈ R)
    (hh : h ∉ R) (hu₀ : u ≠ 0) (hw₀ : w ≠ 0) (F : H → ℝ)
    (hc : ∀ v ≠ 0, ContinuousAt F v) {y : ℝ} (hy : y ∈ Ioo (F u) (F w)) :
    ∃ t ∈ Ioo (0:ℝ) 1, F (omissionArc u w h t) = y := by
  have hn {t : ℝ} (ht : t ∈ Icc 0 1) : omissionArc u w h t ≠ 0 := by
    rcases ht.1.eq_or_lt with h0 | h0
    · simpa only [← h0,omissionArc_zero] using hu₀
    rcases ht.2.eq_or_lt with h1 | h1
    · simpa only [h1,omissionArc_one] using hw₀
    exact fun hz => omissionArc_notMem R hu hw hh ⟨h0,h1⟩ (hz ▸ R.zero_mem)
  have hf : ContinuousOn (fun t => F (omissionArc u w h t)) (Icc (0:ℝ) 1) := fun t ht =>
    ((hc _ (hn ht)).comp (continuous_omissionArc u w h).continuousAt).continuousWithinAt
  apply intermediate_value_Ioo (show (0:ℝ) ≤ 1 by norm_num) hf
  simpa only [omissionArc_zero,omissionArc_one] using hy

/-- An occupied basis state with its physical shell label. -/
def modeWave (n : ℕ+) : Gas := lp.single 2 n (1:ℂ)

theorem modeWave_norm (n : ℕ+) : ‖modeWave n‖ = 1 := by simp [modeWave,lp.norm_single]

theorem heat_modeWave (n : ℕ+) :
    criticalOperator (modeWave n) = (attenuation n:ℂ) • modeWave n :=
  HTGeometry.LpDiagonal.lpDiag_single _ _ _ _ _

theorem modeWave_mem_range (n : ℕ+) : modeWave n ∈ LinearMap.range criticalOperator.toLinearMap := by
  refine ⟨(attenuation n:ℂ)⁻¹ • modeWave n,?_⟩
  change criticalOperator (_ • modeWave n) = _
  rw [map_smul,heat_modeWave,smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (attenuation_pos n).ne'),one_smul]

theorem lineLoss_modeWave (n : ℕ+) : lineLoss (modeWave n) = (attenuation n^2)^2 := by
  have h : ‖criticalOperator (modeWave n)‖ = attenuation n := by
    rw [heat_modeWave,norm_smul,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos n).le,modeWave_norm,mul_one]
  have h₂ : ‖squareHeat.val (modeWave n)‖ = attenuation n^2 := by
    change ‖criticalOperator (criticalOperator (modeWave n))‖ = _
    rw [heat_modeWave,map_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos n).le,h,pow_two]
  rw [lineLoss,h₂,h,modeWave_norm]
  ring

/-- Baseline and excited shell losses straddle every reading in the open unit interval. -/
theorem modeWave_straddle (y : Ioo (0:ℝ) 1) :
    ∃ n : ℕ+, y.val ∈ Ioo (lineLoss (modeWave n)) (lineLoss (modeWave 1)) := by
  have ht : Tendsto (fun k => occupationWeight k^2) atTop (𝓝 0) := by
    simpa only [zero_pow two_ne_zero] using occupationWeight_tendsto.pow 2
  obtain ⟨k,hk⟩ := (ht.eventually_lt_const y.property.1).exists
  refine ⟨number k,?_⟩
  rw [lineLoss_modeWave,lineLoss_modeWave]
  exact ⟨hk,by simpa [attenuation,gain] using y.property.2⟩

#print axioms omissionArc_intermediate
#print axioms lineLoss_modeWave
#print axioms modeWave_straddle

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
