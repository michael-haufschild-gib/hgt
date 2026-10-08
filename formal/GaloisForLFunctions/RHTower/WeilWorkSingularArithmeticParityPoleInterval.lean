import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticParityPoleBound
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPoleSign

/-!
# The actual parity series is confined near its possible double pole

Two fixed polynomial tests constrain the normalized alternating Dirichlet
series to an explicit interval. The argument never assumes that it has a limit.
-/

open Complex Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem four_rpow_neg_half : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
  rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

private theorem quarter_rpow_neg_half : (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) = 2 := by
  rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  norm_num only [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, inv_div, div_one]

/-- Full positivity confines the actual normalized parity series, without a pole-limit premise. -/
theorem eventually_sourceNormalizedParityPole_interval {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |sourceNormalizedParityPole lam σ + (sourcePoleNumerator hW 1).re / 2| ≤
        -Real.sqrt 2 * (sourcePoleNumerator hW 1).re + ε := by
  let κ : ℝ := Real.sqrt 2
  let ell : ℝ := (sourcePoleNumerator hW 1).re
  let a : ℝ → ℝ := fun σ => (σ - 1) ^ 2 *
    (mellin (sourceGaussianProfile lam) ((σ : ℂ) / 2)).re
  let d : ℝ → ℝ := fun σ => (4 : ℝ) ^ (-(σ / 2))
  let e : ℝ → ℝ := fun σ => (1 / 4 : ℝ) ^ (-(σ / 2))
  let den : ℝ → ℝ := fun σ => (κ / 2) * e σ
  have hκ : 0 < κ := Real.sqrt_pos.mpr (by norm_num)
  have hκ2 : κ ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hdenpos (σ : ℝ) : 0 < den σ := by
    exact mul_pos (div_pos hκ (by norm_num)) (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨Bp, hBp⟩ := exists_source_normalized_parity_quadratic_le hW κ
  obtain ⟨Bm, hBm⟩ := exists_source_normalized_parity_quadratic_le hW (-κ)
  let L : ℝ → ℝ := fun σ => ((2 - κ * d σ) * a σ - (σ - 1) ^ 2 * Bp) / den σ
  let U : ℝ → ℝ := fun σ => ((σ - 1) ^ 2 * Bm - (2 + κ * d σ) * a σ) / den σ
  have hbounds : ∀ᶠ σ : ℝ in 𝓝[>] 1,
      L σ ≤ sourceNormalizedParityPole lam σ ∧ sourceNormalizedParityPole lam σ ≤ U σ := by
    have hu : ∀ᶠ σ : ℝ in 𝓝[>] 1, σ < 3 / 2 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (isOpen_Iio.mem_nhds (show (1 : ℝ) ∈ Iio (3 / 2) by norm_num))
    filter_upwards [self_mem_nhdsWithin, hu] with σ hσ hσ'
    have hp := hBp σ hσ hσ'
    have hm := hBm σ hσ hσ'
    change (1 + κ ^ 2 / 2 - κ * d σ) * a σ -
      (κ / 2) * e σ * sourceNormalizedParityPole lam σ ≤ (σ - 1) ^ 2 * Bp at hp
    change (1 + (-κ) ^ 2 / 2 - (-κ) * d σ) * a σ -
      ((-κ) / 2) * e σ * sourceNormalizedParityPole lam σ ≤ (σ - 1) ^ 2 * Bm at hm
    rw [hκ2] at hp
    rw [neg_sq, hκ2] at hm
    constructor
    · apply (div_le_iff₀ (hdenpos σ)).mpr
      dsimp only [den]
      nlinarith only [hp]
    · apply (le_div_iff₀ (hdenpos σ)).mpr
      dsimp only [den]
      nlinarith only [hm]
  have ha : Tendsto a (𝓝[>] 1) (𝓝 ell) :=
    tendsto_sq_mul_re_mellin_sourceGaussianProfile hW
  have hd : Tendsto d (𝓝[>] 1) (𝓝 (1 / 2)) := by
    have hc : ContinuousAt d 1 := by
      apply ContinuousAt.rpow continuousAt_const (by fun_prop)
      exact Or.inl (by norm_num)
    simpa only [d, four_rpow_neg_half] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have he : Tendsto e (𝓝[>] 1) (𝓝 2) := by
    have hc : ContinuousAt e 1 := by
      apply ContinuousAt.rpow continuousAt_const (by fun_prop)
      exact Or.inl (by norm_num)
    simpa only [e, quarter_rpow_neg_half] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hden : Tendsto den (𝓝[>] 1) (𝓝 κ) := by
    have h := (tendsto_const_nhds (x := κ / 2)).mul he
    simpa only [den, show (κ / 2) * 2 = κ by ring] using h
  have hz (B : ℝ) : Tendsto (fun σ : ℝ => (σ - 1) ^ 2 * B) (𝓝[>] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun σ : ℝ => (σ - 1) ^ 2 * B) 1 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlo : ((2 - κ * (1 / 2)) * ell - 0) / κ = (κ - 1 / 2) * ell := by
    calc
      _ = ((κ ^ 2 - κ * (1 / 2)) * ell) / κ := by rw [hκ2]; ring
      _ = _ := by field_simp [hκ.ne']
  have hup : (0 - (2 + κ * (1 / 2)) * ell) / κ = (-κ - 1 / 2) * ell := by
    calc
      _ = (-(κ ^ 2 + κ * (1 / 2)) * ell) / κ := by rw [hκ2]; ring
      _ = _ := by field_simp [hκ.ne']; ring
  have hL : Tendsto L (𝓝[>] 1) (𝓝 ((κ - 1 / 2) * ell)) := by
    rw [← hlo]
    exact (((tendsto_const_nhds.sub (tendsto_const_nhds.mul hd)).mul ha).sub
      (hz Bp)).div hden hκ.ne'
  have hU : Tendsto U (𝓝[>] 1) (𝓝 ((-κ - 1 / 2) * ell)) := by
    rw [← hup]
    exact ((hz Bm).sub ((tendsto_const_nhds.add (tendsto_const_nhds.mul hd)).mul ha)).div
      hden hκ.ne'
  have hLε : ∀ᶠ σ in 𝓝[>] (1 : ℝ), (κ - 1 / 2) * ell - ε < L σ :=
    hL.eventually (isOpen_Ioi.mem_nhds
      (show (κ - 1 / 2) * ell ∈ Ioi ((κ - 1 / 2) * ell - ε) by
        change (κ - 1 / 2) * ell - ε < (κ - 1 / 2) * ell
        linarith only [hε]))
  have hUε : ∀ᶠ σ in 𝓝[>] (1 : ℝ), U σ < (-κ - 1 / 2) * ell + ε :=
    hU.eventually (isOpen_Iio.mem_nhds
      (show (-κ - 1 / 2) * ell ∈ Iio ((-κ - 1 / 2) * ell + ε) by
        change (-κ - 1 / 2) * ell < (-κ - 1 / 2) * ell + ε
        linarith only [hε]))
  filter_upwards [hbounds, hLε, hUε] with σ hσ hLσ hUσ
  change |sourceNormalizedParityPole lam σ + ell / 2| ≤ -κ * ell + ε
  rw [abs_le]
  constructor <;> linarith [hσ.1, hσ.2]

end RHTower.WeilSingularArithmetic
