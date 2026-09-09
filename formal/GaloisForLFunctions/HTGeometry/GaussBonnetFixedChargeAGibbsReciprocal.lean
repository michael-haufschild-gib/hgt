import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsKernel

/-!
# The radial reciprocal's first correction

Its first divided difference has a simple exact form on the phase
interval. The identity also holds eventually at every fixed real
coordinate, and its uniform bounds control the odd profile correction.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsReciprocal (τ t : ℝ) : ℝ := 1 / (1 + egbCoexistenceASymmetricRatio τ * t) ^ 2

theorem egbFixedChargeAGibbsRadialScale_critical_limit (t : ℝ) :
    Tendsto (fun τ => 1 + egbCoexistenceASymmetricRatio τ * t) atBot (𝓝 (1 : ℝ)) := by
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
    (egbCoexistenceASymmetricRatio_critical_limit.mul (tendsto_const_nhds (x := t)))

theorem egbFixedChargeAGibbsReciprocal_critical_limit (t : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsReciprocal τ t) atBot (𝓝 (1 : ℝ)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).div ((egbFixedChargeAGibbsRadialScale_critical_limit t).pow 2) (by norm_num)
  simpa only [egbFixedChargeAGibbsReciprocal, Pi.div_def, one_pow, div_one] using h

theorem egbFixedChargeAGibbsReciprocal_difference_onInterval (τ : ℝ) :
    EqOn (fun t => (egbFixedChargeAGibbsReciprocal τ t - 1) / egbCoexistenceASymmetricRatio τ)
      (fun t => -t * (2 + egbCoexistenceASymmetricRatio τ * t) / (1 + egbCoexistenceASymmetricRatio τ * t) ^ 2)
      (Icc (-1 : ℝ) 1) := by
  intro t ht
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hs := (egbFixedChargeAInteriorScale_mapsTo τ ht).1
  have hp : 0 < 1 + egbCoexistenceASymmetricRatio τ * t := by linarith [hd.2]
  have hdpos := hd.1
  unfold egbFixedChargeAGibbsReciprocal
  field_simp <;> ring

theorem egbFixedChargeAGibbsReciprocal_difference_eventually (t : ℝ) :
    ∀ᶠ τ in atBot, (egbFixedChargeAGibbsReciprocal τ t - 1) / egbCoexistenceASymmetricRatio τ =
      -t * (2 + egbCoexistenceASymmetricRatio τ * t) / (1 + egbCoexistenceASymmetricRatio τ * t) ^ 2 := by
  have hs := (egbFixedChargeAGibbsRadialScale_critical_limit t).eventually_const_lt (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hs] with τ hs
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAGibbsReciprocal
  field_simp <;> ring

theorem egbFixedChargeAGibbsReciprocal_linear_limit (t : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsReciprocal τ t - 1) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (-2 * t)) := by
  have hn := (tendsto_const_nhds (x := -t)).mul ((tendsto_const_nhds (x := (2 : ℝ))).add
    (egbCoexistenceASymmetricRatio_critical_limit.mul (tendsto_const_nhds (x := t))))
  have he : -t * (2 + 0 * t) = -2 * t := by ring
  rw [he] at hn
  have h := hn.div ((egbFixedChargeAGibbsRadialScale_critical_limit t).pow 2) (by norm_num)
  simp only [Pi.div_def, one_pow, div_one] at h
  have hevent : ∀ᶠ τ in atBot,
      -t * (2 + egbCoexistenceASymmetricRatio τ * t) / (1 + egbCoexistenceASymmetricRatio τ * t) ^ 2 =
      (egbFixedChargeAGibbsReciprocal τ t - 1) / egbCoexistenceASymmetricRatio τ := by
    filter_upwards [egbFixedChargeAGibbsReciprocal_difference_eventually t] with τ heq
    exact heq.symm
  exact Filter.Tendsto.congr' hevent h

theorem egbFixedChargeAGibbsReciprocal_uniform_bounds :
    ∀ᶠ τ in atBot, ∀ t ∈ Icc (-1 : ℝ) 1,
      (0 < egbFixedChargeAGibbsReciprocal τ t ∧ egbFixedChargeAGibbsReciprocal τ t ≤ 4) ∧
      |(egbFixedChargeAGibbsReciprocal τ t - 1) / egbCoexistenceASymmetricRatio τ| ≤ 12 := by
  have hdhi := egbCoexistenceASymmetricRatio_critical_limit.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hdhi] with τ hdhi
  intro t ht
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hscale := (egbFixedChargeAInteriorScale_mapsTo τ ht).1
  have hs : 1 / 2 ≤ 1 + egbCoexistenceASymmetricRatio τ * t := by linarith
  have hs2 : 1 / 4 ≤ (1 + egbCoexistenceASymmetricRatio τ * t) ^ 2 := by
    nlinarith [sq_nonneg (1 + egbCoexistenceASymmetricRatio τ * t - 1 / 2)]
  have hsp : 0 < (1 + egbCoexistenceASymmetricRatio τ * t) ^ 2 := by linarith
  have htabs : |t| ≤ 1 := abs_le.mpr ht
  have hdabs : |egbCoexistenceASymmetricRatio τ| ≤ 1 := by rw [abs_of_pos hd]; linarith
  have hdt : |egbCoexistenceASymmetricRatio τ * t| ≤ 1 := by
    rw [abs_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul hdabs htabs (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hsum : |2 + egbCoexistenceASymmetricRatio τ * t| ≤ 3 := by
    calc
      _ ≤ |(2 : ℝ)| + |egbCoexistenceASymmetricRatio τ * t| := abs_add_le _ _
      _ ≤ 2 + 1 := add_le_add (by norm_num) hdt
      _ = _ := by norm_num
  have hn : |-t * (2 + egbCoexistenceASymmetricRatio τ * t)| ≤ 3 := by
    rw [abs_mul, abs_neg]
    calc
      _ ≤ 1 * 3 := mul_le_mul htabs hsum (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  constructor
  · constructor
    · exact div_pos (by norm_num) hsp
    · unfold egbFixedChargeAGibbsReciprocal
      apply (div_le_iff₀ hsp).2
      nlinarith only [hs2]
  · have he := egbFixedChargeAGibbsReciprocal_difference_onInterval τ ht
    dsimp only at he
    rw [he, abs_div, abs_of_pos hsp]
    apply (div_le_iff₀ hsp).2
    nlinarith only [hn, hs2]

end GaloisForLFunctions.HTGeometry
