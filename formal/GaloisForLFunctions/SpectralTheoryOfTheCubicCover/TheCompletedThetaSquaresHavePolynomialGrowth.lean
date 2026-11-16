import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubicThetaPairingsAreBoundedOnVerticalStrips
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubicScatteringHasPolynomialGrowth
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUnramifiedThetaSquareHasADoublePole

/-!
# Polynomial growth of the completed theta squares

On every closed strip inside `1 < Re s < 13/3`, the seed pairings and the
`L²` correction pairings are bounded. The explicit cusp scattering terms
have cubic growth. Their sum gives a common cubic bound for the actual full,
translated and unramified completed theta-square series at `|Im s| ≥ 1`.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

private theorem norm_sub_real_ge_one (s : ℂ) (r : ℝ) (ht : 1 ≤ |s.im|) :
    1 ≤ ‖s - (r : ℂ)‖ := by
  have h : |s.im| ≤ ‖s - (r : ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      Complex.abs_im_le_norm (s - (r : ℂ))
  exact ht.trans h

private theorem thetaPowerTerms_bound (a B : ℝ) (s : ℂ)
    (ha : a ≤ s.re) (hB : s.re ≤ B) (ht : 1 ≤ |s.im|) :
    ‖(2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3)‖ ≤ (2 : ℝ) ^ (B - 2 / 3) ∧
    ‖(2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2‖ ≤ (2 : ℝ) ^ (4 / 3 - a) := by
  have h23 : 1 ≤ ‖s - 2 / 3‖ := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using norm_sub_real_ge_one s (2 / 3) ht
  have h43 : 1 ≤ ‖s - 4 / 3‖ := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using norm_sub_real_ge_one s (4 / 3) ht
  constructor
  · rw [norm_div]
    refine (div_le_self (norm_nonneg _) h23).trans ?_
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simp
    linarith
  · rw [norm_div, norm_pow]
    refine (div_le_self (norm_nonneg _) (one_le_pow₀ h43)).trans ?_
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simp
    linarith

/-- The actual completed full, translated and unramified squares have cubic polynomial growth. -/
theorem completedThetaSquares_vertical_bound (a B : ℝ) (ha : 1 < a) (haB : a ≤ B)
    (hB : B < 13 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ B → 1 ≤ |s.im| →
      ‖completedThetaSq s‖ ≤ C * (1 + ‖s‖) ^ 3 ∧
      ‖completedTranslated s‖ ≤ C * (1 + ‖s‖) ^ 3 ∧
      ‖completedUnramified s‖ ≤ C * (1 + ‖s‖) ^ 3 := by
  obtain ⟨S, hS, hs⟩ := thetaSeedPairings_bounded B hB
  obtain ⟨D, hD, hd⟩ := thetaCorrectionPairings_bounded a B ha haB
  obtain ⟨T, hT, ht⟩ := clearedThetaScattering_vertical_bound a B ha
  let P : ℝ := ‖periodArea * thetaCoeff ^ 2‖ * (2 : ℝ) ^ (B - 2 / 3)
  let Q : ℝ := ‖thetaCoeff ^ 2‖ * T * (2 : ℝ) ^ (4 / 3 - a)
  let C : ℝ := ‖periodArea⁻¹‖ * (S + D + P + Q)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨2 * C, by positivity, ?_⟩
  intro s hsa hsb hsi
  obtain ⟨hseed, htransseed⟩ := hs s hsb
  obtain ⟨hcorr, htranscorr⟩ := hd s hsa hsb hsi
  obtain ⟨hscatter, htransscatter⟩ := ht s hsa hsb hsi
  obtain ⟨hpow, hpow'⟩ := thetaPowerTerms_bound a B s hsa hsb hsi
  have hr : 1 ≤ (1 + ‖s‖) ^ 3 := one_le_pow₀ (by linarith [norm_nonneg s] : 1 ≤ 1 + ‖s‖)
  have hbase : ‖periodArea * thetaCoeff ^ 2 * ((2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3))‖ ≤ P := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  have hfun (X Y Z : ℂ) (hX : ‖X‖ ≤ S) (hY : ‖Y‖ ≤ D)
      (hZ : ‖Z‖ ≤ T * (1 + ‖s‖) ^ 3) :
      ‖periodArea⁻¹ * (X + Y -
        periodArea * thetaCoeff ^ 2 * ((2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3)) +
          thetaCoeff ^ 2 * Z * ((2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2))‖ ≤
        C * (1 + ‖s‖) ^ 3 := by
    have hlast : ‖thetaCoeff ^ 2 * Z * ((2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2)‖ ≤
        Q * (1 + ‖s‖) ^ 3 := by
      rw [norm_mul, norm_mul]
      calc
        _ ≤ ‖thetaCoeff ^ 2‖ * (T * (1 + ‖s‖) ^ 3) * (2 : ℝ) ^ (4 / 3 - a) := by gcongr
        _ = _ := by dsimp only [Q]; ring
    rw [norm_mul]
    calc
      _ ≤ ‖periodArea⁻¹‖ * (‖X‖ + ‖Y‖ +
          ‖periodArea * thetaCoeff ^ 2 * ((2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3))‖ +
            ‖thetaCoeff ^ 2 * Z * ((2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2)‖) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add
          ((norm_sub_le _ _).trans (add_le_add (norm_add_le X Y) le_rfl)) le_rfl)
      _ ≤ ‖periodArea⁻¹‖ * (S + D + P + Q * (1 + ‖s‖) ^ 3) := by gcongr
      _ ≤ ‖periodArea⁻¹‖ * ((S + D + P + Q) * (1 + ‖s‖) ^ 3) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have h := mul_le_mul_of_nonneg_left hr (add_nonneg (add_nonneg hS hD) hP)
        nlinarith only [h]
      _ = C * (1 + ‖s‖) ^ 3 := by dsimp only [C]; ring
  have hf : ‖completedThetaSq s‖ ≤ C * (1 + ‖s‖) ^ 3 := hfun _ _ _ hseed hcorr hscatter
  have hg : ‖completedTranslated s‖ ≤ C * (1 + ‖s‖) ^ 3 := hfun _ _ _ htransseed htranscorr htransscatter
  have hnonneg : 0 ≤ C * (1 + ‖s‖) ^ 3 := by positivity
  refine ⟨hf.trans (by nlinarith only [hnonneg]), hg.trans (by nlinarith only [hnonneg]), ?_⟩
  rw [completedUnramified, norm_mul]
  have hcoef : ‖(2 / 3 : ℂ)‖ = (2 / 3 : ℝ) := by norm_num
  rw [hcoef]
  have hsub := (norm_sub_le (completedThetaSq s) (completedTranslated s)).trans (add_le_add hf hg)
  nlinarith only [hsub, hnonneg]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
