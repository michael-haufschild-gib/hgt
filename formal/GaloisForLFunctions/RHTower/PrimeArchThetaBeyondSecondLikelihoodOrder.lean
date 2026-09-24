import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio
import GaloisForLFunctions.RHTower.PrimeArchThetaTwoAtomNormalizedInterval

/-!
# Likelihood order beyond the second theta atom

The Born--Witten score is strictly increasing in the atom index. Hence every
later atom has decreasing density ratio against atom two; positive summation
preserves this order for the whole tail beyond atom two.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

def thetaCuspAtomPairLikelihoodRatio (m n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspSourceTerm x n / thetaCuspSourceTerm x m

theorem hasDerivAt_thetaCuspAtomPairLikelihoodRatio
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspAtomPairLikelihoodRatio m n)
      (-2 * (thetaCuspBornWittenSuperpotential n x -
          thetaCuspBornWittenSuperpotential m x) *
        thetaCuspAtomPairLikelihoodRatio m n x) x := by
  have hnDeriv := hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore hn hx
  have hmDeriv := hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore hm hx
  have hmpos := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hm
  have hquot := hnDeriv.div hmDeriv hmpos.ne'
  refine hquot.congr_deriv ?_
  simp only [thetaCuspAtomPairLikelihoodRatio]
  field_simp [hmpos.ne']
  ring

theorem thetaCuspAtomPairLikelihoodRatio_antitoneOn
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    AntitoneOn (thetaCuspAtomPairLikelihoodRatio m n) (Ioi 0) := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_thetaCuspAtomPairLikelihoodRatio hm hn hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_thetaCuspAtomPairLikelihoodRatio hm hn hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hscore := thetaCuspBornWittenSuperpotential_mono_nat hm hmn hx.le
    have hratio : 0 ≤ thetaCuspAtomPairLikelihoodRatio m n x :=
      (div_pos
        (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hn)
        (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hm)).le
    rw [(hasDerivAt_thetaCuspAtomPairLikelihoodRatio hm hn hx).deriv]
    nlinarith [mul_nonneg (sub_nonneg.mpr hscore) hratio]

/-- Density of the tail beyond atom two relative to atom two. -/
def thetaCuspBeyondSecondToSecondLikelihoodRatio (x : ℝ) : ℝ :=
  (thetaCuspFullSource x - thetaCuspSourceTerm x 1 -
    thetaCuspSourceTerm x 2) / thetaCuspSourceTerm x 2

theorem summable_thetaCuspBeyondSecondAtomPairLikelihoodRatios (x : ℝ) :
    Summable (fun k : ℕ => thetaCuspAtomPairLikelihoodRatio 2 (k + 3) x) := by
  have hs := summable_thetaCuspSourceTerm x
  have htail : Summable (fun k : ℕ => thetaCuspSourceTerm x (k + 3)) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  simpa only [thetaCuspAtomPairLikelihoodRatio] using
    htail.div_const (thetaCuspSourceTerm x 2)

theorem thetaCuspBeyondSecondToSecondLikelihoodRatio_eq_tsum (x : ℝ) :
    thetaCuspBeyondSecondToSecondLikelihoodRatio x =
      ∑' k : ℕ, thetaCuspAtomPairLikelihoodRatio 2 (k + 3) x := by
  have hs := summable_thetaCuspSourceTerm x
  have hhead :
      (∑ n ∈ Finset.range 3, thetaCuspSourceTerm x n) =
        thetaCuspSourceTerm x 1 + thetaCuspSourceTerm x 2 := by
    simp [Finset.sum_range_succ, thetaCuspSourceTerm, thetaCuspSeed]
  have htail :
      thetaCuspFullSource x - thetaCuspSourceTerm x 1 -
        thetaCuspSourceTerm x 2 =
          ∑' k : ℕ, thetaCuspSourceTerm x (k + 3) := by
    rw [thetaCuspFullSource, ← hs.sum_add_tsum_nat_add 3, hhead]
    ring
  rw [thetaCuspBeyondSecondToSecondLikelihoodRatio, htail]
  simpa only [thetaCuspAtomPairLikelihoodRatio] using
    (tsum_div_const (f := fun k : ℕ => thetaCuspSourceTerm x (k + 3))
      (a := thetaCuspSourceTerm x 2)).symm

/-- The tail past atom two is likelihood-ratio smaller than atom two itself. -/
theorem thetaCuspBeyondSecondToSecondLikelihoodRatio_antitoneOn :
    AntitoneOn thetaCuspBeyondSecondToSecondLikelihoodRatio (Ioi 0) := by
  intro x hx y hy hxy
  rw [thetaCuspBeyondSecondToSecondLikelihoodRatio_eq_tsum,
    thetaCuspBeyondSecondToSecondLikelihoodRatio_eq_tsum]
  exact Summable.tsum_le_tsum
    (fun k => thetaCuspAtomPairLikelihoodRatio_antitoneOn
      (m := 2) (n := k + 3) (by omega) (by omega) hx hy hxy)
    (summable_thetaCuspBeyondSecondAtomPairLikelihoodRatios y)
    (summable_thetaCuspBeyondSecondAtomPairLikelihoodRatios x)

private theorem twoDensity_rawEvenMoment_cross_le
    (f h : ℝ → ℝ) (j : ℕ)
    (hf₀ : Integrable f (volume.restrict (Ioi 0)))
    (hh₀ : Integrable h (volume.restrict (Ioi 0)))
    (hfj : Integrable (fun x : ℝ => x ^ (2 * j) * f x)
      (volume.restrict (Ioi 0)))
    (hhj : Integrable (fun x : ℝ => x ^ (2 * j) * h x)
      (volume.restrict (Ioi 0)))
    (horder : ∀ x y : ℝ, 0 < x → x ≤ y → h y * f x ≤ h x * f y) :
    (2 * ∫ x : ℝ in Ioi 0, x ^ (2 * j) * h x) *
        (2 * ∫ x : ℝ in Ioi 0, f x) ≤
      (2 * ∫ x : ℝ in Ioi 0, x ^ (2 * j) * f x) *
        (2 * ∫ x : ℝ in Ioi 0, h x) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let g : ℝ → ℝ := fun x => x ^ (2 * j)
  have hmem : ∀ᵐ z : ℝ × ℝ ∂μ.prod μ,
      z ∈ (Ioi 0 ×ˢ Ioi 0) := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ⟨hx, hy⟩
  have hkernel : ∀ᵐ z : ℝ × ℝ ∂μ.prod μ,
      0 ≤ (g z.2 - g z.1) *
        (h z.1 * f z.2 - h z.2 * f z.1) := by
    filter_upwards [hmem] with z hz
    rcases hz with ⟨hx, hy⟩
    rcases le_total z.1 z.2 with hxy | hyx
    · exact mul_nonneg
        (sub_nonneg.mpr (pow_le_pow_left₀ hx.le hxy (2 * j)))
        (sub_nonneg.mpr (horder _ _ hx hxy))
    · have hprod := mul_nonneg
        (sub_nonneg.mpr (pow_le_pow_left₀ hy.le hyx (2 * j)))
        (sub_nonneg.mpr (horder _ _ hy hyx))
      nlinarith [hprod]
  have hcross := HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel
    hf₀ hh₀ hfj hhj hkernel
  nlinarith

private theorem integrableOn_pow_mul_thetaCuspBeyondSecondSource (j : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * j) *
      (thetaCuspFullSource x - thetaCuspSourceTerm x 1 -
        thetaCuspSourceTerm x 2)) (Ioi 0) := by
  have hf := integrableOn_thetaCuspRawMoment (2 * j)
  have hg₁ := integrableOn_pow_mul_thetaCuspSourceTerm j 1
  have hg₂ := integrableOn_pow_mul_thetaCuspSourceTerm j 2
  convert (hf.sub hg₁).sub hg₂ using 1
  funext x
  simp only [Pi.sub_apply]
  ring

theorem thetaCuspBeyondSecondAtomRawEvenMoment_eq_integral_tail (j : ℕ) :
    thetaCuspBeyondSecondAtomRawEvenMoment j =
      2 * ∫ x : ℝ in Ioi 0, x ^ (2 * j) *
        (thetaCuspFullSource x - thetaCuspSourceTerm x 1 -
          thetaCuspSourceTerm x 2) := by
  have hf := integrableOn_thetaCuspRawMoment (2 * j)
  have hg₁ := integrableOn_pow_mul_thetaCuspSourceTerm j 1
  have hg₂ := integrableOn_pow_mul_thetaCuspSourceTerm j 2
  simp only [thetaCuspBeyondSecondAtomRawEvenMoment,
    thetaCuspRawEvenMoment, thetaCuspAtomRawEvenMoment]
  calc
    2 * (∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspFullSource x) -
        2 * (∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspSourceTerm x 1) -
        2 * (∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspSourceTerm x 2) =
      2 * ((∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspFullSource x) -
        (∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspSourceTerm x 1) -
        (∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspSourceTerm x 2)) := by ring
    _ = _ := by
      congr 1
      rw [← integral_sub hf hg₁]
      change
        (∫ x : ℝ in Ioi 0,
          ((fun y : ℝ => y ^ (2 * j) * thetaCuspFullSource y) -
            (fun y : ℝ => y ^ (2 * j) * thetaCuspSourceTerm y 1)) x) -
          (∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspSourceTerm x 2) = _
      rw [← integral_sub (hf.sub hg₁) hg₂]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Pi.sub_apply]
      ring

theorem thetaCuspAtomPair_rawEvenMoment_cross_le
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (j : ℕ) :
    thetaCuspAtomRawEvenMoment j n * thetaCuspAtomRawEvenMoment 0 m ≤
      thetaCuspAtomRawEvenMoment j m * thetaCuspAtomRawEvenMoment 0 n := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have horder (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
      thetaCuspSourceTerm y n * thetaCuspSourceTerm x m ≤
        thetaCuspSourceTerm x n * thetaCuspSourceTerm y m := by
    have hy : 0 < y := hx.trans_le hxy
    have hr := thetaCuspAtomPairLikelihoodRatio_antitoneOn hm hmn hx hy hxy
    have hmx := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hm
    have hmy := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hy hm
    exact (div_le_div_iff₀ hmy hmx).mp hr
  have hcross := twoDensity_rawEvenMoment_cross_le
    (thetaCuspSourceTerm · m) (thetaCuspSourceTerm · n) j
    (by
      change IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x m) (Ioi 0)
      simpa using integrableOn_pow_mul_thetaCuspSourceTerm 0 m)
    (by
      change IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x n) (Ioi 0)
      simpa using integrableOn_pow_mul_thetaCuspSourceTerm 0 n)
    (integrableOn_pow_mul_thetaCuspSourceTerm j m)
    (integrableOn_pow_mul_thetaCuspSourceTerm j n) horder
  simpa only [thetaCuspAtomRawEvenMoment, mul_zero, pow_zero, one_mul] using hcross

theorem thetaCuspBeyondSecondSecond_rawEvenMoment_cross_le (j : ℕ) :
    thetaCuspBeyondSecondAtomRawEvenMoment j *
        thetaCuspAtomRawEvenMoment 0 2 ≤
      thetaCuspAtomRawEvenMoment j 2 *
        thetaCuspBeyondSecondAtomRawEvenMoment 0 := by
  let tail : ℝ → ℝ := fun x => thetaCuspFullSource x -
    thetaCuspSourceTerm x 1 - thetaCuspSourceTerm x 2
  have horder (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
      tail y * thetaCuspSourceTerm x 2 ≤
        tail x * thetaCuspSourceTerm y 2 := by
    have hy : 0 < y := hx.trans_le hxy
    have hr := thetaCuspBeyondSecondToSecondLikelihoodRatio_antitoneOn hx hy hxy
    have hmx := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < 2)
    have hmy := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hy (by norm_num : 0 < 2)
    exact (div_le_div_iff₀ hmy hmx).mp hr
  have hcross := twoDensity_rawEvenMoment_cross_le
    (thetaCuspSourceTerm · 2) tail j
    (by
      change IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x 2) (Ioi 0)
      simpa using integrableOn_pow_mul_thetaCuspSourceTerm 0 2)
    (by
      change IntegrableOn tail (Ioi 0)
      simpa [tail] using integrableOn_pow_mul_thetaCuspBeyondSecondSource 0)
    (integrableOn_pow_mul_thetaCuspSourceTerm j 2)
    (integrableOn_pow_mul_thetaCuspBeyondSecondSource j) horder
  simpa only [thetaCuspAtomRawEvenMoment,
    thetaCuspBeyondSecondAtomRawEvenMoment_eq_integral_tail,
    mul_zero, pow_zero, one_mul, tail] using hcross

/-- The later atoms pull every normalized even moment below its first-two-atom value.
This sharpens the upper endpoint of the elementary tail interval without using
the numeric tail factor. -/
theorem thetaCuspNormalizedEvenMoment_le_twoAtomNormalizedEvenMoment (j : ℕ) :
    thetaCuspNormalizedEvenMoment j ≤
      (thetaCuspAtomRawEvenMoment j 1 + thetaCuspAtomRawEvenMoment j 2) /
        (thetaCuspAtomRawEvenMoment 0 1 + thetaCuspAtomRawEvenMoment 0 2) := by
  let a₀ := thetaCuspAtomRawEvenMoment 0 1
  let b₀ := thetaCuspAtomRawEvenMoment 0 2
  let a := thetaCuspAtomRawEvenMoment j 1
  let b := thetaCuspAtomRawEvenMoment j 2
  let r₀ := thetaCuspBeyondSecondAtomRawEvenMoment 0
  let r := thetaCuspBeyondSecondAtomRawEvenMoment j
  have ha₀ : 0 < a₀ := thetaCuspAtomRawEvenMoment_pos_of_nat_pos 0 (by norm_num)
  have hb₀ : 0 < b₀ := thetaCuspAtomRawEvenMoment_pos_of_nat_pos 0 (by norm_num)
  have hr₀ : 0 ≤ r₀ := (thetaCuspBeyondSecondAtomRawEvenMoment_mem_interval 0).1
  have hpair : b * a₀ ≤ a * b₀ :=
    thetaCuspAtomPair_rawEvenMoment_cross_le (by norm_num : 0 < 1)
      (by norm_num : 1 ≤ 2) j
  have htail : r * b₀ ≤ b * r₀ :=
    thetaCuspBeyondSecondSecond_rawEvenMoment_cross_le j
  have htail_first : r * a₀ ≤ a * r₀ := by
    have hp : (r * a₀) * b₀ ≤ (a * r₀) * b₀ := calc
      (r * a₀) * b₀ = (r * b₀) * a₀ := by ring
      _ ≤ (b * r₀) * a₀ := mul_le_mul_of_nonneg_right htail ha₀.le
      _ = (b * a₀) * r₀ := by ring
      _ ≤ (a * b₀) * r₀ := mul_le_mul_of_nonneg_right hpair hr₀
      _ = (a * r₀) * b₀ := by ring
    by_contra hn
    have hdiff : 0 < r * a₀ - a * r₀ := sub_pos.mpr (lt_of_not_ge hn)
    nlinarith [mul_pos hdiff hb₀]
  have hden : 0 < a₀ + b₀ := add_pos ha₀ hb₀
  have hraw₀ : thetaCuspRawEvenMoment 0 = a₀ + b₀ + r₀ := by
    dsimp [a₀, b₀, r₀, thetaCuspBeyondSecondAtomRawEvenMoment]
    ring
  have hraw : thetaCuspRawEvenMoment j = a + b + r := by
    dsimp [a, b, r, thetaCuspBeyondSecondAtomRawEvenMoment]
    ring
  have hsource₀ : 0 < a₀ + b₀ + r₀ := by
    rw [← hraw₀]
    exact thetaCuspRawEvenMoment_zero_pos
  change thetaCuspRawEvenMoment j / thetaCuspRawEvenMoment 0 ≤
    (a + b) / (a₀ + b₀)
  rw [hraw, hraw₀]
  apply (div_le_div_iff₀ hsource₀ hden).2
  nlinarith [htail, htail_first]

end
end RHTower
