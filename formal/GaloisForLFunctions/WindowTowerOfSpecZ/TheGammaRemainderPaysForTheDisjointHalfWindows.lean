import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderRetainsHigherLags
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTrivialApertureAndTheExceptionalSquare

/-!
# The Gamma reserve from disjoint half-windows

Beyond half the support length, autocorrelation is at most half the square
mass. Integrating the retained cubic and quartic Gamma weights there gives
an explicit positive reserve, with coefficient `1/6250` at aperture `1881/5000`.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.WeilMarkovPole _root_.RHTower.WeilLevyPoleGauss
open _root_.RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory BiScaleUncertainty LatticeSectionTheory

/-- Disjoint halves of the support pay a positive mass reserve inside the local Gamma remainder. -/
theorem local_gamma_remainder_ge_half_window_reserve {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) {a : ℝ} (ha : 0 < a)
    (ha1 : 2 * a ≤ 1) (hs : tsupport F ⊆ Icc (-a) a) :
    (a ^ 4 / 512 + 31 * a ^ 5 / 1920) * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) (2 * a), retainedGammaRemainderWeight t *
        (autocorr F 0 - autocorr F t) := by
  let M := ∫ x, F x ^ 2
  let R := fun t => retainedGammaRemainderWeight t * (autocorr F 0 - autocorr F t)
  have hM : 0 ≤ M := integral_nonneg fun x => sq_nonneg (F x)
  have hR : IntegrableOn R (Ioc (0 : ℝ) (2 * a)) :=
    (retainedGammaRemainder_integrable_nonneg hF hcs).1.mono_set
      (fun _ ht => ⟨ht.1, ht.2.trans ha1⟩)
  have hsub0 : Ioc (0 : ℝ) a ⊆ Ioc (0 : ℝ) (2 * a) :=
    fun _ ht => ⟨ht.1, by linarith only [ht.2, ha]⟩
  have hsub1 : Ioc a (2 * a) ⊆ Ioc (0 : ℝ) (2 * a) :=
    fun _ ht => ⟨ha.trans ht.1, ht.2⟩
  have hn : 0 ≤ ∫ t in Ioc (0 : ℝ) a, R t := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    exact mul_nonneg (retainedGammaRemainderWeight_nonneg ⟨ht.1, by linarith only [ht.2, ha1, ha]⟩)
      (sub_nonneg.mpr ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t)))
  have hhalf (t : ℝ) (ht : a < t) : autocorr F t ≤ M / 2 := by
    have h := AbsoluteGeometryOfSpecZ.two_mul_abs_packetAutocorr_le_of_aperture
      hF.continuous hcs (c := 0) ht.le (fun x hx => by
        apply image_eq_zero_of_notMem_tsupport
        intro hxs
        have hb := hs hxs
        simp only [sub_zero] at hx
        exact (not_lt_of_ge (abs_le.mpr hb)) hx)
    change 2 * |autocorr F t| ≤ M at h
    linarith only [h, le_abs_self (autocorr F t)]
  have hp : IntegrableOn (fun t : ℝ => (t ^ 3 / 960 + t ^ 4 / 192) * (M / 2))
      (Ioc a (2 * a)) := by
    exact (show Continuous (fun t : ℝ => (t ^ 3 / 960 + t ^ 4 / 192) * (M / 2))
      from by fun_prop).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hc : (∫ t in Ioc a (2 * a), (t ^ 3 / 960 + t ^ 4 / 192) * (M / 2)) ≤
      ∫ t in Ioc a (2 * a), R t := by
    apply setIntegral_mono_on hp (hR.mono_set hsub1) measurableSet_Ioc
    intro t ht
    have ht0 := ha.trans ht.1
    have hw := retainedGammaRemainderWeight_ge_higher_lags ⟨ht0, ht.2.trans ha1⟩
    have hw0 : 0 ≤ t ^ 3 / 960 + t ^ 4 / 192 := by positivity
    have hd : M / 2 ≤ autocorr F 0 - autocorr F t := by
      rw [autocorr_zero_eq]
      linarith only [hhalf t ht.1]
    exact mul_le_mul hw hd (by positivity) (hw0.trans hw)
  have he : (∫ t in Ioc a (2 * a), (t ^ 3 / 960 + t ^ 4 / 192) * (M / 2)) =
      (a ^ 4 / 512 + 31 * a ^ 5 / 1920) * M := by
    rw [← intervalIntegral.integral_of_le (by linarith only [ha] : a ≤ 2 * a),
      intervalIntegral.integral_mul_const,
      intervalIntegral.integral_add (μ := volume)
        (f := fun t : ℝ => t ^ 3 / 960) (g := fun t : ℝ => t ^ 4 / 192)
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_div, intervalIntegral.integral_div, integral_pow, integral_pow]
    norm_num
    ring
  have hu : Ioc (0 : ℝ) a ∪ Ioc a (2 * a) = Ioc (0 : ℝ) (2 * a) := by
    ext t
    simp only [mem_union, mem_Ioc]
    constructor
    · rintro (⟨ht0, hta⟩ | ⟨hta, ht2⟩)
      · exact ⟨ht0, by linarith only [hta, ha]⟩
      · exact ⟨ha.trans hta, ht2⟩
    · rintro ⟨ht0, ht2⟩
      rcases le_or_gt t a with ht | ht
      · exact Or.inl ⟨ht0, ht⟩
      · exact Or.inr ⟨ht, ht2⟩
  have hadd := setIntegral_union
    (s := Ioc (0 : ℝ) a) (t := Ioc a (2 * a))
    (Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht'.1))
    measurableSet_Ioc (hR.mono_set hsub0) (hR.mono_set hsub1)
  rw [hu] at hadd
  rw [he] at hc
  change _ ≤ ∫ t in Ioc (0 : ℝ) (2 * a), R t
  linarith only [hn, hc, hadd]

/-- The half-window reserve is at least `1/6250` at aperture `1881/5000`. -/
theorem local_gamma_remainder_ge_at_aperture_1881_over_5000 {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1881 / 5000 : ℝ)) (1881 / 5000)) :
    (1 / 6250 : ℝ) * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) (1881 / 2500), retainedGammaRemainderWeight t *
        (autocorr F 0 - autocorr F t) := by
  have h := local_gamma_remainder_ge_half_window_reserve hF hcs (by norm_num) (by norm_num) hs
  have hn : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg (F x)
  norm_num at h
  nlinarith only [h, hn]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.local_gamma_remainder_ge_half_window_reserve
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.local_gamma_remainder_ge_at_aperture_1881_over_5000
