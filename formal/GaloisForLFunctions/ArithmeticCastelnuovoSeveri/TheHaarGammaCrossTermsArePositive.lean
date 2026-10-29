import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarLaplaceMoments
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaFiniteMeanZeroOffDiagonal
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaCouplingUsesOnlyDetailMass
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws

/-!
# Positive Laplace representation of the Haar Gamma interactions

Each ordered rectangle pairing factors into oppositely signed Laplace
moments. The original rectangle measure controls the absolute series,
including touching cells, so every Gamma off-diagonal entry is nonnegative.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open MeanZeroIntervals BiarithmeticGaugeGeometry

/-- The literal off-diagonal Gamma matrix entry; its diagonal is zero. -/
def haarGammaCoupling (a b : ℕ) : ℝ :=
  -(∫ p : ℝ × ℝ, haarProfile a p.1 * haarProfile b p.2
    ∂gammaRectangleMeasure
      (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
      (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)))

private theorem haarPair_order {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    Real.log ((2 * a + 2 : ℕ) : ℝ) ≤ Real.log ((2 * b : ℕ) : ℝ) := by
  apply Real.log_le_log (by positivity)
  exact_mod_cast (show 2 * a + 2 ≤ 2 * b by omega)

private theorem haarPair_disjoint {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b) :
    Disjoint (Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)))
      (Ioo (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ))) := by
  apply disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hab with h | h
  · have hs := haarPair_order ha h
    linarith only [hs, hx.2, hy.1]
  · have hs := haarPair_order hb h
    linarith only [hs, hy.2, hx.1]

theorem haarGammaCoupling_self (a : ℕ) : haarGammaCoupling a a = 0 := by
  rw [haarGammaCoupling, gammaRectangleMeasure_self, integral_zero_measure, neg_zero]

theorem haarGammaCoupling_symm {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    haarGammaCoupling a b = haarGammaCoupling b a := by
  by_cases hab : a = b
  · subst b
    rfl
  have hd := haarPair_disjoint ha hb hab
  have h := integral_gammaRectangle_swap hd
    (fun p : ℝ × ℝ => haarProfile a p.1 * haarProfile b p.2)
  unfold haarGammaCoupling
  rw [← h]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun _ => mul_comm _ _

/-- Every ordered interaction has its full, summable positive Laplace expansion.
The original rectangle measure supplies the absolute bound even at a shared endpoint. -/
theorem haarGammaCoupling_hasSum {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    HasSum (fun k : ℕ =>
      haarLaplaceLeft a (2 * (k : ℝ) + 1 / 2) *
        haarLaplaceRight b (2 * (k : ℝ) + 1 / 2)) (haarGammaCoupling a b) := by
  have hb : 1 ≤ b := by omega
  let L : ℕ → ℝ := fun i => Real.log ((2 * i : ℕ) : ℝ)
  let U : ℕ → ℝ := fun i => Real.log ((2 * i + 2 : ℕ) : ℝ)
  let μ : Measure (ℝ × ℝ) := (volume.restrict (Ioo (L a) (U a))).prod
    (volume.restrict (Ioo (L b) (U b)))
  let P : ℝ × ℝ → ℝ := fun p => haarProfile a p.1 * haarProfile b p.2
  let H : ℝ × ℝ → ℝ := fun p => P p * archLevyDensity |p.2 - p.1|
  let F (k : ℕ) (p : ℝ × ℝ) : ℝ :=
    P p * Real.exp (-(2 * (k : ℝ) + 1 / 2) * (p.2 - p.1))
  let B (k : ℕ) (p : ℝ × ℝ) : ℝ :=
    |P p| * Real.exp (-(2 * (k : ℝ) + 1 / 2) * (p.2 - p.1))
  have hsep : U a ≤ L b := haarPair_order ha hab
  have hd : Disjoint (Ioo (L a) (U a)) (Ioo (L b) (U b)) :=
    haarPair_disjoint ha hb hab.ne
  have hxy : ∀ᵐ p ∂μ, 0 < p.2 - p.1 := by
    have hx : ∀ᵐ p ∂μ, p.1 ∈ Ioo (L a) (U a) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
    have hy : ∀ᵐ p ∂μ, p.2 ∈ Ioo (L b) (U b) :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
    filter_upwards [hx, hy] with p hp hq
    linarith only [hp.2, hq.1, hsep]
  have hwidth : U a - L a ≤ 1 := by
    rw [show U a - L a = logCellWidth a from haarPairWidth ha]
    exact (logCellWidth_le_inv ha).trans
      ((div_le_one (by positivity : (0 : ℝ) < a)).mpr (by exact_mod_cast ha))
  have hlt : L a < U a := by
    apply sub_pos.mp
    rw [show U a - L a = logCellWidth a from haarPairWidth ha]
    exact logCellWidth_pos ha
  have hPm : Measurable P :=
    ((measurable_haarProfile a).comp measurable_fst).mul
      ((measurable_haarProfile b).comp measurable_snd)
  have hiR : Integrable P (gammaRectangleMeasure (L a) (U a) (L b) (U b)) := by
    apply integrable_gammaRectangle_of_bound hlt hwidth hPm 1
    intro p
    change ‖haarProfile a p.1 * haarProfile b p.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (abs_haarProfile_le_one ha p.1) (abs_haarProfile_le_one hb p.2)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hraw : Integrable (fun p : ℝ × ℝ =>
      (ENNReal.ofReal (archLevyDensity |p.2 - p.1|)).toReal • P p) μ := by
    rwa [gammaRectangleMeasure_eq_density hd,
      integrable_withDensity_iff_integrable_smul' measurable_gammaKernel
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hiR
  have hreal : (fun p : ℝ × ℝ =>
      (ENNReal.ofReal (archLevyDensity |p.2 - p.1|)).toReal • P p) =ᵐ[μ] H := by
    filter_upwards [hxy] with p hp
    rw [ENNReal.toReal_ofReal (archLevyDensity_pos (abs_pos.mpr hp.ne')).le]
    exact mul_comm _ _
  have hiH : Integrable H μ := hraw.congr hreal
  have hR : (∫ p, P p ∂gammaRectangleMeasure (L a) (U a) (L b) (U b)) =
      ∫ p, H p ∂μ := by
    rw [gammaRectangleMeasure_eq_density hd,
      integral_withDensity_eq_integral_toReal_smul measurable_gammaKernel
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact integral_congr_ae hreal
  have hFm (k : ℕ) : AEStronglyMeasurable (F k) μ := by
    apply Measurable.aestronglyMeasurable
    exact hPm.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_snd.sub measurable_fst)))
  have hbound (k : ℕ) : ∀ᵐ p ∂μ, ‖F k p‖ ≤ B k p := by
    apply ae_of_all
    intro p
    simp only [F, B, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), le_refl]
  have hBs : ∀ᵐ p ∂μ, HasSum (fun k => B k p) |H p| := by
    filter_upwards [hxy] with p hp
    have h := (ArchimedeanAnomaly.hasSum_archLevyDensity hp).mul_left |P p|
    simpa only [B, H, abs_mul, abs_of_pos hp,
      abs_of_pos (archLevyDensity_pos hp)] using h
  have hBi : Integrable (fun p => ∑' k, B k p) μ := by
    apply hiH.abs.congr
    filter_upwards [hBs] with p hp
    exact hp.tsum_eq.symm
  have hsum : ∀ᵐ p ∂μ, HasSum (fun k => F k p) (H p) := by
    filter_upwards [hxy] with p hp
    simpa only [F, H, abs_of_pos hp] using
      (ArchimedeanAnomaly.hasSum_archLevyDensity hp).mul_left (P p)
  have hs := hasSum_integral_of_dominated_convergence B hFm hbound
    (hBs.mono fun _ h => h.summable) hBi hsum
  have hterm (k : ℕ) : -(∫ p, F k p ∂μ) =
      haarLaplaceLeft a (2 * (k : ℝ) + 1 / 2) *
        haarLaplaceRight b (2 * (k : ℝ) + 1 / 2) := by
    let r : ℝ := 2 * (k : ℝ) + 1 / 2
    have he : F k = fun p : ℝ × ℝ =>
        (haarProfile a p.1 * Real.exp (r * p.1)) *
          (haarProfile b p.2 * Real.exp (-r * p.2)) := by
      funext p
      have hexp : Real.exp (-r * (p.2 - p.1)) =
          Real.exp (r * p.1) * Real.exp (-r * p.2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      change P p * Real.exp (-r * (p.2 - p.1)) = _
      rw [hexp]
      dsimp only [P]
      ring
    have hprod : (∫ p, F k p ∂μ) =
        (∫ x in Ioo (L a) (U a), haarProfile a x * Real.exp (r * x)) *
          (∫ x in Ioo (L b) (U b), haarProfile b x * Real.exp (-r * x)) := by
      rw [he]
      exact integral_prod_mul
        (fun x : ℝ => haarProfile a x * Real.exp (r * x))
        (fun y : ℝ => haarProfile b y * Real.exp (-r * y))
    rw [hprod, setIntegral_haarProfile_mul_eq ha,
      setIntegral_haarProfile_mul_eq hb]
    change -((∫ x, haarProfile a x * Real.exp (r * x)) *
        (∫ x, haarProfile b x * Real.exp (-r * x))) =
      (-(∫ x, haarProfile a x * Real.exp (r * x))) *
        (∫ x, haarProfile b x * Real.exp (-r * x))
    exact (neg_mul _ _).symm
  have hout : -(∫ p, H p ∂μ) = haarGammaCoupling a b := by
    rw [← hR]
    rfl
  simpa only [hterm, hout] using hs.neg

/-- All actual off-diagonal Haar Gamma entries are nonnegative. -/
theorem haarGammaCoupling_nonneg {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 ≤ haarGammaCoupling a b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [← (haarGammaCoupling_hasSum ha hab).tsum_eq]
    exact tsum_nonneg fun k => mul_nonneg (haarLaplaceLeft_nonneg ha (by positivity))
      (haarLaplaceRight_nonneg hb (by positivity))
  · rw [haarGammaCoupling_self]
  · rw [haarGammaCoupling_symm ha hb, ← (haarGammaCoupling_hasSum hb hba).tsum_eq]
    exact tsum_nonneg fun k => mul_nonneg (haarLaplaceLeft_nonneg hb (by positivity))
      (haarLaplaceRight_nonneg ha (by positivity))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
