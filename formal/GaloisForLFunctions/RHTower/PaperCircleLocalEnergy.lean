import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Fourier.Interval
import GaloisForLFunctions.RHTower.CCMArchimedeanCircleTraceCocycle

/-!
# One good set for every local energy window of a native circle symbol

Apply the paper's interval-density estimate to the literal squared modulus of a
`CCMCircleBoundedSymbol`, normalized by one plus its integrated energy. The resulting
constant uses integrated energy; the stored supremum bound pays admissibility only.
-/

namespace RHTower

noncomputable section

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry.FourierLLogL.Period
open scoped ENNReal NNReal

/-- Integrated squared modulus in the native normalized circle measure. -/
def paperCircleSymbolEnergy (a : CCMCircleBoundedSymbol) : ℝ :=
  ∫ y : AddCircle (1 : ℝ), ‖a y‖ ^ 2 ∂AddCircle.haarAddCircle

theorem integrable_paperCircleSymbolSquaredNorm (a : CCMCircleBoundedSymbol) :
    Integrable (fun y : AddCircle (1 : ℝ) => ‖a y‖ ^ 2) AddCircle.haarAddCircle := by
  refine Integrable.of_bound (a.measurable.norm.pow_const 2).aestronglyMeasurable
    (a.bound ^ 2) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (a.norm_le y) 2

theorem paperCircleSymbolEnergy_nonneg (a : CCMCircleBoundedSymbol) :
    0 ≤ paperCircleSymbolEnergy a := integral_nonneg fun _ => sq_nonneg _

private theorem unitCircle_map_volume :
    Measure.map ((↑) : ℝ → AddCircle (1 : ℝ)) μ₁ = AddCircle.haarAddCircle := by
  change Measure.map _ (volume.restrict (Ico (0 : ℝ) 1)) = _
  rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
  simpa only [zero_add, AddCircle.volume_eq_smul_haarAddCircle,
    ENNReal.ofReal_one, one_smul] using (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq

/-- The real period cell computes exactly the native circle energy. -/
theorem integral_paperCircleSymbolSquaredNorm (a : CCMCircleBoundedSymbol) :
    (∫ x : ℝ, ‖a (x : AddCircle (1 : ℝ))‖ ^ 2 ∂μ₁) = paperCircleSymbolEnergy a := by
  unfold paperCircleSymbolEnergy
  rw [← unitCircle_map_volume]
  exact (integral_map AddCircle.measurable_mk'.aemeasurable
    (a.measurable.norm.pow_const 2).aestronglyMeasurable).symm

/-- A source-admissible density, including when the symbol has zero energy. -/
def paperCircleSymbolDensity (a : CCMCircleBoundedSymbol) (x : ℝ) : ℝ :=
  (1 + paperCircleSymbolEnergy a)⁻¹ * ‖a (x : AddCircle (1 : ℝ))‖ ^ 2

theorem measurable_paperCircleSymbolDensity (a : CCMCircleBoundedSymbol) :
    Measurable (paperCircleSymbolDensity a) :=
  measurable_const.mul ((a.measurable.comp AddCircle.measurable_mk').norm.pow_const 2)

theorem periodic_paperCircleSymbolDensity (a : CCMCircleBoundedSymbol) :
    Function.Periodic (paperCircleSymbolDensity a) 1 := by
  intro x
  simp only [paperCircleSymbolDensity, AddCircle.coe_add_period]

theorem paperCircleSymbolDensity_nonneg (a : CCMCircleBoundedSymbol) (x : ℝ) :
    0 ≤ paperCircleSymbolDensity a x := by
  unfold paperCircleSymbolDensity
  exact mul_nonneg (inv_nonneg.mpr (by linarith [paperCircleSymbolEnergy_nonneg a]))
    (sq_nonneg _)

theorem paperCircleSymbolDensity_le (a : CCMCircleBoundedSymbol) (x : ℝ) :
    paperCircleSymbolDensity a x ≤ (1 + paperCircleSymbolEnergy a)⁻¹ * a.bound ^ 2 := by
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (a.norm_le _) 2)
  exact inv_nonneg.mpr (by linarith [paperCircleSymbolEnergy_nonneg a])

theorem integral_paperCircleSymbolDensity_le_one (a : CCMCircleBoundedSymbol) :
    (∫ x, paperCircleSymbolDensity a x ∂μ₁) ≤ 1 := by
  unfold paperCircleSymbolDensity
  rw [integral_const_mul, integral_paperCircleSymbolSquaredNorm, ← div_eq_inv_mul]
  exact (div_le_one (by linarith [paperCircleSymbolEnergy_nonneg a])).mpr (by linarith)

/-- One exceptional-set budget controls every offset and every subperiod window. -/
theorem paperCircleSymbolEnergy_good_set (a : CCMCircleBoundedSymbol) (D : ℝ≥0) :
    ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ Ico 0 1 ∧
      μ₁ Gᶜ ≤ ENNReal.ofReal (64 / ((D : ℝ) + 1)) ∧
      ∀ x ∈ G, ∀ (b s : ℝ), 0 < s → s ≤ 1 → x ∈ Ico b (b + s) →
        (∫ y in Ico b (b + s), ‖a (y : AddCircle (1 : ℝ))‖ ^ 2) ≤
          ((D : ℝ) + 1) * s * (1 + paperCircleSymbolEnergy a) := by
  obtain ⟨G, hG, hsub, hsize, hlocal⟩ := density_good_set
    (paperCircleSymbolDensity a) (measurable_paperCircleSymbolDensity a)
    (periodic_paperCircleSymbolDensity a) (paperCircleSymbolDensity_nonneg a)
    _ (paperCircleSymbolDensity_le a) (integral_paperCircleSymbolDensity_le_one a)
    ((D : ℝ) + 1) (by positivity)
  refine ⟨G, hG, hsub, hsize, ?_⟩
  intro x hx b s hs hs1 hxs
  have h := hlocal x hx b s hs hs1 hxs
  have hE : 0 < 1 + paperCircleSymbolEnergy a := by
    linarith [paperCircleSymbolEnergy_nonneg a]
  simp only [paperCircleSymbolDensity, integral_const_mul] at h
  have hh := mul_le_mul_of_nonneg_left h hE.le
  rw [← mul_assoc, mul_inv_cancel₀ hE.ne', one_mul] at hh
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hh

/-- Every native symbol has an anchor at which all local windows obey an energy-only bound. -/
theorem paperCircleSymbolEnergy_good_anchor (a : CCMCircleBoundedSymbol) :
    ∃ x ∈ Ico (0 : ℝ) 1, ∀ (b s : ℝ), 0 < s → s ≤ 1 → x ∈ Ico b (b + s) →
      (∫ y in Ico b (b + s), ‖a (y : AddCircle (1 : ℝ))‖ ^ 2) ≤
        128 * s * (1 + paperCircleSymbolEnergy a) := by
  obtain ⟨G, _, hsub, hsize, hlocal⟩ := paperCircleSymbolEnergy_good_set a 127
  have hne : G.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => by
    rw [h, compl_empty, measure_univ] at hsize
    norm_num at hsize
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, hsub hx, ?_⟩
  norm_num at hlocal
  simpa only [mem_Ico, and_imp] using hlocal x hx

end

end RHTower
