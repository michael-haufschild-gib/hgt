import GaloisForLFunctions.RHTower.PaperCircleLocalEnergy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # One interval-energy anchor for a finite family of native circle symbols

The source density covering theorem is applied once to the aggregate squared norm.
Its good set consequently works for every channel and every complex linear combination.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL.Period

namespace RHTower
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Integrated energy of the whole native symbol family. -/
def paperCircleFamilyEnergy (a : ι → CCMCircleBoundedSymbol) : ℝ :=
  ∑ i, paperCircleSymbolEnergy (a i)

theorem paperCircleFamilyEnergy_nonneg (a : ι → CCMCircleBoundedSymbol) :
    0 ≤ paperCircleFamilyEnergy a :=
  Finset.sum_nonneg fun i _ => paperCircleSymbolEnergy_nonneg (a i)

private theorem integrableOn_symbolSquare (a : CCMCircleBoundedSymbol) (b c : ℝ) :
    IntegrableOn (fun x : ℝ => ‖a (x : AddCircle (1 : ℝ))‖ ^ 2) (Ico b c) := by
  refine seg_integrable _ ((a.measurable.comp AddCircle.measurable_mk').norm.pow_const 2)
    (a.bound ^ 2) b c (fun x _ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (a.norm_le _) 2

theorem integral_paperCircleFamilySquaredNorm (a : ι → CCMCircleBoundedSymbol) :
    (∫ x : ℝ, ∑ i, ‖a i (x : AddCircle (1 : ℝ))‖ ^ 2 ∂μ₁) =
      paperCircleFamilyEnergy a := by
  have hi (i : ι) : Integrable
      (fun x : ℝ => ‖a i (x : AddCircle (1 : ℝ))‖ ^ 2) μ₁ :=
    integrableOn_symbolSquare (a i) 0 1
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_paperCircleSymbolSquaredNorm, paperCircleFamilyEnergy]

/-- A single good set controls the sum of all channel energies on every local window. -/
theorem paperCircleFamilyEnergy_good_set (a : ι → CCMCircleBoundedSymbol) (D : ℝ≥0) :
    ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ Ico 0 1 ∧
      μ₁ Gᶜ ≤ ENNReal.ofReal (64 / ((D : ℝ) + 1)) ∧
      ∀ x ∈ G, ∀ (b s : ℝ), 0 < s → s ≤ 1 → x ∈ Ico b (b + s) →
        (∑ i, ∫ y in Ico b (b + s), ‖a i (y : AddCircle (1 : ℝ))‖ ^ 2) ≤
          ((D : ℝ) + 1) * s * (1 + paperCircleFamilyEnergy a) := by
  classical
  let C := 1 + paperCircleFamilyEnergy a
  have hC : 0 < C := by dsimp [C]; linarith [paperCircleFamilyEnergy_nonneg a]
  let ρ := fun x : ℝ => C⁻¹ * ∑ i, ‖a i (x : AddCircle (1 : ℝ))‖ ^ 2
  have hm : Measurable ρ := measurable_const.mul (Finset.measurable_sum _
    fun i _ => ((a i).measurable.comp AddCircle.measurable_mk').norm.pow_const 2)
  have hp : Function.Periodic ρ 1 := by
    intro x
    simp only [ρ, AddCircle.coe_add_period]
  have h0 (x : ℝ) : 0 ≤ ρ x := mul_nonneg (inv_nonneg.mpr hC.le)
    (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hb (x : ℝ) : ρ x ≤ C⁻¹ * ∑ i, (a i).bound ^ 2 := by
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) ((a i).norm_le _) 2) (inv_nonneg.mpr hC.le)
  have hi : (∫ x, ρ x ∂μ₁) ≤ 1 := by
    dsimp only [ρ]
    rw [integral_const_mul, integral_paperCircleFamilySquaredNorm, ← div_eq_inv_mul]
    exact (div_le_one hC).mpr (by dsimp [C]; linarith)
  obtain ⟨G, hG, hsub, hsize, hlocal⟩ :=
    density_good_set ρ hm hp h0 _ hb hi ((D : ℝ) + 1) (by positivity)
  refine ⟨G, hG, hsub, hsize, ?_⟩
  intro x hx b s hs hs1 hxs
  have h := hlocal x hx b s hs hs1 hxs
  dsimp only [ρ] at h
  rw [integral_const_mul, integral_finsetSum _
    (fun i _ => integrableOn_symbolSquare (a i) b (b + s))] at h
  have hh := mul_le_mul_of_nonneg_left h hC.le
  rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at hh
  simpa only [C, mul_assoc, mul_comm, mul_left_comm] using hh

/-- The common anchor is chosen before the channel and before the interval. -/
theorem paperCircleFamilyEnergy_good_anchor (a : ι → CCMCircleBoundedSymbol) :
    ∃ x ∈ Ico (0 : ℝ) 1, ∀ (b s : ℝ), 0 < s → s ≤ 1 → x ∈ Ico b (b + s) →
      (∑ i, ∫ y in Ico b (b + s), ‖a i (y : AddCircle (1 : ℝ))‖ ^ 2) ≤
        128 * s * (1 + paperCircleFamilyEnergy a) := by
  obtain ⟨G, _, hsub, hsize, hlocal⟩ := paperCircleFamilyEnergy_good_set a 127
  have hne : G.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => by
    rw [h, compl_empty, measure_univ] at hsize
    norm_num at hsize
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, hsub hx, ?_⟩
  norm_num at hlocal
  simpa only [mem_Ico, and_imp] using hlocal x hx

theorem paperCircleFamilyEnergy_good_anchor_each (a : ι → CCMCircleBoundedSymbol) :
    ∃ x ∈ Ico (0 : ℝ) 1, ∀ i (b s : ℝ), 0 < s → s ≤ 1 → x ∈ Ico b (b + s) →
      (∫ y in Ico b (b + s), ‖a i (y : AddCircle (1 : ℝ))‖ ^ 2) ≤
        128 * s * (1 + paperCircleFamilyEnergy a) := by
  obtain ⟨x, hx, h⟩ := paperCircleFamilyEnergy_good_anchor a
  refine ⟨x, hx, fun i b s hs hs1 hxs => ?_⟩
  exact (Finset.single_le_sum (fun j _ => integral_nonneg fun _ => sq_nonneg _)
    (Finset.mem_univ i)).trans (h b s hs hs1 hxs)

private theorem square_norm_sum_mul_le (c v : ι → ℂ) :
    ‖∑ i, c i * v i‖ ^ 2 ≤ (∑ i, ‖c i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  calc
    _ ≤ (∑ i, ‖c i‖ * ‖v i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by
        simpa only [norm_mul] using norm_sum_le Finset.univ (fun i => c i * v i)) 2
    _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun i _ => sq_nonneg _) (fun i _ => sq_nonneg _)
      (fun i _ => (mul_pow (‖c i‖) (‖v i‖) 2).le)

/-- The same anchor controls the entire complex span, with its squared coefficient norm. -/
theorem paperCircleFamilyEnergy_good_anchor_span (a : ι → CCMCircleBoundedSymbol) :
    ∃ x ∈ Ico (0 : ℝ) 1, ∀ (c : ι → ℂ) (b s : ℝ),
      0 < s → s ≤ 1 → x ∈ Ico b (b + s) →
      (∫ y in Ico b (b + s), ‖∑ i, c i * a i (y : AddCircle (1 : ℝ))‖ ^ 2) ≤
        (∑ i, ‖c i‖ ^ 2) * (128 * s * (1 + paperCircleFamilyEnergy a)) := by
  obtain ⟨x, hx, h⟩ := paperCircleFamilyEnergy_good_anchor a
  refine ⟨x, hx, fun c b s hs hs1 hxs => ?_⟩
  have hc : 0 ≤ ∑ i, ‖c i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm : Measurable (fun y : ℝ => ∑ i, c i * a i (y : AddCircle (1 : ℝ))) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul
      ((a i).measurable.comp AddCircle.measurable_mk')
  have hsum (y : ℝ) : ‖∑ i, c i * a i (y : AddCircle (1 : ℝ))‖ ≤
      ∑ i, ‖c i‖ * (a i).bound := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((a i).norm_le _) (norm_nonneg _)
  have hf := seg_integrable
    (fun y : ℝ => ‖∑ i, c i * a i (y : AddCircle (1 : ℝ))‖ ^ 2)
    (hm.norm.pow_const 2) ((∑ i, ‖c i‖ * (a i).bound) ^ 2) b (b + s) (fun y _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hsum y) 2)
  have hg := (integrable_finsetSum Finset.univ
    (fun i _ => integrableOn_symbolSquare (a i) b (b + s))).const_mul (∑ i, ‖c i‖ ^ 2)
  calc
    _ ≤ ∫ y in Ico b (b + s), (∑ i, ‖c i‖ ^ 2) *
        ∑ i, ‖a i (y : AddCircle (1 : ℝ))‖ ^ 2 :=
      integral_mono hf hg (fun y => square_norm_sum_mul_le c _)
    _ = (∑ i, ‖c i‖ ^ 2) *
        ∑ i, ∫ y in Ico b (b + s), ‖a i (y : AddCircle (1 : ℝ))‖ ^ 2 := by
      rw [integral_const_mul, integral_finsetSum _
        (fun i _ => integrableOn_symbolSquare (a i) b (b + s))]
    _ ≤ _ := mul_le_mul_of_nonneg_left (h b s hs hs1 hxs) hc

end
end RHTower
