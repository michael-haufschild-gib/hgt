import GaloisForLFunctions.RHTower.XiNodalPricedPolarizedDarkHistory
import GaloisForLFunctions.RHTower.XiSourceHistoryResidueTransgression

/-!
# Xi dark-history price escape

A fixed positive transverse response--price gap cannot coexist with norm-darkening at finite
expected price.  More sharply, the expected price must tend to infinity.  Applied to an actual
Xi zero, both the mixed nodal anomaly and the canonical repair-history defect therefore obey the
same law: off-critical analytic darkness can persist only by escaping every finite source-price
window.

This is stronger than bounded-price exclusion because any nondivergent price history already
forces criticality.  It is not an RH proof: the remaining producer must construct a positive
source history whose reciprocal response law and price nonescape are fixed before divisor
selection.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A norm-dark positive coalition with a fixed positive reciprocal response--price gap
must send its expected price to infinity. -/
theorem coalitional_darkHistory_positiveGap_forces_price_escape
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → Finset ι) (mu : ℕ → ι → ℝ) (a : ι → E) (price : ι → ℝ)
    (φ : E →L[ℝ] ℝ)
    {κ : ℝ}
    (hκ : 0 < κ)
    (hmu : ∀ n i, i ∈ F n → 0 ≤ mu n i)
    (hresponse : ∀ n i, i ∈ F n → 0 ≤ φ (a i))
    (hprice : ∀ n i, i ∈ F n → 0 ≤ price i)
    (hmass : ∀ n, ∑ i ∈ F n, mu n i = 1)
    (hdark : Tendsto
      (fun n => ‖∑ i ∈ F n, mu n i • a i‖) atTop (nhds 0))
    (hreciprocal : ∀ n i, i ∈ F n → κ ≤ φ (a i) * price i) :
    Tendsto (fun n => ∑ i ∈ F n, mu n i * price i) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  by_cases hM : M ≤ 0
  · exact Filter.Eventually.of_forall fun n =>
      hM.trans (Finset.sum_nonneg fun i hi =>
        mul_nonneg (hmu n i hi) (hprice n i hi))
  have hMpos : 0 < M := lt_of_not_ge hM
  have hlimit : Tendsto
      (fun n => ‖φ‖ * ‖∑ i ∈ F n, mu n i • a i‖ * M)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hdark).mul tendsto_const_nhds
  have hsmall : ∀ᶠ n in atTop,
      ‖φ‖ * ‖∑ i ∈ F n, mu n i • a i‖ * M < κ :=
    (tendsto_order.1 hlimit).2 κ hκ
  filter_upwards [hsmall] with n hn
  have huncertainty := coalitional_banach_reciprocal_pricing
    (F n) (mu n) a price φ (hmu n) (hresponse n) (hprice n)
    (hmass n) hκ.le (hreciprocal n)
  have hfactor : 0 ≤ ‖φ‖ * ‖∑ i ∈ F n, mu n i • a i‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  by_contra hcost
  have hcostLt : (∑ i ∈ F n, mu n i * price i) < M := lt_of_not_ge hcost
  have hupper :
      ‖φ‖ * ‖∑ i ∈ F n, mu n i • a i‖ *
          (∑ i ∈ F n, mu n i * price i) ≤
        ‖φ‖ * ‖∑ i ∈ F n, mu n i • a i‖ * M :=
    mul_le_mul_of_nonneg_left hcostLt.le hfactor
  exact (not_lt_of_ge huncertainty) (hupper.trans_lt hn)

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open GaloisForLFunctions
open ConstitutiveCriticalCompletionMechanics

/-- Every off-critical Xi dark history satisfying a fixed reciprocal response--price law
escapes to infinite expected source price. -/
theorem xiNodal_offLine_darkHistory_forces_price_escape
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : XiZeroCopy)
    (F : ℕ → Finset ι) (mu : ℕ → ι → ℝ) (a : ι → E) (price : ι → ℝ)
    (φ : E →L[ℝ] ℝ)
    (hoffLine : (q.1 : ℂ).re ≠ 1 / 2)
    (hmu : ∀ n i, i ∈ F n → 0 ≤ mu n i)
    (hresponse : ∀ n i, i ∈ F n → 0 ≤ φ (a i))
    (hprice : ∀ n i, i ∈ F n → 0 ≤ price i)
    (hmass : ∀ n, ∑ i ∈ F n, mu n i = 1)
    (hdark : Tendsto
      (fun n => ‖∑ i ∈ F n, mu n i • a i‖) atTop (nhds 0))
    (hreciprocal : ∀ n i, i ∈ F n →
      |primeDepthBVWoldXiCenteredRate q.1 * (q.1 : ℂ).im| ≤
        φ (a i) * price i) :
    Tendsto (fun n => ∑ i ∈ F n, mu n i * price i) atTop atTop := by
  have hgrade : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
    intro hzero
    exact hoffLine ((primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hzero)
  have hphase : (q.1 : ℂ).im ≠ 0 := xiSupport_im_ne_zero q.1
  have hmixed : primeDepthBVWoldXiCenteredRate q.1 * (q.1 : ℂ).im ≠ 0 :=
    mul_ne_zero hgrade hphase
  exact GaloisForLFunctions.HTGeometry.coalitional_darkHistory_positiveGap_forces_price_escape
    F mu a price φ (abs_pos.mpr hmixed) hmu hresponse hprice hmass hdark hreciprocal

/-- A closed Xi response with nonzero canonical repair-history holonomy can become norm-dark
only by sending reciprocal expected source price to infinity. -/
theorem xiRepairHistory_offLine_darkHistory_forces_price_escape
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : XiZeroCopy) (N clock : ℕ) (hclock : 2 ≤ clock)
    (F : ℕ → Finset ι) (mu : ℕ → ι → ℝ) (a : ι → E) (price : ι → ℝ)
    (φ : E →L[ℝ] ℝ)
    (hoffLine : (q.1 : ℂ).re ≠ 1 / 2)
    (hmu : ∀ n i, i ∈ F n → 0 ≤ mu n i)
    (hresponse : ∀ n i, i ∈ F n → 0 ≤ φ (a i))
    (hprice : ∀ n i, i ∈ F n → 0 ≤ price i)
    (hmass : ∀ n, ∑ i ∈ F n, mu n i = 1)
    (hdark : Tendsto
      (fun n => ‖∑ i ∈ F n, mu n i • a i‖) atTop (nhds 0))
    (hreciprocal : ∀ n i, i ∈ F n →
      |actualRepairOrientationPotential N clock q.1 (left (N + 1)) -
          actualRepairOrientationPotential N clock q.1 (right (N + 1))| ≤
        φ (a i) * price i) :
    Tendsto (fun n => ∑ i ∈ F n, mu n i * price i) atTop atTop := by
  have hdefect :
      actualRepairOrientationPotential N clock q.1 (left (N + 1)) -
          actualRepairOrientationPotential N clock q.1 (right (N + 1)) ≠ 0 := by
    intro hzero
    have herase : RepairProofErasureConsistent N
        (actualRepairOrientationPotential N clock q.1) :=
      (repairProofErasureConsistent_iff_repair_eq N _).2 (sub_eq_zero.mp hzero)
    exact hoffLine ((actualRepairProofErasureConsistent_iff_re_eq_half hclock q.1).1 herase)
  exact GaloisForLFunctions.HTGeometry.coalitional_darkHistory_positiveGap_forces_price_escape
    F mu a price φ (abs_pos.mpr hdefect) hmu hresponse hprice hmass hdark hreciprocal

/-- A nonescaping reciprocal-priced history falsifies nonzero canonical repair holonomy and
therefore places the Xi zero on the critical line. -/
theorem xiRepairHistory_re_eq_half_of_nondivergentPricedDarkHistory
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : XiZeroCopy) (N clock : ℕ) (hclock : 2 ≤ clock)
    (F : ℕ → Finset ι) (mu : ℕ → ι → ℝ) (a : ι → E) (price : ι → ℝ)
    (φ : E →L[ℝ] ℝ)
    (hmu : ∀ n i, i ∈ F n → 0 ≤ mu n i)
    (hresponse : ∀ n i, i ∈ F n → 0 ≤ φ (a i))
    (hprice : ∀ n i, i ∈ F n → 0 ≤ price i)
    (hmass : ∀ n, ∑ i ∈ F n, mu n i = 1)
    (hdark : Tendsto
      (fun n => ‖∑ i ∈ F n, mu n i • a i‖) atTop (nhds 0))
    (hreciprocal : ∀ n i, i ∈ F n →
      |actualRepairOrientationPotential N clock q.1 (left (N + 1)) -
          actualRepairOrientationPotential N clock q.1 (right (N + 1))| ≤
        φ (a i) * price i)
    (hnotEscape : ¬ Tendsto
      (fun n => ∑ i ∈ F n, mu n i * price i) atTop atTop) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoffLine
  exact hnotEscape (xiRepairHistory_offLine_darkHistory_forces_price_escape
    q N clock hclock F mu a price φ hoffLine hmu hresponse hprice hmass hdark hreciprocal)

/-- Nondivergence of one reciprocal-priced nodal dark history falsifies off-criticality. -/
theorem xiNodal_re_eq_half_of_nondivergentPricedPolarizedDarkHistory
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : XiZeroCopy)
    (F : ℕ → Finset ι) (mu : ℕ → ι → ℝ) (a : ι → E) (price : ι → ℝ)
    (φ : E →L[ℝ] ℝ)
    (hmu : ∀ n i, i ∈ F n → 0 ≤ mu n i)
    (hresponse : ∀ n i, i ∈ F n → 0 ≤ φ (a i))
    (hprice : ∀ n i, i ∈ F n → 0 ≤ price i)
    (hmass : ∀ n, ∑ i ∈ F n, mu n i = 1)
    (hdark : Tendsto
      (fun n => ‖∑ i ∈ F n, mu n i • a i‖) atTop (nhds 0))
    (hreciprocal : ∀ n i, i ∈ F n →
      |primeDepthBVWoldXiCenteredRate q.1 * (q.1 : ℂ).im| ≤
        φ (a i) * price i)
    (hnotEscape : ¬ Tendsto
      (fun n => ∑ i ∈ F n, mu n i * price i) atTop atTop) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoffLine
  exact hnotEscape (xiNodal_offLine_darkHistory_forces_price_escape
    q F mu a price φ hoffLine hmu hresponse hprice hmass hdark hreciprocal)

end

end RHTower
