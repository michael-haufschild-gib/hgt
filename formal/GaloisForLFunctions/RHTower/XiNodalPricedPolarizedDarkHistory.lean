import GaloisForLFunctions.HTGeometry.ConstitutiveCoalitionalAttainment
import GaloisForLFunctions.RHTower.XiNodalDefectSuperselection

/-!
# Bounded-price exclusion of source-bright Xi dark states

Analytic cancellation alone can hide a horizontal source defect.  This module gives a precise
condition under which it cannot: finite positive source packets become norm-dark while keeping
bounded expected source price, and one fixed polarized observer sees every active atom with
response-times-price at least a common gap.  Finite reciprocal pricing then forces that gap to
vanish.

For a Xi zero, choose the gap to be the absolute mixed nodal anomaly
`|(2 * re ρ - 1) * im ρ|`.  Since a nontrivial Xi zero has nonzero phase, the bounded-price dark
history forces neutral horizontal grade.  This is a falsifiable source criterion, not an RH proof:
an off-line Xi zero can satisfy it only by breaking positivity, bounded price, norm-darkness, or
the atomwise reciprocal lower bound.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Bounded-price dark-history law.** A positive finite coalition cannot become norm-dark at
bounded expected price while every active atom retains a fixed positive
response-times-price gap. -/
theorem coalitional_boundedPricedDarkHistory_forces_reciprocalGap_zero
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → Finset ι) (mu : ℕ → ι → ℝ) (a : ι → E) (price : ι → ℝ)
    (φ : E →L[ℝ] ℝ)
    {C κ : ℝ}
    (hκ : 0 ≤ κ)
    (hmu : ∀ n i, i ∈ F n → 0 ≤ mu n i)
    (hresponse : ∀ n i, i ∈ F n → 0 ≤ φ (a i))
    (hprice : ∀ n i, i ∈ F n → 0 ≤ price i)
    (hmass : ∀ n, ∑ i ∈ F n, mu n i = 1)
    (hcost : ∀ n, ∑ i ∈ F n, mu n i * price i ≤ C)
    (hdark : Tendsto
      (fun n => ‖∑ i ∈ F n, mu n i • a i‖) atTop (nhds 0))
    (hreciprocal : ∀ n i, i ∈ F n → κ ≤ φ (a i) * price i) :
    κ = 0 := by
  have hbound : ∀ n,
      κ ≤ ‖φ‖ * ‖∑ i ∈ F n, mu n i • a i‖ * C := by
    intro n
    have huncertainty := coalitional_banach_reciprocal_pricing
      (F n) (mu n) a price φ (hmu n) (hresponse n) (hprice n)
      (hmass n) hκ (hreciprocal n)
    have hfactor : 0 ≤ ‖φ‖ * ‖∑ i ∈ F n, mu n i • a i‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    exact huncertainty.trans (mul_le_mul_of_nonneg_left (hcost n) hfactor)
  have hlimit : Tendsto
      (fun n => ‖φ‖ * ‖∑ i ∈ F n, mu n i • a i‖ * C)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hdark).mul tendsto_const_nhds
  exact le_antisymm (ge_of_tendsto hlimit (Filter.Eventually.of_forall hbound)) hκ

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- A bounded-price positive polarized source history whose finite packets become norm-dark
forces one actual Xi zero onto the critical line.  The source data and observer are fixed across
the history; only finite support and weights may vary. -/
theorem xiNodal_re_eq_half_of_boundedPricedPolarizedDarkHistory
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : XiZeroCopy)
    (F : ℕ → Finset ι) (mu : ℕ → ι → ℝ) (a : ι → E) (price : ι → ℝ)
    (φ : E →L[ℝ] ℝ)
    {C : ℝ}
    (hmu : ∀ n i, i ∈ F n → 0 ≤ mu n i)
    (hresponse : ∀ n i, i ∈ F n → 0 ≤ φ (a i))
    (hprice : ∀ n i, i ∈ F n → 0 ≤ price i)
    (hmass : ∀ n, ∑ i ∈ F n, mu n i = 1)
    (hcost : ∀ n, ∑ i ∈ F n, mu n i * price i ≤ C)
    (hdark : Tendsto
      (fun n => ‖∑ i ∈ F n, mu n i • a i‖) atTop (nhds 0))
    (hreciprocal : ∀ n i, i ∈ F n →
      |primeDepthBVWoldXiCenteredRate q.1 * (q.1 : ℂ).im| ≤
        φ (a i) * price i) :
    (q.1 : ℂ).re = 1 / 2 := by
  have hgap :=
    GaloisForLFunctions.HTGeometry.coalitional_boundedPricedDarkHistory_forces_reciprocalGap_zero
      F mu a price φ (abs_nonneg _) hmu hresponse hprice hmass hcost hdark hreciprocal
  have hmixed : primeDepthBVWoldXiCenteredRate q.1 * (q.1 : ℂ).im = 0 :=
    abs_eq_zero.mp hgap
  have hphase : (q.1 : ℂ).im ≠ 0 := xiSupport_im_ne_zero q.1
  have hgrade : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
    (mul_eq_zero.mp hmixed).resolve_right hphase
  exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hgrade

end

end RHTower
