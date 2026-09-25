import GaloisForLFunctions.RHTower.RouteEQuotientParentDominance
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Moving-exponent signed quotient transport

The order-one parent capacity is not tied to a rational kernel.  For every
`r ≥ 1`, the literal parity-paired Gamma--Hankel quotient weight is a divided
difference of `x ↦ x^r` on a reciprocal interval.  Those intervals move left
as the quotient grows, so convexity makes every child no heavier relative to
its parent than at exponent one.  The strict order-one capacity therefore
survives at all receiver exponents `r ≥ 1`, and every finite coprime quotient
section has nonpositive signed weight.

This does not control noninteger primitive-ratio pairs or the full covariance.
-/

open Set Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem ordered_secant_rpow {r x y z w : ℝ}
    (hr : 1 ≤ r) (hx : 0 ≤ x) (hxy : x < y) (hyz : y ≤ z) (hzw : z < w) :
    (y ^ r - x ^ r) / (y - x) ≤ (w ^ r - z ^ r) / (w - z) := by
  have hconv := convexOn_rpow hr
  have hxmem : x ∈ Ici (0 : ℝ) := hx
  have hymem : y ∈ Ici (0 : ℝ) := by simp; linarith
  have hzmem : z ∈ Ici (0 : ℝ) := by simp; linarith
  have hwmem : w ∈ Ici (0 : ℝ) := by simp; linarith
  have h1 := hconv.secant_mono hxmem hymem hwmem (ne_of_gt hxy)
    (ne_of_gt (lt_of_lt_of_le hxy (hyz.trans hzw.le))) (by linarith : y ≤ w)
  have h2 := hconv.secant_mono hwmem hxmem hzmem (by linarith : x ≠ w)
    (by linarith : z ≠ w) (by linarith : x ≤ z)
  have h2' : (w ^ r - x ^ r) / (w - x) ≤ (w ^ r - z ^ r) / (w - z) := by
    calc
      (w ^ r - x ^ r) / (w - x) = (x ^ r - w ^ r) / (x - w) := by
        rw [show x ^ r - w ^ r = -(w ^ r - x ^ r) by ring,
          show x - w = -(w - x) by ring, neg_div_neg_eq]
      _ ≤ (z ^ r - w ^ r) / (z - w) := h2
      _ = (w ^ r - z ^ r) / (w - z) := by
        rw [show z ^ r - w ^ r = -(w ^ r - z ^ r) by ring,
          show z - w = -(w - z) by ring, neg_div_neg_eq]
  exact h1.trans h2'

/-- Divided reciprocal-power weight of one parity-paired quotient. -/
def quotientPowerEdgeWeight (r : ℝ) (q : ℕ) : ℝ :=
  (1 / ((q : ℝ) + 1)) ^ r - (1 / ((q : ℝ) + 2)) ^ r

/-- Child-to-parent weight ratio cannot increase when exponent moves above one. -/
theorem quotientPowerEdgeWeight_cross {r : ℝ} (hr : 1 ≤ r)
    {u v : ℕ} (huv : u < v) :
    quotientPowerEdgeWeight r v * quotientEdgeWeight u ≤
      quotientEdgeWeight v * quotientPowerEdgeWeight r u := by
  let xv : ℝ := 1 / ((v : ℝ) + 2)
  let yv : ℝ := 1 / ((v : ℝ) + 1)
  let xu : ℝ := 1 / ((u : ℝ) + 2)
  let yu : ℝ := 1 / ((u : ℝ) + 1)
  have hxv : 0 ≤ xv := by dsimp [xv]; positivity
  have hxyv : xv < yv := by
    dsimp [xv, yv]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hyv_xu : yv ≤ xu := by
    dsimp [yv, xu]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (Nat.add_le_add_right (Nat.succ_le_iff.mpr huv) 1)
  have hxyu : xu < yu := by
    dsimp [xu, yu]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hbasev : yv - xv = quotientEdgeWeight v := by
    dsimp [xv, yv, quotientEdgeWeight]
    have h1 : (0 : ℝ) < (v : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (v : ℝ) + 2 := by positivity
    field_simp
    ring
  have hbaseu : yu - xu = quotientEdgeWeight u := by
    dsimp [xu, yu, quotientEdgeWeight]
    have h1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (u : ℝ) + 2 := by positivity
    field_simp
    ring
  have hslope := ordered_secant_rpow hr hxv hxyv hyv_xu hxyu
  have hcross := (div_le_div_iff₀ (by linarith : 0 < yv - xv)
    (by linarith : 0 < yu - xu)).mp hslope
  rw [hbasev, hbaseu] at hcross
  dsimp [quotientPowerEdgeWeight, xv, yv, xu, yu] at *
  nlinarith [hcross]

theorem quotientPowerEdgeWeight_nonneg {r : ℝ} (hr : 1 ≤ r) (q : ℕ) :
    0 ≤ quotientPowerEdgeWeight r q := by
  have hq : 1 / ((q : ℝ) + 2) ≤ 1 / ((q : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  unfold quotientPowerEdgeWeight
  exact sub_nonneg.mpr (Real.rpow_le_rpow (by positivity) hq (by linarith))

/-- The strict order-one parent capacity persists at every real exponent `r ≥ 1`. -/
theorem quotientPowerEdgeWeight_parent_load
    {r : ℝ} (hr : 1 ≤ r) {u : ℕ} (hu : 3 ≤ u)
    (s : Finset ℕ) (hs : ∀ p ∈ s, 3 ≤ p ∧ ¬ 2 ∣ p) :
    quotientPowerEdgeWeight r (2 * u) +
        ∑ p ∈ s, quotientPowerEdgeWeight r (p * u) ≤
      (115 / 126 : ℝ) * quotientPowerEdgeWeight r u := by
  classical
  let t : Finset ℕ := {2} ∪ s
  have h2not : 2 ∉ s := by
    intro h2
    exact (hs 2 h2).2 (dvd_refl 2)
  have hbase : (∑ p ∈ t, quotientEdgeWeight (p * u)) ≤
      (115 / 126 : ℝ) * quotientEdgeWeight u := by
    simp only [t, Finset.singleton_union, Finset.sum_insert h2not]
    exact quotientEdgeWeight_parent_load_le hu s hs
  have hbasepos : 0 < quotientEdgeWeight u := by
    unfold quotientEdgeWeight
    positivity
  have hwrpos : 0 ≤ quotientPowerEdgeWeight r u := quotientPowerEdgeWeight_nonneg hr u
  have hcross : ∀ p ∈ t,
      quotientPowerEdgeWeight r (p * u) * quotientEdgeWeight u ≤
        quotientEdgeWeight (p * u) * quotientPowerEdgeWeight r u := by
    intro p hp
    have hp2 : 2 ≤ p := by
      rcases Finset.mem_union.mp hp with h | h
      · simp only [Finset.mem_singleton] at h
        omega
      · have hp3 := (hs p h).1
        omega
    apply quotientPowerEdgeWeight_cross hr
    nlinarith
  have hsum : (∑ p ∈ t, quotientPowerEdgeWeight r (p * u)) * quotientEdgeWeight u ≤
      (∑ p ∈ t, quotientEdgeWeight (p * u)) * quotientPowerEdgeWeight r u := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum hcross
  have hbound : (∑ p ∈ t, quotientEdgeWeight (p * u)) * quotientPowerEdgeWeight r u ≤
      ((115 / 126 : ℝ) * quotientEdgeWeight u) * quotientPowerEdgeWeight r u :=
    mul_le_mul_of_nonneg_right hbase hwrpos
  have hfinal : (∑ p ∈ t, quotientPowerEdgeWeight r (p * u)) ≤
      (115 / 126 : ℝ) * quotientPowerEdgeWeight r u := by
    refine le_of_mul_le_mul_right ?_ hbasepos
    nlinarith [hsum, hbound]
  have hsumunion : (∑ p ∈ t, quotientPowerEdgeWeight r (p * u)) =
      quotientPowerEdgeWeight r (2 * u) +
        ∑ p ∈ s, quotientPowerEdgeWeight r (p * u) := by
    simp only [t, Finset.singleton_union, Finset.sum_insert h2not]
  rw [hsumunion] at hfinal
  exact hfinal

theorem quotientPowerEdgeWeight_parent_load_le_self
    {r : ℝ} (hr : 1 ≤ r) {u : ℕ} (hu : 3 ≤ u)
    (s : Finset ℕ) (hs : ∀ p ∈ s, 3 ≤ p ∧ ¬ 2 ∣ p) :
    quotientPowerEdgeWeight r (2 * u) +
        ∑ p ∈ s, quotientPowerEdgeWeight r (p * u) ≤
      quotientPowerEdgeWeight r u := by
  have hload := quotientPowerEdgeWeight_parent_load hr hu s hs
  have hnonneg := quotientPowerEdgeWeight_nonneg hr u
  nlinarith

/-- Every coprime finite quotient section is nonpositive at every receiver exponent. -/
theorem signedQuotientPowerWeight_le_zero {r : ℝ} (hr : 1 ≤ r) (d Q : ℕ) :
    (∑ q ∈ (Finset.Icc 3 Q).filter (fun q => d.Coprime q),
      (moebius q : ℝ) * quotientPowerEdgeWeight r q) ≤ 0 :=
  signedQuotientWeight_le_zero_of_load (quotientPowerEdgeWeight r)
    (quotientPowerEdgeWeight_nonneg hr)
    (fun _u hu s hs => quotientPowerEdgeWeight_parent_load_le_self hr hu s hs) d Q

end
end RHTower
