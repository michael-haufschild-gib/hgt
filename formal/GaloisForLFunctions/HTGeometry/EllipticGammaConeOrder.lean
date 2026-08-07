import Mathlib
import GaloisForLFunctions.HTGeometry.EllipticGammaConeCocycle

/-!
# The elliptic gamma function is nowhere locally zero

The zero set of an exponential cone product is countable — it is indexed by two natural numbers and
one integer — so the product cannot vanish identically on any neighbourhood, and its analytic order
is finite everywhere.  The same follows for the elliptic gamma function, a quotient of two such
products.

Finiteness of the order is what makes the orbital charge additive under multiplication of sources:
the additivity theorem needs orders that are not `⊤`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology Set

noncomputable section

/-- A countable subset of the plane is not everything. -/
theorem exists_notMem_of_countable {s : Set ℂ} (hs : s.Countable) : ∃ z : ℂ, z ∉ s := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have huniv : s = Set.univ := Set.eq_univ_of_forall hcon
  have hc : (Set.univ : Set ℂ).Countable := huniv ▸ hs
  refine Cardinal.not_countable_real ?_
  have hmap : (Set.univ : Set ℝ) ⊆ (fun z : ℂ => z.re) '' Set.univ := by
    intro x _
    exact ⟨(x : ℂ), Set.mem_univ _, by simp⟩
  exact Set.Countable.mono hmap (hc.image _)

/-- **An entire function with countable zero set is nowhere locally zero.** -/
theorem analyticOrderAt_ne_top_of_countable_zeroSet {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : {z : ℂ | f z = 0}.Countable) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := exists_notMem_of_countable hc
  have han : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf.analyticAt x
  refine han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ w) (Set.mem_univ z) ?_
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hw)]
  exact (by norm_num : (0 : ℕ∞) ≠ ⊤)

/-- A difference of finite orders is finite. -/
theorem withTop_sub_ne_top {x y : WithTop ℤ} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x - y ≠ ⊤ := by
  obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp hy
  have hsub : ((m : ℤ) : WithTop ℤ) - ((n : ℤ) : WithTop ℤ) = (((m - n : ℤ)) : WithTop ℤ) := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    rfl
  rw [hsub]
  exact WithTop.coe_ne_top

/-! ### Countability of the zero sets -/

/-- **The zero set of a cone product is countable.** -/
theorem countable_coneProduct_zeroSet {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) :
    {z : ℂ | coneProduct a b z = 0}.Countable := by
  have hsub : {z : ℂ | coneProduct a b z = 0}
      ⊆ Set.range (fun t : (ℕ × ℕ) × ℤ =>
        ((t.2 : ℂ)) - (t.1.1 : ℂ) * a - (t.1.2 : ℂ) * b) := by
    intro z hz
    obtain ⟨j, k, m, hm⟩ := (coneProduct_eq_zero_iff' ha hb z).mp hz
    refine ⟨((j, k), m), ?_⟩
    simp only
    linear_combination -hm
  exact Set.Countable.mono hsub (Set.countable_range _)

/-- The zero set of the numerator of the elliptic gamma function is countable. -/
theorem countable_ellipticGammaConeNum_zeroSet {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) :
    {w : ℂ | coneProduct a b (a + b - w) = 0}.Countable := by
  have hsub : {w : ℂ | coneProduct a b (a + b - w) = 0}
      ⊆ (fun z : ℂ => a + b - z) '' {z : ℂ | coneProduct a b z = 0} := by
    intro w hw
    exact ⟨a + b - w, hw, by ring⟩
  exact Set.Countable.mono hsub ((countable_coneProduct_zeroSet ha hb).image _)

/-! ### Finiteness of the orders -/

theorem meromorphicOrderAt_coneProduct_ne_top {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (z : ℂ) :
    meromorphicOrderAt (coneProduct a b) z ≠ ⊤ := by
  rw [((differentiable_coneProduct ha hb).analyticAt z).meromorphicOrderAt_eq]
  intro h
  exact analyticOrderAt_ne_top_of_countable_zeroSet (differentiable_coneProduct ha hb)
    (countable_coneProduct_zeroSet ha hb) z (by simpa using h)

theorem meromorphicOrderAt_ellipticGammaConeNum_ne_top {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (z : ℂ) : meromorphicOrderAt (fun w => coneProduct a b (a + b - w)) z ≠ ⊤ := by
  rw [((differentiable_ellipticGammaConeNum ha hb).analyticAt z).meromorphicOrderAt_eq]
  intro h
  exact analyticOrderAt_ne_top_of_countable_zeroSet (differentiable_ellipticGammaConeNum ha hb)
    (countable_ellipticGammaConeNum_zeroSet ha hb) z (by simpa using h)

/-- The elliptic gamma function is meromorphic on the plane. -/
theorem meromorphicOn_ellipticGammaCone {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) :
    MeromorphicOn (ellipticGammaCone a b) Set.univ := by
  intro z _
  exact (((differentiable_ellipticGammaConeNum ha hb).analyticAt z).meromorphicAt).div
    (((differentiable_coneProduct ha hb).analyticAt z).meromorphicAt)

/-- **The elliptic gamma function has finite order everywhere.** -/
theorem meromorphicOrderAt_ellipticGammaCone_ne_top {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (z : ℂ) : meromorphicOrderAt (ellipticGammaCone a b) z ≠ ⊤ := by
  have hnum : MeromorphicAt (fun w => coneProduct a b (a + b - w)) z :=
    ((differentiable_ellipticGammaConeNum ha hb).analyticAt z).meromorphicAt
  have hden : MeromorphicAt (coneProduct a b) z :=
    ((differentiable_coneProduct ha hb).analyticAt z).meromorphicAt
  rw [ellipticGammaCone, meromorphicOrderAt_div hnum hden]
  exact withTop_sub_ne_top (meromorphicOrderAt_ellipticGammaConeNum_ne_top ha hb z)
    (meromorphicOrderAt_coneProduct_ne_top ha hb z)

end

end GaloisForLFunctions.HTGeometry
