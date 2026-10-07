import GaloisForLFunctions.HTGeometry.EntireOddDivisorSquareClass

/-!
# Finite entire packets detected by one odd divisor

Finite products of entire functions agree with products in the actual global
meromorphic field. An odd-order factor, with every remaining factor and an
arbitrary entire multiplier nonzero there, certifies the whole packet nonsquare.
-/

open Complex Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι : Type*} (f : ι → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i))

include hf in
theorem entire_finset_prod_differentiable (S : Finset ι) :
    Differentiable ℂ (fun z => ∏ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (differentiable_const (1 : ℂ))
  | @insert i S hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact (hf i).mul ih

theorem entire_finset_prod_element (S : Finset ι) :
    ofMeromorphic (fun z => ∏ i ∈ S, f i z)
      (fun z => ((entire_finset_prod_differentiable f hf S).analyticAt z).meromorphicAt) =
    ∏ i ∈ S, ofMeromorphic (f i) (fun z => ((hf i).analyticAt z).meromorphicAt) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    apply MeromorphicPlane.germ_injective
    simp only [Finset.prod_empty, germ_ofMeromorphic, germ_one]
    rfl
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, ← ih, ofMeromorphic_mul]
    apply MeromorphicPlane.germ_injective
    rw [germ_ofMeromorphic, germ_ofMeromorphic]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by simp only [Finset.prod_insert hi, Pi.mul_apply]

/-- Isolating one odd divisor certifies a complete finite product is nonsquare. -/
theorem entire_packet_not_isSquare_of_odd_factor {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (S : Finset ι) {i : ι} (hi : i ∈ S) {z : ℂ}
    (hodd : Odd (analyticOrderAt (f i) z).toNat) (hg0 : g z ≠ 0)
    (hothers : ∀ j ∈ S, j ≠ i → f j z ≠ 0) :
    ¬ IsSquare (ofMeromorphic g (fun z => (hg.analyticAt z).meromorphicAt) *
      ∏ j ∈ S, ofMeromorphic (f j) (fun z => ((hf j).analyticAt z).meromorphicAt)) := by
  classical
  have hunit : g z * (∏ j ∈ S.erase i, f j z) ≠ 0 :=
    mul_ne_zero hg0 (Finset.prod_ne_zero_iff.mpr fun j hj =>
      hothers j (Finset.mem_of_mem_erase hj) (Finset.mem_erase.mp hj).1)
  have hp := not_isSquare_plane_mul_of_odd_order (hf i)
    (hg.mul (entire_finset_prod_differentiable f hf (S.erase i))) hodd hunit
  change ¬ IsSquare (ofMeromorphic (f i) (fun z => ((hf i).analyticAt z).meromorphicAt) *
    (ofMeromorphic g (fun z => (hg.analyticAt z).meromorphicAt) *
      ofMeromorphic (fun z => ∏ j ∈ S.erase i, f j z)
        (fun z => ((entire_finset_prod_differentiable f hf (S.erase i)).analyticAt z).meromorphicAt))) at hp
  rw [entire_finset_prod_element f hf] at hp
  have he : ofMeromorphic g (fun z => (hg.analyticAt z).meromorphicAt) *
      ∏ j ∈ S, ofMeromorphic (f j) (fun z => ((hf j).analyticAt z).meromorphicAt) =
    ofMeromorphic (f i) (fun z => ((hf i).analyticAt z).meromorphicAt) *
      (ofMeromorphic g (fun z => (hg.analyticAt z).meromorphicAt) *
        ∏ j ∈ S.erase i, ofMeromorphic (f j) (fun z => ((hf j).analyticAt z).meromorphicAt)) := by
    rw [← Finset.mul_prod_erase S (fun j => ofMeromorphic (f j)
      (fun z => ((hf j).analyticAt z).meromorphicAt)) hi]
    ring
  rw [he]
  exact hp

end
end GaloisForLFunctions.HTGeometry
