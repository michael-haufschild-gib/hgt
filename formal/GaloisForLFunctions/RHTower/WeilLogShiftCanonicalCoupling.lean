import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalEdgePlan
import GaloisForLFunctions.HTGeometry.ConstitutiveHierarchicalMaximalCoupling

/-! The canonical adjacent plan is a coupling in the corpus's finite nonnegative representation. -/

open scoped BigOperators NNReal

noncomputable section
namespace RHTower

def finiteWeilCanonicalPositiveNNProfile (r k : ℕ) (u : Fin (r + 2)) : ℝ≥0 :=
  NNReal.mk (finiteWeilCanonicalPositiveProfile r k u) ((finiteWeilCanonicalProfiles_spec r k).1 u).1

def finiteWeilCanonicalNegativeNNProfile (r k : ℕ) (u : Fin (r + 2)) : ℝ≥0 :=
  NNReal.mk (finiteWeilCanonicalNegativeProfile r k u) ((finiteWeilCanonicalProfiles_spec r k).1 u).2.1

theorem finiteWeilCanonicalPositiveNNProfile_mass (r k : ℕ) :
    (∑ u, finiteWeilCanonicalPositiveNNProfile r k u) = 1 := by
  apply NNReal.coe_injective
  simpa [finiteWeilCanonicalPositiveNNProfile, NNReal.coe_sum] using
    (finiteWeilCanonicalProfiles_spec r k).2.1

theorem finiteWeilCanonicalNegativeNNProfile_mass (r k : ℕ) :
    (∑ u, finiteWeilCanonicalNegativeNNProfile r k u) = 1 := by
  apply NNReal.coe_injective
  simpa [finiteWeilCanonicalNegativeNNProfile, NNReal.coe_sum] using
    (finiteWeilCanonicalProfiles_spec r k).2.2.1

def finiteWeilCanonicalCoupling (r k : ℕ) :
    HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k) where
  plan u v := NNReal.mk (finiteWeilCanonicalEdgePlan r k u v) (finiteWeilCanonicalEdgePlan_nonneg r k u v)
  row u := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, NNReal.coe_mk, finiteWeilCanonicalPositiveNNProfile] using
      (finiteWeilCanonicalEdgePlan_marginals r k u).1
  col v := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, NNReal.coe_mk, finiteWeilCanonicalNegativeNNProfile] using
      (finiteWeilCanonicalEdgePlan_marginals r k v).2

theorem finiteWeilCanonicalCoupling_apply (r k : ℕ) (u v : Fin (r + 2)) :
    ((finiteWeilCanonicalCoupling r k).plan u v : ℝ) = finiteWeilCanonicalEdgePlan r k u v := rfl

theorem finiteWeilCanonicalCoupling_zero_of_nonadjacent (r k : ℕ) (u v : Fin (r + 2))
    (huv : (u : ℕ) + 1 ≠ (v : ℕ)) (hvu : (v : ℕ) + 1 ≠ (u : ℕ)) :
    (finiteWeilCanonicalCoupling r k).plan u v = 0 := by
  apply NNReal.coe_injective
  exact finiteWeilCanonicalEdgePlan_zero_of_nonadjacent r k u v huv hvu

theorem finiteWeilCanonicalCoupling_diagonal (r k : ℕ) (u : Fin (r + 2)) :
    (finiteWeilCanonicalCoupling r k).plan u u = 0 := by
  apply NNReal.coe_injective
  exact finiteWeilCanonicalEdgePlan_diagonal r k u

end RHTower
