import GaloisForLFunctions.RHTower.WeilLogShiftCouplingOperations
import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalIndexTransport

/-! The explicit diagonal-plus-adjacent coupling between ordered mixture parameters. -/

open scoped BigOperators NNReal

noncomputable section
namespace RHTower

def finiteWeilCanonicalMixtureNNProfile (r k : ℕ) (a : Set.Icc (0 : ℝ) 1)
    (u : Fin (r + 2)) : ℝ≥0 :=
  NNReal.mk (finiteWeilCanonicalMixture r k a u)
    ((finiteWeilCanonicalMixture_nonneg_iff r k a).mpr a.property u)

theorem finiteWeilCanonicalMixtureNNProfile_apply (r k : ℕ) (a : Set.Icc (0 : ℝ) 1)
    (u : Fin (r + 2)) :
    (finiteWeilCanonicalMixtureNNProfile r k a u : ℝ) = finiteWeilCanonicalMixture r k a u := rfl

theorem finiteWeilCanonicalMixtureNNProfile_sum (r k : ℕ) (a : Set.Icc (0 : ℝ) 1) :
    (∑ u, finiteWeilCanonicalMixtureNNProfile r k a u) = 1 := by
  apply NNReal.coe_injective
  simpa only [NNReal.coe_sum, finiteWeilCanonicalMixtureNNProfile_apply, NNReal.coe_one] using
    (finiteWeilCanonicalMixture_mem r k a a.property.1 a.property.2).2.1

def finiteWeilOrientedMixturePlan (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (u v : Fin (r + 2)) : ℝ :=
  (if u = v then (b : ℝ) * finiteWeilCanonicalPositiveProfile r k u +
    (1 - (a : ℝ)) * finiteWeilCanonicalNegativeProfile r k u else 0) +
      ((a : ℝ) - (b : ℝ)) * finiteWeilCanonicalEdgePlan r k u v

theorem finiteWeilOrientedMixturePlan_nonneg (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (hba : (b : ℝ) ≤ (a : ℝ)) (u v : Fin (r + 2)) :
    0 ≤ finiteWeilOrientedMixturePlan r k a b u v := by
  unfold finiteWeilOrientedMixturePlan
  apply add_nonneg
  · split_ifs
    · exact add_nonneg
        (mul_nonneg b.property.1 ((finiteWeilCanonicalProfiles_spec r k).1 u).1)
        (mul_nonneg (sub_nonneg.mpr a.property.2) ((finiteWeilCanonicalProfiles_spec r k).1 u).2.1)
    · exact le_rfl
  · exact mul_nonneg (sub_nonneg.mpr hba) (finiteWeilCanonicalEdgePlan_nonneg r k u v)

theorem finiteWeilOrientedMixturePlan_marginals (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (u : Fin (r + 2)) :
    (∑ v, finiteWeilOrientedMixturePlan r k a b u v) = finiteWeilCanonicalMixture r k a u ∧
      (∑ v, finiteWeilOrientedMixturePlan r k a b v u) = finiteWeilCanonicalMixture r k b u := by
  constructor
  · simp only [finiteWeilOrientedMixturePlan, Finset.sum_add_distrib, ← Finset.mul_sum,
      (finiteWeilCanonicalEdgePlan_marginals r k u).1]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, finiteWeilCanonicalMixture]
    ring
  · simp only [finiteWeilOrientedMixturePlan, Finset.sum_add_distrib, ← Finset.mul_sum,
      (finiteWeilCanonicalEdgePlan_marginals r k u).2]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, finiteWeilCanonicalMixture]
    ring

def finiteWeilOrientedMixtureCoupling (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (hba : (b : ℝ) ≤ (a : ℝ)) :
    HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b) where
  plan u v := NNReal.mk (finiteWeilOrientedMixturePlan r k a b u v)
    (finiteWeilOrientedMixturePlan_nonneg r k a b hba u v)
  row u := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, NNReal.coe_mk, finiteWeilCanonicalMixtureNNProfile] using
      (finiteWeilOrientedMixturePlan_marginals r k a b u).1
  col u := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, NNReal.coe_mk, finiteWeilCanonicalMixtureNNProfile] using
      (finiteWeilOrientedMixturePlan_marginals r k a b u).2

theorem finiteWeilOrientedMixtureCoupling_apply (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (hba : (b : ℝ) ≤ (a : ℝ)) (u v : Fin (r + 2)) :
    ((finiteWeilOrientedMixtureCoupling r k a b hba).plan u v : ℝ) =
      finiteWeilOrientedMixturePlan r k a b u v := rfl

theorem finiteWeilOrientedMixtureCoupling_cost_eq (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (hba : (b : ℝ) ≤ (a : ℝ)) (c : Fin (r + 2) → Fin (r + 2) → ℝ) (hc : ∀ u, c u u = 0) :
    finiteWeilCouplingCost (finiteWeilOrientedMixtureCoupling r k a b hba) c =
      ((a : ℝ) - (b : ℝ)) * finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) c := by
  have hd (u : Fin (r + 2)) :
      (∑ v, (if u = v then (b : ℝ) * finiteWeilCanonicalPositiveProfile r k u +
          (1 - (a : ℝ)) * finiteWeilCanonicalNegativeProfile r k u else 0) * c u v) = 0 := by
    simp [ite_mul, hc]
  change (∑ u, ∑ v, finiteWeilOrientedMixturePlan r k a b u v * c u v) =
    ((a : ℝ) - (b : ℝ)) * (∑ u, ∑ v, finiteWeilCanonicalEdgePlan r k u v * c u v)
  simp only [finiteWeilOrientedMixturePlan, add_mul, Finset.sum_add_distrib, hd, zero_add,
    mul_assoc, ← Finset.mul_sum]

theorem finiteWeilCanonicalMixtureNNProfile_pairing (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (f : Fin (r + 2) → ℝ) :
    (∑ u, (finiteWeilCanonicalMixtureNNProfile r k a u : ℝ) * f u) -
      (∑ u, (finiteWeilCanonicalMixtureNNProfile r k b u : ℝ) * f u) =
      ((a : ℝ) - (b : ℝ)) *
        ((∑ u, (finiteWeilCanonicalPositiveNNProfile r k u : ℝ) * f u) -
          (∑ u, (finiteWeilCanonicalNegativeNNProfile r k u : ℝ) * f u)) := by
  change (∑ u, finiteWeilCanonicalMixture r k a u * f u) -
      (∑ u, finiteWeilCanonicalMixture r k b u * f u) =
    ((a : ℝ) - (b : ℝ)) *
      ((∑ u, finiteWeilCanonicalPositiveProfile r k u * f u) -
        (∑ u, finiteWeilCanonicalNegativeProfile r k u * f u))
  calc
    _ = ∑ u, (finiteWeilCanonicalMixture r k a u - finiteWeilCanonicalMixture r k b u) * f u := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ = ∑ u, ((a : ℝ) - (b : ℝ)) *
        ((finiteWeilCanonicalPositiveProfile r k u - finiteWeilCanonicalNegativeProfile r k u) * f u) := by
      simp only [finiteWeilCanonicalMixture_difference, mul_assoc]
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [sub_mul, Finset.sum_sub_distrib]

end RHTower
