import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechComplex

/-! Inserting a fixed index gives the Koszul homotopy for its weight. -/

noncomputable section

namespace GlobalTheory.WH

variable {k ι M : Type*} [CommRing k] [LinearOrder ι] [AddCommGroup M] [Module k M]

/-- Contract in the chosen index by inserting it with the deletion sign. -/
def koszulContraction (i : ι) : (Finset ι → M) →ₗ[k] (Finset ι → M) :=
  LinearMap.pi fun t => if i ∈ t then 0 else
    cubeSign (insert i t) i • LinearMap.proj (insert i t)

theorem koszulContraction_apply (i : ι) (a : Finset ι → M) (t : Finset ι) :
    koszulContraction (k := k) i a t = if i ∈ t then 0 else cubeSign (insert i t) i • a (insert i t) := by
  rw [koszulContraction, LinearMap.pi_apply]
  split_ifs <;> rfl

private theorem cubeSign_square (t : Finset ι) (i : ι) :
    cubeSign t i * cubeSign t i = 1 := by
  change (-1 : ℤ) ^ (t.filter (· < i)).card * (-1 : ℤ) ^ (t.filter (· < i)).card = 1
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

/-- The anticommutator of the differential and insertion is the chosen
weight acting on every coefficient. -/
theorem koszulContraction_wd (w : ι → Module.End k M) (i : ι) (a : Finset ι → M) :
    koszulContraction (k := k) i (wd w a) + wd w (koszulContraction (k := k) i a) =
      fun t => w i (a t) := by
  funext t
  rw [Pi.add_apply, koszulContraction_apply]
  by_cases hi : i ∈ t
  · rw [if_pos hi, zero_add, wd_apply, Finset.sum_eq_single_of_mem i hi]
    · rw [koszulContraction_apply, if_neg (Finset.notMem_erase _ _),
        Finset.insert_erase hi, map_zsmul, smul_smul, cubeSign_square, one_smul]
    · intro j _ hji
      rw [koszulContraction_apply, if_pos (Finset.mem_erase.mpr ⟨hji.symm, hi⟩),
        map_zero, smul_zero]
  · rw [if_neg hi, wd_apply, Finset.sum_insert hi, Finset.erase_insert hi,
      smul_add, smul_smul, cubeSign_square, one_smul, Finset.smul_sum, wd_apply, add_assoc,
      ← Finset.sum_add_distrib]
    suffices hsum : ∑ j ∈ t, (
        cubeSign (insert i t) i • cubeSign (insert i t) j • w j (a ((insert i t).erase j)) +
        cubeSign t j • w j (koszulContraction (k := k) i a (t.erase j))) = 0 by rw [hsum, add_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hji : j ≠ i := fun e => hi (e ▸ hj)
    have he : (insert i t).erase j = insert i (t.erase j) := Finset.erase_insert_of_ne hji.symm
    have hi' : i ∉ t.erase j := fun h => hi (Finset.mem_of_mem_erase h)
    have hsign := cubeSign_mul_erase (Finset.mem_insert_self i t) (Finset.mem_insert_of_mem hj) hji.symm
    rw [Finset.erase_insert hi, he] at hsign
    let a₁ := cubeSign (insert i t) i
    let b₁ := cubeSign (insert i t) j
    let a₀ := cubeSign t j
    let b₀ := cubeSign (insert i (t.erase j)) i
    have hsign' : a₁ * b₁ = -(a₀ * b₀) := by
      calc
        a₁ * b₁ = ((a₁ * a₀) * a₀) * b₁ := by
          rw [mul_assoc a₁ a₀ a₀, show a₀ * a₀ = 1 from cubeSign_square t j, mul_one]
        _ = (a₁ * a₀) * (a₀ * b₁) := mul_assoc _ _ _
        _ = -(b₁ * b₀) * (a₀ * b₁) :=
          congrArg (· * (a₀ * b₁)) hsign
        _ = -(a₀ * b₀) * (b₁ * b₁) := by ring
        _ = -(a₀ * b₀) := by
          rw [show b₁ * b₁ = 1 from cubeSign_square (insert i t) j, mul_one]
    rw [koszulContraction_apply, if_neg hi', he, map_zsmul, smul_smul, smul_smul,
      show cubeSign (insert i t) i * cubeSign (insert i t) j =
        -(cubeSign t j * cubeSign (insert i (t.erase j)) i) from hsign', neg_smul, neg_add_cancel]

/-- Inserting an index lowers the support degree by one. -/
theorem koszulContraction_support (i : ι) {a : Finset ι → M} {n : ℤ}
    (ha : ∀ t : Finset ι, (t.card : ℤ) ≠ n → a t = 0) (t : Finset ι)
    (ht : (t.card : ℤ) ≠ n - 1) : koszulContraction (k := k) i a t = 0 := by
  rw [koszulContraction_apply]
  split_ifs with hi
  · rfl
  · rw [ha _ (by rw [Finset.card_insert_of_notMem hi]; omega), smul_zero]

end GlobalTheory.WH
