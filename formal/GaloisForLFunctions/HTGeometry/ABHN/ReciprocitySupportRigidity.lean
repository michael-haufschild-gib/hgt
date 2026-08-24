import GaloisForLFunctions.HTGeometry.ABHN.HeterogeneousRatModIntReciprocity

/-!
# Support rigidity for heterogeneous reciprocity profiles

ABHN reciprocity is a cancellation law rather than independent placewise descent.  A singleton
profile is reciprocal precisely when its sole invariant vanishes; if the local invariant is
injective, the local class itself vanishes.  For two-place profiles, reciprocity says exactly that
the two local invariants are additive inverses.  Thus nontrivial reciprocal obstruction profiles
must occur in compensating packets of places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u v

/-- A singleton profile has zero global invariant exactly when its local invariant vanishes. -/
theorem heterogeneousRatModIntProfile_single_sum_eq_zero_iff
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (i : ι) (x : A i) :
    heterogeneousRatModIntProfileInvariantSumAddHom A inv (DFinsupp.single i x) = 0 ↔
      inv i x = 0 := by
  rw [heterogeneousRatModIntProfileInvariantSumAddHom_single]

/-- Kernel membership of a singleton profile is exactly vanishing of its local invariant. -/
theorem heterogeneousRatModIntProfile_single_mem_kernel_iff
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (i : ι) (x : A i) :
    DFinsupp.single i x ∈ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker ↔
      inv i x = 0 := by
  rw [AddMonoidHom.mem_ker, heterogeneousRatModIntProfileInvariantSumAddHom_single]

/-- At a place with injective local invariant, a reciprocal singleton profile is zero. -/
theorem heterogeneousRatModIntProfile_single_mem_kernel_iff_eq_zero
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (i : ι) (hinv : Function.Injective (inv i)) (x : A i) :
    DFinsupp.single i x ∈ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker ↔ x = 0 := by
  rw [heterogeneousRatModIntProfile_single_mem_kernel_iff]
  constructor
  · intro hx
    apply hinv
    simpa using hx
  · rintro rfl
    exact map_zero (inv i)

/-- A nonzero class at an injective place cannot by itself satisfy global reciprocity. -/
theorem heterogeneousRatModIntProfile_single_not_mem_kernel
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (i : ι) (hinv : Function.Injective (inv i))
    {x : A i} (hx : x ≠ 0) :
    DFinsupp.single i x ∉ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker := by
  rwa [heterogeneousRatModIntProfile_single_mem_kernel_iff_eq_zero A inv i hinv]

/-- A singleton product-one law is precisely vanishing of its one local invariant. -/
theorem heterogeneousRatModIntProfile_single_product_eq_one_iff
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (inv : ∀ i, A i →+ RatModInt) (i : ι) (x : A i) :
    (DFinsupp.single i x).prod (fun j y => ratModIntStdAddChar (inv j y)) = 1 ↔
      inv i x = 0 := by
  rw [heterogeneousRatModIntProfile_product_eq_one_iff_sum_eq_zero,
    heterogeneousRatModIntProfile_single_sum_eq_zero_iff]

/-- A two-place profile has zero global invariant exactly when its local invariants cancel. -/
theorem heterogeneousRatModIntProfile_pair_sum_eq_zero_iff
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (i j : ι) (x : A i) (y : A j) :
    heterogeneousRatModIntProfileInvariantSumAddHom A inv
        (DFinsupp.single i x + DFinsupp.single j y) = 0 ↔
      inv i x = -(inv j y) := by
  rw [map_add, heterogeneousRatModIntProfileInvariantSumAddHom_single,
    heterogeneousRatModIntProfileInvariantSumAddHom_single, add_eq_zero_iff_eq_neg]

/-- Kernel membership of a two-place profile is exactly cancellation of local invariants. -/
theorem heterogeneousRatModIntProfile_pair_mem_kernel_iff
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (i j : ι) (x : A i) (y : A j) :
    DFinsupp.single i x + DFinsupp.single j y ∈
        (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker ↔
      inv i x = -(inv j y) := by
  rw [AddMonoidHom.mem_ker, heterogeneousRatModIntProfile_pair_sum_eq_zero_iff]

/-- Product-one reciprocity for two places is exact cancellation of their local invariants. -/
theorem heterogeneousRatModIntProfile_pair_product_eq_one_iff
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (inv : ∀ i, A i →+ RatModInt) (i j : ι) (x : A i) (y : A j) :
    (DFinsupp.single i x + DFinsupp.single j y).prod
        (fun k z => ratModIntStdAddChar (inv k z)) = 1 ↔
      inv i x = -(inv j y) := by
  rw [heterogeneousRatModIntProfile_product_eq_one_iff_sum_eq_zero,
    heterogeneousRatModIntProfile_pair_sum_eq_zero_iff]

/-- Any reciprocal profile supported literally at one injective place is the zero profile. -/
theorem heterogeneousRatModIntProfile_eq_single_of_mem_kernel_imp_value_eq_zero
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (f : Π₀ i, A i) (i : ι)
    (hinv : Function.Injective (inv i)) (x : A i)
    (hf : f = DFinsupp.single i x)
    (hrecip : f ∈ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker) :
    x = 0 := by
  rw [hf] at hrecip
  exact (heterogeneousRatModIntProfile_single_mem_kernel_iff_eq_zero A inv i hinv x).mp hrecip

end

end GaloisForLFunctions.HTGeometry.ABHN
