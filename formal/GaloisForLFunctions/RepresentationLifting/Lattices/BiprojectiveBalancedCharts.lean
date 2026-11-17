import GaloisForLFunctions.RepresentationLifting.Lattices.PrimitivePadicBilinearReduction

/-!
# Affine and boundary charts of balanced biprojective systems

When all diagonal products in two nonzero projective blocks agree, either
both blocks normalize in the same affine chart, or they have disjoint support
and normalize in an ordered pair of distinct coordinates. This gives an exact
cover for arbitrary additional bilinear equations, including their primitive
p-adic reductions.

The affine/boundary mechanism of Yang et al., arXiv:2611.21188, Section 2.4,
therefore requires the boundary charts after reduction: the balanced pair
`(1,p),(p,1)` specializes there despite its nonzero common p-adic product.
The precise dividing condition is whether that product remains nonzero in
the residue field. No numerical nonexistence certificate is assumed.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.BalancedCharts
open PrimitiveReduction
variable {K ι τ : Type*} [Field K] [Fintype ι]

/-- Independent projective normalization of one coordinate block. -/
def normalize (x : ι → K) (i : ι) : ι → K := fun k => (x i)⁻¹ * x k

omit [Fintype ι] in
theorem normalize_self (x : ι → K) (i : ι) (hi : x i ≠ 0) : normalize x i i = 1 :=
  inv_mul_cancel₀ hi

theorem normalize_pairing (A : ι → ι → K) (x y : ι → K) (i j : ι) :
    pairing A (normalize x i) (normalize y j) = (x i)⁻¹ * (y j)⁻¹ * pairing A x y :=
  pairing_scale A x y _ _

omit [Fintype ι] in
theorem normalize_product (x y : ι → K) (i j k : ι) :
    normalize x i k * normalize y j k = ((x i)⁻¹ * (y j)⁻¹) * (x k * y k) := by
  simp only [normalize]
  ring

/-- The affine chart of a balanced bilinear system has all diagonal products equal to one. -/
def AffineSolution (A : τ → ι → ι → K) (i₀ : ι) : Prop :=
  ∃ x y : ι → K, x i₀ = 1 ∧ y i₀ = 1 ∧
    (∀ i, x i * y i = 1) ∧ ∀ t, pairing (A t) x y = 0

/-- Boundary charts normalize two distinct coordinates in the two projective blocks. -/
def BoundarySolution (A : τ → ι → ι → K) (i j : ι) : Prop :=
  ∃ x y : ι → K, x i = 1 ∧ y j = 1 ∧ x j = 0 ∧ y i = 0 ∧
    (∀ k, x k * y k = 0) ∧ ∀ t, pairing (A t) x y = 0

omit [Fintype ι] in
private theorem nonzero_of_coordinate_one {x : ι → K} {i : ι} (hi : x i = 1) : x ≠ 0 := by
  intro h
  exact one_ne_zero (hi.symm.trans (congrFun h i))

/-- The affine chart and ordered off-diagonal boundary charts cover every balanced biprojective solution. -/
theorem solution_iff_affine_or_boundary (A : τ → ι → ι → K) (i₀ : ι) :
    (∃ x y : ι → K, x ≠ 0 ∧ y ≠ 0 ∧
      (∀ i, x i * y i = x i₀ * y i₀) ∧ ∀ t, pairing (A t) x y = 0) ↔
    AffineSolution A i₀ ∨ ∃ i j : ι, i ≠ j ∧ BoundarySolution A i j := by
  constructor
  · rintro ⟨x, y, hx, hy, hdiag, hA⟩
    by_cases hc : x i₀ * y i₀ = 0
    · right
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (funext h)
      obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
        by_contra h
        push Not at h
        exact hy (funext h)
      have hz (k : ι) : x k * y k = 0 := (hdiag k).trans hc
      have hxi : y i = 0 := (mul_eq_zero.mp (hz i)).resolve_left hi
      have hyj : x j = 0 := (mul_eq_zero.mp (hz j)).resolve_right hj
      have hij : i ≠ j := by
        intro h
        apply hi
        rw [h]
        exact hyj
      refine ⟨i, j, hij, normalize x i, normalize y j, normalize_self x i hi,
        normalize_self y j hj, ?_, ?_, ?_, ?_⟩
      · simp only [normalize, hyj, mul_zero]
      · simp only [normalize, hxi, mul_zero]
      · intro k
        rw [normalize_product, hz, mul_zero]
      · intro t
        rw [normalize_pairing, hA, mul_zero]
    · left
      have hxi : x i₀ ≠ 0 := (mul_ne_zero_iff.mp hc).1
      have hyi : y i₀ ≠ 0 := (mul_ne_zero_iff.mp hc).2
      refine ⟨normalize x i₀, normalize y i₀, normalize_self x i₀ hxi,
        normalize_self y i₀ hyi, ?_, ?_⟩
      · intro k
        rw [normalize_product, hdiag, ← mul_inv, inv_mul_cancel₀ hc]
      · intro t
        rw [normalize_pairing, hA, mul_zero]
  · rintro (⟨x, y, hx, hy, hdiag, hA⟩ | ⟨i, j, _, x, y, hx, hy, _, _, hdiag, hA⟩)
    · exact ⟨x, y, nonzero_of_coordinate_one hx, nonzero_of_coordinate_one hy,
        fun k => (hdiag k).trans (hdiag i₀).symm, hA⟩
    · exact ⟨x, y, nonzero_of_coordinate_one hx, nonzero_of_coordinate_one hy,
        fun k => (hdiag k).trans (hdiag i₀).symm, hA⟩

omit [Fintype ι] in
/-- Boundary points have disjoint coordinate support in the two projective blocks. -/
theorem boundary_iff_disjoint_support (x y : ι → K) :
    (∀ k, x k * y k = 0) ↔ Disjoint {k | x k ≠ 0} {k | y k ≠ 0} := by
  rw [Set.disjoint_left]
  constructor
  · intro h k hx hy
    exact (mul_ne_zero hx hy) (h k)
  · intro h k
    by_cases hx : x k = 0
    · rw [hx, zero_mul]
    · have hy : y k = 0 := by
        by_contra hy
        exact h hx hy
      rw [hy, mul_zero]

/-- A diagonal balance equation, encoded as one integral bilinear form. -/
def balanceMatrix {R : Type*} [Ring R] (i₀ i : ι) (j k : ι) : R := by
  classical
  exact (if j = i ∧ k = i then 1 else 0) - (if j = i₀ ∧ k = i₀ then 1 else 0)

private theorem pairing_balanceMatrix {R : Type*} [CommRing R]
    (i₀ i : ι) (x y : ι → R) :
    pairing (balanceMatrix i₀ i) x y = x i * y i - x i₀ * y i₀ := by
  classical
  simp [pairing, balanceMatrix, sub_mul, Finset.sum_sub_distrib, ite_and]

omit [Fintype ι] in
private theorem map_balanceMatrix {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (i₀ i j k : ι) :
    f (balanceMatrix (R := R) i₀ i j k) = balanceMatrix (R := S) i₀ i j k := by
  classical
  simp only [balanceMatrix, map_sub]
  split_ifs <;> simp only [map_one, map_zero]

/-- Primitive p-adic reduction lands in an explicit affine or off-diagonal boundary chart. -/
theorem padic_solution_has_residue_chart (p : ℕ) [Fact p.Prime]
    (A : τ → ι → ι → ℤ_[p]) (i₀ : ι)
    (x y : ι → ℚ_[p]) (hx : x ≠ 0) (hy : y ≠ 0)
    (hdiag : ∀ i, x i * y i = x i₀ * y i₀)
    (hA : ∀ t, pairing (fun i j => (A t i j : ℚ_[p])) x y = 0) :
    AffineSolution (fun t i j => PadicInt.toZMod (A t i j)) i₀ ∨
      ∃ i j : ι, i ≠ j ∧ BoundarySolution (fun t i j => PadicInt.toZMod (A t i j)) i j := by
  let B : τ ⊕ ι → ι → ι → ℤ_[p] := fun t => match t with
    | Sum.inl a => A a
    | Sum.inr i => balanceMatrix i₀ i
  have hB (t : τ ⊕ ι) : pairing (fun i j => (B t i j : ℚ_[p])) x y = 0 := by
    cases t with
    | inl t => exact hA t
    | inr i =>
      have he : (fun j k => (B (Sum.inr i) j k : ℚ_[p])) =
          balanceMatrix (R := ℚ_[p]) i₀ i := by
        funext j k
        exact map_balanceMatrix (PadicInt.Coe.ringHom (p := p)) i₀ i j k
      rw [he, pairing_balanceMatrix, hdiag, sub_self]
  obtain ⟨u, v, hu, hv, huv⟩ := bilinear_solution_reduces p B x y hx hy hB
  apply (solution_iff_affine_or_boundary _ i₀).mp
  refine ⟨u, v, hu, hv, ?_, fun t => huv (Sum.inl t)⟩
  intro i
  have h := huv (Sum.inr i)
  have he : (fun j k => PadicInt.toZMod (B (Sum.inr i) j k)) =
      balanceMatrix (R := ZMod p) i₀ i := by
    funext j k
    exact map_balanceMatrix PadicInt.toZMod i₀ i j k
  rw [he, pairing_balanceMatrix] at h
  exact sub_eq_zero.mp h

omit [Fintype ι] in
/-- The reduction meets an affine chart exactly when its common diagonal product survives reduction. -/
theorem reduced_support_meets_iff_common_product (p : ℕ) [Fact p.Prime]
    (x y : ι → ℤ_[p]) (i₀ : ι)
    (hdiag : ∀ i, x i * y i = x i₀ * y i₀) :
    (∃ i, PadicInt.toZMod (x i) ≠ 0 ∧ PadicInt.toZMod (y i) ≠ 0) ↔
      PadicInt.toZMod (x i₀ * y i₀) ≠ 0 := by
  constructor
  · rintro ⟨i, hx, hy⟩ hz
    apply mul_ne_zero hx hy
    rw [← map_mul, hdiag, hz]
  · intro hc
    have hm : PadicInt.toZMod (x i₀) * PadicInt.toZMod (y i₀) ≠ 0 := by
      rwa [← map_mul]
    exact ⟨i₀, (mul_ne_zero_iff.mp hm).1, (mul_ne_zero_iff.mp hm).2⟩

/-- A nonzero balanced p-adic product can specialize to a genuinely off-diagonal boundary point. -/
theorem exists_nonzero_product_boundary_specialization (p : ℕ) [Fact p.Prime] :
    ∃ x y : Fin 2 → ℤ_[p],
      (∀ i, x i * y i = (p : ℤ_[p])) ∧ (p : ℤ_[p]) ≠ 0 ∧
      (∃ i, PadicInt.toZMod (x i) ≠ 0) ∧
      (∃ j, PadicInt.toZMod (y j) ≠ 0) ∧
      (∀ i, PadicInt.toZMod (x i) * PadicInt.toZMod (y i) = 0) ∧
      ¬ ∃ i, PadicInt.toZMod (x i) ≠ 0 ∧ PadicInt.toZMod (y i) ≠ 0 := by
  let x : Fin 2 → ℤ_[p] := fun i => if i = 0 then 1 else p
  let y : Fin 2 → ℤ_[p] := fun i => if i = 0 then p else 1
  have hz : PadicInt.toZMod (p : ℤ_[p]) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero (ZMod p) p
  have h10 : (1 : Fin 2) ≠ 0 := fun h => Nat.one_ne_zero (congrArg Fin.val h)
  have hprod (i : Fin 2) : x i * y i = (p : ℤ_[p]) := by
    by_cases hi : i = 0
    · simp only [x, y, if_pos hi, one_mul]
    · simp only [x, y, if_neg hi, mul_one]
  have hres (i : Fin 2) : PadicInt.toZMod (x i) * PadicInt.toZMod (y i) = 0 := by
    rw [← map_mul, hprod, hz]
  refine ⟨x, y, hprod, Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero,
    ⟨0, ?_⟩, ⟨1, ?_⟩, hres, ?_⟩
  · simp only [x, if_pos rfl, map_one, ne_eq, one_ne_zero, not_false_eq_true]
  · simp only [y, if_neg h10, map_one, ne_eq, one_ne_zero, not_false_eq_true]
  · rintro ⟨i, hx, hy⟩
    exact mul_ne_zero hx hy (hres i)

#print axioms reduced_support_meets_iff_common_product
#print axioms exists_nonzero_product_boundary_specialization
#print axioms padic_solution_has_residue_chart

#print axioms solution_iff_affine_or_boundary
#print axioms boundary_iff_disjoint_support
end GaloisForLFunctions.RepresentationLifting.BalancedCharts
