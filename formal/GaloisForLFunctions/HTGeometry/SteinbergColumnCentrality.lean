import GaloisForLFunctions.HTGeometry.SteinbergColumnInjectivity

/-!
# Centrality of `K₂` on a column subgroup

Milnor's argument that `K₂(R)` is central in the Steinberg group turns on two facts about the
abelian column subgroups, both now proved: they are abelian, and the map to the matrices is
injective on them.  The mechanism is then immediate.

An element `y` of `K₂` maps to the identity, so `y x y⁻¹` and `x` have the same image; if `y` also
carries the column subgroup into itself, injectivity there forces `y x y⁻¹ = x`.  So **an element of
`K₂` in the normalizer of a column subgroup centralizes it**.

The normalizer hypothesis is discharged for every generator whose *first* index avoids the column:
conjugating a column generator by such a generator either leaves it alone (disjoint positions) or
multiplies it by another column generator (the chained relation).  What Milnor's argument adds on
top is the index-avoidance count: an element of `K₂` is a word in finitely many generators, so some
index is unused by it, and the argument applies at that index.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n]

omit [DecidableEq n] in
/-- The inverse of a generator is the generator with the negated entry. -/
theorem steinbergX_neg {i j : n} (hij : i ≠ j) (a : R) :
    steinbergX hij (-a) = (steinbergX hij a)⁻¹ := by
  have h := steinbergX_mul hij a (-a)
  rw [add_neg_cancel, steinbergX_zero] at h
  exact eq_inv_of_mul_eq_one_right h

/-- **Conjugating a column generator by a generator whose first index avoids the column stays in the
column subgroup.** -/
theorem conj_steinbergX_mem_columnSubgroup {j p q k : n} (hpq : p ≠ q) (hkj : k ≠ j)
    (hpj : p ≠ j) (b a : R) :
    steinbergX hpq b * steinbergX hkj a * (steinbergX hpq b)⁻¹
      ∈ columnSubgroup (R := R) (n := n) j := by
  by_cases hqk : q = k
  · subst hqk
    have hchain := steinbergX_chain hpq hkj hpj b a
    have hval : steinbergX hpq b * steinbergX hkj a * (steinbergX hpq b)⁻¹
        = steinbergX hpj (b * a) * steinbergX hkj a := mul_inv_eq_iff_eq_mul.1 hchain
    rw [hval]
    exact Subgroup.mul_mem _ (steinbergX_mem_columnSubgroup hpj (b * a))
      (steinbergX_mem_columnSubgroup hkj a)
  · have hcomm := steinbergX_commute hpq hkj hqk hpj b a
    have hval : steinbergX hpq b * steinbergX hkj a * (steinbergX hpq b)⁻¹
        = steinbergX hkj a := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hval]
    exact steinbergX_mem_columnSubgroup hkj a

/-- The same for the whole column subgroup, not just its generators. -/
theorem conj_columnSubgroup_le {j p q : n} (hpq : p ≠ q) (hpj : p ≠ j) (b : R) :
    ∀ x ∈ columnSubgroup (R := R) (n := n) j,
      steinbergX hpq b * x * (steinbergX hpq b)⁻¹ ∈ columnSubgroup (R := R) (n := n) j := by
  intro x hx
  have hsub : columnSubgroup (R := R) (n := n) j
      ≤ (columnSubgroup (R := R) (n := n) j).comap
        (MulAut.conj (steinbergX hpq b)).toMonoidHom := by
    rw [columnSubgroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro z ⟨k, hkj, a, rfl⟩
    exact conj_steinbergX_mem_columnSubgroup hpq hkj hpj b a
  exact hsub hx

/-- **A generator whose first index avoids the column normalizes the column subgroup.** -/
theorem steinbergX_mem_normalizer {j p q : n} (hpq : p ≠ q) (hpj : p ≠ j) (b : R) :
    steinbergX hpq b ∈ Subgroup.normalizer (columnSubgroup (R := R) (n := n) j) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_columnSubgroup_le hpq hpj b x hx
  · intro hx
    have h := conj_columnSubgroup_le hpq hpj (-b)
      (steinbergX hpq b * x * (steinbergX hpq b)⁻¹) hx
    rw [steinbergX_neg hpq b] at h
    have hval : (steinbergX hpq b)⁻¹ * (steinbergX hpq b * x * (steinbergX hpq b)⁻¹)
        * ((steinbergX hpq b)⁻¹)⁻¹ = x := by
      group
    rwa [hval] at h

variable [Fintype n]

/-- **An element of `K₂` in the normalizer of a column subgroup centralizes it.**  This is the step
Milnor's centrality argument turns on: the conjugate has the same image in the matrices, and the map
is injective on the column. -/
theorem KTwo_commute_of_mem_normalizer {j : n} {y : SteinbergGroup R n}
    (hy : y ∈ KTwo R n) (hnorm : y ∈ Subgroup.normalizer (columnSubgroup (R := R) (n := n) j)) :
    ∀ x ∈ columnSubgroup (R := R) (n := n) j, y * x = x * y := by
  intro x hx
  have hconj : y * x * y⁻¹ ∈ columnSubgroup (R := R) (n := n) j :=
    (Subgroup.mem_normalizer_iff.1 hnorm x).1 hx
  have hy1 : steinbergToGL y = 1 := (mem_KTwo_iff y).1 hy
  have himg : steinbergToGL (y * x * y⁻¹) = steinbergToGL x := by
    rw [map_mul, map_mul, map_inv, hy1, one_mul, inv_one, mul_one]
  have heq : y * x * y⁻¹ = x :=
    steinbergToGL_injOn_columnSubgroup j hconj hx himg
  have hmul := congrArg (fun z => z * y) heq
  simpa [mul_assoc] using hmul

/-- **The generators of the avoiding subgroup centralize the column, once they lie in `K₂`.** -/
theorem KTwo_commute_columnSubgroup_of_avoid {j : n} {y : SteinbergGroup R n}
    (hy : y ∈ KTwo R n)
    (havoid : y ∈ Subgroup.closure
      {z : SteinbergGroup R n | ∃ (p q : n) (hpq : p ≠ q) (_ : p ≠ j) (b : R),
        z = steinbergX hpq b}) :
    ∀ x ∈ columnSubgroup (R := R) (n := n) j, y * x = x * y := by
  refine KTwo_commute_of_mem_normalizer hy ?_
  refine (Subgroup.closure_le _).2 ?_ havoid
  rintro z ⟨p, q, hpq, hpj, b, rfl⟩
  exact steinbergX_mem_normalizer hpq hpj b

end GaloisForLFunctions.HTGeometry

end
