import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.QuadraticFormCounts
import Mathlib.Algebra.Ring.GeomSum

/-!
# Actual projective quadratic zero loci

Nonzero quadratic zeros are quotiented by simultaneous nonzero scalar
multiplication. Every orbit has exactly `q−1` representatives. The affine
discriminant formulas therefore give the exact projective counts.
-/

open Finset Matrix QuadraticMap
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- Nonzero vectors on the affine quadratic zero locus. -/
def quadraticCone (Q : QuadraticForm F (Fin n → F)) : Finset (Fin n → F) :=
  (univ.filter (fun x => Q x = 0)).erase 0

theorem mem_quadraticCone (Q : QuadraticForm F (Fin n → F)) (x : Fin n → F) :
    x ∈ quadraticCone Q ↔ x ≠ 0 ∧ Q x = 0 := by
  simp only [quadraticCone, mem_erase, mem_filter, mem_univ, true_and]

/-- Removing the vertex deletes exactly one affine point. -/
theorem quadraticCone_card_add_one (Q : QuadraticForm F (Fin n → F)) :
    ((quadraticCone Q).card : ℤ) + 1 = quadraticFormCount Q 0 := by
  have h0 : (0 : Fin n → F) ∈ univ.filter (fun x => Q x = 0) := by
    simp only [mem_filter, mem_univ, map_zero, and_self]
  unfold quadraticCone quadraticFormCount
  exact_mod_cast card_erase_add_one h0

/-- Scaling is an actual map of the nonzero quadratic cone. -/
def quadraticConeScale (Q : QuadraticForm F (Fin n → F)) (u : Fˣ)
    (x : ↥(quadraticCone Q)) : ↥(quadraticCone Q) :=
  ⟨(u : F) • x.val, (mem_quadraticCone Q _).mpr ⟨by
    intro h
    apply ((mem_quadraticCone Q x.val).mp x.property).1
    funext i
    have hi : (u : F) * x.val i = 0 := congrFun h i
    exact (mul_eq_zero.mp hi).resolve_left u.ne_zero,
    by rw [QuadraticMap.map_smul, ((mem_quadraticCone Q x.val).mp x.property).2,
      smul_zero]⟩⟩

/-- Scalar equivalence on the nonzero zero locus. -/
def quadraticScalarSetoid (Q : QuadraticForm F (Fin n → F)) : Setoid ↥(quadraticCone Q) where
  r x y := ∃ u : Fˣ, ∀ i, x.val i = (u : F) * y.val i
  iseqv :=
    { refl := fun x => ⟨1, by intro i; simp⟩
      symm := by
        rintro x y ⟨u, hu⟩
        refine ⟨u⁻¹, fun i => ?_⟩
        rw [hu i, ← mul_assoc]
        simp
      trans := by
        rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
        refine ⟨u * v, fun i => ?_⟩
        rw [hu i, hv i, Units.val_mul, mul_assoc] }

/-- The projective quadric consists of the actual nonzero scalar orbits. -/
def ProjectiveQuadric (Q : QuadraticForm F (Fin n → F)) := Quotient (quadraticScalarSetoid Q)

instance (Q : QuadraticForm F (Fin n → F)) : Fintype (ProjectiveQuadric Q) := by
  classical
  exact Fintype.ofSurjective (Quotient.mk (quadraticScalarSetoid Q))
    (fun q => Quotient.exists_rep q)

private theorem quadraticCone_nonzero_coordinate (Q : QuadraticForm F (Fin n → F))
    (x : ↥(quadraticCone Q)) : ∃ i, x.val i ≠ 0 := by
  by_contra! h
  exact ((mem_quadraticCone Q x.val).mp x.property).1 (funext h)

private theorem quadraticOrbit_scalar_exists (Q : QuadraticForm F (Fin n → F))
    (q : ProjectiveQuadric Q)
    (x : {x : ↥(quadraticCone Q) // Quotient.mk (quadraticScalarSetoid Q) x = q}) :
    ∃ u : Fˣ, ∀ i, x.val.val i = (u : F) * q.out.val i :=
  Quotient.exact (x.property.trans (Quotient.out_eq q).symm)

/-- Every projective point has exactly one representative for each nonzero scalar. -/
def projectiveQuadricFiberEquiv (Q : QuadraticForm F (Fin n → F)) (q : ProjectiveQuadric Q) :
    Fˣ ≃ {x : ↥(quadraticCone Q) // Quotient.mk (quadraticScalarSetoid Q) x = q} where
  toFun u := ⟨quadraticConeScale Q u q.out,
    (Quotient.sound (s := quadraticScalarSetoid Q)
      (a := quadraticConeScale Q u q.out) (b := q.out) ⟨u, fun _ => rfl⟩).trans
        (Quotient.out_eq q)⟩
  invFun x := Classical.choose (quadraticOrbit_scalar_exists Q q x)
  left_inv u := by
    apply Units.ext
    obtain ⟨i, hi⟩ := quadraticCone_nonzero_coordinate Q q.out
    apply mul_right_cancel₀ hi
    exact (Classical.choose_spec (quadraticOrbit_scalar_exists Q q _) i).symm
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact (Classical.choose_spec (quadraticOrbit_scalar_exists Q q x) i).symm

/-- The scalar-orbit count is the actual affine cone count divided by `q−1`. -/
theorem quadraticCone_card_orbits (Q : QuadraticForm F (Fin n → F)) :
    (quadraticCone Q).card = Fintype.card (ProjectiveQuadric Q) * (Fintype.card F - 1) := by
  classical
  let π : ↥(quadraticCone Q) → ProjectiveQuadric Q := Quotient.mk (quadraticScalarSetoid Q)
  have hf (q : ProjectiveQuadric Q) : Fintype.card {x // π x = q} = Fintype.card Fˣ := by
    convert (Fintype.card_congr (projectiveQuadricFiberEquiv Q q)).symm <;> rfl
  calc
    (quadraticCone Q).card = Fintype.card ↥(quadraticCone Q) := (Fintype.card_coe _).symm
    _ = Fintype.card (Σ q, {x // π x = q}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv π)).symm
    _ = _ := by
      rw [Fintype.card_sigma, sum_congr rfl (fun q _ => hf q), sum_const,
        card_univ, nsmul_eq_mul, Fintype.card_units, Nat.cast_id]

/-- Integer form of the affine-to-projective counting identity, including dimension zero. -/
theorem projectiveQuadric_card_mul (Q : QuadraticForm F (Fin n → F)) :
    (Fintype.card (ProjectiveQuadric Q) : ℤ) * (Fintype.card F - 1) =
      quadraticFormCount Q 0 - 1 := by
  have hc := quadraticCone_card_add_one Q
  rw [quadraticCone_card_orbits, Nat.cast_mul, Nat.cast_sub Fintype.card_pos, Nat.cast_one] at hc
  linear_combination hc

omit [DecidableEq F] in
private theorem field_card_sub_one_ne_zero : (Fintype.card F : ℤ) - 1 ≠ 0 := by
  have h : (1 : ℤ) < Fintype.card F := by exact_mod_cast (Fintype.one_lt_card (α := F))
  exact (sub_pos.mpr h).ne'

section Discriminant

variable [Invertible (2 : F)]

/-- Odd-dimensional nondegenerate forms have only the ambient projective count. -/
theorem projectiveQuadric_card_odd (hF : ringChar F ≠ 2) (k : ℕ)
    (Q : QuadraticForm F (Fin (2 * k + 1) → F)) (hQ : Q.discr' ≠ 0) :
    (Fintype.card (ProjectiveQuadric Q) : ℤ) =
      ∑ j ∈ range (2 * k), (Fintype.card F : ℤ) ^ j := by
  apply mul_right_cancel₀ (field_card_sub_one_ne_zero (F := F))
  rw [projectiveQuadric_card_mul, quadraticFormCount_odd hF k Q hQ, geom_sum_mul]
  simp only [mul_zero, quadraticChar_zero, zero_mul, add_zero]

/-- Even-dimensional nondegenerate forms have one signed middle-dimensional correction. -/
theorem projectiveQuadric_card_even (hF : ringChar F ≠ 2) (k : ℕ)
    (Q : QuadraticForm F (Fin (2 * k + 2) → F)) (hQ : Q.discr' ≠ 0) :
    (Fintype.card (ProjectiveQuadric Q) : ℤ) =
      (∑ j ∈ range (2 * k + 1), (Fintype.card F : ℤ) ^ j) +
        quadraticChar F ((-1) ^ (k + 1) * Q.discr') * (Fintype.card F : ℤ) ^ k := by
  apply mul_right_cancel₀ (field_card_sub_one_ne_zero (F := F))
  rw [projectiveQuadric_card_mul, quadraticFormCount_even hF k Q hQ,
    quadraticZeroCorrection, if_pos rfl, add_mul, geom_sum_mul]
  ring

end Discriminant

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
