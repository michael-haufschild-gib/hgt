import GaloisForLFunctions.HTGeometry.CenteredGenericField

/-!
# The coefficients of the centered generic polynomial

The centered polynomial is a product of linear factors whose roots lie in the centered field, so
all its coefficients lie there too, and they are fixed by permuting the variables because the whole
polynomial is.

The symmetric group therefore acts on the centered field by automorphisms over the field its
centered coefficients generate, and faithfully, so that automorphism group has at least `d!`
elements.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Polynomial

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-! ## The coefficients lie in the centered field -/

theorem centeredMonicF_mem_lifts :
    centeredMonicF K d ∈
      Polynomial.lifts
        (algebraMap (centeredField K d) (SymmetricRationalField K d)) := by
  rw [centeredMonicF]
  refine Subsemiring.prod_mem _ fun i _ => ?_
  rw [sub_eq_add_neg, ← map_neg Polynomial.C]
  refine add_mem (Polynomial.X_mem_lifts _) ?_
  exact Polynomial.C_mem_lifts _
    (⟨-centeredRoot K d i, neg_mem (centeredRoot_mem_centeredField i)⟩ : centeredField K d)

theorem coeff_centeredMonicF_mem (k : ℕ) :
    (centeredMonicF K d).coeff k ∈ centeredField K d := by
  obtain ⟨y, hy⟩ := (Polynomial.lifts_iff_coeff_lifts (centeredMonicF K d)).1
    (centeredMonicF_mem_lifts (K := K) (d := d)) k
  rw [← hy]
  exact y.2

/-- The coefficients of the centered generic polynomial, as elements of the centered field. -/
noncomputable def centeredCoeff (K : Type*) [Field K] [CharZero K] (d : ℕ) (k : Fin d) :
    centeredField K d :=
  ⟨(centeredMonicF K d).coeff (k : ℕ), coeff_centeredMonicF_mem (k : ℕ)⟩

/-- The field the centered coefficients generate over the constants, inside the centered field. -/
noncomputable def centeredCoeffField (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    IntermediateField K (centeredField K d) :=
  IntermediateField.adjoin K (Set.range (centeredCoeff K d))

/-! ## The coefficients are symmetric -/

theorem smul_centeredCoeff (e : Equiv.Perm (Fin d)) (k : Fin d) :
    e • centeredCoeff K d k = centeredCoeff K d k := by
  refine Subtype.ext ?_
  rw [coe_smul_centeredField]
  have h := congrArg (fun p : Polynomial (SymmetricRationalField K d) => p.coeff (k : ℕ))
    (map_centeredMonicF (K := K) (d := d) e)
  rwa [Polynomial.coeff_map] at h

/-- The elements fixed by one permutation, as an intermediate field over the constants. -/
noncomputable def centeredFixedBy (K : Type*) [Field K] [CharZero K] (d : ℕ)
    (e : Equiv.Perm (Fin d)) : IntermediateField K (centeredField K d) where
  __ := FixedBy.subfield (centeredField K d) e
  algebraMap_mem' := by
    intro c
    show e • (algebraMap K (centeredField K d) c) = algebraMap K (centeredField K d) c
    refine Subtype.ext ?_
    rw [coe_smul_centeredField]
    exact smul_eq_of_mem_symmetricPart ((symmetricPartField K d).algebraMap_mem' c) e

/-- **The centered coefficient field is fixed by every permutation.** -/
theorem smul_eq_of_mem_centeredCoeffField {z : centeredField K d}
    (hz : z ∈ centeredCoeffField K d) (e : Equiv.Perm (Fin d)) : e • z = z := by
  have hle : centeredCoeffField K d ≤ centeredFixedBy K d e := by
    rw [centeredCoeffField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    exact smul_centeredCoeff e k
  exact hle hz

/-! ## The action over the centered coefficient field -/

noncomputable scoped instance centeredCoeffSMulCommClass (K : Type*) [Field K] [CharZero K]
    (d : ℕ) : SMulCommClass (Equiv.Perm (Fin d)) (centeredCoeffField K d)
      (centeredField K d) where
  smul_comm e c x := by
    have hc : e • (c : centeredField K d) = (c : centeredField K d) :=
      smul_eq_of_mem_centeredCoeffField c.2 e
    show e • ((c : centeredField K d) * x) = (c : centeredField K d) * (e • x)
    rw [smul_mul', hc]

/-- **The symmetric group acts by automorphisms over the centered coefficient field.** -/
noncomputable def centeredPermAlgEquiv (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    Equiv.Perm (Fin d) →*
      ((centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d)) :=
  MulSemiringAction.toAlgAut (Equiv.Perm (Fin d)) (centeredCoeffField K d) (centeredField K d)

theorem centeredPermAlgEquiv_injective (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    Function.Injective (centeredPermAlgEquiv K d) := by
  intro a b hab
  refine eq_of_smul_eq_smul (α := centeredField K d) fun x => ?_
  have h := congrArg (fun f => f x) hab
  exact h

end GaloisForLFunctions.HTGeometry
