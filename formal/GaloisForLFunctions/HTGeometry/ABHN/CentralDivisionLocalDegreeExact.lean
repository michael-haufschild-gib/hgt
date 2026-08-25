import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionLocalDegreeBounds
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionResidueFinite
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionValueResidueEquality

/-!
# Exact value and residue degrees of local division algebras

For a finite central division algebra of degree `n` over a locally compact nonarchimedean normed
field, the determinant value quotient and determinant residue extension both have degree `n`.

The proof first obtains finiteness of the base residue field directly from compactness of its unit
ball.  A finite radius-one net surjects onto the residue field.  It then combines defectlessness
`e * f = n²`, the value bound `e ≤ n`, and the residue bound `f² ≤ n²` to force `e = f = n`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [LocallyCompactSpace F]

omit [CompleteSpace F] in
/-- The residue field of the norm valuation on a locally compact nonarchimedean normed field is
finite.  Compactness supplies a finite radius-one net of the valuation ring, and reduction maps
that net onto the residue field. -/
theorem normValuationResidue_finite : Finite (NormValuationResidue (F := F)) := by
  letI : ProperSpace F := .of_locallyCompactSpace F
  letI : CompactSpace (NormValuationSubring (F := F)) := by
    rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
      Subtype.range_coe_subtype]
    change IsCompact {x : F | ‖x‖₊ ≤ 1}
    have h := isCompact_closedBall (0 : F) 1
    convert h using 1
    ext x
    simp [Metric.mem_closedBall, dist_zero_right, ← NNReal.coe_le_coe]
  have happrox := Metric.finite_approx_of_totallyBounded
    (isCompact_univ : IsCompact
      (Set.univ : Set (NormValuationSubring (F := F)))).totallyBounded
      1 zero_lt_one
  simp only [Set.subset_univ, Set.univ_subset_iff, true_and] at happrox
  obtain ⟨t, ht, ht'⟩ := happrox
  rw [← Set.finite_univ_iff]
  refine (ht.image (IsLocalRing.residue _)).subset ?_
  rintro ⟨x⟩ _
  have hx : x ∈ ⋃ y ∈ t, Metric.ball y 1 := by
    rw [ht']
    exact Set.mem_univ x
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hx
  obtain ⟨y, hy, hy'⟩ := hx
  simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk,
    IsLocalRing.residue, Set.mem_image]
  refine ⟨y, hy, ?_⟩
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem y x).mpr
  rw [Valuation.mem_maximalIdeal_iff F (NormedField.valuation (K := F)),
    NormedField.valuation_apply]
  rw [dist_comm] at hy'
  simpa [dist_eq_norm, ← NNReal.coe_lt_coe] using hy'

variable {A : Type u} [DivisionRing A] [Algebra F A] [Module.Finite F A]
  [Algebra.IsCentral F A]

/-- Exact local degree identities: both the relative determinant value index and the determinant
residue degree equal the degree of the central division algebra. -/
theorem divisionAlgebraDeterminant_localDegrees_eq_degree :
    Nat.card (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) =
        divisionAlgebraDegree (F := F) (A := A) ∧
      Module.finrank (NormValuationResidue (F := F))
          (DivisionAlgebraDeterminantResidue (F := F) (A := A)) =
        divisionAlgebraDegree (F := F) (A := A) := by
  letI : Finite (NormValuationResidue (F := F)) :=
    normValuationResidue_finite (F := F)
  let e := Nat.card (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A))
  let f := Module.finrank (NormValuationResidue (F := F))
    (DivisionAlgebraDeterminantResidue (F := F) (A := A))
  let n := divisionAlgebraDegree (F := F) (A := A)
  have hn : 0 < n := divisionAlgebraDegree_pos (F := F) (A := A)
  have he : e ≤ n :=
    divisionAlgebraDeterminantValueQuotient_natCard_le_degree (F := F) (A := A)
  have hf2 : f * f ≤ n * n := by
    rw [divisionAlgebraDegree_mul_self (F := F) (A := A)]
    exact finrank_divisionAlgebraDeterminantResidue_mul_self_le_finrank
      (F := F) (A := A)
  have hef : e * f = n * n :=
    (divisionAlgebraDeterminantValueQuotient_natCard_mul_residue_finrank_eq_finrank
      (F := F) (A := A)).trans
        (divisionAlgebraDegree_mul_self (F := F) (A := A)).symm
  have hf : f ≤ n := by nlinarith
  constructor <;> nlinarith

/-- The relative determinant value-group index of a local central division algebra is its degree. -/
theorem divisionAlgebraDeterminantValueQuotient_natCard_eq_degree :
    Nat.card (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) =
      divisionAlgebraDegree (F := F) (A := A) :=
  (divisionAlgebraDeterminant_localDegrees_eq_degree (F := F) (A := A)).1

/-- The determinant residue degree of a local central division algebra is its degree. -/
theorem finrank_divisionAlgebraDeterminantResidue_eq_degree :
    Module.finrank (NormValuationResidue (F := F))
        (DivisionAlgebraDeterminantResidue (F := F) (A := A)) =
      divisionAlgebraDegree (F := F) (A := A) :=
  (divisionAlgebraDeterminant_localDegrees_eq_degree (F := F) (A := A)).2

/-- A primitive determinant-residue element has an integral lift that generates a commutative
subfield of full division-algebra degree.  Thus the lifted field is already maximal commutative;
no further enlargement is needed. -/
theorem exists_residue_generator_lift_adjoin_finrank_eq_degree :
    ∃ x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A),
      Module.finrank F (Algebra.adjoin F ({(x : A)} : Set A)) =
        divisionAlgebraDegree (F := F) (A := A) := by
  letI : Finite (NormValuationResidue (F := F)) :=
    normValuationResidue_finite (F := F)
  obtain ⟨x, hx⟩ := exists_residue_generator_lift_adjoin_finrank_ge
    (F := F) (A := A)
  obtain ⟨S, hxS, hcommS, hfieldS, hmaxS⟩ :=
    exists_maximalCommutativeSubfield_containing_element F A (x : A)
  have hadjoinS : Module.finrank F (Algebra.adjoin F ({(x : A)} : Set A)) ≤
      Module.finrank F S :=
    Submodule.finrank_mono
      (s := (Algebra.adjoin F ({(x : A)} : Set A)).toSubmodule)
      (t := S.toSubmodule) hxS
  have hSsq : Module.finrank F S * Module.finrank F S = Module.finrank F A :=
    maximalCommutativeSubfield_finrank_sq F A S hcommS hfieldS hmaxS
  have hSdegree : Module.finrank F S = divisionAlgebraDegree (F := F) (A := A) :=
    Nat.mul_self_inj.mp
      (hSsq.trans (divisionAlgebraDegree_mul_self (F := F) (A := A)).symm)
  have hlower : divisionAlgebraDegree (F := F) (A := A) ≤
      Module.finrank F (Algebra.adjoin F ({(x : A)} : Set A)) := by
    rw [← finrank_divisionAlgebraDeterminantResidue_eq_degree (F := F) (A := A)]
    exact hx
  exact ⟨x, Nat.le_antisymm (hadjoinS.trans_eq hSdegree) hlower⟩

/-- Strong residue-lift form of the maximal-subfield construction.  One integral element both
generates the full determinant residue field after reduction and generates a commutative subfield
of degree `deg(A)` before reduction.  This is the precise algebraic certificate behind the
unramified maximal slice; identifying its valuation ring with the induced field valuation is the
remaining step to package it as an unramified valued-field extension. -/
theorem exists_fullResidueDegree_maximalSubfieldGenerator :
    ∃ x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A),
      Module.finrank F (Algebra.adjoin F ({(x : A)} : Set A)) =
          divisionAlgebraDegree (F := F) (A := A) ∧
        Algebra.adjoin (NormValuationResidue (F := F))
            ({Ideal.Quotient.mk
                (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) x} :
              Set (DivisionAlgebraDeterminantResidue (F := F) (A := A))) = ⊤ := by
  letI : Finite (NormValuationResidue (F := F)) :=
    normValuationResidue_finite (F := F)
  let pb := Field.powerBasisOfFiniteOfSeparable
    (NormValuationResidue (F := F))
    (DivisionAlgebraDeterminantResidue (F := F) (A := A))
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective pb.gen
  have hres : LinearIndependent (NormValuationResidue (F := F))
      (fun i : Fin pb.dim => Ideal.Quotient.mk
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) (x ^ (i : ℕ))) := by
    simpa only [map_pow, hx, ← pb.basis_eq_pow] using pb.basis.linearIndependent
  have hlift : LinearIndependent F (fun i : Fin pb.dim => ((x ^ (i : ℕ) : _) : A)) :=
    divisionAlgebraDeterminantResidue_linearIndependent_lifts
      (fun i : Fin pb.dim => x ^ (i : ℕ)) hres
  let T := Algebra.adjoin F ({(x : A)} : Set A)
  let tx : Fin pb.dim → T := fun i =>
    ⟨(x : A) ^ (i : ℕ),
      pow_mem (Algebra.self_mem_adjoin_singleton F (x : A)) (i : ℕ)⟩
  have htx : LinearIndependent F tx := by
    apply LinearIndependent.of_comp T.val.toLinearMap
    change LinearIndependent F (fun i : Fin pb.dim => ((tx i : T) : A))
    convert hlift using 1
    funext i
    rfl
  have hlower : divisionAlgebraDegree (F := F) (A := A) ≤ Module.finrank F T := by
    rw [← finrank_divisionAlgebraDeterminantResidue_eq_degree (F := F) (A := A),
      pb.finrank]
    simpa only [Fintype.card_fin] using htx.fintype_card_le_finrank
  obtain ⟨S, hxS, hcommS, hfieldS, hmaxS⟩ :=
    exists_maximalCommutativeSubfield_containing_element F A (x : A)
  have hTS : Module.finrank F T ≤ Module.finrank F S :=
    Submodule.finrank_mono (s := T.toSubmodule) (t := S.toSubmodule) hxS
  have hSsq : Module.finrank F S * Module.finrank F S = Module.finrank F A :=
    maximalCommutativeSubfield_finrank_sq F A S hcommS hfieldS hmaxS
  have hSdegree : Module.finrank F S = divisionAlgebraDegree (F := F) (A := A) :=
    Nat.mul_self_inj.mp
      (hSsq.trans (divisionAlgebraDegree_mul_self (F := F) (A := A)).symm)
  refine ⟨x, Nat.le_antisymm (hTS.trans_eq hSdegree) hlower, ?_⟩
  rw [hx]
  exact pb.adjoin_gen_eq_top

end

end GaloisForLFunctions.HTGeometry.ABHN
