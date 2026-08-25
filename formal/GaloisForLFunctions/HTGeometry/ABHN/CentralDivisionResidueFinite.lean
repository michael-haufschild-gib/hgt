import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionDeterminantNorm
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionDoubleCentralizer
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Finite residue skew fields of valued division algebras

A residue-linearly independent family in the determinant valuation order lifts to a linearly
independent family in the ambient division algebra.  Consequently the determinant residue skew
field is finite-dimensional over the base residue field.  When the latter is finite, Wedderburn's
little theorem makes the residue skew field commutative.

This is the residue-degree half of the valuation-theoretic route to local Brauer exhaustion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u v

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [DivisionRing A] [Algebra F A] [Module.Finite F A]

/-- Linear independence after reduction modulo the determinant maximal ideal forces linear
independence of arbitrary integral lifts in the ambient division algebra.

The proof normalizes a hypothetical relation by a coefficient of maximal norm.  Every normalized
coefficient then lies in the base valuation ring, while the maximal coefficient reduces to one.
Reduction contradicts the assumed residue independence. -/
theorem divisionAlgebraDeterminantResidue_linearIndependent_lifts
    {ι : Type v}
    (x : ι → divisionAlgebraDeterminantValuationSubring (F := F) (A := A))
    (hx : LinearIndependent (NormValuationResidue (F := F))
      (fun i => Ideal.Quotient.mk
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) (x i))) :
    LinearIndependent F (fun i => (x i : A)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hrel i hi
  by_contra hgi
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s (fun j => ‖g j‖) ⟨i, hi⟩
  have hgm : g m ≠ 0 := by
    intro hzero
    have hle := hmax i hi
    rw [hzero, norm_zero] at hle
    exact (not_lt_of_ge hle) (norm_pos_iff.mpr hgi)
  let c : ι → NormValuationSubring (F := F) := fun j =>
    if hj : j ∈ s then
      ⟨(g m)⁻¹ * g j, by
        change NormedField.valuation ((g m)⁻¹ * g j) ≤ 1
        rw [NormedField.valuation_apply]
        have hle : ‖(g m)⁻¹ * g j‖ ≤ 1 := by
          rw [norm_mul, norm_inv]
          exact (inv_mul_le_one₀ (norm_pos_iff.mpr hgm)).mpr (hmax j hj)
        exact_mod_cast hle⟩
    else 0
  have hnormrel : ∑ j ∈ s, (c j : F) • (x j : A) = 0 := by
    calc
      ∑ j ∈ s, (c j : F) • (x j : A) =
          ∑ j ∈ s, ((g m)⁻¹ * g j) • (x j : A) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (c j : F) = (g m)⁻¹ * g j by simp [c, hj]]
      _ = 0 := by
        calc
          ∑ j ∈ s, ((g m)⁻¹ * g j) • (x j : A) =
              (g m)⁻¹ • ∑ j ∈ s, g j • (x j : A) := by
            simp only [Finset.smul_sum, smul_smul]
          _ = 0 := by rw [hrel, smul_zero]
  have horderrel :
      ∑ j ∈ s,
        normValuationSubringToDivisionAlgebraDeterminantValuationSubring
            (F := F) (A := A) (c j) * x j = 0 := by
    apply Subtype.ext
    change (divisionAlgebraDeterminantValuationSubring (F := F) (A := A)).subtype
      (∑ j ∈ s,
        normValuationSubringToDivisionAlgebraDeterminantValuationSubring
            (F := F) (A := A) (c j) * x j) = (0 : A)
    rw [map_sum]
    simp only [map_mul]
    change ∑ j ∈ s, algebraMap F A (c j : F) * (x j : A) = 0
    simpa only [Algebra.smul_def] using hnormrel
  have hresrel :
      ∑ j ∈ s,
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (NormValuationSubring (F := F))) (c j)) •
          Ideal.Quotient.mk
            (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) (x j) = 0 := by
    have hmap := congrArg
      (Ideal.Quotient.mk
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))) horderrel
    change ∑ j ∈ s,
      normValuationResidueToDivisionAlgebraDeterminantResidue
          (F := F) (A := A)
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (NormValuationSubring (F := F))) (c j)) *
        Ideal.Quotient.mk
          (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) (x j) = 0
    simpa only [map_sum, map_mul, map_zero,
      normValuationResidueToDivisionAlgebraDeterminantResidue,
      Ideal.quotientMap_mk] using hmap
  have hc := (linearIndependent_iff'.mp hx) s
    (fun j => Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (NormValuationSubring (F := F))) (c j)) hresrel m hm
  have hcm : c m = 1 := by
    simp only [c, dif_pos hm]
    apply Subtype.ext
    exact inv_mul_cancel₀ hgm
  rw [hcm, map_one] at hc
  exact one_ne_zero hc

/-- The determinant residue division ring is finite-dimensional over the base residue field. -/
noncomputable instance divisionAlgebraDeterminantResidue_moduleFinite :
    Module.Finite (NormValuationResidue (F := F))
      (DivisionAlgebraDeterminantResidue (F := F) (A := A)) := by
  let b := Module.Free.chooseBasis (NormValuationResidue (F := F))
    (DivisionAlgebraDeterminantResidue (F := F) (A := A))
  choose x hx using fun i => Ideal.Quotient.mk_surjective (b i)
  have hres : LinearIndependent (NormValuationResidue (F := F))
      (fun i => Ideal.Quotient.mk
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) (x i)) := by
    simpa only [hx] using b.linearIndependent
  have hlift : LinearIndependent F (fun i => (x i : A)) :=
    divisionAlgebraDeterminantResidue_linearIndependent_lifts x hres
  letI : Finite (Module.Free.ChooseBasisIndex
      (NormValuationResidue (F := F))
      (DivisionAlgebraDeterminantResidue (F := F) (A := A))) := hlift.finite
  exact Module.Finite.of_basis b

/-- Residue degree is bounded by the ambient vector-space dimension. -/
theorem finrank_divisionAlgebraDeterminantResidue_le_finrank :
    Module.finrank (NormValuationResidue (F := F))
        (DivisionAlgebraDeterminantResidue (F := F) (A := A)) ≤
      Module.finrank F A := by
  let b := Module.Free.chooseBasis (NormValuationResidue (F := F))
    (DivisionAlgebraDeterminantResidue (F := F) (A := A))
  choose x hx using fun i => Ideal.Quotient.mk_surjective (b i)
  have hres : LinearIndependent (NormValuationResidue (F := F))
      (fun i => Ideal.Quotient.mk
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) (x i)) := by
    simpa only [hx] using b.linearIndependent
  have hlift : LinearIndependent F (fun i => (x i : A)) :=
    divisionAlgebraDeterminantResidue_linearIndependent_lifts x hres
  letI : Fintype (Module.Free.ChooseBasisIndex
      (NormValuationResidue (F := F))
      (DivisionAlgebraDeterminantResidue (F := F) (A := A))) :=
    Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis b]
  exact hlift.fintype_card_le_finrank

/-- Finite base residue field plus finite residue degree makes the determinant residue skew field
finite as a type. -/
noncomputable instance divisionAlgebraDeterminantResidue_finite
    [Finite (NormValuationResidue (F := F))] :
    Finite (DivisionAlgebraDeterminantResidue (F := F) (A := A)) :=
  Module.finite_of_finite (NormValuationResidue (F := F))

/-- Wedderburn's little theorem: over a finite base residue field, the determinant residue division
ring is commutative. -/
theorem divisionAlgebraDeterminantResidue_mul_comm_of_finite_base_residue
    [Finite (NormValuationResidue (F := F))]
    (x y : DivisionAlgebraDeterminantResidue (F := F) (A := A)) :
    x * y = y * x := by
  exact mul_comm x y

/-- A primitive element of the finite determinant residue field lifts to an integral element whose
commutative generated subfield has degree at least the full residue degree.  This is the direct
bridge from the residue skew field to construction of an unramified maximal subfield. -/
theorem exists_residue_generator_lift_adjoin_finrank_ge
    [Finite (NormValuationResidue (F := F))] :
    ∃ x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A),
      Module.finrank (NormValuationResidue (F := F))
          (DivisionAlgebraDeterminantResidue (F := F) (A := A)) ≤
        Module.finrank F (Algebra.adjoin F ({(x : A)} : Set A)) := by
  let pb := Field.powerBasisOfFiniteOfSeparable
    (NormValuationResidue (F := F))
    (DivisionAlgebraDeterminantResidue (F := F) (A := A))
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective pb.gen
  refine ⟨x, ?_⟩
  have hres : LinearIndependent (NormValuationResidue (F := F))
      (fun i : Fin pb.dim => Ideal.Quotient.mk
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) (x ^ (i : ℕ))) := by
    simpa only [map_pow, hx, ← pb.basis_eq_pow] using pb.basis.linearIndependent
  have hlift : LinearIndependent F (fun i : Fin pb.dim => ((x ^ (i : ℕ) : _) : A)) :=
    divisionAlgebraDeterminantResidue_linearIndependent_lifts
      (fun i : Fin pb.dim => x ^ (i : ℕ)) hres
  let S := Algebra.adjoin F ({(x : A)} : Set A)
  let sx : Fin pb.dim → S := fun i =>
    ⟨(x : A) ^ (i : ℕ),
      pow_mem (Algebra.self_mem_adjoin_singleton F (x : A)) (i : ℕ)⟩
  have hsx : LinearIndependent F sx := by
    apply LinearIndependent.of_comp S.val.toLinearMap
    change LinearIndependent F (fun i : Fin pb.dim => ((sx i : S) : A))
    convert hlift using 1
    funext i
    rfl
  rw [pb.finrank]
  change pb.dim ≤ Module.finrank F S
  simpa only [Fintype.card_fin] using hsx.fintype_card_le_finrank

/-- For a central division algebra with finite base residue field, the residue degree is at most
the degree of the algebra: in square form, `f² ≤ [A : F]`.  The proof extends the lifted residue
generator to a maximal commutative subfield and applies the double-centralizer dimension formula. -/
theorem finrank_divisionAlgebraDeterminantResidue_mul_self_le_finrank
    [Algebra.IsCentral F A] [Finite (NormValuationResidue (F := F))] :
    Module.finrank (NormValuationResidue (F := F))
          (DivisionAlgebraDeterminantResidue (F := F) (A := A)) *
        Module.finrank (NormValuationResidue (F := F))
          (DivisionAlgebraDeterminantResidue (F := F) (A := A)) ≤
      Module.finrank F A := by
  obtain ⟨x, hx⟩ := exists_residue_generator_lift_adjoin_finrank_ge
    (F := F) (A := A)
  obtain ⟨S, hxS, hcommS, hfieldS, hmaxS⟩ :=
    exists_maximalCommutativeSubfield_containing_element F A (x : A)
  have hadjoinS : Module.finrank F (Algebra.adjoin F ({(x : A)} : Set A)) ≤
      Module.finrank F S :=
    Submodule.finrank_mono
      (s := (Algebra.adjoin F ({(x : A)} : Set A)).toSubmodule)
      (t := S.toSubmodule) hxS
  have hresS : Module.finrank (NormValuationResidue (F := F))
        (DivisionAlgebraDeterminantResidue (F := F) (A := A)) ≤ Module.finrank F S :=
    hx.trans hadjoinS
  calc
    Module.finrank (NormValuationResidue (F := F))
          (DivisionAlgebraDeterminantResidue (F := F) (A := A)) *
        Module.finrank (NormValuationResidue (F := F))
          (DivisionAlgebraDeterminantResidue (F := F) (A := A)) ≤
      Module.finrank F S * Module.finrank F S := Nat.mul_le_mul hresS hresS
    _ = Module.finrank F A :=
      maximalCommutativeSubfield_finrank_sq F A S hcommS hfieldS hmaxS

/-- A finite sum in the division algebra cannot vanish when one summand has strictly larger
determinant norm than every other summand.  This is the ultrametric cancellation lemma needed for
linear independence of representatives of distinct value-group cosets. -/
theorem divisionAlgebraDeterminant_sum_ne_zero_of_unique_max
    {ι : Type v} (s : Finset ι) (x : ι → A) {m : ι} (hm : m ∈ s)
    (hxm : x m ≠ 0)
    (hmax : ∀ j ∈ s, j ≠ m →
      ‖Algebra.norm F (x j)‖ < ‖Algebra.norm F (x m)‖) :
    ∑ j ∈ s, x j ≠ 0 := by
  classical
  let f : A → ℝ := fun a => ‖Algebra.norm F a‖
  have hfmpos : 0 < f (x m) := by
    exact norm_pos_iff.mpr (Algebra.norm_ne_zero_iff.mpr hxm)
  have hsmall : ∀ j ∈ s.erase m, f (x j) < f (x m) := by
    intro j hj
    exact hmax j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  have hrest_aux : ∀ t : Finset ι, t ⊆ s.erase m →
      f (∑ j ∈ t, x j) < f (x m) := by
    intro t
    induction t using Finset.induction with
    | empty => intro _; simpa [f, Algebra.norm_zero] using hfmpos
    | @insert a t ha ih =>
        intro ht
        rw [Finset.sum_insert ha]
        refine lt_of_le_of_lt (divisionAlgebra_norm_isNonarchimedean
          (F := F) (A := A) (x a) (∑ j ∈ t, x j)) ?_
        exact max_lt
          (hsmall a (ht (Finset.mem_insert_self a t)))
          (ih (fun j hj => ht (Finset.mem_insert_of_mem hj)))
  have hrest : f (∑ j ∈ s.erase m, x j) < f (x m) :=
    hrest_aux (s.erase m) le_rfl
  have hne : f (∑ j ∈ s.erase m, x j) ≠ f (x m) := ne_of_lt hrest
  have hadd := IsNonarchimedean.add_eq_max_of_ne' f
    (divisionAlgebra_norm_isNonarchimedean (F := F) (A := A))
    (fun a => (divisionAlgebra_norm_norm_neg (F := F) (A := A) a).symm) hne
  have hsum : ∑ j ∈ s, x j = (∑ j ∈ s.erase m, x j) + x m := by
    exact (Finset.sum_erase_add s x hm).symm
  intro hzero
  have hz : (∑ j ∈ s.erase m, x j) + x m = 0 := hsum.symm.trans hzero
  rw [hz] at hadd
  simp only [f, Algebra.norm_zero, norm_zero, max_eq_right hrest.le] at hadd
  exact hfmpos.ne' hadd.symm

/-- Families separated by determinant norm after every nonzero base scalar rescaling are linearly
independent.  Distinct coset representatives for the division-algebra value group modulo the base
value group satisfy exactly this hypothesis. -/
theorem linearIndependent_of_divisionAlgebraDeterminant_norm_separated
    {ι : Type v} (x : ι → A) (hx : ∀ i, x i ≠ 0)
    (hsep : ∀ {i j : ι}, i ≠ j → ∀ {a b : F}, a ≠ 0 → b ≠ 0 →
      ‖Algebra.norm F (a • x i)‖ ≠ ‖Algebra.norm F (b • x j)‖) :
    LinearIndependent F x := by
  classical
  rw [linearIndependent_iff']
  intro s g hrel i hi
  by_contra hgi
  let t := s.filter (fun j => g j ≠ 0)
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image t
    (fun j => ‖Algebra.norm F (g j • x j)‖) ⟨i, hit⟩
  have hgm : g m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hmterm : g m • x m ≠ 0 := smul_ne_zero hgm (hx m)
  have hstrict : ∀ j ∈ t, j ≠ m →
      ‖Algebra.norm F (g j • x j)‖ < ‖Algebra.norm F (g m • x m)‖ := by
    intro j hj hjm
    exact lt_of_le_of_ne (hmax j hj) (hsep hjm (Finset.mem_filter.mp hj).2 hgm)
  have hnonzero : ∑ j ∈ t, g j • x j ≠ 0 :=
    divisionAlgebraDeterminant_sum_ne_zero_of_unique_max
      t (fun j => g j • x j) hm hmterm hstrict
  have hrel_t : ∑ j ∈ t, g j • x j = 0 := by
    rw [show ∑ j ∈ t, g j • x j = ∑ j ∈ s, g j • x j by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hjs hjt
      have hgj : g j = 0 := by
        simpa only [t, Finset.mem_filter, hjs, true_and, not_not] using hjt
      simp only [hgj, zero_smul]
    ]
    exact hrel
  exact hnonzero hrel_t

end

end GaloisForLFunctions.HTGeometry.ABHN
