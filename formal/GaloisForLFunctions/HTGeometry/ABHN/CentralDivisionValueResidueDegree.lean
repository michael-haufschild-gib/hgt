import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionDeterminantValueGroup

/-!
# Coupled value and residue degree for finite division algebras

Normalize finite combinations of integral residue-basis lifts by a coefficient of maximal norm.
The normalized combination has nonzero reduction, hence is a unit of the determinant valuation
order.  Its determinant value therefore comes from the base field.

Multiplying residue-basis lifts by representatives of all relative determinant value classes gives
a linearly independent product family.  This proves the fundamental inequality

`|Γ_A / Γ_F| * [Ā : F̄] ≤ [A : F]`.

This is the coupled value/residue input toward defectlessness and local Brauer exhaustion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open Module

universe u v

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [DivisionRing A] [Algebra F A] [Module.Finite F A]

/-- A nonzero finite combination of integral residue-independent lifts has the same determinant
norm as a nonzero central base scalar. -/
theorem divisionAlgebraDeterminantResidueCombination_norm_eq_base
    {ι : Type v}
    (x : ι → divisionAlgebraDeterminantValuationSubring (F := F) (A := A))
    (hx : LinearIndependent (NormValuationResidue (F := F))
      (fun i => Ideal.Quotient.mk
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) (x i)))
    (s : Finset ι) (g : ι → F)
    (hy : ∑ i ∈ s, g i • (x i : A) ≠ 0) :
    ∃ c : F, c ≠ 0 ∧
      ‖Algebra.norm F (∑ i ∈ s, g i • (x i : A))‖ =
        ‖Algebra.norm F (algebraMap F A c)‖ := by
  classical
  let t := s.filter (fun i => g i ≠ 0)
  have ht : t.Nonempty := by
    by_contra hempty
    have hgzero : ∀ i ∈ s, g i = 0 := by
      intro i hi
      by_contra hgi
      exact hempty ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
    apply hy
    exact Finset.sum_eq_zero (fun i hi => by rw [hgzero i hi, zero_smul])
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image t (fun j => ‖g j‖) ht
  have hms : m ∈ s := (Finset.mem_filter.mp hm).1
  have hgm : g m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hmaxs : ∀ j ∈ s, ‖g j‖ ≤ ‖g m‖ := by
    intro j hj
    by_cases hgj : g j = 0
    · simp [hgj]
    · exact hmax j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
  let c : ι → NormValuationSubring (F := F) := fun j =>
    if hj : j ∈ s then
      ⟨(g m)⁻¹ * g j, by
        change NormedField.valuation ((g m)⁻¹ * g j) ≤ 1
        rw [NormedField.valuation_apply]
        have hle : ‖(g m)⁻¹ * g j‖ ≤ 1 := by
          rw [norm_mul, norm_inv]
          exact (inv_mul_le_one₀ (norm_pos_iff.mpr hgm)).mpr (hmaxs j hj)
        exact_mod_cast hle⟩
    else 0
  let z : divisionAlgebraDeterminantValuationSubring (F := F) (A := A) :=
    ∑ j ∈ s,
      normValuationSubringToDivisionAlgebraDeterminantValuationSubring
        (F := F) (A := A) (c j) * x j
  have hzcoe : (z : A) = algebraMap F A ((g m)⁻¹) *
      (∑ j ∈ s, g j • (x j : A)) := by
    change (divisionAlgebraDeterminantValuationSubring (F := F) (A := A)).subtype
      (∑ j ∈ s,
        normValuationSubringToDivisionAlgebraDeterminantValuationSubring
          (F := F) (A := A) (c j) * x j) = _
    rw [map_sum]
    simp only [map_mul]
    change ∑ j ∈ s, algebraMap F A (c j : F) * (x j : A) = _
    calc
      ∑ j ∈ s, algebraMap F A (c j : F) * (x j : A) =
          ∑ j ∈ s, ((g m)⁻¹ * g j) • (x j : A) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (c j : F) = (g m)⁻¹ * g j by simp [c, hj], Algebra.smul_def]
      _ = (g m)⁻¹ • ∑ j ∈ s, g j • (x j : A) := by
        simp only [Finset.smul_sum, smul_smul]
      _ = algebraMap F A ((g m)⁻¹) * ∑ j ∈ s, g j • (x j : A) :=
        Algebra.smul_def _ _
  have hzred : Ideal.Quotient.mk
      (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) z ≠ 0 := by
    intro hzero
    have hresrel :
        ∑ j ∈ s,
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (NormValuationSubring (F := F))) (c j)) •
            Ideal.Quotient.mk
              (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) (x j) = 0 := by
      change ∑ j ∈ s,
        normValuationResidueToDivisionAlgebraDeterminantResidue
            (F := F) (A := A)
            (Ideal.Quotient.mk
              (IsLocalRing.maximalIdeal (NormValuationSubring (F := F))) (c j)) *
          Ideal.Quotient.mk
            (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) (x j) = 0
      simpa only [z, map_sum, map_mul,
        normValuationResidueToDivisionAlgebraDeterminantResidue,
        Ideal.quotientMap_mk] using hzero
    have hc := (linearIndependent_iff'.mp hx) s
      (fun j => Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (NormValuationSubring (F := F))) (c j)) hresrel m hms
    have hcm : c m = 1 := by
      simp only [c, dif_pos hms]
      apply Subtype.ext
      exact inv_mul_cancel₀ hgm
    rw [hcm, map_one] at hc
    exact one_ne_zero hc
  have hznotmem : z ∉ divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A) := by
    intro hzmem
    exact hzred (Ideal.Quotient.eq_zero_iff_mem.mpr hzmem)
  have hznlt : ¬ ‖Algebra.norm F (z : A)‖ < 1 := by
    intro hlt
    exact hznotmem (mem_divisionAlgebraDeterminantMaximalIdeal_iff
      (F := F) (A := A) z |>.mpr hlt)
  have hzone : ‖Algebra.norm F (z : A)‖ = 1 :=
    le_antisymm z.property (not_lt.mp hznlt)
  have hyfactor : (∑ j ∈ s, g j • (x j : A)) = algebraMap F A (g m) * (z : A) := by
    rw [hzcoe]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hgm, map_one, one_mul]
  refine ⟨g m, hgm, ?_⟩
  rw [hyfactor, map_mul, norm_mul, hzone, mul_one]

/-- Index type of a chosen basis of the determinant residue division ring. -/
abbrev DivisionAlgebraDeterminantResidueBasisIndex := Module.Free.ChooseBasisIndex
  (NormValuationResidue (F := F))
  (DivisionAlgebraDeterminantResidue (F := F) (A := A))

/-- Chosen basis of the determinant residue division ring over the base residue field. -/
noncomputable def divisionAlgebraDeterminantResidueBasis : Basis (DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A))
    (NormValuationResidue (F := F))
    (DivisionAlgebraDeterminantResidue (F := F) (A := A)) :=
  Module.Free.chooseBasis _ _

/-- Integral lift of each chosen determinant residue basis vector. -/
noncomputable def divisionAlgebraDeterminantResidueBasisLift (i : DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A)) :
    divisionAlgebraDeterminantValuationSubring (F := F) (A := A) :=
  (Ideal.Quotient.mk_surjective (divisionAlgebraDeterminantResidueBasis (F := F) (A := A) i)).choose

/-- Reducing a chosen integral basis lift recovers its residue basis vector. -/
@[simp]
theorem divisionAlgebraDeterminantResidueBasisLift_mk (i : DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A)) :
    Ideal.Quotient.mk
      (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))
      (divisionAlgebraDeterminantResidueBasisLift i) = divisionAlgebraDeterminantResidueBasis (F := F) (A := A) i :=
  (Ideal.Quotient.mk_surjective (divisionAlgebraDeterminantResidueBasis (F := F) (A := A) i)).choose_spec

/-- Chosen integral lifts remain linearly independent after reduction. -/
theorem divisionAlgebraDeterminantResidueBasisLift_residue_linearIndependent :
    LinearIndependent (NormValuationResidue (F := F))
      (fun i : DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A) =>
        Ideal.Quotient.mk
          (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))
          (divisionAlgebraDeterminantResidueBasisLift i)) := by
  simpa only [divisionAlgebraDeterminantResidueBasisLift_mk] using
    (divisionAlgebraDeterminantResidueBasis (F := F) (A := A)).linearIndependent

/-- Chosen residue-basis lifts are linearly independent in the ambient division algebra. -/
theorem divisionAlgebraDeterminantResidueBasisLift_linearIndependent :
    LinearIndependent F
      (fun i : DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A) => (divisionAlgebraDeterminantResidueBasisLift i : A)) :=
  divisionAlgebraDeterminantResidue_linearIndependent_lifts
    (fun i : DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A) => divisionAlgebraDeterminantResidueBasisLift i)
    (divisionAlgebraDeterminantResidueBasisLift_residue_linearIndependent (F := F) (A := A))

/-- Products of determinant value representatives and residue-basis lifts are linearly independent
over the base field. -/
theorem divisionAlgebraDeterminantValueResidueBasis_linearIndependent :
    LinearIndependent F
      (fun p : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A) ×
          DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A) =>
        (divisionAlgebraDeterminantValueRepresentative p.1 : A) *
          (divisionAlgebraDeterminantResidueBasisLift p.2 : A)) := by
  classical
  let Q := DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)
  let I := DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A)
  letI : Fintype Q := Fintype.ofFinite _
  letI : Fintype I := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff]
  intro g hrel p
  by_contra hgp
  let y : Q → A := fun q => ∑ i : I, g (q, i) • (divisionAlgebraDeterminantResidueBasisLift i : A)
  have hyp : y p.1 ≠ 0 := by
    intro hyzero
    have hgzero := (Fintype.linearIndependent_iff.mp
      (divisionAlgebraDeterminantResidueBasisLift_linearIndependent (F := F) (A := A)))
      (fun i : I => g (p.1, i)) hyzero p.2
    exact hgp hgzero
  let t := Finset.univ.filter (fun q : Q => y q ≠ 0)
  have hpt : p.1 ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyp⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image t
    (fun q => ‖Algebra.norm F
      ((divisionAlgebraDeterminantValueRepresentative q : A) * y q)‖) ⟨p.1, hpt⟩
  have hterm_ne (q : Q) (hq : q ∈ t) :
      (divisionAlgebraDeterminantValueRepresentative q : A) * y q ≠ 0 :=
    mul_ne_zero (divisionAlgebraDeterminantValueRepresentative q).ne_zero
      (Finset.mem_filter.mp hq).2
  have hnorm_ne (q r : Q) (hq : q ∈ t) (hr : r ∈ t) (hqr : q ≠ r) :
      ‖Algebra.norm F
          ((divisionAlgebraDeterminantValueRepresentative q : A) * y q)‖ ≠
        ‖Algebra.norm F
          ((divisionAlgebraDeterminantValueRepresentative r : A) * y r)‖ := by
    obtain ⟨cq, hcq0, hcq⟩ := divisionAlgebraDeterminantResidueCombination_norm_eq_base
      (fun i : I => divisionAlgebraDeterminantResidueBasisLift i)
      (divisionAlgebraDeterminantResidueBasisLift_residue_linearIndependent (F := F) (A := A))
      Finset.univ (fun i : I => g (q, i)) (Finset.mem_filter.mp hq).2
    obtain ⟨cr, hcr0, hcr⟩ := divisionAlgebraDeterminantResidueCombination_norm_eq_base
      (fun i : I => divisionAlgebraDeterminantResidueBasisLift i)
      (divisionAlgebraDeterminantResidueBasisLift_residue_linearIndependent (F := F) (A := A))
      Finset.univ (fun i : I => g (r, i)) (Finset.mem_filter.mp hr).2
    have hqeq : ‖Algebra.norm F
        ((divisionAlgebraDeterminantValueRepresentative q : A) * y q)‖ =
        ‖Algebra.norm F
          (cq • (divisionAlgebraDeterminantValueRepresentative q : A))‖ := by
      rw [map_mul, norm_mul, hcq, Algebra.smul_def, map_mul, norm_mul]
      exact mul_comm _ _
    have hreq : ‖Algebra.norm F
        ((divisionAlgebraDeterminantValueRepresentative r : A) * y r)‖ =
        ‖Algebra.norm F
          (cr • (divisionAlgebraDeterminantValueRepresentative r : A))‖ := by
      rw [map_mul, norm_mul, hcr, Algebra.smul_def, map_mul, norm_mul]
      exact mul_comm _ _
    intro heq
    exact divisionAlgebraDeterminantValueRepresentative_separated hqr hcq0 hcr0
      (hqeq.symm.trans (heq.trans hreq))
  have hstrict : ∀ q ∈ t, q ≠ m →
      ‖Algebra.norm F
          ((divisionAlgebraDeterminantValueRepresentative q : A) * y q)‖ <
        ‖Algebra.norm F
          ((divisionAlgebraDeterminantValueRepresentative m : A) * y m)‖ := by
    intro q hq hqm
    exact lt_of_le_of_ne (hmax q hq) (hnorm_ne q m hq hm hqm)
  have hblocks_ne : ∑ q ∈ t,
      (divisionAlgebraDeterminantValueRepresentative q : A) * y q ≠ 0 :=
    divisionAlgebraDeterminant_sum_ne_zero_of_unique_max t
      (fun q => (divisionAlgebraDeterminantValueRepresentative q : A) * y q)
      hm (hterm_ne m hm) hstrict
  have hgroup : (∑ z : Q × I,
      g z • ((divisionAlgebraDeterminantValueRepresentative z.1 : A) *
        (divisionAlgebraDeterminantResidueBasisLift z.2 : A))) =
      ∑ q : Q, (divisionAlgebraDeterminantValueRepresentative q : A) * y q := by
    change (∑ z ∈ (Finset.univ ×ˢ Finset.univ),
      g z • ((divisionAlgebraDeterminantValueRepresentative z.1 : A) *
        (divisionAlgebraDeterminantResidueBasisLift z.2 : A))) =
      ∑ q ∈ Finset.univ,
        (divisionAlgebraDeterminantValueRepresentative q : A) * y q
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Algebra.smul_def]
    calc
      algebraMap F A (g (q, i)) *
          ((divisionAlgebraDeterminantValueRepresentative q : A) *
            (divisionAlgebraDeterminantResidueBasisLift i : A)) =
        (algebraMap F A (g (q, i)) *
          (divisionAlgebraDeterminantValueRepresentative q : A)) *
            (divisionAlgebraDeterminantResidueBasisLift i : A) := (mul_assoc _ _ _).symm
      _ = ((divisionAlgebraDeterminantValueRepresentative q : A) *
          algebraMap F A (g (q, i))) * (divisionAlgebraDeterminantResidueBasisLift i : A) := by
        rw [Algebra.commutes]
      _ = (divisionAlgebraDeterminantValueRepresentative q : A) *
          (algebraMap F A (g (q, i)) * (divisionAlgebraDeterminantResidueBasisLift i : A)) :=
        mul_assoc _ _ _
  have hblocks_zero : ∑ q ∈ t,
      (divisionAlgebraDeterminantValueRepresentative q : A) * y q = 0 := by
    rw [show ∑ q ∈ t,
        (divisionAlgebraDeterminantValueRepresentative q : A) * y q =
      ∑ q : Q, (divisionAlgebraDeterminantValueRepresentative q : A) * y q by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro q hquniv hqt
        have hyq : y q = 0 := by
          simpa only [t, Finset.mem_filter, hquniv, true_and, not_not] using hqt
        rw [hyq, mul_zero]
      ]
    rw [← hgroup]
    exact hrel
  exact hblocks_ne hblocks_zero

/-- Fundamental value/residue inequality for the determinant valuation:
`|Γ_A / Γ_F| * [Ā : F̄] ≤ [A : F]`. -/
theorem divisionAlgebraDeterminantValueQuotient_natCard_mul_residue_finrank_le_finrank :
    Nat.card (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) *
        Module.finrank (NormValuationResidue (F := F))
          (DivisionAlgebraDeterminantResidue (F := F) (A := A)) ≤
      Module.finrank F A := by
  letI : Fintype (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) :=
    Fintype.ofFinite _
  letI : Fintype (DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    Module.finrank_eq_card_basis (divisionAlgebraDeterminantResidueBasis (F := F) (A := A))]
  simpa only [Fintype.card_prod] using
    (divisionAlgebraDeterminantValueResidueBasis_linearIndependent (F := F) (A := A)).fintype_card_le_finrank

end

end GaloisForLFunctions.HTGeometry.ABHN
