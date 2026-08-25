import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionValueResidueDegree
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionRootDeterminantNorm
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Value--residue equality for division algebras over local fields

The mixed products of relative determinant-value representatives and integral residue-basis lifts
were previously known to be linearly independent.  This module proves they span when the base field
is locally compact.

The proof uses the complete root-determinant norm.  Properness gives a best approximation to an
arbitrary element from the mixed span.  If its error is nonzero, its relative value class first
normalizes it to determinant norm one; expanding its nonzero residue in the chosen residue basis
then produces a mixed-span correction with strictly smaller error.  This contradicts minimality.

Consequently the fundamental inequality is an equality:

`|Γ_A / Γ_F| * [Ā : F̄] = [A : F]`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open Module

universe u

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [DivisionRing A] [Algebra F A] [Module.Finite F A]

omit [CompleteSpace F] [IsUltrametricDist F] in
/-- Every nonzero element has the same determinant size as a central rescaling of the chosen
representative of its relative determinant-value class. -/
theorem divisionAlgebraDeterminant_exists_scaled_valueRepresentative_same_norm
    {y : A} (hy : y ≠ 0) :
    ∃ q : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A),
      ∃ c : F, c ≠ 0 ∧
        ‖Algebra.norm F
            (c • (divisionAlgebraDeterminantValueRepresentative q : A))‖ =
          ‖Algebra.norm F y‖ := by
  let yu : Aˣ := Units.mk0 y hy
  let q : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A) := yu
  let r : Aˣ := divisionAlgebraDeterminantValueRepresentative q
  have hq : (r : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) =
      (yu : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) := by
    exact divisionAlgebraDeterminantValueRepresentative_mk q
  have hker : yu / r ∈
      divisionAlgebraDeterminantValueKernel (F := F) (A := A) := by
    exact QuotientGroup.eq_iff_div_mem.mp hq.symm
  rw [divisionAlgebraDeterminantValueKernel, Subgroup.mem_comap,
    divisionAlgebraBaseDeterminantValueSubgroup, MonoidHom.mem_range] at hker
  obtain ⟨c, hc⟩ := hker
  refine ⟨q, (c : F), c.ne_zero, ?_⟩
  have hnn : ‖Algebra.norm F
      ((baseUnitsToDivisionAlgebraUnits (F := F) (A := A) c : Aˣ) : A)‖₊ =
      ‖Algebra.norm F ((yu / r : Aˣ) : A)‖₊ := by
    exact congrArg (fun z : NNRealˣ => ((z : NNRealˣ) : NNReal)) hc
  have hreal : ‖Algebra.norm F
      ((baseUnitsToDivisionAlgebraUnits (F := F) (A := A) c : Aˣ) : A)‖ =
      ‖Algebra.norm F ((yu / r : Aˣ) : A)‖ := by
    exact congrArg (fun z : NNReal => (z : ℝ)) hnn
  change ‖Algebra.norm F ((c : F) • (r : A))‖ = ‖Algebra.norm F y‖
  rw [Algebra.smul_def, map_mul, norm_mul]
  rw [show ((baseUnitsToDivisionAlgebraUnits (F := F) (A := A) c : Aˣ) : A) =
      algebraMap F A (c : F) by rfl] at hreal
  rw [show ((yu / r : Aˣ) : A) = y * (r : A)⁻¹ by
      simp [div_eq_mul_inv, yu],
    map_mul, norm_mul, Algebra.norm_inv, norm_inv] at hreal
  rw [hreal]
  have hr0 : ‖Algebra.norm F (r : A)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Algebra.norm_ne_zero_iff.mpr r.ne_zero)
  field_simp

/-- A determinant-norm-one element has a residue-basis lift approximation with error in the strict
determinant unit ball. -/
theorem divisionAlgebraDeterminant_exists_residueBasisCombination_close
    {a : A} (ha : ‖Algebra.norm F a‖ = 1) :
    ∃ g : DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A) → F,
      ‖Algebra.norm F
          (a - ∑ i, g i • (divisionAlgebraDeterminantResidueBasisLift i : A))‖ < 1 := by
  classical
  let I := DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A)
  letI : Fintype I := Fintype.ofFinite _
  let a0 : divisionAlgebraDeterminantValuationSubring (F := F) (A := A) :=
    ⟨a, ha.le⟩
  let abar : DivisionAlgebraDeterminantResidue (F := F) (A := A) :=
    Ideal.Quotient.mk
      (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) a0
  let d : I → NormValuationResidue (F := F) := fun i =>
    (divisionAlgebraDeterminantResidueBasis (F := F) (A := A)).repr abar i
  let c : I → NormValuationSubring (F := F) := fun i =>
    (Ideal.Quotient.mk_surjective (d i)).choose
  have hc (i : I) :
      Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (NormValuationSubring (F := F))) (c i) = d i :=
    (Ideal.Quotient.mk_surjective (d i)).choose_spec
  let p0 : divisionAlgebraDeterminantValuationSubring (F := F) (A := A) :=
    ∑ i : I,
      normValuationSubringToDivisionAlgebraDeterminantValuationSubring
          (F := F) (A := A) (c i) *
        divisionAlgebraDeterminantResidueBasisLift i
  have hpred :
      Ideal.Quotient.mk
          (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) p0 = abar := by
    change Ideal.Quotient.mk
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))
        (∑ i : I,
          normValuationSubringToDivisionAlgebraDeterminantValuationSubring
              (F := F) (A := A) (c i) *
            divisionAlgebraDeterminantResidueBasisLift i) = abar
    rw [map_sum]
    calc
      ∑ i : I,
          Ideal.Quotient.mk
              (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))
              (normValuationSubringToDivisionAlgebraDeterminantValuationSubring
                  (F := F) (A := A) (c i) *
                divisionAlgebraDeterminantResidueBasisLift i) =
          ∑ i : I, d i •
            divisionAlgebraDeterminantResidueBasis (F := F) (A := A) i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_mul]
        have hbase :
            Ideal.Quotient.mk
                (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))
                (normValuationSubringToDivisionAlgebraDeterminantValuationSubring
                  (F := F) (A := A) (c i)) =
              normValuationResidueToDivisionAlgebraDeterminantResidue
                (F := F) (A := A)
                (Ideal.Quotient.mk
                  (IsLocalRing.maximalIdeal (NormValuationSubring (F := F))) (c i)) := by
          rfl
        rw [hbase, hc, divisionAlgebraDeterminantResidueBasisLift_mk]
        rfl
      _ = abar :=
        (divisionAlgebraDeterminantResidueBasis (F := F) (A := A)).sum_repr abar
  have hdiff : a0 - p0 ∈
      divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub, hpred]
    change abar - abar = 0
    exact sub_self abar
  refine ⟨fun i => (c i : F), ?_⟩
  have hcoe : ((p0 : _) : A) =
      ∑ i : I, (c i : F) •
        (divisionAlgebraDeterminantResidueBasisLift i : A) := by
    change (divisionAlgebraDeterminantValuationSubring (F := F) (A := A)).subtype
        (∑ i : I,
          normValuationSubringToDivisionAlgebraDeterminantValuationSubring
              (F := F) (A := A) (c i) *
            divisionAlgebraDeterminantResidueBasisLift i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul]
    change algebraMap F A (c i : F) *
        (divisionAlgebraDeterminantResidueBasisLift i : A) =
      (c i : F) • (divisionAlgebraDeterminantResidueBasisLift i : A)
    rw [Algebra.smul_def]
  rw [← hcoe]
  change ‖Algebra.norm F (((a0 - p0 : _) : A))‖ < 1
  exact (mem_divisionAlgebraDeterminantMaximalIdeal_iff
    (F := F) (A := A) (a0 - p0)).mp hdiff

/-- Span of the products of relative value representatives and residue-basis lifts. -/
def divisionAlgebraDeterminantValueResidueSpan : Submodule F A :=
  Submodule.span F <| Set.range fun p :
      DivisionAlgebraDeterminantValueQuotient (F := F) (A := A) ×
        DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A) =>
    (divisionAlgebraDeterminantValueRepresentative p.1 : A) *
      (divisionAlgebraDeterminantResidueBasisLift p.2 : A)

/-- Every nonzero element admits a mixed-span correction of strictly smaller determinant size. -/
theorem divisionAlgebraDeterminant_exists_valueResidueSpan_approximation
    {y : A} (hy : y ≠ 0) :
    ∃ w ∈ divisionAlgebraDeterminantValueResidueSpan (F := F) (A := A),
      ‖Algebra.norm F (y - w)‖ < ‖Algebra.norm F y‖ := by
  classical
  let I := DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A)
  letI : Fintype I := Fintype.ofFinite _
  obtain ⟨q, c, hc0, hc⟩ :=
    divisionAlgebraDeterminant_exists_scaled_valueRepresentative_same_norm
      (F := F) (A := A) hy
  let r : A := divisionAlgebraDeterminantValueRepresentative q
  let z : A := c • r
  have hz0 : z ≠ 0 := smul_ne_zero hc0
    (divisionAlgebraDeterminantValueRepresentative q).ne_zero
  have hznorm : ‖Algebra.norm F z‖ = ‖Algebra.norm F y‖ := hc
  let a : A := z⁻¹ * y
  have hanorm : ‖Algebra.norm F a‖ = 1 := by
    change ‖Algebra.norm F (z⁻¹ * y)‖ = 1
    rw [map_mul, Algebra.norm_inv, norm_mul, norm_inv, hznorm]
    exact inv_mul_cancel₀ <| norm_ne_zero_iff.mpr <|
      Algebra.norm_ne_zero_iff.mpr hy
  obtain ⟨g, hg⟩ := divisionAlgebraDeterminant_exists_residueBasisCombination_close
    (F := F) (A := A) hanorm
  let p : A := ∑ i : I, g i •
    (divisionAlgebraDeterminantResidueBasisLift i : A)
  let w : A := ∑ i : I, (c * g i) •
    ((divisionAlgebraDeterminantValueRepresentative q : A) *
      (divisionAlgebraDeterminantResidueBasisLift i : A))
  have hwspan : w ∈
      divisionAlgebraDeterminantValueResidueSpan (F := F) (A := A) := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span <| Set.mem_range.mpr ⟨(q, i), rfl⟩
  have hwfactor : w = z * p := by
    change (∑ i : I, (c * g i) •
        ((divisionAlgebraDeterminantValueRepresentative q : A) *
          (divisionAlgebraDeterminantResidueBasisLift i : A))) =
      z * ∑ i : I, g i •
        (divisionAlgebraDeterminantResidueBasisLift i : A)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [z, r, Algebra.smul_def]
    calc
      algebraMap F A (c * g i) *
          ((divisionAlgebraDeterminantValueRepresentative q : A) *
            (divisionAlgebraDeterminantResidueBasisLift i : A)) =
        (algebraMap F A c * algebraMap F A (g i)) *
          ((divisionAlgebraDeterminantValueRepresentative q : A) *
            (divisionAlgebraDeterminantResidueBasisLift i : A)) := by rw [map_mul]
      _ = (algebraMap F A c *
          (divisionAlgebraDeterminantValueRepresentative q : A)) *
            (algebraMap F A (g i) *
              (divisionAlgebraDeterminantResidueBasisLift i : A)) := by
        calc
          (algebraMap F A c * algebraMap F A (g i)) *
              ((divisionAlgebraDeterminantValueRepresentative q : A) *
                (divisionAlgebraDeterminantResidueBasisLift i : A)) =
            algebraMap F A c *
              ((algebraMap F A (g i) *
                (divisionAlgebraDeterminantValueRepresentative q : A)) *
                  (divisionAlgebraDeterminantResidueBasisLift i : A)) := by
            simp only [mul_assoc]
          _ = algebraMap F A c *
              (((divisionAlgebraDeterminantValueRepresentative q : A) *
                algebraMap F A (g i)) *
                  (divisionAlgebraDeterminantResidueBasisLift i : A)) := by
            rw [Algebra.commutes (g i)
              (divisionAlgebraDeterminantValueRepresentative q : A)]
          _ = (algebraMap F A c *
              (divisionAlgebraDeterminantValueRepresentative q : A)) *
                (algebraMap F A (g i) *
                  (divisionAlgebraDeterminantResidueBasisLift i : A)) := by
            simp only [mul_assoc]
  have hyfactor : y = z * a := by
    change y = z * (z⁻¹ * y)
    rw [← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
  refine ⟨w, hwspan, ?_⟩
  have hdiff : y - w = z * (a - p) := by
    rw [hyfactor, hwfactor, mul_sub]
  rw [hdiff, map_mul, norm_mul, hznorm]
  have hgp : ‖Algebra.norm F (a - p)‖ < 1 := hg
  calc
    ‖Algebra.norm F y‖ * ‖Algebra.norm F (a - p)‖ <
        ‖Algebra.norm F y‖ * 1 :=
      mul_lt_mul_of_pos_left hgp <|
        norm_pos_iff.mpr (Algebra.norm_ne_zero_iff.mpr hy)
    _ = ‖Algebra.norm F y‖ := mul_one _

/-- Every nonzero element admits a mixed-span correction of strictly smaller root-determinant
norm. -/
theorem divisionAlgebraDeterminant_exists_valueResidueSpan_root_approximation
    {y : A} (hy : y ≠ 0) :
    ∃ w ∈ divisionAlgebraDeterminantValueResidueSpan (F := F) (A := A),
      divisionAlgebraRootDeterminantNorm (F := F) (y - w) <
        divisionAlgebraRootDeterminantNorm (F := F) y := by
  obtain ⟨w, hw, hdet⟩ :=
    divisionAlgebraDeterminant_exists_valueResidueSpan_approximation
      (F := F) (A := A) hy
  refine ⟨w, hw, ?_⟩
  apply Real.rpow_lt_rpow (norm_nonneg _) hdet
  exact inv_pos.mpr <| by
    exact_mod_cast Module.finrank_pos (R := F) (M := A)

/-- Properness makes the distance from any element to the mixed value--residue span attain its
minimum. -/
theorem divisionAlgebraDeterminant_exists_best_valueResidueSpan
    [LocallyCompactSpace F] (x : A) :
    ∃ w ∈ divisionAlgebraDeterminantValueResidueSpan (F := F) (A := A),
      ∀ v ∈ divisionAlgebraDeterminantValueResidueSpan (F := F) (A := A),
        divisionAlgebraRootDeterminantNorm (F := F) (x - w) ≤
          divisionAlgebraRootDeterminantNorm (F := F) (x - v) := by
  letI : NormedRing A :=
    divisionAlgebraRootDeterminantNormedRing (F := F) (A := A)
  letI : NormedSpace F A :=
    divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
  letI : ProperSpace A :=
    divisionAlgebraRootDeterminantProperSpace (F := F) (A := A)
  let W := divisionAlgebraDeterminantValueResidueSpan (F := F) (A := A)
  let s : Set A := Metric.closedBall x ‖x‖ ∩ (W : Set A)
  have hscompact : IsCompact s := by
    exact (isCompact_closedBall x ‖x‖).inter_right W.closed_of_finiteDimensional
  have hsnonempty : s.Nonempty := by
    refine ⟨0, ?_⟩
    constructor
    · simp [Metric.mem_closedBall, dist_eq_norm]
    · exact W.zero_mem
  have hfcont : Continuous fun w : A => ‖x - w‖ :=
    (continuous_const.sub continuous_id).norm
  obtain ⟨w, hws, hwmin⟩ :=
    hscompact.exists_isMinOn hsnonempty hfcont.continuousOn
  refine ⟨w, hws.2, ?_⟩
  intro v hv
  change ‖x - w‖ ≤ ‖x - v‖
  by_cases hvball : ‖x - v‖ ≤ ‖x‖
  · exact hwmin ⟨by simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev], hv⟩
  · have hwball : ‖x - w‖ ≤ ‖x‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hws.1
    exact hwball.trans <| le_of_lt <| lt_of_not_ge hvball

/-- Over a locally compact nonarchimedean base field, the mixed value--residue products span the
entire division algebra. -/
theorem divisionAlgebraDeterminantValueResidueSpan_eq_top [LocallyCompactSpace F] :
    divisionAlgebraDeterminantValueResidueSpan (F := F) (A := A) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨w, hw, hwmin⟩ :=
    divisionAlgebraDeterminant_exists_best_valueResidueSpan (F := F) (A := A) x
  by_cases hy : x - w = 0
  · have hxw : x = w := sub_eq_zero.mp hy
    simpa only [hxw] using hw
  · obtain ⟨v, hv, hvstrict⟩ :=
      divisionAlgebraDeterminant_exists_valueResidueSpan_root_approximation
        (F := F) (A := A) hy
    have hwv : w + v ∈
        divisionAlgebraDeterminantValueResidueSpan (F := F) (A := A) :=
      Submodule.add_mem _ hw hv
    have hmin := hwmin (w + v) hwv
    have hrewrite : x - (w + v) = (x - w) - v := by abel
    rw [hrewrite] at hmin
    exact ((not_lt_of_ge hmin) hvstrict).elim

/-- Basis of a local division algebra formed by value representatives times residue lifts. -/
noncomputable def divisionAlgebraDeterminantValueResidueBasis [LocallyCompactSpace F] :
    Basis
      (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A) ×
        DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A)) F A :=
  Basis.mk
    (divisionAlgebraDeterminantValueResidueBasis_linearIndependent (F := F) (A := A))
    (divisionAlgebraDeterminantValueResidueSpan_eq_top (F := F) (A := A)).ge

/-- Fundamental value--residue equality for finite division algebras over locally compact
nonarchimedean fields. -/
theorem divisionAlgebraDeterminantValueQuotient_natCard_mul_residue_finrank_eq_finrank
    [LocallyCompactSpace F] :
    Nat.card (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) *
        Module.finrank (NormValuationResidue (F := F))
          (DivisionAlgebraDeterminantResidue (F := F) (A := A)) =
      Module.finrank F A := by
  letI : Fintype (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) :=
    Fintype.ofFinite _
  letI : Fintype (DivisionAlgebraDeterminantResidueBasisIndex (F := F) (A := A)) :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    Module.finrank_eq_card_basis
      (divisionAlgebraDeterminantResidueBasis (F := F) (A := A)),
    Module.finrank_eq_card_basis
      (divisionAlgebraDeterminantValueResidueBasis (F := F) (A := A)),
    Fintype.card_prod]

end

end GaloisForLFunctions.HTGeometry.ABHN
