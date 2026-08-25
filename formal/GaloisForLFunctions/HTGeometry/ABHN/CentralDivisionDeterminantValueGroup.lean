import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionResidueFinite
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Determinant value groups of finite division algebras

The determinant absolute value defines a homomorphism from the unit group of a finite division
algebra to the positive nonnegative reals.  Quotienting by the inverse image of determinant values
of central base scalars gives the relative determinant value group.

Representatives of distinct relative value classes remain separated after arbitrary nonzero base
scalar rescaling.  Ultrametric cancellation therefore makes them linearly independent over the
base field.  In particular, the relative determinant value group is finite and its order is bounded
by the ambient vector-space dimension.  This is the value-group half of the valuation-theoretic
route to local Brauer exhaustion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [DivisionRing A] [Algebra F A] [Module.Finite F A]

/-- Determinant absolute value on division-algebra units, bundled as a group homomorphism. -/
noncomputable def divisionAlgebraDeterminantAbsoluteValueUnits : Aˣ →* NNRealˣ where
  toFun x := Units.mk0 ‖Algebra.norm F (x : A)‖₊ (by
    exact nnnorm_ne_zero_iff.mpr (Algebra.norm_ne_zero_iff.mpr x.ne_zero))
  map_one' := Units.ext (by simp)
  map_mul' x y := Units.ext (by simp [map_mul, nnnorm_mul])

/-- Central base units embedded into the division-algebra unit group. -/
noncomputable def baseUnitsToDivisionAlgebraUnits : Fˣ →* Aˣ :=
  Units.map (algebraMap F A).toMonoidHom

/-- Determinant values attained by nonzero central base scalars. -/
noncomputable def divisionAlgebraBaseDeterminantValueSubgroup : Subgroup NNRealˣ :=
  (divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)).comp
      (baseUnitsToDivisionAlgebraUnits (F := F) (A := A)) |>.range

/-- Division-algebra units whose determinant value already occurs on a central base scalar. -/
noncomputable def divisionAlgebraDeterminantValueKernel : Subgroup Aˣ :=
  (divisionAlgebraBaseDeterminantValueSubgroup (F := F) (A := A)).comap
    (divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A))

noncomputable instance divisionAlgebraBaseDeterminantValueSubgroup_normal :
    (divisionAlgebraBaseDeterminantValueSubgroup (F := F) (A := A)).Normal :=
  Subgroup.normal_of_isMulCommutative _

noncomputable instance divisionAlgebraDeterminantValueKernel_normal :
    (divisionAlgebraDeterminantValueKernel (F := F) (A := A)).Normal :=
  (Subgroup.normal_of_isMulCommutative
    (divisionAlgebraBaseDeterminantValueSubgroup (F := F) (A := A))).comap
      (divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A))

/-- Relative determinant value group `|N_A(Aˣ)| / |N_A(Fˣ)|`, presented as a quotient of `Aˣ`. -/
abbrev DivisionAlgebraDeterminantValueQuotient : Type u :=
  Aˣ ⧸ divisionAlgebraDeterminantValueKernel (F := F) (A := A)

omit [CompleteSpace F] [IsUltrametricDist F] in
@[simp]
theorem divisionAlgebraDeterminantAbsoluteValueUnits_coe (x : Aˣ) :
    ((divisionAlgebraDeterminantAbsoluteValueUnits
      (F := F) (A := A) x : NNRealˣ) : NNReal) =
      ‖Algebra.norm F (x : A)‖₊ := rfl

omit [CompleteSpace F] [IsUltrametricDist F] [Module.Finite F A] in
@[simp]
theorem baseUnitsToDivisionAlgebraUnits_coe (x : Fˣ) :
    ((baseUnitsToDivisionAlgebraUnits (F := F) (A := A) x : Aˣ) : A) =
      algebraMap F A (x : F) := rfl

/-- Chosen unit representative of a relative determinant value class. -/
noncomputable def divisionAlgebraDeterminantValueRepresentative
    (q : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) : Aˣ :=
  (QuotientGroup.mk_surjective q).choose

omit [CompleteSpace F] [IsUltrametricDist F] in
@[simp]
theorem divisionAlgebraDeterminantValueRepresentative_mk
    (q : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) :
    (divisionAlgebraDeterminantValueRepresentative q :
      DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) = q :=
  (QuotientGroup.mk_surjective q).choose_spec

omit [CompleteSpace F] [IsUltrametricDist F] in
/-- Distinct determinant value classes cannot acquire equal determinant norm after nonzero base
scalar rescaling. -/
theorem divisionAlgebraDeterminantValueRepresentative_separated
    {q r : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)}
    (hqr : q ≠ r) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖Algebra.norm F (a • (divisionAlgebraDeterminantValueRepresentative q : A))‖ ≠
      ‖Algebra.norm F (b • (divisionAlgebraDeterminantValueRepresentative r : A))‖ := by
  intro hnorm
  let au : Fˣ := Units.mk0 a ha
  let bu : Fˣ := Units.mk0 b hb
  let aq : Aˣ := baseUnitsToDivisionAlgebraUnits (F := F) (A := A) au *
    divisionAlgebraDeterminantValueRepresentative q
  let br : Aˣ := baseUnitsToDivisionAlgebraUnits (F := F) (A := A) bu *
    divisionAlgebraDeterminantValueRepresentative r
  have habs : divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A) aq =
      divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A) br := by
    apply Units.ext
    have hnn : ‖Algebra.norm F
        (a • (divisionAlgebraDeterminantValueRepresentative q : A))‖₊ =
        ‖Algebra.norm F
          (b • (divisionAlgebraDeterminantValueRepresentative r : A))‖₊ := by
      apply NNReal.eq
      exact hnorm
    simpa only [aq, br, au, bu, divisionAlgebraDeterminantAbsoluteValueUnits_coe,
      Units.val_mul, baseUnitsToDivisionAlgebraUnits_coe, Units.val_mk0,
      Algebra.smul_def] using hnn
  have hmem : divisionAlgebraDeterminantValueRepresentative q /
      divisionAlgebraDeterminantValueRepresentative r ∈
        divisionAlgebraDeterminantValueKernel (F := F) (A := A) := by
    rw [divisionAlgebraDeterminantValueKernel, Subgroup.mem_comap,
      divisionAlgebraBaseDeterminantValueSubgroup, MonoidHom.mem_range]
    refine ⟨bu / au, ?_⟩
    change divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
        (baseUnitsToDivisionAlgebraUnits (F := F) (A := A) (bu / au)) =
      divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
        (divisionAlgebraDeterminantValueRepresentative q /
          divisionAlgebraDeterminantValueRepresentative r)
    simp only [map_div]
    have habs' :
        divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
            (baseUnitsToDivisionAlgebraUnits (F := F) (A := A) au) *
          divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
            (divisionAlgebraDeterminantValueRepresentative q) =
        divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
            (baseUnitsToDivisionAlgebraUnits (F := F) (A := A) bu) *
          divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
            (divisionAlgebraDeterminantValueRepresentative r) := by
      simpa only [aq, br, map_mul] using habs
    calc
      divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
            (baseUnitsToDivisionAlgebraUnits (F := F) (A := A) bu) /
          divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
            (baseUnitsToDivisionAlgebraUnits (F := F) (A := A) au) =
        (divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
              (baseUnitsToDivisionAlgebraUnits (F := F) (A := A) bu) *
            divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
              (divisionAlgebraDeterminantValueRepresentative r)) /
          (divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
              (baseUnitsToDivisionAlgebraUnits (F := F) (A := A) au) *
            divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
              (divisionAlgebraDeterminantValueRepresentative r)) :=
        (mul_div_mul_right_eq_div _ _ _).symm
      _ = (divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
              (baseUnitsToDivisionAlgebraUnits (F := F) (A := A) au) *
            divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
              (divisionAlgebraDeterminantValueRepresentative q)) /
          (divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
              (baseUnitsToDivisionAlgebraUnits (F := F) (A := A) au) *
            divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
              (divisionAlgebraDeterminantValueRepresentative r)) := by rw [habs']
      _ = divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
              (divisionAlgebraDeterminantValueRepresentative q) /
          divisionAlgebraDeterminantAbsoluteValueUnits (F := F) (A := A)
            (divisionAlgebraDeterminantValueRepresentative r) :=
        mul_div_mul_left_eq_div _ _ _
  apply hqr
  rw [← divisionAlgebraDeterminantValueRepresentative_mk q,
    ← divisionAlgebraDeterminantValueRepresentative_mk r]
  exact QuotientGroup.eq_iff_div_mem.mpr hmem

/-- Representatives of all relative determinant value classes are linearly independent. -/
theorem divisionAlgebraDeterminantValueRepresentative_linearIndependent :
    LinearIndependent F
      (fun q : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A) =>
        (divisionAlgebraDeterminantValueRepresentative q : A)) := by
  apply linearIndependent_of_divisionAlgebraDeterminant_norm_separated
  · exact fun q => (divisionAlgebraDeterminantValueRepresentative q).ne_zero
  · intro q r hqr a b ha hb
    exact divisionAlgebraDeterminantValueRepresentative_separated hqr ha hb

/-- The relative determinant value group of a finite division algebra is finite. -/
noncomputable instance divisionAlgebraDeterminantValueQuotient_finite :
    Finite (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) :=
  divisionAlgebraDeterminantValueRepresentative_linearIndependent
    (F := F) (A := A) |>.finite

/-- The relative determinant value-group index is bounded by the ambient dimension. -/
theorem divisionAlgebraDeterminantValueQuotient_natCard_le_finrank :
    Nat.card (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) ≤
      Module.finrank F A := by
  letI : Fintype (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact divisionAlgebraDeterminantValueRepresentative_linearIndependent
    (F := F) (A := A) |>.fintype_card_le_finrank

end

end GaloisForLFunctions.HTGeometry.ABHN
