import GaloisForLFunctions.HTGeometry.PaperDeterminantUnitRigidity
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.DeterminantLiftWeights

/-!
# A nonprincipal line ideal made principal by the determinant torsor

On the actual quadric `xy = z(z+1)`, the ideal `(x,z)` pulls back to `(b)`
under `(x,y,z) = (ab,dc,db)`. Scalar-unit rigidity and the Laurent fiber
coaction show that this ideal has no generator downstairs. Everything is
proved over an arbitrary field, including finite fields.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable (k : Type*) [Field k]

/-- The concrete two-generator ideal on the source quadric. -/
def paperQuadricLineIdeal : Ideal (Obstruction.B k) :=
  Ideal.span {Obstruction.bX k 0, Obstruction.bX k 2}

/-- A fiber-weight minus-one coordinate cannot come from the weight-zero quadric. -/
theorem paperDeterminant_b_not_in_quadricRange :
    DeterminantRing.b k ∉ Set.range (Obstruction.baseMap k) := by
  rintro ⟨q, hq⟩
  have hw := AlgHom.congr_fun (DeterminantLiftWeights.fiberCoaction_quadricMap k) q
  change DeterminantWeights.fiberCoaction k (Obstruction.baseMap k q) =
    LaurentPolynomial.C (Obstruction.baseMap k q) at hw
  rw [hq, DeterminantWeights.fiberCoaction_b] at hw
  have hz := congrArg (fun p : LaurentPolynomial (DeterminantRing.C k) => p.coeff 0) hw
  change (AddMonoidAlgebra.single (-1 : ℤ) (DeterminantRing.b k)).coeff 0 =
    (AddMonoidAlgebra.single (0 : ℤ) (DeterminantRing.b k)).coeff 0 at hz
  have hn : (-1 : ℤ) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  exact Obstruction.cX_ne_zero k 2 (by
    change DeterminantRing.b k = 0
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      hn, ↓reduceIte]
      using hz.symm)

/-- The actual torsor map makes the quadric line ideal principal, with generator `b`. -/
theorem paperQuadricLineIdeal_map :
    (paperQuadricLineIdeal k).map (Obstruction.baseMap k).toRingHom =
      Ideal.span {DeterminantRing.b k} := by
  rw [paperQuadricLineIdeal, Ideal.map_span]
  change Ideal.span ((Obstruction.baseMap k) ''
      {Obstruction.bX k 0, Obstruction.bX k 2}) = _
  simp only [Set.image_insert_eq, Set.image_singleton, Obstruction.baseMap_bX,
    Matrix.cons_val_zero]
  change Ideal.span {DeterminantRing.a k * DeterminantRing.b k,
      DeterminantRing.d k * DeterminantRing.b k} = _
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro q hq
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · exact Ideal.mem_span_singleton.mpr ⟨DeterminantRing.a k, mul_comm _ _⟩
    · rcases Set.mem_singleton_iff.mp hq with rfl
      exact Ideal.mem_span_singleton.mpr ⟨DeterminantRing.d k, mul_comm _ _⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    apply Ideal.mem_span_pair.mpr
    refine ⟨DeterminantRing.c k, -DeterminantRing.b k, ?_⟩
    calc
      _ = DeterminantRing.b k *
          (DeterminantRing.a k * DeterminantRing.c k -
            DeterminantRing.b k * DeterminantRing.d k) := by ring
      _ = DeterminantRing.b k := by rw [DeterminantRing.determinant_relation, mul_one]

/-- No element of the base quadric generates its line ideal. -/
theorem paperQuadricLineIdeal_not_principal :
    ¬ ∃ q : Obstruction.B k, paperQuadricLineIdeal k = Ideal.span {q} := by
  rintro ⟨q, hq⟩
  have hm := paperQuadricLineIdeal_map k
  rw [hq, Ideal.map_span, Set.image_singleton] at hm
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hm
  obtain ⟨c, hc⟩ := paperDeterminantUnit_eq_scalar k v
  apply paperDeterminant_b_not_in_quadricRange k
  refine ⟨q * algebraMap k (Obstruction.B k) (c : k), ?_⟩
  rw [map_mul, AlgHom.commutes]
  change (show DeterminantRing.C k from Obstruction.baseMap k q) *
    algebraMap k (DeterminantRing.C k) (c : k) = _
  rw [← hc]
  exact hv

/-- The first quadric coordinate is nonzero, so its fraction-field inverse is legitimate. -/
theorem paperQuadric_x_ne_zero : Obstruction.bX k 0 ≠ 0 := by
  intro h
  have hh := congrArg (Obstruction.baseMap k) h
  rw [Obstruction.baseMap_bX, map_zero] at hh
  change DeterminantRing.a k * DeterminantRing.b k = 0 at hh
  exact (mul_ne_zero (Obstruction.cX_ne_zero k 0) (Obstruction.cX_ne_zero k 2)) hh

end

end GaloisForLFunctions.HTGeometry
