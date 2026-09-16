import GaloisForLFunctions.RHTower.SelbergMaassDoubleCosetTrace
import GaloisForLFunctions.RHTower.SelbergMaassTraceCosetFactorization

/-!
# Analytic double-coset block operators

A Mackey block is the rational pullback at one relative-coset representative,
followed by finite trace from its stabilizer image to the acting-subgroup image.
This file packages that trace and proves that it equals the orbit of the
original finite trace summands.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint MulAction
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- The finite trace of one double-coset pullback block to the mapped acting
subgroup. -/
def maassDoubleCosetBlockTraceFunction
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (r : H) (f : glUpperHalfPlaneInvariantFunctions G) : ℍ → ℂ := by
  letI : ((MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))).map
        (H.subtype.comp J.subtype)).IsFiniteRelIndex (J.map H.subtype) :=
    maassTrace_mapped_stabilizer_isFiniteRelIndex_at G H J (QuotientGroup.mk r)
  exact maassTraceFunction (H := J.map H.subtype)
    (maassDoubleCosetBlockPullback G H J r f)

/-- The stabilizer-coset sum of original trace summands in one double-coset
block. -/
def maassDoubleCosetBlockOrbitSum
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (r : H) (f : glUpperHalfPlaneInvariantFunctions G) (z : ℍ) : ℂ := by
  letI : (MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))).FiniteIndex :=
    maassTrace_stabilizer_finiteIndex_at G H J (QuotientGroup.mk r)
  letI : Fintype (J ⧸ MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))) := Fintype.ofFinite _
  exact ∑ j, maassTraceOrbitSummand J f (QuotientGroup.mk r) j z

/-- The finite trace of a double-coset block is its stabilizer-coset orbit sum. -/
theorem maassDoubleCosetBlockTraceFunction_eq_orbitSum
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (r : H) (f : glUpperHalfPlaneInvariantFunctions G) (z : ℍ) :
    maassDoubleCosetBlockTraceFunction G H J r f z =
      maassDoubleCosetBlockOrbitSum G H J r f z := by
  unfold maassDoubleCosetBlockTraceFunction maassDoubleCosetBlockOrbitSum
  let S : Subgroup J := MulAction.stabilizer J (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))
  let K : Subgroup (GL (Fin 2) ℝ) := S.map (H.subtype.comp J.subtype)
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  letI : S.FiniteIndex := maassTrace_stabilizer_finiteIndex_at G H J (QuotientGroup.mk r)
  letI : K.IsFiniteRelIndex T :=
    maassTrace_mapped_stabilizer_isFiniteRelIndex_at G H J (QuotientGroup.mk r)
  letI : Fintype (J ⧸ S) := Fintype.ofFinite _
  letI : Fintype (T ⧸ K.subgroupOf T) := Fintype.ofFinite _
  let e := maassTrace_mappedStabilizerQuotientEquiv J
    (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))
  unfold maassTraceFunction
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro q hq
  induction q using Quotient.inductionOn with
  | h j =>
    rw [maassTrace_mappedStabilizerQuotientEquiv_mk]
    simp only [maassTraceQuotientFunc_mk, maassTraceOrbitSummand_mk]
    change f.1 (r.val⁻¹ • ((j.val.val)⁻¹ • z)) =
      f.1 ((j.val * r).val⁻¹ • z)
    rw [← mul_smul]
    congr 2

/-- A finite-type sum is independent of the enumeration chosen for its index type. -/
private theorem fintype_sum_eq_of_instances
    {ι A : Type*} [AddCommMonoid A] (I I' : Fintype ι) (h : ι → A) :
    (@Finset.univ ι I).sum h = (@Finset.univ ι I').sum h := by
  have huniv : (@Finset.univ ι I) = @Finset.univ ι I' := by
    ext x
    simp
  rw [huniv]

/-- Transporting a relative orbit representative transports its stabilizer-coset summand. -/
private theorem maassTraceOrbitSummand_congr
    {G H : Subgroup (GL (Fin 2) ℝ)} (J : Subgroup H)
    (f : glUpperHalfPlaneInvariantFunctions G) (x y : H ⧸ (G.subgroupOf H))
    (hxy : x = y) (r : J ⧸ MulAction.stabilizer J x) (z : ℍ) :
    maassTraceOrbitSummand J f x r z =
      maassTraceOrbitSummand J f y
        ((Subgroup.quotientEquivOfEq
          (congrArg (fun w => MulAction.stabilizer J w) hxy)) r) z := by
  subst y
  induction r using Quotient.inductionOn with
  | h j =>
    rw [Subgroup.quotientEquivOfEq_mk]

/-- The full finite trace is the sum of the analytic traces of its Mackey double-coset blocks.
The proof uses the existing orbit--stabilizer reindexing and explicitly transports the dependent
stabilizer quotients between chosen orbit representatives. -/
theorem maassTraceFunction_eq_sum_doubleCosetBlockTraceFunctions
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (f : glUpperHalfPlaneInvariantFunctions G) (z : ℍ) :
    let Ω := Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))
    letI : Fintype Ω := maassTraceDoubleCosetOrbitFintype G H J
    letI (q : Ω) : Fintype (J ⧸ MulAction.stabilizer J q.out) :=
      maassTraceDoubleCosetStabilizerFintype G H J q
    maassTraceFunction (H := H) f z =
      ∑ q : Ω, maassDoubleCosetBlockTraceFunction G H J q.out.out f z := by
  dsimp only
  letI : Fintype (H ⧸ (G.subgroupOf H)) := Fintype.ofFinite _
  letI : Fintype (Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))) :=
    maassTraceDoubleCosetOrbitFintype G H J
  letI (q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))) :
      Fintype (J ⧸ MulAction.stabilizer J q.out) :=
    maassTraceDoubleCosetStabilizerFintype G H J q
  rw [maassTraceFunction_doubleCoset G H J f z]
  apply Finset.sum_congr rfl
  intro q hq
  letI : (MulAction.stabilizer J
      (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H))).FiniteIndex :=
    maassTrace_stabilizer_finiteIndex_at G H J
      (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H))
  letI : Fintype (J ⧸ MulAction.stabilizer J
      (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H))) := Fintype.ofFinite _
  have hqout : q.out = (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H)) :=
    (Quotient.out_eq q.out).symm
  let e : J ⧸ MulAction.stabilizer J q.out ≃
      J ⧸ MulAction.stabilizer J (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H)) :=
    Subgroup.quotientEquivOfEq
      (congrArg (fun w => MulAction.stabilizer J w) hqout)
  calc
    (∑ r, maassTraceQuotientFunc f
        ((MulAction.selfEquivSigmaOrbitsQuotientStabilizer J
          (H ⧸ (G.subgroupOf H))).symm ⟨q, r⟩) z) =
        ∑ r, maassTraceOrbitSummand J f q.out r z := by
      apply Finset.sum_congr rfl
      intro r hr
      induction r using Quotient.inductionOn with
      | h j =>
        rw [maassTraceOrbitSummand_mk]
        rfl
    _ = ∑ r, maassTraceOrbitSummand J f
        (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H)) r z := by
      exact Fintype.sum_equiv e _ _ (fun r =>
        maassTraceOrbitSummand_congr J f q.out
          (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H)) hqout r z)
    _ = maassDoubleCosetBlockTraceFunction G H J q.out.out f z := by
      rw [maassDoubleCosetBlockTraceFunction_eq_orbitSum]
      unfold maassDoubleCosetBlockOrbitSum
      exact fintype_sum_eq_of_instances _ _ _

/-- The finite trace of a double-coset pullback, bundled at its stabilizer-image target. -/
def maassDoubleCosetBlockTraceInvariant
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (r : H) (f : glUpperHalfPlaneInvariantFunctions G) :
    glUpperHalfPlaneInvariantFunctions (J.map H.subtype) := by
  letI : ((MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))).map
        (H.subtype.comp J.subtype)).IsFiniteRelIndex (J.map H.subtype) :=
    maassTrace_mapped_stabilizer_isFiniteRelIndex_at G H J (QuotientGroup.mk r)
  exact maassTraceInvariant (H := J.map H.subtype)
    (maassDoubleCosetBlockPullback G H J r f)

/-- A double-coset block traced directly to an outer subgroup containing its target image. -/
def maassDoubleCosetBlockTraceToInvariant
    (G H K : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (r : H) (hTK : J.map H.subtype ≤ K) [(J.map H.subtype).IsFiniteRelIndex K]
    (f : glUpperHalfPlaneInvariantFunctions G) :
    glUpperHalfPlaneInvariantFunctions K := by
  let S : Subgroup J := MulAction.stabilizer J
    (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))
  let L : Subgroup (GL (Fin 2) ℝ) := S.map (H.subtype.comp J.subtype)
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  have hLT : L ≤ T := by
    rintro x ⟨s, hs, rfl⟩
    exact ⟨s, s.2, rfl⟩
  letI : L.IsFiniteRelIndex T :=
    maassTrace_mapped_stabilizer_isFiniteRelIndex_at G H J (QuotientGroup.mk r)
  letI : L.IsFiniteRelIndex K := ⟨by
    rw [← Subgroup.relIndex_mul_relIndex L T K hLT hTK]
    exact mul_ne_zero Subgroup.relIndex_ne_zero Subgroup.relIndex_ne_zero⟩
  exact maassTraceInvariant (H := K) (maassDoubleCosetBlockPullback G H J r f)

/-- Nested trace transitivity flattens a block trace followed by its outer trace into its direct
stabilizer-image-to-outer-target trace. -/
theorem maassTrace_block_then_outer_eq_direct
    (G H K : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (r : H) (hTK : J.map H.subtype ≤ K) [(J.map H.subtype).IsFiniteRelIndex K]
    (f : glUpperHalfPlaneInvariantFunctions G) :
    maassTraceFunction (H := K)
      (maassDoubleCosetBlockTraceInvariant G H J r f) =
      (maassDoubleCosetBlockTraceToInvariant G H K J r hTK f).1 := by
  let S : Subgroup J := MulAction.stabilizer J
    (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))
  let L : Subgroup (GL (Fin 2) ℝ) := S.map (H.subtype.comp J.subtype)
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  have hLT : L ≤ T := by
    rintro x ⟨s, hs, rfl⟩
    exact ⟨s, s.2, rfl⟩
  letI : L.IsFiniteRelIndex T :=
    maassTrace_mapped_stabilizer_isFiniteRelIndex_at G H J (QuotientGroup.mk r)
  letI : L.IsFiniteRelIndex K := ⟨by
    rw [← Subgroup.relIndex_mul_relIndex L T K hLT hTK]
    exact mul_ne_zero Subgroup.relIndex_ne_zero Subgroup.relIndex_ne_zero⟩
  change maassTraceFunction (H := K)
      (maassTraceInvariant (H := T) (maassDoubleCosetBlockPullback G H J r f)) =
    maassTraceFunction (H := K) (maassDoubleCosetBlockPullback G H J r f)
  exact (maassTraceFunction_transitive hLT hTK
    (maassDoubleCosetBlockPullback G H J r f)).symm

/-- Literal relative-coset representatives chosen from the quotient's `out`
representatives form a valid system of orbit representatives. -/
theorem maassTrace_orbitRepresentative_leftInverse
    {G H : Subgroup (GL (Fin 2) ℝ)} (J : Subgroup H) :
    Function.LeftInverse Quotient.mk''
      (fun q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))) =>
        (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H))) := by
  intro q
  change Quotient.mk'' (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H)) = q
  calc
    Quotient.mk'' (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H)) =
        Quotient.mk'' q.out := congrArg Quotient.mk'' (Quotient.out_eq q.out)
    _ = q := Quotient.out_eq q

/-- The representative-based orbit--stabilizer equivalence sends a literal
acting-group representative to its action on the chosen relative coset. -/
theorem maassTrace_repSelfEquiv_inverse_mk
    {G H : Subgroup (GL (Fin 2) ℝ)} (J : Subgroup H)
    (q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))) (j : J) :
    let e := MulAction.selfEquivSigmaOrbitsQuotientStabilizer' J
      (H ⧸ (G.subgroupOf H)) (maassTrace_orbitRepresentative_leftInverse J)
    e.symm ⟨q, QuotientGroup.mk j⟩ =
      j • (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H)) := by
  rfl

end

end GaloisForLFunctions.RHTower
