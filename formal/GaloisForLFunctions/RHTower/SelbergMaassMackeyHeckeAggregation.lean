import GaloisForLFunctions.RHTower.SelbergMaassMackeyOrbitDoubleCoset

/-!
# Hecke-coset form of rational Mackey blocks

Each actual rational Mackey block is an explicit stabilizer-index multiple of
one descended positive-rational Hecke trace.  This is the summand identity
needed before finite orbit fibers can be aggregated into correspondence
coefficients.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint MulAction Subgroup
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- A rational Mackey block is its exact relative-index multiplicity times the
positive-rational Hecke trace of any Hecke element whose real matrix is the
block's rational correspondence. -/
theorem rationalMackey_blockTrace_eq_card_smul_rationalHeckeTrace
    (N : ℕ) (g h b : GL (Fin 2) ℚ)
    (r : rationalConjugateGroup N h)
    (hb : b.map (algebraMap ℚ ℝ) = r.val)
    (d : positiveRationalGLRealImage)
    (hdu : (g * h * b⁻¹).map (algebraMap ℚ ℝ) = d.val)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    let P := principalCongruenceGL N
    let G := rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
    let H := rationalConjugateGroup N h
    let J := P.subgroupOf H
    let R := rationalConjugateGroup N (g * h * b⁻¹)
    let M := R ⊓ P
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex P :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI : G.IsFiniteRelIndex H :=
      rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g) P h
    let L := (MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))).map
        (H.subtype.comp J.subtype)
    let fG := rationalMaassPullbackInvariant_general (rationalConjugateGroup N g) h
      (rationalMaassPullbackInvariant_general P g f)
    let fL := maassDoubleCosetBlockPullback G H J r fG
    letI : R.IsFiniteRelIndex P := rationalConjugateGroup_isFiniteRelIndex N (g * h * b⁻¹)
    letI : M.IsFiniteRelIndex P := by
      rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
      have hsub : M.subgroupOf P = R.subgroupOf P := by
        apply (Subgroup.map_subtype_inj).mp
        rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
        simp only [M]
        rw [inf_assoc, inf_idem]
      rw [hsub]
      exact Subgroup.finiteIndex_of_finite_quotient
    letI : L.IsFiniteRelIndex M :=
      rationalMackey_blockSource_isFiniteRelIndex_rationalDoubleCosetSource N g h b r hb
    letI : L.IsFiniteRelIndex P :=
      ⟨Subgroup.relIndex_ne_zero_trans
        (Subgroup.relIndex_ne_zero (H := L) (K := M))
        (Subgroup.relIndex_ne_zero (H := M) (K := P))⟩
    letI : Fintype (M ⧸ (L.subgroupOf M)) := Fintype.ofFinite _
    maassTraceFunction (H := P) fL =
      (Fintype.card (M ⧸ (L.subgroupOf M)) : ℂ) •
        rationalPrincipalHeckeTrace N d f := by
  dsimp only
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := P.subgroupOf H
  let R : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N (g * h * b⁻¹)
  let M : Subgroup (GL (Fin 2) ℝ) := R ⊓ P
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : G.IsFiniteRelIndex H :=
    rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g) P h
  let L : Subgroup (GL (Fin 2) ℝ) :=
    (MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))).map
        (H.subtype.comp J.subtype)
  let fG : glUpperHalfPlaneInvariantFunctions G :=
    rationalMaassPullbackInvariant_general (rationalConjugateGroup N g) h
      (rationalMaassPullbackInvariant_general P g f)
  let fL : glUpperHalfPlaneInvariantFunctions L :=
    maassDoubleCosetBlockPullback G H J r fG
  letI : R.IsFiniteRelIndex P := rationalConjugateGroup_isFiniteRelIndex N (g * h * b⁻¹)
  have hsub : M.subgroupOf P = R.subgroupOf P := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
    simp only [M]
    rw [inf_assoc, inf_idem]
  letI : M.IsFiniteRelIndex P := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, hsub]
    exact Subgroup.finiteIndex_of_finite_quotient
  letI : L.IsFiniteRelIndex M := by
    simpa only [P, G, H, J, R, M, L] using
      rationalMackey_blockSource_isFiniteRelIndex_rationalDoubleCosetSource N g h b r hb
  letI : L.IsFiniteRelIndex P :=
    ⟨Subgroup.relIndex_ne_zero_trans
      (Subgroup.relIndex_ne_zero (H := L) (K := M))
      (Subgroup.relIndex_ne_zero (H := M) (K := P))⟩
  letI : Fintype (M ⧸ (L.subgroupOf M)) := Fintype.ofFinite _
  have htrace := rationalPrincipalHeckeTrace_eq_rationalTrace_of_map N d (g * h * b⁻¹) hdu f
  rw [rationalMackey_blockTrace_eq_card_smul_rationalTrace N g h b r hb f, ← htrace]

/-- The actual finite orbit carrier occurring in the rational Mackey product. -/
abbrev rationalMackeyOrbit (N : ℕ) (g h : GL (Fin 2) ℚ) :=
  let P := principalCongruenceGL N
  let G := rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H := rationalConjugateGroup N h
  let J := P.subgroupOf H
  Quotient (orbitRel J (H ⧸ G.subgroupOf H))

/-- The exact stabilizer index carried by an actual rational Mackey orbit. -/
noncomputable def rationalMackeyBlockMultiplicity
    (N : ℕ) (g h : GL (Fin 2) ℚ) (q : rationalMackeyOrbit N g h) : ℕ := by
  dsimp only [rationalMackeyOrbit] at q
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := P.subgroupOf H
  let r : H := q.out.out
  let b : GL (Fin 2) ℚ := rationalMackeyRepresentativeLift N h r
  let R : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N (g * h * b⁻¹)
  let M : Subgroup (GL (Fin 2) ℝ) := R ⊓ P
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : G.IsFiniteRelIndex H :=
    rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g) P h
  let L : Subgroup (GL (Fin 2) ℝ) :=
    (MulAction.stabilizer J (QuotientGroup.mk r : H ⧸ G.subgroupOf H)).map
      (H.subtype.comp J.subtype)
  have hb : b.map (algebraMap ℚ ℝ) = r.val := by
    simpa only [b] using rationalMackeyRepresentativeLift_map N h r
  letI : R.IsFiniteRelIndex P := rationalConjugateGroup_isFiniteRelIndex N (g * h * b⁻¹)
  have hsub : M.subgroupOf P = R.subgroupOf P := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
    simp only [M]
    rw [inf_assoc, inf_idem]
  letI : M.IsFiniteRelIndex P := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, hsub]
    exact Subgroup.finiteIndex_of_finite_quotient
  letI : L.IsFiniteRelIndex M := by
    simpa only [P, G, H, J, R, M, L] using
      rationalMackey_blockSource_isFiniteRelIndex_rationalDoubleCosetSource N g h b r hb
  letI : Fintype (M ⧸ L.subgroupOf M) := Fintype.ofFinite _
  exact Fintype.card (M ⧸ L.subgroupOf M)

/-- The literal outer trace of one actual rational Mackey block. -/
noncomputable def rationalMackeyBlockTrace
    (N : ℕ) (g h : GL (Fin 2) ℚ) (q : rationalMackeyOrbit N g h)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) : ℍ → ℂ := by
  dsimp only [rationalMackeyOrbit] at q
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := P.subgroupOf H
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : G.IsFiniteRelIndex H :=
    rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g) P h
  letI : H.IsFiniteRelIndex P := rationalConjugateGroup_isFiniteRelIndex N h
  have hsub : T.subgroupOf P = H.subgroupOf P := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
    simp only [T, J, Subgroup.subgroupOf_map_subtype]
    rw [inf_comm P H, inf_assoc, inf_idem]
  letI : T.IsFiniteRelIndex P := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, hsub]
    exact Subgroup.finiteIndex_of_finite_quotient
  let fG : glUpperHalfPlaneInvariantFunctions G :=
    rationalMaassPullbackInvariant_general (rationalConjugateGroup N g) h
      (rationalMaassPullbackInvariant_general P g f)
  exact (maassDoubleCosetBlockTraceToInvariant G H P J q.out.out
    (by
      rintro x ⟨j, hj, rfl⟩
      exact hj) fG).1

/-- Every actual positive-orientation rational Mackey block equals its
stabilizer multiplicity times the descended trace of its own Hecke label. -/
theorem rationalMackeyBlockTrace_eq_multiplicity_smul_HeckeCosetTrace
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (q : rationalMackeyOrbit N g h)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    rationalMackeyBlockTrace N g h q f =
      (rationalMackeyBlockMultiplicity N g h q : ℂ) •
        rationalPrincipalHeckeCosetTrace N
          (rationalMackeyOrbitToHeckeCoset N g h hg hh q) f := by
  dsimp only [rationalMackeyOrbit] at q
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := P.subgroupOf H
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  let r : H := q.out.out
  let b : GL (Fin 2) ℚ := rationalMackeyRepresentativeLift N h r
  let d : positiveRationalGLRealImage :=
    rationalMackeyRepresentativeHeckeElement N g h hg hh r
  let R : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N (g * h * b⁻¹)
  let M : Subgroup (GL (Fin 2) ℝ) := R ⊓ P
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : G.IsFiniteRelIndex H :=
    rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g) P h
  letI : H.IsFiniteRelIndex P := rationalConjugateGroup_isFiniteRelIndex N h
  have hTsub : T.subgroupOf P = H.subgroupOf P := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
    simp only [T, J, Subgroup.subgroupOf_map_subtype]
    rw [inf_comm P H, inf_assoc, inf_idem]
  letI : T.IsFiniteRelIndex P := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, hTsub]
    exact Subgroup.finiteIndex_of_finite_quotient
  let L : Subgroup (GL (Fin 2) ℝ) :=
    (MulAction.stabilizer J (QuotientGroup.mk r : H ⧸ G.subgroupOf H)).map
      (H.subtype.comp J.subtype)
  let fG : glUpperHalfPlaneInvariantFunctions G :=
    rationalMaassPullbackInvariant_general (rationalConjugateGroup N g) h
      (rationalMaassPullbackInvariant_general P g f)
  let fL : glUpperHalfPlaneInvariantFunctions L :=
    maassDoubleCosetBlockPullback G H J r fG
  have hb : b.map (algebraMap ℚ ℝ) = r.val := by
    simpa only [b] using rationalMackeyRepresentativeLift_map N h r
  have hdu : (g * h * b⁻¹).map (algebraMap ℚ ℝ) = d.val := by
    simpa only [b, d, rationalMackeyRepresentativeProduct] using
      (rationalMackeyRepresentativeHeckeElement_val N g h hg hh r).symm
  letI : R.IsFiniteRelIndex P := rationalConjugateGroup_isFiniteRelIndex N (g * h * b⁻¹)
  have hsub : M.subgroupOf P = R.subgroupOf P := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
    simp only [M]
    rw [inf_assoc, inf_idem]
  letI : M.IsFiniteRelIndex P := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, hsub]
    exact Subgroup.finiteIndex_of_finite_quotient
  letI : L.IsFiniteRelIndex M := by
    simpa only [P, G, H, J, R, M, L] using
      rationalMackey_blockSource_isFiniteRelIndex_rationalDoubleCosetSource N g h b r hb
  letI : L.IsFiniteRelIndex P :=
    ⟨Subgroup.relIndex_ne_zero_trans
      (Subgroup.relIndex_ne_zero (H := L) (K := M))
      (Subgroup.relIndex_ne_zero (H := M) (K := P))⟩
  letI : Fintype (M ⧸ L.subgroupOf M) := Fintype.ofFinite _
  change maassTraceFunction (H := P) fL =
    (Fintype.card (M ⧸ L.subgroupOf M) : ℂ) •
      rationalPrincipalHeckeCosetTrace N (HeckeCoset.mk P P d) f
  simpa only [P, G, H, J, R, M, L, fG, fL, rationalPrincipalHeckeCosetTrace_mk] using
    rationalMackey_blockTrace_eq_card_smul_rationalHeckeTrace N g h b r hb d hdu f

/-- The rational Mackey orbit carrier is finite by its finite relative-index
source quotient. -/
@[implicit_reducible]
noncomputable def rationalMackeyOrbitFintype
    (N : ℕ) (g h : GL (Fin 2) ℚ) : Fintype (rationalMackeyOrbit N g h) := by
  dsimp only [rationalMackeyOrbit]
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := P.subgroupOf H
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : G.IsFiniteRelIndex H :=
    rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g) P h
  exact maassTraceDoubleCosetOrbitFintype G H J

/-- The finite-support correspondence coefficient at one actual Hecke label:
the sum of exact stabilizer multiplicities over its Mackey-orbit fiber. -/
noncomputable def rationalMackeyHeckeFiberCoefficient
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (D : HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N)) : ℂ := by
  classical
  letI : Fintype (rationalMackeyOrbit N g h) := rationalMackeyOrbitFintype N g h
  exact ∑ q ∈ Finset.univ with rationalMackeyOrbitToHeckeCoset N g h hg hh q = D,
    (rationalMackeyBlockMultiplicity N g h q : ℂ)

/-- The actual rational Mackey sum is a finite-support sum of descended Hecke
traces, with each coefficient the exact sum of stabilizer indices in its
Hecke-label fiber. -/
theorem rationalMackeyBlockTrace_sum_eq_fiberwise_HeckeCosetTrace
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    letI : DecidableEq (HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N)) := Classical.decEq _
    letI : Fintype (rationalMackeyOrbit N g h) := rationalMackeyOrbitFintype N g h
    (∑ q : rationalMackeyOrbit N g h, rationalMackeyBlockTrace N g h q f) =
      ∑ D ∈ Finset.univ.image (rationalMackeyOrbitToHeckeCoset N g h hg hh),
        rationalMackeyHeckeFiberCoefficient N g h hg hh D •
          rationalPrincipalHeckeCosetTrace N D f := by
  classical
  letI : Fintype (rationalMackeyOrbit N g h) := rationalMackeyOrbitFintype N g h
  let label := rationalMackeyOrbitToHeckeCoset N g h hg hh
  rw [sum_by_image_fibers label (fun q => rationalMackeyBlockTrace N g h q f)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [rationalMackeyHeckeFiberCoefficient]
  calc
    (∑ q ∈ Finset.univ with label q = D, rationalMackeyBlockTrace N g h q f) =
        ∑ q ∈ Finset.univ with label q = D,
          (rationalMackeyBlockMultiplicity N g h q : ℂ) •
            rationalPrincipalHeckeCosetTrace N (label q) f := by
      apply Finset.sum_congr rfl
      intro q hq
      exact rationalMackeyBlockTrace_eq_multiplicity_smul_HeckeCosetTrace N g h hg hh q f
    _ = ∑ q ∈ Finset.univ with label q = D,
          (rationalMackeyBlockMultiplicity N g h q : ℂ) •
            rationalPrincipalHeckeCosetTrace N D f := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    _ = (∑ q ∈ Finset.univ with label q = D,
          (rationalMackeyBlockMultiplicity N g h q : ℂ)) •
        rationalPrincipalHeckeCosetTrace N D f := by
      rw [Finset.sum_smul]

end

end GaloisForLFunctions.RHTower
