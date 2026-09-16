import GaloisForLFunctions.RHTower.SelbergMaassTraceMultiplicity
import GaloisForLFunctions.RHTower.SelbergMaassMackeyTraceComposition

/-!
# Rational source of a Maass Mackey block

A Mackey block has a literal rational source. If its relative-coset
representative has rational lift `b`, the block is the pullback by
`g * h * b⁻¹`; its stabilizer source lies in the intersection of this rational
source with the outer target. These identities isolate the remaining
finite-index comparison required to convert the Mackey product into Hecke
convolution.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint MulAction Subgroup
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- The mapped stabilizer source of a Mackey block lies in the intersection of
its conjugated ambient source and every outer target containing the acting
subgroup image. -/
theorem maassDoubleCosetBlockSource_le_conjugate_inf
    (Γ H K : Subgroup (GL (Fin 2) ℝ)) [Γ.IsFiniteRelIndex H]
    (J : Subgroup H) (r : H) (hTK : J.map H.subtype ≤ K) :
    ((MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))).map
        (H.subtype.comp J.subtype)) ≤
      (ConjAct.toConjAct r.val • Γ) ⊓ K := by
  rintro x ⟨j, hj, rfl⟩
  constructor
  · change (H.subtype.comp J.subtype) j ∈ ConjAct.toConjAct r.val • Γ
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change r.val⁻¹ * (H.subtype.comp J.subtype) j * r.val ∈ Γ
    have hcomp : (H.subtype.comp J.subtype) j = j.val.val := rfl
    rw [hcomp]
    exact (maassTrace_mem_stabilizer_iff Γ H J r j).mp hj
  · exact hTK ⟨j, j.2, rfl⟩

/-- The mapped stabilizer source of a Mackey block is exactly the intersection
of the conjugated ambient source with the mapped acting subgroup. -/
theorem maassDoubleCosetBlockSource_eq_conjugate_inf
    (Γ H : Subgroup (GL (Fin 2) ℝ)) [Γ.IsFiniteRelIndex H]
    (J : Subgroup H) (r : H) :
    ((MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))).map
        (H.subtype.comp J.subtype)) =
      (ConjAct.toConjAct r.val • Γ) ⊓ J.map H.subtype := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    constructor
    · change (H.subtype.comp J.subtype) j ∈ ConjAct.toConjAct r.val • Γ
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      change r.val⁻¹ * (H.subtype.comp J.subtype) j * r.val ∈ Γ
      have hcomp : (H.subtype.comp J.subtype) j = j.val.val := rfl
      rw [hcomp]
      exact (maassTrace_mem_stabilizer_iff Γ H J r j).mp hj
    · exact ⟨j, j.2, rfl⟩
  · rintro ⟨hconj, hJ⟩
    rcases hJ with ⟨j, hj, rfl⟩
    let j' : J := ⟨j, hj⟩
    refine ⟨j', ?_, rfl⟩
    change (H.subtype.comp J.subtype) j' ∈ ConjAct.toConjAct r.val • Γ at hconj
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hconj
    change r.val⁻¹ * (H.subtype.comp J.subtype) j' * r.val ∈ Γ at hconj
    have hcomp : (H.subtype.comp J.subtype) j' = j'.val.val := rfl
    rw [hcomp] at hconj
    apply (maassTrace_mem_stabilizer_iff Γ H J r j').mpr
    exact hconj

/-- Arithmeticity of the conjugated source, acting source, and outer target
makes every Mackey block source finite relative index in the corresponding
rational double-coset source. -/
theorem maassDoubleCosetBlockSource_isFiniteRelIndex_of_arithmetic
    (Γ H K : Subgroup (GL (Fin 2) ℝ)) [Γ.IsFiniteRelIndex H]
    (J : Subgroup H) (r : H)
    (hconj : (ConjAct.toConjAct r.val • Γ).IsArithmetic)
    (hacting : (J.map H.subtype).IsArithmetic)
    (hK : K.IsArithmetic) :
    ((MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))).map
        (H.subtype.comp J.subtype)).IsFiniteRelIndex
      ((ConjAct.toConjAct r.val • Γ) ⊓ K) := by
  letI : (ConjAct.toConjAct r.val • Γ).IsArithmetic := hconj
  letI : (J.map H.subtype).IsArithmetic := hacting
  letI : K.IsArithmetic := hK
  have hsource :
      ((MulAction.stabilizer J
        (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))).map
          (H.subtype.comp J.subtype)).IsArithmetic := by
    rw [maassDoubleCosetBlockSource_eq_conjugate_inf Γ H J r]
    infer_instance
  have htarget : ((ConjAct.toConjAct r.val • Γ) ⊓ K).IsArithmetic := by
    infer_instance
  exact ⟨hsource.is_commensurable.trans htarget.is_commensurable.symm |>.1⟩

/-- The image in an ambient group of the restriction of one arithmetic
subgroup to another is arithmetic. -/
theorem subgroupOf_map_subtype_isArithmetic
    (P H : Subgroup (GL (Fin 2) ℝ))
    (hP : P.IsArithmetic) (hH : H.IsArithmetic) :
    ((P.subgroupOf H).map H.subtype).IsArithmetic := by
  letI : P.IsArithmetic := hP
  letI : H.IsArithmetic := hH
  rw [Subgroup.subgroupOf_map_subtype]
  infer_instance

/-- Every rational conjugate of the principal Maass source is arithmetic. -/
theorem rationalConjugateGroup_isArithmetic (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalConjugateGroup N g).IsArithmetic :=
  ⟨(rationalConjugateGroup_commensurable N g).trans
    (principalCongruenceGL_isArithmetic N).is_commensurable⟩

/-- Conjugating the ambient source of two successive rational pullbacks by a
representative with rational lift `b` is the rational source of
`g * h * b⁻¹`. -/
theorem rationalMackey_conjugateSource_eq_rationalPullback
    (P : Subgroup (GL (Fin 2) ℝ)) (g h b : GL (Fin 2) ℚ)
    (r : GL (Fin 2) ℝ) (hb : b.map (algebraMap ℚ ℝ) = r) :
    ConjAct.toConjAct r • rationalPullbackConjugateGroup P (g * h) =
      rationalPullbackConjugateGroup P (g * h * b⁻¹) := by
  unfold rationalPullbackConjugateGroup
  let A : GL (Fin 2) ℝ :=
    g.map (algebraMap ℚ ℝ) * h.map (algebraMap ℚ ℝ)
  have hA : (g * h).map (algebraMap ℚ ℝ) = A := by
    rw [Matrix.GeneralLinearGroup.map_mul]
  have hu : (g * h * b⁻¹).map (algebraMap ℚ ℝ) = A * r⁻¹ := by
    dsimp [A]
    rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
      Matrix.GeneralLinearGroup.map_inv, hb]
  rw [hA, hu, ← mul_smul]
  have hmatrix :
      ConjAct.toConjAct r * (ConjAct.toConjAct A)⁻¹ =
        (ConjAct.toConjAct (A * r⁻¹))⁻¹ := by
    calc
      ConjAct.toConjAct r * (ConjAct.toConjAct A)⁻¹ =
          ConjAct.toConjAct r * ConjAct.toConjAct A⁻¹ := by
        rw [ConjAct.toConjAct_inv]
      _ = ConjAct.toConjAct (r * A⁻¹) :=
        (ConjAct.toConjAct_mul r A⁻¹).symm
      _ = ConjAct.toConjAct ((A * r⁻¹)⁻¹) := by
        congr 1
      _ = (ConjAct.toConjAct (A * r⁻¹))⁻¹ := by
        rw [ConjAct.toConjAct_inv]
  exact congrArg (fun x => x • P) hmatrix

/-- In the rational principal Mackey product, every block source is contained
in the source of the rational double-coset operator labelled by `g * h * b⁻¹`. -/
theorem rationalMackey_blockSource_le_rationalDoubleCosetSource
    (N : ℕ) (g h b : GL (Fin 2) ℚ)
    (r : rationalConjugateGroup N h)
    (hb : b.map (algebraMap ℚ ℝ) = r.val) :
    let G := rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
    let H := rationalConjugateGroup N h
    let J := (principalCongruenceGL N).subgroupOf H
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI : G.IsFiniteRelIndex H :=
      rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g)
        (principalCongruenceGL N) h
    ((MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))).map
        (H.subtype.comp J.subtype)) ≤
      rationalConjugateGroup N (g * h * b⁻¹) ⊓ principalCongruenceGL N := by
  dsimp only
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := (principalCongruenceGL N).subgroupOf H
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : G.IsFiniteRelIndex H :=
    rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g)
      (principalCongruenceGL N) h
  have hJ : J.map H.subtype ≤ principalCongruenceGL N := by
    simp only [J, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hGprod : G = rationalPullbackConjugateGroup (principalCongruenceGL N) (g * h) := by
    simpa only [G] using rationalPullbackConjugateGroup_mul (principalCongruenceGL N) g h
  have hsourceConj : ConjAct.toConjAct r.val • G =
      rationalConjugateGroup N (g * h * b⁻¹) := by
    rw [hGprod]
    exact rationalMackey_conjugateSource_eq_rationalPullback
      (principalCongruenceGL N) g h b r.val hb
  have hsource := maassDoubleCosetBlockSource_le_conjugate_inf G H
    (principalCongruenceGL N) J r hJ
  rw [hsourceConj] at hsource
  simpa only [G, H, J] using hsource

/-- In the rational principal Mackey product, every block source has finite
relative index in the rational double-coset source labelled by `g * h * b⁻¹`. -/
theorem rationalMackey_blockSource_isFiniteRelIndex_rationalDoubleCosetSource
    (N : ℕ) (g h b : GL (Fin 2) ℚ)
    (r : rationalConjugateGroup N h)
    (hb : b.map (algebraMap ℚ ℝ) = r.val) :
    let G := rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
    let H := rationalConjugateGroup N h
    let J := (principalCongruenceGL N).subgroupOf H
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI : G.IsFiniteRelIndex H :=
      rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g)
        (principalCongruenceGL N) h
    ((MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))).map
        (H.subtype.comp J.subtype)).IsFiniteRelIndex
      (rationalConjugateGroup N (g * h * b⁻¹) ⊓ principalCongruenceGL N) := by
  dsimp only
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := (principalCongruenceGL N).subgroupOf H
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : G.IsFiniteRelIndex H :=
    rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g)
      (principalCongruenceGL N) h
  have hGprod : G = rationalPullbackConjugateGroup (principalCongruenceGL N) (g * h) := by
    simpa only [G] using rationalPullbackConjugateGroup_mul (principalCongruenceGL N) g h
  have hsourceConj : ConjAct.toConjAct r.val • G =
      rationalConjugateGroup N (g * h * b⁻¹) := by
    rw [hGprod]
    exact rationalMackey_conjugateSource_eq_rationalPullback
      (principalCongruenceGL N) g h b r.val hb
  have hG : (ConjAct.toConjAct r.val • G).IsArithmetic := by
    rw [hsourceConj]
    exact rationalConjugateGroup_isArithmetic N (g * h * b⁻¹)
  have hH : H.IsArithmetic := rationalConjugateGroup_isArithmetic N h
  have hJ : (J.map H.subtype).IsArithmetic := by
    exact subgroupOf_map_subtype_isArithmetic (principalCongruenceGL N) H
      (principalCongruenceGL_isArithmetic N) hH
  have hsource := maassDoubleCosetBlockSource_isFiniteRelIndex_of_arithmetic G H
    (principalCongruenceGL N) J r hG hJ (principalCongruenceGL_isArithmetic N)
  rw [hsourceConj] at hsource
  simpa only [G, H, J] using hsource

/-- The literal function in a rational Mackey block equals the direct rational
pullback by the source matrix supplied by its representative lift. -/
theorem rationalMackey_blockPullback_eq_rationalPullback
    (P H : Subgroup (GL (Fin 2) ℝ)) (g h b : GL (Fin 2) ℚ)
    (J : Subgroup H) (r : H) (hb : b.map (algebraMap ℚ ℝ) = r.val)
    (f : glUpperHalfPlaneInvariantFunctions P) :
    (maassDoubleCosetBlockPullback
      (rationalPullbackConjugateGroup (rationalPullbackConjugateGroup P g) h) H J r
      (rationalMaassPullbackInvariant_general (rationalPullbackConjugateGroup P g) h
        (rationalMaassPullbackInvariant_general P g f))).1 =
      (rationalMaassPullbackInvariant_general P (g * h * b⁻¹) f).1 := by
  funext z
  change f.1 (g.map (algebraMap ℚ ℝ) •
    (h.map (algebraMap ℚ ℝ) • (r.val⁻¹ • z))) =
    f.1 ((g * h * b⁻¹).map (algebraMap ℚ ℝ) • z)
  rw [← mul_smul, ← mul_smul, ← hb, ← Matrix.GeneralLinearGroup.map_inv,
    ← Matrix.GeneralLinearGroup.map_mul, ← Matrix.GeneralLinearGroup.map_mul]

/-- Each rational principal Mackey block is its exact relative-index
multiplicity times the rational trace for the double-coset source carried by
its representative. -/
theorem rationalMackey_blockTrace_eq_card_smul_rationalTrace
    (N : ℕ) (g h b : GL (Fin 2) ℚ)
    (r : rationalConjugateGroup N h)
    (hb : b.map (algebraMap ℚ ℝ) = r.val)
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
    let fR := rationalMaassPullbackInvariant_general P (g * h * b⁻¹) f
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
        maassTraceFunction (H := P) fR := by
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
  let fR : glUpperHalfPlaneInvariantFunctions R :=
    rationalMaassPullbackInvariant_general P (g * h * b⁻¹) f
  let fM : glUpperHalfPlaneInvariantFunctions M :=
    maassInvariantRestrict (show M ≤ R from inf_le_left) fR
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
  have hLM : L ≤ M := by
    simpa only [P, G, H, J, R, M, L] using
      rationalMackey_blockSource_le_rationalDoubleCosetSource N g h b r hb
  have hfun : fL.1 = fM.1 := by
    change fL.1 = fR.1
    simpa only [P, G, H, J, R, fG, fL, fR] using
      rationalMackey_blockPullback_eq_rationalPullback P H g h b J r hb f
  have htrace : maassTraceFunction (H := P) fM = maassTraceFunction (H := P) fR :=
    maassTraceFunction_congr_source hsub fM fR rfl
  calc
    maassTraceFunction (H := P) fL =
        (Fintype.card (M ⧸ (L.subgroupOf M)) : ℂ) •
          maassTraceFunction (H := P) fM :=
      maassTraceFunction_eq_card_smul_of_le_of_targetInvariant L M P hLM inf_le_right fL fM hfun
    _ = (Fintype.card (M ⧸ (L.subgroupOf M)) : ℂ) •
        maassTraceFunction (H := P) fR := by
      rw [htrace]

end

end GaloisForLFunctions.RHTower
