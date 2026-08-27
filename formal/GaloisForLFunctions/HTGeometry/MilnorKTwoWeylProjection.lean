import GaloisForLFunctions.HTGeometry.MilnorKTwoAmalgamatedProjection


/-!
# Milnor's exact monomial extension

The zero-symbol and Spin branches both project onto the full determinant-one monomial group.
Their kernels are exactly the central Milnor `K₂` ranges. Packaging the exhaustive branches gives
the premise-free exact extension underlying Milnor Lemma 12.4.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorDiagonalExtension

variable {F : Type*} [Field F]

theorem fin4AdjacentAction_diag (r : Fin 3)
    (x : MilnorDiagonalExtension F 4) :
    (fin4AdjacentAction (F := F) r x).diag =
      fin4PermuteDiagonal (F := F) (fin4AdjacentPerm r) x.diag := by
  fin_cases r <;> rfl

theorem Fin4AdjacentWord.action_diag (word : Fin4AdjacentWord)
    (x : MilnorDiagonalExtension F 4) :
    (word.action (F := F) x).diag =
      fin4PermuteDiagonal (F := F) word.perm x.diag := by
  induction word generalizing x with
  | one => rfl
  | snoc word r ih =>
      change (word.action (F := F) (fin4AdjacentAction (F := F) r x)).diag = _
      rw [ih, fin4AdjacentAction_diag]
      apply Subtype.ext
      funext p
      rfl

theorem fin4SwapAction_diag (i j : Fin 4)
    (x : MilnorDiagonalExtension F 4) :
    (fin4SwapAction (F := F) i j x).diag =
      fin4PermuteDiagonal (F := F) (Equiv.swap i j) x.diag := by
  rw [fin4SwapAction, Fin4AdjacentWord.action_diag,
    fin4SwapAdjacentWord_perm]

theorem fin4WeylGeneratorAction_diag {i j : Fin 4}
    (hij : i ≠ j) (u : Fˣ) (x : MilnorDiagonalExtension F 4) :
    (fin4WeylGeneratorAction (F := F) hij u x).diag =
      fin4PermuteDiagonal (F := F) (Equiv.swap i j) x.diag := by
  change (fin4SwapAction (F := F) i j
    (fin4DiagonalAction (F := F)
      (steinbergWeylRootScale (i := i) (j := j) u) x)).diag = _
  rw [fin4SwapAction_diag]
  rfl

theorem SteinbergWeylWord.fin4MilnorAction_diag
    (word : SteinbergWeylWord F (Fin 4))
    (x : MilnorDiagonalExtension F 4) :
    (SteinbergWeylWord.fin4MilnorAction word x).diag =
      fin4PermuteDiagonal (F := F) word.perm x.diag := by
  induction word generalizing x with
  | one => rfl
  | snoc word i j hij u ih =>
      change (SteinbergWeylWord.fin4MilnorAction word
        (fin4WeylGeneratorAction (F := F) hij u x)).diag = _
      rw [ih, fin4WeylGeneratorAction_diag]
      apply Subtype.ext
      funext p
      rfl

theorem fieldSignedWeylActionHom_diag
    (A : fieldSignedWeylSubgroup (F := F))
    (x : MilnorDiagonalExtension F 4) :
    (fieldSignedWeylActionHom A x).diag =
      fin4PermuteDiagonal (F := F) (fieldSignedPermutationHom A) x.diag := by
  change (SteinbergWeylWord.fin4MilnorAction
    (fieldSignedWeylChosenWord A) x).diag = _
  rw [SteinbergWeylWord.fin4MilnorAction_diag,
    (fieldSignedWeylChosenWord_data A).1]

theorem fieldProjection_action_map
    (A : fieldSignedWeylSubgroup (F := F))
    (x : MilnorDiagonalExtension F 4) :
    milnorDiagonalToFieldMonomial (fieldSignedWeylActionHom A x) =
      fieldSignedWeylToDetOneMonomial A *
        milnorDiagonalToFieldMonomial x *
        (fieldSignedWeylToDetOneMonomial A)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  change (detOneDiagonalMatrixUnitHom
      (fieldSignedWeylActionHom A x).diag : Matrix (Fin 4) (Fin 4) F) =
    (A.1 : Matrix (Fin 4) (Fin 4) F) *
      (detOneDiagonalMatrixUnitHom x.diag : Matrix (Fin 4) (Fin 4) F) *
      ((A.1⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F)
  rw [fieldSignedWeylActionHom_diag]
  exact congrArg Units.val (fieldSignedWeyl_conj_diagonal A x.diag).symm

theorem fieldProjection_common_map
    (x : fin4MilnorH0 (F := F)) :
    milnorDiagonalToFieldMonomial x.1 =
      fieldSignedWeylToDetOneMonomial
        (fin4MilnorH0ToFieldSignedWeyl x) := by
  apply Subtype.ext
  rfl

theorem fieldProjectionCompatible :
    AmalgamatedSemidirect.ProjectionCompatible
      (fin4MilnorH0 (F := F))
      (fin4MilnorH0ToFieldSignedWeyl (F := F))
      (fieldSignedWeylActionHom (F := F))
      (milnorDiagonalToFieldMonomial (F := F))
      (fieldSignedWeylToDetOneMonomial (F := F)) where
  action_map := fieldProjection_action_map
  common_map := fieldProjection_common_map

def milnorWZeroProjection (he : fin4MinusOneSymbol F = 0) :
    MilnorWZero he →* fieldDetOneMonomialSubgroup (F := F) :=
  AmalgamatedSemidirect.projection
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToFieldSignedWeyl (F := F))
    (fieldSignedWeylActionHom (F := F))
    (fieldSignedWeylCompatible he)
    (milnorDiagonalToFieldMonomial (F := F))
    (fieldSignedWeylToDetOneMonomial (F := F))
    fieldProjectionCompatible

theorem milnorWZeroProjection_surjective
    (he : fin4MinusOneSymbol F = 0) :
    Function.Surjective (milnorWZeroProjection he) := by
  apply AmalgamatedSemidirect.projection_surjective
  intro A
  obtain ⟨u, B, hA⟩ := fieldDetOneMonomial_factorization A
  let g : MilnorDiagonalExtension F 4 := ⟨u, 0⟩
  exact ⟨g, B, hA⟩

theorem milnorDiagonalToFieldMonomial_centralIncl
    (z : Multiplicative (MilnorKDeg F 2)) :
    milnorDiagonalToFieldMonomial (F := F) (centralIncl z) = 1 := by
  apply Subtype.ext
  change detOneDiagonalMatrixUnitHom (F := F) 1 = 1
  exact map_one _

theorem milnorDiagonalToFieldMonomial_kernel
    (g : MilnorDiagonalExtension F 4)
    (hg : milnorDiagonalToFieldMonomial (F := F) g = 1) :
    ∃ z : Multiplicative (MilnorKDeg F 2), centralIncl z = g := by
  have hdiag : g.diag = 1 := by
    apply detOneDiagonalMatrixUnitHom_injective
    exact congrArg Subtype.val hg
  refine ⟨Multiplicative.ofAdd g.central, ?_⟩
  apply MilnorDiagonalExtension.ext
  · simpa using hdiag.symm
  · simp

theorem fieldProjection_alignment
    (g : MilnorDiagonalExtension F 4)
    (A : fieldSignedWeylSubgroup (F := F))
    (hga : milnorDiagonalToFieldMonomial g *
      fieldSignedWeylToDetOneMonomial A = 1) :
    ∃ k : fin4MilnorH0 (F := F),
      fin4MilnorH0ToFieldSignedWeyl k = A := by
  have hunits : detOneDiagonalMatrixUnitHom g.diag * A.1 = 1 :=
    congrArg Subtype.val hga
  have hAunits : A.1 = (detOneDiagonalMatrixUnitHom g.diag)⁻¹ :=
    eq_inv_of_mul_eq_one_right hunits
  have hAmatrix : (A.1 : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix 1 (g.diag⁻¹).1 := by
    rw [hAunits, ← map_inv, detOneDiagonalMatrixUnitHom_matrix]
  have hperm : fieldSignedPermutationHom A = 1 :=
    (fieldSignedMonomialData_eq hAmatrix).1
  have hdiag : A ∈ fieldDiagonalSignedSubgroup := hperm
  rw [← fin4MilnorH0ToFieldSignedWeyl_range_eq_diagonal] at hdiag
  exact hdiag

theorem milnorWZeroProjection_ker
    (he : fin4MinusOneSymbol F = 0) :
    (milnorWZeroProjection he).ker =
      MonoidHom.range (milnorWZeroCentralIncl he) := by
  apply AmalgamatedSemidirect.projection_ker_eq_central_range
    (hcentralMap := milnorDiagonalToFieldMonomial_centralIncl)
    (halign := fieldProjection_alignment)
    (hkernel := milnorDiagonalToFieldMonomial_kernel)

theorem MilnorSpinWeyl.spinWeylToFieldSigned_surjective :
    Function.Surjective
      (MilnorSpinWeyl.spinWeylToFieldSigned (F := F)) := by
  intro A
  rcases A with ⟨A, hA⟩
  let P := fun B : (Matrix (Fin 4) (Fin 4) F)ˣ =>
    ∀ hB : B ∈ fieldSignedWeylSubgroup (F := F),
      ∃ s, MilnorSpinWeyl.spinWeylToFieldSigned (F := F) s = ⟨B, hB⟩
  have hP : P A := by
    apply Subgroup.closure_induction (p := fun B _ => P B)
      ?_ ?_ ?_ ?_ hA
    · intro B hB _
      obtain ⟨i, j, hij, rfl⟩ := hB
      exact ⟨MilnorSpinWeyl.weylLiftSpinWeyl i j hij,
        MilnorSpinWeyl.spinWeylToFieldSigned_weylLift i j hij⟩
    · intro _
      refine ⟨1, ?_⟩
      apply Subtype.ext
      exact congrArg Subtype.val
        (map_one (MilnorSpinWeyl.spinWeylToFieldSigned (F := F)))
    · intro B C hB hC ihB ihC hBC
      obtain ⟨s, hs⟩ := ihB hB
      obtain ⟨t, ht⟩ := ihC hC
      refine ⟨s * t, ?_⟩
      rw [map_mul, hs, ht]
      apply Subtype.ext
      rfl
    · intro B hB ihB hBinv
      obtain ⟨s, hs⟩ := ihB hB
      refine ⟨s⁻¹, ?_⟩
      rw [map_inv, hs]
      apply Subtype.ext
      rfl
  exact hP hA

def MilnorSpinWeyl.spinWeylToDetOneMonomial :
    MilnorSpinWeyl.spinWeylSubgroup →*
      fieldDetOneMonomialSubgroup (F := F) :=
  (fieldSignedWeylToDetOneMonomial (F := F)).comp
    (MilnorSpinWeyl.spinWeylToFieldSigned (F := F))

theorem MilnorSpinWeyl.spinProjection_action_map
    (s : MilnorSpinWeyl.spinWeylSubgroup)
    (x : MilnorDiagonalExtension F 4) :
    milnorDiagonalToFieldMonomial
        (MilnorSpinWeyl.spinWeylActionHom (F := F) s x) =
      MilnorSpinWeyl.spinWeylToDetOneMonomial (F := F) s *
        milnorDiagonalToFieldMonomial x *
        (MilnorSpinWeyl.spinWeylToDetOneMonomial (F := F) s)⁻¹ :=
  fieldProjection_action_map
    (MilnorSpinWeyl.spinWeylToFieldSigned (F := F) s) x

theorem MilnorSpinWeyl.spinProjection_common_map
    (he : fin4MinusOneSymbol F ≠ 0)
    (x : fin4MilnorH0 (F := F)) :
    milnorDiagonalToFieldMonomial x.1 =
      MilnorSpinWeyl.spinWeylToDetOneMonomial (F := F)
        (fin4MilnorH0ToSpinWeyl he x) := by
  change milnorDiagonalToFieldMonomial x.1 =
    fieldSignedWeylToDetOneMonomial
      (MilnorSpinWeyl.spinWeylToFieldSigned
        (fin4MilnorH0ToSpinWeyl he x))
  rw [MilnorSpinWeyl.spinWeylToFieldSigned_fin4MilnorH0 he x]
  exact fieldProjection_common_map x

theorem MilnorSpinWeyl.spinProjectionCompatible
    (he : fin4MinusOneSymbol F ≠ 0) :
    AmalgamatedSemidirect.ProjectionCompatible
      (fin4MilnorH0 (F := F))
      (fin4MilnorH0ToSpinWeyl he)
      (MilnorSpinWeyl.spinWeylActionHom (F := F))
      (milnorDiagonalToFieldMonomial (F := F))
      (MilnorSpinWeyl.spinWeylToDetOneMonomial (F := F)) where
  action_map := MilnorSpinWeyl.spinProjection_action_map
  common_map := MilnorSpinWeyl.spinProjection_common_map he

def MilnorSpinWeyl.milnorWNonzeroProjection
    (he : fin4MinusOneSymbol F ≠ 0) :
    MilnorSpinWeyl.MilnorWNonzero he →*
      fieldDetOneMonomialSubgroup (F := F) :=
  AmalgamatedSemidirect.projection
    (fin4MilnorH0 (F := F))
    (fin4MilnorH0ToSpinWeyl he)
    (MilnorSpinWeyl.spinWeylActionHom (F := F))
    (MilnorSpinWeyl.spinWeylCompatible he)
    (milnorDiagonalToFieldMonomial (F := F))
    (MilnorSpinWeyl.spinWeylToDetOneMonomial (F := F))
    (MilnorSpinWeyl.spinProjectionCompatible he)

theorem MilnorSpinWeyl.milnorWNonzeroProjection_surjective
    (he : fin4MinusOneSymbol F ≠ 0) :
    Function.Surjective (MilnorSpinWeyl.milnorWNonzeroProjection he) := by
  apply AmalgamatedSemidirect.projection_surjective
  intro A
  obtain ⟨u, B, hA⟩ := fieldDetOneMonomial_factorization A
  obtain ⟨s, hs⟩ := MilnorSpinWeyl.spinWeylToFieldSigned_surjective B
  let g : MilnorDiagonalExtension F 4 := ⟨u, 0⟩
  refine ⟨g, s, ?_⟩
  change A = detOneDiagonalToFieldMonomial u *
    fieldSignedWeylToDetOneMonomial
      (MilnorSpinWeyl.spinWeylToFieldSigned s)
  rw [hs]
  exact hA

theorem MilnorSpinWeyl.spinProjection_alignment
    (he : fin4MinusOneSymbol F ≠ 0)
    (g : MilnorDiagonalExtension F 4)
    (s : MilnorSpinWeyl.spinWeylSubgroup)
    (hgs : milnorDiagonalToFieldMonomial g *
      MilnorSpinWeyl.spinWeylToDetOneMonomial (F := F) s = 1) :
    ∃ k : fin4MilnorH0 (F := F), fin4MilnorH0ToSpinWeyl he k = s := by
  let A := MilnorSpinWeyl.spinWeylToFieldSigned (F := F) s
  have hA : milnorDiagonalToFieldMonomial g *
      fieldSignedWeylToDetOneMonomial A = 1 := hgs
  obtain ⟨k, hk⟩ := fieldProjection_alignment g A hA
  have hpermA : fieldSignedPermutationHom A = 1 := by
    rw [← hk]
    exact fin4MilnorH0ToFieldSignedWeyl_mem_diagonal k
  have hsdiag : s ∈ MilnorSpinWeyl.spinDiagonalWeylSubgroup := by
    change MilnorSpinWeyl.spinWeylPermutationHom s = 1
    rw [← MilnorSpinWeyl.fieldSignedPermutationHom_spinWeylToFieldSigned
      (F := F) s]
    exact hpermA
  rw [← fin4MilnorH0ToSpinWeyl_range_eq_spinDiagonal he]
    at hsdiag
  exact hsdiag

theorem MilnorSpinWeyl.milnorWNonzeroProjection_ker
    (he : fin4MinusOneSymbol F ≠ 0) :
    (MilnorSpinWeyl.milnorWNonzeroProjection he).ker =
      MonoidHom.range (MilnorSpinWeyl.milnorWNonzeroCentralIncl he) := by
  apply AmalgamatedSemidirect.projection_ker_eq_central_range
    (hcentralMap := milnorDiagonalToFieldMonomial_centralIncl)
    (halign := MilnorSpinWeyl.spinProjection_alignment he)
    (hkernel := milnorDiagonalToFieldMonomial_kernel)

/-- Exact conjugation of a normalized Weyl matrix by arbitrary signed-monomial data. -/
theorem fieldSignedWeyl_conj_weylGenerator
    (A : fieldSignedWeylSubgroup (F := F))
    (p q : Fin 4) (hpq : p ≠ q) :
    let σ := fieldSignedPermutationHom A
    let c := (fieldSignedMonomialData A).2
    let ratio := c p * (c q)⁻¹
    let hratio : ratio = 1 ∨ ratio = -1 :=
      MilnorSpinWeyl.unitSignRatio_eq_one_or_neg_one
        (fieldSignedMonomialData_signs A p)
        (fieldSignedMonomialData_signs A q)
    A * MilnorSpinWeyl.fieldWeylGeneratorSigned (F := F) p q hpq * A⁻¹ =
      fin4MilnorH0ToFieldSignedWeyl
        (fin4MilnorH0RootLift (σ.injective.ne hpq) ratio hratio) *
      MilnorSpinWeyl.fieldWeylGeneratorSigned (F := F) (σ p) (σ q)
        (σ.injective.ne hpq) := by
  dsimp only
  let σ := fieldSignedPermutationHom A
  let c := (fieldSignedMonomialData A).2
  have hA : (A.1 : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix σ c := fieldSignedMonomialData_matrix A
  have hAinv := signedMonomialMatrix_inv_data_field A.1 σ c hA
  apply Subtype.ext
  apply Units.ext
  change (A.1 : Matrix (Fin 4) (Fin 4) F) *
      (fieldWeylMatrixGenerator (F := F) p q hpq : Matrix (Fin 4) (Fin 4) F) *
      ((A.1⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
    (detOneDiagonalMatrixUnitHom
      (fin4MatsumotoDiagonal (σ p) (σ q) (c p * (c q)⁻¹)) :
        Matrix (Fin 4) (Fin 4) F) *
      (fieldWeylMatrixGenerator (F := F) (σ p) (σ q)
        (σ.injective.ne hpq) : Matrix (Fin 4) (Fin 4) F)
  rw [hA, fieldWeylMatrixGenerator_val, weylMatrix_eq_signedMonomial hpq,
    hAinv, detOneDiagonalMatrixUnitHom_matrix,
    fieldWeylMatrixGenerator_val,
    weylMatrix_eq_signedMonomial (σ.injective.ne hpq),
    signedMonomialMatrix_mul, signedMonomialMatrix_mul,
    signedMonomialMatrix_mul]
  rw [← Equiv.trans_assoc, Equiv.symm_trans_swap_trans]
  change signedMonomialMatrix (Equiv.swap (σ p) (σ q)) _ =
    signedMonomialMatrix (Equiv.swap (σ p) (σ q)) _
  congr 1
  funext s
  by_cases hsp : σ.symm s = p
  · have hs : s = σ p := by
      calc
        s = σ (σ.symm s) := (σ.apply_symm_apply s).symm
        _ = σ p := congrArg σ hsp
    subst s
    simp [Ne.symm hpq, fin4MatsumotoDiagonal, steinbergWeylRootScale]
  · by_cases hsq : σ.symm s = q
    · have hs : s = σ q := by
        calc
          s = σ (σ.symm s) := (σ.apply_symm_apply s).symm
          _ = σ q := congrArg σ hsq
      subst s
      simp [hpq, Ne.symm hpq, fin4MatsumotoDiagonal,
        steinbergWeylRootScale]
    · have hsp' : s ≠ σ p := by
        intro hs
        subst s
        simp at hsp
      have hsq' : s ≠ σ q := by
        intro hs
        subst s
        simp at hsq
      simp [hsp, hsq, hsp', hsq', fin4MatsumotoDiagonal,
        steinbergWeylRootScale, Equiv.swap_apply_def]

/-- Exact signed-monomial action on a canonical root-diagonal lift. -/
theorem fieldSignedWeylActionHom_matsumotoDiagonalLift
    (A : fieldSignedWeylSubgroup (F := F))
    {p q : Fin 4} (hpq : p ≠ q) (v : Fˣ) :
    fieldSignedWeylActionHom A (fin4MatsumotoDiagonalLift hpq v) =
      centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd
            (milnorSym2 F
              ((fieldSignedMonomialData A).2 p *
                ((fieldSignedMonomialData A).2 q)⁻¹) v)) *
        fin4MatsumotoDiagonalLift
          ((fieldSignedPermutationHom A).injective.ne_iff.mpr hpq) v := by
  let word := fieldSignedWeylChosenWord A
  have hdata := fieldSignedWeylChosenWord_data A
  change SteinbergWeylWord.fin4MilnorAction word
      (fin4MatsumotoDiagonalLift hpq v) = _
  rw [SteinbergWeylWord.fin4MilnorAction_matsumotoDiagonalLift,
    hdata.1, hdata.2]

theorem fin4DiagonalAction_centralIncl
    (a : Fin 4 → Fˣ) (z : Multiplicative (MilnorKDeg F 2)) :
    fin4DiagonalAction (F := F) a (centralIncl (F := F) (n := 4) z) =
      centralIncl z := by
  apply MilnorDiagonalExtension.ext <;> simp

private theorem conjugated_fieldSignedWeylAction_matsumotoDiagonalLift
    (g : MilnorDiagonalExtension F 4)
    (A : fieldSignedWeylSubgroup (F := F))
    {p q : Fin 4} (hpq : p ≠ q) (v : Fˣ) :
    g * fieldSignedWeylActionHom A (fin4MatsumotoDiagonalLift hpq v) * g⁻¹ =
      centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd
            (milnorSym2 F
              ((g.diag.1 ((fieldSignedPermutationHom A) p) *
                  (fieldSignedMonomialData A).2 p) *
                (g.diag.1 ((fieldSignedPermutationHom A) q) *
                  (fieldSignedMonomialData A).2 q)⁻¹) v)) *
        fin4MatsumotoDiagonalLift
          ((fieldSignedPermutationHom A).injective.ne_iff.mpr hpq) v := by
  rw [← fin4DiagonalAction_eq_conj g.diag g _ rfl,
    fieldSignedWeylActionHom_matsumotoDiagonalLift,
    map_mul, fin4DiagonalAction_centralIncl,
    fin4DiagonalAction_matsumotoDiagonalLift]
  apply MilnorDiagonalExtension.ext
  · simp
  · simp only [central_mul, centralIncl_central, toAdd_ofAdd]
    simp only [centralIncl_diag, diag_mul, one_mul,
      milnorDiagonalCocycle_one_left]
    simp only [mul_inv_rev, milnorSym2_mul_left, milnorSym2_inv_left]
    abel

/-- Generic form of Milnor Lemma 12.5 for any compatible Weyl cover mapping to signed
monomial matrices. It is the common proof behind the zero-symbol and Spin branches. -/
theorem amalgamated_conjugation_matsumotoDiagonalLift
    {W : Type*} [Group W]
    (i : fin4MilnorH0 (F := F) →* W)
    (rho : W →* MulAut (MilnorDiagonalExtension F 4))
    (h : AmalgamatedSemidirect.Compatible (fin4MilnorH0 (F := F)) i rho)
    (toSigned : W →* fieldSignedWeylSubgroup (F := F))
    (hrho : ∀ w, rho w = fieldSignedWeylActionHom (toSigned w))
    (wmap : W →* fieldDetOneMonomialSubgroup (F := F))
    (hwmap : ∀ w, wmap w = fieldSignedWeylToDetOneMonomial (toSigned w))
    (hp : AmalgamatedSemidirect.ProjectionCompatible
      (fin4MilnorH0 (F := F)) i rho
      (milnorDiagonalToFieldMonomial (F := F))
      wmap)
    (x : AmalgamatedSemidirect.Construction
      (fin4MilnorH0 (F := F)) i rho h)
    {p q : Fin 4} (hpq : p ≠ q) (v : Fˣ) :
    let iH := AmalgamatedSemidirect.inl (fin4MilnorH0 (F := F)) i rho h
    let projection := AmalgamatedSemidirect.projection
      (fin4MilnorH0 (F := F)) i rho h
      (milnorDiagonalToFieldMonomial (F := F))
      wmap hp
    x * iH (fin4MatsumotoDiagonalLift hpq v) * x⁻¹ =
      iH (centralIncl (F := F) (n := 4)
        (Multiplicative.ofAdd
          (milnorSym2 F
            ((fieldMonomialData (projection x)).2 p *
              ((fieldMonomialData (projection x)).2 q)⁻¹) v))) *
      iH (fin4MatsumotoDiagonalLift
        ((fieldMonomialData (projection x)).1.injective.ne_iff.mpr hpq) v) := by
  dsimp only
  let iH := AmalgamatedSemidirect.inl (fin4MilnorH0 (F := F)) i rho h
  let iW := AmalgamatedSemidirect.inr (fin4MilnorH0 (F := F)) i rho h
  let projection := AmalgamatedSemidirect.projection
      (fin4MilnorH0 (F := F)) i rho h
      (milnorDiagonalToFieldMonomial (F := F))
      wmap hp
  obtain ⟨g, w, hx⟩ := AmalgamatedSemidirect.exists_inl_mul_inr
    (fin4MilnorH0 (F := F)) i rho h x
  let A := toSigned w
  have hproj : projection (iH g * iW w) =
      milnorDiagonalToFieldMonomial g *
        fieldSignedWeylToDetOneMonomial A := by
    dsimp [projection, iH, iW, A]
    rw [map_mul, AmalgamatedSemidirect.projection_inl,
      AmalgamatedSemidirect.projection_inr]
    rw [hwmap]
  have hmatrix :
      (((projection (iH g * iW w)).1 :
        (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
        signedMonomialMatrix (fieldSignedPermutationHom A)
          (fun r => g.diag.1 ((fieldSignedPermutationHom A) r) *
            (fieldSignedMonomialData A).2 r) := by
    rw [hproj]
    change (detOneDiagonalMatrixUnitHom g.diag :
        Matrix (Fin 4) (Fin 4) F) * (A.1 : Matrix (Fin 4) (Fin 4) F) = _
    rw [detOneDiagonalMatrixUnitHom_matrix,
      fieldSignedMonomialData_matrix, signedMonomialMatrix_mul]
    rfl
  have hdata : fieldMonomialData (projection (iH g * iW w)) =
      (fieldSignedPermutationHom A,
        fun r => g.diag.1 ((fieldSignedPermutationHom A) r) *
          (fieldSignedMonomialData A).2 r) :=
    Prod.ext (fieldMonomialData_eq hmatrix).1
      (fieldMonomialData_eq hmatrix).2
  rw [hx]
  calc
    (iH g * iW w) * iH (fin4MatsumotoDiagonalLift hpq v) *
        (iH g * iW w)⁻¹ =
      iH g *
        (iW w * iH (fin4MatsumotoDiagonalLift hpq v) * (iW w)⁻¹) *
        (iH g)⁻¹ := by group
    _ = iH g * iH (rho w (fin4MatsumotoDiagonalLift hpq v)) *
        (iH g)⁻¹ := by
      rw [AmalgamatedSemidirect.inr_conj_inl]
    _ = iH (g * fieldSignedWeylActionHom A
          (fin4MatsumotoDiagonalLift hpq v) * g⁻¹) := by
      rw [hrho]
      rw [map_mul, map_mul, map_inv]
    _ = iH (centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd
            (milnorSym2 F
              ((g.diag.1 ((fieldSignedPermutationHom A) p) *
                  (fieldSignedMonomialData A).2 p) *
                (g.diag.1 ((fieldSignedPermutationHom A) q) *
                  (fieldSignedMonomialData A).2 q)⁻¹) v)) *
        fin4MatsumotoDiagonalLift
          ((fieldSignedPermutationHom A).injective.ne_iff.mpr hpq) v) := by
      rw [conjugated_fieldSignedWeylAction_matsumotoDiagonalLift]
    _ = iH (centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd
            (milnorSym2 F
              ((g.diag.1 ((fieldSignedPermutationHom A) p) *
                  (fieldSignedMonomialData A).2 p) *
                (g.diag.1 ((fieldSignedPermutationHom A) q) *
                  (fieldSignedMonomialData A).2 q)⁻¹) v))) *
        iH (fin4MatsumotoDiagonalLift
          ((fieldSignedPermutationHom A).injective.ne_iff.mpr hpq) v) := by
      rw [map_mul]
    _ = _ := by rw [hdata]

private theorem conjugated_rootLift_mul_weylDelta
    (g : MilnorDiagonalExtension F 4)
    {p q : Fin 4} (hpq : p ≠ q) (u : Fˣ) :
    g * fin4MatsumotoDiagonalLift hpq u *
        fin4WeylGeneratorAction (F := F) hpq 1 g⁻¹ =
      fin4MatsumotoDiagonalLift hpq
        ((g.diag.1 p * (g.diag.1 q)⁻¹) * u) := by
  let r := g.diag.1 p * (g.diag.1 q)⁻¹
  calc
    g * fin4MatsumotoDiagonalLift hpq u *
          fin4WeylGeneratorAction (F := F) hpq 1 g⁻¹ =
        (g * fin4MatsumotoDiagonalLift hpq u * g⁻¹) *
          (g * fin4WeylGeneratorAction (F := F) hpq 1 g⁻¹) := by group
    _ = fin4DiagonalAction (F := F) g.diag.1
          (fin4MatsumotoDiagonalLift hpq u) *
        fin4MatsumotoDiagonalLift hpq r := by
      rw [fin4DiagonalAction_eq_conj g.diag g _ rfl,
        fin4Diagonal_conj_weylGeneratorAction]
    _ = fin4MatsumotoDiagonalLift hpq (r * u) := by
      rw [fin4DiagonalAction_matsumotoDiagonalLift]
      change centralIncl (F := F) (n := 4)
          (Multiplicative.ofAdd (milnorSym2 F r u)) *
          fin4MatsumotoDiagonalLift hpq u *
          fin4MatsumotoDiagonalLift hpq r = _
      rw [mul_assoc, fin4MatsumotoDiagonalLift_mul]
      rw [mul_comm u r]
      apply MilnorDiagonalExtension.ext
      · simp [r, mul_comm]
      · simp only [central_mul, centralIncl_central, centralIncl_diag,
          diag_mul, milnorDiagonalCocycle_one_left, toAdd_ofAdd]
        rw [milnorSym2_antisymm]
        abel

/-- Generic second identity in Milnor Lemma 12.5.  It combines exact Weyl-cover conjugation with
the diagonal cocycle law inside the amalgamated semidirect construction. -/
theorem amalgamated_conjugation_weylGenerator
    {W : Type*} [Group W]
    (i : fin4MilnorH0 (F := F) →* W)
    (rho : W →* MulAut (MilnorDiagonalExtension F 4))
    (h : AmalgamatedSemidirect.Compatible (fin4MilnorH0 (F := F)) i rho)
    (toSigned : W →* fieldSignedWeylSubgroup (F := F))
    (hrho : ∀ w, rho w = fieldSignedWeylActionHom (toSigned w))
    (wmap : W →* fieldDetOneMonomialSubgroup (F := F))
    (hwmap : ∀ w, wmap w = fieldSignedWeylToDetOneMonomial (toSigned w))
    (hp : AmalgamatedSemidirect.ProjectionCompatible
      (fin4MilnorH0 (F := F)) i rho
      (milnorDiagonalToFieldMonomial (F := F)) wmap)
    (weylLift : ∀ (p q : Fin 4), p ≠ q → W)
    (hweylSigned : ∀ (p q : Fin 4) (hpq : p ≠ q),
      toSigned (weylLift p q hpq) =
        MilnorSpinWeyl.fieldWeylGeneratorSigned (F := F) p q hpq)
    (hweylConj : ∀ (w : W) (p q : Fin 4) (hpq : p ≠ q),
      let A := toSigned w
      let σ := fieldSignedPermutationHom A
      let c := (fieldSignedMonomialData A).2
      let ratio := c p * (c q)⁻¹
      let hratio : ratio = 1 ∨ ratio = -1 :=
        MilnorSpinWeyl.unitSignRatio_eq_one_or_neg_one
          (fieldSignedMonomialData_signs A p)
          (fieldSignedMonomialData_signs A q)
      w * weylLift p q hpq * w⁻¹ =
        i (fin4MilnorH0RootLift (σ.injective.ne hpq) ratio hratio) *
          weylLift (σ p) (σ q) (σ.injective.ne hpq))
    (x : AmalgamatedSemidirect.Construction
      (fin4MilnorH0 (F := F)) i rho h)
    (p q : Fin 4) (hpq : p ≠ q) :
    let iH := AmalgamatedSemidirect.inl (fin4MilnorH0 (F := F)) i rho h
    let iW := AmalgamatedSemidirect.inr (fin4MilnorH0 (F := F)) i rho h
    let projection := AmalgamatedSemidirect.projection
      (fin4MilnorH0 (F := F)) i rho h
      (milnorDiagonalToFieldMonomial (F := F)) wmap hp
    let σ := (fieldMonomialData (projection x)).1
    let c := (fieldMonomialData (projection x)).2
    x * iW (weylLift p q hpq) * x⁻¹ =
      iH (fin4MatsumotoDiagonalLift (σ.injective.ne hpq)
        (c p * (c q)⁻¹)) *
      iW (weylLift (σ p) (σ q) (σ.injective.ne hpq)) := by
  dsimp only
  let iH := AmalgamatedSemidirect.inl (fin4MilnorH0 (F := F)) i rho h
  let iW := AmalgamatedSemidirect.inr (fin4MilnorH0 (F := F)) i rho h
  let projection := AmalgamatedSemidirect.projection
      (fin4MilnorH0 (F := F)) i rho h
      (milnorDiagonalToFieldMonomial (F := F)) wmap hp
  obtain ⟨g, w, hx⟩ := AmalgamatedSemidirect.exists_inl_mul_inr
    (fin4MilnorH0 (F := F)) i rho h x
  let A := toSigned w
  let σ := fieldSignedPermutationHom A
  let c := (fieldSignedMonomialData A).2
  let ratio := c p * (c q)⁻¹
  have hratio : ratio = 1 ∨ ratio = -1 :=
    MilnorSpinWeyl.unitSignRatio_eq_one_or_neg_one
      (fieldSignedMonomialData_signs A p)
      (fieldSignedMonomialData_signs A q)
  have hproj : projection (iH g * iW w) =
      milnorDiagonalToFieldMonomial g *
        fieldSignedWeylToDetOneMonomial A := by
    dsimp [projection, iH, iW, A]
    rw [map_mul, AmalgamatedSemidirect.projection_inl,
      AmalgamatedSemidirect.projection_inr]
    rw [hwmap]
  have hmatrix :
      (((projection (iH g * iW w)).1 :
        (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) =
        signedMonomialMatrix σ
          (fun r => g.diag.1 (σ r) * c r) := by
    rw [hproj]
    change (detOneDiagonalMatrixUnitHom g.diag :
        Matrix (Fin 4) (Fin 4) F) * (A.1 : Matrix (Fin 4) (Fin 4) F) = _
    rw [detOneDiagonalMatrixUnitHom_matrix,
      fieldSignedMonomialData_matrix, signedMonomialMatrix_mul]
    rfl
  have hdata : fieldMonomialData (projection (iH g * iW w)) =
      (σ, fun r => g.diag.1 (σ r) * c r) :=
    Prod.ext (fieldMonomialData_eq hmatrix).1
      (fieldMonomialData_eq hmatrix).2
  let hpq' : σ p ≠ σ q := σ.injective.ne hpq
  let k : fin4MilnorH0 (F := F) :=
    fin4MilnorH0RootLift hpq' ratio hratio
  have hrhoGen : rho (weylLift (σ p) (σ q) hpq') =
      fin4WeylGeneratorAction (F := F) hpq' 1 := by
    rw [hrho, hweylSigned]
    exact MilnorSpinWeyl.fieldSignedWeylActionHom_matrixGenerator
      (F := F) (σ p) (σ q) hpq'
  rw [hx]
  calc
    (iH g * iW w) * iW (weylLift p q hpq) * (iH g * iW w)⁻¹ =
        iH g *
          (iW w * iW (weylLift p q hpq) * (iW w)⁻¹) *
          (iH g)⁻¹ := by group
    _ = iH g * iW (w * weylLift p q hpq * w⁻¹) * (iH g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    _ = iH g * iW (i k * weylLift (σ p) (σ q) hpq') * (iH g)⁻¹ := by
      rw [show w * weylLift p q hpq * w⁻¹ =
          i k * weylLift (σ p) (σ q) hpq' by
        exact hweylConj w p q hpq]
    _ = iH g * (iH k * iW (weylLift (σ p) (σ q) hpq')) *
          (iH g)⁻¹ := by
      rw [map_mul, ← AmalgamatedSemidirect.common_identified]
    _ = iH (g * k.1 * rho (weylLift (σ p) (σ q) hpq') g⁻¹) *
          iW (weylLift (σ p) (σ q) hpq') := by
      rw [map_mul, map_mul, map_inv]
      rw [← map_inv (rho (weylLift (σ p) (σ q) hpq')) g]
      rw [← AmalgamatedSemidirect.inr_conj_inl
        (K := fin4MilnorH0 (F := F)) (i := i) (rho := rho) (h := h)]
      dsimp [iH, iW]
      rw [map_inv]
      group
    _ = iH (fin4MatsumotoDiagonalLift hpq'
          ((g.diag.1 (σ p) * (g.diag.1 (σ q))⁻¹) * ratio)) *
          iW (weylLift (σ p) (σ q) hpq') := by
      rw [hrhoGen]
      rw [show k.1 = fin4MatsumotoDiagonalLift hpq' ratio by rfl]
      rw [conjugated_rootLift_mul_weylDelta]
    _ = _ := by
      rw [hdata]
      congr 3
      simp only [ratio, mul_inv_rev]
      ac_rfl

structure MilnorWMonomialProjection
    (P : MilnorWPackage F) where
  projection : letI := P.groupW
    P.W →* fieldDetOneMonomialSubgroup (F := F)
  surjective : Function.Surjective projection
  ker_eq_central : letI := P.groupW
    projection.ker = MonoidHom.range P.centralIncl
  projection_diagonalIncl : letI := P.groupW
    ∀ h : MilnorDiagonalExtension F 4,
      projection (P.diagonalIncl h) = milnorDiagonalToFieldMonomial h
  projection_weylGenerator : letI := P.groupW
    ∀ (i j : Fin 4) (hij : i ≠ j),
      (projection (P.weylGenerator i j hij)).1 =
        steinbergToGL (steinbergWeyl hij (1 : Fˣ))
  conjugation_matsumotoDiagonalLift : letI := P.groupW
    ∀ (x : P.W) {p q : Fin 4} (hpq : p ≠ q) (v : Fˣ),
      x * P.diagonalIncl (fin4MatsumotoDiagonalLift hpq v) * x⁻¹ =
        P.centralIncl
          (Multiplicative.ofAdd
            (milnorSym2 F
              ((fieldMonomialData (projection x)).2 p *
                ((fieldMonomialData (projection x)).2 q)⁻¹) v)) *
        P.diagonalIncl (fin4MatsumotoDiagonalLift
          ((fieldMonomialData (projection x)).1.injective.ne_iff.mpr hpq) v)
  conjugation_weylGenerator : letI := P.groupW
    ∀ (x : P.W) (p q : Fin 4) (hpq : p ≠ q),
      let σ := (fieldMonomialData (projection x)).1
      let c := (fieldMonomialData (projection x)).2
      x * P.weylGenerator p q hpq * x⁻¹ =
        P.diagonalIncl (fin4MatsumotoDiagonalLift
          (σ.injective.ne hpq) (c p * (c q)⁻¹)) *
        P.weylGenerator (σ p) (σ q) (σ.injective.ne hpq)

theorem milnorWPackage_eq_zero (he : fin4MinusOneSymbol F = 0) :
    milnorWPackage F = milnorWZeroPackage he := by
  rw [milnorWPackage, dif_pos he]

theorem milnorWPackage_eq_nonzero (he : fin4MinusOneSymbol F ≠ 0) :
    milnorWPackage F = milnorWNonzeroPackage he := by
  rw [milnorWPackage, dif_neg he]

noncomputable def milnorWMonomialProjection :
    MilnorWMonomialProjection (milnorWPackage F) := by
  classical
  by_cases he : fin4MinusOneSymbol F = 0
  · rw [milnorWPackage_eq_zero he]
    exact
      { projection := milnorWZeroProjection he
        surjective := milnorWZeroProjection_surjective he
        ker_eq_central := milnorWZeroProjection_ker he
        projection_diagonalIncl := by
          intro h
          exact AmalgamatedSemidirect.projection_inl _ _ _ _ _ _ _ h
        projection_weylGenerator := by
          intro i j hij
          change ((milnorWZeroProjection he)
            (AmalgamatedSemidirect.inr
              (fin4MilnorH0 (F := F))
              (fin4MilnorH0ToFieldSignedWeyl (F := F))
              (fieldSignedWeylActionHom (F := F))
              (fieldSignedWeylCompatible he)
              (MilnorSpinWeyl.fieldWeylGeneratorSigned (F := F) i j hij))).1 = _
          have hp := AmalgamatedSemidirect.projection_inr
            (fin4MilnorH0 (F := F))
            (fin4MilnorH0ToFieldSignedWeyl (F := F))
            (fieldSignedWeylActionHom (F := F))
            (fieldSignedWeylCompatible he)
            (milnorDiagonalToFieldMonomial (F := F))
            (fieldSignedWeylToDetOneMonomial (F := F))
            fieldProjectionCompatible
            (MilnorSpinWeyl.fieldWeylGeneratorSigned (F := F) i j hij)
          exact congrArg Subtype.val hp
        conjugation_matsumotoDiagonalLift := by
          intro x p q hpq v
          exact amalgamated_conjugation_matsumotoDiagonalLift
            (i := fin4MilnorH0ToFieldSignedWeyl (F := F))
            (rho := fieldSignedWeylActionHom (F := F))
            (h := fieldSignedWeylCompatible he)
            (toSigned := MonoidHom.id _)
            (hrho := fun _ => rfl)
            (wmap := fieldSignedWeylToDetOneMonomial (F := F))
            (hwmap := fun _ => rfl)
            (hp := fieldProjectionCompatible (F := F)) x hpq v
        conjugation_weylGenerator := by
          intro x p q hpq
          exact amalgamated_conjugation_weylGenerator
            (i := fin4MilnorH0ToFieldSignedWeyl (F := F))
            (rho := fieldSignedWeylActionHom (F := F))
            (h := fieldSignedWeylCompatible he)
            (toSigned := MonoidHom.id _)
            (hrho := fun _ => rfl)
            (wmap := fieldSignedWeylToDetOneMonomial (F := F))
            (hwmap := fun _ => rfl)
            (hp := fieldProjectionCompatible (F := F))
            (weylLift := MilnorSpinWeyl.fieldWeylGeneratorSigned (F := F))
            (hweylSigned := fun _ _ _ => rfl)
            (hweylConj := fieldSignedWeyl_conj_weylGenerator (F := F))
            x p q hpq }
  · rw [milnorWPackage_eq_nonzero he]
    exact
      { projection := MilnorSpinWeyl.milnorWNonzeroProjection he
        surjective := MilnorSpinWeyl.milnorWNonzeroProjection_surjective he
        ker_eq_central := MilnorSpinWeyl.milnorWNonzeroProjection_ker he
        projection_diagonalIncl := by
          intro h
          exact AmalgamatedSemidirect.projection_inl _ _ _ _ _ _ _ h
        projection_weylGenerator := by
          intro i j hij
          change ((MilnorSpinWeyl.milnorWNonzeroProjection he)
            (AmalgamatedSemidirect.inr
              (fin4MilnorH0 (F := F))
              (fin4MilnorH0ToSpinWeyl he)
              (MilnorSpinWeyl.spinWeylActionHom (F := F))
              (MilnorSpinWeyl.spinWeylCompatible he)
              (MilnorSpinWeyl.weylLiftSpinWeyl i j hij))).1 = _
          have hp := AmalgamatedSemidirect.projection_inr
            (fin4MilnorH0 (F := F))
            (fin4MilnorH0ToSpinWeyl he)
            (MilnorSpinWeyl.spinWeylActionHom (F := F))
            (MilnorSpinWeyl.spinWeylCompatible he)
            (milnorDiagonalToFieldMonomial (F := F))
            (MilnorSpinWeyl.spinWeylToDetOneMonomial (F := F))
            (MilnorSpinWeyl.spinProjectionCompatible he)
            (MilnorSpinWeyl.weylLiftSpinWeyl i j hij)
          have hpval := congrArg Subtype.val hp
          change _ = (MilnorSpinWeyl.spinWeylToFieldSigned
            (MilnorSpinWeyl.weylLiftSpinWeyl i j hij)).1 at hpval
          rw [MilnorSpinWeyl.spinWeylToFieldSigned_weylLift] at hpval
          exact hpval
        conjugation_matsumotoDiagonalLift := by
          intro x p q hpq v
          exact amalgamated_conjugation_matsumotoDiagonalLift
            (i := fin4MilnorH0ToSpinWeyl he)
            (rho := MilnorSpinWeyl.spinWeylActionHom (F := F))
            (h := MilnorSpinWeyl.spinWeylCompatible he)
            (toSigned := MilnorSpinWeyl.spinWeylToFieldSigned (F := F))
            (hrho := fun _ => rfl)
            (wmap := MilnorSpinWeyl.spinWeylToDetOneMonomial (F := F))
            (hwmap := fun _ => rfl)
            (hp := MilnorSpinWeyl.spinProjectionCompatible he) x hpq v
        conjugation_weylGenerator := by
          intro x p q hpq
          exact amalgamated_conjugation_weylGenerator
            (i := fin4MilnorH0ToSpinWeyl he)
            (rho := MilnorSpinWeyl.spinWeylActionHom (F := F))
            (h := MilnorSpinWeyl.spinWeylCompatible he)
            (toSigned := MilnorSpinWeyl.spinWeylToFieldSigned (F := F))
            (hrho := fun _ => rfl)
            (wmap := MilnorSpinWeyl.spinWeylToDetOneMonomial (F := F))
            (hwmap := fun _ => rfl)
            (hp := MilnorSpinWeyl.spinProjectionCompatible he)
            (weylLift := MilnorSpinWeyl.weylLiftSpinWeyl)
            (hweylSigned :=
              MilnorSpinWeyl.spinWeylToFieldSigned_weylLift (F := F))
            (hweylConj := MilnorSpinWeyl.spinWeyl_conj_weylLift_fieldData he)
            x p q hpq }

noncomputable def milnorWProjection :
    MilnorW F →* fieldDetOneMonomialSubgroup (F := F) :=
  (milnorWMonomialProjection (F := F)).projection

theorem milnorWProjection_diagonalIncl
    (h : MilnorDiagonalExtension F 4) :
    milnorWProjection (F := F) (milnorWDiagonalIncl (F := F) h) =
      milnorDiagonalToFieldMonomial h :=
  (milnorWMonomialProjection (F := F)).projection_diagonalIncl h

theorem milnorWProjection_weylGenerator
    (i j : Fin 4) (hij : i ≠ j) :
    (milnorWProjection (F := F)
      (milnorWWeylGenerator (F := F) i j hij)).1 =
        steinbergToGL (steinbergWeyl hij (1 : Fˣ)) :=
  (milnorWMonomialProjection (F := F)).projection_weylGenerator i j hij

theorem milnorWProjection_surjective :
    Function.Surjective (milnorWProjection (F := F)) :=
  (milnorWMonomialProjection (F := F)).surjective

theorem milnorWProjection_ker :
    (milnorWProjection (F := F)).ker =
      MonoidHom.range (milnorWCentralIncl (F := F)) :=
  (milnorWMonomialProjection (F := F)).ker_eq_central

/-- **Milnor Lemma 12.5, first conjugation identity, premise-free in rank four.**
If `phi(x) = P_sigma diag(c)`, conjugation by `x` sends `h_pq(v)` to the
`{c_p c_q⁻¹, v}` central correction times `h_(sigma p)(sigma q)(v)`. -/
theorem milnorW_conjugation_matsumotoDiagonalLift
    (x : MilnorW F)
    {p q : Fin 4} (hpq : p ≠ q) (v : Fˣ) :
    x * milnorWDiagonalIncl (F := F) (fin4MatsumotoDiagonalLift hpq v) * x⁻¹ =
      milnorWCentralIncl (F := F)
        (Multiplicative.ofAdd
          (milnorSym2 F
            ((fieldMonomialData (milnorWProjection (F := F) x)).2 p *
              ((fieldMonomialData (milnorWProjection (F := F) x)).2 q)⁻¹) v)) *
      milnorWDiagonalIncl (F := F) (fin4MatsumotoDiagonalLift
        ((fieldMonomialData
          (milnorWProjection (F := F) x)).1.injective.ne_iff.mpr hpq) v) :=
  (milnorWMonomialProjection (F := F)).conjugation_matsumotoDiagonalLift
    x hpq v

/-- **Milnor Lemma 12.5, second conjugation identity, premise-free in rank four.**
If `phi(x) = P_sigma diag(c)`, conjugation by `x` sends `w_pq(1)` to
`h_(sigma p)(sigma q)(c_p c_q⁻¹) w_(sigma p)(sigma q)(1)`. -/
theorem milnorW_conjugation_weylGenerator
    (x : MilnorW F) (p q : Fin 4) (hpq : p ≠ q) :
    let σ := (fieldMonomialData (milnorWProjection (F := F) x)).1
    let c := (fieldMonomialData (milnorWProjection (F := F) x)).2
    x * milnorWWeylGenerator (F := F) p q hpq * x⁻¹ =
      milnorWDiagonalIncl (F := F)
        (fin4MatsumotoDiagonalLift
          (σ.injective.ne hpq) (c p * (c q)⁻¹)) *
      milnorWWeylGenerator (F := F) (σ p) (σ q) (σ.injective.ne hpq) :=
  (milnorWMonomialProjection (F := F)).conjugation_weylGenerator x p q hpq

end MilnorDiagonalExtension
end GaloisForLFunctions.HTGeometry

end
