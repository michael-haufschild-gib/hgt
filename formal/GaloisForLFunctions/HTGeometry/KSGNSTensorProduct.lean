import GaloisForLFunctions.HTGeometry.PositiveKernelRightModule

open scoped CStarAlgebra InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open UniformSpace

variable {A B C ι : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [Fintype ι]

/-- Composition of completely positive maps, with positivity proved at every matrix level. -/
def cpMapComp (psi : B →CP C) (phi : A →CP B) : A →CP C where
  toLinearMap := psi.toLinearMap.comp phi.toLinearMap
  map_cstarMatrix_nonneg' := by
    intro n M hM
    have hphi : 0 ≤ M.map phi :=
      CompletelyPositiveMap.map_cstarMatrix_nonneg phi M hM
    have hpsi : 0 ≤ (M.map phi).map psi :=
      CompletelyPositiveMap.map_cstarMatrix_nonneg psi (M.map phi) hphi
    rw [show M.map (psi.toLinearMap.comp phi.toLinearMap) =
        (M.map phi).map psi by
      ext i j
      rfl]
    exact hpsi

@[simp]
theorem cpMapComp_apply (psi : B →CP C) (phi : A →CP B) (a : A) :
    cpMapComp psi phi a = psi (phi a) := rfl

/-- Finite quadratic form of the two-level KSGNS tensor kernel. -/
def ksgnsTensorGramQuadratic (phi : A →CP B) (psi : B →CP C)
    (a : ι → A) (b : ι → B) (c : ι → C) : C :=
  ∑ i, ∑ j,
    star (c i) * psi (star (b i) * phi (star (a i) * a j) * b j) * c j

/-- Complete positivity at both levels makes the internal-tensor Gram form positive. -/
theorem ksgnsTensorGramQuadratic_nonneg (phi : A →CP B) (psi : B →CP C)
    (a : ι → A) (b : ι → B) (c : ι → C) :
    0 ≤ ksgnsTensorGramQuadratic phi psi a b c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      letI := h
      simp [ksgnsTensorGramQuadratic]
  | inr h =>
      letI := h
      let k : ι := Classical.choice h
      let G : CStarMatrix ι ι B := (cpGramMatrix a).map phi
      have hG : 0 ≤ G := CompletelyPositiveMap.map_cstarMatrix_nonneg phi
        (cpGramMatrix a) (cpGramMatrix_nonneg a)
      let V : CStarMatrix ι ι B := fun i j => if i = j then b i else 0
      let H : CStarMatrix ι ι B := fun i j =>
        star (b i) * phi (star (a i) * a j) * b j
      have hVGV : star V * G * V = H := by
        ext i j
        rw [CStarMatrix.mul_apply, Finset.sum_eq_single j]
        · rw [CStarMatrix.mul_apply, Finset.sum_eq_single i]
          · simp [CStarMatrix.star_apply, V, G, H, cpGramMatrix, mul_assoc]
          · intro q _ hqi
            simp [CStarMatrix.star_apply, V, hqi]
          · simp
        · intro q _ hqj
          simp [V, hqj]
        · simp
      have hH : 0 ≤ H := by
        rw [← hVGV]
        exact star_conjugate_nonneg_of_nonneg hG V
      let N : CStarMatrix ι ι C := H.map psi
      have hN : 0 ≤ N := CompletelyPositiveMap.map_cstarMatrix_nonneg psi H hH
      let W : CStarMatrix ι ι C := fun i j => if j = k then c i else 0
      have hq : ksgnsTensorGramQuadratic phi psi a b c = (star W * N * W) k k := by
        rw [CStarMatrix.mul_apply]
        simp only [W, if_pos]
        simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, N,
          CStarMatrix.map_apply, H]
        simp only [if_true, Finset.sum_mul]
        rw [ksgnsTensorGramQuadratic]
        exact Finset.sum_comm
      have hconj : 0 ≤ star W * N * W :=
        star_conjugate_nonneg_of_nonneg hN W
      rw [hq]
      exact cstarMatrix_diagonal_nonneg_of_nonneg _ hconj k

/-- Positive kernel of the cyclic internal tensor product `E_phi tensor_B E_psi`. -/
def ksgnsTensorKernel (phi : A →CP B) (psi : B →CP C) :
    PositiveKernelData (A × B) C where
  kernel p q := psi (star p.2 * phi (star p.1 * q.1) * q.2)
  kernel_star := by
    intro p q
    rw [← map_star psi, star_mul, star_mul, star_star, ← map_star phi]
    simp [mul_assoc]
  quadratic_nonneg := by
    intro x
    let a : x.support → A := fun i => (i : A × B).1
    let b : x.support → B := fun i => (i : A × B).2
    let c : x.support → C := fun i => x i
    have hnonneg := ksgnsTensorGramQuadratic_nonneg phi psi a b c
    change 0 ≤ ∑ p ∈ x.support, ∑ q ∈ x.support,
      star (x p) * psi (star p.2 * phi (star p.1 * q.1) * q.2) * x q
    change 0 ≤ ksgnsTensorGramQuadratic phi psi a b c at hnonneg
    rw [ksgnsTensorGramQuadratic] at hnonneg
    have heq :
        (∑ p ∈ x.support, ∑ q ∈ x.support,
          star (x p) * psi (star p.2 * phi (star p.1 * q.1) * q.2) * x q) =
        ∑ i : x.support, ∑ j : x.support,
          star (c i) * psi (star (b i) * phi (star (a i) * a j) * b j) * c j := by
      rw [Finset.sum_subtype x.support (fun _ => Iff.rfl)]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_subtype x.support (fun _ => Iff.rfl)]
    rw [heq]
    exact hnonneg

/-- Completed cyclic internal tensor product of the two canonical KSGNS correspondences. -/
abbrev KSGNSInternalTensorProduct (phi : A →CP B) (psi : B →CP C) :=
  PositiveKernelCompletion (ksgnsTensorKernel phi psi)

/-- Canonical dense tensor generator
`π_phi(a)ξ_phi tensor π_psi(b)ξ_psi c`. -/
def ksgnsTensorGenerator (phi : A →CP B) (psi : B →CP C)
    (a : A) (b : B) (c : C) : KSGNSInternalTensorProduct phi psi :=
  ((Submodule.Quotient.mk (Finsupp.single (a, b) c) :
      PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
    KSGNSInternalTensorProduct phi psi)

/-- Exact internal-tensor inner product on cyclic generators. -/
theorem ksgnsTensorGenerator_inner (phi : A →CP B) (psi : B →CP C)
    (a a' : A) (b b' : B) (c c' : C) :
    (positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)).inner
        (ksgnsTensorGenerator phi psi a b c)
        (ksgnsTensorGenerator phi psi a' b' c') =
      star c * psi (star b * phi (star a * a') * b') * c' := by
  change MulOpposite.unop
      (positiveKernelCompletedInnerSLM (ksgnsTensorKernel phi psi)
        ((Submodule.Quotient.mk (Finsupp.single (a, b) c) :
          PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
            KSGNSInternalTensorProduct phi psi)
        ((Submodule.Quotient.mk (Finsupp.single (a', b') c') :
          PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
            KSGNSInternalTensorProduct phi psi)) = _
  rw [positiveKernelCompletedInnerSLM_coe_coe]
  change MulOpposite.unop (MulOpposite.op
    (positiveKernelSeparatedInner (ksgnsTensorKernel phi psi)
      (Submodule.Quotient.mk (Finsupp.single (a, b) c))
      (Submodule.Quotient.mk (Finsupp.single (a', b') c')))) = _
  rw [
    positiveKernelSeparatedInner_mk,
    positiveKernelPreInner_single_single]
  rfl

/-- Algebraic embedding of composite cyclic labels into tensor labels `(a,1_B)`. -/
def ksgnsTensorCompositeFreeMap : (A →₀ C) →ₗ[ℂ] ((A × B) →₀ C) :=
  (Finsupp.lsum ℂ) fun a => Finsupp.lsingle (a, 1)

@[simp]
theorem ksgnsTensorCompositeFreeMap_single (a : A) (c : C) :
    ksgnsTensorCompositeFreeMap (B := B) (Finsupp.single a c) =
      Finsupp.single (a, 1) c := by
  classical
  simp [ksgnsTensorCompositeFreeMap]

/-- The free composite embedding preserves the complete two-level Gram form. -/
theorem positiveKernelPreInner_tensorCompositeFreeMap
    (phi : A →CP B) (psi : B →CP C) (x y : A →₀ C) :
    positiveKernelPreInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorCompositeFreeMap (B := B) x)
        (ksgnsTensorCompositeFreeMap (B := B) y) =
      ksgnsPreInner (cpMapComp psi phi) x y := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      simp [positiveKernelPreInner, ksgnsPreInner]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [map_add, positiveKernelPreInner_add_left, hx₁, hx₂,
        ksgnsPreInner_add_left]
  | single a c =>
      induction y using Finsupp.induction_linear with
      | zero =>
          simp [positiveKernelPreInner, ksgnsPreInner]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [map_add, positiveKernelPreInner_add_right, hy₁, hy₂,
            ksgnsPreInner_add_right]
      | single a' c' =>
          rw [ksgnsTensorCompositeFreeMap_single,
            ksgnsTensorCompositeFreeMap_single,
            positiveKernelPreInner_single_single,
            ksgnsPreInner_single_single]
          simp [ksgnsTensorKernel]

/-- Algebraic composite map into the separated tensor-kernel module. -/
def ksgnsTensorCompositeFreeToSeparated (phi : A →CP B) (psi : B →CP C) :
    (A →₀ C) →ₗ[ℂ] PositiveKernelSeparated (ksgnsTensorKernel phi psi) :=
  (positiveKernelPreRadical (ksgnsTensorKernel phi psi)).mkQ.comp
    (ksgnsTensorCompositeFreeMap (B := B))

@[simp]
theorem ksgnsTensorCompositeFreeToSeparated_apply
    (phi : A →CP B) (psi : B →CP C) (x : A →₀ C) :
    ksgnsTensorCompositeFreeToSeparated phi psi x =
      Submodule.Quotient.mk (ksgnsTensorCompositeFreeMap (B := B) x) := rfl

theorem ksgnsTensorCompositeFreeToSeparated_eq_zero_of_mem_radical
    (phi : A →CP B) (psi : B →CP C) {x : A →₀ C}
    (hx : x ∈ ksgnsPreRadical (cpMapComp psi phi)) :
    ksgnsTensorCompositeFreeToSeparated phi psi x = 0 := by
  apply norm_eq_zero.mp
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)]
  change Real.sqrt ‖MulOpposite.op
    (positiveKernelSeparatedInner (ksgnsTensorKernel phi psi)
      (Submodule.Quotient.mk (ksgnsTensorCompositeFreeMap (B := B) x))
      (Submodule.Quotient.mk (ksgnsTensorCompositeFreeMap (B := B) x)))‖ = 0
  rw [positiveKernelSeparatedInner_mk,
    positiveKernelPreInner_tensorCompositeFreeMap, hx x]
  simp

/-- Algebraic isometry from the separated KSGNS module of `psi ∘ phi` to the separated internal
tensor product. -/
def ksgnsTensorCompositeSeparatedMap (phi : A →CP B) (psi : B →CP C) :
    KSGNSSeparated (cpMapComp psi phi) →ₗ[ℂ]
      PositiveKernelSeparated (ksgnsTensorKernel phi psi) :=
  (ksgnsPreRadical (cpMapComp psi phi)).liftQ
    (ksgnsTensorCompositeFreeToSeparated phi psi) (by
      intro x hx
      exact ksgnsTensorCompositeFreeToSeparated_eq_zero_of_mem_radical phi psi hx)

@[simp]
theorem ksgnsTensorCompositeSeparatedMap_mk
    (phi : A →CP B) (psi : B →CP C) (x : A →₀ C) :
    ksgnsTensorCompositeSeparatedMap phi psi (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ksgnsTensorCompositeFreeMap (B := B) x) := by
  rw [ksgnsTensorCompositeSeparatedMap, Submodule.liftQ_apply]
  rfl

theorem positiveKernelSeparatedInner_tensorCompositeSeparatedMap
    (phi : A →CP B) (psi : B →CP C)
    (x y : KSGNSSeparated (cpMapComp psi phi)) :
    positiveKernelSeparatedInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorCompositeSeparatedMap phi psi x)
        (ksgnsTensorCompositeSeparatedMap phi psi y) =
      ksgnsSeparatedInner (cpMapComp psi phi) x y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y =>
      change positiveKernelSeparatedInner (ksgnsTensorKernel phi psi)
          (ksgnsTensorCompositeSeparatedMap phi psi (Submodule.Quotient.mk x))
          (ksgnsTensorCompositeSeparatedMap phi psi (Submodule.Quotient.mk y)) =
        ksgnsSeparatedInner (cpMapComp psi phi)
          (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)
      rw [ksgnsTensorCompositeSeparatedMap_mk,
        ksgnsTensorCompositeSeparatedMap_mk,
        positiveKernelSeparatedInner_mk,
        positiveKernelPreInner_tensorCompositeFreeMap]
      rfl

theorem norm_ksgnsTensorCompositeSeparatedMap
    (phi : A →CP B) (psi : B →CP C)
    (x : KSGNSSeparated (cpMapComp psi phi)) :
    ‖ksgnsTensorCompositeSeparatedMap phi psi x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)]
  change Real.sqrt ‖MulOpposite.op
    (positiveKernelSeparatedInner (ksgnsTensorKernel phi psi)
      (ksgnsTensorCompositeSeparatedMap phi psi x)
      (ksgnsTensorCompositeSeparatedMap phi psi x))‖ = ‖x‖
  rw [positiveKernelSeparatedInner_tensorCompositeSeparatedMap]
  symm
  have h := CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) x
  change ‖x‖ = Real.sqrt ‖MulOpposite.op
    (ksgnsSeparatedInner (cpMapComp psi phi) x x)‖ at h
  exact h

/-- Isometric map on separated algebraic modules. -/
def ksgnsTensorCompositeSeparatedIsometry
    (phi : A →CP B) (psi : B →CP C) :
    KSGNSSeparated (cpMapComp psi phi) →ₗᵢ[ℂ]
      PositiveKernelSeparated (ksgnsTensorKernel phi psi) where
  toLinearMap := ksgnsTensorCompositeSeparatedMap phi psi
  norm_map' := norm_ksgnsTensorCompositeSeparatedMap phi psi

/-- Separated composite map followed by the tensor-product completion embedding. -/
def ksgnsTensorCompositeSeparatedCompletionIsometry
    (phi : A →CP B) (psi : B →CP C) :
    KSGNSSeparated (cpMapComp psi phi) →ₗᵢ[ℂ]
      KSGNSInternalTensorProduct phi psi where
  toLinearMap :=
    (completionCoeLinearIsometry
      (E := PositiveKernelSeparated (ksgnsTensorKernel phi psi))).toLinearMap.comp
      (ksgnsTensorCompositeSeparatedIsometry phi psi).toLinearMap
  norm_map' := by
    intro x
    change ‖(((ksgnsTensorCompositeSeparatedIsometry phi psi) x :
        PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
          KSGNSInternalTensorProduct phi psi)‖ = ‖x‖
    rw [UniformSpace.Completion.norm_coe,
      (ksgnsTensorCompositeSeparatedIsometry phi psi).norm_map]

/-- Equation (5): canonical isometry from the composite KSGNS correspondence into the completed
internal tensor product. -/
def ksgnsCompositeTensorIsometry (phi : A →CP B) (psi : B →CP C) :
    KSGNS (cpMapComp psi phi) →ₗᵢ[ℂ] KSGNSInternalTensorProduct phi psi where
  toLinearMap :=
    (completionExtendSL
      (ksgnsTensorCompositeSeparatedCompletionIsometry phi psi).toContinuousLinearMap).toLinearMap
  norm_map' := by
    intro x
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · exact isClosed_eq
        (continuous_norm.comp
          (completionExtendSL
            (ksgnsTensorCompositeSeparatedCompletionIsometry phi psi).toContinuousLinearMap).continuous)
        continuous_norm
    · intro x
      change ‖completionExtendSL
          (ksgnsTensorCompositeSeparatedCompletionIsometry phi psi).toContinuousLinearMap
          (x : KSGNS (cpMapComp psi phi))‖ = ‖(x : KSGNS (cpMapComp psi phi))‖
      rw [completionExtendSL_coe]
      change ‖ksgnsTensorCompositeSeparatedCompletionIsometry phi psi x‖ =
        ‖(x : KSGNS (cpMapComp psi phi))‖
      rw [(ksgnsTensorCompositeSeparatedCompletionIsometry phi psi).norm_map,
        UniformSpace.Completion.norm_coe]

@[simp]
theorem ksgnsCompositeTensorIsometry_coe
    (phi : A →CP B) (psi : B →CP C)
    (x : KSGNSSeparated (cpMapComp psi phi)) :
    ksgnsCompositeTensorIsometry phi psi (x : KSGNS (cpMapComp psi phi)) =
      ((ksgnsTensorCompositeSeparatedMap phi psi x :
          PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
        KSGNSInternalTensorProduct phi psi) := by
  change completionExtendSL
      (ksgnsTensorCompositeSeparatedCompletionIsometry phi psi).toContinuousLinearMap
      (x : KSGNS (cpMapComp psi phi)) = _
  rw [completionExtendSL_coe]
  rfl

/-- Equation (5) on every cyclic generator. -/
theorem ksgnsCompositeTensorIsometry_cyclicGenerator
    (phi : A →CP B) (psi : B →CP C) (a : A) (c : C) :
    ksgnsCompositeTensorIsometry phi psi
        (MulOpposite.op c •
          ksgnsRepresentation (cpMapComp psi phi) a
            (ksgnsCyclic (cpMapComp psi phi))) =
      ksgnsTensorGenerator phi psi a 1 c := by
  rw [ksgnsRepresentation_cyclic]
  change ksgnsCompositeTensorIsometry phi psi
      (ksgnsCompletedActionCLM (cpMapComp psi phi) (MulOpposite.op c)
        ((Submodule.Quotient.mk (Finsupp.single a 1) :
          KSGNSSeparated (cpMapComp psi phi)) : KSGNS (cpMapComp psi phi))) = _
  rw [ksgnsCompletedActionCLM_coe]
  change ksgnsCompositeTensorIsometry phi psi
      ((MulOpposite.op c •
        (Submodule.Quotient.mk (Finsupp.single a 1) :
          KSGNSSeparated (cpMapComp psi phi)) :
            KSGNSSeparated (cpMapComp psi phi)) :
              KSGNS (cpMapComp psi phi)) = _
  rw [ksgnsSeparated_op_smul_mk, ksgnsCompositeTensorIsometry_coe,
    ksgnsTensorCompositeSeparatedMap_mk,
    ksgnsPreRmul_single,
    ksgnsTensorCompositeFreeMap_single]
  simp [ksgnsTensorGenerator]

/-! ## Centered orthogonal succession inside the completed tensor product -/

/-- Unital centered KSGNS vector. -/
def ksgnsUnitalCentered (phi : A →CP B) (a : A) : KSGNS phi :=
  ksgnsRepresentation phi a (ksgnsCyclic phi) -
    MulOpposite.op (phi a) • ksgnsCyclic phi

/-- Earlier centered tensor summand `D_phi(a) tensor ξ_psi`. -/
def ksgnsTensorEarlierCentered (phi : A →CP B) (psi : B →CP C) (a : A) :
    KSGNSInternalTensorProduct phi psi :=
  ksgnsTensorGenerator phi psi a 1 1 -
    ksgnsTensorGenerator phi psi 1 (phi a) 1

/-- Later centered tensor summand `ξ_phi tensor D_psi(phi(a))`. -/
def ksgnsTensorLaterCentered (phi : A →CP B) (psi : B →CP C) (a : A) :
    KSGNSInternalTensorProduct phi psi :=
  ksgnsTensorGenerator phi psi 1 (phi a) 1 -
    ksgnsTensorGenerator phi psi 1 1 (psi (phi a))

theorem cpMapComp_one (phi : A →CP B) (psi : B →CP C)
    (hphi : phi 1 = 1) (hpsi : psi 1 = 1) :
    cpMapComp psi phi 1 = 1 := by
  rw [cpMapComp_apply, hphi, hpsi]

/-- Equation (6): the centered composite vector splits into earlier and later tensor directions. -/
theorem ksgnsCompositeTensorIsometry_centered
    (phi : A →CP B) (psi : B →CP C) (a : A) :
    ksgnsCompositeTensorIsometry phi psi
        (ksgnsUnitalCentered (cpMapComp psi phi) a) =
      ksgnsTensorEarlierCentered phi psi a +
        ksgnsTensorLaterCentered phi psi a := by
  have hfirst :
      ksgnsCompositeTensorIsometry phi psi
          (ksgnsRepresentation (cpMapComp psi phi) a
            (ksgnsCyclic (cpMapComp psi phi))) =
        ksgnsTensorGenerator phi psi a 1 1 := by
    simpa using ksgnsCompositeTensorIsometry_cyclicGenerator phi psi a (1 : C)
  have hsecond :
      ksgnsCompositeTensorIsometry phi psi
          (MulOpposite.op (psi (phi a)) •
            ksgnsCyclic (cpMapComp psi phi)) =
        ksgnsTensorGenerator phi psi 1 1 (psi (phi a)) := by
    have hone :
        ksgnsRepresentation (cpMapComp psi phi) 1
            (ksgnsCyclic (cpMapComp psi phi)) =
          ksgnsCyclic (cpMapComp psi phi) := by
      rw [ksgnsRepresentation_one]
      rfl
    rw [← hone]
    exact ksgnsCompositeTensorIsometry_cyclicGenerator
      phi psi (1 : A) (psi (phi a))
  change ksgnsCompositeTensorIsometry phi psi
      (ksgnsRepresentation (cpMapComp psi phi) a
        (ksgnsCyclic (cpMapComp psi phi)) -
        MulOpposite.op (psi (phi a)) • ksgnsCyclic (cpMapComp psi phi)) = _
  rw [map_sub, hfirst, hsecond]
  unfold ksgnsTensorEarlierCentered ksgnsTensorLaterCentered
  abel

/-- The earlier and later centered tensor summands are orthogonal. -/
theorem ksgnsTensorEarlierCentered_inner_laterCentered
    (phi : A →CP B) (psi : B →CP C)
    (hphi : phi 1 = 1) (a d : A) :
    (positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)).inner
        (ksgnsTensorEarlierCentered phi psi a)
        (ksgnsTensorLaterCentered phi psi d) = 0 := by
  let M := positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)
  change M.inner
      (ksgnsTensorGenerator phi psi a 1 1 -
        ksgnsTensorGenerator phi psi 1 (phi a) 1)
      (ksgnsTensorGenerator phi psi 1 (phi d) 1 -
        ksgnsTensorGenerator phi psi 1 1 (psi (phi d))) = 0
  rw [M.inner_sub_left, M.inner_sub_right, M.inner_sub_right]
  dsimp [M]
  simp only [ksgnsTensorGenerator_inner, star_one, one_mul, mul_one,
    map_star, hphi]
  noncomm_ring

theorem ksgnsTensorLaterCentered_inner_earlierCentered
    (phi : A →CP B) (psi : B →CP C)
    (hphi : phi 1 = 1) (a d : A) :
    (positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)).inner
        (ksgnsTensorLaterCentered phi psi a)
        (ksgnsTensorEarlierCentered phi psi d) = 0 := by
  rw [← star_eq_zero,
    (positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)).star_inner,
    ksgnsTensorEarlierCentered_inner_laterCentered phi psi hphi]

/-- Gram kernel of the earlier summand is `psi(Γ_phi)`. -/
theorem ksgnsTensorEarlierCentered_inner
    (phi : A →CP B) (psi : B →CP C)
    (hphi : phi 1 = 1) (a d : A) :
    (positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)).inner
        (ksgnsTensorEarlierCentered phi psi a)
        (ksgnsTensorEarlierCentered phi psi d) =
      psi (phi (star a * d) - star (phi a) * phi d) := by
  let M := positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)
  change M.inner
      (ksgnsTensorGenerator phi psi a 1 1 -
        ksgnsTensorGenerator phi psi 1 (phi a) 1)
      (ksgnsTensorGenerator phi psi d 1 1 -
        ksgnsTensorGenerator phi psi 1 (phi d) 1) = _
  rw [M.inner_sub_left, M.inner_sub_right, M.inner_sub_right]
  dsimp [M]
  simp only [ksgnsTensorGenerator_inner, star_one, one_mul, mul_one,
    map_star, hphi, map_sub]
  noncomm_ring

/-- Gram kernel of the later summand is `Γ_psi(phi(a),phi(d))`. -/
theorem ksgnsTensorLaterCentered_inner
    (phi : A →CP B) (psi : B →CP C)
    (hphi : phi 1 = 1) (hpsi : psi 1 = 1) (a d : A) :
    (positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)).inner
        (ksgnsTensorLaterCentered phi psi a)
        (ksgnsTensorLaterCentered phi psi d) =
      psi (star (phi a) * phi d) - star (psi (phi a)) * psi (phi d) := by
  let M := positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)
  change M.inner
      (ksgnsTensorGenerator phi psi 1 (phi a) 1 -
        ksgnsTensorGenerator phi psi 1 1 (psi (phi a)))
      (ksgnsTensorGenerator phi psi 1 (phi d) 1 -
        ksgnsTensorGenerator phi psi 1 1 (psi (phi d))) = _
  rw [M.inner_sub_left, M.inner_sub_right, M.inner_sub_right]
  dsimp [M]
  simp only [ksgnsTensorGenerator_inner, star_one, one_mul, mul_one,
    map_star, hphi, hpsi]
  noncomm_ring

/-- Equation (7), now certified as the Gram identity of the orthogonal decomposition. -/
theorem ksgnsOrthogonalSuccessionPythagoras
    (phi : A →CP B) (psi : B →CP C)
    (hphi : phi 1 = 1) (hpsi : psi 1 = 1) (a d : A) :
    (positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)).inner
        (ksgnsTensorEarlierCentered phi psi a +
          ksgnsTensorLaterCentered phi psi a)
        (ksgnsTensorEarlierCentered phi psi d +
          ksgnsTensorLaterCentered phi psi d) =
      psi (phi (star a * d) - star (phi a) * phi d) +
        (psi (star (phi a) * phi d) -
          star (psi (phi a)) * psi (phi d)) := by
  let M := positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)
  rw [M.inner_add_left, M.inner_add_right, M.inner_add_right,
    ksgnsTensorEarlierCentered_inner_laterCentered phi psi hphi,
    ksgnsTensorLaterCentered_inner_earlierCentered phi psi hphi,
    ksgnsTensorEarlierCentered_inner phi psi hphi,
    ksgnsTensorLaterCentered_inner phi psi hphi hpsi]
  simp only [add_zero, zero_add]

/-- Algebraic form of Equation (7). -/
theorem starMultiplicativeDefect_comp_eq_orthogonal_tensorGrams
    (phi : A →CP B) (psi : B →CP C) (a d : A) :
    starMultiplicativeDefect (cpMapComp psi phi) a d =
      psi (starMultiplicativeDefect phi a d) +
        starMultiplicativeDefect psi (phi a) (phi d) := by
  change psi (phi (star a * d)) - star (psi (phi a)) * psi (phi d) = _
  simp only [starMultiplicativeDefect, map_sub, map_star]
  noncomm_ring

/-! ## Genuine correspondence structure on the internal tensor product -/

/-- Left multiplication on the first algebra label of the algebraic tensor core. -/
def ksgnsTensorPreLmul (a : A) (x : (A × B) →₀ C) : (A × B) →₀ C :=
  x.sum fun p c => Finsupp.single (a * p.1, p.2) c

@[simp]
theorem ksgnsTensorPreLmul_single (a d : A) (b : B) (c : C) :
    ksgnsTensorPreLmul a (Finsupp.single (d, b) c) =
      Finsupp.single (a * d, b) c := by
  classical
  simp [ksgnsTensorPreLmul]

theorem ksgnsTensorPreLmul_add (a : A) (x y : (A × B) →₀ C) :
    ksgnsTensorPreLmul a (x + y) =
      ksgnsTensorPreLmul a x + ksgnsTensorPreLmul a y := by
  classical
  unfold ksgnsTensorPreLmul
  rw [Finsupp.sum_add_index]
  · intro p
    simp
  · intro p _ c d
    simpa using (Finsupp.single_add (a * p.1, p.2) c d)

theorem ksgnsTensorPreLmul_smul (a : A) (q : ℂ) (x : (A × B) →₀ C) :
    ksgnsTensorPreLmul a (q • x) = q • ksgnsTensorPreLmul a x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsTensorPreLmul]
  | add x y hx hy =>
      rw [smul_add, ksgnsTensorPreLmul_add, ksgnsTensorPreLmul_add,
        hx, hy, smul_add]
  | single p c => simp [ksgnsTensorPreLmul]

def ksgnsTensorPreLmulLinear (a : A) :
    ((A × B) →₀ C) →ₗ[ℂ] ((A × B) →₀ C) where
  toFun := ksgnsTensorPreLmul a
  map_add' := ksgnsTensorPreLmul_add a
  map_smul' := ksgnsTensorPreLmul_smul a

theorem ksgnsTensorPreLmul_one (x : (A × B) →₀ C) :
    ksgnsTensorPreLmul 1 x = x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsTensorPreLmul]
  | add x y hx hy => rw [ksgnsTensorPreLmul_add, hx, hy]
  | single p c =>
      rcases p with ⟨p, b⟩
      simp

theorem ksgnsTensorPreLmul_mul (a d : A) (x : (A × B) →₀ C) :
    ksgnsTensorPreLmul (a * d) x =
      ksgnsTensorPreLmul a (ksgnsTensorPreLmul d x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsTensorPreLmul]
  | add x y hx hy =>
      rw [ksgnsTensorPreLmul_add, ksgnsTensorPreLmul_add,
        ksgnsTensorPreLmul_add, hx, hy]
  | single p c =>
      rcases p with ⟨p, b⟩
      simp [mul_assoc]

theorem ksgnsTensorPreInner_lmul_adjoint
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x y : (A × B) →₀ C) :
    positiveKernelPreInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorPreLmul a x) y =
      positiveKernelPreInner (ksgnsTensorKernel phi psi)
        x (ksgnsTensorPreLmul (star a) y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsTensorPreLmul, positiveKernelPreInner]
  | add x z hx hz =>
      rw [ksgnsTensorPreLmul_add, positiveKernelPreInner_add_left,
        hx, hz, positiveKernelPreInner_add_left]
  | single p c =>
      induction y using Finsupp.induction_linear with
      | zero => simp [ksgnsTensorPreLmul, positiveKernelPreInner]
      | add y z hy hz =>
          rw [ksgnsTensorPreLmul_add, positiveKernelPreInner_add_right,
            positiveKernelPreInner_add_right, hy, hz]
      | single q d =>
          rcases p with ⟨p, b⟩
          rcases q with ⟨q, e⟩
          simp [ksgnsTensorKernel, star_mul, mul_assoc]

theorem ksgnsTensorPreInner_lmul_both
    (phi : A →CP B) (psi : B →CP C) (a d : A)
    (x y : (A × B) →₀ C) :
    positiveKernelPreInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorPreLmul a x) (ksgnsTensorPreLmul d y) =
      positiveKernelPreInner (ksgnsTensorKernel phi psi)
        x (ksgnsTensorPreLmul (star a * d) y) := by
  rw [ksgnsTensorPreInner_lmul_adjoint, ← ksgnsTensorPreLmul_mul]

theorem ksgnsTensorPreInner_lmul_add_label
    (phi : A →CP B) (psi : B →CP C) (a d : A)
    (x y : (A × B) →₀ C) :
    positiveKernelPreInner (ksgnsTensorKernel phi psi)
        x (ksgnsTensorPreLmul (a + d) y) =
      positiveKernelPreInner (ksgnsTensorKernel phi psi)
          x (ksgnsTensorPreLmul a y) +
        positiveKernelPreInner (ksgnsTensorKernel phi psi)
          x (ksgnsTensorPreLmul d y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [positiveKernelPreInner]
  | add x z hx hz =>
      simp only [positiveKernelPreInner_add_left, hx, hz]
      abel
  | single p c =>
      induction y using Finsupp.induction_linear with
      | zero => simp [ksgnsTensorPreLmul, positiveKernelPreInner]
      | add y z hy hz =>
          rw [ksgnsTensorPreLmul_add, ksgnsTensorPreLmul_add,
            ksgnsTensorPreLmul_add, positiveKernelPreInner_add_right,
            positiveKernelPreInner_add_right, positiveKernelPreInner_add_right,
            hy, hz]
          abel
      | single q e =>
          rcases p with ⟨p, b⟩
          rcases q with ⟨q, f⟩
          simp [ksgnsTensorKernel, add_mul, mul_add, mul_assoc]

theorem ksgnsTensorPreInner_lmul_smul_label
    (phi : A →CP B) (psi : B →CP C) (r : ℂ) (a : A)
    (x y : (A × B) →₀ C) :
    positiveKernelPreInner (ksgnsTensorKernel phi psi)
        x (ksgnsTensorPreLmul (r • a) y) =
      r • positiveKernelPreInner (ksgnsTensorKernel phi psi)
        x (ksgnsTensorPreLmul a y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [positiveKernelPreInner]
  | add x z hx hz =>
      simp only [positiveKernelPreInner_add_left, hx, hz, smul_add]
  | single p c =>
      induction y using Finsupp.induction_linear with
      | zero => simp [ksgnsTensorPreLmul, positiveKernelPreInner]
      | add y z hy hz =>
          rw [ksgnsTensorPreLmul_add, ksgnsTensorPreLmul_add,
            positiveKernelPreInner_add_right, positiveKernelPreInner_add_right,
            hy, hz, smul_add]
      | single q e =>
          rcases p with ⟨p, b⟩
          rcases q with ⟨q, f⟩
          simp [ksgnsTensorKernel, smul_mul_assoc, mul_smul_comm, mul_assoc]

theorem ksgnsTensorPreInner_lmul_add_label_left
    (phi : A →CP B) (psi : B →CP C) (a d : A)
    (x y : (A × B) →₀ C) :
    positiveKernelPreInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorPreLmul (a + d) x) y =
      positiveKernelPreInner (ksgnsTensorKernel phi psi)
          (ksgnsTensorPreLmul a x) y +
        positiveKernelPreInner (ksgnsTensorKernel phi psi)
          (ksgnsTensorPreLmul d x) y := by
  rw [ksgnsTensorPreInner_lmul_adjoint, star_add,
    ksgnsTensorPreInner_lmul_add_label,
    ← ksgnsTensorPreInner_lmul_adjoint,
    ← ksgnsTensorPreInner_lmul_adjoint]

theorem ksgnsTensorPreInner_lmul_smul_label_left
    (phi : A →CP B) (psi : B →CP C) (r : ℂ) (a : A)
    (x y : (A × B) →₀ C) :
    positiveKernelPreInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorPreLmul (r • a) x) y =
      star r • positiveKernelPreInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorPreLmul a x) y := by
  rw [ksgnsTensorPreInner_lmul_adjoint, star_smul,
    ksgnsTensorPreInner_lmul_smul_label,
    ← ksgnsTensorPreInner_lmul_adjoint]

theorem ksgnsTensorPreInner_lmul_sub_label
    (phi : A →CP B) (psi : B →CP C) (a d : A)
    (x y : (A × B) →₀ C) :
    positiveKernelPreInner (ksgnsTensorKernel phi psi)
        x (ksgnsTensorPreLmul (a - d) y) =
      positiveKernelPreInner (ksgnsTensorKernel phi psi)
          x (ksgnsTensorPreLmul a y) -
        positiveKernelPreInner (ksgnsTensorKernel phi psi)
          x (ksgnsTensorPreLmul d y) := by
  rw [sub_eq_add_neg, ksgnsTensorPreInner_lmul_add_label]
  have hneg := ksgnsTensorPreInner_lmul_smul_label
    phi psi (-1 : ℂ) d x y
  simp only [neg_one_smul] at hneg
  rw [hneg, sub_eq_add_neg]

theorem ksgnsTensorPreInner_lmul_norm_gap
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x : (A × B) →₀ C) :
    (‖a‖ ^ 2 : ℝ) • positiveKernelPreInner (ksgnsTensorKernel phi psi) x x -
        positiveKernelPreInner (ksgnsTensorKernel phi psi)
          (ksgnsTensorPreLmul a x) (ksgnsTensorPreLmul a x) =
      positiveKernelPreInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorPreLmul
          (CFC.sqrt ((‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a)) x)
        (ksgnsTensorPreLmul
          (CFC.sqrt ((‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a)) x) := by
  let h : A := (‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a
  have hh : 0 ≤ h := by
    dsimp [h]
    rw [sub_nonneg]
    have ha := (IsSelfAdjoint.star_mul_self a).le_algebraMap_norm_self
    rw [CStarRing.norm_star_mul_self, Algebra.algebraMap_eq_smul_one] at ha
    simpa [pow_two] using ha
  let p : A := CFC.sqrt h
  have hpstar : star p = p := (CFC.sqrt_nonneg h).star_eq
  have hp2 : star p * p = h := by
    rw [hpstar]
    simpa [pow_two] using CFC.sq_sqrt h hh
  have hrlabel : ((‖a‖ ^ 2 : ℝ) • (1 : A)) =
      ((‖a‖ ^ 2 : ℂ) • (1 : A)) := by
    norm_cast
  change (‖a‖ ^ 2 : ℝ) •
      positiveKernelPreInner (ksgnsTensorKernel phi psi) x x -
        positiveKernelPreInner (ksgnsTensorKernel phi psi)
          (ksgnsTensorPreLmul a x) (ksgnsTensorPreLmul a x) =
      positiveKernelPreInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorPreLmul p x) (ksgnsTensorPreLmul p x)
  rw [ksgnsTensorPreInner_lmul_both,
    ksgnsTensorPreInner_lmul_both, hp2]
  change (‖a‖ ^ 2 : ℝ) •
      positiveKernelPreInner (ksgnsTensorKernel phi psi) x x -
        positiveKernelPreInner (ksgnsTensorKernel phi psi)
          x (ksgnsTensorPreLmul (star a * a) x) =
      positiveKernelPreInner (ksgnsTensorKernel phi psi)
        x (ksgnsTensorPreLmul h x)
  rw [show h = (‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a by rfl,
    ksgnsTensorPreInner_lmul_sub_label, hrlabel,
    ksgnsTensorPreInner_lmul_smul_label, ksgnsTensorPreLmul_one]
  norm_cast

theorem ksgnsTensorPreInner_lmul_self_le
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x : (A × B) →₀ C) :
    positiveKernelPreInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorPreLmul a x) (ksgnsTensorPreLmul a x) ≤
      (‖a‖ ^ 2 : ℝ) •
        positiveKernelPreInner (ksgnsTensorKernel phi psi) x x := by
  apply sub_nonneg.mp
  rw [ksgnsTensorPreInner_lmul_norm_gap]
  exact positiveKernelPreInner_self_nonneg (ksgnsTensorKernel phi psi) _

theorem norm_ksgnsTensorPreInner_lmul_self_le
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x : (A × B) →₀ C) :
    ‖positiveKernelPreInner (ksgnsTensorKernel phi psi)
        (ksgnsTensorPreLmul a x) (ksgnsTensorPreLmul a x)‖ ≤
      ‖a‖ ^ 2 * ‖positiveKernelPreInner (ksgnsTensorKernel phi psi) x x‖ := by
  have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (positiveKernelPreInner_self_nonneg (ksgnsTensorKernel phi psi)
      (ksgnsTensorPreLmul a x))
    (ksgnsTensorPreInner_lmul_self_le phi psi a x)
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖a‖)] at hnorm
  exact hnorm

theorem ksgnsTensorPreLmul_mem_radical
    (phi : A →CP B) (psi : B →CP C) (a : A) {x : (A × B) →₀ C}
    (hx : x ∈ positiveKernelPreRadical (ksgnsTensorKernel phi psi)) :
    ksgnsTensorPreLmul a x ∈
      positiveKernelPreRadical (ksgnsTensorKernel phi psi) := by
  intro y
  rw [ksgnsTensorPreInner_lmul_adjoint]
  exact hx _

/-- Left multiplication descended to the separated internal-tensor core. -/
def ksgnsTensorSeparatedLmul (phi : A →CP B) (psi : B →CP C) (a : A) :
    PositiveKernelSeparated (ksgnsTensorKernel phi psi) →ₗ[ℂ]
      PositiveKernelSeparated (ksgnsTensorKernel phi psi) :=
  (positiveKernelPreRadical (ksgnsTensorKernel phi psi)).mapQ
    (positiveKernelPreRadical (ksgnsTensorKernel phi psi))
    (ksgnsTensorPreLmulLinear a) (by
      intro x hx
      exact ksgnsTensorPreLmul_mem_radical phi psi a hx)

@[simp]
theorem ksgnsTensorSeparatedLmul_mk
    (phi : A →CP B) (psi : B →CP C) (a : A) (x : (A × B) →₀ C) :
    ksgnsTensorSeparatedLmul phi psi a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ksgnsTensorPreLmul a x) := by
  exact Submodule.mapQ_apply _ _ _ _

theorem norm_ksgnsTensorSeparatedLmul_le
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x : PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
    ‖ksgnsTensorSeparatedLmul phi psi a x‖ ≤ ‖a‖ * ‖x‖ := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change ‖(Submodule.Quotient.mk (ksgnsTensorPreLmul a x) :
        PositiveKernelSeparated (ksgnsTensorKernel phi psi))‖ ≤
      ‖a‖ * ‖(Submodule.Quotient.mk x :
        PositiveKernelSeparated (ksgnsTensorKernel phi psi))‖
    rw [← sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg a) (norm_nonneg
        (Submodule.Quotient.mk x :
          PositiveKernelSeparated (ksgnsTensorKernel phi psi))))]
    rw [CStarModule.norm_sq_eq (A := Cᵐᵒᵖ)
        (x := (Submodule.Quotient.mk (ksgnsTensorPreLmul a x) :
          PositiveKernelSeparated (ksgnsTensorKernel phi psi))),
      mul_pow,
      CStarModule.norm_sq_eq (A := Cᵐᵒᵖ)
        (x := (Submodule.Quotient.mk x :
          PositiveKernelSeparated (ksgnsTensorKernel phi psi)))]
    change ‖MulOpposite.op
        (positiveKernelPreInner (ksgnsTensorKernel phi psi)
          (ksgnsTensorPreLmul a x) (ksgnsTensorPreLmul a x))‖ ≤
      ‖a‖ ^ 2 * ‖MulOpposite.op
        (positiveKernelPreInner (ksgnsTensorKernel phi psi) x x)‖
    rw [MulOpposite.norm_op, MulOpposite.norm_op]
    exact norm_ksgnsTensorPreInner_lmul_self_le phi psi a x

noncomputable def ksgnsTensorSeparatedLmulCLM
    (phi : A →CP B) (psi : B →CP C) (a : A) :
    PositiveKernelSeparated (ksgnsTensorKernel phi psi) →L[ℂ]
      PositiveKernelSeparated (ksgnsTensorKernel phi psi) :=
  (ksgnsTensorSeparatedLmul phi psi a).mkContinuous ‖a‖ (by
    intro x
    exact norm_ksgnsTensorSeparatedLmul_le phi psi a x)

@[simp]
theorem ksgnsTensorSeparatedLmulCLM_apply
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x : PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
    ksgnsTensorSeparatedLmulCLM phi psi a x =
      ksgnsTensorSeparatedLmul phi psi a x := rfl

/-- Bounded left `A`-action on the completed internal tensor product. -/
noncomputable def ksgnsTensorRepresentation
    (phi : A →CP B) (psi : B →CP C) (a : A) :
    KSGNSInternalTensorProduct phi psi →L[ℂ]
      KSGNSInternalTensorProduct phi psi :=
  completionExtendSL
    ((completionCoeLinearIsometry
      (E := PositiveKernelSeparated (ksgnsTensorKernel phi psi))).toContinuousLinearMap.comp
      (ksgnsTensorSeparatedLmulCLM phi psi a))

@[simp]
theorem ksgnsTensorRepresentation_coe
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x : PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
    ksgnsTensorRepresentation phi psi a
        (x : KSGNSInternalTensorProduct phi psi) =
      ((ksgnsTensorSeparatedLmul phi psi a x :
        PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
          KSGNSInternalTensorProduct phi psi) := by
  rw [ksgnsTensorRepresentation, completionExtendSL_coe]
  rfl

theorem ksgnsTensorSeparatedLmul_add_label
    (phi : A →CP B) (psi : B →CP C) (a d : A)
    (x : PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
    ksgnsTensorSeparatedLmul phi psi (a + d) x =
      ksgnsTensorSeparatedLmul phi psi a x +
        ksgnsTensorSeparatedLmul phi psi d x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (ksgnsTensorPreLmul (a + d) x) =
      Submodule.Quotient.mk
        (ksgnsTensorPreLmul a x + ksgnsTensorPreLmul d x)
    rw [Submodule.Quotient.eq]
    intro y
    rw [positiveKernelPreInner_sub_left,
      ksgnsTensorPreInner_lmul_add_label_left,
      positiveKernelPreInner_add_left]
    abel

theorem ksgnsTensorSeparatedLmul_smul_label
    (phi : A →CP B) (psi : B →CP C) (r : ℂ) (a : A)
    (x : PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
    ksgnsTensorSeparatedLmul phi psi (r • a) x =
      r • ksgnsTensorSeparatedLmul phi psi a x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (ksgnsTensorPreLmul (r • a) x) =
      Submodule.Quotient.mk (r • ksgnsTensorPreLmul a x)
    rw [Submodule.Quotient.eq]
    intro y
    rw [positiveKernelPreInner_sub_left,
      ksgnsTensorPreInner_lmul_smul_label_left,
      positiveKernelPreInner_smul_left]
    simp

theorem ksgnsTensorSeparatedLmul_one
    (phi : A →CP B) (psi : B →CP C)
    (x : PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
    ksgnsTensorSeparatedLmul phi psi 1 x = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (ksgnsTensorPreLmul 1 x) =
      Submodule.Quotient.mk x
    rw [ksgnsTensorPreLmul_one]

theorem ksgnsTensorSeparatedLmul_mul
    (phi : A →CP B) (psi : B →CP C) (a d : A)
    (x : PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
    ksgnsTensorSeparatedLmul phi psi (a * d) x =
      ksgnsTensorSeparatedLmul phi psi a
        (ksgnsTensorSeparatedLmul phi psi d x) := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (ksgnsTensorPreLmul (a * d) x) =
      Submodule.Quotient.mk
        (ksgnsTensorPreLmul a (ksgnsTensorPreLmul d x))
    rw [ksgnsTensorPreLmul_mul]

theorem ksgnsTensorSeparatedLmul_adjoint
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x y : PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
    ⟪ksgnsTensorSeparatedLmul phi psi a x, y⟫_Cᵐᵒᵖ =
      ⟪x, ksgnsTensorSeparatedLmul phi psi (star a) y⟫_Cᵐᵒᵖ := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y =>
    change MulOpposite.op
        (positiveKernelPreInner (ksgnsTensorKernel phi psi)
          (ksgnsTensorPreLmul a x) y) =
      MulOpposite.op
        (positiveKernelPreInner (ksgnsTensorKernel phi psi)
          x (ksgnsTensorPreLmul (star a) y))
    rw [ksgnsTensorPreInner_lmul_adjoint]

theorem ksgnsTensorSeparatedLmul_rmul
    (phi : A →CP B) (psi : B →CP C) (a : A) (c : C)
    (x : PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
    ksgnsTensorSeparatedLmul phi psi a (MulOpposite.op c • x) =
      MulOpposite.op c • ksgnsTensorSeparatedLmul phi psi a x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk
        (ksgnsTensorPreLmul a (positiveKernelPreRmul x c)) =
      Submodule.Quotient.mk
        (positiveKernelPreRmul (ksgnsTensorPreLmul a x) c)
    congr 1
    classical
    have rmul_add (u v : (A × B) →₀ C) :
        positiveKernelPreRmul (u + v) c =
          positiveKernelPreRmul u c + positiveKernelPreRmul v c := by
      ext p
      simp [positiveKernelPreRmul_apply, add_mul]
    induction x using Finsupp.induction_linear with
    | zero => simp [ksgnsTensorPreLmul, positiveKernelPreRmul]
    | add x y hx hy =>
        rw [rmul_add, ksgnsTensorPreLmul_add, ksgnsTensorPreLmul_add,
          rmul_add, hx, hy]
    | single p d =>
        rcases p with ⟨p, b⟩
        simp [mul_assoc]

theorem ksgnsTensorRepresentation_add
    (phi : A →CP B) (psi : B →CP C) (a d : A) :
    ksgnsTensorRepresentation phi psi (a + d) =
      ksgnsTensorRepresentation phi psi a +
        ksgnsTensorRepresentation phi psi d := by
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsTensorRepresentation phi psi (a + d)).continuous
      ((ksgnsTensorRepresentation phi psi a).continuous.add
        (ksgnsTensorRepresentation phi psi d).continuous)
  · intro x
    rw [ksgnsTensorRepresentation_coe]
    change ((ksgnsTensorSeparatedLmul phi psi (a + d) x :
        PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
          KSGNSInternalTensorProduct phi psi) =
      ksgnsTensorRepresentation phi psi a
          (x : KSGNSInternalTensorProduct phi psi) +
        ksgnsTensorRepresentation phi psi d
          (x : KSGNSInternalTensorProduct phi psi)
    rw [ksgnsTensorRepresentation_coe, ksgnsTensorRepresentation_coe,
      ← Completion.coe_add, ksgnsTensorSeparatedLmul_add_label]

theorem ksgnsTensorRepresentation_smul
    (phi : A →CP B) (psi : B →CP C) (r : ℂ) (a : A) :
    ksgnsTensorRepresentation phi psi (r • a) =
      r • ksgnsTensorRepresentation phi psi a := by
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsTensorRepresentation phi psi (r • a)).continuous
      ((continuous_const_smul r).comp
        (ksgnsTensorRepresentation phi psi a).continuous)
  · intro x
    rw [ksgnsTensorRepresentation_coe]
    change ((ksgnsTensorSeparatedLmul phi psi (r • a) x :
        PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
          KSGNSInternalTensorProduct phi psi) =
      r • ksgnsTensorRepresentation phi psi a
        (x : KSGNSInternalTensorProduct phi psi)
    rw [ksgnsTensorRepresentation_coe, ← Completion.coe_smul,
      ksgnsTensorSeparatedLmul_smul_label]

theorem ksgnsTensorRepresentation_one
    (phi : A →CP B) (psi : B →CP C) :
    ksgnsTensorRepresentation phi psi 1 =
      ContinuousLinearMap.id ℂ (KSGNSInternalTensorProduct phi psi) := by
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsTensorRepresentation phi psi 1).continuous continuous_id
  · intro x
    rw [ksgnsTensorRepresentation_coe,
      ksgnsTensorSeparatedLmul_one]
    rfl

theorem ksgnsTensorRepresentation_mul
    (phi : A →CP B) (psi : B →CP C) (a d : A) :
    ksgnsTensorRepresentation phi psi (a * d) =
      (ksgnsTensorRepresentation phi psi a).comp
        (ksgnsTensorRepresentation phi psi d) := by
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsTensorRepresentation phi psi (a * d)).continuous
      ((ksgnsTensorRepresentation phi psi a).continuous.comp
        (ksgnsTensorRepresentation phi psi d).continuous)
  · intro x
    rw [ksgnsTensorRepresentation_coe]
    change ((ksgnsTensorSeparatedLmul phi psi (a * d) x :
        PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
          KSGNSInternalTensorProduct phi psi) =
      ksgnsTensorRepresentation phi psi a
        (ksgnsTensorRepresentation phi psi d
          (x : KSGNSInternalTensorProduct phi psi))
    rw [ksgnsTensorRepresentation_coe, ksgnsTensorRepresentation_coe,
      ksgnsTensorSeparatedLmul_mul]

theorem ksgnsTensorRepresentation_adjoint
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x y : KSGNSInternalTensorProduct phi psi) :
    ⟪ksgnsTensorRepresentation phi psi a x, y⟫_Cᵐᵒᵖ =
      ⟪x, ksgnsTensorRepresentation phi psi (star a) y⟫_Cᵐᵒᵖ := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      ((continuous_positiveKernelCompleted_inner_pair
          (ksgnsTensorKernel phi psi)).comp
        (((ksgnsTensorRepresentation phi psi a).continuous.comp
          continuous_fst).prodMk continuous_snd))
      ((continuous_positiveKernelCompleted_inner_pair
          (ksgnsTensorKernel phi psi)).comp
        (continuous_fst.prodMk
          ((ksgnsTensorRepresentation phi psi (star a)).continuous.comp
            continuous_snd)))
  · intro x y
    rw [ksgnsTensorRepresentation_coe, ksgnsTensorRepresentation_coe,
      positiveKernelCompleted_inner_apply,
      positiveKernelCompleted_inner_apply,
      positiveKernelCompletedInnerSLM_coe_coe,
      positiveKernelCompletedInnerSLM_coe_coe]
    exact ksgnsTensorSeparatedLmul_adjoint phi psi a x y

theorem ksgnsTensorRepresentation_rmul
    (phi : A →CP B) (psi : B →CP C) (a : A) (c : C)
    (x : KSGNSInternalTensorProduct phi psi) :
    ksgnsTensorRepresentation phi psi a (MulOpposite.op c • x) =
      MulOpposite.op c • ksgnsTensorRepresentation phi psi a x := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      ((ksgnsTensorRepresentation phi psi a).continuous.comp
        (positiveKernelCompletedActionCLM
          (ksgnsTensorKernel phi psi) (MulOpposite.op c)).continuous)
      ((positiveKernelCompletedActionCLM
        (ksgnsTensorKernel phi psi) (MulOpposite.op c)).continuous.comp
          (ksgnsTensorRepresentation phi psi a).continuous)
  · intro x
    change ksgnsTensorRepresentation phi psi a
        (positiveKernelCompletedActionCLM
          (ksgnsTensorKernel phi psi) (MulOpposite.op c)
          (x : KSGNSInternalTensorProduct phi psi)) =
      positiveKernelCompletedActionCLM
        (ksgnsTensorKernel phi psi) (MulOpposite.op c)
          (ksgnsTensorRepresentation phi psi a
            (x : KSGNSInternalTensorProduct phi psi))
    rw [positiveKernelCompletedActionCLM_coe,
      ksgnsTensorRepresentation_coe, ksgnsTensorRepresentation_coe,
      positiveKernelCompletedActionCLM_coe,
      ksgnsTensorSeparatedLmul_rmul]

theorem ksgnsTensorRepresentation_zero
    (phi : A →CP B) (psi : B →CP C) :
    ksgnsTensorRepresentation phi psi 0 = 0 := by
  have h := ksgnsTensorRepresentation_smul phi psi (0 : ℂ) (0 : A)
  simpa using h

noncomputable def ksgnsTensorRepresentationAlgHom
    (phi : A →CP B) (psi : B →CP C) :
    A →ₐ[ℂ]
      (KSGNSInternalTensorProduct phi psi →L[ℂ]
        KSGNSInternalTensorProduct phi psi) where
  toFun := ksgnsTensorRepresentation phi psi
  map_one' := ksgnsTensorRepresentation_one phi psi
  map_mul' a d := by
    rw [ksgnsTensorRepresentation_mul]
    rfl
  map_zero' := ksgnsTensorRepresentation_zero phi psi
  map_add' := ksgnsTensorRepresentation_add phi psi
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one,
      ksgnsTensorRepresentation_smul,
      ksgnsTensorRepresentation_one,
      Algebra.algebraMap_eq_smul_one]
    congr 1

/-- The completed two-level kernel is a genuine `A`-`C` C-star correspondence. -/
noncomputable def canonicalKSGNSInternalTensorRepresentation
    (phi : A →CP B) (psi : B →CP C) :
    CStarModuleRepresentation A C (KSGNSInternalTensorProduct phi psi) where
  toAlgHom := ksgnsTensorRepresentationAlgHom phi psi
  adjoint_inner := ksgnsTensorRepresentation_adjoint phi psi
  map_op_smul := ksgnsTensorRepresentation_rmul phi psi

@[simp]
theorem ksgnsTensorRepresentation_generator
    (phi : A →CP B) (psi : B →CP C)
    (x a : A) (b : B) (c : C) :
    ksgnsTensorRepresentation phi psi x
        (ksgnsTensorGenerator phi psi a b c) =
      ksgnsTensorGenerator phi psi (x * a) b c := by
  rw [ksgnsTensorGenerator, ksgnsTensorRepresentation_coe,
    ksgnsTensorSeparatedLmul_mk, ksgnsTensorPreLmul_single]
  rfl

@[simp]
theorem ksgnsTensorGenerator_op_smul
    (phi : A →CP B) (psi : B →CP C)
    (a : A) (b : B) (c d : C) :
    MulOpposite.op d • ksgnsTensorGenerator phi psi a b c =
      ksgnsTensorGenerator phi psi a b (c * d) := by
  change positiveKernelCompletedActionCLM
      (ksgnsTensorKernel phi psi) (MulOpposite.op d)
      ((Submodule.Quotient.mk (Finsupp.single (a, b) c) :
        PositiveKernelSeparated (ksgnsTensorKernel phi psi)) :
          KSGNSInternalTensorProduct phi psi) = _
  rw [positiveKernelCompletedActionCLM_coe]
  congr 1
  simp

/-- Elementary tensor on cyclic spans:
`(π_phi(a)ξ_phi b) tensor (π_psi(d)ξ_psi c)`. -/
def ksgnsTensorElementary
    (phi : A →CP B) (psi : B →CP C)
    (a : A) (b d : B) (c : C) : KSGNSInternalTensorProduct phi psi :=
  ksgnsTensorGenerator phi psi a (b * d) c

/-- Exact balanced relation on elementary tensors. -/
theorem ksgnsTensorElementary_balance
    (phi : A →CP B) (psi : B →CP C)
    (a : A) (b q d : B) (c : C) :
    ksgnsTensorElementary phi psi a (b * q) d c =
      ksgnsTensorElementary phi psi a b (q * d) c := by
  simp [ksgnsTensorElementary, mul_assoc]

/-- Every dense kernel generator is an elementary balanced tensor. -/
theorem ksgnsTensorGenerator_eq_elementary
    (phi : A →CP B) (psi : B →CP C)
    (a : A) (b : B) (c : C) :
    ksgnsTensorGenerator phi psi a b c =
      ksgnsTensorElementary phi psi a 1 b c := by
  simp [ksgnsTensorElementary]

/-- Internal-tensor inner product on arbitrary cyclic elementary tensors. -/
theorem ksgnsTensorElementary_inner
    (phi : A →CP B) (psi : B →CP C)
    (a a' : A) (b b' d d' : B) (c c' : C) :
    (positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)).inner
        (ksgnsTensorElementary phi psi a b d c)
        (ksgnsTensorElementary phi psi a' b' d' c') =
      star c * psi
        (star d * (star b * phi (star a * a') * b') * d') * c' := by
  rw [ksgnsTensorElementary, ksgnsTensorElementary,
    ksgnsTensorGenerator_inner]
  simp [star_mul, mul_assoc]

theorem ksgnsTensorCompositeFreeMap_lmul
    (a : A) (x : A →₀ C) :
    ksgnsTensorCompositeFreeMap (B := B) (ksgnsPreLmul a x) =
      ksgnsTensorPreLmul a (ksgnsTensorCompositeFreeMap (B := B) x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsPreLmul, ksgnsTensorPreLmul]
  | add x y hx hy =>
      rw [ksgnsPreLmul_add, map_add, map_add,
        ksgnsTensorPreLmul_add, hx, hy]
  | single d c => simp

theorem ksgnsTensorCompositeSeparatedMap_lmul
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x : KSGNSSeparated (cpMapComp psi phi)) :
    ksgnsTensorCompositeSeparatedMap phi psi
        (ksgnsSeparatedLmul (cpMapComp psi phi) a x) =
      ksgnsTensorSeparatedLmul phi psi a
        (ksgnsTensorCompositeSeparatedMap phi psi x) := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change ksgnsTensorCompositeSeparatedMap phi psi
        (Submodule.Quotient.mk (ksgnsPreLmul a x)) =
      ksgnsTensorSeparatedLmul phi psi a
        (Submodule.Quotient.mk
          (ksgnsTensorCompositeFreeMap (B := B) x))
    rw [ksgnsTensorCompositeSeparatedMap_mk,
      ksgnsTensorSeparatedLmul_mk,
      ksgnsTensorCompositeFreeMap_lmul]

/-- The canonical composite isometry intertwines the left `A`-representations. -/
theorem ksgnsCompositeTensorIsometry_act
    (phi : A →CP B) (psi : B →CP C) (a : A)
    (x : KSGNS (cpMapComp psi phi)) :
    ksgnsCompositeTensorIsometry phi psi
        (ksgnsRepresentation (cpMapComp psi phi) a x) =
      ksgnsTensorRepresentation phi psi a
        (ksgnsCompositeTensorIsometry phi psi x) := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      ((ksgnsCompositeTensorIsometry phi psi).continuous.comp
        (ksgnsRepresentation (cpMapComp psi phi) a).continuous)
      ((ksgnsTensorRepresentation phi psi a).continuous.comp
        (ksgnsCompositeTensorIsometry phi psi).continuous)
  · intro x
    rw [ksgnsRepresentation_coe,
      ksgnsCompositeTensorIsometry_coe,
      ksgnsCompositeTensorIsometry_coe,
      ksgnsTensorRepresentation_coe,
      ksgnsTensorCompositeSeparatedMap_lmul]

theorem ksgnsTensorCompositeFreeMap_rmul
    (x : A →₀ C) (c : C) :
    ksgnsTensorCompositeFreeMap (B := B) (ksgnsPreRmul x c) =
      positiveKernelPreRmul (ksgnsTensorCompositeFreeMap (B := B) x) c := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsPreRmul, positiveKernelPreRmul]
  | add x y hx hy =>
      have source_add : ksgnsPreRmul (x + y) c =
          ksgnsPreRmul x c + ksgnsPreRmul y c := by
        ext a
        simp [ksgnsPreRmul_apply, add_mul]
      have target_add : positiveKernelPreRmul
          (ksgnsTensorCompositeFreeMap (B := B) x +
            ksgnsTensorCompositeFreeMap (B := B) y) c =
          positiveKernelPreRmul
              (ksgnsTensorCompositeFreeMap (B := B) x) c +
            positiveKernelPreRmul
              (ksgnsTensorCompositeFreeMap (B := B) y) c := by
        ext p
        simp [positiveKernelPreRmul_apply, add_mul]
      rw [source_add, map_add, map_add, target_add, hx, hy]
  | single a d => simp

theorem ksgnsTensorCompositeSeparatedMap_rmul
    (phi : A →CP B) (psi : B →CP C) (c : C)
    (x : KSGNSSeparated (cpMapComp psi phi)) :
    ksgnsTensorCompositeSeparatedMap phi psi (MulOpposite.op c • x) =
      MulOpposite.op c •
        ksgnsTensorCompositeSeparatedMap phi psi x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change ksgnsTensorCompositeSeparatedMap phi psi
        (Submodule.Quotient.mk (ksgnsPreRmul x c)) =
      MulOpposite.op c •
        (Submodule.Quotient.mk
          (ksgnsTensorCompositeFreeMap (B := B) x) :
            PositiveKernelSeparated (ksgnsTensorKernel phi psi))
    rw [ksgnsTensorCompositeSeparatedMap_mk,
      positiveKernelSeparated_op_smul_mk,
      ksgnsTensorCompositeFreeMap_rmul]

/-- The canonical composite isometry is right `C`-linear. -/
theorem ksgnsCompositeTensorIsometry_rmul
    (phi : A →CP B) (psi : B →CP C) (c : C)
    (x : KSGNS (cpMapComp psi phi)) :
    ksgnsCompositeTensorIsometry phi psi (MulOpposite.op c • x) =
      MulOpposite.op c • ksgnsCompositeTensorIsometry phi psi x := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      ((ksgnsCompositeTensorIsometry phi psi).continuous.comp
        (ksgnsCompletedActionCLM
          (cpMapComp psi phi) (MulOpposite.op c)).continuous)
      ((positiveKernelCompletedActionCLM
        (ksgnsTensorKernel phi psi) (MulOpposite.op c)).continuous.comp
          (ksgnsCompositeTensorIsometry phi psi).continuous)
  · intro x
    change ksgnsCompositeTensorIsometry phi psi
        (ksgnsCompletedActionCLM
          (cpMapComp psi phi) (MulOpposite.op c)
          (x : KSGNS (cpMapComp psi phi))) =
      positiveKernelCompletedActionCLM
        (ksgnsTensorKernel phi psi) (MulOpposite.op c)
          (ksgnsCompositeTensorIsometry phi psi
            (x : KSGNS (cpMapComp psi phi)))
    rw [ksgnsCompletedActionCLM_coe,
      ksgnsCompositeTensorIsometry_coe,
      ksgnsCompositeTensorIsometry_coe,
      positiveKernelCompletedActionCLM_coe,
      ksgnsTensorCompositeSeparatedMap_rmul]

/-- The canonical composite isometry preserves the full `C`-valued inner product. -/
theorem ksgnsCompositeTensorIsometry_inner
    (phi : A →CP B) (psi : B →CP C)
    (x y : KSGNS (cpMapComp psi phi)) :
    ⟪ksgnsCompositeTensorIsometry phi psi x,
      ksgnsCompositeTensorIsometry phi psi y⟫_Cᵐᵒᵖ =
      ⟪x, y⟫_Cᵐᵒᵖ := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      ((continuous_positiveKernelCompleted_inner_pair
        (ksgnsTensorKernel phi psi)).comp
          (((ksgnsCompositeTensorIsometry phi psi).continuous.comp
            continuous_fst).prodMk
          ((ksgnsCompositeTensorIsometry phi psi).continuous.comp
            continuous_snd)))
      (continuous_ksgnsCompleted_inner_pair (cpMapComp psi phi))
  · intro x y
    change positiveKernelCompletedInnerSLM (ksgnsTensorKernel phi psi)
        (ksgnsCompositeTensorIsometry phi psi
          (x : KSGNS (cpMapComp psi phi)))
        (ksgnsCompositeTensorIsometry phi psi
          (y : KSGNS (cpMapComp psi phi))) =
      ksgnsCompletedInnerSLM (cpMapComp psi phi)
        (x : KSGNS (cpMapComp psi phi))
        (y : KSGNS (cpMapComp psi phi))
    rw [ksgnsCompositeTensorIsometry_coe,
      ksgnsCompositeTensorIsometry_coe,
      positiveKernelCompletedInnerSLM_coe_coe,
      ksgnsCompletedInnerSLM_coe_coe]
    exact congrArg MulOpposite.op
      (positiveKernelSeparatedInner_tensorCompositeSeparatedMap phi psi x y)

/-- Standard `C`-valued form of inner-product preservation. -/
theorem ksgnsCompositeTensorIsometry_inner_unop
    (phi : A →CP B) (psi : B →CP C)
    (x y : KSGNS (cpMapComp psi phi)) :
    (positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)).inner
        (ksgnsCompositeTensorIsometry phi psi x)
        (ksgnsCompositeTensorIsometry phi psi y) =
      (ksgnsRightInnerModuleData (cpMapComp psi phi)).inner x y := by
  exact congrArg MulOpposite.unop
    (ksgnsCompositeTensorIsometry_inner phi psi x y)

/-- Point of the completed internal tensor product. -/
def ksgnsTensorCyclic (phi : A →CP B) (psi : B →CP C) :
    KSGNSInternalTensorProduct phi psi :=
  ksgnsTensorGenerator phi psi 1 1 1

theorem ksgnsCompositeTensorIsometry_cyclic
    (phi : A →CP B) (psi : B →CP C) :
    ksgnsCompositeTensorIsometry phi psi
        (ksgnsCyclic (cpMapComp psi phi)) =
      ksgnsTensorCyclic phi psi := by
  have hone :
      MulOpposite.op (1 : C) •
          ksgnsRepresentation (cpMapComp psi phi) 1
            (ksgnsCyclic (cpMapComp psi phi)) =
        ksgnsCyclic (cpMapComp psi phi) := by
    rw [ksgnsRepresentation_one]
    change MulOpposite.op (1 : C) •
        ksgnsCyclic (cpMapComp psi phi) = _
    exact ksgnsCompleted_one_op_smul _ _
  rw [← hone]
  exact ksgnsCompositeTensorIsometry_cyclicGenerator phi psi 1 1

/-- Exact pointed correspondence-isometry package for Equation (5). -/
structure KSGNSCompositePointedIsometry
    (phi : A →CP B) (psi : B →CP C) where
  toLinearIsometry :
    KSGNS (cpMapComp psi phi) →ₗᵢ[ℂ] KSGNSInternalTensorProduct phi psi
  map_cyclic :
    toLinearIsometry (ksgnsCyclic (cpMapComp psi phi)) =
      ksgnsTensorCyclic phi psi
  map_act : ∀ (a : A) (x : KSGNS (cpMapComp psi phi)),
    toLinearIsometry (ksgnsRepresentation (cpMapComp psi phi) a x) =
      ksgnsTensorRepresentation phi psi a (toLinearIsometry x)
  map_rmul : ∀ (c : C) (x : KSGNS (cpMapComp psi phi)),
    toLinearIsometry (MulOpposite.op c • x) =
      MulOpposite.op c • toLinearIsometry x
  map_inner : ∀ (x y : KSGNS (cpMapComp psi phi)),
    (positiveKernelRightInnerModuleData (ksgnsTensorKernel phi psi)).inner
        (toLinearIsometry x) (toLinearIsometry y) =
      (ksgnsRightInnerModuleData (cpMapComp psi phi)).inner x y

/-- Canonical pointed `A`-`C` correspondence isometry implementing KSGNS succession. -/
noncomputable def canonicalKSGNSCompositePointedIsometry
    (phi : A →CP B) (psi : B →CP C) :
    KSGNSCompositePointedIsometry phi psi where
  toLinearIsometry := ksgnsCompositeTensorIsometry phi psi
  map_cyclic := ksgnsCompositeTensorIsometry_cyclic phi psi
  map_act := ksgnsCompositeTensorIsometry_act phi psi
  map_rmul := ksgnsCompositeTensorIsometry_rmul phi psi
  map_inner := ksgnsCompositeTensorIsometry_inner_unop phi psi

/-- Equation (8): weighted succession for the actual CP-map composite, with the canonical
intermediate and output inverse order units left explicit. -/
theorem ksgnsWeightedSuccession
    (phi : A →CP B) (psi : B →CP C)
    (intermediateOrderInv : B) (outputOrderInv : C) (x y : A) :
    weightedStarMultiplicativeDefect
        (cpMapComp psi phi) outputOrderInv x y =
      psi (weightedStarMultiplicativeDefect
        phi intermediateOrderInv x y) +
      relativeWeightedStarMultiplicativeDefect
        psi intermediateOrderInv outputOrderInv (phi x) (phi y) := by
  exact weightedStarMultiplicativeDefect_comp
    (phi := fun z => phi z) (psi := psi.toLinearMap.toAddHom)
    intermediateOrderInv outputOrderInv x y

end GaloisForLFunctions.HTGeometry
