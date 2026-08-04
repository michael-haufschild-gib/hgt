import GaloisForLFunctions.RHTower.CCMRationalNonunitalStrongCyclicTopology
import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicRealContinuity
import GaloisForLFunctions.RHTower.KRealCyclicBarTrace

/-!
# Real structure on the literal nonunital CCM strong target

Quaternionic conjugation acts first on the genuine trace-class ideal field
and then on its one global unitization.  Global augmentation is conjugated,
and normalized diagonal trace is pointwise conjugated, so both defining
kernels of literal Definition 4.9 are stable.  The faithful cyclic embedding
intertwines this Real structure with the verified pointwise-field Real
structure, which proves continuity for the induced topology.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Ideal := CCMRationalMoritaTraceNormOperator
private abbrev IdealField :=
  CCMRationalContinuousTraceNormIdealField
private abbrev FieldUnit :=
  CCMRationalContinuousTraceNormIdealFieldUnitization

/-- Fibrewise quaternionic conjugation on genuine trace-class ideal fields. -/
def ccmRationalContinuousTraceNormIdealFieldReal
    (F : IdealField) : IdealField where
  toFun b := ccmRationalMoritaTraceNormRealStructure (F b)
  continuous_toFun :=
    ccmRationalMoritaTraceNormRealIsometry.continuous.comp F.continuous

@[simp]
theorem ccmRationalContinuousTraceNormIdealFieldReal_apply
    (F : IdealField) (b : Section) :
    ccmRationalContinuousTraceNormIdealFieldReal F b =
      ccmRationalMoritaTraceNormRealStructure (F b) :=
  rfl

@[simp]
theorem ccmRationalContinuousTraceNormIdealFieldReal_add
    (F G : IdealField) :
    ccmRationalContinuousTraceNormIdealFieldReal (F + G) =
      ccmRationalContinuousTraceNormIdealFieldReal F +
        ccmRationalContinuousTraceNormIdealFieldReal G := by
  apply ContinuousMap.ext
  intro b
  exact ccmRationalMoritaTraceNormRealStructure_add (F b) (G b)

@[simp]
theorem ccmRationalContinuousTraceNormIdealFieldReal_smul
    (z : ℂ) (F : IdealField) :
    ccmRationalContinuousTraceNormIdealFieldReal (z • F) =
      star z • ccmRationalContinuousTraceNormIdealFieldReal F := by
  apply ContinuousMap.ext
  intro b
  exact ccmRationalMoritaTraceNormRealStructure_smul z (F b)

@[simp]
theorem ccmRationalContinuousTraceNormIdealFieldReal_mul
    (F G : IdealField) :
    ccmRationalContinuousTraceNormIdealFieldReal (F * G) =
      ccmRationalContinuousTraceNormIdealFieldReal F *
        ccmRationalContinuousTraceNormIdealFieldReal G := by
  apply ContinuousMap.ext
  intro b
  exact ccmRationalMoritaTraceNormRealStructure_mul (F b) (G b)

@[simp]
theorem ccmRationalContinuousTraceNormIdealFieldReal_sq
    (F : IdealField) :
    ccmRationalContinuousTraceNormIdealFieldReal
        (ccmRationalContinuousTraceNormIdealFieldReal F) = F := by
  apply ContinuousMap.ext
  intro b
  exact ccmRationalMoritaTraceNormRealStructure_sq (F b)

@[simp]
theorem ccmRationalContinuousTraceNormIdealFieldReal_zero :
    ccmRationalContinuousTraceNormIdealFieldReal (0 : IdealField) = 0 := by
  apply ContinuousMap.ext
  intro b
  exact ccmRationalMoritaTraceNormRealStructure_zero

/-- Real involution on the one global unitization. -/
def ccmRationalNonunitalFieldReal (x : FieldUnit) : FieldUnit :=
  Unitization.equiv.symm
    (star x.fst, ccmRationalContinuousTraceNormIdealFieldReal x.snd)

@[simp]
theorem ccmRationalNonunitalFieldReal_fst (x : FieldUnit) :
    (ccmRationalNonunitalFieldReal x).fst = star x.fst :=
  rfl

@[simp]
theorem ccmRationalNonunitalFieldReal_snd (x : FieldUnit) :
    (ccmRationalNonunitalFieldReal x).snd =
      ccmRationalContinuousTraceNormIdealFieldReal x.snd :=
  rfl

@[simp]
theorem ccmRationalNonunitalFieldReal_add (x y : FieldUnit) :
    ccmRationalNonunitalFieldReal (x + y) =
      ccmRationalNonunitalFieldReal x + ccmRationalNonunitalFieldReal y := by
  apply Unitization.ext <;> simp [map_add]

@[simp]
theorem ccmRationalNonunitalFieldReal_smul (z : ℂ) (x : FieldUnit) :
    ccmRationalNonunitalFieldReal (z • x) =
      star z • ccmRationalNonunitalFieldReal x := by
  apply Unitization.ext <;> simp [mul_comm]

@[simp]
theorem ccmRationalNonunitalFieldReal_mul (x y : FieldUnit) :
    ccmRationalNonunitalFieldReal (x * y) =
      ccmRationalNonunitalFieldReal x * ccmRationalNonunitalFieldReal y := by
  apply Unitization.ext
  · simp [Unitization.fst_mul, map_mul]
  · simp [Unitization.snd_mul, map_add, map_mul]

@[simp]
theorem ccmRationalNonunitalFieldReal_one :
    ccmRationalNonunitalFieldReal (1 : FieldUnit) = 1 := by
  apply Unitization.ext <;> simp

@[simp]
theorem ccmRationalNonunitalFieldReal_sq (x : FieldUnit) :
    ccmRationalNonunitalFieldReal (ccmRationalNonunitalFieldReal x) = x := by
  apply Unitization.ext <;> simp

def ccmRationalNonunitalFieldRealₛₗ : FieldUnit →ₗ⋆[ℂ] FieldUnit where
  toFun := ccmRationalNonunitalFieldReal
  map_add' := ccmRationalNonunitalFieldReal_add
  map_smul' := ccmRationalNonunitalFieldReal_smul

/-- Even Real algebra structure on the globally unitized ideal-field
algebra. -/
def ccmRationalNonunitalFieldKRealAlgebra :
    KRealAlgebraStructure FieldUnit where
  sigma := ccmRationalNonunitalFieldRealₛₗ
  sq x := by
    change ccmRationalNonunitalFieldReal
        (ccmRationalNonunitalFieldReal x) = kRealParityAction false x
    rw [ccmRationalNonunitalFieldReal_sq]
    rfl
  map_one := ccmRationalNonunitalFieldReal_one
  map_mul := ccmRationalNonunitalFieldReal_mul

/-- Evaluation intertwines global and fibre Real structures. -/
theorem ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation_real
    (b : Section) (x : FieldUnit) :
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation b
        (ccmRationalNonunitalFieldReal x) =
      ccmRationalMoritaTraceNormL1RealStructure
        (ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation b x) := by
  apply WithLp.ofLp_injective
  rw [ccmRationalMoritaTraceNormL1RealStructure_ofLp]
  apply Unitization.ext
  · induction x using Unitization.ind with
    | inl_add_inr z F =>
        simp [ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation,
          ccmRationalNonunitalFieldReal,
          ccmRationalMoritaTraceNormUnitizedRealStructure,
          Unitization.algebraMap_eq_inl]
  · induction x using Unitization.ind with
    | inl_add_inr z F =>
        simp [ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation,
          ccmRationalNonunitalFieldReal,
          ccmRationalMoritaTraceNormUnitizedRealStructure,
          Unitization.algebraMap_eq_inl,
          ccmRationalMoritaTraceNormRealStructure_add,
          ccmRationalMoritaTraceNormRealStructure_smul]

theorem ccmRationalNonunitalFieldPointTrace_real
    (b : Section) (x : FieldUnit) :
    ccmRationalNonunitalFieldPointTrace b
        (ccmRationalNonunitalFieldReal x) =
      star (ccmRationalNonunitalFieldPointTrace b x) := by
  rw [ccmRationalNonunitalFieldPointTrace_apply,
    ccmRationalNonunitalFieldPointTrace_apply,
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation_real]
  exact ccmRationalMoritaTraceNormL1Trace_real _

theorem ccmRationalNonunitalFieldAugmentation_real (x : FieldUnit) :
    ccmRationalNonunitalFieldAugmentation
        (ccmRationalNonunitalFieldReal x) =
      star (ccmRationalNonunitalFieldAugmentation x) :=
  rfl

/-- Diagonal trace is pointwise conjugated in every cyclic degree. -/
theorem ccmRationalNonunitalStrongDiagonalTrace_real
    (n : ℕ) (x : CyclicBarTensor ℂ FieldUnit n) :
    ccmRationalNonunitalStrongDiagonalTrace n
        ((cyclicBarDegreeKReal
          ccmRationalNonunitalFieldKRealAlgebra n).sigma x) =
      fun b => star (ccmRationalNonunitalStrongDiagonalTrace n x b) := by
  funext b
  exact (cyclicBarTraceAugmentation_kReal
    ccmRationalNonunitalFieldKRealAlgebra
    (ccmRationalNonunitalFieldPointTrace b)
    (ccmRationalNonunitalFieldPointTrace_real b) n x).symm

/-- Degreewise Real structure restricted to both literal target kernels. -/
def ccmRationalNonunitalStrongCyclicTargetDegreeKReal (n : ℕ) :
    KRealStructure false
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) where
  sigma :=
    { toFun := fun x =>
        ⟨(cyclicBarDegreeKReal
            ccmRationalNonunitalFieldKRealAlgebra n).sigma x.1,
          (mem_ccmRationalNonunitalStrongCyclicTarget_iff n _).mpr ⟨by
            have haug :=
              (mem_ccmRationalNonunitalStrongCyclicTarget_iff n x.1).mp x.2 |>.1
            change cyclicBarTraceAugmentation
              ccmRationalNonunitalFieldAugmentation n
              ((cyclicBarDegreeKReal
                ccmRationalNonunitalFieldKRealAlgebra n).sigma x.1) = 0
            calc
              cyclicBarTraceAugmentation
                  ccmRationalNonunitalFieldAugmentation n
                  ((cyclicBarDegreeKReal
                    ccmRationalNonunitalFieldKRealAlgebra n).sigma x.1) =
                  star (cyclicBarTraceAugmentation
                    ccmRationalNonunitalFieldAugmentation n x.1) :=
                (cyclicBarTraceAugmentation_kReal
                  ccmRationalNonunitalFieldKRealAlgebra
                  ccmRationalNonunitalFieldAugmentation
                  ccmRationalNonunitalFieldAugmentation_real n x.1).symm
              _ = 0 := by simp [haug], by
            rw [ccmRationalNonunitalStrongDiagonalTrace_real]
            exact CCMRationalStrongClassSpaceScalarTarget.real_mem
              ((mem_ccmRationalNonunitalStrongCyclicTarget_iff n x.1).mp
                x.2 |>.2)⟩⟩
      map_add' x y := by
        apply Subtype.ext
        exact map_add
          (cyclicBarDegreeKReal
            ccmRationalNonunitalFieldKRealAlgebra n).sigma x.1 y.1
      map_smul' z x := by
        apply Subtype.ext
        exact (cyclicBarDegreeKReal
          ccmRationalNonunitalFieldKRealAlgebra n).sigma.map_smulₛₗ z x.1 }
  sq x := by
    apply Subtype.ext
    exact (cyclicBarDegreeKReal
      ccmRationalNonunitalFieldKRealAlgebra n).sq x.1

/-- Literal nonunital strong target with its even Real cyclic structure. -/
def ccmRationalNonunitalStrongCyclicTargetKReal :
    CyclicModule.KReal false CCMRationalNonunitalStrongCyclicTarget where
  real := ccmRationalNonunitalStrongCyclicTargetDegreeKReal
  face_naturality n i x := by
    apply Subtype.ext
    exact (cyclicBarKReal
      ccmRationalNonunitalFieldKRealAlgebra).face_naturality n i x.1
  degeneracy_naturality n i x := by
    apply Subtype.ext
    exact (cyclicBarKReal
      ccmRationalNonunitalFieldKRealAlgebra).degeneracy_naturality n i x.1
  cyclic_naturality n x := by
    apply Subtype.ext
    exact (cyclicBarKReal
      ccmRationalNonunitalFieldKRealAlgebra).cyclic_naturality n x.1

/-- Global-to-pointwise inclusion is Real-equivariant. -/
theorem ccmRationalNonunitalFieldToPointwiseAlgHom_real
    (x : FieldUnit) :
    ccmRationalContinuousTraceNormFieldReal
        (ccmRationalNonunitalFieldToPointwiseAlgHom x) =
      ccmRationalNonunitalFieldToPointwiseAlgHom
        (ccmRationalNonunitalFieldReal x) := by
  apply ContinuousMap.ext
  intro b
  rw [ccmRationalContinuousTraceNormFieldReal_apply,
    ccmRationalNonunitalFieldToPointwiseAlgHom_apply,
    ccmRationalNonunitalFieldToPointwiseAlgHom_apply,
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation_real]

/-- Faithful strong cyclic embedding intertwines Real structures. -/
theorem ccmRationalNonunitalStrongCyclicEmbedding_real
    (n : ℕ)
    (x : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalNonunitalStrongCyclicEmbeddingDegree n
        ((ccmRationalNonunitalStrongCyclicTargetKReal.real n).sigma x) =
      (ccmRationalStrongCyclicTargetKReal.real n).sigma
        (ccmRationalNonunitalStrongCyclicEmbeddingDegree n x) := by
  apply Subtype.ext
  exact (cyclicBarAlgHomDegree_kReal
    ccmRationalNonunitalFieldKRealAlgebra
    ccmRationalContinuousTraceNormFieldKRealAlgebra
    ccmRationalNonunitalFieldToPointwiseAlgHom
    ccmRationalNonunitalFieldToPointwiseAlgHom_real n x.1).symm

/-- Literal target Real involution is continuous in every cyclic degree. -/
theorem ccmRationalNonunitalStrongCyclicDegreeReal_continuous (n : ℕ) :
    @Continuous
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
      (ccmRationalNonunitalStrongCyclicDegreeTopology n)
      (ccmRationalNonunitalStrongCyclicDegreeTopology n)
      (ccmRationalNonunitalStrongCyclicTargetKReal.real n).sigma := by
  letI : TopologicalSpace
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalNonunitalStrongCyclicDegreeTopology n
  have htop :
      ccmRationalStrongCyclicTopology.topology (.op (.mk n)) =
        ccmRationalStrongCyclicDegreeTopology n := by
    rfl
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicDegreeTopology n
  rw [continuous_induced_rng]
  have hembed :
      @Continuous
        (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
        (CCMRationalStrongCyclicTarget.simplicial.degree n)
        (ccmRationalNonunitalStrongCyclicDegreeTopology n)
        (ccmRationalStrongCyclicDegreeTopology n)
        (ccmRationalNonunitalStrongCyclicEmbeddingDegree n) := by
    rw [← htop]
    exact continuous_ccmRationalNonunitalStrongCyclicEmbeddingDegree n
  have h :=
    (ccmRationalStrongCyclicDegreeReal_continuous n).comp hembed
  convert h using 1
  funext x
  exact ccmRationalNonunitalStrongCyclicEmbedding_real n x

/-- Continuous Real structure on literal Definition 4.9. -/
def ccmRationalNonunitalStrongCyclicKRealTopology :
    CyclicModule.KRealTopology ccmRationalNonunitalStrongCyclicTargetKReal
      ccmRationalNonunitalStrongCyclicTopology where
  real_continuous :=
    ccmRationalNonunitalStrongCyclicDegreeReal_continuous

end GaloisForLFunctions.RHTower
