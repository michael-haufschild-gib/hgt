import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentArithmetic
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentQuotientProbability
import Mathlib.Topology.Homeomorph.Quotient

/-!
# Probability on the actual elliptic unipotent arithmetic quotient

The actual restricted unipotent carrier is equipped with its explicit
coefficient topology. Its literal arithmetic intersection corresponds to
the uniformly integral rational matrices. The resulting quotient is
homeomorphic to the product of additive domains and carries a probability
invariant under actual left multiplication.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein MeasureTheory
noncomputable section

/-- The actual restricted unipotent carrier, with coefficient topology below. -/
def AdelicUnipotentModel := adelicPositiveUnipotent

instance : Group AdelicUnipotentModel := inferInstanceAs (Group adelicPositiveUnipotent)

/-- The audited coefficient identification of the actual restricted group. -/
def uniformToAdelicUnipotent : UniformUnipotentModel ≃* AdelicUnipotentModel :=
  adelicUnipotentEquiv

instance : TopologicalSpace AdelicUnipotentModel :=
  TopologicalSpace.induced uniformToAdelicUnipotent.symm inferInstance

/-- The coefficient topology makes the actual carrier identification a homeomorphism. -/
def uniformAdelicUnipotentHomeomorph : UniformUnipotentModel ≃ₜ AdelicUnipotentModel where
  toEquiv := uniformToAdelicUnipotent.toEquiv
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    have he : uniformToAdelicUnipotent.symm ∘ uniformToAdelicUnipotent.toFun = id := by
      funext g
      exact uniformToAdelicUnipotent.symm_apply_apply g
    rw [he]
    exact continuous_id
  continuous_invFun := continuous_induced_dom

/-- The literal arithmetic intersection inside the actual unipotent carrier. -/
def adelicUnipotentArithmetic : Subgroup AdelicUnipotentModel :=
  arithmeticLoopGroup.comap adelicPositiveUnipotent.subtype

/-- The actual arithmetic intersection is precisely the rational coefficient subgroup. -/
theorem uniformToAdelicUnipotent_mem_arithmetic (g : UniformUnipotentModel) :
    uniformToAdelicUnipotent g ∈ adelicUnipotentArithmetic ↔
      g ∈ uniformRationalUnipotentRange := by
  change adelicUnipotentEmbedding g ∈ arithmeticLoopGroup ↔
    g ∈ uniformRationalUnipotentRange
  rw [adelicUnipotentEmbedding_mem_arithmetic_iff]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, Subtype.ext hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, congrArg Subtype.val hr⟩

/-- Right cosets by the literal intersection with the actual arithmetic group. -/
abbrev AdelicUnipotentQuotient := AdelicUnipotentModel ⧸ adelicUnipotentArithmetic

private theorem mulEquiv_leftRel {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) (B : Subgroup H)
    (he : ∀ x, e x ∈ B ↔ x ∈ A) (a b : G) :
    QuotientGroup.leftRel A a b ↔ QuotientGroup.leftRel B (e a) (e b) := by
  rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← e.map_inv, ← e.map_mul]
  exact (he (a⁻¹ * b)).symm

private theorem uniformAdelicUnipotent_relation (a b : UniformUnipotentModel) :
    QuotientGroup.leftRel uniformRationalUnipotentRange a b ↔
      QuotientGroup.leftRel adelicUnipotentArithmetic
        (uniformAdelicUnipotentHomeomorph a) (uniformAdelicUnipotentHomeomorph b) :=
  mulEquiv_leftRel uniformToAdelicUnipotent uniformRationalUnipotentRange
    adelicUnipotentArithmetic uniformToAdelicUnipotent_mem_arithmetic a b

/-- The coefficient quotient is homeomorphic to the literal adelic arithmetic quotient. -/
def unipotentActualQuotientHomeomorph :
    UnipotentCoefficientQuotient ≃ₜ AdelicUnipotentQuotient :=
  Homeomorph.Quotient.congr uniformAdelicUnipotentHomeomorph uniformAdelicUnipotent_relation

@[simp] theorem unipotentActualQuotientHomeomorph_mk (g : UniformUnipotentModel) :
    unipotentActualQuotientHomeomorph (g : UnipotentCoefficientQuotient) =
      (uniformToAdelicUnipotent g : AdelicUnipotentQuotient) := rfl

@[simp] theorem unipotentActualQuotientHomeomorph_symm_mk (g : AdelicUnipotentModel) :
    unipotentActualQuotientHomeomorph.symm (g : AdelicUnipotentQuotient) =
      (uniformToAdelicUnipotent.symm g : UnipotentCoefficientQuotient) := rfl

/-- Actual arithmetic cosets have unique continuous product-domain coordinates. -/
def adelicUnipotentQuotientDomainHomeomorph :
    AdelicUnipotentQuotient ≃ₜ (ℕ → ellipticAdditiveDomain) :=
  unipotentActualQuotientHomeomorph.symm.trans unipotentCoefficientQuotientHomeomorph

instance : MeasurableSpace AdelicUnipotentQuotient := borel _
instance : BorelSpace AdelicUnipotentQuotient := ⟨rfl⟩

/-- The continuous left action on the literal arithmetic quotient. -/
def adelicUnipotentQuotientLeft (g : AdelicUnipotentModel)
    (q : AdelicUnipotentQuotient) : AdelicUnipotentQuotient :=
  unipotentActualQuotientHomeomorph
    (unipotentCoefficientQuotientLeft (uniformToAdelicUnipotent.symm g)
      (unipotentActualQuotientHomeomorph.symm q))

theorem continuous_adelicUnipotentQuotientLeft (g : AdelicUnipotentModel) :
    Continuous (adelicUnipotentQuotientLeft g) :=
  unipotentActualQuotientHomeomorph.continuous.comp
    ((continuous_unipotentCoefficientQuotientLeft (uniformToAdelicUnipotent.symm g)).comp
      unipotentActualQuotientHomeomorph.symm.continuous)

private theorem mulEquiv_apply_symm_mul {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (g h : H) : e (e.symm g * e.symm h) = g * h :=
  (e.map_mul (e.symm g) (e.symm h)).trans
    (congrArg₂ (fun x y : H => x * y) (e.apply_symm_apply g) (e.apply_symm_apply h))

/-- The transported action is literal left multiplication on actual arithmetic cosets. -/
theorem adelicUnipotentQuotientLeft_mk (g h : AdelicUnipotentModel) :
    adelicUnipotentQuotientLeft g (h : AdelicUnipotentQuotient) =
      ((g * h : AdelicUnipotentModel) : AdelicUnipotentQuotient) := by
  exact (congrArg unipotentActualQuotientHomeomorph
    (unipotentCoefficientQuotientLeft_mk
      (uniformToAdelicUnipotent.symm g) (uniformToAdelicUnipotent.symm h))).trans
        (congrArg (fun z : AdelicUnipotentModel => (z : AdelicUnipotentQuotient))
          (mulEquiv_apply_symm_mul uniformToAdelicUnipotent g h))

/-- The canonical probability on the literal adelic unipotent arithmetic quotient. -/
def adelicUnipotentQuotientProbability : Measure AdelicUnipotentQuotient :=
  Measure.map unipotentActualQuotientHomeomorph unipotentCoefficientQuotientProbability

instance adelicUnipotentQuotientProbability_isProbability :
    IsProbabilityMeasure adelicUnipotentQuotientProbability := by
  constructor
  change (Measure.map unipotentActualQuotientHomeomorph
    unipotentCoefficientQuotientProbability) Set.univ = 1
  rw [Measure.map_apply unipotentActualQuotientHomeomorph.continuous.measurable
    MeasurableSet.univ, Set.preimage_univ]
  exact measure_univ

private theorem equiv_conjugate_comp {A B : Type*} (e : A ≃ B) (f : A → A) :
    (fun b => e (f (e.symm b))) ∘ e = e ∘ f := by
  funext a
  exact congrArg (fun x => e (f x)) (e.symm_apply_apply a)

private theorem adelicQuotientLeft_transfer (g : AdelicUnipotentModel) :
    adelicUnipotentQuotientLeft g ∘ unipotentActualQuotientHomeomorph =
      unipotentActualQuotientHomeomorph ∘
        unipotentCoefficientQuotientLeft (uniformToAdelicUnipotent.symm g) :=
  equiv_conjugate_comp unipotentActualQuotientHomeomorph.toEquiv
    (unipotentCoefficientQuotientLeft (uniformToAdelicUnipotent.symm g))

/-- Every actual left translation preserves the quotient probability. -/
theorem measurePreserving_adelicUnipotentQuotientLeft (g : AdelicUnipotentModel) :
    MeasurePreserving (adelicUnipotentQuotientLeft g)
      adelicUnipotentQuotientProbability adelicUnipotentQuotientProbability := by
  refine ⟨(continuous_adelicUnipotentQuotientLeft g).measurable, ?_⟩
  change Measure.map (adelicUnipotentQuotientLeft g)
    (Measure.map unipotentActualQuotientHomeomorph unipotentCoefficientQuotientProbability) =
      Measure.map unipotentActualQuotientHomeomorph unipotentCoefficientQuotientProbability
  rw [Measure.map_map (continuous_adelicUnipotentQuotientLeft g).measurable
    unipotentActualQuotientHomeomorph.continuous.measurable, adelicQuotientLeft_transfer,
    ← Measure.map_map unipotentActualQuotientHomeomorph.continuous.measurable
      (continuous_unipotentCoefficientQuotientLeft (uniformToAdelicUnipotent.symm g)).measurable,
    (measurePreserving_unipotentCoefficientQuotientLeft (uniformToAdelicUnipotent.symm g)).map_eq]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicUnipotentQuotientDomainHomeomorph
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicUnipotentQuotientLeft_mk
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicUnipotentQuotientProbability_isProbability
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.measurePreserving_adelicUnipotentQuotientLeft
