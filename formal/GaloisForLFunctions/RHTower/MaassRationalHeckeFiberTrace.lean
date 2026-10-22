import GaloisForLFunctions.RHTower.MaassRationalHeckeConjugateCoverL2
import GaloisForLFunctions.RHTower.Deninger.DeningerCosetTransfer

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise Function

noncomputable section

noncomputable instance rationalHeckeConjugateFiberFintype (N : ℕ) (g : GL (Fin 2) ℚ) :
    Fintype ((rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) :=
  Fintype.ofFinite _

/-- Finite fiber trace from the common cover to the rational-conjugate quotient.
The quotient lift uses `RHTower.deningerFiberShift`, so it is independent of the
chosen representative of a rational quotient class. -/
noncomputable def rationalHeckeConjugateFiberTrace (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ)
    (x : SL2R ⧸ rationalConjugateSL2Group N g) : ℂ := by
  let K := rationalHeckeCommonCoverReal N g
  let R := rationalConjugateSL2Group N g
  letI : K.IsFiniteRelIndex R :=
    realImage_rationalHeckeIntegralIntersection_isFiniteRelIndex_conjugate N g
  exact Quotient.liftOn' x (fun a : SL2R =>
    ∑ c : R ⧸ K.subgroupOf R, f (RHTower.deningerFiberMap (H := K) a c)) (by
      intro a b hab
      have hmem : a⁻¹ * b ∈ R := QuotientGroup.leftRel_apply.1 hab
      set b₀ : R := ⟨a⁻¹ * b, hmem⟩ with hb₀
      have hb : b = a * (b₀ : SL2R) := by rw [hb₀]; group
      rw [hb]
      exact (Fintype.sum_equiv (RHTower.deningerFiberShift (H := K) b₀) _ _
        (fun c => by rw [RHTower.deningerFiberMap_shift])).symm)

/-- Evaluation of the fiber trace at a literal rational quotient representative. -/
theorem rationalHeckeConjugateFiberTrace_mk (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ) (a : SL2R) :
    rationalHeckeConjugateFiberTrace N g f (QuotientGroup.mk a) =
      ∑ c : (rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g),
        f (RHTower.deningerFiberMap (H := rationalHeckeCommonCoverReal N g) a c) := by
  rfl

/-- The finite fiber trace is complex-linear on raw quotient functions. -/
noncomputable def rationalHeckeConjugateFiberTraceLinear (N : ℕ) (g : GL (Fin 2) ℚ) :
    (SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ) →ₗ[ℂ]
      (SL2R ⧸ rationalConjugateSL2Group N g → ℂ) where
  toFun := rationalHeckeConjugateFiberTrace N g
  map_add' := by
    intro f h
    funext x
    induction x using Quotient.inductionOn with
    | h a =>
      change rationalHeckeConjugateFiberTrace N g (f + h) (QuotientGroup.mk a) =
        rationalHeckeConjugateFiberTrace N g f (QuotientGroup.mk a) +
          rationalHeckeConjugateFiberTrace N g h (QuotientGroup.mk a)
      rw [rationalHeckeConjugateFiberTrace_mk N g (f + h) a,
        rationalHeckeConjugateFiberTrace_mk N g f a,
        rationalHeckeConjugateFiberTrace_mk N g h a]
      simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    funext x
    induction x using Quotient.inductionOn with
    | h a =>
      change rationalHeckeConjugateFiberTrace N g (c • f) (QuotientGroup.mk a) =
        c • rationalHeckeConjugateFiberTrace N g f (QuotientGroup.mk a)
      rw [rationalHeckeConjugateFiberTrace_mk N g (c • f) a,
        rationalHeckeConjugateFiberTrace_mk N g f a]
      simp only [Pi.smul_apply]
      exact Finset.smul_sum.symm

@[simp] theorem rationalHeckeConjugateFiberTraceLinear_apply (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ) :
    rationalHeckeConjugateFiberTraceLinear N g f = rationalHeckeConjugateFiberTrace N g f :=
  rfl

/-- Left regular translation on raw functions over a subgroup quotient. -/
def subgroupQuotientLeftTranslate (H : Subgroup SL2R) (a : SL2R)
    (f : SL2R ⧸ H → ℂ) : SL2R ⧸ H → ℂ :=
  fun x => f (a⁻¹ • x)

/-- The fiber trace is an actual left-regular model intertwiner on raw quotient functions. -/
theorem rationalHeckeConjugateFiberTrace_intertwines_leftTranslate
    (N : ℕ) (g : GL (Fin 2) ℚ) (a : SL2R)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ) :
    rationalHeckeConjugateFiberTrace N g
      (subgroupQuotientLeftTranslate (rationalHeckeCommonCoverReal N g) a f) =
      subgroupQuotientLeftTranslate (rationalConjugateSL2Group N g) a
        (rationalHeckeConjugateFiberTrace N g f) := by
  funext x
  induction x using Quotient.inductionOn with
  | h b =>
    change rationalHeckeConjugateFiberTrace N g
      (subgroupQuotientLeftTranslate (rationalHeckeCommonCoverReal N g) a f)
        (QuotientGroup.mk b) =
      rationalHeckeConjugateFiberTrace N g f (a⁻¹ • (QuotientGroup.mk b))
    change rationalHeckeConjugateFiberTrace N g
      (subgroupQuotientLeftTranslate (rationalHeckeCommonCoverReal N g) a f)
        (QuotientGroup.mk b) =
      rationalHeckeConjugateFiberTrace N g f (QuotientGroup.mk (a⁻¹ * b))
    rw [rationalHeckeConjugateFiberTrace_mk N g
      (subgroupQuotientLeftTranslate (rationalHeckeCommonCoverReal N g) a f) b,
      rationalHeckeConjugateFiberTrace_mk N g f (a⁻¹ * b)]
    apply Finset.sum_congr rfl
    intro c hc
    exact congrArg f (RHTower.deningerFiberMap_smul (H := rationalHeckeCommonCoverReal N g)
      b a⁻¹ c).symm

/-- A finite fiber coordinate has the literal continuous representative
`a ↦ [a * c.out]` on `SL₂(ℝ)`. -/
theorem rationalHeckeConjugateFiberCoordinate_eq_mk_out (N : ℕ) (g : GL (Fin 2) ℚ)
    (a : SL2R)
    (c : (rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) :
    RHTower.deningerFiberMap (H := rationalHeckeCommonCoverReal N g) a c =
      (QuotientGroup.mk (a * (c.out : SL2R)) : SL2R ⧸ rationalHeckeCommonCoverReal N g) := by
  calc
    RHTower.deningerFiberMap (H := rationalHeckeCommonCoverReal N g) a c =
        RHTower.deningerFiberMap (H := rationalHeckeCommonCoverReal N g) a
          (QuotientGroup.mk c.out) := congrArg _ c.out_eq'.symm
    _ = (QuotientGroup.mk (a * (c.out : SL2R)) :
        SL2R ⧸ rationalHeckeCommonCoverReal N g) := RHTower.deningerFiberMap_mk a c.out

/-- Each coordinate in the finite non-normal fiber is continuous. -/
theorem rationalHeckeConjugateFiberCoordinate_continuous (N : ℕ) (g : GL (Fin 2) ℚ)
    (c : (rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) :
    Continuous (fun a : SL2R =>
      RHTower.deningerFiberMap (H := rationalHeckeCommonCoverReal N g) a c) := by
  rw [show (fun a : SL2R => RHTower.deningerFiberMap
      (H := rationalHeckeCommonCoverReal N g) a c) =
      fun a => (QuotientGroup.mk (a * (c.out : SL2R)) :
        SL2R ⧸ rationalHeckeCommonCoverReal N g) from by
          funext a
          exact rationalHeckeConjugateFiberCoordinate_eq_mk_out N g a c]
  exact QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)

/-- The finite fiber trace descends to a continuous function on the rational quotient. -/
theorem rationalHeckeConjugateFiberTrace_continuous (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ) (hf : Continuous f) :
    Continuous (rationalHeckeConjugateFiberTrace N g f) := by
  rw [(QuotientGroup.isQuotientMap_mk (rationalConjugateSL2Group N g)).continuous_iff]
  change Continuous (fun a : SL2R =>
    ∑ c : (rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g),
      f (RHTower.deningerFiberMap (H := rationalHeckeCommonCoverReal N g) a c))
  apply continuous_finsetSum
  intro c hc
  exact hf.comp (rationalHeckeConjugateFiberCoordinate_continuous N g c)

/-- The restriction of a Maass source to the common cover is continuous. -/
theorem rationalHeckeIntegralCoverSourceFunction_continuous (N : ℕ) {lam : ℝ}
    (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    Continuous (rationalHeckeIntegralCoverSourceFunction N g f) :=
  maassInvariantQuotientLift_continuous (rationalHeckeIntegralCoverMaassRestrict N g f)

/-- The raw finite trace of the common-cover Maass source is continuous. -/
theorem rationalHeckeConjugateFiberTrace_source_continuous (N : ℕ) {lam : ℝ}
    (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    Continuous (rationalHeckeConjugateFiberTrace N g
      (rationalHeckeIntegralCoverSourceFunction N g f)) :=
  rationalHeckeConjugateFiberTrace_continuous N g _
    (rationalHeckeIntegralCoverSourceFunction_continuous N g f)

/-- Finite covolume passes from the integral common cover to its rational-conjugate
finite quotient. -/
theorem rationalConjugateSL2QuotientMeasure_finite (N : ℕ) (g : GL (Fin 2) ℚ) :
    IsFiniteMeasure (rationalConjugateSL2QuotientMeasure N g) := by
  letI : (rationalHeckeIntegralIntersection N g).FiniteIndex :=
    rationalHeckeIntegralIntersection_finiteIndex N g
  let μK : Measure (SL2R ⧸ rationalHeckeCommonCoverReal N g) :=
    integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)
  let μR : Measure (SL2R ⧸ rationalConjugateSL2Group N g) :=
    rationalConjugateSL2QuotientMeasure N g
  let p := rationalHeckeConjugateCoverProjection N g
  let D := (rationalConjugateSL2Group N g) ⧸
    (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)
  haveI : Nonempty D := ⟨QuotientGroup.mk 1⟩
  have hD : (Nat.card D : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := D)).ne'
  have hp : Measurable p := subgroupQuotientProjection_measurable _ _
    (realImage_rationalHeckeIntegralIntersection_le_conjugate N g)
  have hmap : Measure.map p μK = Nat.card D • μR :=
    map_rationalHeckeConjugateCoverProjection_integralSubgroupQuotientMeasure N g
  constructor
  have hfin : (Measure.map p μK) Set.univ < ⊤ := by
    rw [Measure.map_apply hp MeasurableSet.univ]
    change μK Set.univ < ⊤
    dsimp only [μK]
    exact measure_lt_top _ Set.univ
  rw [hmap, Measure.smul_apply, nsmul_eq_mul] at hfin
  exact ENNReal.lt_top_of_mul_ne_top_right hfin.ne hD

/-- The common-cover Maass source retains its global cusp bound. -/
theorem rationalHeckeIntegralCoverSourceFunction_norm_le (N : ℕ) {lam : ℝ}
    (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ∃ C : ℝ, ∀ x, ‖rationalHeckeIntegralCoverSourceFunction N g f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := MaassCongruenceL2.source_bounded N f
  refine ⟨C, ?_⟩
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  change ‖f.1.1 (a⁻¹ • UpperHalfPlane.I)‖ ≤ C
  exact hC _

/-- The finite fiber trace has the explicit cardinality-times-source bound. -/
theorem rationalHeckeConjugateFiberTrace_source_norm_le (N : ℕ) {lam : ℝ}
    (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ∃ C : ℝ, ∀ x, ‖rationalHeckeConjugateFiberTrace N g
      (rationalHeckeIntegralCoverSourceFunction N g f) x‖ ≤
      Fintype.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) * C := by
  obtain ⟨C, hC⟩ := rationalHeckeIntegralCoverSourceFunction_norm_le N g f
  refine ⟨C, ?_⟩
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [rationalHeckeConjugateFiberTrace_mk]
  calc
    ‖∑ c : (rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g),
        rationalHeckeIntegralCoverSourceFunction N g f
          (RHTower.deningerFiberMap (H := rationalHeckeCommonCoverReal N g) a c)‖ ≤
        ∑ c : (rationalConjugateSL2Group N g) ⧸
          (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g),
          ‖rationalHeckeIntegralCoverSourceFunction N g f
            (RHTower.deningerFiberMap (H := rationalHeckeCommonCoverReal N g) a c)‖ :=
      norm_sum_le Finset.univ (fun c =>
        rationalHeckeIntegralCoverSourceFunction N g f
          (RHTower.deningerFiberMap (H := rationalHeckeCommonCoverReal N g) a c))
    _ ≤ ∑ _c : (rationalConjugateSL2Group N g) ⧸
          (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g), C := by
      apply Finset.sum_le_sum
      intro c hc
      exact hC _
    _ = Fintype.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl

/-- The raw rational finite trace of every actual principal Maass source is an `L²` vector. -/
theorem rationalHeckeConjugateFiberTrace_source_memLp (N : ℕ) {lam : ℝ}
    (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    MemLp (rationalHeckeConjugateFiberTrace N g
      (rationalHeckeIntegralCoverSourceFunction N g f)) 2
      (rationalConjugateSL2QuotientMeasure N g) := by
  letI : IsFiniteMeasure (rationalConjugateSL2QuotientMeasure N g) :=
    rationalConjugateSL2QuotientMeasure_finite N g
  obtain ⟨C, hC⟩ := rationalHeckeConjugateFiberTrace_source_norm_le N g f
  apply MemLp.of_bound (rationalHeckeConjugateFiberTrace_source_continuous N g f).aestronglyMeasurable
    (Fintype.card ((rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) * C)
  exact ae_of_all _ hC

end

end GaloisForLFunctions.RHTower
