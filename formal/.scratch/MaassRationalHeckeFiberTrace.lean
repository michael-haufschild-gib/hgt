import GaloisForLFunctions.RHTower.MaassRationalHeckeConjugateCoverL2
import GaloisForLFunctions.RHTower.DeningerCosetTransfer

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

end

end GaloisForLFunctions.RHTower
