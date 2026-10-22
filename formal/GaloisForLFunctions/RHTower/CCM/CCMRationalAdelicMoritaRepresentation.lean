import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicMoritaMonomial

/-!
# Exact fixed-base CCM Morita representation of the full crossed product

The monomial representation is linear in its Bruhat--Schwartz coefficient.  Taking its
finite `Finsupp` sum therefore gives a linear representation of the actual nonunital algebraic
crossed product on `ℓ²(ℚˣ)`.  Twisted convolution is proved to map to operator composition on
the full source, not only on monomials.  Every represented element is trace class because its
crossed-product support is finite and every coefficient orbit is `ℓ¹`.
-/

noncomputable section

open ContinuousLinearMap

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev MoritaOperator :=
  CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert

@[simp]
theorem ccmRationalAdelicMoritaMonomial_zero
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : Scale) :
    ccmRationalAdelicMoritaMonomial 0 hbInf b k = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  ext q
  change ccmRationalAdelicBruhatTensorOrbit 0 bInf b (q : ℚ) *
      f (k.val⁻¹ * q) = 0
  rw [ccmRationalAdelicBruhatTensorOrbit_zero, zero_mul]

@[simp]
theorem ccmRationalAdelicMoritaMonomial_add
    (t u : Core) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : Scale) :
    ccmRationalAdelicMoritaMonomial (t + u) hbInf b k =
      ccmRationalAdelicMoritaMonomial t hbInf b k +
        ccmRationalAdelicMoritaMonomial u hbInf b k := by
  apply ContinuousLinearMap.ext
  intro f
  ext q
  change ccmRationalAdelicBruhatTensorOrbit (t + u) bInf b (q : ℚ) *
      f (k.val⁻¹ * q) =
    ccmRationalAdelicBruhatTensorOrbit t bInf b (q : ℚ) *
        f (k.val⁻¹ * q) +
      ccmRationalAdelicBruhatTensorOrbit u bInf b (q : ℚ) *
        f (k.val⁻¹ * q)
  rw [ccmRationalAdelicBruhatTensorOrbit_add]
  ring

@[simp]
theorem ccmRationalAdelicMoritaMonomial_smul
    (z : ℂ) (t : Core) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : Scale) :
    ccmRationalAdelicMoritaMonomial (z • t) hbInf b k =
      z • ccmRationalAdelicMoritaMonomial t hbInf b k := by
  apply ContinuousLinearMap.ext
  intro f
  ext q
  change ccmRationalAdelicBruhatTensorOrbit (z • t) bInf b (q : ℚ) *
      f (k.val⁻¹ * q) =
    z * (ccmRationalAdelicBruhatTensorOrbit t bInf b (q : ℚ) *
      f (k.val⁻¹ * q))
  rw [ccmRationalAdelicBruhatTensorOrbit_smul]
  ring

/-- Coefficient-linear Morita operator in one crossed-product scaling sector. -/
def ccmRationalAdelicMoritaMonomialLinear
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : Scale) :
    Core →ₗ[ℂ] MoritaOperator where
  toFun t := ccmRationalAdelicMoritaMonomial t hbInf b k
  map_add' := fun t u => ccmRationalAdelicMoritaMonomial_add t u hbInf b k
  map_smul' := fun z t => ccmRationalAdelicMoritaMonomial_smul z t hbInf b k

/-- Full fixed-base CCM representation, obtained by summing its finite scaling support. -/
def ccmRationalAdelicMoritaRepresentation
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    Crossed →ₗ[ℂ] MoritaOperator :=
  (Finsupp.lsum ℂ) fun k =>
    ccmRationalAdelicMoritaMonomialLinear hbInf b k

@[simp]
theorem ccmRationalAdelicMoritaRepresentation_single
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : Scale) (t : Core) :
    ccmRationalAdelicMoritaRepresentation hbInf b (Finsupp.single k t) =
      ccmRationalAdelicMoritaMonomial t hbInf b k := by
  simp [ccmRationalAdelicMoritaRepresentation,
    ccmRationalAdelicMoritaMonomialLinear]

@[simp]
theorem ccmRationalAdelicMoritaRepresentation_zero
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    ccmRationalAdelicMoritaRepresentation hbInf b 0 = 0 :=
  map_zero _

@[simp]
theorem ccmRationalAdelicMoritaRepresentation_add
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (F H : Crossed) :
    ccmRationalAdelicMoritaRepresentation hbInf b (F + H) =
      ccmRationalAdelicMoritaRepresentation hbInf b F +
        ccmRationalAdelicMoritaRepresentation hbInf b H :=
  map_add _ _ _

/-- The full twisted crossed-product multiplication is represented by composition. -/
theorem ccmRationalAdelicMoritaRepresentation_mul
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (F H : Crossed) :
    ccmRationalAdelicMoritaRepresentation hbInf b (F * H) =
      ccmRationalAdelicMoritaRepresentation hbInf b F ∘L
        ccmRationalAdelicMoritaRepresentation hbInf b H := by
  have hpureRight (k : Scale) (t : Core) (H : Crossed) :
      ccmRationalAdelicMoritaRepresentation hbInf b
          (Finsupp.single k t * H) =
        ccmRationalAdelicMoritaMonomial t hbInf b k ∘L
          ccmRationalAdelicMoritaRepresentation hbInf b H := by
    induction H using Finsupp.induction with
    | zero => simp
    | @single_add l u H hlu hu hH =>
        rw [ccmRationalAdelicCrossedProduct_mul_add,
          ccmRationalAdelicMoritaRepresentation_add,
          ccmRationalAdelicMoritaRepresentation_add,
          ccmRationalAdelicMoritaRepresentation_single,
          ContinuousLinearMap.comp_add, hH]
        congr 1
        rw [ccmRationalAdelicCrossedProduct_single_mul_single,
          ccmRationalAdelicMoritaRepresentation_single,
          ccmRationalAdelicMoritaMonomial_mul]
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add k t F hkt ht hF =>
      rw [ccmRationalAdelicCrossedProduct_add_mul,
        ccmRationalAdelicMoritaRepresentation_add,
        ccmRationalAdelicMoritaRepresentation_add,
        ccmRationalAdelicMoritaRepresentation_single,
        ContinuousLinearMap.add_comp, hpureRight, hF]

/-- Trace-class operators form an additive class. -/
theorem ccmRationalIsTraceClass_add
    {S T : MoritaOperator} (hS : S.IsTraceClass) (hT : T.IsTraceClass) :
    (S + T).IsTraceClass := by
  have hS1 := _root_.RHTower.IsTraceClass.memSchattenClass_one hS
  have hT1 := _root_.RHTower.IsTraceClass.memSchattenClass_one hT
  exact (_root_.RHTower.memSchattenClass_one_add
    (hS1.isCompactOperator one_pos) (hT1.isCompactOperator one_pos)
    hS1 hT1).one_isTraceClass

/-- Every element of the full algebraic crossed product has trace-class Morita image. -/
theorem ccmRationalAdelicMoritaRepresentation_isTraceClass
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (F : Crossed) :
    (ccmRationalAdelicMoritaRepresentation hbInf b F).IsTraceClass := by
  induction F using Finsupp.induction with
  | zero =>
      have hzero := ccmRationalAdelicMoritaMonomial_isTraceClass
        (0 : Core) hbInf b (1 : Scale)
      simpa using hzero
  | @single_add k t F hkt ht hF =>
      rw [ccmRationalAdelicMoritaRepresentation_add,
        ccmRationalAdelicMoritaRepresentation_single]
      exact ccmRationalIsTraceClass_add
        (ccmRationalAdelicMoritaMonomial_isTraceClass t hbInf b k) hF

end RHTower
end GaloisForLFunctions
