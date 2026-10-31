import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLoopRotation
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticEisensteinCosets
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentAdelicQuotient

/-!
# The independently defined rotated arithmetic Eisenstein series

The actual idele rotation preserves the Borel character. Thus the rotated
arithmetic summand descends to arithmetic Borel cosets. Reindexing gives
arithmetic invariance and then descent to the literal unipotent quotient.
The constant term is defined using its invariant probability. Convergence
and the evaluation of this integral are separate analytic assertions.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory
noncomputable section

/-- The actual arithmetic embedding followed by idele degree rotation. -/
def rotatedArithmeticLoopEmbedding (q : Ideles) : restrictedRationalLoop →* AdelicLoop :=
  (adelicDegreeRotation q).toMonoidHom.comp arithmeticLoopEmbedding

/-- The rotated Iwasawa summand respects the actual arithmetic Borel relation. -/
theorem rotatedIwasawaSection_arithmetic_coset (q : Ideles) (s t : ℂ) (g : AdelicLoop)
    (a b : restrictedRationalLoop) (hab : a⁻¹ * b ∈ arithmeticPositiveBorel) :
    adelicIwasawaSection s t (g * rotatedArithmeticLoopEmbedding q a) =
      adelicIwasawaSection s t (g * rotatedArithmeticLoopEmbedding q b) := by
  let d : adelicPositiveBorel := ⟨arithmeticLoopEmbedding (a⁻¹ * b), hab⟩
  let e := adelicBorelRotation q d
  have hd : adelicBorelCharacter s t e = 1 :=
    (adelicBorelCharacter_rotation q s t d).trans
      (adelicBorelCharacter_arithmetic s t d ⟨a⁻¹ * b, rfl⟩)
  have hr : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b
  have he : rotatedArithmeticLoopEmbedding q a * (e : AdelicLoop) =
      rotatedArithmeticLoopEmbedding q b :=
    ((rotatedArithmeticLoopEmbedding q).map_mul a (a⁻¹ * b)).symm.trans
      (congrArg (rotatedArithmeticLoopEmbedding q) hr)
  symm
  calc
    adelicIwasawaSection s t (g * rotatedArithmeticLoopEmbedding q b) =
        adelicIwasawaSection s t (g * (rotatedArithmeticLoopEmbedding q a * (e : AdelicLoop))) :=
      congrArg (fun z : AdelicLoop => adelicIwasawaSection s t (g * z)) he.symm
    _ = adelicIwasawaSection s t ((g * rotatedArithmeticLoopEmbedding q a) * (e : AdelicLoop)) :=
      congrArg (adelicIwasawaSection s t)
        (mul_assoc g (rotatedArithmeticLoopEmbedding q a) (e : AdelicLoop)).symm
    _ = adelicIwasawaSection s t (g * rotatedArithmeticLoopEmbedding q a) *
        adelicBorelCharacter s t e :=
      adelicIwasawaSection_right_borel s t (g * rotatedArithmeticLoopEmbedding q a) e
    _ = adelicIwasawaSection s t (g * rotatedArithmeticLoopEmbedding q a) := by rw [hd, mul_one]

/-- A spectral summand on the actual arithmetic cosets, with independent degree rotation. -/
def ellipticRotatedEisensteinSummand (q : Ideles) (s t : ℂ) (g : AdelicLoop) :
    ArithmeticBorelCosets → ℂ :=
  Quotient.lift (fun r => adelicIwasawaSection s t (g * rotatedArithmeticLoopEmbedding q r))
    (fun a b h => rotatedIwasawaSection_arithmetic_coset q s t g a b
      (QuotientGroup.leftRel_apply.mp h))

/-- The actual rotated arithmetic coset series, independently of any constant-term formula. -/
def ellipticRotatedEisensteinSeries (q : Ideles) (s t : ℂ) (g : AdelicLoop) : ℂ :=
  ∑' c : ArithmeticBorelCosets, ellipticRotatedEisensteinSummand q s t g c

theorem ellipticRotatedEisensteinSummand_right_arithmetic (q : Ideles) (s t : ℂ)
    (g : AdelicLoop) (r : restrictedRationalLoop) (c : ArithmeticBorelCosets) :
    ellipticRotatedEisensteinSummand q s t (g * rotatedArithmeticLoopEmbedding q r) c =
      ellipticRotatedEisensteinSummand q s t g
        ((MulAction.toPerm r : Equiv.Perm ArithmeticBorelCosets) c) := by
  induction c using Quotient.inductionOn with
  | h a =>
    change adelicIwasawaSection s t
      ((g * rotatedArithmeticLoopEmbedding q r) * rotatedArithmeticLoopEmbedding q a) =
        adelicIwasawaSection s t (g * rotatedArithmeticLoopEmbedding q (r * a))
    apply congrArg (adelicIwasawaSection s t)
    exact (mul_assoc g (rotatedArithmeticLoopEmbedding q r) (rotatedArithmeticLoopEmbedding q a)).trans
      (congrArg (fun z : AdelicLoop => g * z) ((rotatedArithmeticLoopEmbedding q).map_mul r a).symm)

/-- Right multiplication by a rotated arithmetic element reindexes the series. -/
theorem ellipticRotatedEisensteinSeries_right_arithmetic (q : Ideles) (s t : ℂ)
    (g : AdelicLoop) (r : restrictedRationalLoop) :
    ellipticRotatedEisensteinSeries q s t (g * rotatedArithmeticLoopEmbedding q r) =
      ellipticRotatedEisensteinSeries q s t g := by
  unfold ellipticRotatedEisensteinSeries
  calc
    _ = ∑' c : ArithmeticBorelCosets, ellipticRotatedEisensteinSummand q s t g
        ((MulAction.toPerm r : Equiv.Perm ArithmeticBorelCosets) c) :=
      tsum_congr (ellipticRotatedEisensteinSummand_right_arithmetic q s t g r)
    _ = _ := (MulAction.toPerm r : Equiv.Perm ArithmeticBorelCosets).tsum_eq
      (ellipticRotatedEisensteinSummand q s t g)

private theorem mul_of_inv_mul_eq {G : Type*} [Group G] (u v r : G) (hr : r = u⁻¹ * v) :
    u * r = v := by
  rw [hr, mul_inv_cancel_left]

/-- The actual rotated series is constant on right unipotent arithmetic cosets. -/
theorem ellipticRotatedEisensteinSeries_unipotent_coset (q : Ideles) (s t : ℂ)
    (g : AdelicLoop) (u v : AdelicUnipotentModel) (huv : u⁻¹ * v ∈ adelicUnipotentArithmetic) :
    ellipticRotatedEisensteinSeries q s t (g * adelicDegreeRotation q u.1) =
      ellipticRotatedEisensteinSeries q s t (g * adelicDegreeRotation q v.1) := by
  obtain ⟨r, hr⟩ := huv
  change arithmeticLoopEmbedding r = u.1⁻¹ * v.1 at hr
  have hur : u.1 * arithmeticLoopEmbedding r = v.1 :=
    mul_of_inv_mul_eq u.1 v.1 (arithmeticLoopEmbedding r) hr
  have he : (g * adelicDegreeRotation q u.1) * rotatedArithmeticLoopEmbedding q r =
      g * adelicDegreeRotation q v.1 := by
    exact (mul_assoc g (adelicDegreeRotation q u.1) (rotatedArithmeticLoopEmbedding q r)).trans
      (congrArg (fun z : AdelicLoop => g * z)
        (((adelicDegreeRotation q).map_mul u.1 (arithmeticLoopEmbedding r)).symm.trans
          (congrArg (adelicDegreeRotation q) hur)))
  calc
    _ = ellipticRotatedEisensteinSeries q s t
        ((g * adelicDegreeRotation q u.1) * rotatedArithmeticLoopEmbedding q r) :=
      (ellipticRotatedEisensteinSeries_right_arithmetic q s t
        (g * adelicDegreeRotation q u.1) r).symm
    _ = _ := congrArg (ellipticRotatedEisensteinSeries q s t) he

/-- The independently constructed Eisenstein function on the literal unipotent quotient. -/
def ellipticEisensteinOnUnipotentQuotient (q : Ideles) (s t : ℂ) (g : AdelicLoop) :
    AdelicUnipotentQuotient → ℂ :=
  Quotient.lift (fun u => ellipticRotatedEisensteinSeries q s t (g * adelicDegreeRotation q u.1))
    (fun u v h => ellipticRotatedEisensteinSeries_unipotent_coset q s t g u v
      (QuotientGroup.leftRel_apply.mp h))

/-- The arithmetic constant-term integral; integrability and unfolding require separate proofs. -/
def ellipticEisensteinConstantTerm (q : Ideles) (s t : ℂ) (g : AdelicLoop) : ℂ :=
  ∫ u : AdelicUnipotentQuotient, ellipticEisensteinOnUnipotentQuotient q s t g u
    ∂adelicUnipotentQuotientProbability

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.rotatedIwasawaSection_arithmetic_coset
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticRotatedEisensteinSeries_right_arithmetic
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticEisensteinOnUnipotentQuotient
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticEisensteinConstantTerm
