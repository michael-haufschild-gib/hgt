import GaloisForLFunctions.HTGeometry.GammaDatumLexValuation

/-!
# The algebraic-logarithmic valuation of the digamma field

On `L = ℂ(s)⟨ψ⟩` the `Γ`-exponent of the boundary datum is always zero, so what is left of eq. (3) is
the pair `(a, b)` of §3: the argument exponent and the logarithm exponent of the residue
`c·s^a·(log s)^b`.

That pair is a rank-two valuation of `L`, for the order of eq. (26) restricted to the
`Γ`-exponent-zero locus.
-/

open Filter Set Topology Function
open scoped Differential
open scoped Classical

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance digammaLexDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance digammaLexIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance digammaLexDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance digammaLexComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance digammaLexRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance digammaLexRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance digammaLexRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- The digamma field `L = ℂ(s)⟨ψ⟩`, as an intermediate field. -/
def digammaFieldL : IntermediateField (RatFunc ℂ) upperEndMeroField :=
  differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField)

/-- An element of the digamma field is nonzero in the ambient field. -/
theorem coe_digammaFieldL_ne_zero {x : digammaFieldL} (hx : x ≠ 0) :
    ((x : upperEndMeroField)) ≠ 0 := by
  intro h0
  refine hx (Subtype.ext ?_)
  simp only [ZeroMemClass.coe_zero]
  exact h0

/-- Every nonzero element of the digamma field has a datum with `Γ`-exponent zero. -/
theorem exists_digammaPair (x : digammaFieldL) (hx : x ≠ 0) :
    ∃ d : ℤ × ℤ, ∃ c : ℂ,
      HasGammaTubeDatum 1 ((x : upperEndMeroField)) 0 d.1 d.2 c := by
  obtain ⟨a, b, c, hdat⟩ :=
    exists_hasGammaTubeDatum_digammaField one_pos x.2 (coe_digammaFieldL_ne_zero hx)
  exact ⟨(a, b), c, hdat⟩

/-- The algebraic-logarithmic pair of an element of the digamma field. -/
def digammaDatumPair (x : digammaFieldL) : ℤ × ℤ :=
  if h : x = 0 then 0 else Classical.choose (exists_digammaPair x h)

/-- The pair is read off any datum. -/
theorem digammaDatumPair_eq_of {x : digammaFieldL} (hx : x ≠ 0) {a b : ℤ} {c : ℂ}
    (h : HasGammaTubeDatum 1 ((x : upperEndMeroField)) 0 a b c) :
    digammaDatumPair x = (a, b) := by
  rw [digammaDatumPair, dif_neg hx]
  obtain ⟨c', hc'⟩ := Classical.choose_spec (exists_digammaPair x hx)
  obtain ⟨-, h2, h3, -⟩ := hasGammaTubeDatum_unique one_pos hc' h
  exact Prod.ext h2 h3

/-- The value of an algebraic-logarithmic pair in the lexicographic group. -/
def lexPairValue (a b : ℤ) : ℤ ×ₗ ℤ := toLex (a, b)

theorem lexPairValue_add (a b a' b' : ℤ) :
    lexPairValue (a + a') (b + b') = lexPairValue a b + lexPairValue a' b' := rfl

/-- Dominance at `Γ`-exponent zero is exactly the order of the lexicographic pair. -/
theorem lexPairValue_lt_iff {a b a' b' : ℤ} :
    lexPairValue a' b' < lexPairValue a b ↔ ShapeDominates 0 a b 0 a' b' := by
  rw [lexPairValue, lexPairValue, Prod.Lex.lt_iff]
  simp only [ofLex_toLex]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨rfl, h⟩)
    · exact Or.inr (Or.inr ⟨rfl, h1, h2⟩)
  · rintro (h | ⟨-, h⟩ | ⟨-, h1, h2⟩)
    · exact absurd h (lt_irrefl 0)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩

/-- **The algebraic-logarithmic valuation of the digamma field.**  The argument exponent and the
logarithm exponent of the residue add on products, and on a sum the pair never dominates both
summands: eq. (19) as a rank-two valuation. -/
def digammaLexValuation : Valuation digammaFieldL (WithZero (Multiplicative (ℤ ×ₗ ℤ))) where
  toFun x := if x = 0 then (0 : WithZero (Multiplicative (ℤ ×ₗ ℤ)))
    else ((Multiplicative.ofAdd (lexPairValue (digammaDatumPair x).1 (digammaDatumPair x).2) :
      Multiplicative (ℤ ×ₗ ℤ)) : WithZero (Multiplicative (ℤ ×ₗ ℤ)))
  map_zero' := by
    rw [if_pos rfl]
  map_one' := by
    have hone : ((1 : digammaFieldL) : upperEndMeroField) = 1 := by simp
    have hdat : HasGammaTubeDatum 1 (((1 : digammaFieldL)) : upperEndMeroField) 0 0 0 1 := by
      rw [hone]
      exact hasGammaTubeDatum_one
    rw [if_neg (one_ne_zero : (1 : digammaFieldL) ≠ 0), digammaDatumPair_eq_of one_ne_zero hdat]
    rfl
  map_mul' x y := by
    by_cases hx : x = 0
    · rw [hx, zero_mul, if_pos rfl, zero_mul]
    by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos rfl, mul_zero]
    obtain ⟨⟨a, b⟩, c, hdx⟩ := exists_digammaPair x hx
    obtain ⟨⟨a', b'⟩, c', hdy⟩ := exists_digammaPair y hy
    have hcoe : ((x * y : digammaFieldL) : upperEndMeroField)
        = (x : upperEndMeroField) * (y : upperEndMeroField) := by simp
    have hdxy : HasGammaTubeDatum 1 ((x * y : digammaFieldL) : upperEndMeroField)
        0 (a + a') (b + b') (c * c') := by
      rw [hcoe]
      simpa using hdx.mul hdy
    rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, digammaDatumPair_eq_of hx hdx,
      digammaDatumPair_eq_of hy hdy, digammaDatumPair_eq_of (mul_ne_zero hx hy) hdxy,
      ← WithZero.coe_mul]
    refine congrArg _ ?_
    show Multiplicative.ofAdd (lexPairValue (a + a') (b + b'))
      = Multiplicative.ofAdd (lexPairValue a b) * Multiplicative.ofAdd (lexPairValue a' b')
    rw [lexPairValue_add]
    rfl
  map_add_le_max' x y := by
    by_cases hxy : x + y = 0
    · rw [hxy, if_pos rfl]
      exact zero_le
    by_cases hx : x = 0
    · rw [hx, zero_add, if_pos rfl]
      exact le_max_right _ _
    by_cases hy : y = 0
    · rw [hy, add_zero, if_pos rfl]
      exact le_max_left _ _
    obtain ⟨⟨a, b⟩, c, hdx⟩ := exists_digammaPair x hx
    obtain ⟨⟨a', b'⟩, c', hdy⟩ := exists_digammaPair y hy
    obtain ⟨⟨A, B⟩, C, hdxy⟩ := exists_digammaPair (x + y) hxy
    have hcoe : ((x + y : digammaFieldL) : upperEndMeroField)
        = (x : upperEndMeroField) + (y : upperEndMeroField) := by simp
    have hdxy' : HasGammaTubeDatum 1
        ((x : upperEndMeroField) + (y : upperEndMeroField)) 0 A B C := by
      rw [← hcoe]
      exact hdxy
    have hnot := not_hasGammaTubeDatum_add_dominates one_pos hdx hdy hdxy'
    rw [if_neg hxy, if_neg hx, if_neg hy, digammaDatumPair_eq_of hx hdx,
      digammaDatumPair_eq_of hy hdy, digammaDatumPair_eq_of hxy hdxy]
    refine not_lt.mp fun hlt => ?_
    rw [max_lt_iff] at hlt
    obtain ⟨h1, h2⟩ := hlt
    rw [WithZero.coe_lt_coe] at h1 h2
    exact hnot ⟨lexPairValue_lt_iff.mp h1, lexPairValue_lt_iff.mp h2⟩

theorem digammaLexValuation_apply_of_ne_zero {x : digammaFieldL} (hx : x ≠ 0) :
    digammaLexValuation x
      = ((Multiplicative.ofAdd
        (lexPairValue (digammaDatumPair x).1 (digammaDatumPair x).2) :
          Multiplicative (ℤ ×ₗ ℤ)) : WithZero (Multiplicative (ℤ ×ₗ ℤ))) := by
  show (if x = 0 then (0 : WithZero (Multiplicative (ℤ ×ₗ ℤ))) else _) = _
  rw [if_neg hx]

end

end GaloisForLFunctions.HTGeometry
