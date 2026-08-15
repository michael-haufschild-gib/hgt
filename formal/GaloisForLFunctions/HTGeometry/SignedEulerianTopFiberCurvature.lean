import Mathlib

/-!
# Four-label curvature of signed-Eulerian top fibers

The stable multivariate type-B Eulerian polynomial records descent tops, ascent tops, and the
number of negative letters.  It does not record which lower label is paired with a given descent
top.  The positive signed words `3142` and `3241` are the first collision needed by the SP-E route:
they have the same top signature but exchange the two descent bottoms.

Any adjacent-descent weight factoring through the top signature must therefore satisfy a vanishing
`2 x 2` multiplicative minor.  If every ordered four-label minor vanishes and the edge weights are
positive, the lower-triangular edge kernel has rank one.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Type-B descent tops of a signed word, including the boundary letter `0`. -/
def typeBDescentTopsAux (previous : ℤ) : List ℤ → List ℕ
  | [] => []
  | current :: rest =>
      (if previous > current then [max previous.natAbs current.natAbs] else []) ++
        typeBDescentTopsAux current rest

/-- Type-B ascent tops of a signed word, including the boundary letter `0`. -/
def typeBAscentTopsAux (previous : ℤ) : List ℤ → List ℕ
  | [] => []
  | current :: rest =>
      (if previous < current then [max previous.natAbs current.natAbs] else []) ++
        typeBAscentTopsAux current rest

/-- The set of type-B descent-top labels. -/
def typeBDescentTops (word : List ℤ) : Finset ℕ :=
  (typeBDescentTopsAux 0 word).toFinset

/-- The set of type-B ascent-top labels. -/
def typeBAscentTops (word : List ℤ) : Finset ℕ :=
  (typeBAscentTopsAux 0 word).toFinset

/-- Number of negative letters in a signed word. -/
def signedWordNegativeCount : List ℤ → ℕ
  | [] => 0
  | current :: rest =>
      (if current < 0 then 1 else 0) + signedWordNegativeCount rest

/-- The complete statistic used by the Visontai--Williams type-B stable monomial. -/
structure TypeBTopSignature where
  descent : Finset ℕ
  ascent : Finset ℕ
  negatives : ℕ
deriving DecidableEq

/-- Top signature of a signed word. -/
def typeBTopSignature (word : List ℤ) : TypeBTopSignature where
  descent := typeBDescentTops word
  ascent := typeBAscentTops word
  negatives := signedWordNegativeCount word

/-- First word in the four-label top-fiber collision. -/
def signedWord3142 : List ℤ := [3, 1, 4, 2]

/-- Second word in the four-label top-fiber collision. -/
def signedWord3241 : List ℤ := [3, 2, 4, 1]

/-- **Four-label top-fiber collision.**  The words `3142` and `3241` have identical type-B
descent tops, ascent tops, and negative-letter count. -/
theorem typeBTopSignature_signedWord3142_eq_signedWord3241 :
    typeBTopSignature signedWord3142 = typeBTopSignature signedWord3241 := by
  rfl

/-- A scalar monomial specialization of one type-B top signature. -/
def typeBTopSignatureWeight {R : Type*} [CommMonoid R]
    (x y : ℕ → R) (q : R) (signature : TypeBTopSignature) : R :=
  q ^ signature.negatives * signature.descent.prod x * signature.ascent.prod y

/-- Visontai--Williams top-monomial weight of a signed word. -/
def typeBTopWeight {R : Type*} [CommMonoid R]
    (x y : ℕ → R) (q : R) (word : List ℤ) : R :=
  typeBTopSignatureWeight x y q (typeBTopSignature word)

/-- Every scalar top-monomial specialization identifies the four-label collision. -/
theorem typeBTopWeight_signedWord3142_eq_signedWord3241
    {R : Type*} [CommMonoid R] (x y : ℕ → R) (q : R) :
    typeBTopWeight x y q signedWord3142 = typeBTopWeight x y q signedWord3241 := by
  rw [typeBTopWeight, typeBTopWeight,
    typeBTopSignature_signedWord3142_eq_signedWord3241]

/-- Product of local factors over the descending adjacent edges of a signed word. -/
def signedWordDescentEdgeWeightAux {R : Type*} [CommMonoid R]
    (κ : ℕ → ℕ → R) (previous : ℤ) : List ℤ → R
  | [] => 1
  | current :: rest =>
      (if previous > current then κ previous.natAbs current.natAbs else 1) *
        signedWordDescentEdgeWeightAux κ current rest

/-- Product of local factors over descending edges, including the type-B boundary comparison. -/
def signedWordDescentEdgeWeight {R : Type*} [CommMonoid R]
    (κ : ℕ → ℕ → R) (word : List ℤ) : R :=
  signedWordDescentEdgeWeightAux κ 0 word

/-- A word weight factors through the type-B top signature when it is constant on every signature
fiber. -/
def FactorsThroughTypeBTopSignature {R : Type*} (weight : List ℤ → R) : Prop :=
  ∀ word₁ word₂, typeBTopSignature word₁ = typeBTopSignature word₂ →
    weight word₁ = weight word₂

/-- **Four-label curvature obstruction.**  If an adjacent-descent product factors through the
known stable top signature, its first nontrivial multiplicative minor vanishes. -/
theorem crossRelation_of_descentEdgeWeight_factorsThrough
    {R : Type*} [CommMonoid R] (κ : ℕ → ℕ → R)
    (hκ : FactorsThroughTypeBTopSignature (signedWordDescentEdgeWeight κ)) :
    κ 3 1 * κ 4 2 = κ 3 2 * κ 4 1 := by
  have h := hκ signedWord3142 signedWord3241
    typeBTopSignature_signedWord3142_eq_signedWord3241
  simpa [signedWordDescentEdgeWeight, signedWordDescentEdgeWeightAux,
    signedWord3142, signedWord3241] using h

/-- **Rank-one classification.**  A positive lower-triangular edge kernel whose ordered
four-label multiplicative minors all vanish separates into a top factor and a bottom factor. -/
theorem exists_rankOne_of_ordered_crossRelations (κ : ℕ → ℕ → ℝ)
    (hpos : ∀ a c, 1 ≤ a → a < c → 0 < κ c a)
    (hcross : ∀ a b c d, 1 ≤ a → a < b → b < c → c < d →
      κ c a * κ d b = κ c b * κ d a) :
    ∃ α β : ℕ → ℝ, ∀ a c, 1 ≤ a → a < c →
      0 < α c ∧ 0 < β a ∧ κ c a = α c * β a := by
  let α : ℕ → ℝ := fun c => κ c 1
  let β : ℕ → ℝ := fun a =>
    if a = 1 then 1 else κ (a + 1) a / κ (a + 1) 1
  refine ⟨α, β, ?_⟩
  intro a c ha hac
  have h1c : 1 < c := lt_of_le_of_lt ha hac
  have hα : 0 < α c := hpos 1 c (by omega) h1c
  by_cases ha1 : a = 1
  · subst a
    simp [α, β, hα]
  · have h1a : 1 < a := lt_of_le_of_ne ha (Ne.symm ha1)
    have hdenpos : 0 < κ (a + 1) 1 :=
      hpos 1 (a + 1) (by omega) (by omega)
    have hnumpos : 0 < κ (a + 1) a :=
      hpos a (a + 1) ha (by omega)
    have hβ : 0 < β a := by
      simp only [β, if_neg ha1]
      exact div_pos hnumpos hdenpos
    refine ⟨hα, hβ, ?_⟩
    simp only [α, β, if_neg ha1]
    rcases lt_or_eq_of_le (Nat.succ_le_iff.mpr hac) with hsucc | hsucc
    · have hrect := hcross 1 a (a + 1) c (by omega) h1a (by omega) hsucc
      field_simp [ne_of_gt hdenpos]
      nlinarith
    · subst c
      field_simp [ne_of_gt hdenpos]

end GaloisForLFunctions.HTGeometry
