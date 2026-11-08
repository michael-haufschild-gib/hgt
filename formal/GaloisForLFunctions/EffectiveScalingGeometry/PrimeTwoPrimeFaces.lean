import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedSquarefreeIndices

/-!
# Core labels and four arithmetic birth heights

Every finite prime face has a unique core omitting two and three, together
with one of four small-prime tags. The tags contribute degrees `0,1,1,2`
and multiply height by `1,2,3,6`. This partition restricts to an exact
bijection in every exterior degree and product cutoff.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder

private theorem twoPrimeLabels_ne : primeThreeLabel ≠ primeTwoLabel := by
  intro h
  have he := congrArg (fun p : Nat.Primes => p.val) h
  change (3 : ℕ) = 2 at he
  omega

/-- The support shared by one two-prime block. -/
def TwoPrimeCoreFace :=
  {s : Finset Nat.Primes // primeTwoLabel ∉ s ∧ primeThreeLabel ∉ s}

/-- The four possible small-prime parts of a face. -/
inductive TwoPrimeFaceTag
  | base | two | three | both
  deriving DecidableEq

def TwoPrimeFaceTag.degree : TwoPrimeFaceTag → ℕ
  | .base => 0 | .two => 1 | .three => 1 | .both => 2

def TwoPrimeFaceTag.height : TwoPrimeFaceTag → ℕ
  | .base => 1 | .two => 2 | .three => 3 | .both => 6

/-- Recover a full face from its core and small-prime tag. -/
def twoPrimeTaggedFace (c : TwoPrimeCoreFace) : TwoPrimeFaceTag → Finset Nat.Primes
  | .base => c.val
  | .two => insert primeTwoLabel c.val
  | .three => insert primeThreeLabel c.val
  | .both => insert primeTwoLabel (insert primeThreeLabel c.val)

/-- Remove precisely the two small primes from a face. -/
def twoPrimeFaceCore (s : Finset Nat.Primes) : TwoPrimeCoreFace :=
  ⟨(s.erase primeTwoLabel).erase primeThreeLabel,by
    constructor
    · intro h
      exact (Finset.notMem_erase primeTwoLabel s) (Finset.mem_erase.mp h).2
    · exact Finset.notMem_erase _ _⟩

def twoPrimeFaceTag (s : Finset Nat.Primes) : TwoPrimeFaceTag :=
  if primeTwoLabel ∈ s then
    if primeThreeLabel ∈ s then .both else .two
  else if primeThreeLabel ∈ s then .three else .base

/-- Every prime face belongs to exactly one four-generator block. -/
theorem twoPrimeTaggedFace_recover (s : Finset Nat.Primes) :
    twoPrimeTaggedFace (twoPrimeFaceCore s) (twoPrimeFaceTag s) = s := by
  by_cases h2 : primeTwoLabel ∈ s <;> by_cases h3 : primeThreeLabel ∈ s
  all_goals
    simp only [twoPrimeFaceTag,h2,h3,if_true,if_false,twoPrimeTaggedFace,twoPrimeFaceCore]
    ext p
    simp only [Finset.mem_insert,Finset.mem_erase]
    constructor
    · intro h
      aesop
    · intro hp
      by_cases hp2 : p = primeTwoLabel <;> by_cases hp3 : p = primeThreeLabel <;> aesop

/-- Erasing the small-prime tag recovers the original core. -/
theorem twoPrimeFaceCore_tagged (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) :
    twoPrimeFaceCore (twoPrimeTaggedFace c t) = c := by
  apply Subtype.ext
  cases t <;> simp [twoPrimeFaceCore,twoPrimeTaggedFace,c.property.1,c.property.2,
    Ne.symm twoPrimeLabels_ne]

theorem twoPrimeFaceTag_tagged (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) :
    twoPrimeFaceTag (twoPrimeTaggedFace c t) = t := by
  cases t <;> simp [twoPrimeFaceTag,twoPrimeTaggedFace,c.property.1,c.property.2,
    twoPrimeLabels_ne,Ne.symm twoPrimeLabels_ne]

/-- Canonical partition of all finite prime supports into two-prime blocks. -/
def twoPrimeFaceEquiv : Finset Nat.Primes ≃ TwoPrimeCoreFace × TwoPrimeFaceTag where
  toFun s := (twoPrimeFaceCore s,twoPrimeFaceTag s)
  invFun ct := twoPrimeTaggedFace ct.1 ct.2
  left_inv := twoPrimeTaggedFace_recover
  right_inv ct := Prod.ext (twoPrimeFaceCore_tagged ct.1 ct.2) (twoPrimeFaceTag_tagged ct.1 ct.2)

/-- The four tags contribute exterior degrees zero, one, one and two. -/
theorem twoPrimeTaggedFace_card (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) :
    (twoPrimeTaggedFace c t).card = c.val.card + t.degree := by
  cases t <;> simp [twoPrimeTaggedFace,TwoPrimeFaceTag.degree,c.property.1,c.property.2,
    Ne.symm twoPrimeLabels_ne,Nat.add_assoc]

/-- The four tags multiply product height by one, two, three and six. -/
theorem twoPrimeTaggedFace_product (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) :
    (∏ p ∈ twoPrimeTaggedFace c t, p.val) = t.height * ∏ p ∈ c.val, p.val := by
  cases t <;> simp [twoPrimeTaggedFace,TwoPrimeFaceTag.height,c.property.1,c.property.2,
    Ne.symm twoPrimeLabels_ne,primeTwoLabel,primeThreeLabel,← mul_assoc]

#print axioms twoPrimeFaceEquiv
#print axioms twoPrimeTaggedFace_card
#print axioms twoPrimeTaggedFace_product

/-- The core degree and tag degree recover the full exterior degree. -/
theorem twoPrimeFaceCore_card (s : Finset Nat.Primes) :
    (twoPrimeFaceCore s).val.card + (twoPrimeFaceTag s).degree = s.card := by
  rw [← twoPrimeTaggedFace_card,twoPrimeTaggedFace_recover]

/-- The tag's small-prime factor and the core product recover the full height. -/
theorem twoPrimeFaceCore_product (s : Finset Nat.Primes) :
    (twoPrimeFaceTag s).height * (∏ p ∈ (twoPrimeFaceCore s).val, p.val) = ∏ p ∈ s, p.val := by
  rw [← twoPrimeTaggedFace_product,twoPrimeTaggedFace_recover]

/-- Original bounded prime faces in fixed exterior degree. -/
def TwoPrimeBoundedFace (k N : ℕ) :=
  {s : Set.powersetCard Nat.Primes k // primeFaceProduct s ≤ N}

/-- Block labels retain the exact exterior degree and the tag-dependent birth height. -/
def TwoPrimeBlockIndex (k N : ℕ) :=
  {ct : TwoPrimeCoreFace × TwoPrimeFaceTag //
    ct.1.val.card + ct.2.degree = k ∧ ct.2.height * (∏ p ∈ ct.1.val, p.val) ≤ N}

/-- The core/tag partition restricts exactly to every cutoff and degree. -/
def twoPrimeBoundedFaceEquiv (k N : ℕ) : TwoPrimeBoundedFace k N ≃ TwoPrimeBlockIndex k N where
  toFun s := ⟨(twoPrimeFaceCore s.val.val,twoPrimeFaceTag s.val.val),
    (twoPrimeFaceCore_card s.val.val).trans s.val.property,
    (twoPrimeFaceCore_product s.val.val).le.trans s.property⟩
  invFun ct := ⟨⟨twoPrimeTaggedFace ct.val.1 ct.val.2,
    (twoPrimeTaggedFace_card ct.val.1 ct.val.2).trans ct.property.1⟩,
    (twoPrimeTaggedFace_product ct.val.1 ct.val.2).le.trans ct.property.2⟩
  left_inv s := Subtype.ext (Subtype.ext (twoPrimeTaggedFace_recover s.val.val))
  right_inv ct := Subtype.ext
    (Prod.ext (twoPrimeFaceCore_tagged ct.val.1 ct.val.2) (twoPrimeFaceTag_tagged ct.val.1 ct.val.2))

#print axioms twoPrimeBoundedFaceEquiv

end GaloisForLFunctions.EffectiveScalingGeometry
