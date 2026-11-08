import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockEmbeddings

/-! Coordinate extraction from the two-prime normal basis. Exact birth conditions
make scalar and middle realizations split injections into the original cutoff chains. -/

noncomputable section
open scoped Classical
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- A transformed chain has precisely the same prime-product support criterion. -/
theorem primeChainCutoff_iff_twoPrime_repr_support (k N : ℕ) (x : PrimeChainSpace R k) :
    x ∈ primeChainCutoff R k N ↔
      (↑((primeTwoPrimeBasis R k).repr x).support : Set (Set.powersetCard Nat.Primes k)) ⊆
        {s | primeFaceProduct s ≤ N} := by
  rw [primeChainCutoff_eq_span_twoPrimeBasis,Module.Basis.mem_span_image]

/-- Extract a tagged scalar coefficient from the original cutoff chains. -/
def twoPrimeBlockScalarExtraction (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) (N : ℕ) :
    primeChainCutoff R (c.val.card+t.degree) N →ₗ[R]
      twoPrimeBlockScalar R (twoPrimeTaggedBirth c t) N where
  toFun x := ⟨(primeTwoPrimeBasis R _).repr x.val
      ⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩,by
    intro h
    by_contra hn
    have hb := (primeChainCutoff_iff_twoPrime_repr_support R _ N x.val).mp x.property
      (Finsupp.mem_support_iff.mpr hn)
    change (∏ p ∈ twoPrimeTaggedFace c t, p.val) ≤ N at hb
    rw [twoPrimeTaggedFace_product] at hb
    rw [twoPrimeTaggedBirth_eq] at h
    exact (not_le_of_gt h) hb⟩
  map_add' x y := by
    apply Subtype.ext
    exact congrArg (fun f => f ⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩)
      ((primeTwoPrimeBasis R _).repr.map_add x.val y.val)
  map_smul' a x := by
    apply Subtype.ext
    exact congrArg (fun f => f ⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩)
      ((primeTwoPrimeBasis R _).repr.map_smul a x.val)

/-- Scalar realization has its literal basis-coordinate left inverse. -/
theorem twoPrimeBlockScalarExtraction_realization (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag)
    (N : ℕ) (a : twoPrimeBlockScalar R (twoPrimeTaggedBirth c t) N) :
    twoPrimeBlockScalarExtraction R c t N (twoPrimeBlockScalarRealization R c t N a) = a := by
  apply Subtype.ext
  change (primeTwoPrimeBasis R _).repr
    (a.val • primeTwoPrimeBasis R _ ⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩)
      ⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩ = a.val
  rw [map_smul,Module.Basis.repr_self]
  change a.val * Finsupp.single
    (⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩ :
      Set.powersetCard Nat.Primes (c.val.card+t.degree)) (1 : R)
    ⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩ = a.val
  rw [Finsupp.single_eq_same,mul_one]

/-- Extract the two middle tag coordinates, retaining their separate birth conditions. -/
def twoPrimeBlockMiddleExtraction (c : TwoPrimeCoreFace) (N : ℕ) :
    primeChainCutoff R (c.val.card+1) N →ₗ[R] twoPrimeBlockMiddle R (twoPrimeCoreHeight c) N where
  toFun x := ⟨((twoPrimeBlockScalarExtraction R c .two N x).val,
    (twoPrimeBlockScalarExtraction R c .three N x).val),
    ⟨(twoPrimeBlockScalarExtraction R c .two N x).property,
      (twoPrimeBlockScalarExtraction R c .three N x).property⟩⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ((twoPrimeBlockScalarExtraction R c .two N).map_add x y)
    · exact congrArg Subtype.val ((twoPrimeBlockScalarExtraction R c .three N).map_add x y)
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ((twoPrimeBlockScalarExtraction R c .two N).map_smul a x)
    · exact congrArg Subtype.val ((twoPrimeBlockScalarExtraction R c .three N).map_smul a x)

/-- The two middle tagged faces are distinct even over rings with torsion. -/
theorem twoPrimeMiddleFaces_ne (c : TwoPrimeCoreFace) :
    (⟨twoPrimeTaggedFace c .two,twoPrimeTaggedFace_card c .two⟩ :
      Set.powersetCard Nat.Primes (c.val.card+1)) ≠
    ⟨twoPrimeTaggedFace c .three,twoPrimeTaggedFace_card c .three⟩ := by
  intro h
  have ht := congrArg (fun s : Set.powersetCard Nat.Primes (c.val.card+1) => twoPrimeFaceTag s.val) h
  rw [twoPrimeFaceTag_tagged,twoPrimeFaceTag_tagged] at ht
  cases ht

/-- The pair realization has its literal two-coordinate left inverse. -/
theorem twoPrimeBlockMiddleExtraction_realization (c : TwoPrimeCoreFace) (N : ℕ)
    (x : twoPrimeBlockMiddle R (twoPrimeCoreHeight c) N) :
    twoPrimeBlockMiddleExtraction R c N (twoPrimeBlockMiddleRealization R c N x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · change (primeTwoPrimeBasis R (c.val.card+1)).repr
      (x.val.1 • primeTwoPrimeBasis R (c.val.card+1) ⟨twoPrimeTaggedFace c .two,twoPrimeTaggedFace_card c .two⟩ +
       x.val.2 • primeTwoPrimeBasis R (c.val.card+1) ⟨twoPrimeTaggedFace c .three,twoPrimeTaggedFace_card c .three⟩)
      ⟨twoPrimeTaggedFace c .two,twoPrimeTaggedFace_card c .two⟩ = x.val.1
    simp only [map_add,map_smul,Module.Basis.repr_self,Finsupp.add_apply,Finsupp.smul_apply,
      Finsupp.single_apply,if_true,if_neg (twoPrimeMiddleFaces_ne c).symm,
      smul_eq_mul,mul_one,mul_zero,add_zero]
  · change (primeTwoPrimeBasis R (c.val.card+1)).repr
      (x.val.1 • primeTwoPrimeBasis R (c.val.card+1) ⟨twoPrimeTaggedFace c .two,twoPrimeTaggedFace_card c .two⟩ +
       x.val.2 • primeTwoPrimeBasis R (c.val.card+1) ⟨twoPrimeTaggedFace c .three,twoPrimeTaggedFace_card c .three⟩)
      ⟨twoPrimeTaggedFace c .three,twoPrimeTaggedFace_card c .three⟩ = x.val.2
    simp only [map_add,map_smul,Module.Basis.repr_self,Finsupp.add_apply,Finsupp.smul_apply,
      Finsupp.single_apply,if_true,if_neg (twoPrimeMiddleFaces_ne c),
      smul_eq_mul,mul_one,mul_zero,zero_add]

/-- The reconstructed tagged face determines both its core and its tag. -/
theorem twoPrimeTaggedFace_injective :
    Function.Injective (fun ct : TwoPrimeCoreFace × TwoPrimeFaceTag => twoPrimeTaggedFace ct.1 ct.2) :=
  twoPrimeFaceEquiv.symm.injective

/-- Extracting a tag from the actual bounded basis gives the Kronecker coordinate. -/
theorem twoPrimeBlockScalarExtraction_basis (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) (N : ℕ)
    (ct : TwoPrimeBlockIndex (c.val.card+t.degree) N) :
    (twoPrimeBlockScalarExtraction R c t N (twoPrimeBlockBasis R (c.val.card+t.degree) N ct)).val =
      if ct.val=(c,t) then 1 else 0 := by
  change (primeTwoPrimeBasis R (c.val.card+t.degree)).repr
    (twoPrimeBlockBasis R (c.val.card+t.degree) N ct).val
      ⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩ = _
  rw [twoPrimeBlockBasis_val,Module.Basis.repr_self]
  have hf :
      (⟨twoPrimeTaggedFace ct.val.1 ct.val.2,
        (twoPrimeTaggedFace_card ct.val.1 ct.val.2).trans ct.property.1⟩ :
          Set.powersetCard Nat.Primes (c.val.card+t.degree)) =
      ⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩ ↔ ct.val=(c,t) := by
    constructor
    · intro h
      exact twoPrimeTaggedFace_injective (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact congrArg (fun q : TwoPrimeCoreFace × TwoPrimeFaceTag => twoPrimeTaggedFace q.1 q.2) h
  simp only [Finsupp.single_apply,hf]

/-- A bounded label with a specified core and tag realizes that homogeneous vector. -/
theorem twoPrimeBlockBasis_eq_vector (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) (N : ℕ)
    (ct : TwoPrimeBlockIndex (c.val.card+t.degree) N) (h : ct.val=(c,t)) :
    (twoPrimeBlockBasis R (c.val.card+t.degree) N ct).val = twoPrimeBlockVector R c t := by
  rw [twoPrimeBlockBasis_val]
  apply congrArg (primeTwoPrimeBasis R (c.val.card+t.degree))
  apply Subtype.ext
  exact congrArg (fun q : TwoPrimeCoreFace × TwoPrimeFaceTag => twoPrimeTaggedFace q.1 q.2) h

/-- Distinct scalar coefficients realize distinct original cutoff chains. -/
theorem twoPrimeBlockScalarRealization_injective (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) (N : ℕ) :
    Function.Injective (twoPrimeBlockScalarRealization R c t N) :=
  Function.LeftInverse.injective (twoPrimeBlockScalarExtraction_realization R c t N)

/-- Distinct middle pairs realize distinct original cutoff chains. -/
theorem twoPrimeBlockMiddleRealization_injective (c : TwoPrimeCoreFace) (N : ℕ) :
    Function.Injective (twoPrimeBlockMiddleRealization R c N) :=
  Function.LeftInverse.injective (twoPrimeBlockMiddleExtraction_realization R c N)

#print axioms twoPrimeBlockScalarExtraction_basis
#print axioms twoPrimeBlockScalarExtraction_realization
#print axioms twoPrimeBlockMiddleExtraction_realization
end GaloisForLFunctions.EffectiveScalingGeometry
