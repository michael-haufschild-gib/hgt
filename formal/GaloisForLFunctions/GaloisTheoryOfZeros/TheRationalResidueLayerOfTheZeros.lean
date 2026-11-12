import GaloisForLFunctions.GaloisTheoryOfZeros.TheRationalWeightsOfPrimeZeroOrbits

/-!
# The rational-real-part residue layer

All prime values at actual zeros with rational real part generate a normal
subextension of the full prime spectral field over its trace source. Each
individual residue field is quadratic. Conjugate-pair traces and norms give
negative discriminants in the original source field, and their imaginary
square roots generate the complete layer.

All finite discriminant square relations classify its entire Galois group,
including its Krull topology. Ordinary conjugation is the uniform negative
sign and is central on this layer, which contains every critical-zero residue
field. No rationality or purity of the remaining zeros is assumed.
-/

noncomputable section
set_option autoImplicit false
open Complex Polynomial Set RHTower
open scoped BigOperators IntermediateField
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local instance : IsGalois B E := ⟨⟩

/-- Actual zeros with rational real part; this includes every critical zero. -/
def RationalRealPartZero := {ρ : XiDivisorSupport // ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ)}

/-- Conjugation retains the rational real part. -/
def rationalRealPartZeroConj (ρ : RationalRealPartZero) : RationalRealPartZero :=
  ⟨xiZeroConjEquiv ρ.val,ρ.property⟩

private theorem conj_zero_twice (ρ : XiDivisorSupport) :
    xiZeroConjEquiv (xiZeroConjEquiv ρ) = ρ := by
  apply Subtype.ext
  exact Complex.conj_conj (ρ : ℂ)

private theorem zero_ne_conj (ρ : XiDivisorSupport) : ρ ≠ xiZeroConjEquiv ρ := by
  intro h
  have hi := congrArg (fun ζ : XiDivisorSupport => (ζ : ℂ).im) h
  change (ρ : ℂ).im = -(ρ : ℂ).im at hi
  apply xi_divisor_support_im_ne_zero ρ
  linarith only [hi]

/-- Conjugation commutes with every arithmetic action on the rational-real-part zero layer. -/
theorem primeTraceZeroMap_rational_conjugation (σ : G) (ρ : RationalRealPartZero) :
    primeTraceZeroMap σ (xiZeroConjEquiv ρ.val) = xiZeroConjEquiv (primeTraceZeroMap σ ρ.val) := by
  have hi := (primeTraceZeroPermutation σ).injective
  rcases primeTraceZeroMap_rational_orbit ρ.val ρ.property σ with h | h
  · rcases primeTraceZeroMap_rational_orbit (xiZeroConjEquiv ρ.val)
        (rationalRealPartZeroConj ρ).property σ with hc | hc
    · rw [h]
      exact hc
    · rw [conj_zero_twice] at hc
      exact (zero_ne_conj ρ.val (hi (h.trans hc.symm))).elim
  · rcases primeTraceZeroMap_rational_orbit (xiZeroConjEquiv ρ.val)
        (rationalRealPartZeroConj ρ).property σ with hc | hc
    · exact (zero_ne_conj ρ.val (hi (h.trans hc.symm))).elim
    · rw [h]
      exact hc

/-- Conjugation on prime values is the ordinary complex conjugation. -/
theorem primeResidueValue_conjugation (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeTraceConjugation (primeResidueValue p ρ) = primeResidueValue p (xiZeroConjEquiv ρ) := by
  rw [primeResidueValue_map,primeTraceZeroMap_conjugation]

private theorem rational_prime_symmetrics_fixed (p : Nat.Primes) (ρ : RationalRealPartZero) (σ : G) :
    σ (primeResidueValue p ρ.val + primeResidueValue p (xiZeroConjEquiv ρ.val)) =
      primeResidueValue p ρ.val + primeResidueValue p (xiZeroConjEquiv ρ.val) ∧
    σ (primeResidueValue p ρ.val * primeResidueValue p (xiZeroConjEquiv ρ.val)) =
      primeResidueValue p ρ.val * primeResidueValue p (xiZeroConjEquiv ρ.val) := by
  rw [map_add,map_mul,primeResidueValue_map,primeResidueValue_map,
    primeTraceZeroMap_rational_conjugation]
  rcases primeTraceZeroMap_rational_orbit ρ.val ρ.property σ with h | h
  · rw [h]
    exact ⟨rfl,rfl⟩
  · rw [h,conj_zero_twice]
    exact ⟨add_comm _ _,mul_comm _ _⟩

private theorem rational_prime_trace_exists (p : Nat.Primes) (ρ : RationalRealPartZero) :
    ∃ u : B, algebraMap B E u =
      primeResidueValue p ρ.val + primeResidueValue p (xiZeroConjEquiv ρ.val) :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    (fun σ => (rational_prime_symmetrics_fixed p ρ σ).1)

private theorem rational_prime_norm_exists (p : Nat.Primes) (ρ : RationalRealPartZero) :
    ∃ v : B, algebraMap B E v =
      primeResidueValue p ρ.val * primeResidueValue p (xiZeroConjEquiv ρ.val) :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    (fun σ => (rational_prime_symmetrics_fixed p ρ σ).2)

/-- The actual conjugate-pair trace of a prime value, descended to the source field. -/
def rationalPrimeTrace (p : Nat.Primes) (ρ : RationalRealPartZero) : B :=
  Classical.choose (rational_prime_trace_exists p ρ)

/-- The actual conjugate-pair norm, equal to the positive prime weight of twice the real part. -/
def rationalPrimeNorm (p : Nat.Primes) (ρ : RationalRealPartZero) : B :=
  Classical.choose (rational_prime_norm_exists p ρ)

theorem rationalPrimeTrace_value (p : Nat.Primes) (ρ : RationalRealPartZero) :
    algebraMap B E (rationalPrimeTrace p ρ) =
      primeResidueValue p ρ.val + primeResidueValue p (xiZeroConjEquiv ρ.val) :=
  Classical.choose_spec (rational_prime_trace_exists p ρ)

theorem rationalPrimeNorm_value (p : Nat.Primes) (ρ : RationalRealPartZero) :
    algebraMap B E (rationalPrimeNorm p ρ) =
      primeResidueValue p ρ.val * primeResidueValue p (xiZeroConjEquiv ρ.val) :=
  Classical.choose_spec (rational_prime_norm_exists p ρ)

/-- The prime coordinate quadratic is over the original trace field, not an enlarged pair field. -/
def rationalPrimeQuadratic (p : Nat.Primes) (ρ : RationalRealPartZero) : B[X] :=
  X^2 + (C (-rationalPrimeTrace p ρ)*X+C (rationalPrimeNorm p ρ))

private theorem rational_prime_quadratic_degree (p : Nat.Primes) (ρ : RationalRealPartZero) :
    (rationalPrimeQuadratic p ρ).Monic ∧ (rationalPrimeQuadratic p ρ).natDegree=2 := by
  let u := rationalPrimeTrace p ρ
  let v := rationalPrimeNorm p ρ
  have hd : (C (-u)*X+C v : B[X]).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    · simp only [Polynomial.natDegree_C,zero_le]
  have hdeg : (C (-u)*X+C v : B[X]).degree < (2 : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hd)
  constructor
  · exact Polynomial.monic_X_pow_add hdeg
  · change (X^2+(C (-u)*X+C v) : B[X]).natDegree=2
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt
      (by simpa only [Polynomial.degree_X_pow] using hdeg),Polynomial.natDegree_X_pow]

theorem rationalPrimeQuadratic_root (p : Nat.Primes) (ρ : RationalRealPartZero) :
    aeval (primeResidueValue p ρ.val) (rationalPrimeQuadratic p ρ) = 0 := by
  rw [rationalPrimeQuadratic,Polynomial.aeval_def,eval₂_add,eval₂_pow,eval₂_X,
    eval₂_add,eval₂_mul,eval₂_C,eval₂_X,eval₂_C,map_neg,
    rationalPrimeTrace_value,rationalPrimeNorm_value]
  ring

/-- Each rational-real-part zero has a genuinely quadratic full prime residue field over the source. -/
theorem rationalPrimeResidueField_degree_two (ρ : RationalRealPartZero) :
    Module.finrank B (primeResidueField ρ.val) = 2 := by
  have hex : ∃ p : Nat.Primes,
      primeResidueField ρ.val = IntermediateField.adjoin B {primeResidueValue p ρ.val} := by
    rcases primeResidueField_one_of_two ⟨2,Nat.prime_two⟩ ⟨3,Nat.prime_three⟩ (by decide) ρ.val with h | h
    · exact ⟨_,h⟩
    · exact ⟨_,h⟩
  obtain ⟨p,hp⟩ := hex
  have hle : Module.finrank B (primeResidueField ρ.val) ≤ 2 := by
    rw [hp,IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := B) _)]
    calc
      _ ≤ (rationalPrimeQuadratic p ρ).natDegree := Polynomial.natDegree_le_of_dvd
        (minpoly.dvd _ _ (rationalPrimeQuadratic_root p ρ)) (rational_prime_quadratic_degree p ρ).1.ne_zero
      _ = 2 := (rational_prime_quadratic_degree p ρ).2
  have hbot : primeResidueField ρ.val ≠ ⊥ := by
    intro he
    have hv := primeResidueValue_mem p ρ.val
    rw [he,IntermediateField.mem_bot] at hv
    obtain ⟨b,hb⟩ := hv
    apply (primeResidueField_single_iff p ρ.val).mp hp
    have hc := congrArg (fun x : E => (x : ℂ).im) hb
    change (b : ℂ).im = (primeResidueValue p ρ.val : ℂ).im at hc
    exact hc.symm.trans (primeTraceField_real b b.property)
  have hne : Module.finrank B (primeResidueField ρ.val) ≠ 1 := by
    intro h
    exact hbot (IntermediateField.finrank_eq_one_iff.mp h)
  have hpos := Module.finrank_pos (R := B) (M := primeResidueField ρ.val)
  omega

/-- All prime residue fields of rational-real-part zeros, with no height or prime cutoff. -/
def rationalZeroResidueLayer : IntermediateField B E :=
  IntermediateField.adjoin B (Set.range fun i : Nat.Primes × RationalRealPartZero =>
    primeResidueValue i.1 i.2.val)

local notation "L" => rationalZeroResidueLayer

theorem rationalZeroResidueLayer_value_mem (p : Nat.Primes) (ρ : RationalRealPartZero) :
    primeResidueValue p ρ.val ∈ L := IntermediateField.subset_adjoin B _ ⟨(p,ρ),rfl⟩

theorem rationalPrimeResidueField_le_layer (ρ : RationalRealPartZero) : primeResidueField ρ.val ≤ L := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨p,rfl⟩
  exact rationalZeroResidueLayer_value_mem p ρ

/-- Every critical zero contributes its entire residue field to this infinite layer. -/
theorem criticalPrimeResidueField_le_rationalLayer (ρ : XiDivisorSupport) (h : (ρ : ℂ).re=1/2) :
    primeResidueField ρ ≤ L :=
  rationalPrimeResidueField_le_layer ⟨ρ,1/2,by simpa using h⟩

private theorem fixing_rational_layer (σ : G) :
    σ ∈ (L).fixingSubgroup ↔ ∀ p (ρ : RationalRealPartZero),
      σ (primeResidueValue p ρ.val) = primeResidueValue p ρ.val := by
  constructor
  · intro h p ρ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp h _
      (rationalZeroResidueLayer_value_mem p ρ)
  · intro h
    have hext := IntermediateField.algHom_ext_of_eq_adjoin B (S := L) rfl
      (φ₁ := σ.toAlgHom.comp (IntermediateField.val L)) (φ₂ := IntermediateField.val L)
      (by rintro x ⟨⟨p,ρ⟩,rfl⟩; exact h p ρ)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx =>
      DFunLike.congr_fun hext ⟨x,hx⟩

instance rationalZeroResidueLayer_fixing_normal : (L).fixingSubgroup.Normal := by
  constructor
  intro τ hτ σ
  apply (fixing_rational_layer _).mpr
  intro p ρ
  let ζ : RationalRealPartZero := ⟨primeTraceZeroMap σ⁻¹ ρ.val,by
    obtain ⟨r,hr⟩ := ρ.property
    exact ⟨r,(primeTraceZeroMap_rational_real_part ρ.val ρ.property σ⁻¹).trans hr⟩⟩
  have ht := (fixing_rational_layer τ).mp hτ p ζ
  change σ (τ (σ.symm (primeResidueValue p ρ.val))) = primeResidueValue p ρ.val
  have hi : σ.symm (primeResidueValue p ρ.val) = primeResidueValue p ζ.val :=
    primeResidueValue_map σ⁻¹ p ρ.val
  rw [hi,ht,← hi,σ.apply_symm_apply]

/-- The complete rational-real-part residue layer is a normal arithmetic subextension. -/
instance rationalZeroResidueLayer_normal : Normal B L := by
  have hn : Normal B (IntermediateField.fixedField (L).fixingSubgroup) := inferInstance
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hn
  exact hn

instance rationalZeroResidueLayer_isGalois : IsGalois B L := ⟨⟩

/-- Every automorphism of this layer is the restriction of an actual prime-trace automorphism. -/
def rationalZeroResidueRestriction : G →* (L ≃ₐ[B] L) := AlgEquiv.restrictNormalHom L

theorem rationalZeroResidueRestriction_surjective : Function.Surjective rationalZeroResidueRestriction :=
  AlgEquiv.restrictNormalHom_surjective E

theorem rationalZeroResidueRestriction_continuous : Continuous rationalZeroResidueRestriction :=
  InfiniteGalois.restrictNormalHom_continuous L

/-- A prime value as an element of the full rational-real-part residue layer. -/
def rationalPrimeValue (p : Nat.Primes) (ρ : RationalRealPartZero) : L :=
  ⟨primeResidueValue p ρ.val,rationalZeroResidueLayer_value_mem p ρ⟩

/-- The purely imaginary difference of conjugate prime values. -/
def rationalPrimeDifference (p : Nat.Primes) (ρ : RationalRealPartZero) : L :=
  rationalPrimeValue p ρ - rationalPrimeValue p (rationalRealPartZeroConj ρ)

private theorem rational_prime_difference_eq_zero (p : Nat.Primes) (ρ : RationalRealPartZero)
    (h : (primeResidueValue p ρ.val : ℂ).im=0) : rationalPrimeDifference p ρ=0 := by
  apply Subtype.ext
  change primeResidueValue p ρ.val-primeResidueValue p (xiZeroConjEquiv ρ.val)=0
  apply sub_eq_zero.mpr
  rw [← primeResidueValue_conjugation]
  exact Subtype.ext (Complex.conj_eq_iff_im.mpr h).symm

/-- Nonreal prime coordinates index the nonzero imaginary radicals. -/
def NonrealRationalPrime := {i : Nat.Primes × RationalRealPartZero //
  (primeResidueValue i.1 i.2.val : ℂ).im ≠ 0}

def rationalPrimeRadical (i : NonrealRationalPrime) : L :=
  rationalPrimeDifference i.val.1 i.val.2

/-- The actual discriminant in the original trace field. -/
def rationalPrimeRadicand (i : NonrealRationalPrime) : B :=
  rationalPrimeTrace i.val.1 i.val.2 ^ 2 - 4*rationalPrimeNorm i.val.1 i.val.2

theorem rationalPrimeRadical_sq (i : NonrealRationalPrime) :
    rationalPrimeRadical i ^ 2 = algebraMap B L (rationalPrimeRadicand i) := by
  apply Subtype.ext
  change (primeResidueValue i.val.1 i.val.2.val -
    primeResidueValue i.val.1 (xiZeroConjEquiv i.val.2.val))^2 =
    algebraMap B E (rationalPrimeTrace i.val.1 i.val.2 ^ 2 - 4*rationalPrimeNorm i.val.1 i.val.2)
  rw [map_sub,map_pow,map_mul,map_ofNat,rationalPrimeTrace_value,rationalPrimeNorm_value]
  ring

theorem rationalPrimeRadical_ne_zero (i : NonrealRationalPrime) : rationalPrimeRadical i ≠ 0 := by
  intro h
  have he := congrArg (fun x : L => (x : E)) h
  change primeResidueValue i.val.1 i.val.2.val -
    primeResidueValue i.val.1 (xiZeroConjEquiv i.val.2.val)=0 at he
  have hc := (sub_eq_zero.mp he).symm
  rw [← primeResidueValue_conjugation] at hc
  exact i.property (Complex.conj_eq_iff_im.mp (congrArg (fun x : E => (x : ℂ)) hc))

/-- Every nonzero radical has strictly negative discriminant in the chosen real embedding. -/
theorem rationalPrimeRadicand_negative (i : NonrealRationalPrime) :
    (rationalPrimeRadicand i : ℂ).re < 0 := by
  have he := congrArg (fun x : L => ((x : E) : ℂ).re) (rationalPrimeRadical_sq i)
  have hc : (primeResidueValue i.val.1 (xiZeroConjEquiv i.val.2.val) : ℂ) =
      starRingEnd ℂ (primeResidueValue i.val.1 i.val.2.val : ℂ) :=
    (congrArg (fun x : E => (x : ℂ)) (primeResidueValue_conjugation i.val.1 i.val.2.val)).symm
  change (((primeResidueValue i.val.1 i.val.2.val : ℂ)-
    (primeResidueValue i.val.1 (xiZeroConjEquiv i.val.2.val) : ℂ))^2).re =
    (rationalPrimeRadicand i : ℂ).re at he
  rw [hc] at he
  simp only [pow_two,Complex.mul_re,Complex.sub_re,Complex.conj_re,sub_self,
    zero_mul,Complex.sub_im,Complex.conj_im] at he
  have hp := sq_pos_of_ne_zero i.property
  nlinarith only [he,hp]

/-- The imaginary differences generate the entire rational-real-part residue layer. -/
theorem rationalPrimeRadicals_adjoin_top :
    IntermediateField.adjoin B (Set.range rationalPrimeRadical) = ⊤ := by
  let A := IntermediateField.adjoin B (Set.range rationalPrimeRadical)
  have hv (p : Nat.Primes) (ρ : RationalRealPartZero) : rationalPrimeValue p ρ ∈ A := by
    have hu : algebraMap B L (rationalPrimeTrace p ρ) ∈ A := A.algebraMap_mem _
    have hd : rationalPrimeDifference p ρ ∈ A := by
      by_cases h : (primeResidueValue p ρ.val : ℂ).im=0
      · rw [rational_prime_difference_eq_zero p ρ h]
        exact A.zero_mem
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨(p,ρ),h⟩,rfl⟩
    have he : rationalPrimeValue p ρ =
        (algebraMap B L (rationalPrimeTrace p ρ)+rationalPrimeDifference p ρ)/2 := by
      apply Subtype.ext
      change primeResidueValue p ρ.val =
        (algebraMap B E (rationalPrimeTrace p ρ)+
          (primeResidueValue p ρ.val-primeResidueValue p (xiZeroConjEquiv ρ.val)))/2
      rw [rationalPrimeTrace_value]
      ring
    rw [he]
    exact A.div_mem (A.add_mem hu hd) (A.natCast_mem 2)
  have hle : L ≤ A.map (IntermediateField.val L) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨⟨p,ρ⟩,rfl⟩
    exact ⟨rationalPrimeValue p ρ,hv p ρ,rfl⟩
  apply top_unique
  intro z _
  obtain ⟨a,ha,he⟩ := hle z.property
  have haz : a=z := Subtype.ext he
  exact haz ▸ ha

local notation "Γ" => (L ≃ₐ[B] L)

/-- The arithmetic signs on the actual imaginary prime radicals. -/
def rationalResidueSignAction : Γ →* (NonrealRationalPrime → ℤˣ) :=
  radicalSignAction rationalPrimeRadical rationalPrimeRadicand
    rationalPrimeRadical_sq rationalPrimeRadical_ne_zero

/-- All finite discriminant square relations give exactly the realizable signs on the whole layer. -/
theorem rationalResidueSignAction_unique_extension (ε : NonrealRationalPrime → ℤˣ) :
    (∃! σ : Γ, rationalResidueSignAction σ = ε) ↔
      ∀ S : Finset NonrealRationalPrime, IsSquare (∏ i ∈ S, rationalPrimeRadicand i) →
        ∏ i ∈ S, ε i=1 :=
  radicalSignAction_unique_extension rationalPrimeRadical rationalPrimeRadicand
    rationalPrimeRadical_sq rationalPrimeRadical_ne_zero rationalPrimeRadicals_adjoin_top ε

theorem rationalResidueSignAction_injective : Function.Injective rationalResidueSignAction :=
  radicalSignAction_injective rationalPrimeRadical rationalPrimeRadicand
    rationalPrimeRadical_sq rationalPrimeRadical_ne_zero rationalPrimeRadicals_adjoin_top

theorem rationalResidueSignAction_continuous : Continuous rationalResidueSignAction :=
  radicalSignAction_continuous rationalPrimeRadical rationalPrimeRadicand
    rationalPrimeRadical_sq rationalPrimeRadical_ne_zero

private def rationalSignProduct (S : Finset NonrealRationalPrime) :
    (NonrealRationalPrime → ℤˣ) →* ℤˣ where
  toFun ε := ∏ i ∈ S, ε i
  map_one' := by simp
  map_mul' ε η := by simp only [Pi.mul_apply,Finset.prod_mul_distrib]

/-- The closed sign group determined by the actual prime discriminants. -/
def rationalResidueRelationSigns : Subgroup (NonrealRationalPrime → ℤˣ) where
  carrier := {ε | ∀ S : Finset NonrealRationalPrime,
    IsSquare (∏ i ∈ S, rationalPrimeRadicand i) → ∏ i ∈ S, ε i=1}
  one_mem' := by intro S _; simp only [Pi.one_apply,Finset.prod_const_one]
  mul_mem' := by
    intro ε η hε hη S hS
    change rationalSignProduct S (ε*η)=1
    rw [map_mul,show rationalSignProduct S ε=1 from hε S hS,
      show rationalSignProduct S η=1 from hη S hS,mul_one]
  inv_mem' := by
    intro ε hε S hS
    change rationalSignProduct S ε⁻¹=1
    rw [map_inv,show rationalSignProduct S ε=1 from hε S hS,inv_one]

def rationalResidueSignCoordinates : Γ →* rationalResidueRelationSigns where
  toFun σ := ⟨rationalResidueSignAction σ,fun S hS =>
    (radical_product_trivial_iff_square rationalPrimeRadical rationalPrimeRadicand
      rationalPrimeRadical_sq rationalPrimeRadical_ne_zero S).mpr hS σ⟩
  map_one' := Subtype.ext (map_one rationalResidueSignAction)
  map_mul' σ τ := Subtype.ext (map_mul rationalResidueSignAction σ τ)

private theorem rational_sign_coordinates_bijective : Function.Bijective rationalResidueSignCoordinates := by
  constructor
  · intro σ τ h
    exact rationalResidueSignAction_injective (congrArg Subtype.val h)
  · intro ε
    obtain ⟨σ,hσ,_⟩ := (rationalResidueSignAction_unique_extension ε.val).mpr ε.property
    exact ⟨σ,Subtype.ext hσ⟩

/-- The exact Galois group of the complete rational-real-part residue layer. -/
def rationalResidueSignEquiv : Γ ≃* rationalResidueRelationSigns :=
  MulEquiv.ofBijective rationalResidueSignCoordinates rational_sign_coordinates_bijective

/-- The full sign classification preserves the Krull topology. -/
def rationalResidueSignHomeomorph : Γ ≃ₜ rationalResidueRelationSigns :=
  Continuous.homeoOfEquivCompactToT2 (f := rationalResidueSignEquiv.toEquiv)
    (rationalResidueSignAction_continuous.subtype_mk _)

/-- The whole residue layer is an elementary abelian two-extension over the original source. -/
theorem rationalResidueGalois_comm (σ τ : Γ) : σ*τ=τ*σ := by
  apply rationalResidueSignAction_injective
  rw [map_mul,map_mul,mul_comm]

theorem rationalResidueGalois_square (σ : Γ) : σ*σ=1 := by
  apply rationalResidueSignAction_injective
  rw [map_mul,map_one]
  funext i
  change rationalResidueSignAction σ i * rationalResidueSignAction σ i=1
  rcases Int.units_eq_one_or (rationalResidueSignAction σ i) with h | h
  · rw [h,one_mul]
  · rw [h,neg_mul_neg,one_mul]

/-- Ordinary complex conjugation restricted to the full rational-real-part residue layer. -/
def rationalResidueConjugation : Γ := primeTraceConjugation.restrictNormal L

theorem rationalResidueConjugation_radical (i : NonrealRationalPrime) :
    rationalResidueConjugation (rationalPrimeRadical i) = -rationalPrimeRadical i := by
  apply Subtype.ext
  apply (AlgEquiv.restrictNormal_commutes primeTraceConjugation L (rationalPrimeRadical i)).trans
  change primeTraceConjugation (primeResidueValue i.val.1 i.val.2.val-
    primeResidueValue i.val.1 (xiZeroConjEquiv i.val.2.val)) =
    -(primeResidueValue i.val.1 i.val.2.val-primeResidueValue i.val.1 (xiZeroConjEquiv i.val.2.val))
  rw [map_sub,primeResidueValue_conjugation,primeResidueValue_conjugation,conj_zero_twice]
  ring

/-- Conjugation is precisely the uniform negative sign on every imaginary prime radical. -/
theorem rationalResidueConjugation_signs : rationalResidueSignAction rationalResidueConjugation = (fun _ => -1) := by
  funext i
  have hn : rationalResidueSignAction rationalResidueConjugation i ≠ 1 := by
    intro he
    have ha := sourceRootSign_action (rationalPrimeRadical i) (rationalPrimeRadicand i)
      (rationalPrimeRadical_sq i) (rationalPrimeRadical_ne_zero i) rationalResidueConjugation
    change rationalResidueConjugation (rationalPrimeRadical i) =
      ((rationalResidueSignAction rationalResidueConjugation i : ℤ) : L)*rationalPrimeRadical i at ha
    rw [he,Units.val_one,Int.cast_one,one_mul,rationalResidueConjugation_radical] at ha
    apply rationalPrimeRadical_ne_zero i
    linear_combination (-1/2 : L)*ha
  exact (Int.units_eq_one_or _).resolve_left hn

/-- An odd product of actual discriminants is never square in the trace ground field. -/
theorem rationalPrimeRadicands_square_even (S : Finset NonrealRationalPrime)
    (hS : IsSquare (∏ i ∈ S, rationalPrimeRadicand i)) : Even S.card := by
  have he := (radical_product_trivial_iff_square rationalPrimeRadical rationalPrimeRadicand
    rationalPrimeRadical_sq rationalPrimeRadical_ne_zero S).mpr hS rationalResidueConjugation
  change (∏ i ∈ S, rationalResidueSignAction rationalResidueConjugation i)=1 at he
  rw [rationalResidueConjugation_signs,Finset.prod_const] at he
  exact (neg_one_pow_eq_one_iff_even (by decide)).mp he

/-- Uniform sign reversal is realized uniquely by actual complex conjugation. -/
theorem rationalResidueConjugation_unique :
    ∃! σ : Γ, rationalResidueSignAction σ = (fun _ => -1) :=
  ⟨rationalResidueConjugation,rationalResidueConjugation_signs,
    fun _σ hσ => rationalResidueSignAction_injective (hσ.trans rationalResidueConjugation_signs.symm)⟩

/-- Conjugation is central on the whole rational-real-part residue layer. -/
theorem rationalResidueConjugation_central (σ : Γ) :
    σ*rationalResidueConjugation=rationalResidueConjugation*σ := rationalResidueGalois_comm _ _

/-- The descended norm is the actual positive prime weight of twice the real part. -/
theorem rationalPrimeNorm_coe (p : Nat.Primes) (ρ : RationalRealPartZero) :
    (rationalPrimeNorm p ρ : ℂ) =
      Complex.exp ((Real.log (p : ℕ) : ℂ)*((2*(ρ.val : ℂ).re : ℝ) : ℂ)) := by
  have he := congrArg (fun x : E => (x : ℂ)) (rationalPrimeNorm_value p ρ)
  change (rationalPrimeNorm p ρ : ℂ) =
    (primeResidueValue p ρ.val : ℂ)*(primeResidueValue p (xiZeroConjEquiv ρ.val) : ℂ) at he
  rw [he,primeResidueValue_coe,primeResidueValue_coe,← Complex.exp_add,← mul_add]
  congr 2
  change (ρ.val : ℂ)+starRingEnd ℂ (ρ.val : ℂ)=((2*(ρ.val : ℂ).re : ℝ) : ℂ)
  apply Complex.ext
  · simp only [Complex.add_re,Complex.conj_re,Complex.ofReal_re]
    ring
  · simp only [Complex.add_im,Complex.conj_im,Complex.ofReal_im,add_neg_cancel]

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceZeroMap_rational_conjugation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeTrace_value
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeNorm_value
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeQuadratic_root
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeResidueField_degree_two
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeResidueField_le_layer
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.criticalPrimeResidueField_le_rationalLayer
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalZeroResidueLayer_fixing_normal
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalZeroResidueLayer_normal
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalZeroResidueRestriction_surjective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalZeroResidueRestriction_continuous
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeRadical_sq
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeRadical_ne_zero
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeRadicand_negative
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeRadicals_adjoin_top
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueSignAction_unique_extension
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueSignAction_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueSignAction_continuous
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueSignEquiv
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueSignHomeomorph
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueGalois_comm
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueGalois_square
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueConjugation_radical
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueConjugation_signs
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeRadicands_square_even
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueConjugation_unique
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalResidueConjugation_central
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeNorm_coe
