import GaloisForLFunctions.GaloisTheoryOfZeros.TheGroupActsOnAZeroThroughTheTwoInvolutionsIffItsWidthValueLiesInThePrimeTraceField

/-!
# The orbit of a zero lies in its quartet iff its width and ordinate values solve a quadratic

`E` is the field of the prime values `p^ρ` of the zeros, `B` the prime trace field,
`G = Gal(E/B)`. For a zero `ρ = β + iγ` and a prime `p` let `u = 2 cos(2γ log p)` be its ordinate
value and `v = p^{2β−1} + p^{1−2β}` its width value, the values of the exponents `±(ρ − ρ̄)` and
`±(ρ + ρ̄ − 1)`. A permutation of the quartet `{ρ, ρ̄, 1 − ρ, 1 − ρ̄}` that commutes with the
reflection permutes these exponents: if it keeps the pair `{ρ, ρ̄}` it fixes `u` and `v`,
otherwise (a *partial flip*, `σρ̄ = 1 − conj(σρ)`) it exchanges `u` and `v`.

* **Quartet criterion** (`sum_prod_mem_iff_mem_quartet`). For one prime `p`: `u + v ∈ B` and
  `uv ∈ B`, i.e. `u` and `v` are the two roots of a quadratic over `B`, iff every `σ ∈ G` sends
  `ρ` into its quartet.
* **Partial flips** (`exists_partialFlip_iff`, `primeOrdinateValue_mem_iff_width_mem`). If the
  orbit of an off-line zero lies in its quartet, then `u ∈ B ⇔ v ∈ B`, and `u ∉ B` iff some `σ`
  acts as a partial flip; such a `σ` exchanges `u` and `v`.

With the weight and width criteria this classifies the orbits inside a quartet: `{ρ, ρ̄}` iff
`p^{2β} ∈ B`; otherwise the whole quartet, with every `σ` acting on `ρ, ρ̄` as `1, c, r` or `cr`
iff `v ∈ B`, and with a partial flip iff `v ∉ B`.

Proof. If `σ` fixes `u + v` and `uv`, it sends `u` to `u` or to `v`. In the first case it fixes
both, so `σρ, σρ̄` have one real part and `Re σρ + Re σρ̄ − 1 = ±(2β − 1)`; in the second the
prime values of `σ(ρ + ρ̄ − 1)` have modulus one and `Re σρ − Re σρ̄ = ±(2β − 1)`. Either way
`Re σρ ∈ {β, 1 − β}`. Conversely, inside the quartet `σρ̄ ≠ σρ` and `σρ̄ ≠ 1 − σρ` leave
`σρ̄ ∈ {conj(σρ), 1 − conj(σρ)}`.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local notation "Δ" => rawZeroRelationGroup
local instance : IsGalois B E := ⟨⟩

/-! ## The quartet in coordinates -/

/-- An image of `ρ` lies in the quartet iff its real part is `β` or `1 − β`. -/
theorem mem_quartet_iff_re (σ : G) (ρ : XiDivisorSupport) :
    (primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroConjEquiv ρ ∨
      primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ ∨
        primeTraceZeroMap σ ρ = xiZeroReflectEquiv (xiZeroConjEquiv ρ)) ↔
    ((primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap σ ρ : ℂ).re = 1 - (ρ : ℂ).re) := by
  refine ⟨?_, primeTraceZeroMap_mem_quartet_of_re σ ρ⟩
  rintro (e | e | e | e) <;> rw [e]
  · exact Or.inl rfl
  · exact Or.inl (Complex.conj_re _)
  · refine Or.inr ?_
    change (1 - (ρ : ℂ)).re = _
    rw [Complex.sub_re, Complex.one_re]
  · refine Or.inr ?_
    change (1 - starRingEnd ℂ (ρ : ℂ)).re = _
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]

theorem primeTraceExponentHom_ordinate_re (σ : G) (ρ : XiDivisorSupport) :
    ((primeTraceExponentHom σ (primeTraceOrdinate ρ) : Δ) : ℂ).re =
      (primeTraceZeroMap σ ρ : ℂ).re - (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).re := by
  rw [primeTraceExponentHom_ordinate]
  exact Complex.sub_re _ _

theorem primeTraceOrdinate_re (ρ : XiDivisorSupport) :
    ((primeTraceOrdinate ρ : Δ) : ℂ).re = 0 := by
  rw [primeTraceOrdinate_coe, Complex.re_ofReal_mul, Complex.I_re, mul_zero]

theorem primeTraceOrdinate_neg_re (ρ : XiDivisorSupport) :
    ((-primeTraceOrdinate ρ : Δ) : ℂ).re = 0 := by
  rw [AddSubgroup.coe_neg, Complex.neg_re, primeTraceOrdinate_re, neg_zero]

/-! ## From the two symmetric functions to the quartet -/

/-- An automorphism that fixes `u + v` and `uv` sends `ρ` to a zero of real part `β` or
`1 − β`. -/
theorem primeTraceZeroMap_re_of_sum_prod_fixed (p : Nat.Primes) (ρ : XiDivisorSupport) (σ : G)
    (hs : σ (primeOrdinateValue p ρ + primeWidthValue p ρ) =
      primeOrdinateValue p ρ + primeWidthValue p ρ)
    (hp : σ (primeOrdinateValue p ρ * primeWidthValue p ρ) =
      primeOrdinateValue p ρ * primeWidthValue p ρ) :
    (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap σ ρ : ℂ).re = 1 - (ρ : ℂ).re := by
  have hxx := primeTraceExponentValue_mul_neg p (primeTraceCentredWeight ρ)
  have hyy := primeTraceExponentValue_mul_neg p (primeTraceOrdinate ρ)
  have hre := primeTraceExponentHom_centredWeight_re σ ρ
  have hro := primeTraceExponentHom_ordinate_re σ ρ
  rw [map_add] at hs
  rw [map_mul] at hp
  -- `σu` is `u` or `v`
  have hq : (σ (primeOrdinateValue p ρ) - primeOrdinateValue p ρ) *
      (σ (primeOrdinateValue p ρ) - primeWidthValue p ρ) = 0 := by
    linear_combination (σ (primeOrdinateValue p ρ)) * hs - hp
  rcases mul_eq_zero.1 hq with h | h
  · -- `σ` fixes `u` and `v`
    have hu : σ (primeOrdinateValue p ρ) = primeOrdinateValue p ρ := sub_eq_zero.1 h
    have hv : σ (primeWidthValue p ρ) = primeWidthValue p ρ := by
      linear_combination hs - hu
    have hc := primeTraceZeroMap_re_conj_of_fixed p ρ σ hu
    rcases eq_or_eq_of_add_eq hxx hxx hv with e | e
    · have h1 := primeTraceExponentHom_re_of_value_eq p e
      rw [hre, primeTraceCentredWeight_coe, Complex.ofReal_re, hc] at h1
      left
      linarith only [h1]
    · have h1 := primeTraceExponentHom_re_of_value_eq p e
      rw [hre, AddSubgroup.coe_neg, Complex.neg_re, primeTraceCentredWeight_coe,
        Complex.ofReal_re, hc] at h1
      right
      linarith only [h1]
  · -- `σ` exchanges `u` and `v`
    have hu : σ (primeOrdinateValue p ρ) = primeWidthValue p ρ := sub_eq_zero.1 h
    have hv : σ (primeWidthValue p ρ) = primeOrdinateValue p ρ := by
      linear_combination hs - hu
    have hsum : (primeTraceZeroMap σ ρ : ℂ).re +
        (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).re - 1 = 0 := by
      rcases eq_or_eq_of_add_eq hyy hxx hv with e | e
      · have h1 := primeTraceExponentHom_re_of_value_eq p e
        rwa [hre, primeTraceOrdinate_re] at h1
      · have h1 := primeTraceExponentHom_re_of_value_eq p e
        rwa [hre, primeTraceOrdinate_neg_re] at h1
    rcases eq_or_eq_of_add_eq hxx hyy hu with e | e
    · have h1 := primeTraceExponentHom_re_of_value_eq p e
      rw [hro, primeTraceCentredWeight_coe, Complex.ofReal_re] at h1
      left
      linarith only [h1, hsum]
    · have h1 := primeTraceExponentHom_re_of_value_eq p e
      rw [hro, AddSubgroup.coe_neg, Complex.neg_re, primeTraceCentredWeight_coe,
        Complex.ofReal_re] at h1
      right
      linarith only [h1, hsum]

/-! ## Inside the quartet -/

/-- If the orbit of an off-line zero lies in its quartet, each automorphism sends `ρ̄` to
`conj(σρ)` or to `1 − conj(σρ)`: the other two points are `σρ` and `1 − σρ`. -/
theorem primeTraceZeroMap_conj_or_flip (ρ : XiDivisorSupport)
    (h : ∀ τ : G, (primeTraceZeroMap τ ρ : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap τ ρ : ℂ).re = 1 - (ρ : ℂ).re) (hβ : (ρ : ℂ).re ≠ 1 / 2) (σ : G) :
    primeTraceZeroMap σ (xiZeroConjEquiv ρ) = xiZeroConjEquiv (primeTraceZeroMap σ ρ) ∨
      primeTraceZeroMap σ (xiZeroConjEquiv ρ) =
        xiZeroReflectEquiv (xiZeroConjEquiv (primeTraceZeroMap σ ρ)) := by
  have hb : (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).re = 1 - (ρ : ℂ).re := by
    have := h (σ * primeTraceConjugation)
    rwa [primeTraceZeroMap_mul, primeTraceZeroMap_conjugation] at this
  have hne1 : primeTraceZeroMap σ (xiZeroConjEquiv ρ) ≠ primeTraceZeroMap σ ρ := by
    intro e
    have hi := congrArg (fun z : XiDivisorSupport => (z : ℂ).im)
      ((primeTraceZeroPermutation σ).injective e)
    change (starRingEnd ℂ (ρ : ℂ)).im = (ρ : ℂ).im at hi
    rw [Complex.conj_im] at hi
    exact xi_divisor_support_im_ne_zero ρ (by linarith only [hi])
  have hne2 : primeTraceZeroMap σ (xiZeroConjEquiv ρ) ≠
      xiZeroReflectEquiv (primeTraceZeroMap σ ρ) := by
    intro e
    rw [← primeTraceZeroMap_reflection] at e
    have hr := congrArg (fun z : XiDivisorSupport => (z : ℂ).re)
      ((primeTraceZeroPermutation σ).injective e)
    change (starRingEnd ℂ (ρ : ℂ)).re = (1 - (ρ : ℂ)).re at hr
    rw [Complex.conj_re, Complex.sub_re, Complex.one_re] at hr
    exact hβ (by linarith only [hr])
  have hre : (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).re = (primeTraceZeroMap σ ρ : ℂ).re ∨
      (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).re = 1 - (primeTraceZeroMap σ ρ : ℂ).re := by
    rcases h σ with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (hb.trans ha.symm)
    · exact Or.inr (by rw [hb, ha])
    · exact Or.inr (by rw [hb, ha]; ring)
    · exact Or.inl (hb.trans ha.symm)
  have him : (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).im = (primeTraceZeroMap σ ρ : ℂ).im ∨
      (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).im = -(primeTraceZeroMap σ ρ : ℂ).im := by
    refine abs_eq_abs.1 ?_
    rw [primeTraceZeroMap_height, primeTraceZeroMap_height]
    change |(starRingEnd ℂ (ρ : ℂ)).im| = _
    rw [Complex.conj_im, abs_neg]
  rcases hre with hr | hr <;> rcases him with hi | hi
  · exact absurd (Subtype.ext (Complex.ext hr hi)) hne1
  · left
    apply Subtype.ext
    change (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ) =
      starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ)
    exact Complex.ext (by rw [Complex.conj_re]; exact hr) (by rw [Complex.conj_im]; exact hi)
  · right
    apply Subtype.ext
    change (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ) =
      1 - starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ)
    exact Complex.ext (by simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; exact hr)
      (by simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; rw [hi]; ring)
  · refine absurd (Subtype.ext ?_) hne2
    change (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ) = 1 - (primeTraceZeroMap σ ρ : ℂ)
    exact Complex.ext (by simp only [Complex.sub_re, Complex.one_re]; exact hr)
      (by simp only [Complex.sub_im, Complex.one_im]; rw [hi]; ring)

/-- A partial flip `σρ̄ = 1 − conj(σρ)` exchanges the centred weight and the ordinate up to
sign. -/
theorem primeTraceExponentHom_of_flip (σ : G) (ρ : XiDivisorSupport)
    (hf : primeTraceZeroMap σ (xiZeroConjEquiv ρ) =
      xiZeroReflectEquiv (xiZeroConjEquiv (primeTraceZeroMap σ ρ)))
    (hr : (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap σ ρ : ℂ).re = 1 - (ρ : ℂ).re) :
    (primeTraceExponentHom σ (primeTraceCentredWeight ρ) = primeTraceOrdinate ρ ∨
      primeTraceExponentHom σ (primeTraceCentredWeight ρ) = -primeTraceOrdinate ρ) ∧
    (primeTraceExponentHom σ (primeTraceOrdinate ρ) = primeTraceCentredWeight ρ ∨
      primeTraceExponentHom σ (primeTraceOrdinate ρ) = -primeTraceCentredWeight ρ) := by
  constructor
  · rw [primeTraceExponentHom_centredWeight, hf]
    rcases abs_eq_abs.1 (primeTraceZeroMap_height σ ρ) with hi | hi
    · left
      apply Subtype.ext
      change (primeTraceZeroMap σ ρ : ℂ) -
          (1 - (1 - starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ))) = (ρ : ℂ) - starRingEnd ℂ (ρ : ℂ)
      apply Complex.ext <;>
        simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
          Complex.conj_re, Complex.conj_im] <;> linarith only [hi]
    · right
      apply Subtype.ext
      change (primeTraceZeroMap σ ρ : ℂ) -
          (1 - (1 - starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ))) =
        -((ρ : ℂ) - starRingEnd ℂ (ρ : ℂ))
      apply Complex.ext <;>
        simp only [Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im] <;>
        linarith only [hi]
  · rw [primeTraceExponentHom_ordinate, hf]
    rcases hr with hr | hr
    · left
      apply Subtype.ext
      change (primeTraceZeroMap σ ρ : ℂ) - (1 - starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ)) =
        (ρ : ℂ) - (1 - starRingEnd ℂ (ρ : ℂ))
      apply Complex.ext <;>
        simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
          Complex.conj_re, Complex.conj_im] <;> linarith only [hr]
    · right
      apply Subtype.ext
      change (primeTraceZeroMap σ ρ : ℂ) - (1 - starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ)) =
        -((ρ : ℂ) - (1 - starRingEnd ℂ (ρ : ℂ)))
      apply Complex.ext <;>
        simp only [Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im] <;>
        linarith only [hr]

/-- A partial flip exchanges the ordinate value and the width value. -/
theorem primeOrdinateValue_map_of_flip (p : Nat.Primes) (σ : G) (ρ : XiDivisorSupport)
    (hf : primeTraceZeroMap σ (xiZeroConjEquiv ρ) =
      xiZeroReflectEquiv (xiZeroConjEquiv (primeTraceZeroMap σ ρ)))
    (hr : (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap σ ρ : ℂ).re = 1 - (ρ : ℂ).re) :
    σ (primeOrdinateValue p ρ) = primeWidthValue p ρ ∧
      σ (primeWidthValue p ρ) = primeOrdinateValue p ρ :=
  ⟨primeTraceExponentValue_pair_map p (primeTraceExponentHom_of_flip σ ρ hf hr).2,
    primeTraceExponentValue_pair_map p (primeTraceExponentHom_of_flip σ ρ hf hr).1⟩

/-- If the orbit lies in the quartet, each automorphism fixes `u` and `v` or exchanges them. -/
theorem primeTraceZeroMap_values_of_quartet (p : Nat.Primes) (ρ : XiDivisorSupport)
    (h : ∀ τ : G, (primeTraceZeroMap τ ρ : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap τ ρ : ℂ).re = 1 - (ρ : ℂ).re) (σ : G) :
    (σ (primeOrdinateValue p ρ) = primeOrdinateValue p ρ ∧
      σ (primeWidthValue p ρ) = primeWidthValue p ρ) ∨
    (σ (primeOrdinateValue p ρ) = primeWidthValue p ρ ∧
      σ (primeWidthValue p ρ) = primeOrdinateValue p ρ) := by
  by_cases hβ : (ρ : ℂ).re = 1 / 2
  · have hw : (primeWeightValue p ρ : ℂ) ∈ B :=
      primeWeightValue_mem_of_rational p ρ ⟨1 / 2, by rw [hβ]; norm_num⟩
    exact Or.inl ⟨(coe_mem_primeTraceField_iff_fixed _).1
        (primeOrdinateValue_mem_of_weight_mem p p ρ hw) σ,
      (coe_mem_primeTraceField_iff_fixed _).1 (primeWidthValue_mem_of_weight_mem p p ρ hw) σ⟩
  rcases primeTraceZeroMap_conj_or_flip ρ h hβ σ with hc | hf
  · exact Or.inl ⟨primeTraceExponentValue_pair_map p
        (primeTraceExponentHom_ordinate_of_conj σ ρ hc), primeTraceExponentValue_pair_map p
        (primeTraceExponentHom_centredWeight_of_conj σ ρ hc (h σ))⟩
  · exact Or.inr (primeOrdinateValue_map_of_flip p σ ρ hf (h σ))

/-! ## The criterion -/

/-- **The quartet criterion.** For one prime `p`: the sum and the product of the ordinate value
`u = 2 cos(2γ log p)` and the width value `v = p^{2β−1} + p^{1−2β}` of `ρ` lie in `B` iff every
arithmetic automorphism sends `ρ` into its quartet `{ρ, ρ̄, 1 − ρ, 1 − ρ̄}`. -/
theorem sum_prod_mem_iff_mem_quartet (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (((primeOrdinateValue p ρ + primeWidthValue p ρ : E) : ℂ) ∈ B ∧
      ((primeOrdinateValue p ρ * primeWidthValue p ρ : E) : ℂ) ∈ B) ↔
    ∀ σ : G, primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroConjEquiv ρ ∨
      primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ ∨
        primeTraceZeroMap σ ρ = xiZeroReflectEquiv (xiZeroConjEquiv ρ) := by
  rw [forall_congr' fun σ => mem_quartet_iff_re σ ρ]
  constructor
  · rintro ⟨hs, hp⟩ σ
    exact primeTraceZeroMap_re_of_sum_prod_fixed p ρ σ
      ((coe_mem_primeTraceField_iff_fixed _).1 hs σ) ((coe_mem_primeTraceField_iff_fixed _).1 hp σ)
  · intro h
    constructor
    · refine (coe_mem_primeTraceField_iff_fixed _).2 fun σ => ?_
      rcases primeTraceZeroMap_values_of_quartet p ρ h σ with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rw [map_add, hu, hv]
      · rw [map_add, hu, hv, add_comm]
    · refine (coe_mem_primeTraceField_iff_fixed _).2 fun σ => ?_
      rcases primeTraceZeroMap_values_of_quartet p ρ h σ with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rw [map_mul, hu, hv]
      · rw [map_mul, hu, hv, mul_comm]

/-! ## Partial flips -/

/-- If the orbit lies in the quartet, the ordinate value lies in `B` iff the width value does. -/
theorem primeOrdinateValue_mem_iff_width_mem (p : Nat.Primes) (ρ : XiDivisorSupport)
    (h : ∀ σ : G, (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap σ ρ : ℂ).re = 1 - (ρ : ℂ).re) :
    (primeOrdinateValue p ρ : ℂ) ∈ B ↔ (primeWidthValue p ρ : ℂ) ∈ B := by
  simp only [coe_mem_primeTraceField_iff_fixed]
  constructor
  · intro hu σ
    rcases primeTraceZeroMap_values_of_quartet p ρ h σ with ⟨-, hv⟩ | ⟨h1, h2⟩
    · exact hv
    · rw [h2, ← h1, hu σ]
  · intro hv σ
    rcases primeTraceZeroMap_values_of_quartet p ρ h σ with ⟨hu, -⟩ | ⟨h1, h2⟩
    · exact hu
    · rw [h1, ← h2, hv σ]

/-- **Partial flips.** If the orbit of an off-line zero lies in its quartet, some arithmetic
automorphism acts on `ρ, ρ̄` as a partial flip, `σρ̄ = 1 − conj(σρ)`, iff the ordinate value of
`ρ` does not lie in `B`. -/
theorem exists_partialFlip_iff (p : Nat.Primes) (ρ : XiDivisorSupport)
    (h : ∀ σ : G, (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap σ ρ : ℂ).re = 1 - (ρ : ℂ).re) (hβ : (ρ : ℂ).re ≠ 1 / 2) :
    (∃ σ : G, primeTraceZeroMap σ (xiZeroConjEquiv ρ) =
      xiZeroReflectEquiv (xiZeroConjEquiv (primeTraceZeroMap σ ρ))) ↔
      (primeOrdinateValue p ρ : ℂ) ∉ B := by
  constructor
  · rintro ⟨σ, hf⟩ hu
    rw [(primeOrdinateValue_mem_iff_conj p ρ).1 hu σ] at hf
    have hr := congrArg (fun z : XiDivisorSupport => (z : ℂ).re) hf
    change (starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ)).re =
      (1 - starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ)).re at hr
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re] at hr
    rcases h σ with h1 | h1 <;> exact hβ (by linarith only [hr, h1])
  · intro hu
    by_contra hn
    exact hu ((primeOrdinateValue_mem_iff_conj p ρ).2 fun σ =>
      (primeTraceZeroMap_conj_or_flip ρ h hβ σ).resolve_right fun hf => hn ⟨σ, hf⟩)

end GaloisForLFunctions.GaloisTheoryOfZeros
