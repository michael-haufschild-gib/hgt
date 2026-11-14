import GaloisForLFunctions.GaloisTheoryOfZeros.ConjugationIsCentralAtAZeroIffItsOrdinateValueLiesInThePrimeTraceField

/-!
# The group acts on a zero through the two involutions iff its width value lies in `B`

`E` is the field of the prime values `p^ρ` of the zeros, `B` the prime trace field,
`G = Gal(E/B)`, `Δ` the integer span of the zeros. The *centred weight* of a zero `ρ = β + iγ` is
`ρ − (1 − ρ̄) = 2β − 1 ∈ Δ`; the *width value* is `p^{2β−1} + p^{1−2β}`, symmetric under the
reflection `β ↦ 1 − β`.

* **Width criterion** (`primeWidthValue_mem_iff`). For one prime `p`: `p^{2β−1} + p^{1−2β} ∈ B`
  iff every `σ ∈ G` carries `ρ̄` to the conjugate of `σρ` and `σρ` has real part `β` or
  `1 − β`. Equivalently (`primeTraceZeroMap_mem_quartet`) every `σ` agrees on `ρ, ρ̄` with one of
  `1`, `c`, `r`, `cr`: the group acts on the quartet `{ρ, ρ̄, 1 − ρ, 1 − ρ̄}` through the Klein
  group of the two involutions.
* **Chain** (`primeWidthValue_mem_of_weight_mem`, `primeOrdinateValue_mem_of_width_mem`).
  `p^{2β} ∈ B` ⇒ width value in `B` ⇒ ordinate value in `B`, at every prime.
* **Local reflection** (`exists_primeTraceZeroMap_eq_reflect`). If the width value lies in `B`
  and `p^{2β}` does not, some `σ` acts on `ρ, ρ̄` as the reflection `r`, and `Re ρ ≠ ½`.

Proof. `x = p^{2β−1}` is real. An automorphism fixing `x + x⁻¹` sends `x` to `x` or `x⁻¹`; the
stabilizer of `x` contains conjugation and keeps `Re(ρ + ρ̄)`, so by doubling it keeps `Re ρ`
and sends `ρ` into `{ρ, ρ̄}`. For any `σ`, `σ⁻¹cσ` fixes `x`, hence `c(σρ) ∈ {σρ, σρ̄}`; as `σρ`
is not real, `σρ̄ = conj(σρ)`, and then `2 Re σρ − 1 = ±(2β − 1)`.
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

/-! ## The centred weight and the width value -/

/-- The centred weight `ρ − (1 − ρ̄) = 2 Re ρ − 1` of a zero. -/
def primeTraceCentredWeight (ρ : XiDivisorSupport) : Δ :=
  primeTraceSupportRoot ρ - primeTraceSupportRoot (xiZeroReflectEquiv (xiZeroConjEquiv ρ))

theorem primeTraceCentredWeight_coe (ρ : XiDivisorSupport) :
    ((primeTraceCentredWeight ρ : Δ) : ℂ) = ((2 * (ρ : ℂ).re - 1 : ℝ) : ℂ) := by
  change (ρ : ℂ) - (1 - starRingEnd ℂ (ρ : ℂ)) = _
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

/-- The action on the centred weight: `σ(ρ − (1 − ρ̄)) = σρ − (1 − σρ̄)`. -/
theorem primeTraceExponentHom_centredWeight (σ : G) (ρ : XiDivisorSupport) :
    primeTraceExponentHom σ (primeTraceCentredWeight ρ) =
      primeTraceSupportRoot (primeTraceZeroMap σ ρ) -
        primeTraceSupportRoot (xiZeroReflectEquiv (primeTraceZeroMap σ (xiZeroConjEquiv ρ))) := by
  rw [primeTraceCentredWeight, map_sub, primeTraceExponentHom_root, primeTraceExponentHom_root,
    primeTraceZeroMap_reflection]

theorem primeTraceExponentHom_centredWeight_re (σ : G) (ρ : XiDivisorSupport) :
    ((primeTraceExponentHom σ (primeTraceCentredWeight ρ) : Δ) : ℂ).re =
      (primeTraceZeroMap σ ρ : ℂ).re + (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).re - 1 := by
  rw [primeTraceExponentHom_centredWeight]
  change ((primeTraceZeroMap σ ρ : ℂ) - (1 - (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ))).re = _
  simp only [Complex.sub_re, Complex.one_re]
  ring

theorem primeTraceExponentHom_weight_re (σ : G) (ρ : XiDivisorSupport) :
    ((primeTraceExponentHom σ (primeTraceWeight ρ) : Δ) : ℂ).re =
      (primeTraceZeroMap σ ρ : ℂ).re + (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).re := by
  rw [primeTraceWeight, map_add, primeTraceExponentHom_root, primeTraceExponentHom_root]
  exact Complex.add_re _ _

/-- The width value `p^{2β−1} + p^{1−2β}` of a zero `ρ = β + iγ`. -/
def primeWidthValue (p : Nat.Primes) (ρ : XiDivisorSupport) : E :=
  primeTraceExponentValue p (primeTraceCentredWeight ρ) +
    primeTraceExponentValue p (-primeTraceCentredWeight ρ)

theorem primeWidthValue_coe (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeWidthValue p ρ : ℂ) = ((((p : ℕ) : ℝ) ^ (2 * (ρ : ℂ).re - 1) +
      ((p : ℕ) : ℝ) ^ (1 - 2 * (ρ : ℂ).re) : ℝ) : ℂ) := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have h1 : (primeWidthValue p ρ : ℂ) =
      Complex.exp ((Real.log (p : ℕ) : ℂ) * ((primeTraceCentredWeight ρ : Δ) : ℂ)) +
        Complex.exp ((Real.log (p : ℕ) : ℂ) * (-((primeTraceCentredWeight ρ : Δ) : ℂ))) := rfl
  rw [h1, primeTraceCentredWeight_coe, Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp,
    Complex.ofReal_add, Complex.ofReal_exp, Complex.ofReal_exp]
  congr 2 <;> push_cast <;> ring

/-! ## Values, inverses and conjugation -/

theorem primeTraceExponentValue_mul_neg (p : Nat.Primes) (z : Δ) :
    primeTraceExponentValue p z * primeTraceExponentValue p (-z) = 1 := by
  apply Subtype.ext
  change Complex.exp ((Real.log (p : ℕ) : ℂ) * (z : ℂ)) *
    Complex.exp ((Real.log (p : ℕ) : ℂ) * (-(z : ℂ))) = 1
  rw [← Complex.exp_add, mul_neg, add_neg_cancel, Complex.exp_zero]

/-- If `σ(y + y') = x + x'` with `y y' = 1` and `x x' = 1`, then `σy` is `x` or `x'`. -/
theorem eq_or_eq_of_add_eq {σ : G} {x x' y y' : E} (hx : x * x' = 1) (hy : y * y' = 1)
    (h : σ (y + y') = x + x') : σ y = x ∨ σ y = x' := by
  have hy' : σ y * σ y' = 1 := by rw [← map_mul, hy, map_one]
  rw [map_add] at h
  have h0 : (σ y - x) * (σ y - x') = 0 := by
    linear_combination (σ y) * h - hy' + hx
  rcases mul_eq_zero.1 h0 with h0 | h0
  · exact Or.inl (sub_eq_zero.1 h0)
  · exact Or.inr (sub_eq_zero.1 h0)

/-- Equal prime values have equal real parts. -/
theorem primeTraceExponentHom_re_of_value_eq (p : Nat.Primes) {z z' : Δ} {σ : G}
    (h : σ (primeTraceExponentValue p z) = primeTraceExponentValue p z') :
    ((primeTraceExponentHom σ z : Δ) : ℂ).re = (z' : ℂ).re := by
  rw [← primeTraceExponentHom_value] at h
  have hc := congrArg (fun x : E => ‖(x : ℂ)‖) h
  simp only [norm_primeTraceExponentValue] at hc
  have hlog : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  exact mul_left_cancel₀ hlog.ne' (Real.exp_injective hc)

/-- Conjugation fixes the prime values of a real exponent. -/
theorem primeTraceConjugation_value_of_im (p : Nat.Primes) {z : Δ} (hz : (z : ℂ).im = 0) :
    primeTraceConjugation (primeTraceExponentValue p z) = primeTraceExponentValue p z := by
  apply Subtype.ext
  change starRingEnd ℂ (Complex.exp ((Real.log (p : ℕ) : ℂ) * (z : ℂ))) =
    Complex.exp ((Real.log (p : ℕ) : ℂ) * (z : ℂ))
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_eq_iff_im.2 hz]

theorem primeTraceCentredWeight_im (ρ : XiDivisorSupport) :
    ((primeTraceCentredWeight ρ : Δ) : ℂ).im = 0 := by
  rw [primeTraceCentredWeight_coe, Complex.ofReal_im]

theorem primeTraceCentredWeight_neg_im (ρ : XiDivisorSupport) :
    ((-primeTraceCentredWeight ρ : Δ) : ℂ).im = 0 := by
  rw [AddSubgroup.coe_neg, Complex.neg_im, primeTraceCentredWeight_im, neg_zero]

/-! ## The stabilizer of `p^{2β−1}` -/

/-- An automorphism that fixes `p^{2β−1}` keeps the real part of `ρ` and of `ρ̄`: the
stabilizer contains conjugation and keeps the real part of the weight, so doubling applies. -/
theorem primeTraceZeroMap_re_of_fixed_centred (p : Nat.Primes) (ρ : XiDivisorSupport) {τ : G}
    (hτ : τ (primeTraceExponentValue p (primeTraceCentredWeight ρ)) =
      primeTraceExponentValue p (primeTraceCentredWeight ρ)) :
    (primeTraceZeroMap τ ρ : ℂ).re = (ρ : ℂ).re := by
  let K : Subgroup G :=
    MulAction.stabilizer G (primeTraceExponentValue p (primeTraceCentredWeight ρ))
  have hK : ∀ σ : G, σ ∈ K ↔ σ (primeTraceExponentValue p (primeTraceCentredWeight ρ)) =
      primeTraceExponentValue p (primeTraceCentredWeight ρ) := fun σ =>
    MulAction.mem_stabilizer_iff
  refine primeTraceZeroMap_re_of_weight_re_of_mem ρ K
    ((hK _).2 (primeTraceConjugation_value_of_im p (primeTraceCentredWeight_im ρ)))
    (fun σ hσ => ?_) ((hK τ).2 hτ)
  have h := primeTraceExponentHom_re_of_value_eq p ((hK σ).1 hσ)
  rw [primeTraceExponentHom_centredWeight_re, primeTraceCentredWeight_coe,
    Complex.ofReal_re] at h
  rw [primeTraceExponentHom_weight_re]
  linarith only [h]

/-! ## The criterion -/

/-- An automorphism that fixes the width value carries `ρ̄` to the conjugate of `σρ`, and `σρ`
has real part `β` or `1 − β`. -/
theorem primeTraceZeroMap_of_width_fixed (p : Nat.Primes) (ρ : XiDivisorSupport)
    (h : ∀ σ : G, σ (primeWidthValue p ρ) = primeWidthValue p ρ) (σ : G) :
    primeTraceZeroMap σ (xiZeroConjEquiv ρ) = xiZeroConjEquiv (primeTraceZeroMap σ ρ) ∧
      ((primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re ∨
        (primeTraceZeroMap σ ρ : ℂ).re = 1 - (ρ : ℂ).re) := by
  set x := primeTraceExponentValue p (primeTraceCentredWeight ρ)
  set x' := primeTraceExponentValue p (-primeTraceCentredWeight ρ)
  have hxx : x * x' = 1 := primeTraceExponentValue_mul_neg p _
  have hcx : primeTraceConjugation x = x :=
    primeTraceConjugation_value_of_im p (primeTraceCentredWeight_im ρ)
  have hcx' : primeTraceConjugation x' = x' :=
    primeTraceConjugation_value_of_im p (primeTraceCentredWeight_neg_im ρ)
  have hσx := eq_or_eq_of_add_eq hxx hxx (h σ)
  -- `k = σ⁻¹cσ` fixes `x`
  have hcσ : primeTraceConjugation (σ x) = σ x := by
    rcases hσx with e | e <;> rw [e]
    · exact hcx
    · exact hcx'
  have hk : (σ⁻¹ * primeTraceConjugation * σ) x = x := by
    change σ⁻¹ (primeTraceConjugation (σ x)) = x
    rw [hcσ]
    exact σ.symm_apply_apply x
  -- `kρ ∈ {ρ, ρ̄}`
  have hre := primeTraceZeroMap_re_of_fixed_centred p ρ hk
  have hkρ : primeTraceZeroMap (σ⁻¹ * primeTraceConjugation * σ) ρ = ρ ∨
      primeTraceZeroMap (σ⁻¹ * primeTraceConjugation * σ) ρ = xiZeroConjEquiv ρ := by
    rcases abs_eq_abs.1 (primeTraceZeroMap_height (σ⁻¹ * primeTraceConjugation * σ) ρ) with
      hi | hi
    · exact Or.inl (Subtype.ext (Complex.ext hre hi))
    · refine Or.inr (Subtype.ext (Complex.ext ?_ ?_))
      · exact hre.trans (Complex.conj_re (ρ : ℂ)).symm
      · exact hi.trans (Complex.conj_im (ρ : ℂ)).symm
  -- `c(σρ) = σ(kρ) ∈ {σρ, σρ̄}`
  have hσk : primeTraceZeroMap σ (primeTraceZeroMap (σ⁻¹ * primeTraceConjugation * σ) ρ) =
      xiZeroConjEquiv (primeTraceZeroMap σ ρ) := by
    rw [← primeTraceZeroMap_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
      primeTraceZeroMap_mul, primeTraceZeroMap_conjugation]
  have hconj : primeTraceZeroMap σ (xiZeroConjEquiv ρ) =
      xiZeroConjEquiv (primeTraceZeroMap σ ρ) := by
    rcases hkρ with e | e
    · rw [e] at hσk
      have him := congrArg (fun z : XiDivisorSupport => (z : ℂ).im) hσk
      change (primeTraceZeroMap σ ρ : ℂ).im = (starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ)).im
        at him
      rw [Complex.conj_im] at him
      exact (xi_divisor_support_im_ne_zero (primeTraceZeroMap σ ρ) (by linarith only [him])).elim
    · rwa [e] at hσk
  refine ⟨hconj, ?_⟩
  have hσc : ((primeTraceZeroMap σ (xiZeroConjEquiv ρ)) : ℂ).re =
      (primeTraceZeroMap σ ρ : ℂ).re := by
    rw [hconj]
    exact Complex.conj_re _
  rcases hσx with e | e
  · left
    have h1 := primeTraceExponentHom_re_of_value_eq p e
    rw [primeTraceExponentHom_centredWeight_re, primeTraceCentredWeight_coe,
      Complex.ofReal_re, hσc] at h1
    linarith only [h1]
  · right
    have h1 := primeTraceExponentHom_re_of_value_eq p e
    rw [primeTraceExponentHom_centredWeight_re, AddSubgroup.coe_neg, Complex.neg_re,
      primeTraceCentredWeight_coe, Complex.ofReal_re, hσc] at h1
    linarith only [h1]

/-- If `σ` carries `ρ̄` to the conjugate of `σρ` and `σρ` has real part `β` or `1 − β`, it sends
the centred weight to `±` itself. -/
theorem primeTraceExponentHom_centredWeight_of_conj (σ : G) (ρ : XiDivisorSupport)
    (hc : primeTraceZeroMap σ (xiZeroConjEquiv ρ) = xiZeroConjEquiv (primeTraceZeroMap σ ρ))
    (hr : (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap σ ρ : ℂ).re = 1 - (ρ : ℂ).re) :
    primeTraceExponentHom σ (primeTraceCentredWeight ρ) = primeTraceCentredWeight ρ ∨
      primeTraceExponentHom σ (primeTraceCentredWeight ρ) = -primeTraceCentredWeight ρ := by
  rw [primeTraceExponentHom_centredWeight, hc]
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

/-- **The width criterion.** For one prime `p`: the width value `p^{2β−1} + p^{1−2β}` of a zero
`ρ = β + iγ` lies in `B` iff every arithmetic automorphism carries `ρ̄` to the conjugate of the
image of `ρ`, and this image has real part `β` or `1 − β`. -/
theorem primeWidthValue_mem_iff (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeWidthValue p ρ : ℂ) ∈ B ↔ ∀ σ : G,
      primeTraceZeroMap σ (xiZeroConjEquiv ρ) = xiZeroConjEquiv (primeTraceZeroMap σ ρ) ∧
        ((primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re ∨
          (primeTraceZeroMap σ ρ : ℂ).re = 1 - (ρ : ℂ).re) := by
  constructor
  · intro h
    exact primeTraceZeroMap_of_width_fixed p ρ ((coe_mem_primeTraceField_iff_fixed _).1 h)
  · intro h
    exact (coe_mem_primeTraceField_iff_fixed _).2 fun σ => primeTraceExponentValue_pair_map p
      (primeTraceExponentHom_centredWeight_of_conj σ ρ (h σ).1 (h σ).2)

/-- Membership of the width value does not depend on the prime. -/
theorem primeWidthValue_mem_iff_mem (p q : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeWidthValue p ρ : ℂ) ∈ B ↔ (primeWidthValue q ρ : ℂ) ∈ B :=
  (primeWidthValue_mem_iff p ρ).trans (primeWidthValue_mem_iff q ρ).symm

/-- An image of `ρ` with real part `β` or `1 − β` lies in the quartet `{ρ, ρ̄, 1 − ρ, 1 − ρ̄}`. -/
theorem primeTraceZeroMap_mem_quartet_of_re (σ : G) (ρ : XiDivisorSupport)
    (hr : (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re ∨
      (primeTraceZeroMap σ ρ : ℂ).re = 1 - (ρ : ℂ).re) :
    primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroConjEquiv ρ ∨
      primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ ∨
        primeTraceZeroMap σ ρ = xiZeroReflectEquiv (xiZeroConjEquiv ρ) := by
  have hi := abs_eq_abs.1 (primeTraceZeroMap_height σ ρ)
  have e1 : (xiZeroConjEquiv ρ : ℂ) = starRingEnd ℂ (ρ : ℂ) := rfl
  have e2 : (xiZeroReflectEquiv ρ : ℂ) = 1 - (ρ : ℂ) := rfl
  have e3 : (xiZeroReflectEquiv (xiZeroConjEquiv ρ) : ℂ) = 1 - starRingEnd ℂ (ρ : ℂ) := rfl
  rcases hr with hr | hr <;> rcases hi with hi | hi
  · exact Or.inl (Subtype.ext (Complex.ext hr hi))
  · refine Or.inr (Or.inl (Subtype.ext ?_))
    rw [e1]
    exact Complex.ext (by rw [Complex.conj_re]; exact hr) (by rw [Complex.conj_im]; exact hi)
  · refine Or.inr (Or.inr (Or.inr (Subtype.ext ?_)))
    rw [e3]
    exact Complex.ext (by simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; exact hr)
      (by simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; rw [hi]; ring)
  · refine Or.inr (Or.inr (Or.inl (Subtype.ext ?_)))
    rw [e2]
    exact Complex.ext (by simp only [Complex.sub_re, Complex.one_re]; exact hr)
      (by simp only [Complex.sub_im, Complex.one_im]; rw [hi]; ring)

/-- **The quartet form.** If the width value lies in `B`, every automorphism sends `ρ` into the
quartet `{ρ, ρ̄, 1 − ρ, 1 − ρ̄}`, and `ρ̄` to the conjugate of the image. -/
theorem primeTraceZeroMap_mem_quartet (p : Nat.Primes) (ρ : XiDivisorSupport)
    (h : (primeWidthValue p ρ : ℂ) ∈ B) (σ : G) :
    primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroConjEquiv ρ ∨
      primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ ∨
        primeTraceZeroMap σ ρ = xiZeroReflectEquiv (xiZeroConjEquiv ρ) :=
  primeTraceZeroMap_mem_quartet_of_re σ ρ ((primeWidthValue_mem_iff p ρ).1 h σ).2

/-! ## The chain weight ⇒ width ⇒ ordinate -/

/-- If `p^{2 Re ρ} ∈ B`, the width value of `ρ` lies in `B` at every prime. -/
theorem primeWidthValue_mem_of_weight_mem (p q : Nat.Primes) (ρ : XiDivisorSupport)
    (h : (primeWeightValue p ρ : ℂ) ∈ B) : (primeWidthValue q ρ : ℂ) ∈ B :=
  (primeWidthValue_mem_iff q ρ).2 fun σ =>
    ⟨(primeOrdinateValue_mem_iff_conj q ρ).1 (primeOrdinateValue_mem_of_weight_mem p q ρ h) σ,
      Or.inl ((primeWeightValue_mem_iff_re p ρ).1 h σ)⟩

/-- If the width value of `ρ` lies in `B`, so does its ordinate value, at every prime. -/
theorem primeOrdinateValue_mem_of_width_mem (p q : Nat.Primes) (ρ : XiDivisorSupport)
    (h : (primeWidthValue p ρ : ℂ) ∈ B) : (primeOrdinateValue q ρ : ℂ) ∈ B :=
  (primeOrdinateValue_mem_iff_conj q ρ).2 fun σ => ((primeWidthValue_mem_iff p ρ).1 h σ).1

/-! ## The reflection on one quartet -/

/-- **Local reflection.** If the width value of `ρ` lies in `B` and `p^{2 Re ρ}` does not, some
arithmetic automorphism acts on `ρ, ρ̄` as the reflection `r`, and `ρ` is off the line. -/
theorem exists_primeTraceZeroMap_eq_reflect (p : Nat.Primes) (ρ : XiDivisorSupport)
    (hw : (primeWidthValue p ρ : ℂ) ∈ B) (hq : (primeWeightValue p ρ : ℂ) ∉ B) :
    (∃ σ : G, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ ∧
      primeTraceZeroMap σ (xiZeroConjEquiv ρ) = xiZeroReflectEquiv (xiZeroConjEquiv ρ)) ∧
      (ρ : ℂ).re ≠ 1 / 2 := by
  obtain ⟨σ, hσ⟩ := (exists_re_ne_iff_primeWeightValue_not_mem p ρ).2 hq
  have hcrit : (ρ : ℂ).re ≠ 1 / 2 := by
    intro hc
    exact hq (primeWeightValue_mem_of_rational p ρ ⟨1 / 2, by rw [hc]; norm_num⟩)
  refine ⟨?_, hcrit⟩
  have hc := fun τ : G => ((primeWidthValue_mem_iff p ρ).1 hw τ).1
  rcases primeTraceZeroMap_mem_quartet p ρ hw σ with e | e | e | e
  · exact (hσ (by rw [e])).elim
  · exact (hσ (by rw [e]; exact Complex.conj_re _)).elim
  · refine ⟨σ, e, ?_⟩
    rw [hc σ, e]
    apply Subtype.ext
    change starRingEnd ℂ (1 - (ρ : ℂ)) = 1 - starRingEnd ℂ (ρ : ℂ)
    rw [map_sub, map_one]
  · refine ⟨primeTraceConjugation * σ, ?_, ?_⟩
    · rw [primeTraceZeroMap_mul, primeTraceZeroMap_conjugation, e]
      apply Subtype.ext
      change starRingEnd ℂ (1 - starRingEnd ℂ (ρ : ℂ)) = 1 - (ρ : ℂ)
      rw [map_sub, map_one, Complex.conj_conj]
    · rw [primeTraceZeroMap_mul, primeTraceZeroMap_conjugation, hc σ, e]
      apply Subtype.ext
      change starRingEnd ℂ (starRingEnd ℂ (1 - starRingEnd ℂ (ρ : ℂ))) =
        1 - starRingEnd ℂ (ρ : ℂ)
      rw [Complex.conj_conj]

end GaloisForLFunctions.GaloisTheoryOfZeros
