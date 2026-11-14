import GaloisForLFunctions.GaloisTheoryOfZeros.TheDegreeOfTheResidueFieldOfAZeroIsTheSizeOfItsOrbit

/-!
# A lift of the reflection is conjugation exactly where the weight lies in `B`

`B` is the prime trace field and `G = Gal(E/B)` acts on the zeros. Two problems of the programme
meet here: whether the reflection `r : ρ ↦ 1 − ρ` lifts to an element of `G` (decided by the
parity of the square relations among the reflection radicands), and whether the weight value
`p^{2 Re ρ}` lies in `B` (decided by the orbit of `ρ`). Neither alone forces `Re ρ = ½`.

* **Criticality splits** (`re_eq_half_iff_weight_mem_and_reflect`). For one prime `p`:
  `Re ρ = ½` iff `p^{2 Re ρ} ∈ B` and some `σ ∈ G` sends `ρ` to `1 − ρ`.
* **RH splits** (`forall_re_eq_half_iff`). All zeros are critical iff `r` lifts to `G` and every
  weight value lies in `B`.
* **Identification of a lift** (`lift_eq_conjugation_at_iff`, `lift_eq_conjugation_iff`). If `σ`
  lifts `r`, then `σρ = ρ̄` iff `p^{2 Re ρ} ∈ B`; `σ` is conjugation iff every weight value lies
  in `B`.
* **The mirror element** (`conjugation_mul_lift_fixed_iff`). If `σ` lifts `r`, the element `cσ`
  acts as `ρ ↦ 1 − ρ̄`; its fixed zeros are exactly the critical ones, so RH iff `cσ = 1`.

Proof. A weight in `B` confines the orbit of `ρ` to `{ρ, ρ̄}`; `1 − ρ ≠ ρ`, and `1 − ρ = ρ̄` iff
`Re ρ = ½`.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local instance : IsGalois B E := ⟨⟩

/-- `ρ̄ = 1 − ρ` iff `ρ` is critical. -/
theorem xiZeroConjEquiv_eq_reflect_iff (ρ : XiDivisorSupport) :
    xiZeroConjEquiv ρ = xiZeroReflectEquiv ρ ↔ (ρ : ℂ).re = 1 / 2 := by
  constructor
  · intro e
    have hr := congrArg (fun z : XiDivisorSupport => (z : ℂ).re) e
    change (starRingEnd ℂ (ρ : ℂ)).re = (1 - (ρ : ℂ)).re at hr
    rw [Complex.conj_re, Complex.sub_re, Complex.one_re] at hr
    linarith only [hr]
  · intro h
    apply Subtype.ext
    change starRingEnd ℂ (ρ : ℂ) = 1 - (ρ : ℂ)
    apply Complex.ext
    · rw [Complex.conj_re, Complex.sub_re, Complex.one_re]
      linarith only [h]
    · rw [Complex.conj_im, Complex.sub_im, Complex.one_im, zero_sub]

/-- **Criticality splits.** For one prime `p`: `Re ρ = ½` iff `p^{2 Re ρ} ∈ B` and some arithmetic
automorphism sends `ρ` to `1 − ρ`. -/
theorem re_eq_half_iff_weight_mem_and_reflect (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (ρ : ℂ).re = 1 / 2 ↔ (primeWeightValue p ρ : ℂ) ∈ B ∧
      ∃ σ : G, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ := by
  constructor
  · intro h
    refine ⟨primeWeightValue_mem_of_rational p ρ ⟨1 / 2, by rw [h]; norm_num⟩,
      primeTraceConjugation, ?_⟩
    rw [primeTraceZeroMap_conjugation]
    exact (xiZeroConjEquiv_eq_reflect_iff ρ).2 h
  · rintro ⟨hw, σ, hσ⟩
    rcases (primeWeightValue_mem_iff_orbit p ρ).1 hw σ with e | e <;> rw [hσ] at e
    · have hi := congrArg (fun z : XiDivisorSupport => (z : ℂ).im) e
      change (1 - (ρ : ℂ)).im = (ρ : ℂ).im at hi
      rw [Complex.sub_im, Complex.one_im] at hi
      exact (xi_divisor_support_im_ne_zero ρ (by linarith only [hi])).elim
    · exact (xiZeroConjEquiv_eq_reflect_iff ρ).1 e.symm

/-- **RH splits** into the reflection lift and the weights: all zeros are critical iff the
reflection lifts to the arithmetic group and every weight value lies in `B`. -/
theorem forall_re_eq_half_iff (p : Nat.Primes) :
    (∀ ρ : XiDivisorSupport, (ρ : ℂ).re = 1 / 2) ↔
      (∃ σ : G, ∀ ρ, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ) ∧
        ∀ ρ : XiDivisorSupport, (primeWeightValue p ρ : ℂ) ∈ B := by
  constructor
  · intro h
    refine ⟨⟨primeTraceConjugation, fun ρ => ?_⟩, fun ρ =>
      ((re_eq_half_iff_weight_mem_and_reflect p ρ).1 (h ρ)).1⟩
    rw [primeTraceZeroMap_conjugation]
    exact (xiZeroConjEquiv_eq_reflect_iff ρ).2 (h ρ)
  · rintro ⟨⟨σ, hσ⟩, hw⟩ ρ
    exact (re_eq_half_iff_weight_mem_and_reflect p ρ).2 ⟨hw ρ, σ, hσ ρ⟩

/-! ## Identification of a lift -/

section Lift

variable {σ : G} (hσ : ∀ ρ, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ)
include hσ

/-- A lift of the reflection agrees with conjugation at `ρ` iff `p^{2 Re ρ} ∈ B`. -/
theorem lift_eq_conjugation_at_iff (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeTraceZeroMap σ ρ = primeTraceZeroMap primeTraceConjugation ρ ↔
      (primeWeightValue p ρ : ℂ) ∈ B := by
  rw [hσ ρ, primeTraceZeroMap_conjugation, eq_comm, xiZeroConjEquiv_eq_reflect_iff]
  exact ⟨fun h => ((re_eq_half_iff_weight_mem_and_reflect p ρ).1 h).1,
    fun hw => (re_eq_half_iff_weight_mem_and_reflect p ρ).2 ⟨hw, σ, hσ ρ⟩⟩

/-- **Identification of a lift.** A lift of the reflection is conjugation iff every weight value
lies in `B`. -/
theorem lift_eq_conjugation_iff (p : Nat.Primes) :
    σ = primeTraceConjugation ↔ ∀ ρ : XiDivisorSupport, (primeWeightValue p ρ : ℂ) ∈ B := by
  constructor
  · rintro rfl ρ
    exact (lift_eq_conjugation_at_iff hσ p ρ).1 rfl
  · intro hw
    apply primeTraceGaloisAction_injective
    exact Equiv.ext fun ρ => (lift_eq_conjugation_at_iff hσ p ρ).2 (hw ρ)

/-- **The mirror element.** If `σ` lifts the reflection, `cσ` sends `ρ` to `1 − ρ̄` and fixes
exactly the critical zeros. -/
theorem conjugation_mul_lift_fixed_iff (ρ : XiDivisorSupport) :
    primeTraceZeroMap (primeTraceConjugation * σ) ρ = ρ ↔ (ρ : ℂ).re = 1 / 2 := by
  rw [primeTraceZeroMap_mul, hσ ρ, primeTraceZeroMap_conjugation]
  constructor
  · intro e
    have hr := congrArg (fun z : XiDivisorSupport => (z : ℂ).re) e
    change (starRingEnd ℂ (1 - (ρ : ℂ))).re = (ρ : ℂ).re at hr
    rw [Complex.conj_re, Complex.sub_re, Complex.one_re] at hr
    linarith only [hr]
  · intro h
    apply Subtype.ext
    change starRingEnd ℂ (1 - (ρ : ℂ)) = (ρ : ℂ)
    apply Complex.ext
    · rw [Complex.conj_re, Complex.sub_re, Complex.one_re]
      linarith only [h]
    · rw [Complex.conj_im, Complex.sub_im, Complex.one_im, zero_sub, neg_neg]

/-- If the reflection lifts to `σ`, all zeros are critical iff `cσ = 1`. -/
theorem forall_re_eq_half_iff_conjugation_mul_lift_eq_one :
    (∀ ρ : XiDivisorSupport, (ρ : ℂ).re = 1 / 2) ↔ primeTraceConjugation * σ = 1 := by
  constructor
  · intro h
    apply primeTraceGaloisAction_injective
    refine Equiv.ext fun ρ => ?_
    rw [map_one]
    exact (conjugation_mul_lift_fixed_iff hσ ρ).2 (h ρ)
  · intro h ρ
    refine (conjugation_mul_lift_fixed_iff hσ ρ).1 ?_
    rw [h, primeTraceZeroMap_one]

end Lift

end GaloisForLFunctions.GaloisTheoryOfZeros
