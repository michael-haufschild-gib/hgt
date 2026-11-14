import GaloisForLFunctions.GaloisTheoryOfZeros.TheRationalWeightsOfPrimeZeroOrbits

/-!
# The orbit of a zero is its conjugate pair iff its weight lies in the prime trace field

`E` is the field of the prime values `p^ρ` of the zeros, `B` the prime trace field,
`G = Gal(E/B)`. The group acts on the zeros and keeps the absolute ordinate. The *weight* of a
zero is `ρ + ρ̄ = 2 Re ρ`, an element of the integer span `Δ` of the zeros; its prime values are
the positive real numbers `p^{2 Re ρ}`.

* **One prime fixes the real part of the weight** (`primeTraceWeight_re_of_mem`). If
  `p^{2 Re ρ} ∈ B` for one prime, every `τ ∈ G` fixes this number; absolute values give
  `Re τ(ρ + ρ̄) = 2 Re ρ`.
* **Doubling** (`primeTraceZeroMap_re_of_weight_re`). Then `Re (τcτ⁻¹)ρ − Re ρ` is
  `± 2 (Re τρ − Re ρ)`, so the set of the displacements `|Re τρ − Re ρ|` is closed under
  doubling. It is bounded, hence zero.
* **Converse** (`primeTraceExponentHom_weight_of_re`). If every `σ` keeps the real part of `ρ`,
  then `τρ` and `τρ̄` are the two zeros `ρ`, `ρ̄`, and `τ` fixes the weight.

Hence (`primeWeightValue_mem_iff_orbit`): the orbit of `ρ` is contained in `{ρ, ρ̄}` iff
`p^{2 Re ρ} ∈ B`, for any one prime `p`. The orbit contains a zero of another real part iff
`p^{2 Re ρ} ∉ B` (`exists_re_ne_iff_primeWeightValue_not_mem`).
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

/-! ## The weight of a zero -/

/-- The weight `ρ + ρ̄ = 2 Re ρ` of a zero in the integer span of the zeros. -/
def primeTraceWeight (ρ : XiDivisorSupport) : Δ :=
  primeTraceSupportRoot ρ + primeTraceSupportRoot (xiZeroConjEquiv ρ)

theorem primeTraceWeight_coe (ρ : XiDivisorSupport) :
    ((primeTraceWeight ρ : Δ) : ℂ) = ((2 * (ρ : ℂ).re : ℝ) : ℂ) :=
  Complex.add_conj (ρ : ℂ)

/-- The prime value `p^{2 Re ρ}` of the weight of a zero. -/
def primeWeightValue (p : Nat.Primes) (ρ : XiDivisorSupport) : E :=
  primeTraceExponentValue p (primeTraceWeight ρ)

/-- The prime value of the weight is the positive real number `p^{2 Re ρ}`. -/
theorem primeWeightValue_coe (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeWeightValue p ρ : ℂ) = ((((p : ℕ) : ℝ) ^ (2 * (ρ : ℂ).re) : ℝ) : ℂ) := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [primeWeightValue, primeTraceExponentValue_coe, primeTraceWeight_coe,
    Real.rpow_def_of_pos hp, Complex.ofReal_exp, Complex.ofReal_mul]

/-! ## From the weight to the real part -/

/-- **One prime fixes the real part of the weight.** -/
theorem primeTraceWeight_re_of_mem (p : Nat.Primes) (ρ : XiDivisorSupport)
    (h : (primeWeightValue p ρ : ℂ) ∈ B) (τ : G) :
    ((primeTraceExponentHom τ (primeTraceWeight ρ) : Δ) : ℂ).re = 2 * (ρ : ℂ).re := by
  have hb : algebraMap B E ⟨(primeWeightValue p ρ : ℂ), h⟩ = primeWeightValue p ρ :=
    Subtype.ext rfl
  have hfix : τ (primeWeightValue p ρ) = primeWeightValue p ρ :=
    calc τ (primeWeightValue p ρ) = τ (algebraMap B E ⟨(primeWeightValue p ρ : ℂ), h⟩) := by
          rw [hb]
      _ = algebraMap B E ⟨(primeWeightValue p ρ : ℂ), h⟩ := τ.commutes _
      _ = primeWeightValue p ρ := hb
  have hval : primeTraceExponentValue p (primeTraceExponentHom τ (primeTraceWeight ρ)) =
      primeTraceExponentValue p (primeTraceWeight ρ) :=
    (primeTraceExponentHom_value τ p (primeTraceWeight ρ)).trans hfix
  have hc := congrArg (fun x : E => ‖(x : ℂ)‖) hval
  simp only [primeTraceExponentValue_coe, Complex.norm_exp, Complex.re_ofReal_mul] at hc
  have hlog : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  rw [mul_left_cancel₀ hlog.ne' (Real.exp_injective hc), primeTraceWeight_coe,
    Complex.ofReal_re]

/-- A bounded set of nonnegative reals closed under doubling is `{0}`. -/
private theorem doubling_set_eq_zero (S : Set ℝ) (hS : S.Nonempty) (hB : BddAbove S)
    (hd : ∀ x ∈ S, 2 * x ∈ S) (hn : ∀ x ∈ S, 0 ≤ x) : ∀ x ∈ S, x = 0 := by
  have hu : sSup S ≤ sSup S / 2 := by
    apply csSup_le hS
    intro x hx
    have he := le_csSup hB (hd x hx)
    linarith only [he]
  intro x hx
  have hx' := le_csSup hB hx
  exact le_antisymm (by linarith only [hu, hx']) (hn x hx)

/-- **Doubling.** If the real part of the weight is the same along its orbit, every arithmetic
automorphism keeps the real part of the zero. -/
theorem primeTraceZeroMap_re_of_weight_re (ρ : XiDivisorSupport)
    (hq : ∀ τ : G, ((primeTraceExponentHom τ (primeTraceWeight ρ) : Δ) : ℂ).re =
      2 * (ρ : ℂ).re) (σ : G) :
    (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re := by
  let S : Set ℝ := Set.range (fun τ : G => |(primeTraceZeroMap τ ρ : ℂ).re - (ρ : ℂ).re|)
  have hS : S.Nonempty := ⟨_, 1, rfl⟩
  have hB : BddAbove S := by
    refine ⟨1, ?_⟩
    rintro x ⟨τ, rfl⟩
    have ha := xi_divisor_support_re_mem_open_unit (primeTraceZeroMap τ ρ)
    have hb := xi_divisor_support_re_mem_open_unit ρ
    apply le_of_lt
    apply abs_lt.mpr
    constructor <;> linarith only [ha.1, ha.2, hb.1, hb.2]
  -- conjugating complex conjugation by `τ` doubles the displacement of `τ`
  have hd : ∀ x ∈ S, 2 * x ∈ S := by
    rintro x ⟨τ, rfl⟩
    let ζ := primeTraceZeroMap τ⁻¹ ρ
    have hinv : primeTraceZeroMap τ ζ = ρ := by
      dsimp only [ζ]
      rw [← primeTraceZeroMap_mul, mul_inv_cancel, primeTraceZeroMap_one]
    have he : primeTraceSupportRoot (primeTraceZeroMap (τ * primeTraceConjugation * τ⁻¹) ρ) =
        primeTraceExponentHom τ (primeTraceSupportRoot (xiZeroConjEquiv ζ)) := by
      rw [primeTraceExponentHom_root]
      congr 1
      rw [primeTraceZeroMap_mul, primeTraceZeroMap_mul, primeTraceZeroMap_conjugation]
    refine ⟨τ * primeTraceConjugation * τ⁻¹, ?_⟩
    change |(primeTraceZeroMap (τ * primeTraceConjugation * τ⁻¹) ρ : ℂ).re - (ρ : ℂ).re| =
      2 * |(primeTraceZeroMap τ ρ : ℂ).re - (ρ : ℂ).re|
    rcases abs_eq_abs.mp (primeTraceZeroMap_height τ⁻¹ ρ) with hi | hi
    · have hc : primeTraceSupportRoot (xiZeroConjEquiv ζ) =
          primeTraceSupportRoot ζ - (2 • primeTraceSupportRoot ρ - primeTraceWeight ρ) := by
        apply Subtype.ext
        change starRingEnd ℂ (ζ : ℂ) =
          (ζ : ℂ) - (2 • (ρ : ℂ) - ((ρ : ℂ) + starRingEnd ℂ (ρ : ℂ)))
        apply Complex.ext
        · simp only [two_nsmul, Complex.sub_re, Complex.add_re, Complex.conj_re]
          ring
        · change (ζ : ℂ).im = (ρ : ℂ).im at hi
          simp only [two_nsmul, Complex.sub_im, Complex.add_im, Complex.conj_im]
          linarith only [hi]
      rw [hc, map_sub, map_sub, map_nsmul, primeTraceExponentHom_root,
        primeTraceExponentHom_root, hinv] at he
      have hre := congrArg (fun z : Δ => (z : ℂ).re) he
      change (primeTraceZeroMap (τ * primeTraceConjugation * τ⁻¹) ρ : ℂ).re =
        ((ρ : ℂ) - (2 • (primeTraceZeroMap τ ρ : ℂ) -
          ((primeTraceExponentHom τ (primeTraceWeight ρ) : Δ) : ℂ))).re at hre
      simp only [two_nsmul, Complex.sub_re, Complex.add_re] at hre
      rw [hq τ] at hre
      have hd' : (primeTraceZeroMap (τ * primeTraceConjugation * τ⁻¹) ρ : ℂ).re - (ρ : ℂ).re =
          -(2 * ((primeTraceZeroMap τ ρ : ℂ).re - (ρ : ℂ).re)) := by linarith only [hre]
      rw [hd', abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    · have hc : primeTraceSupportRoot (xiZeroConjEquiv ζ) =
          primeTraceSupportRoot ζ + (2 • primeTraceSupportRoot ρ - primeTraceWeight ρ) := by
        apply Subtype.ext
        change starRingEnd ℂ (ζ : ℂ) =
          (ζ : ℂ) + (2 • (ρ : ℂ) - ((ρ : ℂ) + starRingEnd ℂ (ρ : ℂ)))
        apply Complex.ext
        · simp only [two_nsmul, Complex.sub_re, Complex.add_re, Complex.conj_re]
          ring
        · change (ζ : ℂ).im = -(ρ : ℂ).im at hi
          simp only [two_nsmul, Complex.sub_im, Complex.add_im, Complex.conj_im]
          linarith only [hi]
      rw [hc, map_add, map_sub, map_nsmul, primeTraceExponentHom_root,
        primeTraceExponentHom_root, hinv] at he
      have hre := congrArg (fun z : Δ => (z : ℂ).re) he
      change (primeTraceZeroMap (τ * primeTraceConjugation * τ⁻¹) ρ : ℂ).re =
        ((ρ : ℂ) + (2 • (primeTraceZeroMap τ ρ : ℂ) -
          ((primeTraceExponentHom τ (primeTraceWeight ρ) : Δ) : ℂ))).re at hre
      simp only [two_nsmul, Complex.sub_re, Complex.add_re] at hre
      rw [hq τ] at hre
      have hd' : (primeTraceZeroMap (τ * primeTraceConjugation * τ⁻¹) ρ : ℂ).re - (ρ : ℂ).re =
          2 * ((primeTraceZeroMap τ ρ : ℂ).re - (ρ : ℂ).re) := by linarith only [hre]
      rw [hd', abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hn : ∀ x ∈ S, 0 ≤ x := by
    rintro x ⟨τ, rfl⟩
    exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp (doubling_set_eq_zero S hS hB hd hn _ ⟨σ, rfl⟩))

/-! ## From the real part to the weight -/

/-- **Converse.** If every arithmetic automorphism keeps the real part of `ρ`, it carries the
pair `ρ, ρ̄` to itself and fixes the weight. -/
theorem primeTraceExponentHom_weight_of_re (ρ : XiDivisorSupport)
    (h : ∀ σ : G, (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re) (τ : G) :
    primeTraceExponentHom τ (primeTraceWeight ρ) = primeTraceWeight ρ := by
  have ha := h τ
  have hb : (primeTraceZeroMap τ (xiZeroConjEquiv ρ) : ℂ).re = (ρ : ℂ).re := by
    have := h (τ * primeTraceConjugation)
    rwa [primeTraceZeroMap_mul, primeTraceZeroMap_conjugation] at this
  have hia := primeTraceZeroMap_height τ ρ
  have hib : |(primeTraceZeroMap τ (xiZeroConjEquiv ρ) : ℂ).im| = |(ρ : ℂ).im| := by
    rw [primeTraceZeroMap_height]
    change |(starRingEnd ℂ (ρ : ℂ)).im| = _
    rw [Complex.conj_im, abs_neg]
  -- the two images are distinct zeros
  have hne : (primeTraceZeroMap τ ρ : ℂ).im ≠
      (primeTraceZeroMap τ (xiZeroConjEquiv ρ) : ℂ).im := by
    intro him
    have heq : primeTraceZeroMap τ ρ = primeTraceZeroMap τ (xiZeroConjEquiv ρ) :=
      Subtype.ext (Complex.ext (ha.trans hb.symm) him)
    have him' := congrArg (fun z : XiDivisorSupport => (z : ℂ).im)
      ((primeTraceZeroPermutation τ).injective heq)
    change (ρ : ℂ).im = (starRingEnd ℂ (ρ : ℂ)).im at him'
    rw [Complex.conj_im] at him'
    exact xi_divisor_support_im_ne_zero ρ (by linarith only [him'])
  have hsum : (primeTraceZeroMap τ ρ : ℂ).im +
      (primeTraceZeroMap τ (xiZeroConjEquiv ρ) : ℂ).im = 0 := by
    rcases abs_eq_abs.1 hia with h1 | h1 <;> rcases abs_eq_abs.1 hib with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
      ring
    · rw [h1, h2]
      ring
    · exact absurd (h1.trans h2.symm) hne
  apply Subtype.ext
  rw [primeTraceWeight, map_add, primeTraceExponentHom_root, primeTraceExponentHom_root]
  change (primeTraceZeroMap τ ρ : ℂ) + (primeTraceZeroMap τ (xiZeroConjEquiv ρ) : ℂ) =
    (ρ : ℂ) + starRingEnd ℂ (ρ : ℂ)
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re]
    rw [ha, hb]
  · simp only [Complex.add_im, Complex.conj_im]
    rw [hsum]
    ring

/-- A prime value of a fixed weight lies in the prime trace field. -/
theorem primeWeightValue_mem_of_fixed (p : Nat.Primes) (ρ : XiDivisorSupport)
    (h : ∀ τ : G, primeTraceExponentHom τ (primeTraceWeight ρ) = primeTraceWeight ρ) :
    (primeWeightValue p ρ : ℂ) ∈ B := by
  have hf : ∀ τ : G, τ (primeWeightValue p ρ) = primeWeightValue p ρ := fun τ => by
    rw [primeWeightValue, ← primeTraceExponentHom_value, h τ]
  obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (primeWeightValue p ρ)).mpr hf
  rw [← congrArg (fun v : E => (v : ℂ)) hb]
  exact b.property

/-! ## The criterion -/

/-- **The orbit of a zero is its conjugate pair iff its weight lies in the prime trace field.**
For one prime `p`: `p^{2 Re ρ} ∈ B` iff every arithmetic automorphism carries `ρ` to `ρ` or to
`ρ̄`. -/
theorem primeWeightValue_mem_iff_orbit (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeWeightValue p ρ : ℂ) ∈ B ↔
      ∀ σ : G, primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroConjEquiv ρ := by
  constructor
  · intro h σ
    have hre := primeTraceZeroMap_re_of_weight_re ρ (primeTraceWeight_re_of_mem p ρ h) σ
    rcases abs_eq_abs.mp (primeTraceZeroMap_height σ ρ) with hi | hi
    · exact Or.inl (Subtype.ext (Complex.ext hre hi))
    · exact Or.inr (Subtype.ext (Complex.ext hre hi))
  · intro h
    refine primeWeightValue_mem_of_fixed p ρ
      (primeTraceExponentHom_weight_of_re ρ fun σ => ?_)
    rcases h σ with hs | hs
    · rw [hs]
    · rw [hs]
      exact Complex.conj_re _

/-- The criterion in terms of real parts. -/
theorem primeWeightValue_mem_iff_re (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeWeightValue p ρ : ℂ) ∈ B ↔
      ∀ σ : G, (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re :=
  ⟨fun h => primeTraceZeroMap_re_of_weight_re ρ (primeTraceWeight_re_of_mem p ρ h),
    fun h => primeWeightValue_mem_of_fixed p ρ (primeTraceExponentHom_weight_of_re ρ h)⟩

/-- Membership of the weight does not depend on the prime. -/
theorem primeWeightValue_mem_iff_mem (p p' : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeWeightValue p ρ : ℂ) ∈ B ↔ (primeWeightValue p' ρ : ℂ) ∈ B :=
  (primeWeightValue_mem_iff_re p ρ).trans (primeWeightValue_mem_iff_re p' ρ).symm

/-- **The orbit of a zero contains a zero of another real part iff `p^{2 Re ρ} ∉ B`.** -/
theorem exists_re_ne_iff_primeWeightValue_not_mem (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (∃ σ : G, (primeTraceZeroMap σ ρ : ℂ).re ≠ (ρ : ℂ).re) ↔
      (primeWeightValue p ρ : ℂ) ∉ B := by
  rw [primeWeightValue_mem_iff_re p ρ]
  push Not
  rfl

/-- A zero with rational real part has its weight in the prime trace field. -/
theorem primeWeightValue_mem_of_rational (p : Nat.Primes) (ρ : XiDivisorSupport)
    (hr : ∃ r : ℚ, (ρ : ℂ).re = (r : ℝ)) : (primeWeightValue p ρ : ℂ) ∈ B :=
  (primeWeightValue_mem_iff_re p ρ).2 (primeTraceZeroMap_rational_real_part ρ hr)

/-- A zero off the line that some arithmetic automorphism reflects has its weight outside the
prime trace field. -/
theorem primeWeightValue_not_mem_of_reflection (p : Nat.Primes) (ρ : XiDivisorSupport)
    (horbit : ∃ σ : G, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ)
    (hoff : (ρ : ℂ).re ≠ 1 / 2) : (primeWeightValue p ρ : ℂ) ∉ B := by
  obtain ⟨σ, hσ⟩ := horbit
  refine (exists_re_ne_iff_primeWeightValue_not_mem p ρ).1 ⟨σ, ?_⟩
  rw [hσ]
  change (1 - (ρ : ℂ)).re ≠ (ρ : ℂ).re
  intro h
  simp only [Complex.sub_re, Complex.one_re] at h
  exact hoff (by linarith only [h])

end GaloisForLFunctions.GaloisTheoryOfZeros
