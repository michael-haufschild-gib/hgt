import GaloisForLFunctions.RHTower.Deninger.DeningerTestHeightBridge

/-!
# The Kummer map is a homomorphism with kernel the roots of unity

Taking logarithms turns the multiplicativity of the absolute values into additivity: the
logarithmic Kummer function of a product is the sum of the Kummer functions, and the Kummer
function of a power is the multiple.  So the Kummer construction is a homomorphism from the
multiplicative group of the field to the additive group of the test space, and the span of its
image is the Kummer subspace of the card.

Its kernel is exactly the roots of unity: a Kummer function vanishes identically exactly when
every absolute value of the element is one, which by the height-zero theorem happens exactly for
the torsion elements.  So the Kummer subspace is a faithful model of `K^× / μ(K)`.

* `deningerKummerFun_mul`, `_pow`, `_inv` : the logarithmic laws.
* `deningerKummerHom` : **the Kummer homomorphism `K^× → 𝒟(Y)`.**
* `deningerKummerFun_eq_zero_iff` : **it vanishes exactly on the roots of unity.**
* `deningerKummerHom_range_span` : the span of its image is the Kummer subspace.
-/

namespace RHTower

open NumberField

section KummerLaws

variable (K : Type*) [Field K] [NumberField K]

/-- **The Kummer function of a product is the sum of the Kummer functions.** -/
theorem deningerKummerFun_mul {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0) :
    deningerKummerFun K (α * β) = deningerKummerFun K α + deningerKummerFun K β := by
  funext v
  cases v with
  | inl w =>
    show (w.mult : ℝ) * Real.log (w (α * β))
      = (w.mult : ℝ) * Real.log (w α) + (w.mult : ℝ) * Real.log (w β)
    rw [map_mul, Real.log_mul (InfinitePlace.pos_iff.mpr hα).ne'
      (InfinitePlace.pos_iff.mpr hβ).ne', mul_add]
  | inr w =>
    show Real.log (w (α * β)) = Real.log (w α) + Real.log (w β)
    rw [map_mul, Real.log_mul (FinitePlace.pos_iff.mpr hα).ne'
      (FinitePlace.pos_iff.mpr hβ).ne']

/-- The Kummer function of one vanishes. -/
theorem deningerKummerFun_one : deningerKummerFun K (1 : K) = 0 := by
  funext v
  cases v with
  | inl w =>
    show (w.mult : ℝ) * Real.log (w 1) = 0
    rw [map_one, Real.log_one, mul_zero]
  | inr w =>
    show Real.log (w 1) = 0
    rw [map_one, Real.log_one]

/-- **The Kummer function of a power is the multiple of the Kummer function.** -/
theorem deningerKummerFun_pow {α : K} (hα : α ≠ 0) (n : ℕ) :
    deningerKummerFun K (α ^ n) = n • deningerKummerFun K α := by
  induction n with
  | zero => rw [pow_zero, deningerKummerFun_one, zero_smul]
  | succ n ih =>
    rw [pow_succ, deningerKummerFun_mul K (pow_ne_zero n hα) hα, ih, succ_nsmul]

/-- **The Kummer function of an inverse is the negative of the Kummer function.** -/
theorem deningerKummerFun_inv {α : K} (hα : α ≠ 0) :
    deningerKummerFun K α⁻¹ = -deningerKummerFun K α := by
  have hmul := deningerKummerFun_mul K (inv_ne_zero hα) hα
  rw [inv_mul_cancel₀ hα, deningerKummerFun_one] at hmul
  rw [eq_neg_iff_add_eq_zero, hmul]

/-- The test-function form of multiplicativity. -/
theorem deningerKummerTest_mul {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hαβ : α * β ≠ 0) :
    deningerKummerTest K hαβ = deningerKummerTest K hα + deningerKummerTest K hβ :=
  Subtype.ext (deningerKummerFun_mul K hα hβ)

end KummerLaws

section Kernel

variable (K : Type*) [Field K] [NumberField K]

/-- **A logarithmic Kummer function vanishes identically exactly on the roots of unity.**  One
direction is the height-zero theorem, through the identification of the `ℓ¹` seminorm with twice
the height; the other is that a root of unity has logarithm zero at every place. -/
theorem deningerKummerFun_eq_zero_iff {α : K} (hα : α ≠ 0) :
    deningerKummerFun K α = 0 ↔ IsOfFinOrder α := by
  constructor
  · intro hzero
    refine (deningerL1Seminorm_eq_zero_iff hα).mp ?_
    have htest : deningerKummerTest K hα = 0 := Subtype.ext hzero
    rw [htest, map_zero]
  · intro hfin
    obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).mp hfin
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hsmul : (n : ℕ) • deningerKummerFun K α = 0 := by
      rw [← deningerKummerFun_pow K hα n, hpow, deningerKummerFun_one]
    funext v
    have hv : (n : ℝ) * deningerKummerFun K α v = 0 := by
      have := congrFun hsmul v
      simpa [nsmul_eq_mul] using this
    exact (mul_eq_zero.mp hv).resolve_left hnR

end Kernel

section Hom

variable (K : Type*) [Field K] [NumberField K]

/-- **The Kummer homomorphism**: the logarithmic Kummer function, as an additive homomorphism from
the multiplicative group of the field to the test space of the place space. -/
noncomputable def deningerKummerHom :
    Additive Kˣ →+ DeningerTestSpace (DeningerPlace K) where
  toFun u := deningerKummerTest K (Units.ne_zero (Additive.toMul u))
  map_zero' := Subtype.ext (deningerKummerFun_one K)
  map_add' u v := deningerKummerTest_mul K (Units.ne_zero (Additive.toMul u))
    (Units.ne_zero (Additive.toMul v)) _

theorem deningerKummerHom_apply (u : Kˣ) :
    deningerKummerHom K (Additive.ofMul u)
      = deningerKummerTest K (Units.ne_zero u) := rfl

/-- **The Kummer homomorphism kills exactly the roots of unity.** -/
theorem deningerKummerHom_eq_zero_iff (u : Kˣ) :
    deningerKummerHom K (Additive.ofMul u) = 0 ↔ IsOfFinOrder ((u : K)) := by
  rw [deningerKummerHom_apply]
  constructor
  · intro h
    exact (deningerKummerFun_eq_zero_iff K (Units.ne_zero u)).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((deningerKummerFun_eq_zero_iff K (Units.ne_zero u)).mpr h)

/-- The image of the Kummer homomorphism is the set of logarithmic Kummer functions. -/
theorem deningerKummerHom_range :
    Set.range (deningerKummerHom K)
      = {g | ∃ (α : K) (hα : α ≠ 0), g = deningerKummerTest K hα} := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨((Additive.toMul u : Kˣ) : K), Units.ne_zero _, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨Additive.ofMul (Units.mk0 α hα), rfl⟩

/-- **The span of the image of the Kummer homomorphism is the Kummer subspace.** -/
theorem deningerKummerHom_range_span :
    Submodule.span ℝ (Set.range (deningerKummerHom K)) = DeningerKummerSpan K := by
  rw [deningerKummerHom_range]
  rfl

end Hom

end RHTower
