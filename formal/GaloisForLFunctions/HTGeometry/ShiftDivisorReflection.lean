import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Tactic

/-!
# Reflection law for divisor-weighted translate families

A finitely supported complex divisor `w` of shifts turns any function `f : ℂ → ℂ` into the value
`shiftDivisorValue w f s = ∑ a w a * f (s + a)`.  If `f` obeys a signed reflection
`f (2c₀ - z) = ε f z`, then reflecting the observation coordinate about `σ / 2` is exactly
reflecting the shift divisor about `(2c₀ - σ) / 2`, with an overall factor `ε`:

  `shiftDivisorValue w f (σ - s) = ε * shiftDivisorValue (reflectShiftDivisor (2c₀ - σ) w) f s`.

Thus a family of translates inherits an exact reflection law precisely when its divisor is an
eigenvector of the divisor reflection; the eigenvalue `η = ±1` multiplies the functional-equation
sign.  Iterated forward differences are the special case of the difference divisors
`(δ_τ - δ_0)`, whose eigenvalue is `(-1)^n` about the sum of the directions, so the classical
centre-shift-and-flip rule for finite differences is one instance of the divisor law.

The annihilating divisors of `f` form a submodule stable under both translation and reflection
whenever `ε ≠ 0`: the reflection symmetry of `f` is inherited by its whole relation module.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Value at `s` of a finitely supported complex divisor of shifts applied to `f`. -/
def shiftDivisorValue (w : ℂ →₀ ℂ) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  w.sum fun a m => m * f (s + a)

/-- Reflection of a shift divisor about `c / 2`: the shift `a` is sent to `c - a`. -/
def reflectShiftDivisor (c : ℂ) (w : ℂ →₀ ℂ) : ℂ →₀ ℂ :=
  Finsupp.equivMapDomain (Equiv.subLeft c) w

/-- Translation of a shift divisor by `τ`. -/
def translateShiftDivisor (τ : ℂ) (w : ℂ →₀ ℂ) : ℂ →₀ ℂ :=
  Finsupp.equivMapDomain (Equiv.addRight τ) w

@[simp]
theorem reflectShiftDivisor_apply (c : ℂ) (w : ℂ →₀ ℂ) (a : ℂ) :
    reflectShiftDivisor c w a = w (c - a) := by
  rw [reflectShiftDivisor, Finsupp.equivMapDomain_apply]
  norm_num
  exact congrArg (⇑w) (by ring)

@[simp]
theorem translateShiftDivisor_apply (τ : ℂ) (w : ℂ →₀ ℂ) (a : ℂ) :
    translateShiftDivisor τ w a = w (a - τ) := by
  rw [translateShiftDivisor, Finsupp.equivMapDomain_apply]
  norm_num
  exact congrArg (⇑w) (by ring)

/-! ## Linearity -/

@[simp]
theorem shiftDivisorValue_zero (f : ℂ → ℂ) (s : ℂ) : shiftDivisorValue 0 f s = 0 := by
  simp [shiftDivisorValue]

@[simp]
theorem shiftDivisorValue_single (a m : ℂ) (f : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue (Finsupp.single a m) f s = m * f (s + a) := by
  rw [shiftDivisorValue, Finsupp.sum_single_index (by simp)]

theorem shiftDivisorValue_add (v w : ℂ →₀ ℂ) (f : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue (v + w) f s = shiftDivisorValue v f s + shiftDivisorValue w f s :=
  Finsupp.sum_add_index' (by intro a; ring) (by intro a b₁ b₂; ring)

theorem shiftDivisorValue_sub (v w : ℂ →₀ ℂ) (f : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue (v - w) f s = shiftDivisorValue v f s - shiftDivisorValue w f s :=
  Finsupp.sum_sub_index (by intro a b₁ b₂; ring)

theorem shiftDivisorValue_neg (w : ℂ →₀ ℂ) (f : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue (-w) f s = -shiftDivisorValue w f s := by
  simpa using shiftDivisorValue_sub 0 w f s

theorem shiftDivisorValue_smul (m : ℂ) (w : ℂ →₀ ℂ) (f : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue (m • w) f s = m * shiftDivisorValue w f s := by
  rw [shiftDivisorValue, Finsupp.sum_smul_index' (by intro a; ring), shiftDivisorValue,
    Finsupp.mul_sum]
  exact Finsupp.sum_congr fun a _ => by ring

theorem shiftDivisorValue_finset_sum {ι : Type*} (S : Finset ι) (w : ι → ℂ →₀ ℂ)
    (f : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue (∑ i ∈ S, w i) f s = ∑ i ∈ S, shiftDivisorValue (w i) f s := by
  classical
  refine Finset.induction_on S (by simp) ?_
  intro i S hi ih
  rw [Finset.sum_insert hi, shiftDivisorValue_add, ih, Finset.sum_insert hi]

/-- Only the values of the observed function on the divisor support matter. -/
theorem shiftDivisorValue_congr (w : ℂ →₀ ℂ) {f g : ℂ → ℂ} {s : ℂ}
    (h : ∀ a ∈ w.support, f (s + a) = g (s + a)) :
    shiftDivisorValue w f s = shiftDivisorValue w g s :=
  Finsupp.sum_congr fun a ha => by rw [h a ha]

theorem shiftDivisorValue_fun_add (w : ℂ →₀ ℂ) (f g : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue w (fun z => f z + g z) s =
      shiftDivisorValue w f s + shiftDivisorValue w g s := by
  simp only [shiftDivisorValue, Finsupp.sum, mul_add]
  exact Finset.sum_add_distrib

theorem shiftDivisorValue_fun_sub (w : ℂ →₀ ℂ) (f g : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue w (fun z => f z - g z) s =
      shiftDivisorValue w f s - shiftDivisorValue w g s := by
  simp only [shiftDivisorValue, Finsupp.sum, mul_sub, Finset.sum_sub_distrib]

theorem shiftDivisorValue_fun_neg (w : ℂ →₀ ℂ) (f : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue w (fun z => -f z) s = -shiftDivisorValue w f s := by
  simp only [shiftDivisorValue, Finsupp.sum, mul_neg, Finset.sum_neg_distrib]

/-! ## Divisor reflection and translation -/

theorem reflectShiftDivisor_involutive (c : ℂ) (w : ℂ →₀ ℂ) :
    reflectShiftDivisor c (reflectShiftDivisor c w) = w := by
  ext a
  simp

theorem reflectShiftDivisor_add (c : ℂ) (v w : ℂ →₀ ℂ) :
    reflectShiftDivisor c (v + w) = reflectShiftDivisor c v + reflectShiftDivisor c w := by
  ext a; simp

theorem reflectShiftDivisor_sub (c : ℂ) (v w : ℂ →₀ ℂ) :
    reflectShiftDivisor c (v - w) = reflectShiftDivisor c v - reflectShiftDivisor c w := by
  ext a; simp

theorem reflectShiftDivisor_neg (c : ℂ) (w : ℂ →₀ ℂ) :
    reflectShiftDivisor c (-w) = -reflectShiftDivisor c w := by
  ext a; simp

theorem reflectShiftDivisor_smul (c m : ℂ) (w : ℂ →₀ ℂ) :
    reflectShiftDivisor c (m • w) = m • reflectShiftDivisor c w := by
  ext a; simp

theorem translateShiftDivisor_smul (τ m : ℂ) (w : ℂ →₀ ℂ) :
    translateShiftDivisor τ (m • w) = m • translateShiftDivisor τ w := by
  ext a; simp

theorem translateShiftDivisor_sub (τ : ℂ) (v w : ℂ →₀ ℂ) :
    translateShiftDivisor τ (v - w) = translateShiftDivisor τ v - translateShiftDivisor τ w := by
  ext a; simp

/-- Reflecting a translated divisor moves the reflection centre back. -/
theorem reflectShiftDivisor_translateShiftDivisor (c τ : ℂ) (w : ℂ →₀ ℂ) :
    reflectShiftDivisor c (translateShiftDivisor τ w) = reflectShiftDivisor (c - τ) w := by
  ext a
  simp only [reflectShiftDivisor_apply, translateShiftDivisor_apply]
  congr 1
  ring

/-- Moving the reflection centre translates the reflected divisor. -/
theorem reflectShiftDivisor_add_center (c τ : ℂ) (w : ℂ →₀ ℂ) :
    reflectShiftDivisor (c + τ) w = translateShiftDivisor τ (reflectShiftDivisor c w) := by
  ext a
  simp only [reflectShiftDivisor_apply, translateShiftDivisor_apply]
  congr 1
  ring

/-- Reflection carries a point divisor to the point divisor at the reflected shift. -/
theorem reflectShiftDivisor_single (c a m : ℂ) :
    reflectShiftDivisor c (Finsupp.single a m) = Finsupp.single (c - a) m := by
  ext x
  simp only [reflectShiftDivisor_apply, Finsupp.single_apply]
  by_cases h : a = c - x
  · rw [if_pos h, if_pos (by rw [h]; ring)]
  · rw [if_neg h, if_neg (fun hx => h (by rw [← hx]; ring))]

/-! ## Canonical reflection splitting -/

/-- The reflection-anti-invariant part of a shift divisor. -/
def antisymmShiftDivisorPart (c : ℂ) (w : ℂ →₀ ℂ) : ℂ →₀ ℂ :=
  w - reflectShiftDivisor c w

/-- The reflection-invariant part of a shift divisor. -/
def symmShiftDivisorPart (c : ℂ) (w : ℂ →₀ ℂ) : ℂ →₀ ℂ :=
  w + reflectShiftDivisor c w

theorem reflectShiftDivisor_antisymmShiftDivisorPart (c : ℂ) (w : ℂ →₀ ℂ) :
    reflectShiftDivisor c (antisymmShiftDivisorPart c w) = -antisymmShiftDivisorPart c w := by
  rw [antisymmShiftDivisorPart, reflectShiftDivisor_sub, reflectShiftDivisor_involutive]
  abel

theorem reflectShiftDivisor_symmShiftDivisorPart (c : ℂ) (w : ℂ →₀ ℂ) :
    reflectShiftDivisor c (symmShiftDivisorPart c w) = symmShiftDivisorPart c w := by
  rw [symmShiftDivisorPart, reflectShiftDivisor_add, reflectShiftDivisor_involutive]
  abel

/-- **Canonical reflection splitting.** Over a field of characteristic zero every shift divisor is
the half-sum of a reflection-invariant and a reflection-anti-invariant divisor. -/
theorem shiftDivisor_eq_half_symm_add_half_antisymm (c : ℂ) (w : ℂ →₀ ℂ) :
    (2⁻¹ : ℂ) • symmShiftDivisorPart c w + (2⁻¹ : ℂ) • antisymmShiftDivisorPart c w = w := by
  rw [symmShiftDivisorPart, antisymmShiftDivisorPart]
  ext a
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

/-! ## The reflection law -/

theorem shiftDivisorValue_reflectShiftDivisor (c : ℂ) (w : ℂ →₀ ℂ) (f : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue (reflectShiftDivisor c w) f s =
      w.sum fun a m => m * f (s + (c - a)) := by
  rw [shiftDivisorValue, reflectShiftDivisor, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (by intro b; ring) (by intro b m₁ m₂; ring)]
  rfl

theorem shiftDivisorValue_translateShiftDivisor (τ : ℂ) (w : ℂ →₀ ℂ) (f : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue (translateShiftDivisor τ w) f s = shiftDivisorValue w f (s + τ) := by
  rw [shiftDivisorValue, translateShiftDivisor, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (by intro b; ring) (by intro b m₁ m₂; ring), shiftDivisorValue]
  refine Finsupp.sum_congr fun a _ => ?_
  rw [show s + ((Equiv.addRight τ) a) = s + τ + a by simp; ring]

/-- **Divisor reflection law.** -/
theorem shiftDivisorValue_signed_reflection {f : ℂ → ℂ} {c₀ ε : ℂ}
    (hsym : ∀ z, f (2 * c₀ - z) = ε * f z) (w : ℂ →₀ ℂ) (σ s : ℂ) :
    shiftDivisorValue w f (σ - s) =
      ε * shiftDivisorValue (reflectShiftDivisor (2 * c₀ - σ) w) f s := by
  rw [shiftDivisorValue_reflectShiftDivisor, Finsupp.mul_sum, shiftDivisorValue]
  refine Finsupp.sum_congr fun a _ => ?_
  have h := hsym (s + (2 * c₀ - σ - a))
  rw [show 2 * c₀ - (s + (2 * c₀ - σ - a)) = σ - s + a by ring] at h
  rw [h]
  ring

theorem shiftDivisorValue_reflection_of_eigen {f : ℂ → ℂ} {c₀ ε η : ℂ}
    (hsym : ∀ z, f (2 * c₀ - z) = ε * f z) {w : ℂ →₀ ℂ} {σ : ℂ}
    (hw : reflectShiftDivisor (2 * c₀ - σ) w = η • w) (s : ℂ) :
    shiftDivisorValue w f (σ - s) = ε * η * shiftDivisorValue w f s := by
  rw [shiftDivisorValue_signed_reflection hsym, hw, shiftDivisorValue_smul]
  ring

theorem shiftDivisorValue_center_reflection {f : ℂ → ℂ} {c₀ ε η : ℂ}
    (hsym : ∀ z, f (2 * c₀ - z) = ε * f z) {w : ℂ →₀ ℂ} {σ : ℂ}
    (hw : reflectShiftDivisor (2 * c₀ - σ) w = η • w) (s : ℂ) :
    shiftDivisorValue w f (2 * (σ / 2) - s) = ε * η * shiftDivisorValue w f s := by
  rw [show 2 * (σ / 2) = σ by ring]
  exact shiftDivisorValue_reflection_of_eigen hsym hw s

/-! ## The annihilator -/

theorem shiftDivisorValue_reflect_eq_zero {f : ℂ → ℂ} {c₀ ε : ℂ} (hε : ε ≠ 0)
    (hsym : ∀ z, f (2 * c₀ - z) = ε * f z) {w : ℂ →₀ ℂ}
    (hw : ∀ s, shiftDivisorValue w f s = 0) (σ s : ℂ) :
    shiftDivisorValue (reflectShiftDivisor (2 * c₀ - σ) w) f s = 0 := by
  have h := shiftDivisorValue_signed_reflection hsym w σ s
  rw [hw (σ - s)] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hε

/-- Divisors whose weighted translate family annihilates `f`. -/
def shiftDivisorAnnihilator (f : ℂ → ℂ) : Submodule ℂ (ℂ →₀ ℂ) where
  carrier := {w | ∀ s, shiftDivisorValue w f s = 0}
  add_mem' := by
    intro v w hv hw s
    rw [shiftDivisorValue_add, hv s, hw s, add_zero]
  zero_mem' := by intro s; simp
  smul_mem' := by
    intro m w hw s
    rw [shiftDivisorValue_smul, hw s, mul_zero]

@[simp]
theorem mem_shiftDivisorAnnihilator {f : ℂ → ℂ} {w : ℂ →₀ ℂ} :
    w ∈ shiftDivisorAnnihilator f ↔ ∀ s, shiftDivisorValue w f s = 0 :=
  Iff.rfl

theorem translateShiftDivisor_mem_annihilator {f : ℂ → ℂ} {w : ℂ →₀ ℂ}
    (hw : w ∈ shiftDivisorAnnihilator f) (τ : ℂ) :
    translateShiftDivisor τ w ∈ shiftDivisorAnnihilator f := by
  intro s
  rw [shiftDivisorValue_translateShiftDivisor]
  exact hw (s + τ)

theorem reflectShiftDivisor_mem_annihilator {f : ℂ → ℂ} {c₀ ε : ℂ} (hε : ε ≠ 0)
    (hsym : ∀ z, f (2 * c₀ - z) = ε * f z) {w : ℂ →₀ ℂ}
    (hw : w ∈ shiftDivisorAnnihilator f) (c : ℂ) :
    reflectShiftDivisor c w ∈ shiftDivisorAnnihilator f := by
  intro s
  have := shiftDivisorValue_reflect_eq_zero hε hsym hw (2 * c₀ - c) s
  rwa [show 2 * c₀ - (2 * c₀ - c) = c by ring] at this

/-! ## Iterated difference divisors -/

/-- Divisor realizing the iterated forward difference along a finite direction list. -/
def iteratedDifferenceDivisor : List ℂ → (ℂ →₀ ℂ)
  | [] => Finsupp.single 0 1
  | τ :: τs =>
      translateShiftDivisor τ (iteratedDifferenceDivisor τs) - iteratedDifferenceDivisor τs

theorem reflectShiftDivisor_single_zero_zero :
    reflectShiftDivisor 0 (Finsupp.single (0 : ℂ) (1 : ℂ)) = Finsupp.single (0 : ℂ) (1 : ℂ) := by
  ext a
  simp [Finsupp.single_apply, eq_comm]

/-- **Difference-divisor eigenvalue.** -/
theorem reflectShiftDivisor_iteratedDifferenceDivisor (τs : List ℂ) :
    reflectShiftDivisor τs.sum (iteratedDifferenceDivisor τs) =
      ((-1 : ℂ) ^ τs.length) • iteratedDifferenceDivisor τs := by
  induction τs with
  | nil => simpa [iteratedDifferenceDivisor] using reflectShiftDivisor_single_zero_zero
  | cons τ τs ih =>
      have hsum : (τ :: τs).sum = τs.sum + τ := by
        simp [List.sum_cons]; ring
      simp only [iteratedDifferenceDivisor, hsum, List.length_cons]
      rw [reflectShiftDivisor_sub, reflectShiftDivisor_translateShiftDivisor,
        show τs.sum + τ - τ = τs.sum by ring, ih, reflectShiftDivisor_add_center, ih,
        translateShiftDivisor_smul]
      rw [pow_succ]
      ext a
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]
      ring

/-! ## Analyticity -/

theorem shiftDivisorValue_analyticOnNhd_univ {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (w : ℂ →₀ ℂ) :
    AnalyticOnNhd ℂ (shiftDivisorValue w f) Set.univ := by
  intro z _
  have hterm : ∀ a : ℂ, AnalyticAt ℂ (fun s : ℂ => w a * f (s + a)) z := by
    intro a
    have haffine : AnalyticAt ℂ (fun s : ℂ => s + a) z :=
      analyticAt_id.add analyticAt_const
    have hcomp := (hf (z + a) (Set.mem_univ _)).comp (f := fun s : ℂ => s + a) haffine
    have hshift : AnalyticAt ℂ (fun s : ℂ => f (s + a)) z := by
      simpa [Function.comp_def] using hcomp
    exact AnalyticAt.mul analyticAt_const hshift
  have heq : (∑ a ∈ w.support, fun s : ℂ => w a * f (s + a)) = shiftDivisorValue w f := by
    funext s
    simp [shiftDivisorValue, Finsupp.sum, Finset.sum_apply]
  rw [← heq]
  exact Finset.analyticAt_sum _ fun a _ => hterm a

end

end GaloisForLFunctions.HTGeometry
