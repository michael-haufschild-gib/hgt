import GaloisForLFunctions.RHTower.Deninger.DeningerFiniteExtension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Hilbert--Kummer characters: logarithmic modulus, Frobenius scaling, modulus replacement

A character of a group with values in `ℂ` never vanishes, so its logarithmic modulus
`L_P(a) = log ‖P a‖` is an additive function of `a`.  Raising the argument to a power multiplies
it by the exponent, which is the exact scaling law of Deninger's positive rational Frobenius.

Replacing the modulus of a character while keeping its unitary part again produces a character.
The replacement is invisible on torsion, because an additive real-valued function kills torsion,
and matches the original character wherever the new logarithmic modulus was prescribed to agree.
Combined with bounded extension off a finite-dimensional subspace, this realizes any character on
a prescribed finite set by a Hilbert--Kummer bounded one.

* `deningerLogModulus_mul`, `deningerLogModulus_zpow` : additivity and the power law.
* `deningerLogModulus_ratPow` : the rational-exponent scaling law, `r(F_q P) = q r(P)`.
* `deningerModulusReplace_mul` : the replacement is again a character.
* `deningerModulusReplace_eq_self` : it agrees with the original where the modulus was prescribed.
* `deningerModulusReplace_torsion` : it is unchanged on torsion.
* `deningerHilbertKummer_pointwise` : the pointwise density step.
* `deningerSuspensionValue_descent` : descent of the suspension value function.
-/

namespace RHTower

section HilbertKummerCharacter

variable {G : Type*} [Group G]

/-- A character of a group with values in `ℂ` never vanishes: `P a` is invertible. -/
theorem deningerChar_ne_zero (P : G →* ℂ) (a : G) : P a ≠ 0 := by
  intro h
  have h1 : P a * P a⁻¹ = 1 := by
    rw [← P.map_mul, mul_inv_cancel, P.map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- The norm of a character value is strictly positive. -/
theorem deningerChar_norm_pos (P : G →* ℂ) (a : G) : 0 < ‖P a‖ :=
  norm_pos_iff.mpr (deningerChar_ne_zero P a)

/-- The logarithmic modulus of a character. -/
noncomputable def deningerLogModulus (P : G →* ℂ) (a : G) : ℝ := Real.log ‖P a‖

/-- **The logarithmic modulus is additive.** -/
theorem deningerLogModulus_mul (P : G →* ℂ) (a b : G) :
    deningerLogModulus P (a * b) = deningerLogModulus P a + deningerLogModulus P b := by
  unfold deningerLogModulus
  rw [P.map_mul, norm_mul, Real.log_mul (deningerChar_norm_pos P a).ne'
    (deningerChar_norm_pos P b).ne']

@[simp] theorem deningerLogModulus_one (P : G →* ℂ) : deningerLogModulus P 1 = 0 := by
  simp [deningerLogModulus]

/-- **The power law.**  Raising the argument to an integer power multiplies the logarithmic
modulus by the exponent.  This is the scaling law of Deninger's Frobenius. -/
theorem deningerLogModulus_zpow (P : G →* ℂ) (a : G) (n : ℤ) :
    deningerLogModulus P (a ^ n) = n * deningerLogModulus P a := by
  unfold deningerLogModulus
  rw [P.map_zpow, norm_zpow, Real.log_zpow]

/-- **The rational-exponent scaling law.**  If `b` is a rational power `a^{k/m}` — witnessed by
`b^m = a^k` — then its logarithmic modulus is the corresponding rational multiple.  This is the
positive rational Frobenius law `r(F_q P) = q r(P)` in its exponent form. -/
theorem deningerLogModulus_ratPow (P : G →* ℂ) {a b : G} {k m : ℤ} (hm : m ≠ 0)
    (h : b ^ m = a ^ k) :
    deningerLogModulus P b = (k : ℝ) / (m : ℝ) * deningerLogModulus P a := by
  have hcast : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hkey : (m : ℝ) * deningerLogModulus P b = (k : ℝ) * deningerLogModulus P a := by
    rw [← deningerLogModulus_zpow, ← deningerLogModulus_zpow, h]
  field_simp
  linarith [hkey]

/-- A character has modulus one on torsion. -/
theorem deningerLogModulus_torsion (P : G →* ℂ) {a : G} {n : ℕ} (hn : n ≠ 0) (ha : a ^ n = 1) :
    deningerLogModulus P a = 0 := by
  have h : ‖P a‖ ^ n = 1 := by
    rw [← norm_pow, ← P.map_pow, ha, P.map_one, norm_one]
  have hlog : (n : ℝ) * Real.log ‖P a‖ = 0 := by
    rw [← Real.log_pow, h, Real.log_one]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  exact (mul_eq_zero.mp hlog).resolve_left hn'

/-- A character has modulus one on torsion. -/
theorem deningerChar_norm_torsion (P : G →* ℂ) {a : G} {n : ℕ} (hn : n ≠ 0) (ha : a ^ n = 1) :
    ‖P a‖ = 1 := by
  have := deningerLogModulus_torsion P hn ha
  rw [deningerLogModulus] at this
  have := congrArg Real.exp this
  rwa [Real.exp_log (deningerChar_norm_pos P a), Real.exp_zero] at this

/-- The unitary part `P/|P|` of a character. -/
noncomputable def deningerUnitPart (P : G →* ℂ) : G →* ℂ where
  toFun a := P a / (‖P a‖ : ℂ)
  map_one' := by simp
  map_mul' a b := by
    have ha : (‖P a‖ : ℂ) ≠ 0 := by
      exact_mod_cast (deningerChar_norm_pos P a).ne'
    have hb : (‖P b‖ : ℂ) ≠ 0 := by
      exact_mod_cast (deningerChar_norm_pos P b).ne'
    simp only [P.map_mul, norm_mul, Complex.ofReal_mul]
    field_simp

@[simp] theorem deningerUnitPart_apply (P : G →* ℂ) (a : G) :
    deningerUnitPart P a = P a / (‖P a‖ : ℂ) := rfl

/-- The unitary part has modulus one. -/
theorem deningerUnitPart_norm (P : G →* ℂ) (a : G) : ‖deningerUnitPart P a‖ = 1 := by
  rw [deningerUnitPart_apply, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (deningerChar_norm_pos P a)]
  exact div_self (deningerChar_norm_pos P a).ne'

/-- **Modulus replacement.**  Keep the unitary part `u` and install the new logarithmic modulus
`l`. -/
noncomputable def deningerModulusReplace (u : G →* ℂ) (l : G → ℝ) (a : G) : ℂ :=
  (Real.exp (l a) : ℂ) * u a

/-- **The replacement is again a character**, provided the new logarithmic modulus is additive. -/
theorem deningerModulusReplace_mul (u : G →* ℂ) {l : G → ℝ}
    (hl : ∀ a b, l (a * b) = l a + l b) (a b : G) :
    deningerModulusReplace u l (a * b)
      = deningerModulusReplace u l a * deningerModulusReplace u l b := by
  unfold deningerModulusReplace
  rw [hl, Real.exp_add, u.map_mul, Complex.ofReal_mul]
  ring

/-- The replacement has the prescribed modulus. -/
theorem deningerModulusReplace_norm (u : G →* ℂ) (l : G → ℝ) {a : G} (hu : ‖u a‖ = 1) :
    ‖deningerModulusReplace u l a‖ = Real.exp (l a) := by
  rw [deningerModulusReplace, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- **The replacement agrees with the original character** wherever the new logarithmic modulus
was prescribed to be the old one. -/
theorem deningerModulusReplace_eq_self (P : G →* ℂ) {l : G → ℝ} {a : G}
    (ha : l a = deningerLogModulus P a) :
    deningerModulusReplace (deningerUnitPart P) l a = P a := by
  have hpos := deningerChar_norm_pos P a
  have hne : (‖P a‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [deningerModulusReplace, ha, deningerLogModulus, Real.exp_log hpos,
    deningerUnitPart_apply]
  field_simp

/-- An additive real-valued function kills torsion. -/
theorem deningerAdditive_torsion {l : G → ℝ} (hl : ∀ a b, l (a * b) = l a + l b) {a : G} {n : ℕ}
    (hn : n ≠ 0) (ha : a ^ n = 1) : l a = 0 := by
  have hone : l 1 = 0 := by
    have := hl 1 1
    simp only [mul_one] at this
    linarith
  have hpow : ∀ k : ℕ, l (a ^ k) = k * l a := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hl, ih]; push_cast; ring
  have hzero := hpow n
  rw [ha, hone] at hzero
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  exact (mul_eq_zero.mp hzero.symm).resolve_left hn'

/-- **The replacement is invisible on torsion**: it agrees with the original character on every
root of unity, so it preserves the admissibility condition on the torsion kernel. -/
theorem deningerModulusReplace_torsion (P : G →* ℂ) {l : G → ℝ}
    (hl : ∀ a b, l (a * b) = l a + l b) {a : G} {n : ℕ} (hn : n ≠ 0) (ha : a ^ n = 1) :
    deningerModulusReplace (deningerUnitPart P) l a = P a := by
  refine deningerModulusReplace_eq_self P ?_
  rw [deningerAdditive_torsion hl hn ha, deningerLogModulus_torsion P hn ha]

end HilbertKummerCharacter

section HilbertKummerDensity

variable {G : Type*} [Group G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The pointwise density step.**  Suppose the logarithmic modulus of a character `P` is
computed by an — a priori unbounded — linear functional `φ` on the Kummer Hilbert space, along a
class map `f`.  Then for any finite family of arguments there is a genuinely *bounded* functional
whose associated modulus replacement is a character agreeing with `P` on that family, and on all
torsion. -/
theorem deningerHilbertKummer_pointwise {m : ℕ} (P : G →* ℂ) (f : G →* Multiplicative H)
    (φ : H →ₗ[ℝ] ℝ) (hφ : ∀ a : G, φ (Multiplicative.toAdd (f a)) = deningerLogModulus P a)
    (a : Fin m → G) :
    ∃ L : H →L[ℝ] ℝ,
      (∀ b c : G, L (Multiplicative.toAdd (f (b * c)))
          = L (Multiplicative.toAdd (f b)) + L (Multiplicative.toAdd (f c))) ∧
      ∀ i : Fin m,
        deningerModulusReplace (deningerUnitPart P)
          (fun b => L (Multiplicative.toAdd (f b))) (a i) = P (a i) := by
  classical
  set g : Fin m → H := fun i => Multiplicative.toAdd (f (a i)) with hg
  set W : Submodule ℝ H := Submodule.span ℝ (Set.range g) with hW
  haveI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range g)
  obtain ⟨L, hL⟩ := deningerFiniteDimExtend W (φ.comp W.subtype)
  refine ⟨L, fun b c => ?_, fun i => ?_⟩
  · rw [map_mul]
    exact map_add L _ _
  · refine deningerModulusReplace_eq_self P ?_
    have hmem : g i ∈ W := Submodule.subset_span ⟨i, rfl⟩
    have := hL ⟨g i, hmem⟩
    simpa [hg, hφ] using this

end HilbertKummerDensity

section SuspensionValue

/-- **Descent of the suspension value function.**  If the radius `r` scales by `q` under the
Frobenius `F q`, then `u · r(P)` is invariant under the deck relation `(P, u) ↦ (F q P, q⁻¹ u)`,
so it descends to the suspension. -/
theorem deningerSuspensionValue_descent {X : Type*} (r : X → ℝ) (F : ℝ → X → X)
    (hF : ∀ q P, r (F q P) = q * r P) {q : ℝ} (hq : q ≠ 0) (P : X) (u : ℝ) :
    q⁻¹ * u * r (F q P) = u * r P := by
  rw [hF]
  field_simp

/-- **Positivity of the suspension value off the unitary locus.** -/
theorem deningerSuspensionValue_pos {X : Type*} (r : X → ℝ) (hr : ∀ P, 0 ≤ r P) {u : ℝ}
    (hu : 0 < u) (P : X) : 0 < u * r P ↔ r P ≠ 0 := by
  constructor
  · intro h hzero
    rw [hzero, mul_zero] at h
    exact lt_irrefl 0 h
  · intro h
    exact mul_pos hu ((hr P).lt_of_ne (Ne.symm h))

end SuspensionValue

end RHTower
