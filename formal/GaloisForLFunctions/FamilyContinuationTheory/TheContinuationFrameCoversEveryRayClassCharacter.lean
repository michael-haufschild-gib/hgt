import GaloisForLFunctions.FamilyContinuationTheory.TheContinuationFrameHoldsForHeckeLFunctions

/-!
# The continuation frame covers every ray class character

The family of all finite-order Hecke `L`-functions of a number field contains the trivial
characters, whose `L`-functions have a pole at `1`. The pole-cleared function
`(s − 1) L(s, ψ)`, with its removable value at `1`, is entire for every ray class character, and
`exp((s − c)²)/((s − 1) L(s, ψ))` is a signal kernel.

* `isSignalKernel_gauss_div`: `exp((s − c)²)/L(s)` is a signal kernel when `L` is holomorphic
  and nonvanishing on `Re s > 1` and bounded below on `Re s ≥ 2`.
* `heckePoleCleared_eq`: the pole-cleared function is `(s − 1) L(s, ψ)` away from `1`.
* `heckeLFunction_ne_zero_of_family_common_signal_all`: the family step over all ray class
  characters of all moduli. If, whenever all pole-cleared functions are zero-free in
  `Re s > β`, each character has a sum with a direct bound `Z^{a₁}` and a comparison `Z^{a₂}` with
  its signal, `a₁, a₂ < β` the same for all, then no `L(s, ψ)` has a zero `ρ ≠ 1` in
  `Re s > σ₀`.
-/

noncomputable section

open Complex NumberField IsDedekindDomain
open scoped Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions

/-- **A Gaussian over a function bounded below.** If `L` is holomorphic and nonvanishing on
`Re s > 1` and `|L| ≥ m > 0` on `Re s ≥ 2`, then `exp((s − c)²)/L(s)` is a signal kernel. -/
theorem isSignalKernel_gauss_div {L : ℂ → ℂ} {m : ℝ} (hm : 0 < m)
    (hdiff : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ L s) (hne : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hlow : ∀ s : ℂ, 2 ≤ s.re → m ≤ ‖L s‖) (c : ℝ) :
    IsSignalKernel (fun s : ℂ => cexp ((s - c) ^ 2) / L s) where
  differentiableAt s hs :=
    (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) s).div
      (hdiff s hs) (hne s hs)
  decay B := by
    refine ⟨Real.exp ((B + |c|) ^ 2) / m, fun s h2 hB => ?_⟩
    have hz := hlow s h2
    have hzpos : 0 < ‖L s‖ := lt_of_lt_of_le hm hz
    have hsq : (s.re - c) ^ 2 ≤ (B + |c|) ^ 2 := by
      have habs : |s.re - c| ≤ B + |c| := by
        rw [abs_le]
        constructor <;> linarith [neg_abs_le c, le_abs_self c]
      calc (s.re - c) ^ 2 = |s.re - c| ^ 2 := (sq_abs _).symm
        _ ≤ (B + |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hexp : Real.exp (-(s.im ^ 2)) ≤ 1 / (1 + s.im ^ 2) := by
      rw [Real.exp_neg, one_div]
      refine inv_anti₀ (by positivity) ?_
      linarith [Real.add_one_le_exp (s.im ^ 2)]
    have hnum : ‖cexp ((s - c) ^ 2)‖ ≤ Real.exp ((B + |c|) ^ 2) * (1 / (1 + s.im ^ 2)) := by
      rw [norm_cexp_sub_sq, sub_eq_add_neg, Real.exp_add]
      exact mul_le_mul (Real.exp_le_exp.mpr hsq) hexp (Real.exp_pos _).le (Real.exp_pos _).le
    rw [norm_div, div_le_iff₀ hzpos]
    calc ‖cexp ((s - c) ^ 2)‖ ≤ Real.exp ((B + |c|) ^ 2) * (1 / (1 + s.im ^ 2)) := hnum
      _ = Real.exp ((B + |c|) ^ 2) / m / (1 + s.im ^ 2) * m := by
          field_simp
      _ ≤ Real.exp ((B + |c|) ^ 2) / m / (1 + s.im ^ 2) * ‖L s‖ :=
          mul_le_mul_of_nonneg_left hz (by positivity)

variable {K : Type*} [Field K] [NumberField K]
variable (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)

/-- The pole-cleared Hecke `L`-function `(s − 1) L(s, ψ)`, with the removable value at `1`. -/
def heckePoleCleared (s : ℂ) : ℂ :=
  (s - 1) * heckeEntireRegularPart 𝔪 ψ s + heckeThetaPoleCoefficient 𝔪 ψ

theorem differentiable_heckePoleCleared : Differentiable ℂ (heckePoleCleared 𝔪 ψ) :=
  ((differentiable_id.sub_const 1).mul (differentiable_heckeEntireRegularPart 𝔪 ψ)).add_const _

/-- Away from `1` the pole-cleared function is `(s − 1) L(s, ψ)`. -/
theorem heckePoleCleared_eq {s : ℂ} (hs : s ≠ 1) :
    heckePoleCleared 𝔪 ψ s = (s - 1) * heckeLFunction 𝔪 ψ s := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold heckePoleCleared heckeLFunction
  field_simp

theorem heckePoleCleared_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    heckePoleCleared 𝔪 ψ s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  rw [heckePoleCleared_eq 𝔪 ψ hs1, heckeLFunction_eq_heckeL 𝔪 ψ hs]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) (heckeL_ne_zero 𝔪 ψ hs)

/-- On `Re s ≥ 2` the pole-cleared function is bounded below. -/
theorem exp_neg_le_norm_heckePoleCleared {s : ℂ} (hs : 2 ≤ s.re) :
    Real.exp (-(3 / 2 * ∑' v : HeightOneSpectrum (𝓞 K),
        ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖)) ≤ ‖heckePoleCleared 𝔪 ψ s‖ := by
  have hs1 : 1 < s.re := by linarith
  have hne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs1
    exact lt_irrefl _ hs1
  have hnorm : (1 : ℝ) ≤ ‖s - 1‖ := by
    have hre : (1 : ℝ) ≤ (s - 1).re := by rw [sub_re, one_re]; linarith
    exact le_trans hre (le_trans (le_abs_self _) (abs_re_le_norm _))
  rw [heckePoleCleared_eq 𝔪 ψ hne, heckeLFunction_eq_heckeL 𝔪 ψ hs1, norm_mul]
  exact (exp_neg_le_norm_heckeL 𝔪 ψ hs).trans (le_mul_of_one_le_left (norm_nonneg _) hnorm)

/-- The kernel of a ray class character: `exp((s − c)²)/((s − 1) L(s, ψ))`. -/
def heckePoleClearedKernel (c : ℝ) (s : ℂ) : ℂ :=
  cexp ((s - c) ^ 2) / heckePoleCleared 𝔪 ψ s

/-- **The kernel of every ray class character is a signal kernel.** -/
theorem isSignalKernel_heckePoleClearedKernel (c : ℝ) :
    IsSignalKernel (heckePoleClearedKernel 𝔪 ψ c) :=
  isSignalKernel_gauss_div (Real.exp_pos _)
    (fun s _ => differentiable_heckePoleCleared 𝔪 ψ s)
    (fun _ hs => heckePoleCleared_ne_zero_of_one_lt_re 𝔪 ψ hs)
    (fun _ hs => exp_neg_le_norm_heckePoleCleared 𝔪 ψ hs) c

/-- **Family continuation over all ray class characters of a number field.** -/
theorem heckeLFunction_ne_zero_of_family_common_signal_all (K : Type*) [Field K]
    [NumberField K] {σ₀ : ℝ} (hσ₀ : σ₀ < 1) (c : ℝ)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re →
        heckePoleCleared η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (heckePoleClearedKernel η.1 η.2 c) 2 Z‖ ≤ C * Z ^ a₂))
    (𝔫 : Modulus K) (φ : HeckeCharacter 𝔫) (ρ : ℂ) (hρ : σ₀ < ρ.re) (hρ1 : ρ ≠ 1) :
    heckeLFunction 𝔫 φ ρ ≠ 0 := by
  have h := ne_zero_of_family_common_signal
    (ι := Σ 𝔫 : Modulus K, HeckeCharacter 𝔫)
    (G := fun η => heckePoleClearedKernel η.1 η.2 c)
    (L := fun η => heckePoleCleared η.1 η.2)
    (E := fun _ s => cexp ((s - c) ^ 2)) hσ₀
    (fun η => isSignalKernel_heckePoleClearedKernel η.1 η.2 c)
    (fun η => (differentiable_heckePoleCleared η.1 η.2).differentiableOn)
    (fun _ => (by fun_prop : Differentiable ℂ fun s : ℂ => cexp ((s - c) ^ 2)).differentiableOn)
    (fun _ s _ => Complex.exp_ne_zero _)
    (fun η s hs => by
      show heckePoleClearedKernel η.1 η.2 c s * heckePoleCleared η.1 η.2 s =
        cexp ((s - c) ^ 2)
      unfold heckePoleClearedKernel
      exact div_mul_cancel₀ _ (heckePoleCleared_ne_zero_of_one_lt_re η.1 η.2 hs))
    hstep ⟨𝔫, φ⟩ ρ hρ
  intro h0
  apply h
  show heckePoleCleared 𝔫 φ ρ = 0
  rw [heckePoleCleared_eq 𝔫 φ hρ1, h0, mul_zero]

end GaloisForLFunctions.FamilyContinuationTheory
