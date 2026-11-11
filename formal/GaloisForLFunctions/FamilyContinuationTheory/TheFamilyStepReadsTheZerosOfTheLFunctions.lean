import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheThirdCyclotomicFieldContainsZeta
import GaloisForLFunctions.FamilyContinuationTheory.TheHeightIsChosenAfterTheTarget

/-!
# The family step reads the zeros of the `L`-functions

For a nontrivial ray class character `ψ` the pole-cleared function `(s − 1) L(s, ψ)` vanishes at
`s = 1` (`heckePoleCleared_one_of_ne_one`). A family step that asks the pole-cleared functions to
be zero-free in `Re s > β < 1` therefore has a false premise, and at `β = 1` it asks for a signal
whose kernel `exp((s − c)²) H(s)/((s − 1) L(s, ψ))` has a pole at `1`. The step is restated here
in the form of the source: the kernel of `ψ` is `exp((s − c)²) H(s)/L(s, ψ)`, and the zero-free
premise concerns `L(s, ψ)` off `1`.

* `ne_zero_of_family_common_signal_of_zeros`: the family step with `G L = E`, where `E` need not
  vanish only at the zeros of `L`. For the trivial characters `L` is `(s − 1) L(s, ψ)`, which is
  `heckeDensity ≠ 0` at `1`, and `E = exp((s − c)²) H(s) (s − 1)`.
* `isSignalKernel_gauss_mul_div_of_bounded`: `exp((s − c)²) H(s)/L(s)` is a signal kernel for a
  holomorphic `H` bounded on `Re s ≥ 2`; no nonvanishing of `H` is needed for the kernel.
* `heckeHalfPlane_of_family_reciprocal_signal`, `heckeHalfPlane_of_family_reciprocal_height_estimates`,
  `zetaZeroAbscissa_le_of_two_reciprocal_estimates`: the family steps with the reciprocal kernels,
  for every number field and, over `ℚ(ζ₃)`, for `ζ`.
-/

noncomputable section

open Complex NumberField
open scoped Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions _root_.RHTower

/-! ### The family step with a factor that is nonzero at the zeros only -/

/-- **Zeros.** As `ne_zero_of_signal_le`, with `E` required to be nonzero only where `L`
vanishes. -/
theorem ne_zero_of_signal_le_of_zeros {G L E : ℂ → ℂ} (hG : IsSignalKernel G) {b K Z₀ : ℝ}
    (hb : b < 1) (hZ₀ : 0 < Z₀) (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal G 2 Z‖ ≤ K * Z ^ b)
    (hL : DifferentiableOn ℂ L {s : ℂ | b < s.re}) (hE : DifferentiableOn ℂ E {s : ℂ | b < s.re})
    (hE0 : ∀ s : ℂ, b < s.re → L s = 0 → E s ≠ 0) (hGL : ∀ s : ℂ, 1 < s.re → G s * L s = E s)
    (ρ : ℂ) (hρ : b < ρ.re) : L ρ ≠ 0 := by
  obtain ⟨F, hF, hFG⟩ := exists_differentiableOn_eq_of_signal_le hG (by linarith) hZ₀ hK
  rw [max_eq_right hb.le] at hFG
  have hopen : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const continuous_re
  have h2 : ((2 : ℝ) : ℂ) ∈ {s : ℂ | b < s.re} := by
    show b < ((2 : ℝ) : ℂ).re
    rw [ofReal_re]; linarith
  have hev : (fun s => F s * L s) =ᶠ[nhds ((2 : ℝ) : ℂ)] E := by
    have hnhds : {s : ℂ | 1 < s.re} ∈ nhds ((2 : ℝ) : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by
        show 1 < ((2 : ℝ) : ℂ).re
        rw [ofReal_re]; norm_num)
    filter_upwards [hnhds] with s hs
    rw [hFG s hs, hGL s hs]
  have heq := ((hF.mul hL).analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (hE.analyticOnNhd hopen) (convex_halfSpace_re_gt b).isPreconnected h2 hev
  intro h0
  have := heq hρ
  simp only [Pi.mul_apply, h0, mul_zero] at this
  exact hE0 ρ hρ h0 this.symm

/-- **Two estimates give a half-plane**, with `E` nonzero at the zeros of `L` only. -/
theorem ne_zero_of_common_signal_of_zeros {G L E : ℂ → ℂ} (hG : IsSignalKernel G)
    {a₁ a₂ K Z₀ : ℝ} (J : ℝ → ℂ) (ha₁ : a₁ < 1) (ha₂ : a₂ < 1) (hZ₀ : 1 ≤ Z₀)
    (hJ : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ K * Z ^ a₁)
    (hJf : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z - signal G 2 Z‖ ≤ K * Z ^ a₂)
    (hL : DifferentiableOn ℂ L {s : ℂ | max a₁ a₂ < s.re})
    (hE : DifferentiableOn ℂ E {s : ℂ | max a₁ a₂ < s.re})
    (hE0 : ∀ s : ℂ, max a₁ a₂ < s.re → L s = 0 → E s ≠ 0)
    (hGL : ∀ s : ℂ, 1 < s.re → G s * L s = E s)
    (ρ : ℂ) (hρ : max a₁ a₂ < ρ.re) : L ρ ≠ 0 := by
  refine ne_zero_of_signal_le_of_zeros hG (b := max a₁ a₂) (K := 2 * |K|) (max_lt ha₁ ha₂)
    (lt_of_lt_of_le one_pos hZ₀) ?_ hL hE hE0 hGL ρ hρ
  intro Z hZ
  have hZ1 : 1 ≤ Z := le_trans hZ₀ hZ
  have h1 : Z ^ a₁ ≤ Z ^ max a₁ a₂ := Real.rpow_le_rpow_of_exponent_le hZ1 (le_max_left _ _)
  have h2 : Z ^ a₂ ≤ Z ^ max a₁ a₂ := Real.rpow_le_rpow_of_exponent_le hZ1 (le_max_right _ _)
  have hpos1 : 0 ≤ Z ^ a₁ := Real.rpow_nonneg (by linarith) _
  have hpos2 : 0 ≤ Z ^ a₂ := Real.rpow_nonneg (by linarith) _
  calc ‖signal G 2 Z‖ = ‖J Z - (J Z - signal G 2 Z)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖J Z‖ + ‖J Z - signal G 2 Z‖ := norm_sub_le _ _
    _ ≤ K * Z ^ a₁ + K * Z ^ a₂ := add_le_add (hJ Z hZ) (hJf Z hZ)
    _ ≤ |K| * Z ^ max a₁ a₂ + |K| * Z ^ max a₁ a₂ :=
        add_le_add
          (le_trans (mul_le_mul_of_nonneg_right (le_abs_self K) hpos1)
            (mul_le_mul_of_nonneg_left h1 (abs_nonneg K)))
          (le_trans (mul_le_mul_of_nonneg_right (le_abs_self K) hpos2)
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg K)))
    _ = 2 * |K| * Z ^ max a₁ a₂ := by ring

/-- **Family continuation**, with `E η` required to be nonzero only at the zeros of `L η`. -/
theorem ne_zero_of_family_common_signal_of_zeros {ι : Type*} {G L E : ι → ℂ → ℂ} {σ₀ : ℝ}
    (hσ₀ : σ₀ < 1) (hG : ∀ η, IsSignalKernel (G η))
    (hL : ∀ η, DifferentiableOn ℂ (L η) {s : ℂ | σ₀ < s.re})
    (hE : ∀ η, DifferentiableOn ℂ (E η) {s : ℂ | σ₀ < s.re})
    (hE0 : ∀ η (s : ℂ), σ₀ < s.re → L η s = 0 → E η s ≠ 0)
    (hGL : ∀ η (s : ℂ), 1 < s.re → G η s * L η s = E η s)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 → (∀ η (ρ : ℂ), β < ρ.re → L η ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧ ∀ η, ∃ (J : ℝ → ℂ) (K Z₀ : ℝ), 1 ≤ Z₀ ∧
        (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ K * Z ^ a₁) ∧
        (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z - signal (G η) 2 Z‖ ≤ K * Z ^ a₂))
    (η : ι) (ρ : ℂ) (hρ : σ₀ < ρ.re) : L η ρ ≠ 0 := by
  -- right of `1`, `G L = E` and `E ≠ 0` at a zero of `L` exclude the zero
  have hone : ∀ η (z : ℂ), 1 < z.re → L η z ≠ 0 := by
    intro η z hz h0
    have := hGL η z hz
    rw [h0, mul_zero] at this
    exact hE0 η z (by linarith) h0 this.symm
  set S : Set ℝ := {x : ℝ | ∃ (η : ι) (z : ℂ), L η z = 0 ∧ σ₀ < z.re ∧ x = z.re}
  have hS1 : ∀ x ∈ S, x ≤ 1 := by
    rintro x ⟨η, z, hz0, -, rfl⟩
    by_contra hlt
    exact hone η z (not_le.mp hlt) hz0
  have hall : ∀ x ∈ S, x ≤ σ₀ := by
    refine le_of_improving_bounds hS1 fun β hβ hβ1 hub => ?_
    have hfree : ∀ η (z : ℂ), β < z.re → L η z ≠ 0 := by
      intro η z hz h0
      have := hub z.re ⟨η, z, h0, by linarith, rfl⟩
      linarith
    obtain ⟨a₁, a₂, ha₁, ha₂, hJ⟩ := hstep β hβ hβ1 hfree
    refine ⟨β - max σ₀ (max a₁ a₂), by
      have : max σ₀ (max a₁ a₂) < β := max_lt hβ (max_lt ha₁ ha₂)
      linarith, ?_⟩
    rintro x ⟨η, z, hz0, hzσ, rfl⟩
    rw [sub_sub_cancel]
    refine le_trans ?_ (le_max_right _ _)
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨J, K, Z₀, hZ₀, hJ1, hJ2⟩ := hJ η
    have hb1 : max a₁ σ₀ < 1 := max_lt (by linarith) hσ₀
    have hb2 : max a₂ σ₀ < 1 := max_lt (by linarith) hσ₀
    have hmax : max (max a₁ σ₀) (max a₂ σ₀) = max σ₀ (max a₁ a₂) := by
      apply le_antisymm
      · exact max_le
          (max_le (le_trans (le_max_left a₁ a₂) (le_max_right _ _)) (le_max_left _ _))
          (max_le (le_trans (le_max_right a₁ a₂) (le_max_right _ _)) (le_max_left _ _))
      · exact max_le (le_trans (le_max_right a₁ σ₀) (le_max_left _ _))
          (max_le (le_trans (le_max_left a₁ σ₀) (le_max_left _ _))
            (le_trans (le_max_left a₂ σ₀) (le_max_right _ _)))
    have hsub : {s : ℂ | max (max a₁ σ₀) (max a₂ σ₀) < s.re} ⊆ {s : ℂ | σ₀ < s.re} := by
      intro s hs
      exact lt_of_le_of_lt (le_trans (le_max_right a₁ σ₀) (le_max_left _ _)) hs
    have hpow : ∀ {a : ℝ} (Z : ℝ), Z₀ ≤ Z → Z ^ a ≤ Z ^ max a σ₀ := fun Z hZ =>
      Real.rpow_le_rpow_of_exponent_le (le_trans hZ₀ hZ) (le_max_left _ _)
    refine ne_zero_of_common_signal_of_zeros (hG η) (a₁ := max a₁ σ₀) (a₂ := max a₂ σ₀)
      (K := |K|) J hb1 hb2 hZ₀ ?_ ?_ ((hL η).mono hsub) ((hE η).mono hsub)
      (fun s hs h0 => hE0 η s (hsub hs) h0) (hGL η) z (by rw [hmax]; exact hlt) hz0
    · intro Z hZ
      exact le_trans (hJ1 Z hZ) (le_trans
        (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg (by linarith) _))
        (mul_le_mul_of_nonneg_left (hpow Z hZ) (abs_nonneg K)))
    · intro Z hZ
      exact le_trans (hJ2 Z hZ) (le_trans
        (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg (by linarith) _))
        (mul_le_mul_of_nonneg_left (hpow Z hZ) (abs_nonneg K)))
  intro h0
  have := hall ρ.re ⟨η, ρ, h0, hρ, rfl⟩
  linarith

/-- **A Gaussian times a bounded correction over a function bounded below.** Unlike
`isSignalKernel_gauss_mul_div`, the correction may vanish. -/
theorem isSignalKernel_gauss_mul_div_of_bounded {L H : ℂ → ℂ} {m C : ℝ} (hm : 0 < m)
    (hL : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ L s) (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hlow : ∀ s : ℂ, 2 ≤ s.re → m ≤ ‖L s‖)
    (hH : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ H s)
    (hHb : ∀ s : ℂ, 2 ≤ s.re → ‖H s‖ ≤ C) (c : ℝ) :
    IsSignalKernel (fun s : ℂ => cexp ((s - c) ^ 2) * H s / L s) where
  differentiableAt s hs :=
    (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) s)).mul
      (hH s hs)).div (hL s hs) (hL0 s hs)
  decay B := by
    obtain ⟨C₀, hC₀⟩ := (isSignalKernel_gauss_div hm hL hL0 hlow c).decay B
    refine ⟨max C 0 * C₀, fun s h2 hB => ?_⟩
    have hG := hC₀ s h2 hB
    have hC₀0 : 0 ≤ C₀ / (1 + s.im ^ 2) := (norm_nonneg _).trans hG
    calc ‖cexp ((s - c) ^ 2) * H s / L s‖ = ‖H s‖ * ‖cexp ((s - c) ^ 2) / L s‖ := by
          rw [mul_comm (cexp _) (H s), mul_div_assoc, norm_mul]
      _ ≤ max C 0 * (C₀ / (1 + s.im ^ 2)) :=
          mul_le_mul ((hHb s h2).trans (le_max_left _ _)) hG (norm_nonneg _) (le_max_right _ _)
      _ = max C 0 * C₀ / (1 + s.im ^ 2) := by ring

/-! ### Ray class characters -/

section Hecke

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- For a nontrivial character the pole-cleared function `(s − 1) L(s, ψ)` vanishes at `1`. -/
theorem heckePoleCleared_one_of_ne_one {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    heckePoleCleared 𝔪 ψ 1 = 0 := by
  simp [heckePoleCleared, heckeThetaPoleCoefficient_eq_zero 𝔪 hψ]

/-- For the trivial character it is the residue `heckeDensity` at `1`. -/
theorem heckePoleCleared_one_one : heckePoleCleared 𝔪 1 1 = heckeDensity 𝔪 := by
  simp [heckePoleCleared, heckeThetaPoleCoefficient_one]

/-- The entire function whose zeros are the zeros of `L(s, ψ)` off `1`: `(s − 1) L(s, ψ)` for the
trivial character and `L(s, ψ)` otherwise. -/
def heckeZeroFunction (ψ : HeckeCharacter 𝔪) : ℂ → ℂ :=
  if ψ = 1 then heckePoleCleared 𝔪 ψ else heckeLFunction 𝔪 ψ

theorem differentiable_heckeZeroFunction (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeZeroFunction 𝔪 ψ) := by
  unfold heckeZeroFunction
  split_ifs with h
  · exact differentiable_heckePoleCleared 𝔪 ψ
  · exact differentiable_heckeLFunction 𝔪 h

/-- Off `1`, a zero of `L(s, ψ)` is a zero of the zero function. -/
theorem heckeLFunction_ne_zero_of_heckeZeroFunction_ne_zero {ψ : HeckeCharacter 𝔪} {ρ : ℂ}
    (hρ1 : ρ ≠ 1) (h : heckeZeroFunction 𝔪 ψ ρ ≠ 0) : heckeLFunction 𝔪 ψ ρ ≠ 0 := by
  intro h0
  apply h
  unfold heckeZeroFunction
  split_ifs
  · rw [heckePoleCleared_eq 𝔪 ψ hρ1, h0, mul_zero]
  · exact h0

/-- The zero function of the trivial character does not vanish at `1`. -/
theorem heckeZeroFunction_one_one_ne_zero : heckeZeroFunction 𝔪 1 1 ≠ 0 := by
  rw [heckeZeroFunction, if_pos rfl, heckePoleCleared_one_one]
  exact_mod_cast (heckeDensity_pos 𝔪).ne'

theorem heckeLFunction_ne_zero_of_one_lt_re (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeLFunction 𝔪 ψ s ≠ 0 := by
  rw [heckeLFunction_eq_heckeL 𝔪 ψ hs]
  exact heckeL_ne_zero 𝔪 ψ hs

theorem ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  rintro rfl
  rw [one_re] at hs
  exact lt_irrefl _ hs

end Hecke

/-- **The family step with reciprocal kernels.** If, whenever every `L(s, η)` of the ray class
characters of `K` is zero-free in `Re s > β` off `1`, each character has a sum with a direct bound
`Z^{a₁}` and a comparison `Z^{a₂}` with the signal of `exp((s − c)²) H_η(s)/L(s, η)`, `a₁, a₂ < β`
the same for all characters, and `H_η` is holomorphic and nonvanishing on `Re s > σ₀` and bounded
on `Re s ≥ 2`, then `HeckeHalfPlane K σ₀`. -/
theorem heckeHalfPlane_of_family_reciprocal_signal (K : Type*) [Field K] [NumberField K]
    {σ₀ : ℝ} (hσ₀ : σ₀ < 1) (c : ℝ) (H : (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) → ℂ → ℂ)
    (hH : ∀ η, DifferentiableOn ℂ (H η) {s : ℂ | σ₀ < s.re})
    (hH0 : ∀ η (s : ℂ), σ₀ < s.re → H η s ≠ 0)
    (hHb : ∀ η, ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖H η s‖ ≤ C)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re → ρ ≠ 1 →
        heckeLFunction η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (fun s : ℂ => cexp ((s - c) ^ 2) * H η s /
                heckeLFunction η.1 η.2 s) 2 Z‖ ≤ C * Z ^ a₂)) :
    HeckeHalfPlane K σ₀ := by
  have hopen : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const continuous_re
  have hHat : ∀ η (s : ℂ), 1 < s.re → DifferentiableAt ℂ (H η) s := fun η s hs =>
    (hH η).differentiableAt (hopen.mem_nhds (show σ₀ < s.re by linarith))
  have h := ne_zero_of_family_common_signal_of_zeros
    (ι := Σ 𝔫 : Modulus K, HeckeCharacter 𝔫)
    (G := fun η s => cexp ((s - c) ^ 2) * H η s / heckeLFunction η.1 η.2 s)
    (L := fun η => heckeZeroFunction η.1 η.2)
    (E := fun η s => cexp ((s - c) ^ 2) * H η s * (if η.2 = 1 then s - 1 else 1)) hσ₀
    (fun η => by
      obtain ⟨C, hC⟩ := hHb η
      exact isSignalKernel_gauss_mul_div_of_bounded (Real.exp_pos _)
        (fun s hs => differentiableAt_heckeLFunction η.1 η.2 (ne_one_of_one_lt_re hs))
        (fun s hs => heckeLFunction_ne_zero_of_one_lt_re η.1 η.2 hs)
        (fun s hs => by
          rw [heckeLFunction_eq_heckeL η.1 η.2 (by linarith : (1 : ℝ) < s.re)]
          exact exp_neg_le_norm_heckeL η.1 η.2 hs)
        (hHat η) hC c)
    (fun η => (differentiable_heckeZeroFunction η.1 η.2).differentiableOn)
    (fun η => by
      refine (((by fun_prop : Differentiable ℂ fun s : ℂ =>
        cexp ((s - c) ^ 2)).differentiableOn).mul (hH η)).mul ?_
      split_ifs
      · exact (differentiable_id.sub_const 1).differentiableOn
      · exact differentiableOn_const 1)
    (fun η s hs h0 => by
      refine mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (hH0 η s hs)) ?_
      split_ifs with hη
      · refine sub_ne_zero.mpr fun hs1 => ?_
        obtain ⟨𝔫, ψ⟩ := η
        simp only at hη h0 hs1
        rw [hη, hs1] at h0
        exact heckeZeroFunction_one_one_ne_zero 𝔫 h0
      · exact one_ne_zero)
    (fun η s hs => by
      have hL0 := heckeLFunction_ne_zero_of_one_lt_re η.1 η.2 hs
      show cexp ((s - c) ^ 2) * H η s / heckeLFunction η.1 η.2 s * heckeZeroFunction η.1 η.2 s =
        cexp ((s - c) ^ 2) * H η s * (if η.2 = 1 then s - 1 else 1)
      unfold heckeZeroFunction
      split_ifs
      · rw [heckePoleCleared_eq η.1 η.2 (ne_one_of_one_lt_re hs)]
        field_simp
      · field_simp)
    (fun β hβ hβ1 hfree => hstep β hβ hβ1 fun η ρ hρ hρ1 =>
      heckeLFunction_ne_zero_of_heckeZeroFunction_ne_zero η.1 hρ1 (hfree η ρ hρ))
  intro 𝔫 φ ρ hρ hρ1
  exact heckeLFunction_ne_zero_of_heckeZeroFunction_ne_zero 𝔫 hρ1 (h ⟨𝔫, φ⟩ ρ hρ)

/-- **The family step with reciprocal kernels and height estimates.** As
`heckeHalfPlane_of_family_reciprocal_signal`, with comparisons `K (Z^{β − m} (1 + Z^τ)^A +
Z^B (Z^τ)^{−N})` for every small `τ` and every `N`, `m > 0` common to the family and the orders
`A, B` depending on the character. -/
theorem heckeHalfPlane_of_family_reciprocal_height_estimates (K : Type*) [Field K]
    [NumberField K] {σ₀ : ℝ} (hσ₀ : σ₀ < 1) (c : ℝ)
    (H : (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) → ℂ → ℂ)
    (hH : ∀ η, DifferentiableOn ℂ (H η) {s : ℂ | σ₀ < s.re})
    (hH0 : ∀ η (s : ℂ), σ₀ < s.re → H η s ≠ 0)
    (hHb : ∀ η, ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖H η s‖ ≤ C)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re → ρ ≠ 1 →
        heckeLFunction η.1 η.2 ρ ≠ 0) →
      ∃ a₁ m : ℝ, a₁ < β ∧ 0 < m ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₁ A B τ₀ : ℝ), 1 ≤ Z₁ ∧ 0 ≤ A ∧ 0 < τ₀ ∧
            (∀ Z : ℝ, Z₁ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → ∀ N : ℕ, ∃ K' Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (fun s : ℂ => cexp ((s - c) ^ 2) * H η s /
                  heckeLFunction η.1 η.2 s) 2 Z‖ ≤
                K' * (Z ^ (β - m) * (1 + Z ^ τ) ^ A + Z ^ B * (Z ^ τ) ^ (-(N : ℝ)))) :
    HeckeHalfPlane K σ₀ := by
  refine heckeHalfPlane_of_family_reciprocal_signal K hσ₀ c H hH hH0 hHb
    fun β hβ hβ1 hfree => ?_
  obtain ⟨a₁, m, ha₁, hm, hη⟩ := hstep β hβ hβ1 hfree
  refine ⟨a₁, β - m / 2, ha₁, by linarith, fun η => ?_⟩
  obtain ⟨J, C, Z₁, A, B, τ₀, hZ₁, hA, hτ₀, hdirect, hcomp⟩ := hη η
  obtain ⟨K', Z₀, hZ₀, hK'⟩ := exists_bound_of_height_estimates hm hA hτ₀ hcomp
  refine ⟨J, max C K', max Z₁ Z₀, le_max_of_le_left hZ₁, fun Z hZ => ?_, fun Z hZ => ?_⟩
  · have hZpos : 0 < Z := by linarith [(le_max_left Z₁ Z₀).trans hZ]
    exact (hdirect Z ((le_max_left _ _).trans hZ)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hZpos.le _))
  · have hZpos : 0 < Z := by linarith [(le_max_left Z₁ Z₀).trans hZ]
    exact (hK' Z ((le_max_right _ _).trans hZ)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hZpos.le _))

/-- **The two estimates bound the zero abscissa**, with the reciprocal kernels of the source:
over `K = ℚ(ζ₃)`, a direct bound `Z^{a₁}` and a comparison `Z^{a₂}` with the signal of
`exp((s − c)²) H_η(s)/L(s, η)`, `a₁, a₂ < β` common to all ray class characters whenever the
family is zero-free in `Re s > β` off `1`, give `zetaZeroAbscissa ≤ σ₀`. -/
theorem zetaZeroAbscissa_le_of_two_reciprocal_estimates {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {σ₀ : ℝ} (hσ₀ : σ₀ < 1) (c : ℝ)
    (H : (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) → ℂ → ℂ)
    (hH : ∀ η, DifferentiableOn ℂ (H η) {s : ℂ | σ₀ < s.re})
    (hH0 : ∀ η (s : ℂ), σ₀ < s.re → H η s ≠ 0)
    (hHb : ∀ η, ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖H η s‖ ≤ C)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re → ρ ≠ 1 →
        heckeLFunction η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (fun s : ℂ => cexp ((s - c) ^ 2) * H η s /
                heckeLFunction η.1 η.2 s) 2 Z‖ ≤ C * Z ^ a₂)) :
    zetaZeroAbscissa ≤ σ₀ :=
  zetaZeroAbscissa_le_of_heckeHalfPlane_thirdCyclotomic
    (heckeHalfPlane_of_family_reciprocal_signal K hσ₀ c H hH hH0 hHb hstep)

end GaloisForLFunctions.FamilyContinuationTheory
