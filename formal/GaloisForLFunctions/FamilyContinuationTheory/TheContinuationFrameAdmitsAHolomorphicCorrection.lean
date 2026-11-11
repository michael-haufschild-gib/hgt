import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheRationalsContainsZeta

/-!
# The continuation frame admits a holomorphic correction

The signal of a completed sum is the Mellin integral of `Z^s exp((s − c)²) H(s)/((s − 1) L(s, ψ))`,
where `H` collects the local factors that the identity leaves over: holomorphic and nonvanishing
right of the boundary and bounded on `Re s ≥ 2`. The kernel with such a correction is a signal
kernel (`isSignalKernel_gauss_mul_div`), and the family step holds with it
(`heckeHalfPlane_of_family_corrected_signal`): if, whenever the pole-cleared Hecke `L`-functions
of `K` are zero-free in `Re s > β`, every ray class character has a sum with a direct bound
`Z^{a₁}` and a comparison `Z^{a₂}` with its corrected signal, `a₁, a₂ < β` common to all
characters, then `HeckeHalfPlane K σ₀`.
-/

noncomputable section

open Complex NumberField

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions

/-- **A Gaussian times a bounded correction over a function bounded below.** -/
theorem isSignalKernel_gauss_mul_div {L H : ℂ → ℂ} {m C : ℝ} (hm : 0 < m)
    (hL : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ L s) (hL0 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hlow : ∀ s : ℂ, 2 ≤ s.re → m ≤ ‖L s‖)
    (hH : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ H s) (hH0 : ∀ s : ℂ, 1 < s.re → H s ≠ 0)
    (hHb : ∀ s : ℂ, 2 ≤ s.re → ‖H s‖ ≤ C) (c : ℝ) :
    IsSignalKernel (fun s : ℂ => cexp ((s - c) ^ 2) * H s / L s) := by
  have hC : 0 < max C 1 := lt_max_of_lt_right one_pos
  have hfun : (fun s : ℂ => cexp ((s - c) ^ 2) * H s / L s) =
      fun s : ℂ => cexp ((s - c) ^ 2) / (L s / H s) := by
    funext s
    rw [div_div_eq_mul_div]
  rw [hfun]
  refine isSignalKernel_gauss_div (L := fun s => L s / H s) (div_pos hm hC)
    (fun s hs => (hL s hs).div (hH s hs) (hH0 s hs))
    (fun s hs => div_ne_zero (hL0 s hs) (hH0 s hs)) (fun s hs => ?_) c
  have hs1 : 1 < s.re := by linarith
  have hHpos : 0 < ‖H s‖ := norm_pos_iff.mpr (hH0 s hs1)
  rw [norm_div, div_le_div_iff₀ hC hHpos]
  exact mul_le_mul (hlow s hs) ((hHb s hs).trans (le_max_left _ _)) hHpos.le
    (hm.le.trans (hlow s hs))

/-- **The family step with corrected signals.** -/
theorem heckeHalfPlane_of_family_corrected_signal (K : Type*) [Field K] [NumberField K]
    {σ₀ : ℝ} (hσ₀ : σ₀ < 1) (c : ℝ) (H : (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) → ℂ → ℂ)
    (hH : ∀ η, DifferentiableOn ℂ (H η) {s : ℂ | σ₀ < s.re})
    (hH0 : ∀ η (s : ℂ), σ₀ < s.re → H η s ≠ 0)
    (hHb : ∀ η, ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖H η s‖ ≤ C)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re →
        heckePoleCleared η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (fun s : ℂ => cexp ((s - c) ^ 2) * H η s /
                heckePoleCleared η.1 η.2 s) 2 Z‖ ≤ C * Z ^ a₂)) :
    HeckeHalfPlane K σ₀ := by
  have hopen : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const continuous_re
  have hHat : ∀ η (s : ℂ), 1 < s.re → DifferentiableAt ℂ (H η) s := fun η s hs =>
    (hH η).differentiableAt (hopen.mem_nhds (show σ₀ < s.re by linarith))
  have h := ne_zero_of_family_common_signal
    (ι := Σ 𝔫 : Modulus K, HeckeCharacter 𝔫)
    (G := fun η s => cexp ((s - c) ^ 2) * H η s / heckePoleCleared η.1 η.2 s)
    (L := fun η => heckePoleCleared η.1 η.2)
    (E := fun η s => cexp ((s - c) ^ 2) * H η s) hσ₀
    (fun η => by
      obtain ⟨C, hC⟩ := hHb η
      exact isSignalKernel_gauss_mul_div (Real.exp_pos _)
        (fun s _ => differentiable_heckePoleCleared η.1 η.2 s)
        (fun _ hs => heckePoleCleared_ne_zero_of_one_lt_re η.1 η.2 hs)
        (fun _ hs => exp_neg_le_norm_heckePoleCleared η.1 η.2 hs)
        (hHat η) (fun s hs => hH0 η s (by linarith)) hC c)
    (fun η => (differentiable_heckePoleCleared η.1 η.2).differentiableOn)
    (fun η => ((by fun_prop : Differentiable ℂ fun s : ℂ =>
      cexp ((s - c) ^ 2)).differentiableOn).mul (hH η))
    (fun η s hs => mul_ne_zero (Complex.exp_ne_zero _) (hH0 η s hs))
    (fun η s hs => div_mul_cancel₀ _ (heckePoleCleared_ne_zero_of_one_lt_re η.1 η.2 hs))
    hstep
  intro 𝔫 φ ρ hρ hρ1 h0
  apply h ⟨𝔫, φ⟩ ρ hρ
  show heckePoleCleared 𝔫 φ ρ = 0
  rw [heckePoleCleared_eq 𝔫 φ hρ1, h0, mul_zero]

end GaloisForLFunctions.FamilyContinuationTheory
