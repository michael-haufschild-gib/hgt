import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheConductorTwoIsTheFirstExcitation
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin

/-!
# The hyperplane gap is the selective margin

A **uniform pole-hyperplane gap** of a weight is a constant `g` such that for every `ε > 0`,
eventually in `N`, its atomic prime form is at most `(log N − γ − g + ε)|x|²` on the harmonic
hyperplane `Σ_{n ≤ N} x_n/√n = 0` (`HasHyperplaneGap`). It is the quantity that pays the full Weil
form beyond the Robin–Euler point (`ThePoleHyperplaneSeparatesTheFullWeilForms`). Its possible
values are now pinned on both sides.

* **`ζ` has one** (`zeta_hasHyperplaneGap`): some `g > 0` (RenormalizedArithmeticPotentialTheory).
* **Every gap of `ζ` is at most `2 log 2`** (`le_two_mul_log_two_of_hasHyperplaneGap`): the
  conductor-`2` excitation reaches `log N − γ − 2 log 2` on the hyperplane.
* **The Liouville twin has none** (`not_liouville_hasHyperplaneGap`): its prime form reaches the
  ceiling `log N − γ` on the same hyperplane, so no `g > 0` is a gap for it.

So the hyperplane gap is a twin-selective quantity with value in `(0, 2 log 2]` for `ζ` and no
positive value for its Liouville twin. Both are attained exactly, `2 log 2` and `0`, in
`TheSelectiveMarginIsTwoLogTwo`.
-/

noncomputable section

open Finset Filter

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

/-- `g` is a **uniform pole-hyperplane gap** of the gauge `ω`: for every `ε > 0`, eventually in `N`,
`P_N(ωx) ≤ (log N − γ − g + ε)|x|²` whenever `Σ_{n ≤ N} x_n/√n = 0`. -/
def HasHyperplaneGap (ω : ℕ → ℝ) (g : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
    atomicWeilForm N (fun n => ω n * x n) ≤ (Real.log N - γ - g + ε) * ∑ n ∈ Icc 1 N, x n ^ 2

/-- **`ζ` has a positive hyperplane gap.** -/
theorem zeta_hasHyperplaneGap : ∃ g : ℝ, 0 < g ∧ HasHyperplaneGap (fun _ => 1) g := by
  obtain ⟨g, hg, h⟩ := exists_atomicWeilForm_le_of_pole_orthogonal
  exact ⟨g, hg, fun ε hε => by
    obtain ⟨N₀, hN₀⟩ := h ε hε
    exact ⟨N₀, fun N hN x hx => by simpa only [one_mul] using hN₀ N hN x hx⟩⟩

/-- **Every hyperplane gap of `ζ` is at most `2 log 2`.** -/
theorem le_two_mul_log_two_of_hasHyperplaneGap {g : ℝ} (hg : HasHyperplaneGap (fun _ => 1) g) :
    g ≤ 2 * Real.log 2 := by
  by_contra hlt
  rw [not_le] at hlt
  set ε := (g - 2 * Real.log 2) / 4
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨N₀, hN₀⟩ := hg ε hε
  obtain ⟨N, hN, x, hx, hmass, hge⟩ :=
    ((eventually_ge_atTop N₀).and (eventually_exists_harmonic_atomicWeilForm_ge hε)).exists
  have hle := hN₀ N hN x hx
  simp only [one_mul] at hle
  have : (Real.log N - γ - 2 * Real.log 2 - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
      (Real.log N - γ - g + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := hge.trans hle
  have h2 := le_of_mul_le_mul_right this hmass
  simp only [ε] at h2
  linarith

/-- **The Liouville twin has no positive hyperplane gap**: its prime form reaches the ceiling
`log N − γ` on the harmonic hyperplane. -/
theorem not_liouville_hasHyperplaneGap {g : ℝ} (hg : 0 < g) :
    ¬ HasHyperplaneGap liouvilleSign g := by
  intro h
  obtain ⟨_, _, hsep⟩ := exists_pole_hyperplane_separates_liouville
  set ε := g / 4
  have hε : 0 < ε := by positivity
  obtain ⟨N₁, hN₁⟩ := h ε hε
  obtain ⟨N₂, hN₂⟩ := hsep ε hε
  obtain ⟨-, x, hx, hmass, hliou⟩ := hN₂ (max N₁ N₂) (le_max_right _ _)
  have hle := hN₁ (max N₁ N₂) (le_max_left _ _) x hx
  have h2 := le_of_mul_le_mul_right (hliou.trans hle) hmass
  simp only [ε] at h2
  linarith

/-- **The hyperplane gap is the selective margin**: `ζ` has a hyperplane gap, every one of its
hyperplane gaps lies in `(0, 2 log 2]` when positive, and the Liouville twin has no positive one. -/
theorem hyperplaneGap_selective :
    (∃ g : ℝ, 0 < g ∧ HasHyperplaneGap (fun _ => 1) g) ∧
      (∀ g : ℝ, HasHyperplaneGap (fun _ => 1) g → g ≤ 2 * Real.log 2) ∧
      ∀ g : ℝ, 0 < g → ¬ HasHyperplaneGap liouvilleSign g :=
  ⟨zeta_hasHyperplaneGap, fun _ hg => le_two_mul_log_two_of_hasHyperplaneGap hg,
    fun _ hg => not_liouville_hasHyperplaneGap hg⟩

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
