import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheRationalsContainsZeta

/-!
# The height is chosen after the target

The comparison of a completed sum `J` with a signal `f` is proved with an auxiliary height
`T₁ = Z^τ`: for every small `τ > 0` and every order `N`,

`‖J(Z) − f(Z)‖ ≤ K (Z^{c − m} (1 + Z^τ)^A + Z^B (Z^τ)^{−N})`  for large `Z`,

where `J` and `f` do not depend on `τ` and `N`. Taking `τ ≤ m/(4(A + 1))` and then `N` with
`B − τN ≤ c − m/2` gives `‖J(Z) − f(Z)‖ ≤ K' Z^{c − m/2}` (`exists_bound_of_height_estimates`).
The saving `m/2` does not depend on the orders `A`, `B`, so it is common to a family in which
these orders vary with the member.

`heckeHalfPlane_of_family_height_estimates` is the family step for the ray class characters of
a number field with comparisons of this form: a direct bound `Z^{a₁}`, `a₁ < β`, and a height
comparison with exponent `β − m`, `m > 0` common to the family, give `HeckeHalfPlane K σ₀`.
-/

noncomputable section

open Complex NumberField

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions

/-- **Late choice of the height.** A comparison with losses `(1 + Z^τ)^A` and `Z^B (Z^τ)^{−N}`,
valid for every `τ ∈ (0, τ₀]` and every `N`, keeps half of its saving. -/
theorem exists_bound_of_height_estimates {E : Type*} [NormedAddCommGroup E] {J f : ℝ → E}
    {c m A B τ₀ : ℝ} (hm : 0 < m) (hA : 0 ≤ A) (hτ₀ : 0 < τ₀)
    (h : ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → ∀ N : ℕ, ∃ K Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ‖J Z - f Z‖ ≤ K * (Z ^ (c - m) * (1 + Z ^ τ) ^ A + Z ^ B * (Z ^ τ) ^ (-(N : ℝ)))) :
    ∃ K Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z - f Z‖ ≤ K * Z ^ (c - m / 2) := by
  have hA1 : 0 < A + 1 := by linarith
  -- the height exponent: `τ A ≤ m/4`
  set τ := min τ₀ (m / (4 * (A + 1))) with hτdef
  have hτpos : 0 < τ := lt_min hτ₀ (by positivity)
  have hτA : τ * A ≤ m / 4 := by
    have h1 : τ ≤ m / (4 * (A + 1)) := min_le_right _ _
    have h2 : τ * (4 * (A + 1)) ≤ m := (le_div_iff₀ (by positivity)).mp h1
    nlinarith
  -- the order: `B − τ N ≤ c − m/2`
  set N := ⌈(B - c + m / 2) / τ⌉₊ with hNdef
  have hN : B - τ * (N : ℝ) ≤ c - m / 2 := by
    have h1 : (B - c + m / 2) / τ ≤ (N : ℝ) := Nat.le_ceil _
    have h2 : B - c + m / 2 ≤ (N : ℝ) * τ := (div_le_iff₀ hτpos).mp h1
    linarith
  obtain ⟨K, Z₀, hZ₀, hK⟩ := h τ hτpos (min_le_left _ _) N
  refine ⟨max K 0 * (2 ^ A + 1), Z₀, hZ₀, fun Z hZ => ?_⟩
  have hZ1 : (1 : ℝ) ≤ Z := hZ₀.trans hZ
  have hZ0 : 0 < Z := by linarith
  have hpow1 : (1 : ℝ) ≤ Z ^ τ := Real.one_le_rpow hZ1 hτpos.le
  -- the first term
  have hfirst : Z ^ (c - m) * (1 + Z ^ τ) ^ A ≤ 2 ^ A * Z ^ (c - m / 2) := by
    have h1 : (1 + Z ^ τ) ^ A ≤ (2 * Z ^ τ) ^ A :=
      Real.rpow_le_rpow (by positivity) (by linarith) hA
    have h2 : (2 * Z ^ τ) ^ A = 2 ^ A * Z ^ (τ * A) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hZ0.le]
    have h3 : Z ^ (c - m) * Z ^ (τ * A) ≤ Z ^ (c - m / 2) := by
      rw [← Real.rpow_add hZ0]
      exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    calc Z ^ (c - m) * (1 + Z ^ τ) ^ A ≤ Z ^ (c - m) * (2 ^ A * Z ^ (τ * A)) := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ A * (Z ^ (c - m) * Z ^ (τ * A)) := by ring
      _ ≤ 2 ^ A * Z ^ (c - m / 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
  -- the second term
  have hsecond : Z ^ B * (Z ^ τ) ^ (-(N : ℝ)) ≤ Z ^ (c - m / 2) := by
    rw [← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hX : Z ^ (c - m) * (1 + Z ^ τ) ^ A + Z ^ B * (Z ^ τ) ^ (-(N : ℝ)) ≤
      (2 ^ A + 1) * Z ^ (c - m / 2) := by linarith
  have hX0 : 0 ≤ Z ^ (c - m) * (1 + Z ^ τ) ^ A + Z ^ B * (Z ^ τ) ^ (-(N : ℝ)) := by positivity
  calc ‖J Z - f Z‖
      ≤ K * (Z ^ (c - m) * (1 + Z ^ τ) ^ A + Z ^ B * (Z ^ τ) ^ (-(N : ℝ))) := hK Z hZ
    _ ≤ max K 0 * (Z ^ (c - m) * (1 + Z ^ τ) ^ A + Z ^ B * (Z ^ τ) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
    _ ≤ max K 0 * ((2 ^ A + 1) * Z ^ (c - m / 2)) :=
        mul_le_mul_of_nonneg_left hX (le_max_right _ _)
    _ = max K 0 * (2 ^ A + 1) * Z ^ (c - m / 2) := by ring

/-- **The family step with height estimates.** If, whenever all pole-cleared Hecke `L`-functions
of `K` are zero-free in `Re s > β`, there are `a₁ < β` and `m > 0` such that each ray class
character has a sum `J` with `‖J(Z)‖ ≤ C Z^{a₁}` and, for every small `τ` and every `N`, a
comparison `K (Z^{β − m} (1 + Z^τ)^A + Z^B (Z^τ)^{−N})` with its signal, the orders `A`, `B`
depending on the character, then `HeckeHalfPlane K σ₀`. -/
theorem heckeHalfPlane_of_family_height_estimates (K : Type*) [Field K] [NumberField K]
    {σ₀ : ℝ} (hσ₀ : σ₀ < 1) (c : ℝ)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re →
        heckePoleCleared η.1 η.2 ρ ≠ 0) →
      ∃ a₁ m : ℝ, a₁ < β ∧ 0 < m ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₁ A B τ₀ : ℝ), 1 ≤ Z₁ ∧ 0 ≤ A ∧ 0 < τ₀ ∧
            (∀ Z : ℝ, Z₁ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → ∀ N : ℕ, ∃ K' Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (heckePoleClearedKernel η.1 η.2 c) 2 Z‖ ≤
                K' * (Z ^ (β - m) * (1 + Z ^ τ) ^ A + Z ^ B * (Z ^ τ) ^ (-(N : ℝ)))) :
    HeckeHalfPlane K σ₀ := by
  refine heckeHalfPlane_of_family_common_signal K hσ₀ c fun β hβ hβ1 hfree => ?_
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

end GaloisForLFunctions.FamilyContinuationTheory
