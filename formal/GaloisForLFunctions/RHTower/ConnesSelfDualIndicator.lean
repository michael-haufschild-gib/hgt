import Mathlib

/-!
# Appendix II (22)-(24): the ring of integers is self-dual

Appendix II (22)-(24) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  with the character `α` normalised by `α/R = 1`, `α/π^{-1}R ≠ 1`, and the self-dual Haar measure,
  one has `F(1_R) = 1_R`.                                                          (24)

The proof needs nothing about local fields: a non-trivial character integrates to zero over a
subgroup (translation invariance), and a character trivial on the subgroup integrates to its mass.
So the statement here is for an arbitrary commutative ring with a translation-invariant measure,
an additive subgroup `R` of mass one closed under multiplication, and an additive character `α`
that is trivial on `R` and non-trivial on `xR` for every `x ∉ R` - Connes' two normalisations
(22).
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {K : Type*} [CommRing K] [MeasurableSpace K] [MeasurableAdd K]
  {μ : Measure K} [μ.IsAddLeftInvariant]

/-- **A non-trivial character integrates to zero over a subgroup.** -/
theorem connes_character_setIntegral_eq_zero {R : AddSubgroup K}
    (hR : MeasurableSet (R : Set K)) {ψ : K → ℂ}
    (hψ : ∀ a b : K, ψ (a + b) = ψ a * ψ b)
    {y₀ : K} (hy₀ : y₀ ∈ R) (hne : ψ y₀ ≠ 1) :
    (∫ y in (R : Set K), ψ y ∂μ) = 0 := by
  have hind : (∫ y in (R : Set K), ψ y ∂μ) = ∫ y : K, Set.indicator (R : Set K) ψ y ∂μ :=
    (MeasureTheory.integral_indicator hR).symm
  have hshift : (∫ y : K, Set.indicator (R : Set K) ψ (y₀ + y) ∂μ)
      = ∫ y : K, Set.indicator (R : Set K) ψ y ∂μ :=
    MeasureTheory.integral_add_left_eq_self (fun y : K => Set.indicator (R : Set K) ψ y) y₀
  have hpt : ∀ y : K, Set.indicator (R : Set K) ψ (y₀ + y)
      = ψ y₀ * Set.indicator (R : Set K) ψ y := by
    intro y
    by_cases hy : y ∈ (R : Set K)
    · have hmem : y₀ + y ∈ (R : Set K) := R.add_mem hy₀ hy
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hy, hψ]
    · have hmem : y₀ + y ∉ (R : Set K) := by
        intro hc
        exact hy (by simpa using R.add_mem (R.neg_mem hy₀) hc)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hy, mul_zero]
  have hstep : (∫ y : K, Set.indicator (R : Set K) ψ y ∂μ)
      = ψ y₀ * ∫ y : K, Set.indicator (R : Set K) ψ y ∂μ := by
    conv_lhs => rw [← hshift]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul]
  have hfactor : (1 - ψ y₀) * (∫ y : K, Set.indicator (R : Set K) ψ y ∂μ) = 0 := by
    rw [sub_mul, one_mul, ← hstep, sub_self]
  have hne0 : (1 : ℂ) - ψ y₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [hind]
  exact (mul_eq_zero.mp hfactor).resolve_left hne0

/-- **Appendix II (24).**  With Connes' normalisations, the Fourier transform of the indicator of
`R` is the indicator of `R`. -/
theorem connes_selfDual_indicator {R : AddSubgroup K}
    (hR : MeasurableSet (R : Set K)) (hmass : μ.real (R : Set K) = 1)
    {α : K → ℂ} (hαadd : ∀ a b : K, α (a + b) = α a * α b)
    (hαtriv : ∀ y ∈ R, α y = 1)
    (hRmul : ∀ x ∈ R, ∀ y ∈ R, x * y ∈ R)
    (hnontriv : ∀ x : K, x ∉ R → ∃ y ∈ R, α (x * y) ≠ 1)
    (x : K) :
    (∫ y in (R : Set K), α (x * y) ∂μ)
      = Set.indicator (R : Set K) (fun _ : K => (1 : ℂ)) x := by
  by_cases hx : x ∈ (R : Set K)
  · rw [Set.indicator_of_mem hx]
    have hone : ∀ y ∈ (R : Set K), α (x * y) = 1 := by
      intro y hy
      exact hαtriv _ (hRmul x hx y hy)
    rw [MeasureTheory.setIntegral_congr_fun hR hone, MeasureTheory.setIntegral_const,
      hmass, one_smul]
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨y₀, hy₀, hne⟩ := hnontriv x hx
    refine connes_character_setIntegral_eq_zero hR ?_ hy₀ hne
    intro a b
    rw [mul_add, hαadd]

end

end GaloisForLFunctions.RHTower
