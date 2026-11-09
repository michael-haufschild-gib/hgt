import GaloisForLFunctions.RHTower.XiCriticalZeroLinearNodes
import GaloisForLFunctions.SignFreePurityMechanisms.CoefficientGapsSeparateTheRoots

/-!
# The zeros of `ζ` have no coefficient gaps

Separation by absolute value needs lacunary roots: a polynomial with coefficient gaps has at most
two zeros in an annulus `R ≤ |z| ≤ 9R`. The critical zeros of `ζ` are dense on that scale: some
dyadic range `(T, 2T]` contains three ordinates `τ₁ < τ₂ < τ₃` of zeros of `Ξ`
(`exists_three_critical_ordinates`). Hence no polynomial with coefficient gaps vanishes at
`τ₁², τ₂², τ₃²` (`exists_critical_ordinates_not_hasCoeffGaps`): in the variable `w = z²`, in which
the Riemann hypothesis is the reality of the zeros of `Ξ`, the archimedean Newton polygon cannot
certify any polynomial that interpolates one dyadic block of zeros.
-/

open Finset

namespace GaloisForLFunctions.SignFreePurityMechanisms

/-- Three ordinates of critical zeros within a factor two of each other. -/
theorem exists_three_critical_ordinates :
    ∃ τ₁ τ₂ τ₃ : ℝ, 0 < τ₁ ∧ τ₁ < τ₂ ∧ τ₂ < τ₃ ∧ τ₃ ≤ 2 * τ₁ ∧
      RHTower.Xi τ₁ = 0 ∧ RHTower.Xi τ₂ = 0 ∧ RHTower.Xi τ₃ = 0 := by
  obtain ⟨c₀, hc₀, T₀, -, h⟩ := RHTower.exists_many_critical_ordinates_dyadic
  -- a height at which the dyadic range carries at least three ordinates
  obtain ⟨T, hT0, hTe, hTc⟩ : ∃ T : ℝ, T₀ ≤ T ∧ Real.exp 1 ≤ T ∧ 3 / c₀ ≤ T :=
    ⟨max T₀ (max (Real.exp 1) (3 / c₀)), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨τS, hτS, hcard⟩ := h T hT0
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hTe
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hTe
  have h3 : 3 ≤ τS.card := by
    have h3c : 3 ≤ c₀ * T := by
      rw [div_le_iff₀ hc₀] at hTc
      linarith only [hTc]
    have hmul : c₀ * T ≤ c₀ * (T * Real.log T) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hTpos.le hlog) hc₀.le
    exact_mod_cast (h3c.trans hmul).trans hcard
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq h3
  have hmem : ∀ i, t.orderEmbOfFin htcard i ∈ τS := fun i => hts (t.orderEmbOfFin_mem htcard i)
  have h0 := hτS _ (hmem 0)
  have h1 := hτS _ (hmem 1)
  have h2 := hτS _ (hmem 2)
  refine ⟨_, _, _, hTpos.trans h0.1, (t.orderEmbOfFin htcard).strictMono (by decide),
    (t.orderEmbOfFin htcard).strictMono (by decide), ?_, h0.2.2, h1.2.2, h2.2.2⟩
  linarith only [h0.1, h2.2.1]

/-- **No coefficient-gap separation for `ζ`.** There are three critical ordinates such that no
polynomial with coefficient gaps vanishes at their squares. -/
theorem exists_critical_ordinates_not_hasCoeffGaps :
    ∃ τ₁ τ₂ τ₃ : ℝ, RHTower.Xi τ₁ = 0 ∧ RHTower.Xi τ₂ = 0 ∧ RHTower.Xi τ₃ = 0 ∧
      ∀ (a : ℕ → ℂ) (n : ℕ), HasCoeffGaps a n →
        ¬(gapPoly a n ((τ₁ : ℂ) ^ 2) = 0 ∧ gapPoly a n ((τ₂ : ℂ) ^ 2) = 0 ∧
          gapPoly a n ((τ₃ : ℂ) ^ 2) = 0) := by
  obtain ⟨τ₁, τ₂, τ₃, h0, h12, h23, h31, hz₁, hz₂, hz₃⟩ := exists_three_critical_ordinates
  refine ⟨τ₁, τ₂, τ₃, hz₁, hz₂, hz₃, fun a n hgaps => ?_⟩
  rintro ⟨hp₁, hp₂, hp₃⟩
  have hnorm : ∀ τ : ℝ, ‖((τ : ℂ)) ^ 2‖ = τ ^ 2 := fun τ => by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hlt := hgaps.nine_mul_norm_lt hp₁ hp₂ hp₃
    (by rw [hnorm, hnorm]; nlinarith only [h0, h12])
    (by rw [hnorm, hnorm]; nlinarith only [h0, h12, h23])
  rw [hnorm, hnorm] at hlt
  nlinarith only [hlt, h0, h31, h12, h23]

#print axioms exists_three_critical_ordinates
#print axioms exists_critical_ordinates_not_hasCoeffGaps

end GaloisForLFunctions.SignFreePurityMechanisms
