import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleSchurDefect

/-!
# Sharp phase-preserving Schur control for the actual prime transport

The prime number theorem bounds the full row potential, not just the operator
norm. Thus the sharp asymptotic envelope pays simultaneously for the prime
Rayleigh pairing and every complex prime-edge defect. No coefficient, degree,
pole-orthogonality, or unproved arithmetic estimate is assumed.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct BigOperators
noncomputable section
namespace RHTower

/-- One sharp asymptotic budget controls all actual prime edges and every
aperture vector simultaneously. The edge term retains all complex phases. -/
theorem exists_ccmPrimePoleSchurEnergy_add_prime_le_one_add (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      ∀ f : suzukiApertureHilbert a,
        ccmPrimePoleSchurEnergy a f.1 + (inner ℂ (ccmFinitePrimeOperator a f) f).re ≤
          (1 + ε) * Real.exp a.1 * ‖f‖ ^ 2 := by
  have hev : ∀ᶠ x : ℝ in atTop, chebyshevPsiReal x / x < 1 + ε / 2 :=
    tendsto_chebyshevPsiReal_div (Iio_mem_nhds (by linarith))
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp hev
  let x₀ := max x₁ 1
  let D := Chebyshev.psi x₀
  have hD0 : 0 ≤ D := Chebyshev.psi_nonneg _
  let K := Real.log 4 + 4
  have hK0 : 0 ≤ K := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [K]
    linarith
  have hψ : ∀ X : ℝ, 1 ≤ X →
      Chebyshev.psi X ≤ (1 + ε / 2) * X + 0 * Real.sqrt X + D := by
    intro X hX
    by_cases hXx : x₀ ≤ X
    · have h1 := hx₁ X (le_trans (le_max_left _ _) hXx)
      have hident : chebyshevPsiReal X = Chebyshev.psi X := by
        rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_Icc]
        congr 1
        ext n
        simp
      rw [hident, div_lt_iff₀ (by linarith)] at h1
      nlinarith
    · have hmono := Chebyshev.psi_mono (le_of_lt (lt_of_not_ge hXx))
      change Chebyshev.psi X ≤ D at hmono
      nlinarith
  refine ⟨16 / ε + 8 * (D + K) / ε + 1, fun a haA f => ?_⟩
  have ha1 : 1 ≤ a.1 := by
    have : 0 ≤ 16 / ε + 8 * (D + K) / ε := by positivity
    linarith
  have hquad := Real.quadratic_le_exp_of_nonneg (show 0 ≤ a.1 by linarith)
  have hA1 : 16 / ε ≤ a.1 := by
    have : 0 ≤ 8 * (D + K) / ε := by positivity
    linarith
  have hA2 : 8 * (D + K) / ε ≤ a.1 := by
    have : 0 ≤ 16 / ε := by positivity
    linarith
  have h1 : 16 ≤ ε * a.1 := by
    rw [div_le_iff₀ hε] at hA1
    linarith
  have h2 : 8 * (D + K) ≤ ε * a.1 := by
    rw [div_le_iff₀ hε] at hA2
    linarith
  have hkey : 2 * a.1 + D + K ≤ ε / 2 * Real.exp a.1 := by
    nlinarith [mul_le_mul_of_nonneg_left ha1 hε.le]
  rw [ccmPrimePoleSchurEnergy_add_prime_eq_rowPotential]
  apply ccmPrimePoleRowPotential_le_of_row
  intro x hx
  have hrow := primePoleRow_le a (1 + ε / 2) 0 D K le_rfl
    (fun X hX _ => hψ X hX)
    (fun X hX _ => ccmReciprocalMangoldtCumulative_le_log_add X hX) hx
  apply hrow.trans
  apply mul_le_mul_of_nonneg_right _ (primePoleProfile_pos x).le
  nlinarith

/-- The sharp envelope strengthens the actual signed source bound by the
complete nonnegative prime-edge energy, with the mixed pole pairing retained. -/
theorem exists_ccmRestrictedWeilSource_ge_sharp_schurEdgeEnergy (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      ∀ u : CCMArchimedeanFormDomain a,
        let f := ccmArchimedeanFormToAperture a u
        ‖u.1‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1 - (1 + ε) * Real.exp a.1) * ‖f‖ ^ 2 +
          (inner ℂ (ccmPolarOperator a f) f).re + ccmPrimePoleSchurEnergy a f.1 ≤
            ccmRestrictedWeilSourceQuadratic a u := by
  obtain ⟨A, hA⟩ := exists_ccmPrimePoleSchurEnergy_add_prime_le_one_add ε hε
  refine ⟨A, fun a ha u => ?_⟩
  let f := ccmArchimedeanFormToAperture a u
  have he := hA a ha f
  rw [ccmRestrictedWeilSourceQuadratic_eq_formNorm_sq_add_boundedDiagonal]
  unfold ccmRestrictedWeilBoundedDiagonal
  rw [inner_ccmRestrictedWeilBoundedRemainder, Complex.sub_re, Complex.add_re]
  have hself : (ccmArchimedeanRemainderScalar * inner ℂ f f).re =
      (2 * gammaHardyPhaseRate 0 - 1) * ‖f‖ ^ 2 := by
    have hff : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]
      norm_cast
    unfold ccmArchimedeanRemainderScalar
    rw [hff, ← Complex.ofReal_mul, Complex.ofReal_re]
  dsimp only
  change _ ≤ ‖u.1‖ ^ 2 +
    ((ccmArchimedeanRemainderScalar * inner ℂ f f).re +
      (inner ℂ (ccmPolarOperator a f) f).re -
      (inner ℂ (ccmFinitePrimeOperator a f) f).re)
  rw [hself]
  nlinarith

end RHTower
