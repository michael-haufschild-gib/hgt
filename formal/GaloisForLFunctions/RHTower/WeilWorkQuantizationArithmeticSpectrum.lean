import GaloisForLFunctions.RHTower.WeilWorkQuantizationPhaseCoupling

/-!
# Arithmetic frequencies forced by the actual residual phase

A nonrigid source requires an active nonzero rational-log frequency in every
weighted countable phase representation. Every periodic base therefore has a
rational positive power. The source-only alternatives do not assume or produce
a representation, coefficient sign, or discrete spectral measure.
-/

open Complex
noncomputable section
namespace RHTower.WeilSpectral
open IntegerMassRigidity AbelianTwist GaloisForLFunctions.HTGeometry

/-- With no active nonzero arithmetic frequency, the exact rows isolate the
same nonzero scalar times every forward coefficient. -/
theorem quantization_rigidity_of_no_arithmetic_frequency {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' j, p j * cexp (((ω j * x : ℝ) : ℂ) * I))
    (hno : ¬∃ j : ι, ∃ m n : ℕ, p j ≠ 0 ∧ 1 ≤ m ∧ 1 ≤ n ∧ m ≠ n ∧
      ω j = 2 * Real.log ((m : ℝ) / n)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  classical
  let c : ℂ := ∑' j, if ω j = 0 then p j else 0
  have hsum (m : ℕ) (hm : 1 ≤ m) :
      (∑' j, p j * quantizationFrequencyResidue lam (ω j) m) =
        c * dirichletExp (lamLog lam) m := by
    rw [show c * dirichletExp (lamLog lam) m =
      ∑' j, (if ω j = 0 then p j else 0) * dirichletExp (lamLog lam) m from
        tsum_mul_right.symm]
    apply tsum_congr
    intro j
    by_cases hpj : p j = 0
    · simp [hpj]
    by_cases hω : ω j = 0
    · simp [hω, quantizationFrequencyResidue_zero hm]
    have hnone : ¬∃ n, quantizationFrequencyResonates (ω j) m n := by
      rintro ⟨n, hn, he⟩
      have hmn : m ≠ n := by
        intro h
        subst m
        exact hω (by linarith)
      apply hno ⟨j, m, n, hpj, hm, hn, hmn, ?_⟩
      rw [Real.log_div (by exact_mod_cast (show m ≠ 0 by omega))
        (by exact_mod_cast (show n ≠ 0 by omega))]
      linarith
    simp only [quantizationFrequencyResidue, dif_neg hnone, if_neg hω, mul_zero, zero_mul]
  obtain ⟨hne, hrows⟩ := quantization_phase_resonance_constant hW hp hphase
  rw [hsum 1 le_rfl, dirichletExp_one (lamLog_zero lam) (lamLog_one lam), mul_one] at hne hrows
  have hone (m : ℕ) (hm : m ≠ 0) : dirichletExp (lamLog lam) m = 1 := by
    have he := hrows m (Nat.one_le_iff_ne_zero.mpr hm)
    rw [hsum m (Nat.one_le_iff_ne_zero.mpr hm)] at he
    exact mul_left_cancel₀ hne (he.trans (mul_one c).symm)
  exact vonMangoldt_and_RH_of_coeff_eq_one
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ)
    (differentiableOn_weilContinuation hW) (fun _ hs => quantizationContinuation_eq_arch hW hs)
    (fun _ hs => hasDerivAt_quantizationCompletion hW hs) (quantizationCompletion_two hW) hone

/-- Unconditional source alternative: every representation of a nonrigid
canonical phase contains an active nonzero rational-log frequency. -/
theorem quantization_rigidity_or_arithmetic_frequency {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ (ι : Type) [Countable ι] (p : ι → ℂ) (ω : ι → ℝ),
        Summable (fun j => ‖p j‖ * Real.exp (|ω j| / 2)) →
        (∀ x : ℝ, 0 < x →
          cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
            ∑' j, p j * cexp (((ω j * x : ℝ) : ℂ) * I)) →
        ∃ j : ι, ∃ m n : ℕ, p j ≠ 0 ∧ 1 ≤ m ∧ 1 ≤ n ∧ m ≠ n ∧
          ω j = 2 * Real.log ((m : ℝ) / n) := by
  classical
  by_cases hR : (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis
  · exact Or.inl hR
  · right
    intro ι _ p ω hp hphase
    by_contra hno
    exact hR (quantization_rigidity_of_no_arithmetic_frequency hW hp hphase hno)

/-- A nonzero arithmetic harmonic makes a positive power of the base rational. -/
theorem quantization_rational_power_of_arithmetic_harmonic {r : ℝ} (hr : 1 < r)
    {k : ℤ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n)
    (he : 2 * (k : ℝ) * Real.log r = 2 * Real.log ((m : ℝ) / n)) :
    ∃ j m n : ℕ, 1 ≤ j ∧ 1 ≤ m ∧ 1 ≤ n ∧ r ^ j = (m : ℝ) / n := by
  have hr0 : 0 < r := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk : k ≠ 0 := by
    intro hk
    rw [hk, Int.cast_zero, mul_zero, zero_mul,
      Real.log_div hm0.ne' hn0.ne'] at he
    have heq : Real.log (m : ℝ) = Real.log (n : ℝ) := by linarith
    have hexp := congrArg Real.exp heq
    rw [Real.exp_log hm0, Real.exp_log hn0] at hexp
    exact hmn (by exact_mod_cast hexp)
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · have hj : 1 ≤ j := by omega
    refine ⟨j, m, n, hj, hm, hn, ?_⟩
    have hl : Real.log (r ^ j) = Real.log ((m : ℝ) / n) := by
      rw [Real.log_pow]
      simp only [Int.cast_natCast] at he
      linarith
    have h := congrArg Real.exp hl
    simpa only [Real.exp_log (pow_pos hr0 j), Real.exp_log (div_pos hm0 hn0)] using h
  · have hj : 1 ≤ j := by omega
    refine ⟨j, n, m, hj, hn, hm, ?_⟩
    have hl : Real.log (r ^ j) = Real.log ((n : ℝ) / m) := by
      rw [Real.log_pow, Real.log_div hn0.ne' hm0.ne']
      rw [Real.log_div hm0.ne' hn0.ne'] at he
      simp only [Int.cast_neg, Int.cast_natCast] at he
      linarith
    have h := congrArg Real.exp hl
    simpa only [Real.exp_log (pow_pos hr0 j), Real.exp_log (div_pos hn0 hm0)] using h

/-- Every exponentially summable periodic representation of a nonrigid actual
source has a rational positive power of its base. -/
theorem quantization_rigidity_or_rational_period_power {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ r : ℝ, 1 < r → ∀ p : ℤ → ℂ,
        Summable (fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log r| / 2)) →
        (∀ x : ℝ, 0 < x →
          cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
            ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log r * x : ℝ) : ℂ) * I)) →
        ∃ j m n : ℕ, 1 ≤ j ∧ 1 ≤ m ∧ 1 ≤ n ∧ r ^ j = (m : ℝ) / n := by
  rcases quantization_rigidity_or_arithmetic_frequency hW with hR | hfreq
  · exact Or.inl hR
  · right
    intro r hr p hp hphase
    obtain ⟨k, m, n, _, hm, hn, hmn, he⟩ :=
      hfreq ℤ p (fun k => 2 * (k : ℝ) * Real.log r) hp hphase
    exact quantization_rational_power_of_arithmetic_harmonic hr hm hn hmn he

end RHTower.WeilSpectral
