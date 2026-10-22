import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorAbelProducer
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreFiniteContactWidthClassification
import GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH

/-!
# Subpower criterion for the literal Möbius divisor Abel moment

A power bound of exponent `α < 1/2` on the normalized signed moment confines Xi zeros
to `Re ρ ≤ 1/2 + α`. Bounds for every positive exponent are therefore equivalent to RH.
The proof retains the Euler boundary and polar lattice defect, then uses interpolation
of the critical Mellin resolvent between integer logarithms.
-/

open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The normalized literal signed Abel moment admits every positive power bound. -/
def MobiusDivisorSquareRootAbelSubpower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
    |mobiusDivisorSquareRootAbelMoment M / M| ≤ C * (M : ℝ) ^ ε

/-- The exact source-to-resolvent comparison loses only a fixed additive constant. -/
theorem abs_resolvent_log_nat_le_mobiusDivisorSquareRootAbel
    {M : ℕ} (hM : 2 ≤ M) :
    |criticalMellinChebyshevResolventSource (Real.log M)| ≤
      2 * |mobiusDivisorSquareRootAbelMoment M / M| +
        2 * (|2 * Real.eulerMascheroniConstant| + 1) := by
  have hM1 : 1 ≤ M := by omega
  have hMR : (0 : ℝ) < M := by positivity
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hsqrtSq := Real.sq_sqrt hMR.le
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt M := by
    nlinarith [Real.sqrt_nonneg (M : ℝ)]
  have hsqrtLe : Real.sqrt M ≤ (M : ℝ) := by
    nlinarith [Real.sqrt_nonneg (M : ℝ)]
  have hgamma : |(2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M| ≤
      |2 * Real.eulerMascheroniConstant| := by
    rw [abs_div, abs_mul, abs_of_pos hMR,
      abs_of_nonneg (sub_nonneg.mpr hsqrtOne)]
    apply (div_le_iff₀ hMR).2
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hlattice : |coherentSquareRootPolarLatticeDefect M / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hMR]
    exact (div_le_one hMR).2
      ((abs_coherentSquareRootPolarLatticeDefect_le hM1).trans hsqrtLe)
  have hsource := congrArg (fun x : ℝ => x / (M : ℝ))
    (mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary hM1)
  rw [add_div] at hsource
  have hcharge := coherentCompletedOutgoing_eq_abel_add_latticeDefect_div hM
  rw [add_div] at hcharge
  have hres := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM
  have hexact : criticalMellinChebyshevResolventSource (Real.log M) =
      2 * (mobiusDivisorSquareRootAbelMoment M / M -
        (2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M +
        coherentSquareRootPolarLatticeDefect M / M) := by linarith
  rw [hexact, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsub : |mobiusDivisorSquareRootAbelMoment M / M -
      (2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M| ≤
      |mobiusDivisorSquareRootAbelMoment M / M| +
        |(2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (mobiusDivisorSquareRootAbelMoment M / M)
        (-((2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M))
  have hsum := abs_add_le
    (mobiusDivisorSquareRootAbelMoment M / M -
      (2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M)
    (coherentSquareRootPolarLatticeDefect M / M)
  linarith

private theorem source_power_bound_implies_zero_width
    {α C : ℝ} (hα : 0 ≤ α) (hαhalf : α < 1 / 2) (hC : 0 ≤ C)
    (hsource : ∀ M : ℕ, 2 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M / M| ≤ C * (M : ℝ) ^ α) :
    XiZeroHalfPlaneBound α := by
  let K := 2 * (C + |2 * Real.eulerMascheroniConstant| + 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlog : ∀ M : ℕ, 2 ≤ M →
      |criticalMellinChebyshevResolventSource (Real.log M)| ≤
        K * Real.exp (α * Real.log M) := by
    intro M hM
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have hpow : 1 ≤ (M : ℝ) ^ α := Real.one_le_rpow hM1 hα
    have heq : Real.exp (α * Real.log M) = (M : ℝ) ^ α := by
      rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < M)]
      congr 1
      ring
    rw [heq]
    have herror := mul_le_mul_of_nonneg_left hpow
      (by positivity : 0 ≤ 2 * (|2 * Real.eulerMascheroniConstant| + 1))
    have hbound := abs_resolvent_log_nat_le_mobiusDivisorSquareRootAbel hM
    have hmain := hsource M hM
    dsimp [K]
    nlinarith
  obtain ⟨B, hB, hglobal⟩ :=
    exists_global_exponential_bound_criticalMellinChebyshevResolventSource_of_log_nat_exponentialBound
      hα hK hlog
  exact xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventSource_exponentialBound
    hα hαhalf hB hglobal

/-- RH is equivalent to arbitrarily small power loss for the actual signed divisor Abel source. -/
theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbelSubpower :
    RiemannHypothesis ↔ MobiusDivisorSquareRootAbelSubpower := by
  constructor
  · intro hRH ε hε
    obtain ⟨C, hC, hsource⟩ :=
      riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded.mp hRH
    refine ⟨C, hC, fun M hM => (hsource M hM).trans ?_⟩
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.one_le_rpow hM1 hε.le) hC
  · intro hsource
    apply xiZeroHalfPlaneBound_zero_iff_rh.mp
    intro ρ hρ
    have hre : ρ.re ≤ 1 / 2 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hα : 0 < min ε (1 / 4 : ℝ) := lt_min hε (by norm_num)
      obtain ⟨C, hC, hbound⟩ := hsource (min ε (1 / 4)) hα
      have hwidth := source_power_bound_implies_zero_width hα.le
        (lt_of_le_of_lt (min_le_right ε (1 / 4)) (by norm_num)) hC hbound
      have hz := hwidth ρ hρ
      have hmin := min_le_left ε (1 / 4 : ℝ)
      linarith
    simpa only [add_zero] using hre

end

end RHTower
