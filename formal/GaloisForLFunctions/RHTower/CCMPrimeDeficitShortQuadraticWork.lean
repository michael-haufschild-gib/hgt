import GaloisForLFunctions.RHTower.LogarithmicMobiusShortReconstruction
import GaloisForLFunctions.RHTower.CCMPrimeDeficitMobiusTailLocalization

/-!
# Full deficit reconstruction from a short quadratic form

All Möbius coefficients in the quadratic work lie below the square-root
cutoff. The complete deficit differs from this work by a short transform
of the bounded elementary source, hence by at most seven times the
square-root scale. Subtracting the source limit further reduces that
error to a linear function of logarithmic time.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitShortMainWork (T : ℝ) : ℝ :=
  (Real.eulerMascheroniConstant + 1) *
    (Real.exp T * (∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, moebiusCoeff n / n) -
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, moebiusCoeff n) -
    Real.log (2 * Real.pi) / 2 *
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, moebiusCoeff n * (T - Real.log n)

def ccmPrimeDeficitShortQuadraticWork (T : ℝ) : ℝ :=
  2 * ccmPrimeDeficitShortMainWork T -
    logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊
      (logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊
        (logarithmicDilationSum ccmPrimeDeficitDilationSource)) T

theorem logarithmicShortMobiusInverse_dilationSource {T : ℝ} (hT : 0 ≤ T) :
    logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ ccmPrimeDeficitDilationSource T =
      ccmPrimeDeficitShortMainWork T +
        logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ ccmPrimeDeficitDilationRemainder T := by
  have hU : ⌊Real.exp (T / 2)⌋₊ ≤ ⌊Real.exp T⌋₊ := Nat.floor_mono
    (Real.exp_le_exp.mpr (by linarith only [hT]))
  rw [logarithmicShortMobiusInverse_eq_prefix _ _ hU,
    logarithmicShortMobiusInverse_eq_prefix _ _ hU, ccmPrimeDeficitShortMainWork]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [ccmPrimeDeficitDilationRemainder, Real.exp_sub, Real.exp_log hnpos]
  unfold moebiusCoeff
  ring

/-- Exact full signed reconstruction with no coefficient beyond the
half cutoff in either the work or its bounded correction. -/
theorem ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortQuadraticWork T =
      2 * logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ ccmPrimeDeficitDilationRemainder T := by
  have hi : ccmLogChebyshevDeficitPrimitive T =
      logarithmicMobiusInverse ccmPrimeDeficitDilationSource T :=
    ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation hT
  rw [logarithmicMobiusInverse_eq_half_correction,
    logarithmicShortMobiusInverse_dilationSource hT] at hi
  unfold ccmPrimeDeficitShortQuadraticWork
  linarith only [hi]

theorem abs_logarithmicShortMobiusInverse_dilationRemainder_le {T : ℝ} (hT : 0 ≤ T) :
    |logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ ccmPrimeDeficitDilationRemainder T| ≤
      (7 / 2) * Real.exp (T / 2) := by
  have hU : ⌊Real.exp (T / 2)⌋₊ ≤ ⌊Real.exp T⌋₊ := Nat.floor_mono
    (Real.exp_le_exp.mpr (by linarith only [hT]))
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊) :
      |(ArithmeticFunction.moebius n : ℝ) * ccmPrimeDeficitDilationRemainder (T - Real.log n)| ≤
        7 / 2 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnT : (n : ℝ) ≤ Real.exp T :=
      (Nat.le_floor_iff (Real.exp_pos T).le).mp ((Finset.mem_Icc.mp hn).2.trans hU)
    have hm : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := abs_moebiusCoeff_le_one n
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hm
      (abs_ccmPrimeDeficitDilationRemainder_le_uniform
        (sub_nonneg.mpr ((Real.log_le_iff_le_exp hnpos).mpr hnT))) (abs_nonneg _) zero_le_one
  rw [logarithmicShortMobiusInverse_eq_prefix _ _ hU]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        |(ArithmeticFunction.moebius n : ℝ) * ccmPrimeDeficitDilationRemainder (T - Real.log n)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, (7 / 2 : ℝ) := Finset.sum_le_sum hterm
    _ = (7 / 2) * (⌊Real.exp (T / 2)⌋₊ : ℝ) := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le (Real.exp_pos _).le) (by positivity)

/-- The whole deficit and its short quadratic work differ by a uniformly
controlled square-root-scale term. The work itself is kept signed. -/
theorem abs_ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortQuadraticWork T| ≤
      7 * Real.exp (T / 2) := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork hT, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
  linarith only [abs_logarithmicShortMobiusInverse_dilationRemainder_le hT]

/-- The source limit leaves only the previously bounded transient from
the short interval; the quadratic form retains the full long contribution. -/
theorem ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_sub_limit {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortQuadraticWork T -
      2 * ccmPrimeDeficitDilationLimit *
        (∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, moebiusCoeff n) =
      2 * ccmPrimeDeficitMobiusTransientHead T := by
  have hU : ⌊Real.exp (T / 2)⌋₊ ≤ ⌊Real.exp T⌋₊ := Nat.floor_mono
    (Real.exp_le_exp.mpr (by linarith only [hT]))
  rw [ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork hT,
    logarithmicShortMobiusInverse_eq_prefix _ _ hU, ccmPrimeDeficitMobiusTransientHead]
  simp only [moebiusCoeff, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem abs_ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_sub_limit_le
    {T : ℝ} (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortQuadraticWork T -
      2 * ccmPrimeDeficitDilationLimit *
        (∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, moebiusCoeff n)| ≤ (T + 14) / 2 := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_sub_limit hT, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
  linarith only [abs_ccmPrimeDeficitMobiusTransientHead_le hT]

/-- The work is one literal square matrix of the elementary source,
plus its short explicit main terms. -/
theorem ccmPrimeDeficitShortQuadraticWork_eq_square {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitShortQuadraticWork T = 2 * ccmPrimeDeficitShortMainWork T -
      ∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
          (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
            logarithmicDilationSum ccmPrimeDeficitDilationSource (T - Real.log (a * b : ℕ)) := by
  rw [ccmPrimeDeficitShortQuadraticWork, logarithmicShortMobiusInverse_twice_eq_square _ hT]

/-- The full RH target is unchanged by replacing the deficit with its
short quadratic work: the difference already has a fixed critical bound. -/
theorem riemannHypothesis_iff_shortQuadraticWork_bound :
    RiemannHypothesis ↔ ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      |ccmPrimeDeficitShortQuadraticWork T| ≤ B * Real.exp (T / 2) := by
  rw [riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound]
  constructor
  · rintro ⟨B, hB0, hB⟩
    refine ⟨B + 7, by linarith only [hB0], ?_⟩
    intro T hT
    calc
      _ = |ccmLogChebyshevDeficitPrimitive T +
          (ccmPrimeDeficitShortQuadraticWork T - ccmLogChebyshevDeficitPrimitive T)| := by
        congr 1
        ring
      _ ≤ |ccmLogChebyshevDeficitPrimitive T| +
          |ccmPrimeDeficitShortQuadraticWork T - ccmLogChebyshevDeficitPrimitive T| := abs_add_le _ _
      _ = |ccmLogChebyshevDeficitPrimitive T| +
          |ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortQuadraticWork T| := by
        rw [abs_sub_comm (ccmPrimeDeficitShortQuadraticWork T)]
      _ ≤ B * Real.exp (T / 2) + 7 * Real.exp (T / 2) :=
        add_le_add (hB T hT) (abs_ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_le hT)
      _ = _ := by ring
  · rintro ⟨B, hB0, hB⟩
    refine ⟨B + 7, by linarith only [hB0], ?_⟩
    intro T hT
    calc
      _ = |ccmPrimeDeficitShortQuadraticWork T +
          (ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortQuadraticWork T)| := by
        congr 1
        ring
      _ ≤ |ccmPrimeDeficitShortQuadraticWork T| +
          |ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitShortQuadraticWork T| := abs_add_le _ _
      _ ≤ B * Real.exp (T / 2) + 7 * Real.exp (T / 2) :=
        add_le_add (hB T hT) (abs_ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_le hT)
      _ = _ := by ring

end RHTower
