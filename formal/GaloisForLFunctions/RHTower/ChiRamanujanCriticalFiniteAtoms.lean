import GaloisForLFunctions.RHTower.ChiRamanujanPrimeOnlyAtoms

/-!
# Exact critical finite rational prime atoms

Differentiate the finite divisor weights at zero before the physical band
grows, retaining the square-divisor convolution. The resulting literal
rational atoms have exactly the prime logarithms on every covered finite
band. No damping approximation or composite correction remains there.
-/

noncomputable section
open Filter Set ArithmeticFunction
open scoped BigOperators Topology
namespace RHTower.BAGTrace

/-- The derivative of each literal finite divisor atom at zero damping. -/
def ramanujanCriticalAtomWeight (P : Finset ℕ) (a : RamanujanAtomIndex P) : ℝ :=
  -(moebius a.1.val : ℝ) * Real.log a.1.val / (a.1.val : ℝ)

theorem hasDerivAt_ramanujanAtomWeight_zero (P : Finset ℕ) (a : RamanujanAtomIndex P) :
    HasDerivAt (fun ε : ℝ => ramanujanAtomWeight P ε a) (ramanujanCriticalAtomWeight P a) 0 := by
  have hd0 : (a.1.val : ℝ) > 0 := by
    exact_mod_cast Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero
      (Nat.ne_zero_of_mem_divisors a.1.property) (Nat.dvd_of_mem_divisors a.1.property))
  have he : HasDerivAt (fun ε : ℝ => Real.exp (Real.log a.1.val * -ε))
      (-Real.log a.1.val) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).neg.const_mul (Real.log a.1.val)).exp)
  simp only [ramanujanAtomWeight, Real.rpow_def_of_pos hd0, ramanujanCriticalAtomWeight]
  simpa only [neg_mul, mul_neg] using
    (he.const_mul (moebius a.1.val : ℝ)).div_const (a.1.val : ℝ)

theorem tendsto_ramanujanCompensatedAtomWeight_zero (P : Finset ℕ) (a : RamanujanAtomIndex P) :
    Tendsto (fun ε : ℝ => ramanujanCompensatedAtomWeight P ε a) (𝓝[>] (0 : ℝ))
      (𝓝 (ramanujanCriticalAtomWeight P a)) := by
  have ht := (hasDerivAt_ramanujanAtomWeight_zero P a).tendsto_slope_zero_right
  apply ht.congr'
  filter_upwards [] with ε
  simp only [zero_add, smul_eq_mul, ramanujanCompensatedAtomWeight]
  ring

/-- The square-divisor filter is retained while the finite source is differentiated. -/
def ramanujanCriticalPrimeAtomWeight (P : Finset ℕ) (a : RamanujanPrimeOnlyAtomIndex P) : ℝ :=
  ramanujanSquareSieveAtomWeight a.2 * ramanujanCriticalAtomWeight P a.1

theorem tendsto_ramanujanPrimeOnlyAtomWeight_zero (P : Finset ℕ)
    (a : RamanujanPrimeOnlyAtomIndex P) :
    Tendsto (fun ε : ℝ => ramanujanPrimeOnlyAtomWeight P ε a) (𝓝[>] (0 : ℝ))
      (𝓝 (ramanujanCriticalPrimeAtomWeight P a)) :=
  (tendsto_ramanujanCompensatedAtomWeight_zero P a.1).const_mul _

private theorem tendsto_compensated_range (M : ℕ) {n : ℕ} (hn : 1 < n) (hM : n ≤ M) :
    Tendsto (fun ε : ℝ => ramanujanCompensatedMultiplier (Finset.range (M+1)) ε n)
      (𝓝[>] (0 : ℝ)) (𝓝 (vonMangoldt n)) := by
  have hn0 : n ≠ 0 := by omega
  have hP : n.primeFactors ⊆ Finset.range (M+1) := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      ((Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hM))
  have ht := (hasDerivAt_woldIncidenceNormalFactor n).tendsto_slope_zero_right
  apply ht.congr'
  filter_upwards [] with ε
  simp only [zero_add, smul_eq_mul, ramanujanCompensatedMultiplier,
    ramanujanFiniteMultiplier, ramanujanFiniteIncidence_eq hn0 hP, woldIncidenceNormalFactor]
  ring

private theorem tendsto_primeOnly_range (M : ℕ) {n : ℕ} (hn : 1 < n) (hM : n ≤ M) :
    Tendsto (fun ε : ℝ => ramanujanPrimeOnlyMultiplier (Finset.range (M+1)) ε n)
      (𝓝[>] (0 : ℝ)) (𝓝 (if n.Prime then Real.log n else 0)) := by
  have he : (if Squarefree n then (1 : ℝ) else 0) * vonMangoldt n =
      if n.Prime then Real.log n else 0 := by
    rw [← RHTower.Sieve.vaughanSquarefreePart_vonMangoldt n]
    by_cases h : Squarefree n <;> simp [RHTower.Sieve.vaughanSquarefreePart,h]
  have ht := (tendsto_compensated_range M hn hM).const_mul
    (if Squarefree n then (1 : ℝ) else 0)
  rw [he] at ht
  apply ht.congr'
  filter_upwards [] with ε
  rw [ramanujanPrimeOnlyMultiplier_range ε M hn hM,
    ramanujanCompensatedMultiplier_range ε M hn hM]
  split_ifs <;> simp

/-- On a covered finite band the critical rational atoms select primes exactly;
there is no remaining damping limit or squarefree-composite correction. -/
theorem sum_ramanujanCriticalPrimeAtomWeight_fourier_range (M : ℕ) {n : ℕ}
    (hn : 1 < n) (hM : n ≤ M) :
    (∑ a : RamanujanPrimeOnlyAtomIndex (Finset.range (M+1)),
      (ramanujanCriticalPrimeAtomWeight (Finset.range (M+1)) a : ℂ) *
        ramanujanFourierPhase (n : ℤ) (ramanujanPrimeOnlyAtomNode a)) =
      ((if n.Prime then Real.log n else 0 : ℝ) : ℂ) := by
  have ha := tendsto_finsetSum Finset.univ (fun a _ =>
    (Complex.continuous_ofReal.tendsto _ |>.comp
      (tendsto_ramanujanPrimeOnlyAtomWeight_zero (Finset.range (M+1)) a)).mul_const
        (ramanujanFourierPhase (n : ℤ) (ramanujanPrimeOnlyAtomNode a)))
  apply tendsto_nhds_unique ha
  convert (Complex.continuous_ofReal.tendsto _ |>.comp (tendsto_primeOnly_range M hn hM)) using 1
  funext ε
  simp only [Function.comp_apply, sum_ramanujanPrimeOnlyAtomWeight_fourier, Int.natAbs_natCast]

end RHTower.BAGTrace
