import GaloisForLFunctions.HTGeometry.ExponentialCarrierHypertranscendence

/-!
# An explicit hypertranscendental exponential carrier

The frequency hypothesis of the exponential-carrier theorem is inhabited: the logarithms of the
primes are rationally independent, because a vanishing integer combination of them is the statement
that two products of prime powers agree.

Damping the amplitude of the `j`-th prime by its own `j`-th power beats every exponential weight, so
the resulting series is an entire carrier, and it -- together with every unimodular twist of it --
satisfies no algebraic differential equation on any nonempty open set.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Integer linear independence of a frequency family is rational independence of every finite
subfamily.** -/
theorem rationallyIndependentSequence_of_linearIndependent_int {ι : Type*} {omega : ι → ℝ}
    (h : LinearIndependent ℤ omega) : RationallyIndependentSequence omega := by
  classical
  intro s n hn
  rw [linearIndependent_iff'] at h
  have hmem : ∀ i : ((s : Set ι)), (i : ι) ∈ s := fun i => Finset.mem_coe.1 i.2
  have hsum : ∑ i ∈ s, (if hi : i ∈ s then n ⟨i, hi⟩ else 0) • omega i = 0 := by
    rw [← Finset.sum_finset_coe]
    rw [← hn, finiteTorusCharacterDetuning]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dif_pos (hmem i), zsmul_eq_mul]
  funext i
  have hi := h s _ hsum (i : ι) (hmem i)
  rwa [dif_pos (hmem i)] at hi

/-! ## The logarithms of the primes -/

/-- The frequencies: the logarithms of the primes in increasing order. -/
def logPrimeFrequency (j : ℕ) : ℝ := Real.log (Nat.nth Nat.Prime j)

theorem two_le_nth_prime (j : ℕ) : 2 ≤ Nat.nth Nat.Prime j := (Nat.prime_nth_prime j).two_le

theorem two_le_nth_prime_real (j : ℕ) : (2 : ℝ) ≤ (Nat.nth Nat.Prime j : ℝ) := by
  exact_mod_cast two_le_nth_prime j

theorem logPrimeFrequency_nonneg (j : ℕ) : 0 ≤ logPrimeFrequency j :=
  Real.log_nonneg (le_trans one_le_two (two_le_nth_prime_real j))

/-- **The logarithms of the primes are rationally independent.** -/
theorem rationallyIndependentSequence_logPrimeFrequency :
    RationallyIndependentSequence logPrimeFrequency := by
  refine rationallyIndependentSequence_of_linearIndependent_int ?_
  have hinj : Function.Injective
      (fun j : ℕ => (⟨Nat.nth Nat.Prime j, Nat.prime_nth_prime j⟩ : Nat.Primes)) := by
    intro j k hjk
    exact Nat.nth_injective Nat.infinite_setOf_prime (congrArg Subtype.val hjk)
  have hcomp : ((fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ)) ∘
      fun j : ℕ => (⟨Nat.nth Nat.Prime j, Nat.prime_nth_prime j⟩ : Nat.Primes))
      = logPrimeFrequency := rfl
  rw [← hcomp]
  exact logPrime_linearIndependent_int.comp _ hinj

/-! ## Amplitudes beating every exponential weight -/

/-- The amplitudes: the `j`-th prime damped by its own `j`-th power. -/
def logPrimeAmplitude (j : ℕ) : ℂ := ((Nat.nth Nat.Prime j : ℂ) ^ j)⁻¹

theorem norm_logPrimeAmplitude (j : ℕ) :
    ‖logPrimeAmplitude j‖ = (((Nat.nth Nat.Prime j : ℝ)) ^ j)⁻¹ := by
  rw [logPrimeAmplitude, norm_inv, norm_pow, Complex.norm_natCast]

theorem logPrimeAmplitude_ne_zero (j : ℕ) : logPrimeAmplitude j ≠ 0 := by
  refine inv_ne_zero (pow_ne_zero j ?_)
  exact_mod_cast (Nat.prime_nth_prime j).ne_zero

theorem infinite_support_logPrimeAmplitude : {j : ℕ | logPrimeAmplitude j ≠ 0}.Infinite := by
  have hall : {j : ℕ | logPrimeAmplitude j ≠ 0} = Set.univ := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact logPrimeAmplitude_ne_zero j
  rw [hall]
  exact Set.infinite_univ

/-- **The damped amplitudes stay summable against every exponential weight.**  Past the ceiling of
the weight the term is dominated by a geometric series in base two. -/
theorem expSeriesNormallySummable_logPrime :
    ExpSeriesNormallySummable logPrimeAmplitude logPrimeFrequency := by
  intro R
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun j => (2 : ℝ) ^ (⌈R⌉₊) * (1 / 2 : ℝ) ^ j) (summable_geometric_two.mul_left _) ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈R⌉₊] with j hj
  obtain ⟨d, rfl⟩ : ∃ d, j = ⌈R⌉₊ + d := ⟨j - ⌈R⌉₊, (Nat.add_sub_cancel' hj).symm⟩
  set K := ⌈R⌉₊ with hK
  set q : ℝ := (Nat.nth Nat.Prime (K + d) : ℝ) with hq
  have hq2 : (2 : ℝ) ≤ q := two_le_nth_prime_real _
  have hq1 : (1 : ℝ) ≤ q := le_trans one_le_two hq2
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le two_pos hq2
  -- the weight is a power of the prime
  have hweight : Real.exp (R * |logPrimeFrequency (K + d)|) ≤ q ^ K := by
    have habs : |logPrimeFrequency (K + d)| = Real.log q := abs_of_nonneg (logPrimeFrequency_nonneg _)
    rw [habs, mul_comm, ← Real.rpow_def_of_pos hq0, ← Real.rpow_natCast q K]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (Nat.le_ceil R)
  have hnn : 0 ≤ ‖logPrimeAmplitude (K + d)‖ * Real.exp (R * |logPrimeFrequency (K + d)|) :=
    mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
  rw [Real.norm_of_nonneg hnn, norm_logPrimeAmplitude]
  -- the damping beats it
  have hstep : (q ^ (K + d))⁻¹ * Real.exp (R * |logPrimeFrequency (K + d)|)
      ≤ (q ^ (K + d))⁻¹ * q ^ K :=
    mul_le_mul_of_nonneg_left hweight (le_of_lt (inv_pos.2 (pow_pos hq0 _)))
  refine le_trans hstep ?_
  have hcollapse : (q ^ (K + d))⁻¹ * q ^ K = (q ^ d)⁻¹ := by
    rw [pow_add, mul_inv, mul_comm ((q ^ K)⁻¹) ((q ^ d)⁻¹), mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero K (ne_of_gt hq0)), mul_one]
  have htarget : (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (K + d) = ((2 : ℝ) ^ d)⁻¹ := by
    rw [one_div, inv_pow, pow_add, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero K (two_ne_zero' (α := ℝ))), one_mul]
  rw [hcollapse, htarget]
  exact inv_anti₀ (pow_pos two_pos d) (pow_le_pow_left₀ (by norm_num) hq2 d)

/-! ## The carrier -/

/-- **An explicit entire carrier which satisfies no algebraic differential equation on any nonempty
open set**, together with every unimodular twist of it. -/
theorem not_differentiallyAlgebraicOn_logPrimeCarrier {lam : ℕ → ℂ} (hlam : ∀ j, ‖lam j‖ = 1)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ¬ DifferentiallyAlgebraicOn
      (cexpSeriesCarrier (fun j => logPrimeAmplitude j * lam j) logPrimeFrequency) U :=
  not_differentiallyAlgebraicOn_cexpSeriesCarrier_twist
    rationallyIndependentSequence_logPrimeFrequency expSeriesNormallySummable_logPrime
    infinite_support_logPrimeAmplitude hlam hU hUne

end

end GaloisForLFunctions.HTGeometry
