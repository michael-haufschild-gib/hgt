import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheIntegratedCoreIsAPrimeCount
import GaloisForLFunctions.RHTower.Sieve.LogSumFromCount
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The core debt is the prime harmonic series

Summing the integrated core by scales instead of horizons collapses the pronic weights by
telescoping, `Σ_{n = j}^{T} 1/(n(n+1)) = 1/j − 1/(T+1)`, and leaves one sum over scales:

`∫_η^ε core_x(T) dx = Σ_{j ≤ T} (Λ(j)/log j)(j^{-η} − j^{-ε})(1/j − 1/(T+1))`
(`integral_workCore_eq_scaleSum`).

The density `Λ(j)/log j` is `1` at a prime and `1/k` at a `k`-th prime power, so the scale sum is a
**prime harmonic series**: its prime terms are `(p^{-η} − p^{-ε})/p` times a telescoping factor.
Hence the integrated core grows without bound in the horizon — at the rate of `Σ_{p ≤ T} 1/p`
(`exists_horizon_integral_workCore_ge`, using the divergence of the prime reciprocals).

So the explicit positive core of the signed work is a debt of size `log log T`, and admission forces
the deviation terms to carry it: under any energy budget the integrated deviation tends to `−∞`
along the horizons (`exists_horizon_integral_workDeviation_le`).  The continuation layer's
obstruction is thereby identified with the classical divergence of the prime harmonic series: the
only way the energy can stay bounded is that the source's deviation from constancy cancels, to
leading order, the prime harmonic growth of its own tangent.
-/

open Set Filter Finset MeasureTheory RHTower

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The scale form of the integrated core -/

/-- The pronic tail mass from a scale. -/
theorem sum_Icc_pronic_from {j T : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T) :
    (∑ n ∈ Finset.Icc j T, 1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      1 / (j : ℝ) - 1 / ((T : ℝ) + 1) := by
  have hIcc : (Finset.Icc j T : Finset ℕ) = Finset.Icc ((j - 1) + 1) T := by
    congr 1
    omega
  have hcell : ∀ n ∈ Finset.Icc ((j - 1) + 1) T,
      1 / ((n : ℝ) * ((n : ℝ) + 1)) = 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
    intro n hn
    have hn1 : 1 ≤ n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    field_simp
    ring
  rw [hIcc, Finset.sum_congr rfl hcell,
    RHTower.Sieve.sum_Icc_telescope_inv (by omega : j - 1 ≤ T)]
  congr 2
  have : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
    have h : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      have : (1 : ℕ) ≤ j := hj
      push_cast [Nat.cast_sub this]
      ring
    rw [h]
    ring
  rw [this]

/-- **The integrated core, summed by scales.** -/
theorem integral_workCore_eq_scaleSum (η ε : ℝ) (T : ℕ) :
    (∫ x in η..ε, workCore x T) =
      ∑ j ∈ Finset.Icc 1 T, ArithmeticFunction.vonMangoldt j *
        (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) *
          (1 / (j : ℝ) - 1 / ((T : ℝ) + 1)) := by
  classical
  rw [integral_workCore_eq]
  -- extend each inner sum to the full scale range with an indicator, then swap
  have hext : ∀ n ∈ Finset.Icc 1 T,
      (∑ j ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt j *
          (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j)) /
            ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ j ∈ Finset.Icc 1 T, (if j ≤ n then
          ArithmeticFunction.vonMangoldt j *
            (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) /
              ((n : ℝ) * ((n : ℝ) + 1)) else 0) := by
    intro n hn
    have hnT : n ≤ T := (Finset.mem_Icc.mp hn).2
    rw [Finset.sum_div, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun j _ => rfl
    ext j
    rw [Finset.mem_Icc, Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [Finset.sum_congr rfl hext, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjT : j ≤ T := (Finset.mem_Icc.mp hj).2
  rw [← Finset.sum_filter]
  have hfil : (Finset.Icc 1 T).filter (fun n => j ≤ n) = Finset.Icc j T := by
    ext n
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    omega
  rw [hfil]
  have hmass : (∑ n ∈ Finset.Icc j T, 1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      1 / (j : ℝ) - 1 / ((T : ℝ) + 1) := sum_Icc_pronic_from hj1 hjT
  have hfac : ∀ n ∈ Finset.Icc j T,
      ArithmeticFunction.vonMangoldt j *
          (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) /
            ((n : ℝ) * ((n : ℝ) + 1)) =
        (ArithmeticFunction.vonMangoldt j *
          (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j)) *
            (1 / ((n : ℝ) * ((n : ℝ) + 1))) := fun n _ => by ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, hmass]

/-! ## §2. The prime harmonic series -/

/-- The prime harmonic partial sum. -/
def primeHarmonic (N : ℕ) : ℝ := ∑ p ∈ (Finset.range N).filter Nat.Prime, (1 : ℝ) / p

/-- **The prime harmonic series diverges.** -/
theorem tendsto_primeHarmonic_atTop : Filter.Tendsto primeHarmonic atTop atTop := by
  have hnonneg : ∀ n : ℕ, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n := by
    intro n
    refine Set.indicator_nonneg (fun p _ => ?_) n
    positivity
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp
    not_summable_one_div_on_primes
  refine h.congr fun N => ?_
  rw [primeHarmonic, Finset.sum_indicator_eq_sum_filter]
  rfl

/-! ## §3. The core debt -/

theorem primeHarmonic_mono {M N : ℕ} (h : M ≤ N) : primeHarmonic M ≤ primeHarmonic N := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
  exact Finset.filter_subset_filter _ (fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h))

/-- **The integrated core dominates a prime harmonic partial sum.**  The prime scales carry density
one, and the pronic tail factor is at least `1/(2p)` up to half the horizon. -/
theorem integral_workCore_ge_primeHarmonic {η ε : ℝ} (hη : 0 ≤ η) (hηε : η ≤ ε) {T : ℕ}
    (hT : 2 ≤ T) :
    ((T : ℝ) ^ (-η) * (1 - (2 : ℝ) ^ (-(ε - η))) / 2) * primeHarmonic (T / 2 + 1) ≤
      ∫ x in η..ε, workCore x T := by
  classical
  rw [integral_workCore_eq_scaleSum]
  set S : Finset ℕ := (Finset.range (T / 2 + 1)).filter Nat.Prime with hS
  have hsub : S ⊆ Finset.Icc 1 T := by
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_range] at hp
    have hp2 := hp.2.two_le
    rw [Finset.mem_Icc]
    omega
  have hterm_nonneg : ∀ j ∈ Finset.Icc 1 T,
      0 ≤ ArithmeticFunction.vonMangoldt j *
        (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) *
          (1 / (j : ℝ) - 1 / ((T : ℝ) + 1)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjT : j ≤ T := (Finset.mem_Icc.mp hj).2
    have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hlog : 0 ≤ Real.log j := Real.log_natCast_nonneg j
    have hgap : (0 : ℝ) ≤ (j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε) := by
      have := Real.rpow_le_rpow_of_exponent_le hj1R (by linarith : -ε ≤ -η)
      linarith
    have hpron : (0 : ℝ) ≤ 1 / (j : ℝ) - 1 / ((T : ℝ) + 1) := by
      have hjR : (0 : ℝ) < (j : ℝ) := by linarith
      have hjTR : (j : ℝ) ≤ (T : ℝ) := by exact_mod_cast hjT
      have h1 : 1 / ((T : ℝ) + 1) ≤ 1 / (j : ℝ) :=
        one_div_le_one_div_of_le hjR (by linarith)
      linarith
    exact mul_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (div_nonneg hgap hlog)) hpron
  refine le_trans ?_
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hterm_nonneg j hj))
  rw [primeHarmonic, ← hS, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpmem := hp
  rw [hS, Finset.mem_filter, Finset.mem_range] at hpmem
  have hprime : p.Prime := hpmem.2
  have hp2 : 2 ≤ p := hprime.two_le
  have hpT : 2 * p ≤ T := by omega
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hprime.one_lt)
  have hΛ : ArithmeticFunction.vonMangoldt p = Real.log p :=
    ArithmeticFunction.vonMangoldt_apply_prime hprime
  have hdens : ArithmeticFunction.vonMangoldt p *
      (((p : ℝ) ^ (-η) - (p : ℝ) ^ (-ε)) / Real.log p) =
      (p : ℝ) ^ (-η) - (p : ℝ) ^ (-ε) := by
    rw [hΛ, mul_comm, div_mul_cancel₀ _ (ne_of_gt hlogp)]
  have hpTle : (p : ℝ) ≤ (T : ℝ) := by
    have : p ≤ T := by omega
    exact_mod_cast this
  have hTη : (T : ℝ) ^ (-η) ≤ (p : ℝ) ^ (-η) :=
    Real.rpow_le_rpow_of_nonpos hp0 hpTle (by linarith)
  have hbase : (p : ℝ) ^ (-(ε - η)) ≤ (2 : ℝ) ^ (-(ε - η)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by linarith)
  have hpη : (0 : ℝ) < (p : ℝ) ^ (-η) := Real.rpow_pos_of_pos hp0 _
  have h2le : (2 : ℝ) ^ (-(ε - η)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hgap : (T : ℝ) ^ (-η) * (1 - (2 : ℝ) ^ (-(ε - η))) ≤
      (p : ℝ) ^ (-η) - (p : ℝ) ^ (-ε) := by
    have hsplit : (p : ℝ) ^ (-ε) = (p : ℝ) ^ (-η) * (p : ℝ) ^ (-(ε - η)) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    rw [hsplit]
    nlinarith [hTη, hbase, hpη]
  have hgapnn : (0 : ℝ) ≤ (p : ℝ) ^ (-η) - (p : ℝ) ^ (-ε) := by
    have hTηnn : (0 : ℝ) ≤ (T : ℝ) ^ (-η) * (1 - (2 : ℝ) ^ (-(ε - η))) := by
      have : (0 : ℝ) ≤ (T : ℝ) ^ (-η) := Real.rpow_nonneg (Nat.cast_nonneg T) _
      nlinarith
    linarith
  have hmass : 1 / (2 * (p : ℝ)) ≤ 1 / (p : ℝ) - 1 / ((T : ℝ) + 1) := by
    have h2p : (2 : ℝ) * (p : ℝ) ≤ (T : ℝ) := by exact_mod_cast hpT
    have hle : 1 / ((T : ℝ) + 1) ≤ 1 / (2 * (p : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hhalf : 1 / (p : ℝ) - 1 / (2 * (p : ℝ)) = 1 / (2 * (p : ℝ)) := by
      field_simp
      ring
    linarith
  calc (T : ℝ) ^ (-η) * (1 - (2 : ℝ) ^ (-(ε - η))) / 2 * (1 / (p : ℝ))
      = ((T : ℝ) ^ (-η) * (1 - (2 : ℝ) ^ (-(ε - η)))) * (1 / (2 * (p : ℝ))) := by
        field_simp
    _ ≤ ((p : ℝ) ^ (-η) - (p : ℝ) ^ (-ε)) * (1 / (p : ℝ) - 1 / ((T : ℝ) + 1)) := by
        refine mul_le_mul hgap hmass (by positivity) hgapnn
    _ = ArithmeticFunction.vonMangoldt p *
          (((p : ℝ) ^ (-η) - (p : ℝ) ^ (-ε)) / Real.log p) *
          (1 / (p : ℝ) - 1 / ((T : ℝ) + 1)) := by rw [hdens]

/-- **The core debt is unbounded in the horizon.** -/
theorem exists_horizon_integral_workCore_ge {ε : ℝ} (hε : 0 < ε) (M : ℝ) :
    ∃ T : ℕ, 2 ≤ T ∧ M ≤ ∫ x in (0 : ℝ)..ε, workCore x T := by
  have h2 : (2 : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hconst : 0 < (1 - (2 : ℝ) ^ (-ε)) / 2 := by linarith
  obtain ⟨N, hN⟩ := ((Filter.tendsto_atTop.mp tendsto_primeHarmonic_atTop)
    (M / ((1 - (2 : ℝ) ^ (-ε)) / 2))).exists
  refine ⟨2 * N + 2, by omega, ?_⟩
  have hmain := integral_workCore_ge_primeHarmonic (η := 0) (ε := ε) le_rfl hε.le
    (T := 2 * N + 2) (by omega)
  have hfac : ((2 * N + 2 : ℕ) : ℝ) ^ (-(0 : ℝ)) = 1 := by
    rw [neg_zero, Real.rpow_zero]
  rw [hfac, sub_zero, one_mul] at hmain
  have hmono : primeHarmonic N ≤ primeHarmonic ((2 * N + 2) / 2 + 1) :=
    primeHarmonic_mono (by omega)
  have hstep : M ≤ (1 - (2 : ℝ) ^ (-ε)) / 2 * primeHarmonic ((2 * N + 2) / 2 + 1) := by
    have hNle : M / ((1 - (2 : ℝ) ^ (-ε)) / 2) ≤ primeHarmonic ((2 * N + 2) / 2 + 1) :=
      le_trans hN hmono
    rw [div_le_iff₀ hconst] at hNle
    linarith
  linarith

/-- **Admission forces the deviation terms to carry the prime harmonic debt.** -/
theorem integral_workDeviation_le_primeHarmonic {ε B η : ℝ} (hη : 0 < η) (hηε : η ≤ ε)
    (hB : ∀ T : ℕ, dampedMobiusEnergy ε T ≤ B) {T : ℕ} (hT : 2 ≤ T) :
    (∫ x in η..ε, 2 * workDeviation x T) ≤
      B - 2 * (((T : ℝ) ^ (-η) * (1 - (2 : ℝ) ^ (-(ε - η))) / 2) *
        primeHarmonic (T / 2 + 1)) := by
  have hwork := work_integral_le_of_bddAbove hB T hη hηε
  have hcore := integral_workCore_ge_primeHarmonic hη.le hηε hT
  have hintW : IntervalIntegrable (fun x => 2 * signedDampingWork x T) volume η ε :=
    intervalIntegrable_signedDampingWork hη hηε T
  have hintC : IntervalIntegrable (fun x => 2 * workCore x T) volume η ε := by
    refine ContinuousOn.intervalIntegrable (continuousOn_const.mul ?_)
    rw [show (fun x : ℝ => workCore x T) =
        (fun x : ℝ => ∑ n ∈ Finset.Icc 1 T, dampedPrimePrefix x n /
          ((n : ℝ) * ((n : ℝ) + 1))) from rfl]
    refine continuousOn_finsetSum _ fun n _ => ContinuousOn.div_const ?_ _
    rw [show (fun x : ℝ => dampedPrimePrefix x n) =
        (fun x : ℝ => ∑ j ∈ Finset.Icc 1 n, dampedPrimeWeight x j) from rfl]
    exact continuousOn_finsetSum _ fun j hj =>
      continuousOn_const.mul (continuousOn_rpow_neg_natCast (Finset.mem_Icc.mp hj).1 _)
  have hsplit : (∫ x in η..ε, 2 * workDeviation x T) =
      (∫ x in η..ε, 2 * signedDampingWork x T) - ∫ x in η..ε, 2 * workCore x T := by
    rw [← intervalIntegral.integral_sub hintW hintC]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [signedDampingWork_eq_core_add_deviation]
    ring
  have hcore2 : 2 * (((T : ℝ) ^ (-η) * (1 - (2 : ℝ) ^ (-(ε - η))) / 2) *
      primeHarmonic (T / 2 + 1)) ≤ ∫ x in η..ε, 2 * workCore x T := by
    rw [intervalIntegral.integral_const_mul]
    linarith
  rw [hsplit]
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
