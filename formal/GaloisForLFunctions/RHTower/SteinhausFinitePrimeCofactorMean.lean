import GaloisForLFunctions.RHTower.SteinhausModel
import GaloisForLFunctions.RHTower.SelbergDelangeConvolutionTransfer
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Coherent cofactor means preserving a finite prime-phase prefix

A finite Steinhaus phase prescription, extended by the trivial character on every new prime,
has an explicit nonzero mean. Its Möbius divisor correction is supported on the prescribed
primes; its reciprocal series converges absolutely and evaluates to a finite Euler product.
Tannery's theorem then gives the actual normalized summatory limit.

A logarithmic twist can be imposed on all new primes while preserving every old phase.
Removing that twist yields the same finite-defect mean. These are source asymptotics for
successive coherent cofactor extensions in the BAG recurrence-producer construction.
No conditional covariance bound, target probability, or vertical return is assumed or concluded.
-/

open ArithmeticFunction Filter Topology Finset
open scoped ArithmeticFunction.zeta Moebius
namespace RHTower
open SteinhausModel
noncomputable section

/-- A literal Steinhaus phase prescription on a finite prime prefix, trivial elsewhere. -/
def finitePrimePhase (S : Finset ℕ) (omega : Omega) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else X n (fun p => if p ∈ S then omega p else 0)
  map_zero' := by simp

/-- The finite-prefix arithmetic function is the literal Steinhaus character at positive indices. -/
theorem finitePrimePhase_apply {S : Finset ℕ} {omega : Omega} {n : ℕ}
    (hn : n ≠ 0) :
    finitePrimePhase S omega n = X n (fun p => if p ∈ S then omega p else 0) := by
  simp [finitePrimePhase, hn]

private theorem finitePrimePhase_mul (S : Finset ℕ) (omega : Omega) (m n : ℕ) :
    finitePrimePhase S omega (m * n) = finitePrimePhase S omega m * finitePrimePhase S omega n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [finitePrimePhase_apply hm, finitePrimePhase_apply hn,
    finitePrimePhase_apply (mul_ne_zero hm hn), X_mul hm hn]

private theorem finitePrimePhase_multiplicative (S : Finset ℕ) (omega : Omega) :
    (finitePrimePhase S omega).IsMultiplicative :=
  ⟨by simp [finitePrimePhase, X_one], fun {m n} _ => finitePrimePhase_mul S omega m n⟩

private theorem finitePrimePhase_pow (S : Finset ℕ) (omega : Omega) (p k : ℕ) :
    finitePrimePhase S omega (p ^ k) = (finitePrimePhase S omega p) ^ k := by
  induction k with
  | zero => simp [(finitePrimePhase_multiplicative S omega).map_one]
  | succ k ih => rw [pow_succ, finitePrimePhase_mul, ih, pow_succ]

private theorem finitePrimePhase_norm {S : Finset ℕ} {omega : Omega} {n : ℕ}
    (hn : n ≠ 0) : ‖finitePrimePhase S omega n‖ = 1 := by
  rw [finitePrimePhase_apply hn, norm_X]

private theorem finitePrimePhase_prime_outside {S : Finset ℕ} {omega : Omega} {p : ℕ}
    (hp : p.Prime) (hpS : p ∉ S) : finitePrimePhase S omega p = 1 := by
  rw [finitePrimePhase_apply hp.ne_zero]
  simp [X, hp.primeFactors, hpS]

/-- The exact divisor correction of the finite phase prescription. -/
def finitePrimePhaseCorrection (S : Finset ℕ) (omega : Omega) : ArithmeticFunction ℂ :=
  ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) * finitePrimePhase S omega

private theorem finitePrimePhaseCorrection_multiplicative (S : Finset ℕ) (omega : Omega) :
    (finitePrimePhaseCorrection S omega).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul (finitePrimePhase_multiplicative S omega)

/-- The divisor correction reconstructs the literal finite-prefix phase function exactly. -/
theorem finitePrimePhaseCorrection_mul_zeta (S : Finset ℕ) (omega : Omega) :
    finitePrimePhaseCorrection S omega * (ζ : ArithmeticFunction ℂ) = finitePrimePhase S omega := by
  rw [finitePrimePhaseCorrection, mul_right_comm, coe_moebius_mul_coe_zeta, one_mul]

private theorem finitePrimePhaseCorrection_prime_pow (S : Finset ℕ) (omega : Omega)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    finitePrimePhaseCorrection S omega (p ^ (k + 1)) =
      (finitePrimePhase S omega p - 1) * (finitePrimePhase S omega p) ^ k := by
  have hsum (j : ℕ) :
      ∑ i ∈ Finset.range (j + 1), finitePrimePhaseCorrection S omega (p ^ i) =
        (finitePrimePhase S omega p) ^ j := by
    have h := congrArg (fun f : ArithmeticFunction ℂ => f (p ^ j))
      (finitePrimePhaseCorrection_mul_zeta S omega)
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, finitePrimePhase_pow] at h
    exact h
  have hnext := hsum (k + 1)
  rw [Finset.sum_range_succ, hsum k] at hnext
  rw [pow_succ (finitePrimePhase S omega p) k] at hnext
  linear_combination hnext

private theorem finitePrimePhaseCorrection_zero_off_support
    (S : Finset ℕ) (omega : Omega) {n : ℕ} (hn : n ∉ Nat.factoredNumbers S) :
    finitePrimePhaseCorrection S omega n = 0 := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnot : ¬ n.primeFactors ⊆ S := by
    exact fun h => hn (Nat.mem_factoredNumbers_of_primeFactors_subset hn0 h)
  obtain ⟨p, hpn, hpS⟩ := Finset.not_subset.mp hnot
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpn
  have hpos : 0 < n.factorization p := by
    rw [Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hpn
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [(finitePrimePhaseCorrection_multiplicative S omega).multiplicative_factorization _ hn0]
  unfold Finsupp.prod
  apply Finset.prod_eq_zero (i := p)
  · simpa only [Nat.support_factorization] using hpn
  · rw [hk]
    change finitePrimePhaseCorrection S omega (p ^ (k + 1)) = 0
    rw [finitePrimePhaseCorrection_prime_pow S omega hp,
      finitePrimePhase_prime_outside hp hpS]
    simp

private theorem finitePrimePhase_prime_ratio_norm_lt_one
    (S : Finset ℕ) (omega : Omega) {p : ℕ} (hp : p.Prime) :
    ‖finitePrimePhase S omega p / (p : ℂ)‖ < 1 := by
  rw [norm_div, finitePrimePhase_norm hp.ne_zero, Complex.norm_natCast]
  exact (div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)

private theorem finitePrimePhase_prime_den_ne_zero
    (S : Finset ℕ) (omega : Omega) {p : ℕ} (hp : p.Prime) :
    1 - finitePrimePhase S omega p / (p : ℂ) ≠ 0 := by
  intro h
  have heq := sub_eq_zero.mp h
  have hnorm := finitePrimePhase_prime_ratio_norm_lt_one S omega hp
  rw [← heq, norm_one] at hnorm
  exact (lt_irrefl _ hnorm)

private theorem hasSum_finitePrimePhaseCorrection_prime_pow
    (S : Finset ℕ) (omega : Omega) {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => finitePrimePhaseCorrection S omega (p ^ k) / ((p ^ k : ℕ) : ℂ))
      ((1 - 1 / (p : ℂ)) / (1 - finitePrimePhase S omega p / (p : ℂ))) := by
  have hgeom := hasSum_geometric_of_norm_lt_one
    (finitePrimePhase_prime_ratio_norm_lt_one S omega hp)
  have h := hgeom.mul_left ((finitePrimePhase S omega p - 1) / (p : ℂ))
  apply (hasSum_nat_add_iff' 1).mp
  convert h using 1 <;> try rfl
  · funext k
    rw [finitePrimePhaseCorrection_prime_pow S omega hp]
    push_cast
    rw [pow_succ, div_pow]
    ring
  · simp only [Finset.sum_range_one, pow_zero, Nat.cast_one,
      (finitePrimePhaseCorrection_multiplicative S omega).map_one, div_one]
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpu : (p : ℂ) - finitePrimePhase S omega p ≠ 0 := by
      intro hpu
      apply finitePrimePhase_prime_den_ne_zero S omega hp
      rw [← sub_eq_zero.mp hpu, div_self hpC, sub_self]
    field_simp [hpC, hpu]
    ring

/-- The nonzero mean produced by a fixed finite prime phase prescription. -/
def finitePrimePhaseMean (S : Finset ℕ) (omega : Omega) : ℂ :=
  ∏ p ∈ S with p.Prime,
    (1 - 1 / (p : ℂ)) / (1 - finitePrimePhase S omega p / (p : ℂ))

/-- The reciprocal divisor correction is absolutely summable and has the finite Euler mean. -/
theorem hasSum_finitePrimePhaseCorrection_div
    (S : Finset ℕ) (omega : Omega) :
    HasSum (fun n : ℕ => finitePrimePhaseCorrection S omega n / (n : ℂ))
      (finitePrimePhaseMean S omega) := by
  let f : ℕ → ℂ := fun n => finitePrimePhaseCorrection S omega n / (n : ℂ)
  have heuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := f)
    (by simp [f, (finitePrimePhaseCorrection_multiplicative S omega).map_one])
    (fun {m n} hmn => by
      dsimp only [f]
      rw [(finitePrimePhaseCorrection_multiplicative S omega).map_mul_of_coprime hmn,
        Nat.cast_mul, div_mul_div_comm])
    (fun {p} hp => (hasSum_finitePrimePhaseCorrection_prime_pow S omega hp).summable.norm) S
  have h := (hasSum_subtype_iff_indicator (s := Nat.factoredNumbers S) (f := f)).mp heuler.2
  have hfun : (Nat.factoredNumbers S).indicator f = f := by
    funext n
    by_cases hn : n ∈ Nat.factoredNumbers S
    · simp [hn]
    · simp [hn, f, finitePrimePhaseCorrection_zero_off_support S omega hn]
  rw [hfun] at h
  convert h using 1
  unfold finitePrimePhaseMean
  apply Finset.prod_congr rfl
  intro p hp
  exact (hasSum_finitePrimePhaseCorrection_prime_pow S omega (Finset.mem_filter.mp hp).2).tsum_eq.symm

/-- No finite unit-phase prescription destroys the cofactor mean. -/
theorem finitePrimePhaseMean_ne_zero (S : Finset ℕ) (omega : Omega) :
    finitePrimePhaseMean S omega ≠ 0 := by
  unfold finitePrimePhaseMean
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2
  apply div_ne_zero _ (finitePrimePhase_prime_den_ne_zero S omega hp')
  intro h
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  have heq : (p : ℂ) = 1 := by
    have h' := sub_eq_zero.mp h
    field_simp at h'
    exact h'
  exact hp'.ne_one (by exact_mod_cast heq)

private theorem arithmeticSummatory_zeta (N : ℕ) :
    arithmeticSummatory (ζ : ArithmeticFunction ℂ) N = N := by
  unfold arithmeticSummatory
  have hsum : (∑ n ∈ Finset.Icc 1 N, (ζ : ArithmeticFunction ℂ) n) =
      ∑ n ∈ Finset.Icc 1 N, (1 : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn0]
  rw [hsum]
  simp

/-- Prescribing finitely many prime phases produces an explicit nonzero linear cofactor mean.
The asymptotic is proved from the literal divisor correction, with no analytic input hypothesis. -/
theorem tendsto_finitePrimePhase_mean (S : Finset ℕ) (omega : Omega) :
    Tendsto (fun N : ℕ => arithmeticSummatory (finitePrimePhase S omega) N / (N : ℂ))
      atTop (𝓝 (finitePrimePhaseMean S omega)) := by
  let corr := finitePrimePhaseCorrection S omega
  have hseries := hasSum_finitePrimePhaseCorrection_div S omega
  have hbase (d : ℕ) (hd : d ≠ 0) :
      Tendsto (fun N : ℕ => arithmeticSummatory (ζ : ArithmeticFunction ℂ) (N / d) /
        (N : ℂ)) atTop (𝓝 (1 / (d : ℂ))) := by
    simpa only [arithmeticSummatory_zeta, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast] using
      (GaloisForLFunctions.HTGeometry.tendsto_natDiv_div_self (Nat.pos_of_ne_zero hd)).ofReal
  have hdom (N d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
      ‖corr d * arithmeticSummatory (ζ : ArithmeticFunction ℂ) (N / d) / (N : ℂ)‖ ≤
        ‖corr d / (d : ℂ)‖ := by
    have hdN := Finset.mem_Icc.mp hd
    have hNR : (0 : ℝ) < N := by exact_mod_cast hdN.1.trans hdN.2
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdN.1
    rw [arithmeticSummatory_zeta, norm_div, norm_mul, Complex.norm_natCast,
      Complex.norm_natCast, norm_div, Complex.norm_natCast]
    calc
      ‖corr d‖ * ((N / d : ℕ) : ℝ) / (N : ℝ) ≤
          ‖corr d‖ * ((N : ℝ) / (d : ℝ)) / (N : ℝ) := by
        gcongr
        exact Nat.cast_div_le
      _ = ‖corr d‖ / (d : ℝ) := by field_simp
  have h := tendsto_arithmeticSummatory_mul_div_of_dominated_LSeries
    corr (ζ : ArithmeticFunction ℂ) (fun N => (N : ℂ)) 1
    (fun d => ‖corr d / (d : ℂ)‖)
    (fun d => norm_nonneg _) hseries.summable.norm hbase hdom
  have hL : LSeries corr (1 : ℂ) = finitePrimePhaseMean S omega := by
    rw [LSeries]
    have hterm : LSeries.term corr (1 : ℂ) = fun n => corr n / (n : ℂ) := by
      funext n
      by_cases hn : n = 0
      · simp [hn]
      · simp [LSeries.term_of_ne_zero hn]
    rw [hterm]
    exact hseries.tsum_eq
  simpa only [corr, finitePrimePhaseCorrection_mul_zeta, one_mul, hL] using h

/-- Every fixed prime-phase prefix admits linearly large cofactor sums when all new prime
phases are set to one. This is the untwisted source used in successive coherent extensions. -/
theorem exists_eventually_finitePrimePhase_summatory_norm_lower
    (S : Finset ℕ) (omega : Omega) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ≤ ‖arithmeticSummatory (finitePrimePhase S omega) N‖ := by
  have hpos : 0 < ‖finitePrimePhaseMean S omega‖ :=
    norm_pos_iff.mpr (finitePrimePhaseMean_ne_zero S omega)
  refine ⟨‖finitePrimePhaseMean S omega‖ / 2, half_pos hpos, ?_⟩
  have hlarge := (tendsto_finitePrimePhase_mean S omega).norm.eventually
    (eventually_gt_nhds (half_lt_self hpos))
  filter_upwards [hlarge, eventually_gt_atTop 0] with N hlarge hN
  rw [norm_div, Complex.norm_natCast] at hlarge
  exact (le_div_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mp hlarge.le

/-- Preserve the finite prescribed phase prefix and assign one logarithmic twist to every
new prime. Later finite extensions can freeze any initial segment of this prescription. -/
def finitePrimeTwistExtension (S : Finset ℕ) (omega : Omega) (t : ℝ) : Omega :=
  fun p => if p ∈ S then omega p else t * Real.log p / (2 * Real.pi)

/-- A coherent extension preserves every previously prescribed phase exactly. -/
theorem finitePrimeTwistExtension_eq_on_prefix
    (S : Finset ℕ) (omega : Omega) (t : ℝ) {p : ℕ} (hp : p ∈ S) :
    finitePrimeTwistExtension S omega t p = omega p := by
  simp [finitePrimeTwistExtension, hp]

/-- Untwisting the coherent extension leaves precisely a finite prime defect. -/
theorem X_finitePrimeTwistExtension_factor
    (S : Finset ℕ) (omega : Omega) (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    X n (finitePrimeTwistExtension S omega t) =
      finitePrimePhase S (fun p => omega p - t * Real.log p / (2 * Real.pi)) n *
        (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hphase : (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) *
        finitePrimeTwistExtension S omega t p) =
      (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) *
        (if p ∈ S then omega p - t * Real.log p / (2 * Real.pi) else 0)) +
      t / (2 * Real.pi) * Real.log n := by
    rw [Real.log_nat_eq_sum_factorization]
    simp only [Finsupp.sum, Nat.support_factorization, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [finitePrimeTwistExtension]
    split_ifs <;> ring
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [finitePrimePhase_apply hn]
  unfold X
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [Complex.cpow_def_of_ne_zero hnC, hlog, ← Complex.exp_add, hphase]
  congr 1
  dsimp only
  generalize (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) *
    (if p ∈ S then omega p - t * Real.log p / (2 * Real.pi) else 0)) = v
  push_cast
  field_simp [Real.pi_ne_zero]

/-- A coherent extension of any finite phase prescription has the explicit nonzero mean
after removal of its chosen logarithmic twist. -/
theorem tendsto_untwisted_finitePrimeTwistExtension_mean
    (S : Finset ℕ) (omega : Omega) (t : ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, X n (finitePrimeTwistExtension S omega t) /
        (n : ℂ) ^ ((t : ℂ) * Complex.I)) / (N : ℂ)) atTop
      (𝓝 (finitePrimePhaseMean S (fun p => omega p - t * Real.log p / (2 * Real.pi)))) := by
  have h := tendsto_finitePrimePhase_mean S
    (fun p => omega p - t * Real.log p / (2 * Real.pi))
  convert h using 1
  funext N
  congr 1
  unfold arithmeticSummatory
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hpow : (n : ℂ) ^ ((t : ℂ) * Complex.I) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0)]
    exact Complex.exp_ne_zero _
  rw [X_finitePrimeTwistExtension_factor S omega t hn0, mul_div_cancel_right₀ _ hpow]

end
end RHTower
