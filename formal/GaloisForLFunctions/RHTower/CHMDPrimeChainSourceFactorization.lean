import GaloisForLFunctions.RHTower.CHMDReflectedPrimeSingularPart
import GaloisForLFunctions.RHTower.CHMDPrimeChainVariance

/-!
# Complete prime-chain factorization of the original crossing source

At each product index N and logarithmic cut u, the actual prime-power edges
split into complete bipartite prime chains. Their conditional-variance
factorization retains both original theta indices and every arithmetic weight.

Each chain density is nonnegative and integrable. The entire countable family
has summable integral norms and sums exactly to the original crossing source,
including its reflected singular component and exact collar compensation.
The full Doob source identity retains the original negative cosh mass.
No domination of that mass or Riemann Hypothesis is asserted.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower.CHMDPrimeChainSource
open CHMDPrimeChain CHMDPrimeCuts PhiDivisorEnergy

/-- All prime-chain variance sectors at one original theta product index. -/
def density (N : ℕ) (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  fiber N u * chainVariance N u (fun m => v (u - Real.log m))

/-- One original arithmetic chain, with its exact theta fibre and log-prime weight. -/
def chainDensity (N p b : ℕ) (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.log p * fiber N u *
    varianceEnergy (chainLeft N p b u) (chainRight N p b u)
      (fun m => v (u - Real.log m))

theorem density_eq_cutDensity (N : ℕ) (v : ℝ → ℝ) (u : ℝ) :
    density N v u = cutDensity N v u := by
  rw [density, cutDensity, divisorCutEnergy, divisor_cut_eq_chainVariance]

theorem density_eq_sum_chains (N : ℕ) (v : ℝ → ℝ) (u : ℝ) :
    density N v u =
      ∑ p ∈ N.primeFactors, ∑ b ∈ N.divisors, chainDensity N p b v u := by
  unfold density chainVariance chainDensity
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem chainDensity_nonneg (N : ℕ+) {p : ℕ} (hp : p ∈ (N : ℕ).primeFactors)
    (b : ℕ) (v : ℝ → ℝ) (u : ℝ) : 0 ≤ chainDensity N p b v u := by
  by_cases hu : u ∈ Ioo (0 : ℝ) (Real.log (N : ℕ))
  · exact mul_nonneg (mul_nonneg
      (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))
      (fiber_pos_on_central N.pos hu.1.le hu.2.le).le)
      (varianceEnergy_nonneg _ _ _)
  · rw [chainDensity, chainVariance_term_zero_outside _ _ _ _ _ hu, mul_zero]

theorem density_nonneg (N : ℕ+) (v : ℝ → ℝ) (u : ℝ) : 0 ≤ density N v u := by
  rw [density_eq_cutDensity]
  exact cutDensity_nonneg N v u

theorem measurable_chainDensity (N p b : ℕ) {v : ℝ → ℝ} (hv : Continuous v) :
    Measurable (chainDensity N p b v) := by
  have hf : Continuous (fiber N) := by unfold fiber cuspTerm; fun_prop
  unfold chainDensity
  apply Measurable.mul (measurable_const.mul hf.measurable)
  simp_rw [← bipartiteEnergy_eq_variance, chain_bipartite_eq]
  apply Finset.measurable_sum
  intro m _
  apply Finset.measurable_sum
  intro k _
  by_cases hb : b = ordCompl[p] m
  · simp only [if_pos hb]
    by_cases hc : ordCompl[p] m = ordCompl[p] k
    · simp only [hc, and_true]
      exact Measurable.ite measurableSet_Ioo (by fun_prop) measurable_const
    · simp only [hc, and_false, if_false]
      exact measurable_const
  · simp only [if_neg hb]
    exact measurable_const

theorem integrable_density {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (N : ℕ) : Integrable (density N v) := by
  obtain ⟨M, hM⟩ := hvc.exists_bound_of_continuous hv
  have hM0 : 0 ≤ M := (norm_nonneg (v 0)).trans (hM 0)
  have hbound : ∀ x, |v x| ≤ M := by simpa only [Real.norm_eq_abs] using hM
  have he : density N v = fun u => ∑ c ∈ N.divisorsAntidiagonal,
      ∑ q ∈ c.1.divisorsAntidiagonal, cutEdge v q.1 q.2 c.2 u := by
    funext u
    rw [density_eq_cutDensity, cutDensity_eq_sum_edges]
  rw [he]
  apply integrable_finsetSum
  intro c hc
  apply integrable_finsetSum
  intro q hq
  exact integrable_cutEdge hv hM0 hbound
    ⟨q.1, Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hq)⟩
    ⟨q.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hq)⟩
    ⟨c.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hc)⟩

theorem chainDensity_le_density (N : ℕ+) {p b : ℕ}
    (hp : p ∈ (N : ℕ).primeFactors) (hb : b ∈ (N : ℕ).divisors)
    (v : ℝ → ℝ) (u : ℝ) : chainDensity N p b v u ≤ density N v u := by
  rw [density_eq_sum_chains]
  exact (Finset.single_le_sum (fun d _ => chainDensity_nonneg N hp d v u) hb).trans
    (Finset.single_le_sum
      (fun q hq => Finset.sum_nonneg fun d _ => chainDensity_nonneg N hq d v u) hp)

theorem integrable_chainDensity (N : ℕ+) {p b : ℕ}
    (hp : p ∈ (N : ℕ).primeFactors) (hb : b ∈ (N : ℕ).divisors)
    {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (chainDensity N p b v) := by
  apply (integrable_density hv hvc N).mono'
    (measurable_chainDensity N p b hv).aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (chainDensity_nonneg N hp b v u)]
  exact chainDensity_le_density N hp hb v u

theorem density_hasSum {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    HasSum (fun N : ℕ+ => ∫ u, density N v u) (∑' d : ℕ, primeCrossing v d) := by
  simpa only [density_eq_cutDensity] using compact_primeCrossing_hasSum_cuts hv hvc

/-- Every positive product index, prime divisor and chain base; no truncation. -/
abbrev ChainIndex := Σ N : ℕ+,
  {p : ℕ // p ∈ (N : ℕ).primeFactors} × {b : ℕ // b ∈ (N : ℕ).divisors}

def chainIntegral (v : ℝ → ℝ) (q : ChainIndex) : ℝ :=
  ∫ u, chainDensity q.1 q.2.1 q.2.2 v u

theorem chainIntegral_nonneg (v : ℝ → ℝ) (q : ChainIndex) : 0 ≤ chainIntegral v q :=
  integral_nonneg fun u => chainDensity_nonneg q.1 q.2.1.property q.2.2 v u

theorem sum_fiber_integrals {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (N : ℕ+) :
    (∑' q : {p : ℕ // p ∈ (N : ℕ).primeFactors} × {b : ℕ // b ∈ (N : ℕ).divisors},
      ∫ u, chainDensity N q.1 q.2 v u) = ∫ u, density N v u := by
  rw [tsum_fintype, Fintype.sum_prod_type]
  have hb (p : ℕ) : (∑ b : {b : ℕ // b ∈ (N : ℕ).divisors},
      ∫ u, chainDensity N p b v u) =
      ∑ b ∈ (N : ℕ).divisors, ∫ u, chainDensity N p b v u :=
    (Finset.sum_subtype (N : ℕ).divisors (fun _ => Iff.rfl)
      (fun b => ∫ u, chainDensity N p b v u)).symm
  simp_rw [hb]
  rw [← Finset.sum_subtype (N : ℕ).primeFactors (fun _ => Iff.rfl)
    (fun p => ∑ b ∈ (N : ℕ).divisors, ∫ u, chainDensity N p b v u)]
  simp_rw [density_eq_sum_chains]
  rw [integral_finsetSum _ (fun p hp => integrable_finsetSum _
    fun b hb => integrable_chainDensity N hp hb hv hvc)]
  apply Finset.sum_congr rfl
  intro p hp
  exact (integral_finsetSum _ fun b hb => integrable_chainDensity N hp hb hv hvc).symm

/-- The complete arithmetic variance family sums to the actual prime crossing source. -/
theorem complete_chain_hasSum {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    HasSum (chainIntegral v) (∑' d : ℕ, primeCrossing v d) := by
  have hs : Summable (chainIntegral v) :=
    (summable_sigma_of_nonneg (chainIntegral_nonneg v)).mpr ⟨fun _ => (hasSum_fintype _).summable, by
      change Summable (fun N : ℕ+ => ∑' q :
        {p : ℕ // p ∈ (N : ℕ).primeFactors} × {b : ℕ // b ∈ (N : ℕ).divisors},
          ∫ u, chainDensity N q.1 q.2 v u)
      simp_rw [sum_fiber_integrals hv hvc]
      exact (density_hasSum hv hvc).summable⟩
  have he : (∑' q, chainIntegral v q) = ∑' d : ℕ, primeCrossing v d := by
    rw [hs.tsum_sigma]
    simp only [chainIntegral, sum_fiber_integrals hv hvc]
    exact (density_hasSum hv hvc).tsum_eq
  simpa only [he] using hs.hasSum

/-- Absolute convergence justifies regrouping all chains and interchanging the integral. -/
theorem complete_chain_norm_summable {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    Summable (fun q : ChainIndex => ∫ u, ‖chainDensity q.1 q.2.1 q.2.2 v u‖) := by
  have he : (fun q : ChainIndex => ∫ u, ‖chainDensity q.1 q.2.1 q.2.2 v u‖) =
      chainIntegral v := by
    funext q
    unfold chainIntegral
    apply integral_congr_ae
    filter_upwards with u
    exact Real.norm_of_nonneg (chainDensity_nonneg q.1 q.2.1.property q.2.2 v u)
  rw [he]
  exact (complete_chain_hasSum hv hvc).summable

/-- Exact factorization inside the original source, with the cosh subtraction unchanged. -/
theorem doob_source_eq_chain_variances_sub_cosh {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
      phiDoobArchJumpEnergy v + sameSide v + sameSide (fun x => v (-x)) +
        (∑' q : ChainIndex, chainIntegral v q) - phiDoobCoshMass (fun x => v x ^ 2) := by
  rw [doob_source_eq_positive_cuts_sub_cosh hv hvc,
    (complete_chain_hasSum hv.continuous hvc).tsum_eq,
    (compact_primeCrossing_hasSum_cuts hv.continuous hvc).tsum_eq]

theorem integral_complete_chain {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    (∫ u, ∑' q : ChainIndex, chainDensity q.1 q.2.1 q.2.2 v u) =
      ∑' d : ℕ, primeCrossing v d := by
  rw [← integral_tsum_of_summable_integral_norm
    (fun q : ChainIndex => integrable_chainDensity q.1 q.2.1.property q.2.2.property hv hvc)
    (complete_chain_norm_summable hv hvc)]
  exact (complete_chain_hasSum hv hvc).tsum_eq

theorem complete_chain_zero_iff {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    (∑' q : ChainIndex, chainIntegral v q) = 0 ↔ v = 0 := by
  rw [(complete_chain_hasSum hv hvc).tsum_eq,
    ← (compact_primeCrossing_hasSum_cuts hv hvc).tsum_eq]
  exact crossing_cuts_eq_zero_iff hv hvc

/-- The negative reflected-prime sector is retained through its original compensation. -/
theorem reflected_compensation_hasSum_chains {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) :
    HasSum (chainIntegral v)
      (∑' d : ℕ, (vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
        phiDoobCollarKillingDensity v (Real.log d) x) -
          2 * CHMDReflectedPrime.reflectedDifference v d)) := by
  simpa only [CHMDReflectedPrime.primeCrossing_eq_compensation hv hvc hodd] using
    complete_chain_hasSum hv hvc

end RHTower.CHMDPrimeChainSource
