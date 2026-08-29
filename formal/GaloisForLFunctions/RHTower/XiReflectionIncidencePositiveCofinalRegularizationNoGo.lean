import GaloisForLFunctions.RHTower.XiReflectionIncidenceTraceOneSourceConvergence

/-!
# Positive cofinal regularization no-go for trace-one reflection incidence

The literal coefficient-faithful trace-one rational-adelic residue mass is nonnegative.  A natural
attempt to bypass its nuclear endpoint is therefore to insert positive Abel, heat, Cesaro, or
source-dependent damping, recover every fixed prime coefficient at cofinal scale, and ask only for
bounded returns along some sparse cofinal subsequence.

This module closes that entire branch.  For every nonnegative ordered source, coefficientwise
recovery plus cofinally recurring bounded prefix budgets is equivalent to summability of the
undamped source.  No monotonicity, uniform coefficient convergence, or fixed damping law is used.
Applied to the exact trace-one reflection-incidence source, the regularized producer succeeds at a
divisor fibre exactly on the critical line and succeeds globally exactly under RH.

Off the line, the obstruction is sharper than failure of one chosen regularizer: for every
coefficient-recovering family and every proposed budget, every sufficiently late scale has a prime
prefix exceeding that budget.  Thus no positive cofinal regularization has even sparse bounded
returns.  A surviving producer must create signed cancellation before taking norms, abandon
coefficient recovery, or evacuate rather than close the cofinal source.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A nonnegative regularization of an ordered source restores every fixed coefficient and has
cofinally recurring, uniformly bounded full prefix budgets. -/
def PositiveCofinalOrderedRegularizationFrequentlyBounded (f : ℕ → ℝ) : Prop :=
  ∃ w : ℕ → ℕ → ℝ,
    (∀ N n, 0 ≤ w N n) ∧
    (∀ n, Tendsto (fun N : ℕ => w N n) atTop (nhds 1)) ∧
    ∃ C : ℝ, ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ∀ M : ℕ, ∑ n ∈ Finset.range M, w N n * f n ≤ C

private theorem eventually_all_finset_half_le
    {ι : Type*} (w : ℕ → ι → ℝ)
    (hw : ∀ i, Tendsto (fun N : ℕ => w N i) atTop (nhds 1))
    (s : Finset ι) :
    ∀ᶠ N : ℕ in atTop, ∀ i ∈ s, (1 / 2 : ℝ) ≤ w N i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hiEventually : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) < w N i :=
        ((tendsto_order.1 (hw i)).1 (1 / 2) (by norm_num))
      filter_upwards [hiEventually, ih] with N hiN hsN
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hiN.le
      · exact hsN j hj

/-- Positive cofinal regularization has no endpoint gain: even a bounded return along an
arbitrarily sparse cofinal subsequence is equivalent to summability of the undamped source. -/
theorem positiveCofinalOrderedRegularizationFrequentlyBounded_iff_summable
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    PositiveCofinalOrderedRegularizationFrequentlyBounded f ↔ Summable f := by
  constructor
  · rintro ⟨w, _hwNonneg, hwLimit, C, hC⟩
    apply summable_of_sum_range_le (c := 2 * C) hf
    intro M
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
      (eventually_all_finset_half_le w hwLimit (Finset.range M))
    obtain ⟨N, hN, hbound⟩ := hC N₀
    have hhalf :
        (1 / 2 : ℝ) * ∑ n ∈ Finset.range M, f n ≤
          ∑ n ∈ Finset.range M, w N n * f n := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun n hn =>
        mul_le_mul_of_nonneg_right (hN₀ N hN n hn) (hf n)
    have hCle : 0 ≤ C := by
      have := hbound 0
      simpa using this
    nlinarith [hhalf, hbound M]
  · intro hsum
    refine ⟨fun _ _ => 1, ?_, ?_, ∑' n, f n, ?_⟩
    · intro N n
      norm_num
    · intro n
      exact tendsto_const_nhds
    · intro N₀
      refine ⟨N₀, le_rfl, ?_⟩
      intro M
      simpa using hsum.sum_le_tsum (Finset.range M) (fun n _ => hf n)

/-- If the undamped positive source diverges, every coefficient-recovering regularization has
eventually unbounded finite prefixes.  No positivity or monotonicity of the transient weights is
needed for this stronger escape law. -/
theorem positiveCofinalOrderedRegularization_prefixes_eventually_exceed_of_not_summable
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hnot : ¬ Summable f) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n, Tendsto (fun N : ℕ => w N n) atTop (nhds 1)) :
    ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ M : ℕ, C < ∑ n ∈ Finset.range M, w N n * f n := by
  intro C
  have hex : ∃ M : ℕ, max (2 * C) 1 < ∑ n ∈ Finset.range M, f n := by
    by_contra h
    push Not at h
    exact hnot (summable_of_sum_range_le hf fun M => h M)
  obtain ⟨M, hM⟩ := hex
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (eventually_all_finset_half_le w hw (Finset.range M))
  refine ⟨N₀, fun N hN => ⟨M, ?_⟩⟩
  have hhalf :
      (1 / 2 : ℝ) * ∑ n ∈ Finset.range M, f n ≤
        ∑ n ∈ Finset.range M, w N n * f n := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn =>
      mul_le_mul_of_nonneg_right (hN₀ N hN n hn) (hf n)
  have hC : 2 * C ≤ max (2 * C) 1 := le_max_left _ _
  linarith

/-- The literal coefficient-faithful trace-one source mass, with ordinary primes in increasing
order, admits some positive cofinal regularization with bounded returns. -/
def XiReflectionIncidenceTraceOnePositiveCofinalRegularization
    (rho : XiDivisorSupport) : Prop :=
  PositiveCofinalOrderedRegularizationFrequentlyBounded
    (fun n => xiReflectionIncidencePrimeTraceOneSourceMass rho (nthPrimeEquiv n))

/-- Local classification: positive cofinal damping of the trace-one source succeeds exactly on
the critical line. -/
theorem xiReflectionIncidenceTraceOnePositiveCofinalRegularization_iff_criticalLine
    (rho : XiDivisorSupport) :
    XiReflectionIncidenceTraceOnePositiveCofinalRegularization rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [XiReflectionIncidenceTraceOnePositiveCofinalRegularization,
    positiveCofinalOrderedRegularizationFrequentlyBounded_iff_summable
      (fun n => xiReflectionIncidencePrimeTraceOneSourceMass_nonneg rho (nthPrimeEquiv n))]
  change
    Summable ((xiReflectionIncidencePrimeTraceOneSourceMass rho) ∘ nthPrimeEquiv) ↔ _
  rw [nthPrimeEquiv.summable_iff,
    summable_xiReflectionIncidencePrimeTraceOneSourceMass_iff,
    summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_one_iff]

/-- Global positive-regularization producer for every Xi divisor fibre. -/
def XiReflectionIncidenceTraceOnePositiveCofinalRegularizationLanding : Prop :=
  ∀ rho : XiDivisorSupport,
    XiReflectionIncidenceTraceOnePositiveCofinalRegularization rho

/-- Positive Abel/heat/Cesaro-style cofinal repair of the coefficient-faithful trace-one landing
is exactly RH, even if boundedness is requested only along an arbitrary cofinal subsequence. -/
theorem riemannHypothesis_iff_xiReflectionIncidenceTraceOnePositiveCofinalRegularizationLanding :
    RiemannHypothesis ↔
      XiReflectionIncidenceTraceOnePositiveCofinalRegularizationLanding := by
  rw [riemannHypothesis_iff_xiReflectionIncidenceTraceOneSourceOrdinaryLanding]
  apply forall_congr'
  intro rho
  exact xiReflectionIncidenceTraceOneSourceOrdinaryConvergent_iff_criticalLine rho |>.trans
    (xiReflectionIncidenceTraceOnePositiveCofinalRegularization_iff_criticalLine rho).symm

/-- Sharp off-line obstruction: after every sufficiently late regularization scale, some ordinary
prime prefix exceeds any proposed trace budget.  Sparse bounded returns are impossible. -/
theorem xiReflectionIncidenceTraceOnePositiveRegularizedPrefixes_eventually_exceed_of_offLine
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2)
    (w : ℕ → Nat.Primes → ℝ)
    (hw : ∀ p, Tendsto (fun N : ℕ => w N p) atTop (nhds 1)) :
    ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ M : ℕ, C < ∑ n ∈ Finset.range M,
        w N (nthPrimeEquiv n) *
          xiReflectionIncidencePrimeTraceOneSourceMass rho (nthPrimeEquiv n) := by
  apply positiveCofinalOrderedRegularization_prefixes_eventually_exceed_of_not_summable
    (fun n => xiReflectionIncidencePrimeTraceOneSourceMass_nonneg rho (nthPrimeEquiv n))
  · change ¬ Summable
      ((xiReflectionIncidencePrimeTraceOneSourceMass rho) ∘ nthPrimeEquiv)
    rw [nthPrimeEquiv.summable_iff,
      summable_xiReflectionIncidencePrimeTraceOneSourceMass_iff,
      summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_one_iff]
    exact hoff
  · exact fun n => hw (nthPrimeEquiv n)

end

end RHTower
