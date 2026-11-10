import GaloisForLFunctions.HyperbolicArakelovTheory.TheSuspensionOfThePrimeGreenKernel
import Mathlib.Algebra.BigOperators.Field

/-!
# The continuum channel of a prime Green ladder

The translation average of a finite Green ladder has a limit on every compact
packet. Its positive spectral complement is a continuum quadratic form with
exactly the prime-power correlations and one scalar mass coefficient.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm

def correlationCoefficient (p : ℕ) (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (1 / Real.sqrt p) ^ (k + 1) * autocorr f ((k + 1 : ℕ) * Real.log p)

private theorem correlation_cutoff {p : ℕ} (hp : p.Prime)
    {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ K : ℕ, ∀ k, K ≤ k → correlationCoefficient p f k = 0 := by
  have hc : IsCompact (tsupport (autocorr f)) := hasCompactSupport_autocorr hfc
  obtain ⟨B, hB⟩ := hc.bddAbove
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨K, hK⟩ := exists_nat_gt (B / Real.log p)
  refine ⟨K, fun k hk => ?_⟩
  have hz : autocorr f ((k + 1 : ℕ) * Real.log p) = 0 := by
    by_contra hne
    have hb := hB (subset_closure (Function.mem_support.mpr hne))
    have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
    have hKb : B < (K : ℝ) * Real.log p := (div_lt_iff₀ hL).mp hK
    push_cast at hb
    nlinarith only [hb, hKb, hL, mul_le_mul_of_nonneg_right hk' hL.le]
  rw [correlationCoefficient, hz, mul_zero]

theorem correlationCoefficient_finite_support {p : ℕ} (hp : p.Prime)
    {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    (Function.support (correlationCoefficient p f)).Finite := by
  obtain ⟨K, hK⟩ := correlation_cutoff hp hfc
  apply (Finset.finite_toSet (Finset.range K)).subset
  intro k hk
  by_contra hmem
  exact hk (hK k (by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem))

/-- The complete prime-power correlation, finite on compact packets. -/
def primeCorrelation (p : ℕ) (f : ℝ → ℝ) : ℝ :=
  2 * Real.log p * ∑ᶠ k, correlationCoefficient p f k

/-- First lag moment controls the exact finite-ladder error. -/
def correlationMoment (p : ℕ) (f : ℝ → ℝ) : ℝ :=
  2 * Real.log p * ∑ᶠ k, ((k + 1 : ℕ) : ℝ) * correlationCoefficient p f k

/-- The positive upper spectral complement after the ladder length tends to infinity. -/
def continuumChannel (p : ℕ) (f : ℝ → ℝ) : ℝ :=
  capacity p * (∫ u, f u ^ 2) - primeCorrelation p f

/-- Beyond the packet's lag support, the finite-ladder error is exactly a first moment over `N`. -/
theorem positiveChannel_eventually_eq {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∀ᶠ N : ℕ in atTop,
      positiveChannel p N f = continuumChannel p f + correlationMoment p f / N := by
  obtain ⟨K, hK⟩ := correlation_cutoff hp hfc
  filter_upwards [eventually_ge_atTop (max K 1)] with N hN
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right K 1).trans hN)
  have hKN : K ≤ N := (le_max_left K 1).trans hN
  have hs : Function.support (correlationCoefficient p f) ⊆ (Finset.range N : Set ℕ) := by
    intro k hk
    by_contra hmem
    exact hk (hK k (hKN.trans (by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem)))
  have hm : Function.support (fun k => ((k + 1 : ℕ) : ℝ) * correlationCoefficient p f k) ⊆
      (Finset.range N : Set ℕ) := by
    intro k hk
    apply hs
    intro hz
    exact hk (by
      change ((k + 1 : ℕ) : ℝ) * correlationCoefficient p f k = 0
      rw [hz, mul_zero])
  rw [positiveChannel_eq hp hN0 hf hfc, continuumChannel, primeCorrelation, correlationMoment,
    finsum_eq_sum_of_support_subset _ hs, finsum_eq_sum_of_support_subset _ hm]
  change capacity p * (∫ u, f u ^ 2) -
    2 * Real.log p * (∑ k ∈ Finset.range N, (1 - ((k + 1 : ℕ) : ℝ) / N) *
      correlationCoefficient p f k) = _
  simp_rw [sub_mul, one_mul, div_mul_eq_mul_div]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  ring

theorem tendsto_positiveChannel {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun N => positiveChannel p N f) atTop (𝓝 (continuumChannel p f)) := by
  have hi : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h : Tendsto (fun N : ℕ => continuumChannel p f + correlationMoment p f * (1 / N))
      atTop (𝓝 (continuumChannel p f)) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (hi.const_mul (correlationMoment p f))
  apply h.congr'
  filter_upwards [positiveChannel_eventually_eq hp hf hfc] with N hN
  simpa only [div_eq_mul_inv, one_mul] using hN.symm

/-- Positivity survives the continuum limit, including packets with overlapping translates. -/
theorem continuumChannel_nonneg {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : 0 ≤ continuumChannel p f := by
  apply ge_of_tendsto (tendsto_positiveChannel hp hf hfc)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact positiveChannel_nonneg hp (lt_of_lt_of_le Nat.zero_lt_one hN) hf hfc

#print axioms positiveChannel_eventually_eq
#print axioms tendsto_positiveChannel
#print axioms continuumChannel_nonneg

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
