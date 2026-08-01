import GaloisForLFunctions.RHTower.XiPhysicalEndpointLocalStiffness
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

/-!
# Cofinal nonzero completed physical-endpoint prime triangles

The corrected completed physical-endpoint response is continuous and strictly positive at zero.
Euler divergence forces arbitrarily late triples of consecutive primes whose three pairwise
logarithmic gaps lie in any prescribed zero neighborhood.  Hence the literal completed
Euler--Gamma pair response has a cofinal family of strictly positive triangle holonomies.

This closes the prior nonvanishing gap without the prime number theorem, Xi-zero enumeration, or
numerical certification.
-/

open scoped BigOperators
open Complex

namespace RHTower

noncomputable section

theorem continuous_xiPhysicalEndpointValuationCorrectionKernel :
    Continuous xiPhysicalEndpointValuationCorrectionKernel := by
  change Continuous (fun t : ℝ => ∑' pe : Nat.Primes × ℕ,
    xiPhysicalEndpointValuationCorrectionKernelTerm t pe)
  apply continuous_tsum
  · intro pe
    unfold xiPhysicalEndpointValuationCorrectionKernelTerm
    fun_prop
  · exact summable_abs_clocked_xiPhysicalEndpointValuationCorrection
  · intro pe t
    rw [xiPhysicalEndpointValuationCorrectionKernelTerm, norm_mul,
      Complex.norm_exp]
    have him :
        (-Complex.I *
          (((pe.2 + 1 : ℕ) : ℝ) * Real.log (pe.1 : ℝ) * t : ℂ)).re = 0 := by
      have harg :
          -Complex.I *
              (((pe.2 + 1 : ℕ) : ℝ) * Real.log (pe.1 : ℝ) * t : ℂ) =
            ((-(((pe.2 + 1 : ℕ) : ℝ) *
              Real.log (pe.1 : ℝ) * t) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
    rw [him, Real.exp_zero, mul_one, norm_mul,
      Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]

private theorem continuous_seamFluxCochain_vertical (σ : ℝ)
    (hσ : 1 ≤ σ) :
    Continuous (fun t : ℝ =>
      seamFluxCochain ((σ : ℂ) + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hxi : AnalyticAt ℂ xi ((σ : ℂ) + (t : ℂ) * I) :=
    xi_analyticOnNhd_univ _ (Set.mem_univ _)
  have hxi0 : xi ((σ : ℂ) + (t : ℂ) * I) ≠ 0 :=
    xi_ne_zero_of_one_le_re (by simpa [Complex.mul_re] using hσ)
  have houter : ContinuousAt seamFluxCochain
      ((σ : ℂ) + (t : ℂ) * I) := by
    change ContinuousAt (fun z => -logDeriv xi z) _
    exact (hxi.deriv.div hxi hxi0).neg.continuousAt
  have harg : ContinuousAt
      (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) t := by fun_prop
  have hcomp := ContinuousAt.comp
    (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I)
    (g := seamFluxCochain) houter harg
  simpa [Function.comp_def] using hcomp

theorem continuous_xiPhysicalEndpointCompletedKernel :
    Continuous xiPhysicalEndpointCompletedKernel := by
  change Continuous (fun t : ℝ =>
    xiCompletedApertureOffDiagonalKernel (1 / 2) t 0 -
      2 * xiCompletedApertureOffDiagonalKernel (3 / 2) t 0 +
        xiPhysicalEndpointValuationCorrectionKernel t)
  have hone := continuous_seamFluxCochain_vertical 1 (by norm_num)
  have htwo := continuous_seamFluxCochain_vertical 2 (by norm_num)
  have hfirst :
      Continuous (fun t : ℝ =>
        xiCompletedApertureOffDiagonalKernel (1 / 2) t 0) := by
    simpa only [xiCompletedApertureOffDiagonalKernel, sub_zero,
      show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using hone
  have hsecond :
      Continuous (fun t : ℝ =>
        xiCompletedApertureOffDiagonalKernel (3 / 2) t 0) := by
    simpa only [xiCompletedApertureOffDiagonalKernel, sub_zero,
      show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num] using htwo
  exact (hfirst.sub (continuous_const.mul hsecond)).add
    continuous_xiPhysicalEndpointValuationCorrectionKernel

/-- Symmetric real completed endpoint response as a function of one log-ratio coordinate. -/
def xiPhysicalEndpointCompletedSymRealKernel (t : ℝ) : ℝ :=
  ((xiPhysicalEndpointCompletedKernel t +
      xiPhysicalEndpointCompletedKernel (-t)) / 2).re

theorem continuous_xiPhysicalEndpointCompletedSymRealKernel :
    Continuous xiPhysicalEndpointCompletedSymRealKernel := by
  change Continuous (fun t : ℝ =>
    ((xiPhysicalEndpointCompletedKernel t +
      xiPhysicalEndpointCompletedKernel (-t)) / 2).re)
  have hcomplex := (continuous_xiPhysicalEndpointCompletedKernel.add
    (continuous_xiPhysicalEndpointCompletedKernel.comp
      continuous_neg)).div_const 2
  have hre := Complex.continuous_re.comp hcomplex
  simpa [Function.comp_def] using hre

theorem xiPhysicalEndpointCompletedSymRealKernel_zero_pos :
    0 < xiPhysicalEndpointCompletedSymRealKernel 0 := by
  simpa [xiPhysicalEndpointCompletedSymRealKernel] using
    xiPhysicalEndpointCompletedKernel_zero_re_pos

theorem exists_xiPhysicalEndpointCompletedSymRealKernel_pos_near_zero :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      0 < xiPhysicalEndpointCompletedSymRealKernel t := by
  let U : Set ℝ := {t | 0 < xiPhysicalEndpointCompletedSymRealKernel t}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const
      continuous_xiPhysicalEndpointCompletedSymRealKernel
  have h0U : (0 : ℝ) ∈ U :=
    xiPhysicalEndpointCompletedSymRealKernel_zero_pos
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen 0 h0U
  refine ⟨ε, hε, ?_⟩
  intro t ht
  exact hball (by simpa [Real.dist_eq] using ht)

theorem xiPhysicalEndpointCompletedPrimeRatioRealKernel_eq_symReal
    (p q : Nat.Primes) :
    xiPhysicalEndpointCompletedPrimeRatioRealKernel p q =
      xiPhysicalEndpointCompletedSymRealKernel
        (Real.log (p : ℝ) - Real.log (q : ℝ)) := by
  unfold xiPhysicalEndpointCompletedPrimeRatioRealKernel
    xiPhysicalEndpointCompletedSymRealKernel
  rw [show Real.log (q : ℝ) - Real.log (p : ℝ) =
      -(Real.log (p : ℝ) - Real.log (q : ℝ)) by ring]

/-- **Cofinal positive source holonomy.** Arbitrarily far triples of consecutive marked primes
have all three completed physical-endpoint pair responses strictly positive. -/
theorem exists_cofinal_positive_physicalEndpoint_pair_triangle
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      0 < xiPhysicalEndpointCompletedPairResponse
        (nthPrimeSubtype n) (nthPrimeSubtype (n + 1)) ∧
      0 < xiPhysicalEndpointCompletedPairResponse
        (nthPrimeSubtype (n + 1)) (nthPrimeSubtype (n + 2)) ∧
      0 < xiPhysicalEndpointCompletedPairResponse
        (nthPrimeSubtype (n + 2)) (nthPrimeSubtype n) := by
  obtain ⟨ε, hε, hpos⟩ :=
    exists_xiPhysicalEndpointCompletedSymRealKernel_pos_near_zero
  obtain ⟨n, hn, hgap1, hgap2⟩ :=
    exists_two_consecutive_nthPrime_log_gaps_lt (half_pos hε) N
  let p := nthPrimeSubtype n
  let q := nthPrimeSubtype (n + 1)
  let r := nthPrimeSubtype (n + 2)
  have hlogpq :
      |Real.log (p : ℝ) - Real.log (q : ℝ)| < ε := by
    have hmono := nthPrimeSubtype_log_strictMono n.lt_succ_self
    dsimp [p, q]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hlogqr :
      |Real.log (q : ℝ) - Real.log (r : ℝ)| < ε := by
    have hmono := nthPrimeSubtype_log_strictMono (n + 1).lt_succ_self
    dsimp [q, r]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hlogrp :
      |Real.log (r : ℝ) - Real.log (p : ℝ)| < ε := by
    have hmono1 := nthPrimeSubtype_log_strictMono n.lt_succ_self
    have hmono2 := nthPrimeSubtype_log_strictMono (n + 1).lt_succ_self
    dsimp [r, p]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hpqKernel :
      0 < xiPhysicalEndpointCompletedPrimeRatioRealKernel p q := by
    rw [xiPhysicalEndpointCompletedPrimeRatioRealKernel_eq_symReal]
    exact hpos _ hlogpq
  have hqrKernel :
      0 < xiPhysicalEndpointCompletedPrimeRatioRealKernel q r := by
    rw [xiPhysicalEndpointCompletedPrimeRatioRealKernel_eq_symReal]
    exact hpos _ hlogqr
  have hrpKernel :
      0 < xiPhysicalEndpointCompletedPrimeRatioRealKernel r p := by
    rw [xiPhysicalEndpointCompletedPrimeRatioRealKernel_eq_symReal]
    exact hpos _ hlogrp
  refine ⟨n, hn, ?_, ?_, ?_⟩
  · rw [xiPhysicalEndpointCompletedPairResponse]
    exact mul_pos
      (mul_pos (physicalPrimeEndpointWeight_pos p)
        (physicalPrimeEndpointWeight_pos q)) hpqKernel
  · rw [xiPhysicalEndpointCompletedPairResponse]
    exact mul_pos
      (mul_pos (physicalPrimeEndpointWeight_pos q)
        (physicalPrimeEndpointWeight_pos r)) hqrKernel
  · rw [xiPhysicalEndpointCompletedPairResponse]
    exact mul_pos
      (mul_pos (physicalPrimeEndpointWeight_pos r)
        (physicalPrimeEndpointWeight_pos p)) hrpKernel

end

end RHTower
