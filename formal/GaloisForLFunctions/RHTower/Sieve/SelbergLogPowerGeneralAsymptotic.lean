import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerHarmonicGeneral
import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerOriginalAsymptotics

/-!
# The Selberg log-monomial asymptotic at every pair of positive powers

The Barban--Vehov / Graham diagonal analysis needs

`∑_{m,n ≤ N} μ(m)μ(n)(m,n)/(mn) · log(N/m)^i log(N/n)^j  ~  (i·j/(i+j-1)) · (log N)^{i+j-1}`

for every pair of positive exponents.  The previously available instances were the four hand-made
cases `(1,1)`, `(1,2)`, `(2,2)`, `(1,4)`, `(2,3)`.  This file proves the whole family at once, by
combining the already-general harmonic replacement
`tendsto_selbergPrincipalScaledLogPowerModel_sub_harmonic_div_log_pow_zero` with the general
harmonic evaluation `tendsto_selbergLogPowerHarmonicMain_div_log_pow`, and then transporting
through the Euler-correction convolution by dominated convergence.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- **Every fixed principal dilation has leading coefficient `(q+1)(r+1)/(q+r+1)`.** -/
theorem tendsto_selbergPrincipalScaledLogPowerModel_div_log_pow
    (q r : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) a b N /
        Real.log N ^ (q + r + 1))
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1))) := by
  have herr :=
    tendsto_selbergPrincipalScaledLogPowerModel_sub_harmonic_div_log_pow_zero q r ha hb
  have hmain := tendsto_selbergLogPowerHarmonicMain_div_log_pow q r ha hb
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N _
  ring

/-- Termwise limit of the Euler-correction convolution, at every pair of powers. -/
theorem tendsto_selbergCorrectionScaledLogPowerTerm
    (q r : ℕ) (mn : ℕ × ℕ) :
    Tendsto (fun N : ℕ => selbergCorrectionScaledLogPowerTerm q r N mn)
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1) *
        selbergEulerCorrectionCoeff mn.1 mn.2)) := by
  rcases mn with ⟨a, b⟩
  rcases a.eq_zero_or_pos with rfl | ha
  · simp [selbergCorrectionScaledLogPowerTerm, selbergEulerCorrectionCoeff]
  rcases b.eq_zero_or_pos with rfl | hb
  · simp [selbergCorrectionScaledLogPowerTerm, selbergEulerCorrectionCoeff]
  have hmain :=
    (tendsto_selbergPrincipalScaledLogPowerModel_div_log_pow q r ha hb).const_mul
      (selbergEulerCorrectionCoeff a b)
  simpa only [mul_comm] using hmain.congr' (by
    filter_upwards [eventually_ge_atTop (max a b)] with N hN
    rw [selbergCorrectionScaledLogPowerTerm, if_pos]
    exact ⟨Finset.mem_Icc.mpr ⟨ha, (le_max_left a b).trans hN⟩,
      Finset.mem_Icc.mpr ⟨hb, (le_max_right a b).trans hN⟩⟩)

/-- Dominated-convergence limit of the whole Euler-correction convolution. -/
theorem tendsto_tsum_selbergCorrectionScaledLogPowerTerm (q r : ℕ) :
    Tendsto (fun N : ℕ => ∑' mn : ℕ × ℕ,
      selbergCorrectionScaledLogPowerTerm q r N mn)
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1))) := by
  obtain ⟨M, hM, hdomEventually⟩ :=
    exists_eventually_norm_selbergCorrectionScaledLogPowerTerm_le q r
  have hsumAbs : Summable (fun mn : ℕ × ℕ =>
      M * |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
    have hnorm := summable_selbergEulerCorrectionCoeff.norm
    have habs : Summable (fun mn : ℕ × ℕ =>
        |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
      simpa [Real.norm_eq_abs] using hnorm
    exact habs.mul_left M
  have hconv := tendsto_tsum_of_dominated_convergence hsumAbs
    (tendsto_selbergCorrectionScaledLogPowerTerm q r) hdomEventually
  rw [tsum_mul_left, tsum_selbergEulerCorrectionCoeff, mul_one] at hconv
  exact hconv

/-- **The original Selberg log-monomial at every pair of positive powers.** -/
theorem tendsto_selbergOriginalLogMonomial_succ_succ_div_log_pow (q r : ℕ) :
    Tendsto (fun N : ℕ =>
      selbergOriginalLogMonomial (q + 1) (r + 1) N / Real.log N ^ (q + r + 1))
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1))) := by
  refine (tendsto_tsum_selbergCorrectionScaledLogPowerTerm q r).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (selbergOriginalLogMonomial_succ_succ_div_log_pow_eq_tsum q r hN).symm

/-- **Graham's Selberg diagonal for an arbitrary logarithmic monomial.** -/
theorem tendsto_selbergOriginalLogMonomial_div_log_pow
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Tendsto (fun N : ℕ =>
      selbergOriginalLogMonomial i j N / Real.log N ^ (i + j - 1))
      atTop (𝓝 (((i : ℝ) * (j : ℝ)) / ((i : ℝ) + (j : ℝ) - 1))) := by
  obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
  have hexp : q + 1 + (r + 1) - 1 = q + r + 1 := by omega
  rw [hexp]
  have hval : (((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ)) /
      (((q + 1 : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) - 1) =
      (((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1) := by
    push_cast
    ring_nf
  rw [hval]
  exact tendsto_selbergOriginalLogMonomial_succ_succ_div_log_pow q r

end

end RHTower.Sieve
