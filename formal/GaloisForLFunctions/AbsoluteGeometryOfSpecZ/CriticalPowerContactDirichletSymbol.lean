import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerContactMellin

/-!
# The restored critical transform has the actual contact symbol

Subtracting the harmonic source subtracts exactly a multiple of `ζ(s+1)`
from the contact Dirichlet series. Abel summation identifies the bounded
remainder transform on the absolute half-plane; restoring the harmonic
term recovers the literal prime-contact symbol.
-/

noncomputable section

open Complex Finset Filter Topology
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity TransHorizonIncidenceMechanics

private def criticalHarmonicContactSource (n : ℕ) : ℝ :=
  (powerTailZeta 1 * powerTailPrimeDeviation (1 / 2)) n -
    criticalPowerContactCoefficient * powerTailZeta 1 n

private theorem sourcePartialSum_criticalHarmonicContactSource :
    RHTower.sourcePartialSum criticalHarmonicContactSource = criticalHarmonicContacts := by
  funext N
  rw [RHTower.sourcePartialSum, criticalHarmonicContacts, powerContactPrefix]
  simp only [criticalHarmonicContactSource, sum_sub_distrib, ← mul_sum,
    show 2 * (1 / 2 : ℝ) = 1 by ring]
  congr 1
  congr 1
  rw [sum_Icc_one_shift, harm]
  apply sum_congr rfl
  intro n _
  have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have hz : (ζ : ArithmeticFunction ℝ) (n + 1) = 1 := by simp [hn]
  rw [powerTailZeta, powerTailTwist_apply, hz,
    mul_one, powerTailWeight, Real.rpow_neg_one]
  simp only [Nat.cast_add, Nat.cast_one, one_div]

private theorem critical_harmonic_zeta_source {n : ℕ} (hn : n ≠ 0) :
    (((ζ : ArithmeticFunction ℝ) n : ℝ) : ℂ) = (1 : ℕ → ℂ) n := by
  simp [hn]

private theorem summable_critical_harmonic_series {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (fun n => (powerTailZeta 1 n : ℂ)) s := by
  rw [powerTailZeta, LSeriesSummable_powerTailTwist_iff]
  apply (LSeriesSummable_congr _ (fun {n} hn => critical_harmonic_zeta_source hn)).mpr
  apply LSeriesSummable_one_iff.mpr
  simp only [add_re, ofReal_re]
  linarith only [hs]

private theorem critical_harmonic_series_eq {s : ℂ} (hs : 0 < s.re) :
    LSeries (fun n => (powerTailZeta 1 n : ℂ)) s = riemannZeta (s + 1) := by
  rw [powerTailZeta, LSeries_powerTailTwist,
    LSeries_congr (fun {n} hn => critical_harmonic_zeta_source hn)]
  apply LSeries_one_eq_riemannZeta
  simp only [add_re, ofReal_re]
  linarith only [hs]

private theorem term_criticalHarmonicContactSource (s : ℂ) (n : ℕ) :
    LSeries.term (fun k => (criticalHarmonicContactSource k : ℂ)) s n =
      LSeries.term (fun k => ((powerTailZeta 1 * powerTailPrimeDeviation (1 / 2)) k : ℂ)) s n -
        (criticalPowerContactCoefficient : ℂ) *
          LSeries.term (fun k => (powerTailZeta 1 k : ℂ)) s n := by
  by_cases hn : n = 0
  · simp only [hn, LSeries.term_zero, mul_zero, sub_self]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    LSeries.term_of_ne_zero hn, criticalHarmonicContactSource,
    Complex.ofReal_sub, Complex.ofReal_mul]
  ring

private theorem summable_criticalHarmonicContactSource {s : ℂ} (hs : 2 < s.re) :
    LSeriesSummable (fun n => (criticalHarmonicContactSource n : ℂ)) s := by
  have hcont := LSeriesSummable_powerContacts
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith only [hs] : 1 < s.re + 1 / 2)
  norm_num only [show 2 * (1 / 2 : ℝ) = 1 by ring] at hcont
  have hharm := summable_critical_harmonic_series (by linarith only [hs] : 0 < s.re)
  unfold LSeriesSummable at hcont hharm ⊢
  exact (hcont.sub (hharm.mul_left (criticalPowerContactCoefficient : ℂ))).congr
    fun n => (term_criticalHarmonicContactSource s n).symm

private theorem LSeries_criticalHarmonicContactSource {s : ℂ} (hs : 2 < s.re) :
    LSeries (fun n => (criticalHarmonicContactSource n : ℂ)) s =
      riemannZeta (s + 1) *
        (-deriv riemannZeta (s + (1 / 2 : ℝ)) / riemannZeta (s + (1 / 2 : ℝ)) -
          riemannZeta (s + (1 / 2 : ℝ))) -
        (criticalPowerContactCoefficient : ℂ) * riemannZeta (s + 1) := by
  have hcont := LSeriesSummable_powerContacts
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith only [hs] : 1 < s.re + 1 / 2)
  norm_num only [show 2 * (1 / 2 : ℝ) = 1 by ring] at hcont
  have hharm := summable_critical_harmonic_series (by linarith only [hs] : 0 < s.re)
  have hterm : (∑' n : ℕ, LSeries.term (fun k => (criticalHarmonicContactSource k : ℂ)) s n) =
      ∑' n : ℕ, (LSeries.term
        (fun k => ((powerTailZeta 1 * powerTailPrimeDeviation (1 / 2)) k : ℂ)) s n -
          (criticalPowerContactCoefficient : ℂ) *
            LSeries.term (fun k => (powerTailZeta 1 k : ℂ)) s n) :=
    tsum_congr (term_criticalHarmonicContactSource s)
  change LSeries (fun n => (criticalHarmonicContactSource n : ℂ)) s = _ at hterm
  rw [hterm, hcont.tsum_sub (hharm.mul_left (criticalPowerContactCoefficient : ℂ)),
    tsum_mul_left]
  change LSeries (fun n => ((powerTailZeta 1 * powerTailPrimeDeviation (1 / 2)) n : ℂ)) s -
    (criticalPowerContactCoefficient : ℂ) *
      LSeries (fun n => (powerTailZeta 1 n : ℂ)) s = _
  rw [critical_harmonic_series_eq (by linarith only [hs])]
  have he := LSeries_powerContacts (by norm_num : (0 : ℝ) < 1 / 2)
    (by linarith only [hs] : 1 < s.re + 1 / 2)
  norm_num only [show 2 * (1 / 2 : ℝ) = 1 by ring, Complex.ofReal_one] at he
  rw [he]

/-- Any strict interior power bound identifies the restored transform
with the literal contact Dirichlet symbol on the initial half-plane. -/
theorem criticalPowerContactMellin_initial_of_power_bound
    {θ C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, |criticalHarmonicContacts N| ≤ C * (N : ℝ) ^ θ)
    {s : ℂ} (hs : 2 < s.re) (hgap : θ < s.re) :
    criticalPowerContactMellin s =
      riemannZeta (s + 1) *
        (-deriv riemannZeta (s + (1 / 2 : ℝ)) / riemannZeta (s + (1 / 2 : ℝ)) -
          riemannZeta (s + (1 / 2 : ℝ))) := by
  rw [← sourcePartialSum_criticalHarmonicContactSource] at hb
  have hs0 : 0 < s.re := by linarith only [hs]
  rw [criticalPowerContactMellin, ← sourcePartialSum_criticalHarmonicContactSource,
    complexMellinPairing_sourcePartialSum_eq hC hb hs0 hgap,
    RHTower.abelTailSeries_sourcePartialSum hC hb hs0 hgap
      (summable_criticalHarmonicContactSource hs),
    LSeries_criticalHarmonicContactSource hs, sub_add_cancel]

/-- On the absolute half-plane the restored transform equals the literal
prime-contact Dirichlet symbol. -/
theorem criticalPowerContactMellin_initial
    (hc : PowerCombTailConverges (1 / 2)) {s : ℂ} (hs : 2 < s.re) :
    criticalPowerContactMellin s =
      riemannZeta (s + 1) *
        (-deriv riemannZeta (s + (1 / 2 : ℝ)) / riemannZeta (s + (1 / 2 : ℝ)) -
          riemannZeta (s + (1 / 2 : ℝ))) := by
  obtain ⟨L, hL⟩ := criticalPowerCombTailConverges_iff_harmonicContacts_converges.mp hc
  have hnorm : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(0 : ℝ)) * criticalHarmonicContacts N)
      atTop (𝓝 L) := by simpa only [neg_zero, Real.rpow_zero, one_mul] using hL
  obtain ⟨C, hC, hb⟩ := exists_power_bound_of_normalized_tendsto
    criticalHarmonicContacts_zero hnorm
  have hs0 : 0 < s.re := by linarith only [hs]
  exact criticalPowerContactMellin_initial_of_power_bound hC hb hs hs0

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
