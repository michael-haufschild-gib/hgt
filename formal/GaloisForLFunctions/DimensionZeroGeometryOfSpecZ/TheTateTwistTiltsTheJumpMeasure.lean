import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheTateTwistIsTheShiftedPair
import GaloisForLFunctions.ArithmeticIncidencePositivity.ShiftedPairOddWindowSelectivity

/-!
# The Tate twist tilts the jump measure

Weil's form is the energy of a jump process: archimedean jumps of length `t` at rate `ω(t)`
(`archLevyDensity`, the Lévy density of the Gamma factor) and prime jumps of length `log n` at rate
`Λ(n)n^{−1/2}`, plus a potential and the pole. This module computes the symmetric Tate twist
`Q^{(k)}(H) = W(e^{k·}H, e^{−k·}H)` in these terms (`tateTwistedForm_eq_tilted`):

`Q^{(k)}(H) = 2θ′(0)‖H‖² + ∫_{t>0} ω(t)(2‖H‖² − 2cosh(kt) c_H(t)) dt
  − Σ_n Λ(n)n^{−1/2} cosh(k log n)(c_H(log n) + c_H(−log n)) + pole_k(H)`.

**The archimedean place in dimension `k` is the tilted Lévy density `ω(t)cosh(kt)`**, and the
arithmetic place in dimension `k` is the tilted prime measure `Λ(n)n^{−1/2}cosh(k log n)`: the Tate
twist reweights archimedean and arithmetic jumps of the same length by the same factor `cosh(kt)`
(the symmetrized Esscher transform). The diagonal `2‖H‖²∫ω` is untouched; only the correlations
are tilted. Hence the archimedean place does not change its *ratio* to the primes at any length when
the dimension changes — positive dimension does not separate the two places; it amplifies long jumps
of both kinds equally, which is why the twisted form is the zero form of a fake with the zeros moved
off the line (`tateTwistedForm_eq_half_shiftedPairZeroForm`).

Tools: `integral_sub_shift_sq` (`∫(F − F(· + x))² = 2‖F‖² − 2c_F(x)`), and the cosh/sinh splitting of
autocorrelations (`autoCorr_cosh_sub_autoCorr_sinh`, AIP).
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis ArithmeticCriticalityTheory
open _root_.RHTower

/-- `∫(F(u) − F(u + x))² du = 2‖F‖² − 2c_F(x)`. -/
theorem integral_sub_shift_sq {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (x : ℝ) : ∫ u, (F u - F (u + x)) ^ 2 = 2 * (∫ u, F u ^ 2) - 2 * autoCorr F x := by
  have h1 : Integrable fun u => F u ^ 2 :=
    (hF.pow 2).integrable_of_hasCompactSupport (by simpa [sq] using hFc.mul_right (f' := F))
  have h2 : Integrable fun u => F (u + x) ^ 2 := h1.comp_add_right x
  have h3 : Integrable fun u => F u * F (u + x) :=
    (hF.mul (hF.comp (continuous_add_const x))).integrable_of_hasCompactSupport hFc.mul_right
  have e : (fun u => (F u - F (u + x)) ^ 2) =
      fun u => F u ^ 2 + F (u + x) ^ 2 - 2 * (F u * F (u + x)) := by
    funext u; ring
  rw [e, integral_sub (f := fun u => F u ^ 2 + F (u + x) ^ 2) (g := fun u => 2 * (F u * F (u + x)))
    (h1.add h2) (h3.const_mul 2), integral_add h1 h2, integral_const_mul,
    integral_add_right_eq_self (fun u => F u ^ 2) x, autoCorr]
  ring

/-- The **tilted Lévy energy** `∫_{t>0} ω(t)(2‖H‖² − 2cosh(kt)c_H(t)) dt`: the archimedean jumps in
Tate dimension `k`. -/
def tiltedLevyEnergy (k : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), archLevyDensity t * (2 * (∫ u, H u ^ 2) - 2 * Real.cosh (k * t) * autoCorr H t)

/-- The **tilted prime sum** `Σ_n Λ(n)n^{−1/2}cosh(k log n)(c_H(−log n) + c_H(log n))`: the prime jumps
in Tate dimension `k`. -/
def tiltedPrimeSum (k : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n *
    (Real.cosh (k * Real.log n) * (autoCorr H (-Real.log n) + autoCorr H (Real.log n)))

/-- The pole part in Tate dimension `k`. -/
def tiltedPole (k : ℝ) (H : ℝ → ℝ) : ℝ :=
  (2 * coshHalfMoment (fun u => H u * Real.cosh (k * u)) ^ 2 -
      2 * sinhHalfMoment (fun u => H u * Real.cosh (k * u)) ^ 2) -
    (2 * coshHalfMoment (fun u => H u * Real.sinh (k * u)) ^ 2 -
      2 * sinhHalfMoment (fun u => H u * Real.sinh (k * u)) ^ 2)

/-- **The Tate twist tilts the jump measure.** -/
theorem tateTwistedForm_eq_tilted {H : ℝ → ℝ} (hH : H ∈ realTests) (k : ℝ) :
    tateTwistedForm k H = 2 * gammaHardyPhaseRate 0 * (∫ u, H u ^ 2) + tiltedLevyEnergy k H -
      tiltedPrimeSum k H + tiltedPole k H := by
  have hc : (fun u => H u * Real.cosh (k * u)) ∈ realTests := mul_mem_realTests hH (by fun_prop)
  have hs : (fun u => H u * Real.sinh (k * u)) ∈ realTests := mul_mem_realTests hH (by fun_prop)
  set Hc : ℝ → ℝ := fun u => H u * Real.cosh (k * u) with hHc
  set Hs : ℝ → ℝ := fun u => H u * Real.sinh (k * u) with hHs
  have hsq : ∀ F : ℝ → ℝ, F ∈ realTests → Integrable fun u => F u ^ 2 := fun F hF =>
    (hF.1.continuous.pow 2).integrable_of_hasCompactSupport
      (by simpa [sq] using hF.2.mul_right (f' := F))
  -- the norm
  have hnorm : (∫ u, Hc u ^ 2) - (∫ u, Hs u ^ 2) = ∫ u, H u ^ 2 := by
    rw [← integral_sub (hsq Hc hc) (hsq Hs hs)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hHc, hHs]
    have := Real.cosh_sq (k * u)
    nlinarith [this]
  -- the archimedean jumps
  have hlevy : levyEnergy Hc - levyEnergy Hs = tiltedLevyEnergy k H := by
    rw [levyEnergy, levyEnergy, ← integral_sub (integrableOn_levyIntegrand hc.1 hc.2)
      (integrableOn_levyIntegrand hs.1 hs.2), tiltedLevyEnergy]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [integral_sub_shift_sq hc.1.continuous hc.2, integral_sub_shift_sq hs.1.continuous hs.2,
      ← hnorm]
    have hac : autoCorr Hc t - autoCorr Hs t = Real.cosh (k * t) * autoCorr H t :=
      ArithmeticIncidencePositivity.autoCorr_cosh_sub_autoCorr_sinh hH.1.continuous hH.2 k t
    linear_combination (-2 * archLevyDensity t) * hac
  -- the prime jumps
  have hprime : primeSum Hc - primeSum Hs = tiltedPrimeSum k H := by
    rw [primeSum, primeSum, ← (summable_primeSum_terms hc.2).tsum_sub
      (summable_primeSum_terms hs.2), tiltedPrimeSum]
    refine tsum_congr fun n => ?_
    have e1 : ∀ F : ℝ → ℝ, (∫ t, F t * F (t - Real.log n)) = autoCorr F (-Real.log n) :=
      fun F => by simp only [autoCorr, sub_eq_add_neg]
    have hac1 : autoCorr Hc (-Real.log n) - autoCorr Hs (-Real.log n) =
        Real.cosh (k * Real.log n) * autoCorr H (-Real.log n) := by
      have := ArithmeticIncidencePositivity.autoCorr_cosh_sub_autoCorr_sinh hH.1.continuous hH.2 k
        (-Real.log n)
      rwa [mul_neg, Real.cosh_neg] at this
    have hac2 : autoCorr Hc (Real.log n) - autoCorr Hs (Real.log n) =
        Real.cosh (k * Real.log n) * autoCorr H (Real.log n) :=
      ArithmeticIncidencePositivity.autoCorr_cosh_sub_autoCorr_sinh hH.1.continuous hH.2 k
        (Real.log n)
    rw [e1 Hc, e1 Hs]
    show vonMangoldtAtom n * (autoCorr Hc (-Real.log n) + autoCorr Hc (Real.log n)) -
      vonMangoldtAtom n * (autoCorr Hs (-Real.log n) + autoCorr Hs (Real.log n)) = _
    linear_combination vonMangoldtAtom n * hac1 + vonMangoldtAtom n * hac2
  rw [tateTwistedForm_eq hH, weilQuad_eq hc.1 hc.2, weilQuad_eq hs.1 hs.2, tiltedPole, ← hlevy,
    ← hprime, ← hnorm]
  ring

/-- The tilt is even in the dimension: the archimedean place in dimension `k` and in dimension `−k`
agree. -/
theorem tiltedLevyEnergy_neg (k : ℝ) (H : ℝ → ℝ) :
    tiltedLevyEnergy (-k) H = tiltedLevyEnergy k H := by
  simp only [tiltedLevyEnergy, neg_mul, Real.cosh_neg]

/-- At dimension zero the tilted Lévy energy is the Lévy energy. -/
theorem tiltedLevyEnergy_zero {H : ℝ → ℝ} (hH : H ∈ realTests) :
    tiltedLevyEnergy 0 H = levyEnergy H := by
  rw [tiltedLevyEnergy, levyEnergy]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [zero_mul, Real.cosh_zero, mul_one]
  rw [integral_sub_shift_sq hH.1.continuous hH.2]

/-- **The tilt only amplifies**: for every `t`, the archimedean rate in dimension `k` dominates the
rate in dimension zero, `ω(t)cosh(kt) ≥ ω(t)`, and the same factor multiplies the prime rate at
`t = log n`. -/
theorem archLevyDensity_le_tilted {t : ℝ} (ht : 0 < t) (k : ℝ) :
    archLevyDensity t ≤ archLevyDensity t * Real.cosh (k * t) :=
  le_mul_of_one_le_right (archLevyDensity_pos ht).le (Real.one_le_cosh _)

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
