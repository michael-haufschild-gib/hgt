import GaloisForLFunctions.HTGeometry.CarlemanOperatorBound

/-!
# The conductor Hankel kernel is bounded on the half line

The real-place conductor commutator has, in the Fourier picture, the Hankel kernel

`k(u + v) = 2π e^{-2(u+v)} / (u+v)`,

obtained by integrating the rank-one Hankel kernels of the resolvents `1/(λ + 2 + iξ)` over
`λ ∈ (0, ∞)`.  The exponential factor is harmless: pointwise `k(r) ≤ 2π/r`, so the Carleman
(Hilbert) kernel dominates and Schur's test for that kernel gives the bound directly.

This is what replaces the Coifman–Rochberg–Weiss commutator theorem for this symbol.  On the
physical side the row integrals of `(b(x) − b(y))/(x − y)` diverge, which is the `BMO` borderline;
on the Fourier side the exponential factor puts the kernel under the Carleman kernel and an
elementary test closes it.
-/

open MeasureTheory Set Filter Topology ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The conductor Hankel kernel `2π e^{-2r}/r` on the half line. -/
def conductorHankelKernel (r : ℝ) : ℝ := 2 * Real.pi * Real.exp (-2 * r) / r

theorem conductorHankelKernel_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ conductorHankelKernel r := by
  rw [conductorHankelKernel]
  positivity

/-- The exponential factor puts the conductor kernel under the Carleman kernel. -/
theorem conductorHankelKernel_le {r : ℝ} (hr : 0 < r) :
    conductorHankelKernel r ≤ 2 * Real.pi * (1 / r) := by
  rw [conductorHankelKernel, div_le_iff₀ hr]
  have hexp : Real.exp (-2 * r) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    linarith
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  calc 2 * Real.pi * Real.exp (-2 * r) ≤ 2 * Real.pi * 1 :=
        mul_le_mul_of_nonneg_left hexp hpi.le
    _ = 2 * Real.pi * (1 / r) * r := by field_simp

/-- **The conductor Hankel bound.**  Schur's test for the Carleman kernel transfers verbatim to
the conductor kernel, with the constant `(2π)² π²`. -/
theorem lintegral_conductorHankel_sq_le {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ s in Ioi (0:ℝ),
        (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (s + t)) * F t) ^ 2)
      ≤ ENNReal.ofReal (4 * Real.pi ^ 4) * ∫⁻ t in Ioi (0:ℝ), F t ^ 2 := by
  have hstep : ∀ s ∈ Ioi (0:ℝ),
      (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (s + t)) * F t) ^ 2
        ≤ ENNReal.ofReal (2 * Real.pi) ^ 2
          * (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hinner : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (s + t)) * F t)
        ≤ ENNReal.ofReal (2 * Real.pi)
          * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t := by
      rw [← lintegral_const_mul']
      · refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
        have ht0 : (0 : ℝ) < t := ht
        have hst : (0 : ℝ) < s + t := by linarith
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) (F t)
        exact conductorHankelKernel_le hst
      · exact ENNReal.ofReal_ne_top
    calc (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (s + t)) * F t) ^ 2
        ≤ (ENNReal.ofReal (2 * Real.pi)
            * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 := by
          exact pow_le_pow_left' hinner 2
      _ = ENNReal.ofReal (2 * Real.pi) ^ 2
            * (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 := by
          rw [mul_pow]
  have houter : (∫⁻ s in Ioi (0:ℝ),
      (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (conductorHankelKernel (s + t)) * F t) ^ 2)
      ≤ ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (2 * Real.pi) ^ 2
        * (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 :=
    setLIntegral_mono' measurableSet_Ioi hstep
  have hconst : (∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (2 * Real.pi) ^ 2
        * (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2)
      = ENNReal.ofReal (2 * Real.pi) ^ 2
        * ∫⁻ s in Ioi (0:ℝ), (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2 := by
    rw [← lintegral_const_mul']
    exact pow_ne_top ENNReal.ofReal_ne_top
  refine le_trans houter ?_
  rw [hconst]
  refine le_trans (mul_le_mul_left' (lintegral_carleman_sq_le hF) _) ?_
  rw [← mul_assoc]
  refine mul_le_mul_right' ?_ _
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [Real.pi_pos, sq_nonneg Real.pi]

end

end GaloisForLFunctions.HTGeometry
