import GaloisForLFunctions.HTGeometry.OscillatorLadderIdentity

/-!
# The windowed virial identity for the oscillator ladder

Expanding the lowering operator `Av = v′ + ξv` and integrating the cross term by parts gives, on
any window and with no hypothesis beyond differentiability,

`∫_a^b (Av)² = ∫_a^b v′² + ∫_a^b ξ²v² − ∫_a^b v² + [ξv²]_a^b` .

The cross term is exact: `2ξvv′ = (ξv²)′ − v²`.  So the kinetic and potential energies on a window
are controlled by the ladder image, the mass, and one boundary value — which is how square
integrability of `v` and of `Av` propagates to `v′` and to `ξv`.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- The derivative of the boundary weight `ξ·v²`. -/
theorem hasDerivAt_mulSq {v v' : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (v' x) x) (x : ℝ) :
    HasDerivAt (fun y => y * v y ^ (2 : ℕ)) (v x ^ (2 : ℕ) + 2 * x * (v x * v' x)) x := by
  have h := (hasDerivAt_id x).mul ((hv x).pow 2)
  refine h.congr_deriv ?_
  simp only [id_eq, Pi.pow_apply]
  ring

/-- **The windowed virial identity.** -/
theorem integral_oscLower_sq_virial {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x) (hcv' : Continuous v') (a b : ℝ) :
    (∫ x in a..b, oscLower v v' x ^ (2 : ℕ))
      = (∫ x in a..b, v' x ^ (2 : ℕ)) + (∫ x in a..b, x ^ (2 : ℕ) * v x ^ (2 : ℕ))
        - (∫ x in a..b, v x ^ (2 : ℕ)) + (b * v b ^ (2 : ℕ) - a * v a ^ (2 : ℕ)) := by
  have hcv : Continuous v := continuous_of_hasDerivAt hv
  have hA : Continuous fun x : ℝ => v' x ^ (2 : ℕ) := hcv'.pow 2
  have hB : Continuous fun x : ℝ => 2 * x * (v x * v' x) :=
    (continuous_const.mul continuous_id).mul (hcv.mul hcv')
  have hC : Continuous fun x : ℝ => x ^ (2 : ℕ) * v x ^ (2 : ℕ) := (continuous_pow 2).mul (hcv.pow 2)
  have hD : Continuous fun x : ℝ => v x ^ (2 : ℕ) := hcv.pow 2
  -- the cross term integrates exactly
  have hcross : (∫ x in a..b, 2 * x * (v x * v' x))
      = (b * v b ^ (2 : ℕ) - a * v a ^ (2 : ℕ)) - ∫ x in a..b, v x ^ (2 : ℕ) := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => y * v y ^ (2 : ℕ))
      (f' := fun x => v x ^ (2 : ℕ) + 2 * x * (v x * v' x))
      (fun x _ => hasDerivAt_mulSq hv x) ((hD.add hB).intervalIntegrable a b)
    rw [intervalIntegral.integral_add (hD.intervalIntegrable a b)
      (hB.intervalIntegrable a b)] at hftc
    linarith [hftc]
  -- expand the square
  have hexp : (∫ x in a..b, oscLower v v' x ^ (2 : ℕ))
      = (∫ x in a..b, v' x ^ (2 : ℕ)) + (∫ x in a..b, 2 * x * (v x * v' x))
        + ∫ x in a..b, x ^ (2 : ℕ) * v x ^ (2 : ℕ) := by
    have hsplit : (∫ x in a..b, (v' x ^ (2 : ℕ) + 2 * x * (v x * v' x)) + x ^ (2 : ℕ) * v x ^ (2 : ℕ))
        = ((∫ x in a..b, v' x ^ (2 : ℕ)) + (∫ x in a..b, 2 * x * (v x * v' x)))
          + ∫ x in a..b, x ^ (2 : ℕ) * v x ^ (2 : ℕ) := by
      have hAB : IntervalIntegrable (fun x : ℝ => v' x ^ (2 : ℕ) + 2 * x * (v x * v' x))
          volume a b := (hA.add hB).intervalIntegrable a b
      have hAi : IntervalIntegrable (fun x : ℝ => v' x ^ (2 : ℕ)) volume a b :=
        hA.intervalIntegrable a b
      have hBi : IntervalIntegrable (fun x : ℝ => 2 * x * (v x * v' x)) volume a b :=
        hB.intervalIntegrable a b
      have hCi : IntervalIntegrable (fun x : ℝ => x ^ (2 : ℕ) * v x ^ (2 : ℕ)) volume a b :=
        hC.intervalIntegrable a b
      rw [intervalIntegral.integral_add hAB hCi, intervalIntegral.integral_add hAi hBi]
    rw [← hsplit]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [oscLower]
    ring
  rw [hexp, hcross]
  ring

end GaloisForLFunctions.HTGeometry
