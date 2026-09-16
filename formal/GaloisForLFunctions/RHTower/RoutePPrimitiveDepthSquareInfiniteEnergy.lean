import GaloisForLFunctions.RHTower.RoutePPrimitiveDepthSquareModularDefect

/-!
# Route P primitive depth-square infinite cubic-energy transport

The finite-packet depth-square law has an exact infinite counterpart whenever the original
cubic energy is summable.  This transports source energy along the literal injective arithmetic
depth square before any Xi graph landing.  It does not sum graph reporters or control their
cross terms.
-/

namespace RHTower

noncomputable section

/-- The literal depth square preserves summability of any cubic-weighted source energy, with
the exact factor `1 / 8`. -/
theorem summable_routePPrimitiveDepthSquare_cubicWeightedEnergy
    (f : Nat.Primes × ℕ → ℝ)
    (hf : Summable (fun pe =>
      xiGammaEulerPrimitiveCubicLogMomentWeight pe * f pe ^ 2)) :
    Summable (fun pe =>
      xiGammaEulerPrimitiveCubicLogMomentWeight (routePPrimitiveDepthSquare pe) *
        (routePPrimitiveDepthSquareModularGain pe * f pe) ^ 2) := by
  apply (hf.div_const 8).congr
  intro pe
  calc
    (xiGammaEulerPrimitiveCubicLogMomentWeight pe * f pe ^ 2) / 8 =
        (xiGammaEulerPrimitiveCubicLogMomentWeight (routePPrimitiveDepthSquare pe) *
          routePPrimitiveDepthSquareModularGain pe ^ 2) * f pe ^ 2 := by
      rw [routePPrimitiveDepthSquare_cubicWeight_modularGain_sq]
      ring
    _ = xiGammaEulerPrimitiveCubicLogMomentWeight (routePPrimitiveDepthSquare pe) *
        (routePPrimitiveDepthSquareModularGain pe * f pe) ^ 2 := by
      ring

/-- The total cubic energy of a summable source is exactly divided by eight under literal
depth-square transport. -/
theorem tsum_routePPrimitiveDepthSquare_cubicWeightedEnergy
    (f : Nat.Primes × ℕ → ℝ) :
    ∑' pe,
      xiGammaEulerPrimitiveCubicLogMomentWeight (routePPrimitiveDepthSquare pe) *
        (routePPrimitiveDepthSquareModularGain pe * f pe) ^ 2 =
      (∑' pe, xiGammaEulerPrimitiveCubicLogMomentWeight pe * f pe ^ 2) / 8 := by
  rw [div_eq_mul_inv, ← tsum_mul_right]
  apply tsum_congr
  intro pe
  calc
    xiGammaEulerPrimitiveCubicLogMomentWeight (routePPrimitiveDepthSquare pe) *
        (routePPrimitiveDepthSquareModularGain pe * f pe) ^ 2 =
        (xiGammaEulerPrimitiveCubicLogMomentWeight pe * f pe ^ 2) / 8 := by
      calc
        xiGammaEulerPrimitiveCubicLogMomentWeight (routePPrimitiveDepthSquare pe) *
            (routePPrimitiveDepthSquareModularGain pe * f pe) ^ 2 =
            (xiGammaEulerPrimitiveCubicLogMomentWeight (routePPrimitiveDepthSquare pe) *
              routePPrimitiveDepthSquareModularGain pe ^ 2) * f pe ^ 2 := by
                ring
        _ = (xiGammaEulerPrimitiveCubicLogMomentWeight pe * f pe ^ 2) / 8 := by
          rw [routePPrimitiveDepthSquare_cubicWeight_modularGain_sq]
          ring
    _ = (xiGammaEulerPrimitiveCubicLogMomentWeight pe * f pe ^ 2) * (8 : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]

end

end RHTower
