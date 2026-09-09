import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAHellingerCoordinates

/-!
A common positive refresh contracts Hellinger square. The public statement uses
only real scalar and array data; positivity is supplied internally by squares.
This provides the missing geometric step for the critical Gibbs Markov refresh.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem sqrt_common_shift_contraction {c q u v : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (Real.sqrt (c + q * u) - Real.sqrt (c + q * v)) ^ 2 ≤
      q * (Real.sqrt u - Real.sqrt v) ^ 2 := by
  let U := Real.sqrt (c + q * u)
  let V := Real.sqrt (c + q * v)
  let x := Real.sqrt u
  let y := Real.sqrt v
  have hU : U ^ 2 = c + q * u := Real.sq_sqrt (add_nonneg hc (mul_nonneg hq hu))
  have hV : V ^ 2 = c + q * v := Real.sq_sqrt (add_nonneg hc (mul_nonneg hq hv))
  have hx : x ^ 2 = u := Real.sq_sqrt hu
  have hy : y ^ 2 = v := Real.sq_sqrt hv
  have hxy : 0 ≤ c + q * x * y :=
    add_nonneg hc (mul_nonneg (mul_nonneg hq (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hUV : 0 ≤ U * V := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hid : (U * V) ^ 2 - (c + q * x * y) ^ 2 = c * q * (x - y) ^ 2 := by
    rw [mul_pow, hU, hV]
    calc
      _ = (c + q * x ^ 2) * (c + q * y ^ 2) - (c + q * x * y) ^ 2 := by rw [hx, hy]
      _ = _ := by ring
  have hgap : 0 ≤ c * q * (x - y) ^ 2 := mul_nonneg (mul_nonneg hc hq) (sq_nonneg _)
  have hs : (c + q * x * y) ^ 2 ≤ (U * V) ^ 2 := by linarith
  have hp : c + q * x * y ≤ U * V := (sq_le_sq₀ hxy hUV).mp hs
  change (U - V) ^ 2 ≤ q * (x - y) ^ 2
  rw [sub_sq, sub_sq, hU, hV, hx, hy]
  nlinarith

/-- Any common squared background contracts Hellinger square by the squared amplitude scale. -/
theorem egbFixedChargeAHellinger_common_refresh
    (n : ℕ) (q : ℝ) (c u v : Fin n → ℝ) :
    finitePacketHellinger (fun i => c i ^ 2 + q ^ 2 * u i ^ 2)
      (fun i => c i ^ 2 + q ^ 2 * v i ^ 2) ^ 2 ≤
      q ^ 2 * finitePacketHellinger (fun i => u i ^ 2) (fun i => v i ^ 2) ^ 2 := by
  rw [egbFixedChargeAHellinger_coordinate_square, egbFixedChargeAHellinger_coordinate_square,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact sqrt_common_shift_contraction (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)

end

end GaloisForLFunctions.HTGeometry
