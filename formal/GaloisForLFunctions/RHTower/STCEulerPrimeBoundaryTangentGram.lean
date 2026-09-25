import GaloisForLFunctions.RHTower.PrimeLogPowZetaAbelPole

/-!
# Euler prime boundary tangent Gram law

The depth-zero primitive Gamma--Euler source has squared amplitude
`(log p)^2 p^(-1-u)`. The graded prime Abel-pole theorem already proves
its critical mass law. This leaf identifies the two-parameter tangent
Gram kernel obtained by scaling source regulators together.
-/

open Filter Set Topology
namespace RHTower

/-- The two-regulator tangent Gram of the critical prime source is
`4/(a+b)^2`, the Gram of `exp(-a*t/2)` and `exp(-b*t/2)` in `L²(t dt)`. -/
theorem tendsto_stcEulerPrimeBoundaryTangentGram {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun v : ℝ => v ^ (2 : ℕ) * gradedPrimeLogZeta 1 (((a + b) / 2) * v))
      (nhdsWithin 0 (Ioi 0)) (nhds (4 / (a + b) ^ (2 : ℕ))) := by
  let c : ℝ := (a + b) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hmap : Tendsto (fun v : ℝ => c * v) (nhdsWithin 0 (Ioi 0))
      (nhdsWithin 0 (Ioi 0)) := by
    have hId : Tendsto (fun v : ℝ => v) (nhdsWithin 0 (Ioi 0))
        (nhdsWithin 0 (Ioi 0)) := tendsto_id
    simpa using (Filter.TendstoNhdsWithinIoi.const_mul hc hId)
  have hbase := (tendsto_gradedPrimeLogZeta 1).comp hmap
  have hscaled := hbase.const_mul (c⁻¹ ^ (2 : ℕ))
  have hfun : (fun v : ℝ => c⁻¹ ^ (2 : ℕ) *
      ((c * v) ^ (2 : ℕ) * gradedPrimeLogZeta 1 (c * v))) =
      (fun v : ℝ => v ^ (2 : ℕ) * gradedPrimeLogZeta 1 (c * v)) := by
    funext v
    field_simp
  change Tendsto (fun v : ℝ => c⁻¹ ^ (2 : ℕ) *
      ((c * v) ^ (2 : ℕ) * gradedPrimeLogZeta 1 (c * v)))
      (nhdsWithin 0 (Ioi 0)) (nhds (c⁻¹ ^ (2 : ℕ) * (Nat.factorial 1 : ℝ))) at hscaled
  rw [hfun] at hscaled
  have htarget : c⁻¹ ^ (2 : ℕ) * (Nat.factorial 1 : ℝ) =
      4 / (a + b) ^ (2 : ℕ) := by
    simp only [Nat.factorial_one, Nat.cast_one, mul_one]
    dsimp [c]
    field_simp
    ring
  simpa only [htarget, c] using hscaled

end RHTower
