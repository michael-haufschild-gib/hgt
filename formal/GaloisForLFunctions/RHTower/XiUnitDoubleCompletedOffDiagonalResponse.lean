import GaloisForLFunctions.RHTower.XiCompletedApertureReflectionKernel

/-!
# Completed off-diagonal lift of the unit--double response

The clocked valuation-fused response at aperture `a`, after archimedean completion, is the Xi seam
flux `a S(a)` with `S = -xi'/xi`.  Restricting the unit--double shuttle to its diagonal erases all
prime interaction and gives the support-blind coefficient `-log p/(p+1)`.

This file keeps the translation variable before that restriction.  The canonical completed lift is

`K₁₂(x,y) = 2 S(2 + i(x-y)) - S(1 + i(x-y))`.

It is Hermitian, has a constant real diagonal, and at prime-log nodes depends on the exact
logarithmic prime ratio.  These are structural properties of the new response object; no RH
estimate or identification with the joined physical response is asserted here.
-/

namespace RHTower

noncomputable section

/-- The completed unit--double response before diagonal prime-label restriction. -/
def xiUnitDoubleCompletedOffDiagonalResponseKernel (x y : ℝ) : ℂ :=
  2 * xiCompletedApertureOffDiagonalKernel (3 / 2) x y -
    xiCompletedApertureOffDiagonalKernel (1 / 2) x y

/-- Seam-flux form of the completed unit--double off-diagonal response. -/
theorem xiUnitDoubleCompletedOffDiagonalResponseKernel_eq_seamFlux
    (x y : ℝ) :
    xiUnitDoubleCompletedOffDiagonalResponseKernel x y =
      2 * seamFluxCochain
          ((2 : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I) -
        seamFluxCochain
          ((1 : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I) := by
  rw [xiUnitDoubleCompletedOffDiagonalResponseKernel,
    xiCompletedApertureOffDiagonalKernel,
    xiCompletedApertureOffDiagonalKernel]
  norm_num

/-- The completed unit--double response is Hermitian before any Gram compression. -/
theorem xiUnitDoubleCompletedOffDiagonalResponseKernel_swap
    (x y : ℝ) :
    xiUnitDoubleCompletedOffDiagonalResponseKernel y x =
      (starRingEnd ℂ) (xiUnitDoubleCompletedOffDiagonalResponseKernel x y) := by
  have hthree := xiCompletedApertureOffDiagonalKernel_swap (3 / 2) x y
  have hone := xiCompletedApertureOffDiagonalKernel_swap (1 / 2) x y
  rw [xiUnitDoubleCompletedOffDiagonalResponseKernel,
    xiUnitDoubleCompletedOffDiagonalResponseKernel]
  calc
    2 * xiCompletedApertureOffDiagonalKernel (3 / 2) y x -
          xiCompletedApertureOffDiagonalKernel (1 / 2) y x =
        2 * (starRingEnd ℂ)
              (xiCompletedApertureOffDiagonalKernel (3 / 2) x y) -
          (starRingEnd ℂ)
              (xiCompletedApertureOffDiagonalKernel (1 / 2) x y) := by
            rw [hthree, hone]
    _ = (starRingEnd ℂ)
          (2 * xiCompletedApertureOffDiagonalKernel (3 / 2) x y -
            xiCompletedApertureOffDiagonalKernel (1 / 2) x y) := by
      have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 :=
        map_ofNat (starRingEnd ℂ) 2
      rw [map_sub, map_mul]
      rw [htwo]

/-- Diagonal restriction erases the translation node and returns one fixed completed scalar. -/
theorem xiUnitDoubleCompletedOffDiagonalResponseKernel_self
    (x : ℝ) :
    xiUnitDoubleCompletedOffDiagonalResponseKernel x x =
      2 * seamFluxCochain 2 - seamFluxCochain 1 := by
  rw [xiUnitDoubleCompletedOffDiagonalResponseKernel_eq_seamFlux]
  simp

/-- The constant diagonal of the Hermitian completed response is real. -/
theorem xiUnitDoubleCompletedOffDiagonalResponseKernel_self_im
    (x : ℝ) :
    (xiUnitDoubleCompletedOffDiagonalResponseKernel x x).im = 0 := by
  have h := congrArg Complex.im
    (xiUnitDoubleCompletedOffDiagonalResponseKernel_swap x x)
  change (xiUnitDoubleCompletedOffDiagonalResponseKernel x x).im =
    -(xiUnitDoubleCompletedOffDiagonalResponseKernel x x).im at h
  linarith

/-- At actual prime-log nodes the off-diagonal response samples the completed Xi flux at the
exact logarithmic prime ratio. -/
theorem xiUnitDoubleCompletedOffDiagonalResponseKernel_primeLogs
    (p q : Nat.Primes) :
    xiUnitDoubleCompletedOffDiagonalResponseKernel
        (Real.log (p : ℝ)) (Real.log (q : ℝ)) =
      2 * seamFluxCochain
          ((2 : ℂ) +
            (Real.log ((p : ℝ) / (q : ℝ)) : ℂ) * Complex.I) -
        seamFluxCochain
          ((1 : ℂ) +
            (Real.log ((p : ℝ) / (q : ℝ)) : ℂ) * Complex.I) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast q.prop.ne_zero
  rw [xiUnitDoubleCompletedOffDiagonalResponseKernel_eq_seamFlux,
    Real.log_div hp0 hq0]

/-- Finite sampled packet of the completed unit--double response. -/
def xiUnitDoubleCompletedOffDiagonalResponseMatrix {n : ℕ}
    (node : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => xiUnitDoubleCompletedOffDiagonalResponseKernel (node i) (node j)

/-- Every finite sampled packet is pointwise Hermitian. -/
theorem xiUnitDoubleCompletedOffDiagonalResponseMatrix_swap {n : ℕ}
    (node : Fin n → ℝ) (i j : Fin n) :
    xiUnitDoubleCompletedOffDiagonalResponseMatrix node j i =
      (starRingEnd ℂ)
        (xiUnitDoubleCompletedOffDiagonalResponseMatrix node i j) := by
  exact xiUnitDoubleCompletedOffDiagonalResponseKernel_swap (node i) (node j)

end

end RHTower
