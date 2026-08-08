import GaloisForLFunctions.RHTower.CompletedPrimeGammaMomentFarRightAsymptotic

/-!
# All-positive-order far-right asymptotic of the completed Xi source

The existing source split proves the rational and Euler legs vanish at every positive derivative
order and identifies the exact half-argument Gamma limit.  This file records the resulting theorem
without imposing parity.  Keeping the sign is essential for the reverse-Bessel reconstruction of
the full shifted-moment tower.
-/

open Complex Filter Topology LSeries

namespace RHTower

noncomputable section

/-- Every positive derivative order of `xiLogDeriv` has the exact Gamma-determined far-right
constant.  No Riemann-hypothesis assumption enters the statement or proof. -/
theorem tendsto_scaled_iteratedDeriv_xiLogDeriv_allOrder (j : ℕ) (hj : 0 < j) :
    Tendsto
      (fun x : ℝ => (x : ℂ) ^ j * iteratedDeriv j xiLogDeriv (x : ℂ))
      atTop
      (nhds (((-1 : ℂ) ^ (j + 1) * ((j - 1).factorial : ℂ)) / 2)) := by
  have hrat := tendsto_scaled_completedRationalLeg j hj
  have hgamma := tendsto_scaled_completedGammaLeg j hj
  have heuler := tendsto_scaled_completedEulerLeg j
  have hsum := (hrat.add hgamma).add heuler
  have hsum0 : Tendsto
      (fun x : ℝ =>
        (x : ℂ) ^ j *
            iteratedDeriv j
              (fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2) (x : ℂ) +
          (x : ℂ) ^ j * (1 / 2 : ℂ) ^ (j + 1) *
            iteratedDeriv j Complex.digamma ((x : ℂ) / 2) +
          (x : ℂ) ^ j *
            ((-1 : ℂ) ^ (j + 1) * LSeries (vonMangoldtLogCoeff j) (x : ℂ)))
      atTop
      (nhds (((-1 : ℂ) ^ (j + 1) * ((j - 1).factorial : ℂ)) / 2)) := by
    simpa only [zero_add, add_zero] using hsum
  have hsum' : Tendsto
      (fun x : ℝ => (x : ℂ) ^ j *
        (iteratedDeriv j
            (fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2) (x : ℂ) +
          (1 / 2 : ℂ) ^ (j + 1) * iteratedDeriv j Complex.digamma ((x : ℂ) / 2) +
          (-1 : ℂ) ^ (j + 1) * LSeries (vonMangoldtLogCoeff j) (x : ℂ)))
      atTop
      (nhds (((-1 : ℂ) ^ (j + 1) * ((j - 1).factorial : ℂ)) / 2)) := by
    convert hsum0 using 1
    funext x
    ring
  apply hsum'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [iteratedDeriv_xiLogDeriv_split j (s := (x : ℂ)) (by simpa using hx)]
  rfl

end

end RHTower
