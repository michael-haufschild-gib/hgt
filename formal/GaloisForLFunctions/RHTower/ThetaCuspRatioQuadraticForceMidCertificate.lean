import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierAlgebra
/-! Strict middle-clock forcing sign by projective polynomial positivity. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

theorem mid_force_projective_neg (s t z : ℝ) (hs0 : 0≤s) (ht0 : 0≤t) (hz0 : 0≤z) :
    quadraticBoundaryCore ((2/3+(3/4)*s)/(1+s)) (9*t/(1+t))
      (b ((2/3+(3/4)*s)/(1+s))*(1+(6/5)*z)/(1+z))<0 := by
  have hs : 1+s≠0 := by positivity
  have ht : 1+t≠0 := by positivity
  have hz : 1+z≠0 := by positivity
  let d : ℝ := (1+s)^7*(1+t)^3*(1+z)^4
  have hd : 0<d := by dsimp [d]; positivity
  suffices hn : 0< -d*quadraticBoundaryCore ((2/3+(3/4)*s)/(1+s)) (9*t/(1+t))
      (b ((2/3+(3/4)*s)/(1+s))*(1+(6/5)*z)/(1+z)) by
    by_contra hn0
    have := mul_nonneg hd.le (le_of_not_gt hn0)
    nlinarith only [hn,this]
  conv_rhs =>
    unfold d quadraticBoundaryCore D A fieldH b
    field_simp [hs,ht,hz]
    ring_nf (config := {mode := .raw})
  simp only [NNRat.rawCast, Nat.rawCast]
  norm_num1
  all_goals positivity
end
end HTGeometry.ThetaCriticalBarrier

