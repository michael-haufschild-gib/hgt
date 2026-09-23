import GaloisForLFunctions.RHTower.RouteJScalingProfile

/-!
# The unperturbed residual tends to one, and the relative deviation converges to `Φ`

The archimedean four-radius residual `R_k(0) = r_{2k} r_{2k+1} − r_{2k+1}² − r_{2k+2}² + r_{2k+2} r_{2k+3}`
with `r_n² = (n+½)(n+1)` equals `g(M) + g(M') + ½` with `g(M) = √(M(M+½)) − M → 1/4`,
`M = 4k²+5k+1`, `M' = 4k²+13k+10`; hence `R_k(0) → 1`, and the relative first-order deviation
`J_k / R_k(0)` (the quantity computed numerically in the Route J report) converges to `Φ(X)`.
-/

open Filter Topology

namespace RHTower

namespace RouteJProfile

open ScaledHypergeometric CosineModeResponse

local notation "sr" => semilocalArchimedeanJacobiCoefficient

/-- The unperturbed residual `R_k(0)`. -/
noncomputable def residualZero (k : ℕ) : ℝ :=
  sr (2 * k) * sr (2 * k + 1) - sr (2 * k + 1) ^ (2 : ℕ) - sr (2 * k + 2) ^ (2 : ℕ) + sr (2 * k + 2) * sr (2 * k + 3)

/-- `g(M) = √(M(M+½)) − M`. -/
noncomputable def sqrtDefect (M : ℝ) : ℝ := Real.sqrt (M * (M + 1 / 2)) - M

theorem sqrtDefect_eq {M : ℝ} (hM : 0 < M) :
    sqrtDefect M = (1 / 2) / (Real.sqrt (1 + 1 / (2 * M)) + 1) := by
  unfold sqrtDefect
  set s := Real.sqrt (1 + 1 / (2 * M)) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ (2 : ℕ) = 1 + 1 / (2 * M) := Real.sq_sqrt (by positivity)
  have hMs : M * (M + 1 / 2) = (M * s) ^ (2 : ℕ) := by
    rw [mul_pow, hs2]
    field_simp
    try ring
  rw [hMs, Real.sqrt_sq (by positivity)]
  have h1 : 0 < s + 1 := by positivity
  rw [eq_div_iff h1.ne']
  have : (M * s - M) * (s + 1) = M * (s ^ (2 : ℕ) - 1) := by ring
  rw [this, hs2]
  field_simp
  try ring

theorem tendsto_sqrtDefect : Tendsto sqrtDefect atTop (𝓝 (1 / 4)) := by
  have h1 : Tendsto (fun M : ℝ => 1 / (2 * M)) atTop (𝓝 0) := by
    have := (tendsto_id.const_mul_atTop (r := (2 : ℝ)) (by norm_num)).inv_tendsto_atTop
    refine this.congr' (Eventually.of_forall fun M => ?_)
    simp [one_div]
  have h2 : Tendsto (fun M : ℝ => (1 / 2) / (Real.sqrt (1 + 1 / (2 * M)) + 1)) atTop (𝓝 (1 / 4)) := by
    have := (tendsto_const_nhds (x := (1 / 2 : ℝ))).div
      ((((tendsto_const_nhds (x := (1 : ℝ))).add h1).sqrt).add (tendsto_const_nhds (x := (1 : ℝ))))
      (by norm_num)
    rw [show (fun M : ℝ => (1 / 2) / (Real.sqrt (1 + 1 / (2 * M)) + 1)) =
      (fun _ => (1 / 2 : ℝ)) / (fun M => Real.sqrt (1 + 1 / (2 * M)) + 1) from rfl]
    convert this using 2
    norm_num
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  rw [sqrtDefect_eq hM]

theorem residualZero_eq (k : ℕ) :
    residualZero k = sqrtDefect (4 * (k : ℝ) ^ (2 : ℕ) + 5 * k + 1) +
      sqrtDefect (4 * (k : ℝ) ^ (2 : ℕ) + 13 * k + 10) + 1 / 2 := by
  unfold residualZero sqrtDefect
  have h0 := semilocalArchimedeanJacobiCoefficient_sq (2 * k)
  have h1 := semilocalArchimedeanJacobiCoefficient_sq (2 * k + 1)
  have h2 := semilocalArchimedeanJacobiCoefficient_sq (2 * k + 2)
  have h3 := semilocalArchimedeanJacobiCoefficient_sq (2 * k + 3)
  have hp : ∀ n, 0 < sr n := semilocalArchimedeanJacobiCoefficient_pos
  have hprod01 : sr (2 * k) * sr (2 * k + 1) =
      Real.sqrt ((4 * (k : ℝ) ^ (2 : ℕ) + 5 * k + 1) * (4 * (k : ℝ) ^ (2 : ℕ) + 5 * k + 1 + 1 / 2)) := by
    rw [← Real.sqrt_sq (mul_pos (hp _) (hp _)).le, mul_pow, h0, h1]
    congr 1
    push_cast
    ring
  have hprod23 : sr (2 * k + 2) * sr (2 * k + 3) =
      Real.sqrt ((4 * (k : ℝ) ^ (2 : ℕ) + 13 * k + 10) * (4 * (k : ℝ) ^ (2 : ℕ) + 13 * k + 10 + 1 / 2)) := by
    rw [← Real.sqrt_sq (mul_pos (hp _) (hp _)).le, mul_pow, h2, h3]
    congr 1
    push_cast
    ring
  rw [hprod01, hprod23, h1, h2]
  push_cast
  ring

/-- **The unperturbed residual tends to one.** -/
theorem tendsto_residualZero : Tendsto residualZero atTop (𝓝 1) := by
  have hM : Tendsto (fun k : ℕ => 4 * (k : ℝ) ^ (2 : ℕ) + 5 * k + 1) atTop atTop := by
    have h := tendsto_natCast_atTop_atTop (R := ℝ)
    have : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := h
    refine tendsto_atTop_mono (fun k => ?_) this
    nlinarith [sq_nonneg (k : ℝ), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hM' : Tendsto (fun k : ℕ => 4 * (k : ℝ) ^ (2 : ℕ) + 13 * k + 10) atTop atTop := by
    have : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono (fun k => ?_) this
    nlinarith [sq_nonneg (k : ℝ), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h := ((tendsto_sqrtDefect.comp hM).add (tendsto_sqrtDefect.comp hM')).add
    (tendsto_const_nhds (x := (1 / 2 : ℝ)))
  rw [show (1 / 4 : ℝ) + 1 / 4 + 1 / 2 = 1 by norm_num] at h
  refine h.congr' (Eventually.of_forall fun k => ?_)
  rw [residualZero_eq]
  rfl

namespace ScalingData

variable (D : ScalingData)

/-- **The relative first-order deviation converges to `Φ(X)`.** -/
theorem tendsto_residual_ratio_profile :
    Tendsto (fun j => residualJetOf (cosineModeDeterminantJet (D.δ j)) (D.k j) / residualZero (D.k j))
      atTop (𝓝 (profile D.X)) := by
  have h := D.tendsto_residual_profile.div (tendsto_residualZero.comp D.tendsto_k_nat) one_ne_zero
  rw [div_one] at h
  exact h

end ScalingData

end RouteJProfile

end RHTower
