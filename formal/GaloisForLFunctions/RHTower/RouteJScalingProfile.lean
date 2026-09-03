import GaloisForLFunctions.RHTower.RouteJScalingProfileLimits

/-!
# The Route J scaling profile `Φ` as a Lean theorem

For scaling data `p_j → ∞`, `2k_j/p_j → X > 0`, the first-order response of the Route J four-radius
residual to the Euler mode `cos(s log p_j)` converges:

`residualJetOf (cosineModeDeterminantJet (log p_j)) k_j → Φ(X) = 4√(2/π) [√X cos 4X − 8 X^{3/2} sin 4X]`.

The proof assembles the exact first-difference form of the residual, the Mehler–Heine limits of the
hypergeometric sums, the Wallis limit of the central binomial coefficient, and elementary limits of
the rational prefactors.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

namespace RouteJProfile

open ScaledHypergeometric CosineModeResponse

/-- The Route J profile `Φ(X) = 4√(2/π)(√X cos 4X − 8 X^{3/2} sin 4X)`. -/
noncomputable def profile (X : ℝ) : ℝ :=
  4 * Real.sqrt (2 / Real.pi) *
    (Real.sqrt X * Real.cos (4 * X) - 8 * (X * Real.sqrt X) * Real.sin (4 * X))

namespace ScalingData

variable (D : ScalingData)

local notation "sr" => semilocalArchimedeanJacobiCoefficient

/-- `δ_j = log p_j`. -/
noncomputable def δ (j : ℕ) : ℝ := Real.log (D.p j)

/-! ## The explicit residual -/

theorem residual_explicit (j : ℕ) :
    residualJetOf (cosineModeDeterminantJet (D.δ j)) (D.k j) =
      Real.cosh (D.δ j) ^ (-(1 / 2 : ℝ)) * (1 - sq (D.δ j)) *
        (-(sr (2 * D.k j) * sr (2 * D.k j + 1) * cb (2 * D.k j) * (8 * (D.k j : ℝ) + 5) /
            (4 * (2 * (D.k j : ℝ) + 1) * (2 * (D.k j : ℝ) + 2))) *
          (Hh (D.δ j) (2 * D.k j) +
            (4 * (D.k j : ℝ) + 1) * (8 * (D.k j : ℝ) + 7) * (sq (D.δ j) * Kh (D.δ j) (2 * D.k j))) +
        2 * (cb (2 * D.k j + 1) * (4 * (D.k j : ℝ) + 3) * (8 * (D.k j : ℝ) + 9) /
            (8 * (2 * (D.k j : ℝ) + 2))) *
          (3 * Hh (D.δ j) (2 * D.k j + 1) -
            (4 * (D.k j : ℝ) + 5) * (8 * (D.k j : ℝ) + 11) * (sq (D.δ j) * Kh (D.δ j) (2 * D.k j + 1))) -
        sr (2 * D.k j + 2) * sr (2 * D.k j + 3) * cb (2 * D.k j + 2) * (8 * (D.k j : ℝ) + 13) /
            (4 * (2 * (D.k j : ℝ) + 3) * (2 * (D.k j : ℝ) + 4)) *
          (Hh (D.δ j) (2 * D.k j + 2) +
            (4 * (D.k j : ℝ) + 5) * (8 * (D.k j : ℝ) + 15) * (sq (D.δ j) * Kh (D.δ j) (2 * D.k j + 2)))) := by
  have h1 := Q_succ_sub (D.δ j) (2 * D.k j)
  have h2 := rsq_Q_succ_sub (D.δ j) (2 * D.k j + 1)
  have h3 := Q_succ_sub (D.δ j) (2 * D.k j + 2)
  rw [show 2 * D.k j + 1 + 1 = 2 * D.k j + 2 from rfl] at h2
  rw [show 2 * D.k j + 2 + 1 = 2 * D.k j + 3 from rfl] at h3
  rw [residualJetOf_cosineMode_eq, h1, h2, h3]
  push_cast
  ring

/-! ## The normalization `N_j = (cosh δ_j)^{-1/2} C_{2k_j} (2k_j)` -/

theorem tendsto_normalization :
    Tendsto (fun j => Real.cosh (D.δ j) ^ (-(1 / 2 : ℝ)) * cb (2 * D.k j) * (2 * (D.k j : ℝ))) atTop
      (𝓝 (Real.sqrt 2 * (1 / Real.sqrt Real.pi) * Real.sqrt D.X)) := by
  have h := (D.tendsto_cosh_rpow_mul_sqrt.mul (D.tendsto_sqrt_mul_cb 0)).mul D.tendsto_sqrt_ratio
  refine h.congr' ?_
  filter_upwards [D.eventually_p_pos, D.eventually_k_pos] with j hp hk
  simp only [Nat.cast_mul, Nat.cast_ofNat, add_zero]
  have hsp : Real.sqrt (D.p j) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hk2 : (0 : ℝ) ≤ 2 * (D.k j : ℝ) := by positivity
  unfold δ
  field_simp
  rw [Real.sq_sqrt hk2]

/-! ## Rational prefactors -/

theorem tendsto_rat1 :
    Tendsto (fun j => 2 * (D.k j : ℝ) * (8 * (D.k j : ℝ) + 5) /
      (4 * (2 * (D.k j : ℝ) + 1) * (2 * (D.k j : ℝ) + 2))) atTop (𝓝 1) := by
  have he := D.tendsto_k_inv
  have hlim : Tendsto (fun j => 2 * (8 + 5 * (D.k j : ℝ)⁻¹) /
      (4 * (2 + (D.k j : ℝ)⁻¹) * (2 + 2 * (D.k j : ℝ)⁻¹))) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (2 : ℝ))).mul
      ((tendsto_const_nhds (x := (8 : ℝ))).add (he.const_mul 5))).div
      (((tendsto_const_nhds (x := (4 : ℝ))).mul ((tendsto_const_nhds (x := (2 : ℝ))).add he)).mul
        ((tendsto_const_nhds (x := (2 : ℝ))).add (he.const_mul 2))) (by norm_num)
    rw [show (fun j => 2 * (8 + 5 * (D.k j : ℝ)⁻¹) /
        (4 * (2 + (D.k j : ℝ)⁻¹) * (2 + 2 * (D.k j : ℝ)⁻¹))) =
        (fun j => 2 * (8 + 5 * (D.k j : ℝ)⁻¹)) /
          (fun j => 4 * (2 + (D.k j : ℝ)⁻¹) * (2 + 2 * (D.k j : ℝ)⁻¹)) from rfl]
    convert this using 2
    norm_num
  refine hlim.congr' ?_
  filter_upwards [D.eventually_k_pos] with j hk
  have hk0 : (D.k j : ℝ) ≠ 0 := hk.ne'
  field_simp
  try ring

theorem tendsto_rat2 :
    Tendsto (fun j => (4 * (D.k j : ℝ) + 3) * (8 * (D.k j : ℝ) + 9) /
      (8 * (2 * (D.k j : ℝ) + 2) * (2 * (D.k j : ℝ)))) atTop (𝓝 1) := by
  have he := D.tendsto_k_inv
  have hlim : Tendsto (fun j => (4 + 3 * (D.k j : ℝ)⁻¹) * (8 + 9 * (D.k j : ℝ)⁻¹) /
      (8 * (2 + 2 * (D.k j : ℝ)⁻¹) * 2)) atTop (𝓝 1) := by
    have := (((tendsto_const_nhds (x := (4 : ℝ))).add (he.const_mul 3)).mul
      ((tendsto_const_nhds (x := (8 : ℝ))).add (he.const_mul 9))).div
      ((((tendsto_const_nhds (x := (8 : ℝ))).mul ((tendsto_const_nhds (x := (2 : ℝ))).add (he.const_mul 2))).mul
        (tendsto_const_nhds (x := (2 : ℝ))))) (by norm_num)
    rw [show (fun j => (4 + 3 * (D.k j : ℝ)⁻¹) * (8 + 9 * (D.k j : ℝ)⁻¹) /
        (8 * (2 + 2 * (D.k j : ℝ)⁻¹) * 2)) =
        (fun j => (4 + 3 * (D.k j : ℝ)⁻¹) * (8 + 9 * (D.k j : ℝ)⁻¹)) /
          (fun j => 8 * (2 + 2 * (D.k j : ℝ)⁻¹) * 2) from rfl]
    convert this using 2
    norm_num
  refine hlim.congr' ?_
  filter_upwards [D.eventually_k_pos] with j hk
  have hk0 : (D.k j : ℝ) ≠ 0 := hk.ne'
  field_simp
  try ring

theorem tendsto_rat3 :
    Tendsto (fun j => 2 * (D.k j : ℝ) * (8 * (D.k j : ℝ) + 13) /
      (4 * (2 * (D.k j : ℝ) + 3) * (2 * (D.k j : ℝ) + 4))) atTop (𝓝 1) := by
  have he := D.tendsto_k_inv
  have hlim : Tendsto (fun j => 2 * (8 + 13 * (D.k j : ℝ)⁻¹) /
      (4 * (2 + 3 * (D.k j : ℝ)⁻¹) * (2 + 4 * (D.k j : ℝ)⁻¹))) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (2 : ℝ))).mul
      ((tendsto_const_nhds (x := (8 : ℝ))).add (he.const_mul 13))).div
      (((tendsto_const_nhds (x := (4 : ℝ))).mul ((tendsto_const_nhds (x := (2 : ℝ))).add (he.const_mul 3))).mul
        ((tendsto_const_nhds (x := (2 : ℝ))).add (he.const_mul 4))) (by norm_num)
    rw [show (fun j => 2 * (8 + 13 * (D.k j : ℝ)⁻¹) /
        (4 * (2 + 3 * (D.k j : ℝ)⁻¹) * (2 + 4 * (D.k j : ℝ)⁻¹))) =
        (fun j => 2 * (8 + 13 * (D.k j : ℝ)⁻¹)) /
          (fun j => 4 * (2 + 3 * (D.k j : ℝ)⁻¹) * (2 + 4 * (D.k j : ℝ)⁻¹)) from rfl]
    convert this using 2
    norm_num
  refine hlim.congr' ?_
  filter_upwards [D.eventually_k_pos] with j hk
  have hk0 : (D.k j : ℝ) ≠ 0 := hk.ne'
  field_simp
  try ring

/-- `C_{2k+1}/C_{2k} → 1`. -/
theorem tendsto_cb_ratio_one :
    Tendsto (fun j => cb (2 * D.k j + 1) / cb (2 * D.k j)) atTop (𝓝 1) := by
  have he := D.tendsto_k_inv
  have hlim : Tendsto (fun j => (4 + (D.k j : ℝ)⁻¹) / (4 + 2 * (D.k j : ℝ)⁻¹)) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (4 : ℝ))).add he).div
      ((tendsto_const_nhds (x := (4 : ℝ))).add (he.const_mul 2)) (by norm_num)
    rw [show (fun j => (4 + (D.k j : ℝ)⁻¹) / (4 + 2 * (D.k j : ℝ)⁻¹)) =
        (fun j => 4 + (D.k j : ℝ)⁻¹) / (fun j => 4 + 2 * (D.k j : ℝ)⁻¹) from rfl]
    convert this using 2
    norm_num
  refine hlim.congr' ?_
  filter_upwards [D.eventually_k_pos] with j hk
  have hk0 : (D.k j : ℝ) ≠ 0 := hk.ne'
  have hc := (cb_pos (2 * D.k j)).ne'
  rw [cb_succ]
  push_cast
  field_simp
  ring

/-- `C_{2k+2}/C_{2k} → 1`. -/
theorem tendsto_cb_ratio_two :
    Tendsto (fun j => cb (2 * D.k j + 2) / cb (2 * D.k j)) atTop (𝓝 1) := by
  have he := D.tendsto_k_inv
  have hlim : Tendsto (fun j => (4 + (D.k j : ℝ)⁻¹) / (4 + 2 * (D.k j : ℝ)⁻¹) *
      ((4 + 3 * (D.k j : ℝ)⁻¹) / (4 + 4 * (D.k j : ℝ)⁻¹))) atTop (𝓝 1) := by
    have h1 := ((tendsto_const_nhds (x := (4 : ℝ))).add he).div
      ((tendsto_const_nhds (x := (4 : ℝ))).add (he.const_mul 2)) (by norm_num)
    have h2 := ((tendsto_const_nhds (x := (4 : ℝ))).add (he.const_mul 3)).div
      ((tendsto_const_nhds (x := (4 : ℝ))).add (he.const_mul 4)) (by norm_num)
    have := h1.mul h2
    rw [show (fun j => (4 + (D.k j : ℝ)⁻¹) / (4 + 2 * (D.k j : ℝ)⁻¹) *
        ((4 + 3 * (D.k j : ℝ)⁻¹) / (4 + 4 * (D.k j : ℝ)⁻¹))) =
        (fun j => ((fun j => 4 + (D.k j : ℝ)⁻¹) / (fun j => 4 + 2 * (D.k j : ℝ)⁻¹)) j *
          ((fun j => 4 + 3 * (D.k j : ℝ)⁻¹) / (fun j => 4 + 4 * (D.k j : ℝ)⁻¹)) j) from rfl]
    convert this using 2
    norm_num
  refine hlim.congr' ?_
  filter_upwards [D.eventually_k_pos] with j hk
  have hk0 : (D.k j : ℝ) ≠ 0 := hk.ne'
  have hc := (cb_pos (2 * D.k j)).ne'
  rw [show 2 * D.k j + 2 = 2 * D.k j + 1 + 1 by ring, cb_succ, cb_succ]
  push_cast
  field_simp
  ring

/-! ## The hypergeometric brackets -/

theorem tendsto_bracket1 :
    Tendsto (fun j => Hh (D.δ j) (2 * D.k j) +
      (4 * (D.k j : ℝ) + 1) * (8 * (D.k j : ℝ) + 7) * (sq (D.δ j) * Kh (D.δ j) (2 * D.k j))) atTop
      (𝓝 (Real.cos (4 * D.X) + 8 * D.X * Real.sin (4 * D.X))) := by
  have hH := D.tendsto_Hh 0
  have hK := D.tendsto_Kh 0
  have h1 := D.tendsto_affine_mul_σ 4 1
  have h2 := D.tendsto_affine_mul_σ 8 7
  simp only [add_zero] at hH hK
  have h := hH.add ((h1.mul h2).mul hK)
  have hX := D.hX
  have hval : Real.cos (4 * D.X) + 4 * D.X * (8 * D.X) * (Real.sin (4 * D.X) / (4 * D.X)) =
      Real.cos (4 * D.X) + 8 * D.X * Real.sin (4 * D.X) := by
    field_simp
    try ring
  rw [hval] at h
  refine h.congr' (Eventually.of_forall fun j => ?_)
  simp only [δ, sq_log_eq]
  ring

theorem tendsto_bracket2 :
    Tendsto (fun j => 3 * Hh (D.δ j) (2 * D.k j + 1) -
      (4 * (D.k j : ℝ) + 5) * (8 * (D.k j : ℝ) + 11) * (sq (D.δ j) * Kh (D.δ j) (2 * D.k j + 1))) atTop
      (𝓝 (3 * Real.cos (4 * D.X) - 8 * D.X * Real.sin (4 * D.X))) := by
  have hH := D.tendsto_Hh 1
  have hK := D.tendsto_Kh 1
  have h1 := D.tendsto_affine_mul_σ 4 5
  have h2 := D.tendsto_affine_mul_σ 8 11
  have h := (hH.const_mul 3).sub ((h1.mul h2).mul hK)
  have hX := D.hX
  have hval : 3 * Real.cos (4 * D.X) - 4 * D.X * (8 * D.X) * (Real.sin (4 * D.X) / (4 * D.X)) =
      3 * Real.cos (4 * D.X) - 8 * D.X * Real.sin (4 * D.X) := by
    field_simp
    try ring
  rw [hval] at h
  refine h.congr' (Eventually.of_forall fun j => ?_)
  simp only [δ, sq_log_eq]
  ring

theorem tendsto_bracket3 :
    Tendsto (fun j => Hh (D.δ j) (2 * D.k j + 2) +
      (4 * (D.k j : ℝ) + 5) * (8 * (D.k j : ℝ) + 15) * (sq (D.δ j) * Kh (D.δ j) (2 * D.k j + 2))) atTop
      (𝓝 (Real.cos (4 * D.X) + 8 * D.X * Real.sin (4 * D.X))) := by
  have hH := D.tendsto_Hh 2
  have hK := D.tendsto_Kh 2
  have h1 := D.tendsto_affine_mul_σ 4 5
  have h2 := D.tendsto_affine_mul_σ 8 15
  have h := hH.add ((h1.mul h2).mul hK)
  have hX := D.hX
  have hval : Real.cos (4 * D.X) + 4 * D.X * (8 * D.X) * (Real.sin (4 * D.X) / (4 * D.X)) =
      Real.cos (4 * D.X) + 8 * D.X * Real.sin (4 * D.X) := by
    field_simp
    try ring
  rw [hval] at h
  refine h.congr' (Eventually.of_forall fun j => ?_)
  simp only [δ, sq_log_eq]
  ring

/-! ## The assembly -/

/-- The residual as `N_j (1 − x_j) [−ρ₁ B₁ + 2 q₁ rat₂ B₂ − q₂ ρ₃ B₃]`. -/
theorem residual_normalized (j : ℕ) (hk : 0 < (D.k j : ℝ)) :
    residualJetOf (cosineModeDeterminantJet (D.δ j)) (D.k j) =
      (Real.cosh (D.δ j) ^ (-(1 / 2 : ℝ)) * cb (2 * D.k j) * (2 * (D.k j : ℝ))) * (1 - sq (D.δ j)) *
        (-((sr (2 * D.k j) / (2 * (D.k j : ℝ))) * (sr (2 * D.k j + 1) / (2 * (D.k j : ℝ))) *
            (2 * (D.k j : ℝ) * (8 * (D.k j : ℝ) + 5) /
              (4 * (2 * (D.k j : ℝ) + 1) * (2 * (D.k j : ℝ) + 2)))) *
          (Hh (D.δ j) (2 * D.k j) +
            (4 * (D.k j : ℝ) + 1) * (8 * (D.k j : ℝ) + 7) * (sq (D.δ j) * Kh (D.δ j) (2 * D.k j))) +
        2 * (cb (2 * D.k j + 1) / cb (2 * D.k j)) *
          ((4 * (D.k j : ℝ) + 3) * (8 * (D.k j : ℝ) + 9) /
            (8 * (2 * (D.k j : ℝ) + 2) * (2 * (D.k j : ℝ)))) *
          (3 * Hh (D.δ j) (2 * D.k j + 1) -
            (4 * (D.k j : ℝ) + 5) * (8 * (D.k j : ℝ) + 11) * (sq (D.δ j) * Kh (D.δ j) (2 * D.k j + 1))) -
        (cb (2 * D.k j + 2) / cb (2 * D.k j)) *
          ((sr (2 * D.k j + 2) / (2 * (D.k j : ℝ))) * (sr (2 * D.k j + 3) / (2 * (D.k j : ℝ))) *
            (2 * (D.k j : ℝ) * (8 * (D.k j : ℝ) + 13) /
              (4 * (2 * (D.k j : ℝ) + 3) * (2 * (D.k j : ℝ) + 4)))) *
          (Hh (D.δ j) (2 * D.k j + 2) +
            (4 * (D.k j : ℝ) + 5) * (8 * (D.k j : ℝ) + 15) * (sq (D.δ j) * Kh (D.δ j) (2 * D.k j + 2)))) := by
  rw [D.residual_explicit j]
  have hk0 : (D.k j : ℝ) ≠ 0 := hk.ne'
  have hc := (cb_pos (2 * D.k j)).ne'
  field_simp
  try ring

/-- **The Route J scaling profile.**  Along `p_j → ∞`, `2k_j / p_j → X > 0`, the first-order response
of the four-radius residual to the Euler mode `cos(s log p_j)` converges to
`Φ(X) = 4√(2/π)[√X cos 4X − 8 X^{3/2} sin 4X]`. -/
theorem tendsto_residual_profile :
    Tendsto (fun j => residualJetOf (cosineModeDeterminantJet (D.δ j)) (D.k j)) atTop
      (𝓝 (profile D.X)) := by
  have hN := D.tendsto_normalization
  have hx := D.tendsto_one_sub_sq
  have hr0 := D.tendsto_r_div 0
  have hr1 := D.tendsto_r_div 1
  have hr2 := D.tendsto_r_div 2
  have hr3 := D.tendsto_r_div 3
  simp only [add_zero] at hr0
  have hB1 := D.tendsto_bracket1
  have hB2 := D.tendsto_bracket2
  have hB3 := D.tendsto_bracket3
  have hq1 := D.tendsto_cb_ratio_one
  have hq2 := D.tendsto_cb_ratio_two
  have hrat1 := D.tendsto_rat1
  have hrat2 := D.tendsto_rat2
  have hrat3 := D.tendsto_rat3
  have h := (hN.mul hx).mul
    ((((((hr0.mul hr1).mul hrat1).neg).mul hB1).add
      (((tendsto_const_nhds (x := (2 : ℝ))).mul hq1).mul hrat2 |>.mul hB2)).sub
      ((hq2.mul ((hr2.mul hr3).mul hrat3)).mul hB3))
  have hval : Real.sqrt 2 * (1 / Real.sqrt Real.pi) * Real.sqrt D.X * 1 *
      (-(1 * 1 * 1) * (Real.cos (4 * D.X) + 8 * D.X * Real.sin (4 * D.X)) +
        2 * 1 * 1 * (3 * Real.cos (4 * D.X) - 8 * D.X * Real.sin (4 * D.X)) -
        1 * (1 * 1 * 1) * (Real.cos (4 * D.X) + 8 * D.X * Real.sin (4 * D.X))) = profile D.X := by
    unfold profile
    have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    rw [Real.sqrt_div' 2 Real.pi_pos.le]
    field_simp
    ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [D.eventually_k_pos] with j hk
  rw [D.residual_normalized j hk]
  simp only [δ]
  try ring

end ScalingData

end RouteJProfile

end RHTower
