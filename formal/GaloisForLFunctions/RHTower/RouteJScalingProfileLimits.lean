import GaloisForLFunctions.RHTower.RouteJResidualFirstDifferenceForm
import GaloisForLFunctions.HTGeometry.CentralBinomialWallisAsymptotic

/-!
# Elementary limits for the Route J scaling profile

Scaling data: `p_j → ∞` and `2 k_j / p_j → X > 0`.  With `δ_j = log p_j` and `σ_j = sech δ_j`:
`p_j σ_j → 2`, `(c k_j + d) σ_j → c X`, `(2k_j + a) σ_j → 2X`, the hypergeometric sums
`H_{2k_j+a} → cos 4X`, `K_{2k_j+a} → sin 4X / 4X` (Mehler–Heine mechanism), the Wallis limit
`√(2k_j+a) C_{2k_j+a} → 1/√π`, `(cosh δ_j)^{-1/2} √p_j → √2`, and the radii `r_{2k_j+a}/(2k_j) → 1`.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

namespace RouteJProfile

open ScaledHypergeometric

/-- Scaling data for the Route J profile. -/
structure ScalingData where
  p : ℕ → ℝ
  k : ℕ → ℕ
  X : ℝ
  hX : 0 < X
  hp : Tendsto p atTop atTop
  hk : Tendsto (fun j => 2 * (k j : ℝ) / p j) atTop (𝓝 X)

namespace ScalingData

variable (D : ScalingData)

/-- `σ_j = sech (log p_j)`. -/
noncomputable def σ (j : ℕ) : ℝ := 1 / Real.cosh (Real.log (D.p j))

theorem σ_nonneg (j : ℕ) : 0 ≤ D.σ j := by
  unfold σ
  have := Real.cosh_pos (Real.log (D.p j))
  positivity

theorem sq_log_eq (j : ℕ) : sq (Real.log (D.p j)) = D.σ j ^ 2 := rfl

theorem eventually_p_pos : ∀ᶠ j in atTop, 0 < D.p j := D.hp.eventually (eventually_gt_atTop 0)

theorem tendsto_p_inv : Tendsto (fun j => (D.p j)⁻¹) atTop (𝓝 0) := D.hp.inv_tendsto_atTop

/-- `p_j σ_j → 2`. -/
theorem tendsto_p_mul_σ : Tendsto (fun j => D.p j * D.σ j) atTop (𝓝 2) := by
  have h1 := D.tendsto_p_inv
  have h2 : Tendsto (fun j => 2 / (1 + (D.p j)⁻¹ * (D.p j)⁻¹)) atTop (𝓝 2) := by
    have := (tendsto_const_nhds (x := (2 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).add (h1.mul h1)) (by norm_num : (1 : ℝ) + 0 * 0 ≠ 0)
    rw [show (fun j => 2 / (1 + (D.p j)⁻¹ * (D.p j)⁻¹)) =
      (fun _ => (2 : ℝ)) / (fun j => 1 + (D.p j)⁻¹ * (D.p j)⁻¹) from rfl]
    simpa using this
  refine h2.congr' ?_
  filter_upwards [D.eventually_p_pos] with j hj
  unfold σ
  rw [Real.cosh_eq, Real.exp_log hj, Real.exp_neg, Real.exp_log hj]
  have hp0 : D.p j ≠ 0 := hj.ne'
  field_simp

theorem tendsto_σ_zero : Tendsto D.σ atTop (𝓝 0) := by
  have h := D.tendsto_p_mul_σ.mul D.tendsto_p_inv
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [D.eventually_p_pos] with j hj
  have hp0 : D.p j ≠ 0 := hj.ne'
  field_simp

/-- `k_j → ∞` (as reals). -/
theorem tendsto_k_real : Tendsto (fun j => (D.k j : ℝ)) atTop atTop := by
  have h := (D.hk.pos_mul_atTop D.hX D.hp).atTop_div_const (r := (2 : ℝ)) (by norm_num)
  refine h.congr' ?_
  filter_upwards [D.eventually_p_pos] with j hj
  have hp0 : D.p j ≠ 0 := hj.ne'
  field_simp

theorem tendsto_k_nat : Tendsto D.k atTop atTop := tendsto_natCast_atTop_iff.mp D.tendsto_k_real

theorem tendsto_n_nat (a : ℕ) : Tendsto (fun j => 2 * D.k j + a) atTop atTop :=
  tendsto_atTop_mono (fun j => by omega) D.tendsto_k_nat

theorem tendsto_k_inv : Tendsto (fun j => (D.k j : ℝ)⁻¹) atTop (𝓝 0) := D.tendsto_k_real.inv_tendsto_atTop

theorem eventually_k_pos : ∀ᶠ j in atTop, 0 < (D.k j : ℝ) := D.tendsto_k_real.eventually (eventually_gt_atTop 0)

/-- `k_j σ_j → X`. -/
theorem tendsto_k_mul_σ : Tendsto (fun j => (D.k j : ℝ) * D.σ j) atTop (𝓝 D.X) := by
  have h := (D.hk.mul D.tendsto_p_mul_σ).div_const 2
  rw [show D.X * 2 / 2 = D.X by ring] at h
  refine h.congr' ?_
  filter_upwards [D.eventually_p_pos] with j hj
  have hp0 : D.p j ≠ 0 := hj.ne'
  field_simp

/-- `(c k_j + d) σ_j → c X`. -/
theorem tendsto_affine_mul_σ (c d : ℝ) :
    Tendsto (fun j => (c * (D.k j : ℝ) + d) * D.σ j) atTop (𝓝 (c * D.X)) := by
  have h := (D.tendsto_k_mul_σ.const_mul c).add (D.tendsto_σ_zero.const_mul d)
  rw [mul_zero, add_zero] at h
  refine h.congr' (Eventually.of_forall fun j => ?_)
  ring

theorem tendsto_n_mul_σ (a : ℕ) :
    Tendsto (fun j => ((2 * D.k j + a : ℕ) : ℝ) * D.σ j) atTop (𝓝 (2 * D.X)) := by
  have h := D.tendsto_affine_mul_σ 2 a
  refine h.congr' (Eventually.of_forall fun j => ?_)
  push_cast
  ring

/-! ## Hypergeometric limits -/

theorem Hh_eq_hypSum (j : ℕ) (n : ℕ) :
    Hh (Real.log (D.p j)) n = hypSum n (3 / 2) (1 / 2) (D.σ j) := by
  unfold Hh
  rw [hypSum_eq_hypSumSq, sq_log_eq]

theorem Kh_eq_hypSum (j : ℕ) (n : ℕ) :
    Kh (Real.log (D.p j)) n = hypSum n (5 / 2) (3 / 2) (D.σ j) := by
  unfold Kh
  rw [hypSum_eq_hypSumSq, sq_log_eq]

/-- `H_{2k_j + a} → cos 4X`. -/
theorem tendsto_Hh (a : ℕ) :
    Tendsto (fun j => Hh (Real.log (D.p j)) (2 * D.k j + a)) atTop (𝓝 (Real.cos (4 * D.X))) := by
  simp_rw [D.Hh_eq_hypSum]
  have h := tendsto_hypSum (d := 3 / 2) (c := 1 / 2) (by norm_num) (by norm_num) (D.tendsto_n_nat a)
    D.σ_nonneg (D.tendsto_n_mul_σ a)
  rw [tsum_limitTerm_half, show 2 * (2 * D.X) = 4 * D.X by ring] at h
  exact h

/-- `K_{2k_j + a} → sin 4X / 4X`. -/
theorem tendsto_Kh (a : ℕ) :
    Tendsto (fun j => Kh (Real.log (D.p j)) (2 * D.k j + a)) atTop
      (𝓝 (Real.sin (4 * D.X) / (4 * D.X))) := by
  simp_rw [D.Kh_eq_hypSum]
  have h := tendsto_hypSum (d := 5 / 2) (c := 3 / 2) (by norm_num) (by norm_num) (D.tendsto_n_nat a)
    D.σ_nonneg (D.tendsto_n_mul_σ a)
  rw [tsum_limitTerm_three_half (mul_pos two_pos D.hX).ne',
    show 2 * (2 * D.X) = 4 * D.X by ring] at h
  exact h

theorem tendsto_one_sub_sq : Tendsto (fun j => 1 - sq (Real.log (D.p j))) atTop (𝓝 1) := by
  simp_rw [D.sq_log_eq]
  have h := tendsto_const_nhds (x := (1 : ℝ)) |>.sub (D.tendsto_σ_zero.pow 2)
  simpa using h

/-! ## The cosh prefactor and the Wallis factor -/

theorem cosh_rpow_eq_sqrt_σ (j : ℕ) :
    Real.cosh (Real.log (D.p j)) ^ (-(1 / 2 : ℝ)) = Real.sqrt (D.σ j) := by
  unfold σ
  have hc := Real.cosh_pos (Real.log (D.p j))
  rw [Real.rpow_neg hc.le, Real.sqrt_eq_rpow, one_div (Real.cosh (Real.log (D.p j))),
    Real.inv_rpow hc.le]

/-- `(cosh δ_j)^{-1/2} √p_j → √2`. -/
theorem tendsto_cosh_rpow_mul_sqrt :
    Tendsto (fun j => Real.cosh (Real.log (D.p j)) ^ (-(1 / 2 : ℝ)) * Real.sqrt (D.p j)) atTop
      (𝓝 (Real.sqrt 2)) := by
  simp_rw [D.cosh_rpow_eq_sqrt_σ]
  have h := D.tendsto_p_mul_σ.sqrt
  refine h.congr' ?_
  filter_upwards [D.eventually_p_pos] with j hj
  rw [Real.sqrt_mul hj.le, mul_comm]

/-- Wallis: `√(2k_j + a) · C_{2k_j + a} → 1/√π`. -/
theorem tendsto_sqrt_mul_cb (a : ℕ) :
    Tendsto (fun j => Real.sqrt ((2 * D.k j + a : ℕ) : ℝ) * cb (2 * D.k j + a)) atTop
      (𝓝 (1 / Real.sqrt Real.pi)) := by
  have h := GaloisForLFunctions.HTGeometry.tendsto_sqrtNat_mul_normalizedCentralBinom.comp
    (D.tendsto_n_nat a)
  exact h

/-! ## Geometric prefactors -/

theorem r_sq_eq (n : ℕ) :
    semilocalArchimedeanJacobiCoefficient n ^ 2 = ((n : ℝ) + 1 / 2) * ((n : ℝ) + 1) :=
  semilocalArchimedeanJacobiCoefficient_sq n

/-- `r_{2k_j + a} / (2 k_j) → 1`. -/
theorem tendsto_r_div (a : ℕ) :
    Tendsto (fun j => semilocalArchimedeanJacobiCoefficient (2 * D.k j + a) / (2 * (D.k j : ℝ)))
      atTop (𝓝 1) := by
  have he := D.tendsto_k_inv
  have hlim : Tendsto (fun j => Real.sqrt ((1 + ((a : ℝ) + 1 / 2) / 2 * (D.k j : ℝ)⁻¹) *
      (1 + ((a : ℝ) + 1) / 2 * (D.k j : ℝ)⁻¹))) atTop (𝓝 1) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).add (he.const_mul (((a : ℝ) + 1 / 2) / 2))).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add (he.const_mul (((a : ℝ) + 1) / 2)))).sqrt
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [D.eventually_k_pos] with j hj
  have hk0 : (D.k j : ℝ) ≠ 0 := hj.ne'
  unfold semilocalArchimedeanJacobiCoefficient
  rw [eq_div_iff (by positivity), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * (D.k j : ℝ)),
    ← Real.sqrt_mul (by positivity)]
  congr 1
  push_cast
  field_simp
  ring

/-- `√(2 k_j) / √p_j → √X`. -/
theorem tendsto_sqrt_ratio :
    Tendsto (fun j => Real.sqrt (2 * (D.k j : ℝ)) / Real.sqrt (D.p j)) atTop (𝓝 (Real.sqrt D.X)) := by
  have h := D.hk.sqrt
  refine h.congr' ?_
  filter_upwards [D.eventually_p_pos] with j hj
  rw [Real.sqrt_div (by positivity)]

end ScalingData

end RouteJProfile

end RHTower
