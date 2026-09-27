import GaloisForLFunctions.RHTower.STCGammaPrimeHilbertChamber

/-!
# Scalar boundary renormalization of the Gamma chamber has only the zero strong limit

Fix `g ≠ 0`, `a = |g|`, and approach the chamber wall `u = a + v`, `v ↓ 0`.  With
`x_v = b_v` and `y_v = b_{v+2a}` in `ℓ²(primes)` and `P_z = |z⟩⟨z|`,

`Q_{a+v,g} = sign(g) (P_{x_v} - P_{y_v})/2`.

The norm `‖x_v‖` diverges while `‖y_v‖ ≤ ‖b_{2a}‖`; hence `2‖Q‖/‖x_v‖² → 1`.  The unit vectors
`e_v = x_v/‖x_v‖` are weakly null, so the norm-one projections `P_{e_v}` tend strongly to zero and
`2Q/‖x_v‖² → 0` strongly with norms tending to one.  By the uniform boundedness principle every
bounded strong limit of a scalar family `c_v Q_{a+v,g}` is zero, and `Q_{a+v,g}` itself has no
bounded strong limit.
-/

open Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open GaloisForLFunctions.HTGeometry InnerProductSpace

namespace RHTower

noncomputable section

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-- The depth-zero source amplitude as an `ℓ²` vector (zero off the Hilbert range `v > 0`). -/
def stcBoundaryVec (v : ℝ) : ℓ²P :=
  if h : 0 < v then lpOfReal (stcDepthZeroAmplitude v) ((summable_stcDepthZeroAmplitude_sq_iff v).mpr h)
  else 0

theorem stcBoundaryVec_apply {v : ℝ} (hv : 0 < v) (p : Nat.Primes) :
    (stcBoundaryVec v : Nat.Primes → ℂ) p = (stcDepthZeroAmplitude v p : ℂ) := by
  simp [stcBoundaryVec, hv]

theorem norm_sq_stcBoundaryVec {v : ℝ} (hv : 0 < v) :
    ‖stcBoundaryVec v‖ ^ 2 = ∑' p : Nat.Primes, stcDepthZeroAmplitude v p ^ 2 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  refine tsum_congr fun p => ?_
  rw [stcBoundaryVec_apply hv, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem stcDepthZeroAmplitude_sq_anti {v w : ℝ} (hvw : v ≤ w) (p : Nat.Primes) :
    stcDepthZeroAmplitude w p ^ 2 ≤ stcDepthZeroAmplitude v p ^ 2 := by
  rw [stcDepthZeroAmplitude_sq, stcDepthZeroAmplitude_sq]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast p.property.one_lt.le) (by linarith)) (sq_nonneg _)

theorem norm_stcBoundaryVec_anti {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) :
    ‖stcBoundaryVec w‖ ≤ ‖stcBoundaryVec v‖ := by
  have hw : 0 < w := hv.trans_le hvw
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [norm_sq_stcBoundaryVec hv, norm_sq_stcBoundaryVec hw]
  exact Summable.tsum_le_tsum (stcDepthZeroAmplitude_sq_anti hvw)
    ((summable_stcDepthZeroAmplitude_sq_iff w).mpr hw)
    ((summable_stcDepthZeroAmplitude_sq_iff v).mpr hv)

/-- **The critical source escapes.** `‖b_v‖ → ∞` as `v ↓ 0`. -/
theorem tendsto_norm_stcBoundaryVec : Tendsto (fun v => ‖stcBoundaryVec v‖) (𝓝[>] 0) atTop := by
  rw [tendsto_atTop]
  intro M
  have hnon : ¬ Summable (fun p : Nat.Primes => stcDepthZeroAmplitude 0 p ^ 2) := by
    rw [summable_stcDepthZeroAmplitude_sq_iff]; exact lt_irrefl 0
  obtain ⟨S, hS⟩ : ∃ S : Finset Nat.Primes, M ^ 2 < ∑ p ∈ S, stcDepthZeroAmplitude 0 p ^ 2 := by
    by_contra h
    push Not at h
    exact hnon (summable_of_sum_le (fun p => sq_nonneg _) h)
  have hcont : ContinuousAt (fun v : ℝ => ∑ p ∈ S, stcDepthZeroAmplitude v p ^ 2) 0 := by
    have heq : (fun v : ℝ => ∑ p ∈ S, stcDepthZeroAmplitude v p ^ 2) =
        fun v => ∑ p ∈ S, Real.log (p : ℝ) ^ 2 * (p : ℝ) ^ (-1 - v) := by
      funext v; exact Finset.sum_congr rfl fun p _ => stcDepthZeroAmplitude_sq v p
    rw [heq]
    refine tendsto_finsetSum S fun p _ => ?_
    refine (tendsto_const_nhds).mul ?_
    have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.pos.ne'
    exact (Real.continuousAt_const_rpow hp).tendsto.comp
      ((continuous_const.sub continuous_id).tendsto 0)
  have hev : ∀ᶠ v in 𝓝[>] (0 : ℝ), M ^ 2 < ∑ p ∈ S, stcDepthZeroAmplitude v p ^ 2 :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hS)
  filter_upwards [hev, self_mem_nhdsWithin] with v hv hvpos
  have hvpos' : (0 : ℝ) < v := hvpos
  have hle : ∑ p ∈ S, stcDepthZeroAmplitude v p ^ 2 ≤ ‖stcBoundaryVec v‖ ^ 2 := by
    rw [norm_sq_stcBoundaryVec hvpos']
    exact ((summable_stcDepthZeroAmplitude_sq_iff v).mpr hvpos').sum_le_tsum S
      (fun p _ => sq_nonneg _)
  have h2 : M ^ 2 < ‖stcBoundaryVec v‖ ^ 2 := hv.trans_le hle
  by_contra hlt
  push Not at hlt
  rcases le_or_gt M 0 with hM | hM
  · linarith [norm_nonneg (stcBoundaryVec v)]
  · nlinarith [norm_nonneg (stcBoundaryVec v)]

/-- The shifted channel stays bounded: `‖b_{v+2a}‖ ≤ ‖b_{2a}‖`. -/
theorem norm_stcBoundaryVec_shift_le {a v : ℝ} (ha : 0 < a) (hv : 0 ≤ v) :
    ‖stcBoundaryVec (v + 2 * a)‖ ≤ ‖stcBoundaryVec (2 * a)‖ :=
  norm_stcBoundaryVec_anti (by positivity) (by linarith)

/-- The wall operator `sign(g) (P_{x_v} - P_{y_v})/2`. -/
def stcGammaWallOp (g v : ℝ) : ℓ²P →L[ℂ] ℓ²P :=
  ((Real.sign g / 2 : ℝ) : ℂ) • (rankOne ℂ (stcBoundaryVec v) (stcBoundaryVec v) -
    rankOne ℂ (stcBoundaryVec (v + 2 * |g|)) (stcBoundaryVec (v + 2 * |g|)))

/-- **(4)** At `u = |g| + v` the chamber operator is the wall operator. -/
theorem hasLpMatrix_stcGammaWallOp {g v : ℝ} (hg : g ≠ 0) (hv : 0 < v) :
    HasLpMatrix (stcGammaWallOp g v) (stcGammaKernel (|g| + v) g) := by
  have ha : 0 < |g| := abs_pos.mpr hg
  have hw : 0 < v + 2 * |g| := by positivity
  refine ((((hasLpMatrix_rankOne (stcBoundaryVec v) (stcBoundaryVec v)).sub
    (hasLpMatrix_rankOne (stcBoundaryVec (v + 2 * |g|)) (stcBoundaryVec (v + 2 * |g|)))).smul
      ((Real.sign g / 2 : ℝ) : ℂ))).congr fun i j => ?_
  rw [stcBoundaryVec_apply hv, stcBoundaryVec_apply hv, stcBoundaryVec_apply hw,
    stcBoundaryVec_apply hw]
  simp only [Complex.conj_ofReal, stcGammaKernel]
  rw [stcGammaKernel_two_channel_real]
  rcases lt_or_gt_of_ne hg with hneg | hpos
  · rw [Real.sign_of_neg hneg, abs_of_neg hneg,
      show -g + v - g = v + 2 * -g by ring, show -g + v + g = v by ring]
    push_cast
    ring
  · rw [Real.sign_of_pos hpos, abs_of_pos hpos,
      show g + v - g = v by ring, show g + v + g = v + 2 * g by ring]
    push_cast
    ring

private theorem abs_sign {g : ℝ} (hg : g ≠ 0) : |Real.sign g| = 1 := by
  rcases lt_or_gt_of_ne hg with h | h <;> simp [Real.sign_of_neg, Real.sign_of_pos, h]

private theorem norm_wall_bounds {g v : ℝ} (hg : g ≠ 0) :
    (‖stcBoundaryVec v‖ ^ 2 - ‖stcBoundaryVec (v + 2 * |g|)‖ ^ 2) / 2 ≤ ‖stcGammaWallOp g v‖ ∧
      ‖stcGammaWallOp g v‖ ≤ (‖stcBoundaryVec v‖ ^ 2 + ‖stcBoundaryVec (v + 2 * |g|)‖ ^ 2) / 2 := by
  have hs : ‖((Real.sign g / 2 : ℝ) : ℂ)‖ = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_sign hg]; norm_num
  unfold stcGammaWallOp
  rw [norm_smul, hs]
  have h1 := norm_sub_le (rankOne ℂ (stcBoundaryVec v) (stcBoundaryVec v))
    (rankOne ℂ (stcBoundaryVec (v + 2 * |g|)) (stcBoundaryVec (v + 2 * |g|)))
  have h2 := norm_sub_norm_le (rankOne ℂ (stcBoundaryVec v) (stcBoundaryVec v))
    (rankOne ℂ (stcBoundaryVec (v + 2 * |g|)) (stcBoundaryVec (v + 2 * |g|)))
  simp only [norm_rankOne] at h1 h2
  constructor <;> nlinarith

/-- **(5)** `2‖Q_{a+v,g}‖/‖x_v‖² → 1`. -/
theorem tendsto_norm_stcGammaWallOp_ratio {g : ℝ} (hg : g ≠ 0) :
    Tendsto (fun v => 2 * ‖stcGammaWallOp g v‖ / ‖stcBoundaryVec v‖ ^ 2) (𝓝[>] 0) (𝓝 1) := by
  have ha : 0 < |g| := abs_pos.mpr hg
  set Y := ‖stcBoundaryVec (2 * |g|)‖
  have hx := tendsto_norm_stcBoundaryVec
  have hsq : Tendsto (fun v => ‖stcBoundaryVec v‖ ^ 2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hx
  have hr : Tendsto (fun v => Y ^ 2 / ‖stcBoundaryVec v‖ ^ 2) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  have hlo : Tendsto (fun v => 1 - Y ^ 2 / ‖stcBoundaryVec v‖ ^ 2) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hr
  have hhi : Tendsto (fun v => 1 + Y ^ 2 / ‖stcBoundaryVec v‖ ^ 2) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.add hr
  have hpos : ∀ᶠ v in 𝓝[>] (0 : ℝ), 0 < ‖stcBoundaryVec v‖ ^ 2 := hsq.eventually_gt_atTop 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hpos, self_mem_nhdsWithin] with v hv hv0
    have hy := norm_stcBoundaryVec_shift_le ha (le_of_lt hv0)
    have hy2 : ‖stcBoundaryVec (v + 2 * |g|)‖ ^ 2 ≤ Y ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hy 2
    have hb := (norm_wall_bounds (v := v) hg).1
    rw [show 1 - Y ^ 2 / ‖stcBoundaryVec v‖ ^ 2 = (‖stcBoundaryVec v‖ ^ 2 - Y ^ 2) /
      ‖stcBoundaryVec v‖ ^ 2 by rw [sub_div, div_self hv.ne'], div_le_div_iff_of_pos_right hv]
    linarith
  · filter_upwards [hpos, self_mem_nhdsWithin] with v hv hv0
    have hy := norm_stcBoundaryVec_shift_le ha (le_of_lt hv0)
    have hy2 : ‖stcBoundaryVec (v + 2 * |g|)‖ ^ 2 ≤ Y ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hy 2
    have hb := (norm_wall_bounds (v := v) hg).2
    rw [show 1 + Y ^ 2 / ‖stcBoundaryVec v‖ ^ 2 = (‖stcBoundaryVec v‖ ^ 2 + Y ^ 2) /
      ‖stcBoundaryVec v‖ ^ 2 by rw [add_div, div_self hv.ne'], div_le_div_iff_of_pos_right hv]
    linarith

/-- The unit boundary vectors `e_v = x_v/‖x_v‖`. -/
def stcBoundaryUnit (v : ℝ) : ℓ²P := ((‖stcBoundaryVec v‖⁻¹ : ℝ) : ℂ) • stcBoundaryVec v

/-- **Weak nullity.** `e_v ⇀ 0` as `v ↓ 0`. -/
theorem tendsto_inner_stcBoundaryUnit (z : ℓ²P) :
    Tendsto (fun v => ⟪z, stcBoundaryUnit v⟫_ℂ) (𝓝[>] 0) (𝓝 0) := by
  have hx := tendsto_norm_stcBoundaryVec
  have hpos : ∀ᶠ v in 𝓝[>] (0 : ℝ), 0 < ‖stcBoundaryVec v‖ := hx.eventually_gt_atTop 0
  -- restrict to the eventual region where the norm is positive
  have hnorm : ∀ v, ‖stcBoundaryUnit v‖ ≤ 1 := by
    intro v
    unfold stcBoundaryUnit
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    by_cases h : ‖stcBoundaryVec v‖ = 0
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  refine tendsto_inner_lp_of_coord stcBoundaryUnit zero_le_one hnorm (fun p => ?_) z
  have hbound : Tendsto (fun v => stcDepthZeroAmplitude 0 p / ‖stcBoundaryVec v‖) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hx
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hpos, self_mem_nhdsWithin] with v hv hv0
  have hv0' : (0 : ℝ) < v := hv0
  unfold stcBoundaryUnit
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, stcBoundaryVec_apply hv0',
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_norm,
    abs_of_pos (stcDepthZeroAmplitude_pos v p), inv_mul_eq_div]
  apply div_le_div_of_nonneg_right _ hv.le
  have h := stcDepthZeroAmplitude_sq_anti hv0'.le p
  exact (pow_le_pow_iff_left₀ (stcDepthZeroAmplitude_pos v p).le
    (stcDepthZeroAmplitude_pos 0 p).le two_ne_zero).mp h

/-- The normalized projections `P_{e_v}` tend strongly to zero, although eventually each has
norm one. -/
theorem stcBoundaryUnit_projection_strong_zero (z : ℓ²P) :
    Tendsto (fun v => rankOne ℂ (stcBoundaryUnit v) (stcBoundaryUnit v) z) (𝓝[>] 0) (𝓝 0) ∧
      ∀ᶠ v in 𝓝[>] (0 : ℝ), ‖rankOne ℂ (stcBoundaryUnit v) (stcBoundaryUnit v)‖ = 1 := by
  constructor
  · have h := tendsto_inner_stcBoundaryUnit z
    have hconj : Tendsto (fun v => ⟪stcBoundaryUnit v, z⟫_ℂ) (𝓝[>] 0) (𝓝 0) := by
      have := (Complex.continuous_conj.tendsto 0).comp h
      simpa [Function.comp_def, inner_conj_symm] using this
    refine squeeze_zero_norm (fun v => ?_) (by simpa using hconj.norm)
    rw [rankOne_apply, norm_smul]
    have hn : ‖stcBoundaryUnit v‖ ≤ 1 := by
      unfold stcBoundaryUnit
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      by_cases hh : ‖stcBoundaryVec v‖ = 0
      · simp [hh]
      · rw [inv_mul_cancel₀ hh]
    calc ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ * ‖stcBoundaryUnit v‖ ≤ ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ * 1 :=
          mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ := mul_one _
  · filter_upwards [tendsto_norm_stcBoundaryVec.eventually_gt_atTop 0] with v hv
    rw [norm_rankOne]
    unfold stcBoundaryUnit
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hv.ne']
    norm_num

private theorem norm_inner_unit {v : ℝ} (z : ℓ²P) :
    ‖⟪stcBoundaryVec v, z⟫_ℂ‖ = ‖stcBoundaryVec v‖ * ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ := by
  unfold stcBoundaryUnit
  rw [inner_smul_left, Complex.conj_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_norm]
  by_cases h : ‖stcBoundaryVec v‖ = 0
  · rw [norm_eq_zero.mp h]; simp
  · field_simp

private theorem norm_wall_apply_le {g v : ℝ} (hg : g ≠ 0) (z : ℓ²P) :
    ‖stcGammaWallOp g v z‖ ≤ (‖stcBoundaryVec v‖ ^ 2 * ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ +
      ‖stcBoundaryVec (v + 2 * |g|)‖ ^ 2 * ‖z‖) / 2 := by
  have hs : ‖((Real.sign g / 2 : ℝ) : ℂ)‖ = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_sign hg]; norm_num
  unfold stcGammaWallOp
  rw [_root_.smul_apply, norm_smul, hs, _root_.sub_apply,
    rankOne_apply, rankOne_apply]
  have h1 := norm_sub_le (⟪stcBoundaryVec v, z⟫_ℂ • stcBoundaryVec v)
    (⟪stcBoundaryVec (v + 2 * |g|), z⟫_ℂ • stcBoundaryVec (v + 2 * |g|))
  rw [norm_smul, norm_smul, norm_inner_unit] at h1
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (stcBoundaryVec (v + 2 * |g|)) z
  have h3 : ‖⟪stcBoundaryVec (v + 2 * |g|), z⟫_ℂ‖ * ‖stcBoundaryVec (v + 2 * |g|)‖ ≤
      ‖stcBoundaryVec (v + 2 * |g|)‖ ^ 2 * ‖z‖ := by
    have := mul_le_mul_of_nonneg_right h2 (norm_nonneg (stcBoundaryVec (v + 2 * |g|)))
    nlinarith [norm_nonneg z]
  nlinarith [norm_nonneg (stcBoundaryVec v), norm_nonneg ⟪stcBoundaryUnit v, z⟫_ℂ]

private theorem tendsto_inner_unit_left (z : ℓ²P) :
    Tendsto (fun v => ‖⟪stcBoundaryUnit v, z⟫_ℂ‖) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_inner_stcBoundaryUnit z).norm
  rw [norm_zero] at h
  refine h.congr fun v => ?_
  rw [← inner_conj_symm, Complex.norm_conj]

/-- **(6)** `2Q/‖x_v‖² → 0` strongly while its norm tends to one. -/
theorem stcGammaWallOp_rescaled_limits {g : ℝ} (hg : g ≠ 0) :
    (∀ z : ℓ²P, Tendsto (fun v => (((2 / ‖stcBoundaryVec v‖ ^ 2 : ℝ) : ℂ) • stcGammaWallOp g v) z)
      (𝓝[>] 0) (𝓝 0)) ∧
    Tendsto (fun v => ‖((2 / ‖stcBoundaryVec v‖ ^ 2 : ℝ) : ℂ) • stcGammaWallOp g v‖) (𝓝[>] 0)
      (𝓝 1) := by
  have ha : 0 < |g| := abs_pos.mpr hg
  set Y := ‖stcBoundaryVec (2 * |g|)‖
  have hsq : Tendsto (fun v => ‖stcBoundaryVec v‖ ^ 2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_stcBoundaryVec
  constructor
  · intro z
    have hr : Tendsto (fun v => Y ^ 2 * ‖z‖ / ‖stcBoundaryVec v‖ ^ 2) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsq
    have hbound : Tendsto (fun v => ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ +
        Y ^ 2 * ‖z‖ / ‖stcBoundaryVec v‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_inner_unit_left z).add hr
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hsq.eventually_gt_atTop 0, self_mem_nhdsWithin] with v hv hv0
    have hy := norm_stcBoundaryVec_shift_le ha (le_of_lt hv0)
    have hy2 : ‖stcBoundaryVec (v + 2 * |g|)‖ ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
    rw [_root_.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    have hb := norm_wall_apply_le hg (v := v) z
    calc 2 / ‖stcBoundaryVec v‖ ^ 2 * ‖stcGammaWallOp g v z‖
        ≤ 2 / ‖stcBoundaryVec v‖ ^ 2 * ((‖stcBoundaryVec v‖ ^ 2 * ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ +
            ‖stcBoundaryVec (v + 2 * |g|)‖ ^ 2 * ‖z‖) / 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 2 / ‖stcBoundaryVec v‖ ^ 2 * ((‖stcBoundaryVec v‖ ^ 2 * ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ +
            Y ^ 2 * ‖z‖) / 2) := by
          gcongr
      _ = ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ + Y ^ 2 * ‖z‖ / ‖stcBoundaryVec v‖ ^ 2 := by
          have hX1 : ‖stcBoundaryVec v‖ ≠ 0 := by
            intro h0; rw [h0] at hv; norm_num at hv
          field_simp
  · refine (tendsto_norm_stcGammaWallOp_ratio hg).congr' ?_
    filter_upwards [hsq.eventually_gt_atTop 0] with v hv
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring

/-- The approach sequence `v_n = 1/(n+1) ↓ 0`. -/
private theorem tendsto_wall_seq :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_one_div_add_atTop_nhds_zero_nat
    (Eventually.of_forall fun n => by simp only [Set.mem_Ioi]; positivity)

/-- Uniform boundedness: a strongly convergent scalar family has `|c_v| ‖x_v‖²` bounded along the
approach sequence. -/
private theorem wall_scalar_bound {g : ℝ} (hg : g ≠ 0) (c : ℝ → ℂ) (L : ℓ²P →L[ℂ] ℓ²P)
    (h : ∀ z, Tendsto (fun v => (c v • stcGammaWallOp g v) z) (𝓝[>] 0) (𝓝 (L z))) :
    ∃ C, ∀ᶠ n : ℕ in atTop, ‖c (1 / ((n : ℝ) + 1))‖ * ‖stcBoundaryVec (1 / ((n : ℝ) + 1))‖ ^ 2 ≤ C := by
  have ha : 0 < |g| := abs_pos.mpr hg
  set Y := ‖stcBoundaryVec (2 * |g|)‖
  have hpt : ∀ z : ℓ²P, ∃ C, ∀ n : ℕ,
      ‖(c (1 / ((n : ℝ) + 1)) • stcGammaWallOp g (1 / ((n : ℝ) + 1))) z‖ ≤ C := by
    intro z
    have hseq := (h z).comp tendsto_wall_seq
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hseq)
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus hpt
  have hsq : Tendsto (fun n : ℕ => ‖stcBoundaryVec (1 / ((n : ℝ) + 1))‖ ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_stcBoundaryVec.comp tendsto_wall_seq)
  refine ⟨4 * C', ?_⟩
  filter_upwards [hsq.eventually_ge_atTop (2 * Y ^ 2 + 1)] with n hn
  set v : ℝ := 1 / ((n : ℝ) + 1)
  have hv0 : 0 < v := by positivity
  have hy2 : ‖stcBoundaryVec (v + 2 * |g|)‖ ^ 2 ≤ Y ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_stcBoundaryVec_shift_le ha hv0.le) 2
  have hlow := (norm_wall_bounds (v := v) hg).1
  have hnorm := hC' n
  rw [norm_smul] at hnorm
  have hc0 := norm_nonneg (c v)
  have hY := sq_nonneg Y
  nlinarith

/-- **Only the zero strong limit.** If a scalar family `c_v Q_{|g|+v,g}` has a bounded strong
limit `L` as `v ↓ 0`, then `L = 0`. -/
theorem stcGammaWall_scalar_strong_limit_eq_zero {g : ℝ} (hg : g ≠ 0) (c : ℝ → ℂ)
    (L : ℓ²P →L[ℂ] ℓ²P)
    (h : ∀ z, Tendsto (fun v => (c v • stcGammaWallOp g v) z) (𝓝[>] 0) (𝓝 (L z))) : L = 0 := by
  have ha : 0 < |g| := abs_pos.mpr hg
  set Y := ‖stcBoundaryVec (2 * |g|)‖
  obtain ⟨C, hC⟩ := wall_scalar_bound hg c L h
  ext1 z
  have hseq := (h z).comp tendsto_wall_seq
  have hsq : Tendsto (fun n : ℕ => ‖stcBoundaryVec (1 / ((n : ℝ) + 1))‖ ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_stcBoundaryVec.comp tendsto_wall_seq)
  have hinner : Tendsto (fun n : ℕ => ‖⟪stcBoundaryUnit (1 / ((n : ℝ) + 1)), z⟫_ℂ‖) atTop (𝓝 0) :=
    (tendsto_inner_unit_left z).comp tendsto_wall_seq
  have hC0 : 0 ≤ C := by
    obtain ⟨n, hn⟩ := hC.exists
    exact (mul_nonneg (norm_nonneg _) (sq_nonneg _)).trans hn
  have hbound : Tendsto (fun n : ℕ => C / 2 * ‖⟪stcBoundaryUnit (1 / ((n : ℝ) + 1)), z⟫_ℂ‖ +
      C * Y ^ 2 * ‖z‖ / 2 / ‖stcBoundaryVec (1 / ((n : ℝ) + 1))‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hinner.const_mul (C / 2)).add (tendsto_const_nhds.div_atTop hsq)
  have hzero : Tendsto (fun n : ℕ => (c (1 / ((n : ℝ) + 1)) •
      stcGammaWallOp g (1 / ((n : ℝ) + 1))) z) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hC, hsq.eventually_gt_atTop 0] with n hn hpos
    set v : ℝ := 1 / ((n : ℝ) + 1)
    have hv0 : 0 < v := by positivity
    have hy2 : ‖stcBoundaryVec (v + 2 * |g|)‖ ^ 2 ≤ Y ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_stcBoundaryVec_shift_le ha hv0.le) 2
    rw [_root_.smul_apply, norm_smul]
    have hb := norm_wall_apply_le hg (v := v) z
    have hcx : ‖c v‖ ≤ C / ‖stcBoundaryVec v‖ ^ 2 := by rw [le_div_iff₀ hpos]; exact hn
    calc ‖c v‖ * ‖stcGammaWallOp g v z‖
        ≤ ‖c v‖ * ((‖stcBoundaryVec v‖ ^ 2 * ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ +
            Y ^ 2 * ‖z‖) / 2) := by
          refine mul_le_mul_of_nonneg_left (hb.trans ?_) (norm_nonneg _)
          gcongr
      _ = ‖c v‖ * ‖stcBoundaryVec v‖ ^ 2 * ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ / 2 +
            ‖c v‖ * (Y ^ 2 * ‖z‖) / 2 := by ring
      _ ≤ C * ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ / 2 + C / ‖stcBoundaryVec v‖ ^ 2 * (Y ^ 2 * ‖z‖) / 2 := by
          gcongr
      _ = C / 2 * ‖⟪stcBoundaryUnit v, z⟫_ℂ‖ + C * Y ^ 2 * ‖z‖ / 2 / ‖stcBoundaryVec v‖ ^ 2 := by
          field_simp
  rw [_root_.zero_apply]
  exact tendsto_nhds_unique hseq hzero

/-- **No bounded strong limit without a compensating scalar.** -/
theorem not_exists_strong_limit_stcGammaWallOp {g : ℝ} (hg : g ≠ 0) :
    ¬ ∃ L : ℓ²P →L[ℂ] ℓ²P, ∀ z, Tendsto (fun v => stcGammaWallOp g v z) (𝓝[>] 0) (𝓝 (L z)) := by
  rintro ⟨L, hL⟩
  obtain ⟨C, hC⟩ := wall_scalar_bound hg (fun _ => 1) L (fun z => by simpa using hL z)
  have hsq : Tendsto (fun n : ℕ => ‖stcBoundaryVec (1 / ((n : ℝ) + 1))‖ ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_stcBoundaryVec.comp tendsto_wall_seq)
  obtain ⟨n, hn1, hn2⟩ := (hC.and (hsq.eventually_gt_atTop C)).exists
  simp only [norm_one, one_mul] at hn1
  linarith

end

end RHTower
