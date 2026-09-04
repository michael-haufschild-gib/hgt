import GaloisForLFunctions.RHTower.RouteJUniformLawCoefficients

/-!
# The two limits of the uniform law

* Fixed `δ > 0`, `k → ∞`: `M_k(δ)/k^{3/2} − 32√(2/π) σ^{3/2} τ^{5/2} sin((4k+9/2)φ − π/4) → 0`, hence the
  beat law `tendsto_beatMode_profile_of_uniform`.
* Scaling data `p_j → ∞`, `2k_j/p_j → X`, `δ_j = log p_j`: `M_{k_j}(δ_j) → Φ(X)`, hence the scaling
  profile `tendsto_residual_profile_of_uniform`.

Both are corollaries of the single uniform law `abs_residual_sub_uniformMain_le`.
-/

open Filter Topology Finset
open scoped Real

namespace RHTower
namespace RouteJUniform

open LegendreBoost RouteJProfile CosineModeResponse RouteJBeatMode

/-! ## Common tools -/

theorem tendsto_one_div_sqrt : Tendsto (fun k : ℕ => 1 / Real.sqrt k) atTop (𝓝 0) := by
  have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
  rw [Real.sqrt_zero] at this
  refine this.congr' (Eventually.of_forall fun k => ?_)
  show Real.sqrt (1 / (k : ℝ)) = 1 / Real.sqrt k
  rw [one_div, Real.sqrt_inv, one_div]

theorem tendsto_sqrt_div_affine : Tendsto (fun k : ℕ => Real.sqrt k / (4 * (k : ℝ) + 3)) atTop (𝓝 0) := by
  have h1 := tendsto_one_div_sqrt
  have h2 : Tendsto (fun k : ℕ => 4 + 3 * (1 / (k : ℝ))) atTop (𝓝 (4 + 3 * 0)) :=
    tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat.const_mul 3)
  have h := h1.div h2 (by norm_num)
  rw [show (0 : ℝ) / (4 + 3 * 0) = 0 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hs := Real.mul_self_sqrt hk0.le
  have hs0 : Real.sqrt k ≠ 0 := (Real.sqrt_pos.mpr hk0).ne'
  show 1 / Real.sqrt k / (4 + 3 * (1 / (k : ℝ))) = Real.sqrt k / (4 * (k : ℝ) + 3)
  field_simp
  linear_combination (-1 : ℝ) * hs

theorem tendsto_wallis_shift (j : ℕ) :
    Tendsto (fun k : ℕ => Real.sqrt k * cb (4 * k + j)) atTop (𝓝 (1 / (2 * Real.sqrt π))) := by
  have h := tendsto_wallisSeq.mul (tendsto_cb_ratio_four j)
  rw [mul_one] at h
  refine h.congr' (Eventually.of_forall fun k => ?_)
  unfold wallisSeq
  have := (cb_pos (4 * k)).ne'
  field_simp

theorem beatPhase_three_eq (δ : ℝ) (k : ℕ) : beatPhase δ k 3 = beatPhase δ k 4 - beatAngle δ := by
  unfold beatPhase
  push_cast
  ring

theorem cos_beatPhase_three (δ : ℝ) (k : ℕ) :
    Real.cos (beatPhase δ k 3) =
      (1 / Real.cosh δ) * Real.cos (beatPhase δ k 4) +
        Real.sin (beatAngle δ) * Real.sin (beatPhase δ k 4) := by
  rw [beatPhase_three_eq, Real.cos_sub, cos_beatAngle]
  ring

theorem sin_beatAngle_sq (δ : ℝ) : Real.sin (beatAngle δ) ^ 2 = 1 - (1 / Real.cosh δ) ^ 2 := by
  rw [Real.sin_sq, cos_beatAngle]

/-! ## The beat limit of the uniform main term -/

theorem tendsto_uniformMain_beat {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k : ℕ => uniformMain δ k / (k : ℝ) ^ (3 / 2 : ℝ) -
      beatModeAmplitude δ * Real.sin (beatPhase δ k 4)) atTop (𝓝 0) := by
  set σ := 1 / Real.cosh δ with hσ
  set τ := Real.sin (beatAngle δ) with hτ
  set C := Real.cosh δ ^ (-(1 / 2 : ℝ)) * (2 * beatSfac δ) with hC
  have hA := tendsto_twoIndexA_div_sq σ
  have hB := tendsto_twoIndexB_div_sq σ
  have hW3 := tendsto_wallis_shift 3
  have hW4 := tendsto_wallis_shift 4
  have hτσ : 1 - σ ^ 2 = τ ^ 2 := (sin_beatAngle_sq δ).symm
  rw [hτσ] at hA hB
  -- the two vanishing products
  have h1 : Tendsto (fun k : ℕ => twoIndexA k σ / (k : ℝ) ^ 2 * (Real.sqrt k * cb (4 * k + 3)) -
      64 * σ * τ ^ 2 * (1 / (2 * Real.sqrt π))) atTop (𝓝 0) := by
    have := (hA.mul hW3).sub_const (64 * σ * τ ^ 2 * (1 / (2 * Real.sqrt π)))
    rwa [sub_self] at this
  have h2 : Tendsto (fun k : ℕ => twoIndexB k σ / (k : ℝ) ^ 2 * (Real.sqrt k * cb (4 * k + 4)) -
      -64 * σ ^ 2 * τ ^ 2 * (1 / (2 * Real.sqrt π))) atTop (𝓝 0) := by
    have := (hB.mul hW4).sub_const (-64 * σ ^ 2 * τ ^ 2 * (1 / (2 * Real.sqrt π)))
    rwa [sub_self] at this
  have hb3 : IsBoundedUnder (· ≤ ·) atTop
      ((fun x => ‖x‖) ∘ fun k : ℕ => Real.cos (beatPhase δ k 3)) :=
    isBoundedUnder_of ⟨1, fun k => by
      simpa [Function.comp, Real.norm_eq_abs] using Real.abs_cos_le_one (beatPhase δ k 3)⟩
  have hb4 : IsBoundedUnder (· ≤ ·) atTop
      ((fun x => ‖x‖) ∘ fun k : ℕ => Real.cos (beatPhase δ k 4)) :=
    isBoundedUnder_of ⟨1, fun k => by
      simpa [Function.comp, Real.norm_eq_abs] using Real.abs_cos_le_one (beatPhase δ k 4)⟩
  have hsum := ((h1.zero_mul_isBoundedUnder_le hb3).add (h2.zero_mul_isBoundedUnder_le hb4)).const_mul C
  rw [add_zero, mul_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk32 : (k : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt k ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
    norm_num
  have hL := beatAmplitude_eq hδ
  rw [Real.sin_two_mul, cos_beatAngle] at hL
  unfold uniformMain
  rw [hk32, hL, cos_beatPhase_three]
  set t := Real.sqrt k with ht
  have ht0 : t ≠ 0 := (Real.sqrt_pos.mpr hk0).ne'
  have hkt : (k : ℝ) = t ^ 2 := (Real.sq_sqrt hk0.le).symm
  rw [hkt, hσ, hτ, hC]
  have hc : Real.cosh δ ≠ 0 := (Real.cosh_pos δ).ne'
  have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

/-- **The beat law as a corollary of the uniform law.** -/
theorem tendsto_beatMode_profile_of_uniform {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k : ℕ => residualJetOf (cosineModeDeterminantJet δ) k / (k : ℝ) ^ (3 / 2 : ℝ) -
      beatModeAmplitude δ * Real.sin (beatPhase δ k 4)) atTop (𝓝 0) := by
  set σ := 1 / Real.cosh δ with hσ
  have hM := tendsto_uniformMain_beat hδ
  -- the error term
  have hE : Tendsto (fun k : ℕ => (residualJetOf (cosineModeDeterminantJet δ) k - uniformMain δ k) /
      (k : ℝ) ^ (3 / 2 : ℝ)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun k : ℕ => Real.cosh δ ^ (-(1 / 2 : ℝ)) *
        (|twoIndexA k σ / (k : ℝ) ^ 2| + |twoIndexB k σ / (k : ℝ) ^ 2|) *
        (400 / Real.sin (beatAngle δ)) * (Real.sqrt k / (4 * (k : ℝ) + 3))) atTop (𝓝 0) := by
      have := ((((tendsto_twoIndexA_div_sq σ).abs.add (tendsto_twoIndexB_div_sq σ).abs).const_mul
        (Real.cosh δ ^ (-(1 / 2 : ℝ)))).mul_const (400 / Real.sin (beatAngle δ))).mul
        tendsto_sqrt_div_affine
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 2] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hb := abs_residual_sub_uniformMain_le hδ hk
    have hs := sin_beatAngle_pos hδ
    have hk32 : (k : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt k ^ 3 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
      norm_num
    rw [Real.norm_eq_abs, abs_div, hk32, abs_of_pos (pow_pos (Real.sqrt_pos.mpr hk0) 3)]
    have hs3 : 0 < Real.sqrt k ^ 3 := pow_pos (Real.sqrt_pos.mpr hk0) 3
    rw [div_le_iff₀ hs3]
    have hkey : Real.cosh δ ^ (-(1 / 2 : ℝ)) * (|twoIndexA k σ / (k : ℝ) ^ 2| + |twoIndexB k σ / (k : ℝ) ^ 2|) *
        (400 / Real.sin (beatAngle δ)) * (Real.sqrt k / (4 * (k : ℝ) + 3)) * Real.sqrt k ^ 3 =
        Real.cosh δ ^ (-(1 / 2 : ℝ)) * (|twoIndexA k σ| + |twoIndexB k σ|) *
          (400 / (Real.sin (beatAngle δ) * (4 * (k : ℝ) + 3))) := by
      rw [abs_div, abs_div, abs_of_pos (pow_pos hk0 2)]
      set t := Real.sqrt k with ht
      have ht0 : t ≠ 0 := (Real.sqrt_pos.mpr hk0).ne'
      have hkt : (k : ℝ) = t ^ 2 := (Real.sq_sqrt hk0.le).symm
      rw [hkt]
      have h43 : (4 * t ^ 2 + 3) ≠ 0 := by positivity
      field_simp
    rw [hkey]
    exact hb
  have := hE.add hM
  rw [add_zero] at this
  refine this.congr' (Eventually.of_forall fun k => ?_)
  ring

/-! ## The scaling limit of the uniform main term -/

namespace ScalingLimits

open RouteJProfile.ScalingData

variable (D : RouteJProfile.ScalingData)

theorem σ_pos (j : ℕ) : 0 < D.σ j := by
  unfold RouteJProfile.ScalingData.σ
  have := Real.cosh_pos (Real.log (D.p j))
  positivity

theorem beatAngle_eq (j : ℕ) : beatAngle (D.δ j) = Real.arccos (D.σ j) := rfl

theorem tendsto_arcsin_div : Tendsto (fun j => Real.arcsin (D.σ j) / D.σ j) atTop (𝓝 1) := by
  have hd := (Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
    (by norm_num : (0 : ℝ) ≠ 1)).tendsto_slope_zero
  have hσ : Tendsto D.σ atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨D.tendsto_σ_zero,
      Eventually.of_forall fun j => Set.mem_compl_singleton_iff.mpr (σ_pos D j).ne'⟩
  have h := hd.comp hσ
  have hv : (1 : ℝ) / Real.sqrt (1 - (0 : ℝ) ^ 2) = 1 := by norm_num
  rw [hv] at h
  refine h.congr' (Eventually.of_forall fun j => ?_)
  simp only [Function.comp, zero_add, Real.arcsin_zero, sub_zero, smul_eq_mul]
  rw [div_eq_inv_mul]

/-- `θ_j = (4k_j + 9/2) arcsin σ_j → 4X`. -/
theorem tendsto_theta :
    Tendsto (fun j => (4 * (D.k j : ℝ) + 9 / 2) * Real.arcsin (D.σ j)) atTop (𝓝 (4 * D.X)) := by
  have h := (D.tendsto_affine_mul_σ 4 (9 / 2)).mul (tendsto_arcsin_div D)
  rw [mul_one] at h
  refine h.congr' (Eventually.of_forall fun j => ?_)
  have := (σ_pos D j).ne'
  field_simp

theorem tendsto_arcsin_σ : Tendsto (fun j => Real.arcsin (D.σ j)) atTop (𝓝 0) := by
  have := (Real.continuous_arcsin.tendsto 0).comp D.tendsto_σ_zero
  rwa [Real.arcsin_zero] at this

theorem beatPhase_four_eq (j : ℕ) :
    beatPhase (D.δ j) (D.k j) 4 =
      ((D.k j + 1 : ℕ) : ℝ) * (2 * π) - (4 * (D.k j : ℝ) + 9 / 2) * Real.arcsin (D.σ j) := by
  unfold beatPhase
  rw [beatAngle_eq, Real.arccos_eq_pi_div_two_sub_arcsin]
  push_cast
  ring

theorem tendsto_cos_beatPhase_four :
    Tendsto (fun j => Real.cos (beatPhase (D.δ j) (D.k j) 4)) atTop (𝓝 (Real.cos (4 * D.X))) := by
  have h := (Real.continuous_cos.tendsto _).comp (tendsto_theta D)
  refine h.congr' (Eventually.of_forall fun j => ?_)
  simp only [Function.comp]
  rw [beatPhase_four_eq, Real.cos_nat_mul_two_pi_sub]

theorem tendsto_cos_beatPhase_three :
    Tendsto (fun j => Real.cos (beatPhase (D.δ j) (D.k j) 3)) atTop (𝓝 (-Real.sin (4 * D.X))) := by
  have hθ := (tendsto_theta D).sub (tendsto_arcsin_σ D)
  rw [sub_zero] at hθ
  have h := (Real.continuous_sin.tendsto _).comp hθ
  have h' := h.neg
  refine h'.congr' (Eventually.of_forall fun j => ?_)
  simp only [Function.comp]
  rw [beatPhase_three_eq, beatPhase_four_eq, beatAngle_eq, Real.arccos_eq_pi_div_two_sub_arcsin,
    show ((D.k j + 1 : ℕ) : ℝ) * (2 * π) - (4 * (D.k j : ℝ) + 9 / 2) * Real.arcsin (D.σ j) -
        (π / 2 - Real.arcsin (D.σ j)) =
      ((D.k j + 1 : ℕ) : ℝ) * (2 * π) -
        (((4 * (D.k j : ℝ) + 9 / 2) * Real.arcsin (D.σ j) - Real.arcsin (D.σ j)) + π / 2) by ring,
    Real.cos_nat_mul_two_pi_sub, Real.cos_add_pi_div_two]

theorem tendsto_sin_beatAngle : Tendsto (fun j => Real.sin (beatAngle (D.δ j))) atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (D.tendsto_σ_zero.pow 2)).sqrt
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, sub_zero, Real.sqrt_one] at h
  refine h.congr' (Eventually.of_forall fun j => ?_)
  show Real.sqrt (1 - D.σ j ^ 2) = Real.sin (beatAngle (D.δ j))
  rw [beatAngle_eq, Real.sin_arccos]

theorem tendsto_two_beatSfac : Tendsto (fun j => 2 * beatSfac (D.δ j)) atTop (𝓝 (Real.sqrt 2)) := by
  have h2 : Tendsto (fun j => 2 * Real.sin (beatAngle (D.δ j))) atTop (𝓝 (2 * 1)) :=
    (tendsto_sin_beatAngle D).const_mul 2
  have hc : ContinuousAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (2 * 1) :=
    Real.continuousAt_rpow_const _ _ (Or.inl (by norm_num))
  have h := (hc.tendsto.comp h2).const_mul 2
  have hv : (2 : ℝ) * (2 * 1) ^ (-(1 / 2 : ℝ)) = Real.sqrt 2 := by
    rw [mul_one, beat_rpow_neg_half (by norm_num)]
    have := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have h2p : 0 < Real.sqrt 2 := by positivity
    field_simp
    linear_combination (-1 : ℝ) * this
  rw [hv] at h
  exact h

theorem tendsto_cosh_rpow_mul_sqrt_k :
    Tendsto (fun j => Real.cosh (D.δ j) ^ (-(1 / 2 : ℝ)) * Real.sqrt (D.k j)) atTop (𝓝 (Real.sqrt D.X)) := by
  have h := (D.tendsto_cosh_rpow_mul_sqrt.mul D.tendsto_sqrt_ratio).div_const (Real.sqrt 2)
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  rw [show Real.sqrt 2 * Real.sqrt D.X / Real.sqrt 2 = Real.sqrt D.X by field_simp] at h
  refine h.congr' ?_
  filter_upwards [D.eventually_p_pos] with j hj
  have hp : Real.sqrt (D.p j) ≠ 0 := (Real.sqrt_pos.mpr hj).ne'
  show Real.cosh (Real.log (D.p j)) ^ (-(1 / 2 : ℝ)) * Real.sqrt (D.p j) *
      (Real.sqrt (2 * (D.k j : ℝ)) / Real.sqrt (D.p j)) / Real.sqrt 2 =
    Real.cosh (Real.log (D.p j)) ^ (-(1 / 2 : ℝ)) * Real.sqrt (D.k j)
  rw [Real.sqrt_mul (by norm_num)]
  field_simp

theorem tendsto_k_shift_atTop (j₀ : ℕ) : Tendsto (fun j => 4 * D.k j + j₀) atTop atTop :=
  tendsto_atTop_mono (fun j => by omega) D.tendsto_k_nat

theorem tendsto_sqrt_k_mul_cb (j₀ : ℕ) :
    Tendsto (fun j => Real.sqrt (D.k j) * cb (4 * D.k j + j₀)) atTop (𝓝 (1 / (2 * Real.sqrt π))) := by
  have hW := GaloisForLFunctions.HTGeometry.tendsto_sqrtNat_mul_normalizedCentralBinom.comp
    (tendsto_k_shift_atTop D j₀)
  have hr : Tendsto (fun j => Real.sqrt ((D.k j : ℝ) / (4 * (D.k j : ℝ) + j₀))) atTop
      (𝓝 (Real.sqrt (1 / 4))) := by
    have h : Tendsto (fun j => 1 / (4 + (j₀ : ℝ) * (1 / (D.k j : ℝ)))) atTop (𝓝 (1 / (4 + (j₀ : ℝ) * 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add ((tendsto_k_inv' D).const_mul _)) (by norm_num)
    rw [mul_zero, add_zero] at h
    refine h.sqrt.congr' ?_
    filter_upwards [eventually_k_ge D 1] with j hj
    have hk0 : (D.k j : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.k j ≠ 0)
    congr 1
    field_simp
  have h := hr.mul hW
  have hv : Real.sqrt (1 / 4) * (1 / Real.sqrt π) = 1 / (2 * Real.sqrt π) := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_k_ge D 1] with j hj
  have hk0 : (0 : ℝ) < D.k j := by exact_mod_cast (by omega : 0 < D.k j)
  have hpos : (0 : ℝ) < 4 * (D.k j : ℝ) + j₀ := by positivity
  simp only [Function.comp]
  push_cast
  have hcb : cb (4 * D.k j + j₀) =
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom (4 * D.k j + j₀) := rfl
  rw [hcb, Real.sqrt_div' _ hpos.le]
  have hs0 : Real.sqrt (4 * (D.k j : ℝ) + j₀) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  field_simp

/-- **The scaling profile as the limit of the uniform main term.** -/
theorem tendsto_uniformMain_scaling :
    Tendsto (fun j => uniformMain (D.δ j) (D.k j)) atTop (𝓝 (profile D.X)) := by
  have h := ((tendsto_cosh_rpow_mul_sqrt_k D).mul (tendsto_two_beatSfac D)).mul
    ((((tendsto_twoIndexA_div_k D).mul (tendsto_sqrt_k_mul_cb D 3)).mul
        (tendsto_cos_beatPhase_three D)).add
      (((tendsto_twoIndexB_div_k D).mul (tendsto_sqrt_k_mul_cb D 4)).mul
        (tendsto_cos_beatPhase_four D)))
  have hv : Real.sqrt D.X * Real.sqrt 2 *
      (64 * D.X * (1 / (2 * Real.sqrt π)) * -Real.sin (4 * D.X) +
        8 * (1 / (2 * Real.sqrt π)) * Real.cos (4 * D.X)) = profile D.X := by
    unfold profile
    rw [Real.sqrt_div' 2 Real.pi_pos.le]
    have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp
    ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_k_ge D 1] with j hj
  have hk0 : (0 : ℝ) < D.k j := by exact_mod_cast (by omega : 0 < D.k j)
  have hkk : Real.sqrt (D.k j) * Real.sqrt (D.k j) = D.k j := Real.mul_self_sqrt hk0.le
  unfold uniformMain
  have hσ : (1 / Real.cosh (D.δ j)) = D.σ j := rfl
  rw [hσ]
  set t := Real.sqrt (D.k j) with ht
  have ht0 : t ≠ 0 := (Real.sqrt_pos.mpr hk0).ne'
  have hkt : (D.k j : ℝ) = t ^ 2 := (Real.sq_sqrt hk0.le).symm
  rw [hkt]
  field_simp

/-- **The scaling profile as a corollary of the uniform law.** -/
theorem tendsto_residual_profile_of_uniform :
    Tendsto (fun j => residualJetOf (cosineModeDeterminantJet (D.δ j)) (D.k j)) atTop
      (𝓝 (profile D.X)) := by
  have hM := tendsto_uniformMain_scaling D
  have hE : Tendsto (fun j => residualJetOf (cosineModeDeterminantJet (D.δ j)) (D.k j) -
      uniformMain (D.δ j) (D.k j)) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun j => Real.cosh (D.δ j) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
      have := D.tendsto_σ_zero.sqrt
      rw [Real.sqrt_zero] at this
      refine this.congr' (Eventually.of_forall fun j => ?_)
      exact (D.cosh_rpow_eq_sqrt_σ j).symm
    have hab : Tendsto (fun j => (|twoIndexA (D.k j) (D.σ j) / (D.k j : ℝ)| +
        |twoIndexB (D.k j) (D.σ j) / (D.k j : ℝ)|) * ((D.k j : ℝ) / (4 * (D.k j : ℝ) + 3))) atTop
        (𝓝 ((|64 * D.X| + |8|) * (1 / 4))) := by
      refine ((tendsto_twoIndexA_div_k D).abs.add (tendsto_twoIndexB_div_k D).abs).mul ?_
      have h : Tendsto (fun j => 1 / (4 + 3 * (1 / (D.k j : ℝ)))) atTop (𝓝 (1 / (4 + 3 * 0))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.add ((tendsto_k_inv' D).const_mul _)) (by norm_num)
      rw [mul_zero, add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_k_ge D 1] with j hj
      have hk0 : (D.k j : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.k j ≠ 0)
      field_simp
    have hsin : Tendsto (fun j => 400 / Real.sin (beatAngle (D.δ j))) atTop (𝓝 (400 / 1)) :=
      tendsto_const_nhds.div (tendsto_sin_beatAngle D) (by norm_num)
    have hbound := (hsqrt.mul hab).mul hsin
    rw [zero_mul, zero_mul] at hbound
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_k_ge D 2, D.hp.eventually (eventually_gt_atTop 1)] with j hk hp
    have hδ : 0 < D.δ j := Real.log_pos hp
    have hb := abs_residual_sub_uniformMain_le hδ hk
    have hσ : (1 / Real.cosh (D.δ j)) = D.σ j := rfl
    rw [hσ] at hb
    rw [Real.norm_eq_abs]
    refine hb.trans (le_of_eq ?_)
    have hk0 : (0 : ℝ) < D.k j := by exact_mod_cast (by omega : 0 < D.k j)
    have hs := sin_beatAngle_pos hδ
    rw [abs_div, abs_div, abs_of_pos hk0]
    field_simp
  have := hM.add hE
  rw [add_zero] at this
  refine this.congr' (Eventually.of_forall fun j => ?_)
  ring

end ScalingLimits

end RouteJUniform
end RHTower
