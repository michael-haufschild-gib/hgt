import GaloisForLFunctions.RHTower.Suzuki.SuzukiRealKernelForm

/-!
# Suzuki's archimedean primitive has a forced sign change below the half shift

For `0 < ω < 3/2` Suzuki's compact kernel has the endpoint expansions

`g_ω(y) ∼ A_ω (1-y)^{ω-1}`  as `y → 1⁻`,  `A_ω = (2π)^ω/Γ(ω) > 0`,
`g_ω(y) ∼ -B_ω y^{ω-1}`     as `y → 0⁺`,  `B_ω = 4ω π^{ω-1/2} Γ(3/2-ω) > 0`.

Integrating the weighted kernel `y^{-1/2} g_ω(y)` transfers these to the once-integrated kernel
`g_ω^{⟨1⟩}(x) = x^{-1/2} ∫_x^(1 : ℕ) y^{-1/2} g_ω(y) dy`.  In the RH-relevant range `0 < ω < 1/2` the
first exponent lies below `-1`, so the primitive diverges at the origin with the opposite sign:

`g_ω^{⟨1⟩}(x) ∼ -B_ω/(1/2-ω) · x^{ω-1}`  as `x → 0⁺`,
`g_ω^{⟨1⟩}(x) ∼ A_ω/ω · (1-x)^{ω}`       as `x → 1⁻`.

Consequently `g_ω^{⟨1⟩}` is strictly negative on an interval `(0,ε)` and strictly positive on an
interval `(1-δ,1)`: the integrated archimedean kernel entering Suzuki's one-sign criterion changes
sign inside its own support, so no pointwise sign-preservation argument can produce the required
eventual single sign.
-/

namespace RHTower

noncomputable section

open MeasureTheory Set Filter Topology

/-! ## The endpoint constants -/

/-- `A_ω = (2π)^ω/Γ(ω)`, the endpoint constant of `g_ω` at the support endpoint `1`. -/
def suzukiKernelConstantOne (ω : ℝ) : ℝ := (2 * Real.pi) ^ ω / Real.Gamma ω

/-- `B_ω = 4ω π^{ω-1/2} Γ(3/2-ω)`, the endpoint constant of `g_ω` at the origin. -/
def suzukiKernelConstantZero (ω : ℝ) : ℝ :=
  4 * ω * Real.pi ^ (ω - 1 / 2) * Real.Gamma (3 / 2 - ω)

theorem suzukiKernelConstantOne_pos {ω : ℝ} (hω : 0 < ω) : 0 < suzukiKernelConstantOne ω := by
  rw [suzukiKernelConstantOne]
  exact div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos hω)

theorem suzukiKernelConstantZero_pos {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    0 < suzukiKernelConstantZero ω := by
  rw [suzukiKernelConstantZero]
  have hΓ : 0 < Real.Gamma (3 / 2 - ω) := Real.Gamma_pos_of_pos (by linarith)
  have hpi : 0 < Real.pi ^ (ω - 1 / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  positivity

/-- The prefactor of Suzuki's kernel times the complete beta value is the endpoint constant. -/
theorem suzukiKernelConstantZero_eq {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    (2 * Real.pi ^ ω / Real.Gamma ω) * (ω * suzukiRealBetaTail ω 0)
      = suzukiKernelConstantZero ω := by
  have hG : Real.Gamma ω ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hω)
  have hs : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have h32 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    have hx : (3 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
    rw [hx, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hpi : Real.pi ^ (ω - 1 / 2) = Real.pi ^ ω / Real.sqrt Real.pi := by
    rw [Real.rpow_sub Real.pi_pos, Real.sqrt_eq_rpow]
  rw [suzukiRealBetaTail_zero hω hω', suzukiKernelConstantZero, h32, hpi]
  field_simp
  ring

/-- The prefactor of Suzuki's kernel times `2^{ω-1}` is the endpoint constant at `1`. -/
theorem suzukiKernelConstantOne_eq {ω : ℝ} (hω : 0 < ω) :
    (2 * Real.pi ^ ω / Real.Gamma ω) * (2 : ℝ) ^ (ω - 1) = suzukiKernelConstantOne ω := by
  have hG : Real.Gamma ω ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hω)
  have hsplit : (2 * Real.pi) ^ ω = (2 : ℝ) ^ ω * Real.pi ^ ω :=
    Real.mul_rpow (by norm_num) Real.pi_pos.le
  have htwo : (2 : ℝ) * (2 : ℝ) ^ (ω - 1) = (2 : ℝ) ^ ω := by
    have h := Real.rpow_add (show (0 : ℝ) < 2 by norm_num) 1 (ω - 1)
    rw [Real.rpow_one, show (1 : ℝ) + (ω - 1) = ω by ring] at h
    exact h.symm
  rw [suzukiKernelConstantOne, hsplit, ← htwo]
  field_simp

/-! ## Endpoint expansion of the kernel -/

/-- **Endpoint expansion at the origin.**  `g_ω(y)/y^{ω-1} → -B_ω`. -/
theorem tendsto_suzukiRealSourceG_div_rpow_nhdsGT_zero {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    Tendsto (fun y => suzukiRealSourceG ω y / y ^ (ω - 1)) (𝓝[>] (0 : ℝ))
      (𝓝 (-suzukiKernelConstantZero ω)) := by
  have hone : Tendsto (fun y : ℝ => (1 - y ^ 2) ^ (ω - 1)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hinner : ContinuousAt (fun y : ℝ => 1 - y ^ 2) 0 := by fun_prop
    have houter : ContinuousAt (fun u : ℝ => u ^ (ω - 1)) (1 - (0 : ℝ) ^ 2) := by
      have hval : (1 : ℝ) - (0 : ℝ) ^ 2 = 1 := by norm_num
      rw [hval]
      exact Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
    have hcomp : ContinuousAt (fun y : ℝ => (1 - y ^ 2) ^ (ω - 1)) 0 :=
      ContinuousAt.comp (g := fun u : ℝ => u ^ (ω - 1)) (f := fun y : ℝ => 1 - y ^ 2)
        (x := 0) houter hinner
    have hres := hcomp.tendsto
    have hval : ((1 : ℝ) - (0 : ℝ) ^ 2) ^ (ω - 1) = 1 := by norm_num
    rw [hval] at hres
    exact hres.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun y : ℝ => y ^ (3 - 2 * ω)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    HTGeometry.tendsto_rpow_nhdsGT_zero (by linarith)
  have htail := tendsto_suzukiRealBetaTail_nhdsGT_zero hω hω'
  have hK : Tendsto (fun y : ℝ => (2 * Real.pi ^ ω / Real.Gamma ω) *
      (y ^ (3 - 2 * ω) * (1 - y ^ 2) ^ (ω - 1) - ω * suzukiRealBetaTail ω y))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((2 * Real.pi ^ ω / Real.Gamma ω) *
        ((0 : ℝ) * 1 - ω * suzukiRealBetaTail ω 0))) :=
    ((hzero.mul hone).sub (htail.const_mul ω)).const_mul _
  have hval : (2 * Real.pi ^ ω / Real.Gamma ω) * ((0 : ℝ) * 1 - ω * suzukiRealBetaTail ω 0)
      = -suzukiKernelConstantZero ω := by
    rw [← suzukiKernelConstantZero_eq hω hω']
    ring
  rw [hval] at hK
  refine hK.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
  have hy0 : (0 : ℝ) < y := hy.1
  have hne : y ^ (ω - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hy0 _)
  have hpow : y ^ (3 - 2 * ω) = y ^ (2 - ω) / y ^ (ω - 1) := by
    rw [← Real.rpow_sub hy0]
    congr 1
    ring
  rw [suzukiRealSourceG_apply hy0 hy.2, hpow]
  field_simp

/-- The weighted beta tail vanishes at the support endpoint. -/
theorem tendsto_rpow_mul_suzukiRealBetaTail_nhdsLT_one {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    Tendsto (fun y : ℝ => (1 - y) ^ (1 - ω) * suzukiRealBetaTail ω y) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have htailrate := tendsto_suzukiRealBetaTail_nhdsLT_one hω hω'
  have h1 : Tendsto (fun y : ℝ => 1 - y) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun y : ℝ => 1 - y) 1 := by fun_prop
    have hres := hc.tendsto
    norm_num at hres
    exact hres.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun y : ℝ => (1 + y) ^ ω) (𝓝[<] (1 : ℝ)) (𝓝 ((2 : ℝ) ^ ω)) := by
    have hinner : ContinuousAt (fun y : ℝ => 1 + y) 1 := by fun_prop
    have houter : ContinuousAt (fun u : ℝ => u ^ ω) (1 + (1 : ℝ)) := by
      have hval : (1 : ℝ) + 1 = 2 := by norm_num
      rw [hval]
      exact Real.continuousAt_rpow_const 2 _ (Or.inl (by norm_num))
    have hcomp : ContinuousAt (fun y : ℝ => (1 + y) ^ ω) 1 :=
      ContinuousAt.comp (g := fun u : ℝ => u ^ ω) (f := fun y : ℝ => 1 + y) (x := 1)
        houter hinner
    have hres := hcomp.tendsto
    have hval : ((1 : ℝ) + 1) ^ ω = (2 : ℝ) ^ ω := by norm_num
    rw [hval] at hres
    exact hres.mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun y : ℝ => (1 - y) * (1 + y) ^ ω) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hprod := h1.mul h2
    simpa using hprod
  have hprod := htailrate.mul hlin
  have hval : (1 / ω) * (0 : ℝ) = 0 := by ring
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) one_pos] with y hy
  have hy0 : (0 : ℝ) < y := hy.1
  have hy1 : y < 1 := hy.2
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have h1y' : (0 : ℝ) < 1 + y := by linarith
  have hsplit : ((1 : ℝ) - y ^ 2) ^ (-ω) = (1 - y) ^ (-ω) * (1 + y) ^ (-ω) := by
    rw [show (1 : ℝ) - y ^ 2 = (1 - y) * (1 + y) by ring, Real.mul_rpow h1y.le h1y'.le]
  have hcancel : ((1 : ℝ) + y) ^ (-ω) * (1 + y) ^ ω = 1 := by
    rw [← Real.rpow_add h1y']
    simp
  have hpow : ((1 : ℝ) - y) ^ (-ω) * (1 - y) = (1 - y) ^ (1 - ω) := by
    rw [show (1 : ℝ) - ω = -ω + 1 by ring, Real.rpow_add h1y, Real.rpow_one]
  calc ((1 - y ^ 2) ^ (-ω) * suzukiRealBetaTail ω y) * ((1 - y) * (1 + y) ^ ω)
      = (suzukiRealBetaTail ω y * ((1 - y) ^ (-ω) * (1 - y))) *
          ((1 + y) ^ (-ω) * (1 + y) ^ ω) := by
        rw [hsplit]
        ring
    _ = (1 - y) ^ (1 - ω) * suzukiRealBetaTail ω y := by
        rw [hpow, hcancel]
        ring

/-- **Endpoint expansion at the support endpoint.**  `g_ω(y)/(1-y)^{ω-1} → A_ω`. -/
theorem tendsto_suzukiRealSourceG_div_rpow_nhdsLT_one {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    Tendsto (fun y => suzukiRealSourceG ω y / (1 - y) ^ (ω - 1)) (𝓝[<] (1 : ℝ))
      (𝓝 (suzukiKernelConstantOne ω)) := by
  have hpow1 : Tendsto (fun y : ℝ => y ^ (2 - ω)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun y : ℝ => y ^ (2 - ω)) 1 :=
      Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
    have hres := hc.tendsto
    rw [Real.one_rpow] at hres
    exact hres.mono_left nhdsWithin_le_nhds
  have hpow2 : Tendsto (fun y : ℝ => (1 + y) ^ (ω - 1)) (𝓝[<] (1 : ℝ)) (𝓝 ((2 : ℝ) ^ (ω - 1))) := by
    have hinner : ContinuousAt (fun y : ℝ => 1 + y) 1 := by fun_prop
    have houter : ContinuousAt (fun u : ℝ => u ^ (ω - 1)) (1 + (1 : ℝ)) := by
      have hval : (1 : ℝ) + 1 = 2 := by norm_num
      rw [hval]
      exact Real.continuousAt_rpow_const 2 _ (Or.inl (by norm_num))
    have hcomp : ContinuousAt (fun y : ℝ => (1 + y) ^ (ω - 1)) 1 :=
      ContinuousAt.comp (g := fun u : ℝ => u ^ (ω - 1)) (f := fun y : ℝ => 1 + y) (x := 1)
        houter hinner
    have hres := hcomp.tendsto
    have hval : ((1 : ℝ) + 1) ^ (ω - 1) = (2 : ℝ) ^ (ω - 1) := by norm_num
    rw [hval] at hres
    exact hres.mono_left nhdsWithin_le_nhds
  have hpow3 : Tendsto (fun y : ℝ => y ^ (ω - 1)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun y : ℝ => y ^ (ω - 1)) 1 :=
      Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
    have hres := hc.tendsto
    rw [Real.one_rpow] at hres
    exact hres.mono_left nhdsWithin_le_nhds
  have htail := tendsto_rpow_mul_suzukiRealBetaTail_nhdsLT_one hω hω'
  have hK : Tendsto (fun y : ℝ => (2 * Real.pi ^ ω / Real.Gamma ω) *
      (y ^ (2 - ω) * (1 + y) ^ (ω - 1)
        - ω * (y ^ (ω - 1) * ((1 - y) ^ (1 - ω) * suzukiRealBetaTail ω y))))
      (𝓝[<] (1 : ℝ))
      (𝓝 ((2 * Real.pi ^ ω / Real.Gamma ω) *
        ((1 : ℝ) * (2 : ℝ) ^ (ω - 1) - ω * ((1 : ℝ) * (0 : ℝ))))) :=
    ((hpow1.mul hpow2).sub ((hpow3.mul htail).const_mul ω)).const_mul _
  have hval : (2 * Real.pi ^ ω / Real.Gamma ω) *
      ((1 : ℝ) * (2 : ℝ) ^ (ω - 1) - ω * ((1 : ℝ) * (0 : ℝ)))
      = suzukiKernelConstantOne ω := by
    rw [← suzukiKernelConstantOne_eq hω]
    ring
  rw [hval] at hK
  refine hK.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) one_pos] with y hy
  have hy0 : (0 : ℝ) < y := hy.1
  have hy1 : y < 1 := hy.2
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have h1y' : (0 : ℝ) < 1 + y := by linarith
  have hne : ((1 : ℝ) - y) ^ (ω - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h1y _)
  have hsplit : ((1 : ℝ) - y ^ 2) ^ (ω - 1) = (1 - y) ^ (ω - 1) * (1 + y) ^ (ω - 1) := by
    rw [show (1 : ℝ) - y ^ 2 = (1 - y) * (1 + y) by ring, Real.mul_rpow h1y.le h1y'.le]
  have hinv : ((1 : ℝ) - y) ^ (1 - ω) = (((1 : ℝ) - y) ^ (ω - 1))⁻¹ := by
    rw [show (1 : ℝ) - ω = -(ω - 1) by ring, Real.rpow_neg h1y.le]
  rw [suzukiRealSourceG_apply hy0 hy1, hsplit, hinv]
  field_simp

/-! ## Endpoint expansion of the primitive -/

/-- **Divergence of the primitive at the origin.**  For `0 < ω < 1/2`,
`g_ω^{⟨1⟩}(x)/x^{ω-1} → -B_ω/(1/2-ω) < 0`. -/
theorem tendsto_suzukiRealSourceGOne_div_rpow_nhdsGT_zero {ω : ℝ} (hω : 0 < ω) (hω' : ω < 1 / 2) :
    Tendsto (fun x => suzukiRealSourceGOne ω x / x ^ (ω - 1)) (𝓝[>] (0 : ℝ))
      (𝓝 (-suzukiKernelConstantZero ω / (1 / 2 - ω))) := by
  have hω32 : ω < 3 / 2 := by linarith
  have hα : ω - 3 / 2 < -1 := by linarith
  have hint : ∀ x ∈ Ioo (0 : ℝ) 1, IntervalIntegrable (suzukiRealSourceGWeighted ω) volume x 1 :=
    fun x hx => intervalIntegrable_suzukiRealSourceGWeighted hω hω32 hx.1 hx.2
  have hlim : Tendsto (fun y => suzukiRealSourceGWeighted ω y / y ^ (ω - 3 / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (-suzukiKernelConstantZero ω)) := by
    refine (tendsto_suzukiRealSourceG_div_rpow_nhdsGT_zero hω hω32).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    have hne1 : y ^ (-(1 / 2) : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hy0 _)
    have hne2 : y ^ (ω - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hy0 _)
    have hsplit : y ^ (ω - 3 / 2) = y ^ (-(1 / 2) : ℝ) * y ^ (ω - 1) := by
      rw [← Real.rpow_add hy0]
      congr 1
      ring
    rw [suzukiRealSourceGWeighted, hsplit]
    field_simp
  have hmain := HTGeometry.tendsto_rpow_mul_intervalIntegral_nhdsGT_zero hα zero_lt_one hint hlim
  have hval : -(-suzukiKernelConstantZero ω) / (ω - 3 / 2 + 1)
      = -suzukiKernelConstantZero ω / (1 / 2 - ω) := by
    rw [show ω - 3 / 2 + 1 = -(1 / 2 - ω) by ring, div_neg, neg_neg, neg_div]
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with x hx
  have hx0 : (0 : ℝ) < x := hx.1
  have hne : x ^ (ω - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx0 _)
  have hpow : x ^ (-(ω - 3 / 2 + 1)) = x ^ (-(1 / 2) : ℝ) / x ^ (ω - 1) := by
    rw [← Real.rpow_sub hx0]
    congr 1
    ring
  rw [suzukiRealSourceGOne_eq_weighted hx0 hx.2, hpow]
  field_simp

/-- **Vanishing of the primitive at the support endpoint.**  `g_ω^{⟨1⟩}(x)/(1-x)^ω → A_ω/ω > 0`. -/
theorem tendsto_suzukiRealSourceGOne_div_rpow_nhdsLT_one {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    Tendsto (fun x => suzukiRealSourceGOne ω x / (1 - x) ^ ω) (𝓝[<] (1 : ℝ))
      (𝓝 (suzukiKernelConstantOne ω / ω)) := by
  have hβ : (-1 : ℝ) < ω - 1 := by linarith
  have hint : ∀ x ∈ Ioo (0 : ℝ) 1, IntervalIntegrable (suzukiRealSourceGWeighted ω) volume x 1 :=
    fun x hx => intervalIntegrable_suzukiRealSourceGWeighted hω hω' hx.1 hx.2
  have hxpow : Tendsto (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) 1 :=
      Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
    have hres := hc.tendsto
    rw [Real.one_rpow] at hres
    exact hres.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun y => suzukiRealSourceGWeighted ω y / (1 - y) ^ (ω - 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (suzukiKernelConstantOne ω)) := by
    have hprod := hxpow.mul (tendsto_suzukiRealSourceG_div_rpow_nhdsLT_one hω hω')
    rw [one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards with y
    rw [suzukiRealSourceGWeighted]
    ring
  have hmain := HTGeometry.tendsto_rpow_mul_intervalIntegral_nhdsLT hβ zero_lt_one hint hlim
  have hprod := hxpow.mul hmain
  rw [one_mul] at hprod
  have hval : suzukiKernelConstantOne ω / (ω - 1 + 1) = suzukiKernelConstantOne ω / ω := by
    congr 1
    ring
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) one_pos] with x hx
  have hx0 : (0 : ℝ) < x := hx.1
  have hx1 : x < 1 := hx.2
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have hne : ((1 : ℝ) - x) ^ ω ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h1x _)
  have hexp : -(ω - 1 + 1) = -ω := by ring
  rw [suzukiRealSourceGOne_eq_weighted hx0 hx1, hexp, Real.rpow_neg h1x.le]
  field_simp

/-! ## The forced sign change -/

/-- The primitive is strictly negative near the origin. -/
theorem exists_suzukiRealSourceGOne_neg {ω : ℝ} (hω : 0 < ω) (hω' : ω < 1 / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ x ∈ Ioo (0 : ℝ) ε, suzukiRealSourceGOne ω x < 0 := by
  have hneg : -suzukiKernelConstantZero ω / (1 / 2 - ω) < 0 := by
    have hB := suzukiKernelConstantZero_pos hω (by linarith)
    have hden : (0 : ℝ) < 1 / 2 - ω := by linarith
    exact div_neg_of_neg_of_pos (by linarith) hden
  have hev := (tendsto_suzukiRealSourceGOne_div_rpow_nhdsGT_zero hω hω').eventually_lt_const hneg
  have hev2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), suzukiRealSourceGOne ω x < 0 := by
    filter_upwards [hev, self_mem_nhdsWithin] with x hx hx0
    have hpos : (0 : ℝ) < x ^ (ω - 1) := Real.rpow_pos_of_pos hx0 _
    nlinarith [hx, hpos, div_lt_iff₀ hpos |>.1 (by simpa using hx)]
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev2
  refine ⟨min u 1, lt_min hu one_pos, min_le_right _ _, fun x hx => ?_⟩
  exact hsub ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩

/-- The primitive is strictly positive near the support endpoint. -/
theorem exists_suzukiRealSourceGOne_pos {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ x ∈ Ioo δ (1 : ℝ), 0 < suzukiRealSourceGOne ω x := by
  have hpos : 0 < suzukiKernelConstantOne ω / ω :=
    div_pos (suzukiKernelConstantOne_pos hω) hω
  have hev := (tendsto_suzukiRealSourceGOne_div_rpow_nhdsLT_one hω hω').eventually_const_lt hpos
  have hev2 : ∀ᶠ x in 𝓝[<] (1 : ℝ), 0 < suzukiRealSourceGOne ω x := by
    filter_upwards [hev, self_mem_nhdsWithin] with x hx hx1
    have h1x : (0 : ℝ) < 1 - x := by
      have : x < 1 := hx1
      linarith
    have hpow : (0 : ℝ) < (1 - x) ^ ω := Real.rpow_pos_of_pos h1x _
    nlinarith [hx, hpow, (lt_div_iff₀ hpow).1 (by simpa using hx)]
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev2
  refine ⟨max l (1 / 2), lt_of_lt_of_le (by norm_num) (le_max_right _ _),
    max_lt hl (by norm_num), fun x hx => ?_⟩
  exact hsub ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩

/-- **Forced sign change.**  In the RH-relevant range `0 < ω < 1/2` Suzuki's integrated
archimedean kernel takes both signs inside its own support. -/
theorem suzukiRealSourceGOne_sign_change {ω : ℝ} (hω : 0 < ω) (hω' : ω < 1 / 2) :
    ∃ x₁ ∈ Ioo (0 : ℝ) 1, ∃ x₂ ∈ Ioo (0 : ℝ) 1,
      suzukiRealSourceGOne ω x₁ < 0 ∧ 0 < suzukiRealSourceGOne ω x₂ := by
  obtain ⟨ε, hε, hε1, hneg⟩ := exists_suzukiRealSourceGOne_neg hω hω'
  obtain ⟨δ, hδ, hδ1, hpos⟩ := exists_suzukiRealSourceGOne_pos hω (by linarith)
  refine ⟨ε / 2, ⟨by linarith, by linarith⟩, (δ + 1) / 2, ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · exact hneg _ ⟨by linarith, by linarith⟩
  · exact hpos _ ⟨by linarith, by linarith⟩

/-- The same sign change for the complex source kernel. -/
theorem suzukiSourceGOne_sign_change {ω : ℝ} (hω : 0 < ω) (hω' : ω < 1 / 2) :
    ∃ x₁ ∈ Ioo (0 : ℝ) 1, ∃ x₂ ∈ Ioo (0 : ℝ) 1,
      (suzukiSourceGOne ω x₁).re < 0 ∧ 0 < (suzukiSourceGOne ω x₂).re := by
  obtain ⟨x₁, hx₁, x₂, hx₂, h1, h2⟩ := suzukiRealSourceGOne_sign_change hω hω'
  refine ⟨x₁, hx₁, x₂, hx₂, ?_, ?_⟩
  · rw [← ofReal_suzukiRealSourceGOne, Complex.ofReal_re]
    exact h1
  · rw [← ofReal_suzukiRealSourceGOne, Complex.ofReal_re]
    exact h2

end

end RHTower
