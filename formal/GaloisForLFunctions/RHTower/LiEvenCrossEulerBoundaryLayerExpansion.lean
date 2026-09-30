import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Second boundary layer of the two-exponential Euler model

This is ordinary real Taylor analysis of the explicit model. Its uniform model
orientation is independent of any real-order interpolation of actual Euler jets.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- The first two competing exponentials, with small correction parameter `e`. -/
def liEvenCrossEulerBoundaryModel (m b L H e u : ℝ) : ℝ :=
  m * (1 - Real.exp (L * u)) + b * e * Real.exp (H * u)

/-- First displacement of the model crossing. -/
def liEvenCrossEulerBoundaryFirstCorrection (m b L : ℝ) : ℝ := b / (m * L)

/-- Second displacement, retaining the quadratic interaction of both exponentials. -/
def liEvenCrossEulerBoundarySecondCorrection (m b L H : ℝ) : ℝ :=
  liEvenCrossEulerBoundaryFirstCorrection m b L ^ 2 * (H - L / 2)

private def boundaryLayerPath (m b L H c ell e : ℝ) : ℝ :=
  m * (1 - Real.exp (L * (c * e + ell * e ^ 2))) +
    b * e * Real.exp (H * (c * e + ell * e ^ 2))

private def boundaryLayerPathDeriv (m b L H c ell e : ℝ) : ℝ :=
  -m * Real.exp (L * (c * e + ell * e ^ 2)) * (L * (c + 2 * ell * e)) +
    b * Real.exp (H * (c * e + ell * e ^ 2)) +
    b * e * Real.exp (H * (c * e + ell * e ^ 2)) * (H * (c + 2 * ell * e))

private theorem boundaryLayer_hasDerivAt_displacement (c ell e : ℝ) :
    HasDerivAt (fun x : ℝ => c * x + ell * x ^ 2) (c + 2 * ell * e) e := by
  convert ((hasDerivAt_id e).const_mul c).add
    (((hasDerivAt_id e).pow 2).const_mul ell) using 1
  all_goals first | rfl | (simp; ring)

private theorem boundaryLayer_hasDerivAt_path (m b L H c ell e : ℝ) :
    HasDerivAt (boundaryLayerPath m b L H c ell)
      (boundaryLayerPathDeriv m b L H c ell e) e := by
  have hL := ((boundaryLayer_hasDerivAt_displacement c ell e).const_mul L).exp
  have hH := ((boundaryLayer_hasDerivAt_displacement c ell e).const_mul H).exp
  convert (((hasDerivAt_const e (1 : ℝ)).sub hL).const_mul m).add
    (((hasDerivAt_id e).const_mul b).mul hH) using 1
  all_goals first | rfl | (simp only [boundaryLayerPathDeriv, id_eq]; ring)

private theorem boundaryLayer_hasDerivAt_pathDeriv_zero (m b L H c ell : ℝ) :
    HasDerivAt (boundaryLayerPathDeriv m b L H c ell)
      (-m * L ^ 2 * c ^ 2 - 2 * m * L * ell + 2 * b * H * c) 0 := by
  have hL := ((boundaryLayer_hasDerivAt_displacement c ell 0).const_mul L).exp
  have hH := ((boundaryLayer_hasDerivAt_displacement c ell 0).const_mul H).exp
  have hp : HasDerivAt (fun x : ℝ => c + 2 * ell * x) (2 * ell) 0 := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id 0).const_mul (2 * ell)).const_add c
  convert (((hL.const_mul (-m)).mul (hp.const_mul L)).add (hH.const_mul b)).add
    ((((hasDerivAt_id 0).const_mul b).mul hH).mul (hp.const_mul H)) using 1
  all_goals first | rfl | (simp; ring)

private theorem boundaryLayer_path_div_sq_tendsto
    (m b L H c ell : ℝ) (hc : b = m * L * c) :
    Tendsto (fun e => boundaryLayerPath m b L H c ell e / e ^ 2)
      (𝓝[>] 0) (𝓝 (m * L * (c ^ 2 * (H - L / 2) - ell))) := by
  have hcont : ContDiff ℝ 2 (boundaryLayerPath m b L H c ell) := by
    unfold boundaryLayerPath
    fun_prop
  have hder : deriv (boundaryLayerPath m b L H c ell) =
      boundaryLayerPathDeriv m b L H c ell :=
    funext fun e => (boundaryLayer_hasDerivAt_path m b L H c ell e).deriv
  have h0 : boundaryLayerPath m b L H c ell 0 = 0 := by simp [boundaryLayerPath]
  have h1 : iteratedDeriv 1 (boundaryLayerPath m b L H c ell) 0 = 0 := by
    rw [iteratedDeriv_one, hder]
    simp only [boundaryLayerPathDeriv, mul_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, Real.exp_zero, mul_one, zero_mul]
    rw [hc]
    ring
  have h2 : iteratedDeriv 2 (boundaryLayerPath m b L H c ell) 0 =
      2 * (m * L * (c ^ 2 * (H - L / 2) - ell)) := by
    rw [iteratedDeriv_succ', iteratedDeriv_one, hder,
      (boundaryLayer_hasDerivAt_pathDeriv_zero m b L H c ell).deriv, hc]
    ring
  have ht := Real.taylor_tendsto (f := boundaryLayerPath m b L H c ell)
    (x₀ := 0) (n := 2) (s := univ) convex_univ (mem_univ 0) hcont.contDiffOn
  have htaylor (e : ℝ) :
      taylorWithinEval (boundaryLayerPath m b L H c ell) 2 univ 0 e =
        (m * L * (c ^ 2 * (H - L / 2) - ell)) * e ^ 2 := by
    simp [taylorWithinEval_succ, iteratedDerivWithin_univ, h0, h1, h2, smul_eq_mul]
    ring
  simp only [nhdsWithin_univ, sub_zero] at ht
  have ht' : Tendsto (fun e =>
      (boundaryLayerPath m b L H c ell e -
        taylorWithinEval (boundaryLayerPath m b L H c ell) 2 univ 0 e) / e ^ 2)
      (𝓝[>] 0) (𝓝 0) := ht.mono_left nhdsWithin_le_nhds
  have hz := ht'.add_const (m * L * (c ^ 2 * (H - L / 2) - ell))
  apply (show Tendsto (fun e =>
      (boundaryLayerPath m b L H c ell e -
        taylorWithinEval (boundaryLayerPath m b L H c ell) 2 univ 0 e) / e ^ 2 +
          m * L * (c ^ 2 * (H - L / 2) - ell))
      (𝓝[>] 0) (𝓝 (m * L * (c ^ 2 * (H - L / 2) - ell))) from
        by simpa only [zero_add] using hz).congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  have he0 : e ≠ 0 := ne_of_gt he
  rw [htaylor]
  field_simp
  ring

/-- Exact fixed-offset second-layer limit; `H` and `b` may have either sign. -/
theorem liEvenCrossEulerBoundaryModel_second_layer_tendsto
    (m b L H ell : ℝ) (hm : 0 < m) (hL : 0 < L) :
    Tendsto (fun e => liEvenCrossEulerBoundaryModel m b L H e
      (liEvenCrossEulerBoundaryFirstCorrection m b L * e + ell * e ^ 2) / e ^ 2)
      (𝓝[>] 0) (𝓝 (m * L * (liEvenCrossEulerBoundarySecondCorrection m b L H - ell))) := by
  have hc : b = m * L * liEvenCrossEulerBoundaryFirstCorrection m b L := by
    unfold liEvenCrossEulerBoundaryFirstCorrection
    field_simp [hm.ne', hL.ne']
  simpa only [liEvenCrossEulerBoundaryModel, liEvenCrossEulerBoundarySecondCorrection,
    boundaryLayerPath] using boundaryLayer_path_div_sq_tendsto
      m b L H (liEvenCrossEulerBoundaryFirstCorrection m b L) ell hc

/-- Strict quadratic margins at the two second-layer endpoints. -/
theorem liEvenCrossEulerBoundaryModel_eventually_second_layer_sides
    (m b L H : ℝ) (hm : 0 < m) (hL : 0 < L) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      (m * L * δ / 2) * e ^ 2 < liEvenCrossEulerBoundaryModel m b L H e
        (liEvenCrossEulerBoundaryFirstCorrection m b L * e +
          (liEvenCrossEulerBoundarySecondCorrection m b L H - δ) * e ^ 2) ∧
      liEvenCrossEulerBoundaryModel m b L H e
        (liEvenCrossEulerBoundaryFirstCorrection m b L * e +
          (liEvenCrossEulerBoundarySecondCorrection m b L H + δ) * e ^ 2) <
        -(m * L * δ / 2) * e ^ 2 := by
  have hpos := liEvenCrossEulerBoundaryModel_second_layer_tendsto m b L H
    (liEvenCrossEulerBoundarySecondCorrection m b L H - δ) hm hL
  have hneg := liEvenCrossEulerBoundaryModel_second_layer_tendsto m b L H
    (liEvenCrossEulerBoundarySecondCorrection m b L H + δ) hm hL
  have hscale : 0 < m * L * δ := mul_pos (mul_pos hm hL) hδ
  have hp := hpos.eventually_const_lt
    (show m * L * δ / 2 < m * L *
      (liEvenCrossEulerBoundarySecondCorrection m b L H -
        (liEvenCrossEulerBoundarySecondCorrection m b L H - δ)) by nlinarith)
  have hn := hneg.eventually_lt_const
    (show m * L * (liEvenCrossEulerBoundarySecondCorrection m b L H -
      (liEvenCrossEulerBoundarySecondCorrection m b L H + δ)) <
        -(m * L * δ / 2) by nlinarith)
  filter_upwards [hp, hn, self_mem_nhdsWithin] with e hep hen he
  exact ⟨(lt_div_iff₀ (pow_pos he 2)).mp hep,
    (div_lt_iff₀ (pow_pos he 2)).mp hen⟩

private theorem boundaryLayer_hasDerivAt_model (m b L H e u : ℝ) :
    HasDerivAt (liEvenCrossEulerBoundaryModel m b L H e)
      (-m * L * Real.exp (L * u) + b * e * H * Real.exp (H * u)) u := by
  have hL := ((hasDerivAt_id u).const_mul L).exp
  have hH := ((hasDerivAt_id u).const_mul H).exp
  convert (((hasDerivAt_const u (1 : ℝ)).sub hL).const_mul m).add
    (hH.const_mul (b * e)) using 1
  all_goals first | rfl | (simp only [id_eq]; ring)

/-- A uniform negative derivative on the model interval used by integer rounding. -/
theorem liEvenCrossEulerBoundaryModel_deriv_le_neg_half
    (m b L H e : ℝ) (hm : 0 < m) (hb : 0 < b) (hL : 0 < L) (hH : 0 < H)
    (he : 0 ≤ e) (hsmall : e ≤ m * L / (2 * b * H * Real.exp (2 * H)))
    {u : ℝ} (hu : u ∈ Icc 0 2) :
    deriv (liEvenCrossEulerBoundaryModel m b L H e) u ≤ -(m * L / 2) := by
  rw [(boundaryLayer_hasDerivAt_model m b L H e u).deriv]
  have hE1 : 1 ≤ Real.exp (L * u) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (mul_nonneg hL.le hu.1)
  have hE2 : Real.exp (H * u) ≤ Real.exp (2 * H) :=
    Real.exp_le_exp.mpr (by nlinarith [hu.2])
  have hden : 0 < 2 * b * H * Real.exp (2 * H) := by positivity
  have hscale := (le_div_iff₀ hden).mp hsmall
  have hfirst : -m * L * Real.exp (L * u) ≤ -(m * L) := by
    nlinarith [mul_pos hm hL]
  have hsecond : b * e * H * Real.exp (H * u) ≤ b * e * H * Real.exp (2 * H) :=
    mul_le_mul_of_nonneg_left hE2 (by positivity)
  nlinarith only [hfirst, hsecond, hscale]

/-- Small positive correction makes the explicit model strictly decrease on `0 ≤ u ≤ 2`. -/
theorem liEvenCrossEulerBoundaryModel_strictAntiOn_Icc_zero_two
    (m b L H e : ℝ) (hm : 0 < m) (hb : 0 < b) (hL : 0 < L) (hH : 0 < H)
    (he : 0 ≤ e) (hsmall : e ≤ m * L / (2 * b * H * Real.exp (2 * H))) :
    StrictAntiOn (liEvenCrossEulerBoundaryModel m b L H e) (Icc 0 2) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 2)
  · unfold liEvenCrossEulerBoundaryModel
    fun_prop
  · intro u hu
    exact (liEvenCrossEulerBoundaryModel_deriv_le_neg_half m b L H e
      hm hb hL hH he hsmall (interior_subset hu)).trans_lt (by nlinarith [mul_pos hm hL])

end

end RHTower
