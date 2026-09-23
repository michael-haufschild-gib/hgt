import GaloisForLFunctions.RHTower.CauchyKernelTotality
import GaloisForLFunctions.RHTower.SuzukiFGammaOrthonormal
import GaloisForLFunctions.RHTower.SuzukiDslopeBounded
import GaloisForLFunctions.RHTower.SuzukiDeBrangesSpace
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCauchyVanishing

noncomputable section

/-!
# `F_γ` lies in the model space

Proposition 4.1 asserts that the normalized vectors `F_γ` form an orthonormal system *inside* the
model space `K(Θ_ξ)`.  Orthonormality is a statement about `L²(ℝ)`; the containment is proved here.

Two facts are needed.  First, `F_γ` is a Hardy function.  Under the Riemann hypothesis `A/E` is a
bounded holomorphic function of the closed upper half-plane, so `F_γ` is holomorphic there and
decays like `1/|z|`; the integrand `F_γ(z)/(z-w)` with `w` below the axis therefore decays
quadratically, and its contour integral over the closed upper half-plane vanishes.  Because the
Cauchy kernels below the axis are total in the orthogonal complement of `H²`, this places `F_γ`
in `H²`.

Second, `Θ conj(F_γ) = -F_γ` pointwise on the axis: the inner function `Θ = E♯/E` cancels the
conjugated denominator of `F_γ`, and `A` is real on the axis.  Hence `Θ conj(F_γ)` is a Hardy
function too, which is the second clause of `K(Θ) = H² ∩ (Θ H²)^⊥`.  In particular `F_γ` is an
eigenvector of the Clark conjugation with eigenvalue `-1`.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem norm_suzukiFGammaFun_le (hRH : RiemannHypothesis) {γ : ℝ} (m : ℕ)
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) {z : ℂ} (hz : 0 ≤ z.im) (hne : z ≠ ((γ : ℝ) : ℂ)) :
    ‖suzukiFGammaFun γ m z‖
      ≤ Real.sqrt ((m : ℝ) / Real.pi) / ‖z - ((γ : ℝ) : ℂ)‖ := by
  have hd := norm_dslope_suzukiHalfInner_le_inv hRH hγ hz hne
  rw [suzukiFGammaFun, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt ((m : ℝ) / Real.pi) * ‖dslope suzukiHalfInner ((γ : ℝ) : ℂ) z‖
      ≤ Real.sqrt ((m : ℝ) / Real.pi) * (1 / ‖z - ((γ : ℝ) : ℂ)‖) := by
        exact mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _)
    _ = Real.sqrt ((m : ℝ) / Real.pi) / ‖z - ((γ : ℝ) : ℂ)‖ := by
        rw [mul_one_div]

/-- **The Cauchy transform of `F_γ` vanishes below the axis.**  Under the Riemann hypothesis `F_γ`
is holomorphic on the closed upper half-plane and decays there like `1/|z|`, so the integrand
`F_γ(z)/(z-w)` decays quadratically and the closed-contour theorem applies. -/
theorem integral_suzukiFGammaFun_div_eq_zero (hRH : RiemannHypothesis) {γ : ℝ} (m : ℕ)
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) {w : ℂ} (hw : w.im < 0) :
    (∫ x : ℝ, suzukiFGammaFun γ m ((x : ℝ) : ℂ) / (((x : ℝ) : ℂ) - w)) = 0 := by
  set c : ℝ := Real.sqrt ((m : ℝ) / Real.pi) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  set R : ℝ := 2 * (‖((γ : ℝ) : ℂ)‖ + ‖w‖) + 1 with hR
  have hR0 : 0 < R := by positivity
  refine integral_eq_zero_of_upperHalfPlane_farDecay
    (u := fun z : ℂ => suzukiFGammaFun γ m z / (z - w)) (M := 4 * c) (R := R) ?_ hR0 ?_
  · intro z hz
    have hzw : z - w ≠ 0 := by
      intro h
      have : z = w := sub_eq_zero.mp h
      rw [this] at hz
      linarith
    have hF : DifferentiableAt ℂ (fun z : ℂ => suzukiFGammaFun γ m z) z := by
      simp only [suzukiFGammaFun]
      exact ((differentiableAt_dslope_suzukiHalfInner_of_rh hRH hγ hz).const_mul I).const_mul _
    exact hF.div ((differentiableAt_id).sub_const w) hzw
  · intro z hz hzR
    have hzn : 0 < ‖z‖ := lt_of_lt_of_le hR0 hzR
    have hγhalf : ‖((γ : ℝ) : ℂ)‖ ≤ ‖z‖ / 2 := by
      have : 0 ≤ ‖w‖ := norm_nonneg _
      rw [hR] at hzR
      linarith
    have hwhalf : ‖w‖ ≤ ‖z‖ / 2 := by
      have : 0 ≤ ‖((γ : ℝ) : ℂ)‖ := norm_nonneg _
      rw [hR] at hzR
      linarith
    have hzγ : ‖z‖ / 2 ≤ ‖z - ((γ : ℝ) : ℂ)‖ := by
      have h := norm_sub_norm_le z ((γ : ℝ) : ℂ)
      linarith
    have hzw : ‖z‖ / 2 ≤ ‖z - w‖ := by
      have h := norm_sub_norm_le z w
      linarith
    have hhalf : 0 < ‖z‖ / 2 := by linarith
    have hne : z ≠ ((γ : ℝ) : ℂ) := by
      intro h
      rw [h] at hzn hzγ
      rw [sub_self, norm_zero] at hzγ
      linarith
    calc ‖suzukiFGammaFun γ m z / (z - w)‖
        = ‖suzukiFGammaFun γ m z‖ / ‖z - w‖ := norm_div _ _
      _ ≤ (c / (‖z‖ / 2)) / (‖z‖ / 2) := by
          gcongr
          exact le_trans (norm_suzukiFGammaFun_le hRH m hγ hz hne) (by gcongr)
      _ = 4 * c / ‖z‖ ^ (2 : ℕ) := by
          field_simp
          ring

/-- **`F_γ` is a Hardy function.** -/
theorem suzukiFGammaLp_mem_hardyL2 (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞)) (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    suzukiFGammaLp hRH hm hord hγ ∈ hardyL2 := by
  refine mem_hardyL2_of_cauchyTransform_eq_zero ?_
  intro w hw
  have hrw : (∫ x : ℝ, ((suzukiFGammaLp hRH hm hord hγ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
        / (((x : ℝ) : ℂ) - w))
      = ∫ x : ℝ, suzukiFGammaFun γ m ((x : ℝ) : ℂ) / (((x : ℝ) : ℂ) - w) := by
    refine MeasureTheory.integral_congr_ae ?_
    simp only [suzukiFGammaLp]
    filter_upwards [(memLp_suzukiFGammaFun hRH hm hord hγ).coeFn_toLp] with x h1
    rw [h1]
  rw [hrw]
  exact integral_suzukiFGammaFun_div_eq_zero hRH m hγ hw

/-- The inner function reflects `F_γ` to its own negative: `Θ conj(F_γ) = -F_γ` on the axis. -/
theorem suzukiThetaSymbol_mul_conj_suzukiFGammaFun {γ : ℝ} (m : ℕ)
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) {x : ℝ} (hx : x ≠ γ)
    (hE : xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) ≠ 0) :
    suzukiThetaSymbol x * (starRingEnd ℂ) (suzukiFGammaFun γ m ((x : ℝ) : ℂ))
      = -suzukiFGammaFun γ m ((x : ℝ) : ℂ) := by
  have hxne : ((x : ℝ) : ℂ) ≠ ((γ : ℝ) : ℂ) := by simpa using hx
  have hsub : ((x : ℝ) : ℂ) - ((γ : ℝ) : ℂ) ≠ 0 := sub_ne_zero.mpr hxne
  have hEc : (starRingEnd ℂ) (xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) ≠ 0 := by
    simpa using hE
  rw [suzukiThetaSymbol, if_neg hE, xiHedenmalmDeBrangesESharp_ofReal_eq_conj]
  simp only [suzukiFGammaFun, dslope_suzukiHalfInner_apply hγ hxne, suzukiHalfInner,
    map_mul, map_div₀, map_sub, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_eq_iff_im.mpr (XiC_ofReal_im x)]
  field_simp

theorem coeFn_suzukiFGammaLp (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞)) (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    ((suzukiFGammaLp hRH hm hord hγ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun x : ℝ => suzukiFGammaFun γ m ((x : ℝ) : ℂ) := by
  simp only [suzukiFGammaLp]
  exact (memLp_suzukiFGammaFun hRH hm hord hγ).coeFn_toLp

/-- **`F_γ` is an eigenvector of the Clark conjugation.**  Multiplication by the inner function
turns the conjugate of `F_γ` back into `-F_γ`. -/
theorem thetaMul_star_suzukiFGammaLp (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞)) (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    thetaMul (star (suzukiFGammaLp hRH hm hord hγ)) = -(suzukiFGammaLp hRH hm hord hγ) := by
  have hnull : volume ({γ} : Set ℝ) = 0 := by simp
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [thetaMul_coeFn (star (suzukiFGammaLp hRH hm hord hγ)),
    MeasureTheory.Lp.coeFn_star (suzukiFGammaLp hRH hm hord hγ),
    coeFn_suzukiFGammaLp hRH hm hord hγ,
    MeasureTheory.Lp.coeFn_neg (suzukiFGammaLp hRH hm hord hγ),
    ae_xiHedenmalmDeBrangesE_ofReal_ne_zero,
    MeasureTheory.compl_mem_ae_iff.mpr hnull] with x k1 k2 k3 k4 hE hxγ
  have hx : x ≠ γ := fun h => hxγ (by simp [h])
  rw [k1, k2, Pi.star_apply, k3, k4, Pi.neg_apply, k3]
  exact suzukiThetaSymbol_mul_conj_suzukiFGammaFun m hγ hx hE

/-- **Proposition 4.1, containment.**  `F_γ` belongs to the model space `K(Θ_ξ)`. -/
theorem suzukiFGammaLp_mem_suzukiModelSpace (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞)) (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    suzukiFGammaLp hRH hm hord hγ ∈ suzukiModelSpace := by
  rw [mem_suzukiModelSpace_iff_conj]
  refine ⟨suzukiFGammaLp_mem_hardyL2 hRH hm hord hγ, ?_⟩
  rw [thetaMul_star_suzukiFGammaLp]
  exact Submodule.neg_mem _ (suzukiFGammaLp_mem_hardyL2 hRH hm hord hγ)


end RHTower
