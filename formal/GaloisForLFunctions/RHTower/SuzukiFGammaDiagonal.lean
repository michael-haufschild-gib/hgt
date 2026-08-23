import GaloisForLFunctions.RHTower.SuzukiFGammaOffDiagonal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The diagonal normalization of Suzuki's family `F_γ`

The squared norm of `F_γ` is `(m/π)` times `∫ |A/E|² / (x-γ)²`, so orthonormality needs that
integral to be `π/m`.  Unlike the off-diagonal case the integrand `(A/E)/(z-γ)²` has a genuine
simple pole at `γ`, with residue `(A/E)'(γ) = -i/m`.

Rather than indent a contour, this module subtracts an explicit comparison term
`(1/m) / (z - γ + i)` whose pole sits at `γ - i`, strictly below the axis, and whose value at
`γ` matches the residue.  The difference has a removable singularity at `γ`, so its divided
slope is holomorphic on the closed upper half-plane and decays like `‖z‖^{-2}`; Cauchy's
theorem kills its integral.  Taking real parts turns the comparison term into the Cauchy kernel
`(1/m) / ((x-γ)² + 1)`, whose integral is `π/m`, and turns the main term into the boundary
energy.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

/-- The comparison term that cancels the simple pole of `(A/E)/(z-γ)^2` at `γ`.  Its own pole
sits at `γ - i`, strictly below the axis. -/
def suzukiDiagComparison (γ : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  dslope suzukiHalfInner γ z - (1 / (m : ℂ)) / (z - γ + I)

theorem suzukiDiagComparison_self {γ : ℂ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC γ = (m : ℕ∞)) :
    suzukiDiagComparison γ m γ = 0 := by
  have hd : deriv suzukiHalfInner γ = -I / (m : ℂ) :=
    (hasDerivAt_suzukiHalfInner hm hord).deriv
  have hI : (1 / (m : ℂ)) / I = -I / (m : ℂ) := by
    rw [div_eq_mul_inv, Complex.inv_I]
    ring
  rw [suzukiDiagComparison, dslope_same, hd, sub_self, zero_add, hI, sub_self]

theorem sub_add_I_ne_zero {γ : ℂ} (hγim : γ.im = 0) {z : ℂ} (hz : 0 ≤ z.im) :
    z - γ + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.add_im, Complex.sub_im, Complex.I_im, hγim, sub_zero,
    Complex.zero_im] at this
  linarith

theorem eventually_differentiableAt_dslope_suzukiHalfInner {γ : ℂ} (hγ : XiC γ = 0) :
    ∀ᶠ z in 𝓝 γ, DifferentiableAt ℂ (dslope suzukiHalfInner γ) z := by
  obtain ⟨g, hg, hfac, hnbhd⟩ := exists_localFactor_suzukiHalfInner_of_XiC_zero hγ
  filter_upwards [hnbhd] with z hzd
  rcases eq_or_ne z γ with rfl | hne
  · exact differentiableAt_dslope_of_localFactor hg hfac
  · exact (differentiableAt_dslope_of_ne hne).mpr hzd

theorem differentiableAt_suzukiDiagComparison {γ : ℂ} {m : ℕ} {z : ℂ}
    (hd : DifferentiableAt ℂ (dslope suzukiHalfInner γ) z) (hden : z - γ + I ≠ 0) :
    DifferentiableAt ℂ (suzukiDiagComparison γ m) z :=
  hd.sub ((differentiableAt_const _).div
    ((differentiableAt_id.sub_const γ).add_const I) hden)

theorem differentiableAt_dslope_suzukiDiagComparison (hRH : RiemannHypothesis) {γ : ℂ}
    (hγ : XiC γ = 0) (hγim : γ.im = 0) (m : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    DifferentiableAt ℂ (dslope (suzukiDiagComparison γ m) γ) z := by
  rcases eq_or_ne z γ with rfl | hne
  · refine differentiableAt_dslope_of_eventually_differentiableAt ?_
    have hopen : IsOpen {w : ℂ | w - z + I ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    have hmem : z ∈ {w : ℂ | w - z + I ≠ 0} := by
      simp [Complex.I_ne_zero]
    filter_upwards [eventually_differentiableAt_dslope_suzukiHalfInner hγ,
      hopen.mem_nhds hmem] with w hw hwden
    exact differentiableAt_suzukiDiagComparison hw hwden
  · exact (differentiableAt_dslope_of_ne hne).mpr
      (differentiableAt_suzukiDiagComparison
        (differentiableAt_dslope_suzukiHalfInner_of_rh hRH hγ hz)
        (sub_add_I_ne_zero hγim hz))

theorem dslope_suzukiDiagComparison_apply {γ : ℂ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC γ = (m : ℕ∞)) (hγ : XiC γ = 0) {z : ℂ} (hzγ : z ≠ γ)
    (hden : z - γ + I ≠ 0) :
    dslope (suzukiDiagComparison γ m) γ z
      = suzukiHalfInner z / (z - γ) ^ 2 - (1 / (m : ℂ)) / ((z - γ) * (z - γ + I)) := by
  have hsub : z - γ ≠ 0 := sub_ne_zero.mpr hzγ
  rw [dslope_of_ne _ hzγ, slope_def_field, suzukiDiagComparison_self hm hord, sub_zero,
    suzukiDiagComparison, dslope_suzukiHalfInner_apply hγ hzγ]
  field_simp

theorem norm_dslope_suzukiDiagComparison_le (hRH : RiemannHypothesis) {γ : ℂ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC γ = (m : ℕ∞)) (hγ : XiC γ = 0) (hγim : γ.im = 0)
    {z : ℂ} (hz : 0 ≤ z.im) (hR : 2 * (‖γ‖ + 2) ≤ ‖z‖) :
    ‖dslope (suzukiDiagComparison γ m) γ z‖ ≤ 8 / ‖z‖ ^ 2 := by
  have hzpos : 0 < ‖z‖ := by
    have h : (0 : ℝ) < 2 * (‖γ‖ + 2) := by positivity
    linarith
  have hγhalf : ‖γ‖ + 1 ≤ ‖z‖ / 2 := by linarith
  have hgz : ‖z‖ / 2 ≤ ‖z - γ‖ := by
    have h := norm_sub_norm_le z γ
    linarith
  have hzγ : z ≠ γ := by
    intro h
    rw [h] at hzpos hgz
    rw [sub_self, norm_zero] at hgz
    linarith
  have hden : z - γ + I ≠ 0 := sub_add_I_ne_zero hγim hz
  have hdz : ‖z‖ / 2 ≤ ‖z - γ + I‖ := by
    have h1 : ‖z - γ‖ - ‖(-I : ℂ)‖ ≤ ‖z - γ + I‖ := by
      have h := norm_sub_norm_le (z - γ) (-I)
      simpa [sub_neg_eq_add] using h
    rw [norm_neg, Complex.norm_I] at h1
    have h2 := norm_sub_norm_le z γ
    linarith
  have hmC : ((m : ℂ)) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hmnorm : ‖(1 / (m : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_one, Complex.norm_natCast]
    rw [div_le_one (by positivity)]
    exact_mod_cast hm
  have hhalf : (0 : ℝ) < ‖z‖ / 2 := by linarith
  -- bound the comparison itself
  have hC : ‖suzukiDiagComparison γ m z‖ ≤ 4 / ‖z‖ := by
    rw [suzukiDiagComparison, dslope_suzukiHalfInner_apply hγ hzγ]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_div, norm_div]
    have hb1 : ‖suzukiHalfInner z‖ / ‖z - γ‖ ≤ 1 / (‖z‖ / 2) := by
      gcongr
      exact norm_suzukiHalfInner_le_one_of_rh hRH hz
    have hb2 : ‖(1 / (m : ℂ))‖ / ‖z - γ + I‖ ≤ 1 / (‖z‖ / 2) := by
      gcongr
    have : (1 : ℝ) / (‖z‖ / 2) + 1 / (‖z‖ / 2) = 4 / ‖z‖ := by field_simp; ring
    linarith
  have hval : dslope (suzukiDiagComparison γ m) γ z = suzukiDiagComparison γ m z / (z - γ) := by
    rw [dslope_of_ne _ hzγ, slope_def_field, suzukiDiagComparison_self hm hord, sub_zero]
  rw [hval, norm_div]
  calc ‖suzukiDiagComparison γ m z‖ / ‖z - γ‖ ≤ (4 / ‖z‖) / (‖z‖ / 2) := by gcongr
    _ = 8 / ‖z‖ ^ 2 := by field_simp; ring

theorem integral_dslope_suzukiDiagComparison_eq_zero (hRH : RiemannHypothesis) {γ : ℂ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC γ = (m : ℕ∞)) (hγ : XiC γ = 0) (hγim : γ.im = 0) :
    (∫ x : ℝ, dslope (suzukiDiagComparison γ m) γ ((x : ℝ) : ℂ)) = 0 :=
  integral_eq_zero_of_upperHalfPlane_farDecay (M := 8) (R := 2 * (‖γ‖ + 2))
    (fun z hz => differentiableAt_dslope_suzukiDiagComparison hRH hγ hγim m hz)
    (by positivity)
    (fun z hz hR => norm_dslope_suzukiDiagComparison_le hRH hm hord hγ hγim hz hR)

theorem integrable_dslope_suzukiDiagComparison (hRH : RiemannHypothesis) {γ : ℂ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC γ = (m : ℕ∞)) (hγ : XiC γ = 0) (hγim : γ.im = 0) :
    Integrable (fun x : ℝ => dslope (suzukiDiagComparison γ m) γ ((x : ℝ) : ℂ)) :=
  integrable_ofReal_of_farDecay (M := 8) (R := 2 * (‖γ‖ + 2))
    (fun z hz => differentiableAt_dslope_suzukiDiagComparison hRH hγ hγim m hz)
    (by positivity)
    (fun z hz hR => norm_dslope_suzukiDiagComparison_le hRH hm hord hγ hγim hz hR)

/-- The real part of the comparison term on the real axis: the pole contribution is a Cauchy
kernel. -/
theorem re_ofReal_div_mul_add_I (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    (((c : ℝ) : ℂ) / (((s : ℝ) : ℂ) * (((s : ℝ) : ℂ) + I))).re = c / (s ^ 2 + 1) := by
  have hw : (((s : ℝ) : ℂ) * (((s : ℝ) : ℂ) + I)).re = s ^ 2 := by
    simp [Complex.mul_re]
    ring
  have hw2 : (((s : ℝ) : ℂ) * (((s : ℝ) : ℂ) + I)).im = s := by
    simp [Complex.mul_im]
  have hns : Complex.normSq (((s : ℝ) : ℂ) * (((s : ℝ) : ℂ) + I)) = s ^ 2 * (s ^ 2 + 1) := by
    rw [Complex.normSq_apply, hw, hw2]
    ring
  rw [Complex.div_re, hw, hw2, hns, Complex.ofReal_re, Complex.ofReal_im]
  have hs2 : (s : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hs3 : (s : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem re_dslope_suzukiDiagComparison_ofReal {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞)) (hγ : XiC ((γ : ℝ) : ℂ) = 0)
    {x : ℝ} (hx : x ≠ γ) :
    (dslope (suzukiDiagComparison ((γ : ℝ) : ℂ) m) ((γ : ℝ) : ℂ) ((x : ℝ) : ℂ)).re
      = ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ 2 / (x - γ) ^ 2
        - (1 / (m : ℝ)) / ((x - γ) ^ 2 + 1) := by
  have hxγ : ((x : ℝ) : ℂ) ≠ ((γ : ℝ) : ℂ) := by
    simpa using hx
  have hden : ((x : ℝ) : ℂ) - ((γ : ℝ) : ℂ) + I ≠ 0 :=
    sub_add_I_ne_zero (by simp) (by simp)
  have hsne : (x - γ) ≠ 0 := sub_ne_zero.mpr hx
  rw [dslope_suzukiDiagComparison_apply hm hord hγ hxγ hden, Complex.sub_re]
  congr 1
  · have hc : (((x : ℝ) : ℂ) - ((γ : ℝ) : ℂ)) ^ 2 = (((x - γ) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hc, div_ofReal_re, ← norm_sq_suzukiHalfInner_ofReal x]
  · have hs : ((x : ℝ) : ℂ) - ((γ : ℝ) : ℂ) = (((x - γ : ℝ)) : ℂ) := by push_cast; ring
    have hmR : (m : ℝ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hnum : (1 / (m : ℂ)) = (((1 / (m : ℝ) : ℝ)) : ℂ) := by push_cast; ring
    rw [hs, hnum, re_ofReal_div_mul_add_I (1 / (m : ℝ)) hsne]

theorem integrable_and_integral_normSq_suzukiHalfInner_div_sq (hRH : RiemannHypothesis)
    {γ : ℝ} {m : ℕ} (hm : 0 < m) (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞))
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    Integrable (fun x : ℝ => ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ 2 / (x - γ) ^ 2) ∧
      (∫ x : ℝ, ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ 2 / (x - γ) ^ 2) = Real.pi / (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hγim : ((γ : ℝ) : ℂ).im = 0 := by simp
  have hUint := integrable_dslope_suzukiDiagComparison hRH hm hord hγ hγim
  have hUzero := integral_dslope_suzukiDiagComparison_eq_zero hRH hm hord hγ hγim
  set F : ℝ → ℝ := fun x =>
    (dslope (suzukiDiagComparison ((γ : ℝ) : ℂ) m) ((γ : ℝ) : ℂ) ((x : ℝ) : ℂ)).re with hF
  set G : ℝ → ℝ := fun x => (1 / (m : ℝ)) / ((x - γ) ^ 2 + 1) with hG
  have hFint : Integrable F := hUint.re
  have hGint : Integrable G := by
    have hbase : Integrable (fun x : ℝ => (1 + (x - γ) ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.comp_sub_right γ
    refine (hbase.const_mul (1 / (m : ℝ))).congr ?_
    filter_upwards with x
    simp only [hG]
    rw [div_eq_mul_inv]
    ring_nf
  have hFzero : (∫ x : ℝ, F x) = 0 := by
    have hcomm := Complex.reCLM.integral_comp_comm hUint
    rw [hUzero] at hcomm
    simpa [hF] using hcomm
  have hnull : volume ({γ} : Set ℝ) = 0 := by simp
  have hae : (fun x : ℝ => ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ 2 / (x - γ) ^ 2)
      =ᵐ[volume] fun x => F x + G x := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx
    have hxne : x ≠ γ := fun h => hx (by simp [h])
    rw [hF, hG]
    have := re_dslope_suzukiDiagComparison_ofReal hm hord hγ hxne
    simp only at this ⊢
    rw [this]
    ring
  refine ⟨(hFint.add hGint).congr hae.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_add hFint hGint, hFzero,
    zero_add]
  have hGval : (∫ x : ℝ, G x) = Real.pi / (m : ℝ) := by
    have h1 : (fun x : ℝ => G x) = fun x : ℝ => (1 / (m : ℝ)) * (1 + (x - γ) ^ 2)⁻¹ := by
      funext x
      simp only [hG]
      rw [div_eq_mul_inv]
      ring_nf
    rw [h1, MeasureTheory.integral_const_mul]
    have h2 : (∫ x : ℝ, (1 + (x - γ) ^ 2)⁻¹) = Real.pi := by
      rw [MeasureTheory.integral_sub_right_eq_self (fun x : ℝ => (1 + x ^ 2)⁻¹) γ]
      exact integral_univ_inv_one_add_sq
    rw [h2]
    field_simp
  exact hGval


theorem integrable_normSq_suzukiHalfInner_div_sq (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞))
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    Integrable (fun x : ℝ => ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ 2 / (x - γ) ^ 2) :=
  (integrable_and_integral_normSq_suzukiHalfInner_div_sq hRH hm hord hγ).1

/-- **The diagonal norm.**  At a zero of `A` of order `m` the boundary energy integrates to
`π / m` against `(x - γ)^{-2}`. -/
theorem integral_normSq_suzukiHalfInner_div_sq (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞))
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    (∫ x : ℝ, ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ 2 / (x - γ) ^ 2) = Real.pi / (m : ℝ) :=
  (integrable_and_integral_normSq_suzukiHalfInner_div_sq hRH hm hord hγ).2

end
end RHTower
