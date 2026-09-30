import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Functions whose logarithmic derivative is close to a constant

Let `F : ℝ → ℂ` be differentiable on the segment between `u` and `w`, with
`‖F' − aF‖ ≤ η‖F‖` there. Then `F` is close to the exponential model `F(u) e^{(x−u)a}`:

`‖F(w) − F(u) e^{(w−u)a}‖ ≤ ‖F(u)‖ e^{(w−u) Re a} (e^{η|w−u|} − 1)`

(`norm_sub_mul_exp_le`). The proof applies Grönwall's inequality to
`f(x) = F(x) e^{−(x−u)a} − F(u)`, whose derivative `(F' − aF) e^{−(x−u)a}` has norm at most
`η‖f‖ + η‖F(u)‖`; the backward direction follows by reflecting `x ↦ −x`. No non-vanishing of `F`
is assumed. A cruder companion, `norm_le_mul_exp_of_norm_deriv_le_Icc`, bounds `‖F(w)‖` by
`‖F(u)‖ e^{K(w−u)}` when `‖F'‖ ≤ K‖F‖`.
-/

open Complex Set

namespace GaloisForLFunctions.HTGeometry

theorem norm_sub_mul_exp_le_forward {F F' : ℝ → ℂ} {a : ℂ} {η u w : ℝ} (hη : 0 < η)
    (huw : u ≤ w) (hF : ∀ x ∈ Icc u w, HasDerivAt F (F' x) x)
    (hε : ∀ x ∈ Icc u w, ‖F' x - a * F x‖ ≤ η * ‖F x‖) :
    ‖F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
      ‖F u‖ * Real.exp ((w - u) * a.re) * (Real.exp (η * (w - u)) - 1) := by
  set E : ℝ → ℂ := fun x => Complex.exp (((x - u : ℝ) : ℂ) * (-a)) with hE
  have hEd : ∀ x : ℝ, HasDerivAt E (E x * (-a)) x := by
    intro x
    have h1 := (((hasDerivAt_id' x).sub_const u).ofReal_comp.mul_const (-a)).cexp
    simpa [hE] using h1
  have hEnorm : ∀ x : ℝ, ‖E x‖ = Real.exp (-((x - u) * a.re)) := by
    intro x
    rw [hE, Complex.norm_exp, Complex.re_ofReal_mul, Complex.neg_re]
    ring_nf
  set f : ℝ → ℂ := fun x => F x * E x - F u with hf
  set f' : ℝ → ℂ := fun x => (F' x - a * F x) * E x with hf'
  have hderiv : ∀ x ∈ Icc u w, HasDerivAt f (f' x) x := by
    intro x hx
    have := ((hF x hx).mul (hEd x)).sub_const (F u)
    exact this.congr_deriv (by simp only [hf']; ring)
  have hcont : ContinuousOn f (Icc u w) := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hbound : ∀ x ∈ Ico u w, ‖f' x‖ ≤ η * ‖f x‖ + η * ‖F u‖ := by
    intro x hx
    have hx' : x ∈ Icc u w := Ico_subset_Icc_self hx
    have hfx : f x + F u = F x * E x := by simp [hf]
    calc ‖f' x‖ = ‖F' x - a * F x‖ * ‖E x‖ := norm_mul _ _
      _ ≤ η * ‖F x‖ * ‖E x‖ := by gcongr; exact hε x hx'
      _ = η * ‖f x + F u‖ := by rw [hfx, norm_mul]; ring
      _ ≤ η * (‖f x‖ + ‖F u‖) := by gcongr; exact norm_add_le _ _
      _ = η * ‖f x‖ + η * ‖F u‖ := by ring
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun x hx => (hderiv x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (by simp [hf, hE] : ‖f u‖ ≤ 0) hbound w ⟨huw, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hη.ne'] at hgr
  simp only [zero_mul, zero_add] at hgr
  have hkey : F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a) =
      f w * Complex.exp (((w - u : ℝ) : ℂ) * a) := by
    simp only [hf, hE]
    rw [sub_mul, mul_assoc, ← Complex.exp_add]
    simp
  rw [hkey, norm_mul, Complex.norm_exp]
  have hre : (((w - u : ℝ) : ℂ) * a).re = (w - u) * a.re := by simp [Complex.mul_re]
  rw [hre]
  have hle : ‖f w‖ ≤ ‖F u‖ * (Real.exp (η * (w - u)) - 1) := by
    calc ‖f w‖ ≤ η * ‖F u‖ / η * (Real.exp (η * (w - u)) - 1) := hgr
      _ = _ := by field_simp
  calc ‖f w‖ * Real.exp ((w - u) * a.re)
      ≤ ‖F u‖ * (Real.exp (η * (w - u)) - 1) * Real.exp ((w - u) * a.re) := by gcongr
    _ = _ := by ring

theorem norm_sub_mul_exp_le_backward {F F' : ℝ → ℂ} {a : ℂ} {η u w : ℝ} (hη : 0 < η)
    (hwu : w ≤ u) (hF : ∀ x ∈ Icc w u, HasDerivAt F (F' x) x)
    (hε : ∀ x ∈ Icc w u, ‖F' x - a * F x‖ ≤ η * ‖F x‖) :
    ‖F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
      ‖F u‖ * Real.exp ((w - u) * a.re) * (Real.exp (η * (u - w)) - 1) := by
  set G : ℝ → ℂ := fun x => F (-x) with hG
  set G' : ℝ → ℂ := fun x => -F' (-x) with hG'
  have hmem : ∀ x ∈ Icc (-u) (-w), -x ∈ Icc w u := fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hGd : ∀ x ∈ Icc (-u) (-w), HasDerivAt G (G' x) x := by
    intro x hx
    have := (hF (-x) (hmem x hx)).scomp x (hasDerivAt_neg x)
    simpa [hG, hG', Function.comp_def] using this
  have hGε : ∀ x ∈ Icc (-u) (-w), ‖G' x - (-a) * G x‖ ≤ η * ‖G x‖ := by
    intro x hx
    have h := hε (-x) (hmem x hx)
    simp only [hG, hG']
    rw [show -F' (-x) - -a * F (-x) = -(F' (-x) - a * F (-x)) by ring, norm_neg]
    exact h
  have h := norm_sub_mul_exp_le_forward hη (by linarith) hGd hGε
  simp only [hG, neg_neg] at h
  have e1 : (((-w - -u : ℝ) : ℂ) * -a) = (((w - u : ℝ) : ℂ) * a) := by push_cast; ring
  have e2 : (-w - -u) * (-a).re = (w - u) * a.re := by simp; ring
  have e3 : -w - -u = u - w := by ring
  rw [e1, e2, e3] at h
  exact h

/-- **The log-linear model.** If `‖F' − aF‖ ≤ η‖F‖` on the segment between `u` and `w`, then
`‖F(w) − F(u)e^{(w−u)a}‖ ≤ ‖F(u)‖ e^{(w−u) Re a}(e^{η|w−u|} − 1)`. -/
theorem norm_sub_mul_exp_le {F F' : ℝ → ℂ} {a : ℂ} {η u w : ℝ} (hη : 0 < η)
    (hF : ∀ x ∈ uIcc u w, HasDerivAt F (F' x) x)
    (hε : ∀ x ∈ uIcc u w, ‖F' x - a * F x‖ ≤ η * ‖F x‖) :
    ‖F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
      ‖F u‖ * Real.exp ((w - u) * a.re) * (Real.exp (η * |w - u|) - 1) := by
  rcases le_total u w with huw | hwu
  · rw [uIcc_of_le huw] at hF hε
    rw [abs_of_nonneg (by linarith)]
    exact norm_sub_mul_exp_le_forward hη huw hF hε
  · rw [uIcc_of_ge hwu] at hF hε
    rw [abs_of_nonpos (by linarith), neg_sub]
    exact norm_sub_mul_exp_le_backward hη hwu hF hε

/-- Norm Grönwall: `‖F'‖ ≤ K‖F‖` on `[u, w]` gives `‖F(w)‖ ≤ ‖F(u)‖ e^{K(w−u)}`. -/
theorem norm_le_mul_exp_of_norm_deriv_le_Icc {F F' : ℝ → ℂ} {K u w : ℝ} (huw : u ≤ w)
    (hF : ∀ x ∈ Icc u w, HasDerivAt F (F' x) x) (hK : ∀ x ∈ Icc u w, ‖F' x‖ ≤ K * ‖F x‖) :
    ‖F w‖ ≤ ‖F u‖ * Real.exp (K * (w - u)) := by
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun x hx => (hF x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hF x (Ico_subset_Icc_self hx)).hasDerivWithinAt) le_rfl
    (fun x hx => by rw [add_zero]; exact hK x (Ico_subset_Icc_self hx)) w ⟨huw, le_rfl⟩
  rwa [gronwallBound_ε0] at h

end GaloisForLFunctions.HTGeometry
