import GaloisForLFunctions.RHTower.GL3TernaryTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence


/-!
# Analytic continuation and functional equation of the `SL₃(ℤ)` Epstein zeta function

For `z ∈ h³` let `θ_z(t) = Σ_{v ∈ ℤ³} exp(−π t Q_z(v))` (`thetaZ`). In Iwasawa coordinates it is the
nested sum of `GL3TernaryTheta` (`thetaZ_eq_nested`), so the ternary theta transformation gives
`θ_z(1/x) = x^{3/2} (y₁²y₂)⁻¹ θ_{ιz}(x/(y₁y₂)²)` (`thetaZ_feq`), where
`ιz = (x₂, x₁, x₁x₂ − x₃, y₂, y₁)` is the outer involution (`invol`).

`θ_z` is continuous on `(0,∞)` (`continuousOn_thetaZ`) and `θ_z − 1` decays like `e^{−πt/K²}`
because `Q_z(v) ≥ 1/K²` for `v ≠ 0` (`qf_ge`, `thetaZ_sub_one_isBigO`). Together these make
`(θ_z, θ_{ιz}(·/(y₁y₂)²))` a Mellin functional-equation pair of weight `3/2` and root number
`(y₁²y₂)⁻¹` (`epsteinFEPair`), so its completed Mellin transform `Λ_z` is holomorphic away from
`s = 0, 3/2` (`differentiableAt_epsteinΛ`) and satisfies a functional equation
(`epsteinΛ_functional_equation`).

Exchanging the Mellin integral with the lattice sum (the norms are summable by the convergence of
the real Epstein series) gives `Λ_z(s) = π^{-s} Γ(s) Z_z(s)` for `Re s > 3/2`, with
`Z_z(s) = Σ_{v ≠ 0} Q_z(v)^{-s}` (`mellin_thetaZ`, `epsteinΛ_eq`). Hence `Z_z` continues
meromorphically, and for `Re s > 3/2`
`Λ_z(3/2 − s) = (y₁²y₂)⁻¹ ((y₁y₂)²)^s π^{-s} Γ(s) Z_{ιz}(s)` (`epstein_functional_equation`).
-/

open Complex Real Filter Asymptotics Set MeasureTheory

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-! ### The theta series of a point -/

theorem qf_coords (z : H3) (v : Fin 3 → ℤ) :
    qf z v = (z.y1 * z.y2 * v 0) ^ 2 + (z.y1 * (v 1 + z.x2 * v 0)) ^ 2 +
      (v 2 + z.x1 * v 1 + z.x3 * v 0) ^ 2 := by
  rw [qf_eq_sum_sq, Fin.sum_univ_three]
  simp [vR, Matrix.vecMul, dotProduct, Fin.sum_univ_three, mat]
  ring

/-- **The theta series** `θ_z(t) = Σ_{v ∈ ℤ³} exp(−π t Q_z(v))`. -/
noncomputable def thetaZ (z : H3) (t : ℝ) : ℂ := ∑' v : Fin 3 → ℤ, cexp (-π * t * qf z v)

theorem norm_exp_qf (z : H3) (t : ℝ) (v : Fin 3 → ℤ) :
    ‖cexp (-π * t * qf z v)‖ = Real.exp (-π * t * qf z v) := by
  rw [show -π * (t : ℂ) * (qf z v : ℂ) = ((-π * t * qf z v : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_ofReal]

/-- Gaussian majorant over `ℤ³`: `‖v‖²_∞ ≥ (v₀² + v₁² + v₂²)/3`. -/
theorem exp_qf_le (z : H3) {t : ℝ} (ht : 0 < t) (v : Fin 3 → ℤ) :
    Real.exp (-π * t * qf z v) ≤
      ∏ i, Real.exp (-π * (t / (3 * invBound z ^ 2)) * ((v i : ℝ) + 0) ^ 2) := by
  have hK := invBound_pos z
  rw [← Real.exp_sum, Real.exp_le_exp]
  have h1 := norm_sq_le_qf z v
  have h2 : ((v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 + (v 2 : ℝ) ^ 2) / 3 ≤ ‖vR v‖ ^ 2 := by
    have hi : ∀ i, |(v i : ℝ)| ≤ ‖vR v‖ := fun i => by
      have := norm_le_pi_norm (vR v) i
      simpa [vR, Real.norm_eq_abs] using this
    have := fun i => sq_le_sq' (abs_le.1 (hi i)).1 (abs_le.1 (hi i)).2
    linarith [this 0, this 1, this 2]
  simp only [Fin.sum_univ_three, add_zero]
  have hpi := Real.pi_pos
  have : π * (t / (3 * invBound z ^ 2)) * ((v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 + (v 2 : ℝ) ^ 2) ≤
      π * t * qf z v := by
    have h3 : ((v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 + (v 2 : ℝ) ^ 2) / (3 * invBound z ^ 2) ≤ qf z v := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc π * (t / (3 * invBound z ^ 2)) * ((v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 + (v 2 : ℝ) ^ 2)
        = π * t * (((v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 + (v 2 : ℝ) ^ 2) / (3 * invBound z ^ 2)) := by
          field_simp
      _ ≤ π * t * qf z v := mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

/-- Products of summable nonnegative functions are summable over `Fin n → ℤ`. -/
theorem summable_pi_prod {φ : ℤ → ℝ} (hφ : Summable φ) (hφ0 : ∀ k, 0 ≤ φ k) (n : ℕ) :
    Summable fun v : Fin n → ℤ => ∏ i, φ (v i) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
      set ψ : (Fin n → ℤ) → ℝ := fun w => ∏ i, φ (w i)
      have hψ0 : 0 ≤ ψ := fun w => Finset.prod_nonneg fun _ _ => hφ0 _
      have hφ0' : 0 ≤ φ := hφ0
      have hprod : Summable fun p : ℤ × (Fin n → ℤ) => φ p.1 * ψ p.2 :=
        Summable.mul_of_nonneg hφ ih hφ0' hψ0
      have he : ∀ p : ℤ × (Fin n → ℤ),
          (∏ i, φ ((Fin.consEquiv fun _ : Fin (n + 1) => ℤ) p i)) = φ p.1 * ψ p.2 := by
        intro p
        rw [Fin.prod_univ_succ]
        simp only [ψ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      refine (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff.1 ?_
      exact hprod.congr fun p => (he p).symm

theorem summable_prod_gauss {c : ℝ} (hc : 0 < c) :
    Summable fun v : Fin 3 → ℤ => ∏ i, Real.exp (-π * c * ((v i : ℝ) + 0) ^ 2) :=
  summable_pi_prod (summable_realGauss hc 0) (fun _ => by positivity) 3

theorem summable_exp_qf (z : H3) {t : ℝ} (ht : 0 < t) :
    Summable fun v : Fin 3 → ℤ => cexp (-π * t * qf z v) := by
  have hK := invBound_pos z
  refine Summable.of_norm_bounded (summable_prod_gauss (c := t / (3 * invBound z ^ 2))
    (by positivity)) fun v => ?_
  rw [norm_exp_qf]
  exact exp_qf_le z ht v

/-- The coordinate triple of an integer vector. -/
def tripleEquiv : ℤ × ℤ × ℤ ≃ (Fin 3 → ℤ) where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun v := (v 0, v 1, v 2)
  left_inv p := by simp
  right_inv v := by ext i; fin_cases i <;> rfl

/-- **The theta series as a nested sum** in the order `v₀, v₁, v₂`. -/
theorem thetaZ_eq_nested (z : H3) {t : ℝ} (ht : 0 < t) :
    thetaZ z t = ∑' v0 : ℤ, ∑' v1 : ℤ, ∑' v2 : ℤ,
      gaussQ t z.x1 z.x2 z.x3 z.y1 (z.y1 * z.y2) v0 v1 v2 := by
  have hs := summable_exp_qf z ht
  set F : ℤ × ℤ × ℤ → ℂ := fun p => cexp (-π * t * qf z (tripleEquiv p))
  have hF : Summable F := tripleEquiv.summable_iff.2 hs
  have hterm : ∀ p : ℤ × ℤ × ℤ, F p = gaussQ t z.x1 z.x2 z.x3 z.y1 (z.y1 * z.y2) p.1 p.2.1 p.2.2 := by
    intro p
    simp only [F, gaussQ, qf_coords]
    congr 1
    simp [tripleEquiv]
  rw [thetaZ, ← tripleEquiv.tsum_eq, hF.tsum_prod' (fun b => hF.prod_factor b)]
  refine tsum_congr fun v0 => ?_
  have hF1 : Summable fun q : ℤ × ℤ => F (v0, q) := hF.prod_factor v0
  rw [hF1.tsum_prod' (fun b => hF1.prod_factor b)]
  exact tsum_congr fun v1 => tsum_congr fun v2 => hterm (v0, v1, v2)

/-- **The outer involution** `ι(z) = (x₂, x₁, x₁x₂ − x₃, y₂, y₁)`. -/
def invol (z : H3) : H3 := ⟨z.x2, z.x1, z.x1 * z.x2 - z.x3, z.y2, z.y1, z.y2_pos, z.y1_pos⟩

/-- **Functional equation of the theta series**:
`θ_z(1/x) = x^{3/2} (y₁²y₂)⁻¹ θ_{ιz}(x/(y₁y₂)²)`. -/
theorem thetaZ_feq (z : H3) {x : ℝ} (hx : 0 < x) :
    thetaZ z (1 / x) = ((x ^ (3 / 2 : ℝ) / (z.y1 ^ 2 * z.y2) : ℝ) : ℂ) *
      thetaZ (invol z) (x / (z.y1 * z.y2) ^ 2) := by
  have h1 := z.y1_pos; have h2 := z.y2_pos
  have ht : (0 : ℝ) < 1 / x := by positivity
  have hu : (0 : ℝ) < x / (z.y1 * z.y2) ^ 2 := by positivity
  rw [thetaZ_eq_nested z ht, theta_transform _ _ _ _ _ ht h1 (by positivity),
    thetaZ_eq_nested (invol z) hu]
  have e1 : Real.sqrt (1 / x) = x ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, one_div, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
  have e2 : Real.sqrt (1 / x * z.y1 ^ 2) = x ^ (-(1 / 2) : ℝ) * z.y1 := by
    rw [Real.sqrt_mul (by positivity), e1, Real.sqrt_sq h1.le]
  have e3 : Real.sqrt (1 / x * (z.y1 * z.y2) ^ 2) = x ^ (-(1 / 2) : ℝ) * (z.y1 * z.y2) := by
    rw [Real.sqrt_mul (by positivity), e1, Real.sqrt_sq (by positivity)]
  have ex : x ^ (3 / 2 : ℝ) * (x ^ (-(1 / 2) : ℝ)) ^ 3 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]; norm_num
  have hxp : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx _
  have hreal : 1 / Real.sqrt (1 / x) * (1 / Real.sqrt (1 / x * z.y1 ^ 2) *
      (1 / Real.sqrt (1 / x * (z.y1 * z.y2) ^ 2))) = x ^ (3 / 2 : ℝ) / (z.y1 ^ 2 * z.y2) := by
    rw [e1, e2, e3]
    field_simp
    first
      | linear_combination (z.y1 ^ 2 * z.y2) * ex
      | linear_combination (-(z.y1 ^ 2 * z.y2)) * ex
      | linear_combination ex
      | linear_combination -ex
  have hconst : 1 / (Real.sqrt (1 / x) : ℂ) * (1 / (Real.sqrt (1 / x * z.y1 ^ 2) : ℂ) *
      (1 / (Real.sqrt (1 / x * (z.y1 * z.y2) ^ 2) : ℂ))) =
      ((x ^ (3 / 2 : ℝ) / (z.y1 ^ 2 * z.y2) : ℝ) : ℂ) := by
    rw [← hreal]; push_cast; ring
  rw [← mul_assoc, ← mul_assoc, mul_assoc (1 / (Real.sqrt (1 / x) : ℂ)), hconst]
  congr 1
  refine tsum_congr fun n2 => ?_
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun w1 => tsum_congr fun n0 => ?_
  simp only [kern3, gaussQ, invol, Equiv.neg_apply]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hy1 : (z.y1 : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
  have hy2 : (z.y2 : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp
  ring

/-! ### Regularity and decay of the theta series -/

theorem summable_realExp_qf (z : H3) {t : ℝ} (ht : 0 < t) :
    Summable fun v : Fin 3 → ℤ => Real.exp (-π * t * qf z v) := by
  have := (summable_norm_iff.2 (summable_exp_qf z ht))
  exact this.congr fun v => norm_exp_qf z t v

theorem continuousOn_thetaZ (z : H3) : ContinuousOn (thetaZ z) (Ioi 0) := by
  intro t0 ht0
  have hs : ContinuousOn (thetaZ z) (Ioi (t0 / 2)) := by
    refine continuousOn_tsum (u := fun v => Real.exp (-π * (t0 / 2) * qf z v))
      (fun v => by fun_prop) (summable_realExp_qf z (by linarith [ht0.out])) fun v t ht => ?_
    rw [norm_exp_qf, Real.exp_le_exp]
    have hq := qf_nonneg z v
    have h3 : t0 / 2 ≤ t := (mem_Ioi.1 ht).le
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hq) (sub_nonneg.2 h3)]
  exact (hs.continuousAt (Ioi_mem_nhds (by linarith [ht0.out] : t0 / 2 < t0))).continuousWithinAt

theorem one_le_norm_vR {v : Fin 3 → ℤ} (hv : v ≠ 0) : 1 ≤ ‖vR v‖ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have h1 : (1 : ℝ) ≤ |(v i : ℝ)| := by
    have : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
    exact_mod_cast this
  exact h1.trans (by simpa [vR, Real.norm_eq_abs] using norm_le_pi_norm (vR v) i)

theorem qf_ge (z : H3) {v : Fin 3 → ℤ} (hv : v ≠ 0) : 1 / invBound z ^ 2 ≤ qf z v := by
  have hK := invBound_pos z
  have h1 := one_le_norm_vR hv
  have h2 := norm_sq_le_qf z v
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **`θ_z(t) − 1` decays exponentially**: `‖θ_z(t) − 1‖ ≤ e^{−π(t−1)/K²} θ_z^ℝ(1)` for `t ≥ 1`. -/
theorem norm_thetaZ_sub_one_le (z : H3) {t : ℝ} (ht : 1 ≤ t) :
    ‖thetaZ z t - 1‖ ≤ Real.exp (-(π / invBound z ^ 2) * (t - 1)) *
      ∑' v : Fin 3 → ℤ, Real.exp (-π * 1 * qf z v) := by
  classical
  have ht0 : 0 < t := by linarith
  have hK := invBound_pos z
  have hs := summable_exp_qf z ht0
  have h0 : cexp (-π * t * qf z 0) = 1 := by
    have hv0 : vR 0 = 0 := by ext i; simp [vR]
    have : qf z 0 = 0 := by simp [qf, hv0]
    simp [this]
  rw [thetaZ, hs.tsum_eq_add_tsum_ite 0, h0, add_sub_cancel_left]
  have hsR := summable_realExp_qf z (show (0 : ℝ) < 1 by norm_num)
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · refine Summable.of_norm_bounded (summable_realExp_qf z ht0) fun v => ?_
    split_ifs
    · simp only [norm_zero]; positivity
    · rw [norm_norm, norm_exp_qf]
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun v => ?_) ?_ (hsR.mul_left _)
  · split_ifs with hv
    · simp; positivity
    · rw [norm_exp_qf, ← Real.exp_add, Real.exp_le_exp]
      have hq := qf_ge z hv
      have hq0 := qf_nonneg z v
      have hpi := Real.pi_pos
      have h1 : 1 ≤ invBound z ^ 2 * qf z v := by
        rw [div_le_iff₀ (by positivity)] at hq; linarith
      have h2 : π / invBound z ^ 2 * (t - 1) ≤ π * (t - 1) * qf z v := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hpi.le (sub_nonneg.2 ht)) (sub_nonneg.2 h1)]
      have e : π * (t - 1) * qf z v = π * t * qf z v - π * qf z v := by ring
      have e2 : -(π / invBound z ^ 2) * (t - 1) + -π * 1 * qf z v =
          -(π / invBound z ^ 2 * (t - 1)) - π * qf z v := by ring
      rw [e2]
      linarith
  · refine Summable.of_norm_bounded (summable_realExp_qf z ht0) fun v => ?_
    split_ifs
    · simp only [norm_zero]; positivity
    · rw [norm_norm, norm_exp_qf]

theorem thetaZ_sub_one_isBigO (z : H3) (r : ℝ) :
    (fun t => thetaZ z t - 1) =O[atTop] (· ^ r) := by
  have hK := invBound_pos z
  set c := π / invBound z ^ 2
  have hc : 0 < c := by positivity
  set A := ∑' v : Fin 3 → ℤ, Real.exp (-π * 1 * qf z v)
  have h1 : (fun t => thetaZ z t - 1) =O[atTop] fun t => Real.exp (-c * t) := by
    refine IsBigO.of_bound (Real.exp c * A) ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    refine (norm_thetaZ_sub_one_le z ht).trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), show -c * (t - 1) = c + -c * t by ring,
      Real.exp_add]
    ring
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO

/-! ### The functional-equation pair -/

theorem thetaInvol_sub_one_isBigO (z : H3) (r : ℝ) :
    (fun x => thetaZ (invol z) (x / (z.y1 * z.y2) ^ 2) - 1) =O[atTop] (· ^ r) := by
  set c := (z.y1 * z.y2) ^ 2
  have hc : 0 < c := by have := z.y1_pos; have := z.y2_pos; positivity
  have h1 := (thetaZ_sub_one_isBigO (invol z) r).comp_tendsto
    (tendsto_id.atTop_div_const hc)
  refine h1.trans ?_
  have h2 : (fun x : ℝ => (x / c) ^ r) =ᶠ[atTop] fun x => (c ^ r)⁻¹ * x ^ r := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.div_rpow hx.le hc.le]; ring
  exact h2.trans_isBigO (isBigO_const_mul_self _ _ _)

/-- **The Mellin functional-equation pair of the Epstein zeta function of `z`**:
`f = θ_z`, `g(x) = θ_{ιz}(x/(y₁y₂)²)`, weight `3/2`, root number `(y₁²y₂)⁻¹`. -/
noncomputable def epsteinFEPair (z : H3) : WeakFEPair ℂ where
  f := thetaZ z
  g := fun x => thetaZ (invol z) (x / (z.y1 * z.y2) ^ 2)
  k := 3 / 2
  ε := ((1 / (z.y1 ^ 2 * z.y2) : ℝ) : ℂ)
  f₀ := 1
  g₀ := 1
  hf_int := (continuousOn_thetaZ z).locallyIntegrableOn measurableSet_Ioi
  hg_int := by
    have hc : 0 < (z.y1 * z.y2) ^ 2 := by have := z.y1_pos; have := z.y2_pos; positivity
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    exact (continuousOn_thetaZ (invol z)).comp (continuousOn_id.div_const _)
      fun x hx => mem_Ioi.2 (div_pos (mem_Ioi.1 hx) hc)
  hk := by norm_num
  hε := by
    have := z.y1_pos; have := z.y2_pos
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 1 / (z.y1 ^ 2 * z.y2)))
  h_feq x hx := by
    rw [thetaZ_feq z hx, smul_eq_mul]
    congr 1
    push_cast
    ring
  hf_top := thetaZ_sub_one_isBigO z
  hg_top := thetaInvol_sub_one_isBigO z

/-- **Meromorphic continuation**: the completed Epstein function `Λ_z` is holomorphic away from
`s = 0` and `s = 3/2`. -/
theorem differentiableAt_epsteinΛ (z : H3) {s : ℂ} (hs0 : s ≠ 0) (hs : s ≠ 3 / 2) :
    DifferentiableAt ℂ (epsteinFEPair z).Λ s := by
  refine (epsteinFEPair z).differentiableAt_Λ (Or.inl hs0) (Or.inl ?_)
  simpa [epsteinFEPair] using hs

/-- **Functional equation**: `Λ_z(3/2 − s) = (y₁²y₂)⁻¹ Λ^∨_z(s)`, where `Λ^∨_z` is the Mellin
transform of `θ_{ιz}(x/(y₁y₂)²) − 1`. -/
theorem epsteinΛ_functional_equation (z : H3) (s : ℂ) :
    (epsteinFEPair z).Λ (3 / 2 - s) =
      ((1 / (z.y1 ^ 2 * z.y2) : ℝ) : ℂ) • (epsteinFEPair z).symm.Λ s := by
  have := (epsteinFEPair z).functional_equation s
  simpa [epsteinFEPair] using this

/-- For `Re s > 3/2`, `Λ_z(s)` is the Mellin transform of `θ_z − 1`. -/
theorem hasMellin_epsteinΛ (z : H3) {s : ℂ} (hs : 3 / 2 < s.re) :
    HasMellin (fun t => thetaZ z t - 1) s ((epsteinFEPair z).Λ s) :=
  (epsteinFEPair z).hasMellin (by simpa [epsteinFEPair] using hs)

/-! ### Identification with the Epstein zeta function -/

/-- **The complex Epstein zeta function** `Z_z(s) = Σ_{v ≠ 0} Q_z(v)^{-s}`. -/
noncomputable def epsteinC (z : H3) (s : ℂ) : ℂ :=
  ∑' v : Fin 3 → ℤ, if v = 0 then 0 else ((qf z v : ℝ) : ℂ) ^ (-s)

theorem thetaZ_sub_one_eq (z : H3) {t : ℝ} (ht : 0 < t) :
    thetaZ z t - 1 = ∑' v : Fin 3 → ℤ, if v = 0 then 0 else cexp (-π * t * qf z v) := by
  classical
  have hs := summable_exp_qf z ht
  have hv0 : vR 0 = 0 := by ext i; simp [vR]
  have h0 : cexp (-π * t * qf z 0) = 1 := by
    have : qf z 0 = 0 := by simp [qf, hv0]
    simp [this]
  rw [thetaZ, hs.tsum_eq_add_tsum_ite 0, h0, add_sub_cancel_left]

/-- The Mellin summand. -/
noncomputable def mellinTerm (z : H3) (s : ℂ) (v : Fin 3 → ℤ) (t : ℝ) : ℂ :=
  if v = 0 then 0 else (t : ℂ) ^ (s - 1) * cexp (-((π * qf z v : ℝ) : ℂ) * t)

theorem integral_mellinTerm (z : H3) {s : ℂ} (hs : 0 < s.re) {v : Fin 3 → ℤ} (hv : v ≠ 0) :
    ∫ t in Ioi 0, mellinTerm z s v t = (1 / ((π * qf z v : ℝ) : ℂ)) ^ s * Complex.Gamma s := by
  have hq := qf_pos z hv
  simp only [mellinTerm, hv, if_false]
  have := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs (by positivity : 0 < π * qf z v)
  refine (setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_).trans this
  congr 2
  push_cast
  ring

theorem norm_mellinTerm (z : H3) (s : ℂ) {v : Fin 3 → ℤ} (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    ‖mellinTerm z s v t‖ = t ^ (s.re - 1) * Real.exp (-(π * qf z v * t)) := by
  simp only [mellinTerm, hv, if_false, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  rw [show -((π * qf z v : ℝ) : ℂ) * t = ((-(π * qf z v * t) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_ofReal]
  simp

theorem continuousOn_mellinTerm (z : H3) (s : ℂ) (v : Fin 3 → ℤ) :
    ContinuousOn (mellinTerm z s v) (Ioi 0) := by
  by_cases hv : v = 0
  · have e : mellinTerm z s v = fun _ => 0 := by funext t; simp [mellinTerm, hv]
    rw [e]; exact continuousOn_const
  · have e : mellinTerm z s v = fun t : ℝ => (t : ℂ) ^ (s - 1) * cexp (-((π * qf z v : ℝ) : ℂ) * t) := by
      funext t; simp [mellinTerm, hv]
    rw [e]
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (mem_Ioi.1 ht).ne')).mul
      (by fun_prop)

theorem integrable_realGammaKernel {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := σ - 1) (p := 1) (by linarith) le_rfl hr
  refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

theorem integrable_mellinTerm (z : H3) {s : ℂ} (hs : 0 < s.re) (v : Fin 3 → ℤ) :
    IntegrableOn (mellinTerm z s v) (Ioi 0) := by
  by_cases hv : v = 0
  · have e : mellinTerm z s v = fun _ => 0 := by funext t; simp [mellinTerm, hv]
    rw [e]; exact integrableOn_zero
  have hq := qf_pos z hv
  refine Integrable.mono' (integrable_realGammaKernel hs (by positivity : 0 < π * qf z v))
    ((continuousOn_mellinTerm z s v).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  rw [norm_mellinTerm z s hv ht]

theorem integral_norm_mellinTerm (z : H3) {s : ℂ} (hs : 0 < s.re) (v : Fin 3 → ℤ) :
    ∫ t in Ioi 0, ‖mellinTerm z s v t‖ =
      if v = 0 then 0 else (1 / (π * qf z v)) ^ s.re * Real.Gamma s.re := by
  by_cases hv : v = 0
  · simp [mellinTerm, hv]
  have hq := qf_pos z hv
  simp only [hv, if_false]
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by positivity : 0 < π * qf z v)]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => norm_mellinTerm z s hv ht

/-- **Mellin transform of the theta series**: for `Re s > 3/2`,
`∫₀^∞ t^{s-1} (θ_z(t) − 1) dt = π^{-s} Γ(s) Σ_{v ≠ 0} Q_z(v)^{-s}`. -/
theorem mellin_thetaZ (z : H3) {s : ℂ} (hs : 3 / 2 < s.re) :
    mellin (fun t => thetaZ z t - 1) s = (π : ℂ) ^ (-s) * Complex.Gamma s * epsteinC z s := by
  have hs0 : 0 < s.re := by linarith
  have hsumR := summable_epstein z (s := s.re) hs
  -- the integrand as a series
  have hint : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • (thetaZ z t - 1) =
      ∑' v : Fin 3 → ℤ, mellinTerm z s v t := by
    intro t ht
    rw [thetaZ_sub_one_eq z ht, smul_eq_mul, ← tsum_mul_left]
    refine tsum_congr fun v => ?_
    by_cases hv : v = 0
    · simp [mellinTerm, hv]
    · simp only [mellinTerm, hv, if_false]
      congr 2
      push_cast; ring
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hint,
    ← integral_tsum_of_summable_integral_norm (fun v => integrable_mellinTerm z hs0 v)]
  · rw [epsteinC, ← tsum_mul_left]
    refine tsum_congr fun v => ?_
    by_cases hv : v = 0
    · simp [mellinTerm, hv]
    have hq := qf_pos z hv
    simp only [hv, if_false]
    rw [integral_mellinTerm z hs0 hv]
    have e : (1 / ((π * qf z v : ℝ) : ℂ)) ^ s = (π : ℂ) ^ (-s) * ((qf z v : ℝ) : ℂ) ^ (-s) := by
      have hx : (((π * qf z v : ℝ)) : ℂ).arg ≠ π := by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_pos.ne
      rw [one_div, Complex.inv_cpow _ _ hx,
        show ((π * qf z v : ℝ) : ℂ) = ((π : ℝ) : ℂ) * ((qf z v : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hq.le, Complex.cpow_neg, Complex.cpow_neg,
        mul_inv]
    rw [e]; ring
  · simp only [integral_norm_mellinTerm z hs0]
    refine (hsumR.mul_left (π ^ (-s.re) * Real.Gamma s.re)).congr fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    have hq := qf_pos z hv
    simp only [hv, if_false]
    rw [one_div, Real.inv_rpow (by positivity), Real.mul_rpow Real.pi_pos.le hq.le,
      Real.rpow_neg Real.pi_pos.le, Real.rpow_neg hq.le]
    field_simp

/-! ### Continuation and functional equation of the Epstein zeta function -/

/-- **The completed Epstein function continues `π^{-s} Γ(s) Z_z(s)`** from `Re s > 3/2`. -/
theorem epsteinΛ_eq (z : H3) {s : ℂ} (hs : 3 / 2 < s.re) :
    (epsteinFEPair z).Λ s = (π : ℂ) ^ (-s) * Complex.Gamma s * epsteinC z s := by
  rw [← mellin_thetaZ z hs]
  exact (hasMellin_epsteinΛ z hs).2.symm

/-- The dual side: for `Re s > 3/2`, `Λ^∨_z(s) = ((y₁y₂)²)^s π^{-s} Γ(s) Z_{ιz}(s)`. -/
theorem epsteinΛ_symm_eq (z : H3) {s : ℂ} (hs : 3 / 2 < s.re) :
    (epsteinFEPair z).symm.Λ s =
      (((z.y1 * z.y2) ^ 2 : ℝ) : ℂ) ^ s * ((π : ℂ) ^ (-s) * Complex.Gamma s * epsteinC (invol z) s) := by
  have hc : 0 < (z.y1 * z.y2) ^ 2 := by have := z.y1_pos; have := z.y2_pos; positivity
  have hM := (epsteinFEPair z).symm.hasMellin (s := s) (by simpa [epsteinFEPair, WeakFEPair.symm] using hs)
  rw [← hM.2]
  simp only [WeakFEPair.symm, epsteinFEPair]
  have e : (fun x : ℝ => thetaZ (invol z) (x / (z.y1 * z.y2) ^ 2) - 1) =
      fun x => (fun u => thetaZ (invol z) u - 1) ((1 / (z.y1 * z.y2) ^ 2) * x) := by
    funext x; congr 2; ring
  rw [e, mellin_comp_mul_left (fun u => thetaZ (invol z) u - 1) s
    (by positivity : (0 : ℝ) < 1 / (z.y1 * z.y2) ^ 2), mellin_thetaZ (invol z) hs, smul_eq_mul]
  congr 1
  rw [one_div, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hc.le]; exact Real.pi_pos.ne), Complex.cpow_neg, inv_inv]

/-- **The functional equation of the `SL₃(ℤ)` Epstein zeta function** (maximal parabolic
Eisenstein series): for `Re s > 3/2`, the continuation of `π^{-s}Γ(s)Z_z(s)` to `3/2 − s` is
`(y₁²y₂)⁻¹ ((y₁y₂)²)^s π^{-s} Γ(s) Z_{ιz}(s)`. -/
theorem epstein_functional_equation (z : H3) {s : ℂ} (hs : 3 / 2 < s.re) :
    (epsteinFEPair z).Λ (3 / 2 - s) =
      ((1 / (z.y1 ^ 2 * z.y2) : ℝ) : ℂ) * ((((z.y1 * z.y2) ^ 2 : ℝ) : ℂ) ^ s *
        ((π : ℂ) ^ (-s) * Complex.Gamma s * epsteinC (invol z) s)) := by
  rw [epsteinΛ_functional_equation, epsteinΛ_symm_eq z hs, smul_eq_mul]

end H3
end GaloisForLFunctions.RHTower.GL3
