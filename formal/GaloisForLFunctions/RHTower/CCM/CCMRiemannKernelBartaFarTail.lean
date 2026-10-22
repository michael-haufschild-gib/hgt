import GaloisForLFunctions.RHTower.CCM.CCMRiemannKernelBartaEdgeFormDomain

/-!
# The bulk of the truncated Riemann kernel is invisible to the form

Let `S = Φ χ_{b+2,1}`, where `χ_{b+2,1} = 1` on `|t| ≤ b + 1` and `0` on `|t| ≥ b + 2`; it is a smooth
interior source at aperture `b + 3`. Every derivative `Φ^{(k)}` lies in the radical: its transform
vanishes at every zero (`paperFT_riemannKernelDeriv_at_zero`). Two integrations by parts on the
compact test give `γ² Ŝ(γ) = (Φ'' − S'')^(γ)` at every zero `γ`, and `r = Φ'' − S''` vanishes on
`|t| < b + 1`. Beyond `b + 1` it is `O(e^{9|t|} e^{−πe^{2|t|}})`, far below `e^{−πe^{2b}}`.

The zero-side representation `Q(x, S) = ∫ conj x · Σ_q Ŝ(−γ_q) e^{iγ_q t}` then gives
`|Q_{b+3}(x, S)| ≤ C Φ(b − 2w) ∫|x|` with an absolute constant `C` (`exists_bartaFar_bound`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

open RHTower.CCMRealRootedGround RHTower.CCMFullGroundEigen

noncomputable section

/-! ## Decay of `Φ, Φ', Φ''` -/

/-- `|Φ^{(k)}(u)| ≤ C_k e^{(2k + 9/2)|u|} e^{−πe^{2|u|}}`. -/
theorem norm_riemannKernelDeriv_le (k : ℕ) (u : ℝ) :
    ‖riemannKernelDeriv k u‖ ≤ cuspDecayConst (riemannKernelPoly k) *
      Real.exp ((2 * (k : ℝ) + 9 / 2) * |u|) * Real.exp (-π * Real.exp (2 * |u|)) := by
  have hpos : ∀ v : ℝ, 0 ≤ v → ‖riemannKernelDeriv k v‖ ≤ cuspDecayConst (riemannKernelPoly k) *
      Real.exp ((2 * (k : ℝ) + 9 / 2) * v) * Real.exp (-π * Real.exp (2 * v)) := by
    intro v hv
    rw [riemannKernelDeriv_eq_cuspSeries, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_cuspSeries_le _ hv).trans ?_
    have hd : ((riemannKernelPoly k).natDegree : ℝ) ≤ k + 2 := by
      exact_mod_cast natDegree_riemannKernelPoly_le k
    have hC := cuspDecayConst_nonneg (riemannKernelPoly k)
    have h1 : Real.exp (v / 2) * Real.exp (2 * ((riemannKernelPoly k).natDegree : ℝ) * v) ≤
        Real.exp ((2 * (k : ℝ) + 9 / 2) * v) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hd hv])
    calc cuspDecayConst (riemannKernelPoly k) * Real.exp (v / 2) *
          Real.exp (2 * ((riemannKernelPoly k).natDegree : ℝ) * v) *
          Real.exp (-π * Real.exp (2 * v))
        = cuspDecayConst (riemannKernelPoly k) * (Real.exp (v / 2) *
          Real.exp (2 * ((riemannKernelPoly k).natDegree : ℝ) * v)) *
          Real.exp (-π * Real.exp (2 * v)) := by ring
      _ ≤ _ := by gcongr
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]; exact hpos u hu
  · rw [abs_of_nonpos hu]
    have hneg : ‖riemannKernelDeriv k u‖ = ‖riemannKernelDeriv k (-u)‖ := by
      rw [riemannKernelDeriv_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [hneg]
    exact hpos (-u) (by linarith)

/-- For `x ≥ b + 1 ≥ 2` and `c ≤ 13`: `e^{cx} e^{−πe^{2x}} ≤ e^{−πe^{2b}} e^{−2x}`. -/
theorem exp_mul_exp_neg_pi_exp_le {b x c : ℝ} (hc : c ≤ 13) (hb : 1 ≤ b) (hx : b + 1 ≤ x) :
    Real.exp (c * x) * Real.exp (-π * Real.exp (2 * x)) ≤
      Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(2 * x)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hx0 : 0 ≤ x := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * x by linarith)
  have hE : Real.exp (2 * b) * Real.exp 2 ≤ Real.exp (2 * x) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have h7 := seven_lt_exp_two
  have hπ := Real.pi_gt_three
  have hEb := Real.exp_pos (2 * b)
  have hEb' : 7 * Real.exp (2 * b) ≤ Real.exp (2 * x) := by nlinarith
  have h6 : 6 * x ≤ Real.exp (2 * x) := by nlinarith
  have hcx : c * x ≤ 13 * x := mul_le_mul_of_nonneg_right hc hx0
  have hπE : 3 * Real.exp (2 * x) ≤ π * Real.exp (2 * x) :=
    mul_le_mul_of_nonneg_right hπ.le (Real.exp_pos _).le
  have hπEb : π * (7 * Real.exp (2 * b)) ≤ π * Real.exp (2 * x) :=
    mul_le_mul_of_nonneg_left hEb' Real.pi_pos.le
  nlinarith

/-! ## The second derivative of the outer cutoff -/

theorem bartaCutoff_one_eventuallyEq_of_nonneg {c t : ℝ} (hc : 1 < c) (ht : 0 ≤ t) :
    bartaCutoff c 1 =ᶠ[𝓝 t] fun s => Real.smoothTransition (c - s) := by
  have hopen : IsOpen {s : ℝ | 1 < c + s} :=
    isOpen_lt continuous_const (continuous_const.add continuous_id)
  filter_upwards [hopen.mem_nhds (show 1 < c + t by linarith)] with s hs
  unfold bartaCutoff
  rw [div_one, div_one, Real.smoothTransition.one_of_one_le (le_of_lt hs), mul_one]

theorem bartaCutoff_one_eventuallyEq_of_nonpos {c t : ℝ} (hc : 1 < c) (ht : t ≤ 0) :
    bartaCutoff c 1 =ᶠ[𝓝 t] fun s => Real.smoothTransition (c + s) := by
  have hopen : IsOpen {s : ℝ | 1 < c - s} :=
    isOpen_lt continuous_const (continuous_const.sub continuous_id)
  filter_upwards [hopen.mem_nhds (show 1 < c - t by linarith)] with s hs
  unfold bartaCutoff
  rw [div_one, div_one, Real.smoothTransition.one_of_one_le (le_of_lt hs), one_mul]

theorem abs_deriv_deriv_bartaCutoff_le {c Λ₂ : ℝ} (hc : 1 < c)
    (hΛ₂ : ∀ x : ℝ, |iteratedDeriv 2 Real.smoothTransition x| ≤ Λ₂) (t : ℝ) :
    |deriv (deriv (bartaCutoff c 1)) t| ≤ Λ₂ := by
  have h2 : ∀ x : ℝ, iteratedDeriv 2 Real.smoothTransition x =
      deriv (deriv Real.smoothTransition) x := by
    intro x; rw [iteratedDeriv_succ, iteratedDeriv_one]
  rcases le_total 0 t with ht | ht
  · rw [(bartaCutoff_one_eventuallyEq_of_nonneg hc ht).deriv.deriv_eq]
    have hd : deriv (fun s => Real.smoothTransition (c - s)) =
        -fun s => deriv Real.smoothTransition (c - s) :=
      funext fun s => deriv_comp_const_sub _ c s
    rw [hd, deriv.neg, deriv_comp_const_sub, neg_neg, ← h2]
    exact hΛ₂ _
  · rw [(bartaCutoff_one_eventuallyEq_of_nonpos hc ht).deriv.deriv_eq]
    have hd : deriv (fun s => Real.smoothTransition (c + s)) =
        fun s => deriv Real.smoothTransition (c + s) :=
      funext fun s => deriv_comp_const_add _ c s
    rw [hd, deriv_comp_const_add, ← h2]
    exact hΛ₂ _

/-! ## The truncated kernel and its second derivative -/

/-- The complex profile `Φ χ_{c,1}`. -/
def bartaFarFn (c t : ℝ) : ℂ := riemannKernelDeriv 0 t * ((bartaCutoff c 1 t : ℝ) : ℂ)

theorem deriv_riemannKernelDeriv (k : ℕ) :
    deriv (riemannKernelDeriv k) = riemannKernelDeriv (k + 1) :=
  funext fun u => (hasDerivAt_riemannKernelDeriv k u).deriv

theorem differentiable_bartaCutoff (c : ℝ) : Differentiable ℝ (bartaCutoff c 1) :=
  (contDiff_bartaCutoff c 1 (n := 1)).differentiable one_ne_zero

theorem differentiable_deriv_bartaCutoff (c : ℝ) : Differentiable ℝ (deriv (bartaCutoff c 1)) := by
  have h := (contDiff_bartaCutoff c 1 (n := ⊤)).iterate_deriv 1
  exact h.differentiable (by simp)

theorem deriv_bartaFarFn (c : ℝ) :
    deriv (bartaFarFn c) = fun t => riemannKernelDeriv 1 t * ((bartaCutoff c 1 t : ℝ) : ℂ) +
      riemannKernelDeriv 0 t * ((deriv (bartaCutoff c 1) t : ℝ) : ℂ) := by
  funext t
  have hχ := ((differentiable_bartaCutoff c t).hasDerivAt).ofReal_comp
  exact ((hasDerivAt_riemannKernelDeriv 0 t).mul hχ).deriv

theorem deriv_deriv_bartaFarFn (c t : ℝ) :
    deriv (deriv (bartaFarFn c)) t =
      riemannKernelDeriv 2 t * ((bartaCutoff c 1 t : ℝ) : ℂ) +
        2 * (riemannKernelDeriv 1 t * ((deriv (bartaCutoff c 1) t : ℝ) : ℂ)) +
        riemannKernelDeriv 0 t * ((deriv (deriv (bartaCutoff c 1)) t : ℝ) : ℂ) := by
  rw [deriv_bartaFarFn]
  have hχ := ((differentiable_bartaCutoff c t).hasDerivAt).ofReal_comp
  have hχ' := ((differentiable_deriv_bartaCutoff c t).hasDerivAt).ofReal_comp
  have e2 : riemannKernelDeriv (1 + 1) = riemannKernelDeriv 2 := rfl
  have e1 : riemannKernelDeriv (0 + 1) = riemannKernelDeriv 1 := rfl
  have h : HasDerivAt (fun t => riemannKernelDeriv 1 t * ((bartaCutoff c 1 t : ℝ) : ℂ) +
      riemannKernelDeriv 0 t * ((deriv (bartaCutoff c 1) t : ℝ) : ℂ))
      (riemannKernelDeriv (1 + 1) t * ((bartaCutoff c 1 t : ℝ) : ℂ) +
        riemannKernelDeriv 1 t * ((deriv (bartaCutoff c 1) t : ℝ) : ℂ) +
        (riemannKernelDeriv (0 + 1) t * ((deriv (bartaCutoff c 1) t : ℝ) : ℂ) +
          riemannKernelDeriv 0 t * ((deriv (deriv (bartaCutoff c 1)) t : ℝ) : ℂ))) t :=
    ((hasDerivAt_riemannKernelDeriv 1 t).mul hχ).add ((hasDerivAt_riemannKernelDeriv 0 t).mul hχ')
  rw [h.deriv, e2, e1]
  ring

/-- The profile agrees with `Φ` near every point of `|t| < c - 1`. -/
theorem bartaFarFn_eventuallyEq {c t : ℝ} (ht : |t| < c - 1) :
    bartaFarFn c =ᶠ[𝓝 t] riemannKernelDeriv 0 := by
  have hopen : IsOpen {s : ℝ | |s| < c - 1} := isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds ht] with s hs
  unfold bartaFarFn
  rw [bartaCutoff_eq_one one_pos (le_of_lt hs)]
  simp

theorem deriv_deriv_bartaFarFn_of_abs_lt {c t : ℝ} (ht : |t| < c - 1) :
    deriv (deriv (bartaFarFn c)) t = riemannKernelDeriv 2 t := by
  rw [(bartaFarFn_eventuallyEq ht).deriv.deriv_eq, deriv_riemannKernelDeriv,
    deriv_riemannKernelDeriv]

/-- The radical defect `r = Φ'' − (Φχ)''`. -/
def bartaFarDefect (c t : ℝ) : ℂ := riemannKernelDeriv 2 t - deriv (deriv (bartaFarFn c)) t

theorem bartaFarDefect_eq_zero {c t : ℝ} (ht : |t| < c - 1) : bartaFarDefect c t = 0 := by
  rw [bartaFarDefect, deriv_deriv_bartaFarFn_of_abs_lt ht, sub_self]

theorem norm_bartaFarDefect_le {c Λ Λ₂ : ℝ} (hc : 1 < c)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (hΛ₂ : ∀ x : ℝ, |iteratedDeriv 2 Real.smoothTransition x| ≤ Λ₂) (t : ℝ) :
    ‖bartaFarDefect c t‖ ≤ 2 * ‖riemannKernelDeriv 2 t‖ + 4 * Λ * ‖riemannKernelDeriv 1 t‖ +
      Λ₂ * ‖riemannKernelDeriv 0 t‖ := by
  rw [bartaFarDefect, deriv_deriv_bartaFarFn]
  have h0 : |bartaCutoff c 1 t| ≤ 1 := by
    rw [abs_of_nonneg (bartaCutoff_nonneg c 1 t)]; exact bartaCutoff_le_one c 1 t
  have h1 : |deriv (bartaCutoff c 1) t| ≤ 2 * Λ := by
    have := abs_deriv_bartaCutoff_le (c := c) one_pos hΛ t
    rwa [div_one] at this
  have h2 := abs_deriv_deriv_bartaCutoff_le hc hΛ₂ t
  have n2 := norm_nonneg (riemannKernelDeriv 2 t)
  have n1 := norm_nonneg (riemannKernelDeriv 1 t)
  have n0 := norm_nonneg (riemannKernelDeriv 0 t)
  calc ‖riemannKernelDeriv 2 t - (riemannKernelDeriv 2 t * ((bartaCutoff c 1 t : ℝ) : ℂ) +
        2 * (riemannKernelDeriv 1 t * ((deriv (bartaCutoff c 1) t : ℝ) : ℂ)) +
        riemannKernelDeriv 0 t * ((deriv (deriv (bartaCutoff c 1)) t : ℝ) : ℂ))‖
      ≤ ‖riemannKernelDeriv 2 t‖ + (‖riemannKernelDeriv 2 t‖ * |bartaCutoff c 1 t| +
          2 * (‖riemannKernelDeriv 1 t‖ * |deriv (bartaCutoff c 1) t|) +
          ‖riemannKernelDeriv 0 t‖ * |deriv (deriv (bartaCutoff c 1)) t|) := by
        refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_ofNat]
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖riemannKernelDeriv 2 t‖ + (‖riemannKernelDeriv 2 t‖ * 1 +
          2 * (‖riemannKernelDeriv 1 t‖ * (2 * Λ)) + ‖riemannKernelDeriv 0 t‖ * Λ₂) := by
        gcongr
    _ = _ := by ring

theorem superExpDecay_of_continuous_hasCompactSupport {g : ℝ → ℂ} (hg : Continuous g)
    (hs : HasCompactSupport g) : SuperExpDecay g := by
  refine ⟨hg, fun c => ?_⟩
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  exact hs.norm.mul_right

/-! ## The far source -/

/-- The truncated kernel `Φ χ_{b+2,1}` as a smooth interior source at aperture `b + 3`. -/
def bartaFarAt (b : ℝ) (hb : 1 ≤ b) : CCMComplexSmoothInteriorSource (bartaAperture b hb) :=
  bartaSource (bartaAperture b hb) (b + 2) 1 one_pos (by show b + 2 < b + 3; linarith)

theorem coe_bartaFarAt (b : ℝ) (hb : 1 ≤ b) :
    ((bartaFarAt b hb).toSuzukiSmoothCompactTest : ℝ → ℂ) = bartaFarFn (b + 2) := by
  funext t
  rw [show ((bartaFarAt b hb).toSuzukiSmoothCompactTest : ℝ → ℂ) t = bartaFarAt b hb t from rfl,
    bartaFarAt, bartaSource_apply, bartaFarFn, bartaProfile, riemannKernelDeriv_zero,
    riemannPhiKernel_eq_ofReal]
  push_cast
  ring

theorem coe_derivTest_derivTest_bartaFarAt (b : ℝ) (hb : 1 ≤ b) :
    ((bartaFarAt b hb).toSuzukiSmoothCompactTest.derivTest.derivTest : ℝ → ℂ) =
      deriv (deriv (bartaFarFn (b + 2))) := by
  show deriv (deriv ((bartaFarAt b hb).toSuzukiSmoothCompactTest : ℝ → ℂ)) = _
  rw [coe_bartaFarAt]

theorem superExpDecay_bartaFarDefect (b : ℝ) (hb : 1 ≤ b) :
    SuperExpDecay (bartaFarDefect (b + 2)) := by
  have hc : Continuous (deriv (deriv (bartaFarFn (b + 2)))) := by
    rw [← coe_derivTest_derivTest_bartaFarAt b hb]
    exact SuzukiSmoothCompactTest.continuous _
  have hs : HasCompactSupport (deriv (deriv (bartaFarFn (b + 2)))) := by
    rw [← coe_derivTest_derivTest_bartaFarAt b hb]
    exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (SuzukiSmoothCompactTest.support_subset _)
  have h := (superExpDecay_riemannKernelDeriv 2).add
    ((superExpDecay_of_continuous_hasCompactSupport hc hs).const_mul (-1))
  have heq : (riemannKernelDeriv 2 + fun u => (-1 : ℂ) * deriv (deriv (bartaFarFn (b + 2))) u) =
      bartaFarDefect (b + 2) := by
    funext u; simp only [Pi.add_apply, bartaFarDefect]; ring
  rwa [heq] at h

/-- The weighted defect is pointwise `O(e^{−πe^{2b}} e^{−(b+1)} e^{−|u|})`. -/
theorem norm_bartaFarDefect_mul_exp_le {b Λ Λ₂ : ℝ} (hb : 1 ≤ b)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (hΛ₂ : ∀ x : ℝ, |iteratedDeriv 2 Real.smoothTransition x| ≤ Λ₂) (u : ℝ) :
    ‖bartaFarDefect (b + 2) u‖ * Real.exp (1 / 2 * |u|) ≤
      (2 * cuspDecayConst (riemannKernelPoly 2) + 4 * Λ * cuspDecayConst (riemannKernelPoly 1) +
        Λ₂ * cuspDecayConst (riemannKernelPoly 0)) *
        (Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(b + 1))) * Real.exp (-|u|) := by
  have hΛ0 : 0 ≤ Λ := le_trans (abs_nonneg _) (hΛ 0)
  have hΛ₂0 : 0 ≤ Λ₂ := le_trans (abs_nonneg _) (hΛ₂ 0)
  have hC0 := cuspDecayConst_nonneg (riemannKernelPoly 0)
  have hC1 := cuspDecayConst_nonneg (riemannKernelPoly 1)
  have hC2 := cuspDecayConst_nonneg (riemannKernelPoly 2)
  have hK0 : 0 ≤ 2 * cuspDecayConst (riemannKernelPoly 2) +
      4 * Λ * cuspDecayConst (riemannKernelPoly 1) + Λ₂ * cuspDecayConst (riemannKernelPoly 0) :=
    add_nonneg (add_nonneg (by linarith) (mul_nonneg (by linarith) hC1)) (mul_nonneg hΛ₂0 hC0)
  rcases lt_or_ge |u| (b + 1) with hu | hu
  · rw [bartaFarDefect_eq_zero (by linarith), norm_zero, zero_mul]
    exact mul_nonneg (mul_nonneg hK0 (by positivity)) (by positivity)
  set x := |u| with hx
  set G := Real.exp (17 / 2 * x) * Real.exp (-π * Real.exp (2 * x)) with hG
  have hk : ∀ k : ℕ, k ≤ 2 → ‖riemannKernelDeriv k u‖ ≤ cuspDecayConst (riemannKernelPoly k) * G := by
    intro k hk
    have h := norm_riemannKernelDeriv_le k u
    rw [← hx] at h
    refine h.trans ?_
    rw [hG, ← mul_assoc]
    gcongr
    · exact cuspDecayConst_nonneg _
    · have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
      have hx0 : 0 ≤ x := abs_nonneg u
      nlinarith
  have hr := norm_bartaFarDefect_le (c := b + 2) (by linarith) hΛ hΛ₂ u
  have hrG : ‖bartaFarDefect (b + 2) u‖ ≤
      (2 * cuspDecayConst (riemannKernelPoly 2) + 4 * Λ * cuspDecayConst (riemannKernelPoly 1) +
        Λ₂ * cuspDecayConst (riemannKernelPoly 0)) * G := by
    have h2 := hk 2 le_rfl
    have h1 := hk 1 (by norm_num)
    have h0 := hk 0 (by norm_num)
    have hG0 : 0 ≤ G := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4 * Λ by positivity),
      mul_le_mul_of_nonneg_left h0 hΛ₂0]
  have hcomp : G * Real.exp (1 / 2 * x) ≤
      Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(b + 1)) * Real.exp (-x) := by
    have h := exp_mul_exp_neg_pi_exp_le (c := 9) (by norm_num) hb hu
    have hsplit : G * Real.exp (1 / 2 * x) = Real.exp (9 * x) * Real.exp (-π * Real.exp (2 * x)) := by
      rw [hG, mul_right_comm, ← Real.exp_add]; ring_nf
    have h2x : Real.exp (-(2 * x)) ≤ Real.exp (-(b + 1)) * Real.exp (-x) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    rw [hsplit]
    calc Real.exp (9 * x) * Real.exp (-π * Real.exp (2 * x))
        ≤ Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(2 * x)) := h
      _ ≤ Real.exp (-π * Real.exp (2 * b)) * (Real.exp (-(b + 1)) * Real.exp (-x)) := by gcongr
      _ = _ := by ring
  calc ‖bartaFarDefect (b + 2) u‖ * Real.exp (1 / 2 * x)
      ≤ ((2 * cuspDecayConst (riemannKernelPoly 2) + 4 * Λ * cuspDecayConst (riemannKernelPoly 1) +
        Λ₂ * cuspDecayConst (riemannKernelPoly 0)) * G) * Real.exp (1 / 2 * x) := by gcongr
    _ = (2 * cuspDecayConst (riemannKernelPoly 2) + 4 * Λ * cuspDecayConst (riemannKernelPoly 1) +
        Λ₂ * cuspDecayConst (riemannKernelPoly 0)) * (G * Real.exp (1 / 2 * x)) := by ring
    _ ≤ _ := by
        rw [mul_assoc _ (Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(b + 1)))]
        exact mul_le_mul_of_nonneg_left hcomp hK0

/-! ## The zero side of the far source -/

theorem xiSpectralPoint_eq_gammaOf (q : XiZeroCopy) : xiSpectralPoint q = gammaOf (q.1 : ℂ) := by
  rw [xiSpectralPoint, gammaOf, Complex.div_I]
  ring

theorem paperFT_riemannKernelDeriv_neg_xiSpectralPoint (k : ℕ) (q : XiZeroCopy) :
    paperFT (riemannKernelDeriv k) (-xiSpectralPoint q) = 0 := by
  rw [← xiSpectralPoint_reflect, xiSpectralPoint_eq_gammaOf]
  exact (paperFT_riemannKernelDeriv_at_zero k (xiZeroCopy_mem_carrier _)).1

/-- At every zero, `‖γ‖² |Ŝ(−γ)| ≤ ∫ |r| e^{|u|/2}`. -/
theorem sq_norm_mul_norm_suzukiSmoothFourier_bartaFarAt_le (b : ℝ) (hb : 1 ≤ b)
    (q : XiZeroCopy) :
    ‖xiSpectralPoint q‖ ^ 2 *
        ‖suzukiSmoothFourier (bartaFarAt b hb).toSuzukiSmoothCompactTest (-xiSpectralPoint q)‖ ≤
      ∫ u : ℝ, ‖bartaFarDefect (b + 2) u‖ * Real.exp (1 / 2 * |u|) := by
  set ψ := (bartaFarAt b hb).toSuzukiSmoothCompactTest with hψ
  set z := -xiSpectralPoint q with hz
  have hIm : |z.im| ≤ 1 / 2 := by
    have := xiSpectralPoint_im_mem_openHalf q
    rw [hz, Complex.neg_im, abs_neg, abs_le]
    constructor <;> linarith [this.1, this.2]
  have h1 := suzukiSmoothFourier_derivTest ψ.derivTest z
  have h2 := suzukiSmoothFourier_derivTest ψ z
  have hFT2 : suzukiSmoothFourier ψ.derivTest.derivTest z =
      paperFT (deriv (deriv (bartaFarFn (b + 2)))) z := by
    unfold suzukiSmoothFourier paperFT
    rw [show (ψ.derivTest.derivTest : ℝ → ℂ) = deriv (deriv (bartaFarFn (b + 2))) from
      coe_derivTest_derivTest_bartaFarAt b hb]
  have hint1 := (superExpDecay_riemannKernelDeriv 2).integrable_mul_cexp z
  have hint2 : Integrable fun u : ℝ =>
      deriv (deriv (bartaFarFn (b + 2))) u * Complex.exp (I * z * (u : ℂ)) := by
    have := ψ.derivTest.derivTest.integrable_fourierIntegrand z
    rwa [show ψ.derivTest.derivTest.toFun = deriv (deriv (bartaFarFn (b + 2))) from
      coe_derivTest_derivTest_bartaFarAt b hb] at this
  have hsplit : paperFT (deriv (deriv (bartaFarFn (b + 2)))) z =
      -paperFT (bartaFarDefect (b + 2)) z := by
    have hr : paperFT (bartaFarDefect (b + 2)) z =
        paperFT (riemannKernelDeriv 2) z - paperFT (deriv (deriv (bartaFarFn (b + 2)))) z := by
      unfold paperFT
      rw [← integral_sub hint1 hint2]
      congr 1; funext u; rw [bartaFarDefect]; ring
    rw [hr, hz, paperFT_riemannKernelDeriv_neg_xiSpectralPoint, zero_sub, neg_neg]
  have hkey : ‖z‖ ^ 2 * ‖suzukiSmoothFourier ψ z‖ = ‖paperFT (bartaFarDefect (b + 2)) z‖ := by
    rw [← norm_neg (paperFT _ z), ← hsplit, ← hFT2, h1, h2]
    rw [show -(I * z) * (-(I * z) * suzukiSmoothFourier ψ z) =
      (I * z) ^ 2 * suzukiSmoothFourier ψ z by ring]
    rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul]
  rw [show ‖xiSpectralPoint q‖ = ‖z‖ by rw [hz, norm_neg], hkey]
  exact norm_paperFT_le_weighted (superExpDecay_bartaFarDefect b hb) hIm

/-- The zero kernel of the far source is uniformly `≤ e^{|t|/2} E S_Ξ`. -/
theorem norm_zeroKernel_bartaFarAt_le (b : ℝ) (hb : 1 ≤ b) {E : ℝ}
    (hE : ∫ u : ℝ, ‖bartaFarDefect (b + 2) u‖ * Real.exp (1 / 2 * |u|) ≤ E) (t : ℝ) :
    ‖zeroKernel (bartaFarAt b hb).toSuzukiSmoothCompactTest t‖ ≤
      Real.exp (|t| / 2) * (E * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) := by
  have hq : ∀ q : XiZeroCopy, ‖suzukiSmoothFourier (bartaFarAt b hb).toSuzukiSmoothCompactTest
      (-xiSpectralPoint q)‖ ≤ E * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    intro q
    have h := sq_norm_mul_norm_suzukiSmoothFourier_bartaFarAt_le b hb q
    have hpos : 0 < ‖xiSpectralPoint q‖ ^ 2 := by
      have := xiSpectralPoint_ne_zero q
      positivity
    rw [mul_one_div, le_div_iff₀ hpos, mul_comm]
    exact h.trans hE
  have hsum : HasSum (fun q : XiZeroCopy =>
      Real.exp (|t| / 2) * (E * (1 / ‖xiSpectralPoint q‖ ^ 2)))
      (Real.exp (|t| / 2) * (E * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    (xiSpectralPoint_inv_sq_summable.hasSum.mul_left E).mul_left _
  refine tsum_of_norm_bounded hsum fun q => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul (norm_cexp_I_mul_xiSpectralPoint_le q t) (hq q) (norm_nonneg _)
    (Real.exp_pos _).le

/-- The form against the far source is `≤ e^{a/2} E S_Ξ ∫|x|`. -/
theorem norm_ccmRestrictedWeilForm_bartaFarAt_le (b : ℝ) (hb : 1 ≤ b) {E : ℝ}
    (hE : ∫ u : ℝ, ‖bartaFarDefect (b + 2) u‖ * Real.exp (1 / 2 * |u|) ≤ E) (hE0 : 0 ≤ E)
    (x : CCMArchimedeanFormDomain (bartaAperture b hb)) :
    ‖ccmRestrictedWeilForm (bartaAperture b hb) x (bartaFarAt b hb).toCCMFormVector‖ ≤
      (∫ t, ‖timeRep (bartaAperture b hb) x t‖) *
        (Real.exp ((b + 3) / 2) * (E * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2)) := by
  have hSΞ0 : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 :=
    tsum_nonneg fun q => by positivity
  have hsupp := bound_support_of_supportedIn (supportedIn_timeRep (bartaAperture b hb) x)
  have hint := integrable_timeRep (bartaAperture b hb) x
  rw [ccmRestrictedWeilForm_eq_integral_representer, integral_timeRep_formRepresenter_eq,
    ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (ae_of_all _ fun t => norm_nonneg _) (hint.norm.mul_const _) (ae_of_all _ fun t => ?_))
  simp only
  rw [norm_mul, Complex.norm_conj]
  by_cases hx : timeRep (bartaAperture b hb) x t = 0
  · rw [hx, norm_zero, zero_mul, zero_mul]
  · have ht : |t| ≤ b + 3 := hsupp t hx
    refine mul_le_mul_of_nonneg_left ((norm_zeroKernel_bartaFarAt_le b hb hE t).trans ?_)
      (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (mul_nonneg hE0 hSΞ0)

/-- **The far bound.** There is `C` with `|Q_{b+3}(x, Φχ_{b+2,1})| ≤ C Φ(b − 2w) ∫|x|` for all
`b ≥ 1` and every vector `x` of the form domain. -/
theorem exists_bartaFar_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ) (hb : 1 ≤ b)
    (x : CCMArchimedeanFormDomain (bartaAperture b hb)),
    ‖ccmRestrictedWeilForm (bartaAperture b hb) x (bartaFarAt b hb).toCCMFormVector‖ ≤
      (∫ t, ‖timeRep (bartaAperture b hb) x t‖) * (bartaEdge b * C) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨Λ₂, hΛ₂0, hΛ₂⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_iteratedDeriv_smoothTransition 2
  have hC0 := cuspDecayConst_nonneg (riemannKernelPoly 0)
  have hC1 := cuspDecayConst_nonneg (riemannKernelPoly 1)
  have hC2 := cuspDecayConst_nonneg (riemannKernelPoly 2)
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 2 * cuspDecayConst (riemannKernelPoly 2) +
      4 * Λ * cuspDecayConst (riemannKernelPoly 1) + Λ₂ * cuspDecayConst (riemannKernelPoly 0) :=
    ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]
    exact add_nonneg (add_nonneg (by linarith) (mul_nonneg (by linarith) hC1)) (mul_nonneg hΛ₂0 hC0)
  obtain ⟨SΞ, hSΞ⟩ : ∃ SΞ : ℝ, SΞ = ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := ⟨_, rfl⟩
  have hSΞ0 : 0 ≤ SΞ := by rw [hSΞ]; exact tsum_nonneg fun q => by positivity
  refine ⟨2 * K₀ * SΞ * Real.exp (1 / 2),
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK₀0) hSΞ0) (Real.exp_pos _).le,
    fun b hb x => ?_⟩
  have hε0 : 0 ≤ Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(b + 1)) := by positivity
  have hE : ∫ u : ℝ, ‖bartaFarDefect (b + 2) u‖ * Real.exp (1 / 2 * |u|) ≤
      2 * (K₀ * (Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(b + 1)))) := by
    have hint := (superExpDecay_bartaFarDefect b hb).2 (1 / 2)
    calc ∫ u : ℝ, ‖bartaFarDefect (b + 2) u‖ * Real.exp (1 / 2 * |u|)
        ≤ ∫ u : ℝ, K₀ * (Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(b + 1))) *
            Real.exp (-|u|) :=
          integral_mono hint (integrable_exp_neg_abs.const_mul _) fun u => by
            rw [hK₀]; exact norm_bartaFarDefect_mul_exp_le hb hΛ hΛ₂ u
      _ = 2 * (K₀ * (Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(b + 1)))) := by
          rw [integral_const_mul, integral_exp_neg_abs]; ring
  have hbound := norm_ccmRestrictedWeilForm_bartaFarAt_le b hb hE
    (mul_nonneg (by norm_num) (mul_nonneg hK₀0 hε0)) x
  rw [← hSΞ] at hbound
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ (integral_nonneg fun _ => norm_nonneg _))
  have hΦ : Real.exp (-π * Real.exp (2 * b)) ≤ bartaEdge b := by
    have hs0 := (bartaInner_pos hb).le
    have hsb : bartaInner b ≤ b := by unfold bartaInner; linarith [bartaWidth_pos b]
    refine le_trans ?_ (exp_neg_pi_exp_le_riemannKernelReal hs0)
    apply Real.exp_le_exp.mpr
    have := Real.exp_le_exp.mpr (show 2 * bartaInner b ≤ 2 * b by linarith)
    nlinarith [Real.pi_pos]
  have hexp : Real.exp ((b + 3) / 2) * Real.exp (-(b + 1)) ≤ Real.exp (1 / 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  calc Real.exp ((b + 3) / 2) *
        (2 * (K₀ * (Real.exp (-π * Real.exp (2 * b)) * Real.exp (-(b + 1)))) * SΞ)
      = (2 * K₀ * SΞ) * Real.exp (-π * Real.exp (2 * b)) *
          (Real.exp ((b + 3) / 2) * Real.exp (-(b + 1))) := by ring
    _ ≤ (2 * K₀ * SΞ) * bartaEdge b * Real.exp (1 / 2) := by
        have h0 : 0 ≤ 2 * K₀ * SΞ := mul_nonneg (mul_nonneg (by norm_num) hK₀0) hSΞ0
        have h1 : 0 ≤ 2 * K₀ * SΞ * bartaEdge b := mul_nonneg h0 (bartaEdge_pos b).le
        gcongr
    _ = bartaEdge b * (2 * K₀ * SΞ * Real.exp (1 / 2)) := by ring

end

end RHTower
