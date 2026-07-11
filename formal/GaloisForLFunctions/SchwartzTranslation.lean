import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.Taylor

/-!
# Translation on Schwartz space

Mathlib supplies composition of a Schwartz function with a temperate antilipschitz map, but does
not package additive translation as a named continuous linear action.  This module builds that
action, proves its group law, inverse law, continuity for each fixed translation parameter, and
commutation with directional differentiation.  It is the reusable first layer needed to turn a
momentum-symmetry identity for a continuous Schwartz form into simultaneous-translation
invariance.
-/

open Function

namespace SchwartzMap

open LineDeriv

variable (𝕜 : Type*) {E F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

/-- Right translation `f(x) ↦ f(x + a)` as a continuous linear map on Schwartz space. -/
def translateCLM (a : E) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) := by
  have hg : (fun x : E => x + a).HasTemperateGrowth :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const a)
  have hi : Isometry (fun x : E => x + a) := by
    apply Isometry.of_dist_eq
    intro x y
    simp [dist_eq_norm]
  exact SchwartzMap.compCLMOfAntilipschitz 𝕜 hg hi.antilipschitz

@[simp] theorem translateCLM_apply (a : E) (f : 𝓢(E, F)) (x : E) :
    translateCLM 𝕜 a f x = f (x + a) := rfl

@[simp] theorem translateCLM_zero (f : 𝓢(E, F)) :
    translateCLM 𝕜 (0 : E) f = f := by
  ext x
  simp

/-- The right-translation convention gives `T_a T_b = T_(a+b)`. -/
theorem translateCLM_add (a b : E) (f : 𝓢(E, F)) :
    translateCLM 𝕜 a (translateCLM 𝕜 b f) = translateCLM 𝕜 (a + b) f := by
  ext x
  simp [add_assoc]

@[simp] theorem translateCLM_neg_left (a : E) (f : 𝓢(E, F)) :
    translateCLM 𝕜 (-a) (translateCLM 𝕜 a f) = f := by
  rw [translateCLM_add, neg_add_cancel, translateCLM_zero]

@[simp] theorem translateCLM_neg_right (a : E) (f : 𝓢(E, F)) :
    translateCLM 𝕜 a (translateCLM 𝕜 (-a) f) = f := by
  rw [translateCLM_add, add_neg_cancel, translateCLM_zero]

/-- Translation commutes with every Schwartz directional derivative. -/
theorem lineDerivOp_translateCLM (a m : E) (f : 𝓢(E, F)) :
    ∂_{m} (translateCLM 𝕜 a f) = translateCLM 𝕜 a (∂_{m} f) := by
  ext x
  rw [lineDerivOp_apply_eq_fderiv]
  simp only [translateCLM_apply]
  rw [lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y : E => f (y + a)) x m = fderiv ℝ f (x + a) m
  have hshift : HasFDerivAt (fun y : E => y + a) (ContinuousLinearMap.id ℝ E) x := by
    simpa only [id_eq] using (hasFDerivAt_id (𝕜 := ℝ) x).add_const a
  have hcomp := (f.hasFDerivAt (x + a)).comp x hshift
  have hfderiv := hcomp.fderiv
  change (fderiv ℝ (f ∘ fun y : E => y + a) x) m = fderiv ℝ f (x + a) m
  rw [hfderiv]
  rfl

/-! ## One-dimensional strong-orbit infrastructure -/

/-- Iterating the ordinary derivative `m` times after `n` times is the `(n+m)`-th derivative.
This elementary composition law is not currently packaged by mathlib's iterated-derivative API. -/
theorem iteratedDeriv_iteratedDeriv {f : ℝ → ℂ} (m n : ℕ) :
    iteratedDeriv m (iteratedDeriv n f) = iteratedDeriv (n + m) f := by
  simp only [iteratedDeriv_eq_iterate]
  rw [← Function.iterate_add_apply, Nat.add_comm]

/-- Two-sided directional Taylor estimate for a difference quotient.  The unit direction `c`
encodes the sign of the real step, so one theorem handles both right and left translation
increments. -/
theorem directionalDifferenceQuotientError_le
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) {y c r C : ℝ}
    (hr : 0 < r) (hc : |c| = 1)
    (hC : ∀ t ∈ Set.Icc 0 r, ‖iteratedDeriv 2 g (y + c * t)‖ ≤ C) :
    ‖((c * r)⁻¹ : ℝ) • (g (y + c * r) - g y) - deriv g y‖ ≤ C * r := by
  let psi : ℝ → ℂ := fun t => g (y + c * t)
  have hpsi : ContDiff ℝ 2 psi := by
    dsimp only [psi]
    exact hg.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hud : UniqueDiffOn ℝ (Set.Icc 0 r) := uniqueDiffOn_Icc hr
  have hpsi_two (t : ℝ) :
      iteratedDeriv 2 psi t = (c ^ 2 : ℝ) • iteratedDeriv 2 g (y + c * t) := by
    let gy : ℝ → ℂ := fun u => g (y + u)
    have hgy : ContDiff ℝ 2 gy := hg.comp (contDiff_const.add contDiff_id)
    have hs := congrFun (iteratedDeriv_comp_const_smul hgy c) t
    dsimp only [gy] at hs
    change iteratedDeriv 2 (fun x : ℝ => g (y + c * x)) t = _
    rw [hs]
    rw [congrFun (iteratedDeriv_comp_const_add 2 g y) (c * t)]
  have hCpsi : ∀ t ∈ Set.Icc 0 r,
      ‖iteratedDerivWithin 2 psi (Set.Icc 0 r) t‖ ≤ C := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 2) hud hpsi.contDiffAt ht]
    rw [hpsi_two]
    rw [norm_smul, Real.norm_eq_abs, abs_pow, hc, one_pow, one_mul]
    simpa [add_comm] using hC t ht
  have hTaylor := taylor_mean_remainder_bound (n := 1) (a := 0) (b := r)
    (x := r) (C := C) (le_of_lt hr) hpsi.contDiffOn
    (Set.right_mem_Icc.mpr (le_of_lt hr)) hCpsi
  have hpsi_one : iteratedDerivWithin 1 psi (Set.Icc 0 r) 0 = deriv psi 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1) hud
      (hpsi.of_le (by norm_num)).contDiffAt
      (Set.left_mem_Icc.mpr (le_of_lt hr))]
    exact congrFun iteratedDeriv_one 0
  have hpsi_deriv : deriv psi 0 = c • deriv g y := by
    have hgy : ContDiff ℝ 1 (fun u : ℝ => g (y + u)) :=
      (hg.of_le (by norm_num)).comp (contDiff_const.add contDiff_id)
    have hs := congrFun (iteratedDeriv_comp_const_smul hgy c) 0
    rw [show deriv psi 0 = iteratedDeriv 1 (fun x : ℝ => g (y + c * x)) 0 by
      simp [psi]]
    rw [hs]
    simp only [pow_one, mul_zero]
    rw [congrFun (iteratedDeriv_comp_const_add 1 g y) 0]
    simp
  have hTaylor' :
      ‖g (y + c * r) - (g y + r • (c • deriv g y))‖ ≤ C * r ^ 2 := by
    have htaylorEval : taylorWithinEval psi 1 (Set.Icc 0 r) 0 r =
        psi 0 + r • deriv psi 0 := by
      rw [show (1 : ℕ) = 0 + 1 by omega, taylorWithinEval_succ,
        taylor_within_zero_eval, hpsi_one]
      norm_num
    rw [htaylorEval] at hTaylor
    simpa [psi, hpsi_deriv] using hTaylor
  have hc0 : c ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hc
    norm_num at hc
  have hcr : c * r ≠ 0 := mul_ne_zero hc0 (ne_of_gt hr)
  have hid : ((c * r)⁻¹ : ℝ) • (g (y + c * r) - g y) - deriv g y =
      ((c * r)⁻¹ : ℝ) •
        (g (y + c * r) - (g y + r • (c • deriv g y))) := by
    symm
    calc
      ((c * r)⁻¹ : ℝ) •
          (g (y + c * r) - (g y + r • (c • deriv g y))) =
          ((c * r)⁻¹ : ℝ) • (g (y + c * r) - g y) -
            ((c * r)⁻¹ : ℝ) • (r • (c • deriv g y)) := by module
      _ = ((c * r)⁻¹ : ℝ) • (g (y + c * r) - g y) - deriv g y := by
        congr 1
        rw [smul_smul, smul_smul]
        have hcoef : (c * r)⁻¹ * r * c = 1 := by field_simp
        rw [hcoef, one_smul]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_inv, abs_mul, hc, one_mul]
  have hrabs : |r| = r := abs_of_pos hr
  rw [hrabs]
  calc
    r⁻¹ * ‖g (y + c * r) - (g y + r • (c • deriv g y))‖
        ≤ r⁻¹ * (C * r ^ 2) := by gcongr
    _ = C * r := by field_simp

/-- Difference quotient for the real translation parameter on complex-valued Schwartz space. -/
noncomputable def translateDifferenceQuotient (a h : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (h⁻¹ : ℝ) • (translateCLM ℂ (a + h) f - translateCLM ℂ a f)

/-- Difference between the translation difference quotient and its candidate Schwartz derivative. -/
noncomputable def translateDifferenceQuotientError (a h : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  translateDifferenceQuotient a h f - translateCLM ℂ a (derivCLM ℂ ℂ f)

/-- Every derivative of the translation difference-quotient error is the corresponding ordinary
difference quotient of the iterated derivative.  This is the exact algebraic reduction required
before proving convergence in every Schwartz seminorm. -/
theorem iteratedDeriv_translateDifferenceQuotientError
    (a h x : ℝ) (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    iteratedDeriv n (translateDifferenceQuotientError a h f) x =
      (h⁻¹ : ℝ) •
        (iteratedDeriv n f (x + (a + h)) - iteratedDeriv n f (x + a)) -
          iteratedDeriv (n + 1) f (x + a) := by
  change iteratedDeriv n
      (fun y : ℝ => (h⁻¹ : ℝ) • (f (y + (a + h)) - f (y + a)) - deriv f (y + a)) x = _
  have h₁ : ContDiffAt ℝ n (fun y : ℝ => f (y + (a + h))) x :=
    ((f.smooth n).comp (contDiff_id.add contDiff_const)).contDiffAt
  have h₂ : ContDiffAt ℝ n (fun y : ℝ => f (y + a)) x :=
    ((f.smooth n).comp (contDiff_id.add contDiff_const)).contDiffAt
  have hd : ContDiffAt ℝ n (fun y : ℝ => deriv f (y + a)) x := by
    simpa only [derivCLM_apply] using
      (((derivCLM ℂ ℂ f).smooth n).comp (contDiff_id.add contDiff_const)).contDiffAt
  have hsub : iteratedDeriv n
      (fun y : ℝ => f (y + (a + h)) - f (y + a)) x =
      iteratedDeriv n f (x + (a + h)) - iteratedDeriv n f (x + a) := by
    change iteratedDeriv n
      ((fun y : ℝ => f (y + (a + h))) - (fun y : ℝ => f (y + a))) x = _
    rw [iteratedDeriv_sub h₁ h₂]
    exact congrArg₂ (· - ·)
      (congrFun (iteratedDeriv_comp_add_const n f (a + h)) x)
      (congrFun (iteratedDeriv_comp_add_const n f a) x)
  have hderivshift : iteratedDeriv n (fun y : ℝ => deriv f (y + a)) x =
      iteratedDeriv (n + 1) f (x + a) := by
    rw [congrFun (iteratedDeriv_comp_add_const n (deriv f) a) x]
    rw [congrFun iteratedDeriv_succ' (x + a)]
  change iteratedDeriv n
      (((h⁻¹ : ℝ) • (fun y : ℝ => f (y + (a + h)) - f (y + a))) -
        (fun y : ℝ => deriv f (y + a))) x = _
  calc
    _ = iteratedDeriv n ((h⁻¹ : ℝ) •
          (fun y : ℝ => f (y + (a + h)) - f (y + a))) x -
        iteratedDeriv n (fun y : ℝ => deriv f (y + a)) x :=
      iteratedDeriv_sub ((h₁.sub h₂).const_smul (h⁻¹ : ℝ)) hd
    _ = (h⁻¹ : ℝ) • iteratedDeriv n
          (fun y : ℝ => f (y + (a + h)) - f (y + a)) x -
        iteratedDeriv n (fun y : ℝ => deriv f (y + a)) x := by
      rw [iteratedDeriv_const_smul (h₁.sub h₂) (h⁻¹ : ℝ)]
    _ = _ := by
      rw [hsub, hderivshift]

/-- Uniform weighted derivative control under a bounded translation.  This supplies the precise
Schwartz-seminorm majorant needed for the Taylor remainder in the translation parameter. -/
theorem weighted_iteratedDeriv_translate_bound
    (f : 𝓢(ℝ, ℂ)) (a t x : ℝ) (k m : ℕ) (ht : |t| ≤ 1) :
    |x| ^ k * ‖iteratedDeriv m f (x + a + t)‖ ≤
      (2 + |a|) ^ k *
        (2 ^ k * ((Finset.Iic (k, m)).sup
          (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) f) := by
  let z : ℝ := x + a + t
  have hxtriangle : |x| ≤ |z| + |a| + |t| := by
    have hident : z + -a + -t = x := by dsimp [z]; ring
    rw [← hident]
    calc
      |z + -a + -t| ≤ |z + -a| + |-t| := abs_add_le _ _
      _ ≤ |z| + |-a| + |-t| := by gcongr; exact abs_add_le z (-a)
      _ = |z| + |a| + |t| := by rw [abs_neg, abs_neg]
  have hx : |x| ≤ (2 + |a|) * (1 + |z|) := by
    have ha : 0 ≤ |a| := abs_nonneg a
    have hz : 0 ≤ |z| := abs_nonneg z
    calc
      |x| ≤ |z| + |a| + |t| := hxtriangle
      _ ≤ |z| + |a| + 1 := by linarith
      _ ≤ (2 + |a|) * (1 + |z|) := by nlinarith
  have hbase := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (k, m)) (k := k) (n := m) le_rfl le_rfl f z
  rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hbase
  calc
    |x| ^ k * ‖iteratedDeriv m f z‖ ≤
        ((2 + |a|) * (1 + |z|)) ^ k * ‖iteratedDeriv m f z‖ := by
      gcongr
    _ = (2 + |a|) ^ k *
        ((1 + |z|) ^ k * ‖iteratedDeriv m f z‖) := by rw [mul_pow]; ring
    _ ≤ (2 + |a|) ^ k *
        (2 ^ k * ((Finset.Iic (k, m)).sup
          (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) f) := by
      gcongr

/-- Pointwise Taylor bound for every iterated derivative of the translation difference-quotient
error.  The constant is uniform in the spatial variable and linear in the translation step. -/
theorem weighted_iteratedDeriv_translateDifferenceQuotientError_le
    (f : 𝓢(ℝ, ℂ)) (a h x : ℝ) (k n : ℕ) (hh0 : h ≠ 0) (hh1 : |h| ≤ 1) :
    |x| ^ k * ‖iteratedDeriv n (translateDifferenceQuotientError a h f) x‖ ≤
      ((2 + |a|) ^ k *
        (2 ^ k * ((Finset.Iic (k, n + 2)).sup
          (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) f)) * |h| := by
  let r : ℝ := |h|
  let c : ℝ := h / r
  let y : ℝ := x + a
  let g : ℝ → ℂ := iteratedDeriv n f
  let gx : ℝ → ℂ := fun u => |x| ^ k • g u
  let C : ℝ := (2 + |a|) ^ k *
    (2 ^ k * ((Finset.Iic (k, n + 2)).sup
      (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) f)
  have hr : 0 < r := by dsimp [r]; exact abs_pos.mpr hh0
  have hc : |c| = 1 := by
    dsimp [c, r]
    rw [abs_div, abs_abs, div_self (ne_of_gt (abs_pos.mpr hh0))]
  have hcr : c * r = h := by
    dsimp [c, r]
    field_simp
  have hg : ContDiff ℝ 2 g := by
    apply (contDiff_nat_iff_iteratedDeriv).2
    constructor
    · intro m _hm
      have hm : iteratedDeriv m g = iteratedDeriv (n + m) f := by
        dsimp only [g]
        exact iteratedDeriv_iteratedDeriv m n
      rw [hm]
      exact (f.smooth (n + m)).continuous_iteratedDeriv' (n + m)
    · intro m _hm
      have hm : iteratedDeriv m g = iteratedDeriv (n + m) f := by
        dsimp only [g]
        exact iteratedDeriv_iteratedDeriv m n
      rw [hm]
      exact (f.smooth (n + m + 1)).differentiable_iteratedDeriv' (n + m)
  have hgx : ContDiff ℝ 2 gx := hg.const_smul (|x| ^ k)
  have hiter_gx (u : ℝ) :
      iteratedDeriv 2 gx u = |x| ^ k • iteratedDeriv (n + 2) f u := by
    change iteratedDeriv 2 ((|x| ^ k : ℝ) • g) u = _
    rw [iteratedDeriv_const_smul hg.contDiffAt (|x| ^ k)]
    rw [congrFun (iteratedDeriv_iteratedDeriv 2 n) u]
  have hderiv_gx (u : ℝ) :
      deriv gx u = |x| ^ k • iteratedDeriv (n + 1) f u := by
    rw [← congrFun iteratedDeriv_one u]
    change iteratedDeriv 1 ((|x| ^ k : ℝ) • g) u = _
    rw [iteratedDeriv_const_smul (n := 1)
      (hg.of_le (by norm_num)).contDiffAt (|x| ^ k)]
    rw [congrFun (iteratedDeriv_iteratedDeriv 1 n) u]
  have hC : ∀ t ∈ Set.Icc 0 r,
      ‖iteratedDeriv 2 gx (y + c * t)‖ ≤ C := by
    intro t ht
    rw [hiter_gx, norm_smul, Real.norm_eq_abs, abs_pow, abs_abs]
    have htbound : |c * t| ≤ 1 := by
      rw [abs_mul, hc, one_mul, abs_of_nonneg ht.1]
      exact ht.2.trans hh1
    simpa [C, y, add_assoc] using
      weighted_iteratedDeriv_translate_bound f a (c * t) x k (n + 2) htbound
  have hdir := directionalDifferenceQuotientError_le hgx hr hc hC
  rw [hcr] at hdir
  have hscaled : |x| ^ k •
      ((h⁻¹ : ℝ) • (g (y + h) - g y) - iteratedDeriv (n + 1) f y) =
      (h⁻¹ : ℝ) • (gx (y + h) - gx y) - deriv gx y := by
    rw [hderiv_gx]
    dsimp only [gx]
    module
  rw [iteratedDeriv_translateDifferenceQuotientError]
  rw [show x + (a + h) = y + h by dsimp [y]; ring,
    show x + a = y by rfl]
  change |x| ^ k *
      ‖(h⁻¹ : ℝ) • (g (y + h) - g y) - iteratedDeriv (n + 1) f y‖ ≤ C * r
  have hpowabs : ‖(|x| ^ k : ℝ)‖ = |x| ^ k := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  rw [← hpowabs, ← norm_smul, hscaled]
  exact hdir

/-- Every Schwartz seminorm of the translation difference-quotient error is `O(|h|)` with an
explicit bound from finitely many higher seminorms of the original function. -/
theorem seminorm_translateDifferenceQuotientError_le
    (f : 𝓢(ℝ, ℂ)) (a h : ℝ) (k n : ℕ) (hh0 : h ≠ 0) (hh1 : |h| ≤ 1) :
    SchwartzMap.seminorm ℂ k n (translateDifferenceQuotientError a h f) ≤
      ((2 + |a|) ^ k *
        (2 ^ k * ((Finset.Iic (k, n + 2)).sup
          (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) f)) * |h| := by
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℂ) k n
  · positivity
  · intro x
    exact weighted_iteratedDeriv_translateDifferenceQuotientError_le
      f a h x k n hh0 hh1

end SchwartzMap
