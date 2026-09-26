import GaloisForLFunctions.RHTower.ThetaCuspChargeModularCriticality

open Complex Real MeasureTheory Set Filter Topology Polynomial

noncomputable section

namespace RHTower

/-- The renewal increment of a source form in logarithmic coordinates:
`ν_F(2x)/2 = −e^{x/2}·p·F'(p)`, `p = ie^{2x}`.  For `F = θ₃` this is `π Σ n²e^{5x/2−πn²e^{2x}}`. -/
def renewalInc (F : ℂ → ℂ) (x : ℝ) : ℂ :=
  -((Real.exp (x / 2) : ℂ) * modAxisPoint x * deriv F (modAxisPoint x))

theorem renewalInc_eq_tail (F : ℂ → ℂ) (c : ℂ) (x : ℝ) :
    renewalInc F x = modTail F c x / 2 - modTailDeriv F c x := by
  unfold renewalInc modTail modTailDeriv; ring

/-! ### The theta increment -/

theorem thetaCuspTailDerivativePolynomial_one :
    thetaCuspTailDerivativePolynomial 1 = C (1 / 2) - C (2 * Real.pi) * X ^ (2 : ℕ) := by
  simp [thetaCuspTailDerivativePolynomial, thetaCuspLogDerivativeStep]

/-- The positive atom of the theta increment. -/
def thetaIncAtom (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (x / 2) * (2 * Real.pi * ((n + 1 : ℝ) * Real.exp x) ^ 2) *
    Real.exp (-Real.pi * ((n + 1 : ℝ) * Real.exp x) ^ (2 : ℕ))

theorem thetaIncAtom_pos (x : ℝ) (n : ℕ) : 0 < thetaIncAtom x n := by
  unfold thetaIncAtom; positivity

theorem thetaIncAtom_eq (x : ℝ) (n : ℕ) :
    thetaIncAtom x n =
      thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 0) (n + 1) x / 2 -
        thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) (n + 1) x := by
  rw [thetaCuspTailDerivativePolynomial_one]
  simp [thetaIncAtom, thetaCuspPolynomialAtom, thetaCuspTailDerivativePolynomial]
  ring

theorem summable_thetaIncAtom (x : ℝ) : Summable (thetaIncAtom x) := by
  have h0 := summable_thetaCuspTailDerivative 0 x
  have h1 := summable_thetaCuspTailDerivative 1 x
  have := (h0.div_const 2).sub h1
  refine this.congr (fun n => ?_)
  rw [thetaIncAtom_eq]

theorem thetaInc_eq_tsum (x : ℝ) :
    thetaCuspTailDerivative 0 x / 2 - thetaCuspTailDerivative 1 x = ∑' n, thetaIncAtom x n := by
  have h0 := summable_thetaCuspTailDerivative 0 x
  have h1 := summable_thetaCuspTailDerivative 1 x
  unfold thetaCuspTailDerivative
  rw [← tsum_div_const, ← (h0.div_const 2).tsum_sub h1]
  exact tsum_congr (fun n => (thetaIncAtom_eq x n).symm)

theorem renewalInc_thetaGroupBasis_zero (x : ℝ) :
    renewalInc (thetaGroupBasis 0) x = ((∑' n, thetaIncAtom x n : ℝ) : ℂ) := by
  rw [renewalInc_eq_tail _ 1, modTail_thetaGroupBasis_zero, modTailDeriv_thetaGroupBasis_zero,
    ← thetaInc_eq_tsum]
  push_cast; ring

theorem thetaInc_pos (x : ℝ) : 0 < ∑' n, thetaIncAtom x n :=
  (summable_thetaIncAtom x).tsum_pos (fun n => (thetaIncAtom_pos x n).le) 0 (thetaIncAtom_pos x 0)

theorem thetaInc_ge_first (x : ℝ) : thetaIncAtom x 0 ≤ ∑' n, thetaIncAtom x n :=
  (summable_thetaIncAtom x).le_tsum 0 (fun n _ => (thetaIncAtom_pos x n).le)

/-- For `e^{2x} ≥ 3` the increment is a small fraction of `e^{x/2}`. -/
theorem thetaInc_le_small {x : ℝ} (hy : 3 ≤ Real.exp (2 * x)) :
    ∑' n, thetaIncAtom x n ≤ Real.exp (x / 2) / 3 := by
  set r : ℝ := Real.exp (-(3 * Real.pi / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 / 50 := by
    have h1 : r ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    have h2 : Real.exp (-4) ≤ 1 / 50 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have h3 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      have he := Real.exp_one_gt_d9
      have h5 := pow_lt_pow_left₀ he (by norm_num) (by norm_num : (4:ℕ) ≠ 0)
      rw [h3]; norm_num at h5 ⊢; linarith
    linarith
  have hr1' : r < 1 := by linarith
  have hbound : ∀ n : ℕ, thetaIncAtom x n ≤ Real.exp (x / 2) * (2 * Real.pi) * r ^ (n + 1) := by
    intro n
    unfold thetaIncAtom
    set w : ℝ := ((n + 1 : ℝ) * Real.exp x) ^ 2 with hw
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hw3 : 3 * ((n : ℝ) + 1) ≤ w := by
      rw [hw, mul_pow, show Real.exp x ^ 2 = Real.exp (2 * x) by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf]
      nlinarith
    have hwe : w * Real.exp (-Real.pi * w) ≤ Real.exp (-(Real.pi * w / 2)) := by
      have h1 : w ≤ Real.exp (Real.pi * w / 2) := by
        have := Real.add_one_le_exp (Real.pi * w / 2); nlinarith [Real.pi_gt_three]
      have h2 : Real.exp (-Real.pi * w) = Real.exp (-(Real.pi * w / 2)) * Real.exp (-(Real.pi * w / 2)) := by
        rw [← Real.exp_add]; ring_nf
      rw [h2]
      have h3 : w * Real.exp (-(Real.pi * w / 2)) ≤ 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]; exact h1
      nlinarith [Real.exp_pos (-(Real.pi * w / 2))]
    have hrn : Real.exp (-(Real.pi * w / 2)) ≤ r ^ (n + 1) := by
      rw [hr, ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; push_cast; nlinarith [Real.pi_pos]
    calc Real.exp (x / 2) * (2 * Real.pi * w) * Real.exp (-Real.pi * w)
        = Real.exp (x / 2) * (2 * Real.pi) * (w * Real.exp (-Real.pi * w)) := by ring
      _ ≤ Real.exp (x / 2) * (2 * Real.pi) * r ^ (n + 1) := by gcongr; linarith
  have hgeo : Summable (fun n : ℕ => Real.exp (x / 2) * (2 * Real.pi) * r ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hr0 hr1').mul_left (Real.exp (x / 2) * (2 * Real.pi) * r)).congr
      (fun n => by ring)
  have hsum : ∑' n : ℕ, Real.exp (x / 2) * (2 * Real.pi) * r ^ (n + 1) =
      Real.exp (x / 2) * (2 * Real.pi) * (r / (1 - r)) := by
    rw [tsum_mul_left]
    congr 1
    rw [show (fun n : ℕ => r ^ (n + 1)) = fun n => r * r ^ n by funext n; ring,
      tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1']
    ring
  have hle := (summable_thetaIncAtom x).tsum_le_tsum hbound hgeo
  rw [hsum] at hle
  refine le_trans hle ?_
  have hr2 : r / (1 - r) ≤ 2 * r := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hπ := Real.pi_lt_d2
  have hE := Real.exp_pos (x / 2)
  have hk : 2 * Real.pi * (2 * r) ≤ 1 / 3 := by nlinarith
  calc Real.exp (x / 2) * (2 * Real.pi) * (r / (1 - r)) ≤ Real.exp (x / 2) * (2 * Real.pi) * (2 * r) := by
        gcongr
    _ = Real.exp (x / 2) * (2 * Real.pi * (2 * r)) := by ring
    _ ≤ Real.exp (x / 2) * (1 / 3) := by gcongr
    _ = Real.exp (x / 2) / 3 := by ring

/-! ### Reflection law of the increment -/

theorem renewalInc_neg {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x)) (c : ℂ) (x : ℝ) :
    renewalInc F (-x) = modTail F c x - renewalInc F x + c * ((Real.exp (x / 2) / 2 : ℝ) : ℂ) := by
  have h1 : HasDerivAt (fun y => modTail F c (-y)) (-modTailDeriv F c (-x)) x := by
    have h := (hasDerivAt_modTail c hF (-x)).scomp x (hasDerivAt_neg x)
    rw [neg_one_smul] at h
    exact h
  have h2 : HasDerivAt (fun y => modTail F c y + c * modReflectionMode y)
      (modTailDeriv F c x + c * modReflectionModeDeriv x) x :=
    (hasDerivAt_modTail c hF x).add ((hasDerivAt_modReflectionMode x).const_mul c)
  have hfun : (fun y => modTail F c (-y)) = fun y => modTail F c y + c * modReflectionMode y :=
    funext (modTail_neg c hS)
  rw [hfun] at h1
  have hd := h1.unique h2
  rw [renewalInc_eq_tail F c, renewalInc_eq_tail F c, modTail_neg c hS]
  have hdx : modTailDeriv F c (-x) = -(modTailDeriv F c x + c * modReflectionModeDeriv x) := by
    rw [← hd]; ring
  rw [hdx]
  unfold modReflectionMode modReflectionModeDeriv
  push_cast
  have he : Real.exp (-x / 2) = Real.exp (-(x / 2)) := by ring_nf
  ring

/-! ### Reality and domination of the charge increment -/

theorem modTailDeriv_thetaGroupBasis_one_im (x : ℝ) :
    (modTailDeriv (thetaGroupBasis 1) 0 x).im = 0 :=
  im_eq_zero_of_hasDerivAt (fun y => hasDerivAt_modTail (c := 0) (differentiableOn_thetaGroupBasis 1) y)
    modTail_thetaGroupBasis_one_im x

theorem renewalInc_thetaGroupBasis_one_im (x : ℝ) : (renewalInc (thetaGroupBasis 1) x).im = 0 := by
  rw [renewalInc_eq_tail _ 0, Complex.sub_im, Complex.div_im, modTail_thetaGroupBasis_one_im,
    modTailDeriv_thetaGroupBasis_one_im]
  simp

theorem thetaCuspTailDerivative_zero_nonneg (x : ℝ) : 0 ≤ thetaCuspTailDerivative 0 x := by
  unfold thetaCuspTailDerivative
  refine tsum_nonneg (fun n => ?_)
  simp [thetaCuspPolynomialAtom, thetaCuspTailDerivativePolynomial]
  positivity

/-- The theta increment as a real function. -/
def thetaIncReal (x : ℝ) : ℝ := ∑' n, thetaIncAtom x n

theorem continuous_thetaIncReal : Continuous thetaIncReal := by
  have h : thetaIncReal = fun x => thetaCuspTailDerivative 0 x / 2 - thetaCuspTailDerivative 1 x := by
    funext x; unfold thetaIncReal; rw [thetaInc_eq_tsum]
  rw [h]
  have c0 : Continuous (thetaCuspTailDerivative 0) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_thetaCuspTailDerivative 0 x).continuousAt
  have c1 : Continuous (thetaCuspTailDerivative 1) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_thetaCuspTailDerivative 1 x).continuousAt
  exact (c0.div_const 2).sub c1

theorem exists_charge_increment_domination :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖renewalInc (thetaGroupBasis 1) x‖ ≤ C * thetaIncReal x := by
  obtain ⟨M, hM⟩ := exists_thetaGroupBasis_one_cusp
  have hM' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis 1 τ - 0‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; rw [sub_zero]; exact hM τ hτ
  have hM0 : 0 ≤ M := by
    have h := hM Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  have hF := differentiableOn_thetaGroupBasis 1
  have hS := thetaGroupBasis_axis 1
  set X₃ : ℝ := Real.log 3 / 2 with hX₃
  have hX₃0 : 0 < X₃ := by have := Real.log_pos (by norm_num : (1:ℝ) < 3); positivity
  have hexpX : ∀ x : ℝ, X₃ ≤ x → 3 ≤ Real.exp (2 * x) := by
    intro x hx
    have : Real.exp (2 * X₃) = 3 := by
      rw [hX₃, show 2 * (Real.log 3 / 2) = Real.log 3 by ring, Real.exp_log (by norm_num)]
    rw [← this]; exact Real.exp_le_exp.mpr (by linarith)
  -- bound on the positive far side
  have hfar : ∀ x : ℝ, X₃ ≤ x → ‖renewalInc (thetaGroupBasis 1) x‖ ≤
      Real.exp (x / 2) * Real.exp (2 * x) * (2 * M * Real.exp (π / 2)) * Real.exp (-π * Real.exp (2 * x)) := by
    intro x hx
    have hy := hexpX x hx
    have him : 2 ≤ (modAxisPoint x).im := by rw [modAxisPoint_im]; linarith
    have hd := norm_deriv_le_of_cuspDecay (c := 0) hF hM' him
    rw [modAxisPoint_im] at hd
    unfold renewalInc
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), norm_modAxisPoint]
    calc Real.exp (x / 2) * Real.exp (2 * x) * ‖deriv (thetaGroupBasis 1) (modAxisPoint x)‖
        ≤ Real.exp (x / 2) * Real.exp (2 * x) *
            (2 * M * Real.exp (π / 2) * Real.exp (-π * Real.exp (2 * x))) := by gcongr
      _ = _ := by ring
  have hlow : ∀ x : ℝ, 2 * π * (Real.exp (x / 2) * Real.exp (2 * x) * Real.exp (-π * Real.exp (2 * x))) ≤
      thetaIncReal x := by
    intro x
    have h := thetaInc_ge_first x
    unfold thetaIncAtom at h
    have e : (((0 : ℕ) : ℝ) + 1) * Real.exp x = Real.exp x := by simp
    rw [e] at h
    have e2 : Real.exp x ^ 2 = Real.exp (2 * x) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e2] at h
    unfold thetaIncReal
    calc 2 * π * (Real.exp (x / 2) * Real.exp (2 * x) * Real.exp (-π * Real.exp (2 * x)))
        = Real.exp (x / 2) * (2 * Real.pi * Real.exp (2 * x)) * Real.exp (-Real.pi * Real.exp (2 * x)) := by
          ring
      _ ≤ _ := h
  set C₁ : ℝ := M * Real.exp (π / 2) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hpos_side : ∀ x : ℝ, X₃ ≤ x → ‖renewalInc (thetaGroupBasis 1) x‖ ≤ C₁ * thetaIncReal x := by
    intro x hx
    have h1 := hfar x hx
    have h2 := hlow x
    have hπ := Real.pi_gt_three
    set Q := Real.exp (x / 2) * Real.exp (2 * x) * Real.exp (-π * Real.exp (2 * x))
    have hQ : 0 ≤ Q := by positivity
    calc ‖renewalInc (thetaGroupBasis 1) x‖ ≤ Q * (2 * M * Real.exp (π / 2)) := by
          calc _ ≤ _ := h1
            _ = Q * (2 * M * Real.exp (π / 2)) := by ring
      _ ≤ C₁ * (2 * π * Q) := by
          rw [hC₁]
          have hMQ : 0 ≤ M * Real.exp (π / 2) * Q := by positivity
          calc Q * (2 * M * Real.exp (π / 2)) = (M * Real.exp (π / 2) * Q) * 2 := by ring
            _ ≤ (M * Real.exp (π / 2) * Q) * (2 * π) := by gcongr; linarith
            _ = M * Real.exp (π / 2) * (2 * π * Q) := by ring
      _ ≤ C₁ * thetaIncReal x := by gcongr
  -- the negative far side
  set C₂ : ℝ := 6 * (M / 2 + 2 * M * Real.exp (π / 2)) with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hneg_side : ∀ x : ℝ, X₃ ≤ x → ‖renewalInc (thetaGroupBasis 1) (-x)‖ ≤ C₂ * thetaIncReal (-x) := by
    intro x hx
    have hy := hexpX x hx
    have hr1 := renewalInc_neg hF hS 0 x
    rw [zero_mul, add_zero] at hr1
    have hr0 := renewalInc_neg (differentiableOn_thetaGroupBasis 0) (thetaGroupBasis_axis 0) 1 x
    rw [renewalInc_thetaGroupBasis_zero, renewalInc_thetaGroupBasis_zero,
      modTail_thetaGroupBasis_zero] at hr0
    have hr0' : thetaIncReal (-x) = thetaCuspTailDerivative 0 x - thetaIncReal x +
        Real.exp (x / 2) / 2 := by
      have h := hr0; rw [one_mul] at h; simp only at h; unfold thetaIncReal; exact_mod_cast h
    have hsm := thetaInc_le_small hy
    have hT0 := thetaCuspTailDerivative_zero_nonneg x
    have hlow' : Real.exp (x / 2) / 6 ≤ thetaIncReal (-x) := by
      rw [hr0']; unfold thetaIncReal at hsm ⊢; linarith
    have hmt : ‖modTail (thetaGroupBasis 1) 0 x‖ ≤ Real.exp (x / 2) * (M / 2) := by
      unfold modTail
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        sub_zero, Complex.norm_ofNat]
      have him : 1 ≤ (modAxisPoint x).im := by rw [modAxisPoint_im]; linarith
      have hb := hM _ him
      rw [modAxisPoint_im] at hb
      have he : Real.exp (-π * Real.exp (2 * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have := Real.pi_pos; have := Real.exp_pos (2 * x); nlinarith)
      have : ‖thetaGroupBasis 1 (modAxisPoint x)‖ ≤ M := le_trans hb (by nlinarith)
      have hE := Real.exp_pos (x / 2)
      calc Real.exp (x / 2) * ‖thetaGroupBasis 1 (modAxisPoint x)‖ / 2 ≤ Real.exp (x / 2) * M / 2 := by
            gcongr
        _ = _ := by ring
    have hfx := hfar x hx
    have hye : Real.exp (2 * x) * Real.exp (-π * Real.exp (2 * x)) ≤ 1 := by
      rw [show -π * Real.exp (2 * x) = -(π * Real.exp (2 * x)) by ring, Real.exp_neg,
        ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      have := Real.add_one_le_exp (π * Real.exp (2 * x)); nlinarith [Real.pi_gt_three, Real.exp_pos (2 * x)]
    have hfx' : ‖renewalInc (thetaGroupBasis 1) x‖ ≤ Real.exp (x / 2) * (2 * M * Real.exp (π / 2)) := by
      refine le_trans hfx ?_
      have hE := Real.exp_pos (x / 2)
      have h0 : 0 ≤ 2 * M * Real.exp (π / 2) := by positivity
      calc Real.exp (x / 2) * Real.exp (2 * x) * (2 * M * Real.exp (π / 2)) * Real.exp (-π * Real.exp (2 * x))
          = Real.exp (x / 2) * (2 * M * Real.exp (π / 2)) *
              (Real.exp (2 * x) * Real.exp (-π * Real.exp (2 * x))) := by ring
        _ ≤ Real.exp (x / 2) * (2 * M * Real.exp (π / 2)) * 1 := by gcongr
        _ = _ := by ring
    rw [hr1]
    calc ‖modTail (thetaGroupBasis 1) 0 x - renewalInc (thetaGroupBasis 1) x‖
        ≤ ‖modTail (thetaGroupBasis 1) 0 x‖ + ‖renewalInc (thetaGroupBasis 1) x‖ := norm_sub_le _ _
      _ ≤ Real.exp (x / 2) * (M / 2) + Real.exp (x / 2) * (2 * M * Real.exp (π / 2)) := add_le_add hmt hfx'
      _ = C₂ * (Real.exp (x / 2) / 6) := by rw [hC₂]; ring
      _ ≤ C₂ * thetaIncReal (-x) := by gcongr
  -- compact middle
  obtain ⟨xm, hxm, hmin⟩ := (isCompact_Icc (a := -X₃) (b := X₃)).exists_isMinOn
    (nonempty_Icc.mpr (by linarith)) continuous_thetaIncReal.continuousOn
  have hc1 : Continuous fun x => ‖renewalInc (thetaGroupBasis 1) x‖ := by
    have h := fun x => renewalInc_eq_tail (thetaGroupBasis 1) 0 x
    have e : (fun x => renewalInc (thetaGroupBasis 1) x) =
        fun x => modTail (thetaGroupBasis 1) 0 x / 2 - modTailDeriv (thetaGroupBasis 1) 0 x := funext h
    have hc : Continuous fun x => renewalInc (thetaGroupBasis 1) x := by
      rw [e]; exact ((continuous_modTail_zero hF).div_const 2).sub (continuous_modTailDeriv_zero hF)
    exact hc.norm
  obtain ⟨xM, hxM, hmax⟩ := (isCompact_Icc (a := -X₃) (b := X₃)).exists_isMaxOn
    (nonempty_Icc.mpr (by linarith)) hc1.continuousOn
  set m₀ := thetaIncReal xm
  have hm₀ : 0 < m₀ := thetaInc_pos xm
  set C₃ : ℝ := ‖renewalInc (thetaGroupBasis 1) xM‖ / m₀
  have hC₃0 : 0 ≤ C₃ := by positivity
  refine ⟨C₁ + C₂ + C₃, by positivity, fun x => ?_⟩
  have hν := thetaInc_pos x
  rcases le_or_gt X₃ x with h1 | h1
  · calc _ ≤ C₁ * thetaIncReal x := hpos_side x h1
      _ ≤ _ := by gcongr; linarith
  rcases le_or_gt x (-X₃) with h2 | h2
  · have := hneg_side (-x) (by linarith)
    rw [neg_neg] at this
    calc _ ≤ C₂ * thetaIncReal x := this
      _ ≤ _ := by gcongr; linarith
  · have hin : x ∈ Icc (-X₃) X₃ := ⟨h2.le, h1.le⟩
    have hA : ‖renewalInc (thetaGroupBasis 1) x‖ ≤ ‖renewalInc (thetaGroupBasis 1) xM‖ := hmax hin
    have hB : m₀ ≤ thetaIncReal x := hmin hin
    calc ‖renewalInc (thetaGroupBasis 1) x‖ ≤ C₃ * m₀ := by
          rw [div_mul_cancel₀ _ hm₀.ne']; exact hA
      _ ≤ C₃ * thetaIncReal x := by gcongr
      _ ≤ _ := by gcongr; linarith

theorem renewalInc_thetaGroupDeformation (s : ℝ) (x : ℝ) :
    renewalInc (thetaGroupDeformation s 0) x =
      renewalInc (thetaGroupBasis 0) x + (s : ℂ) * renewalInc (thetaGroupBasis 1) x := by
  have e : thetaGroupDeformation s 0 =
      fun τ => (1 : ℂ) * thetaGroupBasis 0 τ + (s : ℂ) * thetaGroupBasis 1 τ := by
    funext τ; unfold thetaGroupDeformation thetaGroupBasis; push_cast; ring
  unfold renewalInc
  rw [e, deriv_linear_comb (differentiableOn_thetaGroupBasis 0) (differentiableOn_thetaGroupBasis 1)
    1 (s : ℂ) (modAxisPoint_mem x)]
  ring

/-- **The frozen statement, all clauses.**  For every `ε > 0` there is `0 < s < ε` such that the
exactly `Γ_θ`-modular source `θ₃(1 + s·h)` is real and strictly positive, has real strictly
positive renewal increment, and its transform `Ξ + sΞ₁` vanishes at some `0 < Im z < 1/2`. -/
theorem thetaGroup_modular_criticality_full {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ s < ε ∧
      (∀ x : ℝ, (modSource (thetaGroupDeformation s 0) x).im = 0 ∧
        0 < (modSource (thetaGroupDeformation s 0) x).re) ∧
      (∀ x : ℝ, (renewalInc (thetaGroupDeformation s 0) x).im = 0 ∧
        0 < (renewalInc (thetaGroupDeformation s 0) x).re) ∧
      ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧ modXi (thetaGroupDeformation s 0) z = 0 := by
  obtain ⟨C, hC0, hdom⟩ := exists_charge_increment_domination
  set ε' : ℝ := min ε (1 / (2 * (C + 1))) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  obtain ⟨s, hs0, hsε, hsrc, hz⟩ := thetaGroup_modular_criticality hε'pos
  refine ⟨s, hs0, lt_of_lt_of_le hsε (min_le_left _ _), hsrc, fun x => ?_, hz⟩
  rw [renewalInc_thetaGroupDeformation, renewalInc_thetaGroupBasis_zero]
  have him := renewalInc_thetaGroupBasis_one_im x
  constructor
  · simp [him]
  · have hre : (((∑' n, thetaIncAtom x n : ℝ) : ℂ) + (s : ℂ) * renewalInc (thetaGroupBasis 1) x).re =
        thetaIncReal x + s * (renewalInc (thetaGroupBasis 1) x).re := by
      unfold thetaIncReal; simp
    rw [hre]
    have hν := thetaInc_pos x
    have h1 : |(renewalInc (thetaGroupBasis 1) x).re| ≤ C * thetaIncReal x :=
      le_trans (Complex.abs_re_le_norm _) (hdom x)
    have hsC : s * C ≤ 1 / 2 := by
      have : s ≤ 1 / (2 * (C + 1)) := le_trans hsε.le (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith
    have h2 := neg_abs_le (renewalInc (thetaGroupBasis 1) x).re
    unfold thetaIncReal at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0.le]

end RHTower
