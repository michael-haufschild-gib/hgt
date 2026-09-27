import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw

/-!
# Resolvent division of super-exponentially decaying kernels

For a continuous `g` integrable against every weight `e^{c|u|}` and a point `γ` with
`|Im γ| ≤ 1/2` and `ĝ(γ) = 0` (`ĝ = paperFT g`), the resolvent division

`D_γ g (x) = -i e^{-iγx} ∫_{u ≤ x} g(u) e^{iγu} du`

has transform `ĝ(z)/(z - γ)` (`paperFT_resolventDiv_mul`) and is again super-exponentially
decaying. The vanishing `ĝ(γ) = 0` lets the integral be taken over `u > x` for `x ≥ 0`, which gives
`‖D_γ g(x)‖ ≤ e^{-μ|x|} ∫_{|u| ≥ |x|} ‖g‖ e^{(μ+1/2)|u|}` (`norm_resolventDiv_le`) and the tail
iteration `∫_{|x|≥X} ‖D_γ g‖ e^{c|x|} ≤ 2 ∫_{|u|≥X} ‖g‖ e^{(c+3/2)|u|}`.

Iterating `m` times at a zero of `ĝ` of order `m` divides the transform by `(z - γ)^m`; the
leading local factor is carried unchanged (`iterResolvent_spec`), and the behaviour at a second
point is tracked by `iterResolvent_eventually_ne`.

This is how a radical kernel, whose transform vanishes at every zero, is turned into a kernel whose
transform vanishes at all zeros but a prescribed one, without losing its decay.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## Super-exponentially decaying functions -/

/-- Continuous, and integrable against every exponential weight `e^{c|u|}`. -/
def SuperExpDecay (g : ℝ → ℂ) : Prop :=
  Continuous g ∧ ∀ c : ℝ, Integrable (fun u : ℝ => ‖g u‖ * Real.exp (c * |u|))

/-- The weighted tail `∫_{|u| ≥ X} ‖g u‖ e^{c|u|} du`. -/
def expTail (g : ℝ → ℂ) (c X : ℝ) : ℝ :=
  ∫ u : ℝ, {u : ℝ | X ≤ |u|}.indicator (fun u => ‖g u‖ * Real.exp (c * |u|)) u

theorem measurableSet_absGe (X : ℝ) : MeasurableSet {u : ℝ | X ≤ |u|} :=
  measurableSet_le measurable_const measurable_norm

theorem expTail_nonneg (g : ℝ → ℂ) (c X : ℝ) : 0 ≤ expTail g c X :=
  integral_nonneg fun u => by
    simp only [indicator]; split_ifs <;> positivity

theorem SuperExpDecay.integrable_tail {g : ℝ → ℂ} (hg : SuperExpDecay g) (c X : ℝ) :
    Integrable ({u : ℝ | X ≤ |u|}.indicator (fun u => ‖g u‖ * Real.exp (c * |u|))) :=
  (hg.2 c).indicator (measurableSet_absGe X)

/-- The tail shrinks as the threshold grows. -/
theorem expTail_anti {g : ℝ → ℂ} (hg : SuperExpDecay g) (c : ℝ) {X Y : ℝ} (hXY : X ≤ Y) :
    expTail g c Y ≤ expTail g c X := by
  unfold expTail
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => ?_) (hg.integrable_tail c X)
    (Eventually.of_forall fun u => ?_)
  · simp only [indicator]; split_ifs <;> positivity
  · simp only [indicator, mem_setOf_eq]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (hXY.trans h1) h2
    · positivity
    · exact le_rfl

/-- The tail is monotone in the weight. -/
theorem expTail_mono_weight {g : ℝ → ℂ} (hg : SuperExpDecay g) {c d : ℝ} (hcd : c ≤ d) (X : ℝ) :
    expTail g c X ≤ expTail g d X := by
  unfold expTail
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => ?_) (hg.integrable_tail d X)
    (Eventually.of_forall fun u => ?_)
  · simp only [indicator]; split_ifs <;> positivity
  · simp only [indicator]
    split_ifs
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hcd (abs_nonneg u))) (norm_nonneg _)
    · exact le_rfl

theorem norm_cexp_I_mul_eq (z : ℂ) (u : ℝ) :
    ‖Complex.exp (I * z * u)‖ = Real.exp (-(z.im * u)) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]

theorem SuperExpDecay.integrable_mul_cexp {g : ℝ → ℂ} (hg : SuperExpDecay g) (z : ℂ) :
    Integrable (fun u : ℝ => g u * Complex.exp (I * z * u)) := by
  refine Integrable.mono' (hg.2 |z.im|) ?_ (Eventually.of_forall fun u => ?_)
  · exact (hg.1.mul (by fun_prop)).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp le_rfl u) (norm_nonneg _)

/-- The transform of a super-exponentially decaying function is continuous in `z`. -/
theorem SuperExpDecay.continuous_paperFT {g : ℝ → ℂ} (hg : SuperExpDecay g) :
    Continuous (paperFT g) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  unfold paperFT
  refine continuousAt_of_dominated (bound := fun u => ‖g u‖ * Real.exp ((|z₀.im| + 1) * |u|))
    (Eventually.of_forall fun z => (hg.1.mul (by fun_prop)).aestronglyMeasurable) ?_
    (hg.2 _) (Eventually.of_forall fun u => by fun_prop)
  have hopen : IsOpen {z : ℂ | |z.im| < |z₀.im| + 1} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  filter_upwards [hopen.mem_nhds (show |z₀.im| < |z₀.im| + 1 by linarith)] with z hz
  refine Eventually.of_forall fun u => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp (le_of_lt hz) u) (norm_nonneg _)

theorem SuperExpDecay.add {g h : ℝ → ℂ} (hg : SuperExpDecay g) (hh : SuperExpDecay h) :
    SuperExpDecay (g + h) := by
  refine ⟨hg.1.add hh.1, fun c => ?_⟩
  refine Integrable.mono' ((hg.2 c).add (hh.2 c)) ?_ (Eventually.of_forall fun u => ?_)
  · exact ((hg.1.add hh.1).norm.mul (by fun_prop)).aestronglyMeasurable
  · simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_pos _).le

theorem SuperExpDecay.const_mul {g : ℝ → ℂ} (hg : SuperExpDecay g) (a : ℂ) :
    SuperExpDecay (fun u => a * g u) := by
  refine ⟨continuous_const.mul hg.1, fun c => ?_⟩
  refine ((hg.2 c).const_mul ‖a‖).congr (Eventually.of_forall fun u => ?_)
  simp only [norm_mul]; ring

/-- Multiplication by a bounded continuous function. -/
theorem SuperExpDecay.mul_bounded {g χ : ℝ → ℂ} (hg : SuperExpDecay g) (hχ : Continuous χ)
    {B : ℝ} (hB : ∀ u, ‖χ u‖ ≤ B) : SuperExpDecay (fun u => χ u * g u) := by
  refine ⟨hχ.mul hg.1, fun c => ?_⟩
  refine Integrable.mono' ((hg.2 c).const_mul B) ?_ (Eventually.of_forall fun u => ?_)
  · exact ((hχ.mul hg.1).norm.mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hB u) (by positivity)

/-- Translation `x ↦ g (x - s)`. -/
theorem SuperExpDecay.comp_sub {g : ℝ → ℂ} (hg : SuperExpDecay g) (s : ℝ) :
    SuperExpDecay (fun u => g (u - s)) := by
  refine ⟨hg.1.comp (by fun_prop), fun c => ?_⟩
  have h1 : Integrable (fun u : ℝ => ‖g (u - s)‖ * Real.exp (|c| * |u - s|)) :=
    (hg.2 |c|).comp_sub_right s
  refine Integrable.mono' (h1.const_mul (Real.exp (|c| * |s|))) ?_
    (Eventually.of_forall fun u => ?_)
  · exact ((hg.1.comp (by fun_prop)).norm.mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hu : |u| ≤ |u - s| + |s| := by
      calc |u| = |(u - s) + s| := by ring_nf
        _ ≤ |u - s| + |s| := abs_add_le _ _
    have hc : c * |u| ≤ |c| * |s| + |c| * |u - s| := by
      calc c * |u| ≤ |c| * |u| := mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg u)
        _ ≤ |c| * (|u - s| + |s|) := mul_le_mul_of_nonneg_left hu (abs_nonneg c)
        _ = |c| * |s| + |c| * |u - s| := by ring
    calc ‖g (u - s)‖ * Real.exp (c * |u|)
        ≤ ‖g (u - s)‖ * (Real.exp (|c| * |s|) * Real.exp (|c| * |u - s|)) := by
          rw [← Real.exp_add]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hc) (norm_nonneg _)
      _ = Real.exp (|c| * |s|) * (‖g (u - s)‖ * Real.exp (|c| * |u - s|)) := by ring

/-! ## The resolvent division -/

/-- **Resolvent division.** `D_γ g (x) = -i e^{-iγx} ∫_{u ≤ x} g(u) e^{iγu} du`. Its transform is
`ĝ(z)/(z - γ)`; when `ĝ(γ) = 0` it inherits the decay of `g`. -/
def resolventDiv (γ : ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  -I * Complex.exp (-(I * γ * x)) * ∫ u in Iic x, g u * Complex.exp (I * γ * u)

theorem resolventDiv_eq_Ioi {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ} (hγ0 : paperFT g γ = 0)
    (x : ℝ) :
    resolventDiv γ g x =
      I * Complex.exp (-(I * γ * x)) * ∫ u in Ioi x, g u * Complex.exp (I * γ * u) := by
  have hint := hg.integrable_mul_cexp γ
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := x) hint.integrableOn hint.integrableOn
  have h0 : ∫ u : ℝ, g u * Complex.exp (I * γ * u) = 0 := hγ0
  rw [h0] at hsplit
  unfold resolventDiv
  rw [show (∫ u in Iic x, g u * Complex.exp (I * γ * u)) =
    -∫ u in Ioi x, g u * Complex.exp (I * γ * u) by linear_combination hsplit]
  ring

/-- The kernel of the resolvent is dominated by `e^{(|u| - |x|)/2}` on the relevant side. -/
theorem norm_cexp_resolvent_le {γ : ℂ} (hγ : |γ.im| ≤ 1 / 2) {x u : ℝ}
    (h : (0 ≤ x ∧ x < u) ∨ (x < 0 ∧ u ≤ x)) :
    ‖Complex.exp (-(I * γ * x)) * Complex.exp (I * γ * u)‖ ≤ Real.exp ((|u| - |x|) / 2) := by
  rw [← Complex.exp_add, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (-(I * γ * (x : ℂ)) + I * γ * (u : ℂ)).re = γ.im * (x - u) := by
    simp [Complex.mul_re]; ring
  rw [hre]
  rcases h with ⟨hx, hxu⟩ | ⟨hx, hux⟩
  · rw [abs_of_nonneg hx, abs_of_nonneg (by linarith)]
    have : γ.im * (x - u) ≤ |γ.im| * (u - x) := by
      calc γ.im * (x - u) ≤ |γ.im * (x - u)| := le_abs_self _
        _ = |γ.im| * (u - x) := by
            rw [abs_mul, abs_of_nonpos (show x - u ≤ 0 by linarith)]; ring
    nlinarith [abs_nonneg γ.im]
  · rw [abs_of_neg hx, abs_of_neg (by linarith)]
    have : γ.im * (x - u) ≤ |γ.im| * (x - u) := by
      calc γ.im * (x - u) ≤ |γ.im * (x - u)| := le_abs_self _
        _ = |γ.im| * (x - u) := by rw [abs_mul, abs_of_nonneg (show 0 ≤ x - u by linarith)]
    nlinarith [abs_nonneg γ.im]

/-- On a set `S` of points with `|x| ≤ |u|` where the resolvent kernel is dominated, the partial
integral is bounded by the weighted tail. -/
theorem norm_resolvent_piece_le {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ} {μ x : ℝ}
    (hμ : 0 ≤ μ) {S : Set ℝ} (hS : MeasurableSet S) (hSx : ∀ u ∈ S, |x| ≤ |u|)
    (hker : ∀ u ∈ S, ‖Complex.exp (-(I * γ * x)) * Complex.exp (I * γ * u)‖ ≤
      Real.exp ((|u| - |x|) / 2)) :
    ‖Complex.exp (-(I * γ * x)) * ∫ u in S, g u * Complex.exp (I * γ * u)‖ ≤
      Real.exp (-(μ * |x|)) * expTail g (μ + 1 / 2) |x| := by
  rw [← integral_const_mul]
  have hint : Integrable (fun u => Complex.exp (-(I * γ * x)) * (g u * Complex.exp (I * γ * u))) :=
    (hg.integrable_mul_cexp γ).const_mul _
  refine (norm_integral_le_integral_norm _).trans ?_
  have hmaj : ∀ u ∈ S, ‖Complex.exp (-(I * γ * x)) * (g u * Complex.exp (I * γ * u))‖ ≤
      Real.exp (-(μ * |x|)) * ({u : ℝ | |x| ≤ |u|}.indicator
        (fun u => ‖g u‖ * Real.exp ((μ + 1 / 2) * |u|)) u) := by
    intro u hu
    have hxu := hSx u hu
    rw [indicator_of_mem (show u ∈ {u : ℝ | |x| ≤ |u|} from hxu)]
    rw [show Complex.exp (-(I * γ * x)) * (g u * Complex.exp (I * γ * u)) =
      g u * (Complex.exp (-(I * γ * x)) * Complex.exp (I * γ * u)) by ring, norm_mul]
    calc ‖g u‖ * ‖Complex.exp (-(I * γ * x)) * Complex.exp (I * γ * u)‖
        ≤ ‖g u‖ * Real.exp ((|u| - |x|) / 2) :=
          mul_le_mul_of_nonneg_left (hker u hu) (norm_nonneg _)
      _ ≤ ‖g u‖ * (Real.exp (-(μ * |x|)) * Real.exp ((μ + 1 / 2) * |u|)) := by
          rw [← Real.exp_add]
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
          nlinarith [abs_nonneg x]
      _ = Real.exp (-(μ * |x|)) * (‖g u‖ * Real.exp ((μ + 1 / 2) * |u|)) := by ring
  calc ∫ u in S, ‖Complex.exp (-(I * γ * x)) * (g u * Complex.exp (I * γ * u))‖
      ≤ ∫ u in S, Real.exp (-(μ * |x|)) * ({u : ℝ | |x| ≤ |u|}.indicator
          (fun u => ‖g u‖ * Real.exp ((μ + 1 / 2) * |u|)) u) :=
        setIntegral_mono_on hint.norm.integrableOn
          (((hg.integrable_tail (μ + 1 / 2) |x|).const_mul _).integrableOn) hS hmaj
    _ ≤ ∫ u, Real.exp (-(μ * |x|)) * ({u : ℝ | |x| ≤ |u|}.indicator
          (fun u => ‖g u‖ * Real.exp ((μ + 1 / 2) * |u|)) u) :=
        setIntegral_le_integral ((hg.integrable_tail (μ + 1 / 2) |x|).const_mul _)
          (Eventually.of_forall fun u => by
            simp only [indicator]; split_ifs <;> positivity)
    _ = Real.exp (-(μ * |x|)) * expTail g (μ + 1 / 2) |x| := by
        rw [integral_const_mul]; rfl

/-- **Pointwise decay of the resolvent division.** If `ĝ(γ) = 0` and `|Im γ| ≤ 1/2`, then for
every `μ ≥ 0`, `‖D_γ g(x)‖ ≤ e^{-μ|x|} ∫_{|u| ≥ |x|} ‖g u‖ e^{(μ+1/2)|u|}`. -/
theorem norm_resolventDiv_le {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ}
    (hγ0 : paperFT g γ = 0) (hγ : |γ.im| ≤ 1 / 2) {μ : ℝ} (hμ : 0 ≤ μ) (x : ℝ) :
    ‖resolventDiv γ g x‖ ≤ Real.exp (-(μ * |x|)) * expTail g (μ + 1 / 2) |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [resolventDiv_eq_Ioi hg hγ0, mul_assoc, norm_mul, Complex.norm_I, one_mul]
    exact norm_resolvent_piece_le hg hμ measurableSet_Ioi
      (fun u hu => by
        rw [abs_of_nonneg hx, abs_of_nonneg (by linarith [mem_Ioi.mp hu])]
        exact (mem_Ioi.mp hu).le)
      (fun u hu => norm_cexp_resolvent_le hγ (Or.inl ⟨hx, mem_Ioi.mp hu⟩))
  · unfold resolventDiv
    rw [mul_assoc, norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact norm_resolvent_piece_le hg hμ measurableSet_Iic
      (fun u hu => by
        rw [abs_of_neg hx, abs_of_neg (by linarith [mem_Iic.mp hu])]
        linarith [mem_Iic.mp hu])
      (fun u hu => norm_cexp_resolvent_le hγ (Or.inr ⟨hx, mem_Iic.mp hu⟩))

/-- The derivative of the resolvent division: `(D_γ g)' = -iγ D_γ g - i g`. -/
theorem hasDerivAt_resolventDiv {g : ℝ → ℂ} (hg : SuperExpDecay g) (γ : ℂ) (x : ℝ) :
    HasDerivAt (resolventDiv γ g) (-I * γ * resolventDiv γ g x - I * g x) x := by
  set F : ℝ → ℂ := fun u => g u * Complex.exp (I * γ * u) with hF
  have hFc : Continuous F := hg.1.mul (by fun_prop)
  have hFi : Integrable F := hg.integrable_mul_cexp γ
  have hsplit : ∀ y : ℝ, ∫ u in Iic y, F u = (∫ u in Iic 0, F u) + ∫ u in (0 : ℝ)..y, F u := by
    intro y
    have := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := y) hFi.integrableOn hFi.integrableOn
    linear_combination this
  have hI : HasDerivAt (fun y => ∫ u in Iic y, F u) (F x) x := by
    have h := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := x)
      (hFc.intervalIntegrable 0 x) (hFc.stronglyMeasurableAtFilter _ _) hFc.continuousAt
    have hfun : (fun y => ∫ u in Iic y, F u) =
        fun y => (∫ u in Iic 0, F u) + ∫ u in (0 : ℝ)..y, F u := funext hsplit
    rw [hfun]
    exact h.const_add _
  have h1 : HasDerivAt (fun y : ℝ => (-(I * γ)) * (y : ℂ)) (-(I * γ)) x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (-(I * γ))
  have hE : HasDerivAt (fun y : ℝ => -I * Complex.exp ((-(I * γ)) * y))
      (-I * (Complex.exp ((-(I * γ)) * x) * (-(I * γ)))) x := (h1.cexp).const_mul (-I)
  have hprod := hE.mul hI
  have hfun2 : ((fun y : ℝ => -I * Complex.exp ((-(I * γ)) * y)) *
      fun y : ℝ => ∫ u in Iic y, F u) = resolventDiv γ g := by
    funext y
    simp only [Pi.mul_apply, resolventDiv, hF]
    rw [show (-(I * γ)) * (y : ℂ) = -(I * γ * y) by ring]
  rw [hfun2] at hprod
  refine hprod.congr_deriv ?_
  unfold resolventDiv
  simp only [hF]
  rw [show (-(I * γ)) * (x : ℂ) = -(I * γ * x) by ring]
  have hEE : Complex.exp (-(I * γ * x)) * Complex.exp (I * γ * x) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (-I * g x) * hEE

theorem continuous_resolventDiv {g : ℝ → ℂ} (hg : SuperExpDecay g) (γ : ℂ) :
    Continuous (resolventDiv γ g) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_resolventDiv hg γ x).continuousAt

theorem integrable_exp_neg_abs : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 2)
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hq := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  rw [show 2 * (1 + x ^ 2)⁻¹ * Real.exp |x| = 2 * Real.exp |x| / (1 + x ^ 2) by field_simp]
  rw [le_div_iff₀ hpos]
  nlinarith [abs_nonneg x]

theorem integral_exp_neg_abs : ∫ x : ℝ, Real.exp (-|x|) = 2 := by
  have h := integral_comp_abs (f := fun x => Real.exp (-x))
  rw [h, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, mul_one]

/-- The resolvent division preserves super-exponential decay. -/
theorem superExpDecay_resolventDiv {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ}
    (hγ0 : paperFT g γ = 0) (hγ : |γ.im| ≤ 1 / 2) : SuperExpDecay (resolventDiv γ g) := by
  refine ⟨continuous_resolventDiv hg γ, fun c => ?_⟩
  set μ : ℝ := |c| + 1
  have hμ : 0 ≤ μ := by positivity
  set T : ℝ := expTail g (μ + 1 / 2) 0
  refine Integrable.mono' (integrable_exp_neg_abs.const_mul T) ?_
    (Eventually.of_forall fun x => ?_)
  · exact ((continuous_resolventDiv hg γ).norm.mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := norm_resolventDiv_le hg hγ0 hγ hμ x
    have h2 : expTail g (μ + 1 / 2) |x| ≤ T := expTail_anti hg _ (abs_nonneg x)
    have hT : 0 ≤ expTail g (μ + 1 / 2) |x| := expTail_nonneg _ _ _
    calc ‖resolventDiv γ g x‖ * Real.exp (c * |x|)
        ≤ (Real.exp (-(μ * |x|)) * T) * Real.exp (c * |x|) :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le))
            (Real.exp_pos _).le
      _ = T * Real.exp (-(μ * |x|) + c * |x|) := by rw [Real.exp_add]; ring
      _ ≤ T * Real.exp (-|x|) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (expTail_nonneg _ _ _)
          have : c * |x| ≤ |c| * |x| := mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg x)
          simp only [μ]; nlinarith [abs_nonneg x]

/-- **Tail iteration.** `∫_{|x|≥X} ‖D_γ g‖ e^{c|x|} ≤ 2 ∫_{|u|≥X} ‖g‖ e^{(c+3/2)|u|}`. -/
theorem expTail_resolventDiv_le {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ}
    (hγ0 : paperFT g γ = 0) (hγ : |γ.im| ≤ 1 / 2) {c X : ℝ} (hc : 0 ≤ c) :
    expTail (resolventDiv γ g) c X ≤ 2 * expTail g (c + 3 / 2) X := by
  set T : ℝ := expTail g (c + 3 / 2) X
  have hD := superExpDecay_resolventDiv hg hγ0 hγ
  unfold expTail
  calc ∫ x : ℝ, {u : ℝ | X ≤ |u|}.indicator
        (fun u => ‖resolventDiv γ g u‖ * Real.exp (c * |u|)) x
      ≤ ∫ x : ℝ, T * Real.exp (-|x|) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u => ?_)
          (integrable_exp_neg_abs.const_mul T) (Eventually.of_forall fun x => ?_)
        · simp only [indicator]; split_ifs <;> positivity
        · simp only [indicator, mem_setOf_eq]
          split_ifs with hx
          · have h1 := norm_resolventDiv_le hg hγ0 hγ (show (0 : ℝ) ≤ c + 1 by linarith) x
            have h2 : expTail g (c + 1 + 1 / 2) |x| ≤ T := by
              rw [show c + 1 + 1 / 2 = c + 3 / 2 by ring]; exact expTail_anti hg _ hx
            calc ‖resolventDiv γ g x‖ * Real.exp (c * |x|)
                ≤ (Real.exp (-((c + 1) * |x|)) * T) * Real.exp (c * |x|) :=
                  mul_le_mul_of_nonneg_right
                    (h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le))
                    (Real.exp_pos _).le
              _ = T * Real.exp (-|x|) := by
                  rw [mul_comm (Real.exp _) T, mul_assoc, ← Real.exp_add]; congr 2; ring
          · exact mul_nonneg (expTail_nonneg _ _ _) (Real.exp_pos _).le
    _ = 2 * T := by rw [integral_const_mul, integral_exp_neg_abs]; ring

/-- The sup bound `‖D_γ g(x)‖ ≤ ∫ ‖g‖ e^{|u|/2}`. -/
theorem norm_resolventDiv_le_expTail {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ}
    (hγ0 : paperFT g γ = 0) (hγ : |γ.im| ≤ 1 / 2) (x : ℝ) :
    ‖resolventDiv γ g x‖ ≤ expTail g (1 / 2) 0 := by
  have h1 := norm_resolventDiv_le hg hγ0 hγ le_rfl x
  rw [zero_mul, neg_zero, Real.exp_zero, one_mul, zero_add] at h1
  exact h1.trans (expTail_anti hg _ (abs_nonneg x))

/-! ## The transform of the resolvent division -/

theorem hasDerivAt_cexp_I_mul (z : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (I * z * y)) (I * z * Complex.exp (I * z * x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => I * z * (y : ℂ)) (I * z) x := by
    have h := ((hasDerivAt_id x).ofReal_comp).const_mul (I * z)
    simp only [id, Complex.ofReal_one, mul_one] at h
    exact h
  exact (h1.cexp).congr_deriv (by ring)

/-- Integration by parts on the line: `(G')^(z) = -iz Ĝ(z)`. -/
theorem paperFT_deriv_of_superExpDecay {G G' : ℝ → ℂ} (hG : SuperExpDecay G)
    (hG' : SuperExpDecay G') (hd : ∀ x, HasDerivAt G (G' x) x) (z : ℂ) :
    paperFT G' z = -(I * z) * paperFT G z := by
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := G) (v := fun y : ℝ => Complex.exp (I * z * y)) (u' := G')
    (v' := fun y : ℝ => I * z * Complex.exp (I * z * y))
    (fun x _ => hd x) (fun x _ => hasDerivAt_cexp_I_mul z x)
    (by
      have h := (hG.integrable_mul_cexp z).const_mul (I * z)
      refine h.congr (Eventually.of_forall fun y => ?_)
      simp only [Pi.mul_apply]; ring)
    (hG'.integrable_mul_cexp z) (hG.integrable_mul_cexp z)
  unfold paperFT
  have hl : ∫ x : ℝ, G x * (I * z * Complex.exp (I * z * x)) =
      I * z * ∫ x : ℝ, G x * Complex.exp (I * z * x) := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [hl] at hibp
  linear_combination hibp

/-- **Transform of the resolvent division.** `(z - γ) · (D_γ g)^(z) = ĝ(z)` for every `z`. -/
theorem paperFT_resolventDiv_mul {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ}
    (hγ0 : paperFT g γ = 0) (hγ : |γ.im| ≤ 1 / 2) (z : ℂ) :
    (z - γ) * paperFT (resolventDiv γ g) z = paperFT g z := by
  set G := resolventDiv γ g
  have hG := superExpDecay_resolventDiv hg hγ0 hγ
  set G' : ℝ → ℂ := fun x => -I * γ * G x - I * g x with hG'def
  have hG'd : SuperExpDecay G' := by
    have h1 := hG.const_mul (-I * γ)
    have h2 := hg.const_mul (-I)
    have h3 := h1.add h2
    refine ⟨?_, ?_⟩
    · have : G' = (fun u => -I * γ * G u) + (fun u => -I * g u) := by
        funext u; simp only [hG'def, Pi.add_apply]; ring
      rw [this]; exact h3.1
    · intro c
      have : (fun u => ‖G' u‖ * Real.exp (c * |u|)) =
          fun u => ‖((fun u => -I * γ * G u) + (fun u => -I * g u)) u‖ * Real.exp (c * |u|) := by
        funext u; simp only [hG'def, Pi.add_apply]; ring_nf
      rw [this]; exact h3.2 c
  have hd : ∀ x, HasDerivAt G (G' x) x := fun x => hasDerivAt_resolventDiv hg γ x
  have hibp := paperFT_deriv_of_superExpDecay hG hG'd hd z
  have hlin : paperFT G' z = -I * γ * paperFT G z - I * paperFT g z := by
    unfold paperFT
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub]
    · congr 1; funext x; simp only [hG'def]; ring
    · exact (hG.integrable_mul_cexp z).const_mul _
    · exact (hg.integrable_mul_cexp z).const_mul _
  rw [hlin] at hibp
  have hI2 : I * I = -1 := Complex.I_mul_I
  linear_combination (-I) * hibp + ((z - γ) * paperFT G z - paperFT g z) * hI2

theorem paperFT_resolventDiv_eq_div {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ}
    (hγ0 : paperFT g γ = 0) (hγ : |γ.im| ≤ 1 / 2) {z : ℂ} (hz : z ≠ γ) :
    paperFT (resolventDiv γ g) z = paperFT g z / (z - γ) := by
  rw [← paperFT_resolventDiv_mul hg hγ0 hγ z]
  field_simp [sub_ne_zero.mpr hz]

/-- Near the divided point, the resolvent lowers the order of vanishing by one. -/
theorem paperFT_resolventDiv_eventually {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ}
    (hγ0 : paperFT g γ = 0) (hγ : |γ.im| ≤ 1 / 2) {k : ℕ} {v : ℂ → ℂ} (hv : ContinuousAt v γ)
    (hloc : paperFT g =ᶠ[𝓝 γ] fun z => (z - γ) ^ (k + 1) * v z) :
    paperFT (resolventDiv γ g) =ᶠ[𝓝 γ] fun z => (z - γ) ^ k * v z := by
  have hG := superExpDecay_resolventDiv hg hγ0 hγ
  have hpunct : ∀ᶠ z in 𝓝[≠] γ, paperFT (resolventDiv γ g) z = (z - γ) ^ k * v z := by
    filter_upwards [nhdsWithin_le_nhds hloc, self_mem_nhdsWithin] with z hz hne
    rw [paperFT_resolventDiv_eq_div hg hγ0 hγ hne, hz]
    have hne' : z - γ ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  have hcont1 : ContinuousAt (paperFT (resolventDiv γ g)) γ := hG.continuous_paperFT.continuousAt
  have hcont2 : ContinuousAt (fun z => (z - γ) ^ k * v z) γ :=
    ((continuousAt_id.sub continuousAt_const).pow k).mul hv
  have hat : paperFT (resolventDiv γ g) γ = (γ - γ) ^ k * v γ := by
    have t1 : Tendsto (paperFT (resolventDiv γ g)) (𝓝[≠] γ) (𝓝 (paperFT (resolventDiv γ g) γ)) :=
      hcont1.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto (paperFT (resolventDiv γ g)) (𝓝[≠] γ) (𝓝 ((γ - γ) ^ k * v γ)) :=
      (hcont2.tendsto.mono_left nhdsWithin_le_nhds).congr' (hpunct.mono fun z hz => hz.symm)
    exact tendsto_nhds_unique t1 t2
  have hsup : ∀ᶠ z in 𝓝[≠] γ ⊔ pure γ,
      paperFT (resolventDiv γ g) z = (z - γ) ^ k * v z :=
    Filter.eventually_sup.mpr ⟨hpunct, Filter.eventually_pure.mpr hat⟩
  rwa [nhdsNE_sup_pure] at hsup

/-- Away from the divided point, the resolvent divides the local factor by `z - γ`. -/
theorem paperFT_resolventDiv_eventually_ne {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ}
    (hγ0 : paperFT g γ = 0) (hγ : |γ.im| ≤ 1 / 2) {γ' : ℂ} (hne : γ' ≠ γ) {k : ℕ}
    {v : ℂ → ℂ} (hloc : paperFT g =ᶠ[𝓝 γ'] fun z => (z - γ') ^ k * v z) :
    paperFT (resolventDiv γ g) =ᶠ[𝓝 γ'] fun z => (z - γ') ^ k * (v z / (z - γ)) := by
  filter_upwards [hloc, eventually_ne_nhds hne] with z hz hzne
  rw [paperFT_resolventDiv_eq_div hg hγ0 hγ hzne, hz]; ring

/-! ## Iterated resolvent division -/

/-- `D_γ^k g`. -/
def iterResolvent (γ : ℂ) (k : ℕ) (g : ℝ → ℂ) : ℝ → ℂ := (resolventDiv γ)^[k] g

theorem iterResolvent_zero (γ : ℂ) (g : ℝ → ℂ) : iterResolvent γ 0 g = g := rfl

theorem iterResolvent_succ (γ : ℂ) (k : ℕ) (g : ℝ → ℂ) :
    iterResolvent γ (k + 1) g = resolventDiv γ (iterResolvent γ k g) :=
  Function.iterate_succ_apply' _ _ _

/-- **Iterated division at a zero of order `m`.** For `k ≤ m`, `D_γ^k g` decays
super-exponentially, its transform vanishes to order `m - k` at `γ` with the same leading factor,
and `(z - γ)^k (D_γ^k g)^ = ĝ`. -/
theorem iterResolvent_spec {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ} (hγ : |γ.im| ≤ 1 / 2)
    {m : ℕ} {v : ℂ → ℂ} (hv : ContinuousAt v γ)
    (hloc : paperFT g =ᶠ[𝓝 γ] fun z => (z - γ) ^ m * v z) :
    ∀ k, k ≤ m → SuperExpDecay (iterResolvent γ k g) ∧
      (paperFT (iterResolvent γ k g) =ᶠ[𝓝 γ] fun z => (z - γ) ^ (m - k) * v z) ∧
      ∀ z, (z - γ) ^ k * paperFT (iterResolvent γ k g) z = paperFT g z := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨hg, ?_, fun z => by simp [iterResolvent_zero]⟩
    simpa [iterResolvent_zero] using hloc
  | succ k ih =>
    intro hk
    obtain ⟨hGk, hlock, hprodk⟩ := ih (by omega)
    have h0 : paperFT (iterResolvent γ k g) γ = 0 := by
      rw [hlock.eq_of_nhds]
      simp only [sub_self]
      rw [zero_pow (by omega), zero_mul]
    rw [iterResolvent_succ]
    refine ⟨superExpDecay_resolventDiv hGk h0 hγ, ?_, fun z => ?_⟩
    · have hlock' : paperFT (iterResolvent γ k g) =ᶠ[𝓝 γ]
          fun z => (z - γ) ^ ((m - (k + 1)) + 1) * v z := by
        rw [show m - (k + 1) + 1 = m - k by omega]; exact hlock
      exact paperFT_resolventDiv_eventually hGk h0 hγ hv hlock'
    · rw [← hprodk z, pow_succ, mul_assoc, paperFT_resolventDiv_mul hGk h0 hγ z]

/-- Tracking a second point `γ' ≠ γ` through the iteration. -/
theorem iterResolvent_eventually_ne {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ}
    (hγ : |γ.im| ≤ 1 / 2) {m : ℕ} {v : ℂ → ℂ} (hv : ContinuousAt v γ)
    (hloc : paperFT g =ᶠ[𝓝 γ] fun z => (z - γ) ^ m * v z) {γ' : ℂ} (hne : γ' ≠ γ) {k' : ℕ}
    {v' : ℂ → ℂ} (hloc' : paperFT g =ᶠ[𝓝 γ'] fun z => (z - γ') ^ k' * v' z) :
    ∀ k, k ≤ m → paperFT (iterResolvent γ k g) =ᶠ[𝓝 γ']
      fun z => (z - γ') ^ k' * (v' z / (z - γ) ^ k) := by
  intro k
  induction k with
  | zero => intro _; simpa [iterResolvent_zero] using hloc'
  | succ k ih =>
    intro hk
    obtain ⟨hGk, hlock, -⟩ := iterResolvent_spec hg hγ hv hloc k (by omega)
    have h0 : paperFT (iterResolvent γ k g) γ = 0 := by
      rw [hlock.eq_of_nhds]
      simp only [sub_self]
      rw [zero_pow (by omega), zero_mul]
    rw [iterResolvent_succ]
    have h := paperFT_resolventDiv_eventually_ne hGk h0 hγ hne (ih (by omega))
    refine h.trans (Eventually.of_forall fun z => ?_)
    simp only
    rw [div_div, ← pow_succ]

/-- Weighted tails along the iteration: each division costs a factor `2` and `3/2` in the weight. -/
theorem expTail_iterResolvent_le {g : ℝ → ℂ} (hg : SuperExpDecay g) {γ : ℂ}
    (hγ : |γ.im| ≤ 1 / 2) {m : ℕ} {v : ℂ → ℂ} (hv : ContinuousAt v γ)
    (hloc : paperFT g =ᶠ[𝓝 γ] fun z => (z - γ) ^ m * v z) :
    ∀ k, k ≤ m → ∀ c X : ℝ, 0 ≤ c →
      expTail (iterResolvent γ k g) c X ≤ 2 ^ k * expTail g (c + 3 / 2 * k) X := by
  intro k
  induction k with
  | zero => intro _ c X _; simp [iterResolvent_zero]
  | succ k ih =>
    intro hk c X hc
    obtain ⟨hGk, hlock, -⟩ := iterResolvent_spec hg hγ hv hloc k (by omega)
    have h0 : paperFT (iterResolvent γ k g) γ = 0 := by
      rw [hlock.eq_of_nhds]
      simp only [sub_self]
      rw [zero_pow (by omega), zero_mul]
    rw [iterResolvent_succ]
    calc expTail (resolventDiv γ (iterResolvent γ k g)) c X
        ≤ 2 * expTail (iterResolvent γ k g) (c + 3 / 2) X := expTail_resolventDiv_le hGk h0 hγ hc
      _ ≤ 2 * (2 ^ k * expTail g (c + 3 / 2 + 3 / 2 * k) X) := by
          gcongr; exact ih (by omega) _ _ (by linarith)
      _ = 2 ^ (k + 1) * expTail g (c + 3 / 2 * ((k + 1 : ℕ) : ℝ)) X := by
          push_cast; ring_nf

end

end RHTower
