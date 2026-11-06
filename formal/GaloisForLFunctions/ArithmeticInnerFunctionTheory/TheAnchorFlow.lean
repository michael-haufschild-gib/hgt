import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The anchor flow of a layered medium

A diagonal canonical system with determinant one is a layered medium with impedance potential
`q = Ψ′`. At the anchor `z = i` its endpoint traces solve

`τ_L′ = τ_L + q τ_R`, `τ_R′ = q τ_L − τ_R`,

and the reproducing kernel is `K = (τ_L² − τ_R²)/2`. In the hyperbolic coordinate `κ = artanh(τ_R/τ_L)` the
reflection obeys a scalar flow

`κ′ = q − sinh 2κ`.

The restoring force grows exponentially, and this gives a priori estimates free of the lower Weil
eigenvalue `μ`:

* **Coming down from infinity** (`abs_le_of_isAnchorFlow`). `|κ(x)| ≤ artanh e^{−2(x−c)} + ∫_c^x |q|`,
  for every `c < x`, with no dependence on the initial value. A flow forgets its past at
  rate `2`, so contact is purely local.
* **Energy identity** (`integral_sq_eq`). `∫ q² = ∫ (κ′² + sinh² 2κ) + [cosh 2κ]`, and
  `cosh 2κ = ½ (log K)′`.
* **Passivity propagates** (`IsAnchorTraces.passive`). For continuous `q` a passive initial state stays
  passive: contact needs a singular potential.
* **Darboux pair** (`IsAnchorTraces.darboux`). `p = τ_L + τ_R` and `w = τ_L − τ_R` are positive solutions of
  `p″ = (1 + q² + q′)p` and `w″ = (1 + q² − q′)w`, with `K = pw/2`. A positive solution of a Schrödinger
  equation is the Allegretto–Piepenbrink certificate; here it is the passive state itself.

**Soft kicks** (`kickFlow`, `abs_kickFlow_le`). Between reflectors `tanh κ` decays by `e^{−2h}`, and a
reflector adds its kick to `κ`. Again `|κ_n| ≤ artanh e^{−2(x_n−x_m)} + Σ_{m<j≤n} |k_j|`,
whatever came before `x_m`.
-/

open Set Filter Topology MeasureTheory intervalIntegral

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

/-! ### Hyperbolic identities -/

theorem one_sub_tanh_sq (x : ℝ) : 1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  have hc := Real.cosh_pos x
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  field_simp
  have := Real.cosh_sq x
  linarith

theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hc := Real.cosh_pos x
  have h := (Real.hasDerivAt_sinh x).fun_div (Real.hasDerivAt_cosh x) hc.ne'
  have e : (fun y => Real.sinh y / Real.cosh y) = Real.tanh := by
    funext y
    rw [Real.tanh_eq_sinh_div_cosh]
  rw [e] at h
  refine h.congr_deriv ?_
  have := Real.cosh_sq x
  congr 1
  nlinarith

theorem monotone_tanh : Monotone Real.tanh :=
  monotone_of_deriv_nonneg (fun x => (hasDerivAt_tanh x).differentiableAt) fun x => by
    rw [(hasDerivAt_tanh x).deriv]
    positivity

/-- The subtraction formula for `tanh`. -/
theorem tanh_sub_eq (u v : ℝ) :
    Real.tanh (u - v) = (Real.tanh u - Real.tanh v) / (1 - Real.tanh u * Real.tanh v) := by
  have hu := (Real.cosh_pos u).ne'
  have hv := (Real.cosh_pos v).ne'
  have hd : Real.cosh u * Real.cosh v - Real.sinh u * Real.sinh v ≠ 0 := by
    rw [← Real.cosh_sub]
    exact (Real.cosh_pos _).ne'
  have e1 : 1 - Real.sinh u / Real.cosh u * (Real.sinh v / Real.cosh v) =
      (Real.cosh u * Real.cosh v - Real.sinh u * Real.sinh v) / (Real.cosh u * Real.cosh v) := by
    field_simp
  have e2 : Real.sinh u / Real.cosh u - Real.sinh v / Real.cosh v =
      (Real.sinh u * Real.cosh v - Real.cosh u * Real.sinh v) / (Real.cosh u * Real.cosh v) := by
    field_simp
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_sub, Real.cosh_sub, Real.tanh_eq_sinh_div_cosh u,
    Real.tanh_eq_sinh_div_cosh v, e1, e2, div_div_div_cancel_right₀ (mul_ne_zero hu hv)]

theorem sinh_two_mul_eq (x : ℝ) : Real.sinh (2 * x) = 2 * Real.sinh x * Real.cosh x :=
  Real.sinh_two_mul x

theorem tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

/-! ### The flow -/

/-- `κ′ = q − sinh 2κ` on `[a, b]`. -/
def IsAnchorFlow (q κ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Icc a b, HasDerivAt κ (q x - Real.sinh (2 * κ x)) x

/-- The reflection `r = tanh κ` obeys `r′ = (1 − r²)q − 2r`. -/
theorem IsAnchorFlow.hasDerivAt_tanh {q κ : ℝ → ℝ} {a b : ℝ} (h : IsAnchorFlow q κ a b) {x : ℝ}
    (hx : x ∈ Icc a b) :
    HasDerivAt (fun y => Real.tanh (κ y))
      ((1 - Real.tanh (κ x) ^ 2) * q x - 2 * Real.tanh (κ x)) x := by
  have h1 : HasDerivAt (fun y => Real.tanh (κ y))
      (1 / Real.cosh (κ x) ^ 2 * (q x - Real.sinh (2 * κ x))) x :=
    (GaloisForLFunctions.ArithmeticInnerFunctionTheory.hasDerivAt_tanh (κ x)).comp x (h x hx)
  refine h1.congr_deriv ?_
  have hc := Real.cosh_pos (κ x)
  rw [one_sub_tanh_sq, sinh_two_mul_eq, Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- Decay of `tanh y e^{2z}` under `y′ ≤ −sinh 2y`, and the survival of positivity backwards. -/
theorem tanh_le_exp_of_deriv_le {y D : ℝ → ℝ} {c x : ℝ} (hcx : c ≤ x)
    (hy : ∀ z ∈ Icc c x, HasDerivAt y (D z) z)
    (hD : ∀ z ∈ Icc c x, 0 ≤ y z → D z ≤ -Real.sinh (2 * y z)) :
    Real.tanh (y x) ≤ Real.exp (-2 * (x - c)) := by
  have hcont : ContinuousOn y (Icc c x) := fun z hz => (hy z hz).continuousAt.continuousWithinAt
  by_cases hyx : y x ≤ 0
  · have h0 : Real.tanh (y x) ≤ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hyx) (Real.cosh_pos _).le
    exact h0.trans (Real.exp_pos _).le
  push Not at hyx
  -- positivity persists backwards
  have hposall : ∀ z ∈ Icc c x, 0 < y z := by
    intro z hz
    by_contra hneg
    push Not at hneg
    set S : Set ℝ := Icc c x ∩ y ⁻¹' Iic 0 with hS
    have hclosed : IsClosed S := by
      exact hcont.preimage_isClosed_of_isClosed isClosed_Icc (t := Iic 0) isClosed_Iic
    have hSne : S.Nonempty := ⟨z, hz, hneg⟩
    have hSb : BddAbove S := ⟨x, fun w hw => hw.1.2⟩
    set x₀ := sSup S with hx₀
    have hmem : x₀ ∈ S := hclosed.csSup_mem hSne hSb
    have hx₀x : x₀ < x := by
      refine lt_of_le_of_ne hmem.1.2 fun he => ?_
      have := hmem.2
      rw [he] at this
      exact absurd this (not_le.mpr hyx)
    have hpos : ∀ w ∈ Ioc x₀ x, 0 < y w := by
      intro w hw
      by_contra hw0
      push Not at hw0
      have hws : w ∈ S := ⟨⟨hmem.1.1.trans hw.1.le, hw.2⟩, hw0⟩
      exact absurd (le_csSup hSb hws) (not_le.mpr hw.1)
    have hsub : Icc x₀ x ⊆ Icc c x := Icc_subset_Icc_left hmem.1.1
    have hanti : AntitoneOn y (Icc x₀ x) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (hcont.mono hsub) ?_ ?_
      · intro w hw
        rw [interior_Icc] at hw
        exact (hy w (hsub (Ioo_subset_Icc_self hw))).differentiableAt.differentiableWithinAt
      · intro w hw
        rw [interior_Icc] at hw
        have hw' := hsub (Ioo_subset_Icc_self hw)
        rw [(hy w hw').deriv]
        have hp := hpos w ⟨hw.1, hw.2.le⟩
        have := hD w hw' hp.le
        have hs : 0 ≤ Real.sinh (2 * y w) := Real.sinh_nonneg_iff.mpr (by positivity)
        linarith
    have := hanti (left_mem_Icc.mpr hx₀x.le) (right_mem_Icc.mpr hx₀x.le) hx₀x.le
    have h0 := hmem.2
    simp only [mem_preimage, mem_Iic] at h0
    linarith
  -- monotonicity of `tanh y e^{2z}`
  set Φ : ℝ → ℝ := fun z => Real.tanh (y z) * Real.exp (2 * z) with hΦ
  have hΦd : ∀ z ∈ Icc c x, HasDerivAt Φ (1 / Real.cosh (y z) ^ 2 * D z * Real.exp (2 * z) +
      Real.tanh (y z) * (Real.exp (2 * z) * 2)) z := by
    intro z hz
    have h1 := (GaloisForLFunctions.ArithmeticInnerFunctionTheory.hasDerivAt_tanh (y z)).comp z (hy z hz)
    have h2 : HasDerivAt (fun w : ℝ => Real.exp (2 * w)) (Real.exp (2 * z) * 2) z := by
      have := ((hasDerivAt_id z).const_mul (2 : ℝ)).exp
      simpa using this
    exact h1.mul h2
  have hanti : AntitoneOn Φ (Icc c x) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun z hz => (hΦd z hz).continuousAt.continuousWithinAt) ?_ ?_
    · intro w hw
      rw [interior_Icc] at hw
      exact (hΦd w (Ioo_subset_Icc_self hw)).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hw' := Ioo_subset_Icc_self hw
      rw [(hΦd w hw').deriv]
      have hp := hposall w hw'
      have hDw := hD w hw' hp.le
      have hc := Real.cosh_pos (y w)
      have he := Real.exp_pos (2 * w)
      have e : 1 / Real.cosh (y w) ^ 2 * D w * Real.exp (2 * w) +
          Real.tanh (y w) * (Real.exp (2 * w) * 2) =
          Real.exp (2 * w) * ((D w + Real.sinh (2 * y w)) / Real.cosh (y w) ^ 2) := by
        rw [sinh_two_mul_eq, Real.tanh_eq_sinh_div_cosh]
        field_simp
      rw [e]
      refine mul_nonpos_of_nonneg_of_nonpos he.le (div_nonpos_of_nonpos_of_nonneg ?_ (by positivity))
      linarith
  have hle := hanti (left_mem_Icc.mpr hcx) (right_mem_Icc.mpr hcx) hcx
  simp only [hΦ] at hle
  have htc : Real.tanh (y c) ≤ 1 := (Real.tanh_lt_one _).le
  have h2 : Real.tanh (y x) * Real.exp (2 * x) ≤ Real.exp (2 * c) := by
    refine hle.trans ?_
    have := mul_le_mul_of_nonneg_right htc (Real.exp_pos (2 * c)).le
    linarith
  have e : Real.exp (-2 * (x - c)) = Real.exp (2 * c) / Real.exp (2 * x) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [e, le_div_iff₀ (Real.exp_pos _)]
  exact h2

/-- `artanh` of the cooling factor. -/
def coolingBound (h : ℝ) : ℝ := Real.artanh (Real.exp (-2 * h))

theorem coolingBound_nonneg (h : ℝ) : 0 ≤ coolingBound h :=
  Real.artanh_nonneg (Real.exp_pos _).le

/-- `tanh y ≤ e^{−2h}` with `h > 0` is `y ≤ artanh e^{−2h}`. -/
theorem le_coolingBound_of_tanh_le {y h : ℝ} (hh : 0 < h) (hy : Real.tanh y ≤ Real.exp (-2 * h)) :
    y ≤ coolingBound h := by
  have h1 : Real.exp (-2 * h) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h2 : -1 < Real.tanh y := (abs_lt.mp (Real.abs_tanh_lt_one y)).1
  have := Real.artanh_le_artanh h2 h1 hy
  rwa [Real.artanh_tanh] at this

/-- **Coming down from infinity.** For `c < x`, `|κ(x)| ≤ artanh e^{−2(x−c)} + ∫_c^x |q|`. No bound on
`κ(c)` is needed. -/
theorem abs_le_of_isAnchorFlow {q κ : ℝ → ℝ} {c x : ℝ} (hq : Continuous q) (hcx : c < x)
    (h : IsAnchorFlow q κ c x) :
    |κ x| ≤ coolingBound (x - c) + ∫ z in c..x, |q z| := by
  have hQc : Continuous fun z => |q z| := hq.abs
  set Q : ℝ → ℝ := fun z => ∫ w in c..z, |q w| with hQ
  have hQd : ∀ z, HasDerivAt Q |q z| z := fun z =>
    intervalIntegral.integral_hasDerivAt_right (hQc.intervalIntegrable _ _)
      (hQc.stronglyMeasurableAtFilter _ _) hQc.continuousAt
  have hQ0 : ∀ z ∈ Icc c x, 0 ≤ Q z := fun z hz =>
    intervalIntegral.integral_nonneg hz.1 fun _ _ => abs_nonneg _
  have hup : κ x - Q x ≤ coolingBound (x - c) := by
    refine le_coolingBound_of_tanh_le (by linarith) ?_
    refine tanh_le_exp_of_deriv_le (y := fun z => κ z - Q z)
      (D := fun z => (q z - Real.sinh (2 * κ z)) - |q z|) hcx.le
      (fun z hz => (h z hz).sub (hQd z)) fun z hz hy => ?_
    have h1 : 2 * (κ z - Q z) ≤ 2 * κ z := by linarith [hQ0 z hz]
    have h2 := Real.sinh_le_sinh.mpr h1
    have h3 := le_abs_self (q z)
    linarith
  have hlo : -κ x - Q x ≤ coolingBound (x - c) := by
    refine le_coolingBound_of_tanh_le (by linarith) ?_
    refine tanh_le_exp_of_deriv_le (y := fun z => -κ z - Q z)
      (D := fun z => -(q z - Real.sinh (2 * κ z)) - |q z|) hcx.le
      (fun z hz => (h z hz).neg.sub (hQd z)) fun z hz hy => ?_
    have h1 : 2 * (-κ z - Q z) ≤ 2 * (-κ z) := by linarith [hQ0 z hz]
    have h2 := Real.sinh_le_sinh.mpr h1
    have h3 := neg_le_abs (q z)
    rw [show 2 * (-κ z) = -(2 * κ z) by ring, Real.sinh_neg] at h2
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The reflection stays a definite distance from the boundary on every bounded `∫|q|`. -/
theorem one_sub_tanh_sq_ge_of_isAnchorFlow {q κ : ℝ → ℝ} {c x : ℝ} (hq : Continuous q) (hcx : c < x)
    (h : IsAnchorFlow q κ c x) :
    1 / Real.cosh (coolingBound (x - c) + ∫ z in c..x, |q z|) ^ 2 ≤ 1 - Real.tanh (κ x) ^ 2 := by
  rw [one_sub_tanh_sq]
  have hab := abs_le_of_isAnchorFlow hq hcx h
  have hc : Real.cosh (κ x) ≤ Real.cosh (coolingBound (x - c) + ∫ z in c..x, |q z|) := by
    rw [← Real.cosh_abs (κ x)]
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_abs]
    exact hab.trans (le_abs_self _)
  exact one_div_le_one_div_of_le (pow_pos (Real.cosh_pos _) 2)
    (pow_le_pow_left₀ (Real.cosh_pos _).le hc 2)

/-- **The energy identity.** `∫ q² = ∫ (κ′² + sinh² 2κ) + cosh 2κ(b) − cosh 2κ(a)`. -/
theorem integral_sq_eq {q κ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hq : Continuous q)
    (h : IsAnchorFlow q κ a b) :
    ∫ x in a..b, q x ^ 2 =
      (∫ x in a..b, ((q x - Real.sinh (2 * κ x)) ^ 2 + Real.sinh (2 * κ x) ^ 2)) +
        Real.cosh (2 * κ b) - Real.cosh (2 * κ a) := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  have hκc : ContinuousOn κ (uIcc a b) := by
    rw [hu]
    exact fun z hz => (h z hz).continuousAt.continuousWithinAt
  have hs : ContinuousOn (fun x => Real.sinh (2 * κ x)) (uIcc a b) :=
    Real.continuous_sinh.comp_continuousOn (continuousOn_const.mul hκc)
  have hc1 : ContinuousOn (fun x => (q x - Real.sinh (2 * κ x)) ^ 2 + Real.sinh (2 * κ x) ^ 2)
      (uIcc a b) := ((hq.continuousOn.sub hs).pow 2).add (hs.pow 2)
  have hc2 : ContinuousOn (fun x => 2 * Real.sinh (2 * κ x) * (q x - Real.sinh (2 * κ x)))
      (uIcc a b) := (continuousOn_const.mul hs).mul (hq.continuousOn.sub hs)
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun y => Real.cosh (2 * κ y))
      (2 * Real.sinh (2 * κ x) * (q x - Real.sinh (2 * κ x))) x := by
    intro x hx
    rw [hu] at hx
    have h1 := ((h x hx).const_mul (2 : ℝ)).cosh
    convert h1 using 1
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc2.intervalIntegrable
  have hsplit : ∀ x, q x ^ 2 = ((q x - Real.sinh (2 * κ x)) ^ 2 + Real.sinh (2 * κ x) ^ 2) +
      2 * Real.sinh (2 * κ x) * (q x - Real.sinh (2 * κ x)) := fun x => by ring
  simp_rw [hsplit]
  rw [intervalIntegral.integral_add hc1.intervalIntegrable hc2.intervalIntegrable, hftc]
  ring

/-- The `L²` norm of `q` bounds the reflection: `cosh 2κ(b) ≤ cosh 2κ(a) + ∫ q²`. -/
theorem cosh_le_add_integral_sq {q κ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hq : Continuous q)
    (h : IsAnchorFlow q κ a b) :
    Real.cosh (2 * κ b) ≤ Real.cosh (2 * κ a) + ∫ x in a..b, q x ^ 2 := by
  have he := integral_sq_eq hab hq h
  have hnn : 0 ≤ ∫ x in a..b, ((q x - Real.sinh (2 * κ x)) ^ 2 + Real.sinh (2 * κ x) ^ 2) :=
    intervalIntegral.integral_nonneg hab fun _ _ => by positivity
  linarith

/-! ### Traces -/

/-- The endpoint traces at the anchor of a medium with potential `q`. -/
structure IsAnchorTraces (q τL τR : ℝ → ℝ) (a b : ℝ) : Prop where
  left : ∀ x ∈ Icc a b, HasDerivAt τL (τL x + q x * τR x) x
  right : ∀ x ∈ Icc a b, HasDerivAt τR (q x * τL x - τR x) x

namespace IsAnchorTraces

variable {q τL τR : ℝ → ℝ} {a b : ℝ} (h : IsAnchorTraces q τL τR a b)

include h

/-- `K = (τ_L² − τ_R²)/2` has `K′ = τ_L² + τ_R²`. -/
theorem hasDerivAt_kernel {x : ℝ} (hx : x ∈ Icc a b) :
    HasDerivAt (fun y => (τL y ^ 2 - τR y ^ 2) / 2) (τL x ^ 2 + τR x ^ 2) x := by
  have h1 := ((h.left x hx).fun_pow 2).fun_sub ((h.right x hx).fun_pow 2)
  refine (h1.div_const 2).congr_deriv ?_
  push_cast
  ring

/-- **Passivity propagates.** A passive initial state stays passive on a regular medium:
`τ_L > |τ_R|` throughout. So contact needs a singular potential. -/
theorem passive (ha : |τR a| < τL a) {x : ℝ} (hx : x ∈ Icc a b) : |τR x| < τL x := by
  set K : ℝ → ℝ := fun y => (τL y ^ 2 - τR y ^ 2) / 2 with hK
  have hKd := fun z hz => h.hasDerivAt_kernel (x := z) hz
  have hmono : MonotoneOn K (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun z hz => (hKd z hz).continuousAt.continuousWithinAt) ?_ ?_
    · intro w hw
      rw [interior_Icc] at hw
      exact (hKd w (Ioo_subset_Icc_self hw)).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      rw [(hKd w (Ioo_subset_Icc_self hw)).deriv]
      positivity
  have hab : a ≤ b := hx.1.trans hx.2
  have hKa : 0 < K a := by
    have h1 : τR a ^ 2 < τL a ^ 2 := sq_lt_sq' (by linarith [abs_lt.mp (lt_of_le_of_lt (le_refl _) ha), neg_abs_le (τR a)]) (lt_of_le_of_lt (le_abs_self _) ha)
    simp only [hK]
    linarith
  have hKz : ∀ z ∈ Icc a b, 0 < K z := fun z hz =>
    lt_of_lt_of_le hKa (hmono (left_mem_Icc.mpr hab) hz hz.1)
  have hτ0 : ∀ z ∈ Icc a b, τL z ≠ 0 := by
    intro z hz h0
    have := hKz z hz
    simp only [hK, h0] at this
    nlinarith [sq_nonneg (τR z)]
  -- `τ_L` keeps its sign by the intermediate value theorem
  have hτpos : ∀ z ∈ Icc a b, 0 < τL z := by
    intro z hz
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn τL (Icc a z) := fun w hw =>
      (h.left w ⟨hw.1, hw.2.trans hz.2⟩).continuousAt.continuousWithinAt
    have hτa : 0 < τL a := lt_of_le_of_lt (abs_nonneg _) ha
    obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' hz.1 hcont ⟨hneg, hτa.le⟩
    exact hτ0 w ⟨hw.1, hw.2.trans hz.2⟩ hw0
  have hK' := hKz x hx
  have hτ' := hτpos x hx
  simp only [hK] at hK'
  have h2 : τR x ^ 2 < τL x ^ 2 := by linarith
  exact abs_lt_of_sq_lt_sq h2 hτ'.le

/-- The Darboux pair: first-order form. -/
theorem hasDerivAt_sum {x : ℝ} (hx : x ∈ Icc a b) :
    HasDerivAt (fun y => τL y + τR y) (q x * (τL x + τR x) + (τL x - τR x)) x := by
  refine ((h.left x hx).fun_add (h.right x hx)).congr_deriv ?_
  ring

theorem hasDerivAt_diff {x : ℝ} (hx : x ∈ Icc a b) :
    HasDerivAt (fun y => τL y - τR y) ((τL x + τR x) - q x * (τL x - τR x)) x := by
  refine ((h.left x hx).fun_sub (h.right x hx)).congr_deriv ?_
  ring

/-- **The Darboux pair.** With `q` differentiable, `p = τ_L + τ_R` and `w = τ_L − τ_R` have derivatives
`p′ = qp + w`, `w′ = p − qw`, and solve `p″ = (1 + q² + q′)p`, `w″ = (1 + q² − q′)w`. Positive solutions of these
Schrödinger equations are the passive state: the certificate of Allegretto and Piepenbrink, read at the anchor. -/
theorem darboux {q' : ℝ → ℝ} (hq : ∀ x ∈ Icc a b, HasDerivAt q (q' x) x) {x : ℝ}
    (hx : x ∈ Ioo a b) :
    HasDerivAt (deriv fun y => τL y + τR y) ((1 + q x ^ 2 + q' x) * (τL x + τR x)) x ∧
      HasDerivAt (deriv fun y => τL y - τR y) ((1 + q x ^ 2 - q' x) * (τL x - τR x)) x := by
  have hx' := Ioo_subset_Icc_self hx
  have hev : ∀ᶠ y in 𝓝 x, y ∈ Icc a b := Icc_mem_nhds hx.1 hx.2
  have hp : deriv (fun y => τL y + τR y) =ᶠ[𝓝 x] fun y => q y * (τL y + τR y) + (τL y - τR y) := by
    filter_upwards [hev] with y hy using (h.hasDerivAt_sum hy).deriv
  have hw : deriv (fun y => τL y - τR y) =ᶠ[𝓝 x] fun y => (τL y + τR y) - q y * (τL y - τR y) := by
    filter_upwards [hev] with y hy using (h.hasDerivAt_diff hy).deriv
  constructor
  · refine HasDerivAt.congr_of_eventuallyEq ?_ hp
    refine (((hq x hx').fun_mul (h.hasDerivAt_sum hx')).fun_add (h.hasDerivAt_diff hx')).congr_deriv ?_
    ring
  · refine HasDerivAt.congr_of_eventuallyEq ?_ hw
    refine ((h.hasDerivAt_sum hx').fun_sub ((hq x hx').fun_mul (h.hasDerivAt_diff hx'))).congr_deriv ?_
    ring

omit h in
/-- The product of the Darboux pair is `2K`. -/
theorem sum_mul_diff (x : ℝ) : (τL x + τR x) * (τL x - τR x) = 2 * ((τL x ^ 2 - τR x ^ 2) / 2) := by
  ring

/-- In the passive region `κ = ½ log (p/w)` solves the anchor flow. -/
theorem isAnchorFlow_kappa (ha : |τR a| < τL a) :
    IsAnchorFlow q (fun x => (1 / 2) * Real.log ((τL x + τR x) / (τL x - τR x))) a b := by
  intro x hx
  have hp := h.passive ha hx
  have hpos1 : 0 < τL x + τR x := by linarith [neg_abs_le (τR x)]
  have hpos2 : 0 < τL x - τR x := by linarith [le_abs_self (τR x)]
  have hd := ((h.hasDerivAt_sum hx).fun_div (h.hasDerivAt_diff hx) hpos2.ne').log (div_pos hpos1 hpos2).ne'
  refine (hd.const_mul (1 / 2 : ℝ)).congr_deriv ?_
  set p := τL x + τR x
  set w := τL x - τR x
  have he : Real.exp (2 * ((1 / 2) * Real.log (p / w))) = p / w := by
    rw [show 2 * ((1 / 2 : ℝ) * Real.log (p / w)) = Real.log (p / w) by ring,
      Real.exp_log (div_pos hpos1 hpos2)]
  have he' : Real.exp (-(2 * ((1 / 2) * Real.log (p / w)))) = w / p := by
    rw [Real.exp_neg, he, inv_div]
  rw [Real.sinh_eq, he, he']
  field_simp
  ring

/-- `κ` is the hyperbolic coordinate of the reflection `r = τ_R/τ_L`. -/
theorem kappa_eq_artanh (ha : |τR a| < τL a) {x : ℝ} (hx : x ∈ Icc a b) :
    (1 / 2) * Real.log ((τL x + τR x) / (τL x - τR x)) = Real.artanh (τR x / τL x) := by
  have hp := h.passive ha hx
  have hL : 0 < τL x := lt_of_le_of_lt (abs_nonneg _) hp
  have hlt := abs_lt.mp hp
  have hr : τR x / τL x ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · rw [le_div_iff₀ hL]; linarith
    · rw [div_le_iff₀ hL]; linarith
  rw [Real.artanh_eq_half_log hr]
  congr 2
  field_simp

/-- **The kernel flow.** In the passive region `(log K)′ = 2 cosh 2κ = 2(1 + r²)/(1 − r²)`. -/
theorem hasDerivAt_log_kernel (ha : |τR a| < τL a) {x : ℝ} (hx : x ∈ Icc a b) :
    HasDerivAt (fun y => Real.log ((τL y ^ 2 - τR y ^ 2) / 2))
      (2 * Real.cosh (2 * ((1 / 2) * Real.log ((τL x + τR x) / (τL x - τR x))))) x := by
  have hp := h.passive ha hx
  have hpos1 : 0 < τL x + τR x := by linarith [neg_abs_le (τR x)]
  have hpos2 : 0 < τL x - τR x := by linarith [le_abs_self (τR x)]
  have hK : (τL x ^ 2 - τR x ^ 2) / 2 ≠ 0 := by
    have : τL x ^ 2 - τR x ^ 2 = (τL x + τR x) * (τL x - τR x) := by ring
    rw [this]
    positivity
  refine ((h.hasDerivAt_kernel hx).log hK).congr_deriv ?_
  rw [show 2 * ((1 / 2 : ℝ) * Real.log ((τL x + τR x) / (τL x - τR x))) =
      Real.log ((τL x + τR x) / (τL x - τR x)) by ring, Real.cosh_eq,
    Real.exp_neg, Real.exp_log (div_pos hpos1 hpos2)]
  have hA : τL x ^ 2 + τR x ^ 2 = ((τL x + τR x) ^ 2 + (τL x - τR x) ^ 2) / 2 := by ring
  have hB : τL x ^ 2 - τR x ^ 2 = (τL x + τR x) * (τL x - τR x) := by ring
  rw [hA, hB]
  generalize τL x + τR x = P at hpos1 ⊢
  generalize τL x - τR x = W at hpos2 ⊢
  field_simp

end IsAnchorTraces

/-! ### Soft kicks -/

/-- Free cooling over a gap `h`: `tanh κ ↦ e^{−2h} tanh κ`. -/
def cool (h κ : ℝ) : ℝ := Real.artanh (Real.exp (-2 * h) * Real.tanh κ)

/-- One step of a kicked medium: free cooling over the gap `h`, then a kick `k`. -/
def kickStep (h k κ : ℝ) : ℝ := cool h κ + k

theorem cool_mem_Ioo {h : ℝ} (hh : 0 ≤ h) (κ : ℝ) :
    Real.exp (-2 * h) * Real.tanh κ ∈ Ioo (-1 : ℝ) 1 := by
  have hq : Real.exp (-2 * h) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hq0 := Real.exp_pos (-2 * h)
  have h1 := abs_lt.mp (Real.abs_tanh_lt_one κ)
  constructor <;> nlinarith

theorem tanh_cool {h : ℝ} (hh : 0 ≤ h) (κ : ℝ) :
    Real.tanh (cool h κ) = Real.exp (-2 * h) * Real.tanh κ :=
  Real.tanh_artanh (cool_mem_Ioo hh κ)

theorem cool_neg {h : ℝ} (hh : 0 ≤ h) (κ : ℝ) : cool h (-κ) = -cool h κ := by
  apply Real.tanh_injective
  rw [tanh_cool hh, Real.tanh_neg, Real.tanh_neg, tanh_cool hh]
  ring

theorem cool_nonneg (h : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ cool h κ :=
  Real.artanh_nonneg (mul_nonneg (Real.exp_pos _).le (tanh_nonneg_of_nonneg hκ))

theorem abs_cool {h : ℝ} (hh : 0 ≤ h) (κ : ℝ) : |cool h κ| = cool h |κ| := by
  rcases le_total 0 κ with hκ | hκ
  · rw [abs_of_nonneg hκ, abs_of_nonneg (cool_nonneg h hκ)]
  · rw [abs_of_nonpos hκ, cool_neg hh, abs_of_nonpos]
    have := cool_nonneg h (neg_nonneg.mpr hκ)
    rw [cool_neg hh] at this
    linarith

/-- The cross-multiplied comparison behind the discrete coming-down estimate. -/
theorem tanh_cool_sub_le {h S A : ℝ} (hh : 0 ≤ h) (hS : 0 ≤ S) (hA : 0 ≤ A) :
    Real.tanh (cool h A - S) ≤ Real.exp (-2 * h) * Real.tanh (A - S) := by
  set q := Real.exp (-2 * h) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := by
    rw [hq, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  set a := Real.tanh A with ha
  set s := Real.tanh S with hs
  have ha0 : 0 ≤ a := tanh_nonneg_of_nonneg hA
  have hs0 : 0 ≤ s := tanh_nonneg_of_nonneg hS
  have ha1 : a < 1 := Real.tanh_lt_one A
  have hs1 : s < 1 := Real.tanh_lt_one S
  rw [tanh_sub_eq, tanh_sub_eq, tanh_cool hh, ← hq, ← ha, ← hs]
  have hd1 : 0 < 1 - q * a * s := by nlinarith [mul_nonneg ha0 hs0, mul_lt_one_of_nonneg_of_lt_one_left ha0 ha1 hs1.le]
  have hd2 : 0 < 1 - a * s := by nlinarith [mul_lt_one_of_nonneg_of_lt_one_left ha0 ha1 hs1.le]
  rw [div_le_iff₀ hd1, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hd2]
  have hbr : 0 ≤ (1 - a * s) + q * a * (a - s) := by
    rcases le_total s a with hsa | hsa
    · have : 0 ≤ q * a * (a - s) := mul_nonneg (mul_nonneg hq0.le ha0) (by linarith)
      linarith
    · have h1 : q * (a * (a - s)) ≥ a * (a - s) := by
        have : a * (a - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 (by linarith)
        nlinarith
      nlinarith [sq_nonneg (1 - a), mul_nonneg ha0 hs0, mul_le_of_le_one_right ha0 hs1.le]
  have key : 0 ≤ (1 - q) * s * ((1 - a * s) + q * a * (a - s)) :=
    mul_nonneg (mul_nonneg (by linarith) hs0) hbr
  nlinarith

/-- A kicked medium: positions `x`, kicks `k`. -/
def kickFlow (x k : ℕ → ℝ) (κ₀ : ℝ) : ℕ → ℝ
  | 0 => κ₀
  | n + 1 => kickStep (x (n + 1) - x n) (k (n + 1)) (kickFlow x k κ₀ n)

/-- **Coming down from infinity with kicks.** Whatever the state at `x_m`,
`tanh (|κ_n| − Σ_{m<j≤n} |k_j|) ≤ e^{−2(x_n − x_m)}`. -/
theorem tanh_abs_kickFlow_sub_le {x k : ℕ → ℝ} (hx : Monotone x) (κ₀ : ℝ) (m n : ℕ) :
    Real.tanh (|kickFlow x k κ₀ (m + n)| - ∑ j ∈ Finset.range n, |k (m + j + 1)|) ≤
      Real.exp (-2 * (x (m + n) - x m)) := by
  induction n with
  | zero =>
    simp only [add_zero, Finset.range_zero, Finset.sum_empty, sub_zero, sub_self, mul_zero,
      Real.exp_zero]
    exact (Real.tanh_lt_one _).le
  | succ n ih =>
    set h := x (m + n + 1) - x (m + n) with hh
    have hh0 : 0 ≤ h := sub_nonneg.mpr (hx (Nat.le_succ _))
    set A := |kickFlow x k κ₀ (m + n)| with hA
    set S := ∑ j ∈ Finset.range n, |k (m + j + 1)| with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hstep : |kickFlow x k κ₀ (m + (n + 1))| ≤ cool h A + |k (m + n + 1)| := by
      change |cool h (kickFlow x k κ₀ (m + n)) + k (m + n + 1)| ≤ _
      refine (abs_add_le _ _).trans ?_
      rw [abs_cool hh0]
    have hmono : Real.tanh (|kickFlow x k κ₀ (m + (n + 1))| -
        ∑ j ∈ Finset.range (n + 1), |k (m + j + 1)|) ≤ Real.tanh (cool h A - S) := by
      refine monotone_tanh ?_
      rw [Finset.sum_range_succ]
      linarith
    have h2 := tanh_cool_sub_le hh0 hS0 (abs_nonneg (kickFlow x k κ₀ (m + n)))
    have hq := Real.exp_pos (-2 * h)
    have h3 := mul_le_mul_of_nonneg_left ih hq.le
    have e : Real.exp (-2 * h) * Real.exp (-2 * (x (m + n) - x m)) =
        Real.exp (-2 * (x (m + (n + 1)) - x m)) := by
      rw [← Real.exp_add]
      congr 1
      rw [hh, ← add_assoc]
      ring
    rw [e] at h3
    exact hmono.trans (h2.trans h3)

/-- **The a priori estimate for kicked media, free of `1/μ`.** -/
theorem abs_kickFlow_le {x k : ℕ → ℝ} (hx : Monotone x) (κ₀ : ℝ) (m n : ℕ) (hmn : x m < x (m + n)) :
    |kickFlow x k κ₀ (m + n)| ≤ coolingBound (x (m + n) - x m) +
      ∑ j ∈ Finset.range n, |k (m + j + 1)| := by
  have h := le_coolingBound_of_tanh_le (sub_pos.mpr hmn) (tanh_abs_kickFlow_sub_le (k := k) hx κ₀ m n)
  linarith

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
