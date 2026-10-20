import GaloisForLFunctions.ArithmeticCriticalityTheory.FoldedSourceOriginJumpMomentLaw
import GaloisForLFunctions.RHTower.RiemannKernelSharpLogDerivative
import GaloisForLFunctions.RHTower.CCMRiemannKernelBartaLayerBounds
import GaloisForLFunctions.RHTower.CCMRiemannKernelBartaFarTail

/-!
# Which half of the folded no-go sees the rates: the extra-jump visibility threshold

No positive profile is a folded supersolution: positive gauges fail near the origin (jump-measure
moment) and at infinity (cosh moment). Perturb the jump measure of the shifted ground state
`ω_a = m_a/Φ` by one extra jump of length `ℓ > 0` at rate `δ > 0`, keeping the potential
`Φ cosh(x/2)`. In test coordinates the extra term is
`m_a(x)(Φ(x+ℓ) + Φ(x−ℓ)) − Φ(x)(m_a(x+ℓ) + m_a(|x−ℓ|))`, and against the scale `Φ(x) e^{x/2}` of the
folded source its size at infinity is governed by `Φ(x−a)Φ(x−ℓ)/Φ(x) ≈ exp(πe^{2x}(1 − e^{−2a} − e^{−2ℓ}))`.

* **Visible jumps** (`exists_foldedGenerator_add_extraJump_gt_potential`). If
  `e^{−2a} + e^{−2ℓ} < 1`, then for every rate `δ > 0`, however small, `ω_a` is a strict supersolution
  of the perturbed folded generator on a neighbourhood of infinity: the extra term grows doubly
  exponentially (`tendsto_extraJumpRatio_atTop`) and beats the source `≈ −2(∫ m_a cosh) Φ e^{x/2}`.
* **Invisible jumps** (`exists_foldedGenerator_add_extraJump_lt_potential`). If
  `e^{−2a} + e^{−2ℓ} > 1`, the extra term is negligible on that scale (`tendsto_extraJumpRatio_zero`)
  and `ω_a` stays a strict subsolution at infinity, for every rate.
* **The origin is rate-blind** (`exists_origin_window_foldedGenerator_add_extraJump_lt_potential`).
  For every extra jump the folded source near the origin tends to `−2Φ(0)(J(m_a) + δ m_a(ℓ)) < 0`:
  extra jumps only deepen the origin failure.

The threshold curve `e^{−2a} + e^{−2ℓ} = 1` is the graph of the window killing function
`N(a) = −½ log(1 − e^{−2a})`, an involution: the ground state `ω_a` detects at infinity exactly the
jumps longer than `N(a)`. For a jump at a prime power, `ℓ = log n`, visibility means
`e^{−2a} < 1 − n^{−2}`; at the prime `2` it is `e^{−2a} < 3/4` (`…_log_two`). The arithmetic rates
are thus critical at infinity in the opposite direction to rate-criticality of the form: any excess
rate at a visible length creates supersolutions at infinity, while the origin half of the no-go does
not see the rates at all.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Decay of `Φ'` and of the shift differences -/

/-- `e^{13v/2} e^{−πe^{2v}} ≤ e⁴ e^{−8v}` for `v ≥ 0`. -/
theorem exp_mul_exp_neg_pi_exp_le_exp_neg_eight {v : ℝ} (hv : 0 ≤ v) :
    Real.exp (13 / 2 * v) * Real.exp (-Real.pi * Real.exp (2 * v)) ≤
      Real.exp 4 * Real.exp (-(8 * v)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : 1 + v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
  have h2 : (1 + v) ^ 2 ≤ Real.exp (2 * v) := by
    rw [show 2 * v = v + v by ring, Real.exp_add]
    nlinarith
  have h3 : 3 * (1 + v) ^ 2 ≤ Real.pi * Real.exp (2 * v) :=
    mul_le_mul Real.pi_gt_three.le h2 (sq_nonneg _) Real.pi_pos.le
  nlinarith [sq_nonneg (v - 17 / 12)]

/-- `|Φ'(u)| ≤ C e^{−8|u|}`. -/
theorem exists_abs_deriv_riemannKernelReal_le_exp_eight :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, |deriv riemannKernelReal u| ≤ C * Real.exp (-(8 * |u|)) := by
  have hC := cuspDecayConst_nonneg (riemannKernelPoly 1)
  refine ⟨cuspDecayConst (riemannKernelPoly 1) * Real.exp 4,
    mul_nonneg hC (Real.exp_pos 4).le, fun u => ?_⟩
  rw [(hasDerivAt_riemannKernelReal u).deriv]
  refine (Complex.abs_re_le_norm _).trans ((norm_riemannKernelDeriv_le 1 u).trans ?_)
  have e : (2 * ((1 : ℕ) : ℝ) + 9 / 2) = 13 / 2 := by norm_num
  rw [e, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (exp_mul_exp_neg_pi_exp_le_exp_neg_eight (abs_nonneg u)) hC

/-- A shift difference of a function with `e^{−8|u|}` decay keeps the decay. -/
theorem abs_sub_comp_add_le {f : ℝ → ℝ} {C : ℝ} (hf : ∀ u, |f u| ≤ C * Real.exp (-(8 * |u|)))
    (a y : ℝ) :
    |f (y - a) - f (y + a)| ≤ 2 * C * Real.exp (8 * |a|) * Real.exp (-(8 * |y|)) := by
  have hC := nonneg_of_abs_le_mul_exp hf
  have e1 : Real.exp (-(8 * |y - a|)) ≤ Real.exp (8 * |a|) * Real.exp (-(8 * |y|)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [abs_sub_abs_le_abs_sub y a])
  have e2 : Real.exp (-(8 * |y + a|)) ≤ Real.exp (8 * |a|) * Real.exp (-(8 * |y|)) := by
    have := abs_sub_abs_le_abs_sub y (-a)
    rw [abs_neg, sub_neg_eq_add] at this
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc |f (y - a) - f (y + a)| ≤ |f (y - a)| + |f (y + a)| := abs_sub _ _
    _ ≤ C * (Real.exp (8 * |a|) * Real.exp (-(8 * |y|))) +
        C * (Real.exp (8 * |a|) * Real.exp (-(8 * |y|))) :=
        add_le_add ((hf _).trans (mul_le_mul_of_nonneg_left e1 hC))
          ((hf _).trans (mul_le_mul_of_nonneg_left e2 hC))
    _ = _ := by ring

/-- `m_a` and `m_a'` decay like `e^{−8|y|}`. -/
theorem exists_shiftDifference_decay_eight (a : ℝ) :
    ∃ C : ℝ, (∀ y, |shiftDifference a y| ≤ C * Real.exp (-(8 * |y|))) ∧
      ∀ y, |deriv (shiftDifference a) y| ≤ C * Real.exp (-(8 * |y|)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_riemannKernelReal_le_exp_eight
  obtain ⟨C₁, hC₁, h₁⟩ := exists_abs_deriv_riemannKernelReal_le_exp_eight
  have h₀' : ∀ u, |riemannKernelReal u| ≤ C₀ * Real.exp (-(8 * |u|)) := fun u => by
    rw [abs_of_pos (riemannKernelReal_pos u)]
    exact h₀ u
  have hE := Real.exp_pos (8 * |a|)
  refine ⟨2 * (C₀ + C₁) * Real.exp (8 * |a|), fun y => ?_, fun y => ?_⟩
  · refine (abs_sub_comp_add_le h₀' a y).trans ?_
    have := Real.exp_pos (-(8 * |y|))
    gcongr
    linarith
  · rw [(hasDerivAt_shiftDifference a y).deriv]
    refine (abs_sub_comp_add_le h₁ a y).trans ?_
    have := Real.exp_pos (-(8 * |y|))
    gcongr
    linarith

/-! ### The extra jump term -/

/-- The folded shift generator of `ω = M/Φ` in test coordinates. -/
theorem foldedShiftGenerator_profileGauge (M : ℝ → ℝ) (t x : ℝ) :
    foldedShiftGenerator (fun y => M y / riemannKernelReal y) t x =
      M x * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) -
        riemannKernelReal x * (M (x + t) + M (|x - t|)) := by
  unfold foldedShiftGenerator
  have h0 := (riemannKernelReal_pos x).ne'
  have h1 := (riemannKernelReal_pos (x + t)).ne'
  have h2 := (riemannKernelReal_pos (|x - t|)).ne'
  rw [(riemannKernelReal_abs' (x - t)).symm]
  field_simp
  ring

theorem shiftedGroundState_eq_div (a : ℝ) :
    shiftedGroundState a = fun y => shiftDifference a y / riemannKernelReal y := rfl

/-- The extra jump term of `ω_a` over `Φ(x)`. -/
theorem foldedShiftGenerator_shiftedGroundState_div (a t x : ℝ) :
    foldedShiftGenerator (shiftedGroundState a) t x / riemannKernelReal x =
      shiftDifference a x * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) /
          riemannKernelReal x - (shiftDifference a (x + t) + shiftDifference a (|x - t|)) := by
  rw [shiftedGroundState_eq_div, foldedShiftGenerator_profileGauge, sub_div,
    mul_div_cancel_left₀ _ (riemannKernelReal_pos x).ne']

/-- The extra jump term of `ω_a` on the scale `Φ(x) e^{x/2}` of the folded source. -/
def extraJumpRatio (a ℓ x : ℝ) : ℝ :=
  foldedShiftGenerator (shiftedGroundState a) ℓ x / (riemannKernelReal x * Real.exp (x / 2))

theorem extraJumpRatio_eq (a ℓ x : ℝ) :
    extraJumpRatio a ℓ x =
      foldedShiftGenerator (shiftedGroundState a) ℓ x / riemannKernelReal x * Real.exp (-(x / 2)) := by
  unfold extraJumpRatio
  rw [Real.exp_neg, div_mul_eq_div_div, div_eq_mul_inv _ (Real.exp _)]

/-! ### The kernel product `Φ(x−a) Φ(x−ℓ) / Φ(x)` -/

theorem exp_two_mul_sub (x a : ℝ) :
    Real.exp (2 * (x - a)) = Real.exp (2 * x) * Real.exp (-(2 * a)) := by
  rw [← Real.exp_add]; congr 1; ring

/-- Lower bound: `Φ(x−a)Φ(x−ℓ)/Φ(x) ≥ exp(πe^{2x}(1 − e^{−2a} − e^{−2ℓ}) − 5ℓ)`. -/
theorem exp_le_kernelProduct_div {a ℓ x : ℝ} (hℓ : 0 ≤ ℓ) (hxa : 0 ≤ x - a)
    (hxℓ : Real.log 3 / 2 ≤ x - ℓ) :
    Real.exp (Real.pi * Real.exp (2 * x) * (1 - Real.exp (-(2 * a)) - Real.exp (-(2 * ℓ))) -
        5 * ℓ) ≤
      riemannKernelReal (x - a) * riemannKernelReal (x - ℓ) / riemannKernelReal x := by
  have hA := exp_neg_pi_exp_le_riemannKernelReal hxa
  have hS := riemannKernelReal_le_sharp hxℓ (by linarith : x - ℓ ≤ x)
  rw [show x - (x - ℓ) = ℓ by ring, exp_two_mul_sub] at hS
  rw [exp_two_mul_sub] at hA
  rw [le_div_iff₀ (riemannKernelReal_pos x)]
  have hL := (riemannKernelReal_pos (x - ℓ)).le
  calc Real.exp (Real.pi * Real.exp (2 * x) * (1 - Real.exp (-(2 * a)) - Real.exp (-(2 * ℓ))) -
        5 * ℓ) * riemannKernelReal x
      ≤ Real.exp (Real.pi * Real.exp (2 * x) * (1 - Real.exp (-(2 * a)) - Real.exp (-(2 * ℓ))) -
        5 * ℓ) * (riemannKernelReal (x - ℓ) * Real.exp (-(Real.pi * (Real.exp (2 * x) -
          Real.exp (2 * x) * Real.exp (-(2 * ℓ)))) + 5 * ℓ)) :=
        mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
    _ = riemannKernelReal (x - ℓ) * Real.exp (Real.pi * Real.exp (2 * x) *
        (1 - Real.exp (-(2 * a)) - Real.exp (-(2 * ℓ))) - 5 * ℓ + (-(Real.pi * (Real.exp (2 * x) -
          Real.exp (2 * x) * Real.exp (-(2 * ℓ)))) + 5 * ℓ)) := by rw [mul_left_comm, ← Real.exp_add]
    _ = riemannKernelReal (x - ℓ) *
        Real.exp (-Real.pi * (Real.exp (2 * x) * Real.exp (-(2 * a)))) := by congr 2; ring
    _ ≤ riemannKernelReal (x - ℓ) * riemannKernelReal (x - a) :=
        mul_le_mul_of_nonneg_left hA hL
    _ = _ := mul_comm _ _

/-- Upper bound: `Φ(x−a)Φ(x−ℓ)/Φ(x) ≤ Φ(0)² e^{6π} exp(−πe^{2x}(e^{−2a} + e^{−2ℓ} − 1) + 10x)`. -/
theorem kernelProduct_div_le {a ℓ x : ℝ} (ha : 0 ≤ a) (hℓ : 0 ≤ ℓ)
    (hxa : Real.log 3 / 2 ≤ x - a) (hxℓ : Real.log 3 / 2 ≤ x - ℓ) :
    riemannKernelReal (x - a) * riemannKernelReal (x - ℓ) / riemannKernelReal x ≤
      riemannKernelReal 0 ^ 2 * Real.exp (6 * Real.pi) *
        Real.exp (-(Real.pi * Real.exp (2 * x) *
          (Real.exp (-(2 * a)) + Real.exp (-(2 * ℓ)) - 1)) + 10 * x) := by
  have hc : 0 < Real.log 3 / 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 3); positivity
  have h3 : Real.exp (2 * (Real.log 3 / 2)) = 3 := by
    rw [show 2 * (Real.log 3 / 2) = Real.log 3 by ring, Real.exp_log (by norm_num)]
  have hΦc := riemannKernelReal_le_zero_point (Real.log 3 / 2)
  have hΦ0 := (riemannKernelReal_pos 0).le
  -- each translate is controlled from the fixed point `½ log 3`
  have hT : ∀ b, 0 ≤ b → Real.log 3 / 2 ≤ x - b → riemannKernelReal (x - b) ≤
      riemannKernelReal 0 * Real.exp (3 * Real.pi -
        Real.pi * (Real.exp (2 * x) * Real.exp (-(2 * b))) + 5 * x) := fun b hb hxb => by
    have h := riemannKernelReal_le_sharp le_rfl hxb
    rw [h3, exp_two_mul_sub] at h
    refine h.trans (mul_le_mul hΦc (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hΦ0)
    nlinarith [Real.pi_pos, hc, hb]
  have hX := exp_neg_pi_exp_le_riemannKernelReal (show 0 ≤ x by linarith)
  rw [div_le_iff₀ (riemannKernelReal_pos x)]
  calc riemannKernelReal (x - a) * riemannKernelReal (x - ℓ)
      ≤ (riemannKernelReal 0 * Real.exp (3 * Real.pi -
          Real.pi * (Real.exp (2 * x) * Real.exp (-(2 * a))) + 5 * x)) *
        (riemannKernelReal 0 * Real.exp (3 * Real.pi -
          Real.pi * (Real.exp (2 * x) * Real.exp (-(2 * ℓ))) + 5 * x)) :=
        mul_le_mul (hT a ha hxa) (hT ℓ hℓ hxℓ) (riemannKernelReal_pos _).le
          (mul_nonneg hΦ0 (Real.exp_pos _).le)
    _ = riemannKernelReal 0 ^ 2 * Real.exp ((3 * Real.pi -
          Real.pi * (Real.exp (2 * x) * Real.exp (-(2 * a))) + 5 * x) + (3 * Real.pi -
          Real.pi * (Real.exp (2 * x) * Real.exp (-(2 * ℓ))) + 5 * x)) := by
        rw [Real.exp_add (3 * Real.pi - Real.pi * (Real.exp (2 * x) * Real.exp (-(2 * a))) + 5 * x)]
        ring
    _ = riemannKernelReal 0 ^ 2 * Real.exp (6 * Real.pi + (-(Real.pi * Real.exp (2 * x) *
          (Real.exp (-(2 * a)) + Real.exp (-(2 * ℓ)) - 1)) + 10 * x) +
          -Real.pi * Real.exp (2 * x)) := by congr 2; ring
    _ = riemannKernelReal 0 ^ 2 * Real.exp (6 * Real.pi) *
        Real.exp (-(Real.pi * Real.exp (2 * x) *
          (Real.exp (-(2 * a)) + Real.exp (-(2 * ℓ)) - 1)) + 10 * x) *
        Real.exp (-Real.pi * Real.exp (2 * x)) := by
        rw [Real.exp_add (6 * Real.pi + (-(Real.pi * Real.exp (2 * x) *
          (Real.exp (-(2 * a)) + Real.exp (-(2 * ℓ)) - 1)) + 10 * x)), Real.exp_add (6 * Real.pi)]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)

/-! ### Growth at infinity -/

/-- `θ e^{2x} − b x − c → ∞` for `θ > 0`. -/
theorem tendsto_mul_exp_two_sub_linear {θ : ℝ} (hθ : 0 < θ) (b c : ℝ) :
    Tendsto (fun x => θ * Real.exp (2 * x) - b * x - c) atTop atTop := by
  have hq : Tendsto (fun x : ℝ => x * (2 * θ * x + -b) + -c) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_atTop₀
      (tendsto_atTop_add_const_right _ _
        (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 * θ by positivity))))
  refine tendsto_atTop_mono' _ ?_ hq
  filter_upwards [eventually_ge_atTop 0] with x hx
  have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * x by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h hθ.le]

/-- **Visible jumps grow doubly exponentially.** If `e^{−2a} + e^{−2ℓ} < 1`, the extra jump term of
`ω_a` tends to `+∞` on the scale of the folded source. -/
theorem tendsto_extraJumpRatio_atTop {a ℓ : ℝ} (ha : 0 ≤ a) (hℓ : 0 ≤ ℓ)
    (hvis : Real.exp (-(2 * a)) + Real.exp (-(2 * ℓ)) < 1) :
    Tendsto (extraJumpRatio a ℓ) atTop atTop := by
  set η := 1 - Real.exp (-(2 * a)) - Real.exp (-(2 * ℓ)) with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hΦ0 := riemannKernelReal_pos 0
  have hg : Tendsto (fun x => Real.exp (Real.pi * η * Real.exp (2 * x) - (1 / 2) * x - 5 * ℓ) +
      -(3 * riemannKernelReal 0)) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (Real.tendsto_exp_atTop.comp (tendsto_mul_exp_two_sub_linear (by positivity) _ _))
  refine tendsto_atTop_mono' _ ?_ hg
  filter_upwards [eventually_ge_atTop (a + ℓ + Real.log 3 / 2)] with x hx
  have hc : 0 < Real.log 3 / 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 3); positivity
  have hx0 : 0 ≤ x := by linarith
  have hP := exp_le_kernelProduct_div (a := a) (ℓ := ℓ) (x := x) hℓ (by linarith) (by linarith)
  have hmx := shiftDifference_nonneg_of_nonneg ha hx0
  have hplus := (riemannKernelReal_pos (x + ℓ)).le
  have hΦx := riemannKernelReal_pos x
  have hb1 := (abs_le.mp (abs_shiftDifference_le a (x + ℓ))).2
  have hb2 := (abs_le.mp (abs_shiftDifference_le a (|x - ℓ|))).2
  -- `m_a(x) Φ(x−ℓ)/Φ(x) ≥ P(x) − Φ(0)`
  have hlead : riemannKernelReal (x - a) * riemannKernelReal (x - ℓ) / riemannKernelReal x -
      riemannKernelReal 0 ≤
      shiftDifference a x * (riemannKernelReal (x + ℓ) + riemannKernelReal (x - ℓ)) /
        riemannKernelReal x := by
    have hxa : riemannKernelReal (x + a) ≤ riemannKernelReal x :=
      riemannKernelReal_antitone_of_nonneg hx0 (by linarith)
    have hxl := riemannKernelReal_le_zero_point (x - ℓ)
    have key : shiftDifference a x * (riemannKernelReal (x + ℓ) + riemannKernelReal (x - ℓ)) /
        riemannKernelReal x - riemannKernelReal (x - a) * riemannKernelReal (x - ℓ) /
          riemannKernelReal x =
        (shiftDifference a x * riemannKernelReal (x + ℓ) -
          riemannKernelReal (x + a) * riemannKernelReal (x - ℓ)) / riemannKernelReal x := by
      rw [div_sub_div_same]; unfold shiftDifference; ring
    have hk : -riemannKernelReal 0 ≤ (shiftDifference a x * riemannKernelReal (x + ℓ) -
        riemannKernelReal (x + a) * riemannKernelReal (x - ℓ)) / riemannKernelReal x := by
      rw [le_div_iff₀ hΦx]
      nlinarith [mul_le_mul_of_nonneg_right hxa (riemannKernelReal_pos (x - ℓ)).le,
        mul_le_mul_of_nonneg_left hxl hΦx.le, mul_nonneg hmx hplus]
    linarith
  have hratio : Real.exp (Real.pi * η * Real.exp (2 * x) - 5 * ℓ) - 3 * riemannKernelReal 0 ≤
      foldedShiftGenerator (shiftedGroundState a) ℓ x / riemannKernelReal x := by
    rw [foldedShiftGenerator_shiftedGroundState_div]
    have e : Real.pi * η * Real.exp (2 * x) - 5 * ℓ = Real.pi * Real.exp (2 * x) *
        (1 - Real.exp (-(2 * a)) - Real.exp (-(2 * ℓ))) - 5 * ℓ := by rw [hη]; ring
    rw [e]
    linarith
  show Real.exp (Real.pi * η * Real.exp (2 * x) - 1 / 2 * x - 5 * ℓ) + -(3 * riemannKernelReal 0) ≤
    extraJumpRatio a ℓ x
  rw [extraJumpRatio_eq]
  have hE := Real.exp_pos (-(x / 2))
  have hE1 : Real.exp (-(x / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsplit : Real.exp (Real.pi * η * Real.exp (2 * x) - 1 / 2 * x - 5 * ℓ) =
      Real.exp (Real.pi * η * Real.exp (2 * x) - 5 * ℓ) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hratio hE.le, mul_le_mul_of_nonneg_left hE1 hΦ0.le]

/-- **Invisible jumps vanish.** If `e^{−2a} + e^{−2ℓ} > 1`, the extra jump term of `ω_a` tends to `0`
on the scale of the folded source. -/
theorem tendsto_extraJumpRatio_zero {a ℓ : ℝ} (ha : 0 ≤ a) (hℓ : 0 ≤ ℓ)
    (hinv : 1 < Real.exp (-(2 * a)) + Real.exp (-(2 * ℓ))) :
    Tendsto (extraJumpRatio a ℓ) atTop (𝓝 0) := by
  set θ := Real.exp (-(2 * a)) + Real.exp (-(2 * ℓ)) - 1 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hΦ0 := riemannKernelReal_pos 0
  set K := riemannKernelReal 0 ^ 2 * Real.exp (6 * Real.pi) with hK
  have hK0 : 0 ≤ K := by positivity
  have hdecay : Tendsto (fun x => Real.exp (-(x / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const two_pos))
  have hP : Tendsto (fun x => K * Real.exp (-(Real.pi * Real.exp (2 * x) * θ) + 10 * x)) atTop
      (𝓝 0) := by
    have h := (tendsto_mul_exp_two_sub_linear (θ := Real.pi * θ) (by positivity) 10 0)
    have h' : Tendsto (fun x => -(Real.pi * Real.exp (2 * x) * θ) + 10 * x) atTop atBot :=
      (tendsto_neg_atTop_atBot.comp h).congr fun x => by simp only [Function.comp_apply]; ring
    have := (Real.tendsto_exp_atBot.comp h').const_mul K
    rw [mul_zero] at this
    exact this
  have hupper : Tendsto (fun x => (riemannKernelReal 0 +
      K * Real.exp (-(Real.pi * Real.exp (2 * x) * θ) + 10 * x)) * Real.exp (-(x / 2))) atTop
      (𝓝 0) := by
    have := (tendsto_const_nhds (x := riemannKernelReal 0)).add hP |>.mul hdecay
    rw [add_zero, mul_zero] at this
    exact this
  have hlower : Tendsto (fun x => -(2 * riemannKernelReal 0) * Real.exp (-(x / 2))) atTop (𝓝 0) := by
    have := hdecay.const_mul (-(2 * riemannKernelReal 0))
    rw [mul_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop ℓ] with x hx
    rw [extraJumpRatio_eq, foldedShiftGenerator_shiftedGroundState_div]
    have hx0 : 0 ≤ x := by linarith
    have hfirst : 0 ≤ shiftDifference a x * (riemannKernelReal (x + ℓ) + riemannKernelReal (x - ℓ)) /
        riemannKernelReal x :=
      div_nonneg (mul_nonneg (shiftDifference_nonneg_of_nonneg ha hx0)
        (add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le))
        (riemannKernelReal_pos x).le
    have hb1 := (abs_le.mp (abs_shiftDifference_le a (x + ℓ))).2
    have hb2 := (abs_le.mp (abs_shiftDifference_le a (|x - ℓ|))).2
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (a + ℓ + Real.log 3 / 2)] with x hx
    have hc : 0 < Real.log 3 / 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 3); positivity
    have hx0 : 0 ≤ x := by linarith
    rw [extraJumpRatio_eq, foldedShiftGenerator_shiftedGroundState_div]
    have hPb := kernelProduct_div_le (x := x) ha hℓ (by linarith) (by linarith)
    rw [← hθ, ← hK] at hPb
    have hΦx := riemannKernelReal_pos x
    have hm1 := shiftDifference_nonneg_of_nonneg ha (show 0 ≤ x + ℓ by linarith)
    have hm2 := shiftDifference_nonneg_of_nonneg ha (abs_nonneg (x - ℓ))
    -- `m_a(x)(Φ(x+ℓ) + Φ(x−ℓ))/Φ(x) ≤ Φ(0) + P(x)`
    have hfirst : shiftDifference a x * (riemannKernelReal (x + ℓ) + riemannKernelReal (x - ℓ)) /
        riemannKernelReal x ≤ riemannKernelReal 0 +
          riemannKernelReal (x - a) * riemannKernelReal (x - ℓ) / riemannKernelReal x := by
      have hxl : riemannKernelReal (x + ℓ) ≤ riemannKernelReal x :=
        riemannKernelReal_antitone_of_nonneg hx0 (by linarith)
      have hm := shiftDifference_nonneg_of_nonneg ha hx0
      have hmk := shiftDifference_le_kernel a x
      have hm0 := (abs_le.mp (abs_shiftDifference_le a x)).2
      rw [div_le_iff₀ hΦx, add_mul, div_mul_cancel₀ _ hΦx.ne']
      nlinarith [mul_le_mul_of_nonneg_left hxl hm, mul_le_mul_of_nonneg_right hmk
        (riemannKernelReal_pos (x - ℓ)).le, mul_le_mul_of_nonneg_right hm0 hΦx.le]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-! ### The three regimes -/

section Regimes

variable {a ℓ δ : ℝ}

/-- The folded source of `ω_a` normalised at infinity tends to `−2 ∫_0^∞ m_a cosh(x/2) < 0`. -/
theorem tendsto_foldedSource_shiftedGroundState_div (a : ℝ) :
    Tendsto (fun x => (foldedGenerator (shiftedGroundState a) x -
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x) /
          (riemannKernelReal x * Real.exp (x / 2))) atTop
      (𝓝 (-(2 * ∫ r in Ioi (0 : ℝ), shiftDifference a r * Real.cosh (r / 2)))) := by
  obtain ⟨C, hdec, hdec'⟩ := exists_shiftDifference_decay_eight a
  exact tendsto_foldedSource_div (contDiff_shiftDifference a) (shiftDifference_zero a) hdec hdec'

theorem coshMoment_shiftDifference_pos (ha : 0 < a) :
    0 < ∫ r in Ioi (0 : ℝ), shiftDifference a r * Real.cosh (r / 2) := by
  obtain ⟨C, hdec, -⟩ := exists_shiftDifference_decay_eight a
  exact coshMoment_pos (continuous_shiftDifference a) hdec
    (fun y hy => shiftDifference_nonneg_of_nonneg ha.le hy) one_pos (shiftDifference_pos ha one_pos)

/-- Combine the source and the extra term on the scale `Φ e^{x/2}`. -/
theorem foldedSource_add_extraJump_div (a ℓ δ x : ℝ) :
    (foldedGenerator (shiftedGroundState a) x + δ * foldedShiftGenerator (shiftedGroundState a) ℓ x -
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x) /
        (riemannKernelReal x * Real.exp (x / 2)) =
      (foldedGenerator (shiftedGroundState a) x -
          riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x) /
          (riemannKernelReal x * Real.exp (x / 2)) + δ * extraJumpRatio a ℓ x := by
  unfold extraJumpRatio
  ring

/-- **Visible extra jumps create supersolutions at infinity.** If `e^{−2a} + e^{−2ℓ} < 1`, then for
every rate `δ > 0` the shifted ground state is a strict supersolution of the folded generator with
one extra jump of length `ℓ` on a neighbourhood of infinity. -/
theorem exists_foldedGenerator_add_extraJump_gt_potential (ha : 0 < a) (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (hvis : Real.exp (-(2 * a)) + Real.exp (-(2 * ℓ)) < 1) :
    ∃ X : ℝ, ∀ x, X ≤ x → riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x <
      foldedGenerator (shiftedGroundState a) x + δ * foldedShiftGenerator (shiftedGroundState a) ℓ x := by
  have hsum := (tendsto_foldedSource_shiftedGroundState_div a).add_atTop
    ((tendsto_extraJumpRatio_atTop ha.le hℓ.le hvis).const_mul_atTop hδ)
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hsum.eventually_gt_atTop 0)
  refine ⟨X, fun x hx => ?_⟩
  have h : 0 < (foldedGenerator (shiftedGroundState a) x -
      riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x) /
        (riemannKernelReal x * Real.exp (x / 2)) + δ * extraJumpRatio a ℓ x := hX x hx
  rw [← foldedSource_add_extraJump_div] at h
  have hD : 0 < riemannKernelReal x * Real.exp (x / 2) :=
    mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)
  linarith [(div_pos_iff_of_pos_right hD).mp h]

/-- **Invisible extra jumps leave the failure at infinity.** If `e^{−2a} + e^{−2ℓ} > 1`, then for
every rate `δ ≥ 0` the shifted ground state is a strict subsolution of the folded generator with one
extra jump of length `ℓ` on a neighbourhood of infinity. -/
theorem exists_foldedGenerator_add_extraJump_lt_potential (ha : 0 < a) (hℓ : 0 ≤ ℓ)
    (hinv : 1 < Real.exp (-(2 * a)) + Real.exp (-(2 * ℓ))) :
    ∃ X : ℝ, ∀ x, X ≤ x →
      foldedGenerator (shiftedGroundState a) x + δ * foldedShiftGenerator (shiftedGroundState a) ℓ x <
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x := by
  have hκ := coshMoment_shiftDifference_pos ha
  have hsum := (tendsto_foldedSource_shiftedGroundState_div a).add
    ((tendsto_extraJumpRatio_zero ha.le hℓ hinv).const_mul δ)
  rw [mul_zero, add_zero] at hsum
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hsum.eventually (gt_mem_nhds (by linarith :
    -(2 * ∫ r in Ioi (0 : ℝ), shiftDifference a r * Real.cosh (r / 2)) < 0)))
  refine ⟨X, fun x hx => ?_⟩
  have h : (foldedGenerator (shiftedGroundState a) x -
      riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x) /
        (riemannKernelReal x * Real.exp (x / 2)) + δ * extraJumpRatio a ℓ x < 0 := hX x hx
  rw [← foldedSource_add_extraJump_div] at h
  have hD : 0 < riemannKernelReal x * Real.exp (x / 2) :=
    mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)
  have := (div_neg_iff.mp h)
  rcases this with ⟨-, h2⟩ | ⟨h1, -⟩
  · linarith
  · linarith

/-- **The origin is rate-blind.** For every extra jump of length `ℓ ≥ 0` at rate `δ ≥ 0`, the shifted
ground state remains a strict subsolution of the perturbed folded generator near the origin. -/
theorem exists_origin_window_foldedGenerator_add_extraJump_lt_potential (ha : 0 < a) (hℓ : 0 ≤ ℓ)
    (hδ : 0 ≤ δ) :
    ∃ ε > 0, ∀ x ∈ Ioo 0 ε,
      foldedGenerator (shiftedGroundState a) x + δ * foldedShiftGenerator (shiftedGroundState a) ℓ x <
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x := by
  obtain ⟨C, hdec, hdec'⟩ := exists_shiftDifference_decay_eight a
  have hJ := jumpMeasureMoment_pos (contDiff_shiftDifference a) (shiftDifference_zero a) hdec'
    (fun y hy => shiftDifference_nonneg_of_nonneg ha.le hy) one_pos (shiftDifference_pos ha one_pos)
  have hsrc := tendsto_foldedSource_div_nhdsGT_zero (contDiff_shiftDifference a)
    (shiftDifference_zero a) hdec hdec'
  -- the extra term over `Φ` is continuous with value `−2 m_a(ℓ)` at the origin
  have hcont : Continuous fun x => shiftDifference a x *
      (riemannKernelReal (x + ℓ) + riemannKernelReal (x - ℓ)) / riemannKernelReal x -
        (shiftDifference a (x + ℓ) + shiftDifference a (|x - ℓ|)) :=
    (((continuous_shiftDifference a).mul
      ((continuous_riemannKernelReal.comp (continuous_id.add continuous_const)).add
        (continuous_riemannKernelReal.comp (continuous_id.sub continuous_const)))).div
      continuous_riemannKernelReal fun x => (riemannKernelReal_pos x).ne').sub
      (((continuous_shiftDifference a).comp (continuous_id.add continuous_const)).add
        ((continuous_shiftDifference a).comp (continuous_id.sub continuous_const).abs))
  have hext : Tendsto (fun x => foldedShiftGenerator (shiftedGroundState a) ℓ x / riemannKernelReal x)
      (𝓝[>] 0) (𝓝 (-(2 * shiftDifference a ℓ))) :=
    ((hcont.tendsto' 0 (-(2 * shiftDifference a ℓ)) (by
      simp only [shiftDifference_zero, zero_mul, zero_div, zero_add, zero_sub, abs_neg,
        abs_of_nonneg hℓ]
      ring)).mono_left nhdsWithin_le_nhds).congr fun x =>
        (foldedShiftGenerator_shiftedGroundState_div a ℓ x).symm
  have hm := shiftDifference_nonneg_of_nonneg ha.le hℓ
  have hsum := hsrc.add (hext.const_mul δ)
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hsum.eventually (gt_mem_nhds
    (by nlinarith : -(2 * jumpMeasureMoment (shiftDifference a)) + δ * -(2 * shiftDifference a ℓ) < 0)))
  refine ⟨ε, hε, fun x hx => ?_⟩
  have h : (foldedGenerator (shiftedGroundState a) x -
      riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x) / riemannKernelReal x +
      δ * (foldedShiftGenerator (shiftedGroundState a) ℓ x / riemannKernelReal x) < 0 := hsub hx
  rw [mul_div_assoc', ← add_div] at h
  have hΦ := riemannKernelReal_pos x
  have := (div_neg_iff.mp h)
  rcases this with ⟨-, h2⟩ | ⟨h1, -⟩
  · linarith
  · linarith

theorem exp_neg_two_mul_log_two : Real.exp (-(2 * Real.log 2)) = 1 / 4 := by
  rw [Real.exp_neg, show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add,
    Real.exp_log two_pos]
  norm_num

/-- **The prime `2`, visible.** If `e^{−2a} < 3/4`, an extra jump of length `log 2` at any rate
`δ > 0` makes `ω_a` a strict folded supersolution at infinity. -/
theorem exists_foldedGenerator_add_extraJump_gt_potential_log_two (ha : 0 < a) (hδ : 0 < δ)
    (hvis : Real.exp (-(2 * a)) < 3 / 4) :
    ∃ X : ℝ, ∀ x, X ≤ x → riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x <
      foldedGenerator (shiftedGroundState a) x +
        δ * foldedShiftGenerator (shiftedGroundState a) (Real.log 2) x :=
  exists_foldedGenerator_add_extraJump_gt_potential ha (Real.log_pos one_lt_two) hδ
    (by rw [exp_neg_two_mul_log_two]; linarith)

/-- **The prime `2`, invisible.** If `e^{−2a} > 3/4`, no extra rate at `log 2` repairs the failure
of `ω_a` at infinity. -/
theorem exists_foldedGenerator_add_extraJump_lt_potential_log_two (ha : 0 < a)
    (hinv : 3 / 4 < Real.exp (-(2 * a))) :
    ∃ X : ℝ, ∀ x, X ≤ x → foldedGenerator (shiftedGroundState a) x +
        δ * foldedShiftGenerator (shiftedGroundState a) (Real.log 2) x <
      riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x :=
  exists_foldedGenerator_add_extraJump_lt_potential ha (Real.log_pos one_lt_two).le
    (by rw [exp_neg_two_mul_log_two]; linarith)

end Regimes

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
