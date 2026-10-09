import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Two mean-zero sources under the Cauchy difference kernel

Let `I = (α, α')` lie to the left of `J = (β, β')`, so `α' ≤ β`, and let `f ∈ L²(I)`, `g ∈ L²(J)`
both have mean zero. Write `w_I(y) = 1/(y − α)` for the distance from `y ∈ J` to the far end of
`I`, and `w_J(x) = 1/(β' − x)` for the distance from `x ∈ I` to the far end of `J`.

**Theorem** (`lintegral_twoInterval_ge`).
`∫_I ∫_J (f(x) − g(y))²/(y − x) dy dx ≥ ‖f‖² ∫_J w_I + ‖g‖² ∫_I w_J`.

For two intervals of one common length `ε` at distance `Dε` apart, both one-sided charges equal
`log((D + 1)/D)` (`lintegral_twoInterval_equalLength_ge`).

A single mean-zero source `f` on `I` facing a free value `v` at `y ∉ I` already costs
`∫_I (f − v)²/|x − y| ≥ ‖f‖² w_I(y)`, because `∫_I (f − v)² = ‖f‖² + |I| v²`. The theorem says that
two sources facing each other still pay both one-sided charges in full: the cross term is absorbed.

**Proof.** Write `1/(y − x) = ∫_0^∞ e^{−u(y−x)} du`, so that each slice is the rank-one kernel
`φ_u(x) ψ_u(y)` with `φ_u(x) = e^{u(x−α)} ≥ 1` on `I` and `ψ_u(y) = e^{−u(y−α)} ≥ m_u = ψ_u(β')` on
`J`. For one slice, with `κ = ∫_J ψ_u` and `Φ = ∫_I φ_u`, the mean-zero conditions give:
* `F = ∫ f φ = ∫ f (φ − 1)` and `G = ∫ g ψ = ∫ g (ψ − m)`;
* weighted Cauchy–Schwarz gives `F² ≤ pA` and `G² ≤ qB`, where `A = ∫ f²(φ − 1)`,
  `B = ∫ g²(ψ − m)`, `p = Φ − |I|` and `q = κ − m|J|`;
* `pq ≤ κΦ`.

So `2FG ≤ κA + ΦB`, which is the slice inequality
`∫∫ (f − g)² φψ ≥ κ‖f‖² + mΦ‖g‖²` (`rankOne_twoInterval_le`). Integrating in `u` (Tonelli) turns
`κ` into `∫_J w_I` and `mΦ = ∫_I e^{−u(β' − x)} dx` into `∫_I w_J`.
-/

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.CauchyDifference

/-! ## Weighted Cauchy–Schwarz and integrability -/

/-- `(∫ h w)² ≤ (∫ w)(∫ h² w)` for a nonnegative weight `w`. -/
theorem sq_setIntegral_mul_le {s : Set ℝ} (hs : MeasurableSet s) {w h : ℝ → ℝ}
    (hw : ∀ x ∈ s, 0 ≤ w x) (hwi : IntegrableOn w s)
    (hhw : IntegrableOn (fun x => h x * w x) s)
    (hh2w : IntegrableOn (fun x => h x ^ 2 * w x) s) :
    (∫ x in s, h x * w x) ^ 2 ≤ (∫ x in s, w x) * ∫ x in s, h x ^ 2 * w x := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x in s, w x) * (t * t) + (-2 * ∫ x in s, h x * w x) * t +
      ∫ x in s, h x ^ 2 * w x := by
    intro t
    have hnn : 0 ≤ ∫ x in s, w x * (h x - t) ^ 2 :=
      setIntegral_nonneg hs fun x hx => mul_nonneg (hw x hx) (sq_nonneg _)
    have hfun : (fun x => w x * (h x - t) ^ 2) =
        fun x => (h x ^ 2 * w x - (2 * t) * (h x * w x)) + t ^ 2 * w x := by
      funext x; ring
    rw [hfun, integral_add, integral_sub, integral_const_mul, integral_const_mul] at hnn
    · nlinarith
    all_goals first
      | exact hh2w | exact hhw.const_mul _ | exact hwi.const_mul _
      | exact hh2w.sub (hhw.const_mul _)
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith

theorem integrableOn_Ioo_of_continuous {a b : ℝ} {c : ℝ → ℝ} (hc : Continuous c) :
    IntegrableOn c (Ioo a b) :=
  hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem integrableOn_Ioo_mul_continuous {a b : ℝ} {h c : ℝ → ℝ} (hh : IntegrableOn h (Ioo a b))
    (hc : Continuous c) : IntegrableOn (fun x => h x * c x) (Ioo a b) :=
  hh.mul_continuousOn_of_subset hc.continuousOn measurableSet_Ioo isCompact_Icc
    Ioo_subset_Icc_self

/-! ## One exponential slice -/

/-- **The slice inequality.** For mean-zero `f ∈ L²(α, α')`, `g ∈ L²(β, β')` and `u ≥ 0`,
`∫_I ∫_J (f(x) − g(y))² e^{−u(y−x)} ≥ (∫_J e^{−u(y−α)}) ‖f‖² + (∫_I e^{−u(β'−x)}) ‖g‖²`. -/
theorem rankOne_twoInterval_le {α α' β β' u : ℝ} (hu : 0 ≤ u) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo α α')))
    (hg : MemLp g 2 (volume.restrict (Ioo β β')))
    (hf0 : ∫ x in Ioo α α', f x = 0) (hg0 : ∫ y in Ioo β β', g y = 0) :
    (∫ y in Ioo β β', exp (-(u * (y - α)))) * (∫ x in Ioo α α', f x ^ 2) +
        (∫ x in Ioo α α', exp (-(u * (β' - x)))) * (∫ y in Ioo β β', g y ^ 2) ≤
      ∫ x in Ioo α α', ∫ y in Ioo β β', (f x - g y) ^ 2 * exp (-(u * (y - x))) := by
  set φ : ℝ → ℝ := fun x => exp (u * (x - α)) with hφ
  set ψ : ℝ → ℝ := fun y => exp (-(u * (y - α))) with hψ
  set m : ℝ := exp (-(u * (β' - α))) with hm
  have hφc : Continuous φ := by fun_prop
  have hψc : Continuous ψ := by fun_prop
  have hfi : IntegrableOn f (Ioo α α') := hf.integrable one_le_two
  have hf2i : IntegrableOn (fun x => f x ^ 2) (Ioo α α') := hf.integrable_sq
  have hgi : IntegrableOn g (Ioo β β') := hg.integrable one_le_two
  have hg2i : IntegrableOn (fun y => g y ^ 2) (Ioo β β') := hg.integrable_sq
  have hφi : IntegrableOn φ (Ioo α α') := integrableOn_Ioo_of_continuous hφc
  have hψi : IntegrableOn ψ (Ioo β β') := integrableOn_Ioo_of_continuous hψc
  have h1I : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo α α') :=
    integrableOn_Ioo_of_continuous continuous_const
  have h1J : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo β β') :=
    integrableOn_Ioo_of_continuous continuous_const
  have hmJ : IntegrableOn (fun _ : ℝ => exp (-(u * (β' - α)))) (Ioo β β') :=
    integrableOn_Ioo_of_continuous continuous_const
  have hfφ := integrableOn_Ioo_mul_continuous hfi hφc
  have hf2φ := integrableOn_Ioo_mul_continuous hf2i hφc
  have hgψ := integrableOn_Ioo_mul_continuous hgi hψc
  have hg2ψ := integrableOn_Ioo_mul_continuous hg2i hψc
  set κ := ∫ y in Ioo β β', ψ y with hκ
  set Φ := ∫ x in Ioo α α', φ x with hΦ
  set LI := ∫ x in Ioo α α', (1 : ℝ) with hLI
  set LJ := ∫ y in Ioo β β', (1 : ℝ) with hLJ
  set Nf := ∫ x in Ioo α α', f x ^ 2 with hNf
  set Ng := ∫ y in Ioo β β', g y ^ 2 with hNg
  set Pf := ∫ x in Ioo α α', f x ^ 2 * φ x with hPf
  set Pg := ∫ y in Ioo β β', g y ^ 2 * ψ y with hPg
  set F := ∫ x in Ioo α α', f x * φ x with hF
  set G := ∫ y in Ioo β β', g y * ψ y with hG
  -- the double integral factorizes slice by slice
  have hkernel : ∀ x y, exp (-(u * (y - x))) = φ x * ψ y := by
    intro x y
    simp only [hφ, hψ]
    rw [← Real.exp_add]
    ring_nf
  have hinner : ∀ x, ∫ y in Ioo β β', (f x - g y) ^ 2 * exp (-(u * (y - x))) =
      f x ^ 2 * φ x * κ - 2 * (f x * φ x) * G + φ x * Pg := by
    intro x
    have hfun : (fun y => (f x - g y) ^ 2 * exp (-(u * (y - x)))) =
        fun y => ((f x ^ 2 * φ x) * ψ y - (2 * (f x * φ x)) * (g y * ψ y)) +
          φ x * (g y ^ 2 * ψ y) := by
      funext y
      rw [hkernel]
      ring
    rw [hfun, integral_add, integral_sub, integral_const_mul, integral_const_mul,
      integral_const_mul]
    all_goals first
      | exact hψi.const_mul _ | exact hgψ.const_mul _ | exact hg2ψ.const_mul _
      | exact (hψi.const_mul _).sub (hgψ.const_mul _)
  have hdouble : ∫ x in Ioo α α', ∫ y in Ioo β β', (f x - g y) ^ 2 * exp (-(u * (y - x))) =
      κ * Pf - 2 * G * F + Pg * Φ := by
    rw [show (fun x => ∫ y in Ioo β β', (f x - g y) ^ 2 * exp (-(u * (y - x)))) =
      fun x => (κ * (f x ^ 2 * φ x) - (2 * G) * (f x * φ x)) + Pg * φ x from by
        funext x
        rw [hinner]
        ring]
    have i1 : IntegrableOn (fun x => κ * (f x ^ 2 * φ x)) (Ioo α α') := hf2φ.const_mul κ
    have i2 : IntegrableOn (fun x => 2 * G * (f x * φ x)) (Ioo α α') := hfφ.const_mul (2 * G)
    have i3 : IntegrableOn (fun x => Pg * φ x) (Ioo α α') := hφi.const_mul Pg
    have i12 : IntegrableOn (fun x => κ * (f x ^ 2 * φ x) - 2 * G * (f x * φ x)) (Ioo α α') :=
      i1.sub i2
    rw [integral_add i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul]
  -- the `g`-charge is `m Φ`
  have hκg : ∫ x in Ioo α α', exp (-(u * (β' - x))) = m * Φ := by
    rw [hΦ, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    simp only [hm, hφ]
    rw [← Real.exp_add]
    ring_nf
  rw [hdouble, hκg]
  -- the weights
  have hφ1 : ∀ x ∈ Ioo α α', 1 ≤ φ x := fun x hx =>
    Real.one_le_exp (mul_nonneg hu (by linarith [hx.1]))
  have hψm : ∀ y ∈ Ioo β β', m ≤ ψ y := fun y hy =>
    Real.exp_le_exp.mpr (by nlinarith [hy.2])
  have hm0 : 0 ≤ m := (Real.exp_pos _).le
  have hLI0 : 0 ≤ LI := setIntegral_nonneg measurableSet_Ioo fun _ _ => zero_le_one
  have hLJ0 : 0 ≤ LJ := setIntegral_nonneg measurableSet_Ioo fun _ _ => zero_le_one
  have hκ0 : 0 ≤ κ := setIntegral_nonneg measurableSet_Ioo fun y _ => (Real.exp_pos _).le
  -- `A = Pf − Nf ≥ 0`, `p = Φ − LI ≥ 0`
  have hA : Pf - Nf = ∫ x in Ioo α α', f x ^ 2 * (φ x - 1) := by
    rw [hPf, hNf, ← integral_sub hf2φ hf2i]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    ring
  have hA0 : 0 ≤ Pf - Nf := by
    rw [hA]
    exact setIntegral_nonneg measurableSet_Ioo fun x hx =>
      mul_nonneg (sq_nonneg _) (by linarith [hφ1 x hx])
  have hp : Φ - LI = ∫ x in Ioo α α', (φ x - 1) := by
    rw [hΦ, hLI, ← integral_sub hφi h1I]
  have hp0 : 0 ≤ Φ - LI := by
    rw [hp]
    exact setIntegral_nonneg measurableSet_Ioo fun x hx => by linarith [hφ1 x hx]
  -- `B = Pg − m Ng ≥ 0`, `q = κ − m LJ ≥ 0`
  have hB : Pg - m * Ng = ∫ y in Ioo β β', g y ^ 2 * (ψ y - m) := by
    rw [hPg, hNg, ← integral_const_mul, ← integral_sub hg2ψ (hg2i.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioo fun y _ => ?_
    ring
  have hB0 : 0 ≤ Pg - m * Ng := by
    rw [hB]
    exact setIntegral_nonneg measurableSet_Ioo fun y hy =>
      mul_nonneg (sq_nonneg _) (by linarith [hψm y hy])
  have hq : κ - m * LJ = ∫ y in Ioo β β', (ψ y - m) := by
    rw [hκ, hLJ, ← integral_const_mul, ← integral_sub hψi (h1J.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioo fun y _ => ?_
    ring
  have hq0 : 0 ≤ κ - m * LJ := by
    rw [hq]
    exact setIntegral_nonneg measurableSet_Ioo fun y hy => by linarith [hψm y hy]
  -- Cauchy–Schwarz on the mean-zero parts
  have hFeq : F = ∫ x in Ioo α α', f x * (φ x - 1) := by
    have : ∫ x in Ioo α α', f x * (φ x - 1) = F - ∫ x in Ioo α α', f x := by
      rw [hF, ← integral_sub hfφ hfi]
      refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
      ring
    rw [this, hf0, sub_zero]
  have hGeq : G = ∫ y in Ioo β β', g y * (ψ y - m) := by
    have : ∫ y in Ioo β β', g y * (ψ y - m) = G - m * ∫ y in Ioo β β', g y := by
      rw [hG, ← integral_const_mul, ← integral_sub hgψ (hgi.const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioo fun y _ => ?_
      ring
    rw [this, hg0, mul_zero, sub_zero]
  have hFcs : F ^ 2 ≤ (Φ - LI) * (Pf - Nf) := by
    rw [hFeq, hp, hA]
    refine sq_setIntegral_mul_le measurableSet_Ioo (fun x hx => by linarith [hφ1 x hx])
      (hφi.sub h1I) ?_ ?_
    · exact (hfφ.sub hfi).congr_fun (fun x _ => by simp only [Pi.sub_apply]; ring)
        measurableSet_Ioo
    · exact (hf2φ.sub hf2i).congr_fun (fun x _ => by simp only [Pi.sub_apply]; ring)
        measurableSet_Ioo
  have hGcs : G ^ 2 ≤ (κ - m * LJ) * (Pg - m * Ng) := by
    rw [hGeq, hq, hB]
    refine sq_setIntegral_mul_le measurableSet_Ioo (fun y hy => by linarith [hψm y hy])
      (hψi.sub hmJ) ?_ ?_
    · exact (hgψ.sub (hgi.const_mul m)).congr_fun (fun y _ => by simp only [Pi.sub_apply]; ring)
        measurableSet_Ioo
    · exact (hg2ψ.sub (hg2i.const_mul m)).congr_fun
        (fun y _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioo
  -- `pq ≤ κΦ`
  have hpq : (Φ - LI) * (κ - m * LJ) ≤ κ * Φ := by
    have hΦLI : LI ≤ Φ := by linarith
    have e : κ * Φ - (Φ - LI) * (κ - m * LJ) = LI * κ + m * LJ * (Φ - LI) := by ring
    linarith [mul_nonneg hLI0 hκ0, mul_nonneg (mul_nonneg hm0 hLJ0) (sub_nonneg.mpr hΦLI)]
  -- `2FG ≤ κA + ΦB`
  set A := Pf - Nf
  set B := Pg - m * Ng
  have hΦ0 : 0 ≤ Φ := by linarith
  have h1 : (F * G) ^ 2 ≤ ((Φ - LI) * A) * ((κ - m * LJ) * B) := by
    rw [mul_pow]
    exact mul_le_mul hFcs hGcs (sq_nonneg _) (mul_nonneg hp0 hA0)
  have h2 : ((Φ - LI) * A) * ((κ - m * LJ) * B) ≤ (κ * Φ) * (A * B) := by
    have := mul_le_mul_of_nonneg_right hpq (mul_nonneg hA0 hB0)
    linarith [this]
  have h3 : 4 * ((κ * Φ) * (A * B)) ≤ (κ * A + Φ * B) ^ 2 := by
    have e : (κ * A + Φ * B) ^ 2 - 4 * ((κ * Φ) * (A * B)) = (κ * A - Φ * B) ^ 2 := by ring
    linarith [sq_nonneg (κ * A - Φ * B)]
  have h4 : (2 * (F * G)) ^ 2 ≤ (κ * A + Φ * B) ^ 2 := by
    have e : (2 * (F * G)) ^ 2 = 4 * (F * G) ^ 2 := by ring
    linarith
  have h5 := (abs_le_of_sq_le_sq' h4 (add_nonneg (mul_nonneg hκ0 hA0) (mul_nonneg hΦ0 hB0))).2
  have hA' : Pf = Nf + A := by simp only [A]; ring
  have hB' : Pg = m * Ng + B := by simp only [B]; ring
  rw [hA', hB']
  have e : κ * (Nf + A) - 2 * G * F + (m * Ng + B) * Φ - (κ * Nf + m * Φ * Ng) =
      κ * A + Φ * B - 2 * (F * G) := by ring
  linarith

/-! ## Integrating the slices -/

/-- For `ψ ≥ 0`, `ofReal (∫_s ψ) ≤ ∫⁻_s ofReal ψ`, with no integrability hypothesis. -/
theorem ofReal_setIntegral_le_setLIntegral {s : Set ℝ} {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x) :
    ENNReal.ofReal (∫ x in s, ψ x) ≤ ∫⁻ x in s, ENNReal.ofReal (ψ x) := by
  by_cases hi : IntegrableOn ψ s
  · rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hψ)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

/-- `∫_0^∞ e^{−uc} du = 1/c` for `c > 0`. -/
theorem setLIntegral_exp_neg_mul_Ioi {c : ℝ} (hc : 0 < c) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (exp (-(u * c))) = ENNReal.ofReal (1 / c) := by
  simp_rw [show ∀ u : ℝ, -(u * c) = -c * u from fun u => by ring]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi (by linarith) 0)
    (ae_of_all _ fun u => (exp_pos _).le), integral_exp_mul_Ioi (by linarith) 0]
  congr 1
  rw [mul_zero, exp_zero]
  field_simp

/-- `∫⁻_s 1/(y − a) dy = ∫_0^∞ ∫_s e^{−u(y−a)} dy du` when `s` lies to the right of `a`. -/
theorem setLIntegral_inv_sub_eq {a b c : ℝ} (hab : a ≤ b) :
    ∫⁻ y in Ioo b c, ENNReal.ofReal (1 / (y - a)) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (∫ y in Ioo b c, exp (-(u * (y - a)))) := by
  have h1 : ∫⁻ y in Ioo b c, ENNReal.ofReal (1 / (y - a)) =
      ∫⁻ y in Ioo b c, ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (exp (-(u * (y - a)))) :=
    setLIntegral_congr_fun measurableSet_Ioo fun y hy =>
      (setLIntegral_exp_neg_mul_Ioi (by linarith [hy.1])).symm
  rw [h1, lintegral_lintegral_swap (by fun_prop)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioo_of_continuous (by fun_prop)) (ae_of_all _ fun y => (exp_pos _).le)]

/-- `∫⁻_s 1/(a − x) dx = ∫_0^∞ ∫_s e^{−u(a−x)} dx du` when `s` lies to the left of `a`. -/
theorem setLIntegral_inv_sub'_eq {a b c : ℝ} (hca : c ≤ a) :
    ∫⁻ x in Ioo b c, ENNReal.ofReal (1 / (a - x)) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (∫ x in Ioo b c, exp (-(u * (a - x)))) := by
  have h1 : ∫⁻ x in Ioo b c, ENNReal.ofReal (1 / (a - x)) =
      ∫⁻ x in Ioo b c, ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (exp (-(u * (a - x)))) :=
    setLIntegral_congr_fun measurableSet_Ioo fun x hx =>
      (setLIntegral_exp_neg_mul_Ioi (by linarith [hx.2])).symm
  rw [h1, lintegral_lintegral_swap (by fun_prop)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioo_of_continuous (by fun_prop)) (ae_of_all _ fun x => (exp_pos _).le)]

/-- **Two mean-zero sources.** For `I = (α, α')` to the left of `J = (β, β')` and mean-zero
`f ∈ L²(I)`, `g ∈ L²(J)`:
`∫_I ∫_J (f(x) − g(y))²/(y − x) ≥ ‖f‖² ∫_J dy/(y − α) + ‖g‖² ∫_I dx/(β' − x)`. -/
theorem lintegral_twoInterval_ge {α α' β β' : ℝ} (hα : α ≤ α') (hαβ : α' ≤ β) (hβ : β ≤ β')
    {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 (volume.restrict (Ioo α α')))
    (hg : MemLp g 2 (volume.restrict (Ioo β β')))
    (hf0 : ∫ x in Ioo α α', f x = 0) (hg0 : ∫ y in Ioo β β', g y = 0) :
    ENNReal.ofReal (∫ x in Ioo α α', f x ^ 2) *
          (∫⁻ y in Ioo β β', ENNReal.ofReal (1 / (y - α))) +
        ENNReal.ofReal (∫ y in Ioo β β', g y ^ 2) *
          (∫⁻ x in Ioo α α', ENNReal.ofReal (1 / (β' - x))) ≤
      ∫⁻ x in Ioo α α', ∫⁻ y in Ioo β β', ENNReal.ofReal ((f x - g y) ^ 2 / (y - x)) := by
  set H : ℝ → ℝ → ℝ → ℝ≥0∞ := fun x y u =>
    ENNReal.ofReal ((f x - g y) ^ 2 * exp (-(u * (y - x)))) with hH
  have hHm : Measurable fun q : (ℝ × ℝ) × ℝ => H q.1.1 q.2 q.1.2 := by
    simp only [hH]
    fun_prop
  -- Laplace representation of the kernel
  have hlap : ∀ x ∈ Ioo α α', ∀ y ∈ Ioo β β',
      ENNReal.ofReal ((f x - g y) ^ 2 / (y - x)) = ∫⁻ u in Ioi (0 : ℝ), H x y u := by
    intro x hx y hy
    have hyx : 0 < y - x := by linarith [hx.2, hy.1]
    simp only [hH]
    simp_rw [ENNReal.ofReal_mul (sq_nonneg (f x - g y))]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_exp_neg_mul_Ioi hyx,
      ← ENNReal.ofReal_mul (sq_nonneg _), div_eq_mul_one_div]
  have hE : ∫⁻ x in Ioo α α', ∫⁻ y in Ioo β β', ENNReal.ofReal ((f x - g y) ^ 2 / (y - x)) =
      ∫⁻ u in Ioi (0 : ℝ), ∫⁻ x in Ioo α α', ∫⁻ y in Ioo β β', H x y u := by
    have h1 : ∫⁻ x in Ioo α α', ∫⁻ y in Ioo β β', ENNReal.ofReal ((f x - g y) ^ 2 / (y - x)) =
        ∫⁻ x in Ioo α α', ∫⁻ u in Ioi (0 : ℝ), ∫⁻ y in Ioo β β', H x y u := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      rw [setLIntegral_congr_fun measurableSet_Ioo fun y hy => hlap x hx y hy]
      exact lintegral_lintegral_swap
        (hHm.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aemeasurable
    rw [h1]
    exact lintegral_lintegral_swap (hHm.lintegral_prod_right'.aemeasurable)
  -- one slice at a time
  set Nf := ∫ x in Ioo α α', f x ^ 2 with hNf
  set Ng := ∫ y in Ioo β β', g y ^ 2 with hNg
  set κf : ℝ → ℝ := fun u => ∫ y in Ioo β β', exp (-(u * (y - α))) with hκf
  set κg : ℝ → ℝ := fun u => ∫ x in Ioo α α', exp (-(u * (β' - x))) with hκg
  have hslice : ∀ u ∈ Ioi (0 : ℝ), ENNReal.ofReal (κf u * Nf + κg u * Ng) ≤
      ∫⁻ x in Ioo α α', ∫⁻ y in Ioo β β', H x y u := by
    intro u hu
    refine (ENNReal.ofReal_le_ofReal
      (rankOne_twoInterval_le (le_of_lt hu) hf hg hf0 hg0)).trans ?_
    refine (ofReal_setIntegral_le_setLIntegral fun x => integral_nonneg fun y =>
      mul_nonneg (sq_nonneg _) (exp_pos _).le).trans ?_
    exact lintegral_mono fun x => ofReal_setIntegral_le_setLIntegral fun y =>
      mul_nonneg (sq_nonneg _) (exp_pos _).le
  have hNf0 : 0 ≤ Nf := integral_nonneg fun x => sq_nonneg _
  have hNg0 : 0 ≤ Ng := integral_nonneg fun y => sq_nonneg _
  have hκf0 : ∀ u, 0 ≤ κf u := fun u => integral_nonneg fun y => (exp_pos _).le
  have hκg0 : ∀ u, 0 ≤ κg u := fun u => integral_nonneg fun x => (exp_pos _).le
  have hWf : ∫⁻ y in Ioo β β', ENNReal.ofReal (1 / (y - α)) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (κf u) :=
    setLIntegral_inv_sub_eq (show α ≤ β by linarith)
  have hWg : ∫⁻ x in Ioo α α', ENNReal.ofReal (1 / (β' - x)) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (κg u) :=
    setLIntegral_inv_sub'_eq (by linarith)
  rw [hE, hWf, hWg, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (le_lintegral_add _ _).trans ?_
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall fun u hu => ?_))
  refine le_trans (le_of_eq ?_) (hslice u hu)
  rw [ENNReal.ofReal_add (mul_nonneg (hκf0 u) hNf0) (mul_nonneg (hκg0 u) hNg0),
    ENNReal.ofReal_mul (hκf0 u), ENNReal.ofReal_mul (hκg0 u), mul_comm (ENNReal.ofReal Nf),
    mul_comm (ENNReal.ofReal Ng)]

/-! ## Explicit charges -/

/-- `∫_b^c dy/(d − y) = log((d − b)/(d − c))` for `b ≤ c < d`. -/
theorem setLIntegral_one_div_sub_left {b c d : ℝ} (hbc : b ≤ c) (hcd : c < d) :
    ∫⁻ y in Ioo b c, ENNReal.ofReal (1 / (d - y)) =
      ENNReal.ofReal (Real.log ((d - b) / (d - c))) := by
  have hcont : ContinuousOn (fun y : ℝ => 1 / (d - y)) (Icc b c) :=
    continuousOn_const.div (by fun_prop) fun y hy => (by linarith [hy.2] : (0 : ℝ) < d - y).ne'
  have hsub := intervalIntegral.integral_comp_sub_left (fun t : ℝ => 1 / t) (a := b) (b := c) d
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun y hy =>
        (one_div_pos.mpr (by linarith [hy.2] : (0 : ℝ) < d - y)).le)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hbc, hsub,
    integral_one_div_of_pos (by linarith) (by linarith)]

/-- `∫_b^c dy/(y − d) = log((c − d)/(b − d))` for `d < b ≤ c`. -/
theorem setLIntegral_one_div_sub_right {b c d : ℝ} (hdb : d < b) (hbc : b ≤ c) :
    ∫⁻ y in Ioo b c, ENNReal.ofReal (1 / (y - d)) =
      ENNReal.ofReal (Real.log ((c - d) / (b - d))) := by
  have hcont : ContinuousOn (fun y : ℝ => 1 / (y - d)) (Icc b c) :=
    continuousOn_const.div (by fun_prop) fun y hy => (by linarith [hy.1] : (0 : ℝ) < y - d).ne'
  have hsub := intervalIntegral.integral_comp_sub_right (fun t : ℝ => 1 / t) (a := b) (b := c) d
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun y hy =>
        (one_div_pos.mpr (by linarith [hy.1] : (0 : ℝ) < y - d)).le)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hbc, hsub,
    integral_one_div_of_pos (by linarith) (by linarith)]

/-- **Two mean-zero sources of one common length.** For `I = (α, α + ε)`, `J = (β, β + ε)` with
`α + ε ≤ β`, i.e. at relative distance `D = (β − α)/ε ≥ 1`, and mean-zero `f ∈ L²(I)`, `g ∈ L²(J)`:
`∫_I ∫_J (f(x) − g(y))²/(y − x) ≥ log((D + 1)/D) (‖f‖² + ‖g‖²)`. -/
theorem lintegral_twoInterval_equalLength_ge {α β ε : ℝ} (hε : 0 < ε) (hαβ : α + ε ≤ β)
    {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 (volume.restrict (Ioo α (α + ε))))
    (hg : MemLp g 2 (volume.restrict (Ioo β (β + ε))))
    (hf0 : ∫ x in Ioo α (α + ε), f x = 0) (hg0 : ∫ y in Ioo β (β + ε), g y = 0) :
    ENNReal.ofReal (Real.log ((β + ε - α) / (β - α)) *
        ((∫ x in Ioo α (α + ε), f x ^ 2) + ∫ y in Ioo β (β + ε), g y ^ 2)) ≤
      ∫⁻ x in Ioo α (α + ε), ∫⁻ y in Ioo β (β + ε),
        ENNReal.ofReal ((f x - g y) ^ 2 / (y - x)) := by
  have h := lintegral_twoInterval_ge (by linarith) hαβ (by linarith) hfm hgm hf hg hf0 hg0
  rw [setLIntegral_one_div_sub_right (by linarith) (by linarith),
    setLIntegral_one_div_sub_left (by linarith) (by linarith),
    show β + ε - (α + ε) = β - α by ring] at h
  have hL : 0 ≤ Real.log ((β + ε - α) / (β - α)) :=
    Real.log_nonneg ((le_div_iff₀ (by linarith)).mpr (by linarith))
  have hNf : 0 ≤ ∫ x in Ioo α (α + ε), f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hNg : 0 ≤ ∫ y in Ioo β (β + ε), g y ^ 2 := integral_nonneg fun y => sq_nonneg _
  rw [mul_add, ENNReal.ofReal_add (mul_nonneg hL hNf) (mul_nonneg hL hNg), ENNReal.ofReal_mul hL,
    ENNReal.ofReal_mul hL, mul_comm (ENNReal.ofReal (Real.log _)),
    mul_comm (ENNReal.ofReal (Real.log _))]
  exact h

end GaloisForLFunctions.HTGeometry.CauchyDifference
