/-
# ReversalSupBound — analytic weak Sup Lemma for Theorem B⁗ (doc 41 §2; task #147)

The (B⁗-a) reversal ledger in the doc 41 §2 unified form is

  `R(1/2,c,0) = c·∫_{(0,log 2]} 2 sinh²(z/2)·csch²(cz/2) dz
              − c·∫_{(log 2,∞)} (1−e^{−z})·½·csch²(cz/2) dz`.

Proved here, fully analytically (no numerics):

* `reversalLedger_le_weak` — `R ≤ 4/(3c)` for every `c ≥ 2`. Chain: `u ↦ sinh(ut)/u`
  is nondecreasing (derivative sign = `sinh_le_mul_cosh`), so
  `sinh(cz/2) ≥ c·sinh(z/2)cosh(z/2)` with equality at `c = 2` (double angle); the
  ahead integrand is then `≤ (2/c²)·sech²(z/2)`, whose integral is
  `(4/c²)·tanh(log2/2) = 4/(3c²)` exactly (`tanh(log2/2) = 1/3`); the behind integral
  is nonnegative and is dropped.
* `reversalLedger_le_two_thirds` — `R ≤ 2/3` for all `c ≥ 2`. This replaces the
  certified-numerics dependence for the qualitative consumer: Theorem B⁗'s downstream
  use (Theorem S′) needs only `ΔG ≥ 1`, i.e. `R ≤ 1 − err(i)` (≈ 0.79 at `i ≥ 200`),
  which `2/3` clears.
* `reversalLedger_lt_quarter_of_gt` — the sharp budget `R < 1/4` for `c > 16/3`
  (improves the doc 41 §2 tail threshold `c ≥ 6`).

Grading (flat): standard analysis; nothing here is new mathematics. What remains OPEN
of (B⁗-a): the sharp `sup_{c≥2} R < 1/4` on `c ∈ [2, 16/3]` (paper max ≈ 0.2474 at
c* ≈ 2.53 — a ≈1% margin this hand bound does not reach); that stays at
certified-numerics grade (1601-pt grid + proven Lipschitz + proven tail, doc 41 §2),
interval-arithmetic Lean replication still open.

Bound quality: at `c = 2` the ahead bound is exact (`I₁(2) = 2/3 = 4/(3·2)`); the weak
bound loses only the dropped behind subtraction. Pre-certified numerically:
`computations/mwm/` scratch `precert_supbound.py` (pointwise inequality, `I₁ ≤ 4/(3c)`
on a c-grid, margins).
-/
import GaloisForLFunctions.RHTower.CothInfra

noncomputable section

namespace RHTower

open MeasureTheory Set

/-- Ahead piece of the doc 41 §2 unified reversal form:
`c·∫_{(0,log2]} 2 sinh²(z/2)·csch²(cz/2) dz`. -/
def reversalAhead (c : ℝ) : ℝ :=
  c * ∫ z in Ioc (0 : ℝ) (Real.log 2),
    2 * Real.sinh (z / 2) ^ 2 * ((Real.sinh (c * z / 2))⁻¹) ^ 2

/-- Behind piece: `c·∫_{(log2,∞)} (1−e^{−z})·½·csch²(cz/2) dz`. -/
def reversalBehind (c : ℝ) : ℝ :=
  c * ∫ z in Ioi (Real.log 2),
    (1 - Real.exp (-z)) * (1 / 2) * ((Real.sinh (c * z / 2))⁻¹) ^ 2

/-- The reversal ledger `R(1/2, c, 0)` (doc 41 §2 unified form). -/
def reversalLedger (c : ℝ) : ℝ := reversalAhead c - reversalBehind c

/-- `tanh(log2/2) = 1/3` exactly: with `a = e^{log2/2}`, `a² = 2` turns the tanh
quotient `(a−a⁻¹)/(a+a⁻¹)` into `(2−1)/(2+1)`. -/
theorem tanh_half_log_two : Real.tanh (Real.log 2 / 2) = 1 / 3 := by
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  set a := Real.exp (Real.log 2 / 2) with ha_def
  have ha : 0 < a := Real.exp_pos _
  have haa : a * a = 2 := by
    rw [ha_def, ← Real.exp_add,
      show Real.log 2 / 2 + Real.log 2 / 2 = Real.log 2 by ring, h2]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, ← ha_def]
  have hane : a ≠ 0 := ne_of_gt ha
  field_simp
  nlinarith [haa]

/-- `tanh′ = sech²` (mathlib has `hasDerivAt_sinh`/`cosh` but no tanh derivative). -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh ((Real.cosh x)⁻¹ ^ 2) x := by
  have h : HasDerivAt (fun y => Real.sinh y / Real.cosh y)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (ne_of_gt (Real.cosh_pos x))
  have h1 : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [h1] at h
  have h3 : Real.tanh = fun y => Real.sinh y / Real.cosh y := by
    funext y; exact Real.tanh_eq_sinh_div_cosh y
  rw [h3]
  convert h using 1
  rw [inv_pow]
  exact (one_div _).symm

/-- `c·sinh t·cosh t ≤ sinh(ct)` for `t > 0`, `c ≥ 2`: the function `u ↦ sinh(ut)/u`
is nondecreasing on `[2, c]` (numerator of its derivative is `ut·cosh(ut) − sinh(ut) ≥ 0`
by `sinh_le_mul_cosh`), and its value at `u = 2` is `sinh t·cosh t` (double angle).
Equality at `c = 2`. -/
theorem mul_sinh_cosh_le_sinh_mul {t c : ℝ} (ht : 0 < t) (hc : 2 ≤ c) :
    c * (Real.sinh t * Real.cosh t) ≤ Real.sinh (c * t) := by
  have hmono : MonotoneOn (fun u : ℝ => Real.sinh (u * t) / u) (Icc 2 c) := by
    have hderiv : ∀ u ∈ interior (Icc (2 : ℝ) c),
        HasDerivAt (fun u : ℝ => Real.sinh (u * t) / u)
          ((Real.cosh (u * t) * t * u - Real.sinh (u * t) * 1) / u ^ 2) u := by
      intro u hu
      rw [interior_Icc, mem_Ioo] at hu
      have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu.1])
      have h1 : HasDerivAt (fun u : ℝ => Real.sinh (u * t)) (Real.cosh (u * t) * t) u := by
        rw [show (fun u : ℝ => Real.sinh (u * t)) =
          Real.sinh ∘ fun u => u * t by rfl]
        exact (Real.hasDerivAt_sinh (u * t)).comp u (hasDerivAt_mul_const t)
      exact h1.div (hasDerivAt_id u) hu0
    apply monotoneOn_of_deriv_nonneg (convex_Icc 2 c)
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu
      exact ne_of_gt (by linarith [hu.1] : (0 : ℝ) < u)
    · intro u hu
      exact (hderiv u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hderiv u hu).deriv]
      rw [interior_Icc, mem_Ioo] at hu
      have hu0 : 0 < u := by linarith [hu.1]
      have hut : 0 ≤ u * t := by positivity
      have hkey := sinh_le_mul_cosh hut
      have hre : u * t * Real.cosh (u * t) = Real.cosh (u * t) * t * u := by ring
      apply div_nonneg _ (by positivity)
      linarith [hkey, hre]
  have hle : Real.sinh (2 * t) / 2 ≤ Real.sinh (c * t) / c :=
    hmono (left_mem_Icc.mpr hc) (right_mem_Icc.mpr hc) hc
  rw [Real.sinh_two_mul] at hle
  have hc0 : (0 : ℝ) < c := by linarith
  rw [le_div_iff₀ hc0] at hle
  calc c * (Real.sinh t * Real.cosh t)
      = 2 * Real.sinh t * Real.cosh t / 2 * c := by ring
    _ ≤ Real.sinh (c * t) := hle

/-- **Ahead bound**: `reversalAhead c ≤ 4/(3c)` for `c ≥ 2` — exact at `c = 2`
(where `I₁(2) = 2/3`). -/
theorem reversalAhead_le {c : ℝ} (hc : 2 ≤ c) : reversalAhead c ≤ 4 / (3 * c) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- pointwise domination on the domain
  have hfg : ∀ z ∈ Ioc (0 : ℝ) (Real.log 2),
      2 * Real.sinh (z / 2) ^ 2 * ((Real.sinh (c * z / 2))⁻¹) ^ 2
        ≤ 2 / c ^ 2 * ((Real.cosh (z / 2))⁻¹) ^ 2 := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have ht : 0 < z / 2 := by linarith
    have hs : 0 < Real.sinh (z / 2) := sinh_pos_of_pos ht
    have hch : 0 < Real.cosh (z / 2) := Real.cosh_pos _
    have hkey : c * (Real.sinh (z / 2) * Real.cosh (z / 2)) ≤ Real.sinh (c * (z / 2)) :=
      mul_sinh_cosh_le_sinh_mul ht hc
    rw [show c * (z / 2) = c * z / 2 by ring] at hkey
    have hpos : 0 < c * (Real.sinh (z / 2) * Real.cosh (z / 2)) := by positivity
    have hspos : 0 < Real.sinh (c * z / 2) := lt_of_lt_of_le hpos hkey
    have hinv : (Real.sinh (c * z / 2))⁻¹
        ≤ (c * (Real.sinh (z / 2) * Real.cosh (z / 2)))⁻¹ := by
      rw [inv_le_inv₀ hspos hpos]
      exact hkey
    have hsq : ((Real.sinh (c * z / 2))⁻¹) ^ 2
        ≤ ((c * (Real.sinh (z / 2) * Real.cosh (z / 2)))⁻¹) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hspos.le) hinv 2
    have hmul := mul_le_mul_of_nonneg_left hsq
      (by positivity : (0 : ℝ) ≤ 2 * Real.sinh (z / 2) ^ 2)
    refine le_trans hmul (le_of_eq ?_)
    have hsne : Real.sinh (z / 2) ≠ 0 := ne_of_gt hs
    have hchne : Real.cosh (z / 2) ≠ 0 := ne_of_gt hch
    field_simp
  -- the dominating function is continuous, hence integrable on the window
  have hchc : Continuous fun z : ℝ => (Real.cosh (z / 2))⁻¹ :=
    (Real.continuous_cosh.comp (continuous_id.div_const 2)).inv₀
      fun x => ne_of_gt (Real.cosh_pos _)
  have hgcont : Continuous fun z : ℝ => 2 / c ^ 2 * ((Real.cosh (z / 2))⁻¹) ^ 2 :=
    continuous_const.mul (hchc.pow 2)
  have hgint : IntegrableOn (fun z : ℝ => 2 / c ^ 2 * ((Real.cosh (z / 2))⁻¹) ^ 2)
      (Ioc 0 (Real.log 2)) := hgcont.integrableOn_Ioc
  -- the integrand is continuous ON the window (sinh(cz/2) ≠ 0 there), so measurable
  have hfmeas : AEStronglyMeasurable
      (fun z : ℝ => 2 * Real.sinh (z / 2) ^ 2 * ((Real.sinh (c * z / 2))⁻¹) ^ 2)
      (volume.restrict (Ioc 0 (Real.log 2))) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀ (by fun_prop)
    intro z hz
    have hcz : 0 < c * z := mul_pos hc0 hz.1
    exact ne_of_gt (sinh_pos_of_pos (by linarith))
  -- integrability by domination (the constant-free route: dominate by the bound itself)
  have hfint : IntegrableOn
      (fun z : ℝ => 2 * Real.sinh (z / 2) ^ 2 * ((Real.sinh (c * z / 2))⁻¹) ^ 2)
      (Ioc 0 (Real.log 2)) := by
    apply Integrable.mono' hgint hfmeas
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with z hz
    rw [Real.norm_of_nonneg (by positivity)]
    exact hfg z hz
  have hIle := setIntegral_mono_on hfint hgint measurableSet_Ioc hfg
  -- exact evaluation of the dominating integral: FTC with antiderivative (4/c²)tanh(z/2)
  have heval : ∫ z in Ioc (0 : ℝ) (Real.log 2), 2 / c ^ 2 * ((Real.cosh (z / 2))⁻¹) ^ 2
      = 4 / (3 * c ^ 2) := by
    rw [← intervalIntegral.integral_of_le hL.le]
    have hF : ∀ z ∈ uIcc (0 : ℝ) (Real.log 2),
        HasDerivAt (fun z : ℝ => 4 / c ^ 2 * Real.tanh (z / 2))
          (2 / c ^ 2 * ((Real.cosh (z / 2))⁻¹) ^ 2) z := by
      intro z _
      have h1 : HasDerivAt (fun z : ℝ => z / 2) (1 / 2 : ℝ) z := by
        simpa using (hasDerivAt_id z).div_const 2
      have h3 := ((hasDerivAt_tanh (z / 2)).comp z h1).const_mul (4 / c ^ 2)
      exact h3.congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (hgcont.intervalIntegrable _ _)]
    rw [show (0 : ℝ) / 2 = 0 by norm_num, Real.tanh_zero, tanh_half_log_two]
    ring
  -- assemble: c·I₁ ≤ c·(4/(3c²)) = 4/(3c)
  unfold reversalAhead
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans hIle (le_of_eq heval)) hc0.le)
    (le_of_eq ?_)
  rw [← mul_div_assoc,
    div_eq_div_iff (by positivity : (0 : ℝ) < 3 * c ^ 2).ne' (by positivity : (0 : ℝ) < 3 * c).ne']
  ring

/-- The behind piece is nonnegative (`1 − e^{−z} ≥ 0` past `log 2 > 0`; the csch² factor
is a square), so it can be dropped for an upper bound on the ledger. -/
theorem reversalBehind_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ reversalBehind c := by
  unfold reversalBehind
  apply mul_nonneg hc
  apply setIntegral_nonneg measurableSet_Ioi
  intro z hz
  have hz0 : Real.log 2 < z := mem_Ioi.mp hz
  have hzpos : 0 < z := lt_trans (Real.log_pos (by norm_num)) hz0
  have hexp : Real.exp (-z) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1 : (0 : ℝ) ≤ 1 - Real.exp (-z) := by linarith
  exact mul_nonneg (mul_nonneg h1 (by norm_num)) (by positivity)

/-- **Weak Sup Lemma (analytic)**: `R(1/2,c,0) ≤ 4/(3c)` for every `c ≥ 2` — no
numerics. Exact at `c = 2` for the ahead piece; the loss is only the dropped behind
subtraction. -/
theorem reversalLedger_le_weak {c : ℝ} (hc : 2 ≤ c) : reversalLedger c ≤ 4 / (3 * c) := by
  unfold reversalLedger
  have h1 := reversalAhead_le hc
  have h2 := reversalBehind_nonneg (by linarith : (0 : ℝ) ≤ c)
  linarith

/-- **Consumer form**: `R(1/2,c,0) ≤ 2/3` for all `c ≥ 2`. Theorem B⁗'s downstream use
needs only `R ≤ 1 − err(i)` (≈ 0.79 at `i ≥ 200`), which this clears — the qualitative
`ΔG ≥ 1` consumption no longer rests on the certified-numerics grid. The sharp `< 1/4`
on `c ∈ [2, 16/3]` remains certified-numerics grade (doc 41 §2). -/
theorem reversalLedger_le_two_thirds {c : ℝ} (hc : 2 ≤ c) : reversalLedger c ≤ 2 / 3 := by
  have h := reversalLedger_le_weak hc
  have h2 : 4 / (3 * c) ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

/-- **Sharp budget, far range**: `R(1/2,c,0) < 1/4` for `c > 16/3` — improves the
doc 41 §2 tail threshold `c ≥ 6` and shrinks the numerics-only zone to `c ∈ [2, 16/3]`. -/
theorem reversalLedger_lt_quarter_of_gt {c : ℝ} (hc : 16 / 3 < c) :
    reversalLedger c < 1 / 4 := by
  have hc2 : (2 : ℝ) ≤ c := by linarith
  have h := reversalLedger_le_weak hc2
  have h2 : 4 / (3 * c) < 1 / 4 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

end RHTower
