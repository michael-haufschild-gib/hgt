import GaloisForLFunctions.ArithmeticCriticalityTheory.FarApartBumpsPositivity

/-!
# Averaging the shifted ground states over the shift

The products `m_a(x) m_a(y)` integrate over the shift `a` to an explicit kernel built from the
autocorrelation `G = Φ ∗ Φ` of Riemann's kernel:

    ∫_0^∞ m_a(x) m_a(y) da = G(x − y) − G(x + y),

and the two-sided source averages to a hyperbolic sine square,

    ∫_0^∞ 4 sinh(a/2) m_a(x) sinh(x/2) da = 2 sinh²(x/2),

because `∫ Φ(s) cosh(s/2) ds = 1/2` and `∫ Φ(s) sinh(s/2) ds = 0`. The autocorrelation is even,
bounded by `G(0)`, and decays like `Φ(|z|/2)`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Substitutions -/

theorem integral_comp_const_sub (f : ℝ → ℝ) (c : ℝ) : (∫ a, f (c - a)) = ∫ a, f a := by
  have h1 : (∫ a, f (c - a)) = ∫ a, f (c + a) := by
    rw [← integral_neg_eq_self (fun a => f (c + a))]
    exact integral_congr_ae (Eventually.of_forall fun a => congrArg f (sub_eq_add_neg c a))
  rw [h1, ← integral_add_right_eq_self (fun a => f a) c]
  exact integral_congr_ae (Eventually.of_forall fun a => congrArg f (add_comm c a))

/-- Even integrable functions: the half-line integral is half the full integral. -/
theorem integral_Ioi_eq_half_of_even {f : ℝ → ℝ} (hf : Integrable f) (heven : ∀ x, f (-x) = f x) :
    (∫ x in Ioi (0 : ℝ), f x) = 1 / 2 * ∫ x, f x := by
  have h := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hf
  rw [Set.compl_Ioi] at h
  have h2 : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    have := integral_comp_neg_Iic (0 : ℝ) f
    rw [neg_zero] at this
    rw [← this]
    exact setIntegral_congr_fun measurableSet_Iic fun x _ => (heven x).symm
  linarith

/-! ### The autocorrelation of Riemann's kernel -/

theorem riemannAutocorr_neg (y : ℝ) : riemannAutocorr (-y) = riemannAutocorr y := by
  unfold riemannAutocorr
  rw [← integral_neg_eq_self (fun t => riemannKernelReal t * riemannKernelReal (t - y))]
  congr 1
  funext t
  show riemannKernelReal t * riemannKernelReal (t - -y) =
    riemannKernelReal (-t) * riemannKernelReal (-t - y)
  rw [riemannKernelReal_neg', show -t - y = -(t - -y) by ring, riemannKernelReal_neg']

theorem riemannAutocorr_nonneg (y : ℝ) : 0 ≤ riemannAutocorr y :=
  integral_nonneg fun t => mul_nonneg (riemannKernelReal_pos t).le (riemannKernelReal_pos _).le

/-- `G(z) ≤ Φ(|z|/2)`: one of the two factors is evaluated at distance at least `|z|/2`. -/
theorem riemannAutocorr_le_kernel_half (z : ℝ) :
    riemannAutocorr z ≤ riemannKernelReal (|z| / 2) := by
  unfold riemannAutocorr
  have hK := (riemannKernelReal_pos (|z| / 2)).le
  have hint1 := integrable_riemannKernelReal
  have hint2 : Integrable fun t : ℝ => riemannKernelReal (t - z) :=
    integrable_riemannKernelReal.comp_sub_right z
  have hmaj : Integrable fun t : ℝ => riemannKernelReal (|z| / 2) *
      (riemannKernelReal t + riemannKernelReal (t - z)) := (hint1.add hint2).const_mul _
  have hpt : ∀ t, riemannKernelReal t * riemannKernelReal (t - z) ≤
      riemannKernelReal (|z| / 2) * (riemannKernelReal t + riemannKernelReal (t - z)) := by
    intro t
    have h1 := (riemannKernelReal_pos t).le
    have h2 := (riemannKernelReal_pos (t - z)).le
    -- one of |t|, |t − z| is at least |z|/2
    rcases le_or_gt (|z| / 2) |t| with ht | ht
    · have : riemannKernelReal t ≤ riemannKernelReal (|z| / 2) := by
        rw [← riemannKernelReal_abs' t]
        exact riemannKernelReal_antitone_of_nonneg (by positivity) ht
      nlinarith
    · have htz : |z| / 2 ≤ |t - z| := by
        have := abs_sub_abs_le_abs_sub z t
        rw [abs_sub_comm t z]
        linarith
      have : riemannKernelReal (t - z) ≤ riemannKernelReal (|z| / 2) := by
        rw [← riemannKernelReal_abs' (t - z)]
        exact riemannKernelReal_antitone_of_nonneg (by positivity) htz
      nlinarith
  calc (∫ t, riemannKernelReal t * riemannKernelReal (t - z))
      ≤ ∫ t, riemannKernelReal (|z| / 2) * (riemannKernelReal t + riemannKernelReal (t - z)) :=
        integral_mono (integrable_riemannKernelReal_mul z) hmaj hpt
    _ = riemannKernelReal (|z| / 2) * ((∫ t, riemannKernelReal t) + ∫ t, riemannKernelReal (t - z)) := by
        rw [integral_const_mul, integral_add hint1 hint2]
    _ = riemannKernelReal (|z| / 2) * (2 * ∫ t, riemannKernelReal t) := by
        rw [integral_sub_right_eq_self (fun t => riemannKernelReal t) z]
        ring
    _ ≤ riemannKernelReal (|z| / 2) * (2 * (1 / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left integral_riemannKernelReal_le_half
          (by norm_num)) hK
    _ = riemannKernelReal (|z| / 2) := by ring

theorem riemannAutocorr_le_zero_point (z : ℝ) : riemannAutocorr z ≤ riemannKernelReal 0 :=
  (riemannAutocorr_le_kernel_half z).trans (riemannKernelReal_le_zero_point _)

/-! ### Shift integrals of products of translated kernels -/

theorem integral_kernel_sub_mul_sub (x y : ℝ) :
    (∫ a, riemannKernelReal (x - a) * riemannKernelReal (y - a)) = riemannAutocorr (x - y) := by
  unfold riemannAutocorr
  rw [← integral_comp_const_sub (fun s => riemannKernelReal s * riemannKernelReal (s - (x - y))) x]
  congr 1
  funext a
  show riemannKernelReal (x - a) * riemannKernelReal (y - a) =
    riemannKernelReal (x - a) * riemannKernelReal (x - a - (x - y))
  rw [show x - a - (x - y) = y - a by ring]

theorem integral_kernel_add_mul_add (x y : ℝ) :
    (∫ a, riemannKernelReal (x + a) * riemannKernelReal (y + a)) = riemannAutocorr (x - y) := by
  unfold riemannAutocorr
  rw [← integral_add_right_eq_self (fun s => riemannKernelReal s * riemannKernelReal (s - (x - y))) x]
  congr 1
  funext a
  show riemannKernelReal (x + a) * riemannKernelReal (y + a) =
    riemannKernelReal (a + x) * riemannKernelReal (a + x - (x - y))
  rw [show a + x - (x - y) = y + a by ring, add_comm a x]

theorem integral_kernel_sub_mul_add (x y : ℝ) :
    (∫ a, riemannKernelReal (x - a) * riemannKernelReal (y + a)) = riemannAutocorr (x + y) := by
  unfold riemannAutocorr
  rw [← integral_comp_const_sub (fun s => riemannKernelReal s * riemannKernelReal (s - (x + y))) x]
  congr 1
  funext a
  show riemannKernelReal (x - a) * riemannKernelReal (y + a) =
    riemannKernelReal (x - a) * riemannKernelReal (x - a - (x + y))
  rw [show x - a - (x + y) = -(y + a) by ring, riemannKernelReal_neg']

theorem integral_kernel_add_mul_sub (x y : ℝ) :
    (∫ a, riemannKernelReal (x + a) * riemannKernelReal (y - a)) = riemannAutocorr (x + y) := by
  rw [show (∫ a, riemannKernelReal (x + a) * riemannKernelReal (y - a)) =
      ∫ a, riemannKernelReal (y - a) * riemannKernelReal (x + a) by
        congr 1; funext a; ring, integral_kernel_sub_mul_add, add_comm]

theorem integrable_kernel_sub_mul_sub (x y : ℝ) :
    Integrable fun a => riemannKernelReal (x - a) * riemannKernelReal (y - a) := by
  have h := (integrable_riemannKernelReal_mul (x - y)).comp_sub_left x
  refine h.congr (Eventually.of_forall fun a => ?_)
  show riemannKernelReal (x - a) * riemannKernelReal (x - a - (x - y)) = _
  rw [show x - a - (x - y) = y - a by ring]

theorem integrable_kernel_add_mul_add (x y : ℝ) :
    Integrable fun a => riemannKernelReal (x + a) * riemannKernelReal (y + a) := by
  have h := (integrable_riemannKernelReal_mul (x - y)).comp_add_left x
  refine h.congr (Eventually.of_forall fun a => ?_)
  show riemannKernelReal (x + a) * riemannKernelReal (x + a - (x - y)) = _
  rw [show x + a - (x - y) = y + a by ring]

theorem integrable_kernel_sub_mul_add (x y : ℝ) :
    Integrable fun a => riemannKernelReal (x - a) * riemannKernelReal (y + a) := by
  have h := (integrable_riemannKernelReal_mul (x + y)).comp_sub_left x
  refine h.congr (Eventually.of_forall fun a => ?_)
  show riemannKernelReal (x - a) * riemannKernelReal (x - a - (x + y)) = _
  rw [show x - a - (x + y) = -(y + a) by ring, riemannKernelReal_neg']

theorem integrable_kernel_add_mul_sub (x y : ℝ) :
    Integrable fun a => riemannKernelReal (x + a) * riemannKernelReal (y - a) := by
  refine (integrable_kernel_sub_mul_add y x).congr (Eventually.of_forall fun a => ?_)
  show riemannKernelReal (y - a) * riemannKernelReal (x + a) = _
  ring

/-! ### The averaged kernel -/

theorem shiftDifference_mul_eq (a x y : ℝ) :
    shiftDifference a x * shiftDifference a y =
      (riemannKernelReal (x - a) * riemannKernelReal (y - a) +
        riemannKernelReal (x + a) * riemannKernelReal (y + a)) -
      (riemannKernelReal (x - a) * riemannKernelReal (y + a) +
        riemannKernelReal (x + a) * riemannKernelReal (y - a)) := by
  unfold shiftDifference
  ring

theorem integrable_shiftDifference_mul_shiftDifference (x y : ℝ) :
    Integrable fun a => shiftDifference a x * shiftDifference a y := by
  have h := ((integrable_kernel_sub_mul_sub x y).add (integrable_kernel_add_mul_add x y)).sub
    ((integrable_kernel_sub_mul_add x y).add (integrable_kernel_add_mul_sub x y))
  refine h.congr (Eventually.of_forall fun a => ?_)
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [shiftDifference_mul_eq]

theorem shiftDifference_mul_shiftDifference_neg (a x y : ℝ) :
    shiftDifference (-a) x * shiftDifference (-a) y = shiftDifference a x * shiftDifference a y := by
  unfold shiftDifference
  rw [show x - -a = x + a by ring, show x + -a = x - a by ring, show y - -a = y + a by ring,
    show y + -a = y - a by ring]
  ring

/-- **The averaged kernel.** `∫_0^∞ m_a(x) m_a(y) da = G(x − y) − G(x + y)`. -/
theorem integral_Ioi_shiftDifference_mul_shiftDifference (x y : ℝ) :
    (∫ a in Ioi (0 : ℝ), shiftDifference a x * shiftDifference a y) =
      riemannAutocorr (x - y) - riemannAutocorr (x + y) := by
  rw [integral_Ioi_eq_half_of_even (integrable_shiftDifference_mul_shiftDifference x y)
    (fun a => shiftDifference_mul_shiftDifference_neg a x y)]
  have hfull : (∫ a, shiftDifference a x * shiftDifference a y) =
      2 * riemannAutocorr (x - y) - 2 * riemannAutocorr (x + y) := by
    have e : (fun a => shiftDifference a x * shiftDifference a y) = fun a =>
        (riemannKernelReal (x - a) * riemannKernelReal (y - a) +
          riemannKernelReal (x + a) * riemannKernelReal (y + a)) -
        (riemannKernelReal (x - a) * riemannKernelReal (y + a) +
          riemannKernelReal (x + a) * riemannKernelReal (y - a)) := by
      funext a
      exact shiftDifference_mul_eq a x y
    have hI12 : Integrable fun a => riemannKernelReal (x - a) * riemannKernelReal (y - a) +
        riemannKernelReal (x + a) * riemannKernelReal (y + a) :=
      (integrable_kernel_sub_mul_sub x y).add (integrable_kernel_add_mul_add x y)
    have hI34 : Integrable fun a => riemannKernelReal (x - a) * riemannKernelReal (y + a) +
        riemannKernelReal (x + a) * riemannKernelReal (y - a) :=
      (integrable_kernel_sub_mul_add x y).add (integrable_kernel_add_mul_sub x y)
    rw [e, integral_sub hI12 hI34,
      integral_add (integrable_kernel_sub_mul_sub x y) (integrable_kernel_add_mul_add x y),
      integral_add (integrable_kernel_sub_mul_add x y) (integrable_kernel_add_mul_sub x y),
      integral_kernel_sub_mul_sub, integral_kernel_add_mul_add, integral_kernel_sub_mul_add,
      integral_kernel_add_mul_sub]
    ring
  rw [hfull]
  ring

/-! ### The averaged source -/

theorem integral_riemannKernelReal_mul_sinh_half :
    (∫ s, riemannKernelReal s * Real.sinh (s / 2)) = 0 := by
  have hint : Integrable fun s : ℝ => riemannKernelReal s * Real.sinh (s / 2) := by
    have h := ((integrable_riemannKernelReal_mul_exp (1 / 2)).sub
      (integrable_riemannKernelReal_mul_exp (-(1 / 2)))).const_mul (1 / 2)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [Real.sinh_eq, show x / 2 = 1 / 2 * x by ring, show -(1 / 2 * x) = -(1 / 2) * x by ring]
    ring
  have hodd : ∀ s : ℝ, riemannKernelReal (-s) * Real.sinh (-s / 2) =
      -(riemannKernelReal s * Real.sinh (s / 2)) := by
    intro s
    rw [riemannKernelReal_neg', show -s / 2 = -(s / 2) by ring, Real.sinh_neg]
    ring
  have h := integral_neg_eq_self (fun s => riemannKernelReal s * Real.sinh (s / 2)) volume
  have h' : (∫ s, riemannKernelReal (-s) * Real.sinh (-s / 2)) =
      -∫ s, riemannKernelReal s * Real.sinh (s / 2) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall hodd)
  have h'' : (∫ s, riemannKernelReal (-s) * Real.sinh (-s / 2)) =
      ∫ s, riemannKernelReal s * Real.sinh (s / 2) := h
  linarith

theorem integrable_kernel_mul_cosh_half :
    Integrable fun s : ℝ => riemannKernelReal s * Real.cosh (s / 2) := by
  have h := ((integrable_riemannKernelReal_mul_exp (1 / 2)).add
    (integrable_riemannKernelReal_mul_exp (-(1 / 2)))).const_mul (1 / 2)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply]
  rw [Real.cosh_eq, show y / 2 = 1 / 2 * y by ring, show -(1 / 2 * y) = -(1 / 2) * y by ring]
  ring

theorem integrable_kernel_mul_sinh_half :
    Integrable fun s : ℝ => riemannKernelReal s * Real.sinh (s / 2) := by
  have h := ((integrable_riemannKernelReal_mul_exp (1 / 2)).sub
    (integrable_riemannKernelReal_mul_exp (-(1 / 2)))).const_mul (1 / 2)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  rw [Real.sinh_eq, show y / 2 = 1 / 2 * y by ring, show -(1 / 2 * y) = -(1 / 2) * y by ring]
  ring

/-- `∫ sinh(a/2) Φ(x − a) da = sinh(x/2)/2`. -/
theorem integral_sinh_mul_kernel_sub (x : ℝ) :
    (∫ a, Real.sinh (a / 2) * riemannKernelReal (x - a)) = Real.sinh (x / 2) / 2 := by
  have hsub : (∫ a, Real.sinh (a / 2) * riemannKernelReal (x - a)) =
      ∫ s, Real.sinh ((x - s) / 2) * riemannKernelReal s := by
    rw [← integral_comp_const_sub (fun s => Real.sinh ((x - s) / 2) * riemannKernelReal s) x]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show Real.sinh (a / 2) * riemannKernelReal (x - a) =
      Real.sinh ((x - (x - a)) / 2) * riemannKernelReal (x - a)
    rw [show x - (x - a) = a by ring]
  have e2 : ∀ s, Real.sinh ((x - s) / 2) * riemannKernelReal s =
      Real.sinh (x / 2) * (riemannKernelReal s * Real.cosh (s / 2)) -
        Real.cosh (x / 2) * (riemannKernelReal s * Real.sinh (s / 2)) := by
    intro s
    rw [show (x - s) / 2 = x / 2 - s / 2 by ring, Real.sinh_sub]
    ring
  rw [hsub, integral_congr_ae (Eventually.of_forall e2),
    integral_sub (integrable_kernel_mul_cosh_half.const_mul _)
      (integrable_kernel_mul_sinh_half.const_mul _),
    integral_const_mul, integral_const_mul, integral_riemannKernelReal_cosh_half,
    integral_riemannKernelReal_mul_sinh_half]
  ring

theorem integrable_sinh_mul_kernel_sub (x : ℝ) :
    Integrable fun a : ℝ => Real.sinh (a / 2) * riemannKernelReal (x - a) := by
  have h1 : Integrable fun a : ℝ => Real.exp (a / 2) * riemannKernelReal (x - a) := by
    have h := ((integrable_riemannKernelReal_mul_exp (-(1 / 2))).comp_sub_left x).const_mul
      (Real.exp (x / 2))
    refine h.congr (Eventually.of_forall fun a => ?_)
    show Real.exp (x / 2) * (riemannKernelReal (x - a) * Real.exp (-(1 / 2) * (x - a))) =
      Real.exp (a / 2) * riemannKernelReal (x - a)
    rw [show Real.exp (a / 2) = Real.exp (x / 2) * Real.exp (-(1 / 2) * (x - a)) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  have h2 : Integrable fun a : ℝ => Real.exp (-(a / 2)) * riemannKernelReal (x - a) := by
    have h := ((integrable_riemannKernelReal_mul_exp (1 / 2)).comp_sub_left x).const_mul
      (Real.exp (-(x / 2)))
    refine h.congr (Eventually.of_forall fun a => ?_)
    show Real.exp (-(x / 2)) * (riemannKernelReal (x - a) * Real.exp (1 / 2 * (x - a))) =
      Real.exp (-(a / 2)) * riemannKernelReal (x - a)
    rw [show Real.exp (-(a / 2)) = Real.exp (-(x / 2)) * Real.exp (1 / 2 * (x - a)) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  refine ((h1.sub h2).const_mul (1 / 2)).congr (Eventually.of_forall fun a => ?_)
  simp only [Pi.sub_apply]
  rw [Real.sinh_eq]
  ring

theorem integrable_sinh_mul_kernel_add (x : ℝ) :
    Integrable fun a : ℝ => Real.sinh (a / 2) * riemannKernelReal (x + a) := by
  refine (integrable_sinh_mul_kernel_sub (-x)).congr (Eventually.of_forall fun a => ?_)
  show Real.sinh (a / 2) * riemannKernelReal (-x - a) = Real.sinh (a / 2) * riemannKernelReal (x + a)
  rw [show -x - a = -(x + a) by ring, riemannKernelReal_neg']

theorem integral_sinh_mul_kernel_add (x : ℝ) :
    (∫ a, Real.sinh (a / 2) * riemannKernelReal (x + a)) = -Real.sinh (x / 2) / 2 := by
  have h := integral_sinh_mul_kernel_sub (-x)
  rw [show -x / 2 = -(x / 2) by ring, Real.sinh_neg] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  show Real.sinh (a / 2) * riemannKernelReal (x + a) = Real.sinh (a / 2) * riemannKernelReal (-x - a)
  rw [show -x - a = -(x + a) by ring, riemannKernelReal_neg']

theorem integrable_sinh_mul_shiftDifference (x : ℝ) :
    Integrable fun a : ℝ => 4 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2) := by
  have h := ((integrable_sinh_mul_kernel_sub x).sub (integrable_sinh_mul_kernel_add x)).const_mul
    (4 * Real.sinh (x / 2))
  refine h.congr (Eventually.of_forall fun a => ?_)
  simp only [Pi.sub_apply]
  unfold shiftDifference
  ring

theorem shiftDifference_neg_shift (a x : ℝ) : shiftDifference (-a) x = -shiftDifference a x := by
  unfold shiftDifference
  rw [show x - -a = x + a by ring, show x + -a = x - a by ring]
  ring

theorem sinh_mul_shiftDifference_neg (a x : ℝ) :
    4 * Real.sinh (-a / 2) * shiftDifference (-a) x * Real.sinh (x / 2) =
      4 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2) := by
  rw [show -a / 2 = -(a / 2) by ring, Real.sinh_neg, shiftDifference_neg_shift]
  ring

/-- **The averaged source.** `∫_0^∞ 4 sinh(a/2) m_a(x) sinh(x/2) da = 2 sinh²(x/2)`. -/
theorem integral_Ioi_sinh_mul_shiftDifference (x : ℝ) :
    (∫ a in Ioi (0 : ℝ), 4 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2)) =
      2 * Real.sinh (x / 2) ^ 2 := by
  rw [integral_Ioi_eq_half_of_even (integrable_sinh_mul_shiftDifference x)
    (fun a => sinh_mul_shiftDifference_neg a x)]
  have e : (fun a => 4 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2)) =
      fun a => 4 * Real.sinh (x / 2) * (Real.sinh (a / 2) * riemannKernelReal (x - a)) -
        4 * Real.sinh (x / 2) * (Real.sinh (a / 2) * riemannKernelReal (x + a)) := by
    funext a
    unfold shiftDifference
    ring
  rw [e, integral_sub ((integrable_sinh_mul_kernel_sub x).const_mul _)
    ((integrable_sinh_mul_kernel_add x).const_mul _), integral_const_mul, integral_const_mul,
    integral_sinh_mul_kernel_sub, integral_sinh_mul_kernel_add]
  ring

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
