import GaloisForLFunctions.RHTower.MaassBesselFunction
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The three-term equation for a Maass inversion defect

Translation invariance gives an exact three-term identity for `u - u ∘ S`, even when
`u` is not automorphic. Its odd weight-one boundary analogue has a telescoping bound:
decay at infinity and a Lipschitz bound near 1 imply `O(1/x)` at infinity and boundedness
at zero. This is an elementary period-function bridge, not higher-denominator rigidity.

The transport from finitely many poles of a cubic quotient to such a boundary function
is not assumed proved here. See the WP07 paper log for those separate obligations.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower.WeilHigherDenominator

/-- The failure of invariance under `S(z) = -1/z`. -/
def inversionDefect (u : ℂ → ℂ) (z : ℂ) : ℂ := u z - u (-z⁻¹)

theorem inversionDefect_inv (u : ℂ → ℂ) (z : ℂ) :
    inversionDefect u (-z⁻¹) = -inversionDefect u z := by
  simp [inversionDefect]

/-- The modular three-term identity requires only translation invariance. -/
theorem inversionDefect_three_term {u : ℂ → ℂ} (hu : Function.Periodic u 1)
    {z : ℂ} (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) :
    inversionDefect u z = inversionDefect u (z + 1) +
      inversionDefect u (z / (z + 1)) := by
  have hfirst : z / (z + 1) = -(z + 1)⁻¹ + 1 := by
    field_simp
    ring
  have hsecond : -(z / (z + 1))⁻¹ = -z⁻¹ - 1 := by
    field_simp
    ring
  unfold inversionDefect
  rw [hsecond, hu.sub_eq, hfirst, hu z, hu (-(z + 1)⁻¹)]
  ring

/-- In particular this identity holds for the actual Bessel-series Maass function. -/
theorem maass_inversionDefect_three_term (g : ℕ → ℂ) (a b : ℂ)
    {z : ℂ} (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) :
    inversionDefect (MaassBesselSeries.maassFun g a b) z =
      inversionDefect (MaassBesselSeries.maassFun g a b) (z + 1) +
      inversionDefect (MaassBesselSeries.maassFun g a b) (z / (z + 1)) :=
  inversionDefect_three_term (MaassBesselSeries.maassFun_add_one a b) hz hz1

/-- The weight-one coboundary on the real boundary. -/
def weightOneDefect (f : ℝ → ℂ) (x : ℝ) : ℂ := f x - f x⁻¹ / (x : ℂ)

theorem weightOneDefect_inv (f : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) :
    weightOneDefect f x = -weightOneDefect f x⁻¹ / (x : ℂ) := by
  simp only [weightOneDefect, inv_inv, ofReal_inv]
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  field_simp
  ring

theorem weightOneDefect_three_term {f : ℝ → ℂ} (hper : Function.Periodic f 1)
    (heven : ∀ x, f (-x) = f x) {x : ℝ} (hx : 0 < x) :
    weightOneDefect f x = weightOneDefect f (x + 1) +
      weightOneDefect f (x / (x + 1)) / ((x + 1 : ℝ) : ℂ) := by
  have hx0 := ne_of_gt hx
  have hx1 : x + 1 ≠ 0 := by positivity
  have harg : x / (x + 1) = -(x + 1)⁻¹ + 1 := by
    field_simp
    ring
  have harg' : (x / (x + 1))⁻¹ = x⁻¹ + 1 := by
    field_simp
    ring
  have hmid : f (x / (x + 1)) = f (x + 1)⁻¹ := by
    rw [harg, hper, heven]
  unfold weightOneDefect
  rw [harg', hmid, hper x, hper x⁻¹]
  push_cast
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0
  have hxc1 : (x : ℂ) + 1 ≠ 0 := by exact_mod_cast hx1
  field_simp
  ring

/-- Odd inversion forces the central boundary value to vanish. -/
theorem weightOne_period_one_eq_zero {q : ℝ → ℂ}
    (hinv : ∀ x > 0, q x = -q x⁻¹ / (x : ℂ)) : q 1 = 0 := by
  have h := hinv 1 zero_lt_one
  simp only [inv_one, ofReal_one, div_one] at h
  linear_combination h / 2

/-- Each step is bounded by an exactly telescoping reciprocal difference. -/
theorem weightOne_period_step_bound {q : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hthree : ∀ x > 0, q x = q (x + 1) + q (x / (x + 1)) / ((x + 1 : ℝ) : ℂ))
    (hlocal : ∀ t ∈ Icc (1 / 2 : ℝ) 1, ‖q t‖ ≤ C * (1 - t))
    {x : ℝ} (hx : 1 ≤ x) :
    ‖q x - q (x + 1)‖ ≤ C / x - C / (x + 1) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx1 : 0 < x + 1 := by positivity
  have ht : x / (x + 1) ∈ Icc (1 / 2 : ℝ) 1 := by
    constructor
    · rw [le_div_iff₀ hx1]
      linarith
    · rw [div_le_iff₀ hx1]
      linarith
  have heq : q x - q (x + 1) = q (x / (x + 1)) / ((x + 1 : ℝ) : ℂ) := by
    linear_combination hthree x hxpos
  rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx1]
  calc
    ‖q (x / (x + 1))‖ / (x + 1) ≤ (C * (1 - x / (x + 1))) / (x + 1) :=
      div_le_div_of_nonneg_right (hlocal _ ht) hx1.le
    _ ≤ C / x - C / (x + 1) := by
      field_simp
      nlinarith

/-- Decay at infinity upgrades the local bound to a reciprocal bound on the full tail. -/
theorem weightOne_period_tail_bound {q : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hthree : ∀ x > 0, q x = q (x + 1) + q (x / (x + 1)) / ((x + 1 : ℝ) : ℂ))
    (hlocal : ∀ t ∈ Icc (1 / 2 : ℝ) 1, ‖q t‖ ≤ C * (1 - t))
    (hdecay : Tendsto q atTop (𝓝 0)) {x : ℝ} (hx : 1 ≤ x) : ‖q x‖ ≤ C / x := by
  have htel (n : ℕ) : ‖q x - q (x + n)‖ ≤ C / x - C / (x + n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hxn : 1 ≤ x + n := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hs := weightOne_period_step_bound hC hthree hlocal hxn
      calc
        ‖q x - q (x + (n + 1 : ℕ))‖ =
            ‖(q x - q (x + n)) + (q (x + n) - q (x + n + 1))‖ := by
          simp only [Nat.cast_add, Nat.cast_one, add_assoc, sub_add_sub_cancel]
        _ ≤ ‖q x - q (x + n)‖ + ‖q (x + n) - q (x + n + 1)‖ := norm_add_le _ _
        _ ≤ (C / x - C / (x + n)) + (C / (x + n) - C / (x + n + 1)) :=
          add_le_add ih hs
        _ = C / x - C / (x + (n + 1 : ℕ)) := by
          simp only [Nat.cast_add, Nat.cast_one, add_assoc]
          ring
  have htop : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => ‖q x - q (x + n)‖) atTop (𝓝 ‖q x‖) := by
    simpa using (tendsto_const_nhds.sub (hdecay.comp htop)).norm
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n => (htel n).trans
    (sub_le_self _ (div_nonneg hC (by linarith [Nat.cast_nonneg (α := ℝ) n])))

/-- The same constant bounds the boundary function near zero, without positivity of its values. -/
theorem weightOne_period_origin_bound {q : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hthree : ∀ x > 0, q x = q (x + 1) + q (x / (x + 1)) / ((x + 1 : ℝ) : ℂ))
    (hinv : ∀ x > 0, q x = -q x⁻¹ / (x : ℂ))
    (hlocal : ∀ t ∈ Icc (1 / 2 : ℝ) 1, ‖q t‖ ≤ C * (1 - t))
    (hdecay : Tendsto q atTop (𝓝 0)) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖q x‖ ≤ C := by
  have hxi : 1 ≤ x⁻¹ := (one_le_inv₀ hx).mpr hx1
  have hb := weightOne_period_tail_bound hC hthree hlocal hdecay hxi
  rw [hinv x hx, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  calc
    ‖q x⁻¹‖ / x ≤ (C / x⁻¹) / x := div_le_div_of_nonneg_right hb hx.le
    _ = C := by field_simp

/-- A continuously differentiable odd period function decaying at infinity is bounded at zero
and decays reciprocally at infinity. The local constant is derived, not an extra input. -/
theorem weightOne_period_bounds {q : ℝ → ℂ} (hreg : ContDiffOn ℝ 1 q (Ioi 0))
    (hthree : ∀ x > 0, q x = q (x + 1) + q (x / (x + 1)) / ((x + 1 : ℝ) : ℂ))
    (hinv : ∀ x > 0, q x = -q x⁻¹ / (x : ℂ))
    (hdecay : Tendsto q atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x ∈ Ioc (0 : ℝ) 1, ‖q x‖ ≤ C) ∧
      (∀ x ≥ 1, ‖q x‖ ≤ C / x) := by
  have hsub : Icc (1 / 2 : ℝ) 1 ⊆ Ioi 0 := by
    intro t ht
    change 0 < t
    linarith [ht.1]
  have hcont := hreg.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont.mono hsub)
  have hD' : ∀ t ∈ Icc (1 / 2 : ℝ) 1, ‖deriv q t‖ ≤ max D 0 :=
    fun t ht => (hD t ht).trans (le_max_left _ _)
  have hdiff : ∀ t ∈ Icc (1 / 2 : ℝ) 1, DifferentiableAt ℝ q t := by
    intro t ht
    exact ((hreg t (hsub ht)).contDiffAt
      (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt (by decide)
  have hlocal : ∀ t ∈ Icc (1 / 2 : ℝ) 1, ‖q t‖ ≤ max D 0 * (1 - t) := by
    intro t ht
    have hb := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hD'
      (convex_Icc (1 / 2 : ℝ) 1) (show (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 by constructor <;> norm_num) ht
    rw [weightOne_period_one_eq_zero hinv, sub_zero, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr ht.2)] at hb
    simpa only [neg_sub] using hb
  refine ⟨max D 0, le_max_right _ _, ?_, ?_⟩
  · exact fun x hx => weightOne_period_origin_bound (le_max_right _ _) hthree hinv hlocal hdecay hx.1 hx.2
  · exact fun x hx => weightOne_period_tail_bound (le_max_right _ _) hthree hlocal hdecay hx

end RHTower.WeilHigherDenominator
