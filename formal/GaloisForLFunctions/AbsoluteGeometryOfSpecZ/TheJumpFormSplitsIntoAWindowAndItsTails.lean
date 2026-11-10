import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsArchimedeanFormIsTheLimitOnInvariantCombs
import GaloisForLFunctions.RHTower.BoxFubini

/-!
# The jump form splits into a window and its tails

For a packet `f` that vanishes outside `(δ, c − δ)`, the jump part of Weil's archimedean form,
`∫_0^∞ 2ω(x)(h(0) − h(x)) dx` with `h` the autocorrelation of `f`, is computed inside the window
`[0, c]`:

  `∫_0^∞ 2ω(x)(h(0) − h(x)) dx = ½ ∫_0^c ∫_0^c ω(|u − v|)(f(u) − f(v))² dv du
      + ∫_0^c f(u)² (Ω(c − u) + Ω(u)) du`,   `Ω(y) = ∫_y^∞ ω`.

The first term is the Dirichlet integral of the jumps with both ends in the window. The second is
the mass of the packet against the rate of the jumps that leave the window on either side.

* **The kernel** (`continuous_jumpKernel`): `ω(|x|)(f(u) − f(u + x))²` is continuous on the plane
  for a Lipschitz packet, with the value `0` on the line `x = 0`.
* **Rows** (`integral_jumpKernel_row`): for `u` in the window, the integral over `|x| ≤ c` is the
  integral of the kernel over the window plus `f(u)²(Ω(c − u) + Ω(u) − 2Ω(c))`.
* **Columns** (`integral_jumpKernel_col`): the integral over `u` in the window is
  `ω(|x|)(h(0) − 2h(x) + ∫_x^{c + x} f²)`.
* **A primitive against the density** (`integral_archLevyDensity_mul_primitive`): integration by
  parts, `∫_0^c ω(x) ∫_0^x φ = ∫_0^c φ(u) Ω(u) du − Ω(c) ∫_0^c φ`, for `φ` vanishing on `[0, δ]`.
* **The identity** (`integral_levyJump_eq_window`): the two iterated integrals of the kernel over
  the rectangle `[0, c] × [−c, c]` agree.
-/

open Finset Filter Topology MeasureTheory
open Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

local notation "ω" => _root_.RHTower.archLevyDensity
local notation "Ω" => _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv

/-! ### The kernels -/

/-- The jump kernel of a packet: `ω(|x|)(f(u) − f(u + x))²`. -/
def jumpKernel (f : ℝ → ℝ) (u x : ℝ) : ℝ := ω |x| * (f u - f (u + x)) ^ 2

/-- The same kernel between two points: `ω(|u − v|)(f(u) − f(v))²`. -/
def boxKernel (f : ℝ → ℝ) (u v : ℝ) : ℝ := ω |u - v| * (f u - f v) ^ 2

theorem archLevyDensity_zero : ω 0 = 0 := by
  simp [_root_.RHTower.archLevyDensity]

theorem boxKernel_eq_jumpKernel (f : ℝ → ℝ) (u v : ℝ) :
    boxKernel f u v = jumpKernel f u (v - u) := by
  have e : u + (v - u) = v := by ring
  rw [boxKernel, jumpKernel, abs_sub_comm, e]

theorem boxKernel_comm (f : ℝ → ℝ) (u v : ℝ) : boxKernel f u v = boxKernel f v u := by
  rw [boxKernel, boxKernel, abs_sub_comm]
  ring

theorem boxKernel_self (f : ℝ → ℝ) (u : ℝ) : boxKernel f u u = 0 := by
  simp [boxKernel]

theorem intervalIntegral_eq_zero_of_eqOn {g : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, g x = 0) : ∫ x in a..b, g x = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => h x hx,
    intervalIntegral.integral_zero]

section Kernel

variable {f : ℝ → ℝ} {L : ℝ}

/-- `ω(|x|)(f(u) − f(u + x))² ≤ L²|x|e^{|x|/2}/2` for an `L`-Lipschitz packet. -/
theorem abs_jumpKernel_le (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (u x : ℝ) :
    |jumpKernel f u x| ≤ L ^ 2 * |x| * (Real.exp (|x| / 2) / 2) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [jumpKernel, archLevyDensity_zero]
  · have hx' : 0 < |x| := abs_pos.mpr hx
    have hω := _root_.RHTower.archLevyDensity_pos hx'
    have h1 := hL u (u + x)
    rw [sub_add_cancel_left, abs_neg] at h1
    have hsq : (f u - f (u + x)) ^ 2 ≤ (L * |x|) ^ 2 := by
      rw [← sq_abs (f u - f (u + x))]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hm := mul_archLevyDensity_le hx'
    rw [jumpKernel, abs_mul, abs_of_pos hω, abs_of_nonneg (sq_nonneg (f u - f (u + x)))]
    calc ω |x| * (f u - f (u + x)) ^ 2 ≤ ω |x| * (L * |x|) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hω.le
      _ = L ^ 2 * |x| * (|x| * ω |x|) := by ring
      _ ≤ L ^ 2 * |x| * (Real.exp (|x| / 2) / 2) :=
          mul_le_mul_of_nonneg_left hm (by positivity)

/-- **The jump kernel is continuous on the plane.** Away from `x = 0` it is a product of
continuous functions; at `x = 0` it is squeezed to `0` by the Lipschitz bound. -/
theorem continuous_jumpKernel (hcont : Continuous f) (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) :
    Continuous (Function.uncurry (jumpKernel f)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨u₀, x₀⟩
  rcases eq_or_ne x₀ 0 with rfl | hx
  · have h0 : Function.uncurry (jumpKernel f) (u₀, 0) = 0 := by
      simp [jumpKernel, archLevyDensity_zero]
    have hb : Continuous fun p : ℝ × ℝ => L ^ 2 * |p.2| * (Real.exp (|p.2| / 2) / 2) := by
      fun_prop
    have hb0 : Tendsto (fun p : ℝ × ℝ => L ^ 2 * |p.2| * (Real.exp (|p.2| / 2) / 2))
        (𝓝 (u₀, 0)) (𝓝 0) := by
      have h := hb.tendsto (u₀, 0)
      simpa using h
    rw [ContinuousAt, h0]
    exact squeeze_zero_norm (fun p => by
      rw [Real.norm_eq_abs]
      exact abs_jumpKernel_le hL p.1 p.2) hb0
  · have hω : ContinuousAt ω |x₀| :=
      _root_.RHTower.WeilLevyPoleGauss.continuousOn_archLevyDensity.continuousAt
        (Ioi_mem_nhds (abs_pos.mpr hx))
    have h1 : ContinuousAt (fun p : ℝ × ℝ => ω |p.2|) (u₀, x₀) :=
      ContinuousAt.comp (g := ω) (f := fun p : ℝ × ℝ => |p.2|) hω (by fun_prop)
    have h2 : Continuous fun p : ℝ × ℝ => (f p.1 - f (p.1 + p.2)) ^ 2 := by fun_prop
    exact h1.mul h2.continuousAt

theorem continuous_boxKernel (hcont : Continuous f) (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) :
    Continuous (Function.uncurry (boxKernel f)) := by
  have hg : Continuous fun p : ℝ × ℝ => (p.1, p.2 - p.1) := by fun_prop
  refine ((continuous_jumpKernel hcont hL).comp hg).congr fun p => ?_
  exact (boxKernel_eq_jumpKernel f p.1 p.2).symm

end Kernel

/-! ### The primitive of the Lévy density -/

theorem integral_archLevyDensity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, ω x = Ω a - Ω b := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := fun x hx => lt_of_lt_of_le (lt_min ha hb) hx.1
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y => -Ω y) (ω x) x := fun x hx =>
    (_root_.RHTower.WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv (hpos x hx)).fun_neg.congr_deriv
      (neg_neg _)
  have hint : IntervalIntegrable ω volume a b :=
    (_root_.RHTower.WeilLevyPoleGauss.continuousOn_archLevyDensity.mono hpos).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

theorem continuous_archLevyAntideriv_max {g : ℝ → ℝ} (hg : Continuous g) {δ : ℝ} (hδ : 0 < δ) :
    Continuous fun u => Ω (max (g u) δ) :=
  continuous_iff_continuousAt.mpr fun u =>
    ContinuousAt.comp (g := Ω) (f := fun u => max (g u) δ)
      (_root_.RHTower.WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv
        (lt_max_of_lt_right hδ : (0 : ℝ) < max (g u) δ)).continuousAt
      (hg.max continuous_const).continuousAt

theorem continuous_archLevyDensity_max {g : ℝ → ℝ} (hg : Continuous g) {δ : ℝ} (hδ : 0 < δ) :
    Continuous fun u => ω (max (g u) δ) :=
  continuous_iff_continuousAt.mpr fun u =>
    ContinuousAt.comp (g := ω) (f := fun u => max (g u) δ)
      (_root_.RHTower.WeilLevyPoleGauss.continuousOn_archLevyDensity.continuousAt
        (Ioi_mem_nhds (lt_max_of_lt_right hδ : (0 : ℝ) < max (g u) δ)))
      (hg.max continuous_const).continuousAt

/-- **Integration by parts against the Lévy density**, for `φ` vanishing on `(−∞, δ]`. -/
theorem integral_archLevyDensity_mul_primitive {φ : ℝ → ℝ} (hφ : Continuous φ) {δ c : ℝ}
    (hδ : 0 < δ) (hδc : δ ≤ c) (h0 : ∀ v, v ≤ δ → φ v = 0) :
    ∫ x in (0 : ℝ)..c, ω (max x δ) * ∫ v in (0 : ℝ)..x, φ v =
      (∫ u in (0 : ℝ)..c, φ u * Ω (max u δ)) - Ω c * ∫ v in (0 : ℝ)..c, φ v := by
  have hPcont : Continuous fun x => ∫ v in (0 : ℝ)..x, φ v :=
    intervalIntegral.continuous_primitive (fun a b => hφ.intervalIntegrable a b) 0
  have hP0 : ∀ x, 0 ≤ x → x ≤ δ → ∫ v in (0 : ℝ)..x, φ v = 0 := fun x hx0 hx =>
    intervalIntegral_eq_zero_of_eqOn fun v hv => by
      rw [Set.uIcc_of_le hx0] at hv
      exact h0 v (hv.2.trans hx)
  have hL1 : Continuous fun x => ω (max x δ) * ∫ v in (0 : ℝ)..x, φ v :=
    (continuous_archLevyDensity_max continuous_id hδ).mul hPcont
  have hR1 : Continuous fun u => φ u * Ω (max u δ) :=
    hφ.mul (continuous_archLevyAntideriv_max continuous_id hδ)
  have hA : ∫ x in (0 : ℝ)..δ, ω (max x δ) * ∫ v in (0 : ℝ)..x, φ v = 0 :=
    intervalIntegral_eq_zero_of_eqOn fun x hx => by
      rw [Set.uIcc_of_le hδ.le] at hx
      rw [hP0 x hx.1 hx.2, mul_zero]
  have hB : ∫ u in (0 : ℝ)..δ, φ u * Ω (max u δ) = 0 :=
    intervalIntegral_eq_zero_of_eqOn fun u hu => by
      rw [Set.uIcc_of_le hδ.le] at hu
      rw [h0 u hu.2, zero_mul]
  have hpos : ∀ x ∈ Set.uIcc δ c, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hδc] at hx
    exact hδ.trans_le hx.1
  have hmax : ∀ x ∈ Set.uIcc δ c, max x δ = x := fun x hx => by
    rw [Set.uIcc_of_le hδc] at hx
    exact max_eq_left hx.1
  have hC : ∫ x in δ..c, ω (max x δ) * ∫ v in (0 : ℝ)..x, φ v =
      ∫ x in δ..c, (∫ v in (0 : ℝ)..x, φ v) * ω x :=
    intervalIntegral.integral_congr fun x hx => by
      show ω (max x δ) * ∫ v in (0 : ℝ)..x, φ v = (∫ v in (0 : ℝ)..x, φ v) * ω x
      rw [hmax x hx, mul_comm]
  have hD : ∫ u in δ..c, φ u * Ω (max u δ) = ∫ u in δ..c, φ u * Ω u :=
    intervalIntegral.integral_congr fun u hu => by
      show φ u * Ω (max u δ) = φ u * Ω u
      rw [hmax u hu]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := δ) (b := c)
    (u := fun x => ∫ v in (0 : ℝ)..x, φ v) (u' := φ) (v := fun y => -Ω y) (v' := ω)
    (fun x _ => (hφ.integral_hasStrictDerivAt 0 x).hasDerivAt)
    (fun x hx =>
      (_root_.RHTower.WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv (hpos x hx)).fun_neg.congr_deriv
        (neg_neg _))
    (hφ.intervalIntegrable _ _)
    (_root_.RHTower.WeilLevyPoleGauss.continuousOn_archLevyDensity.mono hpos).intervalIntegrable
  beta_reduce at hparts
  have hE : ∫ x in δ..c, φ x * -Ω x = -∫ x in δ..c, φ x * Ω x := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    show φ x * -Ω x = -(φ x * Ω x)
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hL1.intervalIntegrable 0 δ)
      (hL1.intervalIntegrable δ c),
    ← intervalIntegral.integral_add_adjacent_intervals (hR1.intervalIntegrable 0 δ)
      (hR1.intervalIntegrable δ c), hA, hB, hC, hD, hparts, hE, hP0 δ hδ.le le_rfl]
  ring

/-! ### Rows: the jumps out of a point of the window -/

theorem integral_jumpKernel_mid (f : ℝ → ℝ) (c u : ℝ) :
    ∫ x in (-u)..(c - u), jumpKernel f u x = ∫ v in (0 : ℝ)..c, boxKernel f u v := by
  have h := intervalIntegral.integral_comp_add_left (a := -u) (b := c - u)
    (fun v => boxKernel f u v) u
  rw [show u + -u = 0 by ring, show u + (c - u) = c by ring] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ => ?_
  show jumpKernel f u x = boxKernel f u (u + x)
  rw [boxKernel_eq_jumpKernel, add_sub_cancel_left]

section Window

variable {f : ℝ → ℝ} {R : ℕ} {B L δ c : ℝ}

theorem ne_zero_imp_mem_window (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) {u : ℝ}
    (hfu : f u ≠ 0) : δ < u ∧ u < c - δ := by
  constructor
  · by_contra h
    exact hfu (hsupp u (Or.inl (not_lt.mp h)))
  · by_contra h
    exact hfu (hsupp u (Or.inr (not_lt.mp h)))

/-- The jumps that leave the window to the right. -/
theorem integral_jumpKernel_right (hδ : 0 < δ) (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0)
    {u : ℝ} (hu0 : 0 ≤ u) (huc : u ≤ c) :
    ∫ x in (c - u)..c, jumpKernel f u x = f u ^ 2 * (Ω (max (c - u) δ) - Ω c) := by
  have hcongr : ∫ x in (c - u)..c, jumpKernel f u x = ∫ x in (c - u)..c, f u ^ 2 * ω x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hfx : f (u + x) = 0 := hsupp _ (Or.inr (by linarith [hx.1]))
    show jumpKernel f u x = f u ^ 2 * ω x
    rw [jumpKernel, hfx, sub_zero, abs_of_nonneg (by linarith [hx.1]), mul_comm]
  rw [hcongr, intervalIntegral.integral_const_mul]
  by_cases hfu : f u = 0
  · rw [hfu]
    ring
  · obtain ⟨h1, h2⟩ := ne_zero_imp_mem_window hsupp hfu
    rw [integral_archLevyDensity (by linarith) (by linarith), max_eq_left (by linarith)]

/-- The jumps that leave the window to the left. -/
theorem integral_jumpKernel_left (hδ : 0 < δ) (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0)
    {u : ℝ} (hu0 : 0 ≤ u) (huc : u ≤ c) :
    ∫ x in (-c)..(-u), jumpKernel f u x = f u ^ 2 * (Ω (max u δ) - Ω c) := by
  have hcongr : ∫ x in (-c)..(-u), jumpKernel f u x = ∫ x in (-c)..(-u), f u ^ 2 * ω (-x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hfx : f (u + x) = 0 := hsupp _ (Or.inl (by linarith [hx.2]))
    show jumpKernel f u x = f u ^ 2 * ω (-x)
    rw [jumpKernel, hfx, sub_zero, abs_of_nonpos (by linarith [hx.2]), mul_comm]
  rw [hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_neg (fun x => ω x), neg_neg, neg_neg]
  by_cases hfu : f u = 0
  · rw [hfu]
    ring
  · obtain ⟨h1, h2⟩ := ne_zero_imp_mem_window hsupp hfu
    rw [integral_archLevyDensity (by linarith) (by linarith), max_eq_left h1.le]

/-- **The jumps out of a point of the window**: those that stay, and the two tails. -/
theorem integral_jumpKernel_row (hcont : Continuous f)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hδ : 0 < δ)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) {u : ℝ} (hu0 : 0 ≤ u) (huc : u ≤ c) :
    ∫ x in (-c)..c, jumpKernel f u x = (∫ v in (0 : ℝ)..c, boxKernel f u v) +
      f u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ) - 2 * Ω c) := by
  have hq : Continuous fun x => jumpKernel f u x :=
    (continuous_jumpKernel hcont hL).comp (continuous_const.prodMk continuous_id)
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun x => jumpKernel f u x) volume a b := fun a b =>
    hq.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-c) (-u)) (hi (-u) c),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-u) (c - u)) (hi (c - u) c),
    integral_jumpKernel_mid, integral_jumpKernel_right hδ hsupp hu0 huc,
    integral_jumpKernel_left hδ hsupp hu0 huc]
  ring

/-! ### Columns: the jumps of a given length -/

theorem packetAutocorr_eq_integral_window (hδ : 0 < δ)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) (x : ℝ) :
    packetAutocorr f x = ∫ u in (0 : ℝ)..c, f u * f (u + x) := by
  rw [packetAutocorr]
  refine (intervalIntegral.integral_eq_integral_of_support_subset fun u hu => ?_).symm
  have hfu : f u ≠ 0 := fun h0 => hu (by
    show f u * f (u + x) = 0
    rw [h0, zero_mul])
  obtain ⟨h1, h2⟩ := ne_zero_imp_mem_window hsupp hfu
  exact ⟨by linarith, by linarith⟩

theorem packetAutocorr_zero_eq_integral_window (hδ : 0 < δ)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) :
    packetAutocorr f 0 = ∫ u in (0 : ℝ)..c, f u ^ 2 := by
  rw [packetAutocorr_eq_integral_window hδ hsupp 0]
  refine intervalIntegral.integral_congr fun u _ => ?_
  show f u * f (u + 0) = f u ^ 2
  rw [add_zero, sq]

theorem packetAutocorr_eq_zero_of_window (hδ : 0 < δ)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) {x : ℝ} (hx : c ≤ x) :
    packetAutocorr f x = 0 := by
  have h0 : ∀ u : ℝ, f u * f (u + x) = 0 := by
    intro u
    by_cases hfu : f u = 0
    · rw [hfu, zero_mul]
    · obtain ⟨h1, h2⟩ := ne_zero_imp_mem_window hsupp hfu
      rw [hsupp (u + x) (Or.inr (by linarith)), mul_zero]
  simp [packetAutocorr, h0]

theorem packetAutocorr_neg (f : ℝ → ℝ) (x : ℝ) : packetAutocorr f (-x) = packetAutocorr f x := by
  rw [packetAutocorr, packetAutocorr,
    ← integral_add_right_eq_self (fun u => f u * f (u + -x)) x]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show f (u + x) * f (u + x + -x) = f u * f (u + x)
  rw [add_neg_cancel_right, mul_comm]

/-- **The jumps of a given length**, integrated over the window. -/
theorem integral_jumpKernel_col (hcont : Continuous f) (hδ : 0 < δ)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) (x : ℝ) :
    ∫ u in (0 : ℝ)..c, jumpKernel f u x =
      ω |x| * (packetAutocorr f 0 - 2 * packetAutocorr f x + ∫ v in x..(c + x), f v ^ 2) := by
  have hshift : Continuous fun u => f (u + x) := hcont.comp (continuous_id.add continuous_const)
  have i1 : IntervalIntegrable (fun u => f u ^ 2) volume 0 c :=
    (hcont.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun u => 2 * (f u * f (u + x))) volume 0 c :=
    (continuous_const.mul (hcont.mul hshift)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun u => f (u + x) ^ 2) volume 0 c :=
    (hshift.pow 2).intervalIntegrable _ _
  have i12 : IntervalIntegrable (fun u => f u ^ 2 - 2 * (f u * f (u + x))) volume 0 c :=
    i1.sub i2
  have hfun : ∫ u in (0 : ℝ)..c, jumpKernel f u x =
      ∫ u in (0 : ℝ)..c, ω |x| * (f u ^ 2 - 2 * (f u * f (u + x)) + f (u + x) ^ 2) :=
    intervalIntegral.integral_congr fun u _ => by
      show jumpKernel f u x = ω |x| * (f u ^ 2 - 2 * (f u * f (u + x)) + f (u + x) ^ 2)
      rw [jumpKernel]
      ring
  have h3 := intervalIntegral.integral_comp_add_right (a := 0) (b := c) (fun v => f v ^ 2) x
  rw [zero_add] at h3
  rw [hfun, intervalIntegral.integral_const_mul, intervalIntegral.integral_add i12 i3,
    intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    ← packetAutocorr_zero_eq_integral_window hδ hsupp,
    ← packetAutocorr_eq_integral_window hδ hsupp x, h3]

/-- The mass of the packet in the window shifted to the right by `x ≥ 0`. -/
theorem integral_sq_shift_right (hcont : Continuous f) (hδ : 0 < δ)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) {x : ℝ} (hx : 0 ≤ x) :
    ∫ v in x..(c + x), f v ^ 2 = packetAutocorr f 0 - ∫ v in (0 : ℝ)..x, f v ^ 2 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun v => f v ^ 2) volume a b := fun a b =>
    (hcont.pow 2).intervalIntegrable a b
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 x) (hi x (c + x))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c (c + x))
  have h0 : ∫ v in c..(c + x), f v ^ 2 = 0 :=
    intervalIntegral_eq_zero_of_eqOn fun v hv => by
      rw [Set.uIcc_of_le (by linarith)] at hv
      rw [hsupp v (Or.inr (by linarith [hv.1])), zero_pow two_ne_zero]
  rw [packetAutocorr_zero_eq_integral_window hδ hsupp (c := c)]
  linarith

/-- The mass of the packet in the window shifted to the left by `y ≥ 0`. -/
theorem integral_sq_shift_left (hcont : Continuous f) (hδ : 0 < δ)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) {y : ℝ} (hy : 0 ≤ y) :
    ∫ v in (-y)..(c + -y), f v ^ 2 =
      packetAutocorr f 0 - ∫ w in (0 : ℝ)..y, f (c - w) ^ 2 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun v => f v ^ 2) volume a b := fun a b =>
    (hcont.pow 2).intervalIntegrable a b
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hi (-y) 0) (hi 0 (c + -y))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (c + -y)) (hi (c + -y) c)
  have h0 : ∫ v in (-y)..(0 : ℝ), f v ^ 2 = 0 :=
    intervalIntegral_eq_zero_of_eqOn fun v hv => by
      rw [Set.uIcc_of_le (by linarith)] at hv
      rw [hsupp v (Or.inl (by linarith [hv.2])), zero_pow two_ne_zero]
  have h3 := intervalIntegral.integral_comp_sub_left (a := 0) (b := y) (fun v => f v ^ 2) c
  rw [sub_zero, sub_eq_add_neg c y] at h3
  rw [packetAutocorr_zero_eq_integral_window hδ hsupp (c := c), h3]
  linarith

/-- A primitive that vanishes on `[0, δ]` does not see the pole of the density. -/
theorem archLevyDensity_mul_primitive_eq {φ : ℝ → ℝ} (h0 : ∀ v, v ≤ δ → φ v = 0)
    {x : ℝ} (hx : 0 ≤ x) :
    ω x * ∫ v in (0 : ℝ)..x, φ v = ω (max x δ) * ∫ v in (0 : ℝ)..x, φ v := by
  rcases le_or_gt x δ with h | h
  · have hz : ∫ v in (0 : ℝ)..x, φ v = 0 :=
      intervalIntegral_eq_zero_of_eqOn fun v hv => by
        rw [Set.uIcc_of_le hx] at hv
        exact h0 v (hv.2.trans h)
    rw [hz, mul_zero, mul_zero]
  · rw [max_eq_left h.le]

/-- The column of a jump to the right. -/
theorem integral_jumpKernel_col_right (hcont : Continuous f) (hδ : 0 < δ)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) {x : ℝ} (hx : 0 ≤ x) :
    ∫ u in (0 : ℝ)..c, jumpKernel f u x =
      levyJump f x - ω (max x δ) * ∫ v in (0 : ℝ)..x, f v ^ 2 := by
  have hφ : ∀ v, v ≤ δ → (fun v => f v ^ 2) v = 0 := fun v hv => by
    show f v ^ 2 = 0
    rw [hsupp v (Or.inl hv), zero_pow two_ne_zero]
  rw [integral_jumpKernel_col hcont hδ hsupp, integral_sq_shift_right hcont hδ hsupp hx,
    abs_of_nonneg hx, ← archLevyDensity_mul_primitive_eq hφ hx, levyJump]
  ring

/-- The column of a jump to the left. -/
theorem integral_jumpKernel_col_left (hcont : Continuous f) (hδ : 0 < δ)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) {y : ℝ} (hy : 0 ≤ y) :
    ∫ u in (0 : ℝ)..c, jumpKernel f u (-y) =
      levyJump f y - ω (max y δ) * ∫ w in (0 : ℝ)..y, f (c - w) ^ 2 := by
  have hφ : ∀ w, w ≤ δ → (fun w => f (c - w) ^ 2) w = 0 := fun w hw => by
    show f (c - w) ^ 2 = 0
    rw [hsupp (c - w) (Or.inr (by linarith)), zero_pow two_ne_zero]
  rw [integral_jumpKernel_col hcont hδ hsupp, integral_sq_shift_left hcont hδ hsupp hy,
    abs_neg, abs_of_nonneg hy, packetAutocorr_neg,
    ← archLevyDensity_mul_primitive_eq hφ hy, levyJump]
  ring

/-! ### The identity -/

theorem integrableOn_levyJump_Ioc (hcont : Continuous f)
    (hsuppR : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (X : ℝ) :
    IntegrableOn (levyJump f) (Set.Ioc 0 X) := by
  refine Integrable.mono' (integrableOn_const
      (C := 2 * R * B * L * Real.exp (X / 2)) measure_Ioc_lt_top.ne)
    (((continuousOn_levyJump hcont hsuppR hB hL).mono fun x hx => hx.1).aestronglyMeasurable
      measurableSet_Ioc) ?_
  exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
    rw [Real.norm_eq_abs]
    exact abs_levyJump_le hcont hsuppR hB hL hx.1 hx.2

/-- The jump integral, split at the width of the window. -/
theorem integral_levyJump_Ioi_window (hcont : Continuous f)
    (hsuppR : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hδ : 0 < δ) (hδc : δ ≤ c)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) :
    ∫ x in Set.Ioi 0, levyJump f x =
      (∫ x in (0 : ℝ)..c, levyJump f x) + 2 * packetAutocorr f 0 * Ω c := by
  have hc : 0 < c := hδ.trans_le hδc
  have hI1 := integrableOn_levyJump_Ioc hcont hsuppR hB hL c
  have heq : Set.EqOn (levyJump f) (fun x => 2 * packetAutocorr f 0 * ω x) (Set.Ioi c) :=
    fun x hx => by
      show levyJump f x = 2 * packetAutocorr f 0 * ω x
      rw [levyJump, packetAutocorr_eq_zero_of_window hδ hsupp (le_of_lt hx)]
      ring
  have hI0 : IntegrableOn (fun x => 2 * packetAutocorr f 0 * ω x) (Set.Ioi c) :=
    Integrable.const_mul (_root_.RHTower.WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hc) _
  have hI2 : IntegrableOn (levyJump f) (Set.Ioi c) := hI0.congr_fun heq.symm measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hc.le, setIntegral_union Set.Ioc_disjoint_Ioi_same
    measurableSet_Ioi hI1 hI2, intervalIntegral.integral_of_le hc.le,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
    _root_.RHTower.WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hc]

/-- **The jump form splits into a window and its tails.** For a packet vanishing outside
`(δ, c − δ)`, the jump integral is half the Dirichlet integral of the kernel over the window
`[0, c]²` plus the mass against the rates `Ω(c − u) + Ω(u)` of the jumps that leave the window. -/
theorem integral_levyJump_eq_window (hcont : Continuous f)
    (hsuppR : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hδ : 0 < δ) (hδc : δ ≤ c)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) :
    ∫ x in Set.Ioi 0, levyJump f x =
      (∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, boxKernel f u v) / 2 +
        ∫ u in (0 : ℝ)..c, f u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ)) := by
  have hc : 0 < c := hδ.trans_le hδc
  have hQ := continuous_jumpKernel hcont hL
  have hmass := packetAutocorr_zero_eq_integral_window (f := f) (c := c) hδ hsupp
  have hsq : Continuous fun u => f u ^ 2 := hcont.pow 2
  have hΩ1 : Continuous fun u : ℝ => Ω (max (c - u) δ) :=
    continuous_archLevyAntideriv_max (continuous_const.sub continuous_id) hδ
  have hΩ2 : Continuous fun u : ℝ => Ω (max u δ) :=
    continuous_archLevyAntideriv_max continuous_id hδ
  have c1 : Continuous fun u => f u ^ 2 * Ω (max (c - u) δ) := hsq.mul hΩ1
  have c2 : Continuous fun u => f u ^ 2 * Ω (max u δ) := hsq.mul hΩ2
  -- the tails, split
  have hTp : ∫ u in (0 : ℝ)..c, f u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ)) =
      (∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max (c - u) δ)) +
        ∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max u δ) := by
    rw [← intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show f u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ)) =
      f u ^ 2 * Ω (max (c - u) δ) + f u ^ 2 * Ω (max u δ)
    ring
  -- rows
  have hbox : Continuous fun u => ∫ v in (0 : ℝ)..c, boxKernel f u v :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_boxKernel hcont hL) 0 c
  have c3 : Continuous fun u => 2 * Ω c * f u ^ 2 := continuous_const.mul hsq
  have c12 : Continuous fun u => f u ^ 2 * Ω (max (c - u) δ) + f u ^ 2 * Ω (max u δ) :=
    c1.add c2
  have c123 : Continuous fun u =>
      f u ^ 2 * Ω (max (c - u) δ) + f u ^ 2 * Ω (max u δ) - 2 * Ω c * f u ^ 2 := c12.sub c3
  have hrows : ∫ u in (0 : ℝ)..c, ∫ x in (-c)..c, jumpKernel f u x =
      (∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, boxKernel f u v) +
        ((∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max (c - u) δ)) +
          (∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max u δ)) - 2 * Ω c * packetAutocorr f 0) := by
    have h1 : ∫ u in (0 : ℝ)..c, ∫ x in (-c)..c, jumpKernel f u x =
        ∫ u in (0 : ℝ)..c, ((∫ v in (0 : ℝ)..c, boxKernel f u v) +
          (f u ^ 2 * Ω (max (c - u) δ) + f u ^ 2 * Ω (max u δ) - 2 * Ω c * f u ^ 2)) :=
      intervalIntegral.integral_congr fun u hu => by
        rw [Set.uIcc_of_le hc.le] at hu
        show ∫ x in (-c)..c, jumpKernel f u x = _
        rw [integral_jumpKernel_row hcont hL hδ hsupp hu.1 hu.2]
        ring
    rw [h1, intervalIntegral.integral_add (hbox.intervalIntegrable _ _)
        (c123.intervalIntegrable _ _),
      intervalIntegral.integral_sub (c12.intervalIntegrable _ _) (c3.intervalIntegrable _ _),
      intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, ← hmass]
  -- columns
  have hswap := _root_.RHTower.interval_integral_swap_of_continuous (a := 0) (b := c)
    (c := -c) (d := c) hc.le (by linarith) (F := fun u x => jumpKernel f u x) hQ
  have hcol : Continuous fun x => ∫ u in (0 : ℝ)..c, jumpKernel f u x :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x u => jumpKernel f u x) (hQ.comp continuous_swap) 0 c
  have hJ : IntervalIntegrable (levyJump f) volume 0 c :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le).mpr
      (integrableOn_levyJump_Ioc hcont hsuppR hB hL c)
  -- the two primitives
  have hφ1 : Continuous fun v => f v ^ 2 := hsq
  have hφ2 : Continuous fun w => f (c - w) ^ 2 :=
    (hcont.comp (continuous_const.sub continuous_id)).pow 2
  have hK1c : Continuous fun x => ω (max x δ) * ∫ v in (0 : ℝ)..x, f v ^ 2 :=
    (continuous_archLevyDensity_max continuous_id hδ).mul
      (intervalIntegral.continuous_primitive (fun a b => hφ1.intervalIntegrable a b) 0)
  have hK2c : Continuous fun y => ω (max y δ) * ∫ w in (0 : ℝ)..y, f (c - w) ^ 2 :=
    (continuous_archLevyDensity_max continuous_id hδ).mul
      (intervalIntegral.continuous_primitive (fun a b => hφ2.intervalIntegrable a b) 0)
  have hK1 := integral_archLevyDensity_mul_primitive hφ1 hδ hδc (fun v hv => by
    show f v ^ 2 = 0
    rw [hsupp v (Or.inl hv), zero_pow two_ne_zero])
  have hK2 := integral_archLevyDensity_mul_primitive hφ2 hδ hδc (fun w hw => by
    show f (c - w) ^ 2 = 0
    rw [hsupp (c - w) (Or.inr (by linarith)), zero_pow two_ne_zero])
  -- reflect the second primitive
  have hrefl1 := intervalIntegral.integral_comp_sub_left (a := 0) (b := c)
    (fun u => f u ^ 2 * Ω (max (c - u) δ)) c
  have hrefl2 := intervalIntegral.integral_comp_sub_left (a := 0) (b := c) (fun u => f u ^ 2) c
  simp only [sub_self, sub_zero, sub_sub_cancel] at hrefl1 hrefl2
  rw [hrefl1, hrefl2, ← hmass] at hK2
  rw [← hmass] at hK1
  -- the two halves of the columns
  have hright : ∫ x in (0 : ℝ)..c, ∫ u in (0 : ℝ)..c, jumpKernel f u x =
      (∫ x in (0 : ℝ)..c, levyJump f x) -
        ∫ x in (0 : ℝ)..c, ω (max x δ) * ∫ v in (0 : ℝ)..x, f v ^ 2 := by
    rw [← intervalIntegral.integral_sub hJ (hK1c.intervalIntegrable (μ := volume) 0 c)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hc.le] at hx
    exact integral_jumpKernel_col_right hcont hδ hsupp hx.1
  have hleft : ∫ x in (-c)..(0 : ℝ), ∫ u in (0 : ℝ)..c, jumpKernel f u x =
      (∫ y in (0 : ℝ)..c, levyJump f y) -
        ∫ y in (0 : ℝ)..c, ω (max y δ) * ∫ w in (0 : ℝ)..y, f (c - w) ^ 2 := by
    have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := c)
      (fun x => ∫ u in (0 : ℝ)..c, jumpKernel f u x)
    rw [neg_zero] at hneg
    rw [← hneg, ← intervalIntegral.integral_sub hJ (hK2c.intervalIntegrable (μ := volume) 0 c)]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hc.le] at hy
    exact integral_jumpKernel_col_left hcont hδ hsupp hy.1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcol.intervalIntegrable (μ := volume) (-c) 0) (hcol.intervalIntegrable (μ := volume) 0 c)
  have hE := integral_levyJump_Ioi_window hcont hsuppR hB hL hδ hδc hsupp
  rw [hE, hTp]
  linarith
