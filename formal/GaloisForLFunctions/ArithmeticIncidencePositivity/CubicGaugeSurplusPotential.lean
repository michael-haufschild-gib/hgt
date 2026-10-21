import GaloisForLFunctions.ArithmeticIncidencePositivity.FoldedSurplusGroundStatePotential

/-!
# The surplus potential of a cubic gauge

For a cubic gauge `h(y) = a₀ + a₁ y + a₂ y² + a₃ y³` the surplus potential `U_h` of
`FoldedSurplusGroundStatePotential` has an explicit lower bound. Split the Lévy density as
`ω(t) = 1/(2t) + ρ(t)`; from `ω(t) = 1/(4 sinh(t/2)) + 1/(4 cosh(t/2))`
(`archLevyDensity_eq_sinh_add_cosh`) one gets `1/4 − t/16 − t²/32 ≤ ρ(t) ≤ 1/4` for every `t > 0`
(`archLevyDensity_le_inv`, `inv_le_archLevyDensity`). The principal kernel
`k₀(x, y) = 1/(2|x − y|) − 1/(2(x + y))` integrates against the differences of `h` in closed form
(`integral_principalSurplus_cubicGauge`):

    ∫_0^r k₀(x, y)(h(x) − h(y)) dy = a₁ x (1 − ℓ) + a₂ (3x²/2 − r x) + a₃ (11x³/6 − r² x/2 − x³ ℓ),

`ℓ = log(x + r) − log x`: the odd part `a₁ y + a₃ y³` of `h` meets the reflected pole `1/(x + y)` and
produces the logarithm, the even part only polynomials. The remainder `ρ(|x − y|) − ρ(x + y)` costs at
most `L ∫_0^r ((x + y)/16 + (x + y)²/32)|x − y| dy` for an `L`-Lipschitz `h`
(`mul_surplusPotential_cubicGauge_ge`).
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The Lévy density near the origin -/

/-- `ω(t) = 1/(4 sinh(t/2)) + 1/(4 cosh(t/2))`. -/
theorem archLevyDensity_eq_sinh_add_cosh {t : ℝ} (ht : 0 < t) :
    archLevyDensity t = 1 / (4 * Real.sinh (t / 2)) + 1 / (4 * Real.cosh (t / 2)) := by
  set v := Real.exp (-t / 2) with hvdef
  have hv0 : 0 < v := Real.exp_pos _
  have hv1 : v < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hinv : Real.exp (t / 2) = v⁻¹ := by
    rw [hvdef, ← Real.exp_neg]; ring_nf
  have e2 : Real.exp (-2 * t) = v ^ 4 := by
    rw [hvdef, ← Real.exp_nat_mul]; ring_nf
  have hs : Real.sinh (t / 2) = (1 - v ^ 2) / (2 * v) := by
    rw [Real.sinh_eq, hinv, show -(t / 2) = -t / 2 by ring, ← hvdef]
    field_simp
  have hc : Real.cosh (t / 2) = (1 + v ^ 2) / (2 * v) := by
    rw [Real.cosh_eq, hinv, show -(t / 2) = -t / 2 by ring, ← hvdef]
    field_simp
  have h1 : 1 - v ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 + v ^ 2 ≠ 0 := by positivity
  have h3 : 1 - v ^ 4 ≠ 0 := by nlinarith [pow_lt_one₀ hv0.le hv1 (show (4 : ℕ) ≠ 0 by norm_num)]
  unfold archLevyDensity
  rw [← hvdef, e2, hs, hc]
  field_simp
  ring

/-- `ω(t) ≤ 1/(2t) + 1/4` for `t > 0`. -/
theorem archLevyDensity_le_inv {t : ℝ} (ht : 0 < t) : archLevyDensity t ≤ 1 / (2 * t) + 1 / 4 := by
  rw [archLevyDensity_eq_sinh_add_cosh ht]
  have hs : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have hc : 1 ≤ Real.cosh (t / 2) := Real.one_le_cosh _
  have h1 : 1 / (4 * Real.sinh (t / 2)) ≤ 1 / (2 * t) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  have h2 : 1 / (4 * Real.cosh (t / 2)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

/-- `ω(t) ≥ 1/(2t) + 1/4 − t/16 − t²/32` for `t > 0`. -/
theorem inv_le_archLevyDensity {t : ℝ} (ht : 0 < t) :
    1 / (2 * t) + 1 / 4 - t / 16 - t ^ 2 / 32 ≤ archLevyDensity t := by
  rw [archLevyDensity_eq_sinh_add_cosh ht]
  have hz : 0 ≤ t / 2 := by linarith
  have hs := sinh_le_mul_cosh hz
  have hs0 : 0 < Real.sinh (t / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hc0 : 0 < Real.cosh (t / 2) := Real.cosh_pos _
  -- `1/cosh z ≥ 1 − z²/2`
  have hic : 1 - (t / 2) ^ 2 / 2 ≤ 1 / Real.cosh (t / 2) := by
    have h1 := Real.cosh_le_exp_half_sq (t / 2)
    have h2 : 1 - (t / 2) ^ 2 / 2 ≤ Real.exp (-((t / 2) ^ 2 / 2)) := by
      linarith [Real.add_one_le_exp (-((t / 2) ^ 2 / 2))]
    have h3 : Real.exp (-((t / 2) ^ 2 / 2)) * Real.exp ((t / 2) ^ 2 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    rw [le_div_iff₀ hc0]
    have h4 : 0 ≤ Real.exp (-((t / 2) ^ 2 / 2)) := (Real.exp_pos _).le
    by_cases h5 : 0 ≤ 1 - (t / 2) ^ 2 / 2
    · nlinarith [mul_le_mul_of_nonneg_left h1 h5, mul_le_mul_of_nonneg_left h1 h4]
    · nlinarith [Real.one_le_cosh (t / 2)]
  have h1 : 1 / (2 * t) * (1 - (t / 2) ^ 2 / 2) ≤ 1 / (4 * Real.sinh (t / 2)) := by
    have : 1 / (2 * t) * (1 / Real.cosh (t / 2)) ≤ 1 / (4 * Real.sinh (t / 2)) := by
      rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact (mul_le_mul_of_nonneg_left hic (by positivity)).trans this
  have h2 : 1 / 4 * (1 - (t / 2) ^ 2 / 2) ≤ 1 / (4 * Real.cosh (t / 2)) := by
    have : 1 / (4 * Real.cosh (t / 2)) = 1 / 4 * (1 / Real.cosh (t / 2)) := by
      rw [div_mul_div_comm, one_mul]
    rw [this]; exact mul_le_mul_of_nonneg_left hic (by norm_num)
  have e : 1 / (2 * t) * (1 - (t / 2) ^ 2 / 2) + 1 / 4 * (1 - (t / 2) ^ 2 / 2) =
      1 / (2 * t) + 1 / 4 - t / 16 - t ^ 2 / 32 := by field_simp; ring
  linarith

/-- The surplus kernel is the principal kernel up to `(x + y)/16 + (x + y)²/32`. -/
theorem abs_surplusKernel_sub_principal_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    |surplusKernel x y - (1 / (2 * |x - y|) - 1 / (2 * (x + y)))| ≤
      (x + y) / 16 + (x + y) ^ 2 / 32 := by
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hs : 0 < x + y := by linarith
  have hdle : |x - y| ≤ x + y := by rw [abs_le]; constructor <;> linarith
  have a1 := archLevyDensity_le_inv hd
  have a2 := inv_le_archLevyDensity hd
  have b1 := archLevyDensity_le_inv hs
  have b2 := inv_le_archLevyDensity hs
  have hsq : |x - y| ^ 2 ≤ (x + y) ^ 2 := pow_le_pow_left₀ hd.le hdle 2
  unfold surplusKernel
  rw [abs_le]; constructor <;> nlinarith

/-! ### The cubic gauge and its closed form -/

/-- The cubic gauge `h(y) = a₀ + a₁ y + a₂ y² + a₃ y³`. -/
def cubicGauge (a₀ a₁ a₂ a₃ y : ℝ) : ℝ := a₀ + a₁ * y + a₂ * y ^ 2 + a₃ * y ^ 3

/-- The principal surplus of a cubic gauge,
`a₁ x (1 − ℓ) + a₂ (3x²/2 − r x) + a₃ (11x³/6 − r² x/2 − x³ ℓ)`, `ℓ = log(x + r) − log x`. -/
def cubicSurplusMain (a₁ a₂ a₃ r x : ℝ) : ℝ :=
  a₁ * x * (1 - (Real.log (x + r) - Real.log x)) + a₂ * (3 / 2 * x ^ 2 - r * x) +
    a₃ * (11 / 6 * x ^ 3 - r ^ 2 * x / 2 - x ^ 3 * (Real.log (x + r) - Real.log x))

/-- The remainder bound `∫_0^r ((x + y)/16 + (x + y)²/32)|x − y| dy`. -/
def surplusRemainder (r x : ℝ) : ℝ :=
  (4 / 3 * x ^ 3 - r * x ^ 2 + r ^ 3 / 3) / 16 +
    (11 / 6 * x ^ 4 - r * x ^ 3 - r ^ 2 * x ^ 2 / 2 + r ^ 3 * x / 3 + r ^ 4 / 4) / 32

theorem hasDerivAt_quartic (c₀ c₁ c₂ c₃ c₄ y : ℝ) :
    HasDerivAt (fun y => c₀ + c₁ * y + c₂ * y ^ 2 + c₃ * y ^ 3 + c₄ * y ^ 4)
      (c₁ + 2 * c₂ * y + 3 * c₃ * y ^ 2 + 4 * c₄ * y ^ 3) y := by
  have h1 := hasDerivAt_id' y
  have h2 := hasDerivAt_pow 2 y
  have h3 := hasDerivAt_pow 3 y
  have h4 := hasDerivAt_pow 4 y
  have := ((((hasDerivAt_const y c₀).add (h1.const_mul c₁)).add (h2.const_mul c₂)).add
    (h3.const_mul c₃)).add (h4.const_mul c₄)
  refine this.congr_deriv ?_
  norm_num
  ring

/-- A function given by a quartic minus `K log(x + y)` on an interval `[a, b] ⊆ (−x, ∞)`
integrates its derivative. -/
theorem integral_quartic_sub_log {x a b c₀ c₁ c₂ c₃ c₄ K : ℝ} (hab : a ≤ b) (ha : 0 < x + a) :
    (∫ y in a..b, (c₁ + 2 * c₂ * y + 3 * c₃ * y ^ 2 + 4 * c₄ * y ^ 3 - K / (x + y))) =
      (c₀ + c₁ * b + c₂ * b ^ 2 + c₃ * b ^ 3 + c₄ * b ^ 4 - K * Real.log (x + b)) -
        (c₀ + c₁ * a + c₂ * a ^ 2 + c₃ * a ^ 3 + c₄ * a ^ 4 - K * Real.log (x + a)) := by
  have hpos : ∀ y ∈ uIcc a b, 0 < x + y := fun y hy => by
    rw [uIcc_of_le hab] at hy; linarith [hy.1]
  refine integral_eq_sub_of_hasDerivAt
    (f := fun y => c₀ + c₁ * y + c₂ * y ^ 2 + c₃ * y ^ 3 + c₄ * y ^ 4 - K * Real.log (x + y))
    (fun y hy => ?_) ?_
  · have hl := ((hasDerivAt_id' y).const_add x).log (hpos y hy).ne'
    refine ((hasDerivAt_quartic c₀ c₁ c₂ c₃ c₄ y).sub (hl.const_mul K)).congr_deriv ?_
    field_simp
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.sub (by fun_prop) (ContinuousOn.div continuousOn_const (by fun_prop)
      fun y hy => (hpos y hy).ne')

/-- **The principal surplus of a cubic gauge in closed form.** For `0 < x ≤ r`,
`∫_{(0, r]} k₀(x, y)(h(x) − h(y)) dy = cubicSurplusMain a₁ a₂ a₃ r x`; on `(0, x)` the integrand is
`a₁ + a₂ y + a₃(x² + y²) − (a₁ x + a₃ x³)/(x + y)`, on `(x, r)` it is
`−a₂ x − a₃ x y − (a₁ x + a₃ x³)/(x + y)`. -/
theorem integral_principalSurplus_cubicGauge (a₀ a₁ a₂ a₃ : ℝ) {r x : ℝ} (hx : 0 < x)
    (hxr : x ≤ r) :
    IntegrableOn (fun y => (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
        (cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y)) (Ioc 0 r) ∧
      (∫ y in Ioc 0 r, (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
        (cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y)) = cubicSurplusMain a₁ a₂ a₃ r x := by
  set g := fun y => (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
    (cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y) with hg
  have hg1 : ∀ y ∈ Ioo 0 x, g y = (a₁ + a₃ * x ^ 2) + 2 * (a₂ / 2) * y + 3 * (a₃ / 3) * y ^ 2 +
      4 * 0 * y ^ 3 - (a₁ * x + a₃ * x ^ 3) / (x + y) := by
    intro y hy
    have h1 : |x - y| = x - y := abs_of_pos (by linarith [hy.2])
    have h2 : x - y ≠ 0 := by linarith [hy.2]
    have h3 : x + y ≠ 0 := by linarith [hy.1]
    simp only [hg, cubicGauge, h1]
    field_simp
    ring
  have hg2 : ∀ y ∈ Ioo x r, g y = (-a₂ * x) + 2 * (-a₃ * x / 2) * y + 3 * 0 * y ^ 2 +
      4 * 0 * y ^ 3 - (a₁ * x + a₃ * x ^ 3) / (x + y) := by
    intro y hy
    have h1 : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_pos (by linarith [hy.1])
    have h2 : y - x ≠ 0 := by linarith [hy.1]
    have h3 : x + y ≠ 0 := by linarith [hy.1]
    simp only [hg, cubicGauge, h1]
    field_simp
    ring
  have hc1 : ContinuousOn (fun y => (a₁ + a₃ * x ^ 2) + 2 * (a₂ / 2) * y + 3 * (a₃ / 3) * y ^ 2 +
      4 * 0 * y ^ 3 - (a₁ * x + a₃ * x ^ 3) / (x + y)) (Icc 0 x) :=
    ContinuousOn.sub (by fun_prop) (ContinuousOn.div continuousOn_const (by fun_prop)
      fun y hy => by linarith [hy.1])
  have hc2 : ContinuousOn (fun y => (-a₂ * x) + 2 * (-a₃ * x / 2) * y + 3 * 0 * y ^ 2 +
      4 * 0 * y ^ 3 - (a₁ * x + a₃ * x ^ 3) / (x + y)) (Icc x r) :=
    ContinuousOn.sub (by fun_prop) (ContinuousOn.div continuousOn_const (by fun_prop)
      fun y hy => by linarith [hy.1])
  have hI1 : IntegrableOn g (Ioc 0 x) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (hc1.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
      (fun y hy => (hg1 y hy).symm) measurableSet_Ioo
  have hI2 : IntegrableOn g (Ioc x r) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (hc2.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
      (fun y hy => (hg2 y hy).symm) measurableSet_Ioo
  have hd : Disjoint (Ioc (0 : ℝ) x) (Ioc x r) :=
    Set.disjoint_left.mpr fun y h1 h2 => by linarith [h1.2, h2.1]
  refine ⟨by rw [← Ioc_union_Ioc_eq_Ioc hx.le hxr]; exact hI1.union hI2, ?_⟩
  rw [← Ioc_union_Ioc_eq_Ioc hx.le hxr, setIntegral_union hd measurableSet_Ioc hI1 hI2,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo (x := x),
    setIntegral_congr_fun measurableSet_Ioo hg1, setIntegral_congr_fun measurableSet_Ioo hg2,
    ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hx.le, ← intervalIntegral.integral_of_le hxr,
    integral_quartic_sub_log (c₀ := 0) hx.le (by linarith),
    integral_quartic_sub_log (c₀ := 0) hxr (by linarith)]
  unfold cubicSurplusMain
  rw [add_zero]
  ring

/-- The remainder integral `∫_{(0, r]} ((x + y)/16 + (x + y)²/32)|x − y| dy = surplusRemainder r x`. -/
theorem integral_surplusRemainder {r x : ℝ} (hx : 0 < x) (hxr : x ≤ r) :
    IntegrableOn (fun y => ((x + y) / 16 + (x + y) ^ 2 / 32) * |x - y|) (Ioc 0 r) ∧
      (∫ y in Ioc 0 r, ((x + y) / 16 + (x + y) ^ 2 / 32) * |x - y|) = surplusRemainder r x := by
  set g := fun y => ((x + y) / 16 + (x + y) ^ 2 / 32) * |x - y| with hg
  have hg1 : ∀ y ∈ Ioo 0 x, g y = (x ^ 2 / 16 + x ^ 3 / 32) + 2 * (x ^ 2 / 64) * y +
      3 * (-1 / 48 - x / 96) * y ^ 2 + 4 * (-1 / 128) * y ^ 3 - 0 / (x + y) := by
    intro y hy
    simp only [hg, abs_of_pos (show 0 < x - y by linarith [hy.2])]
    ring
  have hg2 : ∀ y ∈ Ioo x r, g y = -(x ^ 2 / 16 + x ^ 3 / 32) + 2 * (-(x ^ 2 / 64)) * y +
      3 * (1 / 48 + x / 96) * y ^ 2 + 4 * (1 / 128) * y ^ 3 - 0 / (x + y) := by
    intro y hy
    rw [hg]
    simp only
    rw [abs_sub_comm, abs_of_pos (show 0 < y - x by linarith [hy.1])]
    ring
  have hc : Continuous g := by rw [hg]; fun_prop
  have hI1 : IntegrableOn g (Ioc 0 x) := hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hI2 : IntegrableOn g (Ioc x r) := hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hd : Disjoint (Ioc (0 : ℝ) x) (Ioc x r) :=
    Set.disjoint_left.mpr fun y h1 h2 => by linarith [h1.2, h2.1]
  refine ⟨hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self, ?_⟩
  rw [← Ioc_union_Ioc_eq_Ioc hx.le hxr, setIntegral_union hd measurableSet_Ioc hI1 hI2,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo (x := x),
    setIntegral_congr_fun measurableSet_Ioo hg1, setIntegral_congr_fun measurableSet_Ioo hg2,
    ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hx.le, ← intervalIntegral.integral_of_le hxr,
    integral_quartic_sub_log (c₀ := 0) (K := 0) hx.le (by linarith),
    integral_quartic_sub_log (c₀ := 0) (K := 0) hxr (by linarith)]
  unfold surplusRemainder
  ring

/-- The divided difference of a cubic gauge: `h(x) − h(y) = (x − y)(a₁ + a₂(x + y) + a₃(x² + xy + y²))`. -/
theorem cubicGauge_sub (a₀ a₁ a₂ a₃ x y : ℝ) :
    cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y =
      (x - y) * (a₁ + a₂ * (x + y) + a₃ * (x ^ 2 + x * y + y ^ 2)) := by
  unfold cubicGauge; ring

theorem continuous_cubicGauge (a₀ a₁ a₂ a₃ : ℝ) : Continuous (cubicGauge a₀ a₁ a₂ a₃) := by
  unfold cubicGauge; fun_prop

/-- **The surplus potential of a cubic gauge.** For `0 < x ≤ r ≤ 1/2` and a cubic gauge positive at
`x` whose divided differences are bounded by `L` on `[0, r]`,
`h(x) U_h(x) ≥ cubicSurplusMain a₁ a₂ a₃ r x − L · surplusRemainder r x`. -/
theorem mul_surplusPotential_cubicGauge_ge (a₀ a₁ a₂ a₃ : ℝ) {r x L : ℝ} (hx : 0 < x)
    (hxr : x ≤ r) (hr1 : r ≤ 1 / 2) (hhx : 0 < cubicGauge a₀ a₁ a₂ a₃ x)
    (hL : ∀ u v, 0 ≤ u → u ≤ r → 0 ≤ v → v ≤ r →
      |a₁ + a₂ * (u + v) + a₃ * (u ^ 2 + u * v + v ^ 2)| ≤ L) :
    cubicSurplusMain a₁ a₂ a₃ r x - L * surplusRemainder r x ≤
      cubicGauge a₀ a₁ a₂ a₃ x * surplusPotential (cubicGauge a₀ a₁ a₂ a₃) r x := by
  have hlip : ∀ y, 0 ≤ y → y ≤ r →
      |cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y| ≤ L * |x - y| := fun y hy0 hyr => by
    rw [cubicGauge_sub, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hL x y hx.le hxr hy0 hyr) (abs_nonneg _)
  obtain ⟨hP, hPeq⟩ := integral_principalSurplus_cubicGauge a₀ a₁ a₂ a₃ hx hxr
  obtain ⟨hE, hEeq⟩ := integral_surplusRemainder hx hxr
  have hU : cubicGauge a₀ a₁ a₂ a₃ x * surplusPotential (cubicGauge a₀ a₁ a₂ a₃) r x =
      ∫ y in Ioc 0 r, surplusKernel x y *
        (cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y) := by
    unfold surplusPotential
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    have e : cubicGauge a₀ a₁ a₂ a₃ x * (1 - cubicGauge a₀ a₁ a₂ a₃ y / cubicGauge a₀ a₁ a₂ a₃ x) =
        cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y := by
      field_simp
    calc cubicGauge a₀ a₁ a₂ a₃ x * (surplusKernel x y *
          (1 - cubicGauge a₀ a₁ a₂ a₃ y / cubicGauge a₀ a₁ a₂ a₃ x)) =
        surplusKernel x y * (cubicGauge a₀ a₁ a₂ a₃ x *
          (1 - cubicGauge a₀ a₁ a₂ a₃ y / cubicGauge a₀ a₁ a₂ a₃ x)) := by ring
      _ = _ := by rw [e]
  have hmk : Measurable fun y => surplusKernel x y := by
    unfold surplusKernel
    exact (measurable_archLevyDensity.comp (by fun_prop)).sub
      (measurable_archLevyDensity.comp (by fun_prop))
  have hmh : Measurable fun y => cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y :=
    measurable_const.sub (continuous_cubicGauge a₀ a₁ a₂ a₃).measurable
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL 0 0 le_rfl (by linarith) le_rfl (by linarith))
  have hK : IntegrableOn (fun y => surplusKernel x y *
      (cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y)) (Ioc 0 r) := by
    refine Measure.integrableOn_of_bounded (M := 3 / 2 * L) (by simp)
      (hmk.mul hmh).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs]
    by_cases hxy : x = y
    · rw [hxy, sub_self, mul_zero, abs_zero]; positivity
    have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hk0 := surplusKernel_nonneg hx hy.1 hxy
    have hk1 := (surplusKernel_le hx hy.1).trans (archLevyDensity_le_of_le_one hd
      (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]))
    rw [abs_mul, abs_of_nonneg hk0]
    calc surplusKernel x y * |cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y| ≤
          3 / 2 / |x - y| * (L * |x - y|) :=
          mul_le_mul hk1 (hlip y hy.1.le hy.2) (abs_nonneg _) (by positivity)
      _ = 3 / 2 * L := by field_simp
  have hpt : ∀ y ∈ Ioc 0 r, (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
      (cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y) -
      L * (((x + y) / 16 + (x + y) ^ 2 / 32) * |x - y|) ≤
        surplusKernel x y * (cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y) := by
    intro y hy
    by_cases hxy : x = y
    · rw [hxy, sub_self, sub_self, abs_zero]; simp
    set A := surplusKernel x y - (1 / (2 * |x - y|) - 1 / (2 * (x + y))) with hA
    set D := cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y with hD
    have hdiff : |A| ≤ (x + y) / 16 + (x + y) ^ 2 / 32 := abs_surplusKernel_sub_principal_le hx hy.1 hxy
    have hl : |D| ≤ L * |x - y| := hlip y hy.1.le hy.2
    have hab : |A * D| = |A| * |D| := abs_mul A D
    have hlow := neg_abs_le (A * D)
    have hxy0 : 0 < x + y := by linarith [hy.1]
    have hprod : |A| * |D| ≤ ((x + y) / 16 + (x + y) ^ 2 / 32) * (L * |x - y|) :=
      mul_le_mul hdiff hl (abs_nonneg _) (by positivity)
    have e : surplusKernel x y * D = (1 / (2 * |x - y|) - 1 / (2 * (x + y))) * D + A * D := by
      rw [hA]; ring
    rw [e]
    nlinarith
  have hPE : IntegrableOn (fun y => (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
      (cubicGauge a₀ a₁ a₂ a₃ x - cubicGauge a₀ a₁ a₂ a₃ y) -
      L * (((x + y) / 16 + (x + y) ^ 2 / 32) * |x - y|)) (Ioc 0 r) := hP.sub (hE.const_mul L)
  have hmono := setIntegral_mono_on hPE hK measurableSet_Ioc hpt
  rw [MeasureTheory.integral_sub hP (hE.const_mul L), MeasureTheory.integral_const_mul, hPeq,
    hEeq] at hmono
  rw [hU]
  exact hmono

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
