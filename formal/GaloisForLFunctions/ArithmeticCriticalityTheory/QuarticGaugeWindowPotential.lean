import GaloisForLFunctions.ArithmeticCriticalityTheory.CurvedGaugeWindowPotential

/-!
# The potential of a quartic window gauge

A curved gauge `q P` with `q(y) = 1 − c y²` gains the regional energy `c G(R)` at the window centre but
pays `−2c x² (1 + R/2)` near the edge, where the inward neighbours of `x` are higher. A quartic term
`q(y) = 1 − c y² + d y⁴`, `d > 0`, flattens the gauge near the edge and cuts this price. Its potential
needs the moments `m_k(s) = ∫_0^s u^k ω(u) du` to order four, with signs:

* `u ω(u) = ½ + u/4 − u²/48 − θ u³/32`, `θ ∈ [0, 1]`, on `(0, 1]` (`mul_archLevyDensity_le_sharp`,
  `mul_archLevyDensity_ge_sharp`), hence `P_k − E_k ≤ m_k ≤ P_k` with
  `P_k(s) = s^k/(2k) + s^{k+1}/(4(k+1)) − s^{k+2}/(48(k+2))`, `E_k(s) = s^{k+3}/(32(k+3))`
  (`integral_pow_mul_archLevyDensity_le`, `integral_pow_mul_archLevyDensity_ge`);
* `ω − ν ≤ 3/4 − 3u/16 + u³/48` on `(0, 1]`, from `u ν(u) = u e^{−u}/(2 sinh u)`
  (`archLevyDensity_sub_archDiagonalDensity_le_cubic`): the one-sided killing is at least
  `N(a) − 3a/4 + 3a²/32 − a⁴/192`, exact to second order (the exact value is `Ω(a) − κ`).

For a general profile gauge `M = q P` the potential at a plateau point is the profile times the
two one-sided killings plus the two regional integrals `∫_0^a ω(u)(q(x) − q(x + u))`,
`∫_0^b ω(u)(q(x) − q(x − u))`, `a = R − x`, `b = R + x` (`neg_poleFreeWeilOperator_profileGauge_ge`).
For the quartic gauge and `0 ≤ x` they combine into (`neg_poleFreeWeilOperator_quarticWindowGauge_ge`)

    (c − 6dx²)(m₂(a) + m₂(b)) − d (m₄(a) + m₄(b)) − 2x(c − 2dx²) ∫_a^b u ω + 4dx ∫_a^b u³ ω,

and each moment is replaced by the bound of the right sign. The pole mass of the quartic gauge is at
least `I₀ + (x² I₀ + I₂)/8` with `I₀ = ∫_{−r}^r q`, `I₂ = ∫_{−r}^r y² q`
(`integral_quarticWindowGauge_cosh_ge`, from `cosh z ≥ 1 + z²/2`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The diagonal density and the cubic killing -/

/-- `u ν(u) ≥ ½ (1 − u²/6)(1 − u + u²/2 − u³/6 + u⁴/24 − u⁵/100)` on `(0, 1]`, from
`ν(u) = e^{−u}/(2 sinh u)`. -/
theorem mul_archDiagonalDensity_ge {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    (1 - u ^ 2 / 6) * (1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 100) / 2 ≤
      u * archDiagonalDensity u := by
  obtain ⟨hs1, hs2, -, -⟩ := sinh_cosh_taylor_bounds h0.le h1
  have hS : 0 < Real.sinh u := Real.sinh_pos_iff.mpr h0
  have hT := taylor_le_exp_neg h0.le h1
  have hT0 : 0 ≤ 1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 100 := by
    nlinarith [mul_nonneg (pow_pos h0 3).le (by linarith : (0 : ℝ) ≤ 1 - u),
      mul_nonneg (sq_nonneg u) (by linarith : (0 : ℝ) ≤ 1 - u), pow_pos h0 4, pow_pos h0 5]
  have hA0 : 0 ≤ 1 - u ^ 2 / 6 := by nlinarith
  have hν : u * archDiagonalDensity u = u / (2 * Real.sinh u) * Real.exp (-u) := by
    have h1e : 0 < 1 - Real.exp (-2 * u) := by
      have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have e2 : Real.exp (-2 * u) = Real.exp (-u) * Real.exp (-u) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    have hpos : 0 < Real.exp u - Real.exp (-u) := by
      have := Real.exp_lt_exp.mpr (show -u < u by linarith); linarith
    have key : Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) =
        Real.exp (-u) / (Real.exp u - Real.exp (-u)) := by
      rw [div_eq_div_iff h1e.ne' hpos.ne', e2]
      linear_combination Real.exp (-u) * e3
    unfold archDiagonalDensity
    rw [key, Real.sinh_eq]
    field_simp
  have hq : (1 - u ^ 2 / 6) / 2 ≤ u / (2 * Real.sinh u) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [hν]
  calc (1 - u ^ 2 / 6) * (1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 100) / 2 =
        (1 - u ^ 2 / 6) / 2 * (1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 100) := by ring
    _ ≤ u / (2 * Real.sinh u) * Real.exp (-u) :=
        mul_le_mul hq hT hT0 (by positivity)

/-- **The cubic density difference** `ω − ν ≤ 3/4 − 3u/16 + u³/48` on `(0, 1]`. -/
theorem archLevyDensity_sub_archDiagonalDensity_le_cubic {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    archLevyDensity u - archDiagonalDensity u ≤ 3 / 4 - 3 * u / 16 + u ^ 3 / 48 := by
  have hω := mul_archLevyDensity_le_sharp h0 h1
  have hν := mul_archDiagonalDensity_ge h0 h1
  have hpoly : 1 / 2 + u / 4 - u ^ 2 / 48 -
      (1 - u ^ 2 / 6) * (1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 100) / 2 ≤
      u * (3 / 4 - 3 * u / 16 + u ^ 3 / 48) := by
    nlinarith [mul_nonneg (pow_pos h0 5).le (by linarith : (0 : ℝ) ≤ 1 - u), pow_pos h0 5,
      mul_nonneg (pow_pos h0 6).le (by linarith : (0 : ℝ) ≤ 1 - u), pow_pos h0 7]
  have : u * (archLevyDensity u - archDiagonalDensity u) ≤ u * (3 / 4 - 3 * u / 16 + u ^ 3 / 48) := by
    nlinarith
  exact le_of_mul_le_mul_left this h0

/-- **The cubic one-sided window killing.** For `0 < a ≤ 1`,
`∫_0^∞ (ν − ω 1_{u ≤ a}) ≥ N(a) − (3/4) a + 3a²/32 − a⁴/192`. -/
theorem integral_one_sided_window_ge_cubic {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    IntegrableOn (fun u => if u ≤ a then archDiagonalDensity u - archLevyDensity u
        else archDiagonalDensity u) (Ioi 0) ∧
      -(1 / 2) * Real.log (1 - Real.exp (-2 * a)) - 3 / 4 * a + 3 * a ^ 2 / 32 - a ^ 4 / 192 ≤
        ∫ u in Ioi (0 : ℝ), (if u ≤ a then archDiagonalDensity u - archLevyDensity u
          else archDiagonalDensity u) := by
  obtain ⟨hint, -⟩ := integral_one_sided_window_ge ha
  refine ⟨hint, ?_⟩
  have hunion : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  have hmeasD : Measurable archDiagonalDensity := by unfold archDiagonalDensity; fun_prop
  have hbd : ∀ u ∈ Ioc (0 : ℝ) a, |archDiagonalDensity u - archLevyDensity u| ≤ 3 / 4 := by
    intro u hu
    have h1 := archLevyDensity_sub_archDiagonalDensity_le hu.1
    have h2 : archDiagonalDensity u ≤ archLevyDensity u := archDiagonalDensity_le hu.1
    rw [abs_le]
    constructor <;> linarith
  have hI1 : IntegrableOn (fun u => archDiagonalDensity u - archLevyDensity u) (Ioc 0 a) := by
    refine Measure.integrableOn_of_bounded (M := 3 / 4) (by simp)
      ((hmeasD.sub measurable_archLevyDensity).aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => by
      rw [Real.norm_eq_abs]; exact hbd u hu)
  rw [hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set (hunion ▸ subset_union_left)) (hint.mono_set (hunion ▸ subset_union_right))]
  have e1 : (∫ u in Ioc 0 a, (if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u)) = ∫ u in Ioc 0 a, (archDiagonalDensity u - archLevyDensity u) :=
    setIntegral_congr_fun measurableSet_Ioc fun u hu => by rw [if_pos hu.2]
  have e2 : (∫ u in Ioi a, (if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u)) = ∫ u in Ioi a, archDiagonalDensity u :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => by rw [if_neg (not_le.mpr hu)]
  have hpc : Continuous fun u : ℝ => -(3 / 4) + 3 * u / 16 - u ^ 3 / 48 := by fun_prop
  have hlin : IntegrableOn (fun u : ℝ => -(3 / 4) + 3 * u / 16 - u ^ 3 / 48) (Ioc 0 a) :=
    hpc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hlow : (∫ u in Ioc 0 a, (-(3 / 4) + 3 * u / 16 - u ^ 3 / 48)) ≤
      ∫ u in Ioc 0 a, (archDiagonalDensity u - archLevyDensity u) :=
    setIntegral_mono_on hlin hI1 measurableSet_Ioc fun u hu => by
      have := archLevyDensity_sub_archDiagonalDensity_le_cubic hu.1 (hu.2.trans ha1)
      linarith
  have hval : (∫ u in Ioc 0 a, (-(3 / 4) + 3 * u / 16 - u ^ 3 / 48)) =
      -(3 / 4) * a + 3 * a ^ 2 / 32 - a ^ 4 / 192 := by
    rw [← intervalIntegral.integral_of_le ha.le]
    have hd : ∀ y ∈ uIcc (0 : ℝ) a, HasDerivAt (fun y : ℝ => -(3 / 4) * y + 3 * y ^ 2 / 32 -
        y ^ 4 / 192) (-(3 / 4) + 3 * y / 16 - y ^ 3 / 48) y := fun y _ => by
      have h := (((hasDerivAt_id' y).const_mul (-(3 / 4))).add
        (((hasDerivAt_pow 2 y).const_mul 3).div_const 32)).sub
        ((hasDerivAt_pow 4 y).div_const 192)
      exact h.congr_deriv (by push_cast; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hpc.intervalIntegrable _ _)]
    ring
  rw [e1, e2, integral_Ioi_archDiagonalDensity ha]
  linarith

/-- The killing bracket with the cubic one-sided bound: with `N(s) ≥ −½ log 2s + s/2 − s²/12`,
`N(a) + N(b) − (3/4)(a + b) + 3(a² + b²)/32 − (a⁴ + b⁴)/192 − 2C` is at least
`−log 2R − R/2 − 2C − ½ log(1 − x²/R²) + (a² + b²)/96 − (a⁴ + b⁴)/192`. -/
theorem cubicGauge_bracket_ge {R x : ℝ} (hR0 : 0 < R) (hR : R ≤ 1 / 2) (hx : |x| < R) :
    -Real.log (2 * R) - R / 2 - 2 * archConstantReal + -(1 / 2) * Real.log (1 - x ^ 2 / R ^ 2) +
        ((R - x) ^ 2 + (R + x) ^ 2) / 96 - ((R - x) ^ 4 + (R + x) ^ 4) / 192 ≤
      (-(1 / 2) * Real.log (1 - Real.exp (-2 * (R - x))) - 3 / 4 * (R - x) +
          3 * (R - x) ^ 2 / 32 - (R - x) ^ 4 / 192) +
        (-(1 / 2) * Real.log (1 - Real.exp (-2 * (R + x))) - 3 / 4 * (R + x) +
          3 * (R + x) ^ 2 / 32 - (R + x) ^ 4 / 192) - 2 * archConstantReal := by
  have h := curvedGauge_bracket_ge hR0 hR hx
  nlinarith [h]

/-! ### The Lévy moments -/

/-- The moment polynomial `P_k(s) = s^k/(2k) + s^{k+1}/(4(k+1)) − s^{k+2}/(48(k+2))`. -/
def levyMomentPoly (k : ℕ) (s : ℝ) : ℝ :=
  s ^ k / (2 * k) + s ^ (k + 1) / (4 * (k + 1)) - s ^ (k + 2) / (48 * (k + 2))

/-- The moment error `E_k(s) = s^{k+3}/(32(k+3))`. -/
def levyMomentErr (k : ℕ) (s : ℝ) : ℝ := s ^ (k + 3) / (32 * (k + 3))

theorem levyMomentPoly_zero {k : ℕ} (hk : 1 ≤ k) : levyMomentPoly k 0 = 0 := by
  unfold levyMomentPoly
  rw [zero_pow (by omega), zero_pow (by omega), zero_pow (by omega)]
  simp

theorem levyMomentErr_zero (k : ℕ) : levyMomentErr k 0 = 0 := by
  unfold levyMomentErr
  rw [zero_pow (by omega)]
  simp

theorem hasDerivAt_levyMomentPoly {k : ℕ} (hk : 1 ≤ k) (y : ℝ) :
    HasDerivAt (levyMomentPoly k) (y ^ (k - 1) * (1 / 2 + y / 4 - y ^ 2 / 48)) y := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h := (((hasDerivAt_pow (m + 1) y).div_const (2 * ((m + 1 : ℕ) : ℝ))).add
    ((hasDerivAt_pow (m + 1 + 1) y).div_const (4 * (((m + 1 : ℕ) : ℝ) + 1)))).sub
    ((hasDerivAt_pow (m + 1 + 2) y).div_const (48 * (((m + 1 : ℕ) : ℝ) + 2)))
  have e : levyMomentPoly (m + 1) = fun s => s ^ (m + 1) / (2 * ((m + 1 : ℕ) : ℝ)) +
      s ^ (m + 1 + 1) / (4 * (((m + 1 : ℕ) : ℝ) + 1)) -
        s ^ (m + 1 + 2) / (48 * (((m + 1 : ℕ) : ℝ) + 2)) := by
    funext s; unfold levyMomentPoly; push_cast; ring
  rw [e]
  refine h.congr_deriv ?_
  simp only [Nat.add_sub_cancel, show m + 1 + 1 - 1 = m + 1 by omega, show m + 1 + 2 - 1 = m + 2 by omega]
  push_cast
  have h1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (m : ℝ) + 1 + 1 ≠ 0 := by positivity
  have h3 : (m : ℝ) + 1 + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem hasDerivAt_levyMomentErr (k : ℕ) (y : ℝ) :
    HasDerivAt (levyMomentErr k) (y ^ (k - 1) * (y ^ 3 / 32)) y ∨ k = 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exact Or.inr hk
  left
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h := (hasDerivAt_pow (m + 1 + 3) y).div_const (32 * (((m + 1 : ℕ) : ℝ) + 3))
  have e : levyMomentErr (m + 1) = fun s => s ^ (m + 1 + 3) / (32 * (((m + 1 : ℕ) : ℝ) + 3)) := by
    funext s; unfold levyMomentErr; push_cast; ring
  rw [e]
  refine h.congr_deriv ?_
  simp only [Nat.add_sub_cancel, show m + 1 + 3 - 1 = m + 3 by omega]
  push_cast
  have h3 : (m : ℝ) + 1 + 3 ≠ 0 := by positivity
  field_simp
  ring

theorem integrableOn_pow_mul_archLevyDensity {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (ha : 0 ≤ a)
    (hb : b ≤ 1) : IntegrableOn (fun u => u ^ k * archLevyDensity u) (Ioc a b) := by
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((measurable_id.pow_const k).mul measurable_archLevyDensity).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => ?_)
  have hu0 : 0 < u := lt_of_le_of_lt ha hu.1
  have hu1 : u ≤ 1 := hu.2.trans hb
  have h1 := mul_archLevyDensity_le hu0 hu1
  have h2 := mul_nonneg hu0.le (archLevyDensity_pos hu0).le
  have hp : u ^ (k - 1) ≤ 1 := pow_le_one₀ hu0.le hu1
  have hp0 : 0 ≤ u ^ (k - 1) := by positivity
  have e : u ^ k * archLevyDensity u = u ^ (k - 1) * (u * archLevyDensity u) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [Real.norm_eq_abs, e, abs_of_nonneg (mul_nonneg hp0 h2)]
  calc u ^ (k - 1) * (u * archLevyDensity u) ≤ 1 * (1 / 2 + u / 4) :=
        mul_le_mul hp h1 h2 zero_le_one
    _ ≤ 1 := by linarith

/-- **Upper moment bound** `∫_a^b u^k ω ≤ P_k(b) − P_k(a)` for `1 ≤ k`, `0 ≤ a ≤ b ≤ 1`. -/
theorem integral_pow_mul_archLevyDensity_le {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ u in Ioc a b, u ^ k * archLevyDensity u) ≤ levyMomentPoly k b - levyMomentPoly k a := by
  have hpc : Continuous fun u : ℝ => u ^ (k - 1) * (1 / 2 + u / 4 - u ^ 2 / 48) := by fun_prop
  have hval : (∫ u in Ioc a b, u ^ (k - 1) * (1 / 2 + u / 4 - u ^ 2 / 48)) =
      levyMomentPoly k b - levyMomentPoly k a := by
    rw [← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_levyMomentPoly hk y)
        (hpc.intervalIntegrable _ _)]
  rw [← hval]
  refine setIntegral_mono_on (integrableOn_pow_mul_archLevyDensity hk ha hb)
    (hpc.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc fun u hu => ?_
  have hu0 : 0 < u := lt_of_le_of_lt ha hu.1
  have h := mul_archLevyDensity_le_sharp hu0 (hu.2.trans hb)
  have e : u ^ k * archLevyDensity u = u ^ (k - 1) * (u * archLevyDensity u) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **Lower moment bound** `∫_a^b u^k ω ≥ P_k(b) − P_k(a) − (E_k(b) − E_k(a))` for `1 ≤ k`,
`0 ≤ a ≤ b ≤ 1`. -/
theorem integral_pow_mul_archLevyDensity_ge {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    levyMomentPoly k b - levyMomentPoly k a - (levyMomentErr k b - levyMomentErr k a) ≤
      ∫ u in Ioc a b, u ^ k * archLevyDensity u := by
  have hpc : Continuous fun u : ℝ => u ^ (k - 1) * (1 / 2 + u / 4 - u ^ 2 / 48) := by fun_prop
  have hec : Continuous fun u : ℝ => u ^ (k - 1) * (u ^ 3 / 32) := by fun_prop
  have hdE : ∀ y, HasDerivAt (levyMomentErr k) (y ^ (k - 1) * (y ^ 3 / 32)) y := fun y =>
    (hasDerivAt_levyMomentErr k y).resolve_right (by omega)
  have hval : (∫ u in Ioc a b, (u ^ (k - 1) * (1 / 2 + u / 4 - u ^ 2 / 48) -
      u ^ (k - 1) * (u ^ 3 / 32))) =
      levyMomentPoly k b - levyMomentPoly k a - (levyMomentErr k b - levyMomentErr k a) := by
    rw [← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_sub (hpc.intervalIntegrable _ _) (hec.intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_levyMomentPoly hk y)
        (hpc.intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hdE y)
        (hec.intervalIntegrable _ _)]
  rw [← hval]
  refine setIntegral_mono_on ((hpc.sub hec).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (integrableOn_pow_mul_archLevyDensity hk ha hb) measurableSet_Ioc fun u hu => ?_
  have hu0 : 0 < u := lt_of_le_of_lt ha hu.1
  have h := mul_archLevyDensity_ge_sharp hu0 (hu.2.trans hb)
  have e : u ^ k * archLevyDensity u = u ^ (k - 1) * (u * archLevyDensity u) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [e, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The quartic Lévy integral as a combination of moments. -/
theorem integral_archLevyDensity_mul_quartic {s : Set ℝ}
    (h1 : IntegrableOn (fun u => u ^ 1 * archLevyDensity u) s)
    (h2 : IntegrableOn (fun u => u ^ 2 * archLevyDensity u) s)
    (h3 : IntegrableOn (fun u => u ^ 3 * archLevyDensity u) s)
    (h4 : IntegrableOn (fun u => u ^ 4 * archLevyDensity u) s) (α₁ α₂ α₃ α₄ : ℝ) :
    (∫ u in s, archLevyDensity u * (α₁ * u + α₂ * u ^ 2 + α₃ * u ^ 3 + α₄ * u ^ 4)) =
      α₁ * (∫ u in s, u ^ 1 * archLevyDensity u) + α₂ * (∫ u in s, u ^ 2 * archLevyDensity u) +
        α₃ * (∫ u in s, u ^ 3 * archLevyDensity u) + α₄ * ∫ u in s, u ^ 4 * archLevyDensity u := by
  have e : (fun u => archLevyDensity u * (α₁ * u + α₂ * u ^ 2 + α₃ * u ^ 3 + α₄ * u ^ 4)) =
      fun u => α₁ * (u ^ 1 * archLevyDensity u) + α₂ * (u ^ 2 * archLevyDensity u) +
        α₃ * (u ^ 3 * archLevyDensity u) + α₄ * (u ^ 4 * archLevyDensity u) := by
    funext u; ring
  have i1 : IntegrableOn (fun u => α₁ * (u ^ 1 * archLevyDensity u)) s := h1.const_mul α₁
  have i2 : IntegrableOn (fun u => α₂ * (u ^ 2 * archLevyDensity u)) s := h2.const_mul α₂
  have i3 : IntegrableOn (fun u => α₃ * (u ^ 3 * archLevyDensity u)) s := h3.const_mul α₃
  have i4 : IntegrableOn (fun u => α₄ * (u ^ 4 * archLevyDensity u)) s := h4.const_mul α₄
  have i12 : IntegrableOn (fun u => α₁ * (u ^ 1 * archLevyDensity u) +
      α₂ * (u ^ 2 * archLevyDensity u)) s := i1.add i2
  have i123 : IntegrableOn (fun u => α₁ * (u ^ 1 * archLevyDensity u) +
      α₂ * (u ^ 2 * archLevyDensity u) + α₃ * (u ^ 3 * archLevyDensity u)) s := i12.add i3
  rw [e, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul]

/-! ### The potential of a profile gauge -/

/-- **The potential of a profile gauge** `M = q P` at a plateau point `|x| ≤ R − δ`: the profile
times the two one-sided killings plus the two one-sided regional integrals. -/
theorem neg_poleFreeWeilOperator_profileGauge_ge {q : ℝ → ℝ} {R δ x : ℝ} (hqd : ContDiff ℝ 2 q)
    (hδ : 0 < δ) (hR : R ≤ 1 / 3) (hx : |x| ≤ R - δ) (hq0 : ∀ y, |y| ≤ R → 0 ≤ q y)
    (hia : IntegrableOn (fun u => archLevyDensity u * (q x - q (x + u))) (Ioc 0 (R - x)))
    (hib : IntegrableOn (fun u => archLevyDensity u * (q x - q (x - u))) (Ioc 0 (R + x))) :
    q x * ((∫ u in Ioi (0 : ℝ), (if u ≤ R - x then archDiagonalDensity u - archLevyDensity u
          else archDiagonalDensity u)) +
        (∫ u in Ioi (0 : ℝ), (if u ≤ R + x then archDiagonalDensity u - archLevyDensity u
          else archDiagonalDensity u)) - 2 * archConstantReal) +
      ((∫ u in Ioc 0 (R - x), archLevyDensity u * (q x - q (x + u))) +
        ∫ u in Ioc 0 (R + x), archLevyDensity u * (q x - q (x - u))) ≤
      -poleFreeWeilOperator (fun y => q y * plateauGauge R δ y) x := by
  set M : ℝ → ℝ := fun y => q y * plateauGauge R δ y with hMdef
  set a : ℝ := R - x with hadef
  set b : ℝ := R + x with hbdef
  have hxR : |x| < R := by linarith
  have hx' := abs_le.mp hx
  have ha : 0 < a := by rw [hadef]; linarith
  have hb : 0 < b := by rw [hbdef]; linarith
  have hMx : M x = q x := by simp only [hMdef]; rw [plateauGauge_eq_one hδ hx, mul_one]
  have hzero : ∀ y, R ≤ |y| → M y = 0 := fun y hy => by
    simp only [hMdef]; rw [plateauGauge_eq_zero hδ hy, mul_zero]
  have hle : ∀ y, |y| ≤ R → M y ≤ q y := fun y hy => by
    simp only [hMdef]
    have h0 := hq0 y hy
    nlinarith [mul_nonneg h0 (by linarith [plateauGauge_le_one R δ y] :
      (0 : ℝ) ≤ 1 - plateauGauge R δ y)]
  have hprime : profilePrimeSum M x = 0 :=
    profilePrimeSum_eq_zero hzero (by have := Real.log_two_gt_d9; linarith) hxR
  obtain ⟨hIa, -⟩ := integral_one_sided_window_ge ha
  obtain ⟨hIb, -⟩ := integral_one_sided_window_ge hb
  set ra : ℝ → ℝ := (Ioc 0 a).indicator fun u => archLevyDensity u * (q x - q (x + u)) with hra
  set rb : ℝ → ℝ := (Ioc 0 b).indicator fun u => archLevyDensity u * (q x - q (x - u)) with hrb
  have hia' : IntegrableOn ra (Ioi 0) := (hia.integrable_indicator measurableSet_Ioc).integrableOn
  have hib' : IntegrableOn rb (Ioi 0) := (hib.integrable_indicator measurableSet_Ioc).integrableOn
  set ga : ℝ → ℝ := fun u => if u ≤ a then archDiagonalDensity u - archLevyDensity u
    else archDiagonalDensity u with hgadef
  set gb : ℝ → ℝ := fun u => if u ≤ b then archDiagonalDensity u - archLevyDensity u
    else archDiagonalDensity u with hgbdef
  -- pointwise domination
  have hpt : ∀ u ∈ Ioi (0 : ℝ), q x * (ga u + gb u) + (ra u + rb u) ≤ profileArchTerm M x u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hω := archLevyDensity_pos hu0
    have h1 : M (x + u) ≤ if u ≤ a then q (x + u) else 0 := by
      split_ifs with h
      · exact hle _ (abs_le.mpr ⟨by linarith, by rw [hadef] at h; linarith⟩)
      · exact (hzero _ (by rw [abs_of_pos (by linarith : 0 < x + u)]; rw [hadef] at h; linarith)).le
    have h2 : M (x - u) ≤ if u ≤ b then q (x - u) else 0 := by
      split_ifs with h
      · exact hle _ (abs_le.mpr ⟨by rw [hbdef] at h; linarith, by linarith⟩)
      · exact (hzero _ (by rw [abs_of_neg (by linarith : x - u < 0)]; rw [hbdef] at h; linarith)).le
    have hm1 := mul_le_mul_of_nonneg_left h1 hω.le
    have hm2 := mul_le_mul_of_nonneg_left h2 hω.le
    unfold profileArchTerm
    simp only [hgadef, hgbdef]
    rw [hMx, hra, hrb]
    by_cases hua : u ≤ a <;> by_cases hub : u ≤ b
    · rw [Set.indicator_of_mem (show u ∈ Ioc 0 a from ⟨hu0, hua⟩),
        Set.indicator_of_mem (show u ∈ Ioc 0 b from ⟨hu0, hub⟩), if_pos hua, if_pos hub]
      rw [if_pos hua] at hm1; rw [if_pos hub] at hm2
      linarith
    · rw [Set.indicator_of_mem (show u ∈ Ioc 0 a from ⟨hu0, hua⟩),
        Set.indicator_of_notMem (fun h => hub h.2), if_pos hua, if_neg hub]
      rw [if_pos hua] at hm1; rw [if_neg hub, mul_zero] at hm2
      linarith
    · rw [Set.indicator_of_notMem (fun h => hua h.2),
        Set.indicator_of_mem (show u ∈ Ioc 0 b from ⟨hu0, hub⟩), if_neg hua, if_pos hub]
      rw [if_neg hua, mul_zero] at hm1; rw [if_pos hub] at hm2
      linarith
    · rw [Set.indicator_of_notMem (fun h => hua h.2), Set.indicator_of_notMem (fun h => hub h.2),
        if_neg hua, if_neg hub]
      rw [if_neg hua, mul_zero] at hm1; rw [if_neg hub, mul_zero] at hm2
      linarith
  have hMd : ContDiff ℝ 2 M := hqd.mul (contDiff_plateauGauge _ _)
  have hMcs : HasCompactSupport M := (hasCompactSupport_plateauGauge hδ).mul_left
  obtain ⟨K, -, hK⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hLip : ∀ a b, |M a - M b| ≤ K * |a - b| := fun a b => hK b a
  have hg2 : IntegrableOn (fun u => q x * (ga u + gb u)) (Ioi 0) := (hIa.add hIb).const_mul _
  have hr2 : IntegrableOn (fun u => ra u + rb u) (Ioi 0) := hia'.add hib'
  have hL : IntegrableOn (fun u => q x * (ga u + gb u) + (ra u + rb u)) (Ioi 0) := hg2.add hr2
  have hmono := setIntegral_mono_on hL (integrableOn_profileArchTerm hMd.continuous hLip x)
    measurableSet_Ioi hpt
  have eL : (∫ u in Ioi (0 : ℝ), (q x * (ga u + gb u) + (ra u + rb u))) =
      q x * ((∫ u in Ioi (0 : ℝ), ga u) + ∫ u in Ioi (0 : ℝ), gb u) +
        ((∫ u in Ioi (0 : ℝ), ra u) + ∫ u in Ioi (0 : ℝ), rb u) := by
    rw [integral_add hg2 hr2, integral_const_mul, integral_add hIa hIb, integral_add hia' hib']
  rw [eL] at hmono
  have eIa : (∫ u in Ioi (0 : ℝ), ra u) = ∫ u in Ioc 0 a, archLevyDensity u * (q x - q (x + u)) := by
    rw [hra, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self]
  have eIb : (∫ u in Ioi (0 : ℝ), rb u) = ∫ u in Ioc 0 b, archLevyDensity u * (q x - q (x - u)) := by
    rw [hrb, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self]
  rw [eIa, eIb] at hmono
  have hW : -poleFreeWeilOperator M x = (∫ u in Ioi (0 : ℝ), profileArchTerm M x u) -
      2 * archConstantReal * q x := by
    unfold poleFreeWeilOperator
    rw [hprime, hMx]
    ring
  rw [hW]
  linarith

/-! ### The quartic gauge -/

/-- The quartic profile `q(y) = 1 − c y² + d y⁴`. -/
def quarticProfile (c d y : ℝ) : ℝ := 1 - c * y ^ 2 + d * y ^ 4

/-- The quartic window gauge `q P`, `P` the plateau of radius `R` with collar `δ`. -/
def quarticWindowGauge (c d R δ y : ℝ) : ℝ := quarticProfile c d y * plateauGauge R δ y

theorem contDiff_quarticProfile (c d : ℝ) : ContDiff ℝ 2 (quarticProfile c d) := by
  unfold quarticProfile
  fun_prop

theorem contDiff_quarticWindowGauge (c d R δ : ℝ) : ContDiff ℝ 2 (quarticWindowGauge c d R δ) :=
  (contDiff_quarticProfile c d).mul (contDiff_plateauGauge _ _)

theorem hasCompactSupport_quarticWindowGauge (c d R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (quarticWindowGauge c d R δ) :=
  (hasCompactSupport_plateauGauge hδ).mul_left

theorem quarticProfile_neg (c d y : ℝ) : quarticProfile c d (-y) = quarticProfile c d y := by
  unfold quarticProfile; ring

theorem quarticWindowGauge_neg (c d R δ y : ℝ) :
    quarticWindowGauge c d R δ (-y) = quarticWindowGauge c d R δ y := by
  simp only [quarticWindowGauge, quarticProfile, plateauGauge, sub_neg_eq_add, ← sub_eq_add_neg,
    neg_sq, (show (-y) ^ 4 = y ^ 4 by ring)]
  ring

/-- On `[−R, R]` the quartic profile decreases in `y²` when `2 d R² ≤ c`: `q(y) ≥ q(R)`. -/
theorem quarticProfile_ge_of_le {c d R y : ℝ} (hd : 0 ≤ d) (hdc : 2 * d * R ^ 2 ≤ c)
    (hy : |y| ≤ R) : 1 - c * R ^ 2 + d * R ^ 4 ≤ quarticProfile c d y := by
  unfold quarticProfile
  have h2 : y ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hfac : (R ^ 2 - y ^ 2) * (c - d * (y ^ 2 + R ^ 2)) ≥ 0 :=
    mul_nonneg (by linarith) (by nlinarith [mul_le_mul_of_nonneg_left h2 hd])
  nlinarith [hfac]

theorem quarticProfile_le_one {c d R y : ℝ} (hd : 0 ≤ d) (hdc : 2 * d * R ^ 2 ≤ c)
    (hy : |y| ≤ R) : quarticProfile c d y ≤ 1 := by
  unfold quarticProfile
  have h2 : y ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hdy : d * y ^ 2 ≤ c := by nlinarith [mul_le_mul_of_nonneg_left h2 hd, mul_nonneg hd (sq_nonneg R)]
  have : y ^ 2 * (d * y ^ 2 - c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (by linarith)
  have e : y ^ 2 * (d * y ^ 2 - c) = d * y ^ 4 - c * y ^ 2 := by ring
  linarith

theorem quarticWindowGauge_eq_zero (c d : ℝ) {R δ y : ℝ} (hδ : 0 < δ) (hy : R ≤ |y|) :
    quarticWindowGauge c d R δ y = 0 := by
  unfold quarticWindowGauge
  rw [plateauGauge_eq_zero hδ hy, mul_zero]

theorem quarticWindowGauge_eq (c d : ℝ) {R δ y : ℝ} (hδ : 0 < δ) (hy : |y| ≤ R - δ) :
    quarticWindowGauge c d R δ y = quarticProfile c d y := by
  unfold quarticWindowGauge
  rw [plateauGauge_eq_one hδ hy, mul_one]

theorem quarticWindowGauge_nonneg {c d R δ : ℝ} (hd : 0 ≤ d) (hdc : 2 * d * R ^ 2 ≤ c)
    (hqR : 0 ≤ 1 - c * R ^ 2 + d * R ^ 4) (hδ : 0 < δ) (y : ℝ) :
    0 ≤ quarticWindowGauge c d R δ y := by
  by_cases hy : |y| < R
  · exact mul_nonneg (by linarith [quarticProfile_ge_of_le hd hdc hy.le])
      (plateauGauge_nonneg _ _ _)
  · rw [quarticWindowGauge_eq_zero c d hδ (not_lt.mp hy)]

theorem quarticWindowGauge_le_one {c d R δ : ℝ} (hd : 0 ≤ d) (hdc : 2 * d * R ^ 2 ≤ c)
    (hqR : 0 ≤ 1 - c * R ^ 2 + d * R ^ 4) (hδ : 0 < δ) (y : ℝ) :
    quarticWindowGauge c d R δ y ≤ 1 := by
  by_cases hy : |y| < R
  · unfold quarticWindowGauge
    have h0 : 0 ≤ quarticProfile c d y := by linarith [quarticProfile_ge_of_le hd hdc hy.le]
    have h1 := quarticProfile_le_one hd hdc hy.le
    have hP := plateauGauge_le_one R δ y
    have hP0 := plateauGauge_nonneg R δ y
    nlinarith [mul_le_mul h1 hP hP0 zero_le_one]
  · rw [quarticWindowGauge_eq_zero c d hδ (not_lt.mp hy)]; norm_num

/-- **The potential of the quartic gauge** at a plateau point `0 ≤ x ≤ R − δ`: the killing
bracket plus the regional moments with bounds of the right sign; the second-moment coefficient
`c − 6dx²` may change sign, whence the correction `max(c − 6dx², 0)(E₂(a) + E₂(b))`. -/
theorem neg_poleFreeWeilOperator_quarticWindowGauge_ge_max {c d R δ x : ℝ} (hd : 0 ≤ d)
    (hdc2 : 2 * d * R ^ 2 ≤ c) (hqR : 0 ≤ 1 - c * R ^ 2 + d * R ^ 4) (hδ : 0 < δ)
    (hR : R ≤ 1 / 3) (hx0 : 0 ≤ x) (hx : x ≤ R - δ) :
    quarticProfile c d x *
        ((-(1 / 2) * Real.log (1 - Real.exp (-2 * (R - x))) - 3 / 4 * (R - x) +
            3 * (R - x) ^ 2 / 32 - (R - x) ^ 4 / 192) +
          (-(1 / 2) * Real.log (1 - Real.exp (-2 * (R + x))) - 3 / 4 * (R + x) +
            3 * (R + x) ^ 2 / 32 - (R + x) ^ 4 / 192) - 2 * archConstantReal) +
      ((c - 6 * d * x ^ 2) * (levyMomentPoly 2 (R - x) + levyMomentPoly 2 (R + x)) -
        max (c - 6 * d * x ^ 2) 0 * (levyMomentErr 2 (R - x) + levyMomentErr 2 (R + x)) -
        d * (levyMomentPoly 4 (R - x) + levyMomentPoly 4 (R + x)) -
        2 * x * (c - 2 * d * x ^ 2) * (levyMomentPoly 1 (R + x) - levyMomentPoly 1 (R - x)) +
        4 * d * x * (levyMomentPoly 3 (R + x) - levyMomentPoly 3 (R - x) -
          (levyMomentErr 3 (R + x) - levyMomentErr 3 (R - x)))) ≤
      -poleFreeWeilOperator (quarticWindowGauge c d R δ) x := by
  set q := quarticProfile c d with hqdef
  set a : ℝ := R - x with hadef
  set b : ℝ := R + x with hbdef
  have hc : 0 ≤ c := le_trans (by positivity) hdc2
  have hxabs : |x| ≤ R - δ := by rw [abs_of_nonneg hx0]; exact hx
  have ha : 0 < a := by rw [hadef]; linarith
  have hb : 0 < b := by rw [hbdef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have hb1 : b ≤ 1 := by rw [hbdef]; linarith
  have ha1 : a ≤ 1 := by linarith
  have hq0 : ∀ y, |y| ≤ R → 0 ≤ q y := fun y hy => by
    have := quarticProfile_ge_of_le hd hdc2 hy
    rw [hqdef]; linarith
  have hx2 : x ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hx0 (by linarith) 2
  have hdx := mul_le_mul_of_nonneg_left hx2 hd
  have hα1 : 0 ≤ 2 * x * (c - 2 * d * x ^ 2) := mul_nonneg (by linarith) (by linarith)
  have hα3 : 0 ≤ 4 * d * x := by positivity
  -- moment integrability
  have im : ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ, s ≤ 1 →
      IntegrableOn (fun u => u ^ k * archLevyDensity u) (Ioc 0 s) := fun k hk s hs =>
    integrableOn_pow_mul_archLevyDensity hk le_rfl hs
  -- the regional integrands as moment combinations
  have epa : ∀ u, archLevyDensity u * (q x - q (x + u)) = archLevyDensity u *
      ((2 * c * x - 4 * d * x ^ 3) * u + (c - 6 * d * x ^ 2) * u ^ 2 + (-(4 * d * x)) * u ^ 3 +
        (-d) * u ^ 4) := fun u => by rw [hqdef]; unfold quarticProfile; ring
  have epb : ∀ u, archLevyDensity u * (q x - q (x - u)) = archLevyDensity u *
      ((-(2 * c * x - 4 * d * x ^ 3)) * u + (c - 6 * d * x ^ 2) * u ^ 2 + (4 * d * x) * u ^ 3 +
        (-d) * u ^ 4) := fun u => by rw [hqdef]; unfold quarticProfile; ring
  have hcomb : ∀ s : ℝ, s ≤ 1 → ∀ α₁ α₂ α₃ α₄ : ℝ,
      IntegrableOn (fun u => archLevyDensity u * (α₁ * u + α₂ * u ^ 2 + α₃ * u ^ 3 + α₄ * u ^ 4))
        (Ioc 0 s) := fun s hs α₁ α₂ α₃ α₄ => by
    have h := ((((im 1 le_rfl s hs).const_mul α₁).add ((im 2 (by norm_num) s hs).const_mul α₂)).add
      ((im 3 (by norm_num) s hs).const_mul α₃)).add ((im 4 (by norm_num) s hs).const_mul α₄)
    exact IntegrableOn.congr_fun h (fun u _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioc
  have hia : IntegrableOn (fun u => archLevyDensity u * (q x - q (x + u))) (Ioc 0 a) := by
    simp_rw [epa]; exact hcomb a ha1 _ _ _ _
  have hib : IntegrableOn (fun u => archLevyDensity u * (q x - q (x - u))) (Ioc 0 b) := by
    simp_rw [epb]; exact hcomb b hb1 _ _ _ _
  have hgen := neg_poleFreeWeilOperator_profileGauge_ge (contDiff_quarticProfile c d) hδ hR hxabs
    hq0 hia hib
  have hgauge : (fun y => q y * plateauGauge R δ y) = quarticWindowGauge c d R δ := rfl
  rw [hgauge] at hgen
  -- the killing
  obtain ⟨-, hVa⟩ := integral_one_sided_window_ge_cubic ha ha1
  obtain ⟨-, hVb⟩ := integral_one_sided_window_ge_cubic hb hb1
  have hqx : 0 ≤ q x := hq0 x (by linarith [hxabs])
  have hqV := mul_le_mul_of_nonneg_left (add_le_add hVa hVb) hqx
  -- the regional integrals
  have eA : (∫ u in Ioc 0 a, archLevyDensity u * (q x - q (x + u))) =
      (2 * c * x - 4 * d * x ^ 3) * (∫ u in Ioc 0 a, u ^ 1 * archLevyDensity u) +
        (c - 6 * d * x ^ 2) * (∫ u in Ioc 0 a, u ^ 2 * archLevyDensity u) +
        (-(4 * d * x)) * (∫ u in Ioc 0 a, u ^ 3 * archLevyDensity u) +
        (-d) * ∫ u in Ioc 0 a, u ^ 4 * archLevyDensity u := by
    simp_rw [epa]
    exact integral_archLevyDensity_mul_quartic (im 1 le_rfl a ha1) (im 2 (by norm_num) a ha1)
      (im 3 (by norm_num) a ha1) (im 4 (by norm_num) a ha1) _ _ _ _
  have eB : (∫ u in Ioc 0 b, archLevyDensity u * (q x - q (x - u))) =
      (-(2 * c * x - 4 * d * x ^ 3)) * (∫ u in Ioc 0 b, u ^ 1 * archLevyDensity u) +
        (c - 6 * d * x ^ 2) * (∫ u in Ioc 0 b, u ^ 2 * archLevyDensity u) +
        (4 * d * x) * (∫ u in Ioc 0 b, u ^ 3 * archLevyDensity u) +
        (-d) * ∫ u in Ioc 0 b, u ^ 4 * archLevyDensity u := by
    simp_rw [epb]
    exact integral_archLevyDensity_mul_quartic (im 1 le_rfl b hb1) (im 2 (by norm_num) b hb1)
      (im 3 (by norm_num) b hb1) (im 4 (by norm_num) b hb1) _ _ _ _
  -- the increments `∫_a^b`
  have split : ∀ k : ℕ, 1 ≤ k → (∫ u in Ioc 0 b, u ^ k * archLevyDensity u) =
      (∫ u in Ioc 0 a, u ^ k * archLevyDensity u) + ∫ u in Ioc a b, u ^ k * archLevyDensity u :=
    fun k hk => by
      rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc (im k hk a ha1)
        (integrableOn_pow_mul_archLevyDensity hk ha.le hb1), Ioc_union_Ioc_eq_Ioc ha.le hab]
  rw [split 1 le_rfl, split 3 (by norm_num)] at eB
  -- moment bounds
  have L2a := integral_pow_mul_archLevyDensity_ge (k := 2) (by norm_num) le_rfl ha.le ha1
  have L2b := integral_pow_mul_archLevyDensity_ge (k := 2) (by norm_num) le_rfl hb.le hb1
  have U2a := integral_pow_mul_archLevyDensity_le (k := 2) (by norm_num) le_rfl ha.le ha1
  have U2b := integral_pow_mul_archLevyDensity_le (k := 2) (by norm_num) le_rfl hb.le hb1
  have U4a := integral_pow_mul_archLevyDensity_le (k := 4) (by norm_num) le_rfl ha.le ha1
  have U4b := integral_pow_mul_archLevyDensity_le (k := 4) (by norm_num) le_rfl hb.le hb1
  have U1 := integral_pow_mul_archLevyDensity_le (k := 1) le_rfl ha.le hab hb1
  have L3 := integral_pow_mul_archLevyDensity_ge (k := 3) (by norm_num) ha.le hab hb1
  rw [levyMomentPoly_zero (by norm_num), levyMomentErr_zero] at L2a L2b
  rw [levyMomentPoly_zero (by norm_num)] at U4a U4b U2a U2b
  simp only [sub_zero] at U2a U2b
  have k2 : (c - 6 * d * x ^ 2) * (levyMomentPoly 2 a + levyMomentPoly 2 b) -
      max (c - 6 * d * x ^ 2) 0 * (levyMomentErr 2 a + levyMomentErr 2 b) ≤
      (c - 6 * d * x ^ 2) * ((∫ u in Ioc 0 a, u ^ 2 * archLevyDensity u) +
        ∫ u in Ioc 0 b, u ^ 2 * archLevyDensity u) := by
    rcases le_total 0 (c - 6 * d * x ^ 2) with hα2 | hα2
    · rw [max_eq_left hα2]
      have := mul_le_mul_of_nonneg_left (add_le_add L2a L2b) hα2
      simp only [sub_zero] at this
      linarith
    · rw [max_eq_right hα2, zero_mul, sub_zero]
      exact mul_le_mul_of_nonpos_left (add_le_add U2a U2b) hα2
  have k4 := mul_le_mul_of_nonneg_left (add_le_add U4a U4b) hd
  have k1 := mul_le_mul_of_nonneg_left U1 hα1
  have k3 := mul_le_mul_of_nonneg_left L3 hα3
  have hlinear : (2 * c * x - 4 * d * x ^ 3) = 2 * x * (c - 2 * d * x ^ 2) := by ring
  rw [hlinear] at eA eB
  linarith [hgen, hqV, eA, eB, k1, k2, k3, k4]

/-- **The potential of the quartic gauge** at a plateau point `0 ≤ x ≤ R − δ` when the
second-moment coefficient is nonnegative (`6 d R² ≤ c`). -/
theorem neg_poleFreeWeilOperator_quarticWindowGauge_ge {c d R δ x : ℝ} (hd : 0 ≤ d)
    (hdc : 6 * d * R ^ 2 ≤ c) (hqR : 0 ≤ 1 - c * R ^ 2 + d * R ^ 4) (hδ : 0 < δ)
    (hR : R ≤ 1 / 3) (hx0 : 0 ≤ x) (hx : x ≤ R - δ) :
    quarticProfile c d x *
        ((-(1 / 2) * Real.log (1 - Real.exp (-2 * (R - x))) - 3 / 4 * (R - x) +
            3 * (R - x) ^ 2 / 32 - (R - x) ^ 4 / 192) +
          (-(1 / 2) * Real.log (1 - Real.exp (-2 * (R + x))) - 3 / 4 * (R + x) +
            3 * (R + x) ^ 2 / 32 - (R + x) ^ 4 / 192) - 2 * archConstantReal) +
      ((c - 6 * d * x ^ 2) * (levyMomentPoly 2 (R - x) - levyMomentErr 2 (R - x) +
          (levyMomentPoly 2 (R + x) - levyMomentErr 2 (R + x))) -
        d * (levyMomentPoly 4 (R - x) + levyMomentPoly 4 (R + x)) -
        2 * x * (c - 2 * d * x ^ 2) * (levyMomentPoly 1 (R + x) - levyMomentPoly 1 (R - x)) +
        4 * d * x * (levyMomentPoly 3 (R + x) - levyMomentPoly 3 (R - x) -
          (levyMomentErr 3 (R + x) - levyMomentErr 3 (R - x)))) ≤
      -poleFreeWeilOperator (quarticWindowGauge c d R δ) x := by
  have hc : 0 ≤ c := le_trans (by positivity) hdc
  have hdc2 : 2 * d * R ^ 2 ≤ c := le_trans (by nlinarith [mul_nonneg hd (sq_nonneg R)]) hdc
  have hx2 : x ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hx0 (by linarith) 2
  have hα2 : 0 ≤ c - 6 * d * x ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hx2 hd]
  have h := neg_poleFreeWeilOperator_quarticWindowGauge_ge_max hd hdc2 hqR hδ hR hx0 hx
  rw [max_eq_left hα2] at h
  linarith

/-! ### The pole mass of the quartic gauge -/

theorem one_add_sq_div_two_le_cosh {z : ℝ} (hz : |z| ≤ 1) : 1 + z ^ 2 / 2 ≤ Real.cosh z := by
  have h := (sinh_cosh_taylor_bounds (abs_nonneg z) hz).2.2.1
  rwa [Real.cosh_abs, sq_abs] at h

/-- `∫ M(y) cosh((x − y)/2) dy ≥ I₀ + (x² I₀ + I₂)/8`, `I₀ = 2(r − c r³/3 + d r⁵/5)`,
`I₂ = 2(r³/3 − c r⁵/5 + d r⁷/7)`, `r = R − δ`, for `|x| ≤ R`, `R ≤ 1/2`. -/
theorem integral_quarticWindowGauge_cosh_ge {c d R δ x : ℝ} (hd : 0 ≤ d) (hdc : 2 * d * R ^ 2 ≤ c)
    (hqR : 0 ≤ 1 - c * R ^ 2 + d * R ^ 4) (hδ : 0 < δ) (hδR : δ ≤ R) (hR : R ≤ 1 / 2)
    (hx : |x| ≤ R) :
    2 * ((R - δ) - c * (R - δ) ^ 3 / 3 + d * (R - δ) ^ 5 / 5) * (1 + x ^ 2 / 8) +
        2 * ((R - δ) ^ 3 / 3 - c * (R - δ) ^ 5 / 5 + d * (R - δ) ^ 7 / 7) / 8 ≤
      ∫ y, quarticWindowGauge c d R δ y * Real.cosh ((x - y) / 2) := by
  set r : ℝ := R - δ with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hint : Integrable fun y => quarticWindowGauge c d R δ y * Real.cosh ((x - y) / 2) :=
    ((contDiff_quarticWindowGauge c d R δ).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_quarticWindowGauge c d R hδ).mul_right
  have hset : (∫ y in Icc (-r) r, quarticWindowGauge c d R δ y * Real.cosh ((x - y) / 2)) ≤
      ∫ y, quarticWindowGauge c d R δ y * Real.cosh ((x - y) / 2) :=
    setIntegral_le_integral hint (Eventually.of_forall fun y =>
      mul_nonneg (quarticWindowGauge_nonneg hd hdc hqR hδ y) (Real.cosh_pos _).le)
  have hpc : Continuous fun y : ℝ => quarticProfile c d y * (1 + (x - y) ^ 2 / 8) := by
    unfold quarticProfile; fun_prop
  have hlow : (∫ y in Icc (-r) r, quarticProfile c d y * (1 + (x - y) ^ 2 / 8)) ≤
      ∫ y in Icc (-r) r, quarticWindowGauge c d R δ y * Real.cosh ((x - y) / 2) :=
    setIntegral_mono_on hpc.integrableOn_Icc hint.integrableOn measurableSet_Icc fun y hy => by
      have hy' : -r ≤ y ∧ y ≤ r := hy
      have hyR : |y| ≤ R := abs_le.mpr ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
      rw [quarticWindowGauge_eq c d hδ (abs_le.mpr hy')]
      have hz : |(x - y) / 2| ≤ 1 := by
        rw [abs_div, abs_two, div_le_one (by norm_num)]
        have := abs_sub x y
        linarith
      have h1 := one_add_sq_div_two_le_cosh hz
      have h0 : 0 ≤ quarticProfile c d y := by
        have := quarticProfile_ge_of_le hd hdc hyR; linarith
      have e : 1 + (x - y) ^ 2 / 8 = 1 + ((x - y) / 2) ^ 2 / 2 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h1 h0
  have hval : (∫ y in Icc (-r) r, quarticProfile c d y * (1 + (x - y) ^ 2 / 8)) =
      2 * (r - c * r ^ 3 / 3 + d * r ^ 5 / 5) * (1 + x ^ 2 / 8) +
        2 * (r ^ 3 / 3 - c * r ^ 5 / 5 + d * r ^ 7 / 7) / 8 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    set G : ℝ → ℝ := fun y => (1 + x ^ 2 / 8) * (y - c * y ^ 3 / 3 + d * y ^ 5 / 5) -
      x / 4 * (y ^ 2 / 2 - c * y ^ 4 / 4 + d * y ^ 6 / 6) +
        (y ^ 3 / 3 - c * y ^ 5 / 5 + d * y ^ 7 / 7) / 8 with hG
    have hd' : ∀ y ∈ uIcc (-r) r, HasDerivAt G (quarticProfile c d y * (1 + (x - y) ^ 2 / 8)) y :=
      fun y _ => by
        have h := (((((hasDerivAt_id' y).sub ((hasDerivAt_pow 3 y).const_mul c |>.div_const 3)).add
          ((hasDerivAt_pow 5 y).const_mul d |>.div_const 5)).const_mul (1 + x ^ 2 / 8)).sub
          (((((hasDerivAt_pow 2 y).div_const 2).sub ((hasDerivAt_pow 4 y).const_mul c |>.div_const 4)).add
            ((hasDerivAt_pow 6 y).const_mul d |>.div_const 6)).const_mul (x / 4))).add
          (((((hasDerivAt_pow 3 y).div_const 3).sub ((hasDerivAt_pow 5 y).const_mul c |>.div_const 5)).add
            ((hasDerivAt_pow 7 y).const_mul d |>.div_const 7)).div_const 8)
        refine h.congr_deriv ?_
        unfold quarticProfile
        push_cast
        ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd' (hpc.intervalIntegrable _ _)]
    simp only [hG]
    ring
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory
