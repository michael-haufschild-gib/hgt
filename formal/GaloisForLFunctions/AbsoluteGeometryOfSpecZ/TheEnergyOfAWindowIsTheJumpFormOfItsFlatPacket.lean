import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheJetsPairFlatPacketsByTheirEndpoints
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheJumpFormSplitsIntoAWindowAndItsTails

/-!
# The energy of a window is the jump form of its flat packet

The flat packet of the window `(a, b]` of degree points is the function `e^{u/2}` on
`(log a, log b]` in the logarithmic coordinate: the constant `1` in the normalization of the
jets. It is not continuous, and Weil's functional is defined on `C²` tests. Its
Lévy–Khintchine expression is defined for every packet:

  `A(0)·h(0) + ∫_0^∞ 2ω(x)(h(0) − h(x)) dx`,   `h(x) = ∫ F(u)F(u + x) du`.

* **The autocorrelation** (`packetAutocorr_flatPacket_of_le`, `packetAutocorr_flatPacket_of_ge`):
  `h(x) = b e^{−x/2} − a e^{x/2}` for `0 ≤ x ≤ log(b/a)` and `h(x) = 0` beyond.
* **The jump integral** (`integral_levyJump_flatPacket`): in the variable `t = e^{−x/2}` the two
  rates `ω(x)(1 − e^{−x/2})` and `ω(x)(e^{x/2} − 1)` are rational, with elementary primitives.
* **The identity** (`flatPairing_window_eq_jumpForm`): the finite part of the energy of the jets
  inside the window, `W(b, b) − 2W(a, b) + W(a, a)`, is minus the Lévy–Khintchine expression of
  the flat packet. The arctangents of the three pieces cancel, and so does `log b`.
* **The limit** (`tendsto_windowEnergy_jumpForm`): the energy of the jets in `(aN, bN]` with the
  counterterm `log(n/2π)`, per degree point of the scale, tends to minus the Lévy–Khintchine
  expression of the flat packet of `(a, b]`.

So the closed forms on step packets and the limit on `C²` packets are values of one functional.
-/

open Finset Filter Topology MeasureTheory
open Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

local notation "ω" => _root_.RHTower.archLevyDensity
local notation "Ω" => _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv

/-! ### The flat packet of a window -/

/-- The flat packet of the window `(a, b]` in the logarithmic coordinate: `e^{u/2}` for
`log a < u ≤ log b`. -/
def flatPacket (a b : ℝ) (u : ℝ) : ℝ :=
  Set.indicator (Set.Ioc (Real.log a) (Real.log b)) (fun u => Real.exp (u / 2)) u

section FlatPacket

variable {a b : ℝ}

theorem flatPacket_mul_shift {x : ℝ} (hx : 0 ≤ x) (u : ℝ) :
    flatPacket a b u * flatPacket a b (u + x) =
      Set.indicator (Set.Ioc (Real.log a) (Real.log b - x))
        (fun u => Real.exp (x / 2) * Real.exp u) u := by
  simp only [flatPacket, Set.indicator_apply, Set.mem_Ioc]
  by_cases h1 : Real.log a < u ∧ u ≤ Real.log b - x
  · have h2 : Real.log a < u ∧ u ≤ Real.log b := ⟨h1.1, by linarith [h1.2]⟩
    have h3 : Real.log a < u + x ∧ u + x ≤ Real.log b :=
      ⟨by linarith [h1.1], by linarith [h1.2]⟩
    rw [if_pos h2, if_pos h3, if_pos h1, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · rw [if_neg h1]
    by_cases h2 : Real.log a < u ∧ u ≤ Real.log b
    · have h3 : ¬(Real.log a < u + x ∧ u + x ≤ Real.log b) := fun h =>
        h1 ⟨h2.1, by linarith [h.2]⟩
      rw [if_neg h3, mul_zero]
    · rw [if_neg h2, zero_mul]

/-- The autocorrelation of the flat packet inside the width of the window. -/
theorem packetAutocorr_flatPacket_of_le (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ Real.log b - Real.log a) :
    packetAutocorr (flatPacket a b) x = b * Real.exp (-x / 2) - a * Real.exp (x / 2) := by
  have hle : Real.log a ≤ Real.log b - x := by linarith
  have e1 : Real.exp (-x / 2) = Real.exp (x / 2) / Real.exp x := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [packetAutocorr,
    integral_congr_ae (Eventually.of_forall fun u => flatPacket_mul_shift hx0 u),
    integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_const_mul, integral_exp, Real.exp_sub, Real.exp_log ha,
    Real.exp_log hb, e1]
  have hex : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  field_simp

/-- The autocorrelation of the flat packet vanishes beyond the width of the window. -/
theorem packetAutocorr_flatPacket_of_ge {x : ℝ} (hx0 : 0 ≤ x)
    (hx : Real.log b - Real.log a ≤ x) : packetAutocorr (flatPacket a b) x = 0 := by
  rw [packetAutocorr,
    integral_congr_ae (Eventually.of_forall fun u => flatPacket_mul_shift hx0 u),
    Set.Ioc_eq_empty (not_lt.mpr (by linarith))]
  simp

theorem packetAutocorr_flatPacket_zero (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    packetAutocorr (flatPacket a b) 0 = b - a := by
  rw [packetAutocorr_flatPacket_of_le ha hb le_rfl
    (sub_nonneg.mpr (Real.log_le_log ha hab))]
  simp

end FlatPacket

/-! ### The two rates and their primitives -/

/-- `ω(x)(1 − e^{−x/2})` in the variable `t = e^{−x/2}`: `t/((1 + t)(1 + t²))`. -/
def flatRateOut (x : ℝ) : ℝ :=
  Real.exp (-x / 2) / ((1 + Real.exp (-x / 2)) * (1 + Real.exp (-x / 2) ^ 2))

/-- `ω(x)(e^{x/2} − 1)` in the variable `t = e^{−x/2}`: `1/((1 + t)(1 + t²))`. -/
def flatRateIn (x : ℝ) : ℝ :=
  1 / ((1 + Real.exp (-x / 2)) * (1 + Real.exp (-x / 2) ^ 2))

theorem exp_neg_two_mul_eq (x : ℝ) : Real.exp (-2 * x) = Real.exp (-x / 2) ^ 4 := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem archLevyDensity_mul_out {x : ℝ} (hx : 0 < x) :
    ω x * (1 - Real.exp (-x / 2)) = flatRateOut x := by
  have ht0 : 0 < Real.exp (-x / 2) := Real.exp_pos _
  have ht1 : Real.exp (-x / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold _root_.RHTower.archLevyDensity flatRateOut
  rw [exp_neg_two_mul_eq]
  generalize Real.exp (-x / 2) = t at ht0 ht1
  have h1 : (1 : ℝ) - t ^ 4 ≠ 0 := (sub_pos.mpr (pow_lt_one₀ ht0.le ht1 (by norm_num))).ne'
  have h2 : (1 : ℝ) + t ≠ 0 := by positivity
  have h3 : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_eq_div_iff h1 (mul_ne_zero h2 h3)]
  ring

theorem archLevyDensity_mul_in {x : ℝ} (hx : 0 < x) :
    ω x * (Real.exp (x / 2) - 1) = flatRateIn x := by
  have ht0 : 0 < Real.exp (-x / 2) := Real.exp_pos _
  have ht1 : Real.exp (-x / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hinv : Real.exp (x / 2) = (Real.exp (-x / 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  unfold _root_.RHTower.archLevyDensity flatRateIn
  rw [exp_neg_two_mul_eq, hinv]
  generalize Real.exp (-x / 2) = t at ht0 ht1
  have h1 : (1 : ℝ) - t ^ 4 ≠ 0 := (sub_pos.mpr (pow_lt_one₀ ht0.le ht1 (by norm_num))).ne'
  have h2 : (1 : ℝ) + t ≠ 0 := by positivity
  have h3 : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have h4 : t ≠ 0 := ht0.ne'
  rw [div_mul_eq_mul_div, div_eq_div_iff h1 (mul_ne_zero h2 h3)]
  field_simp
  ring

/-- A primitive of `flatRateOut`. -/
def flatPrimOut (x : ℝ) : ℝ :=
  -(Real.log (1 + Real.exp (-x / 2)) - Real.log (1 + Real.exp (-x / 2) ^ 2) / 2 +
    Real.arctan (Real.exp (-x / 2)))

/-- A primitive of `flatRateIn`. -/
def flatPrimIn (x : ℝ) : ℝ :=
  x + Real.log (1 + Real.exp (-x / 2)) + Real.log (1 + Real.exp (-x / 2) ^ 2) / 2 +
    Real.arctan (Real.exp (-x / 2))

theorem hasDerivAt_exp_neg_half (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y / 2)) (Real.exp (-x / 2) * (-1 / 2)) x :=
  ((hasDerivAt_id x).neg.div_const 2).exp

theorem hasDerivAt_flatPrimOut (x : ℝ) : HasDerivAt flatPrimOut (flatRateOut x) x := by
  have ht := hasDerivAt_exp_neg_half x
  have ht0 : 0 < Real.exp (-x / 2) := Real.exp_pos _
  have h1 := (ht.const_add 1).log (by positivity)
  have hsq : HasDerivAt (fun y : ℝ => Real.exp (-y / 2) ^ 2)
      (↑(2 : ℕ) * Real.exp (-x / 2) ^ (2 - 1) * (Real.exp (-x / 2) * (-1 / 2))) x := ht.pow 2
  have h2 := (hsq.const_add 1).log (by positivity)
  have h3 := ht.arctan
  have h := ((h1.sub (h2.div_const 2)).add h3).neg
  refine h.congr_deriv ?_
  unfold flatRateOut
  generalize Real.exp (-x / 2) = t at ht0
  have h2' : (1 : ℝ) + t ≠ 0 := by positivity
  have h3' : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  ring

theorem hasDerivAt_flatPrimIn (x : ℝ) : HasDerivAt flatPrimIn (flatRateIn x) x := by
  have ht := hasDerivAt_exp_neg_half x
  have ht0 : 0 < Real.exp (-x / 2) := Real.exp_pos _
  have h1 := (ht.const_add 1).log (by positivity)
  have hsq : HasDerivAt (fun y : ℝ => Real.exp (-y / 2) ^ 2)
      (↑(2 : ℕ) * Real.exp (-x / 2) ^ (2 - 1) * (Real.exp (-x / 2) * (-1 / 2))) x := ht.pow 2
  have h2 := (hsq.const_add 1).log (by positivity)
  have h3 := ht.arctan
  have h := ((((hasDerivAt_id x).add h1).add (h2.div_const 2)).add h3)
  refine h.congr_deriv ?_
  unfold flatRateIn
  generalize Real.exp (-x / 2) = t at ht0
  have h2' : (1 : ℝ) + t ≠ 0 := by positivity
  have h3' : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  ring

theorem continuous_flatRateOut : Continuous flatRateOut := by
  unfold flatRateOut
  exact Continuous.div (by fun_prop) (by fun_prop) fun x => by positivity

theorem continuous_flatRateIn : Continuous flatRateIn := by
  unfold flatRateIn
  exact Continuous.div (by fun_prop) (by fun_prop) fun x => by positivity

theorem integral_flatRateOut (c : ℝ) :
    ∫ x in (0 : ℝ)..c, flatRateOut x = flatPrimOut c - flatPrimOut 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_flatPrimOut x)
    (continuous_flatRateOut.intervalIntegrable _ _)

theorem integral_flatRateIn (c : ℝ) :
    ∫ x in (0 : ℝ)..c, flatRateIn x = flatPrimIn c - flatPrimIn 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_flatPrimIn x)
    (continuous_flatRateIn.intervalIntegrable _ _)

theorem flatPrimOut_zero : flatPrimOut 0 = -(Real.log 2 / 2 + Real.pi / 4) := by
  unfold flatPrimOut
  rw [neg_zero, zero_div, Real.exp_zero, one_pow, Real.arctan_one]
  norm_num
  ring

theorem flatPrimIn_zero : flatPrimIn 0 = 3 * Real.log 2 / 2 + Real.pi / 4 := by
  unfold flatPrimIn
  rw [neg_zero, zero_div, Real.exp_zero, one_pow, Real.arctan_one]
  norm_num
  ring

/-! ### The jump integral of the flat packet -/

section Jump

variable {a b : ℝ}

theorem levyJump_flatPacket_of_le (ha : 0 < a) (hab : a ≤ b) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ Real.log b - Real.log a) :
    levyJump (flatPacket a b) x = 2 * b * flatRateOut x + 2 * a * flatRateIn x := by
  have hb : 0 < b := ha.trans_le hab
  rw [levyJump, packetAutocorr_flatPacket_zero ha hb hab,
    packetAutocorr_flatPacket_of_le ha hb hx0.le hx, ← archLevyDensity_mul_out hx0,
    ← archLevyDensity_mul_in hx0]
  ring

theorem levyJump_flatPacket_of_ge (ha : 0 < a) (hab : a ≤ b) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : Real.log b - Real.log a ≤ x) :
    levyJump (flatPacket a b) x = 2 * (b - a) * ω x := by
  rw [levyJump, packetAutocorr_flatPacket_zero ha (ha.trans_le hab) hab,
    packetAutocorr_flatPacket_of_ge hx0 hx]
  ring

/-- **The jump integral of the flat packet**, by the two primitives and the tail. -/
theorem integral_levyJump_flatPacket (ha : 0 < a) (hab : a < b) :
    ∫ x in Set.Ioi 0, levyJump (flatPacket a b) x =
      2 * b * (flatPrimOut (Real.log b - Real.log a) - flatPrimOut 0) +
        2 * a * (flatPrimIn (Real.log b - Real.log a) - flatPrimIn 0) +
        2 * (b - a) * Ω (Real.log b - Real.log a) := by
  have hc : 0 < Real.log b - Real.log a := sub_pos.mpr (Real.log_lt_log ha hab)
  have hcontR : Continuous fun x => 2 * b * flatRateOut x + 2 * a * flatRateIn x :=
    (continuous_const.mul continuous_flatRateOut).add
      (continuous_const.mul continuous_flatRateIn)
  have heq1 : Set.EqOn (levyJump (flatPacket a b))
      (fun x => 2 * b * flatRateOut x + 2 * a * flatRateIn x)
      (Set.Ioc 0 (Real.log b - Real.log a)) := fun x hx =>
    levyJump_flatPacket_of_le ha hab.le hx.1 hx.2
  have heq2 : Set.EqOn (levyJump (flatPacket a b)) (fun x => 2 * (b - a) * ω x)
      (Set.Ioi (Real.log b - Real.log a)) := fun x hx =>
    levyJump_flatPacket_of_ge ha hab.le (hc.le.trans (le_of_lt hx)) (le_of_lt hx)
  have hI1 : IntegrableOn (levyJump (flatPacket a b)) (Set.Ioc 0 (Real.log b - Real.log a)) :=
    (hcontR.integrableOn_Ioc).congr_fun heq1.symm measurableSet_Ioc
  have hI0 : IntegrableOn (fun x => 2 * (b - a) * ω x) (Set.Ioi (Real.log b - Real.log a)) :=
    Integrable.const_mul (_root_.RHTower.WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hc) _
  have hI2 : IntegrableOn (levyJump (flatPacket a b)) (Set.Ioi (Real.log b - Real.log a)) :=
    hI0.congr_fun heq2.symm measurableSet_Ioi
  have i1 : IntervalIntegrable (fun x => 2 * b * flatRateOut x) volume 0
      (Real.log b - Real.log a) :=
    (continuous_const.mul continuous_flatRateOut).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => 2 * a * flatRateIn x) volume 0
      (Real.log b - Real.log a) :=
    (continuous_const.mul continuous_flatRateIn).intervalIntegrable _ _
  rw [← Set.Ioc_union_Ioi_eq_Ioi hc.le, setIntegral_union Set.Ioc_disjoint_Ioi_same
    measurableSet_Ioi hI1 hI2, setIntegral_congr_fun measurableSet_Ioc heq1,
    setIntegral_congr_fun measurableSet_Ioi heq2, integral_const_mul,
    _root_.RHTower.WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hc,
    ← intervalIntegral.integral_of_le hc.le, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_flatRateOut, integral_flatRateIn]

end Jump

/-! ### The identity -/

/-- **The finite part of the energy of a window is minus the Lévy–Khintchine expression of its
flat packet.** -/
theorem flatPairing_window_eq_jumpForm {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    flatPairing b b - 2 * flatPairing a b + flatPairing a a =
      -(EF.gammaBracket 0 * packetAutocorr (flatPacket a b) 0 +
        ∫ x in Set.Ioi 0, levyJump (flatPacket a b) x) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hb' : (0 : ℝ) < b := ha'.trans hab'
  have hc : 0 < Real.log b - Real.log a := sub_pos.mpr (Real.log_lt_log ha' hab')
  -- the variable `t = e^{−c/2}` at the width of the window, `t² = a/b`
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.exp (-(Real.log b - Real.log a) / 2) := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact Real.exp_pos _
  have ht1 : t < 1 := by
    rw [ht]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have ht2 : t ^ 2 = a / b := by
    rw [ht, ← Real.exp_nat_mul, ← Real.exp_log ha', ← Real.exp_log hb', ← Real.exp_sub,
      Real.log_exp, Real.log_exp]
    congr 1
    push_cast
    ring
  -- the logarithms at the width of the window
  have hZ : Real.log (1 + t ^ 2) = Real.log ((b : ℝ) + a) - Real.log b := by
    rw [ht2, ← Real.log_div (by positivity) hb'.ne']
    congr 1
    field_simp
  have hXY : Real.log (1 + t) + Real.log (1 - t) = Real.log ((b : ℝ) - a) - Real.log b := by
    rw [← Real.log_mul (by positivity) (by linarith),
      ← Real.log_div (by linarith) hb'.ne']
    congr 1
    have e : (1 + t) * (1 - t) = 1 - t ^ 2 := by ring
    rw [e, ht2]
    field_simp
  -- the constants
  have h2b : Real.log ((b : ℝ) + b) = Real.log 2 + Real.log b := by
    rw [← two_mul, Real.log_mul (by norm_num) hb'.ne']
  have h2a : Real.log ((a : ℝ) + a) = Real.log 2 + Real.log a := by
    rw [← two_mul, Real.log_mul (by norm_num) ha'.ne']
  have h8 : Real.log (8 * Real.pi) = 2 * Real.log 2 + Real.log (2 * Real.pi) := by
    rw [show (8 : ℝ) * Real.pi = 2 ^ 2 * (2 * Real.pi) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  rw [integral_levyJump_flatPacket ha' hab', packetAutocorr_flatPacket_zero ha' hb' hab'.le,
    _root_.RHTower.ArchimedeanAnomaly.gammaBracket_zero_eq, h8, flatPrimOut_zero, flatPrimIn_zero]
  unfold flatPairing flatPrimOut flatPrimIn _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv
  rw [← ht, hZ, h2b, h2a, sub_self, sub_self, zero_mul]
  linear_combination (-((b : ℝ) - a)) * hXY

/-- **The energy of a window, per degree point of the scale, tends to minus the
Lévy–Khintchine expression of its flat packet.** -/
theorem tendsto_windowEnergy_jumpForm {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    Tendsto (fun N : ℕ =>
        (windowEnergy (a * N) (b * N) -
          ∑ n ∈ Ioc (a * N) (b * N), Real.log ((n : ℝ) / (2 * Real.pi))) / N)
      atTop (𝓝 (-(EF.gammaBracket 0 * packetAutocorr (flatPacket a b) 0 +
        ∫ x in Set.Ioi 0, levyJump (flatPacket a b) x))) := by
  rw [← flatPairing_window_eq_jumpForm ha hab]
  exact tendsto_windowEnergy_sub_counterterm_div ha hab.le

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
