import GaloisForLFunctions.RHTower.ShiftedEulerFloorMobiusTailCoupling

/-!
# The floor discrepancy and the Möbius tail as one complementary shift incidence

After the logarithmic change of variables `X = e^t`, the two pieces of the shifted-Euler
summatory error are the lower and upper halves of a *single* projection incidence indexed by the
divisor `d`:

```text
e^{-(1+ω+δ)t} E_ω(e^t)
  = ∑_{d ≥ 1} μ(d) d^{-1-2ω} ( d^{-δ} V_{log d} k_{ω,δ} − (1/(1+ω)) (I − P_{log d}) q_δ )(t),
```

with `V_a` the right shift, `P_a` the projection onto `[a, ∞)`, `q_δ(t) = e^{-δ t}` and
`k_{ω,δ}(t) = e^{-(1+ω+δ)t} R_ω(e^t)`.  At the unique normalization `δ = 0` both branches carry
the *same* arithmetic coefficient `μ(d) d^{-1-2ω}`, and the common upper input is the constant
function, which is not in `L²(0,∞)`: its squared norm is exactly `1/(2δ)`.

* `suzukiCoupledErrorReal_eq` — Theorem A of the parent card at a real argument;
* `coupledErrorVector_eq_tsum` — **equation (8)**, and at `δ = 0` **equation (15)**;
* `integral_dampingMode_sq`, `tendsto_integral_dampingMode_sq` — **equation (18)**;
* `integrableOn_floorIncidenceVector_sq`, `integrableOn_dampingMode_sq` — equation (5),
  membership of both vectors in `H`.
-/

open Finset ArithmeticFunction Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-! ## The shifted-Euler error at a real argument -/

theorem suzukiShiftedSummatoryReal_eq (ω : ℝ) (X : ℝ) :
    suzukiShiftedSummatoryReal ω X
      = ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
          * ∑ m ∈ Finset.Icc 1 (⌊X⌋₊ / d), (m : ℝ) ^ ω := by
  rw [show suzukiShiftedSummatoryReal ω X = suzukiShiftedSummatory ω ⌊X⌋₊ from rfl,
    suzukiShiftedSummatory_eq]

/-- **Theorem A at a real argument.** -/
theorem suzukiCoupledErrorReal_eq {ω : ℝ} (hω : 0 < ω) {X : ℝ} (hX : 0 ≤ X) :
    suzukiCoupledErrorReal ω X
      = (∑ d ∈ Finset.Icc 1 ⌊X⌋₊, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
            * powerSumRemainder ω (X / (d : ℝ)))
        - X ^ (1 + ω) / (1 + ω) * mobiusShiftTail ω ⌊X⌋₊ := by
  have hterm : ∀ d ∈ Finset.Icc 1 ⌊X⌋₊,
      ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω) * ∑ m ∈ Finset.Icc 1 (⌊X⌋₊ / d), (m : ℝ) ^ ω
        = ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω) * powerSumRemainder ω (X / (d : ℝ))
          + X ^ (1 + ω) / (1 + ω)
            * (((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 + 2 * ω))) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hfl : ⌊X / (d : ℝ)⌋₊ = ⌊X⌋₊ / d := Nat.floor_div_natCast X d
    have hsum : ∑ m ∈ Finset.Icc 1 (⌊X⌋₊ / d), (m : ℝ) ^ ω
        = powerSumRemainder ω (X / (d : ℝ))
          + (X / (d : ℝ)) ^ (1 + ω) / (1 + ω) := by
      rw [← sum_Icc_rpow_eq_remainder hω, hfl]
    have hdd : (d : ℝ) ^ (-ω) * (X / (d : ℝ)) ^ (1 + ω)
        = X ^ (1 + ω) * (d : ℝ) ^ (-(1 + 2 * ω)) := by
      rw [Real.div_rpow hX hd0.le, div_eq_mul_inv, ← Real.rpow_neg hd0.le]
      rw [show (d : ℝ) ^ (-ω) * (X ^ (1 + ω) * (d : ℝ) ^ (-(1 + ω)))
          = X ^ (1 + ω) * ((d : ℝ) ^ (-ω) * (d : ℝ) ^ (-(1 + ω))) by ring]
      rw [← Real.rpow_add hd0]
      congr 2
      ring
    rw [hsum]
    have hexp : ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
          * (powerSumRemainder ω (X / (d : ℝ)) + (X / (d : ℝ)) ^ (1 + ω) / (1 + ω))
        = ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω) * powerSumRemainder ω (X / (d : ℝ))
          + ((moebius d : ℤ) : ℝ) * ((d : ℝ) ^ (-ω) * (X / (d : ℝ)) ^ (1 + ω)) / (1 + ω) := by
      ring
    rw [hexp, hdd]
    ring
  have hM : suzukiMainTermReal ω X
      = suzukiEulerDensityConstant ω * X ^ (1 + ω) / (1 + ω) := rfl
  have hsplit := tsum_moebius_split hω ⌊X⌋₊
  have hr := suzukiEulerDensityConstant_eq_tsum hω
  have hfin : (∑ d ∈ Finset.Icc 1 ⌊X⌋₊, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 + 2 * ω)))
      = suzukiEulerDensityConstant ω - mobiusShiftTail ω ⌊X⌋₊ := by
    rw [hr]
    linarith [hsplit]
  rw [suzukiCoupledErrorReal, suzukiShiftedSummatoryReal_eq, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, ← Finset.mul_sum, hfin, hM]
  ring

/-! ## The Hilbert-space vectors of the incidence -/

/-- The right shift `V_a f (t) = 1_{t ≥ a} f(t − a)`, equation (1). -/
def rightShift (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun t => if a ≤ t then f (t - a) else 0

/-- The lower incidence projection `P_a f (t) = 1_{t ≥ a} f(t)`, equation (2). -/
def lowerIncidence (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun t => if a ≤ t then f t else 0

/-- The complementary upper incidence `(I − P_a) f (t) = 1_{t < a} f(t)`, equation (2). -/
def upperIncidence (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun t => if a ≤ t then 0 else f t

theorem lowerIncidence_add_upperIncidence (a : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    lowerIncidence a f t + upperIncidence a f t = f t := by
  simp only [lowerIncidence, upperIncidence]
  by_cases h : a ≤ t <;> simp [h]

/-- The boundary damping mode `q_δ(t) = e^{−δ t}`. -/
def dampingMode (δ : ℝ) : ℝ → ℝ := fun t => Real.exp (-(δ * t))

/-- The floor-discrepancy vector `k_{ω,δ}(t) = e^{−(1+ω+δ)t} R_ω(e^t)`, equation (5). -/
def floorIncidenceVector (ω δ : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (-((1 + ω + δ) * t)) * powerSumRemainder ω (Real.exp t)

/-- The normalized coupled error `F_{ω,δ}(t) = e^{−(1+ω+δ)t} E_ω(e^t)`, equation (7). -/
def coupledErrorVector (ω δ : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (-((1 + ω + δ) * t)) * suzukiCoupledErrorReal ω (Real.exp t)

/-! ### The boundary mode is in `H` exactly when `δ > 0`, with norm `1/(2δ)` -/

theorem integrableOn_dampingMode_sq {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t => dampingMode δ t ^ 2) (Set.Ioi (0 : ℝ)) volume := by
  have h := exp_neg_integrableOn_Ioi (0 : ℝ) (b := 2 * δ) (by linarith)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  simp only [dampingMode]
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- **Equation (18).**  The squared `H`-norm of the boundary mode is `1/(2δ)`. -/
theorem integral_dampingMode_sq {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in Set.Ioi (0 : ℝ), dampingMode δ t ^ 2) = 1 / (2 * δ) := by
  have hb : (0 : ℝ) < 2 * δ := by linarith
  have hcongr : (∫ t in Set.Ioi (0 : ℝ), dampingMode δ t ^ 2)
      = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(2 * δ * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [dampingMode]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 hb
  rw [mul_zero, integral_exp_neg_Ioi] at h
  rw [hcongr]
  rw [show (fun t : ℝ => Real.exp (-(2 * δ * t)))
      = fun t : ℝ => (fun x : ℝ => Real.exp (-x)) (2 * δ * t) from rfl, h]
  rw [neg_zero, Real.exp_zero, smul_eq_mul, mul_one, one_div]

/-- The boundary mode leaves `H` as `δ ↓ 0`: the common upper input of the incidence is not in
`L²(0,∞)`. -/
theorem tendsto_integral_dampingMode_sq :
    Tendsto (fun δ : ℝ => (∫ t in Set.Ioi (0 : ℝ), dampingMode δ t ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have h : Tendsto (fun δ : ℝ => δ⁻¹ * (2 : ℝ)⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    Filter.Tendsto.atTop_mul_const (by norm_num) tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [integral_dampingMode_sq (Set.mem_Ioi.mp hδ)]
  field_simp


/-! ### The floor-discrepancy vector is in `H` -/

theorem abs_floorIncidenceVector_le {ω δ : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    |floorIncidenceVector ω δ t| ≤ 2 * Real.exp (-((1 + δ) * t)) := by
  have hexp : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht
  have hR : |powerSumRemainder ω (Real.exp t)| ≤ (Real.exp t + 1) ^ ω :=
    abs_powerSumRemainder_le ω hω0.le (Real.exp_nonneg t)
  have hstep : (Real.exp t + 1) ^ ω ≤ 2 * Real.exp t ^ ω := by
    have h1 : Real.exp t + 1 ≤ 2 * Real.exp t := by linarith
    have h2 : (Real.exp t + 1) ^ ω ≤ (2 * Real.exp t) ^ ω :=
      Real.rpow_le_rpow (by positivity) h1 hω0.le
    have h3 : (2 * Real.exp t) ^ ω = (2 : ℝ) ^ ω * Real.exp t ^ ω :=
      Real.mul_rpow (by norm_num) (Real.exp_nonneg t)
    have h4 : (2 : ℝ) ^ ω ≤ 2 := by
      calc (2 : ℝ) ^ ω ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hω1
        _ = 2 := by norm_num
    have h5 : (0 : ℝ) ≤ Real.exp t ^ ω := Real.rpow_nonneg (Real.exp_nonneg t) _
    nlinarith [h2, h3.le, h3.ge, h4, h5]
  have hpow : Real.exp t ^ ω = Real.exp (ω * t) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
    congr 1
    ring
  have hposfac : (0 : ℝ) < Real.exp (-((1 + ω + δ) * t)) := Real.exp_pos _
  rw [floorIncidenceVector, abs_mul, abs_of_pos hposfac]
  have hkey : Real.exp (-((1 + ω + δ) * t)) * (2 * Real.exp (ω * t))
      = 2 * Real.exp (-((1 + δ) * t)) := by
    rw [mul_comm (2 : ℝ) (Real.exp (ω * t)), ← mul_assoc, ← Real.exp_add]
    rw [show -((1 + ω + δ) * t) + ω * t = -((1 + δ) * t) by ring]
    ring
  calc Real.exp (-((1 + ω + δ) * t)) * |powerSumRemainder ω (Real.exp t)|
      ≤ Real.exp (-((1 + ω + δ) * t)) * (2 * Real.exp (ω * t)) := by
        rw [← hpow]
        exact mul_le_mul_of_nonneg_left (le_trans hR hstep) hposfac.le
    _ = 2 * Real.exp (-((1 + δ) * t)) := hkey

theorem measurable_powerSumRemainder (ω : ℝ) : Measurable (powerSumRemainder ω) := by
  have hstep : Measurable fun Y : ℝ => ∑ i ∈ Finset.range (⌊Y⌋₊ + 1), (i : ℝ) ^ ω := by
    have hnat : Measurable fun Y : ℝ => ⌊Y⌋₊ := Nat.measurable_floor
    exact (measurable_from_top (f := fun n : ℕ => ∑ i ∈ Finset.range (n + 1), (i : ℝ) ^ ω)).comp
      hnat
  have hmain : Measurable fun Y : ℝ => Y ^ (1 + ω) / (1 + ω) := by
    fun_prop
  exact hstep.sub hmain

theorem measurable_floorIncidenceVector (ω δ : ℝ) : Measurable (floorIncidenceVector ω δ) := by
  refine Measurable.mul ?_ ?_
  · exact (Real.measurable_exp.comp (measurable_id.const_mul _).neg)
  · exact (measurable_powerSumRemainder ω).comp Real.measurable_exp

theorem integrableOn_floorIncidenceVector_sq {ω δ : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1)
    (hδ : 0 < δ) :
    IntegrableOn (fun t => floorIncidenceVector ω δ t ^ 2) (Set.Ioi (0 : ℝ)) volume := by
  have hmaj : IntegrableOn (fun t : ℝ => 4 * Real.exp (-(2 * (1 + δ)) * t))
      (Set.Ioi (0 : ℝ)) volume :=
    (exp_neg_integrableOn_Ioi (0 : ℝ) (b := 2 * (1 + δ)) (by linarith)).const_mul 4
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((measurable_floorIncidenceVector ω δ).pow_const 2).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    have hb := abs_floorIncidenceVector_le hω0 hω1 (δ := δ) ht0
    have habs : |floorIncidenceVector ω δ t| ≥ 0 := abs_nonneg _
    have hsq : floorIncidenceVector ω δ t ^ 2 = |floorIncidenceVector ω δ t| ^ 2 := by
      rw [sq_abs]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hsq]
    have hexp : Real.exp (-((1 + δ) * t)) ^ 2 = Real.exp (-(2 * (1 + δ)) * t) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    nlinarith [hb, habs, hexp.le, hexp.ge, Real.exp_pos (-((1 + δ) * t))]


/-! ## Equation (8): the exact regularized complementary-shift incidence -/

/-- The lower (floor-discrepancy) branch of the incidence at the divisor `d+1`. -/
def incidenceLower (ω δ t : ℝ) (d : ℕ) : ℝ :=
  ((moebius (d + 1) : ℤ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω))
    * (((d + 1 : ℕ) : ℝ) ^ (-δ)
        * rightShift (Real.log ((d + 1 : ℕ) : ℝ)) (floorIncidenceVector ω δ) t)

/-- The upper (Möbius-tail) branch of the incidence at the divisor `d+1`. -/
def incidenceUpper (ω δ t : ℝ) (d : ℕ) : ℝ :=
  ((moebius (d + 1) : ℤ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω))
    * ((1 / (1 + ω)) * upperIncidence (Real.log ((d + 1 : ℕ) : ℝ)) (dampingMode δ) t)

theorem log_le_iff_succ_le_floor {t : ℝ} (ht : 0 ≤ t) (d : ℕ) :
    Real.log ((d + 1 : ℕ) : ℝ) ≤ t ↔ d + 1 ≤ ⌊Real.exp t⌋₊ := by
  have hd0 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  rw [Real.log_le_iff_le_exp hd0, Nat.le_floor_iff (Real.exp_nonneg t)]

theorem incidenceLower_eq {ω δ : ℝ} {t : ℝ} (ht : 0 ≤ t) (d : ℕ) :
    incidenceLower ω δ t d
      = if d + 1 ≤ ⌊Real.exp t⌋₊ then
          Real.exp (-((1 + ω + δ) * t)) * (((moebius (d + 1) : ℤ) : ℝ)
            * ((d + 1 : ℕ) : ℝ) ^ (-ω)
            * powerSumRemainder ω (Real.exp t / ((d + 1 : ℕ) : ℝ)))
        else 0 := by
  have hd0 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  by_cases hcase : d + 1 ≤ ⌊Real.exp t⌋₊
  · have hlog : Real.log ((d + 1 : ℕ) : ℝ) ≤ t := (log_le_iff_succ_le_floor ht d).mpr hcase
    rw [if_pos hcase, incidenceLower, rightShift, if_pos hlog, floorIncidenceVector]
    have hexpsub : Real.exp (t - Real.log ((d + 1 : ℕ) : ℝ))
        = Real.exp t / ((d + 1 : ℕ) : ℝ) := by
      rw [Real.exp_sub, Real.exp_log hd0]
    have hfac : Real.exp (-((1 + ω + δ) * (t - Real.log ((d + 1 : ℕ) : ℝ))))
        = Real.exp (-((1 + ω + δ) * t)) * ((d + 1 : ℕ) : ℝ) ^ (1 + ω + δ) := by
      rw [Real.rpow_def_of_pos hd0, ← Real.exp_add]
      congr 1
      ring
    rw [hexpsub, hfac]
    have hpow : ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω)) * ((d + 1 : ℕ) : ℝ) ^ (-δ)
          * ((d + 1 : ℕ) : ℝ) ^ (1 + ω + δ)
        = ((d + 1 : ℕ) : ℝ) ^ (-ω) := by
      rw [← Real.rpow_add hd0, ← Real.rpow_add hd0]
      congr 1
      ring
    calc ((moebius (d + 1) : ℤ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω))
            * (((d + 1 : ℕ) : ℝ) ^ (-δ)
              * (Real.exp (-((1 + ω + δ) * t)) * ((d + 1 : ℕ) : ℝ) ^ (1 + ω + δ)
                * powerSumRemainder ω (Real.exp t / ((d + 1 : ℕ) : ℝ))))
        = Real.exp (-((1 + ω + δ) * t)) * (((moebius (d + 1) : ℤ) : ℝ)
            * (((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω)) * ((d + 1 : ℕ) : ℝ) ^ (-δ)
              * ((d + 1 : ℕ) : ℝ) ^ (1 + ω + δ))
            * powerSumRemainder ω (Real.exp t / ((d + 1 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [hpow]
  · have hlog : ¬ Real.log ((d + 1 : ℕ) : ℝ) ≤ t := fun h =>
      hcase ((log_le_iff_succ_le_floor ht d).mp h)
    rw [if_neg hcase, incidenceLower, rightShift, if_neg hlog]
    ring

theorem incidenceUpper_eq {ω δ : ℝ} {t : ℝ} (ht : 0 ≤ t) (d : ℕ) :
    incidenceUpper ω δ t d
      = if d + 1 ≤ ⌊Real.exp t⌋₊ then 0
        else (1 / (1 + ω)) * Real.exp (-(δ * t))
          * (((moebius (d + 1) : ℤ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω))) := by
  by_cases hcase : d + 1 ≤ ⌊Real.exp t⌋₊
  · have hlog : Real.log ((d + 1 : ℕ) : ℝ) ≤ t := (log_le_iff_succ_le_floor ht d).mpr hcase
    rw [if_pos hcase, incidenceUpper, upperIncidence, if_pos hlog]
    ring
  · have hlog : ¬ Real.log ((d + 1 : ℕ) : ℝ) ≤ t := fun h =>
      hcase ((log_le_iff_succ_le_floor ht d).mp h)
    rw [if_neg hcase, incidenceUpper, upperIncidence, if_neg hlog, dampingMode]
    ring

theorem summable_natSucc_rpow {ω : ℝ} (hω : 0 < ω) :
    Summable (fun d : ℕ => ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω))) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + 2 * ω))) := by
    have h' : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (1 + 2 * ω)) :=
      Real.summable_one_div_nat_rpow.mpr (by linarith)
    refine h'.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  exact h.comp_injective (add_left_injective 1)

theorem summable_incidenceUpper {ω δ : ℝ} (hω : 0 < ω) (t : ℝ) :
    Summable (incidenceUpper ω δ t) := by
  have h1ω : (0 : ℝ) < 1 / (1 + ω) := by positivity
  refine Summable.of_norm_bounded
    ((summable_natSucc_rpow hω).mul_left ((1 / (1 + ω)) * Real.exp (-(δ * t)))) fun d => ?_
  have hnn : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hμ := abs_moebiusReal_le_one (d + 1)
  have hup : |upperIncidence (Real.log ((d + 1 : ℕ) : ℝ)) (dampingMode δ) t|
      ≤ Real.exp (-(δ * t)) := by
    simp only [upperIncidence, dampingMode]
    by_cases h : Real.log ((d + 1 : ℕ) : ℝ) ≤ t
    · rw [if_pos h, abs_zero]
      exact (Real.exp_pos _).le
    · rw [if_neg h, abs_of_pos (Real.exp_pos _)]
  rw [Real.norm_eq_abs, incidenceUpper, abs_mul, abs_mul, abs_of_nonneg hnn,
    abs_mul, abs_of_pos h1ω]
  have hA : |((moebius (d + 1) : ℤ) : ℝ)| * ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω))
      ≤ ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω)) := by
    nlinarith [hμ, hnn, abs_nonneg (((moebius (d + 1) : ℤ) : ℝ))]
  have hB : (1 / (1 + ω)) * |upperIncidence (Real.log ((d + 1 : ℕ) : ℝ)) (dampingMode δ) t|
      ≤ (1 / (1 + ω)) * Real.exp (-(δ * t)) := mul_le_mul_of_nonneg_left hup h1ω.le
  have hBnn : (0 : ℝ)
      ≤ (1 / (1 + ω)) * |upperIncidence (Real.log ((d + 1 : ℕ) : ℝ)) (dampingMode δ) t| := by
    positivity
  calc |((moebius (d + 1) : ℤ) : ℝ)| * ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω))
        * ((1 / (1 + ω)) * |upperIncidence (Real.log ((d + 1 : ℕ) : ℝ)) (dampingMode δ) t|)
      ≤ ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω)) * ((1 / (1 + ω)) * Real.exp (-(δ * t))) :=
        mul_le_mul hA hB hBnn hnn
    _ = (1 / (1 + ω)) * Real.exp (-(δ * t)) * ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω)) := by ring

theorem summable_incidenceLower {ω δ : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    Summable (incidenceLower ω δ t) := by
  refine summable_of_ne_finset_zero (s := Finset.range ⌊Real.exp t⌋₊) fun d hd => ?_
  rw [incidenceLower_eq ht d, if_neg]
  intro hcon
  exact hd (Finset.mem_range.mpr (by omega))

theorem tsum_incidenceLower {ω δ : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    ∑' d : ℕ, incidenceLower ω δ t d
      = Real.exp (-((1 + ω + δ) * t))
        * ∑ d ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
            * powerSumRemainder ω (Real.exp t / (d : ℝ)) := by
  classical
  set N : ℕ := ⌊Real.exp t⌋₊ with hN
  have hfin : ∑' d : ℕ, incidenceLower ω δ t d
      = ∑ d ∈ Finset.range N, incidenceLower ω δ t d := by
    refine tsum_eq_sum fun d hd => ?_
    rw [incidenceLower_eq ht d, if_neg]
    intro hcon
    exact hd (Finset.mem_range.mpr (by omega))
  rw [hfin, Finset.mul_sum]
  refine Finset.sum_nbij' (i := fun d => d + 1) (j := fun m => m - 1) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_range] at hd
    rw [Finset.mem_Icc]
    omega
  · intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_range]
    omega
  · intro d _
    omega
  · intro m hm
    rw [Finset.mem_Icc] at hm
    omega
  · intro d hd
    rw [Finset.mem_range] at hd
    rw [incidenceLower_eq ht d, if_pos (by omega)]

theorem tsum_incidenceUpper {ω δ : ℝ} (hω : 0 < ω) {t : ℝ} (ht : 0 ≤ t) :
    ∑' d : ℕ, incidenceUpper ω δ t d
      = (1 / (1 + ω)) * Real.exp (-(δ * t)) * mobiusShiftTail ω ⌊Real.exp t⌋₊ := by
  classical
  set N : ℕ := ⌊Real.exp t⌋₊ with hN
  have hsum := (summable_incidenceUpper (δ := δ) hω t).sum_add_tsum_nat_add N
  have hhead : ∑ d ∈ Finset.range N, incidenceUpper ω δ t d = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [Finset.mem_range] at hd
    rw [incidenceUpper_eq ht d, if_pos (by omega)]
  rw [hhead, zero_add] at hsum
  rw [← hsum, mobiusShiftTail, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [incidenceUpper_eq ht (i + N), if_neg (by omega)]
  have hcast : ((i + N + 1 : ℕ) : ℝ) = ((i + (N + 1) : ℕ) : ℝ) := rfl
  have hcast2 : moebius (i + N + 1) = moebius (i + (N + 1)) := rfl
  rw [hcast, hcast2]

/-- **Equation (8).**  The regularized coupled error is exactly the complementary shift
incidence: for each divisor `d` the *same* arithmetic coefficient `μ(d) d^{-1-2ω}` weights a
right-shifted floor-discrepancy vector selected by `P_d` and the upper incidence `I − P_d`
applied to the boundary mode. -/
theorem coupledErrorVector_eq_tsum {ω δ : ℝ} (hω : 0 < ω) {t : ℝ} (ht : 0 ≤ t) :
    coupledErrorVector ω δ t
      = ∑' d : ℕ, (incidenceLower ω δ t d - incidenceUpper ω δ t d) := by
  have hsub := (summable_incidenceLower (ω := ω) (δ := δ) ht).tsum_sub
    (summable_incidenceUpper (δ := δ) hω t)
  rw [hsub, tsum_incidenceLower ht, tsum_incidenceUpper hω ht]
  rw [coupledErrorVector, suzukiCoupledErrorReal_eq hω (Real.exp_nonneg t)]
  have hpow : (Real.exp t) ^ (1 + ω) = Real.exp ((1 + ω) * t) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
    congr 1
    ring
  rw [hpow]
  have hexp : Real.exp (-((1 + ω + δ) * t)) * (Real.exp ((1 + ω) * t) / (1 + ω))
      = (1 / (1 + ω)) * Real.exp (-(δ * t)) := by
    rw [div_eq_mul_inv, ← mul_assoc, ← Real.exp_add]
    rw [show -((1 + ω + δ) * t) + (1 + ω) * t = -(δ * t) by ring]
    ring
  rw [mul_sub, ← hexp]
  ring


/-- **Equation (15).**  At the unique normalization `δ = 0` the two branches of the incidence
carry the identical arithmetic coefficient `μ(d) d^{-1-2ω}`. -/
theorem coupledErrorVector_eq_tsum_zero {ω : ℝ} (hω : 0 < ω) {t : ℝ} (ht : 0 ≤ t) :
    coupledErrorVector ω 0 t
      = ∑' d : ℕ, (incidenceLower ω 0 t d - incidenceUpper ω 0 t d) :=
  coupledErrorVector_eq_tsum hω ht

/-- **Equation (17).**  At `δ = 0` the lower branch is the arithmetic coefficient times the pure
right shift of `k_{ω,0}`. -/
theorem incidenceLower_zero_delta {ω : ℝ} (t : ℝ) (d : ℕ) :
    incidenceLower ω 0 t d
      = ((moebius (d + 1) : ℤ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω))
        * rightShift (Real.log ((d + 1 : ℕ) : ℝ)) (floorIncidenceVector ω 0) t := by
  have hd0 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  rw [incidenceLower, neg_zero, Real.rpow_zero, one_mul]

/-- **Equation (19).**  On the squarefree support the common incidence coefficient is the signed
square of the normalized Möbius channel amplitude `μ(d) d^{-1/2-ω}`. -/
theorem incidence_coefficient_eq_signed_square {ω : ℝ} {d : ℕ} (hd : 0 < d)
    (hsq : Squarefree d) :
    ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 + 2 * ω))
      = ((moebius d : ℤ) : ℝ)
        * (((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 / 2 + ω))) ^ 2 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmu : ((moebius d : ℤ) : ℝ) ^ 2 = 1 := by
    rw [moebius_apply_of_squarefree hsq]
    rcases Nat.even_or_odd (cardFactors d) with h | h
    · rw [Even.neg_one_pow h]
      norm_num
    · rw [Odd.neg_one_pow h]
      norm_num
  have hpow : ((d : ℝ) ^ (-(1 / 2 + ω))) ^ 2 = (d : ℝ) ^ (-(1 + 2 * ω)) := by
    rw [← Real.rpow_natCast ((d : ℝ) ^ (-(1 / 2 + ω))) 2, ← Real.rpow_mul hd0.le]
    congr 1
    push_cast
    ring
  calc ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 + 2 * ω))
      = ((moebius d : ℤ) : ℝ) * (((moebius d : ℤ) : ℝ) ^ 2
          * ((d : ℝ) ^ (-(1 / 2 + ω))) ^ 2) := by
        rw [hmu, hpow]
        ring
    _ = ((moebius d : ℤ) : ℝ)
          * (((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 / 2 + ω))) ^ 2 := by ring

end

end RHTower
