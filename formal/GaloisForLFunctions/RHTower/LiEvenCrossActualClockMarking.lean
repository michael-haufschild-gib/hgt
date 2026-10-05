import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDampedCutoffEscape
import GaloisForLFunctions.HTGeometry.LaplaceMomentPositivity
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitiveCumulant
import GaloisForLFunctions.RHTower.ProfileRenewalLogKernel

/-!
# Exponential marking of the integrated actual clock

For `p, r > 0` put `a = p - r`, `σ_p(t) = e^{-pt} P(t)/t` and the marked density
`κ_{p,r}(t) = r e^{-rt} D_a(t)`.

* (marking) `κ = (r e^{-r·}) ⋆ σ_p`, `κ' + rκ = r σ_p`, and `e^{pt} κ(t)/r = e^{at} D_a(t)`;
* (Laplace) for `s > max(-r, β - p)`, `∫_0^∞ e^{-st} κ = r H(p+s)/(r+s)`, `H(q) = log Φ(1/q)`;
  in particular the total mass is `H(p)` whenever `p > β`;
* (positivity range) `κ > 0` on `t > 0` iff `r ≤ p - β`, and below that range
  `T_n e^{(p-β)T_n} κ(T_n) → -(r/2) Σ_{q∈Q} (β-p+r)/((β-p+r)² + u_q²) < 0`;
* (compensated cone) for `p - r ≥ β`, every moment `∫ t^n e^{-st} κ` is positive, equals
  `(-1)^n h^{(n)}(s)`, and `Σ_{k≤n} (r+s)^k (-1)^k H^{(k)}(p+s)/k! > 0`; for `r > p - β` some moment
  is negative;
* (pole) for `a > β`, `d = a - β`, `q = r + d`: `D_a = H(a) - Tail_a`,
  `|Tail_a(t)| ≤ (A/2) e^{-dt}(t/d + 1/d²)`, `κ = r H(a) e^{-rt} + R` with
  `|R(t)| ≤ (Ar/2) e^{-qt}(t/d + 1/d²)`, `R' + rR = r σ_p`, and the moments satisfy
  `|m_n - H(a) n!/r^n| ≤ (Ar/2)((n+1)!/(d q^{n+2}) + n!/(d² q^{n+1}))`, `r^n m_n/n! → H(a)`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "β" => liEvenCrossActualClockMaxGrowthRate
local notation "u" => liEvenCrossActualClockReciprocalFrequency
local notation "D" => liEvenCrossActualClockDampedCutoff

/-! ## Continuity of the profile -/

theorem liEvenCrossActualClockResponse_zero : liEvenCrossActualClockResponse 0 = 0 := by
  unfold liEvenCrossActualClockResponse
  simp

theorem liEvenCrossActualClockPrimitive_div_eq_dslope (t : ℝ) : P t / t = dslope P 0 t := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [div_zero, dslope_same, (hasDerivAt_liEvenCrossActualClockPrimitive 0).deriv,
      liEvenCrossActualClockResponse_zero]
  · rw [dslope_of_ne _ ht, slope_def_field]
    simp [liEvenCrossActualClockPrimitive]

theorem continuous_liEvenCrossActualClockPrimitive_div : Continuous fun t => P t / t := by
  have e : (fun t => P t / t) = dslope P 0 := funext liEvenCrossActualClockPrimitive_div_eq_dslope
  rw [e, continuous_iff_continuousAt]
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · exact continuousAt_dslope_same.2 (hasDerivAt_liEvenCrossActualClockPrimitive 0).differentiableAt
  · exact (continuousAt_dslope_of_ne ht).2 continuous_liEvenCrossActualClockPrimitive.continuousAt

theorem continuous_liEvenCrossActualClockDampedProfile (a : ℝ) :
    Continuous fun t => Real.exp (-a * t) * P t / t := by
  have := ((by fun_prop : Continuous fun t : ℝ => Real.exp (-a * t))).mul
    continuous_liEvenCrossActualClockPrimitive_div
  refine this.congr fun t => ?_
  simp only [Pi.mul_apply]
  ring

theorem hasDerivAt_liEvenCrossActualClockDampedCutoff (a t : ℝ) :
    HasDerivAt (D a) (Real.exp (-a * t) * P t / t) t :=
  ((continuous_liEvenCrossActualClockDampedProfile a).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem continuous_liEvenCrossActualClockDampedCutoff (a : ℝ) : Continuous (D a) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_liEvenCrossActualClockDampedCutoff a t).continuousAt

/-- `|D_a(t)| ≤ (A/2) t² e^{max(β-a,0) t}` for `t ≥ 0`. -/
theorem abs_liEvenCrossActualClockDampedCutoff_le (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |D a t| ≤ xiShiftAbsoluteMass 0 / 2 * t ^ 2 * Real.exp (max (β - a) 0 * t) := by
  have hA := xiShiftAbsoluteMass_nonneg 0
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (C := xiShiftAbsoluteMass 0 / 2 * t * Real.exp (max (β - a) 0 * t))
    (f := fun s => Real.exp (-a * s) * P s / s) fun s hs => by
      rw [uIoc_of_le ht] at hs
      rw [Real.norm_eq_abs]
      refine (abs_exp_mul_liEvenCrossActualClockPrimitive_div_le a hs.1).trans ?_
      have h1 : (β - a) * s ≤ max (β - a) 0 * t :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hs.1.le).trans
          (mul_le_mul_of_nonneg_left hs.2 (le_max_right _ _))
      have h2 := Real.exp_le_exp.2 h1
      have h3 : xiShiftAbsoluteMass 0 / 2 * s ≤ xiShiftAbsoluteMass 0 / 2 * t :=
        mul_le_mul_of_nonneg_left hs.2 (by positivity)
      exact mul_le_mul h3 h2 (Real.exp_pos _).le (by positivity)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at h
  unfold liEvenCrossActualClockDampedCutoff
  refine h.trans (le_of_eq ?_)
  ring

/-! ## The marked density -/

/-- `σ_p(t) = e^{-pt} P(t)/t`. -/
def liClockMarkedSource (p t : ℝ) : ℝ := Real.exp (-p * t) * P t / t

/-- `κ_{p,r}(t) = r e^{-rt} D_{p-r}(t)`. -/
def liClockMarkedDensity (p r t : ℝ) : ℝ := r * Real.exp (-r * t) * D (p - r) t

theorem continuous_liClockMarkedSource (p : ℝ) : Continuous (liClockMarkedSource p) :=
  continuous_liEvenCrossActualClockDampedProfile p

theorem continuous_liClockMarkedDensity (p r : ℝ) : Continuous (liClockMarkedDensity p r) :=
  ((by fun_prop : Continuous fun t : ℝ => r * Real.exp (-r * t))).mul
    (continuous_liEvenCrossActualClockDampedCutoff _)

/-- **Exact marking (I15).**  `κ_{p,r} = (r e^{-r·}) ⋆ σ_p`. -/
theorem liClockMarkedDensity_eq_volterraConv (p r t : ℝ) :
    liClockMarkedDensity p r t =
      volterraConv (fun s => r * Real.exp (-r * s)) (liClockMarkedSource p) t := by
  unfold liClockMarkedDensity volterraConv liEvenCrossActualClockDampedCutoff liClockMarkedSource
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only
  have e : Real.exp (-r * t) * Real.exp (-(p - r) * s) = Real.exp (-r * (t - s)) * Real.exp (-p * s) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [show r * Real.exp (-r * t) * (Real.exp (-(p - r) * s) * P s / s) =
    r * (Real.exp (-r * t) * Real.exp (-(p - r) * s)) * P s / s by ring, e]
  ring

/-- **Exact inverse (I18).**  `κ' + rκ = r σ_p`. -/
theorem hasDerivAt_liClockMarkedDensity (p r t : ℝ) :
    HasDerivAt (liClockMarkedDensity p r)
      (-r * liClockMarkedDensity p r t + r * liClockMarkedSource p t) t := by
  have h1 : HasDerivAt (fun t => r * Real.exp (-r * t)) (r * (Real.exp (-r * t) * (-r))) t := by
    have := ((hasDerivAt_id' t).const_mul (-r)).exp.const_mul r
    exact this.congr_deriv (by ring)
  have h := h1.mul (hasDerivAt_liEvenCrossActualClockDampedCutoff (p - r) t)
  refine h.congr_deriv ?_
  unfold liClockMarkedDensity liClockMarkedSource
  have e : Real.exp (-r * t) * Real.exp (-(p - r) * t) = Real.exp (-p * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [show r * Real.exp (-r * t) * (Real.exp (-(p - r) * t) * P t / t) =
    r * (Real.exp (-r * t) * Real.exp (-(p - r) * t)) * P t / t by ring, e]
  ring

/-- **Unmarked clock (I19).**  `e^{pt} κ(t)/r = e^{at} D_a(t) = ∫_0^t e^{a(t-v)} P(v)/v dv`. -/
theorem exp_mul_liClockMarkedDensity_div {p r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    Real.exp (p * t) * liClockMarkedDensity p r t / r = Real.exp ((p - r) * t) * D (p - r) t ∧
      Real.exp ((p - r) * t) * D (p - r) t =
        ∫ v in (0 : ℝ)..t, Real.exp ((p - r) * (t - v)) * P v / v := by
  constructor
  · unfold liClockMarkedDensity
    have e : Real.exp (p * t) * Real.exp (-r * t) = Real.exp ((p - r) * t) := by
      rw [← Real.exp_add]; ring_nf
    field_simp
    have e' : Real.exp (p * t) * Real.exp (-(t * r)) = Real.exp (t * (p - r)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e']
    ring
  · unfold liEvenCrossActualClockDampedCutoff
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v _ => ?_
    rw [show Real.exp ((p - r) * t) * (Real.exp (-(p - r) * v) * P v / v) =
      Real.exp ((p - r) * t) * Real.exp (-(p - r) * v) * P v / v by ring, ← Real.exp_add]
    ring_nf

/-! ## Integrability and the Laplace transform of the mark -/

/-- `|κ(t)| ≤ (rA/2) t² e^{(max(β-a,0) - r) t}` for `t ≥ 0`, `a = p - r`, `r ≥ 0`. -/
theorem abs_liClockMarkedDensity_le {p r : ℝ} (hr : 0 ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    |liClockMarkedDensity p r t| ≤
      r * (xiShiftAbsoluteMass 0 / 2) * t ^ 2 * Real.exp ((max (β - (p - r)) 0 - r) * t) := by
  unfold liClockMarkedDensity
  rw [abs_mul, abs_mul, abs_of_nonneg hr, Real.abs_exp]
  have h := abs_liEvenCrossActualClockDampedCutoff_le (p - r) ht
  calc r * Real.exp (-r * t) * |D (p - r) t| ≤ r * Real.exp (-r * t) *
      (xiShiftAbsoluteMass 0 / 2 * t ^ 2 * Real.exp (max (β - (p - r)) 0 * t)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [show (max (β - (p - r)) 0 - r) * t = -r * t + max (β - (p - r)) 0 * t by ring,
        Real.exp_add]; ring

theorem integrableOn_liClockMarkedDensity_moment {p r : ℝ} (hr : 0 ≤ r) (n : ℕ) {s : ℝ}
    (hs : max (β - (p - r)) 0 - r < s) :
    IntegrableOn (fun t => t ^ n * Real.exp (-(s * t)) * liClockMarkedDensity p r t) (Ioi 0) := by
  set c := s - (max (β - (p - r)) 0 - r)
  have hc : 0 < c := by simp only [c]; linarith
  have hb : IntegrableOn (fun t => r * (xiShiftAbsoluteMass 0 / 2) * ((n + 2).factorial : ℝ) *
      (dividedPowerFn (n + 2) t * Real.exp (-(c * t)))) (Ioi 0) :=
    (integrableOn_dividedPowerFn_mul_exp_neg (n + 2) hc).const_mul _
  refine hb.mono' ((((by fun_prop : Continuous fun t : ℝ => t ^ n * Real.exp (-(s * t)))).mul
    (continuous_liClockMarkedDensity p r)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht0 : 0 < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (pow_pos ht0 n), Real.abs_exp]
  have hf : ((n + 2).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  calc t ^ n * Real.exp (-(s * t)) * |liClockMarkedDensity p r t| ≤ t ^ n * Real.exp (-(s * t)) *
      (r * (xiShiftAbsoluteMass 0 / 2) * t ^ 2 * Real.exp ((max (β - (p - r)) 0 - r) * t)) :=
        mul_le_mul_of_nonneg_left (abs_liClockMarkedDensity_le hr ht0.le) (by positivity)
    _ = _ := by
        unfold dividedPowerFn
        rw [show -(c * t) = -(s * t) + (max (β - (p - r)) 0 - r) * t by simp only [c]; ring,
          Real.exp_add]
        field_simp
        ring

private theorem complex_integral_eq_ofReal (s : ℝ) (f : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-((s : ℂ) * t)) * (f t : ℂ) =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * f t : ℝ) : ℂ) := by
  have h1 : ∫ t in Ioi (0 : ℝ), Complex.exp (-((s : ℂ) * t)) * (f t : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((Real.exp (-(s * t)) * f t : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by push_cast; ring_nf
  rw [h1]
  exact integral_ofReal

/-- **Marked Laplace transform.**  For `r > 0`, `s > -r` and `p + s > β`,
`∫_0^∞ e^{-st} κ_{p,r}(t) dt = r H(p+s)/(r+s)`, `H(q) = log Φ(1/q)`. -/
theorem integral_exp_mul_liClockMarkedDensity {p r s : ℝ} (hr : 0 < r) (hs : -r < s)
    (hps : β < p + s) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * liClockMarkedDensity p r t =
      r / (r + s) * Real.log (liClockThetaGeneratorReal (p + s)⁻¹) := by
  have hf : Continuous fun t : ℝ => r * Real.exp (-r * t) := by fun_prop
  have hg := continuous_liClockMarkedSource p
  have hfi : IntegrableOn (fun t => Real.exp (-((s : ℂ).re * t)) * |r * Real.exp (-r * t)|) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 (show 0 < s + r by linarith)).const_mul r
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    simp only [Complex.ofReal_re]
    rw [abs_of_pos (by positivity), show -(s + r) * t = -(s * t) + -r * t by ring, Real.exp_add]
    ring
  have hgi : IntegrableOn (fun t => Real.exp (-((s : ℂ).re * t)) * |liClockMarkedSource p t|) (Ioi 0) := by
    have := (integrableOn_liClockPrimitiveLaplaceMoment 0 hps).abs
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    simp only [Complex.ofReal_re, liClockMarkedSource, pow_zero, one_mul]
    rw [abs_mul, Real.abs_exp, mul_div_assoc, abs_mul, Real.abs_exp, ← mul_assoc, ← Real.exp_add]
    ring_nf
  have hconv := integral_Ioi_cexp_mul_volterraConv hf hg hfi hgi
  rw [complex_integral_eq_ofReal, complex_integral_eq_ofReal, complex_integral_eq_ofReal,
    ← Complex.ofReal_mul] at hconv
  have hreal := Complex.ofReal_injective hconv
  have e1 : ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * volterraConv (fun s => r * Real.exp (-r * s))
      (liClockMarkedSource p) t = ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * liClockMarkedDensity p r t :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [liClockMarkedDensity_eq_volterraConv]
  have e2 : ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (r * Real.exp (-r * t)) = r / (r + s) := by
    have h := integral_exp_mul_Ioi (show -(r + s) < 0 by linarith) 0
    have e : ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (r * Real.exp (-r * t)) =
        r * ∫ t in Ioi (0 : ℝ), Real.exp (-(r + s) * t) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [show -(r + s) * t = -(s * t) + -r * t by ring, Real.exp_add]; ring
    rw [e, h, mul_zero, Real.exp_zero]
    field_simp
  have e3 : ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * liClockMarkedSource p t =
      Real.log (liClockThetaGeneratorReal (p + s)⁻¹) := by
    rw [log_liClockThetaGeneratorReal_inv_eq hps]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [liClockMarkedSource, pow_zero, one_mul]
    rw [mul_div_assoc, ← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [e1, e2, e3] at hreal
  exact hreal

/-- The total marked mass is `H(p)` for every `r > 0` and `p > β`. -/
theorem integral_liClockMarkedDensity {p r : ℝ} (hr : 0 < r) (hp : β < p) :
    ∫ t in Ioi (0 : ℝ), liClockMarkedDensity p r t = Real.log (liClockThetaGeneratorReal p⁻¹) := by
  have h := integral_exp_mul_liClockMarkedDensity (s := 0) hr (by linarith) (by linarith)
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, add_zero, div_self hr.ne'] at h
  exact h

/-! ## The positivity range of the mark -/

theorem liClockMarkedDensity_pos {p r t : ℝ} (hr : 0 < r) (ha : β ≤ p - r) (ht : 0 < t) :
    0 < liClockMarkedDensity p r t :=
  mul_pos (mul_pos hr (Real.exp_pos _)) (liEvenCrossActualClockDampedCutoff_pos ha ht)

theorem liClockMarkedDensity_pos_of_rh (hRH : RiemannHypothesis) {p r t : ℝ} (hr : 0 < r)
    (ht : 0 < t) : 0 < liClockMarkedDensity p r t :=
  mul_pos (mul_pos hr (Real.exp_pos _)) (liEvenCrossActualClockDampedCutoff_pos_of_rh hRH _ ht)

/-- **Marking range (I16).**  If RH fails, `κ_{p,r} ≥ 0` on `t > 0` iff `r ≤ p - β`. -/
theorem liClockMarkedDensity_nonneg_iff_of_not_rh (hnot : ¬RiemannHypothesis) {p r : ℝ}
    (hr : 0 < r) : (∀ t, 0 < t → 0 ≤ liClockMarkedDensity p r t) ↔ r ≤ p - β := by
  rw [show r ≤ p - β ↔ β ≤ p - r by constructor <;> intro h <;> linarith,
    ← liEvenCrossActualClockDampedCutoff_nonneg_iff_of_not_rh hnot (p - r)]
  refine forall_congr' fun t => imp_congr_right fun _ => ?_
  unfold liClockMarkedDensity
  constructor
  · intro h; exact nonneg_of_mul_nonneg_right h (mul_pos hr (Real.exp_pos _)) |> fun h' => by
      rwa [mul_comm, ← mul_assoc, mul_comm (D (p - r) t)] at h
  · intro h; exact mul_nonneg (mul_pos hr (Real.exp_pos _)).le h

/-- **Negative marks (I16a).**  If RH fails and `r > p - β`, the top packet gives clocks with
`T_n e^{(p-β)T_n} κ(T_n) → -(r/2) Σ_{q∈S} (β-p+r)/((β-p+r)² + u_q²) < 0`. -/
theorem liClockMarkedDensity_escape_of_not_rh (hnot : ¬RiemannHypothesis) {p r : ℝ} (hr : 0 < r)
    (hlt : p - β < r) :
    ∃ S : Finset XiZeroCopy, S.Nonempty ∧
      (∀ q, q ∈ S ↔ liEvenCrossActualClockReciprocalGrowthRate q = β) ∧
      ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
        Tendsto (fun n => t n * Real.exp ((p - β) * t n) * liClockMarkedDensity p r (t n)) atTop
          (𝓝 (-(r / 2) * ∑ q ∈ S, (β - p + r) / ((β - p + r) ^ 2 + u q ^ 2))) ∧
        -(r / 2) * ∑ q ∈ S, (β - p + r) / ((β - p + r) ^ 2 + u q ^ 2) < 0 := by
  obtain ⟨S, hSne, hS, t, _, htop, hlim, hneg, _⟩ :=
    liEvenCrossActualClockDampedCutoff_escape_of_not_rh hnot (a := p - r) (by linarith)
  have hsum : ∑ q ∈ S, (β - (p - r)) / ((β - (p - r)) ^ 2 + u q ^ 2) =
      ∑ q ∈ S, (β - p + r) / ((β - p + r) ^ 2 + u q ^ 2) :=
    Finset.sum_congr rfl fun q _ => by ring_nf
  refine ⟨S, hSne, hS, t, htop, ?_, ?_⟩
  · have := hlim.const_mul r
    rw [hsum, show r * (-(1 / 2) * ∑ q ∈ S, (β - p + r) / ((β - p + r) ^ 2 + u q ^ 2)) =
      -(r / 2) * ∑ q ∈ S, (β - p + r) / ((β - p + r) ^ 2 + u q ^ 2) by ring] at this
    refine this.congr fun n => ?_
    unfold liClockMarkedDensity
    have e : Real.exp ((p - β) * t n) * Real.exp (-r * t n) = Real.exp (-((β - (p - r)) * t n)) := by
      rw [← Real.exp_add]; ring_nf
    rw [show t n * Real.exp ((p - β) * t n) * (r * Real.exp (-r * t n) * D (p - r) (t n)) =
      r * (t n * (Real.exp ((p - β) * t n) * Real.exp (-r * t n)) * D (p - r) (t n)) by ring, e]
  · rw [hsum] at hneg
    have : -(r / 2) * ∑ q ∈ S, (β - p + r) / ((β - p + r) ^ 2 + u q ^ 2) =
        r * (-(1 / 2) * ∑ q ∈ S, (β - p + r) / ((β - p + r) ^ 2 + u q ^ 2)) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg hr hneg

/-! ## The compensated cone -/

theorem measurable_liClockMarkedDensity (p r : ℝ) : Measurable (liClockMarkedDensity p r) :=
  (continuous_liClockMarkedDensity p r).measurable

private theorem hint_of_le {p r c : ℝ} (hr : 0 ≤ r) (hc1 : max (β - (p - r)) 0 - r ≤ c) :
    ∀ n : ℕ, ∀ s, c < s → IntegrableOn
      (fun t => t ^ n * Real.exp (-(s * t)) * liClockMarkedDensity p r t) (Ioi 0) :=
  fun n _ hs => integrableOn_liClockMarkedDensity_moment hr n (hc1.trans_lt hs)

private theorem hc1_admissible {p r : ℝ} (ha : β ≤ p - r) : max (β - (p - r)) 0 - r ≤ -r := by
  rw [max_eq_right (by linarith)]; linarith

private theorem hint_admissible {p r : ℝ} (hr : 0 < r) (ha : β ≤ p - r) :
    ∀ n : ℕ, ∀ s, -r < s → IntegrableOn
      (fun t => t ^ n * Real.exp (-(s * t)) * liClockMarkedDensity p r t) (Ioi 0) :=
  hint_of_le hr.le (hc1_admissible ha)

/-- Positive marks have positive compensated moments on their convergence domain. -/
theorem laplaceWeightedMoment_liClockMarkedDensity_pos_of {p r c : ℝ} (hr : 0 < r)
    (hc1 : max (β - (p - r)) 0 - r ≤ c) (hpos : ∀ t, 0 < t → 0 < liClockMarkedDensity p r t)
    (n : ℕ) {s : ℝ} (hs : c < s) : 0 < laplaceWeightedMoment (liClockMarkedDensity p r) n s := by
  have hint := hint_of_le hr.le hc1 n s hs
  have hpos' : ∀ t ∈ Ioi (0 : ℝ), 0 < t ^ n * Real.exp (-(s * t)) * liClockMarkedDensity p r t :=
    fun t ht => mul_pos (mul_pos (pow_pos ht n) (Real.exp_pos _)) (hpos t ht)
  unfold laplaceWeightedMoment
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hpos' t ht).le) hint]
  have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun t => t ^ n * Real.exp (-(s * t)) *
      liClockMarkedDensity p r t) ∩ Ioi 0 := fun t ht => ⟨(hpos' t ht).ne', ht⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- Every compensated moment of an admissible mark is positive. -/
theorem laplaceWeightedMoment_liClockMarkedDensity_pos {p r : ℝ} (hr : 0 < r) (ha : β ≤ p - r) (n : ℕ)
    {s : ℝ} (hs : -r < s) : 0 < laplaceWeightedMoment (liClockMarkedDensity p r) n s :=
  laplaceWeightedMoment_liClockMarkedDensity_pos_of hr (hc1_admissible ha)
    (fun _ ht => liClockMarkedDensity_pos hr ha ht) n hs

theorem iteratedDeriv_liClockMarkedLaplace_of {p r c : ℝ} (hr : 0 ≤ r)
    (hc1 : max (β - (p - r)) 0 - r ≤ c) (n : ℕ) {s : ℝ} (hs : c < s) :
    iteratedDeriv n (laplaceWeightedMoment (liClockMarkedDensity p r) 0) s =
      (-1) ^ n * laplaceWeightedMoment (liClockMarkedDensity p r) n s :=
  iteratedDeriv_laplaceWeightedMoment_zero (measurable_liClockMarkedDensity p r) (hint_of_le hr hc1) n hs

/-- `(d/ds)^n ∫ e^{-st} κ = (-1)^n ∫ t^n e^{-st} κ` on `s > -r`. -/
theorem iteratedDeriv_liClockMarkedLaplace {p r : ℝ} (hr : 0 < r) (ha : β ≤ p - r) (n : ℕ) {s : ℝ}
    (hs : -r < s) :
    iteratedDeriv n (laplaceWeightedMoment (liClockMarkedDensity p r) 0) s =
      (-1) ^ n * laplaceWeightedMoment (liClockMarkedDensity p r) n s :=
  iteratedDeriv_liClockMarkedLaplace_of hr.le (hc1_admissible ha) n hs

theorem liClockMarkedLaplace_eq_of {p r c : ℝ} (hr : 0 < r) (hc2 : -r ≤ c) (hc3 : β - p ≤ c)
    {s : ℝ} (hs : c < s) :
    laplaceWeightedMoment (liClockMarkedDensity p r) 0 s =
      r * Real.log (liClockThetaGeneratorReal (s + p)⁻¹) * (s + r)⁻¹ := by
  have h := integral_exp_mul_liClockMarkedDensity hr (hc2.trans_lt hs) (show β < p + s by linarith)
  unfold laplaceWeightedMoment
  simp only [pow_zero, one_mul]
  rw [h, add_comm p s, add_comm r s]
  ring

theorem liClockMarkedLaplace_eq {p r : ℝ} (hr : 0 < r) (ha : β ≤ p - r) {s : ℝ} (hs : -r < s) :
    laplaceWeightedMoment (liClockMarkedDensity p r) 0 s =
      r * Real.log (liClockThetaGeneratorReal (s + p)⁻¹) * (s + r)⁻¹ :=
  liClockMarkedLaplace_eq_of hr le_rfl (by linarith) hs

private theorem iteratedDeriv_inv_add (r : ℝ) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y : ℝ => (y + r)⁻¹) x = (-1) ^ j * j.factorial * ((x + r) ^ (j + 1))⁻¹ := by
  have h := iter_deriv_inv_linear (𝕜 := ℝ) j 1 r
  rw [iteratedDeriv_eq_iterate]
  have e : (fun y : ℝ => (y + r)⁻¹) = fun y : ℝ => (1 * y + r)⁻¹ := by simp
  rw [e, h]
  simp only [one_pow, mul_one, one_mul]
  rw [show (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]

/-- **Compensated identity.**  On the convergence domain `s > c`,
`Σ_{k≤n} (r+s)^k (-1)^k H^{(k)}(p+s)/k! = (r+s)^{n+1}/(r n!) ∫ t^n e^{-st} κ`. -/
theorem compensated_liClockMarked_eq_of {p r c : ℝ} (hr : 0 < r)
    (hc1 : max (β - (p - r)) 0 - r ≤ c) (hc2 : -r ≤ c) (hc3 : β - p ≤ c) (n : ℕ) {s : ℝ}
    (hs : c < s) :
    ∑ k ∈ Finset.range (n + 1), (r + s) ^ k * (-1) ^ k *
        iteratedDeriv k (fun q => Real.log (liClockThetaGeneratorReal q⁻¹)) (p + s) / k.factorial =
      (r + s) ^ (n + 1) / (r * n.factorial) * laplaceWeightedMoment (liClockMarkedDensity p r) n s := by
  set H : ℝ → ℝ := fun q => Real.log (liClockThetaGeneratorReal q⁻¹)
  have hps : 0 < s + p := by linarith [liEvenCrossActualClockMaxGrowthRate_nonneg]
  have hsr : 0 < s + r := by linarith
  have hH : ∀ m : ℕ, ContDiffAt ℝ m (fun x => H (x + p)) s := fun m =>
    ((contDiff_liClockThetaLogGenerator.contDiffAt.comp s
      ((contDiffAt_id.add contDiffAt_const).inv hps.ne')).of_le (by exact_mod_cast le_top))
  have hI : ∀ m : ℕ, ContDiffAt ℝ m (fun x : ℝ => (x + r)⁻¹) s := fun m =>
    ((contDiffAt_id.add contDiffAt_const).inv hsr.ne').of_le (by exact_mod_cast le_top)
  have hev : laplaceWeightedMoment (liClockMarkedDensity p r) 0 =ᶠ[𝓝 s]
      (fun x => r * H (x + p)) * fun x => (x + r)⁻¹ := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    rw [liClockMarkedLaplace_eq_of hr hc2 hc3 hx]
    simp only [Pi.mul_apply, H]
  have hmom := iteratedDeriv_liClockMarkedLaplace_of hr.le hc1 n hs
  rw [hev.iteratedDeriv_eq n, iteratedDeriv_mul (contDiffAt_const.mul (hH n)) (hI n)] at hmom
  have hm : laplaceWeightedMoment (liClockMarkedDensity p r) n s = (-1) ^ n *
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (r * iteratedDeriv i H (s + p)) *
        ((-1) ^ (n - i) * (n - i).factorial * ((s + r) ^ (n - i + 1))⁻¹) := by
    have h1 : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    have e : ∀ i, iteratedDeriv i (fun x => r * H (x + p)) s = r * iteratedDeriv i H (s + p) := by
      intro i
      rw [iteratedDeriv_const_mul r (hH i)]
      rw [iteratedDeriv_comp_add_const]
    simp only [e, iteratedDeriv_inv_add] at hmom
    linear_combination (-((-1 : ℝ) ^ n)) * hmom - laplaceWeightedMoment (liClockMarkedDensity p r) n s * h1
  rw [hm, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hin
  rw [Nat.add_sub_cancel_left, add_comm s p, add_comm s r]
  have hc := Nat.choose_mul_factorial_mul_factorial (le_add_right le_rfl : i ≤ i + d)
  rw [Nat.add_sub_cancel_left] at hc
  have hc' : ((i + d).choose i : ℝ) * (d.factorial : ℝ) = (i + d).factorial / i.factorial := by
    have hfi : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [eq_div_iff hfi]
    have : ((i + d).choose i : ℝ) * (i.factorial : ℝ) * (d.factorial : ℝ) = (i + d).factorial := by
      exact_mod_cast hc
    linarith [this]
  have hsgn : (-1 : ℝ) ^ (i + d) * (-1) ^ d = (-1) ^ i := by
    rw [← pow_add, show i + d + d = i + 2 * d by ring, pow_add, pow_mul]; simp
  have hrs : r + s ≠ 0 := by linarith
  have hpow : (r + s) ^ (i + d + 1) * ((r + s) ^ (d + 1))⁻¹ = (r + s) ^ i := by
    rw [show i + d + 1 = i + (d + 1) by ring, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hrs),
      mul_one]
  set G := iteratedDeriv i H (p + s)
  have e : (r + s) ^ (i + d + 1) / (r * ((i + d).factorial : ℝ)) *
      ((-1) ^ (i + d) * (((i + d).choose i : ℝ) * (r * G) *
        ((-1) ^ d * (d.factorial : ℝ) * ((r + s) ^ (d + 1))⁻¹))) =
      ((-1) ^ (i + d) * (-1) ^ d) * (((i + d).choose i : ℝ) * (d.factorial : ℝ)) *
        ((r + s) ^ (i + d + 1) * ((r + s) ^ (d + 1))⁻¹) * G * (r / r) / ((i + d).factorial : ℝ) := by
    ring
  rw [e, hsgn, hc', hpow, div_self hr.ne']
  have hf : ((i + d).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfi : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-- **Compensated cone (I17).**  For `r > 0`, `p - r ≥ β` and `s > -r`,
`Σ_{k≤n} (r+s)^k (-1)^k H^{(k)}(p+s)/k! = (r+s)^{n+1}/(r n!) ∫ t^n e^{-st} κ`. -/
theorem compensated_liClockMarked_eq {p r : ℝ} (hr : 0 < r) (ha : β ≤ p - r) (n : ℕ) {s : ℝ}
    (hs : -r < s) :
    ∑ k ∈ Finset.range (n + 1), (r + s) ^ k * (-1) ^ k *
        iteratedDeriv k (fun q => Real.log (liClockThetaGeneratorReal q⁻¹)) (p + s) / k.factorial =
      (r + s) ^ (n + 1) / (r * n.factorial) * laplaceWeightedMoment (liClockMarkedDensity p r) n s :=
  compensated_liClockMarked_eq_of hr (hc1_admissible ha) le_rfl (by linarith) n hs

/-- The compensated sums are positive on the admissible marking range. -/
theorem compensated_liClockMarked_pos {p r : ℝ} (hr : 0 < r) (ha : β ≤ p - r) (n : ℕ) {s : ℝ}
    (hs : -r < s) :
    0 < ∑ k ∈ Finset.range (n + 1), (r + s) ^ k * (-1) ^ k *
      iteratedDeriv k (fun q => Real.log (liClockThetaGeneratorReal q⁻¹)) (p + s) / k.factorial := by
  rw [compensated_liClockMarked_eq hr ha n hs]
  have hrs : 0 < r + s := by linarith
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact mul_pos (div_pos (pow_pos hrs _) (mul_pos hr hf))
    (laplaceWeightedMoment_liClockMarkedDensity_pos hr ha n hs)

/-- **RH branch of the compensated cone.**  Under RH every rate `r > 0` gives positive compensated
moments and sums on `s > max(-p, -r)`. -/
theorem compensated_liClockMarked_pos_of_rh (hRH : RiemannHypothesis) {p r : ℝ} (hr : 0 < r)
    (n : ℕ) {s : ℝ} (hs : max (-p) (-r) < s) :
    0 < laplaceWeightedMoment (liClockMarkedDensity p r) n s ∧
      0 < ∑ k ∈ Finset.range (n + 1), (r + s) ^ k * (-1) ^ k *
        iteratedDeriv k (fun q => Real.log (liClockThetaGeneratorReal q⁻¹)) (p + s) / k.factorial := by
  have hβ := liEvenCrossActualClockMaxGrowthRate_eq_zero_iff.2 hRH
  have hc1 : max (β - (p - r)) 0 - r ≤ max (-p) (-r) := by
    rw [hβ]
    rcases le_total (0 - (p - r)) (0 : ℝ) with h | h
    · rw [max_eq_right h, zero_sub]; exact le_max_right (-p) (-r)
    · rw [max_eq_left h]; linarith [le_max_left (-p) (-r)]
  have hc2 : -r ≤ max (-p) (-r) := le_max_right _ _
  have hc3 : β - p ≤ max (-p) (-r) := by rw [hβ, zero_sub]; exact le_max_left _ _
  have hpos := laplaceWeightedMoment_liClockMarkedDensity_pos_of hr hc1
    (fun _ ht => liClockMarkedDensity_pos_of_rh hRH hr ht) n hs
  refine ⟨hpos, ?_⟩
  rw [compensated_liClockMarked_eq_of hr hc1 hc2 hc3 n hs]
  have hrs : 0 < r + s := by linarith [le_max_right (-p) (-r)]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact mul_pos (div_pos (pow_pos hrs _) (mul_pos hr hf)) hpos

/-- **Forbidden range (I17 converse).**  If RH fails, `p > β` and `r > p - β`, some compensated
moment `∫ t^n e^{-st} κ` with `s > 0` is negative. -/
theorem exists_laplaceWeightedMoment_liClockMarkedDensity_neg (hnot : ¬RiemannHypothesis) {p r : ℝ}
    (hr : 0 < r) (hp : β < p) (hlt : p - β < r) :
    ∃ n : ℕ, ∃ s, 0 < s ∧ laplaceWeightedMoment (liClockMarkedDensity p r) n s < 0 := by
  by_contra h
  push Not at h
  have hnn : ∀ t, 0 < t → 0 ≤ liClockMarkedDensity p r t := by
    intro t ht
    refine nonneg_of_laplaceMoments_nonneg (γ := 0) ht
      (continuous_liClockMarkedDensity p r).continuousAt (fun n s hs => ?_) (fun n s hs => h n s hs)
    refine integrableOn_liClockMarkedDensity_moment hr.le n ?_
    have : max (β - (p - r)) 0 < s + r := max_lt (by linarith) (by linarith)
    linarith
  have := (liClockMarkedDensity_nonneg_iff_of_not_rh hnot hr).1 hnn
  linarith

/-! ## The positive pole and the signed remainder -/

/-- The signed tail `Tail_a(t) = ∫_t^∞ e^{-as} P(s)/s ds`. -/
def liEvenCrossActualClockDampedTail (a t : ℝ) : ℝ :=
  ∫ s in Ioi t, Real.exp (-a * s) * P s / s

private theorem integrableOn_profile_Ioi {a : ℝ} (ha : β < a) :
    IntegrableOn (fun s => Real.exp (-a * s) * P s / s) (Ioi 0) := by
  refine (integrableOn_liClockPrimitiveLaplaceMoment 0 ha).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [pow_zero, one_mul, neg_mul]
  ring

/-- **Pole decomposition (I20).**  `D_a(t) = H(a) - Tail_a(t)` for `a > β`, `t ≥ 0`. -/
theorem liEvenCrossActualClockDampedCutoff_eq_sub_tail {a : ℝ} (ha : β < a) {t : ℝ} (ht : 0 ≤ t) :
    D a t = Real.log (liClockThetaGeneratorReal a⁻¹) - liEvenCrossActualClockDampedTail a t := by
  have hi := integrableOn_profile_Ioi ha
  rw [log_liClockThetaGeneratorReal_inv_eq ha]
  have e : liClockPrimitiveLaplaceMoment 0 a = ∫ s in Ioi (0 : ℝ), Real.exp (-a * s) * P s / s :=
    setIntegral_congr_fun measurableSet_Ioi fun s _ => by simp only [pow_zero, one_mul, neg_mul]; ring
  rw [e, ← Ioc_union_Ioi_eq_Ioi ht, setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi ht))]
  unfold liEvenCrossActualClockDampedCutoff liEvenCrossActualClockDampedTail
  rw [intervalIntegral.integral_of_le ht]
  ring

private theorem integral_Ioi_mul_exp_neg {d : ℝ} (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Ioi t, s * Real.exp (-(d * s)) = Real.exp (-(d * t)) * (t / d + 1 / d ^ 2) := by
  set F : ℝ → ℝ := fun s => -(Real.exp (-(d * s)) * (s / d + 1 / d ^ 2))
  have hF : ∀ s, HasDerivAt F (s * Real.exp (-(d * s))) s := by
    intro s
    have h1 := ((hasDerivAt_id' s).const_mul d).fun_neg.exp
    have h2 := ((hasDerivAt_id' s).div_const d).add_const (1 / d ^ 2)
    refine (h1.mul h2).fun_neg.congr_deriv ?_
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => s * Real.exp (-(d * s))) atTop (𝓝 0) := by
      have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop hd)).const_mul (1 / d)
      refine (this.congr fun s => ?_).trans (by simp)
      simp only [Function.comp_apply, id, pow_one]
      field_simp
    have h2 : Tendsto (fun s : ℝ => Real.exp (-(d * s))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hd)
    have := ((h1.div_const d).add (h2.const_mul (1 / d ^ 2))).neg
    simp only [zero_div, mul_zero, add_zero, neg_zero] at this
    refine this.congr fun s => ?_
    simp only [F]; ring
  have hint : IntegrableOn (fun s => s * Real.exp (-(d * s))) (Ioi t) := by
    have := (integrableOn_dividedPowerFn_mul_exp_neg 1 hd).mono_set (Ioi_subset_Ioi ht)
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp [dividedPowerFn]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hF t).continuousAt.continuousWithinAt
    (fun s _ => hF s) hint hlim]
  simp only [F]; ring

/-- `|Tail_a(t)| ≤ (A/2) e^{-dt}(t/d + 1/d²)`, `d = a - β`. -/
theorem abs_liEvenCrossActualClockDampedTail_le {a : ℝ} (ha : β < a) {t : ℝ} (ht : 0 ≤ t) :
    |liEvenCrossActualClockDampedTail a t| ≤ xiShiftAbsoluteMass 0 / 2 *
      (Real.exp (-((a - β) * t)) * (t / (a - β) + 1 / (a - β) ^ 2)) := by
  have hd : 0 < a - β := by linarith
  have hi := (integrableOn_profile_Ioi ha).mono_set (Ioi_subset_Ioi ht)
  have hb : IntegrableOn (fun s => xiShiftAbsoluteMass 0 / 2 * (s * Real.exp (-((a - β) * s))))
      (Ioi t) := by
    have := (integrableOn_dividedPowerFn_mul_exp_neg 1 hd).mono_set (Ioi_subset_Ioi ht)
    refine IntegrableOn.congr_fun (this.const_mul (xiShiftAbsoluteMass 0 / 2)) (fun s _ => ?_)
      measurableSet_Ioi
    simp [dividedPowerFn]
  unfold liEvenCrossActualClockDampedTail
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_Ioi_mul_exp_neg hd ht, ← integral_const_mul]
  refine setIntegral_mono_on hi.norm hb measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := lt_of_le_of_lt ht hs
  rw [Real.norm_eq_abs]
  refine (abs_exp_mul_liEvenCrossActualClockPrimitive_div_le a hs0).trans (le_of_eq ?_)
  rw [show (β - a) * s = -((a - β) * s) by ring]
  ring

/-- The signed remainder `R(t) = κ(t) - r H(a) e^{-rt}`, `a = p - r`. -/
def liClockMarkedRemainder (p r t : ℝ) : ℝ :=
  liClockMarkedDensity p r t - r * Real.log (liClockThetaGeneratorReal (p - r)⁻¹) * Real.exp (-r * t)

/-- **Signed remainder (I21).**  For `a = p - r > β`, `d = a - β`, `q = r + d`:
`|R(t)| ≤ (Ar/2) e^{-qt}(t/d + 1/d²)`. -/
theorem abs_liClockMarkedRemainder_le {p r : ℝ} (hr : 0 ≤ r) (ha : β < p - r) {t : ℝ} (ht : 0 ≤ t) :
    |liClockMarkedRemainder p r t| ≤ xiShiftAbsoluteMass 0 * r / 2 *
      (Real.exp (-((r + (p - r - β)) * t)) * (t / (p - r - β) + 1 / (p - r - β) ^ 2)) := by
  have e : liClockMarkedRemainder p r t = -(r * Real.exp (-r * t) *
      liEvenCrossActualClockDampedTail (p - r) t) := by
    unfold liClockMarkedRemainder liClockMarkedDensity
    rw [liEvenCrossActualClockDampedCutoff_eq_sub_tail ha ht]
    ring
  rw [e, abs_neg, abs_mul, abs_mul, abs_of_nonneg hr, Real.abs_exp]
  have hT := abs_liEvenCrossActualClockDampedTail_le ha ht
  calc r * Real.exp (-r * t) * |liEvenCrossActualClockDampedTail (p - r) t| ≤
      r * Real.exp (-r * t) * (xiShiftAbsoluteMass 0 / 2 *
        (Real.exp (-((p - r - β) * t)) * (t / (p - r - β) + 1 / (p - r - β) ^ 2))) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = _ := by
        rw [show -((r + (p - r - β)) * t) = -r * t + -((p - r - β) * t) by ring, Real.exp_add]
        ring

/-- **Pole cancellation (I24).**  `R' + rR = r σ_p`. -/
theorem hasDerivAt_liClockMarkedRemainder (p r t : ℝ) :
    HasDerivAt (liClockMarkedRemainder p r)
      (-r * liClockMarkedRemainder p r t + r * liClockMarkedSource p t) t := by
  have h1 := hasDerivAt_liClockMarkedDensity p r t
  have h2 : HasDerivAt (fun t => r * Real.log (liClockThetaGeneratorReal (p - r)⁻¹) * Real.exp (-r * t))
      (r * Real.log (liClockThetaGeneratorReal (p - r)⁻¹) * (Real.exp (-r * t) * (-r))) t :=
    (((hasDerivAt_id' t).const_mul (-r)).exp.const_mul _).congr_deriv (by ring)
  refine (h1.sub h2).congr_deriv ?_
  unfold liClockMarkedRemainder
  ring

/-! ## All-order moments of the mark -/

private theorem integral_pow_mul_exp_neg (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t ^ m * Real.exp (-(c * t)) = m.factorial / c ^ (m + 1) := by
  have h := integral_Ioi_dividedPowerFn_mul_exp_neg m hc
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have e : ∫ t in Ioi (0 : ℝ), t ^ m * Real.exp (-(c * t)) =
      m.factorial * ∫ t in Ioi (0 : ℝ), dividedPowerFn m t * Real.exp (-(c * t)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    unfold dividedPowerFn; field_simp
  rw [e, h]; field_simp

private theorem integrableOn_pow_mul_exp_neg (m : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t => t ^ m * Real.exp (-(c * t))) (Ioi 0) := by
  have h := (integrableOn_dividedPowerFn_mul_exp_neg m hc).const_mul (m.factorial : ℝ)
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  unfold dividedPowerFn; field_simp

/-- **All-order error (I22–I23).**  For `a = p - r > β`, `d = a - β`, `q = r + d`, `s > -r`:
`|∫ t^n e^{-st} κ - r H(a) n!/(r+s)^{n+1}| ≤ (Ar/2)((n+1)!/(d (q+s)^{n+2}) + n!/(d² (q+s)^{n+1}))`. -/
theorem abs_laplaceWeightedMoment_liClockMarkedDensity_sub_le {p r : ℝ} (hr : 0 < r) (ha : β < p - r)
    (n : ℕ) {s : ℝ} (hs : -r < s) :
    |laplaceWeightedMoment (liClockMarkedDensity p r) n s -
        r * Real.log (liClockThetaGeneratorReal (p - r)⁻¹) * n.factorial / (r + s) ^ (n + 1)| ≤
      xiShiftAbsoluteMass 0 * r / 2 * ((n + 1).factorial / ((p - r - β) * (r + (p - r - β) + s) ^ (n + 2)) +
        n.factorial / ((p - r - β) ^ 2 * (r + (p - r - β) + s) ^ (n + 1))) := by
  set d := p - r - β
  set q := r + d
  set Hval := Real.log (liClockThetaGeneratorReal (p - r)⁻¹)
  have hd : 0 < d := by simp only [d]; linarith
  have hrs : 0 < r + s := by linarith
  have hqs : 0 < q + s := by simp only [q]; linarith
  have hκ := hint_admissible hr ha.le n s hs
  have hg : IntegrableOn (fun t => t ^ n * Real.exp (-(s * t)) * (r * Hval * Real.exp (-r * t)))
      (Ioi 0) := by
    refine IntegrableOn.congr_fun ((integrableOn_pow_mul_exp_neg n hrs).const_mul (r * Hval))
      (fun t _ => ?_) measurableSet_Ioi
    rw [show -((r + s) * t) = -(s * t) + -r * t by ring, Real.exp_add]; ring
  have hR : IntegrableOn (fun t => t ^ n * Real.exp (-(s * t)) * liClockMarkedRemainder p r t) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hκ.sub hg) (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, liClockMarkedRemainder]; ring
  have hsplit : laplaceWeightedMoment (liClockMarkedDensity p r) n s =
      r * Hval * n.factorial / (r + s) ^ (n + 1) +
        ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(s * t)) * liClockMarkedRemainder p r t := by
    have e1 : laplaceWeightedMoment (liClockMarkedDensity p r) n s =
        (∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(s * t)) * (r * Hval * Real.exp (-r * t))) +
          ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(s * t)) * liClockMarkedRemainder p r t := by
      rw [← integral_add hg hR]
      unfold laplaceWeightedMoment
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [liClockMarkedRemainder, Hval]; ring
    rw [e1]
    congr 1
    have e2 : ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(s * t)) * (r * Hval * Real.exp (-r * t)) =
        r * Hval * ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-((r + s) * t)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [show -((r + s) * t) = -(s * t) + -r * t by ring, Real.exp_add]; ring
    rw [e2, integral_pow_mul_exp_neg n hrs]
    ring
  rw [hsplit, add_sub_cancel_left, ← Real.norm_eq_abs]
  have hb : IntegrableOn (fun t => xiShiftAbsoluteMass 0 * r / 2 *
      ((1 / d) * (t ^ (n + 1) * Real.exp (-((q + s) * t))) +
        (1 / d ^ 2) * (t ^ n * Real.exp (-((q + s) * t))))) (Ioi 0) :=
    (((integrableOn_pow_mul_exp_neg (n + 1) hqs).const_mul (1 / d)).add
      ((integrableOn_pow_mul_exp_neg n hqs).const_mul (1 / d ^ 2))).const_mul _
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (setIntegral_mono_on hR.norm hb measurableSet_Ioi fun t ht => ?_).trans (le_of_eq ?_)
  · have ht0 : 0 < t := ht
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (pow_pos ht0 n), Real.abs_exp]
    have hb := abs_liClockMarkedRemainder_le hr.le ha ht0.le
    calc t ^ n * Real.exp (-(s * t)) * |liClockMarkedRemainder p r t| ≤
        t ^ n * Real.exp (-(s * t)) * (xiShiftAbsoluteMass 0 * r / 2 *
          (Real.exp (-(q * t)) * (t / d + 1 / d ^ 2))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by
          rw [show -((q + s) * t) = -(s * t) + -(q * t) by ring, Real.exp_add]
          field_simp
          ring
  · rw [integral_const_mul, integral_add ((integrableOn_pow_mul_exp_neg (n + 1) hqs).const_mul _)
      ((integrableOn_pow_mul_exp_neg n hqs).const_mul _), integral_const_mul, integral_const_mul,
      integral_pow_mul_exp_neg (n + 1) hqs, integral_pow_mul_exp_neg n hqs]
    field_simp

/-- **Normalized moments (I23).**  `(r+s)^{n+1}/(r n!) ∫ t^n e^{-st} κ → H(a)` for `s > -r`. -/
theorem tendsto_normalized_laplaceWeightedMoment_liClockMarkedDensity {p r : ℝ} (hr : 0 < r)
    (ha : β < p - r) {s : ℝ} (hs : -r < s) :
    Tendsto (fun n : ℕ => (r + s) ^ (n + 1) / (r * n.factorial) *
      laplaceWeightedMoment (liClockMarkedDensity p r) n s) atTop
        (𝓝 (Real.log (liClockThetaGeneratorReal (p - r)⁻¹))) := by
  set d := p - r - β
  set q := r + d
  set Hval := Real.log (liClockThetaGeneratorReal (p - r)⁻¹)
  have hd : 0 < d := by simp only [d]; linarith
  have hrs : 0 < r + s := by linarith
  have hqs : 0 < q + s := by simp only [q]; linarith
  set ρ := (r + s) / (q + s)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [div_lt_one hqs]; simp only [q]; linarith
  have hA := xiShiftAbsoluteMass_nonneg 0
  have hlim1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ρ ^ (n + 1)) atTop (𝓝 0) := by
    have := (tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  have hlim2 : Tendsto (fun n : ℕ => ρ ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp (tendsto_add_atTop_nat 1)
  have hbound : Tendsto (fun n : ℕ => xiShiftAbsoluteMass 0 / 2 *
      (((n : ℝ) + 1) * ρ ^ (n + 1) / (d * (q + s)) + ρ ^ (n + 1) / d ^ 2)) atTop (𝓝 0) := by
    have := ((hlim1.div_const (d * (q + s))).add (hlim2.div_const (d ^ 2))).const_mul
      (xiShiftAbsoluteMass 0 / 2)
    simpa using this
  have hmain : ∀ n : ℕ, |(r + s) ^ (n + 1) / (r * n.factorial) *
      laplaceWeightedMoment (liClockMarkedDensity p r) n s - Hval| ≤ xiShiftAbsoluteMass 0 / 2 *
        (((n : ℝ) + 1) * ρ ^ (n + 1) / (d * (q + s)) + ρ ^ (n + 1) / d ^ 2) := by
    intro n
    have h := abs_laplaceWeightedMoment_liClockMarkedDensity_sub_le hr ha n hs
    rw [show p - r - β = d from rfl, show r + d + s = q + s from rfl,
      show Real.log (liClockThetaGeneratorReal (p - r)⁻¹) = Hval from rfl] at h
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hk : 0 < (r + s) ^ (n + 1) / (r * n.factorial) := by positivity
    have e : (r + s) ^ (n + 1) / (r * n.factorial) * laplaceWeightedMoment (liClockMarkedDensity p r) n s -
        Hval = (r + s) ^ (n + 1) / (r * n.factorial) * (laplaceWeightedMoment (liClockMarkedDensity p r) n s -
          r * Hval * n.factorial / (r + s) ^ (n + 1)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hk]
    refine (mul_le_mul_of_nonneg_left h hk.le).trans (le_of_eq ?_)
    rw [Nat.factorial_succ]
    simp only [ρ, div_pow]
    push_cast
    have hd0 := hd.ne'
    have hq0 := hqs.ne'
    have hr0 := hr.ne'
    have hf0 := hf.ne'
    field_simp
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hmain n) hbound

/-- **Moment pole (I22).**  `r^n m_n/n! → H(a)` for the plain moments `m_n = ∫ t^n κ`. -/
theorem tendsto_normalized_moment_liClockMarkedDensity {p r : ℝ} (hr : 0 < r) (ha : β < p - r) :
    Tendsto (fun n : ℕ => r ^ n * (∫ t in Ioi (0 : ℝ), t ^ n * liClockMarkedDensity p r t) /
      n.factorial) atTop (𝓝 (Real.log (liClockThetaGeneratorReal (p - r)⁻¹))) := by
  have h := tendsto_normalized_laplaceWeightedMoment_liClockMarkedDensity hr ha (s := 0) (by linarith)
  refine h.congr fun n => ?_
  unfold laplaceWeightedMoment
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, add_zero]
  field_simp
  ring

/-- **Compensated limit (I23).**  `Σ_{k≤n} (r+s)^k (-1)^k H^{(k)}(p+s)/k! → H(a)`. -/
theorem tendsto_compensated_liClockMarked {p r : ℝ} (hr : 0 < r) (ha : β < p - r) {s : ℝ}
    (hs : -r < s) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), (r + s) ^ k * (-1) ^ k *
      iteratedDeriv k (fun q => Real.log (liClockThetaGeneratorReal q⁻¹)) (p + s) / k.factorial)
        atTop (𝓝 (Real.log (liClockThetaGeneratorReal (p - r)⁻¹))) := by
  refine (tendsto_normalized_laplaceWeightedMoment_liClockMarkedDensity hr ha hs).congr fun n => ?_
  rw [compensated_liClockMarked_eq hr ha.le n hs]

/-! ## Composition of marks -/

/-- One exponential mark `M_r h = (r e^{-r·}) ⋆ h`. -/
def liClockExpMark (r : ℝ) (h : ℝ → ℝ) : ℝ → ℝ :=
  volterraConv (fun s => r * Real.exp (-r * s)) h

/-- The iterated mark over a finite list of rates. -/
def liClockIteratedMark (rates : List ℝ) (h : ℝ → ℝ) : ℝ → ℝ :=
  rates.foldr liClockExpMark h

theorem liClockMarkedDensity_eq_expMark (p r : ℝ) :
    liClockMarkedDensity p r = liClockExpMark r (liClockMarkedSource p) :=
  funext (liClockMarkedDensity_eq_volterraConv p r)

theorem continuous_liClockExpMark (r : ℝ) {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous (liClockExpMark r h) :=
  continuous_volterraConv (by fun_prop) hh

theorem liClockExpMark_nonneg {r : ℝ} (hr : 0 ≤ r) {h : ℝ → ℝ} (hh : ∀ t, 0 ≤ t → 0 ≤ h t)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ liClockExpMark r h t :=
  intervalIntegral.integral_nonneg ht fun s hs =>
    mul_nonneg (mul_nonneg hr (Real.exp_pos _).le) (hh s hs.1)

/-- **Forward closure.**  Positive rates preserve nonnegativity on `t ≥ 0`. -/
theorem liClockIteratedMark_nonneg (rates : List ℝ) (hrates : ∀ r ∈ rates, 0 ≤ r) {h : ℝ → ℝ}
    (hh : ∀ t, 0 ≤ t → 0 ≤ h t) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ liClockIteratedMark rates h t := by
  induction rates generalizing t with
  | nil => exact hh t ht
  | cons r rs ih =>
    exact liClockExpMark_nonneg (hrates r List.mem_cons_self)
      (fun s hs => ih (fun r' hr' => hrates r' (List.mem_cons_of_mem r hr')) hs) ht

theorem continuous_liClockIteratedMark (rates : List ℝ) {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous (liClockIteratedMark rates h) := by
  induction rates with
  | nil => exact hh
  | cons r rs ih => exact continuous_liClockExpMark r ih

/-- **Differential inverse.**  `(d/dt + r) M_r h = r h`. -/
theorem hasDerivAt_liClockExpMark (r : ℝ) {h : ℝ → ℝ} (hh : Continuous h) (t : ℝ) :
    HasDerivAt (liClockExpMark r h) (-r * liClockExpMark r h t + r * h t) t := by
  have hd : ∀ s, HasDerivAt (fun s => r * Real.exp (-r * s)) (-r * (r * Real.exp (-r * s))) s :=
    fun s => (((hasDerivAt_id' s).const_mul (-r)).exp.const_mul r).congr_deriv (by ring)
  have h1 := hasDerivAt_volterraConv hd (by fun_prop) hh t
  refine h1.congr_deriv ?_
  rw [volterraConv_smul_left]
  simp only [mul_zero, Real.exp_zero, mul_one]
  unfold liClockExpMark
  ring

/-- **Laplace multiplier.**  `∫_0^∞ e^{-st} M_r h = r/(r+s) ∫_0^∞ e^{-st} h` for `s > -r`. -/
theorem integral_exp_mul_liClockExpMark {r s : ℝ} (hr : 0 < r) (hs : -r < s) {h : ℝ → ℝ}
    (hh : Continuous h) (hint : IntegrableOn (fun t => Real.exp (-(s * t)) * |h t|) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * liClockExpMark r h t =
      r / (r + s) * ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * h t := by
  have hf : Continuous fun t : ℝ => r * Real.exp (-r * t) := by fun_prop
  have hfi : IntegrableOn (fun t => Real.exp (-((s : ℂ).re * t)) * |r * Real.exp (-r * t)|) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 (show 0 < s + r by linarith)).const_mul r
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    simp only [Complex.ofReal_re]
    rw [abs_of_pos (by positivity), show -(s + r) * t = -(s * t) + -r * t by ring, Real.exp_add]
    ring
  have hgi : IntegrableOn (fun t => Real.exp (-((s : ℂ).re * t)) * |h t|) (Ioi 0) := by
    simpa using hint
  have hconv := integral_Ioi_cexp_mul_volterraConv hf hh hfi hgi
  rw [complex_integral_eq_ofReal, complex_integral_eq_ofReal, complex_integral_eq_ofReal,
    ← Complex.ofReal_mul] at hconv
  have hreal := Complex.ofReal_injective hconv
  have e2 : ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (r * Real.exp (-r * t)) = r / (r + s) := by
    have hI := integral_exp_mul_Ioi (show -(r + s) < 0 by linarith) 0
    have e : ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (r * Real.exp (-r * t)) =
        r * ∫ t in Ioi (0 : ℝ), Real.exp (-(r + s) * t) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [show -(r + s) * t = -(s * t) + -r * t by ring, Real.exp_add]; ring
    rw [e, hI, mul_zero, Real.exp_zero]
    field_simp
  unfold liClockExpMark
  rw [hreal, e2]

/-- Weighted integrability is preserved by a mark of a nonnegative input. -/
theorem integrableOn_exp_mul_liClockExpMark {r s : ℝ} (hr : 0 < r) (hs : -r < s) {h : ℝ → ℝ}
    (hh : Continuous h) (h0 : ∀ t, 0 ≤ t → 0 ≤ h t)
    (hint : IntegrableOn (fun t => Real.exp (-(s * t)) * h t) (Ioi 0)) :
    IntegrableOn (fun t => Real.exp (-(s * t)) * liClockExpMark r h t) (Ioi 0) := by
  have hF : IntegrableOn (fun t => Real.exp (-s * t) * (r * Real.exp (-r * t))) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 (show 0 < s + r by linarith)).const_mul r
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    rw [show -(s + r) * t = -s * t + -r * t by ring, Real.exp_add]; ring
  have hG : IntegrableOn (fun t => Real.exp (-s * t) * h t) (Ioi 0) :=
    IntegrableOn.congr_fun hint (fun t _ => by simp only [neg_mul]) measurableSet_Ioi
  have hc := integrableOn_volterraConv_of_nonneg (F := fun t => Real.exp (-s * t) * (r * Real.exp (-r * t)))
    (G := fun t => Real.exp (-s * t) * h t) (by fun_prop) ((by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-s * t)).mul hh) (fun t _ => by positivity) (fun t ht => mul_nonneg
        (Real.exp_pos _).le (h0 t ht)) hF hG
  refine IntegrableOn.congr_fun hc (fun t _ => ?_) measurableSet_Ioi
  unfold liClockExpMark
  rw [← exp_mul_volterraConv, neg_mul]

/-- **Composed marks.**  For positive rates and an admissible first mark (`p - r ≥ β`), every
iterated mark is nonnegative, and its Laplace function is `H(p+s) · r/(r+s) · Π_i r_i/(r_i+s)`;
in particular its total mass is `H(p)`. -/
theorem liClockIteratedMark_marked {p r : ℝ} (hr : 0 < r) (ha : β ≤ p - r) (rates : List ℝ)
    (hrates : ∀ r' ∈ rates, 0 < r') {s : ℝ} (hs0 : 0 ≤ s) :
    (∀ t, 0 ≤ t → 0 ≤ liClockIteratedMark rates (liClockMarkedDensity p r) t) ∧
      IntegrableOn (fun t => Real.exp (-(s * t)) *
        liClockIteratedMark rates (liClockMarkedDensity p r) t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * liClockIteratedMark rates (liClockMarkedDensity p r) t =
        (rates.map fun r' => r' / (r' + s)).prod * (r / (r + s) *
          Real.log (liClockThetaGeneratorReal (p + s)⁻¹)) := by
  have hβp : β < p + s := by linarith [hr]
  have hκ0 : ∀ t, 0 ≤ t → 0 ≤ liClockMarkedDensity p r t := fun t ht => by
    rcases ht.eq_or_lt with rfl | ht
    · simp [liClockMarkedDensity, liEvenCrossActualClockDampedCutoff]
    · exact (liClockMarkedDensity_pos hr ha ht).le
  induction rates with
  | nil =>
    refine ⟨hκ0, ?_, ?_⟩
    · have := hint_admissible hr ha 0 s (by linarith)
      refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
      simp [liClockIteratedMark]
    · simp only [liClockIteratedMark, List.foldr_nil, List.map_nil, List.prod_nil, one_mul]
      exact integral_exp_mul_liClockMarkedDensity hr (by linarith) hβp
  | cons r' rs ih =>
    obtain ⟨h0, hi, hL⟩ := ih fun x hx => hrates x (List.mem_cons_of_mem r' hx)
    have hr' := hrates r' List.mem_cons_self
    have hcont := continuous_liClockIteratedMark rs (continuous_liClockMarkedDensity p r)
    refine ⟨fun t ht => liClockExpMark_nonneg hr'.le h0 ht, ?_, ?_⟩
    · exact integrableOn_exp_mul_liClockExpMark hr' (by linarith) hcont h0 hi
    · have hiabs : IntegrableOn (fun t => Real.exp (-(s * t)) *
          |liClockIteratedMark rs (liClockMarkedDensity p r) t|) (Ioi 0) :=
        IntegrableOn.congr_fun hi (fun t ht => by rw [abs_of_nonneg (h0 t (le_of_lt ht))])
          measurableSet_Ioi
      show ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) *
          liClockExpMark r' (liClockIteratedMark rs (liClockMarkedDensity p r)) t = _
      rw [integral_exp_mul_liClockExpMark hr' (by linarith) hcont hiabs, hL]
      simp only [List.map_cons, List.prod_cons]
      ring

end RHTower
