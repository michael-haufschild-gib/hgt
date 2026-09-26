import GaloisForLFunctions.RHTower.ConstrainedWeilBathtubFloor
import GaloisForLFunctions.RHTower.ConstrainedWeilResidualPolynomialBound
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper

/-!
# Lower bounds for the archimedean constrained multiplier at the prime-2 threshold

At the aperture `S = log 2` the archimedean multiplier is `M_S(η) = A(S) + Λ_S(η)` with

`A(log 2) = −γ − log π − 3 log 2 + 2 log(1 + √2) − arctan(√2/4)`   (`π` cancels),

obtained from the closed form `∫_0^S (e^{h/2} − 1)/sinh h dh = F(S) − F(0)`,
`F(h) = −2 log(1 + e^{h/2}) + log(1 + e^h) + 2 arctan e^{h/2}`, and the identity
`2 arctan √2 − π/2 = arctan(1/(2√2))`.  With `γ < 0.577216` this gives `A(log 2) > −2.379`.

For the energy, `K₊(h) = e^{h/2}/sinh h ≥ 1/h + 11/25` on `(0, 7/10]`, so
`Λ_S(η) ≥ Cin(Sη) + (11/25)(S − sin(Sη)/η)`, where `Cin(x) = ∫_0^x (1 − cos t)/t dt` is increasing
and bounded below by the integral of the alternating Taylor polynomial of degree 28.
-/

open Real MeasureTheory Set Finset intervalIntegral

namespace RHTower

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

/-! ## Elementary constants -/

theorem sqrt_two_gt_d8 : (141421356 / 100000000 : ℝ) < √2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem sqrt_two_lt_d8 : √2 < (141421357 / 100000000 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem log_pi_lt_d5 : Real.log Real.pi < 114474 / 100000 := by
  have hexp := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 114474 / 100000) 12
  have hpi : Real.pi < Real.exp (114474 / 100000) := by
    calc Real.pi < 3.141593 := Real.pi_lt_d6
      _ < ∑ i ∈ Finset.range 12, (114474 / 100000 : ℝ) ^ i / i.factorial := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ _ := hexp
  exact (Real.log_lt_iff_lt_exp Real.pi_pos).2 hpi

/-- `arctan x ≤ x − x³/3 + x⁵/5` for `x ≥ 0`. -/
theorem arctan_le_quintic {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => y - y ^ 3 / 3 + y ^ 5 / 5 - Real.arctan y)
      (y ^ 6 / (1 + y ^ 2)) y := by
    intro y
    have h := ((((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 3)).add
      ((hasDerivAt_pow 5 y).div_const 5)).sub (Real.hasDerivAt_arctan y))
    refine h.congr_deriv ?_
    have hy : (1 + y ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have := nonneg_of_hasDerivAt_nonneg hd (by simp) (fun y _ => by positivity) hx
  linarith

/-- `log(1 + √2) > 0.88136`, from the `artanh` series at `1/√2`. -/
theorem log_one_add_sqrt_two_gt : (88136 / 100000 : ℝ) < Real.log (1 + √2) := by
  set x : ℝ := (√2)⁻¹ with hxdef
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hspos : 0 < √2 := by positivity
  have hx2 : x ^ 2 = 1 / 2 := by
    rw [hxdef, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hxlo : (70710678 / 100000000 : ℝ) < x := by
    rw [hxdef, lt_inv_comm₀ (by norm_num) hspos]
    calc √2 < 141421357 / 100000000 := sqrt_two_lt_d8
      _ < _ := by norm_num
  have hxlt : |x| < 1 := by
    rw [abs_of_pos (by positivity)]
    rw [hxdef, inv_lt_one₀ hspos]
    calc (1 : ℝ) < 141421356 / 100000000 := by norm_num
      _ < √2 := sqrt_two_gt_d8
  have hsum := Real.hasSum_log_sub_log_of_abs_lt_one hxlt
  have hle := sum_le_hasSum (Finset.range 12) (fun k _ => by
    have : 0 ≤ x := by positivity
    positivity) hsum
  have hlog : Real.log (1 + x) - Real.log (1 - x) = 2 * Real.log (1 + √2) := by
    have h1 : 0 < 1 - x := by
      have := (abs_lt.1 hxlt).2; linarith
    rw [← Real.log_div (by positivity) h1.ne']
    have hq : (1 + x) / (1 - x) = (1 + √2) ^ 2 := by
      rw [hxdef]
      field_simp
      nlinarith [hs2]
    rw [hq, Real.log_pow]
    push_cast; ring
  have hpow : ∀ k : ℕ, x ^ (2 * k + 1) = x * (1 / 2) ^ k := by
    intro k; rw [pow_succ, pow_mul, hx2]; ring
  simp only [hpow] at hle
  norm_num [Finset.sum_range_succ] at hle
  rw [hlog] at hle
  nlinarith

/-! ## The constant `A(log 2)` -/

theorem exp_half_log_two : Real.exp (Real.log 2 / 2) = √2 := by
  have hsq : Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (Real.log 2 / 2) = Real.log 2 by ring, Real.exp_log (by norm_num)]
  rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]

theorem hasDerivAt_halfExpSinhPrimitive (h : ℝ) :
    HasDerivAt (fun h : ℝ => -2 * Real.log (1 + Real.exp (h / 2)) + Real.log (1 + Real.exp h) +
      2 * Real.arctan (Real.exp (h / 2)))
      (2 * Real.exp h / ((1 + Real.exp (h / 2)) * (1 + Real.exp h))) h := by
  have hy : HasDerivAt (fun h : ℝ => Real.exp (h / 2)) (Real.exp (h / 2) * (1 / 2)) h :=
    (Real.hasDerivAt_exp (h / 2)).comp h ((hasDerivAt_id h).div_const 2)
  have h1 : HasDerivAt (fun h : ℝ => 1 + Real.exp (h / 2)) (Real.exp (h / 2) * (1 / 2)) h :=
    hy.const_add 1
  have h2 : HasDerivAt (fun h : ℝ => 1 + Real.exp h) (Real.exp h) h :=
    (Real.hasDerivAt_exp h).const_add 1
  have hne1 : 1 + Real.exp (h / 2) ≠ 0 := by positivity
  have hne2 : 1 + Real.exp h ≠ 0 := by positivity
  have hsum := (((h1.log hne1).const_mul (-2)).add (h2.log hne2)).add
    ((hy.arctan).const_mul 2)
  refine hsum.congr_deriv ?_
  have he : Real.exp h = Real.exp (h / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [he]
  have hp : 0 < Real.exp (h / 2) := Real.exp_pos _
  have hq : 1 + (Real.exp (h / 2)) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- `∫_0^{log 2} (e^{h/2} − 1)/sinh h dh = −2 log(1+√2) + log 3 + log 2 + 2 arctan √2 − π/2`. -/
theorem integral_Ioc_exp_half_sub_one_div_sinh_log_two :
    (∫ h in Ioc (0 : ℝ) (Real.log 2), (Real.exp (h / 2) - 1) / Real.sinh h) =
      -2 * Real.log (1 + √2) + Real.log 3 + Real.log 2 + 2 * Real.arctan √2 - Real.pi / 2 := by
  have hS : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpt : ∀ h ∈ Ioc (0 : ℝ) (Real.log 2), (Real.exp (h / 2) - 1) / Real.sinh h =
      2 * Real.exp h / ((1 + Real.exp (h / 2)) * (1 + Real.exp h)) := by
    intro h hh
    have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh.1.ne'
    have he : Real.exp h = Real.exp (h / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hp : 0 < Real.exp (h / 2) := Real.exp_pos _
    rw [div_eq_div_iff hsinh (by positivity), Real.sinh_eq, Real.exp_neg, he]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, ← intervalIntegral.integral_of_le hS.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun h _ => hasDerivAt_halfExpSinhPrimitive h)]
  · simp only [exp_half_log_two, Real.exp_log (by norm_num : (0 : ℝ) < 2), zero_div,
      Real.exp_zero, Real.arctan_one]
    rw [show (1 : ℝ) + 2 = 3 by norm_num, show (1 : ℝ) + 1 = 2 by norm_num]
    ring
  · exact (Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)).intervalIntegrable _ _

/-- `2 arctan √2 − π/2 = arctan (1/(2√2))`. -/
theorem two_arctan_sqrt_two_sub_pi_div_two :
    2 * Real.arctan √2 - Real.pi / 2 = Real.arctan (2 * √2)⁻¹ := by
  have hs : 0 < √2 := by positivity
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h1 : Real.arctan √2 = Real.pi / 2 - Real.arctan (√2)⁻¹ := by
    rw [← Real.arctan_inv_of_pos (inv_pos.2 hs), inv_inv]
  have hlt : (√2)⁻¹ * (√2)⁻¹ < 1 := by
    rw [← mul_inv, hs2]; norm_num
  have h2 : Real.arctan (√2)⁻¹ + Real.arctan (√2)⁻¹ = Real.arctan (2 * √2) := by
    rw [Real.arctan_add hlt]
    congr 1
    rw [← mul_inv, hs2]
    field_simp
    nlinarith [hs2]
  have h3 : Real.arctan (2 * √2) = Real.pi / 2 - Real.arctan (2 * √2)⁻¹ := by
    rw [← Real.arctan_inv_of_pos (inv_pos.2 (by positivity)), inv_inv]
  linarith

theorem arctan_inv_two_sqrt_two_lt : Real.arctan (2 * √2)⁻¹ < 339927 / 1000000 := by
  have hx0 : 0 ≤ (2 * √2)⁻¹ := by positivity
  have hxhi : (2 * √2)⁻¹ ≤ 35355340 / 100000000 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    have := sqrt_two_gt_d8
    norm_num
    linarith
  calc Real.arctan (2 * √2)⁻¹ ≤ Real.arctan (35355340 / 100000000) :=
        Real.arctan_strictMono.monotone hxhi
    _ ≤ (35355340 / 100000000 : ℝ) - (35355340 / 100000000) ^ 3 / 3 +
        (35355340 / 100000000) ^ 5 / 5 := arctan_le_quintic (by norm_num)
    _ < 339927 / 1000000 := by norm_num

/-- **Closed form of the aperture constant at `log 2`.** -/
theorem weilConstrainedConstant_log_two :
    weilConstrainedConstant (Real.log 2) =
      -Real.eulerMascheroniConstant - Real.log Real.pi - 3 * Real.log 2 +
        2 * Real.log (1 + √2) - Real.arctan (2 * √2)⁻¹ := by
  have hS : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJ := integral_Ioc_exp_half_sub_one_div_sinh hS
  rw [integral_Ioc_exp_half_sub_one_div_sinh_log_two] at hJ
  have hexp1 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hexp2 : Real.exp (-(2 * Real.log 2)) = 1 / 4 := by
    rw [show -(2 * Real.log 2) = 2 * (-Real.log 2) by ring, Real.exp_nat_mul' , hexp1]
    norm_num
  rw [hexp1] at hJ
  unfold weilConstrainedConstant
  rw [hexp2, ← two_arctan_sqrt_two_sub_pi_div_two]
  have hl34 : Real.log (1 - 1 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  have hl32 : Real.log (1 + 1 / 2) = Real.log 3 - Real.log 2 := by
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [hl34]
  rw [hl32] at hJ
  linarith

/-- **`A(log 2) > −2.379`.** -/
theorem weilConstrainedConstant_log_two_gt : (-2379 / 1000 : ℝ) < weilConstrainedConstant (Real.log 2) := by
  rw [weilConstrainedConstant_log_two]
  have hγ := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hπ := log_pi_lt_d5
  have h2 := Real.log_two_lt_d9
  have hs := log_one_add_sqrt_two_gt
  have ha := arctan_inv_two_sqrt_two_lt
  norm_num at h2
  linarith

end RHTower
