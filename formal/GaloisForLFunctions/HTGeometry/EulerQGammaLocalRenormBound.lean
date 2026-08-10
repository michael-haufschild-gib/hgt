import GaloisForLFunctions.HTGeometry.EulerQGammaGenusOneBound
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne

/-!
# The renormalised local factor is one plus a quadratically small error

Splitting Jackson's local response into its power factor, its numerator product and its
denominator product, and distributing the first-activation counterterm
`ℓ_q(s) = q(s−1) + q^{1+s}` over the three pieces, each piece becomes a genus-one renormalised
factor: the power factor is `exp(−s(log(1−q)+q))`, the numerator is `(q;q)_∞ eq` and the
denominator is `(q^{1+s};q)_∞ e^{q^{1+s}}`.  Each deviates from `1` quadratically in its own small
parameter.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The logarithmic defect of the power factor -/

/-- On the half interval the logarithm deviates from its linear term quadratically. -/
theorem abs_log_one_sub_add_self_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hxabs : |x| = x := abs_of_nonneg hx0
  have habs : |x| < 1 := by
    rw [hxabs]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  have hsum : (∑ i ∈ Finset.range 1, x ^ (i + 1) / ((i : ℝ) + 1)) = x := by
    simp
  rw [hsum, hxabs] at h
  have hle : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  rw [add_comm (Real.log (1 - x)) x]
  linarith

/-! ## The three renormalised pieces -/

/-- The renormalised power factor `(1−q)^{−s} e^{−qs}`. -/
def eqgPowerFactor (q : RealEulerNome) (s : ℂ) : ℂ :=
  ((1 - q.val : ℝ) : ℂ) ^ (-s) * Complex.exp (-((q.val : ℂ) * s))

/-- The renormalised numerator factor `(q;q)_∞ e^q`. -/
def eqgNumerFactor (q : RealEulerNome) : ℂ :=
  ((realQFactorialInf q : ℝ) : ℂ) * Complex.exp ((q.val : ℂ))

/-- The renormalised denominator factor `(q^{1+s};q)_∞ e^{q^{1+s}}`. -/
def eqgDenomFactorRenorm (q : RealEulerNome) (s : ℂ) : ℂ :=
  qDenomProduct q (1 + s) * Complex.exp ((q.val : ℂ) ^ (1 + s))

/-- **The three-factor split of the renormalised local response.** -/
theorem eqgRenormLocal_factorization (q : RealEulerNome) {s : ℂ} (hs : 1 + s ∈ qHalfPlane) :
    eqgRenormLocal q s
      = eqgPowerFactor q s * eqgNumerFactor q * (eqgDenomFactorRenorm q s)⁻¹ := by
  have hD : qDenomProduct q (1 + s) ≠ 0 := qDenomProduct_ne_zero q hs
  have hE : Complex.exp ((q.val : ℂ) ^ (1 + s)) ≠ 0 := Complex.exp_ne_zero _
  rw [eqgRenormLocal, qGammaOn, eqgPowerFactor, eqgNumerFactor, eqgDenomFactorRenorm,
    eqgActivation]
  have hpow : ((1 - q.val : ℝ) : ℂ) ^ (1 - (1 + s)) = ((1 - q.val : ℝ) : ℂ) ^ (-s) := by
    congr 1
    ring
  rw [hpow, mul_inv]
  have hexp : Complex.exp (-((q.val : ℂ) * (s - 1) + (q.val : ℂ) ^ (1 + s)))
      = Complex.exp (-((q.val : ℂ) * s)) * Complex.exp ((q.val : ℂ))
        * (Complex.exp ((q.val : ℂ) ^ (1 + s)))⁻¹ := by
    rw [← Complex.exp_add, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp

/-! ## The power factor -/

theorem eqgPowerFactor_eq_exp (q : RealEulerNome) (s : ℂ) :
    eqgPowerFactor q s
      = Complex.exp (-(s * ((Real.log (1 - q.val) + q.val : ℝ) : ℂ))) := by
  have h1 : ((1 - q.val : ℝ) : ℂ) ≠ 0 := q.one_sub_complex_ne_zero
  have h2 : (0 : ℝ) ≤ 1 - q.val := by
    have := q.lt_one
    linarith
  rw [eqgPowerFactor, Complex.cpow_def_of_ne_zero h1, ← Complex.exp_add,
    ← Complex.ofReal_log h2]
  congr 1
  push_cast
  ring

theorem norm_eqgPowerFactor_sub_one_le (q : RealEulerNome) (hq : q.val ≤ 1 / 2) (s : ℂ) :
    ‖eqgPowerFactor q s - 1‖
      ≤ Real.exp (2 * ‖s‖ * q.val ^ 2) * (2 * ‖s‖ * q.val ^ 2) := by
  rw [eqgPowerFactor_eq_exp]
  refine norm_cexp_sub_one_le_of_le ?_
  rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hlog := abs_log_one_sub_add_self_le q.pos.le hq
  have hs : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  calc ‖s‖ * |Real.log (1 - q.val) + q.val| ≤ ‖s‖ * (2 * q.val ^ 2) :=
        mul_le_mul_of_nonneg_left hlog hs
    _ = 2 * ‖s‖ * q.val ^ 2 := by ring

/-! ## The renormalised q-Pochhammer factor -/

theorem real_exp_sub_one_le {t : ℝ} (_ht : 0 ≤ t) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.add_one_le_exp (-t)
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have hmul : (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t := by
    refine mul_le_mul_of_nonneg_right ?_ hpos.le
    linarith
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
  nlinarith

theorem summable_norm_nome_shift (q : RealEulerNome) (z : ℂ) :
    Summable (fun k : ℕ => ‖-((q.val : ℂ) ^ (z + (k : ℂ)))‖) := by
  have hgeom : Summable (fun k : ℕ => q.val ^ z.re * q.val ^ k) :=
    (summable_geometric_of_lt_one q.pos.le q.lt_one).mul_left _
  refine hgeom.congr fun k => ?_
  rw [norm_neg, qcpow_add_natCast, norm_mul, norm_qcpow, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos q.pos]

theorem hasProd_qDenomFactor (q : RealEulerNome) (z : ℂ) :
    HasProd (fun k : ℕ => 1 + -((q.val : ℂ) ^ (z + (k : ℂ)))) (qDenomProduct q z) := by
  have hmul := Complex.multipliable_one_add_of_summable
    (f := fun k : ℕ => -((q.val : ℂ) ^ (z + (k : ℂ)))) (summable_norm_nome_shift q z).of_norm
  have hval : qDenomProduct q z = ∏' k : ℕ, (1 + -((q.val : ℂ) ^ (z + (k : ℂ)))) := by
    rw [qDenomProduct]
    refine tprod_congr fun k => ?_
    rw [qDenomFactor]
    ring
  rw [hval]
  exact hmul.hasProd

theorem tsum_norm_nome_shift_tail_le (q : RealEulerNome) (hq : q.val ≤ 1 / 2) (z : ℂ) :
    ∑' k : ℕ, (if k = 0 then 0 else ‖-((q.val : ℂ) ^ (z + (k : ℂ)))‖)
      ≤ 2 * (q.val ^ z.re * q.val) := by
  have hnorm : ∀ k : ℕ, ‖-((q.val : ℂ) ^ (z + (k : ℂ)))‖ = q.val ^ z.re * q.val ^ k := by
    intro k
    rw [norm_neg, qcpow_add_natCast, norm_mul, norm_qcpow, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos q.pos]
  have hsum : Summable (fun k : ℕ => ‖-((q.val : ℂ) ^ (z + (k : ℂ)))‖) :=
    summable_norm_nome_shift q z
  have hsplit := hsum.tsum_eq_add_tsum_ite (0 : ℕ)
  have htotal : ∑' k : ℕ, ‖-((q.val : ℂ) ^ (z + (k : ℂ)))‖ = q.val ^ z.re * (1 - q.val)⁻¹ := by
    rw [tsum_congr hnorm, tsum_mul_left, tsum_geometric_of_lt_one q.pos.le q.lt_one]
  have hzero : ‖-((q.val : ℂ) ^ (z + ((0 : ℕ) : ℂ)))‖ = q.val ^ z.re := by
    rw [hnorm 0, pow_zero, mul_one]
  have hpos : (0 : ℝ) < q.val ^ z.re := Real.rpow_pos_of_pos q.pos _
  have hq1 : (0 : ℝ) < 1 - q.val := by
    have := q.lt_one
    linarith
  have hval : ∑' k : ℕ, (if k = 0 then 0 else ‖-((q.val : ℂ) ^ (z + (k : ℂ)))‖)
      = q.val ^ z.re * (1 - q.val)⁻¹ - q.val ^ z.re := by
    rw [← htotal, hsplit, hzero]
    ring
  rw [hval]
  have hkey : q.val ^ z.re * (1 - q.val)⁻¹ - q.val ^ z.re
      = q.val ^ z.re * q.val * (1 - q.val)⁻¹ := by
    field_simp
    ring
  rw [hkey]
  have hinv : (1 - q.val)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hq1 (by norm_num)]
    linarith
  have hbase : (0 : ℝ) ≤ q.val ^ z.re * q.val := mul_nonneg hpos.le q.pos.le
  nlinarith

/-- The genus-one renormalised q-Pochhammer factor `(q^z; q)_∞ e^{q^z}`. -/
def eqgRenormPochhammer (q : RealEulerNome) (z : ℂ) : ℂ :=
  qDenomProduct q z * Complex.exp ((q.val : ℂ) ^ z)

/-- **The renormalised q-Pochhammer factor is quadratically close to one.** -/
theorem norm_eqgRenormPochhammer_sub_one_le (q : RealEulerNome) (hq : q.val ≤ 1 / 2) {z : ℂ}
    (hz : q.val ^ z.re ≤ 1 / 2) :
    ‖eqgRenormPochhammer q z - 1‖
      ≤ 3 * Real.exp 2 * (q.val ^ z.re * q.val)
        + genusOneBoundConst * (q.val ^ z.re) ^ 2 := by
  set x : ℂ := (q.val : ℂ) ^ z with hx
  set m : ℝ := q.val ^ z.re * q.val with hm
  have hxnorm : ‖x‖ = q.val ^ z.re := by
    rw [hx, norm_qcpow]
  have hxhalf : ‖x‖ ≤ 1 / 2 := by
    rw [hxnorm]
    exact hz
  have hpos : (0 : ℝ) < q.val ^ z.re := Real.rpow_pos_of_pos q.pos _
  have hmnn : (0 : ℝ) ≤ m := by
    rw [hm]
    exact mul_nonneg hpos.le q.pos.le
  have hsplit := norm_hasProd_sub_single_le (0 : ℕ) (hasProd_qDenomFactor q z)
    (summable_norm_nome_shift q z) (tsum_norm_nome_shift_tail_le q hq z)
  have hlead : (1 : ℂ) + -((q.val : ℂ) ^ (z + ((0 : ℕ) : ℂ))) = 1 - x := by
    rw [hx]
    push_cast
    rw [add_zero]
    ring
  rw [hlead] at hsplit
  have hmass2 : (0 : ℝ) ≤ 2 * m := by linarith
  have hmasshalf : 2 * m ≤ 1 / 2 := by
    rw [hm]
    nlinarith [q.pos.le, hpos.le]
  have hexpnn : 0 ≤ Real.exp (2 * m) - 1 := by
    have := Real.add_one_le_exp (2 * m)
    linarith
  have hexpmass : Real.exp (2 * m) - 1 ≤ 2 * m * Real.exp 1 := by
    have h := real_exp_sub_one_le hmass2
    have hle : Real.exp (2 * m) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    have hmul : 2 * m * Real.exp (2 * m) ≤ 2 * m * Real.exp 1 :=
      mul_le_mul_of_nonneg_left hle hmass2
    linarith
  have hleadnorm : ‖(1 : ℂ) - x‖ ≤ 3 / 2 := by
    calc ‖(1 : ℂ) - x‖ ≤ ‖(1 : ℂ)‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 1 + 1 / 2 := by
          rw [norm_one]
          linarith
      _ = 3 / 2 := by norm_num
  have hexpnorm : ‖Complex.exp x‖ ≤ Real.exp 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (le_trans (le_trans (Complex.re_le_norm x) hxhalf) (by norm_num))
  have hA : ‖qDenomProduct q z - (1 - x)‖ ≤ 3 * m * Real.exp 1 := by
    refine le_trans hsplit ?_
    calc ‖(1 : ℂ) - x‖ * (Real.exp (2 * m) - 1)
        ≤ (3 / 2) * (2 * m * Real.exp 1) :=
          mul_le_mul hleadnorm hexpmass hexpnn (by norm_num)
      _ = 3 * m * Real.exp 1 := by ring
  have hid : eqgRenormPochhammer q z - 1
      = (qDenomProduct q z - (1 - x)) * Complex.exp x
        + (eulerProcessGenusOneFactor x - 1) := by
    rw [eqgRenormPochhammer, eulerProcessGenusOneFactor, ← hx]
    ring
  rw [hid]
  refine le_trans (norm_add_le _ _) ?_
  have hfirst : ‖(qDenomProduct q z - (1 - x)) * Complex.exp x‖ ≤ 3 * Real.exp 2 * m := by
    rw [norm_mul]
    have hnn : (0 : ℝ) ≤ ‖qDenomProduct q z - (1 - x)‖ := norm_nonneg _
    have hep : (0 : ℝ) ≤ 3 * m * Real.exp 1 := by
      have := Real.exp_pos 1
      nlinarith
    calc ‖qDenomProduct q z - (1 - x)‖ * ‖Complex.exp x‖
        ≤ (3 * m * Real.exp 1) * Real.exp 1 :=
          mul_le_mul hA hexpnorm (norm_nonneg _) hep
      _ = 3 * (Real.exp 1 * Real.exp 1) * m := by ring
      _ = 3 * Real.exp 2 * m := by
          rw [← Real.exp_add]
          norm_num
  have hsecond : ‖eulerProcessGenusOneFactor x - 1‖
      ≤ genusOneBoundConst * (q.val ^ z.re) ^ 2 := by
    have h := norm_genusOneFactor_sub_one_le hxhalf
    rw [hxnorm] at h
    exact h
  linarith

/-! ## Identifying the two products -/

theorem qDenomProduct_one (q : RealEulerNome) :
    qDenomProduct q 1 = ((realQFactorialInf q : ℝ) : ℂ) := by
  rw [qDenomProduct_eq, Complex.cpow_one, qPochhammerInf_nome_eq]

theorem eqgNumerFactor_eq (q : RealEulerNome) :
    eqgNumerFactor q = eqgRenormPochhammer q 1 := by
  rw [eqgNumerFactor, eqgRenormPochhammer, qDenomProduct_one, Complex.cpow_one]

theorem eqgDenomFactorRenorm_eq (q : RealEulerNome) (s : ℂ) :
    eqgDenomFactorRenorm q s = eqgRenormPochhammer q (1 + s) := rfl

/-! ## The total local deviation -/

/-- **The renormalised local response is one plus the accumulated deviation of its three
renormalised pieces.** -/
theorem norm_eqgRenormLocal_sub_one_le (q : RealEulerNome) {s : ℂ} (hs : 1 + s ∈ qHalfPlane)
    {a b c : ℝ}
    (ha : ‖eqgPowerFactor q s - 1‖ ≤ a)
    (hb : ‖eqgNumerFactor q - 1‖ ≤ b)
    (hc : ‖eqgDenomFactorRenorm q s - 1‖ ≤ c) (hc2 : c ≤ 1 / 2) :
    ‖eqgRenormLocal q s - 1‖
      ≤ (a + b + a * b) + 2 * c + (a + b + a * b) * (2 * c) := by
  have hcsmall : ‖eqgDenomFactorRenorm q s - 1‖ ≤ 1 / 2 := le_trans hc hc2
  have hinv : ‖(eqgDenomFactorRenorm q s)⁻¹ - 1‖ ≤ 2 * c := by
    refine le_trans (norm_inv_sub_one_le hcsmall) ?_
    linarith
  have hprod := norm_mul_sub_one_le ha hb
  rw [eqgRenormLocal_factorization q hs]
  exact norm_mul_sub_one_le hprod hinv

end

end GaloisForLFunctions.HTGeometry
