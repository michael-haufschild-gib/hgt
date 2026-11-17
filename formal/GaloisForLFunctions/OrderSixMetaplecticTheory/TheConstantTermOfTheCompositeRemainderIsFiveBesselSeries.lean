import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConstantTermOfTheCompositeTraceIsFiveCorrelations

/-!
# The constant term of the composite remainder is five Bessel series

The coset sums of `integral_sourceTrace` evaluate by the Gauss sums of the twisted cosets at `p` and `q`
(`C_p(k) = g(χ_p², 9k)`, `C_p(k)T(k) = |p|T(kp)`):

* the `(U, L)` cosets carry `C_q(k)` (`sum_ul_phase`), the `(L, U)` cosets `C_p(k)`;
* the `(L, L)` cosets carry `C_m(k) = χ_p(v̄)χ_q(ū)C_p(k)C_q(k)` (`llWeight_eq`, `up + vq = 1`), and with Patterson at both
  primes and cubic reciprocity `C_m(k)T(k)² = |m|T(k)T(km)` for `(k, m) = 1` (`llWeight_mul_sq`): the reciprocity
  phases cancel in the low–low cosets.

Hence (`cuspConstantTerm_remainder`), with `ρ = |p|`, `σ = |q|`, the constant term of `G'_m` is `N(m)|P|` times

`2(ρσ)^{−2}R_A(ρσv) + 2(p/q)₃(ρσ)^{−2}R_B(ρσv) + 2ρ^{−2}σR_{UL}(ρv/σ) + 2σ^{−2}ρR_{LU}(σv/ρ) + ρσR_{D_m}(v/ρσ)
  − (2 + 2(p/q)₃)R(v)`,

the Bessel series of `T(h)T(−m²h)`, `T(lq²)T(−lp²)`, `[q ∤ k]T(kq)T(−kp²)`, `[p ∤ k]T(kp)T(−kq²)` and
`[(k, m) = 1]T(k)T(km)`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

theorem sum_units_mul {F : Type*} [Field F] [Fintype F] (g : {y : F // y ≠ 0} → ℂ) (a : F) (ha : a ≠ 0) :
    ∑ y : {y : F // y ≠ 0}, g ⟨y.1 * a, mul_ne_zero y.2 ha⟩ = ∑ y, g y :=
  Fintype.sum_bijective (fun y : {y : F // y ≠ 0} => (⟨y.1 * a, mul_ne_zero y.2 ha⟩ : {y : F // y ≠ 0}))
    ⟨fun x y h => Subtype.ext (mul_right_cancel₀ ha (congrArg Subtype.val h)),
      fun y => ⟨⟨y.1 * a⁻¹, mul_ne_zero y.2 (inv_ne_zero ha)⟩, Subtype.ext (by
        show y.1 * a⁻¹ * a = y.1
        rw [inv_mul_cancel_right₀ ha])⟩⟩ _ _ fun _ => rfl

/-- `T(h)T(h')·w·K·w'·K = c·T(h)T(h')·d²K²` when `ww' = cd²`. -/
theorem bessel_prod (T T' K a b c d : ℂ) (h : a * b = c * d ^ 2) :
    T * a * K * (T' * b * K) = c * (T * T' * (d ^ 2 * K ^ 2)) := by
  linear_combination (T * T' * K ^ 2) * h

theorem bessel_prod_twisted (C T T' T'' K a b c d ρ : ℂ) (hC : C * T = ρ * T'') (h : a * b = c * d ^ 2) :
    C * (T * a * K * (T' * b * K)) = c * ρ * (T'' * T' * (d ^ 2 * K ^ 2)) := by
  linear_combination (a * b * T' * K ^ 2) * hC + (ρ * T'' * T' * K ^ 2) * h

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `C_p(k) = Σ_{y≢0} χ_p(3y)ψ_k((9y)⁻¹)`. -/
theorem twistedCoeff_eq_sum (k : O) :
    P.twistedCoeff k = ∑ y : {y : P.Res // y ≠ 0}, P.chi (3 * y.1) * P.psi k ((9 * y.1)⁻¹) := by
  unfold twistedCoeff
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← P.chi_res, map_mul, res_lift, res_three, P.phase_eq_psi, P.res_neg_lowBeta _ (P.not_dvd_lift y), res_lift]

/-- `Σ_{y≢0} χ_p(3y)ψ_k(c(9y)⁻¹) = χ_p(c)C_p(k)` for `c ≢ 0`. -/
theorem sum_twisted_unit (k : O) (c : P.Res) (hc : c ≠ 0) :
    ∑ y : {y : P.Res // y ≠ 0}, P.chi (3 * y.1) * P.psi k ((9 * y.1)⁻¹ * c) = P.chi c * P.twistedCoeff k := by
  rw [P.twistedCoeff_eq_sum, Finset.mul_sum, ← sum_units_mul _ c hc]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h9 : (9 : P.Res) * y.1 ≠ 0 := mul_ne_zero P.nine_ne_zero' y.2
  rw [show (9 * (y.1 * c))⁻¹ * c = (9 * y.1)⁻¹ by field_simp, show (3 : P.Res) * (y.1 * c) = c * (3 * y.1) by ring,
    map_mul]
  ring

end PrimaryPrime

namespace PrimaryPair

variable (R : PrimaryPair)

/-! ### The coset weights -/

/-- **The `(U, L)` cosets carry `C_q`.** -/
theorem sum_ul_phase (k : O) :
    ∑ y₂ : {y : R.Q.Res // y ≠ 0}, ringComplex (symbol (3 * R.yUL y₂) R.Q.p) *
        tracePhase (cuspFrequency k * (-(3 * ringComplex (R.Q.lowBeta (R.yUL y₂))) / ringComplex R.Q.p)) =
      R.Q.twistedCoeff k :=
  sum_units_mul (fun y : {y : R.Q.Res // y ≠ 0} => ringComplex (symbol (3 * R.Q.lift y.1) R.Q.p) *
    tracePhase (cuspFrequency k * (-(3 * ringComplex (R.Q.lowBeta (R.Q.lift y.1))) / ringComplex R.Q.p)))
    R.pInv R.pInv_ne_zero

/-- **The `(L, U)` cosets carry `C_p`.** -/
theorem sum_lu_phase (k : O) :
    ∑ y₁ : {y : R.P.Res // y ≠ 0}, ringComplex (symbol (3 * R.yLU y₁) R.P.p) *
        tracePhase (cuspFrequency k * (-(3 * ringComplex (R.P.lowBeta (R.yLU y₁))) / ringComplex R.P.p)) =
      R.P.twistedCoeff k :=
  sum_units_mul (fun y : {y : R.P.Res // y ≠ 0} => ringComplex (symbol (3 * R.P.lift y.1) R.P.p) *
    tracePhase (cuspFrequency k * (-(3 * ringComplex (R.P.lowBeta (R.P.lift y.1))) / ringComplex R.P.p)))
    R.qInv R.qInv_ne_zero

theorem summable_twisted_terms (a b : O → ℂ) (ha : Summable (fun h => ‖a h‖)) (hb : Summable (fun h => ‖b h‖))
    (f : O → O) (c : ℂ) (φ : O → ℂ) (hφ : ∀ k, ‖φ k‖ = 1) :
    Summable (fun k => c * (a k * φ k * b (f k))) := by
  refine Summable.mul_left _ (Summable.of_norm_bounded (ha.mul_right (∑' j, ‖b j‖)) fun k => ?_)
  rw [norm_mul, norm_mul, hφ, mul_one]
  exact mul_le_mul_of_nonneg_left (hb.le_tsum _ fun j _ => norm_nonneg _) (norm_nonneg _)

theorem ul_sum_eq (v : ℝ) (hv : 0 < v) :
    ∑ y₂ : {y : R.Q.Res // y ≠ 0}, ringComplex (symbol (3 * R.yUL y₂) R.Q.p) * R.ulConv v (R.Q.lowBeta (R.yUL y₂)) 0 =
      ∑' k : O, R.Q.twistedCoeff k * (R.ampHL v k * R.ampLL v (-(k * (R.P.p * R.P.p)))) := by
  simp only [ulConv, cuspConv_dilate_zero R.PP_ne_zero, phasedCoeff]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun y _ => summable_twisted_terms _ _ (R.summable_ampHL v hv)
    (R.summable_ampLL v hv) _ _ _ fun k => tracePhase_norm _)]
  refine tsum_congr fun k => ?_
  rw [← R.sum_ul_phase k, Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem lu_sum_eq (v : ℝ) (hv : 0 < v) :
    ∑ y₁ : {y : R.P.Res // y ≠ 0}, ringComplex (symbol (3 * R.yLU y₁) R.P.p) * R.luConv v (R.P.lowBeta (R.yLU y₁)) 0 =
      ∑' k : O, R.P.twistedCoeff k * (R.ampLH v k * R.ampLL v (-(k * (R.Q.p * R.Q.p)))) := by
  simp only [luConv, cuspConv_dilate_zero R.QQ_ne_zero, phasedCoeff]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun y _ => summable_twisted_terms _ _ (R.summable_ampLH v hv)
    (R.summable_ampLL v hv) _ _ _ fun k => tracePhase_norm _)]
  refine tsum_congr fun k => ?_
  rw [← R.sum_lu_phase k, Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- The weight `C_m(k)` of the low–low cosets. -/
def llWeight (k : O) : ℂ :=
  ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
    ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
      tracePhase (cuspFrequency k *
        (-(3 * ringComplex (R.mLowBeta (R.crt y₁.1 y₂.1))) / ringComplex R.Q.p / ringComplex R.P.p))

theorem ll_sum_eq (v : ℝ) (hv : 0 < v) :
    ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
        ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) * R.llConv v (R.mLowBeta (R.crt y₁.1 y₂.1)) 0 =
      ∑' k : O, R.llWeight k * (R.ampLL v k * R.ampLL v (-k)) := by
  simp only [llConv, cuspConv, phasedCoeff, zero_sub]
  simp_rw [← tsum_mul_left]
  have hs : ∀ (y₁ : {y : R.P.Res // y ≠ 0}) (y₂ : {y : R.Q.Res // y ≠ 0}), Summable (fun k =>
      ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) * (R.ampLL v k *
        tracePhase (cuspFrequency k * (-(3 * ringComplex (R.mLowBeta (R.crt y₁.1 y₂.1))) / ringComplex R.Q.p /
          ringComplex R.P.p)) * R.ampLL v (-k))) := fun _ _ =>
    summable_twisted_terms _ _ (R.summable_ampLL v hv) (R.summable_ampLL v hv) _ _ _ fun k => tracePhase_norm _
  simp_rw [← Summable.tsum_finsetSum (fun y₂ _ => hs _ y₂)]
  rw [← Summable.tsum_finsetSum (fun y₁ _ => summable_sum fun y₂ _ => hs y₁ y₂)]
  refine tsum_congr fun k => ?_
  rw [llWeight, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun y₂ _ => by ring

theorem P_res_neg_mLowBeta (y₁ : {y : R.P.Res // y ≠ 0}) (y₂ : {y : R.Q.Res // y ≠ 0}) :
    R.P.res (-R.mLowBeta (R.crt y₁.1 y₂.1)) = (9 * y₁.1)⁻¹ := by
  have h := congrArg R.P.res (R.m_low_det _ (R.isCoprime_crt y₁ y₂))
  simp only [map_sub, map_mul, map_one, R.P.res_p, zero_mul, zero_sub, R.P_res_crt, PrimaryPrime.res_nine] at h
  apply eq_inv_of_mul_eq_one_left
  rw [map_neg]
  linear_combination h

theorem Q_res_neg_mLowBeta (y₁ : {y : R.P.Res // y ≠ 0}) (y₂ : {y : R.Q.Res // y ≠ 0}) :
    R.Q.res (-R.mLowBeta (R.crt y₁.1 y₂.1)) = (9 * y₂.1)⁻¹ := by
  have h := congrArg R.Q.res (R.m_low_det _ (R.isCoprime_crt y₁ y₂))
  simp only [map_sub, map_mul, map_one, R.Q.res_p, zero_mul, mul_zero, zero_sub, R.Q_res_crt,
    PrimaryPrime.res_nine] at h
  apply eq_inv_of_mul_eq_one_left
  rw [map_neg]
  linear_combination h

/-- The phase at `m` splits by `1/m = u/q + v/p`. -/
theorem phase_split (k β : O) :
    tracePhase (cuspFrequency k * (-(3 * ringComplex β) / ringComplex R.Q.p / ringComplex R.P.p)) =
      R.P.psi k (R.P.res (-(β * R.crtV))) * R.Q.psi k (R.Q.res (-(β * R.crtU))) := by
  have hP := R.P.ringComplex_ne_zero
  have hQ := R.Q.ringComplex_ne_zero
  have hs := congrArg ringComplex R.crt_spec
  simp only [map_add, map_mul, map_one] at hs
  rw [← R.P.phase_eq_psi k (β * R.crtV), ← R.Q.phase_eq_psi k (β * R.crtU), ← AddChar.map_add_eq_mul, ← mul_add]
  congr 2
  rw [map_mul, map_mul, show -(3 * ringComplex β) = -(3 * ringComplex β) *
    (ringComplex R.crtU * ringComplex R.P.p + ringComplex R.crtV * ringComplex R.Q.p) by rw [hs, mul_one]]
  field_simp
  ring

/-- **The low–low weight factors**: `C_m(k) = χ_p(v̄)χ_q(ū)C_p(k)C_q(k)`. -/
theorem llWeight_eq (k : O) :
    R.llWeight k = R.P.chi (R.P.res R.crtV) * R.Q.chi (R.Q.res R.crtU) * (R.P.twistedCoeff k * R.Q.twistedCoeff k) := by
  have hterm : ∀ (y₁ : {y : R.P.Res // y ≠ 0}) (y₂ : {y : R.Q.Res // y ≠ 0}),
      ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
        tracePhase (cuspFrequency k *
          (-(3 * ringComplex (R.mLowBeta (R.crt y₁.1 y₂.1))) / ringComplex R.Q.p / ringComplex R.P.p)) =
      (R.P.chi (3 * y₁.1) * R.P.psi k ((9 * y₁.1)⁻¹ * R.P.res R.crtV)) *
        (R.Q.chi (3 * y₂.1) * R.Q.psi k ((9 * y₂.1)⁻¹ * R.Q.res R.crtU)) := by
    intro y₁ y₂
    rw [symbol_mul_denominator, map_mul, ← R.P.chi_res, ← R.Q.chi_res, R.phase_split, ← neg_mul, ← neg_mul]
    simp only [map_mul, R.P_res_neg_mLowBeta, R.Q_res_neg_mLowBeta, R.P_res_crt, R.Q_res_crt, PrimaryPrime.res_three]
    ring
  have hcp : R.P.res R.crtV ≠ 0 := fun h => R.not_dvd_crtV ((R.P.res_eq_zero_iff _).mp h)
  have hcq : R.Q.res R.crtU ≠ 0 := fun h => R.not_dvd_crtU_mul (by
    rw [← R.Q.res_eq_zero_iff, map_mul, h, zero_mul])
  rw [llWeight]
  simp_rw [hterm]
  rw [← Finset.sum_mul_sum, R.P.sum_twisted_unit k _ hcp, R.Q.sum_twisted_unit k _ hcq]
  ring

/-! ### Patterson at both primes and reciprocity -/

/-- `T(k)T(km)` for `k` prime to `m`, `0` otherwise. -/
def mDilateCoeff (k : O) : ℂ :=
  if R.P.p ∣ k ∨ R.Q.p ∣ k then 0 else
    rationalSourceResidualFourierCoefficient k * rationalSourceResidualFourierCoefficient (k * (R.P.p * R.Q.p))

theorem chi_crtV_mul : R.P.chi (R.P.res R.crtV) * ringComplex (symbol R.Q.p R.P.p) = 1 := by
  have h : R.P.res R.crtV * R.P.res R.Q.p = 1 := by
    rw [← map_mul, show R.crtV * R.Q.p = 1 - R.crtU * R.P.p by linear_combination R.crt_spec, map_sub, map_one,
      map_mul, R.P.res_p, mul_zero, sub_zero]
  rw [← R.P.chi_res, ← map_mul, h, MulChar.map_one]

theorem chi_crtU_mul : R.Q.chi (R.Q.res R.crtU) * ringComplex (symbol R.P.p R.Q.p) = 1 := by
  have h : R.Q.res R.crtU * R.Q.res R.P.p = 1 := by
    rw [← map_mul, show R.crtU * R.P.p = 1 - R.crtV * R.Q.p by linear_combination R.crt_spec, map_sub, map_one,
      map_mul, R.Q.res_p, mul_zero, sub_zero]
  rw [← R.Q.chi_res, ← map_mul, h, MulChar.map_one]

theorem symbol_reciprocity_pair : symbol R.P.p R.Q.p = symbol R.Q.p R.P.p :=
  symbol_reciprocity _ _ R.P.primary R.Q.primary

theorem symbol_cube : ringComplex (symbol R.Q.p R.P.p) ^ 3 = 1 := by
  rw [← map_pow, symbol_cube_of_isCoprime _ _ R.P.primary R.coprime.symm, map_one]

/-- `χ_p(v̄)χ_q(ū) = (q/p)₃`. -/
theorem chi_crt_mul : R.P.chi (R.P.res R.crtV) * R.Q.chi (R.Q.res R.crtU) = ringComplex (symbol R.Q.p R.P.p) := by
  have hX := R.chi_crtV_mul
  have hY := R.chi_crtU_mul
  rw [R.symbol_reciprocity_pair] at hY
  linear_combination (-(R.P.chi (R.P.res R.crtV) * R.Q.chi (R.Q.res R.crtU))) * R.symbol_cube +
    ringComplex (symbol R.Q.p R.P.p) * (R.Q.chi (R.Q.res R.crtU) * ringComplex (symbol R.Q.p R.P.p)) * hX +
    ringComplex (symbol R.Q.p R.P.p) * hY

/-- **The reciprocity phases cancel in the low–low cosets**: `C_m(k)T(k)² = |p||q|T(k)T(km)`. -/
theorem llWeight_mul_sq (k : O) :
    R.llWeight k * rationalSourceResidualFourierCoefficient k ^ 2 =
      (‖ringComplex R.P.p‖ : ℂ) * (‖ringComplex R.Q.p‖ : ℂ) * R.mDilateCoeff k := by
  rw [R.llWeight_eq]
  by_cases hp : R.P.p ∣ k
  · rw [R.P.twistedCoeff_of_dvd k hp, mDilateCoeff, if_pos (Or.inl hp)]
    ring
  by_cases hq : R.Q.p ∣ k
  · rw [R.Q.twistedCoeff_of_dvd k hq, mDilateCoeff, if_pos (Or.inr hq)]
    ring
  have hpq : ¬ R.P.p ∣ k * R.Q.p := fun h => (R.P.prime.dvd_or_dvd h).elim hp R.P_not_dvd_Q
  have e1 := R.P.twistedCoeff_mul k hp
  have e2 := R.Q.twistedCoeff_mul k hq
  have n1 := rationalSourceResidualFourierCoefficient_prime_normalized R.P.p R.P.prime R.P.primary k hp
  have n2 := rationalSourceResidualFourierCoefficient_prime_normalized R.Q.p R.Q.prime R.Q.primary k hq
  have n3 := rationalSourceResidualFourierCoefficient_prime_normalized R.P.p R.P.prime R.P.primary _ hpq
  rw [show 9 * (k * R.Q.p) = 9 * k * R.Q.p by ring, symbol_mul_numerator, map_mul] at n3
  rw [mDilateCoeff, if_neg (not_or.mpr ⟨hp, hq⟩), show k * (R.P.p * R.Q.p) = k * R.Q.p * R.P.p by ring, n3,
    show R.P.chi (R.P.res R.crtV) * R.Q.chi (R.Q.res R.crtU) * (R.P.twistedCoeff k * R.Q.twistedCoeff k) *
        rationalSourceResidualFourierCoefficient k ^ 2 =
      R.P.chi (R.P.res R.crtV) * R.Q.chi (R.Q.res R.crtU) *
        ((R.P.twistedCoeff k * rationalSourceResidualFourierCoefficient k) *
          (R.Q.twistedCoeff k * rationalSourceResidualFourierCoefficient k)) by ring, e1, e2, n1, n2, R.chi_crt_mul]
  ring

/-! ### The Bessel series -/

/-- `T(h)T(−m²h)`. -/
def shiftCoeff (h : O) : ℂ :=
  rationalSourceResidualFourierCoefficient h *
    rationalSourceResidualFourierCoefficient (-(h * (R.P.p * R.Q.p)) * R.Q.p * R.P.p)

/-- `T(lq²)T(−lp²)`. -/
def crossCoeff (l : O) : ℂ :=
  rationalSourceResidualFourierCoefficient (l * R.Q.p * R.Q.p) *
    rationalSourceResidualFourierCoefficient (-(l * R.P.p) * R.P.p)

/-- `T(kq)T(−kp²)` for `q ∤ k`. -/
def ulCoeff (k : O) : ℂ :=
  if R.Q.p ∣ k then 0 else
    rationalSourceResidualFourierCoefficient (k * R.Q.p) *
      rationalSourceResidualFourierCoefficient (-(k * (R.P.p * R.P.p)))

/-- `T(kp)T(−kq²)` for `p ∤ k`. -/
def luCoeff (k : O) : ℂ :=
  if R.P.p ∣ k then 0 else
    rationalSourceResidualFourierCoefficient (k * R.P.p) *
      rationalSourceResidualFourierCoefficient (-(k * (R.Q.p * R.Q.p)))

theorem hh_series_eq (v : ℝ) (hv : 0 < v) :
    ∑' h : O, R.ampHH v h * R.ampLL v (-(h * (R.P.p * R.Q.p)) * R.Q.p * R.P.p) =
      thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
        ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ *
          besselRemainder R.shiftCoeff (‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v)) := by
  have hp := R.P.norm_pos
  have hq := R.Q.norm_pos
  have hs := summable_amplitude_mul (R.summable_ampHH v hv) (R.summable_ampLL v hv)
    (fun h => -(h * (R.P.p * R.Q.p)) * R.Q.p * R.P.p)
  rw [hs.tsum_eq_add_tsum_ite 0, besselRemainder, ← tsum_mul_left]
  congr 1
  · rw [zero_mul, neg_zero, zero_mul, zero_mul, ampHH, ampLL, rationalSourceModeAmplitude_zero,
      rationalSourceModeAmplitude_zero,
      ← PrimaryPrime.cpow_mul_mul_cpow_div (‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) v (mul_pos hp hq) hv,
      show ‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v) = ‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖ * v by ring,
      show v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖ = v / (‖ringComplex R.P.p‖ * ‖ringComplex R.Q.p‖) by
        rw [div_div, mul_comm]]
    push_cast
    ring
  · refine tsum_congr fun h => ?_
    by_cases hh : h = 0
    · simp [hh]
    · have hh' : -(h * (R.P.p * R.Q.p)) * R.Q.p * R.P.p ≠ 0 :=
        mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hh (mul_ne_zero R.P.ne_zero R.Q.ne_zero)))
          R.Q.ne_zero) R.P.ne_zero
      have hn : ‖cuspFrequency (-(h * (R.P.p * R.Q.p)) * R.Q.p * R.P.p)‖ =
          ‖cuspFrequency h‖ * (‖ringComplex R.P.p‖ ^ 2 * ‖ringComplex R.Q.p‖ ^ 2) := by
        simp only [cuspFrequency_mul_right, cuspFrequency_neg, norm_mul, norm_neg, map_mul]
        ring
      have e : 4 * Real.pi * (‖cuspFrequency h‖ * (‖ringComplex R.P.p‖ ^ 2 * ‖ringComplex R.Q.p‖ ^ 2)) *
          (v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖) =
          4 * Real.pi * ‖cuspFrequency h‖ * (‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v)) := by
        field_simp
      rw [if_neg hh, if_neg hh, ampHH, ampLL, rationalSourceModeAmplitude_bessel _ (mul_pos hp (mul_pos hq hv)) h hh,
        rationalSourceModeAmplitude_bessel _ (div_pos (div_pos hv hq) hp) _ hh', hn, e, shiftCoeff, besselSq]
      exact bessel_prod _ _ _ _ _ _ _ (by push_cast; field_simp)

theorem hl_series_eq (v : ℝ) (hv : 0 < v) :
    ∑' l : O, R.ampHL v (l * R.Q.p * R.Q.p) * R.ampLH v (-(l * R.P.p) * R.P.p) =
      thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
        ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ *
          besselRemainder R.crossCoeff (‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v)) := by
  have hp := R.P.norm_pos
  have hq := R.Q.norm_pos
  have hs := summable_amplitude_mul ((R.summable_ampHL v hv).comp_injective
    (mul_right_injective_O R.QQ_ne_zero)) (R.summable_ampLH v hv) (fun l => -(l * R.P.p) * R.P.p)
  simp only [← mul_assoc] at hs
  rw [hs.tsum_eq_add_tsum_ite 0, besselRemainder, ← tsum_mul_left]
  congr 1
  · rw [zero_mul, zero_mul, zero_mul, neg_zero, zero_mul, ampHL, ampLH, rationalSourceModeAmplitude_zero,
      rationalSourceModeAmplitude_zero,
      ← PrimaryPrime.cpow_mul_mul_cpow_div (‖ringComplex R.P.p‖ / ‖ringComplex R.Q.p‖) v (div_pos hp hq) hv,
      ← div_mul_eq_mul_div, show ‖ringComplex R.Q.p‖ * v / ‖ringComplex R.P.p‖ =
        v / (‖ringComplex R.P.p‖ / ‖ringComplex R.Q.p‖) by rw [div_div_eq_mul_div, mul_comm]]
    push_cast
    ring
  · refine tsum_congr fun l => ?_
    by_cases hl : l = 0
    · simp [hl]
    · have h1 : l * R.Q.p * R.Q.p ≠ 0 := mul_ne_zero (mul_ne_zero hl R.Q.ne_zero) R.Q.ne_zero
      have h2 : -(l * R.P.p) * R.P.p ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hl R.P.ne_zero)) R.P.ne_zero
      have hn1 : ‖cuspFrequency (l * R.Q.p * R.Q.p)‖ = ‖cuspFrequency l‖ * ‖ringComplex R.Q.p‖ ^ 2 := by
        simp only [cuspFrequency_mul_right, norm_mul]
        ring
      have hn2 : ‖cuspFrequency (-(l * R.P.p) * R.P.p)‖ = ‖cuspFrequency l‖ * ‖ringComplex R.P.p‖ ^ 2 := by
        simp only [cuspFrequency_mul_right, cuspFrequency_neg, norm_mul, norm_neg]
        ring
      have e1 : 4 * Real.pi * (‖cuspFrequency l‖ * ‖ringComplex R.Q.p‖ ^ 2) * (‖ringComplex R.P.p‖ * v / ‖ringComplex R.Q.p‖) =
          4 * Real.pi * ‖cuspFrequency l‖ * (‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v)) := by
        field_simp
      have e2 : 4 * Real.pi * (‖cuspFrequency l‖ * ‖ringComplex R.P.p‖ ^ 2) * (‖ringComplex R.Q.p‖ * v / ‖ringComplex R.P.p‖) =
          4 * Real.pi * ‖cuspFrequency l‖ * (‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v)) := by
        field_simp
      rw [if_neg hl, if_neg hl, ampHL, ampLH, rationalSourceModeAmplitude_bessel _ (div_pos (mul_pos hp hv) hq) _ h1,
        rationalSourceModeAmplitude_bessel _ (div_pos (mul_pos hq hv) hp) _ h2, hn1, hn2, e1, e2, crossCoeff, besselSq]
      exact bessel_prod _ _ _ _ _ _ _ (by push_cast; field_simp)

theorem ul_series_eq (v : ℝ) (hv : 0 < v) :
    ∑' k : O, R.Q.twistedCoeff k * (R.ampHL v k * R.ampLL v (-(k * (R.P.p * R.P.p)))) =
      ((‖ringComplex R.P.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.Q.p‖ : ℂ) *
        besselRemainder R.ulCoeff (‖ringComplex R.P.p‖ * v / ‖ringComplex R.Q.p‖) := by
  have hp := R.P.norm_pos
  have hq := R.Q.norm_pos
  rw [besselRemainder, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · rw [if_pos hk, hk, R.Q.twistedCoeff_of_dvd 0 (dvd_zero _)]
    ring
  rw [if_neg hk]
  by_cases hqk : R.Q.p ∣ k
  · rw [R.Q.twistedCoeff_of_dvd k hqk, ulCoeff, if_pos hqk]
    ring
  have hk' : -(k * (R.P.p * R.P.p)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hk R.PP_ne_zero)
  have hn : ‖cuspFrequency (-(k * (R.P.p * R.P.p)))‖ = ‖cuspFrequency k‖ * ‖ringComplex R.P.p‖ ^ 2 := by
    simp only [cuspFrequency_neg, norm_neg, cuspFrequency_mul_right, norm_mul, map_mul]
    ring
  have e : 4 * Real.pi * (‖cuspFrequency k‖ * ‖ringComplex R.P.p‖ ^ 2) * (v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖) =
      4 * Real.pi * ‖cuspFrequency k‖ * (‖ringComplex R.P.p‖ * v / ‖ringComplex R.Q.p‖) := by
    field_simp
  rw [ampHL, ampLL, rationalSourceModeAmplitude_bessel _ (div_pos (mul_pos hp hv) hq) k hk,
    rationalSourceModeAmplitude_bessel _ (div_pos (div_pos hv hq) hp) _ hk', hn, e, ulCoeff, if_neg hqk, besselSq]
  exact bessel_prod_twisted _ _ _ _ _ _ _ _ _ _ (R.Q.twistedCoeff_mul k hqk) (by push_cast; field_simp)

theorem lu_series_eq (v : ℝ) (hv : 0 < v) :
    ∑' k : O, R.P.twistedCoeff k * (R.ampLH v k * R.ampLL v (-(k * (R.Q.p * R.Q.p)))) =
      ((‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.P.p‖ : ℂ) *
        besselRemainder R.luCoeff (‖ringComplex R.Q.p‖ * v / ‖ringComplex R.P.p‖) := by
  have hp := R.P.norm_pos
  have hq := R.Q.norm_pos
  rw [besselRemainder, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · rw [if_pos hk, hk, R.P.twistedCoeff_of_dvd 0 (dvd_zero _)]
    ring
  rw [if_neg hk]
  by_cases hpk : R.P.p ∣ k
  · rw [R.P.twistedCoeff_of_dvd k hpk, luCoeff, if_pos hpk]
    ring
  have hk' : -(k * (R.Q.p * R.Q.p)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hk R.QQ_ne_zero)
  have hn : ‖cuspFrequency (-(k * (R.Q.p * R.Q.p)))‖ = ‖cuspFrequency k‖ * ‖ringComplex R.Q.p‖ ^ 2 := by
    simp only [cuspFrequency_neg, norm_neg, cuspFrequency_mul_right, norm_mul, map_mul]
    ring
  have e : 4 * Real.pi * (‖cuspFrequency k‖ * ‖ringComplex R.Q.p‖ ^ 2) * (v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖) =
      4 * Real.pi * ‖cuspFrequency k‖ * (‖ringComplex R.Q.p‖ * v / ‖ringComplex R.P.p‖) := by
    field_simp
  rw [ampLH, ampLL, rationalSourceModeAmplitude_bessel _ (div_pos (mul_pos hq hv) hp) k hk,
    rationalSourceModeAmplitude_bessel _ (div_pos (div_pos hv hq) hp) _ hk', hn, e, luCoeff, if_neg hpk, besselSq]
  exact bessel_prod_twisted _ _ _ _ _ _ _ _ _ _ (R.P.twistedCoeff_mul k hpk) (by push_cast; field_simp)

theorem ll_series_eq (v : ℝ) (hv : 0 < v) :
    ∑' k : O, R.llWeight k * (R.ampLL v k * R.ampLL v (-k)) =
      (‖ringComplex R.P.p‖ : ℂ) * (‖ringComplex R.Q.p‖ : ℂ) *
        besselRemainder R.mDilateCoeff (v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖) := by
  have hw : 0 < v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖ := div_pos (div_pos hv R.Q.norm_pos) R.P.norm_pos
  rw [besselRemainder, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · rw [if_pos hk, hk, llWeight_eq, R.P.twistedCoeff_of_dvd 0 (dvd_zero _)]
    ring
  rw [if_neg hk, ampLL, sourceAmplitude_mul_neg _ hw k hk, besselSq]
  linear_combination (((v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ 2 *
    schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency k‖ * (v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖)) ^ 2) *
      R.llWeight_mul_sq k

/-! ### The constant term of `G'_m` -/

theorem sourceTrace_continuous_z (v : ℝ) (hv : 0 < v) : Continuous (fun z => R.sourceTrace (upperPoint z v hv)) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := R.continuous_blocks v hv
  have h : (fun z => R.sourceTrace (upperPoint z v hv)) = fun z =>
      2 * (R.hh sourceTheta (upperPoint z v hv) * R.llSum sourceTheta (upperPoint z v hv)) +
        2 * ringComplex (symbol R.P.p R.Q.p) *
          (R.hlSum sourceTheta (upperPoint z v hv) * R.lhSum sourceTheta (upperPoint z v hv)) +
        2 * R.ulBlock sourceTheta (upperPoint z v hv) + 2 * R.luBlock sourceTheta (upperPoint z v hv) +
        R.llBlock sourceTheta (upperPoint z v hv) := funext fun z => by
    rw [sourceTrace, R.heckeTrace_eq_blocks sourceTheta sourceTheta_automorphy]
  rw [h]
  exact ((((continuous_const.mul c1).add (continuous_const.mul c2)).add (continuous_const.mul c3)).add
    (continuous_const.mul c4)).add c5

/-- **The constant term of `G'_m` as five Bessel series.** -/
theorem cuspConstantTerm_remainder (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm R.remainder v = R.normM * periodArea *
      (2 * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ *
          besselRemainder R.shiftCoeff (‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v)) +
        2 * ringComplex (symbol R.P.p R.Q.p) * ((‖ringComplex R.P.p‖ : ℂ) ^ 2 * (‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ *
          besselRemainder R.crossCoeff (‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v)) +
        2 * (((‖ringComplex R.P.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.Q.p‖ : ℂ)) *
          besselRemainder R.ulCoeff (‖ringComplex R.P.p‖ * v / ‖ringComplex R.Q.p‖) +
        2 * (((‖ringComplex R.Q.p‖ : ℂ) ^ 2)⁻¹ * (‖ringComplex R.P.p‖ : ℂ)) *
          besselRemainder R.luCoeff (‖ringComplex R.Q.p‖ * v / ‖ringComplex R.P.p‖) +
        (‖ringComplex R.P.p‖ : ℂ) * (‖ringComplex R.Q.p‖ : ℂ) *
          besselRemainder R.mDilateCoeff (v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖) -
        (2 + 2 * ringComplex (symbol R.P.p R.Q.p)) *
          besselRemainder (fun h => rationalSourceResidualFourierCoefficient h ^ 2) v) := by
  have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z => cuspCoordinateLift_positive v z hv
  have hc1 := R.sourceTrace_continuous_z v hv
  have hc2 : Continuous (fun z : ℂ => sourceTheta (upperPoint z v hv) ^ 2) := by
    have h := cuspCharacterSeries_continuous _ (rationalSourceModeAmplitude_summable v hv)
    simp_rw [sourceTheta, cubicSourceResidualFunction_fourier_expansion]
    exact h.pow 2
  rw [cuspConstantTerm]
  simp_rw [hlift, remainder]
  rw [integral_sub (integrableOn_periodDomain_of_continuous _ hc1)
    ((integrableOn_periodDomain_of_continuous _ hc2).const_mul _), integral_const_mul, R.integral_sourceTrace v hv,
    R.hh_series_eq v hv, R.hl_series_eq v hv, R.ul_sum_eq v hv, R.ul_series_eq v hv, R.lu_sum_eq v hv,
    R.lu_series_eq v hv, R.ll_sum_eq v hv, R.ll_series_eq v hv, integral_sourceThetaSq_periodDomain v hv,
    thetaSqRemainder_eq v hv, growth, normM]
  ring

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
