import GaloisForLFunctions.RHTower.GaussianCentralGapCompleteBias

/-!
# An explicit uniform form of the central Gaussian budget

With `P(y) = Σ Λ(n) n^{-1/2} e^{-yn²}` and `C(y) = ∫₁^∞ u^{-1/2} e^{-yu²} du`:

**RH ⟺ `P(y) − C(y) ≤ −1/10 + 32 √y` for every `0 < y ≤ 1`**
(`riemannHypothesis_iff_gaussianCentralGap_le_explicit`).

Every constant is explicit, so RH becomes a single inequality required at each `y ∈ (0, 1]`.  A
violation at one `y` refutes RH, and for `y < (1/320)²` the inequality already forces `P(y) < C(y)`.

* The archimedean transform satisfies `Re A_y(½) ≤ Re A(½) + ‖A(½) − A_y(½)‖` with
  `‖A(½) − A_y(½)‖ ≤ (y(‖c_A‖ + 3/2) + 4(2y + 2Γ(3/2)√y)) π²/6 ≤ 31 √y`
  (`norm_gaussianArchimedeanCurrent_half_sub_MB_le`), and `Re A(½) ≤ −7/24`.
* Under RH the critical germ field is at most `2(1+y)(2 + γ − log 4π)` for **every** `y > 0`
  (`norm_tsum_criticalZeroGerm_le_of_riemannHypothesis`).
* The converse is the central budget law.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open XiAtlasFinitePart

theorem norm_gaussianArchimedeanConstant_le : ‖gaussianArchimedeanConstant‖ ≤ 1 := by
  rw [gaussianArchimedeanConstant]
  have hlog : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  rw [hlog, show (1 / 2 : ℂ) - ((Real.log Real.pi : ℝ) : ℂ) / 2 -
      (Real.eulerMascheroniConstant : ℂ) / 2 =
      ((1 / 2 - Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  have hl0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl1 : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
  have hpi := Real.pi_lt_d2
  have hγ0 := Real.one_half_lt_eulerMascheroniConstant
  have hγ1 := Real.eulerMascheroniConstant_lt_two_thirds
  rw [abs_le]
  constructor <;> norm_num at hpi ⊢ <;> linarith

theorem tsum_one_div_nat_add_one_sq_le :
    ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 ≤ 1654 / 1000 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
  rw [h.tsum_eq]
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  norm_num at hpi ⊢
  nlinarith

theorem gamma_three_halves_lt : Real.Gamma ((4 - 1) / 2) < 8875 / 10000 := by
  rw [show ((4 : ℝ) - 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  have hpi := Real.pi_lt_d2
  have hs : √Real.pi < 1775 / 1000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num at hpi ⊢
    linarith
  linarith

/-- `‖A(½) − A_y(½)‖ ≤ 31 √y` on `(0, 1]`. -/
theorem norm_gaussianArchimedeanCurrent_half_sub_MB_le {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ‖gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ) - gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ)‖ ≤
      31 * Real.sqrt y := by
  have hs : 0 < ((1 / 2 : ℝ) : ℂ).re := by norm_num
  have h := norm_gaussianArchimedeanCurrent_sub_MB_le two_pos hy hs
  have hre : ((1 / 2 : ℝ) : ℂ).re = 1 / 2 := by norm_num
  have hn : ‖((1 / 2 : ℝ) : ℂ) - 2‖ = 3 / 2 := by
    rw [show ((1 / 2 : ℝ) : ℂ) - 2 = ((-(3 / 2) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
  rw [hre, hn, show min (1 / 2 : ℝ) 1 / 2 = 1 / 4 by norm_num, ← Real.sqrt_eq_rpow] at h
  have hc := norm_gaussianArchimedeanConstant_le
  have hS := tsum_one_div_nat_add_one_sq_le
  have hS0 : 0 ≤ ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 := tsum_nonneg fun m => by positivity
  have hG := gamma_three_halves_lt
  have hG0 : 0 ≤ Real.Gamma ((4 - 1) / 2) := (Real.Gamma_pos_of_pos (by norm_num)).le
  have hsq : y ≤ Real.sqrt y := by
    have := Real.sqrt_le_sqrt hy1
    rw [Real.sqrt_one] at this
    nlinarith [Real.sq_sqrt hy.le, Real.sqrt_nonneg y]
  have hsq0 := Real.sqrt_nonneg y
  have hc0 := norm_nonneg gaussianArchimedeanConstant
  have hbr : y * ‖gaussianArchimedeanConstant‖ + y * (3 / 2) +
      (2 * y + 2 * Real.Gamma ((4 - 1) / 2) * Real.sqrt y) / (1 / 4) ≤ 18 * Real.sqrt y := by
    have e1 : y * ‖gaussianArchimedeanConstant‖ ≤ 1 * Real.sqrt y := by nlinarith
    have e2 : 2 * Real.Gamma ((4 - 1) / 2) * Real.sqrt y ≤ 2 * (8875 / 10000) * Real.sqrt y := by
      nlinarith
    have hd : (2 * y + 2 * Real.Gamma ((4 - 1) / 2) * Real.sqrt y) / (1 / 4) =
        4 * (2 * y + 2 * Real.Gamma ((4 - 1) / 2) * Real.sqrt y) := by ring
    rw [hd]
    nlinarith
  calc _ ≤ _ := h
    _ ≤ (18 * Real.sqrt y) * (1654 / 1000) := by
        gcongr
    _ ≤ 31 * Real.sqrt y := by nlinarith

/-- **Uniform bound under RH.**  Under RH, `P(y) − C(y) ≤ −1/10 + 32 √y` for every
`0 < y ≤ 1`. -/
theorem gaussianCentralGap_le_explicit_of_riemannHypothesis (hRH : RiemannHypothesis) {y : ℝ}
    (hy : 0 < y) (hy1 : y ≤ 1) :
    gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y ≤
      -1 / 10 + 32 * Real.sqrt y := by
  have hcast : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  have hgap := gaussianWeightedGap_eq_MB_sub_germField (σ := 1 / 2) (by norm_num) hy
  have hZ := norm_tsum_criticalZeroGerm_le_of_riemannHypothesis hRH hy
  have hA := norm_gaussianArchimedeanCurrent_half_sub_MB_le hy hy1
  have hbias := re_gaussianArchimedeanCurrent_half_le
  rw [← hcast] at hbias
  have hκ := xiEndpointCompletedCurvature_lt_231_div_2500
  have hκ0 := xiEndpointCompletedCurvature_pos
  set Z : ℂ := ∑' q : XiZeroCopy, ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
      gaussianIncompleteMellin y (xiZero q - ((1 / 2 : ℝ) : ℂ))) with hZdef
  set M : ℂ := gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ) with hM
  set A : ℂ := gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ) with hAdef
  have hre : gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y =
      A.re - (A - M).re - Z.re := by
    have := congrArg Complex.re hgap
    rw [Complex.ofReal_re, Complex.sub_re] at this
    rw [this, Complex.sub_re]
    ring
  rw [hre]
  have h1 : -(A - M).re ≤ 31 * Real.sqrt y := (neg_le_abs _).trans
    ((Complex.abs_re_le_norm _).trans hA)
  have h2 : -Z.re ≤ 2 * (1 + y) * xiEndpointCompletedCurvature :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hZ)
  have hsq : y ≤ Real.sqrt y := by
    have := Real.sqrt_le_sqrt hy1
    rw [Real.sqrt_one] at this
    nlinarith [Real.sq_sqrt hy.le, Real.sqrt_nonneg y]
  nlinarith

/-- **RH as an explicit uniform inequality.**  RH holds iff
`Σ Λ(n) n^{-1/2} e^{-yn²} ≤ ∫₁^∞ u^{-1/2} e^{-yu²} du − 1/10 + 32 √y` for every `0 < y ≤ 1`. -/
theorem riemannHypothesis_iff_gaussianCentralGap_le_explicit :
    RiemannHypothesis ↔ ∀ y : ℝ, 0 < y → y ≤ 1 →
      gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y ≤
        -1 / 10 + 32 * Real.sqrt y := by
  constructor
  · exact fun hRH y hy hy1 => gaussianCentralGap_le_explicit_of_riemannHypothesis hRH hy hy1
  · intro h
    refine riemannHypothesis_iff_gaussianCentralPrimeBudget.2 ⟨32, fun y hy hy1 => ?_⟩
    have := h y hy hy1
    have hs : Real.sqrt y ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt hy1
    linarith

end

end RHTower
