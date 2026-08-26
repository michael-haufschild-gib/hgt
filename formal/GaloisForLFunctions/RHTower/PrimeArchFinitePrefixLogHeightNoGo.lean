import GaloisForLFunctions.RHTower.PrimeArchFourthTracePurePrimeTail
import GaloisForLFunctions.RHTower.PrimeMassSharpUpper

/-!
# Finite-prefix no-go for the scalar prime defect

Every fixed initial von Mangoldt Dirichlet polynomial is uniformly bounded on the vertical
line `Re s = 1/4`.  The logarithmic normalization in the canonical scalar prime defect tends
to infinity there.  Consequently every fixed finite prime prefix drives its defect below every
real floor along Gaussian-rational heights.  Any proof of the scalar RH endpoint must therefore
use genuinely infinite, height-dependent prime cancellation.
-/

open Complex Set Filter

namespace RHTower

noncomputable section

/-- Finite initial von Mangoldt Dirichlet polynomial. -/
def finiteVonMangoldtPrimeFlux (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s n

/-- Uniform vertical envelope for the finite polynomial at real part `1/4`. -/
def finiteVonMangoldtPrimeFluxQuarterEnvelope (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-(1 / 4 : ℝ))

/-- A fixed finite von Mangoldt prefix is uniformly norm-bounded on `Re s = 1/4`. -/
theorem norm_finiteVonMangoldtPrimeFlux_le_quarterEnvelope
    (N : ℕ) {s : ℂ} (hs : s.re = 1 / 4) :
    ‖finiteVonMangoldtPrimeFlux N s‖ ≤
      finiteVonMangoldtPrimeFluxQuarterEnvelope N := by
  rw [finiteVonMangoldtPrimeFlux, finiteVonMangoldtPrimeFluxQuarterEnvelope]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, ← Complex.cpow_neg, norm_mul]
    have hpow : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) :=
      GaloisForLFunctions.norm_cpow_neg_eq_rpow_re (n : ℝ) (by positivity) s
    rw [hpow, hs]

/-- The absolute quarter-line envelope of the first `N` von Mangoldt terms is at most
`4(N+1)`.  The quarter power in `log n ≤ 4 n^(1/4)` exactly cancels the vertical envelope
weight `n^(-1/4)`. -/
theorem finiteVonMangoldtPrimeFluxQuarterEnvelope_le_four_mul_depth (N : ℕ) :
    finiteVonMangoldtPrimeFluxQuarterEnvelope N ≤ 4 * (N + 1 : ℝ) := by
  rw [finiteVonMangoldtPrimeFluxQuarterEnvelope]
  calc
    ∑ n ∈ Finset.range (N + 1),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ *
          (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
        ∑ _n ∈ Finset.range (N + 1), (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        simp
      · have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn0
        have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPosNat
        have hquarterPos : 0 < (n : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_pos_of_pos hnPos _
        have hlogQuarter := Real.log_le_sub_one_of_pos hquarterPos
        rw [Real.log_rpow hnPos] at hlogQuarter
        have hlog : Real.log n ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
          linarith
        have hLambda : ArithmeticFunction.vonMangoldt n ≤
            4 * (n : ℝ) ^ ((1 : ℝ) / 4) :=
          ArithmeticFunction.vonMangoldt_le_log.trans hlog
        rw [show ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
            ArithmeticFunction.vonMangoldt n by
          simp [Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]]
        calc
          ArithmeticFunction.vonMangoldt n *
              (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
              (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_right hLambda
              (Real.rpow_nonneg (by positivity) _)
          _ = 4 := by
            rw [mul_assoc, ← Real.rpow_add hnPos]
            norm_num
    _ = 4 * (N + 1 : ℝ) := by
      simp
      ring

/-- Chebyshev-scale sharpening of the finite envelope.  The proved half-weighted mass bound
`∑_{n≤N} Λ(n)n⁻¹ᐟ² ≤ 21√N`, multiplied by the maximal factor `N¹ᐟ⁴`, gives the natural
quarter-line growth `21N³ᐟ⁴`. -/
theorem finiteVonMangoldtPrimeFluxQuarterEnvelope_le_twentyOne_mul_depth_rpow_threeQuarter
    (N : ℕ) (hN : 1 ≤ N) :
    finiteVonMangoldtPrimeFluxQuarterEnvelope N ≤
      21 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
  have hNPos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hvm0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    exact not_isPrimePow_zero
  rw [finiteVonMangoldtPrimeFluxQuarterEnvelope]
  calc
    ∑ n ∈ Finset.range (N + 1),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ *
          (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
        ∑ n ∈ Finset.range (N + 1),
          (N : ℝ) ^ ((1 : ℝ) / 4) *
            (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        simp [hvm0]
      · have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn0
        have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPosNat
        have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        have hnNCast : (n : ℝ) ≤ N := by exact_mod_cast hnN
        have hpow : (n : ℝ) ^ ((1 : ℝ) / 4) ≤
            (N : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow hnPos.le hnNCast (by norm_num)
        have hid :
            ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ *
                (n : ℝ) ^ (-(1 / 4 : ℝ)) =
              (n : ℝ) ^ ((1 : ℝ) / 4) *
                (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by
          rw [show ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
              ArithmeticFunction.vonMangoldt n by
            simp [Real.norm_eq_abs,
              abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]]
          rw [Real.sqrt_eq_rpow]
          have hhalfPos : 0 < (n : ℝ) ^ ((1 : ℝ) / 2) :=
            Real.rpow_pos_of_pos hnPos _
          rw [show (n : ℝ) ^ ((1 : ℝ) / 4) *
              (ArithmeticFunction.vonMangoldt n /
                (n : ℝ) ^ ((1 : ℝ) / 2)) =
              ((n : ℝ) ^ ((1 : ℝ) / 4) *
                ArithmeticFunction.vonMangoldt n) /
                (n : ℝ) ^ ((1 : ℝ) / 2) by ring]
          rw [eq_div_iff (ne_of_gt hhalfPos)]
          calc
            ArithmeticFunction.vonMangoldt n *
                (n : ℝ) ^ (-(1 / 4 : ℝ)) *
                (n : ℝ) ^ ((1 : ℝ) / 2) =
              ArithmeticFunction.vonMangoldt n *
                ((n : ℝ) ^ (-(1 / 4 : ℝ)) *
                  (n : ℝ) ^ ((1 : ℝ) / 2)) := by ring
            _ = ArithmeticFunction.vonMangoldt n *
                (n : ℝ) ^ ((1 : ℝ) / 4) := by
              rw [← Real.rpow_add hnPos]
              norm_num
            _ = (n : ℝ) ^ ((1 : ℝ) / 4) *
                ArithmeticFunction.vonMangoldt n := by ring
        rw [hid]
        exact mul_le_mul_of_nonneg_right hpow
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.sqrt_nonneg _))
    _ = (N : ℝ) ^ ((1 : ℝ) / 4) *
        ∑ n ∈ Finset.Icc 1 N,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
      rw [← Finset.mul_sum]
      have hRange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
        ext n
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hRange, Finset.sum_insert (by simp), hvm0]
      simp
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (21 * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (primeMassHalf_nat_le N hN)
        (Real.rpow_nonneg (by positivity) _)
    _ = 21 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow]
      calc
        (N : ℝ) ^ ((1 : ℝ) / 4) *
            (21 * (N : ℝ) ^ ((1 : ℝ) / 2)) =
          21 * ((N : ℝ) ^ ((1 : ℝ) / 4) *
            (N : ℝ) ^ ((1 : ℝ) / 2)) := by ring
        _ = 21 * (N : ℝ) ^ ((1 : ℝ) / 4 + (1 : ℝ) / 2) := by
          rw [Real.rpow_add hNPos]
        _ = 21 * (N : ℝ) ^ ((3 : ℝ) / 4) := by norm_num

/-- Scalar log-height defect formed from a fixed finite prime prefix. -/
def finiteVonMangoldtPrimeLogHeightDefect (N : ℕ) (s : ℂ) : ℝ :=
  2 * (finiteVonMangoldtPrimeFlux N s).re - Real.log s.im

/-- Sharp necessary envelope law: if a finite prefix reaches a scalar defect floor at one
quarter-line point, its absolute coefficient envelope must supply at least the corresponding
half-logarithmic height. -/
theorem half_log_height_le_finiteVonMangoldtPrimeFluxQuarterEnvelope_of_defect_ge
    (N : ℕ) {s : ℂ} (hs : s.re = 1 / 4) {L : ℝ}
    (hfloor : L ≤ finiteVonMangoldtPrimeLogHeightDefect N s) :
    (L + Real.log s.im) / 2 ≤ finiteVonMangoldtPrimeFluxQuarterEnvelope N := by
  have hnorm := norm_finiteVonMangoldtPrimeFlux_le_quarterEnvelope N hs
  have hre : (finiteVonMangoldtPrimeFlux N s).re ≤
      finiteVonMangoldtPrimeFluxQuarterEnvelope N :=
    (Complex.re_le_norm _).trans hnorm
  dsimp [finiteVonMangoldtPrimeLogHeightDefect] at hfloor
  linarith

/-- Explicit depth boundary for every finite-prefix proof attempt.  Reaching a common scalar
defect floor `L` at quarter-line height `t` requires at least logarithmic prefix depth. -/
theorem finiteVonMangoldtPrimePrefix_depth_lower_of_defect_ge
    (N : ℕ) {s : ℂ} (hs : s.re = 1 / 4) {L : ℝ}
    (hfloor : L ≤ finiteVonMangoldtPrimeLogHeightDefect N s) :
    (L + Real.log s.im) / 8 - 1 ≤ (N : ℝ) := by
  have hhalf :=
    half_log_height_le_finiteVonMangoldtPrimeFluxQuarterEnvelope_of_defect_ge
      N hs hfloor
  have hdepth := finiteVonMangoldtPrimeFluxQuarterEnvelope_le_four_mul_depth N
  linarith

/-- Chebyshev-strength necessary depth law.  A finite prefix attaining defect floor `L` at
quarter-line height `t` must have its three-quarter power dominate `(L + log t) / 42`. -/
theorem finiteVonMangoldtPrimePrefix_depth_threeQuarter_lower_of_defect_ge
    (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : s.re = 1 / 4) {L : ℝ}
    (hfloor : L ≤ finiteVonMangoldtPrimeLogHeightDefect N s) :
    (L + Real.log s.im) / 42 ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := by
  have hhalf :=
    half_log_height_le_finiteVonMangoldtPrimeFluxQuarterEnvelope_of_defect_ge
      N hs hfloor
  have henv :=
    finiteVonMangoldtPrimeFluxQuarterEnvelope_le_twentyOne_mul_depth_rpow_threeQuarter N hN
  linarith

/-- No fixed finite von Mangoldt prefix can satisfy the scalar prime-defect endpoint: its defect
falls below every proposed floor at arbitrarily high Gaussian-rational points on `Re s=1/4`. -/
theorem finiteVonMangoldtPrimeLogHeightDefect_cofinally_unboundedBelow
    (N : ℕ) :
    ∀ L : ℝ, ∃ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re ∧
      (gaussianRatPoint q).re < 1 / 2 ∧ 233 / 20 < (gaussianRatPoint q).im ∧
        finiteVonMangoldtPrimeLogHeightDefect N (gaussianRatPoint q) < L := by
  intro L
  let C := finiteVonMangoldtPrimeFluxQuarterEnvelope N
  have hlogTendsto : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop, 2 * C - L < Real.log n :=
    hlogTendsto.eventually_gt_atTop (2 * C - L)
  rw [eventually_atTop] at hevent
  obtain ⟨n₀, hn₀⟩ := hevent
  let n := max n₀ 12
  let q : ℚ × ℚ := (1 / 4, n)
  have hn₀n : n₀ ≤ n := le_max_left _ _
  have hn12 : 12 ≤ n := le_max_right _ _
  have hlog : 2 * C - L < Real.log n := hn₀ n hn₀n
  have hqre : (gaussianRatPoint q).re = 1 / 4 := by
    simp [q, gaussianRatPoint]
  have hqim : (gaussianRatPoint q).im = n := by
    simp [q, gaussianRatPoint]
  have hnorm := norm_finiteVonMangoldtPrimeFlux_le_quarterEnvelope N hqre
  have hre : (finiteVonMangoldtPrimeFlux N (gaussianRatPoint q)).re ≤ C :=
    (Complex.re_le_norm _).trans hnorm
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · rw [hqre]
    norm_num
  · rw [hqre]
    norm_num
  · rw [hqim]
    exact lt_of_lt_of_le (by norm_num : (233 / 20 : ℝ) < 12) (by exact_mod_cast hn12)
  · rw [finiteVonMangoldtPrimeLogHeightDefect, hqim]
    linarith

/-- Height-dependent strengthening of the finite-prefix no-go.  Any eventually positive
truncation schedule whose three-quarter power stays below `log(t) / 84` still has scalar defect
below every real floor beyond every requested height.  Thus a potentially viable schedule must
reach at least the `(log t)^(4/3)` scale. -/
theorem finiteVonMangoldtPrimeLogHeightDefect_slowSchedule_cofinally_unboundedBelow
    (depth : ℕ → ℕ)
    (hpos : ∀ᶠ n : ℕ in atTop, 1 ≤ depth n)
    (hslow : ∀ᶠ n : ℕ in atTop,
      84 * (depth n : ℝ) ^ ((3 : ℝ) / 4) ≤ Real.log n) :
    ∀ (L : ℝ) (U : ℕ), ∃ n : ℕ, 12 ≤ n ∧ U ≤ n ∧
      finiteVonMangoldtPrimeLogHeightDefect (depth n)
        (gaussianRatPoint ((1 / 4, n) : ℚ × ℚ)) < L := by
  intro L U
  have hlogTendsto : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog : ∀ᶠ n : ℕ in atTop, -2 * L < Real.log n :=
    hlogTendsto.eventually_gt_atTop (-2 * L)
  have hn12 : ∀ᶠ n : ℕ in atTop, 12 ≤ n := eventually_ge_atTop 12
  have hnU : ∀ᶠ n : ℕ in atTop, U ≤ n := eventually_ge_atTop U
  have hevent : ∀ᶠ n : ℕ in atTop, 12 ≤ n ∧ U ≤ n ∧
      finiteVonMangoldtPrimeLogHeightDefect (depth n)
        (gaussianRatPoint ((1 / 4, n) : ℚ × ℚ)) < L := by
    filter_upwards [hpos, hslow, hlog, hn12, hnU] with n hnPos hnSlow hnLog hnTwelve hnUpper
    let q : ℚ × ℚ := (1 / 4, n)
    have hqre : (gaussianRatPoint q).re = 1 / 4 := by
      simp [q, gaussianRatPoint]
    have hqim : (gaussianRatPoint q).im = n := by
      simp [q, gaussianRatPoint]
    have hnorm := norm_finiteVonMangoldtPrimeFlux_le_quarterEnvelope
      (depth n) hqre
    have hre : (finiteVonMangoldtPrimeFlux (depth n)
        (gaussianRatPoint q)).re ≤
        finiteVonMangoldtPrimeFluxQuarterEnvelope (depth n) :=
      (Complex.re_le_norm _).trans hnorm
    have henv :=
      finiteVonMangoldtPrimeFluxQuarterEnvelope_le_twentyOne_mul_depth_rpow_threeQuarter
        (depth n) hnPos
    refine ⟨hnTwelve, hnUpper, ?_⟩
    change finiteVonMangoldtPrimeLogHeightDefect (depth n)
        (gaussianRatPoint q) < L
    rw [finiteVonMangoldtPrimeLogHeightDefect, hqim]
    linarith
  exact hevent.exists

end

end RHTower
