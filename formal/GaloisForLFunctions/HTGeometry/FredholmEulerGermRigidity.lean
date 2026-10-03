import GaloisForLFunctions.HTGeometry.FredholmDeterminantTracePowers
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteRankDensity
import GaloisForLFunctions.HTGeometry.TraceOneDensityPurity
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# A Fredholm determinant cannot carry a scalar Euler factor unless the density is pure

For a Hilbert–Schmidt contraction `T`, near the origin
`log det(1 - zT) = -∑_{k ≥ 1} Tr(Tᵏ) zᵏ/k`, while `log(1 - z) = -∑_{k ≥ 1} zᵏ/k`.  If the two
determinants agree as germs, the exponents agree near `0`, and uniqueness of power-series
coefficients forces `Tr(Tᵏ) = 1` for every `k ≥ 1`.  For a positive trace-one density, already
`Tr T² = 1` forces `T = |e⟩⟨e|`: only pure states reproduce the scalar Euler factor.
-/

open Filter Topology Metric
open scoped InnerProductSpace NNReal ENNReal
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## Uniqueness of scalar power-series coefficients -/

theorem hasFPowerSeriesAt_tsum_ofScalars {a : ℕ → ℂ} {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C) :
    HasFPowerSeriesAt (fun z : ℂ => ∑' n, a n * z ^ n)
      (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  set p := FormalMultilinearSeries.ofScalars ℂ a
  have hrad : ((1 / 2 : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    refine p.le_radius_of_bound C fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm]
    calc ‖a n‖ * ((1 / 2 : ℝ≥0) : ℝ) ^ n ≤ ‖a n‖ * 1 := by
          gcongr
          exact pow_le_one₀ (by norm_num) (by norm_num)
      _ ≤ C := by rw [mul_one]; exact ha n
  have hpos : 0 < p.radius := lt_of_lt_of_le (by norm_num) hrad
  have h := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [FormalMultilinearSeries.sum, p, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul]

/-- Two bounded coefficient sequences whose power series agree near `0` are equal. -/
theorem coeff_eq_of_eventually_tsum_eq {a b : ℕ → ℂ} {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C)
    (hb : ∀ n, ‖b n‖ ≤ C)
    (h : ∀ᶠ z in 𝓝 (0 : ℂ), ∑' n, a n * z ^ n = ∑' n, b n * z ^ n) : a = b :=
  FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    ((hasFPowerSeriesAt_tsum_ofScalars ha).eq_formalMultilinearSeries_of_eventually
      (hasFPowerSeriesAt_tsum_ofScalars hb) h)

/-! ## The determinant exponent -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)

/-- The coefficients `Tr(Tᵏ)/k` of `-log det(1 - zT)`. -/
def logDetCoeff (T : H →L[ℂ] H) (k : ℕ) : ℂ := opTrace (T ^ k) / (k : ℂ)

theorem norm_opTrace_pow_le {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (hn : ‖T‖ ≤ 1) (n : ℕ) :
    ‖opTrace (T ^ (n + 2))‖ ≤ hsNorm T ^ 2 := by
  have hpow : ∀ m, IsHilbertSchmidt (T ^ (m + 1)) ∧ hsNorm (T ^ (m + 1)) ≤ hsNorm T := by
    intro m
    induction m with
    | zero =>
      rw [zero_add, pow_one]
      exact ⟨hT, le_rfl⟩
    | succ m ih =>
      have heq : T ^ (m + 1 + 1) = (T ^ (m + 1)) ∘L T := by
        rw [pow_succ]
        rfl
      rw [heq]
      refine ⟨ih.1.comp_right T, (ih.1.hsNorm_comp_right_le T).trans ?_⟩
      calc hsNorm (T ^ (m + 1)) * ‖T‖ ≤ hsNorm T * 1 :=
            mul_le_mul ih.2 hn (norm_nonneg _) (hsNorm_nonneg _)
        _ = hsNorm T := mul_one _
  have heq : T ^ (n + 2) = T ∘L (T ^ (n + 1)) := by
    rw [pow_succ']
    rfl
  rw [heq]
  calc ‖opTrace (T ∘L (T ^ (n + 1)))‖ ≤ hsNorm T * hsNorm (T ^ (n + 1)) :=
        norm_opTrace_comp_le hT (hpow n).1
    _ ≤ hsNorm T * hsNorm T := mul_le_mul_of_nonneg_left (hpow n).2 (hsNorm_nonneg _)
    _ = hsNorm T ^ 2 := (sq _).symm

theorem norm_logDetCoeff_le {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (hn : ‖T‖ ≤ 1) (k : ℕ) :
    ‖logDetCoeff T k‖ ≤ ‖opTrace T‖ + hsNorm T ^ 2 := by
  rw [logDetCoeff]
  rcases k with _ | _ | n
  · rw [Nat.cast_zero, div_zero, norm_zero]
    positivity
  · show ‖opTrace (T ^ (0 + 1)) / ((0 + 1 : ℕ) : ℂ)‖ ≤ _
    rw [zero_add, pow_one, Nat.cast_one, div_one]
    exact le_add_of_nonneg_right (sq_nonneg (hsNorm T))
  · rw [norm_div]
    have hk : (1 : ℝ) ≤ ‖((n + 2 : ℕ) : ℂ)‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast (by omega : 1 ≤ n + 2)
    calc ‖opTrace (T ^ (n + 2))‖ / ‖((n + 2 : ℕ) : ℂ)‖ ≤ ‖opTrace (T ^ (n + 2))‖ :=
          div_le_self (norm_nonneg _) hk
      _ ≤ hsNorm T ^ 2 := norm_opTrace_pow_le hT hn n
      _ ≤ ‖opTrace T‖ + hsNorm T ^ 2 := le_add_of_nonneg_left (norm_nonneg _)

/-- `traceExponent T z + z Tr T = ∑ₖ (Tr Tᵏ/k) zᵏ` for `‖z‖ < 1`. -/
theorem traceExponent_add_eq_tsum {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (hn : ‖T‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    traceExponent T z + z * opTrace T = ∑' k, logDetCoeff T k * z ^ k := by
  have hsum : Summable fun k => logDetCoeff T k * z ^ k := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖opTrace T‖ + hsNorm T ^ 2))
      fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (norm_logDetCoeff_le hT hn k) (by positivity)
  have hsum1 : Summable fun k => logDetCoeff T (k + 1) * z ^ (k + 1) :=
    (summable_nat_add_iff 1).2 hsum
  rw [hsum.tsum_eq_zero_add, hsum1.tsum_eq_zero_add]
  simp only [logDetCoeff, zero_add, pow_zero, Nat.cast_zero, div_zero, zero_mul, pow_one,
    Nat.cast_one, div_one]
  rw [traceExponent]
  have hfun : (fun n : ℕ => opTrace (T ^ (n + 1 + 1)) / ((n + 1 + 1 : ℕ) : ℂ) * z ^ (n + 1 + 1)) =
      fun n : ℕ => z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * opTrace (T ^ (n + 2)) := by
    funext n
    ring
  simp only [hfun]
  ring

/-- **Germ rigidity.**  If `det(1 - zT) = 1 - z` near `0` for a Hilbert–Schmidt contraction,
then `Tr(Tᵏ) = 1` for every `k ≥ 1`. -/
theorem opTrace_pow_eq_one_of_detOneSub_eq_euler {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    (hn : ‖T‖ ≤ 1) (h : ∀ᶠ z in 𝓝 (0 : ℂ), detOneSub b T z = 1 - z) :
    ∀ k, 1 ≤ k → opTrace (T ^ k) = 1 := by
  obtain ⟨r, hr, hexp⟩ := exists_detOneSub_eq_exp b hT
  set A : ℂ → ℂ := fun z => traceExponent T z + z * opTrace T
  set B : ℂ → ℂ := fun z => -Complex.log (1 - z)
  -- `A` and `B` are continuous at `0` and vanish there
  have hAeq : ∀ᶠ z in 𝓝 (0 : ℂ), A z = ∑' k, logDetCoeff T k * z ^ k :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) fun z hz =>
      traceExponent_add_eq_tsum hT hn (by simpa using hz)
  have hBeq : ∀ᶠ z in 𝓝 (0 : ℂ), B z = ∑' k : ℕ, (1 / (k : ℂ)) * z ^ k :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) fun z hz => by
      have := (Complex.hasSum_taylorSeries_neg_log (z := z) (by simpa using hz)).tsum_eq
      simp only [B]
      rw [← this]
      exact tsum_congr fun k => by ring
  have hAcont : ContinuousAt A 0 := by
    have hcoeffs := hasFPowerSeriesAt_tsum_ofScalars (C := ‖opTrace T‖ + hsNorm T ^ 2)
      (norm_logDetCoeff_le hT hn)
    exact (hcoeffs.continuousAt).congr (hAeq.mono fun z hz => hz.symm)
  have hBcont : ContinuousAt B 0 := by
    refine (continuous_neg.continuousAt).comp (continuousAt_clog ?_ |>.comp
      (continuous_const.sub continuous_id).continuousAt)
    simp
  have hA0 : A 0 = 0 := by simp [A, traceExponent]
  have hB0 : B 0 = 0 := by simp [B]
  -- exponentials agree near `0`
  have hexpeq : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (-A z) = Complex.exp (-B z) := by
    filter_upwards [h, isOpen_ball.mem_nhds (mem_ball_self hr),
      isOpen_ball.mem_nhds (mem_ball_self one_pos)] with z hz hzr hz1
    have hne : (1 : ℂ) - z ≠ 0 := by
      intro h0
      have : z = 1 := by linear_combination -h0
      rw [this, mem_ball, dist_zero_right, norm_one] at hz1
      exact lt_irrefl _ hz1
    rw [show -A z = -(traceExponent T z) - z * opTrace T by simp only [A]; ring, ← hexp z hzr, hz,
      show -B z = Complex.log (1 - z) by simp [B], Complex.exp_log hne]
  -- hence the exponents agree near `0`
  have hdiff : ContinuousAt (fun z => A z - B z) 0 := hAcont.sub hBcont
  have hsmall : ∀ᶠ z in 𝓝 (0 : ℂ), ‖A z - B z‖ < 2 * Real.pi := by
    have := hdiff.eventually (Metric.ball_mem_nhds (A 0 - B 0) (by positivity : (0 : ℝ) < 2 * Real.pi))
    filter_upwards [this] with z hz
    rw [hA0, hB0, sub_zero, dist_zero_right] at hz
    exact hz
  have hAB : ∀ᶠ z in 𝓝 (0 : ℂ), A z = B z := by
    filter_upwards [hexpeq, hsmall] with z hz hzs
    have h1 : Complex.exp (B z - A z) = 1 := by
      have hq : Complex.exp (B z - A z) = Complex.exp (-A z) / Complex.exp (-B z) := by
        rw [← Complex.exp_sub]
        ring_nf
      rw [hq, hz, div_self (Complex.exp_ne_zero _)]
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h1
    have hm0 : m = 0 := by
      by_contra hm0
      have hnorm : ‖B z - A z‖ = |(m : ℝ)| * (2 * Real.pi) := by
        rw [hm, norm_mul, norm_mul, Complex.norm_intCast, norm_mul, Complex.norm_ofNat,
          Complex.norm_real, Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le]
        ring
      have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hm0
      have : 2 * Real.pi ≤ ‖A z - B z‖ := by
        rw [norm_sub_rev, hnorm]
        nlinarith [Real.pi_pos]
      linarith
    rw [hm0, Int.cast_zero, zero_mul, sub_eq_zero] at hm
    exact hm.symm
  -- compare coefficients
  have hcoeff := coeff_eq_of_eventually_tsum_eq (C := ‖opTrace T‖ + hsNorm T ^ 2 + 1)
    (fun k => (norm_logDetCoeff_le hT hn k).trans (le_add_of_nonneg_right zero_le_one))
    (fun k => by
      have : ‖(1 : ℂ) / (k : ℂ)‖ ≤ 1 := by
        rcases k with _ | k
        · simp
        · rw [norm_div, norm_one, Complex.norm_natCast]
          exact (div_le_one (by positivity)).2 (by exact_mod_cast Nat.succ_pos k)
      exact this.trans (by
        have := hsNorm_nonneg T
        nlinarith [norm_nonneg (opTrace T)]))
    (by filter_upwards [hAeq, hBeq, hAB] with z h1 h2 h3; rw [← h1, ← h2, h3])
  intro k hk
  have hk' := congrFun hcoeff k
  rw [logDetCoeff] at hk'
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  field_simp at hk'
  exact hk'

/-- **Only pure states carry the scalar Euler factor.**  A positive trace-one density whose
Fredholm determinant germ is `1 - z` is a pure state `|e⟩⟨e|`. -/
theorem exists_eq_rankOne_of_detOneSub_eq_euler {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hS : MemSchattenClass 1 T) (htr : opTrace T = 1)
    (h : ∀ᶠ z in 𝓝 (0 : ℂ), detOneSub b T z = 1 - z) :
    ∃ e : H, ‖e‖ = 1 ∧ T = rankOne ℂ e e := by
  have hHS : IsHilbertSchmidt T := by
    obtain ⟨A, B, hA, -, hfac⟩ := hS.one_isTraceClass
    rw [hfac]
    exact hA.comp_right B
  have hn := norm_le_one_of_opTrace_eq_one hT hS htr
  have h2 := opTrace_pow_eq_one_of_detOneSub_eq_euler b hHS hn h 2 (by norm_num)
  rw [sq, ContinuousLinearMap.mul_def] at h2
  exact exists_eq_rankOne_of_opTrace_sq_eq_one hT hS htr h2

end GaloisForLFunctions.HTGeometry
