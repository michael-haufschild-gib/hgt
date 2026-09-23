import GaloisForLFunctions.RHTower.HardyDyadicPhaseTests
import GaloisForLFunctions.RHTower.HardyTwistCellCombination
import GaloisForLFunctions.RHTower.SmoothAFECutoffSum
import GaloisForLFunctions.RHTower.HardyZSmoothAFEReal
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualContourLimit
import GaloisForLFunctions.RHTower.SmoothAFEZetaPoleDecay

/-!
# The mean of Hardy's `Z` over a dyadic window

The exact Gaussian smooth approximate functional equation writes `Z` as a direct Dirichlet edge
with constant weights, a reflected edge whose weights carry the whole height dependence, and a
pole residue.  On `[T, 2T]` with smoothing scale `x = T\sqrt T`:

* the reflected edge is `O((1+\tau)/x)` termwise, so its window integral is `O(\sqrt T)`;
* the residue is `O(\sqrt x\,e^{-\tau^(2 : ℕ)})`, hence bounded;
* the direct edge splits at `n \approx 5\sqrt T`.  Below that the second-derivative test gives
  `O(\sqrt T)` per term, and the head weight sum is `O(T^{1/4})`; above it the phase velocity is
  bounded away from zero and the first-derivative test gives `O(1)` per term against a total
  weight `O(\sqrt x)`.

Both halves are `O(T^{3/4})`, so `\int_T^{2T} Z = O(T^{3/4})`.
-/

open Set MeasureTheory Complex Finset

namespace RHTower

noncomputable section

/-- The `n`-th term of the direct edge of the real Gaussian smooth AFE for Hardy's `Z`. -/
def hardyDirectTerm (x : ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  (Real.sqrt ((n : ℝ) + 1))⁻¹ *
    (Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
        (smoothAFECutoff (((n : ℝ) + 1) / x)).re -
      Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
        (smoothAFECutoff (((n : ℝ) + 1) / x)).im)

/-- The `n`-th term of the reflected edge. -/
def hardyDualTerm (x : ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  (Real.sqrt ((n : ℝ) + 1))⁻¹ *
    (Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
        (smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)).re +
      Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
        (smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)).im)

theorem hardyZ_eq_direct_add_dual_sub_residue {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    hardyZ τ = (∑' n : ℕ, hardyDirectTerm x n τ) + (∑' n : ℕ, hardyDualTerm x n τ)
      - (Complex.exp (Complex.I * (gammaHardyTheta τ : ℂ)) *
          smoothAFEZetaShiftedPoleResidue (linePt τ) x).re :=
  hardyZ_eq_two_tsum_smoothAFE_real hx τ

theorem re_mul_exp_I_ofReal (c : ℂ) (θ : ℝ) :
    (c * Complex.exp (Complex.I * (θ : ℂ))).re
      = Real.cos θ * c.re - Real.sin θ * c.im := by
  rw [mul_comm Complex.I _, Complex.exp_mul_I]
  simp [Complex.mul_re, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem hardyDirectTerm_eq (x : ℝ) (n : ℕ) (τ : ℝ) :
    hardyDirectTerm x n τ = (Real.sqrt ((n : ℝ) + 1))⁻¹ *
      (smoothAFECutoff (((n : ℝ) + 1) / x) *
        Complex.exp (Complex.I *
          ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))).re := by
  rw [hardyDirectTerm, re_mul_exp_I_ofReal]

theorem continuous_hardyDirectTerm (x : ℝ) (n : ℕ) : Continuous (hardyDirectTerm x n) := by
  unfold hardyDirectTerm
  exact continuous_const.mul
    (((Real.continuous_cos.comp (continuous_hardyTwistPhase _)).mul continuous_const).sub
      ((Real.continuous_sin.comp (continuous_hardyTwistPhase _)).mul continuous_const))

theorem abs_hardyDirectTerm_le (x : ℝ) (n : ℕ) (τ : ℝ) :
    |hardyDirectTerm x n τ| ≤ cutoffWeight x n := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ := by positivity
  rw [hardyDirectTerm_eq, abs_mul, abs_of_nonneg hs, cutoffWeight]
  refine mul_le_mul_of_nonneg_left ?_ hs
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [norm_mul, Complex.norm_exp]
  simp

/-! ## The window integral of a single direct term -/

theorem intervalIntegrable_directPhase (x : ℝ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => smoothAFECutoff (((n : ℝ) + 1) / x) *
      Complex.exp (Complex.I *
        ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))) volume a b := by
  refine (Continuous.intervalIntegrable ?_ a b)
  exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_hardyTwistPhase _))))

theorem integral_hardyDirectTerm_eq (x : ℝ) (n : ℕ) (a b : ℝ) :
    ∫ τ in a..b, hardyDirectTerm x n τ
      = (Real.sqrt ((n : ℝ) + 1))⁻¹ *
        (∫ τ in a..b, smoothAFECutoff (((n : ℝ) + 1) / x) *
          Complex.exp (Complex.I *
            ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))).re := by
  simp_rw [hardyDirectTerm_eq]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact Complex.reCLM.intervalIntegral_comp_comm (intervalIntegrable_directPhase x n a b)

theorem abs_integral_hardyDirectTerm_le_second {T : ℝ} (hT : 4 ≤ T) (x : ℝ) (n : ℕ) :
    |∫ τ in T..(2 * T), hardyDirectTerm x n τ|
      ≤ 64 * Real.sqrt (200 * T) * cutoffWeight x n := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ := by positivity
  rw [integral_hardyDirectTerm_eq, abs_mul, abs_of_nonneg hs]
  have hre := Complex.abs_re_le_norm (∫ τ in T..(2 * T),
    smoothAFECutoff (((n : ℝ) + 1) / x) *
      Complex.exp (Complex.I *
        ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ)))
  have hosc := norm_integral_twist_second_le hT (Real.log ((n : ℝ) + 1))
    (smoothAFECutoff (((n : ℝ) + 1) / x))
  have hchain := le_trans hre hosc
  calc (Real.sqrt ((n : ℝ) + 1))⁻¹ * |(∫ τ in T..(2 * T),
        smoothAFECutoff (((n : ℝ) + 1) / x) *
          Complex.exp (Complex.I *
            ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))).re|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
          (64 * ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖ * Real.sqrt (200 * T)) :=
        mul_le_mul_of_nonneg_left hchain hs
    _ = 64 * Real.sqrt (200 * T) * cutoffWeight x n := by
        unfold cutoffWeight; ring

theorem abs_integral_hardyDirectTerm_le_first {T : ℝ} (hT : 16 ≤ T) (x : ℝ) (n : ℕ)
    (hn : Real.log (5 * Real.sqrt T) ≤ Real.log ((n : ℝ) + 1)) :
    |∫ τ in T..(2 * T), hardyDirectTerm x n τ| ≤ 8 * cutoffWeight x n := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ := by positivity
  rw [integral_hardyDirectTerm_eq, abs_mul, abs_of_nonneg hs]
  have hre := Complex.abs_re_le_norm (∫ τ in T..(2 * T),
    smoothAFECutoff (((n : ℝ) + 1) / x) *
      Complex.exp (Complex.I *
        ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ)))
  have hosc := norm_integral_twist_first_le hT hn
    (smoothAFECutoff (((n : ℝ) + 1) / x))
  have hchain := le_trans hre hosc
  calc (Real.sqrt ((n : ℝ) + 1))⁻¹ * |(∫ τ in T..(2 * T),
        smoothAFECutoff (((n : ℝ) + 1) / x) *
          Complex.exp (Complex.I *
            ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))).re|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
          (8 * ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖) :=
        mul_le_mul_of_nonneg_left hchain hs
    _ = 8 * cutoffWeight x n := by
        unfold cutoffWeight; ring

/-! ## The direct edge as a whole -/

theorem setIntegral_norm_hardyDirectTerm_le {T : ℝ} (hT : 0 ≤ T) (x : ℝ) (n : ℕ) :
    (∫ τ in Ioc T (2 * T), ‖hardyDirectTerm x n τ‖) ≤ cutoffWeight x n * T := by
  have hTle : T ≤ 2 * T := by linarith
  have hb : (∫ τ in Ioc T (2 * T), ‖hardyDirectTerm x n τ‖)
      ≤ ∫ _ in Ioc T (2 * T), cutoffWeight x n := by
    refine setIntegral_mono_on
      ((continuous_hardyDirectTerm x n).integrableOn_Ioc.norm)
      (continuous_const.integrableOn_Ioc) measurableSet_Ioc (fun τ _ => ?_)
    rw [Real.norm_eq_abs]
    exact abs_hardyDirectTerm_le x n τ
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hTle, smul_eq_mul] at hb
  calc (∫ τ in Ioc T (2 * T), ‖hardyDirectTerm x n τ‖)
      ≤ (2 * T - T) * cutoffWeight x n := hb
    _ = cutoffWeight x n * T := by ring

theorem integral_hardyDirectSeries_eq {T : ℝ} (hT : 0 ≤ T) {x : ℝ} (hx : 1 ≤ x) :
    ∫ τ in T..(2 * T), (∑' n : ℕ, hardyDirectTerm x n τ)
      = ∑' n : ℕ, ∫ τ in T..(2 * T), hardyDirectTerm x n τ := by
  obtain ⟨C, hC, hmain⟩ := exists_summable_tsum_cutoffWeight_le
  obtain ⟨hsumm, hle⟩ := hmain hx
  have hTle : T ≤ 2 * T := by linarith
  have hint : ∀ n : ℕ, Integrable (hardyDirectTerm x n) (volume.restrict (Ioc T (2 * T))) :=
    fun n => (continuous_hardyDirectTerm x n).integrableOn_Ioc
  have hnorm : Summable (fun n : ℕ =>
      ∫ τ in Ioc T (2 * T), ‖hardyDirectTerm x n τ‖) := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => setIntegral_norm_hardyDirectTerm_le hT x n) (hsumm.mul_right T)
  have hs := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioc T (2 * T))) hint hnorm
  rw [intervalIntegral.integral_of_le hTle]
  simp_rw [intervalIntegral.integral_of_le hTle]
  exact hs.tsum_eq.symm

theorem exists_abs_integral_hardyDirectSeries_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T x : ℝ}, 16 ≤ T → 1 ≤ x →
      |∫ τ in T..(2 * T), (∑' n : ℕ, hardyDirectTerm x n τ)|
        ≤ C * (Real.sqrt T * Real.sqrt (Real.sqrt T) + Real.sqrt x) := by
  obtain ⟨Ct, hCt, hmain⟩ := exists_summable_tsum_cutoffWeight_le
  obtain ⟨Ch, hCh, hhead⟩ := exists_sum_range_cutoffWeight_le
  refine ⟨max (64 * Ch * Real.sqrt 200 * Real.sqrt 6) (8 * Ct), ?_, ?_⟩
  · exact le_trans (by positivity) (le_max_right _ _)
  intro T x hT hx
  have hT0 : (0 : ℝ) < T := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨hsumm, hle⟩ := hmain hx
  set M : ℕ := ⌈5 * Real.sqrt T⌉₊ with hMdef
  have hsT : Real.sqrt T ≥ 4 := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt hT
  have hMge : 5 * Real.sqrt T ≤ (M : ℝ) := Nat.le_ceil _
  have hMlt : (M : ℝ) < 5 * Real.sqrt T + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMle : (M : ℝ) ≤ 6 * Real.sqrt T := by linarith
  -- per-term bounds
  have hsecond : ∀ n : ℕ, |∫ τ in T..(2 * T), hardyDirectTerm x n τ|
      ≤ 64 * Real.sqrt (200 * T) * cutoffWeight x n :=
    fun n => abs_integral_hardyDirectTerm_le_second (by linarith) x n
  have hfirst : ∀ n : ℕ, |∫ τ in T..(2 * T), hardyDirectTerm x (n + M) τ|
      ≤ 8 * cutoffWeight x (n + M) := by
    intro n
    refine abs_integral_hardyDirectTerm_le_first hT x (n + M) ?_
    refine Real.log_le_log (by positivity) ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : ((n + M : ℕ) : ℝ) + 1 = (n : ℝ) + (M : ℝ) + 1 := by push_cast; ring
    rw [this]
    linarith
  -- summability of the term integrals
  have habs : Summable (fun n : ℕ => |∫ τ in T..(2 * T), hardyDirectTerm x n τ|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) hsecond ?_
    exact hsumm.mul_left (64 * Real.sqrt (200 * T))
  have hshift : Summable (fun n : ℕ => |∫ τ in T..(2 * T), hardyDirectTerm x (n + M) τ|) :=
    (summable_nat_add_iff M).mpr habs
  -- the split
  have hsplit := habs.sum_add_tsum_nat_add M
  have hheadbd : ∑ n ∈ range M, |∫ τ in T..(2 * T), hardyDirectTerm x n τ|
      ≤ 64 * Real.sqrt (200 * T) * (Ch * Real.sqrt (M : ℝ)) := by
    refine le_trans (Finset.sum_le_sum (fun n _ => hsecond n)) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hhead hx0 M) (by positivity)
  have htailbd : ∑' n : ℕ, |∫ τ in T..(2 * T), hardyDirectTerm x (n + M) τ|
      ≤ 8 * (Ct * Real.sqrt x) := by
    refine le_trans (hshift.tsum_le_tsum hfirst
      (((summable_nat_add_iff M).mpr hsumm).mul_left 8)) ?_
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact le_trans (tsum_cutoffWeight_shift_le hx M) hle
  -- combine
  have hsq200 : Real.sqrt (200 * T) = Real.sqrt 200 * Real.sqrt T :=
    Real.sqrt_mul (by norm_num) T
  have hsqM : Real.sqrt (M : ℝ) ≤ Real.sqrt 6 * Real.sqrt (Real.sqrt T) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6)]
    exact Real.sqrt_le_sqrt hMle
  have hstep1 : 64 * Real.sqrt (200 * T) * (Ch * Real.sqrt (M : ℝ))
      ≤ 64 * Ch * Real.sqrt 200 * Real.sqrt 6 * (Real.sqrt T * Real.sqrt (Real.sqrt T)) := by
    rw [hsq200]
    have hbase : (0 : ℝ) ≤ 64 * (Real.sqrt 200 * Real.sqrt T) := by positivity
    have hinner : Ch * Real.sqrt (M : ℝ) ≤ Ch * (Real.sqrt 6 * Real.sqrt (Real.sqrt T)) :=
      mul_le_mul_of_nonneg_left hsqM hCh
    calc 64 * (Real.sqrt 200 * Real.sqrt T) * (Ch * Real.sqrt (M : ℝ))
        ≤ 64 * (Real.sqrt 200 * Real.sqrt T) *
            (Ch * (Real.sqrt 6 * Real.sqrt (Real.sqrt T))) :=
          mul_le_mul_of_nonneg_left hinner hbase
      _ = 64 * Ch * Real.sqrt 200 * Real.sqrt 6 *
            (Real.sqrt T * Real.sqrt (Real.sqrt T)) := by ring
  have hfinal : |∫ τ in T..(2 * T), (∑' n : ℕ, hardyDirectTerm x n τ)|
      ≤ ∑' n : ℕ, |∫ τ in T..(2 * T), hardyDirectTerm x n τ| := by
    rw [integral_hardyDirectSeries_eq hT0.le hx]
    have := norm_tsum_le_tsum_norm (f := fun n : ℕ => ∫ τ in T..(2 * T), hardyDirectTerm x n τ)
      (by simpa [Real.norm_eq_abs] using habs)
    simpa [Real.norm_eq_abs] using this
  have hAnn : (0 : ℝ) ≤ Real.sqrt T * Real.sqrt (Real.sqrt T) := by positivity
  have hBnn : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h1 : 64 * Ch * Real.sqrt 200 * Real.sqrt 6
      ≤ max (64 * Ch * Real.sqrt 200 * Real.sqrt 6) (8 * Ct) := le_max_left _ _
  have h2 : 8 * Ct ≤ max (64 * Ch * Real.sqrt 200 * Real.sqrt 6) (8 * Ct) := le_max_right _ _
  calc |∫ τ in T..(2 * T), (∑' n : ℕ, hardyDirectTerm x n τ)|
      ≤ ∑' n : ℕ, |∫ τ in T..(2 * T), hardyDirectTerm x n τ| := hfinal
    _ = ∑ n ∈ range M, |∫ τ in T..(2 * T), hardyDirectTerm x n τ|
          + ∑' n : ℕ, |∫ τ in T..(2 * T), hardyDirectTerm x (n + M) τ| := hsplit.symm
    _ ≤ 64 * Ch * Real.sqrt 200 * Real.sqrt 6 * (Real.sqrt T * Real.sqrt (Real.sqrt T))
          + 8 * Ct * Real.sqrt x := by
        have := htailbd
        nlinarith [hheadbd, hstep1]
    _ ≤ max (64 * Ch * Real.sqrt 200 * Real.sqrt 6) (8 * Ct) *
          (Real.sqrt T * Real.sqrt (Real.sqrt T) + Real.sqrt x) := by
        nlinarith [h1, h2, hAnn, hBnn]

/-! ## The reflected edge and the residue -/

theorem re_mul_exp_neg_I_ofReal (c : ℂ) (θ : ℝ) :
    (c * Complex.exp (Complex.I * ((-θ : ℝ) : ℂ))).re
      = Real.cos θ * c.re + Real.sin θ * c.im := by
  rw [re_mul_exp_I_ofReal]
  rw [Real.cos_neg, Real.sin_neg]
  ring

theorem hardyDualTerm_eq (x : ℝ) (n : ℕ) (τ : ℝ) :
    hardyDualTerm x n τ = (Real.sqrt ((n : ℝ) + 1))⁻¹ *
      (smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x) *
        Complex.exp (Complex.I *
          ((-hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))).re := by
  rw [hardyDualTerm, re_mul_exp_neg_I_ofReal]

theorem abs_hardyDualTerm_le (x : ℝ) (n : ℕ) (τ : ℝ) :
    |hardyDualTerm x n τ|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ * ‖smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)‖ := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ := by positivity
  rw [hardyDualTerm_eq, abs_mul, abs_of_nonneg hs]
  refine mul_le_mul_of_nonneg_left ?_ hs
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [norm_mul, Complex.norm_exp]
  simp

theorem exists_abs_tsum_hardyDualTerm_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {x : ℝ}, 0 < x → ∀ τ : ℝ,
      |∑' n : ℕ, hardyDualTerm x n τ| ≤ 3 * K * (1 + |τ|) / x := by
  obtain ⟨K, hK, hbound⟩ := exists_norm_smoothAFEZetaDualWeight_le_inv
  refine ⟨K, hK, fun {x} hx τ => ?_⟩
  have hterm : ∀ n : ℕ, |hardyDualTerm x n τ|
      ≤ (K * (1 + |τ|) / x) * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hY : (0 : ℝ) < ((n : ℝ) + 1) * x := by positivity
    have hb := hbound τ hY
    have hs : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ := by positivity
    refine le_trans (abs_hardyDualTerm_le x n τ) ?_
    calc (Real.sqrt ((n : ℝ) + 1))⁻¹ * ‖smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)‖
        ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ * (K * (1 + |τ|) * (((n : ℝ) + 1) * x)⁻¹) :=
          mul_le_mul_of_nonneg_left hb hs
      _ = (K * (1 + |τ|) / x) * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ := by
          have hnp : ((n : ℝ) + 1) ≠ 0 := by positivity
          have hsp : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
          field_simp
  have hmaj : Summable (fun n : ℕ =>
      (K * (1 + |τ|) / x) * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹) :=
    summable_inv_sqrt_cube.mul_left _
  have habs : Summable (fun n : ℕ => |hardyDualTerm x n τ|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hterm hmaj
  have hstep : |∑' n : ℕ, hardyDualTerm x n τ| ≤ ∑' n : ℕ, |hardyDualTerm x n τ| := by
    have := norm_tsum_le_tsum_norm (f := fun n : ℕ => hardyDualTerm x n τ)
      (by simpa [Real.norm_eq_abs] using habs)
    simpa [Real.norm_eq_abs] using this
  refine le_trans hstep (le_trans (habs.tsum_le_tsum hterm hmaj) ?_)
  rw [tsum_mul_left]
  have hcoef : (0 : ℝ) ≤ K * (1 + |τ|) / x := by
    have : (0 : ℝ) ≤ 1 + |τ| := by positivity
    positivity
  calc (K * (1 + |τ|) / x) * ∑' n : ℕ, (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹
      ≤ (K * (1 + |τ|) / x) * 3 := mul_le_mul_of_nonneg_left tsum_inv_sqrt_cube_le hcoef
    _ = 3 * K * (1 + |τ|) / x := by ring

theorem abs_hardyResidue_le {x τ : ℝ} (hx : 0 < x) (hτ : 1 ≤ |τ|) :
    |(Complex.exp (Complex.I * (gammaHardyTheta τ : ℂ)) *
        smoothAFEZetaShiftedPoleResidue (linePt τ) x).re|
      ≤ Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(τ ^ (2 : ℕ))) := by
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, sub_zero, Real.exp_zero, one_mul,
    mul_zero]
  simpa using norm_smoothAFEZetaShiftedPoleResidue_line_le hx hτ

theorem continuous_hardyDirectSeries {x : ℝ} (hx : 1 ≤ x) :
    Continuous (fun τ : ℝ => ∑' n : ℕ, hardyDirectTerm x n τ) := by
  obtain ⟨C, hC, hmain⟩ := exists_summable_tsum_cutoffWeight_le
  obtain ⟨hsumm, _⟩ := hmain hx
  refine continuous_tsum (continuous_hardyDirectTerm x) hsumm (fun n τ => ?_)
  rw [Real.norm_eq_abs]
  exact abs_hardyDirectTerm_le x n τ

/-- Pointwise size of the two edges the direct Dirichlet series does not carry. -/
theorem exists_abs_hardyZ_sub_direct_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {x : ℝ}, 0 < x → ∀ {τ : ℝ}, 1 ≤ τ →
      |hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ|
        ≤ 3 * K * (1 + τ) / x + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(τ ^ (2 : ℕ))) := by
  obtain ⟨K, hK, hdual⟩ := exists_abs_tsum_hardyDualTerm_le
  refine ⟨K, hK, fun {x} hx {τ} hτ => ?_⟩
  have habs : |τ| = τ := abs_of_nonneg (by linarith)
  have hτ1 : (1 : ℝ) ≤ |τ| := by rw [habs]; exact hτ
  have hsplit := hardyZ_eq_direct_add_dual_sub_residue hx τ
  have heq : hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ
      = (∑' n : ℕ, hardyDualTerm x n τ)
        - (Complex.exp (Complex.I * (gammaHardyTheta τ : ℂ)) *
            smoothAFEZetaShiftedPoleResidue (linePt τ) x).re := by
    rw [hsplit]; ring
  rw [heq]
  refine le_trans (abs_sub _ _) ?_
  have h1 := hdual hx τ
  rw [habs] at h1
  have h2 := abs_hardyResidue_le hx hτ1
  linarith

/-- **The mean of Hardy's `Z` over a dyadic window is `O(T^{3/4})`.** -/
theorem exists_abs_integral_hardyZ_dyadic_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ}, 16 ≤ T →
      |∫ τ in T..(2 * T), hardyZ τ| ≤ C * (Real.sqrt T * Real.sqrt (Real.sqrt T)) := by
  obtain ⟨CD, hCD, hdirect⟩ := exists_abs_integral_hardyDirectSeries_le
  obtain ⟨K, hK, htail⟩ := exists_abs_hardyZ_sub_direct_le
  refine ⟨2 * CD + 9 * K + 2, by positivity, fun {T} hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  set s : ℝ := Real.sqrt T with hs
  have hs2 : s * s = T := Real.mul_self_sqrt hT0.le
  have hs4 : (4 : ℝ) ≤ s := by
    rw [hs, show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt hT
  have hs0 : (0 : ℝ) < s := by linarith
  set x : ℝ := T * s with hx
  have hx1 : (1 : ℝ) ≤ x := by nlinarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hsqx : Real.sqrt x = s * Real.sqrt s := by
    rw [hx, Real.sqrt_mul hT0.le, ← hs]
  have hss : Real.sqrt s ≤ s := by
    nlinarith [Real.sq_sqrt hs0.le, Real.sqrt_nonneg s, sq_nonneg (Real.sqrt s - 1)]
  have hsqs1 : (1 : ℝ) ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  -- the two pieces
  have hTle : T ≤ 2 * T := by linarith
  have hZint : IntervalIntegrable hardyZ volume T (2 * T) :=
    continuous_hardyZ.intervalIntegrable _ _
  have hDint : IntervalIntegrable (fun τ : ℝ => ∑' n : ℕ, hardyDirectTerm x n τ)
      volume T (2 * T) := (continuous_hardyDirectSeries hx1).intervalIntegrable _ _
  have hdecomp : (∫ τ in T..(2 * T), hardyZ τ)
      = (∫ τ in T..(2 * T), (∑' n : ℕ, hardyDirectTerm x n τ))
        + ∫ τ in T..(2 * T), (hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ) := by
    rw [intervalIntegral.integral_sub hZint hDint]
    ring
  -- the tail integral
  have hconst : ∀ τ ∈ Set.uIoc T (2 * T),
      ‖hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ‖
        ≤ 9 * K / s + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) := by
    intro τ hτ
    rw [Set.uIoc_of_le hTle] at hτ
    have hτ1 : (1 : ℝ) ≤ τ := by linarith [hτ.1]
    have hb := htail hx0 hτ1
    rw [Real.norm_eq_abs]
    refine le_trans hb (add_le_add ?_ ?_)
    · have hnum : 3 * K * (1 + τ) ≤ 9 * K * T := by nlinarith [hτ.2, hK]
      rw [div_le_div_iff₀ hx0 hs0]
      nlinarith [hK, hs0.le]
    · have hexp : Real.exp (-(τ ^ (2 : ℕ))) ≤ Real.exp (-(T ^ (2 : ℕ))) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hτ.1]
      have hcoef : (0 : ℝ) ≤ Real.sqrt x * Real.exp (1 / 4) := by positivity
      exact mul_le_mul_of_nonneg_left hexp hcoef
  have htailint := intervalIntegral.norm_integral_le_of_norm_le_const hconst
  rw [Real.norm_eq_abs, show |2 * T - T| = T by rw [show 2 * T - T = T by ring,
    abs_of_nonneg hT0.le]] at htailint
  -- the exponential piece is bounded
  have hexpbd : Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) * T ≤ 2 := by
    have h1 : Real.sqrt x ≤ T := by
      rw [hsqx]; nlinarith
    have h2 : Real.exp (1 / 4) ≤ 2 := by
      have hlog : Real.exp (1 / 4) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
      rwa [Real.exp_log (by norm_num)] at hlog
    have h3 : T ^ (2 : ℕ) * Real.exp (-(T ^ (2 : ℕ))) ≤ 1 := by
      have hle : T ^ (2 : ℕ) ≤ Real.exp (T ^ (2 : ℕ)) := by
        have := Real.add_one_le_exp (T ^ (2 : ℕ))
        linarith
      have hpos : (0 : ℝ) < Real.exp (T ^ (2 : ℕ)) := Real.exp_pos _
      rw [Real.exp_neg, mul_inv_le_iff₀ hpos]
      linarith
    have hexppos : (0 : ℝ) < Real.exp (-(T ^ (2 : ℕ))) := Real.exp_pos _
    have hstep : Real.sqrt x * Real.exp (1 / 4) ≤ T * 2 := by
      nlinarith [Real.sqrt_nonneg x, Real.exp_pos (1 / 4 : ℝ), hT0.le]
    calc Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) * T
        ≤ T * 2 * Real.exp (-(T ^ (2 : ℕ))) * T :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hstep hexppos.le) hT0.le
      _ = 2 * (T ^ (2 : ℕ) * Real.exp (-(T ^ (2 : ℕ)))) := by ring
      _ ≤ 2 * 1 := by nlinarith
      _ = 2 := by ring
  have hdirbd := hdirect hT hx1
  rw [hsqx] at hdirbd
  -- combine
  have hsplitbd : |∫ τ in T..(2 * T), hardyZ τ|
      ≤ CD * (s * Real.sqrt s + s * Real.sqrt s)
        + (9 * K / s + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ)))) * T := by
    rw [hdecomp]
    refine le_trans (abs_add_le _ _) ?_
    exact add_le_add hdirbd htailint
  have hks : 9 * K / s * T = 9 * K * s := by
    field_simp
    nlinarith
  have hfinal : (9 * K / s + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ)))) * T
      ≤ 9 * K * s + 2 := by
    rw [add_mul, hks]
    linarith [hexpbd]
  have hs_le : s ≤ s * Real.sqrt s := by nlinarith
  have h2_le : (2 : ℝ) ≤ s * Real.sqrt s := by nlinarith
  calc |∫ τ in T..(2 * T), hardyZ τ|
      ≤ CD * (s * Real.sqrt s + s * Real.sqrt s) + (9 * K * s + 2) := by linarith
    _ ≤ (2 * CD + 9 * K + 2) * (s * Real.sqrt s) := by nlinarith [hCD, hK]

end

end RHTower
