import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AlmostEveryZeroOrdinateIsWeilPositive

/-!
# A positive proportion of heights is Weil-positive for a whole class of tests

`AlmostEveryZeroOrdinateIsWeilPositive` proves positivity of `Q_γ(F₀) = Q(F₀ cos γ·) + Q(F₀ sin γ·)` at
almost every zero ordinate for nonnegative tests. A zero at distance `≤ 1/(A + 1)` from the height `γ`
still contributes at least `(∫ F₀)²/4` for every nonnegative `F₀` supported in `[-A, A]`, because
`cos(xu) ≥ 1/2` for `|xu| ≤ 1`. Such heights fill a positive proportion of every short window.

**Theorem** (`exists_shortWindow_positiveProportion_heights_weilPositive`). There are `c > 0`, `C` and
`Γ₀` such that for `Γ ≥ Γ₀`, `Γ^{99/100} ≤ H ≤ Γ/8`, `A ≥ 0` and `η > 0` there is a set
`S ⊆ [Γ, Γ + H]` of measure at least `c H/(A + 1) - C H/(η log Γ)` such that for every `γ ∈ S` and
every nonnegative `F₀ ∈ C²_c([-A, A])`:
`Q_γ(F₀) ≥ (∫ F₀)²/4 - 4η (A + 1)² e^A N(F₀)²`.

The set depends on `A` and `η` only: for every nonnegative test with
`16η (A + 1)² e^A N(F₀)² < (∫ F₀)²`, the Weil form is positive at every height of `S`.

**Proof.** The heights within `r = 1/(A + 1)` of a zero ordinate of the window cover measure
`≥ 2r #Z / (max local count) ≥ c r H` (overlap counting against `#{q : |Im q - γ| ≤ 1} = O(log Γ)`),
and the heights with `Φ(γ) > η` have measure `≤ C H/(η log Γ)`.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped BigOperators Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.BiScaleUncertainty
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A zero within `1/A` of the height is seen with at least half the mass:
`(1/2) ∫ F₀ ≤ ‖F̂(depthSum_ρ)(-γ)‖` for nonnegative `F₀` supported in `[-A, A]` and
`|Im ρ - γ| A ≤ 1`. -/
theorem half_integral_le_norm_paperFT_depthSumProfile {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    (hnn : ∀ u, 0 ≤ F₀ u) (ρ : ℂ) {γ : ℝ} (hγ : |ρ.im - γ| * A ≤ 1) :
    (1 / 2) * (∫ u, F₀ u) ≤ ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ := by
  set c : ℝ → ℝ := fun u => (Real.exp ((ρ.re - 1 / 2) * u) + Real.exp (-((ρ.re - 1 / 2) * u))) / 2
    with hc
  set θ : ℝ := ρ.im - γ with hθ
  have hc1 : ∀ u, 1 ≤ c u := fun u => by
    rw [hc]
    have h := Real.one_le_cosh ((ρ.re - 1 / 2) * u)
    rwa [Real.cosh_eq] at h
  have hpt : ∀ u : ℝ, depthSumProfile F₀ ρ u * Complex.exp (Complex.I * (-(γ : ℂ)) * u) =
      ((F₀ u * c u : ℝ) : ℂ) * Complex.exp (((θ * u : ℝ) : ℂ) * Complex.I) := fun u => by
    unfold depthSumProfile
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hθ]; push_cast; ring
  have hcc : Continuous c := by rw [hc]; fun_prop
  have hint : Integrable fun u : ℝ => ((F₀ u * c u : ℝ) : ℂ) * Complex.exp (((θ * u : ℝ) : ℂ) * Complex.I) :=
    ((Complex.continuous_ofReal.comp (hF₀.mul hcc)).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hF₀c.mul_right.comp_left Complex.ofReal_zero).mul_right)
  have hre : (paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))).re =
      ∫ u, F₀ u * c u * Real.cos (θ * u) := by
    unfold paperFT
    simp_rw [hpt]
    have h := (integral_re hint).symm
    simp only [RCLike.re_to_complex] at h
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hint1 : Integrable F₀ := hF₀.integrable_of_hasCompactSupport hF₀c
  have hint2 : Integrable fun u => F₀ u * c u * Real.cos (θ * u) :=
    ((hF₀.mul hcc).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hF₀c.mul_right.mul_right)
  have hmono : (∫ u, (1 / 2) * F₀ u) ≤ ∫ u, F₀ u * c u * Real.cos (θ * u) := by
    refine integral_mono (hint1.const_mul _) hint2 fun u => ?_
    by_cases hu : |u| ≤ A
    · have hθu : |θ * u| ≤ 1 := by
        rw [abs_mul]
        calc |θ| * |u| ≤ |θ| * A := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
          _ ≤ 1 := hγ
      have hcos : 1 / 2 ≤ Real.cos (θ * u) := by
        have h := Real.one_sub_sq_div_two_le_cos (x := θ * u)
        have hsq : (θ * u) ^ 2 ≤ 1 := by
          rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hθu
        linarith
      have h1 : (1 / 2 : ℝ) ≤ c u * Real.cos (θ * u) := by
        nlinarith [hc1 u, hcos]
      calc (1 / 2) * F₀ u ≤ (c u * Real.cos (θ * u)) * F₀ u :=
            mul_le_mul_of_nonneg_right h1 (hnn u)
        _ = F₀ u * c u * Real.cos (θ * u) := by ring
    · rw [hsupp u (not_le.mp hu)]
      simp
  rw [integral_const_mul] at hmono
  rw [← hre] at hmono
  exact hmono.trans (Complex.re_le_norm _)

/-- **Pointwise law near a zero ordinate.** If a zero copy `q` has `|Im q - γ| A ≤ 1`, then for every
nonnegative `F₀ ∈ C²_c([-A, A])`:
`Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ (∫ F₀)²/4 - 4 (A + 1)² e^A N(F₀)² Φ(γ)`. -/
theorem quarter_sq_integral_sub_offLineField_le_fullZeroForm {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    (hnn : ∀ u, 0 ≤ F₀ u) (q : XiZeroCopy) {γ : ℝ} (hγ : |(q.1 : ℂ).im - γ| * A ≤ 1) :
    (1 / 4) * (∫ u, F₀ u) ^ 2 - 4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 *
        offLineField γ ≤
      fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  classical
  rw [fullZeroForm_cosine_add_sine_eq_zeta_W_re hF₀ hF₀c γ]
  obtain ⟨hsum, -⟩ := integral_Icc_tsum_depthDiff_div_four_le hF₀ hF₀c (Γ := 1) le_rfl hA hsupp
  set ρ₀ : zetaZeroConfig.carrier := xiDivisorZetaCarrierEquiv q.1 with hρ₀
  have h := re_zeta_W_complexModulatedSource_ge_finset hF₀ hF₀c γ {ρ₀} (hsum γ)
  rw [Finset.sum_singleton] at h
  have hcoe : ((ρ₀ : ℂ)) = (q.1 : ℂ) := rfl
  have hm : (1 : ℝ) ≤ (zetaZeroConfig.mult ρ₀ : ℝ) := by
    have h1 := xiDivisorZetaCarrierEquiv_multiplicity q.1
    have h2 := xiSupportMultiplicity_pos q.1
    have h3 : (1 : ℕ) ≤ zetaZeroConfig.mult ρ₀ := by
      rw [hρ₀, ← h1]
      exact h2
    exact_mod_cast h3
  have hmain : (1 / 4) * (∫ u, F₀ u) ^ 2 ≤
      ‖paperFT (depthSumProfile F₀ (ρ₀ : ℂ)) (-(γ : ℂ))‖ ^ 2 := by
    have hI : 0 ≤ ∫ u, F₀ u := integral_nonneg hnn
    have h1 := half_integral_le_norm_paperFT_depthSumProfile hF₀.continuous hF₀c hsupp hnn
      (q.1 : ℂ) hγ
    rw [hcoe]
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    calc (1 / 4) * (∫ u, F₀ u) ^ 2 = ((1 / 2) * (∫ u, F₀ u)) ^ 2 := by ring
      _ ≤ _ := h2
  have hmain' : (1 / 4) * (∫ u, F₀ u) ^ 2 ≤ (zetaZeroConfig.mult ρ₀ : ℝ) *
      ‖paperFT (depthSumProfile F₀ (ρ₀ : ℂ)) (-(γ : ℂ))‖ ^ 2 :=
    hmain.trans (le_mul_of_one_le_left (sq_nonneg _) hm)
  have htail := tsum_depthDiff_le_offLineField hF₀ hF₀c hA hsupp γ
  linarith

/-! ### Heights near a zero ordinate fill a positive proportion of a window -/

/-- **Overlap counting.** If a finite family of intervals `[t_i - r, t_i + r] ⊆ W` has every point
in at most `K` of them, their union has measure at least `2r · #family / K`. -/
theorem le_volume_biUnion_of_overlap {ι : Type*} (Z : Finset ι) (t : ι → ℝ) {r K : ℝ}
    (hr : 0 ≤ r)
    (hover : ∀ γ : ℝ, ((Z.filter fun i => |t i - γ| ≤ r).card : ℝ) ≤ K) :
    2 * r * (Z.card : ℝ) ≤ K * (volume (⋃ i ∈ Z, Icc (t i - r) (t i + r))).toReal := by
  classical
  set U : Set ℝ := ⋃ i ∈ Z, Icc (t i - r) (t i + r) with hU
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion Z fun i _ => measurableSet_Icc
  have hUfin : volume U < ⊤ := by
    refine (measure_biUnion_finset_le Z _).trans_lt ?_
    exact ENNReal.sum_lt_top.mpr fun i _ => by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hind : ∀ i ∈ Z, Integrable ((Icc (t i - r) (t i + r)).indicator (fun _ => (1 : ℝ))) :=
    fun i _ => (integrableOn_const (C := (1 : ℝ)) (by rw [Real.volume_Icc]; exact
      ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hsum_int : ∫ γ, ∑ i ∈ Z, (Icc (t i - r) (t i + r)).indicator (fun _ => (1 : ℝ)) γ =
      2 * r * (Z.card : ℝ) := by
    rw [integral_finsetSum Z hind]
    have : ∀ i ∈ Z, ∫ γ, (Icc (t i - r) (t i + r)).indicator (fun _ => (1 : ℝ)) γ = 2 * r :=
      fun i _ => by
        rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
        ring
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    ring
  have hpt : ∀ γ, ∑ i ∈ Z, (Icc (t i - r) (t i + r)).indicator (fun _ => (1 : ℝ)) γ ≤
      U.indicator (fun _ => K) γ := by
    intro γ
    by_cases hγ : γ ∈ U
    · rw [Set.indicator_of_mem hγ]
      have heq : ∑ i ∈ Z, (Icc (t i - r) (t i + r)).indicator (fun _ => (1 : ℝ)) γ =
          ((Z.filter fun i => |t i - γ| ≤ r).card : ℝ) := by
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : |t i - γ| ≤ r
        · have hmem : γ ∈ Icc (t i - r) (t i + r) := by
            rw [abs_le] at hi; exact ⟨by linarith, by linarith⟩
          rw [Set.indicator_of_mem hmem, if_pos hi, Nat.cast_one]
        · have hmem : γ ∉ Icc (t i - r) (t i + r) := fun h => hi (abs_le.mpr
            ⟨by linarith [h.2], by linarith [h.1]⟩)
          rw [Set.indicator_of_notMem hmem, if_neg hi, Nat.cast_zero]
      rw [heq]
      exact hover γ
    · rw [Set.indicator_of_notMem hγ]
      refine le_of_eq (Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (fun h => hγ ?_) _)
      rw [hU]
      exact Set.mem_biUnion hi h
  have hKint : Integrable (U.indicator (fun _ => K)) :=
    (integrableOn_const (C := K) hUfin.ne).integrable_indicator hUm
  have hmono := integral_mono (integrable_finsetSum Z hind) hKint hpt
  rw [hsum_int, integral_indicator_const _ hUm, Measure.real, smul_eq_mul] at hmono
  calc 2 * r * (Z.card : ℝ) ≤ (volume U).toReal * K := hmono
    _ = K * (volume U).toReal := by ring

/-- **A positive proportion of heights is Weil-positive for a whole class of tests.** There are
`c > 0`, `C ≥ 0` and `Γ₀` such that for `Γ ≥ Γ₀`, `Γ^{99/100} ≤ H ≤ Γ/8`, `A ≥ 0` and `η > 0` there is
`S ⊆ [Γ, Γ + H]` with `volume S ≥ c H/(A + 1) - C H/(η log Γ)` such that at every `γ ∈ S`, for every
nonnegative `F₀ ∈ C²_c([-A, A])`, `Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ (∫ F₀)²/4 - 4η (A + 1)² e^A N(F₀)²`. -/
theorem exists_shortWindow_positiveProportion_heights_weilPositive :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∃ Γ₀ : ℝ, 64 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ H : ℝ, Γ ^ (99 / 100 : ℝ) ≤ H → H ≤ Γ / 8 →
        ∀ A : ℝ, 0 ≤ A → ∀ η : ℝ, 0 < η →
          ∃ S : Set ℝ, S ⊆ Icc Γ (Γ + H) ∧
            ENNReal.ofReal (c * H / (A + 1) - C * H / (η * Real.log Γ)) ≤ volume S ∧
            ∀ γ ∈ S, ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
              (∀ u : ℝ, A < |u| → F₀ u = 0) → (∀ u, 0 ≤ F₀ u) →
              (1 / 4) * (∫ u, F₀ u) ^ 2 -
                  4 * η * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 ≤
                fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  obtain ⟨C, hC, Γ₁, hΓ₁, hvol⟩ := exists_volume_offLineField_gt_le
  obtain ⟨Γ_c, hΓ_c, hcore⟩ := exists_window_core_count
  obtain ⟨Cw, hCw, T₀w, hT₀w, hwinle⟩ := exists_xiZeroCount_window_le
  set K₄ : ℝ := 2 * (1 + 2 * Cw) with hK₄
  have hK₄0 : 0 < K₄ := by rw [hK₄]; positivity
  refine ⟨1 / (16 * Real.pi * K₄), C, by positivity, hC, max Γ₁ (max Γ_c (T₀w + 8)),
    hΓ₁.trans (le_max_left _ _), fun Γ hΓ H hH1 hH2 A hA η hη => ?_⟩
  classical
  have hΓ64 : 64 ≤ Γ := (hΓ₁.trans (le_max_left _ _)).trans hΓ
  have hΓT : T₀w + 8 ≤ Γ := ((le_max_right _ _).trans (le_max_right _ _)).trans hΓ
  have hΓ0 : 0 < Γ := by linarith
  have hL : 1 ≤ Real.log Γ := by
    have : Real.exp 1 ≤ Γ := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) this
    rwa [Real.log_exp] at this
  have hL0 : 0 < Real.log Γ := by linarith
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hΓ0 _) hH1
  have hH8 : 8 ≤ H := by
    have h1 : Γ ^ (1 / 2 : ℝ) ≤ H :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)).trans hH1
    have h2 : (8 : ℝ) ≤ Γ ^ (1 / 2 : ℝ) := by
      have := Real.rpow_le_rpow (by norm_num) hΓ64 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have e : (64 : ℝ) ^ (1 / 2 : ℝ) = 8 := by
        rw [show (64 : ℝ) = 8 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith
    linarith
  set r : ℝ := 1 / (A + 1) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one (by linarith)]; linarith
  have hrA : r * A ≤ 1 := by
    rw [hr, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; linarith
  -- The core zero copies, well inside the window.
  set W := xiSupportsWindow (Γ + H / 4) (Γ + 3 * H / 4)
  have hW0 : (0 : ℝ) ≤ Γ + H / 4 := by linarith
  set Z := xiCopiesOf W with hZ
  have hZmem : ∀ q ∈ Z, Γ + H / 4 < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + 3 * H / 4 := fun q hq => by
    rw [hZ] at hq
    unfold xiCopiesOf at hq
    rw [Finset.mem_sigma] at hq
    exact (mem_xiSupportsWindow hW0).mp hq.1
  have hZcard : H * Real.log Γ / (16 * Real.pi) ≤ (Z.card : ℝ) := by
    obtain ⟨hlow, -⟩ := hcore Γ ((le_max_left _ _).trans ((le_max_right _ _).trans hΓ)) H hH1 hH2
    have hcopies : ((xiCopiesOf W).card : ℝ) = ∑ ρ ∈ W, (xiSupportMultiplicity ρ : ℝ) := by
      unfold xiCopiesOf
      rw [Finset.card_sigma]
      push_cast
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Finset.card_univ, Fintype.card_fin]
      rfl
    rw [hZ, hcopies]
    have e : H * Real.log Γ / (16 * Real.pi) = (1 / (16 * Real.pi)) * H * Real.log Γ := by ring
    linarith
  -- At most `K₄ log Γ` copies within distance `r` of any height of the window.
  have hover : ∀ γ : ℝ, ((Z.filter fun q => |(q.1 : ℂ).im - γ| ≤ r).card : ℝ) ≤
      K₄ * Real.log Γ := by
    intro γ
    by_cases hγ : ∃ q ∈ Z, |(q.1 : ℂ).im - γ| ≤ r
    · obtain ⟨q₀, hq₀, hd₀⟩ := hγ
      have hq₀' := hZmem q₀ hq₀
      have hγlo : Γ + H / 4 - 1 ≤ γ := by
        have := (abs_le.mp hd₀).2; linarith [hq₀'.1]
      have hγhi : γ ≤ Γ + 3 * H / 4 + 1 := by
        have := (abs_le.mp hd₀).1; linarith [hq₀'.2]
      have ha0 : (0 : ℝ) ≤ γ - 2 := by linarith
      have hc := card_le_xiZeroCount_sub (a := γ - 2) (b := γ + 1) ha0 (by linarith)
        (Z.filter fun q => |(q.1 : ℂ).im - γ| ≤ r)
        fun q hq => by
          have h := (abs_le.mp (Finset.mem_filter.mp hq).2)
          exact ⟨by linarith [h.1], by linarith [h.2]⟩
      have hw := hwinle (γ - 2) (by linarith) 3 (by norm_num)
      rw [show γ - 2 + 3 = γ + 1 by ring] at hw
      have hlog : Real.log (γ + 1) ≤ 2 * Real.log Γ := by
        have hΓsq : 16 * Γ ≤ Γ ^ 2 := by
          rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hΓ0.le
        have : Real.log (γ + 1) ≤ Real.log (Γ ^ 2) := Real.log_le_log (by linarith) (by linarith)
        rw [Real.log_pow] at this; push_cast at this; linarith
      have hlog0 : 0 ≤ Real.log (γ + 1) := Real.log_nonneg (by linarith)
      have hπ : 3 / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
      calc ((Z.filter fun q => |(q.1 : ℂ).im - γ| ≤ r).card : ℝ)
          ≤ 3 / (2 * Real.pi) * Real.log (γ + 1) + 2 * Cw * Real.log (γ + 1) := hc.trans hw
        _ ≤ 1 * Real.log (γ + 1) + 2 * Cw * Real.log (γ + 1) := by
            gcongr
        _ = (1 + 2 * Cw) * Real.log (γ + 1) := by ring
        _ ≤ (1 + 2 * Cw) * (2 * Real.log Γ) := mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = K₄ * Real.log Γ := by rw [hK₄]; ring
    · push Not at hγ
      have : (Z.filter fun q => |(q.1 : ℂ).im - γ| ≤ r) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun q hq => not_le.mpr (hγ q hq)
      rw [this, Finset.card_empty, Nat.cast_zero]
      positivity
  have hKL : 0 < K₄ * Real.log Γ := by positivity
  set U : Set ℝ := ⋃ q ∈ Z, Icc ((q.1 : ℂ).im - r) ((q.1 : ℂ).im + r) with hU
  have hUvol := le_volume_biUnion_of_overlap Z (fun q => (q.1 : ℂ).im) hr0.le hover
  have hUsub : U ⊆ Icc Γ (Γ + H) := by
    intro γ hγ
    rw [hU, Set.mem_iUnion₂] at hγ
    obtain ⟨q, hq, hγq⟩ := hγ
    have hq' := hZmem q hq
    exact ⟨by linarith [hγq.1, hq'.1], by linarith [hγq.2, hq'.2]⟩
  -- Remove the heights with a large off-line field.
  set B : Set ℝ := {γ | γ ∈ Icc Γ (Γ + H) ∧ η < offLineField γ} with hB
  have hBvol := hvol Γ ((le_max_left _ _).trans hΓ) H hH1 hH2 η hη
  refine ⟨U \ B, Set.sdiff_subset.trans hUsub, ?_, ?_⟩
  · have hUfin : volume U ≠ ⊤ :=
      ((measure_mono hUsub).trans_lt (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)).ne
    have hle : volume U ≤ volume (U \ B) + volume B := by
      calc volume U ≤ volume ((U \ B) ∪ B) := measure_mono fun γ hγ => by
            by_cases h : γ ∈ B
            · exact Or.inr h
            · exact Or.inl ⟨hγ, h⟩
        _ ≤ volume (U \ B) + volume B := measure_union_le _ _
    have hU_real : (1 / (16 * Real.pi * K₄)) * H / (A + 1) ≤ (volume U).toReal := by
      have h1 : 2 * r * (H * Real.log Γ / (16 * Real.pi)) ≤ K₄ * Real.log Γ * (volume U).toReal :=
        (mul_le_mul_of_nonneg_left hZcard (by positivity)).trans hUvol
      have e : (1 / (16 * Real.pi * K₄)) * H / (A + 1) * (K₄ * Real.log Γ) =
          (1 / 2) * (2 * r * (H * Real.log Γ / (16 * Real.pi))) := by
        rw [hr]; field_simp
      have h3 : 0 ≤ 2 * r * (H * Real.log Γ / (16 * Real.pi)) := by positivity
      have h4 : (1 / (16 * Real.pi * K₄)) * H / (A + 1) * (K₄ * Real.log Γ) ≤
          (volume U).toReal * (K₄ * Real.log Γ) := by
        rw [e]; nlinarith [h1, h3]
      exact le_of_mul_le_mul_right h4 hKL
    calc ENNReal.ofReal ((1 / (16 * Real.pi * K₄)) * H / (A + 1) - C * H / (η * Real.log Γ))
        ≤ ENNReal.ofReal ((volume U).toReal - (volume B).toReal) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hBreal : (volume B).toReal ≤ C * H / (η * Real.log Γ) := by
            have hBfin : volume B ≠ ⊤ := (hBvol.trans_lt ENNReal.ofReal_lt_top).ne
            calc (volume B).toReal ≤ (ENNReal.ofReal (C * H / (η * Real.log Γ))).toReal :=
                  ENNReal.toReal_mono ENNReal.ofReal_ne_top hBvol
              _ = C * H / (η * Real.log Γ) := ENNReal.toReal_ofReal (by positivity)
          linarith
      _ = volume U - volume B := by
          have hBfin : volume B ≠ ⊤ := (hBvol.trans_lt ENNReal.ofReal_lt_top).ne
          rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hUfin,
            ENNReal.ofReal_toReal hBfin]
      _ ≤ volume (U \ B) := tsub_le_iff_right.mpr hle
  · intro γ hγ F₀ hF₀ hF₀c hsupp hnn
    obtain ⟨hγU, hγB⟩ := hγ
    rw [hU, Set.mem_iUnion₂] at hγU
    obtain ⟨q, hq, hγq⟩ := hγU
    have hdist : |(q.1 : ℂ).im - γ| * A ≤ 1 := by
      have h1 : |(q.1 : ℂ).im - γ| ≤ r :=
        abs_le.mpr ⟨by linarith [hγq.2], by linarith [hγq.1]⟩
      calc |(q.1 : ℂ).im - γ| * A ≤ r * A := mul_le_mul_of_nonneg_right h1 hA
        _ ≤ 1 := hrA
    have hγwin : γ ∈ Icc Γ (Γ + H) := hUsub (by rw [hU, Set.mem_iUnion₂]; exact ⟨q, hq, hγq⟩)
    have hΦ : offLineField γ ≤ η := not_lt.mp fun h => hγB ⟨hγwin, h⟩
    have h := quarter_sq_integral_sub_offLineField_le_fullZeroForm hF₀ hF₀c hA hsupp hnn q hdist
    have hK : 0 ≤ 4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hΦ hK
    linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
