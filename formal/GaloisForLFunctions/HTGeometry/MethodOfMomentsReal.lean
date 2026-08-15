import GaloisForLFunctions.HTGeometry.HardyStieltjesDeterminacy
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# The method of moments on the real line

A probability measure whose absolute moments grow no faster than a factorial-geometric sequence has
a bilateral exponential window at the origin, hence is determined by its moments.

A sequence of probability measures obeying one such bound uniformly is tight, so every subsequence
has a weakly convergent further subsequence.  Truncating a monomial at a clamped level turns the
uniform bound into convergence of every moment along that subsequence, and determinacy identifies
the limit.  Consequently convergence of all moments to those of one measure with a factorial
moment bound forces weak convergence to that measure.
-/

open Filter MeasureTheory ProbabilityTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Window

/-- All absolute moments of the measure are bounded by a factorial-geometric sequence. -/
def HasFactorialMomentBound (ρ : Measure ℝ) (M : ℝ) : Prop :=
  ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (|x| ^ n) ∂ρ ≤ ENNReal.ofReal ((Nat.factorial n : ℝ) * M ^ n)

theorem lintegral_abs_pow_ne_top {ρ : Measure ℝ} {M : ℝ} (h : HasFactorialMomentBound ρ M)
    (n : ℕ) : ∫⁻ x, ENNReal.ofReal (|x| ^ n) ∂ρ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h n)

theorem integrable_pow_of_factorialMomentBound {ρ : Measure ℝ} {M : ℝ}
    (h : HasFactorialMomentBound ρ M) (n : ℕ) : Integrable (fun x : ℝ => x ^ n) ρ := by
  refine ⟨(measurable_id.pow_const n).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hle : ∀ x : ℝ, ‖x ^ n‖ₑ = ENNReal.ofReal (|x| ^ n) := by
    intro x
    rw [← Real.enorm_eq_ofReal (by positivity), ← abs_pow]
    simp
  simp_rw [hle]
  exact lt_of_le_of_ne le_top (lintegral_abs_pow_ne_top h n)

theorem integrable_abs_pow_of_factorialMomentBound {ρ : Measure ℝ} {M : ℝ}
    (h : HasFactorialMomentBound ρ M) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) ρ := by
  have := integrable_pow_of_factorialMomentBound h n
  simpa [abs_pow] using this.abs

theorem integral_abs_pow_le {ρ : Measure ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : HasFactorialMomentBound ρ M) (n : ℕ) :
    ∫ x : ℝ, |x| ^ n ∂ρ ≤ (Nat.factorial n : ℝ) * M ^ n := by
  have hnn : 0 ≤ᵐ[ρ] fun x : ℝ => |x| ^ n := Filter.Eventually.of_forall fun x => by positivity
  have hlint : ENNReal.ofReal (∫ x : ℝ, |x| ^ n ∂ρ) = ∫⁻ x, ENNReal.ofReal (|x| ^ n) ∂ρ :=
    ofReal_integral_eq_lintegral_ofReal (integrable_abs_pow_of_factorialMomentBound h n) hnn
  have hle : ENNReal.ofReal (∫ x : ℝ, |x| ^ n ∂ρ) ≤
      ENNReal.ofReal ((Nat.factorial n : ℝ) * M ^ n) := by
    rw [hlint]
    exact h n
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle

/-- **Exponential window from factorial moments.**  A factorial-geometric moment bound makes every
exponential with small enough rate integrable. -/
theorem integrable_exp_mul_of_factorialMomentBound {ρ : Measure ℝ} {M : ℝ} (hM : 0 < M)
    (h : HasFactorialMomentBound ρ M) {t : ℝ} (ht : |t| * M < 1) :
    Integrable (fun x : ℝ => Real.exp (t * x)) ρ := by
  set q : ℝ := |t| * M with hq
  have hq0 : 0 ≤ q := by positivity
  have hsummable : Summable fun n : ℕ => q ^ n := summable_geometric_of_lt_one hq0 ht
  have hbound : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal ((|t| * |x|) ^ n / (Nat.factorial n : ℝ)) ∂ρ ≤
      ENNReal.ofReal (q ^ n) := by
    intro n
    have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    have hrw : ∀ x : ℝ, ENNReal.ofReal ((|t| * |x|) ^ n / (Nat.factorial n : ℝ)) =
        ENNReal.ofReal (|t| ^ n / (Nat.factorial n : ℝ)) * ENNReal.ofReal (|x| ^ n) := by
      intro x
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_pow]
      field_simp
    simp_rw [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (mul_le_mul' le_rfl (h n)) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [hq, mul_pow]
    field_simp
  have hfinite : ∫⁻ x, ENNReal.ofReal (Real.exp (|t| * |x|)) ∂ρ ≤
      ENNReal.ofReal (1 - q)⁻¹ := by
    have hseries : ∀ x : ℝ, ENNReal.ofReal (Real.exp (|t| * |x|)) =
        ∑' n : ℕ, ENNReal.ofReal ((|t| * |x|) ^ n / (Nat.factorial n : ℝ)) := by
      intro x
      have hexp : Real.exp (|t| * |x|) =
          ∑' n : ℕ, (|t| * |x|) ^ n / (Nat.factorial n : ℝ) := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      rw [hexp]
      refine ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) ?_
      have := Real.summable_pow_div_factorial (|t| * |x|)
      simpa using this
    simp_rw [hseries]
    have hswap := lintegral_tsum (μ := ρ)
      (f := fun (n : ℕ) (x : ℝ) => ENNReal.ofReal ((|t| * |x|) ^ n / (Nat.factorial n : ℝ)))
      (fun n => (ENNReal.measurable_ofReal.comp
        (((measurable_const.mul measurable_id.abs).pow_const n).div_const _)).aemeasurable)
    rw [hswap]
    refine le_trans (ENNReal.tsum_le_tsum hbound) ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [tsum_geometric_of_lt_one hq0 ht]

  have hgint : Integrable (fun x : ℝ => Real.exp (|t| * |x|)) ρ := by
    refine ⟨(Real.continuous_exp.comp (continuous_const.mul continuous_abs)).measurable
      |>.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hfinite ENNReal.ofReal_lt_top
  refine Integrable.mono' hgint ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
      ).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  calc t * x ≤ |t * x| := le_abs_self _
    _ = |t| * |x| := abs_mul t x

theorem zero_mem_interior_integrableExpSet {ρ : Measure ℝ} {M : ℝ} (hM : 0 < M)
    (h : HasFactorialMomentBound ρ M) : 0 ∈ interior (integrableExpSet id ρ) := by
  have hsub : Set.Ioo (-M⁻¹) M⁻¹ ⊆ integrableExpSet id ρ := by
    intro t ht
    have habs : |t| < M⁻¹ := abs_lt.mpr ⟨ht.1, ht.2⟩
    have hlt : |t| * M < 1 := by
      calc |t| * M < M⁻¹ * M := mul_lt_mul_of_pos_right habs hM
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hM)
    exact integrable_exp_mul_of_factorialMomentBound hM h hlt
  have hopen : IsOpen (Set.Ioo (-M⁻¹) M⁻¹) := isOpen_Ioo
  have hmem : (0 : ℝ) ∈ Set.Ioo (-M⁻¹) M⁻¹ := by
    constructor
    · simp [inv_pos.mpr hM]
    · exact inv_pos.mpr hM
  exact interior_maximal hsub hopen hmem

end Window

section Tightness

theorem measure_norm_gt_le {ρ : Measure ℝ} {M : ℝ} (h : HasFactorialMomentBound ρ M)
    {r : ℝ} (hr : 0 < r) :
    ρ {x : ℝ | r < ‖x‖} ≤ ENNReal.ofReal (2 * M ^ 2 / r ^ 2) := by
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal (|x| ^ 2)) ρ :=
    (ENNReal.measurable_ofReal.comp (measurable_id.abs.pow_const 2)).aemeasurable
  have hcheb := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (r ^ 2))
  have hsubset : {x : ℝ | r < ‖x‖} ⊆
      {x : ℝ | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (|x| ^ 2)} := by
    intro x hx
    have hx' : r < |x| := hx
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : (0 : ℝ) ≤ r := hr.le
    nlinarith [hx', h0, abs_nonneg x]
  have hmono : ENNReal.ofReal (r ^ 2) * ρ {x : ℝ | r < ‖x‖} ≤
      ENNReal.ofReal (r ^ 2) * ρ {x : ℝ | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (|x| ^ 2)} :=
    mul_le_mul' le_rfl (measure_mono hsubset)
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have hkey : ENNReal.ofReal (r ^ 2) * ρ {x : ℝ | r < ‖x‖} ≤
      ENNReal.ofReal (2 * M ^ 2) := by
    have h2 := le_trans hmono (le_trans hcheb (h 2))
    rwa [hfac] at h2
  have hrpos : (0 : ℝ) < r ^ 2 := by positivity
  have hne0 : ENNReal.ofReal (r ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hrpos
  rw [ENNReal.ofReal_div_of_pos hrpos,
    ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact hkey

/-- **Tightness from a uniform factorial moment bound.** -/
theorem isTightMeasureSet_of_factorialMomentBound {S : Set (ProbabilityMeasure ℝ)} {M : ℝ}
    (h : ∀ μ ∈ S, HasFactorialMomentBound ((μ : ProbabilityMeasure ℝ) : Measure ℝ) M) :
    IsTightMeasureSet {x | ∃ μ ∈ S, ((μ : ProbabilityMeasure ℝ) : Measure ℝ) = x} := by
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have hupper : Tendsto
      (fun r : ℝ => ENNReal.ofReal (2 * M ^ 2 / r ^ 2)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun r : ℝ => 2 * M ^ 2 / r ^ 2) atTop (𝓝 0) := by
      have hsq : Tendsto (fun r : ℝ => r ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
      exact tendsto_const_nhds.div_atTop hsq
    have h2 : Tendsto (fun r : ℝ => ENNReal.ofReal (2 * M ^ 2 / r ^ 2)) atTop
        (𝓝 (ENNReal.ofReal 0)) := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun r => bot_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  refine iSup_le fun ρ => ?_
  refine iSup_le fun hρ => ?_
  obtain ⟨μ, hμS, rfl⟩ := hρ
  exact measure_norm_gt_le (h μ hμS) hr

end Tightness

section Truncation

/-- The symmetric clamp of a real number to a prescribed level. -/
def clamp (R x : ℝ) : ℝ := max (-R) (min R x)

theorem continuous_clamp (R : ℝ) : Continuous (clamp R) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_clamp_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clamp R x| ≤ R := by
  rw [abs_le, clamp]
  constructor
  · exact le_max_left _ _
  · refine max_le (by linarith) ?_
    exact min_le_left _ _

theorem clamp_eq_self {R x : ℝ} (hx : |x| ≤ R) : clamp R x = x := by
  rw [abs_le] at hx
  rw [clamp, min_eq_right hx.2, max_eq_right hx.1]

/-- The clamped monomial differs from the monomial by at most the next absolute moment scaled by
the clamping level. -/
theorem abs_pow_sub_clamp_pow_le {R : ℝ} (hR : 0 < R) (n : ℕ) (x : ℝ) :
    |x ^ n - clamp R x ^ n| ≤ 2 * |x| ^ (n + 1) / R := by
  by_cases hx : |x| ≤ R
  · rw [clamp_eq_self hx, sub_self, abs_zero]
    positivity
  · replace hx : R < |x| := not_le.mp hx
    have hxn : R ^ n ≤ |x| ^ n := pow_le_pow_left₀ hR.le hx.le n
    have h1 : |x ^ n - clamp R x ^ n| ≤ |x| ^ n + R ^ n := by
      refine le_trans (abs_sub _ _) ?_
      have h2 : |clamp R x ^ n| ≤ R ^ n := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_clamp_le hR.le x) n
      have h3 : |x ^ n| = |x| ^ n := abs_pow x n
      linarith [h2, h3.le, h3.ge]
    have h4 : |x| ^ n + R ^ n ≤ 2 * |x| ^ n := by linarith
    have h5 : 2 * |x| ^ n ≤ 2 * |x| ^ (n + 1) / R := by
      rw [le_div_iff₀ hR, pow_succ]
      nlinarith [pow_nonneg (abs_nonneg x) n, hx, hR]
    linarith

theorem abs_integral_pow_sub_clamp_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {M : ℝ}
    (hM : 0 ≤ M) (h : HasFactorialMomentBound ρ M) (n : ℕ) {R : ℝ} (hR : 0 < R) :
    |(∫ x : ℝ, x ^ n ∂ρ) - ∫ x : ℝ, clamp R x ^ n ∂ρ| ≤
      2 * ((Nat.factorial (n + 1) : ℝ) * M ^ (n + 1)) / R := by
  have hint1 : Integrable (fun x : ℝ => x ^ n) ρ := integrable_pow_of_factorialMomentBound h n
  have hint2 : Integrable (fun x : ℝ => clamp R x ^ n) ρ := by
    refine ⟨((continuous_clamp R).measurable.pow_const n).aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (R ^ n)).mono ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) (abs_clamp_le hR.le x) n) ?_
    exact le_abs_self _
  have hbound : Integrable (fun x : ℝ => 2 * |x| ^ (n + 1) / R) ρ := by
    have := integrable_abs_pow_of_factorialMomentBound h (n + 1)
    simpa [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm] using
      (this.const_mul (2 : ℝ)).mul_const R⁻¹
  rw [← integral_sub hint1 hint2]
  refine le_trans (abs_integral_le_integral_abs) ?_
  refine le_trans (integral_mono ((hint1.sub hint2).abs) hbound
    (fun x => abs_pow_sub_clamp_pow_le hR n x)) ?_
  have hsplit : ∫ x : ℝ, 2 * |x| ^ (n + 1) / R ∂ρ =
      2 * (∫ x : ℝ, |x| ^ (n + 1) ∂ρ) / R := by
    simp_rw [div_eq_mul_inv, mul_assoc]
    rw [integral_const_mul, integral_mul_const]
  rw [hsplit]
  have hmom := integral_abs_pow_le hM h (n + 1)
  have hR' : (0 : ℝ) < R := hR
  rw [div_le_div_iff_of_pos_right hR']
  linarith

end Truncation

section WeakLimits

/-- The clamped monomial as a bounded continuous function. -/
def clampBCF (R : ℝ) (hR : 0 ≤ R) (n : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => clamp R x ^ n)
    ((continuous_clamp R).pow n) (R ^ n) (fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_clamp_le hR x) n)

/-- The clamped absolute monomial as a bounded continuous function. -/
def clampAbsBCF (R : ℝ) (hR : 0 ≤ R) (n : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (min |x| R) ^ n)
    ((continuous_abs.min continuous_const).pow n) (R ^ n) (fun x => by
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (le_min (abs_nonneg x) hR)]
      exact pow_le_pow_left₀ (le_min (abs_nonneg x) hR) (min_le_right _ _) n)

theorem integral_clampAbsBCF_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {M : ℝ} (hM : 0 ≤ M)
    (h : HasFactorialMomentBound ρ M) {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ∫ x : ℝ, (min |x| R) ^ n ∂ρ ≤ (Nat.factorial n : ℝ) * M ^ n := by
  refine le_trans (integral_mono ?_ (integrable_abs_pow_of_factorialMomentBound h n)
    (fun x => pow_le_pow_left₀ (le_min (abs_nonneg x) hR) (min_le_left _ _) n))
    (integral_abs_pow_le hM h n)
  exact (clampAbsBCF R hR n).integrable ρ

/-- **A uniform factorial moment bound passes to weak limits.** -/
theorem hasFactorialMomentBound_of_tendsto {μ : ℕ → ProbabilityMeasure ℝ}
    {ρ : ProbabilityMeasure ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hμ : ∀ k, HasFactorialMomentBound ((μ k : ProbabilityMeasure ℝ) : Measure ℝ) M)
    (hconv : Tendsto μ atTop (𝓝 ρ)) :
    HasFactorialMomentBound ((ρ : ProbabilityMeasure ℝ) : Measure ℝ) M := by
  intro n
  have hstep : ∀ j : ℕ, ∫ x : ℝ, (min |x| (j : ℝ)) ^ n ∂(ρ : Measure ℝ) ≤
      (Nat.factorial n : ℝ) * M ^ n := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hlim := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv)
      (clampAbsBCF (j : ℝ) hj n)
    refine le_of_tendsto hlim ?_
    refine Eventually.of_forall fun k => ?_
    exact integral_clampAbsBCF_le hM (hμ k) hj n
  have hmeas : ∀ j : ℕ, Measurable fun x : ℝ => ENNReal.ofReal ((min |x| (j : ℝ)) ^ n) :=
    fun j => ENNReal.measurable_ofReal.comp ((measurable_id.abs.min measurable_const).pow_const n)
  have hmono : Monotone fun j : ℕ => fun x : ℝ => ENNReal.ofReal ((min |x| (j : ℝ)) ^ n) := by
    intro i j hij x
    refine ENNReal.ofReal_le_ofReal ?_
    refine pow_le_pow_left₀ (le_min (abs_nonneg x) (Nat.cast_nonneg i)) ?_ n
    exact min_le_min le_rfl (by exact_mod_cast hij)
  have hsup : (fun x : ℝ => ⨆ j : ℕ, ENNReal.ofReal ((min |x| (j : ℝ)) ^ n)) =
      fun x : ℝ => ENNReal.ofReal (|x| ^ n) := by
    funext x
    refine le_antisymm (iSup_le fun j => ?_) ?_
    · exact ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (le_min (abs_nonneg x) (Nat.cast_nonneg j)) (min_le_left _ _) n)
    · obtain ⟨j, hj⟩ := exists_nat_ge |x|
      refine le_trans (le_of_eq ?_) (le_iSup (fun j : ℕ =>
        ENNReal.ofReal ((min |x| (j : ℝ)) ^ n)) j)
      rw [min_eq_left hj]
  have hlint : ∫⁻ x, ENNReal.ofReal (|x| ^ n) ∂(ρ : Measure ℝ) =
      ⨆ j : ℕ, ∫⁻ x, ENNReal.ofReal ((min |x| (j : ℝ)) ^ n) ∂(ρ : Measure ℝ) := by
    rw [← hsup, lintegral_iSup hmeas hmono]
  rw [hlint]
  refine iSup_le fun j => ?_
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have heq : ∫⁻ x, ENNReal.ofReal ((min |x| (j : ℝ)) ^ n) ∂(ρ : Measure ℝ) =
      ENNReal.ofReal (∫ x : ℝ, (min |x| (j : ℝ)) ^ n ∂(ρ : Measure ℝ)) := by
    refine (ofReal_integral_eq_lintegral_ofReal ((clampAbsBCF (j : ℝ) hj n).integrable _) ?_).symm
    exact Eventually.of_forall fun x => pow_nonneg (le_min (abs_nonneg x) hj) n
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (hstep j)

/-- **Moments pass to weak limits under a uniform factorial moment bound.** -/
theorem tendsto_integral_pow_of_tendsto {μ : ℕ → ProbabilityMeasure ℝ}
    {ρ : ProbabilityMeasure ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hμ : ∀ k, HasFactorialMomentBound ((μ k : ProbabilityMeasure ℝ) : Measure ℝ) M)
    (hconv : Tendsto μ atTop (𝓝 ρ)) (n : ℕ) :
    Tendsto (fun k => ∫ x : ℝ, x ^ n ∂((μ k : ProbabilityMeasure ℝ) : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, x ^ n ∂((ρ : ProbabilityMeasure ℝ) : Measure ℝ))) := by
  have hρ := hasFactorialMomentBound_of_tendsto hM hμ hconv
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C : ℝ := 2 * ((Nat.factorial (n + 1) : ℝ) * M ^ (n + 1)) with hC
  have hC0 : 0 ≤ C := by
    have h1 : (0 : ℝ) ≤ M ^ (n + 1) := pow_nonneg hM _
    have h2 : (0 : ℝ) ≤ (Nat.factorial (n + 1) : ℝ) := Nat.cast_nonneg _
    rw [hC]
    nlinarith [h1, h2]
  obtain ⟨R, hR0, hRlt⟩ : ∃ R : ℝ, 0 < R ∧ C / R < ε / 3 := by
    have hden : (0 : ℝ) < 3 * C + 3 := by linarith
    refine ⟨(3 * C + 3) / ε, div_pos hden hε, ?_⟩
    rw [div_div_eq_mul_div, div_lt_div_iff₀ hden (by norm_num)]
    nlinarith [hC0, hε]
  have hbcf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv)
    (clampBCF R hR0.le n)
  rw [Metric.tendsto_atTop] at hbcf
  obtain ⟨N, hN⟩ := hbcf (ε / 3) (by linarith)
  refine ⟨N, fun k hk => ?_⟩
  have h1 : |(∫ x : ℝ, x ^ n ∂((μ k : ProbabilityMeasure ℝ) : Measure ℝ)) -
      ∫ x : ℝ, clamp R x ^ n ∂((μ k : ProbabilityMeasure ℝ) : Measure ℝ)| ≤ C / R :=
    abs_integral_pow_sub_clamp_le hM (hμ k) n hR0
  have h2 : |(∫ x : ℝ, x ^ n ∂((ρ : ProbabilityMeasure ℝ) : Measure ℝ)) -
      ∫ x : ℝ, clamp R x ^ n ∂((ρ : ProbabilityMeasure ℝ) : Measure ℝ)| ≤ C / R :=
    abs_integral_pow_sub_clamp_le hM hρ n hR0
  have h3 := hN k hk
  rw [Real.dist_eq] at h3 ⊢
  have hval : ∀ σ : ProbabilityMeasure ℝ,
      ∫ x : ℝ, (clampBCF R hR0.le n) x ∂(σ : Measure ℝ) =
        ∫ x : ℝ, clamp R x ^ n ∂(σ : Measure ℝ) := fun σ => rfl
  rw [hval, hval] at h3
  have habs1 := abs_le.mp h1
  have habs2 := abs_le.mp h2
  have habs3 := abs_lt.mp h3
  rw [abs_lt]
  constructor <;> linarith

/-- **Method of moments.**  Convergence of every moment to the moments of a measure with a
factorial-geometric moment bound, along a sequence obeying that bound uniformly, is weak
convergence. -/
theorem tendsto_of_tendsto_moments {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {M : ℝ} (hM : 0 < M)
    (hμ : ∀ k, HasFactorialMomentBound ((μ k : ProbabilityMeasure ℝ) : Measure ℝ) M)
    (hν : HasFactorialMomentBound ((ν : ProbabilityMeasure ℝ) : Measure ℝ) M)
    (hmom : ∀ n : ℕ, Tendsto
      (fun k => ∫ x : ℝ, x ^ n ∂((μ k : ProbabilityMeasure ℝ) : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, x ^ n ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ)))) :
    Tendsto μ atTop (𝓝 ν) := by
  have htight : IsTightMeasureSet
      {x | ∃ σ ∈ Set.range μ, ((σ : ProbabilityMeasure ℝ) : Measure ℝ) = x} := by
    refine isTightMeasureSet_of_factorialMomentBound (M := M) ?_
    rintro σ ⟨k, rfl⟩
    exact hμ k
  have hcompact : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet htight
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hmem : ∀ j : ℕ, μ (ns j) ∈ closure (Set.range μ) := fun j =>
    subset_closure ⟨ns j, rfl⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
  refine ⟨φ, ?_⟩
  have hsub : Tendsto (fun j => μ (ns (φ j))) atTop (𝓝 a) := hlim
  have hbound : ∀ j : ℕ,
      HasFactorialMomentBound ((μ (ns (φ j)) : ProbabilityMeasure ℝ) : Measure ℝ) M :=
    fun j => hμ (ns (φ j))
  have habound := hasFactorialMomentBound_of_tendsto hM.le hbound hsub
  have hamom : ∀ n : ℕ, ∫ x : ℝ, x ^ n ∂((a : ProbabilityMeasure ℝ) : Measure ℝ) =
      ∫ x : ℝ, x ^ n ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ) := by
    intro n
    have hA := tendsto_integral_pow_of_tendsto hM.le hbound hsub n
    have hB : Tendsto (fun j => ∫ x : ℝ, x ^ n ∂((μ (ns (φ j)) : ProbabilityMeasure ℝ)
        : Measure ℝ)) atTop
        (𝓝 (∫ x : ℝ, x ^ n ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ))) :=
      ((hmom n).comp hns).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique hA hB
  have heq : ((a : ProbabilityMeasure ℝ) : Measure ℝ) =
      ((ν : ProbabilityMeasure ℝ) : Measure ℝ) :=
    HTGeometry.measure_eq_of_moments_eq_of_bilateral_exponential_window
      (zero_mem_interior_integrableExpSet hM habound)
      (zero_mem_interior_integrableExpSet hM hν) hamom
  have hae : a = ν := ProbabilityMeasure.toMeasure_injective heq
  rw [← hae]
  exact hsub

end WeakLimits

end

end GaloisForLFunctions.HTGeometry
