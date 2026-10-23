import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanDefectCountsTheOuterEigenvalues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheKroneckerRankDichotomy
import GaloisForLFunctions.RHTower.ZeroLatticeDepthNyquistLaw
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# The scaling surface of a curve: three Hodge index theorems over `𝔽_q`

The zeta function of a curve datum has the zeros `ρ` of `Π_i (1 − β_i q^{½−s})`, i.e.
`q^{ρ − ½} = β_i` (`mem_curveConfig_iff`). In Weil's normalization they are the points
(`zetaZero`, `cpow_zetaZero`)

    ρ_{i,k} = ½ + log|β_i|/log q + i (arg β_i + 2πk)/log q,   k ∈ ℤ,

a configuration periodic in height with period `2π/log q` (`zetaZero_add_period`). For data in the
strip (`|β_i| ≤ √q`, the condition for the zeros to lie in `0 ≤ Re ρ ≤ 1`) they form a tempered
zero configuration (`curveConfig`, `temperedConfig_curveConfig`), with multiplicity
`#{i : β_i = q^{ρ−½}}` and the reflection `ρ ↦ 1 − ρ̄` induced by `β ↦ 1/β̄`
(`reflect_zetaZero`). Its right zeros are the vertical translates of the eigenvalues outside the
unit circle (`re_zetaZero_gt_iff`).

**Theorem** (`curve_hodgeIndex_tfae`). For a curve datum in the strip the following are
equivalent:

1. RH for the datum, `|β_i| = 1` for all `i`;
2. Hodge index on the Frobenius window `Γ₀, …, Γ_{2g−1}` (`unitary_iff_negIndex_spanGram_eq_zero`);
3. Hodge index of the scaling surface: Weil's form of the zero configuration has no negative square
   on any finite family of `C²` compactly supported tests.

The defects differ: the Frobenius span has defect `#{distinct β : |β| > 1}` (`pontryagin_law_curve`),
while the scaling surface has defect `0` or `∞` (`curveConfig_rightZeros_infinite_iff`): each outer
eigenvalue reappears as a negative square once per period, because continuous tests separate the
vertical translates that the Frobenius graphs identify. The span is the quotient of the scaling
surface by the period; this is Kronecker rank one (`periodic_pontryagin_dichotomy`). For `ζ` there
is no period, and the two counts are not related by a quotient.
-/

open Complex Finset
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

theorem log_q_pos : 0 < Real.log D.q := Real.log_pos D.one_lt_q

/-- The vertical period `2π / log q` of the zeros. -/
def period : ℝ := 2 * π / Real.log D.q

theorem period_pos : 0 < D.period := div_pos (by positivity) D.log_q_pos

/-- The zero `ρ_{i,k}` of the zeta function attached to `β_i` in the `k`-th period. -/
def zetaZero (i : ι) (k : ℤ) : ℂ :=
  ⟨1 / 2 + Real.log ‖D.β i‖ / Real.log D.q, arg (D.β i) / Real.log D.q + k * D.period⟩

theorem re_zetaZero (i : ι) (k : ℤ) :
    (D.zetaZero i k).re = 1 / 2 + Real.log ‖D.β i‖ / Real.log D.q := rfl

theorem im_zetaZero (i : ι) (k : ℤ) :
    (D.zetaZero i k).im = arg (D.β i) / Real.log D.q + k * D.period := rfl

theorem norm_β_fePerm (i : ι) : ‖D.β (D.fePerm i)‖ = ‖D.β i‖⁻¹ := by
  have h := congrArg norm (D.β_fePerm i)
  rw [norm_mul, norm_one] at h
  exact eq_inv_of_mul_eq_one_left h

/-- `log q · (ρ_{i,k} − ½) = log β_i + 2πik`. -/
theorem log_q_mul_zetaZero (i : ι) (k : ℤ) :
    (Real.log D.q : ℂ) * (D.zetaZero i k - 1 / 2) = log (D.β i) + k * (2 * π * I) := by
  have hl := D.log_q_pos.ne'
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im, re_zetaZero, im_zetaZero, Complex.add_re, Complex.log_re,
      Complex.intCast_re, Complex.intCast_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    norm_num
    field_simp
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im, re_zetaZero, im_zetaZero, Complex.add_im, Complex.log_im,
      Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.I_re, Complex.I_im, period]
    norm_num
    field_simp

/-- **`ρ_{i,k}` is a zero**: `q^{ρ_{i,k} − ½} = β_i`. -/
theorem cpow_zetaZero (i : ι) (k : ℤ) : (D.q : ℂ) ^ (D.zetaZero i k - 1 / 2) = D.β i := by
  have hq : (D.q : ℂ) ≠ 0 := by
    exact_mod_cast (show D.q ≠ 0 by linarith [D.one_lt_q])
  rw [cpow_def_of_ne_zero hq, ← Complex.ofReal_log (by linarith [D.one_lt_q]),
    log_q_mul_zetaZero, Complex.exp_add, Complex.exp_log (D.β_ne_zero i),
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Every solution of `q^{ρ − ½} = β_i` is some `ρ_{i,k}`. -/
theorem exists_zetaZero_eq {ρ : ℂ} {i : ι} (h : (D.q : ℂ) ^ (ρ - 1 / 2) = D.β i) :
    ∃ k : ℤ, D.zetaZero i k = ρ := by
  have hq : (D.q : ℂ) ≠ 0 := by
    exact_mod_cast (show D.q ≠ 0 by linarith [D.one_lt_q])
  have hl := D.log_q_pos.ne'
  rw [cpow_def_of_ne_zero hq, ← Complex.exp_log (D.β_ne_zero i), Complex.exp_eq_exp_iff_exists_int,
    ← Complex.ofReal_log (by linarith [D.one_lt_q])] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have e := (D.log_q_mul_zetaZero i k).trans (hk.symm)
  have hl' : (Real.log D.q : ℂ) ≠ 0 := by exact_mod_cast hl
  have := mul_left_cancel₀ hl' e
  linear_combination this

/-- The circle reflection of the eigenvalues is the reflection `ρ ↦ 1 − ρ̄` of the zeros. -/
theorem reflect_zetaZero (i : ι) (k : ℤ) :
    reflect (D.zetaZero i k) = D.zetaZero (D.reflPerm i) k := by
  have hβ := D.β_reflPerm i
  have hnorm : ‖D.β (D.reflPerm i)‖ = ‖D.β i‖⁻¹ := by rw [hβ, norm_circleReflect]
  have harg : arg (D.β (D.reflPerm i)) = arg (D.β i) := by
    rw [hβ, circleReflect, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj]
    exact Complex.arg_mul_real (inv_pos.mpr (Complex.normSq_pos.mpr (D.β_ne_zero i))) _
  apply Complex.ext
  · simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re, re_zetaZero, hnorm,
      Real.log_inv]
    ring
  · simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im, im_zetaZero, harg]
    ring

/-- The zeros are periodic in height. -/
theorem zetaZero_add_period (i : ι) (k : ℤ) :
    D.zetaZero i k + I * D.period = D.zetaZero i (k + 1) := by
  apply Complex.ext
  · simp [re_zetaZero]
  · simp only [Complex.add_im, im_zetaZero, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    push_cast
    ring

/-- A zero lies right of the line iff its eigenvalue lies outside the unit circle. -/
theorem re_zetaZero_gt_iff (i : ι) (k : ℤ) : 1 / 2 < (D.zetaZero i k).re ↔ 1 < ‖D.β i‖ := by
  rw [re_zetaZero, lt_add_iff_pos_right, div_pos_iff_of_pos_right D.log_q_pos]
  constructor
  · intro h
    by_contra hle
    exact absurd h (not_lt.mpr (Real.log_nonpos (norm_nonneg _) (not_lt.mp hle)))
  · exact Real.log_pos

/-- The `ε`-bound on heights used for temperedness: `(k · period/2)² ≤ (Im ρ_{i,k})²`. -/
theorem sq_le_sq_im_zetaZero (i : ι) (k : ℤ) :
    ((k : ℝ) * (D.period / 2)) ^ 2 ≤ (D.zetaZero i k).im ^ 2 := by
  have hP := D.period_pos
  have harg : |arg (D.β i) / Real.log D.q| ≤ D.period / 2 := by
    rw [abs_div, abs_of_pos D.log_q_pos, period, div_le_iff₀ D.log_q_pos]
    have := Complex.abs_arg_le_pi (D.β i)
    have hl := D.log_q_pos.ne'
    field_simp
    linarith
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [Int.cast_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    positivity
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
    have hkh : |(k : ℝ) * D.period| = |(k : ℝ)| * D.period := by
      rw [abs_mul, abs_of_pos hP]
    have htri : |(k : ℝ) * D.period| ≤ |(D.zetaZero i k).im| + |arg (D.β i) / Real.log D.q| := by
      rw [im_zetaZero]
      calc |(k : ℝ) * D.period|
          = |(arg (D.β i) / Real.log D.q + k * D.period) - arg (D.β i) / Real.log D.q| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have hlow : |(k : ℝ)| * (D.period / 2) ≤ |(D.zetaZero i k).im| := by nlinarith
    have h0 : 0 ≤ |(k : ℝ)| * (D.period / 2) := by positivity
    calc ((k : ℝ) * (D.period / 2)) ^ 2 = (|(k : ℝ)| * (D.period / 2)) ^ 2 := by
          rw [mul_pow, mul_pow, sq_abs]
      _ ≤ |(D.zetaZero i k).im| ^ 2 := pow_le_pow_left₀ h0 hlow 2
      _ = (D.zetaZero i k).im ^ 2 := sq_abs _

/-! ### The zero configuration -/

open scoped Classical in
/-- **The zero configuration of a curve datum in the strip.** Carrier: the points `ρ_{i,k}`;
multiplicity: `#{i : β_i = q^{ρ − ½}}`. -/
def curveConfig (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) : ZeroConfig where
  carrier := Set.range fun p : ι × ℤ => D.zetaZero p.1 p.2
  mult ρ := (univ.filter fun i => (D.q : ℂ) ^ (ρ - 1 / 2) = D.β i).card
  one_le_mult := by
    rintro _ ⟨⟨i, k⟩, rfl⟩
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.cpow_zetaZero i k⟩⟩
  strip := by
    rintro _ ⟨⟨i, k⟩, rfl⟩
    have hl := D.log_q_pos
    have hsq : Real.log D.sqrtq = Real.log D.q / 2 := Real.log_sqrt (by linarith [D.one_lt_q])
    have hpos : 0 < ‖D.β i‖ := norm_pos_iff.mpr (D.β_ne_zero i)
    have hup : Real.log ‖D.β i‖ ≤ Real.log D.q / 2 := by
      rw [← hsq]; exact Real.log_le_log hpos (hD i)
    have hlow : -Real.log ‖D.β i‖ ≤ Real.log D.q / 2 := by
      have := hD (D.fePerm i)
      rw [norm_β_fePerm] at this
      rw [← hsq, ← Real.log_inv]
      exact Real.log_le_log (inv_pos.mpr hpos) this
    simp only [re_zetaZero]
    constructor
    · have : -(1 / 2 : ℝ) ≤ Real.log ‖D.β i‖ / Real.log D.q := by
        rw [le_div_iff₀ hl]; linarith
      linarith
    · have : Real.log ‖D.β i‖ / Real.log D.q ≤ 1 / 2 := by
        rw [div_le_iff₀ hl]; linarith
      linarith
  reflect_mem := by
    rintro _ ⟨⟨i, k⟩, rfl⟩
    exact ⟨⟨D.reflPerm i, k⟩, (D.reflect_zetaZero i k).symm⟩
  mult_reflect := by
    rintro _ ⟨⟨i, k⟩, rfl⟩
    rw [D.reflect_zetaZero, D.cpow_zetaZero, D.cpow_zetaZero]
    refine Finset.card_bij (fun j _ => D.reflPerm j) (fun j hj => ?_)
      (fun _ _ _ _ h => D.reflPerm.injective h) (fun j hj => ⟨D.reflPerm.symm j, ?_, by simp⟩)
    · have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [D.β_reflPerm j, ← hj', D.β_reflPerm, circleReflect_circleReflect]
    · have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h1 : D.β j = circleReflect (D.β (D.reflPerm.symm j)) := by
        rw [← D.β_reflPerm, Equiv.apply_symm_apply]
      rw [D.β_reflPerm, hj', h1, circleReflect_circleReflect]
  finite_window := by
    intro T₁ T₂
    refine (Set.finite_iUnion fun i : ι => (RHTower.finite_latticeWindow D.period_pos
      (T₁ - arg (D.β i) / Real.log D.q) (T₂ - arg (D.β i) / Real.log D.q)).image
        (D.zetaZero i)).subset ?_
    rintro _ ⟨⟨⟨i, k⟩, rfl⟩, h1, h2⟩
    refine Set.mem_iUnion.mpr ⟨i, k, ⟨?_, ?_⟩, rfl⟩
    · simp only [im_zetaZero] at h1; linarith
    · simp only [im_zetaZero] at h2; linarith

variable (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

theorem mem_curveConfig_iff {ρ : ℂ} :
    ρ ∈ (D.curveConfig hD).carrier ↔ ∃ i, (D.q : ℂ) ^ (ρ - 1 / 2) = D.β i := by
  constructor
  · rintro ⟨⟨i, k⟩, rfl⟩
    exact ⟨i, D.cpow_zetaZero i k⟩
  · rintro ⟨i, h⟩
    obtain ⟨k, hk⟩ := D.exists_zetaZero_eq h
    exact ⟨⟨i, k⟩, hk⟩

theorem curveConfig_mult_le (ρ : ℂ) : (D.curveConfig hD).mult ρ ≤ Fintype.card ι :=
  (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- The weight of `ρ_{i,k}` in the temperedness sum is at most `C/(1 + |k|)²`. -/
theorem curveWeight_le (i : ι) (k : ℤ) :
    ((D.curveConfig hD).mult (D.zetaZero i k) : ℝ) /
        (1 + Complex.normSq (gammaOf (D.zetaZero i k))) ≤
      Fintype.card ι * (2 / min 1 ((D.period / 2) ^ 2)) * (1 / (1 + |(k : ℝ)|) ^ 2) := by
  set c := D.period / 2 with hc
  have hc0 : 0 < c := by have := D.period_pos; positivity
  set m := min 1 (c ^ 2) with hm
  have hm0 : 0 < m := lt_min one_pos (by positivity)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hm2 : m ≤ c ^ 2 := min_le_right _ _
  have hmult : ((D.curveConfig hD).mult (D.zetaZero i k) : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast D.curveConfig_mult_le hD _
  -- `|γ|² ≥ (Im ρ)²` and `(Im ρ_{i,k})² ≥ (k c)²`
  have hγ : (D.zetaZero i k).im ^ 2 ≤ Complex.normSq (gammaOf (D.zetaZero i k)) := by
    rw [gammaOf, Complex.normSq_div, Complex.normSq_I, div_one, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    norm_num
    nlinarith [sq_nonneg ((D.zetaZero i k).re - 1 / 2)]
  have hk : ((k : ℝ) * c) ^ 2 ≤ (D.zetaZero i k).im ^ 2 := D.sq_le_sq_im_zetaZero i k
  set x : ℝ := (k : ℝ)
  set N := Complex.normSq (gammaOf (D.zetaZero i k))
  have hN : 0 ≤ N := Complex.normSq_nonneg _
  have hsq : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  have hcx : m * x ^ 2 ≤ (x * c) ^ 2 := by rw [mul_pow]; nlinarith [sq_nonneg x]
  have h2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ m / 2 by linarith)
  have hlow : m / 2 * (1 + |x|) ^ 2 ≤ 1 + N := by nlinarith
  have hden : 0 < 1 + N := by linarith
  have hpos : 0 < (1 + |x|) ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  calc ((D.curveConfig hD).mult (D.zetaZero i k) : ℝ) ≤ Fintype.card ι := hmult
    _ = Fintype.card ι * (2 / m) * (1 / (1 + |x|) ^ 2) * (m / 2 * (1 + |x|) ^ 2) := by
        field_simp
    _ ≤ Fintype.card ι * (2 / m) * (1 / (1 + |x|) ^ 2) * (1 + N) := by gcongr

/-- **The zero configuration of a curve is tempered.** -/
theorem temperedConfig_curveConfig : TemperedConfig (D.curveConfig hD) := by
  have hex : ∀ ρ : (D.curveConfig hD).carrier, ∃ p : ι × ℤ, D.zetaZero p.1 p.2 = ρ :=
    fun ρ => ρ.2
  choose e he using hex
  have hinj : Function.Injective e := fun ρ σ h => Subtype.ext (by rw [← he ρ, ← he σ, h])
  set C : ℝ := Fintype.card ι * (2 / min 1 ((D.period / 2) ^ 2))
  have h1 : Summable fun _ : ι => (1 : ℝ) := (hasSum_fintype fun _ : ι => (1 : ℝ)).summable
  have hg : Summable fun p : ι × ℤ => C * (1 * (1 / (1 + |(p.2 : ℝ)|) ^ 2)) :=
    (h1.mul_of_nonneg RHTower.hasSum_inv_one_add_abs_sq.summable (fun _ => zero_le_one)
      (fun _ => by positivity)).mul_left C
  have hF : Summable fun p : ι × ℤ => ((D.curveConfig hD).mult (D.zetaZero p.1 p.2) : ℝ) /
      (1 + Complex.normSq (gammaOf (D.zetaZero p.1 p.2))) := by
    refine Summable.of_nonneg_of_le (fun p => div_nonneg (Nat.cast_nonneg _)
      (add_nonneg zero_le_one (Complex.normSq_nonneg _))) (fun p => ?_) hg
    rw [one_mul]
    exact D.curveWeight_le hD p.1 p.2
  refine (hF.comp_injective hinj).congr fun ρ => ?_
  simp only [Function.comp_apply, he ρ]

theorem rightZeros_curveConfig_nonempty_iff :
    (rightZeros (D.curveConfig hD)).Nonempty ↔ D.outerSpectrum.Nonempty := by
  constructor
  · rintro ⟨_, ⟨⟨i, k⟩, rfl⟩, hre⟩
    exact ⟨D.β i, D.mem_outerSpectrum ((D.re_zetaZero_gt_iff i k).mp hre)⟩
  · rintro ⟨z, hz⟩
    obtain ⟨hzs, hz1⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hzs
    exact ⟨D.zetaZero i 0, ⟨⟨i, 0⟩, rfl⟩, (D.re_zetaZero_gt_iff i 0).mpr hz1⟩

theorem curveConfig_periodic :
    ∀ ρ ∈ (D.curveConfig hD).carrier, ρ + I * D.period ∈ (D.curveConfig hD).carrier := by
  rintro _ ⟨⟨i, k⟩, rfl⟩
  exact ⟨⟨i, k + 1⟩, (D.zetaZero_add_period i k).symm⟩

/-- **The scaling surface of a curve overcounts.** Its Hodge defect is infinite as soon as one
eigenvalue lies outside the unit circle, while the Frobenius span sees each such eigenvalue once. -/
theorem curveConfig_rightZeros_infinite_iff :
    (rightZeros (D.curveConfig hD)).Infinite ↔ D.outerSpectrum.Nonempty := by
  refine ⟨fun h => (D.rightZeros_curveConfig_nonempty_iff hD).mp h.nonempty, fun h => ?_⟩
  exact rightZeros_infinite_of_recurrent _
    (verticallyRecurrent_of_periodic _ D.period_pos (D.curveConfig_periodic hD))
    ((D.rightZeros_curveConfig_nonempty_iff hD).mpr h)

theorem nonempty_outerSpectrum_iff : D.outerSpectrum.Nonempty ↔ ¬ ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · rintro ⟨z, hz⟩ hU
    obtain ⟨hzs, hz1⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hzs
    rw [hU i] at hz1
    exact lt_irrefl _ hz1
  · intro hU
    push Not at hU
    obtain ⟨i, hi⟩ := hU
    rcases lt_or_gt_of_ne hi with h | h
    · refine ⟨_, D.mem_outerSpectrum (i := D.fePerm i) ?_⟩
      rw [norm_β_fePerm]
      exact (one_lt_inv₀ (norm_pos_iff.mpr (D.β_ne_zero i))).mpr h
    · exact ⟨_, D.mem_outerSpectrum h⟩

/-- **Three Hodge index theorems over `𝔽_q`.** For a curve datum in the strip, RH for the datum,
Hodge index on the Frobenius window of length `2g`, and Hodge index of the scaling surface (no
negative square of Weil's form on any finite family of tests) are equivalent. -/
theorem curve_hodgeIndex_tfae :
    [∀ i, ‖D.β i‖ = 1,
      hermNegIndex (D.spanGram (Fintype.card ι)) = 0,
      ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
        hermNegIndex (zeroGram (D.curveConfig hD) f) = 0].TFAE := by
  tfae_have 1 ↔ 2 := D.unitary_iff_negIndex_spanGram_eq_zero
  tfae_have 1 → 3 := by
    intro hU n f hf hfc
    have hR : rightZeros (D.curveConfig hD) = ∅ := by
      by_contra hne
      exact (D.nonempty_outerSpectrum_iff.mp
        ((D.rightZeros_curveConfig_nonempty_iff hD).mp (Set.nonempty_iff_ne_empty.mpr hne))) hU
    have h := negIndex_zeroGram_le_of_tempered _ (D.temperedConfig_curveConfig hD) f hf hfc
    rw [hR, Set.encard_empty] at h
    have h0 : hermNegIndex (zeroGram (D.curveConfig hD) f) ≤ 0 := by exact_mod_cast h
    omega
  tfae_have 3 → 1 := by
    intro h3
    by_contra hU
    have hinf := (D.curveConfig_rightZeros_infinite_iff hD).mpr
      (D.nonempty_outerSpectrum_iff.mpr hU)
    obtain ⟨f, hf, hfc, hle⟩ := (pontryagin_law _ (D.temperedConfig_curveConfig hD) 1).mpr
      (by rw [Set.encard_eq_top_iff.mpr hinf]; exact le_top)
    have := h3 1 f hf hfc
    omega
  tfae_finish

end CurveDatum

open Real in
/-- The golden datum lies in the strip: `φ ≤ √5`. -/
theorem goldenDatum_strip : ∀ i, ‖goldenDatum.β i‖ ≤ goldenDatum.sqrtq := by
  have hs : goldenDatum.sqrtq = Real.sqrt 5 := rfl
  have h5 : (2 : ℝ) ≤ Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  intro i
  rw [hs]
  fin_cases i
  · show ‖((goldenRatio : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg goldenRatio_pos.le]
    linarith [goldenRatio_lt_two]
  · show ‖((goldenRatio⁻¹ : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr goldenRatio_pos).le]
    linarith [inv_lt_one_of_one_lt₀ one_lt_goldenRatio]

/-- **The golden fake curve: span defect `1`, scaling defect `∞`.** -/
theorem goldenDatum_scaling_defect :
    (∀ n, 2 ≤ n → hermNegIndex (goldenDatum.spanGram n) = 1) ∧
      (rightZeros (goldenDatum.curveConfig goldenDatum_strip)).Infinite :=
  ⟨fun _ hn => goldenDatum_negIndex_spanGram hn,
    (goldenDatum.curveConfig_rightZeros_infinite_iff goldenDatum_strip).mpr
      (goldenDatum.nonempty_outerSpectrum_iff.mpr goldenDatum_not_unitary)⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
