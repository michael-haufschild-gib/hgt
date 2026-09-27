import GaloisForLFunctions.RHTower.DivisorContinuousHeadRegularity
import GaloisForLFunctions.RHTower.MobiusDivisorDilationMeanRenewal
import GaloisForLFunctions.RHTower.Sieve.SquarefreeCount

/-!
# One physical cutoff for every finite prime core

Let `U` be the continuous unit divisor head and `H_P(x) = ∑_{d ∣ ∏P} μ(d) √d U(x/d)` its finite
Möbius dilation.  Only the divisors `d ≤ x` contribute at `x`, each by at most `(3/5)√x`, and there
are at most `x` of them whatever `P` is, so `|H_P(x)| ≤ (3/5) x^{3/2}` uniformly in `P`.  Hence the
inverse-cube tail `∫_X^∞ |H_P|/x³` is at most `2/√X`, uniformly in the core.

Subtracting that tail from the core-uniform positive moment `m` gives a single physical cutoff
`X ≥ max(1, (4/m)²)` at which `∫_1^X H_P/x³ ≥ m/2` for every finite prime core.  The same holds for
the two-scale head `H_P(x) + A H_P(x/A)`, uniformly in `A ≥ 1`, at `X ≥ max(1, (8/m)²)`, and a
Cauchy–Schwarz step turns it into the synchronized energy bound
`E_P(X) + C_P(A; X/A)/A ≥ m²/4`, with `E_P(X) = ∫_1^X H_P²/x³` and
`C_P(A; Y) = ∫_1^Y H_P(Ax) H_P(x)/x³`.

Finally the insertion of a fresh prime `p` expands the density-weighted correlation drop exactly:
a positive main term of the synchronized shape at `A = p²`, plus the signed annular boundary term
`∫_{X/p}^X H_P(px) [H_P(x) + p^{3/2} H_P(x/p)]/x³`.  No sign is asserted for the annulus.
-/

noncomputable section
open MeasureTheory Set Finset Filter Topology
namespace RHTower

/-! ### The core-uniform envelope -/

/-- A finite Möbius-type dilation of the unit head, with coefficients of modulus at most one, has
the envelope `(3/5) x^{3/2}`: only the divisors `d ≤ x` contribute, each by at most `(3/5)√x`, and
there are at most `x` of them. -/
theorem abs_sum_dilation_unitHead_le (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d) (c : ℕ → ℝ)
    (hc : ∀ d, |c d| ≤ 1) (x : ℝ) :
    |∑ d ∈ D, c d * Real.sqrt d * divisorContinuousUnitHead (x / d)|
      ≤ 3 / 5 * x * Real.sqrt x := by
  classical
  rcases le_or_gt x 0 with hx | hx
  · have hz : ∀ d ∈ D, c d * Real.sqrt d * divisorContinuousUnitHead (x / d) = 0 := by
      intro d hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast hD d hd
      have hle : x / d ≤ 1 := (div_nonpos_of_nonpos_of_nonneg hx hdR.le).trans zero_le_one
      rw [divisorContinuousUnitHead_eq_zero hle, mul_zero]
    rw [Finset.sum_eq_zero hz, abs_zero, Real.sqrt_eq_zero'.mpr hx, mul_zero]
  have hsplit : ∑ d ∈ D with (d : ℝ) ≤ x, c d * Real.sqrt d * divisorContinuousUnitHead (x / d)
      = ∑ d ∈ D, c d * Real.sqrt d * divisorContinuousUnitHead (x / d) := by
    apply Finset.sum_filter_of_ne
    intro d hd hne
    by_contra hdx
    apply hne
    have hdR : (0 : ℝ) < d := by exact_mod_cast hD d hd
    rw [divisorContinuousUnitHead_eq_zero ((div_le_one hdR).mpr (le_of_not_ge hdx).le), mul_zero]
  rw [← hsplit]
  have hterm : ∀ d ∈ D with (d : ℝ) ≤ x,
      |c d * Real.sqrt d * divisorContinuousUnitHead (x / d)| ≤ 3 / 5 * Real.sqrt x := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hD d (Finset.mem_filter.mp hd).1
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (divisorContinuousUnitHead_nonneg _)]
    calc |c d| * Real.sqrt d * divisorContinuousUnitHead (x / d)
        ≤ 1 * Real.sqrt d * (3 / 5 * Real.sqrt (x / d)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (hc d) (Real.sqrt_nonneg _))
            (divisorContinuousUnitHead_le_sqrt _) (divisorContinuousUnitHead_nonneg _)
            (by positivity)
      _ = 3 / 5 * Real.sqrt x := by
          rw [Real.sqrt_div hx.le, one_mul]
          have hs : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hd0).ne'
          field_simp
  have hcard : ((D.filter (fun d => (d : ℝ) ≤ x)).card : ℝ) ≤ x := by
    have hsub : D.filter (fun d => (d : ℝ) ≤ x) ⊆ Finset.Icc 1 ⌊x⌋₊ := by
      intro d hd
      rw [Finset.mem_filter] at hd
      exact Finset.mem_Icc.mpr ⟨hD d hd.1, Nat.le_floor hd.2⟩
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    calc ((D.filter (fun d => (d : ℝ) ≤ x)).card : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ x := Nat.floor_le hx.le
  calc |∑ d ∈ D with (d : ℝ) ≤ x, c d * Real.sqrt d * divisorContinuousUnitHead (x / d)|
      ≤ ∑ d ∈ D with (d : ℝ) ≤ x, |c d * Real.sqrt d * divisorContinuousUnitHead (x / d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ D with (d : ℝ) ≤ x, 3 / 5 * Real.sqrt x := Finset.sum_le_sum hterm
    _ = ((D.filter (fun d => (d : ℝ) ≤ x)).card : ℝ) * (3 / 5 * Real.sqrt x) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ x * (3 / 5 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 3 / 5 * x * Real.sqrt x := by ring

/-- **The core-uniform envelope.**  `|H_P(x)| ≤ (3/5) x^{3/2}` for every finite core `P`. -/
theorem abs_mobiusDivisorContinuousHead_le (P : Finset ℕ) (x : ℝ) :
    |mobiusDivisorContinuousHead P x| ≤ 3 / 5 * x * Real.sqrt x := by
  unfold mobiusDivisorContinuousHead
  refine abs_sum_dilation_unitHead_le _ (fun d hd => Nat.pos_of_mem_divisors hd)
    (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) (fun d => ?_) x
  have h := ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [← Int.cast_abs]
  exact_mod_cast h

/-- The envelope, monotone form: on `[0, Y]` the head is at most `(3/5) Y^{3/2}`. -/
theorem abs_mobiusDivisorContinuousHead_le_of_le (P : Finset ℕ) {t Y : ℝ} (ht : t ≤ Y) :
    |mobiusDivisorContinuousHead P t| ≤ 3 / 5 * Y * Real.sqrt Y := by
  rcases le_or_gt t 0 with ht0 | ht0
  · rw [mobiusDivisorContinuousHead_eq_zero P (ht0.trans zero_le_one), abs_zero]
    have hY : 0 ≤ Y * Real.sqrt Y := by
      rcases le_or_gt Y 0 with hY | hY
      · rw [Real.sqrt_eq_zero'.mpr hY, mul_zero]
      · positivity
    linarith
  · refine (abs_mobiusDivisorContinuousHead_le P t).trans ?_
    have := mul_le_mul ht (Real.sqrt_le_sqrt ht) (Real.sqrt_nonneg _) (ht0.le.trans ht)
    nlinarith

/-- The inverse-cube weighted head is bounded by `3/5` on the whole line. -/
theorem abs_mobiusDivisorContinuousHead_div_cube_le (P : Finset ℕ) (x : ℝ) :
    |mobiusDivisorContinuousHead P x / x ^ 3| ≤ 3 / 5 := by
  rcases le_or_gt x 1 with hx | hx
  · rw [mobiusDivisorContinuousHead_eq_zero P hx, zero_div, abs_zero]
    norm_num
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hs1 : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx.le
  rw [abs_div, abs_of_pos (pow_pos hx0 3), div_le_iff₀ (pow_pos hx0 3)]
  refine (abs_mobiusDivisorContinuousHead_le P x).trans ?_
  have hsx : Real.sqrt x ≤ x := by
    rw [Real.sqrt_le_left hx0.le]
    nlinarith
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx.le
  nlinarith

/-- A product of two dilated heads, weighted by `x^{-3}`, is bounded on the whole line. -/
theorem abs_mobiusDivisorContinuousHead_mul_div_cube_le (P Q : Finset ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ) :
    |mobiusDivisorContinuousHead P (a * x) * mobiusDivisorContinuousHead Q (b * x) / x ^ 3|
      ≤ 9 / 25 * (a * b) * Real.sqrt (a * b) := by
  rcases le_or_gt x 0 with hx | hx
  · have hbx : b * x ≤ 1 := (mul_nonpos_of_nonneg_of_nonpos hb hx).trans zero_le_one
    rw [mobiusDivisorContinuousHead_eq_zero Q hbx, mul_zero, zero_div, abs_zero]
    positivity
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  rw [abs_div, abs_of_pos hx3, div_le_iff₀ hx3, abs_mul]
  have h1 := abs_mobiusDivisorContinuousHead_le P (a * x)
  have h2 := abs_mobiusDivisorContinuousHead_le Q (b * x)
  have hsq : Real.sqrt (a * x) * Real.sqrt (b * x) = Real.sqrt (a * b) * x := by
    rw [← Real.sqrt_mul (mul_nonneg ha hx.le),
      show a * x * (b * x) = (a * b) * x ^ 2 by ring,
      Real.sqrt_mul (mul_nonneg ha hb), Real.sqrt_sq hx.le]
  calc |mobiusDivisorContinuousHead P (a * x)| * |mobiusDivisorContinuousHead Q (b * x)|
      ≤ (3 / 5 * (a * x) * Real.sqrt (a * x)) * (3 / 5 * (b * x) * Real.sqrt (b * x)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
    _ = 9 / 25 * (a * b) * (Real.sqrt (a * x) * Real.sqrt (b * x)) * x ^ 2 := by ring
    _ = 9 / 25 * (a * b) * Real.sqrt (a * b) * x ^ 3 := by rw [hsq]; ring

/-! ### Integrability bookkeeping -/

/-- A measurable function bounded on `(a, b]` is integrable there. -/
theorem integrableOn_Ioc_of_abs_le {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} {a b : ℝ}
    (h : ∀ x ∈ Ioc a b, |f x| ≤ K) : IntegrableOn f (Ioc a b) :=
  Measure.integrableOn_of_bounded (M := K) measure_Ioc_lt_top.ne hf.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun x hx => by
      rw [Real.norm_eq_abs]; exact h x hx)))

theorem measurable_mobiusDivisorContinuousHead_comp_mul (P : Finset ℕ) (a : ℝ) :
    Measurable (fun x : ℝ => mobiusDivisorContinuousHead P (a * x)) :=
  (measurable_mobiusDivisorContinuousHead P).comp (measurable_const.mul measurable_id)

theorem measurable_div_cube {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun x : ℝ => f x / x ^ 3) :=
  hf.div (measurable_id.pow_const 3)

/-- Every weighted pair of dilated heads is integrable on every bounded interval. -/
theorem integrableOn_Ioc_head_mul_head_div_cube (P Q : Finset ℕ) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (s t : ℝ) :
    IntegrableOn (fun x : ℝ =>
      mobiusDivisorContinuousHead P (a * x) * mobiusDivisorContinuousHead Q (b * x) / x ^ 3)
      (Ioc s t) :=
  integrableOn_Ioc_of_abs_le
    (measurable_div_cube ((measurable_mobiusDivisorContinuousHead_comp_mul P a).mul
      (measurable_mobiusDivisorContinuousHead_comp_mul Q b)))
    (fun x _ => abs_mobiusDivisorContinuousHead_mul_div_cube_le P Q ha hb x)

/-- The weighted head is integrable on every bounded interval. -/
theorem integrableOn_Ioc_head_div_cube (P : Finset ℕ) (s t : ℝ) :
    IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P x / x ^ 3) (Ioc s t) :=
  integrableOn_Ioc_of_abs_le (measurable_div_cube (measurable_mobiusDivisorContinuousHead P))
    (fun x _ => abs_mobiusDivisorContinuousHead_div_cube_le P x)

/-! ### The uniform tail -/

private lemma cube_envelope_eq {x : ℝ} (hx : 0 < x) :
    x * Real.sqrt x / x ^ 3 = x ^ (-(3 / 2 : ℝ)) := by
  have h32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hx.le, h32]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  field_simp
  nlinarith [hss]

/-- **The inverse-cube tail of any function with envelope `c x^{3/2}`.**  It is integrable above
every positive cutoff, with tail at most `2c/√X`. -/
theorem integrableOn_abs_div_cube_Ioi_and_le {f : ℝ → ℝ} (hf : Measurable f) {c : ℝ}
    (hc : 0 ≤ c) (hb : ∀ x, |f x| ≤ c * x * Real.sqrt x) {X : ℝ} (hX : 0 < X) :
    IntegrableOn (fun x => |f x| / x ^ 3) (Ioi X) ∧
      ∫ x in Ioi X, |f x| / x ^ 3 ≤ 2 * c / Real.sqrt X := by
  have hrp : IntegrableOn (fun x : ℝ => c * x ^ (-(3 / 2 : ℝ))) (Ioi X) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hX).const_mul c
  have hpt : ∀ x ∈ Ioi X, |f x| / x ^ 3 ≤ c * x ^ (-(3 / 2 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := hX.trans hx
    rw [← cube_envelope_eq hx0, div_le_iff₀ (pow_pos hx0 3)]
    have := hb x
    have h3 : 0 < x ^ 3 := pow_pos hx0 3
    calc |f x| ≤ c * x * Real.sqrt x := this
      _ = c * (x * Real.sqrt x / x ^ 3) * x ^ 3 := by field_simp
  have hint : IntegrableOn (fun x => |f x| / x ^ 3) (Ioi X) := by
    refine Integrable.mono' hrp
      (measurable_div_cube (continuous_abs.measurable.comp hf)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _)
      (pow_pos (hX.trans hx) 3).le)]
    exact hpt x hx
  refine ⟨hint, ?_⟩
  calc ∫ x in Ioi X, |f x| / x ^ 3 ≤ ∫ x in Ioi X, c * x ^ (-(3 / 2 : ℝ)) :=
        setIntegral_mono_on hint hrp measurableSet_Ioi hpt
    _ = 2 * c / Real.sqrt X := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hX]
        have hsX : Real.sqrt X = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
        rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num, Real.rpow_neg hX.le, ← hsX]
        have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
        field_simp
        ring

/-- **The tail bound (2).**  For every finite core and every `X > 0`,
`∫_X^∞ |H_P(x)|/x³ dx ≤ 2/√X`. -/
theorem integral_abs_mobiusDivisorContinuousHead_tail_le (P : Finset ℕ) {X : ℝ} (hX : 0 < X) :
    ∫ x in Ioi X, |mobiusDivisorContinuousHead P x| / x ^ 3 ≤ 2 / Real.sqrt X := by
  have h := (integrableOn_abs_div_cube_Ioi_and_le (measurable_mobiusDivisorContinuousHead P)
    (by norm_num : (0 : ℝ) ≤ 3 / 5) (abs_mobiusDivisorContinuousHead_le P) hX).2
  refine h.trans ?_
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  rw [div_le_div_iff_of_pos_right hs]
  norm_num

/-! ### The core-uniform positive moment -/

/-- The core-uniform moment `m = exp(−2 ∑ n^{−3/2}) ∫_1^∞ U(x)/x³ dx`. -/
def mobiusDivisorUniformMoment : ℝ :=
  Real.exp (-2 * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ)) *
    ∫ x in Ioi (1 : ℝ), divisorContinuousUnitHead x / x ^ 3

theorem integral_Ioi_one_divisorContinuousUnitHead :
    (∫ x in Ioi (1 : ℝ), divisorContinuousUnitHead x / x ^ 3) =
      ∫ x in Ioi (0 : ℝ), divisorContinuousUnitHead x / x ^ 3 := by
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  intro x hx
  rw [divisorContinuousUnitHead_eq_zero (le_of_not_gt hx.2), zero_div]

theorem mobiusDivisorUniformMoment_pos : 0 < mobiusDivisorUniformMoment := by
  unfold mobiusDivisorUniformMoment
  rw [integral_Ioi_one_divisorContinuousUnitHead]
  exact mul_pos (Real.exp_pos _) integral_divisorContinuousUnitHead_moment_pos

/-- **The positive signed moment (1).**  `∫_1^∞ H_P/x³ ≥ m` for every finite prime core. -/
theorem mobiusDivisorUniformMoment_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    mobiusDivisorUniformMoment ≤ ∫ x in Ioi (1 : ℝ), mobiusDivisorContinuousHead P x / x ^ 3 := by
  unfold mobiusDivisorUniformMoment
  rw [integral_Ioi_one_divisorContinuousUnitHead,
    integral_mobiusDivisorContinuousHead_moment_Ioi_one]
  exact integral_mobiusDivisorContinuousHead_moment_uniform_lower P hP

/-- The truncated moment loses at most the tail: `∫_1^X H_P/x³ ≥ m − 2/√X` for `X ≥ 1`. -/
theorem mobiusDivisorUniformMoment_sub_tail_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {X : ℝ}
    (hX : 1 ≤ X) :
    mobiusDivisorUniformMoment - 2 / Real.sqrt X ≤
      ∫ x in Ioc 1 X, mobiusDivisorContinuousHead P x / x ^ 3 := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hiM : IntegrableOn (fun x => mobiusDivisorContinuousHead P x / x ^ 3) (Ioi 1) :=
    (integrable_mobiusDivisorContinuousHead_moment P).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hsplit : (∫ x in Ioi (1 : ℝ), mobiusDivisorContinuousHead P x / x ^ 3) =
      (∫ x in Ioc 1 X, mobiusDivisorContinuousHead P x / x ^ 3) +
        ∫ x in Ioi X, mobiusDivisorContinuousHead P x / x ^ 3 := by
    rw [← Ioc_union_Ioi_eq_Ioi hX]
    exact setIntegral_union (Set.disjoint_left.mpr (fun x hx hx' => not_lt.mpr hx.2 hx'))
      measurableSet_Ioi (hiM.mono_set (fun x hx => hx.1)) (hiM.mono_set (Ioi_subset_Ioi hX))
  have htail : ∫ x in Ioi X, mobiusDivisorContinuousHead P x / x ^ 3 ≤ 2 / Real.sqrt X := by
    have hab := (integrableOn_abs_div_cube_Ioi_and_le (measurable_mobiusDivisorContinuousHead P)
      (by norm_num : (0 : ℝ) ≤ 3 / 5) (abs_mobiusDivisorContinuousHead_le P) hX0).1
    refine (setIntegral_mono_on (hiM.mono_set (Ioi_subset_Ioi hX)) hab measurableSet_Ioi
      (fun x hx => ?_)).trans (integral_abs_mobiusDivisorContinuousHead_tail_le P hX0)
    exact div_le_div_of_nonneg_right (le_abs_self _) (pow_pos (hX0.trans hx) 3).le
  have hm := mobiusDivisorUniformMoment_le P hP
  linarith

private lemma two_div_sqrt_le {m c X : ℝ} (hm : 0 < m) (hc : 0 < c) (hX : (c / m) ^ 2 ≤ X) :
    2 / Real.sqrt X ≤ 2 * m / c := by
  have hcm : 0 < c / m := div_pos hc hm
  have hs : c / m ≤ Real.sqrt X := by
    rw [← Real.sqrt_sq hcm.le]
    exact Real.sqrt_le_sqrt hX
  calc 2 / Real.sqrt X ≤ 2 / (c / m) := div_le_div_of_nonneg_left (by norm_num) hcm hs
    _ = 2 * m / c := by field_simp

/-- **The single physical cutoff (3).**  For every `X ≥ max(1, (4/m)²)` and every finite prime
core, `∫_1^X H_P/x³ ≥ m/2`. -/
theorem mobiusDivisor_physicalCutoff_moment_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {X : ℝ} (hX : 1 ≤ X) (hXm : (4 / mobiusDivisorUniformMoment) ^ 2 ≤ X) :
    mobiusDivisorUniformMoment / 2 ≤ ∫ x in Ioc 1 X, mobiusDivisorContinuousHead P x / x ^ 3 := by
  have hm := mobiusDivisorUniformMoment_pos
  have h1 := mobiusDivisorUniformMoment_sub_tail_le P hP hX
  have h2 := two_div_sqrt_le hm (by norm_num : (0 : ℝ) < 4) hXm
  linarith

/-! ### Rescaling on the physical interval -/

/-- On `(1, Y]` and on `(0, Y]` the same integral, for integrands vanishing at and below one. -/
theorem setIntegral_Ioc_one_eq_intervalIntegral {G : ℝ → ℝ} (hG : ∀ y ≤ 1, G y = 0) {Y : ℝ}
    (hY : 0 ≤ Y) :
    ∫ x in Ioc 1 Y, G x / x ^ 3 = ∫ x in (0 : ℝ)..Y, G x / x ^ 3 := by
  rw [intervalIntegral.integral_of_le hY]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc_left zero_le_one)
  intro x hx
  have hx1 : x ≤ 1 := by
    by_contra h
    exact hx.2 ⟨lt_of_not_ge h, hx.1.2⟩
  rw [hG x hx1, zero_div]

/-- **Rescaling.**  For `F` vanishing at and below one and `B ≥ 1`,
`∫_1^X F(x/B)/x³ dx = B^{−2} ∫_1^{X/B} F(y)/y³ dy`, empty intervals giving zero. -/
theorem setIntegral_Ioc_one_comp_div {F : ℝ → ℝ} (hF : ∀ y ≤ 1, F y = 0) {B : ℝ} (hB : 1 ≤ B)
    (X : ℝ) :
    ∫ x in Ioc 1 X, F (x / B) / x ^ 3 = (B ^ 2)⁻¹ * ∫ y in Ioc 1 (X / B), F y / y ^ 3 := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  rcases lt_or_ge X 1 with hX | hX
  · have hXB : X / B ≤ 1 := (div_le_one hB0).mpr (hX.le.trans hB)
    rw [Ioc_eq_empty_of_le hX.le, Ioc_eq_empty_of_le hXB, Measure.restrict_empty,
      Measure.restrict_empty, integral_zero_measure, integral_zero_measure, mul_zero]
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hFB : ∀ y ≤ 1, F (y / B) = 0 := fun y hy => hF _ ((div_le_one hB0).mpr (hy.trans hB))
  rw [setIntegral_Ioc_one_eq_intervalIntegral hFB hX0,
    setIntegral_Ioc_one_eq_intervalIntegral hF (div_nonneg hX0 hB0.le)]
  have hpt : ∀ x : ℝ, F (x / B) / x ^ 3 = (B ^ 3)⁻¹ * (F (x / B) / (x / B) ^ 3) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · field_simp
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun y => F y / y ^ 3) hB0.ne', zero_div, smul_eq_mul]
  field_simp

/-! ### The two-scale moment -/

/-- The two-scale head `g_{P,A}(x) = H_P(x) + A H_P(x/A)`. -/
def mobiusDivisorTwoScaleHead (P : Finset ℕ) (A x : ℝ) : ℝ :=
  mobiusDivisorContinuousHead P x + A * mobiusDivisorContinuousHead P (x / A)

private lemma head_comp_div_eq_zero (P : Finset ℕ) {A : ℝ} (hA : 1 ≤ A) :
    ∀ y ≤ 1, mobiusDivisorContinuousHead P y = 0 :=
  fun _ hy => mobiusDivisorContinuousHead_eq_zero P hy

/-- The truncated moment of the rescaled head. -/
theorem setIntegral_Ioc_one_head_comp_div (P : Finset ℕ) {A : ℝ} (hA : 1 ≤ A) (X : ℝ) :
    ∫ x in Ioc 1 X, mobiusDivisorContinuousHead P (x / A) / x ^ 3 =
      (A ^ 2)⁻¹ * ∫ y in Ioc 1 (X / A), mobiusDivisorContinuousHead P y / y ^ 3 :=
  setIntegral_Ioc_one_comp_div (fun _ hy => mobiusDivisorContinuousHead_eq_zero P hy) hA X

/-- **The two-scale physical cutoff (4).**  For every `X ≥ max(1, (8/m)²)`, uniformly in the
finite prime core and in `A ≥ 1`, `∫_1^X g_{P,A}/x³ ≥ m/2`. -/
theorem mobiusDivisor_physicalCutoff_twoScale_moment_lower (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {A : ℝ} (hA : 1 ≤ A) {X : ℝ} (hX : 1 ≤ X)
    (hXm : (8 / mobiusDivisorUniformMoment) ^ 2 ≤ X) :
    mobiusDivisorUniformMoment / 2 ≤
      ∫ x in Ioc 1 X, mobiusDivisorTwoScaleHead P A x / x ^ 3 := by
  have hm := mobiusDivisorUniformMoment_pos
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hi1 := integrableOn_Ioc_head_div_cube P 1 X
  have hi2 : IntegrableOn (fun x => mobiusDivisorContinuousHead P (x / A) / x ^ 3) (Ioc 1 X) := by
    have h := integrableOn_Ioc_head_mul_head_div_cube P ∅ (inv_nonneg.mpr hA0.le)
      (zero_le_one) 1 X
    refine integrableOn_Ioc_of_abs_le
      (measurable_div_cube ((measurable_mobiusDivisorContinuousHead P).comp
        (measurable_id.div_const A))) (K := 3 / 5) (fun x hx => ?_)
    have hx0 : 0 < x := zero_lt_one.trans hx.1
    rcases le_or_gt (x / A) 1 with hxA | hxA
    · rw [mobiusDivisorContinuousHead_eq_zero P hxA, zero_div, abs_zero]; norm_num
    · have hxA' : x / A ≤ x := div_le_self hx0.le hA
      rw [abs_div, abs_of_pos (pow_pos hx0 3), div_le_iff₀ (pow_pos hx0 3)]
      have h1 := abs_mobiusDivisorContinuousHead_le_of_le P hxA'
      have hsx : Real.sqrt x ≤ x := by
        rw [Real.sqrt_le_left hx0.le]; nlinarith [hx.1]
      have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx.1.le
      nlinarith [Real.sqrt_nonneg x]
  have hsum : ∫ x in Ioc 1 X, mobiusDivisorTwoScaleHead P A x / x ^ 3 =
      (∫ x in Ioc 1 X, mobiusDivisorContinuousHead P x / x ^ 3) +
        A * ((A ^ 2)⁻¹ * ∫ y in Ioc 1 (X / A), mobiusDivisorContinuousHead P y / y ^ 3) := by
    rw [← setIntegral_Ioc_one_head_comp_div P hA X, ← integral_const_mul, ← integral_add hi1
      (hi2.const_mul A)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    simp only [mobiusDivisorTwoScaleHead]
    ring
  rw [hsum]
  have hmain := mobiusDivisorUniformMoment_sub_tail_le P hP hX
  have h8 := two_div_sqrt_le hm (by norm_num : (0 : ℝ) < 8) hXm
  rcases lt_or_ge (X / A) 1 with hXA | hXA
  · rw [Ioc_eq_empty_of_le hXA.le, Measure.restrict_empty, integral_zero_measure, mul_zero,
      mul_zero, add_zero]
    have : 2 * mobiusDivisorUniformMoment / 8 ≤ mobiusDivisorUniformMoment / 2 := by linarith
    linarith
  · have hsec := mobiusDivisorUniformMoment_sub_tail_le P hP hXA
    have hXA0 : 0 < X / A := zero_lt_one.trans_le hXA
    have hsXA : Real.sqrt X ≤ A * Real.sqrt (X / A) := by
      have h1 : Real.sqrt X = Real.sqrt A * Real.sqrt (X / A) := by
        rw [← Real.sqrt_mul hA0.le, mul_div_cancel₀ _ hA0.ne']
      have h2 : Real.sqrt A ≤ A := by
        rw [Real.sqrt_le_left hA0.le]; nlinarith
      rw [h1]
      exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
    have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
    have hsXA0 : 0 < Real.sqrt (X / A) := Real.sqrt_pos.mpr hXA0
    have hkey : A * ((A ^ 2)⁻¹ * ∫ y in Ioc 1 (X / A), mobiusDivisorContinuousHead P y / y ^ 3)
        ≥ -(2 / Real.sqrt X) := by
      have hA2 : A * (A ^ 2)⁻¹ = A⁻¹ := by field_simp
      rw [← mul_assoc, hA2]
      have hlow : A⁻¹ * (mobiusDivisorUniformMoment - 2 / Real.sqrt (X / A)) ≤
          A⁻¹ * ∫ y in Ioc 1 (X / A), mobiusDivisorContinuousHead P y / y ^ 3 :=
        mul_le_mul_of_nonneg_left hsec (inv_nonneg.mpr hA0.le)
      have hcmp : A⁻¹ * (2 / Real.sqrt (X / A)) ≤ 2 / Real.sqrt X := by
        rw [inv_mul_eq_div, div_div, div_le_div_iff₀ (by positivity) hsX]
        nlinarith [hsXA]
      have hmA : 0 ≤ A⁻¹ * mobiusDivisorUniformMoment := by positivity
      nlinarith [hlow, hcmp, hmA]
    linarith

/-! ### The synchronized energy -/

/-- The physical energy `E_P(X) = ∫_1^X H_P(x)²/x³ dx`. -/
def mobiusDivisorPhysicalEnergy (P : Finset ℕ) (X : ℝ) : ℝ :=
  ∫ x in Ioc 1 X, mobiusDivisorContinuousHead P x ^ 2 / x ^ 3

/-- The physical dilation correlation `C_P(A; Y) = ∫_1^Y H_P(Ax) H_P(x)/x³ dx`. -/
def mobiusDivisorPhysicalCorrelation (P : Finset ℕ) (A Y : ℝ) : ℝ :=
  ∫ x in Ioc 1 Y, mobiusDivisorContinuousHead P (A * x) * mobiusDivisorContinuousHead P x / x ^ 3

private lemma cube_weight_Ioc_le (X : ℝ) : ∫ x in Ioc 1 X, (1 : ℝ) / x ^ 3 ≤ 1 / 2 := by
  have heq : (fun x : ℝ => x ^ (-(3 : ℝ))) = fun x => 1 / x ^ (3 : ℕ) := by
    funext x
    rw [show (-(3 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg_natCast, one_div,
      zpow_neg, zpow_natCast]
  have hint : IntegrableOn (fun x : ℝ => (1 : ℝ) / x ^ 3) (Ioi 1) := by
    rw [← heq]; exact integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hval : ∫ x in Ioi (1 : ℝ), (1 : ℝ) / x ^ 3 = 1 / 2 := by
    rw [← heq, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]; norm_num
  rw [← hval]
  refine setIntegral_mono_set hint ?_ (ae_of_all _ (fun x hx => hx.1))
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
  exact div_nonneg zero_le_one (pow_pos (zero_lt_one.trans hx) 3).le

/-- **The synchronized energy law (5).**  For every `X ≥ max(1, (8/m)²)`, uniformly in the finite
prime core and in `A ≥ 1`, `E_P(X) + C_P(A; X/A)/A ≥ m²/4`. -/
theorem mobiusDivisor_physicalCutoff_synchronized_energy_lower (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {A : ℝ} (hA : 1 ≤ A) {X : ℝ} (hX : 1 ≤ X)
    (hXm : (8 / mobiusDivisorUniformMoment) ^ 2 ≤ X) :
    mobiusDivisorUniformMoment ^ 2 / 4 ≤
      mobiusDivisorPhysicalEnergy P X + mobiusDivisorPhysicalCorrelation P A (X / A) / A := by
  set m := mobiusDivisorUniformMoment with hmdef
  have hm : 0 < m := mobiusDivisorUniformMoment_pos
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  set H := mobiusDivisorContinuousHead P with hH
  have hHz : ∀ y ≤ 1, H y = 0 := fun y hy => mobiusDivisorContinuousHead_eq_zero P hy
  set g := mobiusDivisorTwoScaleHead P A with hg
  -- integrability of the three pieces of `g²`
  have hHx : ∀ x, H x = H (1 * x) := fun x => by rw [one_mul]
  have hi0 : IntegrableOn (fun x => H x ^ 2 / x ^ 3) (Ioc 1 X) := by
    have := integrableOn_Ioc_head_mul_head_div_cube P P zero_le_one zero_le_one 1 X
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp only [one_mul, hH]; ring
  have hi1 : IntegrableOn (fun x => H (A * (x / A)) * H (x / A) / x ^ 3) (Ioc 1 X) := by
    have := integrableOn_Ioc_head_mul_head_div_cube P P zero_le_one (inv_nonneg.mpr hA0.le) 1 X
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp only [one_mul, hH]
    rw [mul_div_cancel₀ _ hA0.ne', div_eq_inv_mul]
  have hi2 : IntegrableOn (fun x => H (x / A) ^ 2 / x ^ 3) (Ioc 1 X) := by
    have := integrableOn_Ioc_head_mul_head_div_cube P P (inv_nonneg.mpr hA0.le)
      (inv_nonneg.mpr hA0.le) 1 X
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp only [hH]
    rw [div_eq_inv_mul]; ring
  -- the expansion of the square
  have hexp : ∫ x in Ioc 1 X, g x ^ 2 / x ^ 3 =
      mobiusDivisorPhysicalEnergy P X + mobiusDivisorPhysicalEnergy P (X / A) +
        2 * mobiusDivisorPhysicalCorrelation P A (X / A) / A := by
    have hpt : ∀ x, g x ^ 2 / x ^ 3 = H x ^ 2 / x ^ 3 +
        (2 * A) * (H (A * (x / A)) * H (x / A) / x ^ 3) + A ^ 2 * (H (x / A) ^ 2 / x ^ 3) := by
      intro x
      simp only [hg, mobiusDivisorTwoScaleHead, hH]
      rw [mul_div_cancel₀ _ hA0.ne']
      ring
    simp_rw [hpt]
    rw [integral_add (hi0.add (hi1.const_mul _)) (hi2.const_mul _),
      integral_add hi0 (hi1.const_mul _), integral_const_mul, integral_const_mul]
    have hs1 := setIntegral_Ioc_one_comp_div (F := fun y => H (A * y) * H y)
      (fun y hy => by simp only; rw [hHz y hy, mul_zero]) hA X
    have hs2 := setIntegral_Ioc_one_comp_div (F := fun y => H y ^ 2)
      (fun y hy => by simp only; rw [hHz y hy]; ring) hA X
    simp only at hs1 hs2
    rw [hs1, hs2]
    simp only [mobiusDivisorPhysicalEnergy, mobiusDivisorPhysicalCorrelation, hH]
    field_simp
    ring
  -- Cauchy–Schwarz in the form `g² ≥ 2 m g − m²`
  have hig : IntegrableOn (fun x => g x / x ^ 3) (Ioc 1 X) := by
    have h1 := integrableOn_Ioc_head_div_cube P 1 X
    have h2 : IntegrableOn (fun x => H (x / A) * H (1 * x) / x ^ 3) (Ioc 1 X) := by
      have := integrableOn_Ioc_head_mul_head_div_cube P P (inv_nonneg.mpr hA0.le) zero_le_one 1 X
      refine this.congr_fun (fun x _ => ?_) measurableSet_Ioc
      simp only [hH]; rw [div_eq_inv_mul]
    -- `H(x/A)/x³` is bounded on `(1, X]`
    have h3 : IntegrableOn (fun x => H (x / A) / x ^ 3) (Ioc 1 X) := by
      refine integrableOn_Ioc_of_abs_le
        (measurable_div_cube ((measurable_mobiusDivisorContinuousHead P).comp
          (measurable_id.div_const A))) (K := 3 / 5 * X * Real.sqrt X) (fun x hx => ?_)
      have hx0 : 0 < x := zero_lt_one.trans hx.1
      have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx.1.le
      rw [abs_div, abs_of_pos (pow_pos hx0 3)]
      refine (div_le_self (abs_nonneg _) hx3).trans ?_
      exact abs_mobiusDivisorContinuousHead_le_of_le P
        ((div_le_self hx0.le hA).trans hx.2)
    refine (h1.add (h3.const_mul A)).congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp only [hg, mobiusDivisorTwoScaleHead, hH, Pi.add_apply]
    ring
  have hlin := mobiusDivisor_physicalCutoff_twoScale_moment_lower P hP hA hX hXm
  have hcw := cube_weight_Ioc_le X
  have hcwint : IntegrableOn (fun x : ℝ => (1 : ℝ) / x ^ 3) (Ioc 1 X) :=
    integrableOn_Ioc_of_abs_le (measurable_div_cube measurable_const) (K := 1) (fun x hx => by
      have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx.1.le
      rw [abs_div, abs_one, abs_of_pos (zero_lt_one.trans_le hx3)]
      exact div_le_one_of_le₀ hx3 (zero_le_one.trans hx3))
  have hig2 : IntegrableOn (fun x => g x ^ 2 / x ^ 3) (Ioc 1 X) := by
    have hpt : ∀ x, g x ^ 2 / x ^ 3 = H x ^ 2 / x ^ 3 +
        (2 * A) * (H (A * (x / A)) * H (x / A) / x ^ 3) + A ^ 2 * (H (x / A) ^ 2 / x ^ 3) := by
      intro x
      simp only [hg, mobiusDivisorTwoScaleHead, hH]
      rw [mul_div_cancel₀ _ hA0.ne']
      ring
    refine ((hi0.add (hi1.const_mul _)).add (hi2.const_mul _)).congr_fun
      (fun x _ => (hpt x).symm) measurableSet_Ioc
  have hcs : 2 * m * (∫ x in Ioc 1 X, g x / x ^ 3) - m ^ 2 * (∫ x in Ioc 1 X, (1 : ℝ) / x ^ 3)
      ≤ ∫ x in Ioc 1 X, g x ^ 2 / x ^ 3 := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hig.const_mul _)
      (hcwint.const_mul _)]
    refine setIntegral_mono_on ((hig.const_mul _).sub (hcwint.const_mul _)) hig2
      measurableSet_Ioc (fun x hx => ?_)
    have hx3 : 0 < x ^ 3 := pow_pos (zero_lt_one.trans hx.1) 3
    have hsq : 2 * m * g x - m ^ 2 ≤ g x ^ 2 := by nlinarith [sq_nonneg (g x - m)]
    have := div_le_div_of_nonneg_right hsq hx3.le
    simp only [Pi.sub_apply]
    calc 2 * m * (g x / x ^ 3) - m ^ 2 * (1 / x ^ 3) = (2 * m * g x - m ^ 2) / x ^ 3 := by
          ring
      _ ≤ g x ^ 2 / x ^ 3 := this
  -- monotonicity of the energy
  have hmono : mobiusDivisorPhysicalEnergy P (X / A) ≤ mobiusDivisorPhysicalEnergy P X := by
    unfold mobiusDivisorPhysicalEnergy
    refine setIntegral_mono_set hi0 ?_ (ae_of_all _ (fun x hx =>
      ⟨hx.1, hx.2.trans (div_le_self hX0.le hA)⟩))
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun x hx => ?_))
    exact div_nonneg (sq_nonneg _) (pow_pos (zero_lt_one.trans hx.1) 3).le
  rw [hexp] at hcs
  have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
  nlinarith [hcs, hlin, hcw, hmono, mul_le_mul_of_nonneg_left hcw hm2,
    mul_le_mul_of_nonneg_left hlin (by linarith : (0 : ℝ) ≤ 2 * m)]

/-! ### The prime-insertion correlation drop -/

/-- The core density `ρ_P = (squarefree density) ∏_{q ∈ P} q/(q+1)`. -/
def mobiusDivisorCoreDensity (P : Finset ℕ) : ℝ :=
  Sieve.squarefreeDensity * ∏ q ∈ P, (q : ℝ) / (q + 1)

/-- The density-weighted physical correlation drop at cutoff `X` for inserting `p`. -/
def mobiusDivisorPhysicalCorrelationDrop (P : Finset ℕ) (p : ℕ) (X : ℝ) : ℝ :=
  mobiusDivisorCoreDensity P * mobiusDivisorPhysicalCorrelation P p X -
    mobiusDivisorCoreDensity (insert p P) * mobiusDivisorPhysicalCorrelation (insert p P) p X

/-- **The exact insertion identity (6).**  For a fresh prime `p`,
`D_{P,p}(X) = ρ_P p√p/(p+1) [E_P(X) + C_P(p²; X/p)/p²] + ρ_P/(p+1) [C_P(p; X) − C_P(p; X/p)]`. -/
theorem mobiusDivisorPhysicalCorrelationDrop_eq (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) (X : ℝ) :
    mobiusDivisorPhysicalCorrelationDrop P p X =
      mobiusDivisorCoreDensity P * ((p : ℝ) * Real.sqrt p / (p + 1)) *
          (mobiusDivisorPhysicalEnergy P X +
            mobiusDivisorPhysicalCorrelation P ((p : ℝ) ^ 2) (X / p) / (p : ℝ) ^ 2) +
        mobiusDivisorCoreDensity P / (p + 1) *
          (mobiusDivisorPhysicalCorrelation P p X - mobiusDivisorPhysicalCorrelation P p (X / p)) := by
  set H := mobiusDivisorContinuousHead P with hH
  have hHz : ∀ y ≤ 1, H y = 0 := fun y hy => mobiusDivisorContinuousHead_eq_zero P hy
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hsp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hins : ∀ x, mobiusDivisorContinuousHead (insert p P) x = H x - Real.sqrt p * H (x / p) :=
    fun x => mobiusDivisorContinuousHead_insert P hP hp hpP x
  -- the four pieces
  have hi1 := integrableOn_Ioc_head_mul_head_div_cube P P hp0.le zero_le_one 1 X
  have hi2 : IntegrableOn (fun x => H ((p : ℝ) ^ 2 * (x / p)) * H (x / p) / x ^ 3) (Ioc 1 X) := by
    have := integrableOn_Ioc_head_mul_head_div_cube P P hp0.le (inv_nonneg.mpr hp0.le) 1 X
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp only [hH]
    rw [show (p : ℝ) ^ 2 * (x / p) = p * x by field_simp, div_eq_inv_mul x]
  have hi3 : IntegrableOn (fun x => H x ^ 2 / x ^ 3) (Ioc 1 X) := by
    have := integrableOn_Ioc_head_mul_head_div_cube P P zero_le_one zero_le_one 1 X
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp only [one_mul, hH]; ring
  have hi4 : IntegrableOn (fun x => H ((p : ℝ) * (x / p)) * H (x / p) / x ^ 3) (Ioc 1 X) := by
    have := integrableOn_Ioc_head_mul_head_div_cube P P zero_le_one (inv_nonneg.mpr hp0.le) 1 X
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp only [one_mul, hH]
    rw [mul_div_cancel₀ _ hp0.ne', div_eq_inv_mul x]
  have hcorr : mobiusDivisorPhysicalCorrelation (insert p P) p X =
      mobiusDivisorPhysicalCorrelation P p X -
        Real.sqrt p * ((((p : ℝ) ^ 2) ^ 2)⁻¹ * 0 +
          ((p : ℝ) ^ 2)⁻¹ * mobiusDivisorPhysicalCorrelation P ((p : ℝ) ^ 2) (X / p)) -
        Real.sqrt p * mobiusDivisorPhysicalEnergy P X +
        (p : ℝ) * (((p : ℝ) ^ 2)⁻¹ * mobiusDivisorPhysicalCorrelation P p (X / p)) := by
    have hpt : ∀ x, mobiusDivisorContinuousHead (insert p P) (p * x) *
        mobiusDivisorContinuousHead (insert p P) x / x ^ 3 =
        H (p * x) * H x / x ^ 3 - Real.sqrt p * (H ((p : ℝ) ^ 2 * (x / p)) * H (x / p) / x ^ 3) -
          Real.sqrt p * (H x ^ 2 / x ^ 3) +
          (p : ℝ) * (H ((p : ℝ) * (x / p)) * H (x / p) / x ^ 3) := by
      intro x
      rw [hins, hins, show (p : ℝ) * x / p = x by field_simp,
        show (p : ℝ) ^ 2 * (x / p) = p * x by field_simp, mul_div_cancel₀ _ hp0.ne']
      have : (p : ℝ) = Real.sqrt p * Real.sqrt p := hsp.symm
      rw [this]
      ring
    unfold mobiusDivisorPhysicalCorrelation
    simp_rw [hpt]
    rw [integral_add ((hi1.sub (hi2.const_mul _)).sub (hi3.const_mul _)) (hi4.const_mul _),
      integral_sub (hi1.sub (hi2.const_mul _)) (hi3.const_mul _),
      integral_sub hi1 (hi2.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul]
    have hs2 := setIntegral_Ioc_one_comp_div (F := fun y => H ((p : ℝ) ^ 2 * y) * H y)
      (fun y hy => by simp only; rw [hHz y hy, mul_zero]) hp1 X
    have hs4 := setIntegral_Ioc_one_comp_div (F := fun y => H ((p : ℝ) * y) * H y)
      (fun y hy => by simp only; rw [hHz y hy, mul_zero]) hp1 X
    simp only at hs2 hs4
    rw [hs2, hs4]
    simp only [mobiusDivisorPhysicalEnergy, hH]
    ring
  have hdens : mobiusDivisorCoreDensity (insert p P) =
      mobiusDivisorCoreDensity P * ((p : ℝ) / (p + 1)) := by
    unfold mobiusDivisorCoreDensity
    rw [Finset.prod_insert hpP]
    ring
  unfold mobiusDivisorPhysicalCorrelationDrop
  rw [hcorr, hdens]
  have hp1' : (p : ℝ) + 1 ≠ 0 := by positivity
  have hsp0 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt hp0.le
  field_simp
  ring

/-- **The annular boundary term (7).**  After rescaling, the two signed annuli left over in (6) —
the first bracket's defect from the synchronized law at `A = p²`, and the second bracket — combine
to one integral over `(X/p, X]`:
`p√p [C_P(p²; X/p) − C_P(p²; X/p²)]/p² + [C_P(p; X) − C_P(p; X/p)]
  = ∫_{X/p}^X H_P(px) [H_P(x) + p^{3/2} H_P(x/p)]/x³ dx`. -/
theorem mobiusDivisorPhysicalCorrelation_annulus_eq (P : Finset ℕ) {p : ℕ} (hp : p.Prime)
    {X : ℝ} (hX : 0 ≤ X) :
    (p : ℝ) * Real.sqrt p * (mobiusDivisorPhysicalCorrelation P ((p : ℝ) ^ 2) (X / p) -
        mobiusDivisorPhysicalCorrelation P ((p : ℝ) ^ 2) (X / p / p)) / (p : ℝ) ^ 2 +
      (mobiusDivisorPhysicalCorrelation P p X - mobiusDivisorPhysicalCorrelation P p (X / p)) =
    ∫ x in Ioc (X / p) X, mobiusDivisorContinuousHead P (p * x) *
      (mobiusDivisorContinuousHead P x +
        (p : ℝ) * Real.sqrt p * mobiusDivisorContinuousHead P (x / p)) / x ^ 3 := by
  set H := mobiusDivisorContinuousHead P with hH
  have hHz : ∀ y ≤ 1, H y = 0 := fun y hy => mobiusDivisorContinuousHead_eq_zero P hy
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hXp : X / p ≤ X := div_le_self hX hp1
  have hXp0 : 0 ≤ X / p := div_nonneg hX hp0.le
  -- a difference of physical integrals is the annulus
  have hdiff : ∀ G : ℝ → ℝ, (∀ y ≤ 1, G y = 0) → Measurable G → (∃ K, ∀ x, |G x / x ^ 3| ≤ K) →
      (∫ x in Ioc 1 X, G x / x ^ 3) - (∫ x in Ioc 1 (X / p), G x / x ^ 3) =
        ∫ x in Ioc (X / p) X, G x / x ^ 3 := by
    intro G hG hGm hGb
    obtain ⟨K, hK⟩ := hGb
    have hint : ∀ s t, IntegrableOn (fun x => G x / x ^ 3) (Ioc s t) := fun s t =>
      integrableOn_Ioc_of_abs_le (measurable_div_cube hGm) (fun x _ => hK x)
    rw [setIntegral_Ioc_one_eq_intervalIntegral hG hX,
      setIntegral_Ioc_one_eq_intervalIntegral hG hXp0,
      intervalIntegral.integral_interval_sub_left
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr (hint 0 X))
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hXp0).mpr (hint 0 (X / p))),
      intervalIntegral.integral_of_le hXp]
  have hm1 : Measurable (fun y => H ((p : ℝ) * y) * H y) :=
    (measurable_mobiusDivisorContinuousHead_comp_mul P _).mul
      (measurable_mobiusDivisorContinuousHead P)
  have hm2 : Measurable (fun y => H ((p : ℝ) * y) * H (y / p)) :=
    (measurable_mobiusDivisorContinuousHead_comp_mul P _).mul
      ((measurable_mobiusDivisorContinuousHead P).comp (measurable_id.div_const _))
  have hb1 : ∃ K, ∀ x, |H ((p : ℝ) * x) * H x / x ^ 3| ≤ K := by
    refine ⟨_, fun x => ?_⟩
    have := abs_mobiusDivisorContinuousHead_mul_div_cube_le P P hp0.le zero_le_one x
    rwa [one_mul] at this
  have hb2 : ∃ K, ∀ x, |H ((p : ℝ) * x) * H (x / p) / x ^ 3| ≤ K := by
    refine ⟨_, fun x => ?_⟩
    have := abs_mobiusDivisorContinuousHead_mul_div_cube_le P P hp0.le
      (inv_nonneg.mpr hp0.le) x
    rwa [← div_eq_inv_mul] at this
  have hz1 : ∀ y ≤ 1, H ((p : ℝ) * y) * H y = 0 := fun y hy => by rw [hHz y hy, mul_zero]
  have hz2 : ∀ y ≤ 1, H ((p : ℝ) * y) * H (y / p) = 0 := fun y hy => by
    rw [hHz (y / p) ((div_le_one hp0).mpr (hy.trans hp1)), mul_zero]
  have hA1 := hdiff _ hz1 hm1 hb1
  have hA2 := hdiff _ hz2 hm2 hb2
  -- rescaling identifies the `p²` correlations with the first annulus
  have hsc : ∀ Z, ∫ x in Ioc 1 Z, H ((p : ℝ) * x) * H (x / p) / x ^ 3 =
      ((p : ℝ) ^ 2)⁻¹ * mobiusDivisorPhysicalCorrelation P ((p : ℝ) ^ 2) (Z / p) := by
    intro Z
    have h := setIntegral_Ioc_one_comp_div (F := fun y => H ((p : ℝ) ^ 2 * y) * H y)
      (fun y hy => by simp only; rw [hHz y hy, mul_zero]) hp1 Z
    simp only at h
    unfold mobiusDivisorPhysicalCorrelation
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    simp only [hH]
    rw [show (p : ℝ) ^ 2 * (x / p) = p * x by field_simp]
  have hC1 : mobiusDivisorPhysicalCorrelation P p X - mobiusDivisorPhysicalCorrelation P p (X / p)
      = ∫ x in Ioc (X / p) X, H ((p : ℝ) * x) * H x / x ^ 3 := hA1
  have hC2 : ((p : ℝ) ^ 2)⁻¹ * (mobiusDivisorPhysicalCorrelation P ((p : ℝ) ^ 2) (X / p) -
      mobiusDivisorPhysicalCorrelation P ((p : ℝ) ^ 2) (X / p / p)) =
      ∫ x in Ioc (X / p) X, H ((p : ℝ) * x) * H (x / p) / x ^ 3 := by
    rw [mul_sub, ← hsc X, ← hsc (X / p)]
    exact hA2
  have hint1 : IntegrableOn (fun x => H ((p : ℝ) * x) * H x / x ^ 3) (Ioc (X / p) X) := by
    obtain ⟨K, hK⟩ := hb1
    exact integrableOn_Ioc_of_abs_le (measurable_div_cube hm1) (fun x _ => hK x)
  have hint2 : IntegrableOn (fun x => H ((p : ℝ) * x) * H (x / p) / x ^ 3) (Ioc (X / p) X) := by
    obtain ⟨K, hK⟩ := hb2
    exact integrableOn_Ioc_of_abs_le (measurable_div_cube hm2) (fun x _ => hK x)
  have hsplit : ∫ x in Ioc (X / p) X, H ((p : ℝ) * x) *
      (H x + (p : ℝ) * Real.sqrt p * H (x / p)) / x ^ 3 =
      (∫ x in Ioc (X / p) X, H ((p : ℝ) * x) * H x / x ^ 3) +
        (p : ℝ) * Real.sqrt p * ∫ x in Ioc (X / p) X, H ((p : ℝ) * x) * H (x / p) / x ^ 3 := by
    rw [← integral_const_mul, ← integral_add hint1 (hint2.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    ring
  rw [hsplit, ← hC1, ← hC2]
  ring

end RHTower
