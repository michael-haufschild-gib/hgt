import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!+# Phase resonance inside a normalized factor-two envelope

The smooth densities `1+t(sin(2u)-sin u)/2`, `|t|≤1`, have mean one
and bounded ordinary discrepancy primitives. Their centered dyadic Frullani
integrals nevertheless have logarithmic residue `t/2`. The relevant residue
is the mean of the density error times the oscillatory kernel numerator.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- A bounded primitive of the mean-subtracted numerator controls its logarithmic integral. -/
theorem logarithmicIntegral_residue_bound {h H : ℝ → ℝ} {m B R : ℝ}
    (hR : 1 ≤ R) (hc : ContinuousOn h (Set.Icc 1 R))
    (hd : ∀ u ∈ Set.Icc 1 R, HasDerivAt H (h u - m) u)
    (hB : ∀ u ∈ Set.Icc 1 R, |H u| ≤ B) :
    |(∫ u in (1 : ℝ)..R, h u / u) - m * Real.log R| ≤ 3 * B := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hB0 : 0 ≤ B := (abs_nonneg (H 1)).trans (hB 1 ⟨le_rfl, hR⟩)
  have hpos (u : ℝ) (hu : u ∈ Set.Icc 1 R) : 0 < u :=
    lt_of_lt_of_le zero_lt_one hu.1
  have hcH : ContinuousOn H (Set.Icc 1 R) :=
    fun u hu => (hd u hu).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun u => h u / u) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hR]
    exact hc.div continuousOn_id fun u hu => (hpos u hu).ne'
  have hiH : IntervalIntegrable (fun u => H u / u ^ 2) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hR]
    exact hcH.div (continuousOn_id.pow 2) fun u hu => pow_ne_zero 2 (hpos u hu).ne'
  have hiInv : IntervalIntegrable (fun u : ℝ => 1 / u ^ 2) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hR]
    exact continuousOn_const.div (continuousOn_id.pow 2)
      fun u hu => pow_ne_zero 2 (hpos u hu).ne'
  have hderiv (u : ℝ) (hu : u ∈ Set.uIcc 1 R) :
      HasDerivAt (fun u => H u / u + m * Real.log u)
        (h u / u - H u / u ^ 2) u := by
    rw [Set.uIcc_of_le hR] at hu
    have hu0 := (hpos u hu).ne'
    have hd' := ((hd u hu).div (hasDerivAt_id u) hu0).add
      ((Real.hasDerivAt_log hu0).const_mul m)
    apply hd'.congr_deriv
    simp only [id_eq]
    field_simp
    ring
  have hparts := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi.sub hiH)
  rw [intervalIntegral.integral_sub hi hiH] at hparts
  simp only [div_one, Real.log_one, mul_zero, add_zero] at hparts
  have hinv : (∫ u in (1 : ℝ)..R, 1 / u ^ 2) = 1 - 1 / R := by
    have hdinv (u : ℝ) (hu : u ∈ Set.uIcc 1 R) :
        HasDerivAt (fun u : ℝ => -(1 / u)) (1 / u ^ 2) u := by
      rw [Set.uIcc_of_le hR] at hu
      have hd' := ((hasDerivAt_const u (1 : ℝ)).div (hasDerivAt_id u)
        (hpos u hu).ne').neg
      apply hd'.congr_deriv
      simp only [id_eq]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hdinv hiInv]
    ring
  have htail : |∫ u in (1 : ℝ)..R, H u / u ^ 2| ≤ B := by
    calc
      _ ≤ ∫ u in (1 : ℝ)..R, |H u / u ^ 2| :=
        intervalIntegral.abs_integral_le_integral_abs hR
      _ ≤ ∫ u in (1 : ℝ)..R, B * (1 / u ^ 2) := by
        apply intervalIntegral.integral_mono_on hR hiH.abs (hiInv.const_mul B)
        intro u hu
        rw [abs_div, abs_of_nonneg (sq_nonneg u), mul_one_div]
        exact div_le_div_of_nonneg_right (hB u hu) (sq_nonneg u)
      _ = B * (1 - 1 / R) := by rw [intervalIntegral.integral_const_mul, hinv]
      _ ≤ B := by nlinarith only [mul_nonneg hB0 (one_div_nonneg.mpr hRp.le)]
  have hend : |H R / R| ≤ B := by
    rw [abs_div, abs_of_pos hRp]
    exact (div_le_div_of_nonneg_right (hB R ⟨hR, le_rfl⟩) hRp.le).trans
      (div_le_self hB0 hR)
  calc
    _ = |H R / R - H 1 + ∫ u in (1 : ℝ)..R, H u / u ^ 2| := by
      congr 1
      linarith only [hparts]
    _ ≤ |H R / R - H 1| + |∫ u in (1 : ℝ)..R, H u / u ^ 2| := abs_add_le _ _
    _ ≤ (|H R / R| + |H 1|) + |∫ u in (1 : ℝ)..R, H u / u ^ 2| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ 3 * B := by linarith only [hend, hB 1 ⟨le_rfl, hR⟩, htail]

/-- Smooth mean-one densities with a tunable dyadic phase resonance. -/
def frullaniResonantDensity (t u : ℝ) : ℝ :=
  1 + t * (Real.sin (2 * u) - Real.sin u) / 2

private def phasePrimitive (u : ℝ) : ℝ :=
  -Real.sin (4 * u) / 8 - Real.sin (2 * u) / 4 - Real.sin u + Real.sin (3 * u) / 3

private theorem phase_square (u : ℝ) :
    (Real.sin (2 * u) - Real.sin u) ^ 2 =
      1 - Real.cos (4 * u) / 2 - Real.cos (2 * u) / 2 - Real.cos u + Real.cos (3 * u) := by
  have h1 := Real.cos_two_mul u
  have h2 := Real.cos_two_mul (2 * u)
  have h3 := Real.cos_sub (2 * u) u
  have h4 := Real.cos_add (2 * u) u
  rw [show 2 * u - u = u by ring] at h3
  rw [show 2 * u + u = 3 * u by ring] at h4
  rw [show 2 * (2 * u) = 4 * u by ring] at h2
  nlinarith only [h1, h2, h3, h4, Real.sin_sq_add_cos_sq u,
    Real.sin_sq_add_cos_sq (2 * u)]

private theorem phasePrimitive_deriv (u : ℝ) :
    HasDerivAt phasePrimitive ((Real.sin (2 * u) - Real.sin u) ^ 2 - 1) u := by
  have hd4 := (Real.hasDerivAt_sin (4 * u)).comp u ((hasDerivAt_id u).const_mul 4)
  have hd2 := (Real.hasDerivAt_sin (2 * u)).comp u ((hasDerivAt_id u).const_mul 2)
  have hd3 := (Real.hasDerivAt_sin (3 * u)).comp u ((hasDerivAt_id u).const_mul 3)
  have hd := (((hd4.neg.div_const 8).sub (hd2.div_const 4)).sub
    (Real.hasDerivAt_sin u)).add (hd3.div_const 3)
  apply hd.congr_deriv
  rw [phase_square]
  ring

private theorem phasePrimitive_bound (u : ℝ) : |phasePrimitive u| ≤ 2 := by
  unfold phasePrimitive
  calc
    _ ≤ |-Real.sin (4 * u) / 8 - Real.sin (2 * u) / 4 - Real.sin u| +
        |Real.sin (3 * u) / 3| := abs_add_le _ _
    _ ≤ ((|-Real.sin (4 * u) / 8| + |Real.sin (2 * u) / 4|) + |Real.sin u|) +
        |Real.sin (3 * u) / 3| := by
      linarith only [abs_sub (-Real.sin (4 * u) / 8 - Real.sin (2 * u) / 4) (Real.sin u),
        abs_sub (-Real.sin (4 * u) / 8) (Real.sin (2 * u) / 4)]
    _ ≤ 2 := by
      simp only [abs_div, abs_neg]
      norm_num
      linarith only [Real.abs_sin_le_one (4 * u), Real.abs_sin_le_one (2 * u),
        Real.abs_sin_le_one u, Real.abs_sin_le_one (3 * u)]

/-- The full resonance family obeys the same nonnegative factor-two envelope. -/
theorem frullaniResonantDensity_bounds {t : ℝ} (ht : |t| ≤ 1) (u : ℝ) :
    0 ≤ frullaniResonantDensity t u ∧ frullaniResonantDensity t u ≤ 2 := by
  have hg : |Real.sin (2 * u) - Real.sin u| ≤ 2 :=
    (abs_sub _ _).trans (by linarith only [Real.abs_sin_le_one (2 * u), Real.abs_sin_le_one u])
  have hh : |t * (Real.sin (2 * u) - Real.sin u)| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul ht hg (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  unfold frullaniResonantDensity
  constructor <;> linarith only [hl, hu]

private theorem density_discrepancy_integral (t a b : ℝ) :
    (∫ u in a..b, frullaniResonantDensity t u - 1) =
      (t / 2) * ((Real.cos b - Real.cos (2 * b) / 2) -
        (Real.cos a - Real.cos (2 * a) / 2)) := by
  have hd (u : ℝ) : HasDerivAt
      (fun u => (t / 2) * (Real.cos u - Real.cos (2 * u) / 2))
      (frullaniResonantDensity t u - 1) u := by
    have hd2 := (Real.hasDerivAt_cos (2 * u)).comp u ((hasDerivAt_id u).const_mul 2)
    apply (((Real.hasDerivAt_cos u).sub (hd2.div_const 2)).const_mul (t / 2)).congr_deriv
    unfold frullaniResonantDensity
    ring
  have hc : Continuous (fun u => frullaniResonantDensity t u - 1) := by
    unfold frullaniResonantDensity
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable _ _)]
  ring

/-- Ordinary interval discrepancy is uniformly bounded, including across arbitrarily many periods. -/
theorem frullaniResonantDensity_discrepancy (t a b : ℝ) :
    |∫ u in a..b, frullaniResonantDensity t u - 1| ≤ (3 / 2) * |t| := by
  rw [density_discrepancy_integral, abs_mul]
  have hc (u : ℝ) : |Real.cos u - Real.cos (2 * u) / 2| ≤ 3 / 2 := by
    calc
      _ ≤ |Real.cos u| + |Real.cos (2 * u) / 2| := abs_sub _ _
      _ ≤ 3 / 2 := by
        rw [abs_div]
        norm_num
        linarith only [Real.abs_cos_le_one u, Real.abs_cos_le_one (2 * u)]
  have hab : |(Real.cos b - Real.cos (2 * b) / 2) -
      (Real.cos a - Real.cos (2 * a) / 2)| ≤ 3 :=
    (abs_sub _ _).trans (by linarith only [hc a, hc b])
  calc
    _ ≤ |t / 2| * 3 := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    _ = _ := by rw [abs_div]; norm_num; ring

/-- Every complete period has exactly the same mass as the constant density one. -/
theorem frullaniResonantDensity_period_mass (t a : ℝ) :
    (∫ u in a..(a + 2 * Real.pi), frullaniResonantDensity t u) = 2 * Real.pi := by
  have hc : Continuous (frullaniResonantDensity t) := by
    unfold frullaniResonantDensity
    fun_prop
  have h := density_discrepancy_integral t a (a + 2 * Real.pi)
  rw [show 2 * (a + 2 * Real.pi) = (2 * a + 2 * Real.pi) + 2 * Real.pi by ring,
    Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_add_two_pi] at h
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const] at h
  simp only [sub_self, mul_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  linarith only [h]

/-- The centered signed integral has residue `t/2`, despite mean-one normalization. -/
theorem frullaniResonantDensity_log_residue (t : ℝ) {R : ℝ} (hR : 1 ≤ R) :
    |(∫ u in (1 : ℝ)..R, (frullaniResonantDensity t u - 1) *
        (Real.sin (2 * u) - Real.sin u) / u) - (t / 2) * Real.log R| ≤ 3 * |t| := by
  have hc : Continuous (fun u : ℝ => (Real.sin (2 * u) - Real.sin u) ^ 2) := by
    fun_prop
  have hb := logarithmicIntegral_residue_bound (m := 1) hR hc.continuousOn
    (fun u _ => phasePrimitive_deriv u) (fun u _ => phasePrimitive_bound u)
  have heq : (fun u : ℝ => (frullaniResonantDensity t u - 1) *
      (Real.sin (2 * u) - Real.sin u) / u) =
      fun u => (t / 2) * ((Real.sin (2 * u) - Real.sin u) ^ 2 / u) := by
    funext u
    unfold frullaniResonantDensity
    ring
  rw [heq, intervalIntegral.integral_const_mul, ← mul_sub, abs_mul]
  simp only [one_mul] at hb
  calc
    _ ≤ |t / 2| * (3 * 2) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by rw [abs_div]; norm_num; ring

/-- The logarithmic residue is unique; ordinary mean normalization leaves it unrestricted. -/
theorem frullaniResonantDensity_residue_iff (t m : ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      |(∫ u in (1 : ℝ)..R, (frullaniResonantDensity t u - 1) *
        (Real.sin (2 * u) - Real.sin u) / u) - m * Real.log R| ≤ C) ↔ m = t / 2 := by
  constructor
  · rintro ⟨C, hC, h⟩
    by_contra hm
    have hd : 0 < |t / 2 - m| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hm))
    let x := (C + 3 * |t| + 1) / |t / 2 - m|
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hR : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
    have h1 := frullaniResonantDensity_log_residue t hR
    have h2 := h (Real.exp x) hR
    rw [Real.log_exp] at h1 h2
    have hb : |(t / 2 - m) * x| ≤ 3 * |t| + C := by
      have he : (t / 2 - m) * x =
          -((∫ u in (1 : ℝ)..Real.exp x, (frullaniResonantDensity t u - 1) *
            (Real.sin (2 * u) - Real.sin u) / u) - (t / 2) * x) +
          ((∫ u in (1 : ℝ)..Real.exp x, (frullaniResonantDensity t u - 1) *
            (Real.sin (2 * u) - Real.sin u) / u) - m * x) := by ring
      rw [he]
      exact (abs_add_le _ _).trans (add_le_add (by simpa only [abs_neg] using h1) h2)
    rw [abs_mul, abs_of_nonneg hx] at hb
    have hid : |t / 2 - m| * x = C + 3 * |t| + 1 := by
      dsimp [x]
      exact mul_div_cancel₀ _ hd.ne'
    linarith only [hb, hid]
  · rintro rfl
    exact ⟨3 * |t|, by positivity, fun R hR => frullaniResonantDensity_log_residue t hR⟩

/-- Positive phase resonance gives an unbounded centered Frullani integral. -/
theorem frullaniResonantDensity_unbounded {t : ℝ} (ht : 0 < t) (M : ℝ) :
    ∃ R : ℝ, 1 ≤ R ∧ M < ∫ u in (1 : ℝ)..R,
      (frullaniResonantDensity t u - 1) * (Real.sin (2 * u) - Real.sin u) / u := by
  let x := 2 * (|M| + 3 * |t| + 1) / t
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hR : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  refine ⟨Real.exp x, hR, ?_⟩
  have h := (abs_le.mp (frullaniResonantDensity_log_residue t hR)).1
  rw [Real.log_exp] at h
  have hxid : (t / 2) * x = |M| + 3 * |t| + 1 := by
    dsimp [x]
    field_simp
  linarith only [h, hxid, le_abs_self M]

/-- A smooth, mean-one, factor-two envelope with bounded ordinary discrepancy can have
unbounded signed Frullani discrepancy. -/
theorem frullani_factorTwo_meanOne_counterexample :
    ∃ a : ℝ → ℝ, ContDiff ℝ ⊤ a ∧ (∀ u, 0 ≤ a u ∧ a u ≤ 2) ∧
      (∀ x, (∫ u in x..(x + 2 * Real.pi), a u) = 2 * Real.pi) ∧
      (∀ L R, |∫ u in L..R, a u - 1| ≤ 3 / 2) ∧
      ∀ M : ℝ, ∃ R : ℝ, 1 ≤ R ∧ M < ∫ u in (1 : ℝ)..R,
        (a u - 1) * (Real.sin (2 * u) - Real.sin u) / u := by
  refine ⟨frullaniResonantDensity 1, ?_,
    frullaniResonantDensity_bounds (by norm_num),
    frullaniResonantDensity_period_mass 1, ?_,
    frullaniResonantDensity_unbounded (by norm_num)⟩
  · unfold frullaniResonantDensity
    fun_prop
  · intro L R
    simpa only [abs_one, mul_one] using frullaniResonantDensity_discrepancy 1 L R

private theorem integral_abs_argument (f : ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ u in a..b, f |u|) = ∫ u in a..b, f u := by
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  rw [abs_of_nonneg ((le_min ha hb).trans hu.1)]

/-- Reflection preserves the obstruction for an even pair density on positive lags. -/
theorem frullani_factorTwo_even_counterexample :
    ∃ a : ℝ → ℝ, Continuous a ∧ (∀ u, a (-u) = a u) ∧
      (∀ u, 0 ≤ a u ∧ a u ≤ 2) ∧
      (∀ x : ℝ, 0 ≤ x → (∫ u in x..(x + 2 * Real.pi), a u) = 2 * Real.pi) ∧
      (∀ L R : ℝ, 0 ≤ L → 0 ≤ R → |∫ u in L..R, a u - 1| ≤ 3 / 2) ∧
      ∀ M : ℝ, ∃ R : ℝ, 1 ≤ R ∧ M < ∫ u in (1 : ℝ)..R,
        (a u - 1) * (Real.sin (2 * u) - Real.sin u) / u := by
  refine ⟨fun u => frullaniResonantDensity 1 |u|, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold frullaniResonantDensity
    fun_prop
  · intro u
    dsimp only
    rw [abs_neg]
  · intro u
    exact frullaniResonantDensity_bounds (by norm_num) |u|
  · intro x hx
    rw [integral_abs_argument (frullaniResonantDensity 1) hx (by positivity)]
    exact frullaniResonantDensity_period_mass 1 x
  · intro L R hL hR
    rw [integral_abs_argument (fun u => frullaniResonantDensity 1 u - 1) hL hR]
    simpa only [abs_one, mul_one] using frullaniResonantDensity_discrepancy 1 L R
  · intro M
    obtain ⟨R, hR, hM⟩ := frullaniResonantDensity_unbounded (t := 1) (by norm_num) M
    refine ⟨R, hR, ?_⟩
    have heq : (∫ u in (1 : ℝ)..R, (frullaniResonantDensity 1 |u| - 1) *
        (Real.sin (2 * u) - Real.sin u) / u) =
        ∫ u in (1 : ℝ)..R, (frullaniResonantDensity 1 u - 1) *
          (Real.sin (2 * u) - Real.sin u) / u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hR] at hu
      dsimp only
      rw [abs_of_nonneg (zero_le_one.trans hu.1)]
    rw [heq]
    exact hM

/-- The resonance can be made arbitrarily close to the constant density one. -/
theorem abs_frullaniResonantDensity_sub_one_le (t u : ℝ) :
    |frullaniResonantDensity t u - 1| ≤ |t| := by
  have hg : |Real.sin (2 * u) - Real.sin u| ≤ 2 :=
    (abs_sub _ _).trans (by linarith only [Real.abs_sin_le_one (2 * u), Real.abs_sin_le_one u])
  have he : frullaniResonantDensity t u - 1 = t * (Real.sin (2 * u) - Real.sin u) / 2 := by
    unfold frullaniResonantDensity
    ring
  rw [he, abs_div, abs_mul]
  norm_num
  nlinarith only [mul_le_mul_of_nonneg_left hg (abs_nonneg t)]

/-- No positive tolerance in an unsigned near-one envelope forces centered Frullani cancellation. -/
theorem frullani_near_one_counterexample {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ → ℝ, ContDiff ℝ ⊤ a ∧ (∀ u, 0 ≤ a u ∧ |a u - 1| ≤ ε) ∧
      (∀ x, (∫ u in x..(x + 2 * Real.pi), a u) = 2 * Real.pi) ∧
      (∀ L R, |∫ u in L..R, a u - 1| ≤ (3 / 2) * ε) ∧
      ∀ M : ℝ, ∃ R : ℝ, 1 ≤ R ∧ M < ∫ u in (1 : ℝ)..R,
        (a u - 1) * (Real.sin (2 * u) - Real.sin u) / u := by
  let t := min ε 1
  have ht : 0 < t := lt_min hε zero_lt_one
  have htε : t ≤ ε := min_le_left _ _
  have ht1 : |t| ≤ 1 := by rw [abs_of_pos ht]; exact min_le_right _ _
  refine ⟨frullaniResonantDensity t, ?_, ?_, frullaniResonantDensity_period_mass t,
    ?_, frullaniResonantDensity_unbounded ht⟩
  · unfold frullaniResonantDensity
    fun_prop
  · intro u
    refine ⟨(frullaniResonantDensity_bounds ht1 u).1, ?_⟩
    exact (abs_frullaniResonantDensity_sub_one_le t u).trans ((abs_of_pos ht).le.trans htε)
  · intro L R
    have h := frullaniResonantDensity_discrepancy t L R
    rw [abs_of_pos ht] at h
    exact h.trans (mul_le_mul_of_nonneg_left htε (by norm_num))

end GaloisForLFunctions.TransThresholdPairCorrelation
