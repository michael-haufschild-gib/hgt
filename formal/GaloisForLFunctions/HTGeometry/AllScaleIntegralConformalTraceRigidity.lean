import GaloisForLFunctions.HTGeometry.PolynomialPowerConvexConfinement

/-!
# All-scale integral conformal-trace rigidity

Functional-equation reflection pairs the unnormalized formation weights `n^(1+b)` and
`n^(1-b)`.  Their determinant is always `n^2`.  This file proves that, in the unit strip, their
trace can be integral at every natural scale only when `b = 0`.
-/

open Filter Finset Asymptotics Topology

namespace GaloisForLFunctions

noncomputable section

/-- Second-unit-difference stencil `(1, -2, 1)`. -/
def conformalSecondDifferenceStencil : ℕ →₀ ℝ :=
  tupleDifference (fun i : Fin 2 => if (i : ℕ) = 0 then 2 else 0)
    (fun _ : Fin 2 => 1)

lemma polynomialPowerFiniteDifference_conformalSecondDifferenceStencil (β x : ℝ) :
    polynomialPowerFiniteDifference β conformalSecondDifferenceStencil x =
      (x + 2) ^ β - 2 * (x + 1) ^ β + x ^ β := by
  rw [conformalSecondDifferenceStencil, polynomialPowerFiniteDifference_tupleDifference]
  simp [Fin.sum_univ_two]
  ring

/-- The second-difference asymptotic for every exponent except its two polynomial zeros. -/
lemma conformalSecondDifference_isEquivalent {β : ℝ}
    (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) :
    (fun x : ℝ => (x + 2) ^ β - 2 * (x + 1) ^ β + x ^ β) ~[atTop]
      fun x => (β * (β - 1)) * x ^ (β - 2) := by
  have h := polynomialPowerFiniteDifference_isEquivalent
    (β := β) conformalSecondDifferenceStencil 2
    (by
      intro k hk
      rw [conformalSecondDifferenceStencil, stretchedMoment_tupleDifference]
      interval_cases k <;> simp)
    (by
      rw [conformalSecondDifferenceStencil, stretchedMoment_tupleDifference]
      norm_num [Fin.sum_univ_two])
    (by
      rw [descPochhammer_eval_eq_prod_range]
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      have hjlt : j < 2 := Finset.mem_range.mp hj
      interval_cases j
      · simpa using hβ0
      · simpa using sub_ne_zero.mpr hβ1)
  have hc : polynomialPowerDifferenceCoefficient β conformalSecondDifferenceStencil 2 =
      β * (β - 1) := by
    rw [polynomialPowerDifferenceCoefficient, conformalSecondDifferenceStencil,
      stretchedMoment_tupleDifference]
    norm_num [Fin.sum_univ_two, descPochhammer]
  rw [hc] at h
  simpa only [Nat.cast_ofNat] using h.congr_left (Eventually.of_forall fun x =>
    polynomialPowerFiniteDifference_conformalSecondDifferenceStencil β x)

lemma rpow_isLittleO_rpow_atTop_of_lt {α β : ℝ} (hαβ : α < β) :
    (fun x : ℝ => x ^ α) =o[atTop] fun x : ℝ => x ^ β := by
  apply (isLittleO_iff_tendsto' ?_).2
  · have hlim := tendsto_rpow_neg_atTop (sub_pos.mpr hαβ)
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_sub hx]
    congr 1
    ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hzero
    exact (ne_of_gt (Real.rpow_pos_of_pos hx β) hzero).elim

/-- Unnormalized trace of the two functional-equation orientations at scale `x`. -/
def allScaleConformalTrace (b x : ℝ) : ℝ :=
  x ^ (1 + b) + x ^ (1 - b)

/-- Second discrete curvature of the unnormalized paired trace. -/
def allScaleConformalCurvature (b x : ℝ) : ℝ :=
  allScaleConformalTrace b (x + 2) - 2 * allScaleConformalTrace b (x + 1) +
    allScaleConformalTrace b x

theorem allScaleConformalCurvature_isEquivalent {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    allScaleConformalCurvature b ~[atTop]
      fun x => ((1 + b) * b) * x ^ (b - 1) := by
  have hp := conformalSecondDifference_isEquivalent
    (β := 1 + b) (by positivity) (by linarith)
  have hm := conformalSecondDifference_isEquivalent
    (β := 1 - b) (by linarith) (by linarith)
  have hpow : (fun x : ℝ => x ^ (-b - 1)) =o[atTop]
      fun x : ℝ => x ^ (b - 1) :=
    rpow_isLittleO_rpow_atTop_of_lt (by linarith)
  have hmodel : (fun x : ℝ => ((1 - b) * (-b)) * x ^ (-b - 1)) =o[atTop]
      fun x : ℝ => ((1 + b) * b) * x ^ (b - 1) := by
    exact (hpow.const_mul_left ((1 - b) * (-b))).const_mul_right
      (mul_ne_zero (by linarith) (ne_of_gt hb0))
  have hmLittle : (fun x : ℝ =>
      (x + 2) ^ (1 - b) - 2 * (x + 1) ^ (1 - b) + x ^ (1 - b)) =o[atTop]
      fun x : ℝ => ((1 + b) * b) * x ^ (b - 1) := by
    have hm' : (fun x : ℝ =>
        (x + 2) ^ (1 - b) - 2 * (x + 1) ^ (1 - b) + x ^ (1 - b)) ~[atTop]
        fun x : ℝ => ((1 - b) * (-b)) * x ^ (-b - 1) := by
      convert hm using 1
      all_goals ring_nf
    exact hm'.trans_isLittleO hmodel
  have hp' : (fun x : ℝ =>
      (x + 2) ^ (1 + b) - 2 * (x + 1) ^ (1 + b) + x ^ (1 + b)) ~[atTop]
      fun x : ℝ => ((1 + b) * b) * x ^ (b - 1) := by
    convert hp using 1
    all_goals ring_nf
  exact (hp'.add_isLittleO hmLittle).congr_left (Eventually.of_forall fun x => by
    simp only [Pi.add_apply, allScaleConformalCurvature, allScaleConformalTrace]
    ring)

/-- Functional-equation orientations conserve the full determinant `n^2` at positive scales. -/
theorem allScaleConformalDeterminant_succ (b : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ (1 + b) * ((n + 1 : ℕ) : ℝ) ^ (1 - b) =
      ((n + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
  rw [← Real.rpow_add (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
  congr 1
  ring

def allScaleConformalTraceNat (b : ℝ) (n : ℕ) : ℝ :=
  allScaleConformalTrace b (n : ℝ)

def allScaleConformalCurvatureNat (b : ℝ) (n : ℕ) : ℝ :=
  allScaleConformalTraceNat b (n + 2) - 2 * allScaleConformalTraceNat b (n + 1) +
    allScaleConformalTraceNat b n

/-- Every natural-scale trace is the real image of an integer. -/
def AllScaleIntegralConformalTrace (b : ℝ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, allScaleConformalTraceNat b n = (z : ℝ)

lemma allScaleConformalCurvatureNat_eq (b : ℝ) (n : ℕ) :
    allScaleConformalCurvatureNat b n = allScaleConformalCurvature b (n : ℝ) := by
  simp [allScaleConformalCurvatureNat, allScaleConformalTraceNat,
    allScaleConformalCurvature, Nat.cast_add]

lemma AllScaleIntegralConformalTrace.curvature_integral {b : ℝ}
    (h : AllScaleIntegralConformalTrace b) (n : ℕ) :
    ∃ z : ℤ, allScaleConformalCurvatureNat b n = (z : ℝ) := by
  obtain ⟨z0, hz0⟩ := h n
  obtain ⟨z1, hz1⟩ := h (n + 1)
  obtain ⟨z2, hz2⟩ := h (n + 2)
  refine ⟨z2 - 2 * z1 + z0, ?_⟩
  rw [allScaleConformalCurvatureNat, hz2, hz1, hz0]
  push_cast
  ring

theorem allScaleConformalCurvature_eventually_pos_and_tendsto_zero
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    (∀ᶠ n : ℕ in atTop, 0 < allScaleConformalCurvatureNat b n) ∧
      Tendsto (allScaleConformalCurvatureNat b) atTop (𝓝 0) := by
  have heq := allScaleConformalCurvature_isEquivalent hb0 hb1
  have hleadPos : ∀ᶠ x : ℝ in atTop,
      0 < ((1 + b) * b) * x ^ (b - 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos (mul_pos (by linarith) hb0) (Real.rpow_pos_of_pos hx _)
  have hcurvPos := heq.eventually_pos hleadPos
  have hpow0 : Tendsto (fun x : ℝ => x ^ (b - 1)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (sub_pos.mpr hb1)
    apply h.congr'
    filter_upwards with x
    congr 1
    ring
  have hlead0 : Tendsto (fun x : ℝ => ((1 + b) * b) * x ^ (b - 1))
      atTop (𝓝 0) := by
    simpa using hpow0.const_mul ((1 + b) * b)
  have hcurv0 : Tendsto (allScaleConformalCurvature b) atTop (𝓝 0) :=
    heq.tendsto_nhds_iff.mpr hlead0
  constructor
  · have hpull : ∀ᶠ n : ℕ in atTop,
        0 < allScaleConformalCurvature b (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually hcurvPos
    filter_upwards [hpull] with n hn
    rwa [allScaleConformalCurvatureNat_eq]
  · apply (hcurv0.comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards with n
    simp only [Function.comp_apply, allScaleConformalCurvatureNat_eq]

/-- On `0 ≤ b < 1`, integral paired trace at every natural scale is equivalent to `b = 0`. -/
theorem allScaleIntegralConformalTrace_iff_zero_on_unit_interval (b : ℝ) :
    (0 ≤ b ∧ b < 1 ∧ AllScaleIntegralConformalTrace b) ↔ b = 0 := by
  constructor
  · rintro ⟨hbnonneg, hb1, hint⟩
    apply le_antisymm ?_ hbnonneg
    by_contra hbnot
    have hb0 : 0 < b := lt_of_not_ge hbnot
    obtain ⟨hpos, hzero⟩ :=
      allScaleConformalCurvature_eventually_pos_and_tendsto_zero hb0 hb1
    have hlt : ∀ᶠ n : ℕ in atTop, allScaleConformalCurvatureNat b n < 1 :=
      hzero.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨n, hnpos, hnlt⟩ := (hpos.and hlt).exists
    obtain ⟨z, hz⟩ := hint.curvature_integral n
    have hzpos : 0 < z := by exact_mod_cast (hz ▸ hnpos)
    have hzlt : z < 1 := by exact_mod_cast (hz ▸ hnlt)
    omega
  · rintro rfl
    refine ⟨le_rfl, by norm_num, ?_⟩
    intro n
    refine ⟨2 * (n : ℤ), ?_⟩
    simp [allScaleConformalTraceNat, allScaleConformalTrace]
    ring

/-- Critical-strip admission plus all-scale integral formation trace. -/
def StripIntegralConformalFormation (a : ℝ) : Prop :=
  |a| < 1 ∧ AllScaleIntegralConformalTrace |a|

/-- Closed capstone: an admitted integral conformal formation has neutral horizontal grade. -/
theorem stripIntegralConformalFormation_iff_grade_zero (a : ℝ) :
    StripIntegralConformalFormation a ↔ a = 0 := by
  rw [StripIntegralConformalFormation]
  constructor
  · rintro ⟨ha1, hint⟩
    have habs : |a| = 0 :=
      (allScaleIntegralConformalTrace_iff_zero_on_unit_interval |a|).mp
        ⟨abs_nonneg a, ha1, hint⟩
    exact abs_eq_zero.mp habs
  · rintro rfl
    have h := (allScaleIntegralConformalTrace_iff_zero_on_unit_interval 0).mpr rfl
    exact ⟨by norm_num, by simpa only [abs_zero] using h.2.2⟩

/-! ## Hyperbolic trace/supertrace ledger -/

def hyperbolicFormationEven (scale u : ℝ) : ℝ := scale * Real.exp u

def hyperbolicFormationOdd (scale u : ℝ) : ℝ := scale * Real.exp (-u)

def hyperbolicFormationTrace (scale u : ℝ) : ℝ :=
  hyperbolicFormationEven scale u + hyperbolicFormationOdd scale u

def hyperbolicFormationSupertrace (scale u : ℝ) : ℝ :=
  hyperbolicFormationEven scale u - hyperbolicFormationOdd scale u

/-- Forgetting parity gives the hyperbolic cosine channel. -/
theorem hyperbolicFormationTrace_eq (scale u : ℝ) :
    hyperbolicFormationTrace scale u = 2 * scale * Real.cosh u := by
  rw [hyperbolicFormationTrace, hyperbolicFormationEven, hyperbolicFormationOdd,
    Real.cosh_eq]
  ring

/-- Retaining parity gives the hyperbolic sine channel. -/
theorem hyperbolicFormationSupertrace_eq (scale u : ℝ) :
    hyperbolicFormationSupertrace scale u = 2 * scale * Real.sinh u := by
  rw [hyperbolicFormationSupertrace, hyperbolicFormationEven, hyperbolicFormationOdd,
    Real.sinh_eq]
  ring

/-- The reciprocal orientation legs conserve the square of the common formation scale. -/
theorem hyperbolicFormationDeterminant_eq (scale u : ℝ) :
    hyperbolicFormationEven scale u * hyperbolicFormationOdd scale u = scale ^ 2 := by
  rw [hyperbolicFormationEven, hyperbolicFormationOdd]
  calc
    scale * Real.exp u * (scale * Real.exp (-u)) =
        scale ^ 2 * (Real.exp u * Real.exp (-u)) := by ring
    _ = scale ^ 2 := by rw [← Real.exp_add]; simp

/-- Trace and supertrace are the two coordinates of one conserved hyperbolic ledger. -/
theorem hyperbolicFormationMinkowskiConservation (scale u : ℝ) :
    hyperbolicFormationTrace scale u ^ 2 - hyperbolicFormationSupertrace scale u ^ 2 =
      4 * scale ^ 2 := by
  rw [hyperbolicFormationTrace_eq, hyperbolicFormationSupertrace_eq]
  nlinarith [Real.cosh_sq_sub_sinh_sq u]

/-- Likelihood contrast is supertrace divided by trace. -/
theorem hyperbolicFormationContrast_eq_tanh (u : ℝ) (n : ℕ) :
    hyperbolicFormationSupertrace ((n + 1 : ℕ) : ℝ) u /
        hyperbolicFormationTrace ((n + 1 : ℕ) : ℝ) u = Real.tanh u := by
  rw [hyperbolicFormationTrace_eq, hyperbolicFormationSupertrace_eq,
    Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- Likelihood visibility is conserved scale divided by trace. -/
theorem hyperbolicFormationVisibility_eq_inv_cosh (u : ℝ) (n : ℕ) :
    (2 * ((n + 1 : ℕ) : ℝ)) /
        hyperbolicFormationTrace ((n + 1 : ℕ) : ℝ) u = (Real.cosh u)⁻¹ := by
  rw [hyperbolicFormationTrace_eq]
  field_simp

/-! ## Integral supertrace rigidity -/

def allScaleConformalSupertrace (b x : ℝ) : ℝ :=
  x ^ (1 + b) - x ^ (1 - b)

def allScaleConformalSupercurvature (b x : ℝ) : ℝ :=
  allScaleConformalSupertrace b (x + 2) -
    2 * allScaleConformalSupertrace b (x + 1) + allScaleConformalSupertrace b x

theorem allScaleConformalSupercurvature_isEquivalent
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    allScaleConformalSupercurvature b ~[atTop]
      fun x => ((1 + b) * b) * x ^ (b - 1) := by
  have hp := conformalSecondDifference_isEquivalent
    (β := 1 + b) (by positivity) (by linarith)
  have hm := conformalSecondDifference_isEquivalent
    (β := 1 - b) (by linarith) (by linarith)
  have hpow : (fun x : ℝ => x ^ (-b - 1)) =o[atTop]
      fun x : ℝ => x ^ (b - 1) :=
    rpow_isLittleO_rpow_atTop_of_lt (by linarith)
  have hmodel : (fun x : ℝ => ((1 - b) * (-b)) * x ^ (-b - 1)) =o[atTop]
      fun x : ℝ => ((1 + b) * b) * x ^ (b - 1) := by
    exact (hpow.const_mul_left ((1 - b) * (-b))).const_mul_right
      (mul_ne_zero (by linarith) (ne_of_gt hb0))
  have hmLittle : (fun x : ℝ =>
      (x + 2) ^ (1 - b) - 2 * (x + 1) ^ (1 - b) + x ^ (1 - b)) =o[atTop]
      fun x : ℝ => ((1 + b) * b) * x ^ (b - 1) := by
    have hm' : (fun x : ℝ =>
        (x + 2) ^ (1 - b) - 2 * (x + 1) ^ (1 - b) + x ^ (1 - b)) ~[atTop]
        fun x : ℝ => ((1 - b) * (-b)) * x ^ (-b - 1) := by
      convert hm using 1
      all_goals ring_nf
    exact hm'.trans_isLittleO hmodel
  have hp' : (fun x : ℝ =>
      (x + 2) ^ (1 + b) - 2 * (x + 1) ^ (1 + b) + x ^ (1 + b)) ~[atTop]
      fun x : ℝ => ((1 + b) * b) * x ^ (b - 1) := by
    convert hp using 1
    all_goals ring_nf
  exact (hp'.sub_isLittleO hmLittle).congr_left (Eventually.of_forall fun x => by
    simp only [Pi.sub_apply, allScaleConformalSupercurvature,
      allScaleConformalSupertrace]
    ring)

def allScaleConformalSupertraceNat (b : ℝ) (n : ℕ) : ℝ :=
  allScaleConformalSupertrace b (n : ℝ)

def allScaleConformalSupercurvatureNat (b : ℝ) (n : ℕ) : ℝ :=
  allScaleConformalSupertraceNat b (n + 2) -
    2 * allScaleConformalSupertraceNat b (n + 1) + allScaleConformalSupertraceNat b n

/-- Every natural-scale supertrace is the real image of an integer. -/
def AllScaleIntegralConformalSupertrace (b : ℝ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, allScaleConformalSupertraceNat b n = (z : ℝ)

lemma allScaleConformalSupercurvatureNat_eq (b : ℝ) (n : ℕ) :
    allScaleConformalSupercurvatureNat b n =
      allScaleConformalSupercurvature b (n : ℝ) := by
  simp [allScaleConformalSupercurvatureNat, allScaleConformalSupertraceNat,
    allScaleConformalSupercurvature, Nat.cast_add]

lemma AllScaleIntegralConformalSupertrace.supercurvature_integral {b : ℝ}
    (h : AllScaleIntegralConformalSupertrace b) (n : ℕ) :
    ∃ z : ℤ, allScaleConformalSupercurvatureNat b n = (z : ℝ) := by
  obtain ⟨z0, hz0⟩ := h n
  obtain ⟨z1, hz1⟩ := h (n + 1)
  obtain ⟨z2, hz2⟩ := h (n + 2)
  refine ⟨z2 - 2 * z1 + z0, ?_⟩
  rw [allScaleConformalSupercurvatureNat, hz2, hz1, hz0]
  push_cast
  ring

theorem allScaleConformalSupercurvature_eventually_pos_and_tendsto_zero
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    (∀ᶠ n : ℕ in atTop, 0 < allScaleConformalSupercurvatureNat b n) ∧
      Tendsto (allScaleConformalSupercurvatureNat b) atTop (𝓝 0) := by
  have heq := allScaleConformalSupercurvature_isEquivalent hb0 hb1
  have hleadPos : ∀ᶠ x : ℝ in atTop,
      0 < ((1 + b) * b) * x ^ (b - 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos (mul_pos (by linarith) hb0) (Real.rpow_pos_of_pos hx _)
  have hcurvPos := heq.eventually_pos hleadPos
  have hpow0 : Tendsto (fun x : ℝ => x ^ (b - 1)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (sub_pos.mpr hb1)
    apply h.congr'
    filter_upwards with x
    congr 1
    ring
  have hlead0 : Tendsto (fun x : ℝ => ((1 + b) * b) * x ^ (b - 1))
      atTop (𝓝 0) := by
    simpa using hpow0.const_mul ((1 + b) * b)
  have hcurv0 : Tendsto (allScaleConformalSupercurvature b) atTop (𝓝 0) :=
    heq.tendsto_nhds_iff.mpr hlead0
  constructor
  · have hpull : ∀ᶠ n : ℕ in atTop,
        0 < allScaleConformalSupercurvature b (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually hcurvPos
    filter_upwards [hpull] with n hn
    rwa [allScaleConformalSupercurvatureNat_eq]
  · apply (hcurv0.comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards with n
    simp only [Function.comp_apply, allScaleConformalSupercurvatureNat_eq]

/-- Integral parity-retaining trace at every natural scale also forces neutral grade. -/
theorem allScaleIntegralConformalSupertrace_iff_zero_on_unit_interval (b : ℝ) :
    (0 ≤ b ∧ b < 1 ∧ AllScaleIntegralConformalSupertrace b) ↔ b = 0 := by
  constructor
  · rintro ⟨hbnonneg, hb1, hint⟩
    apply le_antisymm ?_ hbnonneg
    by_contra hbnot
    have hb0 : 0 < b := lt_of_not_ge hbnot
    obtain ⟨hpos, hzero⟩ :=
      allScaleConformalSupercurvature_eventually_pos_and_tendsto_zero hb0 hb1
    have hlt : ∀ᶠ n : ℕ in atTop, allScaleConformalSupercurvatureNat b n < 1 :=
      hzero.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨n, hnpos, hnlt⟩ := (hpos.and hlt).exists
    obtain ⟨z, hz⟩ := hint.supercurvature_integral n
    have hzpos : 0 < z := by exact_mod_cast (hz ▸ hnpos)
    have hzlt : z < 1 := by exact_mod_cast (hz ▸ hnlt)
    omega
  · rintro rfl
    refine ⟨le_rfl, by norm_num, ?_⟩
    intro n
    exact ⟨0, by simp [allScaleConformalSupertraceNat,
      allScaleConformalSupertrace]⟩

/-- Closed parity-retaining capstone in the critical strip. -/
theorem stripIntegralConformalSupertrace_iff_grade_zero (a : ℝ) :
    (|a| < 1 ∧ AllScaleIntegralConformalSupertrace |a|) ↔ a = 0 := by
  constructor
  · rintro ⟨ha1, hint⟩
    have habs : |a| = 0 :=
      (allScaleIntegralConformalSupertrace_iff_zero_on_unit_interval |a|).mp
        ⟨abs_nonneg a, ha1, hint⟩
    exact abs_eq_zero.mp habs
  · rintro rfl
    have h := (allScaleIntegralConformalSupertrace_iff_zero_on_unit_interval 0).mpr rfl
    exact ⟨by norm_num, by simpa only [abs_zero] using h.2.2⟩

end
end GaloisForLFunctions
