import GaloisForLFunctions.ArithmeticCriticalityTheory.DoobSourcePoleMomentLawAtInfinity
import GaloisForLFunctions.ArithmeticCriticalityTheory.GeneralGaugeGroundStateRepresentation
import GaloisForLFunctions.ArithmeticCriticalityTheory.FullZeroFormWeilPositivity
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Weil positivity on a window from a plateau gauge

Take a gauge `M` with `0 ≤ M ≤ 1`, `M = 1` on `[−r, r]` and `M = 0` outside `(−R, R)`, `2R < log 2`. For
a test `F` supported in `[−r, r]`, `F = M · F`, and the ground-state representation in the gauge `M`
(`markovEnergy_phiDoob_mul_eq_signedJump_add_source` with the exact source `−Φ 𝒲M`) reads

    Q(F) = J_M(F) − ∫ F² 𝒲M,       J_M(F) = ∫ dm(t) ∫ M(x) M(x+t) (F(x) − F(x+t))² ≥ 0.

All conductances `M(x)M(x+t)` are nonnegative, and on the window the pole-free Weil operator is
purely archimedean: no prime shift of a point of `[−r, r]` lands in `(−R, R)`. At `x` with `M(x) = 1`,
with `a = R − x`, `b = R + x`, `ν(u) = e^{−2u}/(1 − e^{−2u})` and `ω − ν ≤ 3/4`
(`archLevyDensity_sub_archDiagonalDensity_le`),

    −𝒲M(x) = ∫_0^∞ [2ν(u) − ω(u)(M(x+u) + M(x−u))] du − (γ + log π)
           ≥ N(a) + N(b) − (3/4)(a + b) − (γ + log π),     N(a) = ∫_a^∞ ν = −½ log(1 − e^{−2a}),

(`integral_profileArchTerm_ge`, `integral_Ioi_archDiagonalDensity`), and `N(a) + N(b) ≥ −log(2R)`. The
gauge cannot feel the window edge except through the killing `N`, which is logarithmically large on
short windows. With `R = e^{−2}/2` the potential is at least `2 − (3/4)e^{−2} − (γ + log π) > 0.0817`
(`two_sub_three_quarter_exp_neg_two_sub_archConstant_gt`).

**Theorem** (`fullZeroForm_ge_of_support_le`). Every real `F ∈ C²_c` supported in `[−r, r]`,
`r < e^{−2}/2`, satisfies `Ẑ(F) ≥ (3/40) ∫ F²`; the odd pole moment costs at most `4R³ ∫F²`
(`sq_oddPoleMoment_le`).

The mechanism is the ground-state representation of the theory with a positive gauge: below the
first prime the conductances of every nonnegative gauge are nonnegative, so positivity of the full
zero form reduces to positivity of one explicit potential, a pointwise inequality between the
archimedean densities, the window killing `−½ log(1 − e^{−2a})` and the constant `γ + log π`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The two archimedean densities -/

/-- `ω − ν ≤ 3/4` on the positive half line. -/
theorem archLevyDensity_sub_archDiagonalDensity_le {u : ℝ} (hu : 0 < u) :
    archLevyDensity u - archDiagonalDensity u ≤ 3 / 4 := by
  set z := Real.exp (-u / 2) with hz
  have hz0 : 0 < z := Real.exp_pos _
  have hz1 : z < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h4 : Real.exp (-2 * u) = z ^ 4 := by
    rw [hz, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hden : 0 < 1 - z ^ 4 := by nlinarith [pow_lt_one₀ hz0.le hz1 (by norm_num : (4 : ℕ) ≠ 0)]
  unfold archLevyDensity archDiagonalDensity
  rw [h4, ← hz, div_sub_div_same, div_le_iff₀ hden]
  have hz2 : z ^ 2 < 1 := pow_lt_one₀ hz0.le hz1 (by norm_num)
  have hz3 : z ^ 3 < 1 := pow_lt_one₀ hz0.le hz1 (by norm_num)
  have hfac : 0 ≤ (1 - z) * (3 - z - z ^ 2 - z ^ 3) := mul_nonneg (by linarith) (by linarith)
  nlinarith [hfac]

theorem archDiagonalDensity_pos {u : ℝ} (hu : 0 < u) : 0 < archDiagonalDensity u := by
  unfold archDiagonalDensity
  have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact div_pos (Real.exp_pos _) (by linarith)

theorem hasDerivAt_half_log_one_sub_exp {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u => (1 / 2) * Real.log (1 - Real.exp (-2 * u))) (archDiagonalDensity u) u := by
  have hlt : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he : HasDerivAt (fun u => 1 - Real.exp (-2 * u)) (-(Real.exp (-2 * u) * -2)) u := by
    have := ((hasDerivAt_id u).const_mul (-2)).exp
    simpa using this.const_sub 1
  refine ((he.log (by linarith)).const_mul (1 / 2)).congr_deriv ?_
  unfold archDiagonalDensity
  field_simp

theorem tendsto_half_log_one_sub_exp :
    Tendsto (fun u : ℝ => (1 / 2) * Real.log (1 - Real.exp (-2 * u))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun u : ℝ => Real.exp (-2 * u)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
      (by norm_num : (-2 : ℝ) < 0))
    simpa [Function.comp_def] using this
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  rw [sub_zero] at h1
  have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1).const_mul (1 / 2)
  rw [Real.log_one, mul_zero] at h2
  exact h2

/-- **The window killing.** `∫_a^∞ ν = −½ log(1 − e^{−2a})` for `a > 0`. -/
theorem integral_Ioi_archDiagonalDensity {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi a, archDiagonalDensity u = -(1 / 2) * Real.log (1 - Real.exp (-2 * a)) := by
  have hlim := tendsto_half_log_one_sub_exp
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hasDerivAt_half_log_one_sub_exp ha).continuousAt.continuousWithinAt)
    (fun u hu => hasDerivAt_half_log_one_sub_exp (lt_trans ha hu))
    (fun u hu => (archDiagonalDensity_pos (lt_trans ha hu)).le) hlim
  rw [h]
  ring

theorem integrableOn_Ioi_archDiagonalDensity {a : ℝ} (ha : 0 < a) :
    IntegrableOn archDiagonalDensity (Ioi a) := by
  have hlim := tendsto_half_log_one_sub_exp
  exact integrableOn_Ioi_deriv_of_nonneg
    ((hasDerivAt_half_log_one_sub_exp ha).continuousAt.continuousWithinAt)
    (fun u hu => hasDerivAt_half_log_one_sub_exp (lt_trans ha hu))
    (fun u hu => (archDiagonalDensity_pos (lt_trans ha hu)).le) hlim

/-- `N(a) ≥ −½ log(2a)`. -/
theorem neg_half_log_one_sub_exp_ge {a : ℝ} (ha : 0 < a) :
    -(1 / 2) * Real.log (2 * a) ≤ -(1 / 2) * Real.log (1 - Real.exp (-2 * a)) := by
  have hlt : Real.exp (-2 * a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hle : 1 - Real.exp (-2 * a) ≤ 2 * a := by
    have := Real.add_one_le_exp (-2 * a)
    linarith
  have := Real.log_le_log (by linarith) hle
  linarith

/-- The killing seen from the left and from the right half of the window: `∫_0^∞` of
`ν − ω 1_{u ≤ a}` is at least `N(a) − (3/4) a`. -/
theorem integral_one_sided_window_ge {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u => if u ≤ a then archDiagonalDensity u - archLevyDensity u
        else archDiagonalDensity u) (Ioi 0) ∧
      -(1 / 2) * Real.log (1 - Real.exp (-2 * a)) - 3 / 4 * a ≤
        ∫ u in Ioi (0 : ℝ), (if u ≤ a then archDiagonalDensity u - archLevyDensity u
          else archDiagonalDensity u) := by
  have hunion : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  have hmeasD : Measurable archDiagonalDensity := by unfold archDiagonalDensity; fun_prop
  have hbd : ∀ u ∈ Ioc (0 : ℝ) a, |archDiagonalDensity u - archLevyDensity u| ≤ 3 / 4 := by
    intro u hu
    have h1 := archLevyDensity_sub_archDiagonalDensity_le hu.1
    have h2 : archDiagonalDensity u ≤ archLevyDensity u := archDiagonalDensity_le hu.1
    rw [abs_le]
    constructor <;> linarith
  have hI1 : IntegrableOn (fun u => archDiagonalDensity u - archLevyDensity u) (Ioc 0 a) := by
    refine Measure.integrableOn_of_bounded (M := 3 / 4) (by simp)
      ((hmeasD.sub measurable_archLevyDensity).aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => by
      rw [Real.norm_eq_abs]; exact hbd u hu)
  have hI2 := integrableOn_Ioi_archDiagonalDensity ha
  have hpiece1 : IntegrableOn (fun u => if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u) (Ioc 0 a) :=
    hI1.congr_fun (fun u hu => by rw [if_pos hu.2]) measurableSet_Ioc
  have hpiece2 : IntegrableOn (fun u => if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u) (Ioi a) :=
    hI2.congr_fun (fun u hu => by rw [if_neg (not_le.mpr hu)]) measurableSet_Ioi
  have hint : IntegrableOn (fun u => if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u) (Ioi 0) := by
    rw [hunion]
    exact hpiece1.union hpiece2
  refine ⟨hint, ?_⟩
  rw [hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hpiece1 hpiece2]
  have e1 : (∫ u in Ioc 0 a, (if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u)) = ∫ u in Ioc 0 a, (archDiagonalDensity u - archLevyDensity u) :=
    setIntegral_congr_fun measurableSet_Ioc fun u hu => by rw [if_pos hu.2]
  have e2 : (∫ u in Ioi a, (if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u)) = ∫ u in Ioi a, archDiagonalDensity u :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => by rw [if_neg (not_le.mpr hu)]
  have hlow : -(3 / 4) * a ≤ ∫ u in Ioc 0 a, (archDiagonalDensity u - archLevyDensity u) := by
    have h := setIntegral_mono_on (integrableOn_const (C := -(3 / 4 : ℝ)) (by simp)) hI1
      measurableSet_Ioc fun u hu => by
        have := hbd u hu
        rw [abs_le] at this
        exact this.1
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul] at h
    linarith
  rw [e1, e2, integral_Ioi_archDiagonalDensity ha]
  linarith

/-! ### The potential of a plateau gauge -/

section Gauge

variable {M : ℝ → ℝ} {K R : ℝ} (hMc : Continuous M) (hLip : ∀ a b, |M a - M b| ≤ K * |a - b|)
  (hnn : ∀ y, 0 ≤ M y) (hle : ∀ y, M y ≤ 1) (hsupp : ∀ y, R ≤ |y| → M y = 0)

include hMc hLip hle hsupp in
/-- **The archimedean integral at a plateau point.** If `M(x) = 1`, `|x| < R`, then
`∫_0^∞ profileArchTerm ≥ N(R − x) + N(R + x) − (3/2) R`. -/
theorem integral_profileArchTerm_ge {x : ℝ} (hx : |x| < R) (hMx : M x = 1) :
    -(1 / 2) * Real.log (1 - Real.exp (-2 * (R - x))) +
        -(1 / 2) * Real.log (1 - Real.exp (-2 * (R + x))) - 3 / 2 * R ≤
      ∫ u in Ioi (0 : ℝ), profileArchTerm M x u := by
  have ha : 0 < R - x := by linarith [le_abs_self x]
  have hb : 0 < R + x := by linarith [neg_abs_le x]
  obtain ⟨hIa, hVa⟩ := integral_one_sided_window_ge ha
  obtain ⟨hIb, hVb⟩ := integral_one_sided_window_ge hb
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (if u ≤ R - x then archDiagonalDensity u - archLevyDensity u
        else archDiagonalDensity u) +
      (if u ≤ R + x then archDiagonalDensity u - archLevyDensity u else archDiagonalDensity u) ≤
        profileArchTerm M x u := by
    intro u hu
    have hω := archLevyDensity_pos hu
    have h1 : M (x + u) ≤ if u ≤ R - x then 1 else 0 := by
      split_ifs with h
      · exact hle _
      · exact (hsupp _ (by rw [abs_of_pos (by linarith [le_abs_self x] : 0 < x + u)]; linarith)).le
    have h2 : M (x - u) ≤ if u ≤ R + x then 1 else 0 := by
      split_ifs with h
      · exact hle _
      · exact (hsupp _ (by rw [abs_of_neg (by linarith [neg_abs_le x] : x - u < 0)]; linarith)).le
    unfold profileArchTerm
    rw [hMx]
    have hm1 := mul_le_mul_of_nonneg_left h1 hω.le
    have hm2 := mul_le_mul_of_nonneg_left h2 hω.le
    split_ifs at hm1 hm2 ⊢ <;> nlinarith
  have hmono := setIntegral_mono_on (f := fun u =>
      (if u ≤ R - x then archDiagonalDensity u - archLevyDensity u else archDiagonalDensity u) +
      (if u ≤ R + x then archDiagonalDensity u - archLevyDensity u else archDiagonalDensity u))
    (hIa.add hIb) (integrableOn_profileArchTerm hMc hLip x) measurableSet_Ioi hpt
  rw [integral_add hIa hIb] at hmono
  linarith

include hsupp in
/-- On a window `2R < log 2` no prime shift of a plateau point lands in the gauge. -/
theorem profilePrimeSum_eq_zero {x : ℝ} (hR : 2 * R < Real.log 2) (hx : |x| < R) :
    profilePrimeSum M x = 0 := by
  unfold profilePrimeSum
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · unfold vonMangoldtAtom
    rw [if_neg (by omega), zero_mul]
  · have hlog : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast h2)
    rw [hsupp (x + Real.log n) ?_, hsupp (x - Real.log n) ?_, add_zero, mul_zero]
    · rw [abs_sub_comm]
      have := abs_sub_abs_le_abs_sub (Real.log n) x
      rw [abs_of_nonneg (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])] at this
      linarith
    · have := abs_sub_abs_le_abs_sub (Real.log n) (-x)
      rw [abs_of_nonneg (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]), abs_neg,
        sub_neg_eq_add, add_comm] at this
      linarith

include hMc hLip hle hsupp in
/-- **The potential of the plateau gauge.** At a plateau point,
`−𝒲M(x) ≥ −log(2R) − (3/2) R − (γ + log π)`. -/
theorem neg_poleFreeWeilOperator_ge {x : ℝ} (hR : 2 * R < Real.log 2) (hx : |x| < R)
    (hMx : M x = 1) :
    -Real.log (2 * R) - 3 / 2 * R - 2 * archConstantReal ≤ -poleFreeWeilOperator M x := by
  have ha : 0 < R - x := by linarith [le_abs_self x]
  have hb : 0 < R + x := by linarith [neg_abs_le x]
  have hI := integral_profileArchTerm_ge hMc hLip hle hsupp hx hMx
  have hNa := neg_half_log_one_sub_exp_ge ha
  have hNb := neg_half_log_one_sub_exp_ge hb
  have hprod : Real.log (2 * (R - x)) + Real.log (2 * (R + x)) ≤ 2 * Real.log (2 * R) := by
    rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_rpow (by linarith),
      Real.rpow_two]
    exact Real.log_le_log (by positivity) (by nlinarith [sq_nonneg x])
  unfold poleFreeWeilOperator
  rw [profilePrimeSum_eq_zero hsupp hR hx, hMx]
  linarith

end Gauge

/-! ### Numerical constants -/

theorem log_pi_lt : Real.log Real.pi < 1.15 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.15)
  have h3 : Real.exp 1.15 = Real.exp 1 * Real.exp 0.15 := by
    rw [← Real.exp_add]; norm_num
  have h4 := Real.pi_lt_d2
  rw [h3]
  nlinarith [Real.exp_pos 0.15]

theorem exp_neg_two_lt : Real.exp (-2) < 0.1355 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 2) (by norm_num), h2]
  nlinarith

/-- `2 − (3/4) e^{−2} − (γ + log π) > 0.0817`. -/
theorem two_sub_three_quarter_exp_neg_two_sub_archConstant_gt :
    0.0817 < 2 - 3 / 4 * Real.exp (-2) - 2 * archConstantReal := by
  have h1 := Real.eulerMascheroniConstant_lt_two_thirds
  have h2 := log_pi_lt
  have h3 := exp_neg_two_lt
  unfold archConstantReal
  linarith

/-! ### The odd pole moment on a window -/

theorem abs_sinh_half_le {x : ℝ} (hx : |x| ≤ 2) : |Real.sinh (x / 2)| ≤ |x| := by
  have h1 := Real.abs_exp_sub_one_le (x := x / 2) (by rw [abs_div, abs_two]; linarith)
  have h2 := Real.abs_exp_sub_one_le (x := -(x / 2)) (by rw [abs_neg, abs_div, abs_two]; linarith)
  rw [Real.sinh_eq]
  calc |(Real.exp (x / 2) - Real.exp (-(x / 2))) / 2|
      = |(Real.exp (x / 2) - 1) - (Real.exp (-(x / 2)) - 1)| / 2 := by
        rw [abs_div, abs_two]; ring_nf
    _ ≤ (|Real.exp (x / 2) - 1| + |Real.exp (-(x / 2)) - 1|) / 2 := by
        gcongr; exact abs_sub _ _
    _ ≤ (2 * |x / 2| + 2 * |-(x / 2)|) / 2 := by gcongr
    _ = |x| := by rw [abs_neg, abs_div, abs_two]; ring

theorem sq_gauge_mul_sinh_le {M : ℝ → ℝ} {R : ℝ} (hR2 : R ≤ 2) (hnn : ∀ y, 0 ≤ M y)
    (hle : ∀ y, M y ≤ 1) (hsupp : ∀ y, R ≤ |y| → M y = 0) (x : ℝ) :
    (M x * Real.sinh (x / 2)) ^ 2 ≤ Set.indicator (Icc (-R) R) (fun _ => R ^ 2) x := by
  by_cases hx : |x| < R
  · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨(abs_le.mp hx.le).1, (abs_le.mp hx.le).2⟩)]
    have h1 := abs_sinh_half_le (by linarith : |x| ≤ 2)
    have h2 : |M x * Real.sinh (x / 2)| ≤ R := by
      rw [abs_mul, abs_of_nonneg (hnn x)]
      calc M x * |Real.sinh (x / 2)| ≤ 1 * |x| :=
            mul_le_mul (hle x) h1 (abs_nonneg _) zero_le_one
        _ ≤ R := by linarith
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  · rw [hsupp x (not_lt.mp hx), zero_mul, zero_pow two_ne_zero]
    exact Set.indicator_nonneg (fun _ _ => sq_nonneg R) x

theorem integral_indicator_Icc_sq {R : ℝ} (hR0 : 0 ≤ R) :
    ∫ x, Set.indicator (Icc (-R) R) (fun _ => R ^ 2) x = 2 * R ^ 3 := by
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
    Real.volume_real_Icc, max_eq_left (by linarith)]
  ring

/-- **The odd pole moment on a window.** If `F` vanishes off the set where a continuous compactly
supported `0 ≤ M ≤ 1` equals `1`, and `M = 0` outside `(−R, R)`, `R ≤ 2`, then `S(F)² ≤ 2R³ ∫ F²`. -/
theorem sq_oddPoleMoment_le {F M : ℝ → ℝ} {R : ℝ} (hR0 : 0 ≤ R) (hR2 : R ≤ 2) (hF : Continuous F)
    (hFc : HasCompactSupport F) (hMc : Continuous M) (hMcs : HasCompactSupport M)
    (hnn : ∀ y, 0 ≤ M y) (hle : ∀ y, M y ≤ 1) (hsupp : ∀ y, R ≤ |y| → M y = 0)
    (hFM : ∀ x, F x ≠ 0 → M x = 1) :
    oddPoleMoment F ^ 2 ≤ 2 * R ^ 3 * ∫ x, F x ^ 2 := by
  have hGc : Continuous fun x => M x * Real.sinh (x / 2) :=
    hMc.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hS : oddPoleMoment F = ∫ x, F x * (M x * Real.sinh (x / 2)) := by
    unfold oddPoleMoment
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases h : F x = 0
    · simp only [h, zero_mul]
    · simp only [hFM x h, one_mul]
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hGcs : HasCompactSupport fun x => M x * Real.sinh (x / 2) := hMcs.mul_right
  have hG2 : Integrable fun x => (M x * Real.sinh (x / 2)) ^ 2 :=
    (hGc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hGcs)
  have hCS := GaloisForLFunctions.HTGeometry.sq_integral_mul_le hF.aestronglyMeasurable
    hGc.aestronglyMeasurable hF2 hG2
  have hGb : ∫ x, (M x * Real.sinh (x / 2)) ^ 2 ≤ 2 * R ^ 3 := by
    rw [← integral_indicator_Icc_sq hR0]
    exact integral_mono hG2 ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simp))) (sq_gauge_mul_sinh_le hR2 hnn hle hsupp)
  rw [hS]
  calc (∫ x, F x * (M x * Real.sinh (x / 2))) ^ 2 ≤
      (∫ x, F x ^ 2) * ∫ x, (M x * Real.sinh (x / 2)) ^ 2 := hCS
    _ ≤ (∫ x, F x ^ 2) * (2 * R ^ 3) :=
        mul_le_mul_of_nonneg_left hGb (integral_nonneg fun x => sq_nonneg _)
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
