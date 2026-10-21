import GaloisForLFunctions.ArithmeticCriticalityTheory.CurvedGaugeArchimedeanBounds

/-!
# The potential of a curved window gauge

For `c ≥ 0` and `0 < δ < R ≤ 1/4` with `c R² ≤ 1`, let `q(y) = 1 − c y²` and let `P` be the plateau of
radius `R` with collar `δ`. The curved gauge `M = q P` (`curvedWindowGauge c R δ`) has, at a plateau
point `|x| ≤ R − δ` (`neg_poleFreeWeilOperator_curvedWindowGauge_ge`),

    −𝒲M(x) ≥ q(x) [N(a) + N(b) − (3/4)(a + b) + (a² + b²)/12 − (γ + log π)]
              + c [G(a) + G(b) − 2(1 + R/2) x²],          a = R − x, b = R + x,

`N(s) = −½ log(1 − e^{−2s})`, `G(s) = s²/4 + s³/12 − s⁴/64 ≤ ∫_0^s u² ω`. The term `c G` is the regional
jump energy kept by the curvature; `−2c(1 + R/2) x²` is the price of the asymmetric window
(`∫_a^b u ω ≤ (b − a)/2 + (b² − a²)/8`). With `N(s) ≥ −½ log(2s) + s/2 − s²/12` the bracket is at least
`−log(2R) − R/2 − (γ + log π) − ½ log(1 − x²/R²)` (`curvedGauge_bracket_ge`): the second-order terms
cancel. The pole mass is `∫ M(y) cosh((x − y)/2) dy ≥ 2r − (2c/3) r³`, `r = R − δ`
(`integral_curvedWindowGauge_cosh_ge`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The gauge -/

/-- The curvature profile `q(y) = 1 − c y²`. -/
def curvedProfile (c y : ℝ) : ℝ := 1 - c * y ^ 2

/-- The curved window gauge `q P`, `P` the plateau of radius `R` with collar `δ`. -/
def curvedWindowGauge (c R δ y : ℝ) : ℝ := curvedProfile c y * plateauGauge R δ y

theorem contDiff_curvedProfile (c : ℝ) : ContDiff ℝ 2 (curvedProfile c) := by
  unfold curvedProfile
  exact contDiff_const.sub (contDiff_const.mul (contDiff_id.pow 2))

theorem contDiff_curvedWindowGauge (c R δ : ℝ) : ContDiff ℝ 2 (curvedWindowGauge c R δ) :=
  (contDiff_curvedProfile c).mul (contDiff_plateauGauge _ _)

theorem hasCompactSupport_curvedWindowGauge (c R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (curvedWindowGauge c R δ) :=
  (hasCompactSupport_plateauGauge hδ).mul_left

theorem curvedProfile_neg (c y : ℝ) : curvedProfile c (-y) = curvedProfile c y := by
  unfold curvedProfile; ring

theorem curvedWindowGauge_neg (c R δ y : ℝ) :
    curvedWindowGauge c R δ (-y) = curvedWindowGauge c R δ y := by
  simp only [curvedWindowGauge, curvedProfile, plateauGauge, sub_neg_eq_add, ← sub_eq_add_neg, neg_sq]
  ring

theorem curvedProfile_ge_of_le {c R y : ℝ} (hc : 0 ≤ c) (hy : |y| ≤ R) :
    1 - c * R ^ 2 ≤ curvedProfile c y := by
  unfold curvedProfile
  have : y ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  nlinarith [mul_le_mul_of_nonneg_left this hc]

theorem curvedProfile_le {c : ℝ} (hc : 0 ≤ c) (y : ℝ) : curvedProfile c y ≤ 1 := by
  unfold curvedProfile; nlinarith [mul_nonneg hc (sq_nonneg y)]

theorem curvedWindowGauge_eq_zero (c : ℝ) {R δ y : ℝ} (hδ : 0 < δ) (hy : R ≤ |y|) :
    curvedWindowGauge c R δ y = 0 := by
  unfold curvedWindowGauge
  rw [plateauGauge_eq_zero hδ hy, mul_zero]

theorem curvedWindowGauge_eq (c : ℝ) {R δ y : ℝ} (hδ : 0 < δ) (hy : |y| ≤ R - δ) :
    curvedWindowGauge c R δ y = curvedProfile c y := by
  unfold curvedWindowGauge
  rw [plateauGauge_eq_one hδ hy, mul_one]

theorem curvedWindowGauge_le_profile {c R δ y : ℝ} (hc : 0 ≤ c) (hcR : c * R ^ 2 ≤ 1)
    (hy : |y| ≤ R) : curvedWindowGauge c R δ y ≤ curvedProfile c y := by
  unfold curvedWindowGauge
  have hq : 0 ≤ curvedProfile c y := by linarith [curvedProfile_ge_of_le hc hy]
  nlinarith [mul_nonneg hq (by linarith [plateauGauge_le_one R δ y] : 0 ≤ 1 - plateauGauge R δ y)]

theorem curvedWindowGauge_nonneg {c R δ : ℝ} (hc : 0 ≤ c) (hcR : c * R ^ 2 ≤ 1) (hδ : 0 < δ)
    (y : ℝ) : 0 ≤ curvedWindowGauge c R δ y := by
  by_cases hy : |y| < R
  · exact mul_nonneg (by linarith [curvedProfile_ge_of_le hc hy.le]) (plateauGauge_nonneg _ _ _)
  · rw [curvedWindowGauge_eq_zero c hδ (not_lt.mp hy)]

theorem curvedWindowGauge_le_one {c R δ : ℝ} (hc : 0 ≤ c) (hcR : c * R ^ 2 ≤ 1) (hδ : 0 < δ)
    (y : ℝ) : curvedWindowGauge c R δ y ≤ 1 := by
  by_cases hy : |y| < R
  · exact (curvedWindowGauge_le_profile hc hcR hy.le).trans (curvedProfile_le hc y)
  · rw [curvedWindowGauge_eq_zero c hδ (not_lt.mp hy)]; norm_num

/-! ### The potential of the curved gauge -/

/-- The quadratic-moment floor `G(s) = s²/4 + s³/12 − s⁴/64 ≤ ∫_0^s u² ω`. -/
def sqMomentFloor (s : ℝ) : ℝ := s ^ 2 / 4 + s ^ 3 / 12 - s ^ 4 / 64

/-- **The potential of the curved gauge** at a plateau point `|x| ≤ R − δ`. -/
theorem neg_poleFreeWeilOperator_curvedWindowGauge_ge {c R δ x : ℝ} (hc : 0 ≤ c)
    (hcR : c * R ^ 2 ≤ 1) (hδ : 0 < δ) (hR : R ≤ 1 / 4) (hx : |x| ≤ R - δ) :
    curvedProfile c x *
        ((-(1 / 2) * Real.log (1 - Real.exp (-2 * (R - x))) - 3 / 4 * (R - x) +
            (R - x) ^ 2 / 12) +
          (-(1 / 2) * Real.log (1 - Real.exp (-2 * (R + x))) - 3 / 4 * (R + x) +
            (R + x) ^ 2 / 12) - 2 * archConstantReal) +
      c * (sqMomentFloor (R - x) + sqMomentFloor (R + x) - 2 * (1 + R / 2) * x ^ 2) ≤
      -poleFreeWeilOperator (curvedWindowGauge c R δ) x := by
  set M := curvedWindowGauge c R δ with hMdef
  set a : ℝ := R - x with hadef
  set b : ℝ := R + x with hbdef
  have hxR : |x| < R := by linarith
  have hx' := abs_le.mp hx
  have ha : 0 < a := by rw [hadef]; linarith
  have hb : 0 < b := by rw [hbdef]; linarith
  have ha1 : a ≤ 1 / 2 := by rw [hadef]; linarith
  have hb1 : b ≤ 1 / 2 := by rw [hbdef]; linarith
  have hMx : M x = curvedProfile c x := curvedWindowGauge_eq c hδ hx
  have hzero : ∀ y, R ≤ |y| → M y = 0 := fun y hy => curvedWindowGauge_eq_zero c hδ hy
  have hq0 : 0 ≤ curvedProfile c x := by linarith [curvedProfile_ge_of_le hc hxR.le]
  have hprime : profilePrimeSum M x = 0 :=
    profilePrimeSum_eq_zero hzero (by have := Real.log_two_gt_d9; linarith) hxR
  obtain ⟨hIa, hVa⟩ := integral_one_sided_window_ge_sharp ha (by linarith)
  obtain ⟨hIb, hVb⟩ := integral_one_sided_window_ge_sharp hb (by linarith)
  -- regional integrands
  set ra : ℝ → ℝ := (Ioc 0 a).indicator fun u => archLevyDensity u * (2 * x * u + u ^ 2) with hra
  set rb : ℝ → ℝ := (Ioc 0 b).indicator fun u => archLevyDensity u * (u ^ 2 - 2 * x * u) with hrb
  have hoa : IntegrableOn (fun u => archLevyDensity u * (2 * x * u + u ^ 2)) (Ioc 0 a) := by
    have h : IntegrableOn (fun u => 2 * x * (u * archLevyDensity u) + u ^ 2 * archLevyDensity u)
        (Ioc 0 a) := ((integrableOn_mul_archLevyDensity le_rfl (by linarith)).const_mul (2 * x)).add
      (integrableOn_sq_mul_archLevyDensity (by linarith))
    exact h.congr_fun (fun u _ => by ring) measurableSet_Ioc
  have hob : IntegrableOn (fun u => archLevyDensity u * (u ^ 2 - 2 * x * u)) (Ioc 0 b) := by
    have h : IntegrableOn (fun u => u ^ 2 * archLevyDensity u - 2 * x * (u * archLevyDensity u))
        (Ioc 0 b) := (integrableOn_sq_mul_archLevyDensity (by linarith)).sub
      ((integrableOn_mul_archLevyDensity le_rfl (by linarith)).const_mul (2 * x))
    exact h.congr_fun (fun u _ => by ring) measurableSet_Ioc
  have hia : IntegrableOn ra (Ioi 0) := (hoa.integrable_indicator measurableSet_Ioc).integrableOn
  have hib : IntegrableOn rb (Ioi 0) := (hob.integrable_indicator measurableSet_Ioc).integrableOn
  -- pointwise domination
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      curvedProfile c x * ((if u ≤ a then archDiagonalDensity u - archLevyDensity u
          else archDiagonalDensity u) +
        (if u ≤ b then archDiagonalDensity u - archLevyDensity u else archDiagonalDensity u)) +
        c * (ra u + rb u) ≤ profileArchTerm M x u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hω := archLevyDensity_pos hu0
    have h1 : M (x + u) ≤ if u ≤ a then curvedProfile c (x + u) else 0 := by
      split_ifs with h
      · exact curvedWindowGauge_le_profile hc hcR
          (abs_le.mpr ⟨by linarith, by rw [hadef] at h; linarith⟩)
      · exact (hzero _ (by rw [abs_of_pos (by linarith : 0 < x + u)]; rw [hadef] at h; linarith)).le
    have h2 : M (x - u) ≤ if u ≤ b then curvedProfile c (x - u) else 0 := by
      split_ifs with h
      · exact curvedWindowGauge_le_profile hc hcR
          (abs_le.mpr ⟨by rw [hbdef] at h; linarith, by linarith⟩)
      · exact (hzero _ (by rw [abs_of_neg (by linarith : x - u < 0)]; rw [hbdef] at h; linarith)).le
    set ω := archLevyDensity u with hωdef
    have e1 : ω * curvedProfile c x - ω * curvedProfile c (x + u) =
        c * (ω * (2 * x * u + u ^ 2)) := by unfold curvedProfile; ring
    have e2 : ω * curvedProfile c x - ω * curvedProfile c (x - u) =
        c * (ω * (u ^ 2 - 2 * x * u)) := by unfold curvedProfile; ring
    unfold profileArchTerm
    rw [hMx, hra, hrb, ← hωdef]
    have hm1 := mul_le_mul_of_nonneg_left h1 hω.le
    have hm2 := mul_le_mul_of_nonneg_left h2 hω.le
    by_cases hua : u ≤ a <;> by_cases hub : u ≤ b
    · rw [Set.indicator_of_mem (show u ∈ Ioc 0 a from ⟨hu0, hua⟩),
        Set.indicator_of_mem (show u ∈ Ioc 0 b from ⟨hu0, hub⟩), if_pos hua, if_pos hub]
      rw [if_pos hua] at hm1; rw [if_pos hub] at hm2
      linarith
    · rw [Set.indicator_of_mem (show u ∈ Ioc 0 a from ⟨hu0, hua⟩),
        Set.indicator_of_notMem (fun h => hub h.2), if_pos hua, if_neg hub]
      rw [if_pos hua] at hm1; rw [if_neg hub, mul_zero] at hm2
      linarith
    · rw [Set.indicator_of_notMem (fun h => hua h.2),
        Set.indicator_of_mem (show u ∈ Ioc 0 b from ⟨hu0, hub⟩), if_neg hua, if_pos hub]
      rw [if_neg hua, mul_zero] at hm1; rw [if_pos hub] at hm2
      linarith
    · rw [Set.indicator_of_notMem (fun h => hua h.2), Set.indicator_of_notMem (fun h => hub h.2),
        if_neg hua, if_neg hub]
      rw [if_neg hua, mul_zero] at hm1; rw [if_neg hub, mul_zero] at hm2
      linarith
  obtain ⟨K, -, hK⟩ := exists_lipschitz_bound_of_compactSupport
    ((contDiff_curvedWindowGauge c R δ).of_le (by norm_num))
    (hasCompactSupport_curvedWindowGauge c R hδ)
  have hLip : ∀ a b, |M a - M b| ≤ K * |a - b| := fun a b => hK b a
  set ga : ℝ → ℝ := fun u => if u ≤ a then archDiagonalDensity u - archLevyDensity u
    else archDiagonalDensity u with hgadef
  set gb : ℝ → ℝ := fun u => if u ≤ b then archDiagonalDensity u - archLevyDensity u
    else archDiagonalDensity u with hgbdef
  have hg2 : IntegrableOn (fun u => curvedProfile c x * (ga u + gb u)) (Ioi 0) :=
    (hIa.add hIb).const_mul _
  have hr2 : IntegrableOn (fun u => c * (ra u + rb u)) (Ioi 0) := (hia.add hib).const_mul _
  have hL : IntegrableOn (fun u => curvedProfile c x * (ga u + gb u) + c * (ra u + rb u))
      (Ioi 0) := hg2.add hr2
  have hmono := setIntegral_mono_on hL
    (integrableOn_profileArchTerm (contDiff_curvedWindowGauge c R δ).continuous hLip x)
      measurableSet_Ioi hpt
  have eL : (∫ u in Ioi (0 : ℝ), (curvedProfile c x * (ga u + gb u) + c * (ra u + rb u))) =
      curvedProfile c x * ((∫ u in Ioi (0 : ℝ), ga u) + ∫ u in Ioi (0 : ℝ), gb u) +
        c * ((∫ u in Ioi (0 : ℝ), ra u) + ∫ u in Ioi (0 : ℝ), rb u) := by
    rw [integral_add hg2 hr2, integral_const_mul, integral_const_mul, integral_add hIa hIb,
      integral_add hia hib]
  rw [eL] at hmono
  -- the regional integrals
  have eIa : (∫ u in Ioi (0 : ℝ), ra u) =
      ∫ u in Ioc 0 a, archLevyDensity u * (2 * x * u + u ^ 2) := by
    rw [hra, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self]
  have eIb : (∫ u in Ioi (0 : ℝ), rb u) =
      ∫ u in Ioc 0 b, archLevyDensity u * (u ^ 2 - 2 * x * u) := by
    rw [hrb, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self]
  have hsplit : ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∀ s : ℝ,
      (∫ u in Ioc 0 c, archLevyDensity u * (s * u + u ^ 2)) =
        s * (∫ u in Ioc 0 c, u * archLevyDensity u) + ∫ u in Ioc 0 c, u ^ 2 * archLevyDensity u := by
    intro c hc hc1 s
    rw [← integral_const_mul, ← integral_add ((integrableOn_mul_archLevyDensity le_rfl
      (by linarith)).const_mul s) (integrableOn_sq_mul_archLevyDensity (by linarith))]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    ring
  have hIa' := hsplit a ha ha1 (2 * x)
  have hIb' : (∫ u in Ioc 0 b, archLevyDensity u * (u ^ 2 - 2 * x * u)) =
      (-(2 * x)) * (∫ u in Ioc 0 b, u * archLevyDensity u) +
        ∫ u in Ioc 0 b, u ^ 2 * archLevyDensity u := by
    rw [← hsplit b hb hb1 (-(2 * x))]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    ring
  have hGa := integral_sq_mul_archLevyDensity_ge ha (by linarith)
  have hGb := integral_sq_mul_archLevyDensity_ge hb (by linarith)
  -- the `x`-linear part
  have hlin : -(x * (x + R / 2 * x)) ≤
      x * ((∫ u in Ioc 0 a, u * archLevyDensity u) - ∫ u in Ioc 0 b, u * archLevyDensity u) := by
    rcases le_or_gt 0 x with h0 | h0
    · have hab : a ≤ b := by rw [hadef, hbdef]; linarith
      have hU : (∫ u in Ioc 0 b, u * archLevyDensity u) =
          (∫ u in Ioc 0 a, u * archLevyDensity u) + ∫ u in Ioc a b, u * archLevyDensity u := by
        rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
          (integrableOn_mul_archLevyDensity le_rfl (by linarith))
          (integrableOn_mul_archLevyDensity ha.le (by linarith)), Ioc_union_Ioc_eq_Ioc ha.le hab]
      have hle := integral_mul_archLevyDensity_le ha.le hab (by linarith)
      rw [hU]
      have e : (b - a) / 2 + (b ^ 2 - a ^ 2) / 8 = x + R / 2 * x := by rw [hadef, hbdef]; ring
      rw [e] at hle
      have := mul_le_mul_of_nonneg_left hle h0
      linarith
    · have hba : b ≤ a := by rw [hadef, hbdef]; linarith
      have hU : (∫ u in Ioc 0 a, u * archLevyDensity u) =
          (∫ u in Ioc 0 b, u * archLevyDensity u) + ∫ u in Ioc b a, u * archLevyDensity u := by
        rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
          (integrableOn_mul_archLevyDensity le_rfl (by linarith))
          (integrableOn_mul_archLevyDensity hb.le (by linarith)), Ioc_union_Ioc_eq_Ioc hb.le hba]
      have hle := integral_mul_archLevyDensity_le hb.le hba (by linarith)
      rw [hU]
      have e : (a - b) / 2 + (a ^ 2 - b ^ 2) / 8 = -(x + R / 2 * x) := by rw [hadef, hbdef]; ring
      rw [e] at hle
      have := mul_le_mul_of_nonpos_left hle h0.le
      linarith
  -- assemble
  have hW : -poleFreeWeilOperator M x = (∫ u in Ioi (0 : ℝ), profileArchTerm M x u) -
      2 * archConstantReal * curvedProfile c x := by
    unfold poleFreeWeilOperator
    rw [hprime, hMx]
    ring
  rw [hW]
  rw [eIa, eIb, hIa', hIb'] at hmono
  have hqV := mul_le_mul_of_nonneg_left (add_le_add hVa hVb) hq0
  have hinner : sqMomentFloor a + sqMomentFloor b - 2 * (1 + R / 2) * x ^ 2 ≤
      (2 * x * (∫ u in Ioc 0 a, u * archLevyDensity u) +
          ∫ u in Ioc 0 a, u ^ 2 * archLevyDensity u) +
        ((-(2 * x)) * (∫ u in Ioc 0 b, u * archLevyDensity u) +
          ∫ u in Ioc 0 b, u ^ 2 * archLevyDensity u) := by
    unfold sqMomentFloor
    linarith [hGa, hGb, hlin]
  have hcI := mul_le_mul_of_nonneg_left hinner hc
  linarith [hqV, hmono, hcI]

/-! ### The killing bracket and the pole mass -/

/-- The killing bracket is at least `−log(2R) − R/2 − 2C − ½ log(1 − x²/R²)`: with
`N(s) ≥ −½ log(2s) + s/2 − s²/12` the second-order terms cancel. -/
theorem curvedGauge_bracket_ge {R x : ℝ} (hR0 : 0 < R) (hR : R ≤ 1 / 2) (hx : |x| < R) :
    -Real.log (2 * R) - R / 2 - 2 * archConstantReal + -(1 / 2) * Real.log (1 - x ^ 2 / R ^ 2) ≤
      (-(1 / 2) * Real.log (1 - Real.exp (-2 * (R - x))) - 3 / 4 * (R - x) + (R - x) ^ 2 / 12) +
        (-(1 / 2) * Real.log (1 - Real.exp (-2 * (R + x))) - 3 / 4 * (R + x) + (R + x) ^ 2 / 12) -
          2 * archConstantReal := by
  have hx' := abs_lt.mp hx
  have ha : 0 < R - x := by linarith
  have hb : 0 < R + x := by linarith
  have hNa := neg_half_log_one_sub_exp_ge_sharp ha (by linarith)
  have hNb := neg_half_log_one_sub_exp_ge_sharp hb (by linarith)
  have hRne : R ≠ 0 := hR0.ne'
  have h1 : 0 < 1 - x ^ 2 / R ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]
    exact sq_lt_sq' hx'.1 hx'.2
  have hlog : Real.log (2 * (R - x)) + Real.log (2 * (R + x)) =
      2 * Real.log (2 * R) + Real.log (1 - x ^ 2 / R ^ 2) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      show 2 * (R - x) * (2 * (R + x)) = (2 * R) ^ 2 * (1 - x ^ 2 / R ^ 2) by field_simp; ring,
      Real.log_mul (by positivity) h1.ne', Real.log_pow]
    push_cast
    ring
  linarith

/-- `∫ M(y) cosh((x − y)/2) dy ≥ ∫_{−r}^{r} q = 2r − (2c/3) r³`, `r = R − δ`. -/
theorem integral_curvedWindowGauge_cosh_ge {c R δ : ℝ} (hc : 0 ≤ c) (hcR : c * R ^ 2 ≤ 1)
    (hδ : 0 < δ) (hδR : δ ≤ R) (x : ℝ) :
    2 * (R - δ) - 2 / 3 * c * (R - δ) ^ 3 ≤
      ∫ y, curvedWindowGauge c R δ y * Real.cosh ((x - y) / 2) := by
  set r : ℝ := R - δ with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hint : Integrable fun y => curvedWindowGauge c R δ y * Real.cosh ((x - y) / 2) :=
    ((contDiff_curvedWindowGauge c R δ).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_curvedWindowGauge c R hδ).mul_right
  have hset : (∫ y in Icc (-r) r, curvedWindowGauge c R δ y * Real.cosh ((x - y) / 2)) ≤
      ∫ y, curvedWindowGauge c R δ y * Real.cosh ((x - y) / 2) :=
    setIntegral_le_integral hint (Eventually.of_forall fun y =>
      mul_nonneg (curvedWindowGauge_nonneg hc hcR hδ y) (Real.cosh_pos _).le)
  have hq : IntegrableOn (curvedProfile c) (Icc (-r) r) :=
    (contDiff_curvedProfile c).continuous.integrableOn_Icc
  have hlow : (∫ y in Icc (-r) r, curvedProfile c y) ≤
      ∫ y in Icc (-r) r, curvedWindowGauge c R δ y * Real.cosh ((x - y) / 2) :=
    setIntegral_mono_on hq hint.integrableOn measurableSet_Icc fun y hy => by
      have hy' : -r ≤ y ∧ y ≤ r := hy
      rw [curvedWindowGauge_eq c hδ (abs_le.mpr hy')]
      have h1 := Real.one_le_cosh ((x - y) / 2)
      have h0 : 0 ≤ curvedProfile c y := by
        have := curvedProfile_ge_of_le hc
          (abs_le.mpr ⟨by linarith [hy'.1], by linarith [hy'.2]⟩ : |y| ≤ R)
        linarith
      nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ Real.cosh ((x - y) / 2) - 1)]
  have hval : (∫ y in Icc (-r) r, curvedProfile c y) = 2 * r - 2 / 3 * c * r ^ 3 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    unfold curvedProfile
    rw [intervalIntegral.integral_sub (f := fun _ => (1 : ℝ)) (g := fun x : ℝ => c * x ^ 2)
      intervalIntegrable_const ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow]
    simp only [smul_eq_mul]
    push_cast
    ring
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory
