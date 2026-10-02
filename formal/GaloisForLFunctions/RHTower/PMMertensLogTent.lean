import GaloisForLFunctions.RHTower.PMLogMobiusMellinPair
import GaloisForLFunctions.RHTower.ChronologicalWeightedBoundary
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Mertens window oscillation that survives scalar centering

For every fixed `q > 1`, arbitrarily large integer cutoffs `N` have a
positive lower bound for `∫_(N,q²N] ((M(⌊t⌋)-c)/t)²`, simultaneously for
every real center `c`.

The logarithmic tent has Mellin transform `(1-q^(-s))²/s²`, nonzero in
`Re(s)>0`. Its exact Möbius source is the difference of two adjacent
logarithmic Mertens integrals. The critical source floor therefore survives
constant centering. A Lipschitz estimate transfers the floor to integer
cutoffs. These statements are unconditional; PM witness positivity remains
a separate open problem.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace RHTower

def pmWindowLogBase (t : ℝ) : ℂ := pmLogarithmicRamp t⁻¹

theorem hasMellin_pmWindowLogBase {s : ℂ} (hs : 0 < s.re) :
    HasMellin pmWindowLogBase s (1 / s ^ 2) := by
  constructor
  · change MellinConvergent (fun t : ℝ => pmLogarithmicRamp t⁻¹) s
    have h := (MellinConvergent.comp_rpow (s := s)
      (f := pmLogarithmicRamp) (by norm_num : (-1 : ℝ) ≠ 0)).mpr
        (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one]
          using (hasMellin_pmLogarithmicRamp hs).1)
    simpa only [Real.rpow_neg_one] using h
  · exact (mellin_comp_inv pmLogarithmicRamp s).trans
      (hasMellin_pmLogarithmicRamp hs).2

def pmWindowLogTent (q t : ℝ) : ℂ :=
  pmWindowLogBase t - 2 * pmWindowLogBase (q * t) + pmWindowLogBase (q ^ 2 * t)

theorem hasMellin_pmWindowLogTent {q : ℝ} (hq : 0 < q)
    {s : ℂ} (hs : 0 < s.re) :
    HasMellin (pmWindowLogTent q) s ((1 - (q : ℂ) ^ (-s)) ^ 2 / s ^ 2) := by
  have h0 := hasMellin_pmWindowLogBase hs
  have h1 := (MellinConvergent.comp_mul_left hq).mpr h0.1
  have h2 := (MellinConvergent.comp_mul_left (sq_pos_of_pos hq)).mpr h0.1
  have hi0 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * pmWindowLogBase t)
      (Ioi 0) := by simpa only [MellinConvergent, smul_eq_mul] using h0.1
  have hi1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * pmWindowLogBase (q * t))
      (Ioi 0) := by simpa only [MellinConvergent, smul_eq_mul] using h1
  have hi2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * pmWindowLogBase (q ^ 2 * t))
      (Ioi 0) := by simpa only [MellinConvergent, smul_eq_mul] using h2
  have hf : (fun t : ℝ => (t : ℂ) ^ (s - 1) * pmWindowLogTent q t) =
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * pmWindowLogBase t -
        (2 : ℂ) * ((t : ℂ) ^ (s - 1) * pmWindowLogBase (q * t)) +
        (t : ℂ) ^ (s - 1) * pmWindowLogBase (q ^ 2 * t)) := by
    funext t
    simp only [pmWindowLogTent]
    ring
  constructor
  · change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * pmWindowLogTent q t) (Ioi 0)
    rw [hf]
    exact (hi0.sub (hi1.const_mul (2 : ℂ))).add hi2
  · change (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * pmWindowLogTent q t) = _
    have ha := integral_add (hi0.sub (hi1.const_mul (2 : ℂ))) hi2
    simp only [Pi.sub_apply] at ha
    rw [hf, ha,
      integral_sub hi0 (hi1.const_mul (2 : ℂ)), integral_const_mul]
    change mellin pmWindowLogBase s -
      2 * mellin (fun t => pmWindowLogBase (q * t)) s +
      mellin (fun t => pmWindowLogBase (q ^ 2 * t)) s = _
    rw [mellin_comp_mul_left pmWindowLogBase s hq,
      mellin_comp_mul_left pmWindowLogBase s (sq_pos_of_pos hq), h0.2]
    have hp : ((q ^ 2 : ℝ) : ℂ) ^ (-s) = ((q : ℂ) ^ (-s)) ^ 2 := by
      rw [pow_two, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hq.le hq.le]
      ring
    rw [hp]
    simp only [smul_eq_mul]
    ring

theorem mellin_pmWindowLogTent_ne_zero {q : ℝ} (hq : 1 < q)
    {s : ℂ} (hs : 0 < s.re) : mellin (pmWindowLogTent q) s ≠ 0 := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  rw [(hasMellin_pmWindowLogTent hq0 hs).2]
  have hp : ‖(q : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)
  have hp1 : (q : ℂ) ^ (-s) ≠ 1 := by
    intro he
    simp only [he, norm_one, lt_self_iff_false] at hp
  have hs0 : s ≠ 0 := by
    intro he
    simp only [he, Complex.zero_re, lt_self_iff_false] at hs
  exact div_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hp1.symm)) (pow_ne_zero 2 hs0)

theorem measurable_pmWindowLogBase : Measurable pmWindowLogBase := by
  unfold pmWindowLogBase pmLogarithmicRamp
  exact ((Complex.measurable_ofReal.comp Real.measurable_log).indicator
    measurableSet_Ioi).comp measurable_inv

theorem measurable_pmWindowLogTent (q : ℝ) : Measurable (pmWindowLogTent q) := by
  exact (measurable_pmWindowLogBase.sub
    ((measurable_pmWindowLogBase.comp (measurable_const.mul measurable_id)).const_mul 2)).add
      (measurable_pmWindowLogBase.comp (measurable_const.mul measurable_id))

theorem pmWindowLogBase_eq_max {t : ℝ} (ht : 0 < t) :
    pmWindowLogBase t = ((max (-Real.log t) 0 : ℝ) : ℂ) := by
  by_cases ht1 : 1 ≤ t
  · have hi : t⁻¹ ≤ 1 := by
      have h := (div_le_iff₀ ht).2 (show (1 : ℝ) ≤ 1 * t by simpa using ht1)
      simpa only [one_div] using h
    have hl : -Real.log t ≤ 0 := neg_nonpos.mpr (Real.log_nonneg ht1)
    simp [pmWindowLogBase, pmLogarithmicRamp, not_lt.mpr hi, max_eq_right hl]
  · have ht1' : t ≤ 1 := (lt_of_not_ge ht1).le
    have hi : 1 ≤ t⁻¹ := by
      have h := (le_div_iff₀ ht).2 (show 1 * t ≤ (1 : ℝ) by simpa using ht1')
      simpa only [one_div] using h
    have hl : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos ht.le ht1')
    rw [pmWindowLogBase, pmLogarithmicRamp_of_one_le hi, Real.log_inv,
      max_eq_left hl, Complex.ofReal_neg]

private theorem logTentReal_bounds (a u : ℝ) (ha : 0 ≤ a) :
    0 ≤ max u 0 - 2 * max (u - a) 0 + max (u - 2 * a) 0 ∧
      max u 0 - 2 * max (u - a) 0 + max (u - 2 * a) 0 ≤ a := by
  rcases le_or_gt u 0 with hu | hu
  · simp only [max_eq_right hu, max_eq_right (by linarith : u - a ≤ 0),
      max_eq_right (by linarith : u - 2 * a ≤ 0)]
    constructor <;> linarith
  · rcases le_or_gt u a with hua | hua
    · simp only [max_eq_left hu.le, max_eq_right (sub_nonpos.mpr hua),
        max_eq_right (by linarith : u - 2 * a ≤ 0)]
      constructor <;> linarith
    · rcases le_or_gt u (2 * a) with hua2 | hua2
      · simp only [max_eq_left hu.le, max_eq_left (by linarith : 0 ≤ u - a),
          max_eq_right (sub_nonpos.mpr hua2)]
        constructor <;> linarith
      · simp only [max_eq_left hu.le, max_eq_left (by linarith : 0 ≤ u - a),
          max_eq_left (by linarith : 0 ≤ u - 2 * a)]
        constructor <;> linarith

theorem norm_pmWindowLogTent_le {q : ℝ} (hq : 1 ≤ q) {t : ℝ} (ht : 0 < t) :
    ‖pmWindowLogTent q t‖ ≤ Real.log q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  let a := Real.log q
  let u := -Real.log t
  have he1 : -Real.log (q * t) = u - a := by
    rw [Real.log_mul hq0.ne' ht.ne']
    dsimp only [u, a]
    ring
  have he2 : -Real.log (q ^ 2 * t) = u - 2 * a := by
    rw [Real.log_mul (pow_ne_zero 2 hq0.ne') ht.ne', Real.log_pow]
    dsimp only [u, a]
    push_cast
    ring
  have he : pmWindowLogTent q t =
      ((max u 0 - 2 * max (u - a) 0 + max (u - 2 * a) 0 : ℝ) : ℂ) := by
    rw [pmWindowLogTent, pmWindowLogBase_eq_max ht,
      pmWindowLogBase_eq_max (mul_pos hq0 ht),
      pmWindowLogBase_eq_max (mul_pos (sq_pos_of_pos hq0) ht), he1, he2]
    dsimp only [u]
    push_cast
    ring
  have hb := logTentReal_bounds a u (Real.log_nonneg hq)
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

theorem pmWindowLogBase_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    pmWindowLogBase t = 0 := by
  rw [pmWindowLogBase_eq_max (zero_lt_one.trans_le ht),
    max_eq_right (neg_nonpos.mpr (Real.log_nonneg ht)), Complex.ofReal_zero]

theorem pmWindowLogTent_eq_zero {q : ℝ} (hq : 1 ≤ q) {t : ℝ} (ht : 1 < t) :
    pmWindowLogTent q t = 0 := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hq2 : 1 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have hqt : 1 ≤ q * t := by
    simpa only [one_mul] using mul_le_mul hq ht.le zero_le_one hq0
  have hq2t : 1 ≤ q ^ 2 * t := by
    simpa only [one_mul] using mul_le_mul hq2 ht.le zero_le_one (sq_nonneg q)
  simp only [pmWindowLogTent, pmWindowLogBase_eq_zero_of_one_le ht.le,
    pmWindowLogBase_eq_zero_of_one_le hqt, pmWindowLogBase_eq_zero_of_one_le hq2t,
    mul_zero, sub_zero, add_zero]

theorem pmWindowLogTent_source_cofinal_critical_floor {q : ℝ} (hq : 1 < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ∃ t : ℝ,
      0 < t ∧ t < δ ∧ ε < t ^ (1 / 2 : ℝ) *
        ‖chronologicalMobiusWeightedSource (pmWindowLogTent q) t‖ := by
  obtain ⟨T₀, _hT₀, hzero⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, _hτ, hτzero⟩ := hzero T₀ le_rfl
  exact chronologicalMobiusWeightedSource_cofinal_critical_floor
    (measurable_pmWindowLogTent q) (Real.log_nonneg hq.le)
    (fun _ ht => norm_pmWindowLogTent_le hq.le ht)
    (fun _ ht => pmWindowLogTent_eq_zero hq.le ht)
    (linePt_re τ) hτzero
    (mellin_pmWindowLogTent_ne_zero hq (by rw [linePt_re]; norm_num))

theorem pmWindowLogBase_source_eq_sum_log {x : ℝ} (hx : 1 ≤ x) :
    chronologicalMobiusWeightedSource pmWindowLogBase x⁻¹ =
      ((∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (Real.log x - Real.log n) : ℝ) : ℂ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hcut : 1 < ((⌊x⌋₊ : ℝ) + 1) * x⁻¹ := by
    have h := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one x) (inv_pos.mpr hx0)
    simpa only [mul_inv_cancel₀ hx0.ne'] using h
  rw [chronologicalMobiusWeightedSource_eq_sum pmWindowLogBase ⌊x⌋₊
    (inv_pos.mpr hx0) (fun _ h => pmWindowLogBase_eq_zero_of_one_le h.le) hcut]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnx : (n : ℝ) ≤ x :=
    (Nat.le_floor_iff hx0.le).mp (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  have hnt0 : 0 < (n : ℝ) * x⁻¹ := mul_pos hnpos (inv_pos.mpr hx0)
  have hnt1 : (n : ℝ) * x⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hnx (inv_nonneg.mpr hx0.le)
    simpa only [mul_inv_cancel₀ hx0.ne'] using h
  rw [pmWindowLogBase_eq_max hnt0,
    max_eq_left (neg_nonneg.mpr (Real.log_nonpos hnt0.le hnt1)),
    Real.log_mul hnpos.ne' (inv_ne_zero hx0.ne'), Real.log_inv]
  push_cast
  ring

theorem integrableOn_pmMertens_div_Icc (x : ℝ) :
    IntegrableOn (fun t : ℝ => Sieve.mertensM ⌊t⌋₊ / t) (Icc 1 x) := by
  let c : ℕ → ℝ := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)
  have hi : IntegrableOn (fun t : ℝ => t⁻¹) (Icc 1 x) :=
    (continuousOn_id.inv₀ (fun t ht => (zero_lt_one.trans_le ht.1).ne')).integrableOn_Icc
  have h := integrableOn_mul_sum_Icc c (m := 0) zero_le_one hi
  apply h.congr_fun _ measurableSet_Icc
  intro t _ht
  simp only [Sieve.mertensM, Nat.range_succ_eq_Icc_zero, c, div_eq_mul_inv]
  ring

theorem integral_pmMertens_div_eq_sum_log (x : ℝ) :
    (∫ t in Ioc (1 : ℝ) x, Sieve.mertensM ⌊t⌋₊ / t) =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (Real.log x - Real.log n) := by
  let c : ℕ → ℝ := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)
  have hc0 : c 0 = 0 := by simp [c]
  have hd : ∀ t ∈ Icc (1 : ℝ) x, DifferentiableAt ℝ Real.log t :=
    fun t ht => (Real.hasDerivAt_log (zero_lt_one.trans_le ht.1).ne').differentiableAt
  have hi : IntegrableOn (deriv Real.log) (Icc 1 x) := by
    have h : IntegrableOn (fun t : ℝ => t⁻¹) (Icc 1 x) :=
      (continuousOn_id.inv₀ (fun t ht => (zero_lt_one.trans_le ht.1).ne')).integrableOn_Icc
    simpa only [Real.deriv_log'] using h
  have ha := sum_mul_eq_sub_integral_mul₀ c hc0 x hd hi
  simp only [Real.deriv_log, ← Nat.range_succ_eq_Icc_zero] at ha
  have he : (∫ t in Ioc (1 : ℝ) x, Sieve.mertensM ⌊t⌋₊ / t) =
      ∫ t in Ioc (1 : ℝ) x, t⁻¹ * ∑ n ∈ Finset.range (⌊t⌋₊ + 1), c n := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _ht
    simp only [Sieve.mertensM, c, div_eq_mul_inv]
    ring
  rw [he]
  change _ = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), c n * (Real.log x - Real.log n)
  have hs : (∑ n ∈ Finset.range (⌊x⌋₊ + 1), c n * (Real.log x - Real.log n)) =
      Real.log x * (∑ n ∈ Finset.range (⌊x⌋₊ + 1), c n) -
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Real.log n * c n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  rw [hs]
  linarith [ha]

theorem pmWindowLogBase_source_eq_integral_mertens {x : ℝ} (hx : 1 ≤ x) :
    chronologicalMobiusWeightedSource pmWindowLogBase x⁻¹ =
      ((∫ t in Ioc (1 : ℝ) x, Sieve.mertensM ⌊t⌋₊ / t : ℝ) : ℂ) := by
  rw [pmWindowLogBase_source_eq_sum_log hx, integral_pmMertens_div_eq_sum_log]

theorem pmWindowLogTent_source_eq_logBase {q t : ℝ} (hq : 1 ≤ q) (ht : 0 < t) :
    chronologicalMobiusWeightedSource (pmWindowLogTent q) t =
      chronologicalMobiusWeightedSource pmWindowLogBase t -
        2 * chronologicalMobiusWeightedSource pmWindowLogBase (q * t) +
        chronologicalMobiusWeightedSource pmWindowLogBase (q ^ 2 * t) := by
  let N := ⌊t⁻¹⌋₊
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hq2 : 1 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have hcut : 1 < ((N : ℝ) + 1) * t := by
    have h := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one t⁻¹) ht
    simpa only [inv_mul_cancel₀ ht.ne'] using h
  have hcutA {a : ℝ} (ha : 1 ≤ a) : 1 < ((N : ℝ) + 1) * (a * t) := by
    have hm := mul_le_mul_of_nonneg_right ha
      (show 0 ≤ ((N : ℝ) + 1) * t by positivity)
    nlinarith
  rw [chronologicalMobiusWeightedSource_eq_sum (pmWindowLogTent q) N ht
      (fun _ h => pmWindowLogTent_eq_zero hq h) hcut,
    chronologicalMobiusWeightedSource_eq_sum pmWindowLogBase N ht
      (fun _ h => pmWindowLogBase_eq_zero_of_one_le h.le) hcut,
    chronologicalMobiusWeightedSource_eq_sum pmWindowLogBase N (mul_pos hq0 ht)
      (fun _ h => pmWindowLogBase_eq_zero_of_one_le h.le) (hcutA hq),
    chronologicalMobiusWeightedSource_eq_sum pmWindowLogBase N
      (mul_pos (sq_pos_of_pos hq0) ht)
      (fun _ h => pmWindowLogBase_eq_zero_of_one_le h.le) (hcutA hq2)]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [pmWindowLogTent]
  rw [show q * ((n : ℝ) * t) = (n : ℝ) * (q * t) by ring,
    show q ^ 2 * ((n : ℝ) * t) = (n : ℝ) * (q ^ 2 * t) by ring]
  ring

theorem integral_pmMertens_div_split {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in Ioc (1 : ℝ) b, Sieve.mertensM ⌊t⌋₊ / t) =
      (∫ t in Ioc (1 : ℝ) a, Sieve.mertensM ⌊t⌋₊ / t) +
        ∫ t in Ioc a b, Sieve.mertensM ⌊t⌋₊ / t := by
  have hi := integrableOn_pmMertens_div_Icc b
  have hi1 : IntegrableOn (fun t : ℝ => Sieve.mertensM ⌊t⌋₊ / t) (Ioc 1 a) :=
    hi.mono_set (fun _ ht => ⟨ht.1.le, ht.2.trans hab⟩)
  have hi2 : IntegrableOn (fun t : ℝ => Sieve.mertensM ⌊t⌋₊ / t) (Ioc a b) :=
    hi.mono_set (fun _ ht => ⟨ha.trans ht.1.le, ht.2⟩)
  rw [← Ioc_union_Ioc_eq_Ioc ha hab]
  apply setIntegral_union _ measurableSet_Ioc hi1 hi2
  rw [disjoint_left]
  intro t ht ht'
  exact (not_lt_of_ge ht.2) ht'.1

theorem pmWindowLogTent_source_eq_mertens_windows {q x : ℝ}
    (hq : 1 ≤ q) (hx : 1 ≤ x) :
    chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * x)⁻¹ =
      (((∫ t in Ioc (q * x) (q ^ 2 * x), Sieve.mertensM ⌊t⌋₊ / t) -
        ∫ t in Ioc x (q * x), Sieve.mertensM ⌊t⌋₊ / t : ℝ) : ℂ) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hq2 : 1 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have hxqx : x ≤ q * x := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq hx0.le
  have hqxq2x : q * x ≤ q ^ 2 * x := by
    have h := mul_le_mul_of_nonneg_right hq (mul_pos hq0 hx0).le
    nlinarith
  have hqx1 : 1 ≤ q * x := hx.trans hxqx
  have hq2x1 : 1 ≤ q ^ 2 * x := hqx1.trans hqxq2x
  rw [pmWindowLogTent_source_eq_logBase hq (inv_pos.mpr (mul_pos (sq_pos_of_pos hq0) hx0)),
    show q * (q ^ 2 * x)⁻¹ = (q * x)⁻¹ by field_simp,
    show q ^ 2 * (q ^ 2 * x)⁻¹ = x⁻¹ by field_simp,
    pmWindowLogBase_source_eq_integral_mertens hq2x1,
    pmWindowLogBase_source_eq_integral_mertens hqx1,
    pmWindowLogBase_source_eq_integral_mertens hx,
    integral_pmMertens_div_split hqx1 hqxq2x,
    integral_pmMertens_div_split hx hxqx]
  push_cast
  ring

theorem integral_pmMertens_centered_div {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (c : ℝ) :
    (∫ t in Ioc a b, (Sieve.mertensM ⌊t⌋₊ - c) / t) =
      (∫ t in Ioc a b, Sieve.mertensM ⌊t⌋₊ / t) - c * Real.log (b / a) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hi := (integrableOn_pmMertens_div_Icc b).mono_set
    (show Ioc a b ⊆ Icc 1 b from fun _ ht => ⟨ha.trans ht.1.le, ht.2⟩)
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun t ht => (ha0.trans_le ht.1).ne')
  have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc a b) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have he : (fun t : ℝ => (Sieve.mertensM ⌊t⌋₊ - c) / t) =
      fun t => Sieve.mertensM ⌊t⌋₊ / t - c * t⁻¹ := by
    funext t
    simp only [div_eq_mul_inv]
    ring
  have hlog : (∫ t in Ioc a b, t⁻¹) = Real.log (b / a) := by
    rw [← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha0 hb0]
  rw [he, integral_sub hi (hinv.const_mul c), integral_const_mul, hlog]

theorem pmWindowLogTent_source_eq_centered_mertens_windows {q x : ℝ}
    (hq : 1 ≤ q) (hx : 1 ≤ x) (c : ℝ) :
    chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * x)⁻¹ =
      (((∫ t in Ioc (q * x) (q ^ 2 * x), (Sieve.mertensM ⌊t⌋₊ - c) / t) -
        ∫ t in Ioc x (q * x), (Sieve.mertensM ⌊t⌋₊ - c) / t : ℝ) : ℂ) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxqx : x ≤ q * x := by nlinarith
  have hqxq2x : q * x ≤ q ^ 2 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (mul_pos hq0 hx0).le]
  rw [integral_pmMertens_centered_div (hx.trans hxqx) hqxq2x c,
    integral_pmMertens_centered_div hx hxqx c,
    show q ^ 2 * x / (q * x) = q by field_simp,
    show q * x / x = q by field_simp,
    pmWindowLogTent_source_eq_mertens_windows hq hx]
  congr 1
  ring

theorem norm_pmMertens_le (N : ℕ) : ‖Sieve.mertensM N‖ ≤ N := by
  unfold Sieve.mertensM
  rw [Finset.sum_range_succ']
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, add_zero]
  calc
    ‖∑ i ∈ Finset.range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ)‖ ≤
        ∑ i ∈ Finset.range N, ‖((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [Real.norm_eq_abs, ← Int.cast_abs]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := i + 1))
    _ = N := by simp

theorem norm_pmMertens_centered_div_le {t : ℝ} (ht : 1 ≤ t) (c : ℝ) :
    ‖(Sieve.mertensM ⌊t⌋₊ - c) / t‖ ≤ 1 + ‖c‖ := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [norm_div, Real.norm_eq_abs t, abs_of_pos ht0, div_le_iff₀ ht0]
  have hM := (norm_pmMertens_le ⌊t⌋₊).trans (Nat.floor_le ht0.le)
  have hc := mul_le_mul_of_nonneg_left ht (norm_nonneg c)
  have hs := norm_sub_le (Sieve.mertensM ⌊t⌋₊) c
  nlinarith

theorem measurable_pmMertens_centered_div (c : ℝ) :
    Measurable (fun t : ℝ => (Sieve.mertensM ⌊t⌋₊ - c) / t) := by
  exact (((Measurable.of_discrete : Measurable Sieve.mertensM).comp
    Nat.measurable_floor).sub_const c).div measurable_id

theorem integrableOn_pmMertens_centered_div_sq {a b : ℝ} (ha : 1 ≤ a) (c : ℝ) :
    IntegrableOn (fun t : ℝ => ((Sieve.mertensM ⌊t⌋₊ - c) / t) ^ 2) (Ioc a b) := by
  have hi : IntegrableOn (fun _t : ℝ => (1 + ‖c‖) ^ 2) (Ioc a b) :=
    integrableOn_const measure_Ioc_lt_top.ne
  refine hi.mono' ((measurable_pmMertens_centered_div c).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_pow]
  have h := norm_pmMertens_centered_div_le (ha.trans ht.1.le) c
  nlinarith [norm_nonneg ((Sieve.mertensM ⌊t⌋₊ - c) / t)]

theorem sq_integral_pmMertens_centered_div_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (c : ℝ) :
    (∫ t in Ioc a b, (Sieve.mertensM ⌊t⌋₊ - c) / t) ^ 2 ≤
      (b - a) * ∫ t in Ioc a b, ((Sieve.mertensM ⌊t⌋₊ - c) / t) ^ 2 := by
  have hc : IntegrableOn (fun _t : ℝ => (1 : ℝ) ^ 2) (Ioc a b) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have h := GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    (f := fun _t : ℝ => (1 : ℝ)) (μ := volume.restrict (Ioc a b))
    aestronglyMeasurable_const (measurable_pmMertens_centered_div c).aestronglyMeasurable
    hc (integrableOn_pmMertens_centered_div_sq ha c)
  simpa only [one_mul, one_pow, setIntegral_one_eq_measureReal,
    Real.volume_real_Ioc_of_le hab] using h

theorem pmWindowLogTent_source_sq_le_centered_energy {q x : ℝ}
    (hq : 1 ≤ q) (hx : 1 ≤ x) (c : ℝ) :
    ‖chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * x)⁻¹‖ ^ 2 ≤
      2 * (q ^ 2 * x) *
        ∫ t in Ioc x (q ^ 2 * x), ((Sieve.mertensM ⌊t⌋₊ - c) / t) ^ 2 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxqx : x ≤ q * x := by nlinarith
  have hqxq2x : q * x ≤ q ^ 2 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (mul_pos hq0 hx0).le]
  let E := ∫ t in Ioc x (q ^ 2 * x), ((Sieve.mertensM ⌊t⌋₊ - c) / t) ^ 2
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hi := integrableOn_pmMertens_centered_div_sq (b := q ^ 2 * x) hx c
  have hEU : (∫ t in Ioc (q * x) (q ^ 2 * x),
      ((Sieve.mertensM ⌊t⌋₊ - c) / t) ^ 2) ≤ E := by
    apply setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
    exact Eventually.of_forall (fun _ ht => ⟨hxqx.trans_lt ht.1, ht.2⟩)
  have hEL : (∫ t in Ioc x (q * x),
      ((Sieve.mertensM ⌊t⌋₊ - c) / t) ^ 2) ≤ E := by
    apply setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
    exact Eventually.of_forall (fun _ ht => ⟨ht.1, ht.2.trans hqxq2x⟩)
  have hU := (sq_integral_pmMertens_centered_div_le (hx.trans hxqx) hqxq2x c).trans
    (mul_le_mul_of_nonneg_left hEU (sub_nonneg.mpr hqxq2x))
  have hL := (sq_integral_pmMertens_centered_div_le hx hxqx c).trans
    (mul_le_mul_of_nonneg_left hEL (sub_nonneg.mpr hxqx))
  rw [pmWindowLogTent_source_eq_centered_mertens_windows hq hx c,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change _ ≤ 2 * (q ^ 2 * x) * E
  nlinarith [sq_nonneg
    ((∫ t in Ioc (q * x) (q ^ 2 * x), (Sieve.mertensM ⌊t⌋₊ - c) / t) +
      ∫ t in Ioc x (q * x), (Sieve.mertensM ⌊t⌋₊ - c) / t),
    mul_nonneg hx0.le hE]

theorem pmWindowLogTent_source_cofinal_square_floor {q : ℝ} (hq : 1 < q) :
    ∃ η : ℝ, 0 < η ∧ ∀ X : ℝ, ∃ x : ℝ,
      1 ≤ x ∧ X ≤ x ∧ η * x <
        ‖chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * x)⁻¹‖ ^ 2 := by
  obtain ⟨ε, hε, hf⟩ := pmWindowLogTent_source_cofinal_critical_floor hq
  refine ⟨ε ^ 2 * q ^ 2, by positivity, ?_⟩
  intro X
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hY0 : 0 < max 1 X := zero_lt_one.trans_le (le_max_left _ _)
  have hden : 0 < q ^ 2 * max 1 X := mul_pos (sq_pos_of_pos hq0) hY0
  obtain ⟨t, ht0, htδ, htf⟩ := hf (q ^ 2 * max 1 X)⁻¹ (inv_pos.mpr hden)
  let x := (q ^ 2 * t)⁻¹
  have hqt : 0 < q ^ 2 * t := mul_pos (sq_pos_of_pos hq0) ht0
  have hxt : x * (q ^ 2 * t) = 1 := inv_mul_cancel₀ hqt.ne'
  have hYx : max 1 X < x := by
    have h := mul_lt_mul_of_pos_right htδ hden
    rw [inv_mul_cancel₀ hden.ne'] at h
    nlinarith
  have hx0 : 0 < x := hY0.trans hYx
  have harg : (q ^ 2 * x)⁻¹ = t := by
    dsimp [x]
    field_simp
  have hroot : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← Real.rpow_two, ← Real.rpow_mul ht0.le]
    norm_num
  have hs : ε ^ 2 < t * ‖chronologicalMobiusWeightedSource (pmWindowLogTent q) t‖ ^ 2 := by
    have h := mul_self_lt_mul_self hε.le htf
    nlinarith [hroot]
  refine ⟨x, (le_max_left 1 X).trans hYx.le, (le_max_right 1 X).trans hYx.le, ?_⟩
  rw [harg]
  have h := mul_lt_mul_of_pos_right hs (mul_pos (sq_pos_of_pos hq0) hx0)
  have hid : t * (q ^ 2 * x) = 1 := by nlinarith [hxt]
  have he : t * ‖chronologicalMobiusWeightedSource (pmWindowLogTent q) t‖ ^ 2 *
      (q ^ 2 * x) = ‖chronologicalMobiusWeightedSource (pmWindowLogTent q) t‖ ^ 2 := by
    calc
      _ = (t * (q ^ 2 * x)) *
          ‖chronologicalMobiusWeightedSource (pmWindowLogTent q) t‖ ^ 2 := by ring
      _ = _ := by rw [hid, one_mul]
  rw [he] at h
  nlinarith

theorem pmMertens_centered_window_energy_cofinal_floor {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, ∃ x : ℝ, 1 ≤ x ∧ X ≤ x ∧ ∀ c : ℝ,
      C ≤ ∫ t in Ioc x (q ^ 2 * x), ((Sieve.mertensM ⌊t⌋₊ - c) / t) ^ 2 := by
  obtain ⟨η, hη, hf⟩ := pmWindowLogTent_source_cofinal_square_floor hq
  have hq0 : 0 < q := zero_lt_one.trans hq
  refine ⟨η / (2 * q ^ 2), by positivity, ?_⟩
  intro X
  obtain ⟨x, hx, hXx, hfloor⟩ := hf X
  refine ⟨x, hx, hXx, fun c => ?_⟩
  have hbound := pmWindowLogTent_source_sq_le_centered_energy hq.le hx c
  rw [div_le_iff₀ (show 0 < 2 * q ^ 2 by positivity)]
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  nlinarith

theorem norm_integral_pmMertens_div_sub_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖(∫ t in Ioc (1 : ℝ) b, Sieve.mertensM ⌊t⌋₊ / t) -
      ∫ t in Ioc (1 : ℝ) a, Sieve.mertensM ⌊t⌋₊ / t‖ ≤ b - a := by
  rw [integral_pmMertens_div_split ha hab]
  simp only [add_sub_cancel_left]
  have hi : IntegrableOn (fun _t : ℝ => (1 : ℝ)) (Ioc a b) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have h := norm_integral_le_of_norm_le (f := fun t : ℝ => Sieve.mertensM ⌊t⌋₊ / t)
    hi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa only [sub_zero, norm_zero, add_zero] using
        norm_pmMertens_centered_div_le (ha.trans ht.1.le) 0)
  simpa only [setIntegral_one_eq_measureReal, Real.volume_real_Ioc_of_le hab] using h

theorem pmWindowLogTent_source_eq_mertens_log_difference {q x : ℝ}
    (hq : 1 ≤ q) (hx : 1 ≤ x) :
    chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * x)⁻¹ =
      (((∫ t in Ioc (1 : ℝ) (q ^ 2 * x), Sieve.mertensM ⌊t⌋₊ / t) -
        2 * (∫ t in Ioc (1 : ℝ) (q * x), Sieve.mertensM ⌊t⌋₊ / t) +
        ∫ t in Ioc (1 : ℝ) x, Sieve.mertensM ⌊t⌋₊ / t : ℝ) : ℂ) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxqx : x ≤ q * x := by nlinarith
  have hqxq2x : q * x ≤ q ^ 2 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (mul_pos hq0 hx0).le]
  rw [pmWindowLogTent_source_eq_mertens_windows hq hx]
  congr 1
  linarith [integral_pmMertens_div_split hx hxqx,
    integral_pmMertens_div_split (hx.trans hxqx) hqxq2x]

theorem norm_pmWindowLogTent_source_sub_le {q x y : ℝ}
    (hq : 1 ≤ q) (hy : 1 ≤ y) (hyx : y ≤ x) :
    ‖chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * x)⁻¹ -
      chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * y)⁻¹‖ ≤
        (q ^ 2 + 2 * q + 1) * (x - y) := by
  let L := fun z : ℝ => ∫ t in Ioc (1 : ℝ) z, Sieve.mertensM ⌊t⌋₊ / t
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hqy : 1 ≤ q * y := by nlinarith
  have hq2 : 1 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have hq2y : 1 ≤ q ^ 2 * y := by nlinarith
  have hA : ‖L (q ^ 2 * x) - L (q ^ 2 * y)‖ ≤ q ^ 2 * x - q ^ 2 * y :=
    norm_integral_pmMertens_div_sub_le hq2y (mul_le_mul_of_nonneg_left hyx (sq_nonneg q))
  have hB : ‖L (q * x) - L (q * y)‖ ≤ q * x - q * y :=
    norm_integral_pmMertens_div_sub_le hqy (mul_le_mul_of_nonneg_left hyx hq0.le)
  have hC : ‖L x - L y‖ ≤ x - y := norm_integral_pmMertens_div_sub_le hy hyx
  have he : chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * x)⁻¹ -
      chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * y)⁻¹ =
      (((L (q ^ 2 * x) - L (q ^ 2 * y)) - 2 * (L (q * x) - L (q * y)) +
        (L x - L y) : ℝ) : ℂ) := by
    rw [pmWindowLogTent_source_eq_mertens_log_difference hq (hy.trans hyx),
      pmWindowLogTent_source_eq_mertens_log_difference hq hy]
    dsimp [L]
    push_cast
    ring
  rw [he, Complex.norm_real]
  calc
    _ ≤ ‖L (q ^ 2 * x) - L (q ^ 2 * y)‖ + ‖2 * (L (q * x) - L (q * y))‖ +
        ‖L x - L y‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = ‖L (q ^ 2 * x) - L (q ^ 2 * y)‖ + 2 * ‖L (q * x) - L (q * y)‖ +
        ‖L x - L y‖ := by rw [norm_mul]; norm_num
    _ ≤ (q ^ 2 * x - q ^ 2 * y) + 2 * (q * x - q * y) + (x - y) := by linarith
    _ = _ := by ring

theorem pmWindowLogTent_source_nat_cofinal_square_floor {q : ℝ} (hq : 1 < q) :
    ∃ η : ℝ, 0 < η ∧ ∀ N₀ : ℕ, ∃ N : ℕ,
      1 ≤ N ∧ N₀ ≤ N ∧ η * N <
        ‖chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * N)⁻¹‖ ^ 2 := by
  obtain ⟨η, hη, hf⟩ := pmWindowLogTent_source_cofinal_square_floor hq
  let K := q ^ 2 + 2 * q + 1
  let f := fun x : ℝ => chronologicalMobiusWeightedSource (pmWindowLogTent q) (q ^ 2 * x)⁻¹
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨η / 4, by positivity, ?_⟩
  intro N₀
  obtain ⟨x, hx, hXx, hfloor⟩ := hf (max ((N₀ : ℝ) + 2) (4 * K ^ 2 / η + 2))
  let N := ⌊x⌋₊
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (zero_lt_one.trans_le hx).le
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hN₀x : (N₀ : ℝ) + 2 ≤ x := (le_max_left _ _).trans hXx
  have hKNx : 4 * K ^ 2 / η + 2 ≤ x := (le_max_right _ _).trans hXx
  have hN1 : (1 : ℝ) ≤ N := by
    have hn : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
    linarith
  have hN₀N : (N₀ : ℝ) ≤ N := by linarith
  have hNK : 4 * K ^ 2 < η * N := by
    have hdiv : 4 * K ^ 2 / η < (N : ℝ) := by linarith
    have hm := mul_lt_mul_of_pos_right hdiv hη
    have he : 4 * K ^ 2 / η * η = 4 * K ^ 2 := by field_simp
    nlinarith
  have hLip : ‖f x - f N‖ ≤ K := by
    have h := norm_pmWindowLogTent_source_sub_le hq.le hN1 hNx
    change ‖f x - f N‖ ≤ K * (x - N) at h
    have hm := mul_le_mul_of_nonneg_left (show x - (N : ℝ) ≤ 1 by linarith) hK
    nlinarith
  have hnorm : ‖f x‖ ≤ ‖f N‖ + K := by
    calc
      ‖f x‖ = ‖(f x - f N) + f N‖ := by congr 1; ring
      _ ≤ ‖f x - f N‖ + ‖f N‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hsq : ‖f x‖ ^ 2 ≤ 2 * ‖f N‖ ^ 2 + 2 * K ^ 2 := by
    have h := mul_self_le_mul_self (norm_nonneg (f x)) hnorm
    nlinarith [sq_nonneg (‖f N‖ - K)]
  refine ⟨N, by exact_mod_cast hN1, by exact_mod_cast hN₀N, ?_⟩
  change η * x < ‖f x‖ ^ 2 at hfloor
  change η / 4 * N < ‖f N‖ ^ 2
  nlinarith [mul_le_mul_of_nonneg_left hNx hη.le]

theorem pmMertens_centered_nat_window_energy_cofinal_floor {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ N₀ : ℕ, ∃ N : ℕ, 1 ≤ N ∧ N₀ ≤ N ∧ ∀ c : ℝ,
      C ≤ ∫ t in Ioc (N : ℝ) (q ^ 2 * N), ((Sieve.mertensM ⌊t⌋₊ - c) / t) ^ 2 := by
  obtain ⟨η, hη, hf⟩ := pmWindowLogTent_source_nat_cofinal_square_floor hq
  have hq0 : 0 < q := zero_lt_one.trans hq
  refine ⟨η / (2 * q ^ 2), by positivity, ?_⟩
  intro N₀
  obtain ⟨N, hN1, hN₀N, hfloor⟩ := hf N₀
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  refine ⟨N, hN1, hN₀N, fun c => ?_⟩
  have hbound := pmWindowLogTent_source_sq_le_centered_energy hq.le hN c
  rw [div_le_iff₀ (show 0 < 2 * q ^ 2 by positivity)]
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN
  nlinarith

theorem pmMertens_centered_dyadic_window_energy_cofinal_floor :
    ∃ C : ℝ, 0 < C ∧ ∀ N₀ : ℕ, ∃ N : ℕ, 1 ≤ N ∧ N₀ ≤ N ∧ ∀ c : ℝ,
      C ≤ ∫ t in Ioc (N : ℝ) (2 * N), ((Sieve.mertensM ⌊t⌋₊ - c) / t) ^ 2 := by
  simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using
    pmMertens_centered_nat_window_energy_cofinal_floor Real.one_lt_sqrt_two

end RHTower
