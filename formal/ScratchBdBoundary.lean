import GaloisForLFunctions.RHTower.BaezDuarteMobiusPrefixApproximation
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import GaloisForLFunctions.RHTower.AbelTailLSeries
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding

open Complex Filter Set Topology Asymptotics
open scoped Topology LSeries.notation
open ArithmeticFunction

noncomputable section

namespace RHTower

def bdHarmonicCoeff (k : ℕ) : ℂ :=
  (((moebius (k + 1) : ℤ) : ℝ) : ℂ) / ((k + 1 : ℕ) : ℂ)

def bdHarmonicSource (n : ℕ) : ℝ := ((moebius n : ℤ) : ℝ) / (n : ℝ)

theorem coeffPartial_bdHarmonicCoeff (N : ℕ) :
    coeffPartial bdHarmonicCoeff N = (deningerHarmonicPartial N : ℂ) := by
  induction N with
  | zero => simp [coeffPartial, bdHarmonicCoeff, deningerHarmonicPartial]
  | succ N ih =>
      rw [coeffPartial, Finset.sum_range_succ]
      change coeffPartial bdHarmonicCoeff N + bdHarmonicCoeff N = _
      rw [ih]
      have hrec : deningerHarmonicPartial (N + 1) = deningerHarmonicPartial N +
          ((moebius (N + 1) : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
        change (∑ n ∈ Finset.range (N + 2), ((moebius n : ℤ) : ℝ) / (n : ℝ)) =
          (∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℝ) / (n : ℝ)) + _
        rw [Finset.sum_range_succ]
      rw [hrec, Complex.ofReal_add]
      congr 1
      simp [bdHarmonicCoeff]

theorem sourcePartialSum_bdHarmonicSource (N : ℕ) :
    sourcePartialSum bdHarmonicSource N = deningerHarmonicPartial N := by
  rw [sourcePartialSum, deningerHarmonicPartial_eq_sum_Icc]
  rfl

private theorem LSeries_term_bdHarmonicSource (w : ℂ) (n : ℕ) :
    LSeries.term (fun m : ℕ => (bdHarmonicSource m : ℂ)) w n =
      LSeries.term (fun m : ℕ => (moebius m : ℂ)) (1 + w) n := by
  rcases n with _ | n
  · simp
  rw [LSeries.term_of_ne_zero (by omega : n + 1 ≠ 0),
    LSeries.term_of_ne_zero (by omega : n + 1 ≠ 0), bdHarmonicSource]
  have hn0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  rw [Complex.cpow_add _ _ hn0, Complex.cpow_one]
  push_cast
  field_simp

private theorem norm_cpow_unit_diff_le_of_neg_one_lt_re {w : ℂ} (hw : -1 < w.re)
    {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-w) - ((x + 1 : ℝ) : ℂ) ^ (-w)‖ ≤
      ‖w‖ * x ^ (-w.re - 1) := by
  by_cases hw0 : w = 0
  · simp [hw0]
  have hderiv : ∀ t ∈ Set.uIcc x (x + 1),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-w))
        ((-w) * (t : ℂ) ^ (-w - 1)) (Set.uIcc x (x + 1)) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hx (by
      rcases Set.mem_uIcc.1 ht with h | h
      · exact h.1
      · linarith [h.2])
    exact (hasDerivAt_ofReal_cpow_const htpos.ne' (neg_ne_zero.mpr hw0)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.uIcc x (x + 1),
      ‖(-w) * (t : ℂ) ^ (-w - 1)‖ ≤ ‖w‖ * x ^ (-w.re - 1) := by
    intro t ht
    have hxt : x ≤ t := by
      rcases Set.mem_uIcc.1 ht with h | h
      · exact h.1
      · linarith [h.2]
    have htpos : 0 < t := lt_of_lt_of_le hx hxt
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    have hre : (-w - 1).re = -w.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx hxt (by linarith)) (norm_nonneg _)
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => (y : ℂ) ^ (-w))
    (f' := fun y : ℝ => (-w) * (y : ℂ) ^ (-w - 1))
    hderiv hbound (convex_uIcc _ _) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [norm_sub_rev] at hmain
  simpa using hmain

private theorem exists_bdHarmonicCoeff_partial_rpow_bound
    (h : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) * deningerHarmonicPartial N)
      atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      ‖coeffPartial bdHarmonicCoeff (k + 1)‖ ≤
        C * (((k : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  have hshift : Tendsto
      (fun k : ℕ => Real.sqrt ((k + 1 : ℕ) : ℝ) * deningerHarmonicPartial (k + 1))
      atTop (𝓝 0) := h.comp (tendsto_add_atTop_nat 1)
  obtain ⟨C, hC⟩ := deningerBounded_of_tendsto hshift
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  refine ⟨C, hC0, fun k => ?_⟩
  rw [coeffPartial_bdHarmonicCoeff, Complex.norm_real, Real.norm_eq_abs]
  have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hkpos
  have hbound := hC k
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hbound
  have hdiv : |deningerHarmonicPartial (k + 1)| ≤
      C / Real.sqrt ((k + 1 : ℕ) : ℝ) :=
    (le_div_iff₀ hsqrt).2 (by simpa [mul_comm] using hbound)
  refine hdiv.trans_eq ?_
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hkpos.le]
  congr 2
  push_cast
  ring

private theorem differentiableAt_abelDirichlet_bdHarmonicCoeff_of_tendsto
    (h : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) * deningerHarmonicPartial N)
      atTop (𝓝 0)) {w₀ : ℂ} (hw₀ : -(1 / 2 : ℝ) < w₀.re) :
    DifferentiableAt ℂ (abelDirichlet bdHarmonicCoeff) w₀ := by
  obtain ⟨C, hC0, hC⟩ := exists_bdHarmonicCoeff_partial_rpow_bound h
  set r : ℝ := (w₀.re + 1 / 2) / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  set a : ℝ := w₀.re - r with hadef
  have ha : -(1 / 2 : ℝ) < a := by rw [hadef, hrdef]; linarith
  set U : Set ℂ := Metric.ball w₀ r with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hwU : w₀ ∈ U := Metric.mem_ball_self hr
  have hfacts : ∀ w ∈ U, a ≤ w.re ∧ ‖w‖ ≤ ‖w₀‖ + r := by
    intro w hw
    have hdist : ‖w - w₀‖ < r := by
      rw [hUdef] at hw
      simpa [Complex.dist_eq] using hw
    have hre : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
      simpa using Complex.abs_re_le_norm (w - w₀)
    have hrelt : |w.re - w₀.re| < r := lt_of_le_of_lt hre hdist
    constructor
    · rw [hadef]
      linarith [(abs_lt.1 hrelt).1]
    · have htri : ‖w‖ ≤ ‖w - w₀‖ + ‖w₀‖ := by
        simpa using norm_add_le (w - w₀) w₀
      linarith
  set u : ℕ → ℝ := fun k =>
    (C * (‖w₀‖ + r)) * (((k : ℝ) + 1) ^ (-a - 3 / 2)) with hudef
  have hq : 0 < a + 1 / 2 := by linarith
  have husum : Summable u := by
    have hbase := summable_shiftMajorant (w := ((a + 1 / 2 : ℝ) : ℂ)) (by simpa using hq)
    refine ((hbase.mul_left (C * (‖w₀‖ + r))).congr fun k => ?_)
    rw [hudef]
    congr 2
    simp only [Complex.ofReal_re]
    ring
  have hle : ∀ k : ℕ, ∀ w ∈ U,
      ‖coeffPartial bdHarmonicCoeff (k + 1) *
        (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w) -
          ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-w))‖ ≤ u k := by
    intro k w hw
    obtain ⟨hwre, hwnorm⟩ := hfacts w hw
    have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hinc := norm_cpow_unit_diff_le_of_neg_one_lt_re
      (w := w) (by linarith [ha, hwre]) hx
    have hcast : ((k : ℝ) + 1) + 1 = (k : ℝ) + 2 := by ring
    rw [hcast] at hinc
    have hpow : ((k : ℝ) + 1) ^ (-w.re - 1) ≤
        ((k : ℝ) + 1) ^ (-a - 1) := by
      exact Real.rpow_le_rpow_of_exponent_le (by simp) (by linarith)
    rw [norm_mul]
    have hleft0 : 0 ≤ C * (((k : ℝ) + 1) ^ (-(1 / 2 : ℝ))) :=
      mul_nonneg hC0 (Real.rpow_nonneg (by positivity) _)
    refine (mul_le_mul (hC k) hinc (norm_nonneg _) hleft0).trans ?_
    rw [hudef]
    have hwpow : ‖w‖ * ((k : ℝ) + 1) ^ (-w.re - 1) ≤
        (‖w₀‖ + r) * ((k : ℝ) + 1) ^ (-a - 1) :=
      mul_le_mul hwnorm hpow (Real.rpow_nonneg (by positivity) _) (by positivity)
    refine (mul_le_mul_of_nonneg_left hwpow hleft0).trans_eq ?_
    change C * ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
        ((‖w₀‖ + r) * ((k : ℝ) + 1) ^ (-a - 1)) =
      C * (‖w₀‖ + r) * ((k : ℝ) + 1) ^ (-a - 3 / 2)
    rw [show C * ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
        ((‖w₀‖ + r) * ((k : ℝ) + 1) ^ (-a - 1)) =
      C * (‖w₀‖ + r) *
        (((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * ((k : ℝ) + 1) ^ (-a - 1)) by ring,
      ← Real.rpow_add hx]
    ring
  have hdiff := differentiableOn_tsum_of_summable_norm husum
    (fun k => (differentiable_abelTerm bdHarmonicCoeff k).differentiableOn) hUopen hle
  exact hdiff.differentiableAt (hUopen.mem_nhds hwU)

private theorem abelDirichlet_bdHarmonicCoeff_mul_riemannZeta {w : ℂ} (hw : 0 < w.re) :
    abelDirichlet bdHarmonicCoeff w * riemannZeta (1 + w) = 1 := by
  obtain ⟨C, hC⟩ := deningerHarmonicPartial_bounded
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hb : ∀ N : ℕ, |sourcePartialSum bdHarmonicSource N| ≤ C * (N : ℝ) ^ (0 : ℝ) := by
    intro N
    rw [sourcePartialSum_bdHarmonicSource, Real.rpow_zero, mul_one]
    exact hC N
  have hmusum : LSeriesSummable (fun n : ℕ => (moebius n : ℂ)) (1 + w) := by
    rw [LSeriesSummable_moebius_iff]
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hbsum : LSeriesSummable (fun n : ℕ => (bdHarmonicSource n : ℂ)) w := by
    exact hmusum.congr fun n => (LSeries_term_bdHarmonicSource w n).symm
  have hab := abelTailSeries_sourcePartialSum hC0 hb hw hw hbsum
  have hF : abelDirichlet bdHarmonicCoeff w = abelTailSeries (sourcePartialSum bdHarmonicSource) w := by
    rw [abelDirichlet, abelTailSeries]
    refine tsum_congr fun k => ?_
    rw [coeffPartial_bdHarmonicCoeff, sourcePartialSum_bdHarmonicSource]
  have hL : LSeries (fun n : ℕ => (bdHarmonicSource n : ℂ)) w =
      LSeries (fun n : ℕ => (moebius n : ℂ)) (1 + w) := by
    rw [LSeries, LSeries]
    exact tsum_congr (LSeries_term_bdHarmonicSource w)
  rw [hF, hab, hL]
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius
    (s := 1 + w) (by simpa using (show (1 : ℝ) < (1 + w).re by simp; linarith [hw]))
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta
    (by simpa using (show (1 : ℝ) < (1 + w).re by simp; linarith [hw]))] at hprod
  rw [mul_comm]
  exact hprod

private theorem mul_natSucc_rpow_le_four_mul_deningerAbelWeight
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (n : ℕ) :
    σ * (((n : ℝ) + 1) ^ (-1 - σ)) ≤ 4 * deningerAbelWeight σ n := by
  set x : ℝ := (n : ℝ) + 1 with hxdef
  have hx : 0 < x := by rw [hxdef]; positivity
  have hx1 : 1 ≤ x := by rw [hxdef]; simp
  have hderiv : ∀ t ∈ Set.Icc x (x + 1),
      HasDerivWithinAt (fun y : ℝ => -(y ^ (-σ)))
        (σ * t ^ (-σ - 1)) (Set.Icc x (x + 1)) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hx ht.1
    convert ((Real.hasDerivAt_rpow_const (p := -σ) htpos).neg).hasDerivWithinAt using 1 <;> ring
  have hlower : ∀ t ∈ Set.Ioo x (x + 1),
      σ * (x + 1) ^ (-σ - 1) ≤ σ * t ^ (-σ - 1) := by
    intro t ht
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (lt_trans hx ht.1) ht.2.le (by linarith)) hσ.le
  have hmvt := (convex_Icc x (x + 1)).mul_sub_le_image_sub_of_le_deriv
    (continuousOn_of_forall_continuousAt fun t => by
      exact (Real.continuousAt_rpow_const (by linarith [hx])).neg)
    (by linarith) hderiv hlower
  have hweight : σ * (x + 1) ^ (-σ - 1) ≤ deningerAbelWeight σ n := by
    simpa [deningerAbelWeight, hxdef] using hmvt
  have hratio : x ^ (-1 - σ) ≤ 4 * (x + 1) ^ (-1 - σ) := by
    sorry
  calc
    σ * x ^ (-1 - σ) ≤ σ * (4 * (x + 1) ^ (-1 - σ)) :=
      mul_le_mul_of_nonneg_left hratio hσ.le
    _ = 4 * (σ * (x + 1) ^ (-σ - 1)) := by ring
    _ ≤ 4 * deningerAbelWeight σ n := mul_le_mul_of_nonneg_left hweight (by norm_num)

end RHTower
