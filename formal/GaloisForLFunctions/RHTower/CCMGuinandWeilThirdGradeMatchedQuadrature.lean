import GaloisForLFunctions.RHTower.CCMActualHeadMatchedBoundaryCoverageSeam
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCesaroAnchoredMoment
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz

open MeasureTheory Set

noncomputable section

namespace RHTower

def ccmMatchedPrimePolarQuadratureDefect
    (phi : ℝ → ℝ) (n : ℕ) : ℝ :=
  criticalMellinAtomWeight n * phi (Real.log n) -
    ∫ h in
      (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..
      (Real.log n + ccmActualHeadMatchedPrimePolarRadius n),
      Real.exp (h / 2) * phi h

theorem ccmMatchedPrimePolarQuadratureDefect_eq_integral
    {phi : ℝ → ℝ} (hphi : Continuous phi) (n : ℕ) :
    ccmMatchedPrimePolarQuadratureDefect phi n =
      ∫ h in
        (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..
        (Real.log n + ccmActualHeadMatchedPrimePolarRadius n),
        Real.exp (h / 2) * (phi (Real.log n) - phi h) := by
  let lo := Real.log n - ccmActualHeadMatchedPrimePolarRadius n
  let hi := Real.log n + ccmActualHeadMatchedPrimePolarRadius n
  have hweight : Continuous (fun h : ℝ => Real.exp (h / 2)) := by fun_prop
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * phi (Real.log n)) volume lo hi :=
    (hweight.mul continuous_const).intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * phi h) volume lo hi :=
    (hweight.mul hphi).intervalIntegrable _ _
  rw [ccmMatchedPrimePolarQuadratureDefect]
  have hmass := integral_exp_half_matchedPrimePolarCell_eq_atomWeight n
  have hfirst :
      criticalMellinAtomWeight n * phi (Real.log n) =
        ∫ h in lo..hi, Real.exp (h / 2) * phi (Real.log n) := by
    calc
      _ = phi (Real.log n) *
          (∫ h in lo..hi, Real.exp (h / 2)) := by
            rw [hmass]
            ring
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro h hh
        ring
  rw [hfirst, ← intervalIntegral.integral_sub hconst hvar]
  apply intervalIntegral.integral_congr
  intro h hh
  ring

theorem abs_ccmMatchedPrimePolarQuadratureDefect_le
    {K : NNReal} {phi : ℝ → ℝ} (hphi : LipschitzWith K phi) (n : ℕ) :
    |ccmMatchedPrimePolarQuadratureDefect phi n| ≤
      (K : ℝ) * criticalMellinAtomWeight n ^ 2 /
        (2 * Real.exp (Real.log n / 2)) := by
  let s := Real.log n
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  let w := criticalMellinAtomWeight n
  let A := Real.exp (Real.log n / 2)
  have hrho : 0 ≤ rho := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hw : 0 ≤ w := criticalMellinAtomWeight_nonneg n
  have hA : 0 < A := Real.exp_pos _
  have hcont : Continuous phi := hphi.continuous
  rw [ccmMatchedPrimePolarQuadratureDefect_eq_integral hcont]
  change |∫ h in (s - rho)..(s + rho),
      Real.exp (h / 2) * (phi s - phi h)| ≤ _
  have hintegrable : IntervalIntegrable
      (fun h : ℝ =>
        |Real.exp (h / 2) * (phi s - phi h)|) volume
      (s - rho) (s + rho) := by
    exact ((by fun_prop : Continuous fun h : ℝ =>
      |Real.exp (h / 2) * (phi s - phi h)|)).intervalIntegrable _ _
  have hmajorIntegrable : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * ((K : ℝ) * rho)) volume
      (s - rho) (s + rho) := by
    exact ((by fun_prop : Continuous fun h : ℝ =>
      Real.exp (h / 2) * ((K : ℝ) * rho))).intervalIntegrable _ _
  have hpoint : ∀ h ∈ Icc (s - rho) (s + rho),
      |Real.exp (h / 2) * (phi s - phi h)| ≤
        Real.exp (h / 2) * ((K : ℝ) * rho) := by
    intro h hh
    have hdist : |s - h| ≤ rho := by
      rw [abs_le]
      constructor <;> linarith [hh.1, hh.2]
    have hlip : |phi s - phi h| ≤ (K : ℝ) * |s - h| := by
      simpa only [Real.dist_eq] using hphi.dist_le_mul s h
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (hlip.trans (mul_le_mul_of_nonneg_left hdist K.coe_nonneg))
      (Real.exp_pos _).le
  have hint :
      (∫ h in (s - rho)..(s + rho),
        |Real.exp (h / 2) * (phi s - phi h)|) ≤
      ∫ h in (s - rho)..(s + rho),
        Real.exp (h / 2) * ((K : ℝ) * rho) :=
    intervalIntegral.integral_mono_on (by linarith)
      hintegrable hmajorIntegrable hpoint
  calc
    |∫ h in (s - rho)..(s + rho),
        Real.exp (h / 2) * (phi s - phi h)| ≤
      ∫ h in (s - rho)..(s + rho),
        |Real.exp (h / 2) * (phi s - phi h)| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ h in (s - rho)..(s + rho),
        Real.exp (h / 2) * ((K : ℝ) * rho) := hint
    _ = ((K : ℝ) * rho) * w := by
      rw [show (fun h : ℝ => Real.exp (h / 2) * ((K : ℝ) * rho)) =
          fun h : ℝ => ((K : ℝ) * rho) * Real.exp (h / 2) by
        funext h; ring,
        intervalIntegral.integral_const_mul,
        integral_exp_half_matchedPrimePolarCell_eq_atomWeight]
    _ ≤ ((K : ℝ) * (w / (2 * A))) * w := by
      have hrad : rho ≤ w / (2 * A) := by
        simpa only [rho, w, A] using
          ccmActualHeadMatchedPrimePolarRadius_le_weight_div n
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrad K.coe_nonneg) hw
    _ = (K : ℝ) * criticalMellinAtomWeight n ^ 2 /
        (2 * Real.exp (Real.log n / 2)) := by
      dsimp only [w, A]
      field_simp [Real.exp_ne_zero]

theorem summable_ccmMatchedPrimePolarQuadratureDefect
    {K : NNReal} {phi : ℝ → ℝ} (hphi : LipschitzWith K phi) :
    Summable (ccmMatchedPrimePolarQuadratureDefect phi) := by
  have hmajor :=
    summable_criticalMellinAtomWeight_sq_div_exp_half_log.mul_left
      ((K : ℝ) / 2)
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [Real.norm_eq_abs]
  have h := abs_ccmMatchedPrimePolarQuadratureDefect_le hphi n
  calc
    |ccmMatchedPrimePolarQuadratureDefect phi n| ≤
        (K : ℝ) * criticalMellinAtomWeight n ^ 2 /
          (2 * Real.exp (Real.log n / 2)) := h
    _ = (K : ℝ) / 2 *
        (criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2)) := by ring

theorem abs_sum_ccmMatchedPrimePolarQuadratureDefect_le
    {K : NNReal} {phi : ℝ → ℝ} (hphi : LipschitzWith K phi)
    (s : Finset ℕ) :
    |∑ n ∈ s, ccmMatchedPrimePolarQuadratureDefect phi n| ≤
      (K : ℝ) / 2 *
        ∑' n : ℕ, criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2) := by
  let M : ℕ → ℝ := fun n => (K : ℝ) / 2 *
    (criticalMellinAtomWeight n ^ 2 / Real.exp (Real.log n / 2))
  have hM : Summable M :=
    summable_criticalMellinAtomWeight_sq_div_exp_half_log.mul_left
      ((K : ℝ) / 2)
  calc
    |∑ n ∈ s, ccmMatchedPrimePolarQuadratureDefect phi n| ≤
        ∑ n ∈ s, |ccmMatchedPrimePolarQuadratureDefect phi n| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ s, M n := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        |ccmMatchedPrimePolarQuadratureDefect phi n| ≤
            (K : ℝ) * criticalMellinAtomWeight n ^ 2 /
              (2 * Real.exp (Real.log n / 2)) :=
          abs_ccmMatchedPrimePolarQuadratureDefect_le hphi n
        _ = M n := by
          dsimp only [M]
          ring
    _ ≤ ∑' n : ℕ, M n := hM.sum_le_tsum s (by
      intro n hn
      dsimp only [M]
      positivity)
    _ = (K : ℝ) / 2 *
        ∑' n : ℕ, criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2) := by
      dsimp only [M]
      rw [tsum_mul_left]

end RHTower

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Uniform Lipschitz budget for the lower-clipped third-grade triangular reporter. -/
def ccmThirdGradeCesaroTriangularLipschitzConstant (b : ℝ) : NNReal :=
  ⟨160 / b ^ 4, by positivity⟩

/-- Global reporter obtained by freezing the literal triangular weight below `b` and truncating
its negative continuation above the moving upper wall. -/
def ccmThirdGradeCesaroClippedTriangularWeight (b H h : ℝ) : ℝ :=
  max (ccmGuinandWeilThirdGradeCesaroTriangularWeight H (max b h)) 0

theorem lipschitzWith_ccmThirdGradeCesaroClippedTriangularWeight
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    LipschitzWith (ccmThirdGradeCesaroTriangularLipschitzConstant b)
      (ccmThirdGradeCesaroClippedTriangularWeight b H) := by
  let C := ccmThirdGradeCesaroTriangularLipschitzConstant b
  let F := ccmGuinandWeilThirdGradeCesaroTriangularWeight H
  have hH : 0 < H := hb.trans_le hbH
  have hraw : LipschitzOnWith C F (Set.Ici b) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (convex_Ici b) (f' := fun x => -ccmGuinandWeilThirdGradeCesaroErrorKernel H x)
    · intro x hx
      exact (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
        (ne_of_gt (hb.trans_le hx))).hasDerivWithinAt
    · intro x hx
      have hxpos : 0 < x := hb.trans_le hx
      have hx3 : b ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hb.le hx 3
      have hx4 : b ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hb.le hx 4
      have hinvH : 1 / H ≤ 1 / b := one_div_le_one_div_of_le hb hbH
      have hinvX3 : 1 / x ^ 3 ≤ 1 / b ^ 3 :=
        one_div_le_one_div_of_le (pow_pos hb 3) hx3
      have hinvX4 : 1 / x ^ 4 ≤ 1 / b ^ 4 :=
        one_div_le_one_div_of_le (pow_pos hb 4) hx4
      have hq : 0 ≤ 64 * x / H := by positivity
      have hnum : |96 - 64 * x / H| ≤ 96 + 64 * x / H := by
        calc
          |96 - 64 * x / H| ≤ |(96 : ℝ)| + |64 * x / H| := abs_sub _ _
          _ = 96 + 64 * x / H := by
            rw [abs_of_nonneg (by norm_num), abs_of_nonneg hq]
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      dsimp only [C, ccmThirdGradeCesaroTriangularLipschitzConstant]
      unfold ccmGuinandWeilThirdGradeCesaroErrorKernel
      change |-((96 - 64 * x / H) / x ^ 4)| ≤ 160 / b ^ 4
      rw [abs_neg, abs_div, abs_pow, abs_of_pos hxpos]
      calc
        |96 - 64 * x / H| / x ^ 4 ≤
            (96 + 64 * x / H) / x ^ 4 :=
          div_le_div_of_nonneg_right hnum (pow_nonneg hxpos.le 4)
        _ = 96 * (1 / x ^ 4) + 64 * (1 / H) * (1 / x ^ 3) := by
          field_simp [hxpos.ne', hH.ne']
        _ ≤ 96 * (1 / b ^ 4) + 64 * (1 / b) * (1 / b ^ 3) := by
          gcongr
        _ = 160 / b ^ 4 := by
          field_simp [hb.ne']
          ring
  have hclamp : LipschitzWith 1 (fun h : ℝ => max b h) := by
    simpa only [id_eq] using (LipschitzWith.id.const_max b :
      LipschitzWith 1 (fun h : ℝ => max b (id h)))
  have hcomposeOn : LipschitzOnWith (C * 1)
      (F ∘ fun h : ℝ => max b h) Set.univ :=
    hraw.comp hclamp.lipschitzOnWith
      (by intro h hh; exact le_max_left b h)
  have hcompose : LipschitzWith C (F ∘ fun h : ℝ => max b h) := by
    have h := lipschitzOnWith_univ.mp hcomposeOn
    simpa using h
  change LipschitzWith (ccmThirdGradeCesaroTriangularLipschitzConstant b)
    (fun h : ℝ => max
      (ccmGuinandWeilThirdGradeCesaroTriangularWeight H (max b h)) 0)
  simpa [Function.comp_apply, F, C] using
    hcompose.max_const 0

theorem ccmThirdGradeCesaroClippedTriangularWeight_eq
    {b H h : ℝ} (hb : 0 < b) (hbh : b ≤ h) (hhH : h ≤ H) :
    ccmThirdGradeCesaroClippedTriangularWeight b H h =
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h := by
  have hH : 0 < H := hb.trans_le (hbh.trans hhH)
  have hh : 0 < h := hb.trans_le hbh
  have hfactor : 0 ≤ 1 - h / H := by
    rw [sub_nonneg, div_le_one hH]
    exact hhH
  have hweight : 0 ≤ ccmGuinandWeilThirdGradeCesaroTriangularWeight H h := by
    unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
    positivity
  simp only [ccmThirdGradeCesaroClippedTriangularWeight, max_eq_right hbh,
    max_eq_left hweight]

theorem summable_ccmThirdGradeCesaroMatchedQuadratureDefect
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    Summable (_root_.RHTower.ccmMatchedPrimePolarQuadratureDefect
      (ccmThirdGradeCesaroClippedTriangularWeight b H)) :=
  _root_.RHTower.summable_ccmMatchedPrimePolarQuadratureDefect
    (lipschitzWith_ccmThirdGradeCesaroClippedTriangularWeight hb hbH)

/-- Every finite matched-cell block tested by the literal moving triangular reporter has one
bound depending only on the fixed lower wall. The prime atom and its polar cell remain coupled in
each summand; no separate prime or polar absolute estimate is used. -/
theorem abs_sum_ccmThirdGradeCesaroMatchedQuadratureDefect_le
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) (s : Finset ℕ) :
    |∑ n ∈ s, _root_.RHTower.ccmMatchedPrimePolarQuadratureDefect
        (ccmThirdGradeCesaroClippedTriangularWeight b H) n| ≤
      (ccmThirdGradeCesaroTriangularLipschitzConstant b : ℝ) / 2 *
        ∑' n : ℕ, criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2) :=
  _root_.RHTower.abs_sum_ccmMatchedPrimePolarQuadratureDefect_le
    (lipschitzWith_ccmThirdGradeCesaroClippedTriangularWeight hb hbH) s

/-- Physical finite matched-cell block: same cutoff and strict lower-wall convention as the
literal Guinand--Weil prime window. -/
def ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock (b H : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    if b < Real.log n then
      _root_.RHTower.ccmMatchedPrimePolarQuadratureDefect
        (ccmThirdGradeCesaroClippedTriangularWeight b H) n
    else 0

theorem abs_ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock_le
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    |ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock b H| ≤
      (ccmThirdGradeCesaroTriangularLipschitzConstant b : ℝ) / 2 *
        ∑' n : ℕ, criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2) := by
  let s := (Finset.Icc 2 ⌊Real.exp H⌋₊).filter
    (fun n : ℕ => b < Real.log n)
  have h := abs_sum_ccmThirdGradeCesaroMatchedQuadratureDefect_le hb hbH s
  simpa only [ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock, s,
    Finset.sum_filter] using h

/-- Polar part of one matched scalar cell, tested by the globally clipped moving reporter. -/
def ccmThirdGradeCesaroMatchedPolarCell (b H : ℝ) (n : ℕ) : ℝ :=
  ∫ h in
      (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..
      (Real.log n + ccmActualHeadMatchedPrimePolarRadius n),
    Real.exp (h / 2) * ccmThirdGradeCesaroClippedTriangularWeight b H h

/-- Signed failure of physical matched scalar cells to cover the literal outgoing polar interval.
This is the global term not controlled by atomwise mass matching. -/
def ccmThirdGradeCesaroMatchedCoverageSeam (b H : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      if b < Real.log n then
        ccmThirdGradeCesaroMatchedPolarCell b H n else 0) -
    ∫ h in b..H,
      Real.exp (h / 2) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h

/-- Incoming exponential half of the literal hyperbolic polar density. -/
def ccmThirdGradeCesaroIncomingPolarTail (b H : ℝ) : ℝ :=
  ∫ h in b..H,
    Real.exp (-(h / 2)) *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h

private theorem ccmThirdGradeCesaro_primeSum_eq_matchedBlock_add_cells
    {b H : ℝ} (hb : 0 < b) :
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log n then
          criticalMellinAtomWeight n *
            ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log n)
        else 0) =
      ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock b H +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log n then
            ccmThirdGradeCesaroMatchedPolarCell b H n else 0 := by
  rw [ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hbn : b < Real.log n
  · have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    have hnexp : (n : ℝ) ≤ Real.exp H :=
      (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hn).2
    have hlogH : Real.log n ≤ H :=
      (Real.log_le_iff_le_exp hnpos).mpr hnexp
    simp only [if_pos hbn]
    rw [ccmThirdGradeCesaroMatchedPolarCell,
      _root_.RHTower.ccmMatchedPrimePolarQuadratureDefect]
    rw [ccmThirdGradeCesaroClippedTriangularWeight_eq hb hbn.le hlogH]
    ring
  · simp only [hbn, if_false, zero_add]

private theorem integral_thirdGradeCesaroTriangularWeight_mul_two_cosh_eq_split
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∫ h in b..H,
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
          (2 * Real.cosh (h / 2))) =
      (∫ h in b..H,
        Real.exp (h / 2) *
          ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) +
      ∫ h in b..H,
        Real.exp (-(h / 2)) *
          ccmGuinandWeilThirdGradeCesaroTriangularWeight H h := by
  have hF : ContinuousOn
      (ccmGuinandWeilThirdGradeCesaroTriangularWeight H) (Set.uIcc b H) := by
    rw [Set.uIcc_of_le hbH]
    intro h hh
    exact (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
      (ne_of_gt (hb.trans_le hh.1))).continuousAt.continuousWithinAt
  have hplus : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) volume b H :=
    ((by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).continuousOn.mul hF).intervalIntegrable
  have hminus : IntervalIntegrable
      (fun h : ℝ => Real.exp (-(h / 2)) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) volume b H :=
    ((by fun_prop : Continuous fun h : ℝ => Real.exp (-(h / 2))).continuousOn.mul hF).intervalIntegrable
  rw [← intervalIntegral.integral_add hplus hminus]
  apply intervalIntegral.integral_congr
  intro h hh
  change ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
      (2 * Real.cosh (h / 2)) =
    Real.exp (h / 2) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h +
      Real.exp (-(h / 2)) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h
  rw [Real.cosh_eq]
  ring

/-- Exact frontier decomposition for the RH-bearing literal triangular window. Local matched-cell
quadrature and the incoming exponential polar half are separated from the sole global outgoing
coverage seam; prime and outgoing polar masses are never estimated separately. -/
theorem ccmGuinandWeilPrimePolarTriangularWindow_eq_matchedBlock_add_coverageSeam_sub_incoming
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H) =
      ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock b H +
        ccmThirdGradeCesaroMatchedCoverageSeam b H -
          ccmThirdGradeCesaroIncomingPolarTail b H := by
  rw [ccmGuinandWeilPrimePolarWeightedWindow,
    ccmThirdGradeCesaro_primeSum_eq_matchedBlock_add_cells hb,
    integral_thirdGradeCesaroTriangularWeight_mul_two_cosh_eq_split hb hbH]
  unfold ccmThirdGradeCesaroMatchedCoverageSeam
    ccmThirdGradeCesaroIncomingPolarTail
  ring

/-- Incoming hyperbolic branch is uniformly harmless. Its bound depends only on the fixed lower
wall and uses no arithmetic information. -/
theorem abs_ccmThirdGradeCesaroIncomingPolarTail_le
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    |ccmThirdGradeCesaroIncomingPolarTail b H| ≤ 64 / b ^ 3 := by
  have hH : 0 < H := hb.trans_le hbH
  have htriNonneg : ∀ h ∈ Set.Icc b H,
      0 ≤ ccmGuinandWeilThirdGradeCesaroTriangularWeight H h := by
    intro h hh
    have hhpos : 0 < h := hb.trans_le hh.1
    have hfac : 0 ≤ 1 - h / H := by
      rw [sub_nonneg, div_le_one hH]
      exact hh.2
    unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
    positivity
  have htriLe : ∀ h ∈ Set.Icc b H,
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h ≤ 32 / b ^ 3 := by
    intro h hh
    have hhpos : 0 < h := hb.trans_le hh.1
    have hb3 : 0 < b ^ 3 := pow_pos hb 3
    have hpow : b ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ hb.le hh.1 3
    have hw : 32 / h ^ 3 ≤ 32 / b ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) hb3 hpow
    have hfac0 : 0 ≤ 1 - h / H := by
      rw [sub_nonneg, div_le_one hH]
      exact hh.2
    have hfac1 : 1 - h / H ≤ 1 := by
      have : 0 ≤ h / H := by positivity
      linarith
    unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
    calc
      (32 / h ^ 3) * (1 - h / H) ≤
          (32 / b ^ 3) * (1 - h / H) :=
        mul_le_mul_of_nonneg_right hw hfac0
      _ ≤ (32 / b ^ 3) * 1 :=
        mul_le_mul_of_nonneg_left hfac1 (by positivity)
      _ = 32 / b ^ 3 := by ring
  have htriCont : ContinuousOn
      (ccmGuinandWeilThirdGradeCesaroTriangularWeight H) (Set.uIcc b H) := by
    rw [Set.uIcc_of_le hbH]
    intro h hh
    exact (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
      (ne_of_gt (hb.trans_le hh.1))).continuousAt.continuousWithinAt
  have hintegrable : IntervalIntegrable
      (fun h : ℝ => Real.exp (-(h / 2)) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) volume b H :=
    ((by fun_prop : Continuous fun h : ℝ => Real.exp (-(h / 2))).continuousOn.mul
      htriCont).intervalIntegrable
  have hmajorIntegrable : IntervalIntegrable
      (fun h : ℝ => Real.exp (-(h / 2)) * (32 / b ^ 3)) volume b H :=
    (by fun_prop : Continuous fun h : ℝ =>
      Real.exp (-(h / 2)) * (32 / b ^ 3)).intervalIntegrable _ _
  have hnonneg : 0 ≤ ccmThirdGradeCesaroIncomingPolarTail b H := by
    unfold ccmThirdGradeCesaroIncomingPolarTail
    apply intervalIntegral.integral_nonneg hbH
    intro h hh
    exact mul_nonneg (Real.exp_pos _).le (htriNonneg h hh)
  have hmono : ccmThirdGradeCesaroIncomingPolarTail b H ≤
      ∫ h in b..H, Real.exp (-(h / 2)) * (32 / b ^ 3) := by
    unfold ccmThirdGradeCesaroIncomingPolarTail
    apply intervalIntegral.integral_mono_on hbH hintegrable hmajorIntegrable
    intro h hh
    exact mul_le_mul_of_nonneg_left (htriLe h hh) (Real.exp_pos _).le
  have hexpInt : IntervalIntegrable
      (fun h : ℝ => Real.exp (-(h / 2))) volume b H :=
    (by fun_prop : Continuous fun h : ℝ => Real.exp (-(h / 2))).intervalIntegrable _ _
  have hexpVal : (∫ h in b..H, Real.exp (-(h / 2))) =
      -2 * Real.exp (-(H / 2)) - (-2 * Real.exp (-(b / 2))) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro h hh
      have hinner : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2 : ℝ) h := by
        simpa using ((hasDerivAt_id h).neg.div_const 2)
      have hderiv := hinner.exp.const_mul (-2 : ℝ)
      have hval : (-2 : ℝ) * (Real.exp (-h / 2) * (-1 / 2)) =
          Real.exp (-h / 2) := by ring
      rw [hval] at hderiv
      simpa only [neg_div] using hderiv
    · exact hexpInt
  have hexpLe : (∫ h in b..H, Real.exp (-(h / 2))) ≤ 2 := by
    rw [hexpVal]
    have hHb : 0 < Real.exp (-(H / 2)) := Real.exp_pos _
    have hbe : Real.exp (-(b / 2)) ≤ 1 := by
      simpa only [← Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : -(b / 2) ≤ 0)
    linarith
  rw [abs_of_nonneg hnonneg]
  calc
    ccmThirdGradeCesaroIncomingPolarTail b H ≤
        ∫ h in b..H, Real.exp (-(h / 2)) * (32 / b ^ 3) := hmono
    _ = (32 / b ^ 3) * ∫ h in b..H, Real.exp (-(h / 2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro h hh
      ring
    _ ≤ (32 / b ^ 3) * 2 :=
      mul_le_mul_of_nonneg_left hexpLe (by positivity)
    _ = 64 / b ^ 3 := by ring

/-- Uniform boundedness of the literal triangular prime--polar window is exactly uniform
boundedness of the outgoing matched-cell coverage seam. All other terms have explicit fixed-wall
bounds. This equivalence rules out treating local matched quadrature as completion of CCM-FU. -/
theorem uniformlyBounded_primePolarTriangularWindow_iff_matchedCoverageSeam
    {b : ℝ} (hb : 0 < b) :
    (∃ C : ℝ, ∀ H : ℝ, b ≤ H →
      |ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)| ≤ C) ↔
    (∃ C : ℝ, ∀ H : ℝ, b ≤ H →
      |ccmThirdGradeCesaroMatchedCoverageSeam b H| ≤ C) := by
  let L : ℝ :=
    (ccmThirdGradeCesaroTriangularLipschitzConstant b : ℝ) / 2 *
      ∑' n : ℕ, criticalMellinAtomWeight n ^ 2 /
        Real.exp (Real.log n / 2)
  let I : ℝ := 64 / b ^ 3
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + L + I, ?_⟩
    intro H hbH
    let W := ccmGuinandWeilPrimePolarWeightedWindow b H
      (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)
    let B := ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock b H
    let S := ccmThirdGradeCesaroMatchedCoverageSeam b H
    let J := ccmThirdGradeCesaroIncomingPolarTail b H
    have hid :=
      ccmGuinandWeilPrimePolarTriangularWindow_eq_matchedBlock_add_coverageSeam_sub_incoming
        hb hbH
    have hW : |W| ≤ C := hC H hbH
    have hB := abs_ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock_le hb hbH
    have hJ := abs_ccmThirdGradeCesaroIncomingPolarTail_le hb hbH
    change |B| ≤ L at hB
    change |J| ≤ I at hJ
    change W = B + S - J at hid
    have hSid : S = W - B + J := by linarith
    have htri1 : |W - B + J| ≤ |W - B| + |J| := abs_add_le _ _
    have htri2 : |W - B| ≤ |W| + |B| := abs_sub _ _
    change |S| ≤ C + L + I
    rw [hSid]
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨L + C + I, ?_⟩
    intro H hbH
    let W := ccmGuinandWeilPrimePolarWeightedWindow b H
      (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)
    let B := ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock b H
    let S := ccmThirdGradeCesaroMatchedCoverageSeam b H
    let J := ccmThirdGradeCesaroIncomingPolarTail b H
    have hid :=
      ccmGuinandWeilPrimePolarTriangularWindow_eq_matchedBlock_add_coverageSeam_sub_incoming
        hb hbH
    have hS : |S| ≤ C := hC H hbH
    have hB := abs_ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock_le hb hbH
    have hJ := abs_ccmThirdGradeCesaroIncomingPolarTail_le hb hbH
    change |B| ≤ L at hB
    change |J| ≤ I at hJ
    change W = B + S - J at hid
    have htri1 : |B + S - J| ≤ |B + S| + |J| := abs_sub _ _
    have htri2 : |B + S| ≤ |B| + |S| := abs_add_le _ _
    change |W| ≤ L + C + I
    rw [hid]
    linarith

/-- RH-bearing anchored completed-error moment is uniformly bounded exactly when the newly
isolated outgoing matched-coverage seam is uniformly bounded. -/
theorem uniformlyBounded_thirdGradeCesaroAnchoredErrorMoment_iff_matchedCoverageSeam
    {b : ℝ} (hb : 0 < b) :
    (∃ C : ℝ, ∀ H : ℝ, b ≤ H →
      |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| ≤ C) ↔
    (∃ C : ℝ, ∀ H : ℝ, b ≤ H →
      |ccmThirdGradeCesaroMatchedCoverageSeam b H| ≤ C) := by
  rw [← uniformlyBounded_primePolarTriangularWindow_iff_matchedCoverageSeam hb]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro H hbH
    rw [← ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_primePolarTriangularWindow
      hb hbH]
    exact hC H hbH
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro H hbH
    rw [ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_primePolarTriangularWindow
      hb hbH]
    exact hC H hbH

end GaloisForLFunctions.RHTower
