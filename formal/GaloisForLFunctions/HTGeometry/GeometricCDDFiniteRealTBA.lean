import GaloisForLFunctions.HTGeometry.GeometricCDDBoundarySelection
import GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Contracting

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One summand of the geometric CDD rapidity-delay kernel. -/
def geometricCDDTBAKernelTerm (q C θ : ℝ) (k : ℕ) : ℝ :=
  4 * (q ^ k * Real.cosh θ / C) /
    (1 + (q ^ k * Real.sinh θ / C) ^ 2)

/-- Exact infinite geometric CDD rapidity-delay kernel. -/
def geometricCDDTBAKernel (q C θ : ℝ) : ℝ :=
  ∑' k : ℕ, geometricCDDTBAKernelTerm q C θ k

theorem summable_geometricCDDTBAKernelTerm
    {q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 < C) (θ : ℝ) :
    Summable (geometricCDDTBAKernelTerm q C θ) := by
  have hgeom : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_lt_one hq0 hq1
  apply (hgeom.mul_left (4 * (Real.cosh θ / C))).of_norm_bounded
  intro k
  unfold geometricCDDTBAKernelTerm
  rw [Real.norm_eq_abs]
  have hnum : 0 ≤ 4 * (q ^ k * Real.cosh θ / C) := by positivity
  rw [abs_of_nonneg (div_nonneg hnum (by positivity))]
  calc
    4 * (q ^ k * Real.cosh θ / C) /
          (1 + (q ^ k * Real.sinh θ / C) ^ 2) ≤
        4 * (q ^ k * Real.cosh θ / C) :=
      div_le_self hnum (by nlinarith [sq_nonneg (q ^ k * Real.sinh θ / C)])
    _ = 4 * (Real.cosh θ / C) * q ^ k := by ring

theorem geometricCDDTBAKernelTerm_nonneg
    {q C : ℝ} (hq0 : 0 ≤ q) (hC : 0 < C) (θ : ℝ) (k : ℕ) :
    0 ≤ geometricCDDTBAKernelTerm q C θ k := by
  unfold geometricCDDTBAKernelTerm
  positivity

theorem geometricCDDTBAKernel_even (q C : ℝ) :
    Function.Even (geometricCDDTBAKernel q C) := by
  intro θ
  unfold geometricCDDTBAKernel geometricCDDTBAKernelTerm
  apply tsum_congr
  intro k
  rw [Real.cosh_neg, Real.sinh_neg]
  ring_nf

/-- A scale `x ≥ 1` meets a unique-enough geometric shell in `[1,q⁻¹)`. -/
theorem exists_geometric_shell
    {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : 1 ≤ x) :
    ∃ n : ℕ, 1 ≤ q ^ n * x ∧ q ^ n * x < q⁻¹ := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxin : 0 < x⁻¹ := inv_pos.mpr hx0
  have hxle : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  obtain ⟨n, hnlt, hnle⟩ :=
    exists_nat_pow_near_of_lt_one hxin hxle hq0 hq1
  refine ⟨n, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hnle hx0.le
    simpa [inv_mul_cancel₀ hx0.ne'] using this
  · have hqnx : q * (q ^ n * x) < 1 := by
      calc
        q * (q ^ n * x) = q ^ (n + 1) * x := by rw [pow_succ']; ring
        _ < x⁻¹ * x := mul_lt_mul_of_pos_right hnlt hx0
        _ = 1 := inv_mul_cancel₀ hx0.ne'
    have hinv : q ^ n * x < q⁻¹ * 1 :=
      (lt_inv_mul_iff₀ hq0).mpr (by simpa [mul_assoc] using hqnx)
    simpa using hinv

theorem four_mul_q_le_shellDelay
    {q y : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hy1 : 1 ≤ y) (hyq : y < q⁻¹) :
    4 * q / (1 + q ^ 2) ≤ 4 * y / (1 + y ^ 2) := by
  have hqle1 : q ≤ 1 := hq1.le
  have hy0 : 0 < y := zero_lt_one.trans_le hy1
  have hqy : q * y < 1 := by
    have hyq' : y < q⁻¹ * 1 := by simpa using hyq
    simpa using (lt_inv_mul_iff₀ hq0).mp hyq'
  have hdenq : 0 < 1 + q ^ 2 := by positivity
  have hdeny : 0 < 1 + y ^ 2 := by positivity
  rw [div_le_div_iff₀ hdenq hdeny]
  nlinarith

theorem geometricCDDLogShellDelay_nonneg {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ geometricCDDLogShellDelay z := by
  unfold geometricCDDLogShellDelay
  positivity

theorem geometricCDDLogShellDelay_le_four_mul {z : ℝ} (hz : 0 ≤ z) :
    geometricCDDLogShellDelay z ≤ 4 * z := by
  unfold geometricCDDLogShellDelay
  exact div_le_self (by positivity) (by nlinarith [sq_nonneg z])

theorem geometricCDDLogShellDelay_le_four_mul_inv {z : ℝ} (hz : 0 < z) :
    geometricCDDLogShellDelay z ≤ 4 * z⁻¹ := by
  unfold geometricCDDLogShellDelay
  have hden : 0 < 1 + z ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  field_simp
  nlinarith [sq_nonneg z]

/-- The logarithmic shell sum is uniformly bounded on the ultraviolet half-line. -/
theorem geometricCDDLogPhaseDelay_le
    {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : 1 ≤ x) :
    geometricCDDLogPhaseDelay q x ≤ 8 * (1 - q)⁻¹ := by
  obtain ⟨n, hyn1, hynq⟩ := exists_geometric_shell hq0 hq1 hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hq0' : 0 ≤ q := hq0.le
  have hqabs : |q| < 1 := by simpa [abs_of_pos hq0] using hq1
  let f : ℕ → ℝ := fun k => geometricCDDLogShellDelay (q ^ k * x)
  have hf : Summable f := by
    simpa [f, geometricCDDLogPhaseDelay, geometricCDDLogShellDelay] using
      summable_geometricCDDLogPhaseDelay hqabs x
  have hsplit := hf.sum_add_tsum_nat_add (n + 1)
  have hgeom : Summable (fun j : ℕ => 4 * q ^ j) :=
    (summable_geometric_of_lt_one hq0' hq1).mul_left 4
  have hearlyTerm : ∀ k ∈ Finset.range (n + 1),
      f k ≤ 4 * q ^ (n - k) := by
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hz : 0 < q ^ k * x := mul_pos (pow_pos hq0 k) hx0
    have hpowid : q ^ (n - k) * (q ^ k * x) = q ^ n * x := by
      calc
        q ^ (n - k) * (q ^ k * x) = (q ^ (n - k) * q ^ k) * x := by ring
        _ = q ^ ((n - k) + k) * x := by rw [pow_add]
        _ = q ^ n * x := by rw [Nat.sub_add_cancel hkn]
    have hinv : (q ^ k * x)⁻¹ ≤ q ^ (n - k) := by
      rw [inv_le_iff_one_le_mul₀' hz]
      calc
        1 ≤ q ^ (n - k) * (q ^ k * x) := by rw [hpowid]; exact hyn1
        _ = q ^ k * x * q ^ (n - k) := by ring
    exact (geometricCDDLogShellDelay_le_four_mul_inv hz).trans
      (mul_le_mul_of_nonneg_left hinv (by norm_num))
  have hearly : (∑ k ∈ Finset.range (n + 1), f k) ≤ 4 * (1 - q)⁻¹ := by
    calc
      (∑ k ∈ Finset.range (n + 1), f k) ≤
          ∑ k ∈ Finset.range (n + 1), 4 * q ^ (n - k) :=
        Finset.sum_le_sum hearlyTerm
      _ = ∑ j ∈ Finset.range (n + 1), 4 * q ^ j := by
        have hreflect := Finset.sum_range_reflect (fun j : ℕ => 4 * q ^ j) (n + 1)
        simpa using hreflect
      _ ≤ ∑' j : ℕ, 4 * q ^ j :=
        Summable.sum_le_tsum (Finset.range (n + 1)) (fun j _ => by positivity) hgeom
      _ = 4 * (1 - q)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0' hq1]
  have hqn1 : q ^ (n + 1) * x ≤ 1 := by
    have hqy : q * (q ^ n * x) < 1 := by
      have hyq' : q ^ n * x < q⁻¹ * 1 := by simpa using hynq
      simpa using (lt_inv_mul_iff₀ hq0).mp hyq'
    rw [pow_succ']
    nlinarith
  have htailTerm : ∀ j : ℕ,
      f (j + (n + 1)) ≤ 4 * q ^ j := by
    intro j
    have hz0 : 0 ≤ q ^ (j + (n + 1)) * x := by positivity
    calc
      f (j + (n + 1)) ≤ 4 * (q ^ (j + (n + 1)) * x) :=
        geometricCDDLogShellDelay_le_four_mul hz0
      _ = 4 * (q ^ j * (q ^ (n + 1) * x)) := by
        rw [pow_add]
        ring
      _ ≤ 4 * q ^ j := by
        have := mul_le_mul_of_nonneg_left hqn1 (pow_nonneg hq0' j)
        nlinarith
  have htailSummable : Summable (fun j : ℕ => f (j + (n + 1))) :=
    hf.comp_injective (by
      intro i j hij
      exact Nat.add_right_cancel hij)
  have htail : (∑' j : ℕ, f (j + (n + 1))) ≤ 4 * (1 - q)⁻¹ := by
    calc
      (∑' j : ℕ, f (j + (n + 1))) ≤ ∑' j : ℕ, 4 * q ^ j :=
        Summable.tsum_le_tsum htailTerm htailSummable hgeom
      _ = 4 * (1 - q)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0' hq1]
  unfold geometricCDDLogPhaseDelay
  change (∑' k : ℕ, f k) ≤ _
  rw [← hsplit]
  linarith [inv_nonneg.mpr (sub_nonneg.mpr hq1.le)]

theorem geometricCDDTBAKernel_eq_cosh_div_absSinh_mul_delay
    {q C θ : ℝ} (hC : 0 < C) (hθ : Real.sinh θ ≠ 0) :
    geometricCDDTBAKernel q C θ =
      Real.cosh θ / |Real.sinh θ| *
        geometricCDDLogPhaseDelay q (|Real.sinh θ| / C) := by
  unfold geometricCDDTBAKernel geometricCDDLogPhaseDelay
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold geometricCDDTBAKernelTerm
  have habs : |Real.sinh θ| ≠ 0 := abs_ne_zero.mpr hθ
  have hsq : (q ^ k * (|Real.sinh θ| / C)) ^ 2 =
      (q ^ k * Real.sinh θ / C) ^ 2 := by
    rw [mul_div_assoc, mul_pow, mul_pow, div_pow, div_pow, sq_abs]
  rw [hsq]
  field_simp [hC.ne', habs]

theorem geometricCDDTBAKernel_upper
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    geometricCDDTBAKernel q C θ ≤
      8 * Real.sqrt (1 + C ^ 2) / (C * (1 - q)) := by
  have hC0 : 0 < C := zero_lt_one.trans hC
  have hq0' : 0 ≤ q := hq0.le
  have hqsub : 0 < 1 - q := sub_pos.mpr hq1
  have hsqrt0 : 0 ≤ Real.sqrt (1 + C ^ 2) := Real.sqrt_nonneg _
  have hsqrtsq : Real.sqrt (1 + C ^ 2) ^ 2 = 1 + C ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hs := summable_geometricCDDTBAKernelTerm hq0' hq1 hC0 θ
  let x := |Real.sinh θ| / C
  by_cases hx : x ≤ 1
  · have hsinh : |Real.sinh θ| ≤ C := by
      dsimp [x] at hx
      rwa [div_le_one hC0] at hx
    have hcosh : Real.cosh θ ≤ Real.sqrt (1 + C ^ 2) := by
      apply (sq_le_sq₀ (Real.cosh_pos θ).le hsqrt0).mp
      rw [hsqrtsq]
      have hsinhSq : Real.sinh θ ^ 2 ≤ C ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_pos hC0] using hsinh
      nlinarith [Real.cosh_sq_sub_sinh_sq θ]
    have hgeom : Summable (fun k : ℕ => 4 * (Real.cosh θ / C) * q ^ k) :=
      (summable_geometric_of_lt_one hq0' hq1).mul_left _
    have hterm : ∀ k : ℕ, geometricCDDTBAKernelTerm q C θ k ≤
        4 * (Real.cosh θ / C) * q ^ k := by
      intro k
      unfold geometricCDDTBAKernelTerm
      have hnum : 0 ≤ 4 * (q ^ k * Real.cosh θ / C) := by positivity
      calc
        4 * (q ^ k * Real.cosh θ / C) /
            (1 + (q ^ k * Real.sinh θ / C) ^ 2) ≤
            4 * (q ^ k * Real.cosh θ / C) :=
          div_le_self hnum (by nlinarith [sq_nonneg (q ^ k * Real.sinh θ / C)])
        _ = 4 * (Real.cosh θ / C) * q ^ k := by ring
    unfold geometricCDDTBAKernel
    calc
      (∑' k : ℕ, geometricCDDTBAKernelTerm q C θ k) ≤
          ∑' k : ℕ, 4 * (Real.cosh θ / C) * q ^ k :=
        Summable.tsum_le_tsum hterm hs hgeom
      _ = 4 * (Real.cosh θ / C) * (1 - q)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0' hq1]
      _ ≤ 4 * (Real.sqrt (1 + C ^ 2) / C) * (1 - q)⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hcosh hC0.le) (by norm_num))
          (inv_nonneg.mpr hqsub.le)
      _ ≤ 8 * Real.sqrt (1 + C ^ 2) / (C * (1 - q)) := by
        field_simp
        nlinarith
  · have hx1 : 1 ≤ x := le_of_not_ge hx
    have hθ : Real.sinh θ ≠ 0 := by
      intro hzero
      have : x = 0 := by simp [x, hzero]
      rw [this] at hx1
      norm_num at hx1
    have hsinhC : C ≤ |Real.sinh θ| := by
      dsimp [x] at hx1
      rwa [one_le_div hC0] at hx1
    have hsinh0 : 0 < |Real.sinh θ| := lt_of_lt_of_le hC0 hsinhC
    have hfactor : Real.cosh θ / |Real.sinh θ| ≤
        Real.sqrt (1 + C ^ 2) / C := by
      rw [div_le_div_iff₀ hsinh0 hC0]
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      rw [mul_pow, mul_pow, hsqrtsq, sq_abs]
      have hsinhSq : C ^ 2 ≤ Real.sinh θ ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_pos hC0] using hsinhC
      nlinarith [Real.cosh_sq_sub_sinh_sq θ]
    rw [geometricCDDTBAKernel_eq_cosh_div_absSinh_mul_delay hC0 hθ]
    have hdelay := geometricCDDLogPhaseDelay_le hq0 hq1 hx1
    have hdelay0 : 0 ≤ geometricCDDLogPhaseDelay q x := by
      unfold geometricCDDLogPhaseDelay
      exact tsum_nonneg fun k => geometricCDDLogShellDelay_nonneg (by positivity)
    calc
      Real.cosh θ / |Real.sinh θ| * geometricCDDLogPhaseDelay q x ≤
          (Real.sqrt (1 + C ^ 2) / C) * geometricCDDLogPhaseDelay q x :=
        mul_le_mul_of_nonneg_right hfactor hdelay0
      _ ≤ (Real.sqrt (1 + C ^ 2) / C) * (8 * (1 - q)⁻¹) :=
        mul_le_mul_of_nonneg_left hdelay (by positivity)
      _ = 8 * Real.sqrt (1 + C ^ 2) / (C * (1 - q)) := by
        field_simp

theorem geometricCDDTBAKernel_floor
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    min (2 / C) (4 * q / (1 + q ^ 2)) ≤ geometricCDDTBAKernel q C θ := by
  have hC0 : 0 < C := zero_lt_one.trans hC
  have hs := summable_geometricCDDTBAKernelTerm hq0.le hq1 hC0 θ
  have hnonneg := geometricCDDTBAKernelTerm_nonneg hq0.le hC0 θ
  let x := |Real.sinh θ| / C
  by_cases hx : x ≤ 1
  · have hterm0 : 2 / C ≤ geometricCDDTBAKernelTerm q C θ 0 := by
      unfold geometricCDDTBAKernelTerm
      simp only [pow_zero, one_mul]
      have hcosh : 1 ≤ Real.cosh θ := Real.one_le_cosh θ
      have hx' : (Real.sinh θ / C) ^ 2 ≤ 1 := by
        have habs : |Real.sinh θ / C| ≤ 1 := by
          simpa [x, abs_div, abs_of_pos hC0] using hx
        rw [← sq_abs]
        simpa using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr habs
      have hden : 0 < 1 + (Real.sinh θ / C) ^ 2 := by positivity
      have hinner : 2 ≤ 4 * Real.cosh θ /
          (1 + (Real.sinh θ / C) ^ 2) := by
        rw [le_div_iff₀ hden]
        nlinarith
      calc
        2 / C ≤ (4 * Real.cosh θ /
            (1 + (Real.sinh θ / C) ^ 2)) / C :=
          div_le_div_of_nonneg_right hinner hC0.le
        _ = 4 * (Real.cosh θ / C) /
            (1 + (Real.sinh θ / C) ^ 2) := by field_simp
    exact (min_le_left _ _).trans
      (hterm0.trans (hs.le_tsum 0 (fun j _ => hnonneg j)))
  · have hx1 : 1 ≤ x := le_of_not_ge hx
    obtain ⟨n, hyn1, hynq⟩ := exists_geometric_shell hq0 hq1 hx1
    let y := q ^ n * x
    have hy1 : 1 ≤ y := hyn1
    have hyq : y < q⁻¹ := hynq
    have hshell : 4 * q / (1 + q ^ 2) ≤ 4 * y / (1 + y ^ 2) :=
      four_mul_q_le_shellDelay hq0 hq1 hy1 hyq
    have hsinh0 : 0 < |Real.sinh θ| := by
      rw [abs_pos]
      intro hsinh
      have : x = 0 := by simp [x, hsinh]
      rw [this] at hx1
      norm_num at hx1
    have hcosh : |Real.sinh θ| ≤ Real.cosh θ := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.cosh_pos θ).le).mp
      rw [sq_abs]
      nlinarith [Real.cosh_sq_sub_sinh_sq θ]
    have hterm : 4 * y / (1 + y ^ 2) ≤
        geometricCDDTBAKernelTerm q C θ n := by
      unfold geometricCDDTBAKernelTerm
      dsimp [y, x]
      have hpow : 0 ≤ q ^ n := pow_nonneg hq0.le n
      have habsdiv : |Real.sinh θ| / C = |Real.sinh θ / C| := by
        rw [abs_div, abs_of_pos hC0]
      rw [habsdiv]
      have hsq : (q ^ n * |Real.sinh θ / C|) ^ 2 =
          (q ^ n * (Real.sinh θ / C)) ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs]
      rw [hsq]
      have hden : 0 < 1 + (q ^ n * (Real.sinh θ / C)) ^ 2 := by positivity
      have hnumle : 4 * (q ^ n * |Real.sinh θ / C|) ≤
          4 * (q ^ n * Real.cosh θ / C) := by
        rw [abs_div, abs_of_pos hC0]
        have hscaled := mul_le_mul_of_nonneg_left hcosh hpow
        have hbase : q ^ n * (|Real.sinh θ| / C) ≤
            q ^ n * Real.cosh θ / C := by
          simpa only [mul_div_assoc] using
            div_le_div_of_nonneg_right hscaled hC0.le
        exact mul_le_mul_of_nonneg_left hbase (by norm_num)
      have hdiv := div_le_div_of_nonneg_right hnumle hden.le
      simpa only [mul_div_assoc] using hdiv
    exact (min_le_right _ _).trans
      (hshell.trans (hterm.trans (hs.le_tsum n (fun j _ => hnonneg j))))

theorem measurable_geometricCDDTBAKernel (q C : ℝ) :
    Measurable (geometricCDDTBAKernel q C) := by
  unfold geometricCDDTBAKernel
  apply Measurable.tsum
  intro k
  unfold geometricCDDTBAKernelTerm
  fun_prop

theorem continuous_geometricCDDTBAKernel
    {q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 < C) :
    Continuous (geometricCDDTBAKernel q C) := by
  rw [continuous_iff_continuousAt]
  intro θ₀
  let B := 4 * (Real.exp (|θ₀| + 1) / C)
  let u : ℕ → ℝ := fun k => B * q ^ k
  have hu : Summable u :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left B
  have htermCont : ∀ k : ℕ, Continuous (geometricCDDTBAKernelTerm q C · k) := by
    intro k
    unfold geometricCDDTBAKernelTerm
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro θ
      positivity
  have hbound : ∀ k : ℕ, ∀ θ ∈ Set.Icc (θ₀ - 1) (θ₀ + 1),
      ‖geometricCDDTBAKernelTerm q C θ k‖ ≤ u k := by
    intro k θ hθ
    have habsdiff : |θ - θ₀| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
    have habsθ : |θ| ≤ |θ₀| + 1 := by
      calc
        |θ| = |(θ - θ₀) + θ₀| := by ring_nf
        _ ≤ |θ - θ₀| + |θ₀| := abs_add_le _ _
        _ ≤ |θ₀| + 1 := by linarith
    have hcosh : Real.cosh θ ≤ Real.exp (|θ₀| + 1) :=
      (cosh_le_exp_abs θ).trans (Real.exp_le_exp.mpr habsθ)
    unfold geometricCDDTBAKernelTerm
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hnum : 0 ≤ 4 * (q ^ k * Real.cosh θ / C) := by positivity
    calc
      4 * (q ^ k * Real.cosh θ / C) /
          (1 + (q ^ k * Real.sinh θ / C) ^ 2) ≤
          4 * (q ^ k * Real.cosh θ / C) :=
        div_le_self hnum (by nlinarith [sq_nonneg (q ^ k * Real.sinh θ / C)])
      _ ≤ 4 * (q ^ k * Real.exp (|θ₀| + 1) / C) := by
        gcongr
      _ = u k := by dsimp [u, B]; ring
  have hcontOn : ContinuousOn (geometricCDDTBAKernel q C)
      (Set.Icc (θ₀ - 1) (θ₀ + 1)) := by
    unfold geometricCDDTBAKernel
    exact continuousOn_tsum (fun k => (htermCont k).continuousOn) hu hbound
  exact hcontOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

theorem one_add_sq_div_two_le_cosh (θ : ℝ) :
    1 + θ ^ 2 / 2 ≤ Real.cosh θ := by
  have hs := (Real.hasSum_cosh θ).summable
  have hpartial := Summable.sum_le_tsum (Finset.range 2) (fun n _ => by
    have hpow : 0 ≤ θ ^ (2 * n) := by
      rw [show 2 * n = n + n by omega, pow_add]
      exact mul_self_nonneg (θ ^ n)
    exact div_nonneg hpow (by
      exact_mod_cast (Nat.zero_le (2 * n).factorial))) hs
  rw [← Real.cosh_eq_tsum] at hpartial
  norm_num [Finset.sum_range_succ] at hpartial ⊢
  simpa [pow_two] using hpartial

theorem integrable_exp_neg_mul_cosh {r : ℝ} (hr : 0 < r) :
    Integrable (fun θ : ℝ => Real.exp (-r * Real.cosh θ)) := by
  have hgauss := (integrable_exp_neg_mul_sq (half_pos hr)).const_mul (Real.exp (-r))
  apply hgauss.mono'
  · fun_prop
  · filter_upwards with θ
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))] using
      (show Real.exp (-r * Real.cosh θ) ≤
          Real.exp (-r) * Real.exp (-(r / 2) * θ ^ 2) from by
        calc
          Real.exp (-r * Real.cosh θ) ≤
              Real.exp (-r * (1 + θ ^ 2 / 2)) := by
            exact Real.exp_le_exp.mpr
              (mul_le_mul_of_nonpos_left (one_add_sq_div_two_le_cosh θ)
                (neg_nonpos.mpr hr.le))
          _ = Real.exp (-r) * Real.exp (-(r / 2) * θ ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            ring)

theorem integral_exp_neg_mul_cosh_le
    {r : ℝ} (hr : 1 ≤ r) :
    (∫ θ : ℝ, Real.exp (-r * Real.cosh θ)) ≤
      Real.exp (-(r / 2)) *
        (∫ θ : ℝ, Real.exp (-(1 / 2 : ℝ) * θ ^ 2)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hleft := integrable_exp_neg_mul_cosh hr0
  have hgauss := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have hright := hgauss.const_mul (Real.exp (-(r / 2)))
  rw [← integral_const_mul]
  apply integral_mono hleft hright
  intro θ
  change Real.exp (-r * Real.cosh θ) ≤
    Real.exp (-(r / 2)) * Real.exp (-(1 / 2) * θ ^ 2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcosh := one_add_sq_div_two_le_cosh θ
  have hsq : 0 ≤ θ ^ 2 := sq_nonneg θ
  nlinarith

theorem tendsto_integral_exp_neg_mul_cosh_atTop :
    Tendsto (fun r : ℝ => ∫ θ : ℝ, Real.exp (-r * Real.cosh θ))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun r => integral_nonneg fun θ => (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact integral_exp_neg_mul_cosh_le hr
  · have hexp : Tendsto (fun r : ℝ => Real.exp (-(r / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    convert hexp.mul_const
      (∫ θ : ℝ, Real.exp (-(1 / 2 : ℝ) * θ ^ 2)) using 1 <;> simp

/-- Fermionic TBA occupation associated to a real pseudoenergy. -/
def fermionicTBAOccupation (ε : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-ε θ))

/-- Dimensionless finite free energy, with the physical `2π` normalization. -/
def fermionicTBAFreeEnergy (ε : ℝ → ℝ) : ℝ :=
  (∫ θ : ℝ, fermionicTBAOccupation ε θ) / (2 * Real.pi)

/-- Literal real finite-free-energy solution class for the scalar fermionic TBA equation. -/
def IsRealFiniteFreeEnergyTBASolution (φ : ℝ → ℝ) (r : ℝ) (ε : ℝ → ℝ) : Prop :=
  Measurable ε ∧
    Integrable (fermionicTBAOccupation ε) ∧
    (∀ θ : ℝ, Integrable (fun θ' => φ (θ - θ') * fermionicTBAOccupation ε θ')) ∧
    (∀ θ : ℝ, ε θ = r * Real.cosh θ -
      (∫ θ' : ℝ, φ (θ - θ') * fermionicTBAOccupation ε θ') / (2 * Real.pi))

theorem fermionicTBAOccupation_pos (ε : ℝ → ℝ) (θ : ℝ) :
    0 < fermionicTBAOccupation ε θ := by
  unfold fermionicTBAOccupation
  exact Real.log_pos (by linarith [Real.exp_pos (-ε θ)])

theorem fermionicTBAOccupation_nonneg (ε : ℝ → ℝ) (θ : ℝ) :
    0 ≤ fermionicTBAOccupation ε θ :=
  (fermionicTBAOccupation_pos ε θ).le

/-- Sharp elementary softplus lower bound used by the exclusion radius. -/
theorem div_one_add_exp_one_lt_log_one_add_exp_sub_one
    (a : ℝ) :
    a / (1 + Real.exp 1) < Real.log (1 + Real.exp (a - 1)) := by
  let w0 : ℝ := Real.exp 1 / (1 + Real.exp 1)
  let w1 : ℝ := 1 / (1 + Real.exp 1)
  have hden : 0 < 1 + Real.exp 1 := by positivity
  have hw0 : 0 ≤ w0 := by dsimp [w0]; positivity
  have hw1 : 0 ≤ w1 := by dsimp [w1]; positivity
  have hwsum : w0 + w1 = 1 := by
    dsimp [w0, w1]
    field_simp
    ring
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
    (Set.mem_univ a) hw0 hw1 hwsum
  have harg : w0 • (0 : ℝ) + w1 • a = a / (1 + Real.exp 1) := by
    dsimp [w0, w1]
    simp only [mul_zero, zero_add]
    ring
  rw [harg, Real.exp_zero] at hconv
  have harith : w0 * 1 + w1 * Real.exp a < 1 + Real.exp (a - 1) := by
    dsimp [w0, w1]
    rw [Real.exp_sub]
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have hnum : 0 < Real.exp 1 + Real.exp a := by positivity
    field_simp
    nlinarith
  have hexp : Real.exp (a / (1 + Real.exp 1)) < 1 + Real.exp (a - 1) :=
    hconv.trans_lt harith
  have hright : 0 < 1 + Real.exp (a - 1) := by
    linarith [Real.exp_pos (a - 1)]
  have hlog := Real.strictMonoOn_log (Real.exp_pos _) hright hexp
  simpa [Real.log_exp] using hlog

/-- Explicit positive radius below which the geometric CDD TBA has no real physical solution. -/
def geometricCDDTBAExclusionRadius (q C : ℝ) : ℝ :=
  Real.exp (-Real.pi * (1 + Real.exp 1) /
    min (2 / C) (4 * q / (1 + q ^ 2)))

theorem geometricCDDTBAExclusionRadius_pos (q C : ℝ) :
    0 < geometricCDDTBAExclusionRadius q C :=
  Real.exp_pos _

theorem geometricCDDTBAKernel_floor_pos
    {q C : ℝ} (hq0 : 0 < q) (hC : 1 < C) :
    0 < min (2 / C) (4 * q / (1 + q ^ 2)) := by
  apply lt_min
  · positivity
  · positivity

theorem no_realFiniteFreeEnergyTBASolution_geometricCDD_of_smallRadius
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C)
    (hr0 : 0 < r) (hr : r ≤ geometricCDDTBAExclusionRadius q C) :
    ¬ ∃ ε : ℝ → ℝ,
      IsRealFiniteFreeEnergyTBASolution (geometricCDDTBAKernel q C) r ε := by
  rintro ⟨ε, hεmeas, hLint, hconvInt, heq⟩
  let c := min (2 / C) (4 * q / (1 + q ^ 2))
  let A := fermionicTBAFreeEnergy ε
  let L := Real.log (1 / r)
  have hc : 0 < c := geometricCDDTBAKernel_floor_pos hq0 hC
  have hpi : 0 < 2 * Real.pi := by positivity
  have hLnonneg : ∀ θ, 0 ≤ fermionicTBAOccupation ε θ :=
    fermionicTBAOccupation_nonneg ε
  have hA0 : 0 ≤ A := by
    dsimp [A, fermionicTBAFreeEnergy]
    exact div_nonneg (integral_nonneg hLnonneg) hpi.le
  have hkernel : ∀ θ, c ≤ geometricCDDTBAKernel q C θ :=
    geometricCDDTBAKernel_floor hq0 hq1 hC
  have hepsilon : ∀ θ, ε θ ≤ r * Real.cosh θ - c * A := by
    intro θ
    have hconstInt : Integrable (fun θ' => c * fermionicTBAOccupation ε θ') :=
      hLint.const_mul c
    have hconvLower : c * (∫ θ' : ℝ, fermionicTBAOccupation ε θ') ≤
        ∫ θ' : ℝ, geometricCDDTBAKernel q C (θ - θ') *
          fermionicTBAOccupation ε θ' := by
      rw [← integral_const_mul]
      apply integral_mono hconstInt (hconvInt θ)
      intro θ'
      exact mul_le_mul_of_nonneg_right (hkernel (θ - θ')) (hLnonneg θ')
    rw [heq θ]
    have hnorm : c * A =
        (c * (∫ θ' : ℝ, fermionicTBAOccupation ε θ')) / (2 * Real.pi) := by
      dsimp [A, fermionicTBAFreeEnergy]
      field_simp
    rw [hnorm]
    exact sub_le_sub_left (div_le_div_of_nonneg_right hconvLower hpi.le) _
  have hrexcl_lt_one : geometricCDDTBAExclusionRadius q C < 1 := by
    unfold geometricCDDTBAExclusionRadius
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos)
        (by positivity : 0 < 1 + Real.exp 1)) hc
  have hr1 : r ≤ 1 := hr.trans hrexcl_lt_one.le
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg ((one_le_div₀ hr0).mpr hr1)
  have hLbound : Real.pi * (1 + Real.exp 1) / c ≤ L := by
    have hlog := Real.strictMonoOn_log.monotoneOn hr0
      (geometricCDDTBAExclusionRadius_pos q C) hr
    rw [geometricCDDTBAExclusionRadius, Real.log_exp] at hlog
    change Real.log r ≤ -Real.pi * (1 + Real.exp 1) / c at hlog
    dsimp [L]
    rw [Real.log_div (by norm_num) hr0.ne', Real.log_one]
    calc
      Real.pi * (1 + Real.exp 1) / c =
          -(-Real.pi * (1 + Real.exp 1) / c) := by ring
      _ ≤ -Real.log r := neg_le_neg hlog
      _ = 0 - Real.log r := by ring
  have hrapidity : ∀ θ ∈ Set.Icc (-L) L, r * Real.cosh θ ≤ 1 := by
    intro θ hθ
    have hexpθ : Real.exp θ ≤ 1 / r := by
      rw [← Real.exp_log (div_pos (by norm_num) hr0)]
      exact Real.exp_le_exp.mpr hθ.2
    have hexpnegθ : Real.exp (-θ) ≤ 1 / r := by
      rw [← Real.exp_log (div_pos (by norm_num) hr0)]
      exact Real.exp_le_exp.mpr (by linarith [hθ.1])
    rw [Real.cosh_eq]
    have hrnonneg := hr0.le
    have h1 := mul_le_mul_of_nonneg_left hexpθ hrnonneg
    have h2 := mul_le_mul_of_nonneg_left hexpnegθ hrnonneg
    field_simp at h1 h2 ⊢
    nlinarith
  have hoccLower : ∀ θ ∈ Set.Icc (-L) L,
      Real.log (1 + Real.exp (c * A - 1)) ≤ fermionicTBAOccupation ε θ := by
    intro θ hθ
    have heps := hepsilon θ
    have hrap := hrapidity θ hθ
    have harg : c * A - 1 ≤ -ε θ := by linarith
    unfold fermionicTBAOccupation
    apply Real.strictMonoOn_log.monotoneOn
    · show 0 < 1 + Real.exp (c * A - 1)
      linarith [Real.exp_pos (c * A - 1)]
    · show 0 < 1 + Real.exp (-ε θ)
      linarith [Real.exp_pos (-ε θ)]
    · simpa [add_comm] using add_le_add_left (Real.exp_le_exp.mpr harg) 1
  have hintervalInt :
      Real.log (1 + Real.exp (c * A - 1)) * (2 * L) ≤
        ∫ θ in Set.Icc (-L) L, fermionicTBAOccupation ε θ := by
    have hmeasure : volume.real (Set.Icc (-L) L) = 2 * L := by
      rw [Real.volume_real_Icc_of_le (by linarith)]
      ring
    rw [← hmeasure]
    exact setIntegral_ge_of_const_le_real measurableSet_Icc
      measure_Icc_lt_top.ne hoccLower hLint.integrableOn
  have hfullInt :
      Real.log (1 + Real.exp (c * A - 1)) * (2 * L) ≤
        ∫ θ : ℝ, fermionicTBAOccupation ε θ :=
    hintervalInt.trans (setIntegral_le_integral hLint
      (Filter.Eventually.of_forall hLnonneg))
  have hsoft : c * A / (1 + Real.exp 1) <
      Real.log (1 + Real.exp (c * A - 1)) :=
    div_one_add_exp_one_lt_log_one_add_exp_sub_one (c * A)
  have hLA : A < L / Real.pi *
      Real.log (1 + Real.exp (c * A - 1)) := by
    have hcoeff : (1 + Real.exp 1) / c ≤ L / Real.pi := by
      rw [div_le_div_iff₀ hc Real.pi_pos]
      field_simp [hc.ne'] at hLbound ⊢
      nlinarith
    have hstep : A < (1 + Real.exp 1) / c *
        Real.log (1 + Real.exp (c * A - 1)) := by
      have hsoft' := mul_lt_mul_of_pos_left hsoft
        (div_pos (by positivity : 0 < 1 + Real.exp 1) hc)
      field_simp [hc.ne'] at hsoft' ⊢
      nlinarith
    exact hstep.trans_le (mul_le_mul_of_nonneg_right hcoeff
      (Real.log_nonneg (by linarith [Real.exp_pos (c * A - 1)])))
  have hAfull : L / Real.pi *
      Real.log (1 + Real.exp (c * A - 1)) ≤ A := by
    dsimp [A, fermionicTBAFreeEnergy]
    rw [le_div_iff₀ hpi]
    calc
      (L / Real.pi * Real.log (1 + Real.exp (c * A - 1))) *
          (2 * Real.pi) =
          Real.log (1 + Real.exp (c * A - 1)) * (2 * L) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ ∫ θ : ℝ, fermionicTBAOccupation ε θ := hfullInt
  exact (not_lt_of_ge hAfull) hLA

/-- Bounded continuous correction profiles for the primary large-radius branch. -/
abbrev TBACorrectionProfile := BoundedContinuousFunction ℝ ℝ

/-- Occupation generated by a bounded correction to the free driving term. -/
def primaryTBAOccupation (r : ℝ) (h : TBACorrectionProfile) (θ : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-r * Real.cosh θ - h θ))

theorem continuous_primaryTBAOccupation (r : ℝ) (h : TBACorrectionProfile) :
    Continuous (primaryTBAOccupation r h) := by
  unfold primaryTBAOccupation
  have hrconst : Continuous (fun _ : ℝ => -r) := continuous_const
  have hinner : Continuous (fun θ : ℝ => -r * Real.cosh θ - h θ) :=
    (hrconst.mul Real.continuous_cosh).sub h.continuous
  have hone : Continuous (fun _ : ℝ => (1 : ℝ)) := continuous_const
  have hsum : Continuous (fun θ : ℝ => 1 + Real.exp (-r * Real.cosh θ - h θ)) :=
    hone.add (Real.continuous_exp.comp hinner)
  exact hsum.log (fun θ => ne_of_gt
    (add_pos_of_pos_of_nonneg zero_lt_one (Real.exp_pos _).le))

theorem primaryTBAOccupation_pos (r : ℝ) (h : TBACorrectionProfile) (θ : ℝ) :
    0 < primaryTBAOccupation r h θ := by
  unfold primaryTBAOccupation
  exact Real.log_pos (by linarith [Real.exp_pos (-r * Real.cosh θ - h θ)])

theorem primaryTBAOccupation_le
    {r : ℝ} {h : TBACorrectionProfile} (hh : ‖h‖ ≤ 1) (θ : ℝ) :
    primaryTBAOccupation r h θ ≤ Real.exp (1 - r * Real.cosh θ) := by
  have hpoint : |h θ| ≤ 1 := by
    simpa [Real.norm_eq_abs] using (h.norm_coe_le_norm θ).trans hh
  unfold primaryTBAOccupation
  calc
    Real.log (1 + Real.exp (-r * Real.cosh θ - h θ)) ≤
        Real.exp (-r * Real.cosh θ - h θ) := by
      have hlog := Real.log_le_sub_one_of_pos
        (by linarith [Real.exp_pos (-r * Real.cosh θ - h θ)] :
          0 < 1 + Real.exp (-r * Real.cosh θ - h θ))
      linarith
    _ ≤ Real.exp (1 - r * Real.cosh θ) := by
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hpoint).1])

theorem primaryTBAOccupation_le_norm (r : ℝ) (h : TBACorrectionProfile) (θ : ℝ) :
    primaryTBAOccupation r h θ ≤ Real.exp (‖h‖ - r * Real.cosh θ) := by
  have hpoint : |h θ| ≤ ‖h‖ := by
    simpa [Real.norm_eq_abs] using h.norm_coe_le_norm θ
  unfold primaryTBAOccupation
  calc
    Real.log (1 + Real.exp (-r * Real.cosh θ - h θ)) ≤
        Real.exp (-r * Real.cosh θ - h θ) := by
      have hlog := Real.log_le_sub_one_of_pos
        (by linarith [Real.exp_pos (-r * Real.cosh θ - h θ)] :
          0 < 1 + Real.exp (-r * Real.cosh θ - h θ))
      linarith
    _ ≤ Real.exp (‖h‖ - r * Real.cosh θ) := by
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hpoint).1])

theorem integrable_primaryTBAOccupation_general
    {r : ℝ} (hr : 0 < r) (h : TBACorrectionProfile) :
    Integrable (primaryTBAOccupation r h) := by
  have hmajor : Integrable
      (fun θ : ℝ => Real.exp ‖h‖ * Real.exp (-r * Real.cosh θ)) :=
    (integrable_exp_neg_mul_cosh hr).const_mul (Real.exp ‖h‖)
  apply hmajor.mono' (continuous_primaryTBAOccupation r h).aestronglyMeasurable
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_of_pos (primaryTBAOccupation_pos r h θ)]
  calc
    primaryTBAOccupation r h θ ≤ Real.exp (‖h‖ - r * Real.cosh θ) :=
      primaryTBAOccupation_le_norm r h θ
    _ = Real.exp ‖h‖ * Real.exp (-r * Real.cosh θ) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem integrable_primaryTBAOccupation
    {r : ℝ} (hr : 0 < r) {h : TBACorrectionProfile} (hh : ‖h‖ ≤ 1) :
    Integrable (primaryTBAOccupation r h) := by
  have hmajor : Integrable (fun θ : ℝ => Real.exp 1 * Real.exp (-r * Real.cosh θ)) :=
    (integrable_exp_neg_mul_cosh hr).const_mul (Real.exp 1)
  apply hmajor.mono' (continuous_primaryTBAOccupation r h).aestronglyMeasurable
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_of_pos (primaryTBAOccupation_pos r h θ)]
  calc
    primaryTBAOccupation r h θ ≤ Real.exp (1 - r * Real.cosh θ) :=
      primaryTBAOccupation_le hh θ
    _ = Real.exp 1 * Real.exp (-r * Real.cosh θ) := by rw [← Real.exp_add]; congr 1; ring

theorem primaryTBAOccupation_lipschitz
    {r : ℝ} {h g : TBACorrectionProfile} (hh : ‖h‖ ≤ 1) (hg : ‖g‖ ≤ 1) (θ : ℝ) :
    |primaryTBAOccupation r h θ - primaryTBAOccupation r g θ| ≤
      Real.exp (1 - r * Real.cosh θ) * |h θ - g θ| := by
  let f : ℝ → ℝ := fun z => Real.log (1 + Real.exp (-r * Real.cosh θ - z))
  have hderiv (z : ℝ) : HasDerivAt f
      (-Real.exp (-r * Real.cosh θ - z) /
        (1 + Real.exp (-r * Real.cosh θ - z))) z := by
    have hinner : HasDerivAt (fun z : ℝ => -r * Real.cosh θ - z) (-1) z := by
      simpa [sub_eq_add_neg] using (hasDerivAt_neg z).const_add (-r * Real.cosh θ)
    have hlog := ((hinner.exp).const_add 1).log
      (by linarith [Real.exp_pos (-r * Real.cosh θ - z)] :
        1 + Real.exp (-r * Real.cosh θ - z) ≠ 0)
    simpa [f, neg_div] using hlog
  have hbound (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
      ‖deriv f z‖ ≤ Real.exp (1 - r * Real.cosh θ) := by
    rw [(hderiv z).deriv]
    have hden : 0 < 1 + Real.exp (-r * Real.cosh θ - z) := by positivity
    have hfrac : Real.exp (-r * Real.cosh θ - z) /
        (1 + Real.exp (-r * Real.cosh θ - z)) ≤
        Real.exp (-r * Real.cosh θ - z) := by
      rw [div_le_iff₀ hden]
      nlinarith [Real.exp_pos (-r * Real.cosh θ - z)]
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos hden]
    exact hfrac.trans (Real.exp_le_exp.mpr (by linarith [hz.1]))
  have hhpoint : h θ ∈ Set.Icc (-1 : ℝ) 1 := by
    have := (h.norm_coe_le_norm θ).trans hh
    simpa [Real.norm_eq_abs, abs_le] using this
  have hgpoint : g θ ∈ Set.Icc (-1 : ℝ) 1 := by
    have := (g.norm_coe_le_norm θ).trans hg
    simpa [Real.norm_eq_abs, abs_le] using this
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (-1 : ℝ) 1) (fun z _ => (hderiv z).differentiableAt)
    hbound (convex_Icc _ _) hgpoint hhpoint
  simpa [f, primaryTBAOccupation, Real.norm_eq_abs] using hmv

theorem geometricCDDTBAKernel_nonneg
    {q C : ℝ} (hq0 : 0 < q) (_hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    0 ≤ geometricCDDTBAKernel q C θ := by
  exact tsum_nonneg fun k => geometricCDDTBAKernelTerm_nonneg hq0.le (zero_lt_one.trans hC) θ k

/-- Uniform kernel height used in the large-radius contraction estimate. -/
def geometricCDDTBAKernelBound (q C : ℝ) : ℝ :=
  8 * Real.sqrt (1 + C ^ 2) / (C * (1 - q))

theorem geometricCDDTBAKernelBound_pos
    {q C : ℝ} (_hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    0 < geometricCDDTBAKernelBound q C := by
  unfold geometricCDDTBAKernelBound
  positivity

theorem geometricCDDTBAKernel_norm_le_bound
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    ‖geometricCDDTBAKernel q C θ‖ ≤ geometricCDDTBAKernelBound q C := by
  rw [Real.norm_eq_abs, abs_of_nonneg (geometricCDDTBAKernel_nonneg hq0 hq1 hC θ)]
  exact geometricCDDTBAKernel_upper hq0 hq1 hC θ

/-- Literal normalized nonlinear TBA integral operator. -/
noncomputable def primaryTBAIntegralOperator
    (q C r : ℝ) (h : TBACorrectionProfile) (θ : ℝ) : ℝ :=
  -( ∫ θ' : ℝ, geometricCDDTBAKernel q C (θ - θ') *
      primaryTBAOccupation r h θ') / (2 * Real.pi)

theorem integrable_kernel_mul_primaryTBAOccupation
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    (h : TBACorrectionProfile) (θ : ℝ) :
    Integrable (fun θ' : ℝ => geometricCDDTBAKernel q C (θ - θ') *
      primaryTBAOccupation r h θ') := by
  have hocc := integrable_primaryTBAOccupation_general hr h
  have hmajor : Integrable
      (fun θ' : ℝ => geometricCDDTBAKernelBound q C * primaryTBAOccupation r h θ') :=
    hocc.const_mul (geometricCDDTBAKernelBound q C)
  apply hmajor.mono'
  · have hkcont : Continuous
        (fun θ' : ℝ => geometricCDDTBAKernel q C (θ - θ')) :=
      (continuous_geometricCDDTBAKernel hq0.le hq1 (zero_lt_one.trans hC)).comp
        (continuous_const.sub continuous_id)
    exact (hkcont.mul (continuous_primaryTBAOccupation r h)).aestronglyMeasurable
  · filter_upwards with θ'
    simp only [norm_mul, Real.norm_eq_abs,
      abs_of_pos (primaryTBAOccupation_pos r h θ')]
    exact mul_le_mul_of_nonneg_right
      (geometricCDDTBAKernel_norm_le_bound hq0 hq1 hC (θ - θ'))
      (primaryTBAOccupation_pos r h θ').le

theorem continuous_primaryTBAIntegralOperator
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    (h : TBACorrectionProfile) :
    Continuous (primaryTBAIntegralOperator q C r h) := by
  have hbdd : BddAbove
      (Set.range fun θ : ℝ => ‖geometricCDDTBAKernel q C θ‖) := by
    refine ⟨geometricCDDTBAKernelBound q C, ?_⟩
    rintro _ ⟨θ, rfl⟩
    exact geometricCDDTBAKernel_norm_le_bound hq0 hq1 hC θ
  have hconv : Continuous (MeasureTheory.convolution
      (geometricCDDTBAKernel q C) (primaryTBAOccupation r h)
      (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hbdd.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℝ ℝ)
      (continuous_geometricCDDTBAKernel hq0.le hq1 (zero_lt_one.trans hC))
      (integrable_primaryTBAOccupation_general hr h)
  have heq : primaryTBAIntegralOperator q C r h = fun θ =>
      -(MeasureTheory.convolution (geometricCDDTBAKernel q C)
        (primaryTBAOccupation r h) (ContinuousLinearMap.mul ℝ ℝ) volume θ) /
          (2 * Real.pi) := by
    funext θ
    rw [MeasureTheory.convolution_mul_swap]
    rfl
  rw [heq]
  exact hconv.neg.div_const _

theorem norm_primaryTBAIntegralOperator_le
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    (h : TBACorrectionProfile) (θ : ℝ) :
    ‖primaryTBAIntegralOperator q C r h θ‖ ≤
      geometricCDDTBAKernelBound q C *
        (∫ θ' : ℝ, primaryTBAOccupation r h θ') / (2 * Real.pi) := by
  have hocc := integrable_primaryTBAOccupation_general hr h
  have hmajor : Integrable
      (fun θ' : ℝ => geometricCDDTBAKernelBound q C * primaryTBAOccupation r h θ') :=
    hocc.const_mul (geometricCDDTBAKernelBound q C)
  have hint : ‖∫ θ' : ℝ, geometricCDDTBAKernel q C (θ - θ') *
        primaryTBAOccupation r h θ'‖ ≤
      ∫ θ' : ℝ, geometricCDDTBAKernelBound q C * primaryTBAOccupation r h θ' := by
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards with θ'
    simp only [norm_mul, Real.norm_eq_abs,
      abs_of_pos (primaryTBAOccupation_pos r h θ')]
    exact mul_le_mul_of_nonneg_right
      (geometricCDDTBAKernel_norm_le_bound hq0 hq1 hC (θ - θ'))
      (primaryTBAOccupation_pos r h θ').le
  have hint' : ‖∫ θ' : ℝ, geometricCDDTBAKernel q C (θ - θ') *
        primaryTBAOccupation r h θ'‖ ≤
      geometricCDDTBAKernelBound q C *
        (∫ θ' : ℝ, primaryTBAOccupation r h θ') := by
    calc
      _ ≤ ∫ θ' : ℝ, geometricCDDTBAKernelBound q C *
          primaryTBAOccupation r h θ' := hint
      _ = _ := by rw [integral_const_mul]
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  unfold primaryTBAIntegralOperator
  simp only [norm_div, norm_neg, Real.norm_eq_abs, abs_of_pos hpi]
  exact div_le_div_of_nonneg_right
    (by simpa [Real.norm_eq_abs] using hint') hpi.le

/-- Bounded-continuous realization of the nonlinear integral operator. -/
noncomputable def primaryTBAMap
    (q C r : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r) :
    TBACorrectionProfile → TBACorrectionProfile := fun h =>
  BoundedContinuousFunction.ofNormedAddCommGroup
    (primaryTBAIntegralOperator q C r h)
    (continuous_primaryTBAIntegralOperator hq0 hq1 hC hr h)
    (geometricCDDTBAKernelBound q C *
      (∫ θ : ℝ, primaryTBAOccupation r h θ) / (2 * Real.pi))
    (norm_primaryTBAIntegralOperator_le hq0 hq1 hC hr h)

@[simp] theorem primaryTBAMap_apply
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    (h : TBACorrectionProfile) (θ : ℝ) :
    primaryTBAMap q C r hq0 hq1 hC hr h θ = primaryTBAIntegralOperator q C r h θ := rfl

/-- Explicit contraction constant on the closed unit ball. -/
noncomputable def primaryTBAContractionFactor (q C r : ℝ) : ℝ :=
  geometricCDDTBAKernelBound q C *
    (Real.exp 1 * (∫ θ : ℝ, Real.exp (-r * Real.cosh θ))) / (2 * Real.pi)

theorem primaryTBAContractionFactor_nonneg
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    0 ≤ primaryTBAContractionFactor q C r := by
  unfold primaryTBAContractionFactor
  exact div_nonneg
    (mul_nonneg (geometricCDDTBAKernelBound_pos hq0 hq1 hC).le
      (mul_nonneg (Real.exp_pos 1).le
        (integral_nonneg fun θ => (Real.exp_pos (-r * Real.cosh θ)).le)))
    (mul_pos (by norm_num) Real.pi_pos).le

theorem integral_primaryTBAOccupation_le
    {r : ℝ} (hr : 0 < r) {h : TBACorrectionProfile} (hh : ‖h‖ ≤ 1) :
    (∫ θ : ℝ, primaryTBAOccupation r h θ) ≤
      Real.exp 1 * (∫ θ : ℝ, Real.exp (-r * Real.cosh θ)) := by
  have hocc := integrable_primaryTBAOccupation hr hh
  have hmajor : Integrable (fun θ : ℝ => Real.exp 1 * Real.exp (-r * Real.cosh θ)) :=
    (integrable_exp_neg_mul_cosh hr).const_mul (Real.exp 1)
  rw [← integral_const_mul]
  exact integral_mono hocc hmajor fun θ => by
    calc
      primaryTBAOccupation r h θ ≤ Real.exp (1 - r * Real.cosh θ) :=
        primaryTBAOccupation_le hh θ
      _ = Real.exp 1 * Real.exp (-r * Real.cosh θ) := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem norm_primaryTBAMap_le_factor
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    {h : TBACorrectionProfile} (hh : ‖h‖ ≤ 1) :
    ‖primaryTBAMap q C r hq0 hq1 hC hr h‖ ≤ primaryTBAContractionFactor q C r := by
  rw [BoundedContinuousFunction.norm_le
    (primaryTBAContractionFactor_nonneg hq0 hq1 hC)]
  intro θ
  rw [primaryTBAMap_apply]
  calc
    ‖primaryTBAIntegralOperator q C r h θ‖ ≤
        geometricCDDTBAKernelBound q C *
          (∫ θ' : ℝ, primaryTBAOccupation r h θ') / (2 * Real.pi) :=
      norm_primaryTBAIntegralOperator_le hq0 hq1 hC hr h θ
    _ ≤ geometricCDDTBAKernelBound q C *
        (Real.exp 1 * (∫ θ' : ℝ, Real.exp (-r * Real.cosh θ'))) /
          (2 * Real.pi) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (integral_primaryTBAOccupation_le hr hh)
          (geometricCDDTBAKernelBound_pos hq0 hq1 hC).le)
        (mul_pos (by norm_num) Real.pi_pos).le
    _ = primaryTBAContractionFactor q C r := rfl

theorem tendsto_primaryTBAContractionFactor_atTop
    {q C : ℝ} : Tendsto (primaryTBAContractionFactor q C) atTop (𝓝 0) := by
  have ht := tendsto_integral_exp_neg_mul_cosh_atTop.const_mul
    (geometricCDDTBAKernelBound q C * Real.exp 1 / (2 * Real.pi))
  convert ht using 1
  · funext r
    unfold primaryTBAContractionFactor
    ring
  · simp

theorem norm_primaryTBAIntegralOperator_sub_le
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    {h g : TBACorrectionProfile} (hh : ‖h‖ ≤ 1) (hg : ‖g‖ ≤ 1) (θ : ℝ) :
    ‖primaryTBAIntegralOperator q C r h θ - primaryTBAIntegralOperator q C r g θ‖ ≤
      primaryTBAContractionFactor q C r * ‖h - g‖ := by
  let Fh : ℝ → ℝ := fun θ' => geometricCDDTBAKernel q C (θ - θ') *
    primaryTBAOccupation r h θ'
  let Fg : ℝ → ℝ := fun θ' => geometricCDDTBAKernel q C (θ - θ') *
    primaryTBAOccupation r g θ'
  let D : ℝ → ℝ := fun θ' => geometricCDDTBAKernel q C (θ - θ') *
    (primaryTBAOccupation r h θ' - primaryTBAOccupation r g θ')
  have hFh : Integrable Fh := integrable_kernel_mul_primaryTBAOccupation hq0 hq1 hC hr h θ
  have hFg : Integrable Fg := integrable_kernel_mul_primaryTBAOccupation hq0 hq1 hC hr g θ
  have hDint : (∫ θ' : ℝ, D θ') = (∫ θ' : ℝ, Fh θ') - (∫ θ' : ℝ, Fg θ') := by
    simpa [D, Fh, Fg, mul_sub] using integral_sub hFh hFg
  have hopsub : primaryTBAIntegralOperator q C r h θ -
      primaryTBAIntegralOperator q C r g θ = -(∫ θ' : ℝ, D θ') / (2 * Real.pi) := by
    unfold primaryTBAIntegralOperator
    rw [hDint]
    dsimp [Fh, Fg]
    ring
  have hweight : Integrable (fun θ' : ℝ =>
      geometricCDDTBAKernelBound q C *
        (Real.exp (1 - r * Real.cosh θ') * ‖h - g‖)) := by
    have hbase := (integrable_exp_neg_mul_cosh hr).const_mul
      (geometricCDDTBAKernelBound q C * Real.exp 1 * ‖h - g‖)
    convert hbase using 1
    funext θ'
    rw [show Real.exp (1 - r * Real.cosh θ') =
      Real.exp 1 * Real.exp (-r * Real.cosh θ') by
        rw [← Real.exp_add]
        congr 1
        ring]
    ring
  have hpoint : ∀ θ' : ℝ, ‖D θ'‖ ≤
      geometricCDDTBAKernelBound q C *
        (Real.exp (1 - r * Real.cosh θ') * ‖h - g‖) := by
    intro θ'
    have hprofile : |h θ' - g θ'| ≤ ‖h - g‖ := by
      simpa [Real.norm_eq_abs] using (h - g).norm_coe_le_norm θ'
    dsimp [D]
    rw [abs_mul]
    calc
      |geometricCDDTBAKernel q C (θ - θ')| *
          |primaryTBAOccupation r h θ' - primaryTBAOccupation r g θ'| ≤
          geometricCDDTBAKernelBound q C *
            |primaryTBAOccupation r h θ' - primaryTBAOccupation r g θ'| := by
        exact mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using
            geometricCDDTBAKernel_norm_le_bound hq0 hq1 hC (θ - θ'))
          (abs_nonneg _)
      _ ≤ geometricCDDTBAKernelBound q C *
          (Real.exp (1 - r * Real.cosh θ') * |h θ' - g θ'|) := by
        exact mul_le_mul_of_nonneg_left (primaryTBAOccupation_lipschitz hh hg θ')
          (geometricCDDTBAKernelBound_pos hq0 hq1 hC).le
      _ ≤ geometricCDDTBAKernelBound q C *
          (Real.exp (1 - r * Real.cosh θ') * ‖h - g‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hprofile (Real.exp_pos _).le)
          (geometricCDDTBAKernelBound_pos hq0 hq1 hC).le
  have hint : ‖∫ θ' : ℝ, D θ'‖ ≤
      ∫ θ' : ℝ, geometricCDDTBAKernelBound q C *
        (Real.exp (1 - r * Real.cosh θ') * ‖h - g‖) :=
    norm_integral_le_of_norm_le hweight (Filter.Eventually.of_forall hpoint)
  have hint' : ‖∫ θ' : ℝ, D θ'‖ ≤
      geometricCDDTBAKernelBound q C *
        (Real.exp 1 * (∫ θ' : ℝ, Real.exp (-r * Real.cosh θ'))) * ‖h - g‖ := by
    calc
      _ ≤ ∫ θ' : ℝ, geometricCDDTBAKernelBound q C *
          (Real.exp (1 - r * Real.cosh θ') * ‖h - g‖) := hint
      _ = _ := by
        calc
          (∫ θ' : ℝ, geometricCDDTBAKernelBound q C *
              (Real.exp (1 - r * Real.cosh θ') * ‖h - g‖)) =
              ∫ θ' : ℝ, (geometricCDDTBAKernelBound q C * ‖h - g‖ * Real.exp 1) *
                Real.exp (-r * Real.cosh θ') := by
            congr 1
            funext θ'
            rw [show Real.exp (1 - r * Real.cosh θ') =
              Real.exp 1 * Real.exp (-r * Real.cosh θ') by
                rw [← Real.exp_add]
                congr 1
                ring]
            ring
          _ = (geometricCDDTBAKernelBound q C * ‖h - g‖ * Real.exp 1) *
              (∫ θ' : ℝ, Real.exp (-r * Real.cosh θ')) := by
            rw [integral_const_mul]
          _ = _ := by ring
  rw [hopsub, norm_div, norm_neg]
  have hpi : 0 < ‖(2 * Real.pi : ℝ)‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  calc
    ‖∫ θ' : ℝ, D θ'‖ / ‖(2 * Real.pi : ℝ)‖ ≤
        (geometricCDDTBAKernelBound q C *
          (Real.exp 1 * (∫ θ' : ℝ, Real.exp (-r * Real.cosh θ'))) * ‖h - g‖) /
            ‖(2 * Real.pi : ℝ)‖ := div_le_div_of_nonneg_right hint' hpi.le
    _ = primaryTBAContractionFactor q C r * ‖h - g‖ := by
      unfold primaryTBAContractionFactor
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
      ring

theorem norm_primaryTBAMap_sub_le
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    {h g : TBACorrectionProfile} (hh : ‖h‖ ≤ 1) (hg : ‖g‖ ≤ 1) :
    ‖primaryTBAMap q C r hq0 hq1 hC hr h - primaryTBAMap q C r hq0 hq1 hC hr g‖ ≤
      primaryTBAContractionFactor q C r * ‖h - g‖ := by
  rw [BoundedContinuousFunction.norm_le
    (mul_nonneg (primaryTBAContractionFactor_nonneg hq0 hq1 hC) (norm_nonneg _))]
  intro θ
  simpa [Real.norm_eq_abs] using
    norm_primaryTBAIntegralOperator_sub_le hq0 hq1 hC hr hh hg θ

theorem exists_unique_primaryTBAMap_fixedPoint
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    (hfactor : primaryTBAContractionFactor q C r < 1) :
    ∃! h : TBACorrectionProfile,
      ‖h‖ ≤ 1 ∧ primaryTBAMap q C r hq0 hq1 hC hr h = h := by
  let s : Set TBACorrectionProfile := Metric.closedBall 0 1
  let T : TBACorrectionProfile → TBACorrectionProfile :=
    primaryTBAMap q C r hq0 hq1 hC hr
  have hmaps : Set.MapsTo T s s := by
    intro h hh
    have hhnorm : ‖h‖ ≤ 1 := by
      simpa [s, Metric.mem_closedBall, dist_zero_right] using hh
    have hT := norm_primaryTBAMap_le_factor hq0 hq1 hC hr hhnorm
    have hTone : ‖T h‖ ≤ 1 := hT.trans hfactor.le
    simpa [s, Metric.mem_closedBall, dist_zero_right] using hTone
  let K : NNReal := ⟨primaryTBAContractionFactor q C r,
    primaryTBAContractionFactor_nonneg hq0 hq1 hC⟩
  have hcontract : ContractingWith K (hmaps.restrict T s s) := by
    refine ⟨(by exact_mod_cast hfactor), LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have hxnorm : ‖(x.1 : TBACorrectionProfile)‖ ≤ 1 := by
      have hxmem := x.2
      change (x.1 : TBACorrectionProfile) ∈ Metric.closedBall 0 1 at hxmem
      rw [Metric.mem_closedBall] at hxmem
      simpa [dist_zero_right] using hxmem
    have hynorm : ‖(y.1 : TBACorrectionProfile)‖ ≤ 1 := by
      have hymem := y.2
      change (y.1 : TBACorrectionProfile) ∈ Metric.closedBall 0 1 at hymem
      rw [Metric.mem_closedBall] at hymem
      simpa [dist_zero_right] using hymem
    have hxy := norm_primaryTBAMap_sub_le hq0 hq1 hC hr
      (h := x.1) (g := y.1) hxnorm hynorm
    change dist (T x.1) (T y.1) ≤ (K : ℝ) * dist x.1 y.1
    have hKcoe : (K : ℝ) = primaryTBAContractionFactor q C r := rfl
    rw [hKcoe]
    simpa [T, dist_eq_norm] using hxy
  obtain ⟨h, hh, hfix, -, -⟩ := hcontract.exists_fixedPoint'
    (Metric.isClosed_closedBall.isComplete : IsComplete s) hmaps
    (x := (0 : TBACorrectionProfile)) (by simp) (edist_ne_top _ _)
  have hhnorm : ‖h‖ ≤ 1 := by
    simpa [s, Metric.mem_closedBall, dist_zero_right] using hh
  have hfix' : primaryTBAMap q C r hq0 hq1 hC hr h = h := by
    change T h = h at hfix
    exact hfix
  refine ⟨h, ⟨hhnorm, hfix'⟩, ?_⟩
  intro g hg
  have hsub := norm_primaryTBAMap_sub_le hq0 hq1 hC hr hhnorm hg.1
  rw [hfix', hg.2] at hsub
  have hfac0 : 0 ≤ primaryTBAContractionFactor q C r :=
    primaryTBAContractionFactor_nonneg (r := r) hq0 hq1 hC
  have hnorm0 : ‖h - g‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖h - g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  have hsubzero : h - g = 0 := norm_eq_zero.mp hnorm0
  have heq : h = g := sub_eq_zero.mp hsubzero
  exact heq.symm

/-- Pseudoenergy represented by a bounded correction to the free driving term. -/
def primaryTBAPseudoenergy (r : ℝ) (h : TBACorrectionProfile) (θ : ℝ) : ℝ :=
  r * Real.cosh θ + h θ

theorem fermionicTBAOccupation_primaryTBAPseudoenergy
    (r : ℝ) (h : TBACorrectionProfile) :
    fermionicTBAOccupation (primaryTBAPseudoenergy r h) = primaryTBAOccupation r h := by
  funext θ
  unfold fermionicTBAOccupation primaryTBAPseudoenergy primaryTBAOccupation
  congr 2
  ring

/-- Primary real solution: finite-free-energy TBA solution whose correction lies in unit ball. -/
def IsPrimaryGeometricCDDTBASolution (q C r : ℝ) (h : TBACorrectionProfile) : Prop :=
  ‖h‖ ≤ 1 ∧ IsRealFiniteFreeEnergyTBASolution
    (geometricCDDTBAKernel q C) r (primaryTBAPseudoenergy r h)

theorem fixedPoint_isPrimaryGeometricCDDTBASolution
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    {h : TBACorrectionProfile} (hh : ‖h‖ ≤ 1)
    (hfix : primaryTBAMap q C r hq0 hq1 hC hr h = h) :
    IsPrimaryGeometricCDDTBASolution q C r h := by
  refine ⟨hh, ?_⟩
  have hoccEq := fermionicTBAOccupation_primaryTBAPseudoenergy r h
  have hoccInt : Integrable
      (fermionicTBAOccupation (primaryTBAPseudoenergy r h)) := by
    rw [hoccEq]
    exact integrable_primaryTBAOccupation hr hh
  refine ⟨?_, hoccInt, ?_, ?_⟩
  · exact ((continuous_const.mul Real.continuous_cosh).add h.continuous).measurable
  · intro θ
    rw [hoccEq]
    exact integrable_kernel_mul_primaryTBAOccupation hq0 hq1 hC hr h θ
  · intro θ
    have hpoint := congrArg (fun u : TBACorrectionProfile => u θ) hfix
    rw [primaryTBAMap_apply] at hpoint
    unfold primaryTBAIntegralOperator at hpoint
    rw [neg_div] at hpoint
    rw [hoccEq]
    unfold primaryTBAPseudoenergy
    rw [← hpoint]
    ring

theorem isPrimaryGeometricCDDTBASolution_isFixedPoint
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    {h : TBACorrectionProfile} (hsol : IsPrimaryGeometricCDDTBASolution q C r h) :
    primaryTBAMap q C r hq0 hq1 hC hr h = h := by
  apply BoundedContinuousFunction.ext
  intro θ
  rw [primaryTBAMap_apply]
  unfold primaryTBAIntegralOperator
  have heq := hsol.2.2.2.2 θ
  rw [fermionicTBAOccupation_primaryTBAPseudoenergy] at heq
  unfold primaryTBAPseudoenergy at heq
  rw [neg_div]
  linarith

theorem exists_unique_primaryGeometricCDDTBASolution
    {q C r : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (hr : 0 < r)
    (hfactor : primaryTBAContractionFactor q C r < 1) :
    ∃! h : TBACorrectionProfile, IsPrimaryGeometricCDDTBASolution q C r h := by
  obtain ⟨h, hh, huniq⟩ := exists_unique_primaryTBAMap_fixedPoint hq0 hq1 hC hr hfactor
  refine ⟨h, fixedPoint_isPrimaryGeometricCDDTBASolution hq0 hq1 hC hr hh.1 hh.2, ?_⟩
  intro g hg
  exact huniq g ⟨hg.1, isPrimaryGeometricCDDTBASolution_isFixedPoint hq0 hq1 hC hr hg⟩

/-- Constructive large-radius primary branch, with literal normalized TBA equation and uniqueness. -/
theorem exists_largeRadius_unique_primaryGeometricCDDTBASolution
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      ∃! h : TBACorrectionProfile, IsPrimaryGeometricCDDTBASolution q C r h := by
  have hevent : ∀ᶠ r : ℝ in atTop, primaryTBAContractionFactor q C r < 1 :=
    tendsto_primaryTBAContractionFactor_atTop.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨R₀, hR₀⟩ := (eventually_atTop.1 hevent)
  refine ⟨max 1 R₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_left 1 R₀).trans hr)
  have hfactor : primaryTBAContractionFactor q C r < 1 :=
    hR₀ r ((le_max_right 1 R₀).trans hr)
  exact exists_unique_primaryGeometricCDDTBASolution hq0 hq1 hC hrpos hfactor

/-- Full finite-radius separation: explicit small-radius no-go and constructive primary branch. -/
theorem geometricCDD_finiteRealTBA_obstruction_and_primaryBranch
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    (∀ r : ℝ, 0 < r → r ≤ geometricCDDTBAExclusionRadius q C →
      ¬ ∃ ε : ℝ → ℝ,
        IsRealFiniteFreeEnergyTBASolution (geometricCDDTBAKernel q C) r ε) ∧
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      ∃! h : TBACorrectionProfile, IsPrimaryGeometricCDDTBASolution q C r h := by
  constructor
  · intro r hr0 hr
    exact no_realFiniteFreeEnergyTBASolution_geometricCDD_of_smallRadius
      hq0 hq1 hC hr0 hr
  · exact exists_largeRadius_unique_primaryGeometricCDDTBASolution hq0 hq1 hC

end

end GaloisForLFunctions.HTGeometry
