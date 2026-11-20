import GaloisForLFunctions.HTGeometry.ConvexIntegralTrapezoid
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Mul

/-!
# One-sided Euler–Maclaurin comparisons

Sums of a concave function over unit cells compare with integrals in both directions, with no
derivative hypothesis:

* **Midpoint (lower bound for the sum).** If `φ` is concave on `[c − h, c + h]` then
  `∫_{c−h}^{c+h} φ ≤ 2h φ(c)`; summing over the cells centred at `a, a + 1, …, a + n − 1` gives
  `∫_{a−1/2}^{a+n−1/2} φ ≤ Σ_{k<n} φ(a + k)`.
* **Trapezoid (upper bound for the sum).** With the corpus trapezoid bound for convex integrands,
  `Σ_{k≤n} φ(a + k) ≤ ∫_a^{a+n} φ + (φ(a) + φ(a + n))/2`.
* **Monotone summands, centred cells.** For monotone `g` the centred comparison
  `|Σ_{k<n} g(a + k) − ∫_{a−1/2}^{a+n−1/2} g| ≤ (g(a + n − 1/2) − g(a − 1/2))/2` has half the
  error of the left-endpoint comparison.

Applied to `log` and `x ↦ 1/x`: `(n + 1/2) log(n + 1/2) − n + (log 2)/2 ≤ log n!`,
`log n! ≤ n log n − n + 1 + (log n)/2`, and `H_n ≤ log(2n + 1)`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### One cell -/

/-- **Midpoint inequality** for a concave integrand. -/
theorem concaveOn_integral_le_midpoint {φ : ℝ → ℝ} {c h : ℝ} (hh : 0 ≤ h)
    (hφ : ConcaveOn ℝ (Icc (c - h) (c + h)) φ) (hc : ContinuousOn φ (Icc (c - h) (c + h))) :
    ∫ x in (c - h)..(c + h), φ x ≤ 2 * h * φ c := by
  have hint1 : IntervalIntegrable φ volume (c - h) c :=
    (hc.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hint2 : IntervalIntegrable φ volume c (c + h) :=
    (hc.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (by linarith)
  have hm1 : MapsTo (fun t => c - t) (Icc 0 h) (Icc (c - h) (c + h)) :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hm2 : MapsTo (fun t => c + t) (Icc 0 h) (Icc (c - h) (c + h)) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hi1 : IntervalIntegrable (fun t => φ (c - t)) volume 0 h :=
    (hc.comp (by fun_prop) hm1).intervalIntegrable_of_Icc hh
  have hi2 : IntervalIntegrable (fun t => φ (c + t)) volume 0 h :=
    (hc.comp (by fun_prop) hm2).intervalIntegrable_of_Icc hh
  have e1 : ∫ t in (0 : ℝ)..h, φ (c - t) = ∫ x in (c - h)..c, φ x := by
    rw [intervalIntegral.integral_comp_sub_left]; simp
  have e2 : ∫ t in (0 : ℝ)..h, φ (c + t) = ∫ x in c..(c + h), φ x := by
    rw [intervalIntegral.integral_comp_add_left]; simp
  rw [← integral_add_adjacent_intervals hint1 hint2, ← e1, ← e2, ← integral_add hi1 hi2]
  have hle : ∫ t in (0 : ℝ)..h, (φ (c - t) + φ (c + t)) ≤ ∫ t in (0 : ℝ)..h, 2 * φ c := by
    apply intervalIntegral.integral_mono_on hh (hi1.add hi2) intervalIntegrable_const
    intro t ht
    have hconc := hφ.2 (hm1 ht) (hm2 ht) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hconc
    rw [show 1 / 2 * (c - t) + 1 / 2 * (c + t) = c by ring] at hconc
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  linarith

/-- **Trapezoid inequality** for a concave integrand, from the corpus convex trapezoid bound. -/
theorem concaveOn_trapezoid_le_integral {φ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hφ : ConcaveOn ℝ (Icc a b) φ) (hint : IntervalIntegrable φ volume a b) :
    (b - a) * (φ a + φ b) / 2 ≤ ∫ x in a..b, φ x := by
  have := GaloisForLFunctions.ConvexOn.integral_le_trapezoid hab hφ.neg hint.neg
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at this
  linarith

/-! ### Sums over unit cells -/

/-- **Midpoint sum bound:** the sum of a concave function dominates the integral over the
centred cells. -/
theorem integral_le_sum_of_concaveOn {φ : ℝ → ℝ} {a : ℝ} {n : ℕ}
    (hφ : ConcaveOn ℝ (Icc (a - 1 / 2) (a + n - 1 / 2)) φ)
    (hc : ContinuousOn φ (Icc (a - 1 / 2) (a + n - 1 / 2))) :
    ∫ x in (a - 1 / 2)..(a + n - 1 / 2), φ x ≤ ∑ k ∈ Finset.range n, φ (a + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a + ((n + 1 : ℕ) : ℝ) - 1 / 2 = (a + n) + 1 / 2 := by push_cast; ring
    rw [e] at hφ hc ⊢
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hsub : Icc (a - 1 / 2) (a + n - 1 / 2) ⊆ Icc (a - 1 / 2) ((a + n) + 1 / 2) :=
      Icc_subset_Icc le_rfl (by linarith)
    have hsub2 : Icc ((a + n) - 1 / 2) ((a + n) + 1 / 2) ⊆ Icc (a - 1 / 2) ((a + n) + 1 / 2) :=
      Icc_subset_Icc (by linarith) le_rfl
    have ih' := ih (hφ.subset hsub (convex_Icc _ _)) (hc.mono hsub)
    have hcell := concaveOn_integral_le_midpoint (c := a + n) (h := 1 / 2) (by norm_num)
      (hφ.subset hsub2 (convex_Icc _ _)) (hc.mono hsub2)
    have i1 : IntervalIntegrable φ volume (a - 1 / 2) (a + n - 1 / 2) :=
      (hc.mono hsub).intervalIntegrable_of_Icc (by linarith)
    have i2 : IntervalIntegrable φ volume (a + n - 1 / 2) ((a + n) + 1 / 2) :=
      (hc.mono hsub2).intervalIntegrable_of_Icc (by linarith)
    rw [Finset.sum_range_succ, ← integral_add_adjacent_intervals i1 i2]
    linarith

/-- **Trapezoid sum bound:** the sum of a concave function is at most the integral plus the
mean of the end values. -/
theorem sum_le_integral_add_of_concaveOn {φ : ℝ → ℝ} {a : ℝ} {n : ℕ}
    (hφ : ConcaveOn ℝ (Icc a (a + n)) φ) (hc : ContinuousOn φ (Icc a (a + n))) :
    ∑ k ∈ Finset.range (n + 1), φ (a + k) ≤ (∫ x in a..(a + n), φ x) + (φ a + φ (a + n)) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a + ((n + 1 : ℕ) : ℝ) = (a + n) + 1 := by push_cast; ring
    rw [e] at hφ hc ⊢
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hsub : Icc a (a + n) ⊆ Icc a ((a + n) + 1) := Icc_subset_Icc le_rfl (by linarith)
    have hsub2 : Icc (a + n) ((a + n) + 1) ⊆ Icc a ((a + n) + 1) :=
      Icc_subset_Icc (by linarith) le_rfl
    have ih' := ih (hφ.subset hsub (convex_Icc _ _)) (hc.mono hsub)
    have i1 : IntervalIntegrable φ volume a (a + n) :=
      (hc.mono hsub).intervalIntegrable_of_Icc (by linarith)
    have i2 : IntervalIntegrable φ volume (a + n) ((a + n) + 1) :=
      (hc.mono hsub2).intervalIntegrable_of_Icc (by linarith)
    have hcell := concaveOn_trapezoid_le_integral (by linarith : a + n < (a + n) + 1)
      (hφ.subset hsub2 (convex_Icc _ _)) i2
    rw [Finset.sum_range_succ, ← integral_add_adjacent_intervals i1 i2]
    have e2 : a + ((n + 1 : ℕ) : ℝ) = (a + n) + 1 := by push_cast; ring
    rw [e2]
    linarith

/-- Bounds for a monotone function on one centred cell. -/
theorem monotone_cell_bounds {g : ℝ → ℝ} {c : ℝ}
    (hg : MonotoneOn g (Icc (c - 1 / 2) (c + 1 / 2))) :
    -(g (c + 1 / 2) - g c) / 2 ≤ g c - ∫ x in (c - 1 / 2)..(c + 1 / 2), g x ∧
      g c - ∫ x in (c - 1 / 2)..(c + 1 / 2), g x ≤ (g c - g (c - 1 / 2)) / 2 := by
  have hL : MonotoneOn g (uIcc (c - 1 / 2) c) := by
    rw [uIcc_of_le (by linarith)]; exact hg.mono (Icc_subset_Icc le_rfl (by linarith))
  have hR : MonotoneOn g (uIcc c (c + 1 / 2)) := by
    rw [uIcc_of_le (by linarith)]; exact hg.mono (Icc_subset_Icc (by linarith) le_rfl)
  have i1 := hL.intervalIntegrable (μ := volume)
  have i2 := hR.intervalIntegrable (μ := volume)
  have mem : ∀ x ∈ Icc (c - 1 / 2) (c + 1 / 2), x ∈ Icc (c - 1 / 2) (c + 1 / 2) := fun x hx => hx
  have cmem : c ∈ Icc (c - 1 / 2) (c + 1 / 2) := ⟨by linarith, by linarith⟩
  have lmem : c - 1 / 2 ∈ Icc (c - 1 / 2) (c + 1 / 2) := ⟨le_rfl, by linarith⟩
  have rmem : c + 1 / 2 ∈ Icc (c - 1 / 2) (c + 1 / 2) := ⟨by linarith, le_rfl⟩
  -- left half: values between `g(c − 1/2)` and `g(c)`
  have l1 : ∫ x in (c - 1 / 2)..c, g x ≤ ∫ x in (c - 1 / 2)..c, g c :=
    intervalIntegral.integral_mono_on (by linarith) i1 intervalIntegrable_const
      (fun x hx => hg ⟨hx.1, by linarith [hx.2]⟩ cmem hx.2)
  have l2 : ∫ x in (c - 1 / 2)..c, g (c - 1 / 2) ≤ ∫ x in (c - 1 / 2)..c, g x :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const i1
      (fun x hx => hg lmem ⟨hx.1, by linarith [hx.2]⟩ hx.1)
  have r1 : ∫ x in c..(c + 1 / 2), g x ≤ ∫ x in c..(c + 1 / 2), g (c + 1 / 2) :=
    intervalIntegral.integral_mono_on (by linarith) i2 intervalIntegrable_const
      (fun x hx => hg ⟨by linarith [hx.1], hx.2⟩ rmem hx.2)
  have r2 : ∫ x in c..(c + 1 / 2), g c ≤ ∫ x in c..(c + 1 / 2), g x :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const i2
      (fun x hx => hg cmem ⟨by linarith [hx.1], hx.2⟩ hx.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at l1 l2 r1 r2
  rw [← integral_add_adjacent_intervals i1 i2]
  constructor <;> linarith

/-- **Centred monotone comparison** with half the left-endpoint error. -/
theorem abs_sum_sub_integral_centred_le {g : ℝ → ℝ} {a : ℝ} {n : ℕ}
    (hg : MonotoneOn g (Icc (a - 1 / 2) (a + n - 1 / 2))) :
    |∑ k ∈ Finset.range n, g (a + k) - ∫ x in (a - 1 / 2)..(a + n - 1 / 2), g x| ≤
      (g (a + n - 1 / 2) - g (a - 1 / 2)) / 2 := by
  rw [abs_le]
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a + ((n + 1 : ℕ) : ℝ) - 1 / 2 = (a + n) + 1 / 2 := by push_cast; ring
    rw [e] at hg ⊢
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hsub : Icc (a - 1 / 2) (a + n - 1 / 2) ⊆ Icc (a - 1 / 2) ((a + n) + 1 / 2) :=
      Icc_subset_Icc le_rfl (by linarith)
    have hsub2 : Icc ((a + n) - 1 / 2) ((a + n) + 1 / 2) ⊆ Icc (a - 1 / 2) ((a + n) + 1 / 2) :=
      Icc_subset_Icc (by linarith) le_rfl
    have ih' := ih (hg.mono hsub)
    have hcell := monotone_cell_bounds (c := a + n) (hg.mono hsub2)
    have hL : MonotoneOn g (uIcc (a - 1 / 2) (a + n - 1 / 2)) := by
      rw [uIcc_of_le (by linarith)]; exact hg.mono hsub
    have hR : MonotoneOn g (uIcc (a + n - 1 / 2) ((a + n) + 1 / 2)) := by
      rw [uIcc_of_le (by linarith)]; exact hg.mono hsub2
    rw [Finset.sum_range_succ, ← integral_add_adjacent_intervals (hL.intervalIntegrable (μ := volume))
      (hR.intervalIntegrable (μ := volume))]
    -- the half-integer end values are ordered by monotonicity
    have hmid : g (a - 1 / 2) ≤ g (a + n - 1 / 2) :=
      hg ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    have hc1 : g (a + n - 1 / 2) ≤ g (a + n) :=
      hg ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    have hc2 : g (a + n) ≤ g ((a + n) + 1 / 2) :=
      hg ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    constructor <;> linarith [hcell.1, hcell.2, ih'.1, ih'.2]

/-! ### Applications: factorials and harmonic numbers -/

theorem sum_log_eq_log_factorial (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.log (1 + k) = Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos n).ne')]
    push_cast; ring_nf

/-- **Midpoint Stirling bound:** `(n + 1/2) log(n + 1/2) − n + (log 2)/2 ≤ log n!`. -/
theorem log_factorial_ge_midpoint (n : ℕ) :
    (n + 1 / 2) * Real.log (n + 1 / 2) - n + Real.log 2 / 2 ≤ Real.log (n.factorial : ℝ) := by
  rw [← sum_log_eq_log_factorial]
  have hsub : Icc (1 - 1 / 2 : ℝ) (1 + n - 1 / 2) ⊆ Ioi 0 := fun x hx => by
    simp only [mem_Ioi]; linarith [hx.1]
  have hconc : ConcaveOn ℝ (Icc (1 - 1 / 2 : ℝ) (1 + n - 1 / 2)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn.subset hsub (convex_Icc _ _)
  have hcont : ContinuousOn Real.log (Icc (1 - 1 / 2 : ℝ) (1 + n - 1 / 2)) :=
    Real.continuousOn_log.mono (fun x hx => by simp only [mem_compl_iff, mem_singleton_iff]; linarith [(hsub hx : x ∈ Ioi 0).out])
  have h := integral_le_sum_of_concaveOn hconc hcont
  rw [integral_log] at h
  have e1 : (1 + (n : ℝ) - 1 / 2) = n + 1 / 2 := by ring
  have e2 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [e1, e2] at h
  have hl : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [hl] at h
  linarith

/-- **Trapezoid Stirling bound:** `log n! ≤ n log n − n + 1 + (log n)/2` for `n ≥ 1`. -/
theorem log_factorial_le_trapezoid {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← sum_log_eq_log_factorial]
  have hsub : Icc (1 : ℝ) (1 + m) ⊆ Ioi 0 := fun x hx => by simp only [mem_Ioi]; linarith [hx.1]
  have hconc : ConcaveOn ℝ (Icc (1 : ℝ) (1 + m)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn.subset hsub (convex_Icc _ _)
  have hcont : ContinuousOn Real.log (Icc (1 : ℝ) (1 + m)) :=
    Real.continuousOn_log.mono (fun x hx => by simp only [mem_compl_iff, mem_singleton_iff]; linarith [(hsub hx : x ∈ Ioi 0).out])
  have h := sum_le_integral_add_of_concaveOn hconc hcont
  rw [integral_log, Real.log_one] at h
  push_cast
  rw [show (m : ℝ) + 1 = 1 + m by ring]
  linarith

/-- **Midpoint bound for the harmonic numbers:** `H_n ≤ log(2n + 1)`. -/
theorem harmonic_le_log_two_mul_add_one (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 + (k : ℝ))⁻¹ ≤ Real.log (2 * n + 1) := by
  have hsub : Icc (1 - 1 / 2 : ℝ) (1 + n - 1 / 2) ⊆ Ioi 0 := fun x hx => by
    simp only [mem_Ioi]; linarith [hx.1]
  have hinv : ConvexOn ℝ (Ioi 0) (fun x : ℝ => x⁻¹) := by
    simpa using convexOn_zpow (𝕜 := ℝ) (-1)
  have hconc : ConcaveOn ℝ (Icc (1 - 1 / 2 : ℝ) (1 + n - 1 / 2)) (fun x => -x⁻¹) :=
    (hinv.subset hsub (convex_Icc _ _)).neg
  have hcont : ContinuousOn (fun x : ℝ => -x⁻¹) (Icc (1 - 1 / 2 : ℝ) (1 + n - 1 / 2)) :=
    (continuousOn_inv₀.mono (fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [(hsub hx : x ∈ Ioi 0).out])).neg
  have h := integral_le_sum_of_concaveOn hconc hcont
  rw [intervalIntegral.integral_neg, integral_inv_of_pos (by norm_num) (by have := n.cast_nonneg (α := ℝ); linarith)] at h
  simp only [Finset.sum_neg_distrib] at h
  have e : (1 + (n : ℝ) - 1 / 2) / (1 - 1 / 2) = 2 * n + 1 := by norm_num; ring
  rw [e] at h
  linarith

end GaloisForLFunctions.HagedornBootstrap
