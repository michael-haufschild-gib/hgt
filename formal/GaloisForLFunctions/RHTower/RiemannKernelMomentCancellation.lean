import GaloisForLFunctions.RHTower.RiemannAutocorrBalancedQuadratic
import Mathlib.Analysis.Calculus.Taylor

/-!
# All-order cancellation for the actual Riemann kernel

The derivative family already present in the corpus supplies every Taylor
coefficient and every remainder bound. Finite moment cancellation therefore
requires no additional smoothness or analytic hypothesis.
-/

open scoped BigOperators
open Set

namespace RHTower

theorem iteratedDeriv_riemannKernelDeriv (n k : ℕ) :
    iteratedDeriv n (riemannKernelDeriv k) = riemannKernelDeriv (k + n) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    simpa only [Nat.add_assoc] using (hasDerivAt_riemannKernelDeriv (k + n) x).deriv

/-- An actual Taylor remainder with an exponentially decaying constant,
uniform in the base point. -/
theorem riemannKernelDeriv_taylor_bound_of_envelope (r k : ℕ) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z, ‖riemannKernelDeriv (k + (r + 1)) z‖ ≤ C * Real.exp (-3 * |z|)) :
    ∀ x h : ℝ, 0 ≤ h → h ≤ 1 →
      ‖riemannKernelDeriv k (x + h) -
        ∑ p ∈ Finset.range (r + 1),
          ((p.factorial : ℝ)⁻¹ * h ^ p) • riemannKernelDeriv (k + p) x‖ ≤
        (C * Real.exp 3 / (r.factorial : ℝ)) * Real.exp (-3 * |x|) * h ^ (r + 1) := by
  intro x h h0 h1
  have hdiff : UniqueDiffOn ℝ (Icc x (x + 1)) := uniqueDiffOn_Icc (by linarith)
  have hder (n : ℕ) (z : ℝ) (hz : z ∈ Icc x (x + 1)) :
      iteratedDerivWithin n (riemannKernelDeriv k) (Icc x (x + 1)) z =
        riemannKernelDeriv (k + n) z := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hdiff
      (contDiff_riemannKernelDeriv n k).contDiffAt hz,
      iteratedDeriv_riemannKernelDeriv]
  have hlocal (z : ℝ) (hz : z ∈ Icc x (x + 1)) :
      ‖iteratedDerivWithin (r + 1) (riemannKernelDeriv k) (Icc x (x + 1)) z‖ ≤
        C * Real.exp 3 * Real.exp (-3 * |x|) := by
    rw [hder (r + 1) z hz]
    have ha : |x| ≤ |z| + 1 := by
      have hdz : |x - z| ≤ 1 := abs_le.mpr ⟨by linarith [hz.2], by linarith [hz.1]⟩
      calc
        |x| = |z + (x - z)| := by congr 1; ring
        _ ≤ |z| + |x - z| := abs_add_le _ _
        _ ≤ |z| + 1 := by linarith [hdz]
    calc
      ‖riemannKernelDeriv (k + (r + 1)) z‖ ≤ C * Real.exp (-3 * |z|) :=
        by simpa only [neg_mul] using hbound z
      _ ≤ C * Real.exp (3 + -3 * |x|) := by gcongr; linarith
      _ = C * Real.exp 3 * Real.exp (-3 * |x|) := by rw [Real.exp_add]; ring
  have ht := taylor_mean_remainder_bound (f := riemannKernelDeriv k)
    (a := x) (b := x + 1) (n := r) (x := x + h) (by linarith)
    (contDiff_riemannKernelDeriv (r + 1) k).contDiffOn
    ⟨by linarith, by linarith⟩ hlocal
  have hpoly : taylorWithinEval (riemannKernelDeriv k) r (Icc x (x + 1)) x (x + h) =
      ∑ p ∈ Finset.range (r + 1),
        ((p.factorial : ℝ)⁻¹ * h ^ p) • riemannKernelDeriv (k + p) x := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hder p x ⟨le_rfl, by linarith⟩]
    congr 2
    ring
  rw [hpoly, show x + h - x = h by ring] at ht
  convert ht using 1
  ring

theorem exists_riemannKernelDeriv_taylor_envelope (r k : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ x h : ℝ, 0 ≤ h → h ≤ 1 →
      ‖riemannKernelDeriv k (x + h) -
        ∑ p ∈ Finset.range (r + 1),
          ((p.factorial : ℝ)⁻¹ * h ^ p) • riemannKernelDeriv (k + p) x‖ ≤
        D * Real.exp (-3 * |x|) * h ^ (r + 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_riemannKernelDeriv_cubic_exp_envelope (k + (r + 1))
  refine ⟨C * Real.exp 3 / (r.factorial : ℝ), by positivity, ?_⟩
  exact riemannKernelDeriv_taylor_bound_of_envelope r k hC
    (fun z => by simpa only [neg_mul] using hbound z)

/-- The real kernel inherits the same Taylor remainder from its complex lift. -/
theorem exists_riemannKernelReal_taylor_envelope (r : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ x h : ℝ, 0 ≤ h → h ≤ 1 →
      |riemannKernelReal (x + h) -
        ∑ p ∈ Finset.range (r + 1),
          ((p.factorial : ℝ)⁻¹ * h ^ p) * (riemannKernelDeriv p x).re| ≤
        D * Real.exp (-3 * |x|) * h ^ (r + 1) := by
  obtain ⟨D, hD, hbound⟩ := exists_riemannKernelDeriv_taylor_envelope r 0
  refine ⟨D, hD, ?_⟩
  intro x h h0 h1
  have hb := hbound x h h0 h1
  have hre := Complex.abs_re_le_norm (riemannKernelDeriv 0 (x + h) -
    ∑ p ∈ Finset.range (r + 1),
      ((p.factorial : ℝ)⁻¹ * h ^ p) • riemannKernelDeriv (0 + p) x)
  simp only [Nat.zero_add, riemannKernelDeriv_zero, riemannPhiKernel_eq_ofReal,
    Complex.sub_re, Complex.re_sum, Complex.smul_re, smul_eq_mul, Complex.ofReal_re] at hre hb
  exact hre.trans hb

/-- Annihilating the first `r+1` moments gains `r+1` powers of the cluster width.
The coefficients may have either sign and the estimate is uniform in the base point. -/
theorem riemannKernelReal_moment_cancellation_of_taylor_bound (r : ℕ) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ x h : ℝ, 0 ≤ h → h ≤ 1 →
      |riemannKernelReal (x + h) -
        ∑ p ∈ Finset.range (r + 1),
          ((p.factorial : ℝ)⁻¹ * h ^ p) * (riemannKernelDeriv p x).re| ≤
        D * Real.exp (-3 * |x|) * h ^ (r + 1)) :
    ∀ (ι : Type) [Fintype ι] (c h : ι → ℝ) (H : ℝ),
      0 ≤ H → H ≤ 1 → (∀ i, 0 ≤ h i ∧ h i ≤ H) →
      (∀ p ≤ r, ∑ i, c i * h i ^ p = 0) → ∀ x : ℝ,
      |∑ i, c i * riemannKernelReal (x + h i)| ≤
        D * Real.exp (-3 * |x|) * (∑ i, |c i|) * H ^ (r + 1) := by
  intro ι _ c h H hH0 hH1 hh hm x
  have hpoly : (∑ i, c i * ∑ p ∈ Finset.range (r + 1),
      ((p.factorial : ℝ)⁻¹ * h i ^ p) * (riemannKernelDeriv p x).re) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro p hp
    calc
      ∑ i, c i * (((p.factorial : ℝ)⁻¹ * h i ^ p) * (riemannKernelDeriv p x).re) =
          ((p.factorial : ℝ)⁻¹ * (riemannKernelDeriv p x).re) * ∑ i, c i * h i ^ p := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := by rw [hm p (by have := Finset.mem_range.mp hp; omega), mul_zero]
  calc
    |∑ i, c i * riemannKernelReal (x + h i)| =
        |∑ i, c i * (riemannKernelReal (x + h i) -
          ∑ p ∈ Finset.range (r + 1),
            ((p.factorial : ℝ)⁻¹ * h i ^ p) * (riemannKernelDeriv p x).re)| := by
      simp only [mul_sub, Finset.sum_sub_distrib, hpoly, sub_zero]
    _ ≤ ∑ i, |c i| * |riemannKernelReal (x + h i) -
          ∑ p ∈ Finset.range (r + 1),
            ((p.factorial : ℝ)⁻¹ * h i ^ p) * (riemannKernelDeriv p x).re| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (s := Finset.univ)
        (f := fun i => c i * (riemannKernelReal (x + h i) -
          ∑ p ∈ Finset.range (r + 1),
            ((p.factorial : ℝ)⁻¹ * h i ^ p) * (riemannKernelDeriv p x).re))
    _ ≤ ∑ i, |c i| * (D * Real.exp (-3 * |x|) * H ^ (r + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (hbound x (h i) (hh i).1 ((hh i).2.trans hH1)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hh i).1 (hh i).2 _) (by positivity))
    _ = D * Real.exp (-3 * |x|) * (∑ i, |c i|) * H ^ (r + 1) := by
      rw [← Finset.sum_mul]
      ring

theorem exists_riemannKernelReal_moment_cancellation_envelope (r : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (ι : Type) [Fintype ι] (c h : ι → ℝ) (H : ℝ),
      0 ≤ H → H ≤ 1 → (∀ i, 0 ≤ h i ∧ h i ≤ H) →
      (∀ p ≤ r, ∑ i, c i * h i ^ p = 0) → ∀ x : ℝ,
      |∑ i, c i * riemannKernelReal (x + h i)| ≤
        D * Real.exp (-3 * |x|) * (∑ i, |c i|) * H ^ (r + 1) := by
  obtain ⟨D, hD, hbound⟩ := exists_riemannKernelReal_taylor_envelope r
  exact ⟨D, hD, riemannKernelReal_moment_cancellation_of_taylor_bound r hD hbound⟩

end RHTower
