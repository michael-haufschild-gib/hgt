import GaloisForLFunctions.HTGeometry.VerticalAlmostPeriodicDerivative

/-!
# Exponential sums inhabit the strip almost periodic class

A finite sum `∑ a_k e^{λ_k z}` with real frequencies is almost periodic on every vertical strip: the
exponential factors are bounded on the strip, and the characters `t ↦ e^{i λ_k t}` share a relatively
dense set of almost periods, so a common almost period of the characters is an almost period of the
sum with the tolerance scaled by the bound.

This is the non-vacuity check for the finite-phase law: the hypothesis class contains nonconstant
functions with an arbitrary prescribed finite frequency set — in particular with arbitrarily large
rational frequency rank — so the dimension bound is a statement about a rich class, not an empty one.
On the plane the class would collapse: a translated difference bounded on all of `ℂ` is constant by
Liouville, which forces genuine periodicity.
-/

open Filter Topology Metric Finset

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- A finite exponential sum with real frequencies. -/
noncomputable def expSum {n : ℕ} (a : Fin n → ℂ) (lam : Fin n → ℝ) : ℂ → ℂ :=
  fun z => ∑ k, a k * Complex.exp ((lam k : ℂ) * z)

theorem differentiable_expSum {n : ℕ} (a : Fin n → ℂ) (lam : Fin n → ℝ) :
    Differentiable ℂ (expSum a lam) := by
  unfold expSum
  fun_prop

/-- **Finite exponential sums are strip almost periodic on every strip.** -/
theorem isStripAlmostPeriodic_expSum {n : ℕ} (a : Fin n → ℂ) (lam : Fin n → ℝ) (σ R : ℝ) :
    IsStripAlmostPeriodic (expSum a lam) σ R := by
  classical
  intro r _hr ε hε
  set B : Fin n → ℝ := fun k => ‖a k‖ * Real.exp (|lam k| * (|σ| + |r|)) with hBdef
  set C : ℝ := ∑ k, B k + 1 with hCdef
  have hBnonneg : ∀ k, 0 ≤ B k := by
    intro k
    rw [hBdef]
    positivity
  have hCpos : 0 < C := by
    have hs : 0 ≤ ∑ k, B k := Finset.sum_nonneg fun k _ => hBnonneg k
    rw [hCdef]
    linarith
  set g : Fin n → ℝ → ℂ := fun k t => Complex.exp (((lam k * t : ℝ) : ℂ) * Complex.I) with hgdef
  have hgeq : ∀ k, g k = bohrChar (-(lam k)) := by
    intro k
    funext t
    rw [hgdef, bohrChar]
    norm_num
  have hgcont : ∀ k, Continuous (g k) := by
    intro k
    rw [hgeq k]
    exact continuous_bohrChar _
  have hgap : ∀ k, IsBohrAlmostPeriodic (g k) := by
    intro k
    rw [hgeq k]
    exact isBohrAlmostPeriodic_bohrChar _
  obtain ⟨L, hL, hdense⟩ := isBohrAlmostPeriodic_fin hgcont hgap (ε / C) (by positivity)
  refine ⟨L, hL, fun x => ?_⟩
  obtain ⟨τ, hτ, hb⟩ := hdense x
  refine ⟨τ, hτ, fun z hz => ?_⟩
  have hchar : ∀ k, ‖Complex.exp (((lam k * τ : ℝ) : ℂ) * Complex.I) - 1‖ ≤ ε / C := by
    intro k
    have h := hb 0
    rw [pi_norm_le_iff_of_nonneg (by positivity)] at h
    have hk := h k
    simp only [hgdef, Pi.sub_apply, zero_add] at hk
    have hzero : Complex.exp (((lam k * 0 : ℝ) : ℂ) * Complex.I) = 1 := by norm_num
    rwa [hzero] at hk
  have hterm : ∀ k, a k * Complex.exp ((lam k : ℂ) * (z + (τ : ℂ) * Complex.I))
      - a k * Complex.exp ((lam k : ℂ) * z)
      = a k * Complex.exp ((lam k : ℂ) * z)
        * (Complex.exp (((lam k * τ : ℝ) : ℂ) * Complex.I) - 1) := by
    intro k
    have hsplit : (lam k : ℂ) * (z + (τ : ℂ) * Complex.I)
        = (lam k : ℂ) * z + ((lam k * τ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hsplit, Complex.exp_add]
    ring
  have hnormterm : ∀ k, ‖a k * Complex.exp ((lam k : ℂ) * z)‖ ≤ B k := by
    intro k
    rw [norm_mul, Complex.norm_exp]
    have hre : ((lam k : ℂ) * z).re = lam k * z.re := by
      simp [Complex.mul_re]
    rw [hre, hBdef]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Real.exp_le_exp.mpr ?_
    have h1 : |z.re| ≤ |σ| + |r| := by
      have h2 : |z.re - σ| ≤ r := hz
      calc |z.re| = |(z.re - σ) + σ| := by ring_nf
        _ ≤ |z.re - σ| + |σ| := abs_add_le _ _
        _ ≤ r + |σ| := by linarith [le_abs_self r]
        _ ≤ |r| + |σ| := by linarith [le_abs_self r]
        _ = |σ| + |r| := by ring
    calc lam k * z.re ≤ |lam k * z.re| := le_abs_self _
      _ = |lam k| * |z.re| := abs_mul _ _
      _ ≤ |lam k| * (|σ| + |r|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hrewrite : expSum a lam (z + (τ : ℂ) * Complex.I) - expSum a lam z
      = ∑ k, a k * Complex.exp ((lam k : ℂ) * z)
          * (Complex.exp (((lam k * τ : ℝ) : ℂ) * Complex.I) - 1) := by
    unfold expSum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => hterm k
  rw [hrewrite]
  calc ‖∑ k, a k * Complex.exp ((lam k : ℂ) * z)
          * (Complex.exp (((lam k * τ : ℝ) : ℂ) * Complex.I) - 1)‖
      ≤ ∑ k, ‖a k * Complex.exp ((lam k : ℂ) * z)
          * (Complex.exp (((lam k * τ : ℝ) : ℂ) * Complex.I) - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k, B k * (ε / C) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hnormterm k) (hchar k) (norm_nonneg _) (hBnonneg k)
    _ = (∑ k, B k) * (ε / C) := by rw [← Finset.sum_mul]
    _ ≤ ε := by
        have hs : (∑ k, B k) ≤ C := by rw [hCdef]; linarith
        have hpos : 0 < ε / C := by positivity
        calc (∑ k, B k) * (ε / C) ≤ C * (ε / C) := mul_le_mul_of_nonneg_right hs hpos.le
          _ = ε := by field_simp

end GaloisForLFunctions
