import GaloisForLFunctions.HTGeometry.SampledSmallSmooth
import GaloisForLFunctions.HTGeometry.SampledSmallLocalization
import GaloisForLFunctions.HTGeometry.SampledWindowDecay

/-!
# Fixed-order ray rate transfer for half-plane analytic functions

The window estimate and the fixed-order ray transfer, with the global
entirety hypothesis weakened to analyticity on a right half-plane
`{Re > T}`: a smooth bump supported in the analyticity region converts
the real restriction into a globally smooth curve agreeing with the
function near each window, so the smooth-curve estimate applies with the
complex derivative bounds transported through the local identification.
This is the transfer applicable to Lambert-type transforms, which are
analytic only where their exponential test is contractive.
-/

noncomputable section

namespace HTGeometry

open Complex Set Metric

/-- **Half-plane window estimate**: the sampled-window bound at canonical
separation for a function analytic on `{Re > T}` with `T < a`. -/
theorem norm_le_window_of_sampled_halfplane
    {T : ℝ} {H : ℂ → ℂ} (hH : ∀ t : ℝ, T < t → AnalyticAt ℂ H (t : ℂ))
    {N : ℕ} {s : Finset ℝ} (hcard : s.card = N + 1)
    {a : ℝ} (hTa : T < a) (hsub : ↑s ⊆ Set.Icc a (a + 1))
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u →
      1 / (4 * ((N : ℝ) + 1)) ≤ |t - u|)
    {M : ℝ}
    (hM : ∀ t ∈ Set.Icc a (a + 1), ‖iteratedDeriv (N + 1) H (t : ℂ)‖ ≤ M)
    {ε₀ : ℝ} (hε₀0 : 0 ≤ ε₀) (hε₀ : ∀ t ∈ s, ‖H (t : ℂ)‖ ≤ ε₀)
    {x : ℝ} (hx : x ∈ Set.Icc a (a + 1)) :
    ‖H (x : ℂ)‖ ≤ 2 * Real.exp (6 * ((N : ℝ) + 1)) * ε₀
      + 2 * (M / (N + 1).factorial) := by
  set ε : ℝ := min (a - T) 1 with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) one_pos
  have hεT : ε ≤ a - T := min_le_left _ _
  have hε1 : ε ≤ 1 := min_le_right _ _
  set bump : ContDiffBump (a + 1 / 2) :=
    ⟨1 / 2 + ε / 2, 1 / 2 + 3 * ε / 4, by linarith, by linarith⟩
    with hbumpdef
  have hrIn : bump.rIn = 1 / 2 + ε / 2 := rfl
  have hrOut : bump.rOut = 1 / 2 + 3 * ε / 4 := rfl
  have hrestrict := contDiffOn_comp_ofReal_of_analyticAt hH
  set g : ℝ → ℂ := fun t => bump t • H (t : ℂ) with hgdef
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [contDiff_iff_contDiffAt]
    intro t
    rcases lt_or_ge (dist t (a + 1 / 2)) (1 / 2 + ε) with hin | hout
    · have htT : T < t := by
        rw [Real.dist_eq, abs_lt] at hin
        linarith
      exact (bump.contDiff.contDiffAt).smul
        (hrestrict.contDiffAt (Ioi_mem_nhds htT))
    · have hzero : ∀ᶠ u in nhds t, g u = 0 := by
        have hopen : {u : ℝ | 1 / 2 + 7 * ε / 8 < dist u (a + 1 / 2)}
            ∈ nhds t := by
          have h1 : IsOpen {u : ℝ | 1 / 2 + 7 * ε / 8
              < dist u (a + 1 / 2)} :=
            isOpen_lt continuous_const (continuous_id.dist continuous_const)
          apply h1.mem_nhds
          rw [Set.mem_setOf_eq]
          linarith
        filter_upwards [hopen] with u hu
        rw [hgdef]
        simp only
        rw [bump.zero_of_le_dist
          (by rw [hrOut]; linarith : bump.rOut ≤ dist u (a + 1 / 2)),
          zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  have hone : ∀ u ∈ Set.Icc (a - ε / 4) (a + 1 + ε / 4),
      g u = H (u : ℂ) := by
    intro u hu
    rw [Set.mem_Icc] at hu
    have h1 : u ∈ closedBall (a + 1 / 2) bump.rIn := by
      rw [mem_closedBall, hrIn, Real.dist_eq, abs_le]
      constructor <;> linarith
    rw [hgdef]
    simp only
    rw [bump.one_of_mem_closedBall h1, one_smul]
  have hnhds : ∀ t ∈ Set.Icc a (a + 1),
      g =ᶠ[nhds t] fun u : ℝ => H (u : ℂ) := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have hmem : Set.Ioo (a - ε / 4) (a + 1 + ε / 4) ∈ nhds t :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hmem] with u hu
    exact hone u ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hη : (0 : ℝ) < 1 / (4 * ((N : ℝ) + 1)) := by positivity
  have hM' : ∀ t ∈ Set.Icc a (a + 1),
      ‖iteratedDeriv (N + 1) g t‖ ≤ M := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq (N + 1) (hnhds t ht),
      iteratedDeriv_comp_ofReal_of_analyticAt (N + 1) hH t
        (by rw [Set.mem_Icc] at ht; linarith)]
    exact hM t ht
  have hε₀' : ∀ t ∈ s, ‖g t‖ ≤ ε₀ := by
    intro t ht
    have h1 := hsub ht
    rw [Set.mem_Icc] at h1
    rw [hone t ⟨by linarith, by linarith⟩]
    exact hε₀ t ht
  have hmain := norm_le_of_sampled_small_smooth hg hcard hsub hη hsep hM'
    hε₀0 hε₀' hx
  have hgx : g x = H (x : ℂ) := by
    rw [Set.mem_Icc] at hx
    exact hone x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [hgx] at hmain
  have hconst := interpolation_constant_le N
  have hconst' : ((N : ℝ) + 1) * (2 ^ N
      / ((1 / (4 * ((N : ℝ) + 1))) ^ N * N.factorial))
      ≤ Real.exp (6 * ((N : ℝ) + 1)) := by
    rw [← mul_div_assoc]
    exact hconst
  have hfac0 : (0 : ℝ) ≤ M / (N + 1).factorial := by
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x hx)
    positivity
  nlinarith [mul_le_mul_of_nonneg_right hconst' hε₀0, hmain]

/-- **Half-plane fixed-order ray rate transfer**. -/
theorem norm_le_ray_of_sampled_decay_fixed_halfplane
    {T : ℝ} {H : ℂ → ℂ} (hH : ∀ t : ℝ, T < t → AnalyticAt ℂ H (t : ℂ))
    {R₀ δ K σ C : ℝ} {N : ℕ}
    (hTR₀ : T < R₀) (hR₀0 : 0 ≤ R₀) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hσ0 : 0 ≤ σ) (hδ0 : 0 ≤ δ)
    (hder : ∀ R : ℝ, R₀ ≤ R → ∀ x ∈ Set.Icc R (R + 1),
      ‖iteratedDeriv (N + 1) H (x : ℂ)‖ ≤ K * Real.exp (-(δ * R)))
    (hnodes : ∀ R : ℝ, R₀ ≤ R → ∃ s : Finset ℝ,
      s.card = N + 1 ∧ ↑s ⊆ Set.Icc R (R + 1) ∧
      (∀ t ∈ s, ∀ u ∈ s, t ≠ u →
        1 / (4 * ((N : ℝ) + 1)) ≤ |t - u|) ∧
      (∀ t ∈ s, ‖H (t : ℂ)‖ ≤ C * Real.exp (-(σ * R)))) :
    ∀ x : ℝ, R₀ + 1 ≤ x →
      ‖H (x : ℂ)‖ ≤ (2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
          + 2 * K * Real.exp δ / (N + 1).factorial)
        * Real.exp (-(min σ δ * x)) := by
  intro x hx
  have hRR₀ : R₀ ≤ x - 1 := by linarith
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨s, hcard, hsub, hsep, hsamp⟩ := hnodes (x - 1) hRR₀
  have hxmem : x ∈ Set.Icc (x - 1) (x - 1 + 1) := by
    constructor <;> linarith
  have hwin := norm_le_window_of_sampled_halfplane hH hcard
    (by linarith : T < x - 1) hsub hsep (hder (x - 1) hRR₀)
    (by positivity) hsamp hxmem
  have hmin : 0 ≤ min σ δ := le_min hσ0 hδ0
  have hA : 2 * Real.exp (6 * ((N : ℝ) + 1)) * (C * Real.exp (-(σ * (x - 1))))
      ≤ 2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
        * Real.exp (-(min σ δ * x)) := by
    have h1 : Real.exp (-(σ * (x - 1)))
        ≤ Real.exp σ * Real.exp (-(min σ δ * x)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h2 : min σ δ * x ≤ σ * x :=
        mul_le_mul_of_nonneg_right (min_le_left σ δ) hx0
      linarith
    calc 2 * Real.exp (6 * ((N : ℝ) + 1)) * (C * Real.exp (-(σ * (x - 1))))
        ≤ 2 * Real.exp (6 * ((N : ℝ) + 1))
          * (C * (Real.exp σ * Real.exp (-(min σ δ * x)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h1 hC
      _ = 2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
          * Real.exp (-(min σ δ * x)) := by ring
  have hB : 2 * (K * Real.exp (-(δ * (x - 1))) / (N + 1).factorial)
      ≤ 2 * K * Real.exp δ / (N + 1).factorial
        * Real.exp (-(min σ δ * x)) := by
    have h1 : Real.exp (-(δ * (x - 1)))
        ≤ Real.exp δ * Real.exp (-(min σ δ * x)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h2 : min σ δ * x ≤ δ * x :=
        mul_le_mul_of_nonneg_right (min_le_right σ δ) hx0
      linarith
    have hfac0 : (0 : ℝ) < ((N + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (N + 1)
    calc 2 * (K * Real.exp (-(δ * (x - 1))) / (N + 1).factorial)
        ≤ 2 * (K * (Real.exp δ * Real.exp (-(min σ δ * x)))
            / (N + 1).factorial) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply div_le_div_of_nonneg_right _ hfac0.le
          exact mul_le_mul_of_nonneg_left h1 hK
      _ = 2 * K * Real.exp δ / (N + 1).factorial
          * Real.exp (-(min σ δ * x)) := by ring
  calc ‖H (x : ℂ)‖
      ≤ 2 * Real.exp (6 * ((N : ℝ) + 1))
          * (C * Real.exp (-(σ * (x - 1))))
        + 2 * (K * Real.exp (-(δ * (x - 1))) / (N + 1).factorial) := hwin
    _ ≤ 2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
          * Real.exp (-(min σ δ * x))
        + 2 * K * Real.exp δ / (N + 1).factorial
          * Real.exp (-(min σ δ * x)) := add_le_add hA hB
    _ = (2 * Real.exp (6 * ((N : ℝ) + 1)) * C * Real.exp σ
          + 2 * K * Real.exp δ / (N + 1).factorial)
        * Real.exp (-(min σ δ * x)) := by ring

end HTGeometry
