import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Vanishing to finite order forces a power bound

A function whose derivative is dominated by `K t^m` on `[0,b]` and which vanishes at the origin is
dominated by `K t^{m+1}/(m+1)`.  Iterating downward from the top derivative, a smooth function all of
whose derivatives up to order `N` vanish at the origin satisfies

`‖f^{(j)}(x)‖ ≤ M |x|^{N+1-j}`

on a unit interval, where `M` bounds the `(N+1)`-st derivative.  This is the quantitative form of
"vanishing to order `N`" used by every local structure theorem at a point.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Power-boundary comparison.** -/
theorem norm_le_of_deriv_norm_le_pow {g g' : ℝ → X} {K b : ℝ} (m : ℕ)
    (hg0 : g 0 = 0)
    (hderiv : ∀ t ∈ Icc (0:ℝ) b, HasDerivAt g (g' t) t)
    (hbound : ∀ t ∈ Icc (0:ℝ) b, ‖g' t‖ ≤ K * t ^ m) :
    ∀ x ∈ Icc (0:ℝ) b, ‖g x‖ ≤ K * x ^ (m+1) / (m+1) := by
  intro x hx
  set B : ℝ → ℝ := fun t => K * t ^ (m+1) / (m+1) with hB
  have hBderiv : ∀ t : ℝ, HasDerivAt B (K * t ^ m) t := by
    intro t
    have hpow : HasDerivAt (fun y : ℝ => y ^ (m+1)) (((m:ℝ)+1) * t ^ m) t := by
      simpa using hasDerivAt_pow (m+1) t
    have h1 : HasDerivAt (fun y : ℝ => K * y ^ (m+1)) (K * (((m:ℝ)+1) * t ^ m)) t :=
      hpow.const_mul K
    have h2 := h1.div_const ((m:ℝ)+1)
    have hne : ((m:ℝ)+1) ≠ 0 := by positivity
    have hval : K * (((m:ℝ)+1) * t ^ m) / ((m:ℝ)+1) = K * t ^ m := by
      field_simp
    rw [hval] at h2
    have hfun : B = fun y : ℝ => K * y ^ (m+1) / (((m:ℝ)+1)) := by
      funext y
      rw [hB]
    rw [hfun]
    exact h2
  have hcont : ContinuousOn g (Icc (0:ℝ) b) := fun t ht =>
    ((hderiv t ht).continuousAt).continuousWithinAt
  have hderiv' : ∀ t ∈ Ico (0:ℝ) b, HasDerivWithinAt g (g' t) (Ici t) t := fun t ht =>
    (hderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  have hB0 : ‖g 0‖ ≤ B 0 := by
    rw [hg0, norm_zero, hB]
    simp
  have hbnd : ∀ t ∈ Ico (0:ℝ) b, ‖g' t‖ ≤ K * t ^ m := fun t ht =>
    hbound t (Ico_subset_Icc_self ht)
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hderiv' hB0 hBderiv hbnd hx
  have hval : B x = K * x ^ (m+1) / (m+1) := by
    rw [hB]
  rwa [hval] at h

/-- **Two-sided power-boundary comparison.** -/
theorem norm_le_of_deriv_norm_le_abs_pow {g g' : ℝ → X} {K b : ℝ} (m : ℕ)
    (hg0 : g 0 = 0)
    (hderiv : ∀ t ∈ Icc (-b) b, HasDerivAt g (g' t) t)
    (hbound : ∀ t ∈ Icc (-b) b, ‖g' t‖ ≤ K * |t| ^ m) :
    ∀ x ∈ Icc (-b) b, ‖g x‖ ≤ K * |x| ^ (m+1) / (m+1) := by
  intro x hx
  have hb : (0:ℝ) ≤ b := by
    have h1 := hx.1
    have h2 := hx.2
    linarith
  rcases le_total 0 x with hx0 | hx0
  · have hsub : ∀ t ∈ Icc (0:ℝ) b, t ∈ Icc (-b) b := by
      intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩
    have hd : ∀ t ∈ Icc (0:ℝ) b, HasDerivAt g (g' t) t := fun t ht => hderiv t (hsub t ht)
    have hb' : ∀ t ∈ Icc (0:ℝ) b, ‖g' t‖ ≤ K * t ^ m := by
      intro t ht
      have := hbound t (hsub t ht)
      rwa [abs_of_nonneg ht.1] at this
    have h := norm_le_of_deriv_norm_le_pow m hg0 hd hb' x ⟨hx0, hx.2⟩
    rwa [abs_of_nonneg hx0]
  · set gr : ℝ → X := fun t => g (-t) with hgr
    set gr' : ℝ → X := fun t => -g' (-t) with hgr'
    have hsub : ∀ t ∈ Icc (0:ℝ) b, -t ∈ Icc (-b) b := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1, hb]⟩
    have hd : ∀ t ∈ Icc (0:ℝ) b, HasDerivAt gr (gr' t) t := by
      intro t ht
      have hn : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) t := (hasDerivAt_id t).neg
      have hcomp := (hderiv (-t) (hsub t ht)).scomp t hn
      rw [neg_one_smul] at hcomp
      rw [hgr, hgr']
      exact hcomp
    have hb' : ∀ t ∈ Icc (0:ℝ) b, ‖gr' t‖ ≤ K * t ^ m := by
      intro t ht
      have := hbound (-t) (hsub t ht)
      rw [hgr', norm_neg]
      rwa [abs_neg, abs_of_nonneg ht.1] at this
    have hgr0 : gr 0 = 0 := by
      rw [hgr]
      simpa using hg0
    have hxmem : -x ∈ Icc (0:ℝ) b := ⟨by linarith, by linarith [hx.1]⟩
    have h := norm_le_of_deriv_norm_le_pow m hgr0 hd hb' (-x) hxmem
    rw [hgr] at h
    simp only [neg_neg] at h
    rwa [abs_of_nonpos hx0]

/-- **Vanishing to order `N` forces the `j`-th derivative to be `O(|x|^{N+1-j})`.** -/
theorem norm_iteratedDeriv_le_of_vanishing {f : ℝ → X} {M b : ℝ} {N : ℕ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hvanish : ∀ j, j ≤ N → iteratedDeriv j f 0 = 0)
    (hM : ∀ t ∈ Icc (-b) b, ‖iteratedDeriv (N+1) f t‖ ≤ M) :
    ∀ d, d ≤ N + 1 → ∀ x ∈ Icc (-b) b,
      ‖iteratedDeriv (N + 1 - d) f x‖ ≤ M * |x| ^ d / (Nat.factorial d) := by
  have hstep : ∀ k : ℕ, ∀ t : ℝ, HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k+1) f t) t := by
    intro k t
    have hd : Differentiable ℝ (iteratedDeriv k f) :=
      hf.differentiable_iteratedDeriv k (by exact_mod_cast lt_top_iff_ne_top.mpr (by simp))
    have h := (hd t).hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  intro d
  induction d with
  | zero =>
    intro _ x hx
    simpa using hM x hx
  | succ d ih =>
    intro hd x hx
    have hdle : d ≤ N + 1 := le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self d) hd)
    have hih := ih hdle
    have hindex : N + 1 - (d + 1) + 1 = N + 1 - d := by omega
    have hg0 : iteratedDeriv (N + 1 - (d+1)) f 0 = 0 := by
      refine hvanish _ ?_
      omega
    have hderiv : ∀ t ∈ Icc (-b) b,
        HasDerivAt (iteratedDeriv (N + 1 - (d+1)) f) (iteratedDeriv (N + 1 - d) f t) t := by
      intro t _
      have := hstep (N + 1 - (d+1)) t
      rwa [hindex] at this
    have hbound : ∀ t ∈ Icc (-b) b,
        ‖iteratedDeriv (N + 1 - d) f t‖ ≤ (M / (Nat.factorial d)) * |t| ^ d := by
      intro t ht
      have heq : M * |t| ^ d / (Nat.factorial d) = (M / (Nat.factorial d)) * |t| ^ d := by ring
      rw [← heq]
      exact hih t ht
    have h := norm_le_of_deriv_norm_le_abs_pow d hg0 hderiv hbound x hx
    refine le_trans h (le_of_eq ?_)
    rw [Nat.factorial_succ]
    push_cast
    field_simp

end GaloisForLFunctions.HTGeometry
