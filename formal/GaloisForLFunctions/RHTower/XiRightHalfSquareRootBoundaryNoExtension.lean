import GaloisForLFunctions.RHTower.GlobalParityWall

/-!
# Boundary non-extension of a right-half Xi square root

Hardy's sign-flip theorem gives critical-line zeros of odd analytic order above every height.
An analytic square-root germ would double its own local order, so it cannot square to Xi near any
such point.  Consequently Xi has no globally entire square root, and any square root witnessing
`RHLadder 1` on the strict right half-plane must be intrinsically half-plane-local: it cannot be
the restriction of an entire determinant or Pfaffian.

This does not construct the missing right-half root.  It is the sharp positive survivor of the
global-determinant route: a successful arithmetic construction must carry unavoidable boundary
branching at arbitrarily high critical-line points while remaining single-valued on `Re s > 1/2`.
-/

open Complex Filter Topology Real

namespace RHTower

/-- An odd-order Xi zero has no analytic square-root germ. -/
theorem no_local_analytic_sqrt_xi_of_odd_order
    {rho : ℂ} (hodd : Odd (analyticOrderAt xi rho).toNat) :
    ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧
      (fun s => g s ^ 2) =ᶠ[𝓝 rho] xi := by
  rintro ⟨g, hg, hsq⟩
  have hord :
      analyticOrderAt (fun s => g s ^ 2) rho = analyticOrderAt xi rho :=
    analyticOrderAt_congr hsq
  have heven : Even (analyticOrderAt xi rho).toNat := by
    rw [← hord, show (fun s => g s ^ 2) = g ^ 2 by rfl,
      analyticOrderAt_pow hg]
    rw [show (2 • analyticOrderAt g rho).toNat =
        2 * (analyticOrderAt g rho).toNat by
      rw [nsmul_eq_mul, ENat.toNat_mul]
      norm_num]
    exact even_two.mul_right _
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- Arbitrarily high critical-line Xi zeros admit no analytic square-root germ. -/
theorem exists_odd_order_line_zero_no_local_analytic_sqrt_gt (T : ℝ) :
    ∃ tau : ℝ, T < tau ∧ xi (linePt tau) = 0 ∧
      ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g (linePt tau) ∧
        (fun s => g s ^ 2) =ᶠ[𝓝 (linePt tau)] xi := by
  obtain ⟨tau, hT, hzero, hodd⟩ := exists_odd_order_line_zero_gt T
  exact ⟨tau, hT, hzero, no_local_analytic_sqrt_xi_of_odd_order hodd⟩

/-- Xi has no globally entire square root. -/
theorem not_exists_entire_sqrt_xi :
    ¬ ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s, g s ^ 2 = xi s := by
  rintro ⟨g, hg, hsq⟩
  obtain ⟨rho, _hzero, hodd⟩ := exists_odd_order_zero_xi
  exact no_local_analytic_sqrt_xi_of_odd_order hodd
    ⟨g, hg.analyticAt rho, Filter.Eventually.of_forall hsq⟩

/-- Any exact square root of Xi on the strict right half-plane is necessarily non-entire. -/
theorem rightHalf_sqrt_not_entire {g : ℂ → ℂ}
    (hgsq : ∀ s ∈ rightHalf, g s ^ 2 = xi s) :
    ¬ Differentiable ℂ g := by
  intro hg
  apply not_exists_entire_sqrt_xi
  refine ⟨g, hg, ?_⟩
  have hgan : AnalyticOnNhd ℂ (fun s => g s ^ 2) Set.univ := by
    intro s _hs
    exact (hg.analyticAt s).pow 2
  have heq : (fun s => g s ^ 2) =ᶠ[𝓝 (1 : ℂ)] xi := by
    filter_upwards [isOpen_rightHalf.mem_nhds
      (show (1 : ℂ) ∈ rightHalf by rw [mem_rightHalf]; norm_num)] with s hs
    exact hgsq s hs
  exact fun s => hgan.eqOn_of_preconnected_of_eventuallyEq
    (xi_analyticOnNhd Set.univ) isPreconnected_univ (Set.mem_univ 1) heq
    (Set.mem_univ s)

/-- The first ladder rung is exactly existence of a necessarily non-entire right-half square
root.  The extra non-entire clause is forced unconditionally by Hardy's odd seam zeros. -/
theorem rhLadder_one_iff_exists_rightHalf_sqrt_not_entire :
    RHLadder 1 ↔ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g rightHalf ∧
      (∀ s ∈ rightHalf, g s ^ 2 = xi s) ∧ ¬ Differentiable ℂ g := by
  rw [rhLadder_one_iff_sqrt_rightHalf]
  constructor
  · rintro ⟨g, hg, hsq⟩
    exact ⟨g, hg, hsq, rightHalf_sqrt_not_entire hsq⟩
  · rintro ⟨g, hg, hsq, _⟩
    exact ⟨g, hg, hsq⟩

end RHTower
