import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticRigidity
import GaloisForLFunctions.RHTower.DirichletLZeroHalfPlane
import GaloisForLFunctions.RHTower.DirichletLZeroExistence
import GaloisForLFunctions.RHTower.DirichletCompletedLOrderOne
import GaloisForLFunctions.RHTower.DirichletCompletedLRayGrowth

/-!
# Infinitely many zeros of completed primitive Dirichlet L-functions

The finite-zero subquadratic rigidity theorem upgrades the existing one-zero argument to zero-set
infinitude.  The completed Dirichlet L-function is entire of order at most one and has logarithmic
norm beating every linear slope on the positive real ray, so a finite divisor is impossible.

For primitive characters, the Euler zero-free half-plane and functional equation confine every
completed zero to `0 < re s < 1`.  Local isolated-zero finiteness then forces the zero ordinates to
be unbounded.  These are the analytic inputs needed for the actual GL(1) automorphic Real-corona
classification.
-/

noncomputable section

open Complex Filter Metric Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

variable {N : ℕ} [NeZero N]

def completedDirichletZeroSet (chi : DirichletCharacter ℂ N) : Set ℂ :=
  {z | DirichletCharacter.completedLFunction chi z = 0}

/-- Every nontrivial completed Dirichlet L-function has infinitely many distinct zeros. -/
theorem completedLFunction_zeroSet_infinite
    {chi : DirichletCharacter ℂ N} (hchi : chi ≠ 1) :
    (completedDirichletZeroSet chi).Infinite := by
  obtain ⟨C, hC, hgrow⟩ := (completedLFunction_orderOneEnvelope hchi).subquadratic
  exact zeroSet_infinite_of_subquadratic_superlinear_ray
    (DirichletCharacter.differentiable_completedLFunction hchi)
    (by norm_num) (by norm_num) hC hgrow
    (fun A => completedLFunction_ray_growth A)

/-- Zeros of a nontrivial primitive completion lie in the open critical strip. -/
theorem completedLFunction_zero_mem_openUnitStrip
    {chi : DirichletCharacter ℂ N} (hchi : chi ≠ 1)
    (hprim : chi.IsPrimitive) {rho : ℂ}
    (hrho : rho ∈ completedDirichletZeroSet chi) :
    0 < rho.re ∧ rho.re < 1 := by
  change DirichletCharacter.completedLFunction chi rho = 0 at hrho
  constructor
  · by_contra hnot
    have hre : rho.re ≤ 0 := le_of_not_gt hnot
    let w : ℂ := 1 - rho
    have hwre : 1 ≤ w.re := by
      dsimp [w]
      linarith
    have hwne : w ≠ 0 := by
      intro hw
      rw [hw] at hwre
      norm_num at hwre
    have hchiInv : chi⁻¹ ≠ 1 := by
      intro h
      exact hchi (by rw [← inv_inv chi, h, inv_one])
    have hFE := hprim.completedLFunction_one_sub (1 - rho)
    rw [show (1 : ℂ) - (1 - rho) = rho by ring, hrho] at hFE
    have hNne : ((N : ℂ)) ^ (((1 : ℂ) - rho) - 1 / 2) ≠ 0 := by
      refine fun h => ?_
      rw [Complex.cpow_eq_zero_iff] at h
      exact (Nat.cast_ne_zero.mpr (NeZero.ne N)) h.1
    have hLambdaInv : DirichletCharacter.completedLFunction chi⁻¹ w = 0 := by
      rcases mul_eq_zero.mp hFE.symm with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hNne
        · exact absurd h' (rootNumber_ne_zero hprim)
      · exact h
    have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi⁻¹ w
      (Or.inl hwne)
    rw [hLambdaInv, zero_div] at hL
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi⁻¹
      (Or.inl hchiInv) hwre hL
  · by_contra hnot
    have hre : 1 ≤ rho.re := not_lt.mp hnot
    have hrhoNe : rho ≠ 0 := by
      intro h
      rw [h] at hre
      norm_num at hre
    have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi rho
      (Or.inl hrhoNe)
    rw [hrho, zero_div] at hL
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi
      (Or.inl hchi) hre hL

/-- The completed Dirichlet zero set is locally finite in every closed disc. -/
theorem completedLFunction_zeros_closedBall_finite
    {chi : DirichletCharacter ℂ N} (hchi : chi ≠ 1) (c : ℂ) (R : ℝ) :
    {z ∈ Metric.closedBall c R |
      DirichletCharacter.completedLFunction chi z = 0}.Finite := by
  obtain ⟨sigma, _, hne⟩ := exists_completedLFunction_ne_zero_ray (χ := chi)
  have hA : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction chi) Set.univ :=
    (DirichletCharacter.differentiable_completedLFunction hchi).differentiableOn.analyticOnNhd
      isOpen_univ
  have hcod :
      ((DirichletCharacter.completedLFunction chi) ⁻¹' {0}ᶜ) ∈
        codiscreteWithin (Set.univ : Set ℂ) :=
    hA.preimage_zero_mem_codiscreteWithin
      (x := (sigma : ℂ)) hne (Set.mem_univ _) isConnected_univ
  have hcodK :
      ((DirichletCharacter.completedLFunction chi) ⁻¹' {0}ᶜ) ∈
        codiscreteWithin (Metric.closedBall c R) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine ((isCompact_closedBall c R).finite_sdiff_of_mem_codiscreteWithin hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

/-- Primitive completed Dirichlet zero ordinates are unbounded. -/
theorem exists_completedLFunction_zero_im_abs_gt
    {chi : DirichletCharacter ℂ N} (hchi : chi ≠ 1)
    (hprim : chi.IsPrimitive) (T : ℝ) :
    ∃ rho ∈ completedDirichletZeroSet chi, T < |rho.im| := by
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_and, not_lt] at hcon
  have hsub : completedDirichletZeroSet chi ⊆
      {z ∈ Metric.closedBall (0 : ℂ) (1 + |T|) |
        DirichletCharacter.completedLFunction chi z = 0} := by
    intro z hz
    have hstrip := completedLFunction_zero_mem_openUnitStrip hchi hprim hz
    have him := hcon z hz
    refine ⟨?_, hz⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |T| := by
        have h1 : |z.re| ≤ 1 := by
          rw [abs_of_pos hstrip.1]
          linarith [hstrip.2]
        have h2 : |z.im| ≤ |T| := le_trans him (le_abs_self T)
        linarith
  exact completedLFunction_zeroSet_infinite hchi
    ((completedLFunction_zeros_closedBall_finite hchi 0 (1 + |T|)).subset hsub)

end RHTower
