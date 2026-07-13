/-
# A zero-free fundamental boundary for Jacobi theta

The theta zero set is finite in every compact disc.  Real coordinates in the basis `(1, τ)` then
allow a diagonal translate of a fundamental parallelogram to avoid this finite set on all four
edges.  This supplies the regular contour consumed by the fundamental-parallelogram charge.
-/
import GaloisForLFunctions.HTGeometry.JacobiThetaParallelogramCharge
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex Set Metric Filter

namespace GaloisForLFunctions

noncomputable section

/-- The coefficient of `τ` in the real basis decomposition `z=x+yτ`. -/
def tauCoordY (τ z : ℂ) : ℝ := z.im / τ.im

/-- The coefficient of `1` in the real basis decomposition `z=x+yτ`. -/
def tauCoordX (τ z : ℂ) : ℝ := z.re - tauCoordY τ z * τ.re

theorem tauCoord_decomposition {τ z : ℂ} (hτ : τ.im ≠ 0) :
    z = (tauCoordX τ z : ℂ) + (tauCoordY τ z : ℂ) * τ := by
  apply Complex.ext
  · simp [tauCoordX, tauCoordY]
  · simp [tauCoordY]
    field_simp

theorem tauCoordX_add {τ z w : ℂ} (hτ : τ.im ≠ 0) :
    tauCoordX τ (z + w) = tauCoordX τ z + tauCoordX τ w := by
  simp [tauCoordX, tauCoordY]
  field_simp
  ring

theorem tauCoordY_add {τ z w : ℂ} :
    tauCoordY τ (z + w) = tauCoordY τ z + tauCoordY τ w := by
  simp [tauCoordY]
  ring

theorem tauCoordX_ofReal {τ : ℂ} (x : ℝ) :
    tauCoordX τ (x : ℂ) = x := by
  simp [tauCoordX, tauCoordY]

theorem tauCoordY_ofReal (τ : ℂ) (x : ℝ) :
    tauCoordY τ (x : ℂ) = 0 := by
  simp [tauCoordY]

theorem tauCoordX_tau {τ : ℂ} (hτ : τ.im ≠ 0) : tauCoordX τ τ = 0 := by
  simp [tauCoordX, tauCoordY, hτ]

theorem tauCoordY_tau {τ : ℂ} (hτ : τ.im ≠ 0) : tauCoordY τ τ = 1 := by
  simp [tauCoordY, hτ]

theorem tauCoordY_diagonal_bottom {τ : ℂ} (hτ : τ.im ≠ 0) (s t : ℝ) :
    tauCoordY τ (-((s : ℂ) * (1 + τ)) + (t : ℂ)) = -s := by
  simp [tauCoordY]
  field_simp

theorem tauCoordX_diagonal_left {τ : ℂ} (hτ : τ.im ≠ 0) (s t : ℝ) :
    tauCoordX τ (-((s : ℂ) * (1 + τ)) + (t : ℂ) * τ) = -s := by
  simp [tauCoordX, tauCoordY]
  field_simp
  ring

theorem norm_diagonal_bottom_le {τ : ℂ} {s t : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖-((s : ℂ) * (1 + τ)) + (t : ℂ)‖ ≤ 2 + 2 * ‖τ‖ := by
  calc
    ‖-((s : ℂ) * (1 + τ)) + (t : ℂ)‖ ≤
        ‖((s : ℂ) * (1 + τ))‖ + ‖(t : ℂ)‖ := by
      simpa only [norm_neg] using norm_add_le (-((s : ℂ) * (1 + τ))) (t : ℂ)
    _ = s * ‖1 + τ‖ + t := by simp [abs_of_nonneg hs0, abs_of_nonneg ht0]
    _ ≤ s * (1 + ‖τ‖) + t := by
      gcongr
      simpa using norm_add_le (1 : ℂ) τ
    _ ≤ 2 + 2 * ‖τ‖ := by nlinarith [norm_nonneg τ]

theorem norm_diagonal_left_le {τ : ℂ} {s t : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖-((s : ℂ) * (1 + τ)) + (t : ℂ) * τ‖ ≤ 2 + 2 * ‖τ‖ := by
  calc
    ‖-((s : ℂ) * (1 + τ)) + (t : ℂ) * τ‖ ≤
        ‖((s : ℂ) * (1 + τ))‖ + ‖(t : ℂ) * τ‖ := by
      simpa only [norm_neg] using norm_add_le (-((s : ℂ) * (1 + τ))) ((t : ℂ) * τ)
    _ = s * ‖1 + τ‖ + t * ‖τ‖ := by
      simp [abs_of_nonneg hs0, abs_of_nonneg ht0]
    _ ≤ s * (1 + ‖τ‖) + t * ‖τ‖ := by
      gcongr
      simpa using norm_add_le (1 : ℂ) τ
    _ ≤ 2 + 2 * ‖τ‖ := by nlinarith [norm_nonneg τ]

/-- The zeros of fixed-parameter Jacobi theta in any closed disc form a finite set. -/
theorem jacobiTheta₂_zeros_closedBall_finite {τ : ℂ} (hτ : 0 < τ.im) (c : ℂ) (R : ℝ) :
    {z ∈ closedBall c R | jacobiTheta₂ z τ = 0}.Finite := by
  have hcod : ((jacobiTheta₂ · τ) ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    (jacobiTheta₂_analyticOnNhd_fst τ hτ).preimage_zero_mem_codiscreteWithin
      (x := 0) (by
        simpa [Bottcher.thetaThree] using Bottcher.thetaThree_ne_zero_of_im_pos hτ)
      (Set.mem_univ 0) isConnected_univ
  have hcodK : ((jacobiTheta₂ · τ) ⁻¹' {0}ᶜ) ∈ codiscreteWithin (closedBall c R) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine ((isCompact_closedBall c R).finite_diff_of_mem_codiscreteWithin hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

/-- There is a diagonal translate of the fundamental parallelogram whose entire boundary avoids
the theta zero set. -/
theorem exists_thetaParallelogramBoundaryRegular {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ a : ℂ, ThetaParallelogramBoundaryRegular τ a := by
  let R : ℝ := 2 + 2 * ‖τ‖
  let Z : Set ℂ := {z ∈ closedBall 0 R | jacobiTheta₂ z τ = 0}
  have hZ : Z.Finite := jacobiTheta₂_zeros_closedBall_finite hτ 0 R
  let Bad : Set ℝ :=
    (fun z : ℂ ↦ -tauCoordY τ z) '' Z ∪ (fun z : ℂ ↦ -tauCoordX τ z) '' Z
  have hBad : Bad.Finite := (hZ.image _).union (hZ.image _)
  have hI : (Ioo ((1 : ℝ) / 4) (1 / 3)).Infinite := Set.Ioo_infinite (by norm_num)
  obtain ⟨s, hsI, hsBad⟩ := (hI.diff hBad).nonempty
  have hs : (1 : ℝ) / 4 < s ∧ s < 1 / 3 := hsI
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  refine ⟨-((s : ℂ) * (1 + τ)), ?_, ?_⟩
  · intro t ht
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Icc] at ht
    intro hzero
    let z : ℂ := -((s : ℂ) * (1 + τ)) + (t : ℂ)
    have hzball : z ∈ closedBall 0 R := by
      rw [mem_closedBall, dist_zero_right]
      exact norm_diagonal_bottom_le hs0 hs1 ht.1 ht.2
    have hzZ : z ∈ Z := ⟨hzball, hzero⟩
    have hbad : s ∈ Bad := by
      apply Or.inl
      refine ⟨z, hzZ, ?_⟩
      dsimp [z]
      rw [tauCoordY_diagonal_bottom hτ.ne' s t]
      simp
    exact hsBad hbad
  · intro t ht
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Icc] at ht
    intro hzero
    let z : ℂ := -((s : ℂ) * (1 + τ)) + (t : ℂ) * τ
    have hzball : z ∈ closedBall 0 R := by
      rw [mem_closedBall, dist_zero_right]
      exact norm_diagonal_left_le hs0 hs1 ht.1 ht.2
    have hzZ : z ∈ Z := ⟨hzball, hzero⟩
    have hbad : s ∈ Bad := by
      apply Or.inr
      refine ⟨z, hzZ, ?_⟩
      dsimp [z]
      rw [tauCoordX_diagonal_left hτ.ne' s t]
      simp
    exact hsBad hbad

/-- A zero-free fundamental theta boundary with its exact logarithmic-derivative charge. -/
theorem exists_thetaParallelogramBoundaryRegular_charge {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ a : ℂ, ThetaParallelogramBoundaryRegular τ a ∧
      thetaParallelogramIntegral τ a = 2 * Real.pi * I := by
  obtain ⟨a, ha⟩ := exists_thetaParallelogramBoundaryRegular hτ
  exact ⟨a, ha, thetaParallelogramIntegral_eq_two_pi_I hτ ha⟩

end

end GaloisForLFunctions
