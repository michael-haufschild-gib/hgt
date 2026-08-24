import GaloisForLFunctions.HTGeometry.CayleyGeneralizedSchurCongruence
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeAdjointFaithfulness
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeBoundary
import GaloisForLFunctions.HTGeometry.KernelNegativeSquareConjugation

open Complex Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unreflected generalized-Schur value kernel. -/
def finiteBlaschkeGeneralizedSchurValueKernel
    (F : DiskMultiplier) (B : FiniteBlaschke) (z w : ℂ) : ℂ :=
  diskGeneralizedSchurValueKernel
    (B.fn z) (B.fn w) (F.fn z) (F.fn w) z w

theorem finiteBlaschkeGeneralizedSchurValueKernel_eq_conj_realization
    (F : DiskMultiplier) (B : FiniteBlaschke) {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    finiteBlaschkeGeneralizedSchurValueKernel F B z w =
      (starRingEnd ℂ)
        ((finiteBlaschkeGeneralizedSchurRealization F B).kernel
          ((starRingEnd ℂ) z) ((starRingEnd ℂ) w)) := by
  rw [finiteBlaschkeGeneralizedSchurRealization_kernel_eq F B
    (z := (starRingEnd ℂ) z) (w := (starRingEnd ℂ) w)
    (by simpa using hz) (by simpa using hw)]
  rw [finiteBlaschkeGeneralizedSchurValueKernel,
    finiteBlaschkeGeneralizedSchurKernel,
    diskGeneralizedSchurValueKernel, reflectedDiskMultiplierValue]
  simp only [FiniteBlaschke.toMultiplier, map_div₀, map_sub, map_mul, map_one]
  simp [reflectedDiskMultiplierValue]

/-- Complex conjugation as an equivalence of any conjugation-invariant node set. -/
def conjugationEquivOn (S : Set ℂ)
    (hS : ∀ z, z ∈ S ↔ (starRingEnd ℂ) z ∈ S) : S ≃ S where
  toFun z := ⟨(starRingEnd ℂ) z, (hS z).mp z.property⟩
  invFun z := ⟨(starRingEnd ℂ) z, by
    apply (hS ((starRingEnd ℂ) z)).mpr
    convert z.property using 1
    simp⟩
  left_inv z := by ext; simp
  right_inv z := by ext; simp

theorem hasFiniteKernelNegativeDimension_valueKernel_iff_realization
    (F : DiskMultiplier) (B : FiniteBlaschke)
    (S : Set ℂ) (hsub : S ⊆ Metric.ball 0 1)
    (hS : ∀ z, z ∈ S ↔ (starRingEnd ℂ) z ∈ S)
    (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : S => finiteBlaschkeGeneralizedSchurValueKernel F B z w) r ↔
      HasFiniteKernelNegativeDimension
        (fun z w : S =>
          (finiteBlaschkeGeneralizedSchurRealization F B).kernel z w) r := by
  let R := finiteBlaschkeGeneralizedSchurRealization F B
  let e : S ≃ S := conjugationEquivOn S hS
  let KC : S → S → ℂ := fun z w =>
    (starRingEnd ℂ) (R.kernel z w)
  have hpoint : (fun z w : S =>
      finiteBlaschkeGeneralizedSchurValueKernel F B z w) =
      fun z w => KC (e z) (e w) := by
    funext z w
    apply finiteBlaschkeGeneralizedSchurValueKernel_eq_conj_realization
    · simpa [Metric.mem_ball, dist_zero_right] using hsub z.property
    · simpa [Metric.mem_ball, dist_zero_right] using hsub w.property
  rw [hpoint]
  have heq := hasFiniteKernelNegativeDimension_diagonal_equiv_iff
    (fun z w : S => KC (e z) (e w)) KC e (fun _ => 1)
      (fun _ => one_ne_zero)
      (by intro z w; simp) r
  rw [heq]
  exact hasFiniteKernelNegativeDimension_conjugate_iff
    (fun z w : S => R.kernel z w) r

/-- Exterior annulus of a finite Blaschke product, avoiding every denominator zero. -/
def FiniteBlaschke.exteriorDisk (B : FiniteBlaschke) : Set ℂ :=
  {z | B.bound < ‖z‖ ∧ ‖z‖ < 1}

theorem FiniteBlaschke.isOpen_exteriorDisk (B : FiniteBlaschke) :
    IsOpen B.exteriorDisk := by
  exact (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem FiniteBlaschke.exteriorDisk_subset_ball (B : FiniteBlaschke) :
    B.exteriorDisk ⊆ Metric.ball 0 1 := by
  intro z hz
  simpa [Metric.mem_ball, dist_zero_right] using hz.2

theorem FiniteBlaschke.exteriorDisk_nonempty (B : FiniteBlaschke) :
    B.exteriorDisk.Nonempty := by
  let r : ℝ := (B.bound + 1) / 2
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith [B.bound_nonneg]
  have hnorm : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  refine ⟨(r : ℂ), ?_⟩
  constructor <;> rw [hnorm] <;> dsimp [r] <;> linarith [B.bound_lt]

theorem FiniteBlaschke.exteriorDisk_conj_mem_iff (B : FiniteBlaschke) (z : ℂ) :
    z ∈ B.exteriorDisk ↔ (starRingEnd ℂ) z ∈ B.exteriorDisk := by
  simp only [FiniteBlaschke.exteriorDisk, Set.mem_setOf_eq, RCLike.norm_conj]

theorem FiniteBlaschke.fn_ne_zero_of_mem_exteriorDisk
    (B : FiniteBlaschke) {z : ℂ} (hz : z ∈ B.exteriorDisk) :
    B.fn z ≠ 0 := by
  intro hzero
  have hnorm : ‖z‖ ≤ 1 := hz.2.le
  have hzeros : ∀ j : Fin B.deg, ‖B.zeros j‖ < 1 := fun j =>
    lt_of_le_of_lt (B.zeros_le j) B.bound_lt
  have hex : ∃ j : Fin B.deg, z = B.zeros j := by
    apply (finBlaschke_eq_zero_iff hzeros hnorm).mp
    simpa [FiniteBlaschke.fn, blaschkeProd, blaschkeFactor] using hzero
  obtain ⟨j, rfl⟩ := hex
  exact (not_lt_of_ge (B.zeros_le j)) hz.1

/-- Exterior annulus as an analytic uniqueness region for the generalized-Schur realization. -/
def finiteBlaschkeExteriorOpenRegion (F : DiskMultiplier) (B : FiniteBlaschke) :
    (finiteBlaschkeGeneralizedSchurRealization F B).toAnalyticTotalSectionFamily.OpenRegion where
  region := B.exteriorDisk
  isOpen_region := B.isOpen_exteriorDisk
  region_subset := B.exteriorDisk_subset_ball
  region_nonempty := B.exteriorDisk_nonempty

theorem finiteBlaschkeGeneralizedSchurValueKernel_exactNegativeSquares
    (F : DiskMultiplier) (B : FiniteBlaschke) (hFbd : F.bd ≤ 1)
    (hzero : ∀ j : Fin B.deg, F.fn (B.zeros j) ≠ 0) :
    HasFiniteKernelNegativeDimension
        (fun z w : Metric.ball (0 : ℂ) 1 =>
          finiteBlaschkeGeneralizedSchurValueKernel F B z w) B.deg ∧
      ∀ r : ℕ,
        HasFiniteKernelNegativeDimension
          (fun z w : Metric.ball (0 : ℂ) 1 =>
            finiteBlaschkeGeneralizedSchurValueKernel F B z w) r →
          r ≤ B.deg := by
  have hexact := finiteBlaschkeGeneralizedSchurKernel_exactNegativeSquares_of_nonzero
    F B hFbd hzero
  constructor
  · rw [hasFiniteKernelNegativeDimension_valueKernel_iff_realization
      F B (Metric.ball 0 1) (fun _ h => h)
      (fun z => by simp [Metric.mem_ball, dist_zero_right])]
    exact (hasFiniteGramNegativeDimensionOn_iff_kernel
      (finiteBlaschkeGeneralizedSchurRealization F B) (Metric.ball 0 1) B.deg).mp
      hexact.1
  · intro r hr
    apply hexact.2 r
    apply (hasFiniteGramNegativeDimensionOn_iff_kernel
      (finiteBlaschkeGeneralizedSchurRealization F B) (Metric.ball 0 1) r).mpr
    exact (hasFiniteKernelNegativeDimension_valueKernel_iff_realization
      F B (Metric.ball 0 1) (fun _ h => h)
      (fun z => by simp [Metric.mem_ball, dist_zero_right]) r).mp hr

theorem finiteBlaschkeGeneralizedSchurValueKernel_hasExteriorNegativeDimension
    (F : DiskMultiplier) (B : FiniteBlaschke)
    (hzero : ∀ j : Fin B.deg, F.fn (B.zeros j) ≠ 0) :
    HasFiniteKernelNegativeDimension
      (fun z w : B.exteriorDisk =>
        finiteBlaschkeGeneralizedSchurValueKernel F B z w) B.deg := by
  have hglobal := finiteBlaschkeGeneralizedSchur_hasFiniteGramNegativeDimension_of_nonzero
    F B hzero
  let R := finiteBlaschkeGeneralizedSchurRealization F B
  let V := finiteBlaschkeExteriorOpenRegion F B
  have hext : R.HasFiniteGramNegativeDimensionOn B.exteriorDisk B.deg :=
    (R.hasFiniteGramNegativeDimensionOn_openRegion_iff V B.deg).mpr hglobal
  have hraw := (hasFiniteGramNegativeDimensionOn_iff_kernel
    R B.exteriorDisk B.deg).mp hext
  exact (hasFiniteKernelNegativeDimension_valueKernel_iff_realization
    F B B.exteriorDisk B.exteriorDisk_subset_ball
      B.exteriorDisk_conj_mem_iff B.deg).mpr hraw

end

end GaloisForLFunctions.HTGeometry
