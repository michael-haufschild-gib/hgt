import GaloisForLFunctions.HTGeometry.GeneralizedSchurKernelRankProfile
import GaloisForLFunctions.HTGeometry.KernelNegativeSquareConjugation
import GaloisForLFunctions.HTGeometry.CayleyGeneralizedSchurCongruence

/-!
# Arbitrary-inner generalized-Schur value-kernel rank profile

This module transfers the reflected Hardy realization to the unreflected value orientation used
by Cayley transport. It also proves that every nonempty open disk region retains the complete
finite negative-dimension profile.
-/

open Complex Set Metric
open scoped InnerProductSpace ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unreflected generalized-Schur value kernel for arbitrary disk multipliers. -/
def generalizedSchurValueKernel
    (F B : DiskMultiplier) (z w : ℂ) : ℂ :=
  diskGeneralizedSchurValueKernel
    (B.fn z) (B.fn w) (F.fn z) (F.fn w) z w

/-- Schwarz-conjugate image of a complex node set, written as a preimage so openness is direct. -/
def conjugatedNodeSet (S : Set ℂ) : Set ℂ :=
  (starRingEnd ℂ) ⁻¹' S

/-- Complex conjugation identifies a node set with its Schwarz-conjugate image. -/
def conjugationEquivConjugatedNodeSet (S : Set ℂ) :
    S ≃ conjugatedNodeSet S where
  toFun z := ⟨(starRingEnd ℂ) z.1, by
    change (starRingEnd ℂ) ((starRingEnd ℂ) z.1) ∈ S
    have hstar : (starRingEnd ℂ) ((starRingEnd ℂ) z.1) = z.1 := by simp
    rw [hstar]
    exact z.2⟩
  invFun z := ⟨(starRingEnd ℂ) z.1, z.2⟩
  left_inv z := by ext; simp
  right_inv z := by ext; simp

/-- The unreflected value kernel is the conjugate of the analytic reflected kernel at conjugated
nodes. -/
theorem generalizedSchurValueKernel_eq_conj_realization
    (F B : DiskMultiplier) {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    generalizedSchurValueKernel F B z w =
      (starRingEnd ℂ)
        ((generalizedSchurRealization F B).kernel
          ((starRingEnd ℂ) z) ((starRingEnd ℂ) w)) := by
  rw [generalizedSchurRealization_kernel_eq F B
    (z := (starRingEnd ℂ) z) (w := (starRingEnd ℂ) w)
    (by simpa using hz) (by simpa using hw)]
  rw [generalizedSchurValueKernel, generalizedSchurKernel,
    diskGeneralizedSchurValueKernel, reflectedDiskMultiplierValue]
  simp only [map_div₀, map_sub, map_mul, map_one]
  simp [reflectedDiskMultiplierValue]

/-- On any disk node set, the unreflected value kernel and the analytic realization on the
conjugated node set have identical finite negative dimensions. -/
theorem hasFiniteKernelNegativeDimension_generalizedSchurValueKernel_iff_realization
    (F B : DiskMultiplier) (S : Set ℂ)
    (hsub : S ⊆ Metric.ball 0 1) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : S => generalizedSchurValueKernel F B z.1 w.1) r ↔
      HasFiniteKernelNegativeDimension
        (fun z w : conjugatedNodeSet S =>
          (generalizedSchurRealization F B).kernel z.1 w.1) r := by
  let R := generalizedSchurRealization F B
  let e : S ≃ conjugatedNodeSet S := conjugationEquivConjugatedNodeSet S
  let KC : conjugatedNodeSet S → conjugatedNodeSet S → ℂ :=
    fun z w => (starRingEnd ℂ) (R.kernel z.1 w.1)
  have hpoint : (fun z w : S => generalizedSchurValueKernel F B z.1 w.1) =
      fun z w => KC (e z) (e w) := by
    funext z w
    apply generalizedSchurValueKernel_eq_conj_realization
    · have hz : dist z.1 0 < 1 := hsub z.2
      simpa [dist_zero_right] using hz
    · have hw : dist w.1 0 < 1 := hsub w.2
      simpa [dist_zero_right] using hw
  rw [hpoint]
  have heq := hasFiniteKernelNegativeDimension_diagonal_equiv_iff
    (fun z w : S => KC (e z) (e w)) KC e (fun _ => 1)
      (fun _ => one_ne_zero) (by intro z w; simp) r
  rw [heq]
  exact hasFiniteKernelNegativeDimension_conjugate_iff
    (fun z w : conjugatedNodeSet S => R.kernel z.1 w.1) r

/-- Restricting an arbitrary generalized-Schur value kernel to any nonempty open disk region
preserves every finite negative dimension. -/
theorem generalizedSchurValueKernel_openRegion_negativeDimension_iff
    (F B : DiskMultiplier) (V : Set ℂ) (hopen : IsOpen V)
    (hsub : V ⊆ Metric.ball 0 1) (hne : V.Nonempty) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : V => generalizedSchurValueKernel F B z.1 w.1) r ↔
      HasFiniteKernelNegativeDimension
        (fun z w : Metric.ball (0 : ℂ) 1 =>
          generalizedSchurValueKernel F B z.1 w.1) r := by
  let R := generalizedSchurRealization F B
  have hopenC : IsOpen (conjugatedNodeSet V) := by
    exact hopen.preimage Complex.continuous_conj
  have hsubC : conjugatedNodeSet V ⊆ R.domain := by
    intro z hz
    have hzV : (starRingEnd ℂ) z ∈ V := by
      exact hz
    have hzball := hsub hzV
    change z ∈ Metric.ball (0 : ℂ) 1
    simpa [Metric.mem_ball, dist_zero_right] using hzball
  have hneC : (conjugatedNodeSet V).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨(starRingEnd ℂ) z, by simpa [conjugatedNodeSet] using hz⟩
  let O : R.toAnalyticTotalSectionFamily.OpenRegion := {
    region := conjugatedNodeSet V
    isOpen_region := hopenC
    region_subset := hsubC
    region_nonempty := hneC }
  have hloc := R.hasFiniteGramNegativeDimensionOn_openRegion_iff O r
  rw [hasFiniteGramNegativeDimensionOn_iff_kernel,
    hasFiniteGramNegativeDimensionOn_iff_kernel] at hloc
  change HasFiniteKernelNegativeDimension
      (fun z w : conjugatedNodeSet V => R.kernel z.1 w.1) r ↔
    HasFiniteKernelNegativeDimension
      (fun z w : Metric.ball (0 : ℂ) 1 => R.kernel z.1 w.1) r at hloc
  have hV := hasFiniteKernelNegativeDimension_generalizedSchurValueKernel_iff_realization
    F B V hsub r
  have hball := hasFiniteKernelNegativeDimension_generalizedSchurValueKernel_iff_realization
    F B (Metric.ball (0 : ℂ) 1) (fun _ h => h) r
  rw [hV, hball]
  let e : conjugatedNodeSet (Metric.ball (0 : ℂ) 1) ≃
      Metric.ball (0 : ℂ) 1 := {
    toFun := fun z => ⟨z.1, by
      have hz := z.property
      change (starRingEnd ℂ) z.val ∈ Metric.ball (0 : ℂ) 1 at hz
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      simpa only [RCLike.norm_conj] using hz⟩
    invFun := fun z => ⟨z.1, by
      have hz := z.property
      rw [Metric.mem_ball, dist_zero_right] at hz
      change (starRingEnd ℂ) z.val ∈ Metric.ball (0 : ℂ) 1
      rw [Metric.mem_ball, dist_zero_right]
      simpa only [RCLike.norm_conj] using hz⟩
    left_inv := fun z => rfl
    right_inv := fun z => rfl }
  have heq := hasFiniteKernelNegativeDimension_diagonal_equiv_iff
    (fun z w : conjugatedNodeSet (Metric.ball (0 : ℂ) 1) => R.kernel z.1 w.1)
    (fun z w : Metric.ball (0 : ℂ) 1 => R.kernel z.1 w.1)
    e (fun _ => 1) (fun _ => one_ne_zero) (by intro z w; simp [e]) r
  exact hloc.trans heq.symm

/-- Exact arbitrary-rank profile of the unreflected generalized-Schur value kernel. -/
theorem generalizedSchurValueKernel_negativeDimension_iff_rankAtLeast
    (F B : DiskMultiplier) (hF : F.bd ≤ 1)
    (hB : HardyMultiplierIsometry B) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : Metric.ball (0 : ℂ) 1 =>
          generalizedSchurValueKernel F B z.1 w.1) r ↔
      RestrictedAdjointRankAtLeast
        (hardyMultiplierModelSpace B) (hardyMul F) r := by
  have hvalue := hasFiniteKernelNegativeDimension_generalizedSchurValueKernel_iff_realization
    F B (Metric.ball (0 : ℂ) 1) (fun _ h => h) r
  rw [hvalue]
  have hkernel : (fun z w : conjugatedNodeSet (Metric.ball (0 : ℂ) 1) =>
      (generalizedSchurRealization F B).kernel z.1 w.1) =
      fun z w => generalizedSchurKernel F B z.1 w.1 := by
    funext z w
    apply generalizedSchurRealization_kernel_eq
    · have hz := z.property
      change (starRingEnd ℂ) z.val ∈ Metric.ball (0 : ℂ) 1 at hz
      rw [Metric.mem_ball, dist_zero_right] at hz
      simpa only [RCLike.norm_conj] using hz
    · have hw := w.property
      change (starRingEnd ℂ) w.val ∈ Metric.ball (0 : ℂ) 1 at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      simpa only [RCLike.norm_conj] using hw
  rw [hkernel]
  let e : conjugatedNodeSet (Metric.ball (0 : ℂ) 1) ≃
      Metric.ball (0 : ℂ) 1 := {
    toFun := fun z => ⟨z.1, by
      have hz := z.property
      change (starRingEnd ℂ) z.val ∈ Metric.ball (0 : ℂ) 1 at hz
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      simpa only [RCLike.norm_conj] using hz⟩
    invFun := fun z => ⟨z.1, by
      have hz := z.property
      rw [Metric.mem_ball, dist_zero_right] at hz
      change (starRingEnd ℂ) z.val ∈ Metric.ball (0 : ℂ) 1
      rw [Metric.mem_ball, dist_zero_right]
      simpa only [RCLike.norm_conj] using hz⟩
    left_inv := fun z => rfl
    right_inv := fun z => rfl }
  rw [hasFiniteKernelNegativeDimension_diagonal_equiv_iff
    (fun z w : conjugatedNodeSet (Metric.ball (0 : ℂ) 1) =>
      generalizedSchurKernel F B z.1 w.1)
    (fun z w : Metric.ball (0 : ℂ) 1 =>
      generalizedSchurKernel F B z.1 w.1)
    e (fun _ => 1) (fun _ => one_ne_zero) (by intro z w; simp [e]) r]
  exact generalizedSchurKernel_negativeDimension_iff_rankAtLeast F B hF hB r

end

end GaloisForLFunctions.HTGeometry
