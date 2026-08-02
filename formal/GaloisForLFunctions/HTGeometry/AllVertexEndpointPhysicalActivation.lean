import GaloisForLFunctions.HTGeometry.AllVertexEndpointSimultaneousResponse
import GaloisForLFunctions.HTGeometry.AffineEigenbranchDiagonalProbeLaw
import GaloisForLFunctions.HTGeometry.HermitianLocalSpectralObserverLaw

/-!
# Simultaneous physical activation of all old-observer endpoint channels

The polynomial response law supplies one collision-free real layer shift
where every prescribed two-step response is nonzero.  This file pulls the
simple eigenvalue branches back to the one-parameter affine Hamiltonian and
shows that the same physical edge-coupling direction has nonzero first
derivative in every observer channel.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite simple diagonal spectrum admits simultaneous analytic labelled
eigenbranches along every one-parameter affine matrix direction. -/
theorem exists_all_affineMatrixEigenbranches
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy : I → ℂ) (hinj : Function.Injective energy)
    (V : Matrix I I ℂ) :
    ∃ branch : I → ℂ → ℂ,
      (∀ x, AnalyticAt ℂ (branch x) 0) ∧
      (∀ x, branch x 0 = energy x) ∧
      ∀ x,
        ∀ᶠ g in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal energy + g • V, branch x g) = 0 := by
  have hone :
      ∀ x : I,
        ∃ branch : ℂ → ℂ,
          AnalyticAt ℂ branch 0 ∧
          branch 0 = energy x ∧
          ∀ᶠ g in 𝓝 0,
            matrixCharpolyRelation
              (Matrix.diagonal energy + g • V, branch g) = 0 := by
    intro x
    let H : ℂ → Matrix I I ℂ :=
      fun g => Matrix.diagonal energy + g • V
    have hH : AnalyticAt ℂ
        (fun g : ℂ => fun i : I => fun j : I =>
          Matrix.diagonal energy i j + g * V i j) 0 := by
      apply AnalyticAt.pi
      intro i
      apply AnalyticAt.pi
      intro j
      fun_prop
    have hbase : H 0 = Matrix.diagonal energy := by
      simp [H]
    simpa only [H] using
      analyticMatrixFamily_eigenvalueBranch
        (H := H) hH energy hinj hbase x
  choose branch hanalytic hbase hroot using hone
  exact ⟨branch, hanalytic, hbase, hroot⟩

/-- **One-shift, one-direction all-observer activation law.**  For every
finite family of two-step old-observer channels, one nonnegative integer
onsite shift and one common two-layer coupling direction admit labelled
analytic eigenbranches whose cross-layer transition derivatives are
simultaneously nonzero.

The attachment matrix is shared by every channel.  No unselected attachment
or observer entry is constrained. -/
theorem
    exists_natCast_all_twoLayerCrossMatrixProbe_deriv_ne_zero
    {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (attachment : Matrix I I ℂ)
    (observer : J → Matrix I I ℂ)
    (a g b : J → I)
    (hag : ∀ q, a q ≠ g q)
    (hgb : ∀ q, g q ≠ b q)
    (hattachmentSymm :
      ∀ x y, attachment x y = attachment y x)
    (hattachment : ∀ q, attachment (a q) (g q) ≠ 0)
    (hobserver : ∀ q, observer q (g q) (b q) ≠ 0) :
    ∃ n : ℕ, ∃ branch : I × Bool → ℂ → ℂ,
      (n : ℂ) ∉
          twoLayerForbiddenShift (fun i => (energy i : ℂ)) ∧
      (∀ x, AnalyticAt ℂ (branch x) 0) ∧
      (∀ x,
        branch x 0 =
          twoLayerEnergy (fun i => (energy i : ℂ)) n x) ∧
      (∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal
                (twoLayerEnergy
                  (fun i => (energy i : ℂ)) n) +
              t • twoLayerCoupling attachment,
              branch x t) = 0) ∧
      ∀ q,
        deriv
            (affineEigenbranchMatrixProbe
              (twoLayerEnergy
                (fun i => (energy i : ℂ)) n)
              (twoLayerCoupling attachment)
              (branch (a q, false))
              (branch (b q, true))
              (layerMatrixCoupling (observer q)
                (1 : Matrix Bool Bool ℂ))
              (a q, false) (b q, true)) 0 ≠ 0 := by
  have hinjR : Function.Injective energy :=
    maximallyProjectiveEnergy_injective energy hmax
  have hinjC :
      Function.Injective (fun i => (energy i : ℂ)) := by
    intro x y hxy
    exact hinjR (Complex.ofReal_injective hxy)
  obtain ⟨n, hnForbidden, _hnPole, hnResponse⟩ :=
    exists_natCast_all_twoStepEndpointPacketResponses_ne_zero
      energy hmax (fun _ : J => attachment) observer
      a g b hag hgb hattachment hobserver
  have hinjTwo :
      Function.Injective
        (twoLayerEnergy (fun i => (energy i : ℂ)) n) :=
    twoLayerEnergy_injective_of_not_forbidden
      (fun i => (energy i : ℂ)) hinjC hnForbidden
  obtain ⟨branch, hbranchAnalytic, hbranchBase, hbranchRoot⟩ :=
    exists_all_affineMatrixEigenbranches
      (twoLayerEnergy (fun i => (energy i : ℂ)) n)
      hinjTwo (twoLayerCoupling attachment)
  refine ⟨n, branch, hnForbidden, hbranchAnalytic,
    hbranchBase, hbranchRoot, ?_⟩
  intro q
  have hpacket :
      (∑ d,
          attachment (a q) d * observer q d (b q) /
            ((n : ℂ) + energy (a q) - energy d)) +
        ∑ d,
          observer q (a q) d * attachment d (b q) /
            (-(n : ℂ) + energy (b q) - energy d) ≠ 0 := by
    rw [← twoStepEndpointPacketResponse_eq]
    exact hnResponse q
  exact
    twoLayerCrossMatrixProbe_deriv_ne_zero_of_twoStepSums
      (fun i => (energy i : ℂ)) hinjC hnForbidden
      attachment (observer q) hattachmentSymm
      (a q) (b q)
      (branch (a q, false)) (branch (b q, true))
      (hbranchAnalytic (a q, false))
      (hbranchAnalytic (b q, true))
      (by simpa using hbranchBase (a q, false))
      (by simpa using hbranchBase (b q, true))
      (hbranchRoot (a q, false))
      (hbranchRoot (b q, true))
      hpacket

/-- The simultaneous nonzero derivatives activate all prescribed bilinear
transition amplitudes throughout one common punctured interval of real edge
couplings.  Thus no observer receives a separately tuned coupling. -/
theorem
    exists_eventually_all_twoLayerCrossMatrixProbes_ne_zero
    {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (attachment : Matrix I I ℂ)
    (observer : J → Matrix I I ℂ)
    (a g b : J → I)
    (hag : ∀ q, a q ≠ g q)
    (hgb : ∀ q, g q ≠ b q)
    (hattachmentSymm :
      ∀ x y, attachment x y = attachment y x)
    (hattachment : ∀ q, attachment (a q) (g q) ≠ 0)
    (hobserver : ∀ q, observer q (g q) (b q) ≠ 0) :
    ∃ n : ℕ, ∃ branch : I × Bool → ℂ → ℂ,
      (n : ℂ) ∉
          twoLayerForbiddenShift (fun i => (energy i : ℂ)) ∧
      (∀ x, AnalyticAt ℂ (branch x) 0) ∧
      (∀ x,
        branch x 0 =
          twoLayerEnergy (fun i => (energy i : ℂ)) n x) ∧
      (∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal
                (twoLayerEnergy
                  (fun i => (energy i : ℂ)) n) +
              t • twoLayerCoupling attachment,
              branch x t) = 0) ∧
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ q,
        affineEigenbranchMatrixProbe
          (twoLayerEnergy
            (fun i => (energy i : ℂ)) n)
          (twoLayerCoupling attachment)
          (branch (a q, false))
          (branch (b q, true))
          (layerMatrixCoupling (observer q)
            (1 : Matrix Bool Bool ℂ))
          (a q, false) (b q, true) t ≠ 0 := by
  obtain ⟨n, branch, hnForbidden, hbranchAnalytic,
      hbranchBase, hbranchRoot, hderiv⟩ :=
    exists_natCast_all_twoLayerCrossMatrixProbe_deriv_ne_zero
      energy hmax attachment observer a g b hag hgb
      hattachmentSymm hattachment hobserver
  refine ⟨n, branch, hnForbidden, hbranchAnalytic,
    hbranchBase, hbranchRoot, ?_⟩
  apply Filter.eventually_all.mpr
  intro q
  apply
    eventually_affineEigenbranchMatrixProbe_ne_zero_of_deriv
      (twoLayerEnergy (fun i => (energy i : ℂ)) n)
      (twoLayerCoupling attachment)
      (branch (a q, false))
      (branch (b q, true))
      (layerMatrixCoupling (observer q)
        (1 : Matrix Bool Bool ℂ))
      (a q, false) (b q, true)
      (hbranchAnalytic (a q, false))
      (hbranchAnalytic (b q, true))
      (hbranchBase (a q, false))
      (hbranchBase (b q, true))
      (by simp [layerMatrixCoupling])
      (hderiv q)

/-- A real-symmetric old-system attachment induces a Hermitian two-layer
coupling. -/
theorem twoLayerCoupling_isHermitian_of_real_symmetric
    {I : Type*}
    (attachment : Matrix I I ℂ)
    (hsymm : ∀ x y, attachment x y = attachment y x)
    (hreal :
      ∀ x y,
        (starRingEnd ℂ) (attachment x y) = attachment x y) :
    (twoLayerCoupling attachment).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  rcases x with ⟨x, r⟩
  rcases y with ⟨y, s⟩
  simp only [Matrix.conjTranspose_apply]
  by_cases hrs : r = s
  · subst s
    simp [twoLayerCoupling]
  · have hsr : s ≠ r := Ne.symm hrs
    simp [twoLayerCoupling, hrs, hsr, hreal, hsymm]

/-- Every real point of the common two-layer affine family is a physical
Hermitian Hamiltonian. -/
theorem twoLayerAffineMatrix_isHermitian_real
    {I : Type*} [DecidableEq I]
    (energy : I → ℝ) (z t : ℝ)
    (attachment : Matrix I I ℂ)
    (hsymm : ∀ x y, attachment x y = attachment y x)
    (hreal :
      ∀ x y,
        (starRingEnd ℂ) (attachment x y) = attachment x y) :
    (Matrix.diagonal
        (twoLayerEnergy
          (fun i => (energy i : ℂ)) (z : ℂ)) +
      (t : ℂ) • twoLayerCoupling attachment).IsHermitian := by
  apply Matrix.IsHermitian.add
  · rw [Matrix.isHermitian_diagonal_iff]
    rintro ⟨i, r⟩
    rw [isSelfAdjoint_iff]
    cases r <;> simp [twoLayerEnergy]
  · exact
      (twoLayerCoupling_isHermitian_of_real_symmetric
        attachment hsymm hreal).smul
        (by rw [isSelfAdjoint_iff]; simp)

/-- Characteristic-root branches of the common real-symmetric affine family
are simultaneously real on one real neighborhood of the uncoupled point. -/
theorem eventually_all_twoLayerEigenbranches_real
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (z : ℝ)
    (attachment : Matrix I I ℂ)
    (hsymm : ∀ x y, attachment x y = attachment y x)
    (hreal :
      ∀ x y,
        (starRingEnd ℂ) (attachment x y) = attachment x y)
    (branch : I × Bool → ℂ → ℂ)
    (hroot :
      ∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal
                (twoLayerEnergy
                  (fun i => (energy i : ℂ)) (z : ℂ)) +
              t • twoLayerCoupling attachment,
              branch x t) = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
      (starRingEnd ℂ) (branch x t) = branch x t := by
  have hc :
      Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero] using
      Complex.continuous_ofReal.tendsto (0 : ℝ)
  apply Filter.eventually_all.mpr
  intro x
  filter_upwards [hc.eventually (hroot x)] with t ht
  have him :
      (branch x (t : ℂ)).im = 0 :=
    matrixCharpolyRelation_im_eq_zero_of_isHermitian
      _
      (twoLayerAffineMatrix_isHermitian_real
        energy z t attachment hsymm hreal)
      _ ht
  apply Complex.ext
  · simp
  · simp [him]

/-- **Physical all-observer activation law.**  On a real-symmetric
Hamiltonian slice, one real onsite shift and one shared real edge-coupling
interval make every prescribed physical sesquilinear old-observer
transition nonzero simultaneously. -/
theorem
    exists_eventually_all_twoLayerCrossSesquilinearProbes_ne_zero
    {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (attachment : Matrix I I ℂ)
    (observer : J → Matrix I I ℂ)
    (a g b : J → I)
    (hag : ∀ q, a q ≠ g q)
    (hgb : ∀ q, g q ≠ b q)
    (hattachmentSymm :
      ∀ x y, attachment x y = attachment y x)
    (hattachmentReal :
      ∀ x y,
        (starRingEnd ℂ) (attachment x y) = attachment x y)
    (hattachment : ∀ q, attachment (a q) (g q) ≠ 0)
    (hobserver : ∀ q, observer q (g q) (b q) ≠ 0) :
    ∃ n : ℕ, ∃ branch : I × Bool → ℂ → ℂ,
      (n : ℂ) ∉
          twoLayerForbiddenShift (fun i => (energy i : ℂ)) ∧
      (∀ x, AnalyticAt ℂ (branch x) 0) ∧
      (∀ x,
        branch x 0 =
          twoLayerEnergy (fun i => (energy i : ℂ)) n x) ∧
      (∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal
                (twoLayerEnergy
                  (fun i => (energy i : ℂ)) n) +
              t • twoLayerCoupling attachment,
              branch x t) = 0) ∧
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ q,
        affineEigenbranchSesquilinearMatrixProbe
          (twoLayerEnergy
            (fun i => (energy i : ℂ)) n)
          (twoLayerCoupling attachment)
          (branch (a q, false))
          (branch (b q, true))
          (layerMatrixCoupling (observer q)
            (1 : Matrix Bool Bool ℂ))
          (a q, false) (b q, true) t ≠ 0 := by
  obtain ⟨n, branch, hnForbidden, hbranchAnalytic,
      hbranchBase, hbranchRoot, hbilinear⟩ :=
    exists_eventually_all_twoLayerCrossMatrixProbes_ne_zero
      energy hmax attachment observer a g b hag hgb
      hattachmentSymm hattachment hobserver
  refine ⟨n, branch, hnForbidden, hbranchAnalytic,
    hbranchBase, hbranchRoot, ?_⟩
  have hbranchReal :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    eventually_all_twoLayerEigenbranches_real
      energy n attachment hattachmentSymm hattachmentReal
      branch hbranchRoot
  have hbranchRealPunctured :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    Filter.Eventually.filter_mono inf_le_left hbranchReal
  filter_upwards [hbilinear, hbranchRealPunctured] with t ht hreal
  intro q
  rw [
    affineEigenbranchSesquilinearMatrixProbe_eq_bilinear_of_left_real
      (twoLayerEnergy (fun i => (energy i : ℂ)) n)
      (twoLayerCoupling attachment)
      (branch (a q, false))
      (branch (b q, true))
      (layerMatrixCoupling (observer q)
        (1 : Matrix Bool Bool ℂ))
      (a q, false) (b q, true) t]
  · exact ht q
  · intro i
    apply star_affineEigenbranchAdjugateColumn_eq
    · rintro ⟨k, r⟩
      cases r <;> simp [twoLayerEnergy]
    · rintro ⟨k, r⟩ ⟨l, s⟩
      by_cases hrs : r = s
      · subst s
        simp [twoLayerCoupling]
      · simp [twoLayerCoupling, hrs, hattachmentReal]
    · exact hreal (a q, false)
    · simp

end

end GaloisForLFunctions.HTGeometry
