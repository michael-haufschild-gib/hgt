import GaloisForLFunctions.HTGeometry.HermitianEigenbranchProbeResponse
import GaloisForLFunctions.HTGeometry.AllLayerEndpointPhysicalActivation

/-!
# Hermitian arbitrary-alphabet endpoint activation

The adjugate row--column response specializes to the anchor-star local
extension without any entrywise-reality or symmetry premise on the old
attachment channel.  A Hermitian attachment is enough on the physical real
coupling line.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Hermitian arbitrary-alphabet first-order endpoint law.**  The physical
row--column derivative sees exactly the two-step response packet for an
arbitrary oriented old attachment matrix. -/
theorem allLayerCrossRowColumnProbe_deriv_eq_twoStepSums
    {I ρ : Type*} [Fintype I] [DecidableEq I]
    [Fintype ρ] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (hinj : Function.Injective (layeredEnergy energy shift))
    (attachment observer : Matrix I I ℂ)
    {anchor layer : ρ} (hlayer : layer ≠ anchor)
    (a b : I)
    (branchX branchY : ℂ → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbaseX :
      branchX 0 = layeredEnergy energy shift (a, layer))
    (hbaseY :
      branchY 0 = layeredEnergy energy shift (b, anchor))
    (hrootX :
      ∀ᶠ t in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal (layeredEnergy energy shift) +
            t • layerMatrixCoupling attachment
              (anchorStarLayerEdge anchor),
            branchX t) = 0)
    (hrootY :
      ∀ᶠ t in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal (layeredEnergy energy shift) +
            t • layerMatrixCoupling attachment
              (anchorStarLayerEdge anchor),
            branchY t) = 0) :
    deriv
        (affineEigenbranchRowColumnMatrixProbe
          (layeredEnergy energy shift)
          (layerMatrixCoupling attachment
            (anchorStarLayerEdge anchor))
          branchX branchY
          (layerMatrixCoupling observer
            (1 : Matrix ρ ρ ℂ))
          (a, layer) (b, anchor)) 0 =
      ((∏ k ∈ Finset.univ.erase (a, layer),
          (layeredEnergy energy shift (a, layer) -
            layeredEnergy energy shift k)) *
        (∏ k ∈ Finset.univ.erase (b, anchor),
          (layeredEnergy energy shift (b, anchor) -
            layeredEnergy energy shift k))) *
        ((∑ d,
            attachment a d * observer d b /
              ((shift layer - shift anchor) +
                energy a - energy d)) +
          ∑ d,
            observer a d * attachment d b /
              (-(shift layer - shift anchor) +
                energy b - energy d)) := by
  have hOxy :
      layerMatrixCoupling observer (1 : Matrix ρ ρ ℂ)
          (a, layer) (b, anchor) = 0 := by
    simp [layerMatrixCoupling, hlayer]
  have hformula :=
    affineEigenbranchRowColumnMatrixProbe_deriv_eq_gapPackets
      (layeredEnergy energy shift) hinj
      (layerMatrixCoupling attachment
        (anchorStarLayerEdge anchor))
      (a, layer) (b, anchor)
      branchX branchY hbranchX hbranchY
      hbaseX hbaseY hrootX hrootY
      (layerMatrixCoupling observer
        (1 : Matrix ρ ρ ℂ))
      hOxy
  have hfirst :
      (∑ i : I × ρ,
          layerMatrixCoupling attachment
                (anchorStarLayerEdge anchor) (a, layer) i *
              layerMatrixCoupling observer
                (1 : Matrix ρ ρ ℂ) i (b, anchor) /
            (layeredEnergy energy shift (a, layer) -
              layeredEnergy energy shift i)) =
        ∑ d,
          attachment a d * observer d b /
            ((shift layer - shift anchor) +
              energy a - energy d) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_eq_single anchor]
    · simp [layerMatrixCoupling, anchorStarLayerEdge,
        layeredEnergy, hlayer]
      congr 1
      ring
    · intro r hr hra
      simp [layerMatrixCoupling, hra]
    · exact fun ha => absurd (Finset.mem_univ anchor) ha
  have hsecond :
      (∑ j : I × ρ,
          layerMatrixCoupling observer
                (1 : Matrix ρ ρ ℂ) (a, layer) j *
              layerMatrixCoupling attachment
                (anchorStarLayerEdge anchor) j (b, anchor) /
            (layeredEnergy energy shift (b, anchor) -
              layeredEnergy energy shift j)) =
        ∑ d,
          observer a d * attachment d b /
            (-(shift layer - shift anchor) +
              energy b - energy d) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_eq_single layer]
    · simp [layerMatrixCoupling, anchorStarLayerEdge,
        layeredEnergy, hlayer]
      congr 1
      ring
    · intro r hr hrl
      have hlr : layer ≠ r := Ne.symm hrl
      simp [layerMatrixCoupling, hlr]
    · exact fun ha => absurd (Finset.mem_univ layer) ha
  rw [hfirst, hsecond] at hformula
  exact hformula

/-- A nonzero two-step packet gives a nonzero physical row--column
derivative without a real-symmetry premise. -/
theorem allLayerCrossRowColumnProbe_deriv_ne_zero_of_twoStepSums
    {I ρ : Type*} [Fintype I] [DecidableEq I]
    [Fintype ρ] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (hinj : Function.Injective (layeredEnergy energy shift))
    (attachment observer : Matrix I I ℂ)
    {anchor layer : ρ} (hlayer : layer ≠ anchor)
    (a b : I)
    (branchX branchY : ℂ → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbaseX :
      branchX 0 = layeredEnergy energy shift (a, layer))
    (hbaseY :
      branchY 0 = layeredEnergy energy shift (b, anchor))
    (hrootX :
      ∀ᶠ t in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal (layeredEnergy energy shift) +
            t • layerMatrixCoupling attachment
              (anchorStarLayerEdge anchor),
            branchX t) = 0)
    (hrootY :
      ∀ᶠ t in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal (layeredEnergy energy shift) +
            t • layerMatrixCoupling attachment
              (anchorStarLayerEdge anchor),
            branchY t) = 0)
    (hpacket :
      (∑ d,
          attachment a d * observer d b /
            ((shift layer - shift anchor) +
              energy a - energy d)) +
        ∑ d,
          observer a d * attachment d b /
            (-(shift layer - shift anchor) +
              energy b - energy d) ≠ 0) :
    deriv
        (affineEigenbranchRowColumnMatrixProbe
          (layeredEnergy energy shift)
          (layerMatrixCoupling attachment
            (anchorStarLayerEdge anchor))
          branchX branchY
          (layerMatrixCoupling observer
            (1 : Matrix ρ ρ ℂ))
          (a, layer) (b, anchor)) 0 ≠ 0 := by
  have hPx :
      ∏ k ∈ Finset.univ.erase (a, layer),
          (layeredEnergy energy shift (a, layer) -
            layeredEnergy energy shift k) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hk).1 (hinj heq.symm)
  have hPy :
      ∏ k ∈ Finset.univ.erase (b, anchor),
          (layeredEnergy energy shift (b, anchor) -
            layeredEnergy energy shift k) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hk).1 (hinj heq.symm)
  rw [allLayerCrossRowColumnProbe_deriv_eq_twoStepSums
    energy shift hinj attachment observer
    hlayer a b branchX branchY hbranchX hbranchY
    hbaseX hbaseY hrootX hrootY]
  exact mul_ne_zero (mul_ne_zero hPx hPy) hpacket

/-- One coded onsite vector makes every prescribed Hermitian row--column
cross response have nonzero derivative, with no symmetry assumption on the
old attachment matrix. -/
theorem
    exists_codedShift_allLayerCrossRowColumnProbe_deriv_ne_zero
    {I ρ J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype ρ] [DecidableEq ρ]
    [Fintype J]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (anchor : ρ) (layer : J → ρ)
    (hlayer : ∀ q, layer q ≠ anchor)
    (attachment : Matrix I I ℂ)
    (observer : J → Matrix I I ℂ)
    (a g b : J → I)
    (hag : ∀ q, a q ≠ g q)
    (hgb : ∀ q, g q ≠ b q)
    (hattachment : ∀ q, attachment (a q) (g q) ≠ 0)
    (hobserver : ∀ q, observer q (g q) (b q) ≠ 0) :
    ∃ n : ℕ, ∃ branch : I × ρ → ℂ → ℂ,
      Function.Injective
        (layeredEnergy
          (fun i => (energy i : ℂ))
          (fun r =>
            (codedIntegerLayerShift anchor n r : ℂ))) ∧
      (∀ x, AnalyticAt ℂ (branch x) 0) ∧
      (∀ x,
        branch x 0 =
          layeredEnergy
            (fun i => (energy i : ℂ))
            (fun r =>
              (codedIntegerLayerShift anchor n r : ℂ)) x) ∧
      (∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal
                (layeredEnergy
                  (fun i => (energy i : ℂ))
                  (fun r =>
                    (codedIntegerLayerShift anchor n r : ℂ))) +
              t • layerMatrixCoupling attachment
                (anchorStarLayerEdge anchor),
              branch x t) = 0) ∧
      ∀ q,
        deriv
            (affineEigenbranchRowColumnMatrixProbe
              (layeredEnergy
                (fun i => (energy i : ℂ))
                (fun r =>
                  (codedIntegerLayerShift anchor n r : ℂ)))
              (layerMatrixCoupling attachment
                (anchorStarLayerEdge anchor))
              (branch (a q, layer q))
              (branch (b q, anchor))
              (layerMatrixCoupling (observer q)
                (1 : Matrix ρ ρ ℂ))
              (a q, layer q) (b q, anchor)) 0 ≠ 0 := by
  obtain ⟨n, hinj, hresponse⟩ :=
    exists_codedIntegerLayerShift_all_responses_ne_zero
      energy hmax anchor layer hlayer attachment observer
      a g b hag hgb hattachment hobserver
  letI : Nonempty ρ := ⟨anchor⟩
  let shift : ρ → ℂ :=
    fun r => (codedIntegerLayerShift anchor n r : ℂ)
  let fullEnergy : I × ρ → ℂ :=
    layeredEnergy (fun i => (energy i : ℂ)) shift
  let V : Matrix (I × ρ) (I × ρ) ℂ :=
    layerMatrixCoupling attachment (anchorStarLayerEdge anchor)
  obtain ⟨branch, hbranchAnalytic, hbranchBase, hbranchRoot⟩ :=
    exists_all_affineMatrixEigenbranches fullEnergy hinj V
  refine ⟨n, branch, hinj, hbranchAnalytic,
    hbranchBase, hbranchRoot, ?_⟩
  intro q
  have hpacket :
      (∑ d,
          attachment (a q) d * observer q d (b q) /
            ((shift (layer q) - shift anchor) +
              (energy (a q) : ℂ) - energy d)) +
        ∑ d,
          observer q (a q) d * attachment d (b q) /
            (-(shift (layer q) - shift anchor) +
              (energy (b q) : ℂ) - energy d) ≠ 0 := by
    rw [← twoStepEndpointPacketResponse_eq]
    exact hresponse q
  exact
    allLayerCrossRowColumnProbe_deriv_ne_zero_of_twoStepSums
      (fun i => (energy i : ℂ)) shift hinj
      attachment (observer q)
      (hlayer q) (a q) (b q)
      (branch (a q, layer q)) (branch (b q, anchor))
      (hbranchAnalytic (a q, layer q))
      (hbranchAnalytic (b q, anchor))
      (hbranchBase (a q, layer q))
      (hbranchBase (b q, anchor))
      (hbranchRoot (a q, layer q))
      (hbranchRoot (b q, anchor))
      hpacket

/-- Every real point of an anchor-star family with a Hermitian old
attachment is Hermitian. -/
theorem allLayerStarAffineMatrix_isHermitian_of_isHermitian
    {I ρ : Type*} [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℝ) (shift : ρ → ℝ) (t : ℝ)
    (anchor : ρ)
    (attachment : Matrix I I ℂ)
    (hattachment : attachment.IsHermitian) :
    (Matrix.diagonal
        (layeredEnergy
          (fun i => (energy i : ℂ))
          (fun r => (shift r : ℂ))) +
      (t : ℂ) •
        layerMatrixCoupling attachment
          (anchorStarLayerEdge anchor)).IsHermitian := by
  apply Matrix.IsHermitian.add
  · rw [Matrix.isHermitian_diagonal_iff]
    rintro ⟨i, r⟩
    rw [isSelfAdjoint_iff]
    simp [layeredEnergy]
  · exact
      (layerMatrixCoupling_isHermitian hattachment
        (anchorStarLayerEdge_isHermitian anchor)).smul
        (by rw [isSelfAdjoint_iff]; simp)

/-- The affine characteristic matrix is Hermitian whenever the affine
Hamiltonian and selected spectral value are Hermitian. -/
theorem affineBranchCharacteristicMatrix_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ)
    (branch : ℂ → ℂ) (g : ℂ)
    (hH : (Matrix.diagonal energy + g • V).IsHermitian)
    (hbranch : (starRingEnd ℂ) (branch g) = branch g) :
    (affineBranchCharacteristicMatrix
      energy V branch g).IsHermitian := by
  have hscalar :
      (Matrix.scalar ι (branch g)).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.conjTranspose_apply, Matrix.scalar_apply,
        hbranch]
    · simp [Matrix.conjTranspose_apply, Matrix.scalar_apply,
        hij, Ne.symm hij]
  have heq :
      affineBranchCharacteristicMatrix energy V branch g =
        Matrix.scalar ι (branch g) -
          (Matrix.diagonal energy + g • V) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [affineBranchCharacteristicMatrix, Matrix.scalar_apply]
      ring
    · simp [affineBranchCharacteristicMatrix, Matrix.scalar_apply,
        hij]
  rw [heq]
  exact hscalar.sub hH

/-- Labeled roots of a Hermitian anchor-star family are real on the real
coupling line, without entrywise-reality assumptions. -/
theorem eventually_allLayerStarEigenbranches_real_of_isHermitian
    {I ρ : Type*} [Fintype I] [DecidableEq I]
    [Fintype ρ] [DecidableEq ρ]
    (energy : I → ℝ) (shift : ρ → ℝ)
    (anchor : ρ)
    (attachment : Matrix I I ℂ)
    (hattachment : attachment.IsHermitian)
    (branch : I × ρ → ℂ → ℂ)
    (hroot :
      ∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal
                (layeredEnergy
                  (fun i => (energy i : ℂ))
                  (fun r => (shift r : ℂ))) +
              t • layerMatrixCoupling attachment
                (anchorStarLayerEdge anchor),
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
      (allLayerStarAffineMatrix_isHermitian_of_isHermitian
        energy shift t anchor attachment hattachment)
      _ ht
  apply Complex.ext
  · simp
  · simp [him]

/-- **Hermitian physical arbitrary-alphabet activation law.** For every
finite observer query family, an arbitrary Hermitian old attachment channel
admits one coded onsite vector and one real anchor-star coupling line on
which every prescribed physical bra--ket cross transition is nonzero.

This removes the real-symmetric attachment restriction from old-observer
leaf preservation. -/
theorem
    exists_eventually_allLayerCrossSesquilinearProbes_ne_zero_of_isHermitian
    {I ρ J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype ρ] [DecidableEq ρ]
    [Fintype J]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (anchor : ρ) (layer : J → ρ)
    (hlayer : ∀ q, layer q ≠ anchor)
    (attachment : Matrix I I ℂ)
    (hattachmentHermitian : attachment.IsHermitian)
    (observer : J → Matrix I I ℂ)
    (_hobserverHermitian : ∀ q, (observer q).IsHermitian)
    (a g b : J → I)
    (hag : ∀ q, a q ≠ g q)
    (hgb : ∀ q, g q ≠ b q)
    (hattachment : ∀ q, attachment (a q) (g q) ≠ 0)
    (hobserver : ∀ q, observer q (g q) (b q) ≠ 0) :
    ∃ n : ℕ, ∃ branch : I × ρ → ℂ → ℂ,
      Function.Injective
        (layeredEnergy
          (fun i => (energy i : ℂ))
          (fun r =>
            (codedIntegerLayerShift anchor n r : ℂ))) ∧
      (∀ x, AnalyticAt ℂ (branch x) 0) ∧
      (∀ x,
        branch x 0 =
          layeredEnergy
            (fun i => (energy i : ℂ))
            (fun r =>
              (codedIntegerLayerShift anchor n r : ℂ)) x) ∧
      (∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal
                (layeredEnergy
                  (fun i => (energy i : ℂ))
                  (fun r =>
                    (codedIntegerLayerShift anchor n r : ℂ))) +
              t • layerMatrixCoupling attachment
                (anchorStarLayerEdge anchor),
              branch x t) = 0) ∧
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ q,
        affineEigenbranchSesquilinearMatrixProbe
          (layeredEnergy
            (fun i => (energy i : ℂ))
            (fun r =>
              (codedIntegerLayerShift anchor n r : ℂ)))
          (layerMatrixCoupling attachment
            (anchorStarLayerEdge anchor))
          (branch (a q, layer q))
          (branch (b q, anchor))
          (layerMatrixCoupling (observer q)
            (1 : Matrix ρ ρ ℂ))
          (a q, layer q) (b q, anchor) t ≠ 0 := by
  obtain ⟨n, branch, hinj, hbranchAnalytic,
      hbranchBase, hbranchRoot, hderiv⟩ :=
    exists_codedShift_allLayerCrossRowColumnProbe_deriv_ne_zero
      energy hmax anchor layer hlayer attachment observer
      a g b hag hgb hattachment hobserver
  refine ⟨n, branch, hinj, hbranchAnalytic,
    hbranchBase, hbranchRoot, ?_⟩
  let fullEnergy : I × ρ → ℂ :=
    layeredEnergy
      (fun i => (energy i : ℂ))
      (fun r => (codedIntegerLayerShift anchor n r : ℂ))
  let V : Matrix (I × ρ) (I × ρ) ℂ :=
    layerMatrixCoupling attachment (anchorStarLayerEdge anchor)
  have hrow :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ q,
        affineEigenbranchRowColumnMatrixProbe
          fullEnergy V
          (branch (a q, layer q))
          (branch (b q, anchor))
          (layerMatrixCoupling (observer q)
            (1 : Matrix ρ ρ ℂ))
          (a q, layer q) (b q, anchor) t ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro q
    let f : ℂ → ℂ :=
      affineEigenbranchRowColumnMatrixProbe
        fullEnergy V
        (branch (a q, layer q))
        (branch (b q, anchor))
        (layerMatrixCoupling (observer q)
          (1 : Matrix ρ ρ ℂ))
        (a q, layer q) (b q, anchor)
    have hfan : AnalyticAt ℂ f 0 :=
      analyticAt_affineEigenbranchRowColumnMatrixProbe
        fullEnergy V
        (branch (a q, layer q))
        (branch (b q, anchor))
        (layerMatrixCoupling (observer q)
          (1 : Matrix ρ ρ ℂ))
        (a q, layer q) (b q, anchor)
        (hbranchAnalytic (a q, layer q))
        (hbranchAnalytic (b q, anchor))
    have hf0 : f 0 = 0 := by
      dsimp [f]
      rw [affineEigenbranchRowColumnMatrixProbe_zero
        fullEnergy V
        (branch (a q, layer q))
        (branch (b q, anchor))
        (layerMatrixCoupling (observer q)
          (1 : Matrix ρ ρ ℂ))
        (a q, layer q) (b q, anchor)
        (hbranchBase (a q, layer q))
        (hbranchBase (b q, anchor))]
      simp [layerMatrixCoupling, hlayer q]
    have hev :=
      eventually_real_ne_of_complex_deriv_ne_zero
        f (deriv f 0)
        hfan.differentiableAt.hasDerivAt
        (hderiv q)
    filter_upwards [hev] with t ht
    simpa [hf0] using ht
  have hbranchReal :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    eventually_allLayerStarEigenbranches_real_of_isHermitian
      energy (codedIntegerLayerShift anchor n)
      anchor attachment hattachmentHermitian
      branch hbranchRoot
  have hbranchRealPunctured :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    Filter.Eventually.filter_mono inf_le_left hbranchReal
  filter_upwards [hrow, hbranchRealPunctured] with t ht hreal
  intro q
  rw [
    affineEigenbranchSesquilinearMatrixProbe_eq_rowColumn_of_isHermitian
      fullEnergy V
      (branch (a q, layer q))
      (branch (b q, anchor))
      (layerMatrixCoupling (observer q)
        (1 : Matrix ρ ρ ℂ))
      (a q, layer q) (b q, anchor) t]
  · exact ht q
  · apply affineBranchCharacteristicMatrix_isHermitian
    · simpa [fullEnergy, V] using
        allLayerStarAffineMatrix_isHermitian_of_isHermitian
          energy (codedIntegerLayerShift anchor n) t
          anchor attachment hattachmentHermitian
    · exact hreal (a q, layer q)

/-- Every finite family of nonzero base entries persists for the analytic
row--column probes on the real coupling line. -/
theorem eventually_all_affineRowColumnMatrixProbes_ne_zero_of_base_entries
    {K L : Type*} [Fintype K] [DecidableEq K]
    [Fintype L]
    (energy : K → ℂ) (hinj : Function.Injective energy)
    (V : Matrix K K ℂ)
    (branch : K → ℂ → ℂ)
    (hbranchAnalytic : ∀ x, AnalyticAt ℂ (branch x) 0)
    (hbranchBase : ∀ x, branch x 0 = energy x)
    (probe : L → Matrix K K ℂ)
    (source target : L → K)
    (hentry :
      ∀ l, probe l (source l) (target l) ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ l,
      affineEigenbranchRowColumnMatrixProbe
        energy V
        (branch (source l)) (branch (target l))
        (probe l) (source l) (target l) t ≠ 0 := by
  have hc :
      Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero] using
      Complex.continuous_ofReal.tendsto (0 : ℝ)
  apply Filter.eventually_all.mpr
  intro l
  let f : ℂ → ℂ :=
    affineEigenbranchRowColumnMatrixProbe
      energy V
      (branch (source l)) (branch (target l))
      (probe l) (source l) (target l)
  have hPx :
      ∏ k ∈ Finset.univ.erase (source l),
          (energy (source l) - energy k) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hk).1 (hinj heq.symm)
  have hPy :
      ∏ k ∈ Finset.univ.erase (target l),
          (energy (target l) - energy k) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hk).1 (hinj heq.symm)
  have hf0 : f 0 ≠ 0 := by
    dsimp [f]
    rw [affineEigenbranchRowColumnMatrixProbe_zero
      energy V
      (branch (source l)) (branch (target l))
      (probe l) (source l) (target l)
      (hbranchBase (source l)) (hbranchBase (target l))]
    exact mul_ne_zero
      (mul_ne_zero hPx (hentry l)) hPy
  have hfan : AnalyticAt ℂ f 0 :=
    analyticAt_affineEigenbranchRowColumnMatrixProbe
      energy V
      (branch (source l)) (branch (target l))
      (probe l) (source l) (target l)
      (hbranchAnalytic (source l))
      (hbranchAnalytic (target l))
  exact hc.eventually (hfan.continuousAt.eventually_ne hf0)

/-- **Arbitrary-Hermitian birth-and-persistence law.**  One coded onsite
vector, one Hermitian leaf interaction, and one real coupling interval
simultaneously create every prescribed cross-layer transition and preserve
every prescribed transition already nonzero at the uncoupled spectrum. -/
theorem
    exists_eventually_allLayerCrossAndPersistentProbes_ne_zero_of_isHermitian
    {I ρ J L : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype ρ] [DecidableEq ρ]
    [Fintype J] [Fintype L]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (anchor : ρ) (layer : J → ρ)
    (hlayer : ∀ q, layer q ≠ anchor)
    (attachment : Matrix I I ℂ)
    (hattachmentHermitian : attachment.IsHermitian)
    (observer : J → Matrix I I ℂ)
    (hobserverHermitian : ∀ q, (observer q).IsHermitian)
    (a g b : J → I)
    (hag : ∀ q, a q ≠ g q)
    (hgb : ∀ q, g q ≠ b q)
    (hattachment : ∀ q, attachment (a q) (g q) ≠ 0)
    (hobserver : ∀ q, observer q (g q) (b q) ≠ 0)
    (persistentProbe : L → Matrix (I × ρ) (I × ρ) ℂ)
    (persistentSource persistentTarget : L → I × ρ)
    (hpersistent :
      ∀ l,
        persistentProbe l
          (persistentSource l) (persistentTarget l) ≠ 0) :
    ∃ n : ℕ, ∃ branch : I × ρ → ℂ → ℂ,
      Function.Injective
        (layeredEnergy
          (fun i => (energy i : ℂ))
          (fun r =>
            (codedIntegerLayerShift anchor n r : ℂ))) ∧
      (∀ x, AnalyticAt ℂ (branch x) 0) ∧
      (∀ x,
        branch x 0 =
          layeredEnergy
            (fun i => (energy i : ℂ))
            (fun r =>
              (codedIntegerLayerShift anchor n r : ℂ)) x) ∧
      (∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal
                (layeredEnergy
                  (fun i => (energy i : ℂ))
                  (fun r =>
                    (codedIntegerLayerShift anchor n r : ℂ))) +
              t • layerMatrixCoupling attachment
                (anchorStarLayerEdge anchor),
              branch x t) = 0) ∧
      ∀ᶠ t : ℝ in 𝓝[≠] 0,
        (∀ q,
          affineEigenbranchSesquilinearMatrixProbe
            (layeredEnergy
              (fun i => (energy i : ℂ))
              (fun r =>
                (codedIntegerLayerShift anchor n r : ℂ)))
            (layerMatrixCoupling attachment
              (anchorStarLayerEdge anchor))
            (branch (a q, layer q))
            (branch (b q, anchor))
            (layerMatrixCoupling (observer q)
              (1 : Matrix ρ ρ ℂ))
            (a q, layer q) (b q, anchor) t ≠ 0) ∧
        ∀ l,
          affineEigenbranchSesquilinearMatrixProbe
            (layeredEnergy
              (fun i => (energy i : ℂ))
              (fun r =>
                (codedIntegerLayerShift anchor n r : ℂ)))
            (layerMatrixCoupling attachment
              (anchorStarLayerEdge anchor))
            (branch (persistentSource l))
            (branch (persistentTarget l))
            (persistentProbe l)
            (persistentSource l) (persistentTarget l) t ≠ 0 := by
  obtain ⟨n, branch, hinj, hbranchAnalytic,
      hbranchBase, hbranchRoot, hcross⟩ :=
    exists_eventually_allLayerCrossSesquilinearProbes_ne_zero_of_isHermitian
      energy hmax anchor layer hlayer
      attachment hattachmentHermitian
      observer hobserverHermitian
      a g b hag hgb hattachment hobserver
  refine ⟨n, branch, hinj, hbranchAnalytic,
    hbranchBase, hbranchRoot, ?_⟩
  let fullEnergy : I × ρ → ℂ :=
    layeredEnergy
      (fun i => (energy i : ℂ))
      (fun r => (codedIntegerLayerShift anchor n r : ℂ))
  let V : Matrix (I × ρ) (I × ρ) ℂ :=
    layerMatrixCoupling attachment (anchorStarLayerEdge anchor)
  have hpersistentRow :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ l,
        affineEigenbranchRowColumnMatrixProbe
          fullEnergy V
          (branch (persistentSource l))
          (branch (persistentTarget l))
          (persistentProbe l)
          (persistentSource l) (persistentTarget l) t ≠ 0 :=
    eventually_all_affineRowColumnMatrixProbes_ne_zero_of_base_entries
      fullEnergy hinj V branch hbranchAnalytic hbranchBase
      persistentProbe persistentSource persistentTarget hpersistent
  have hbranchReal :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    eventually_allLayerStarEigenbranches_real_of_isHermitian
      energy (codedIntegerLayerShift anchor n)
      anchor attachment hattachmentHermitian
      branch hbranchRoot
  have hpersistentRowPunctured :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ l,
        affineEigenbranchRowColumnMatrixProbe
          fullEnergy V
          (branch (persistentSource l))
          (branch (persistentTarget l))
          (persistentProbe l)
          (persistentSource l) (persistentTarget l) t ≠ 0 :=
    Filter.Eventually.filter_mono inf_le_left hpersistentRow
  have hbranchRealPunctured :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    Filter.Eventually.filter_mono inf_le_left hbranchReal
  filter_upwards
    [hcross, hpersistentRowPunctured, hbranchRealPunctured]
      with t hcrossT hpersistentT hrealT
  refine ⟨hcrossT, ?_⟩
  intro l
  rw [
    affineEigenbranchSesquilinearMatrixProbe_eq_rowColumn_of_isHermitian
      fullEnergy V
      (branch (persistentSource l))
      (branch (persistentTarget l))
      (persistentProbe l)
      (persistentSource l) (persistentTarget l) t]
  · exact hpersistentT l
  · apply affineBranchCharacteristicMatrix_isHermitian
    · simpa [fullEnergy, V] using
        allLayerStarAffineMatrix_isHermitian_of_isHermitian
          energy (codedIntegerLayerShift anchor n) t
          anchor attachment hattachmentHermitian
    · exact hrealT (persistentSource l)

/-- A Hermitian tensor interaction creates a same-layer response of one
directed new-factor probe through its conjugate-oriented physical channel. -/
theorem localDirectedRowColumnProbe_sameLayer_deriv_ne_zero_of_isHermitian
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I × ρ → ℂ) (hinj : Function.Injective energy)
    (transition : Matrix I I ℂ) (htransitionHermitian : transition.IsHermitian)
    (edge : Matrix ρ ρ ℂ) (hedgeHermitian : edge.IsHermitian)
    (a b : I) (r s : ρ) (hab : a ≠ b) (hrs : r ≠ s)
    (htransition : transition b a ≠ 0)
    (hedge : edge s r ≠ 0)
    (branchX branchY : ℂ → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbaseX : branchX 0 = energy (a, r))
    (hbaseY : branchY 0 = energy (b, r))
    (hrootX :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy +
            g • layerMatrixCoupling transition edge,
            branchX g) = 0) :
    deriv
      (affineEigenbranchRowColumnMatrixProbe
        energy (layerMatrixCoupling transition edge)
        branchX branchY
        (layerMatrixCoupling (1 : Matrix I I ℂ)
          (directedLayerMatrix s r))
        (a, r) (b, r)) 0 ≠ 0 := by
  have htransition' : transition a b ≠ 0 := by
    intro hzero
    apply htransition
    rw [← htransitionHermitian.apply b a]
    simp [hzero]
  have hedge' : edge r s ≠ 0 := by
    intro hzero
    apply hedge
    rw [← hedgeHermitian.apply s r]
    simp [hzero]
  apply
    affineEigenbranchRowColumnMatrixProbe_deriv_ne_zero_of_one_sided
      energy hinj (layerMatrixCoupling transition edge)
      (a, r) (b, r) (b, s)
  · intro h
    exact hab (congrArg Prod.fst h).symm
  · exact hbranchX
  · exact hbranchY
  · exact hbaseX
  · exact hbaseY
  · exact hrootX
  · intro j
    simp [layerMatrixCoupling, directedLayerMatrix, hrs]
  · intro i hi
    by_cases hiold : i.1 = b
    · by_cases hilayer : i.2 = s
      · exfalso
        apply hi
        exact Prod.ext hiold hilayer
      · simp [layerMatrixCoupling, directedLayerMatrix,
          hilayer]
    · simp [layerMatrixCoupling, directedLayerMatrix, hiold]
  · simp [layerMatrixCoupling, directedLayerMatrix]
  · exact mul_ne_zero htransition' hedge'

/-- Every Hermitian same-layer interaction birth can be witnessed by one
strictly new-factor-local Hermitian cosine or sine probe. -/
theorem exists_hermitianNewLayerProbe_sameLayer_rowColumn_deriv_ne_zero
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I × ρ → ℂ) (hinj : Function.Injective energy)
    (transition : Matrix I I ℂ) (htransitionHermitian : transition.IsHermitian)
    (edge : Matrix ρ ρ ℂ) (hedgeHermitian : edge.IsHermitian)
    (a b : I) (r s : ρ) (hab : a ≠ b) (hrs : r ≠ s)
    (htransition : transition b a ≠ 0)
    (hedge : edge s r ≠ 0)
    (branchX branchY : ℂ → ℂ)
    (hbranchX : AnalyticAt ℂ branchX 0)
    (hbranchY : AnalyticAt ℂ branchY 0)
    (hbaseX : branchX 0 = energy (a, r))
    (hbaseY : branchY 0 = energy (b, r))
    (hrootX :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy +
            g • layerMatrixCoupling transition edge,
            branchX g) = 0) :
    ∃ B : Matrix ρ ρ ℂ,
      B.IsHermitian ∧
        deriv
          (affineEigenbranchRowColumnMatrixProbe
            energy (layerMatrixCoupling transition edge)
            branchX branchY
            (layerMatrixCoupling (1 : Matrix I I ℂ) B)
            (a, r) (b, r)) 0 ≠ 0 := by
  have hdir :=
    localDirectedRowColumnProbe_sameLayer_deriv_ne_zero_of_isHermitian
      energy hinj transition htransitionHermitian
      edge hedgeHermitian a b r s hab hrs
      htransition hedge branchX branchY
      hbranchX hbranchY hbaseX hbaseY hrootX
  let BX : Matrix ρ ρ ℂ :=
    hermitianLayerCosineProbe s r
  let BY : Matrix ρ ρ ℂ :=
    hermitianLayerSineProbe s r
  let OX : Matrix (I × ρ) (I × ρ) ℂ :=
    layerMatrixCoupling (1 : Matrix I I ℂ) BX
  let OY : Matrix (I × ρ) (I × ρ) ℂ :=
    layerMatrixCoupling (1 : Matrix I I ℂ) BY
  have hquadratures :=
    affineEigenbranchRowColumnMatrixProbe_directed_eq_quadratures
      energy (layerMatrixCoupling transition edge)
      branchX branchY s r hrs.symm
      (fun B =>
        layerMatrixCoupling (1 : Matrix I I ℂ) B)
      (by
        intro A B
        ext i j
        simp [layerMatrixCoupling, mul_add])
      (by
        intro c A
        ext i j
        simp [layerMatrixCoupling]
        ring)
      (a, r) (b, r)
  have hOXan :
      AnalyticAt ℂ
        (affineEigenbranchRowColumnMatrixProbe
          energy (layerMatrixCoupling transition edge)
          branchX branchY OX (a, r) (b, r)) 0 :=
    analyticAt_affineEigenbranchRowColumnMatrixProbe
      energy (layerMatrixCoupling transition edge)
      branchX branchY OX (a, r) (b, r)
      hbranchX hbranchY
  have hOYan :
      AnalyticAt ℂ
        (affineEigenbranchRowColumnMatrixProbe
          energy (layerMatrixCoupling transition edge)
          branchX branchY OY (a, r) (b, r)) 0 :=
    analyticAt_affineEigenbranchRowColumnMatrixProbe
      energy (layerMatrixCoupling transition edge)
      branchX branchY OY (a, r) (b, r)
      hbranchX hbranchY
  by_cases hx :
      deriv
        (affineEigenbranchRowColumnMatrixProbe
          energy (layerMatrixCoupling transition edge)
          branchX branchY OX (a, r) (b, r)) 0 ≠ 0
  · exact ⟨BX,
      hermitianLayerCosineProbe_isHermitian s r, hx⟩
  · refine ⟨BY, hermitianLayerSineProbe_isHermitian s r, ?_⟩
    intro hy
    apply hdir
    rw [hquadratures]
    have hsum :
        HasDerivAt
          (fun g =>
            (2 : ℂ)⁻¹ *
                affineEigenbranchRowColumnMatrixProbe
                  energy (layerMatrixCoupling transition edge)
                  branchX branchY OX (a, r) (b, r) g +
              (-(2 : ℂ)⁻¹ * Complex.I) *
                affineEigenbranchRowColumnMatrixProbe
                  energy (layerMatrixCoupling transition edge)
                  branchX branchY OY (a, r) (b, r) g)
          ((2 : ℂ)⁻¹ *
              deriv
                (affineEigenbranchRowColumnMatrixProbe
                  energy (layerMatrixCoupling transition edge)
                  branchX branchY OX (a, r) (b, r)) 0 +
            (-(2 : ℂ)⁻¹ * Complex.I) *
              deriv
                (affineEigenbranchRowColumnMatrixProbe
                  energy (layerMatrixCoupling transition edge)
                  branchX branchY OY (a, r) (b, r)) 0) 0 := by
      exact
        (hOXan.differentiableAt.hasDerivAt.const_mul
          (2 : ℂ)⁻¹).add
          (hOYan.differentiableAt.hasDerivAt.const_mul
            (-(2 : ℂ)⁻¹ * Complex.I))
    rw [hsum.deriv, not_ne_iff.mp hx, hy]
    ring

/-- A diagonal real-energy affine family with Hermitian interaction is
Hermitian at every real coupling. -/
theorem affineMatrix_isHermitian_real_of_isHermitian
    {K : Type*} [DecidableEq K]
    (energy : K → ℂ)
    (henergyReal :
      ∀ x, (starRingEnd ℂ) (energy x) = energy x)
    (V : Matrix K K ℂ) (hV : V.IsHermitian)
    (t : ℝ) :
    (Matrix.diagonal energy + (t : ℂ) • V).IsHermitian := by
  apply Matrix.IsHermitian.add
  · rw [Matrix.isHermitian_diagonal_iff]
    intro x
    rw [isSelfAdjoint_iff]
    exact henergyReal x
  · exact hV.smul (by rw [isSelfAdjoint_iff]; simp)

/-- Simultaneous same-layer births for a Hermitian attachment channel,
still in the holomorphic row--column representation. -/
theorem
    exists_eventually_all_hermitianNewLayerRowColumnProbes_ne_zero
    {I ρ K : Type*} [Fintype I] [Fintype ρ] [Fintype K]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I × ρ → ℂ) (hinj : Function.Injective energy)
    (transition : Matrix I I ℂ)
    (htransitionHermitian : transition.IsHermitian)
    (anchor other : ρ) (hother : other ≠ anchor)
    (branch : I × ρ → ℂ → ℂ)
    (hbranchAnalytic : ∀ x, AnalyticAt ℂ (branch x) 0)
    (hbranchBase : ∀ x, branch x 0 = energy x)
    (hbranchRoot :
      ∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal energy +
              t • layerMatrixCoupling transition
                (anchorStarLayerEdge anchor),
              branch x t) = 0)
    (a b : K → I)
    (hab : ∀ q, a q ≠ b q)
    (htransition : ∀ q, transition (b q) (a q) ≠ 0) :
    ∃ probe : K → ρ → Matrix ρ ρ ℂ,
      (∀ q r, (probe q r).IsHermitian) ∧
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ q r,
        affineEigenbranchRowColumnMatrixProbe
          energy
          (layerMatrixCoupling transition
            (anchorStarLayerEdge anchor))
          (branch (a q, r)) (branch (b q, r))
          (layerMatrixCoupling (1 : Matrix I I ℂ)
            (probe q r))
          (a q, r) (b q, r) t ≠ 0 := by
  have hone :
      ∀ q r,
        ∃ B : Matrix ρ ρ ℂ,
          B.IsHermitian ∧
            deriv
              (affineEigenbranchRowColumnMatrixProbe
                energy
                (layerMatrixCoupling transition
                  (anchorStarLayerEdge anchor))
                (branch (a q, r)) (branch (b q, r))
                (layerMatrixCoupling (1 : Matrix I I ℂ) B)
                (a q, r) (b q, r)) 0 ≠ 0 := by
    intro q r
    exact
      exists_hermitianNewLayerProbe_sameLayer_rowColumn_deriv_ne_zero
        energy hinj transition htransitionHermitian
        (anchorStarLayerEdge anchor)
        (anchorStarLayerEdge_isHermitian anchor)
        (a q) (b q) r (anchorStarCompanion anchor other r)
        (hab q)
        (anchorStarCompanion_ne hother r).symm
        (htransition q)
        (anchorStarLayerEdge_companion_ne_zero hother r)
        (branch (a q, r)) (branch (b q, r))
        (hbranchAnalytic (a q, r))
        (hbranchAnalytic (b q, r))
        (hbranchBase (a q, r))
        (hbranchBase (b q, r))
        (hbranchRoot (a q, r))
  choose probe hprobeHermitian hprobeDeriv using hone
  refine ⟨probe, hprobeHermitian, ?_⟩
  apply Filter.eventually_all.mpr
  intro q
  apply Filter.eventually_all.mpr
  intro r
  let f : ℂ → ℂ :=
    affineEigenbranchRowColumnMatrixProbe
      energy
      (layerMatrixCoupling transition
        (anchorStarLayerEdge anchor))
      (branch (a q, r)) (branch (b q, r))
      (layerMatrixCoupling (1 : Matrix I I ℂ)
        (probe q r))
      (a q, r) (b q, r)
  have hfan : AnalyticAt ℂ f 0 :=
    analyticAt_affineEigenbranchRowColumnMatrixProbe
      energy
      (layerMatrixCoupling transition
        (anchorStarLayerEdge anchor))
      (branch (a q, r)) (branch (b q, r))
      (layerMatrixCoupling (1 : Matrix I I ℂ)
        (probe q r))
      (a q, r) (b q, r)
      (hbranchAnalytic (a q, r))
      (hbranchAnalytic (b q, r))
  have hf0 : f 0 = 0 := by
    dsimp [f]
    rw [affineEigenbranchRowColumnMatrixProbe_zero
      energy
      (layerMatrixCoupling transition
        (anchorStarLayerEdge anchor))
      (branch (a q, r)) (branch (b q, r))
      (layerMatrixCoupling (1 : Matrix I I ℂ)
        (probe q r))
      (a q, r) (b q, r)
      (hbranchBase (a q, r))
      (hbranchBase (b q, r))]
    simp [layerMatrixCoupling, hab q]
  have hev :=
    eventually_real_ne_of_complex_deriv_ne_zero
      f (deriv f 0)
      hfan.differentiableAt.hasDerivAt
      (hprobeDeriv q r)
  filter_upwards [hev] with t ht
  simpa [hf0] using ht

/-- **Hermitian physical same-layer activation law.**  Every finite family
of nonzero old transition channels is born simultaneously in every new
factor layer.  The old attachment may be an arbitrary Hermitian matrix:
no entrywise-reality or symmetry premise remains. -/
theorem
    exists_eventually_all_hermitianNewLayerSesquilinearProbes_ne_zero_of_isHermitian
    {I ρ K : Type*} [Fintype I] [Fintype ρ] [Fintype K]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I × ρ → ℂ) (hinj : Function.Injective energy)
    (henergyReal :
      ∀ x, (starRingEnd ℂ) (energy x) = energy x)
    (transition : Matrix I I ℂ)
    (htransitionHermitian : transition.IsHermitian)
    (anchor other : ρ) (hother : other ≠ anchor)
    (branch : I × ρ → ℂ → ℂ)
    (hbranchAnalytic : ∀ x, AnalyticAt ℂ (branch x) 0)
    (hbranchBase : ∀ x, branch x 0 = energy x)
    (hbranchRoot :
      ∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal energy +
              t • layerMatrixCoupling transition
                (anchorStarLayerEdge anchor),
              branch x t) = 0)
    (hbranchReal :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t)
    (a b : K → I)
    (hab : ∀ q, a q ≠ b q)
    (htransition : ∀ q, transition (b q) (a q) ≠ 0) :
    ∃ probe : K → ρ → Matrix ρ ρ ℂ,
      (∀ q r, (probe q r).IsHermitian) ∧
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ q r,
        affineEigenbranchSesquilinearMatrixProbe
          energy
          (layerMatrixCoupling transition
            (anchorStarLayerEdge anchor))
          (branch (a q, r)) (branch (b q, r))
          (layerMatrixCoupling (1 : Matrix I I ℂ)
            (probe q r))
          (a q, r) (b q, r) t ≠ 0 := by
  obtain ⟨probe, hprobeHermitian, hrow⟩ :=
    exists_eventually_all_hermitianNewLayerRowColumnProbes_ne_zero
      energy hinj transition htransitionHermitian
      anchor other hother
      branch hbranchAnalytic hbranchBase hbranchRoot
      a b hab htransition
  refine ⟨probe, hprobeHermitian, ?_⟩
  have hbranchRealPunctured :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    Filter.Eventually.filter_mono inf_le_left hbranchReal
  filter_upwards [hrow, hbranchRealPunctured] with t ht hreal
  intro q r
  rw [
    affineEigenbranchSesquilinearMatrixProbe_eq_rowColumn_of_isHermitian
      energy
      (layerMatrixCoupling transition
        (anchorStarLayerEdge anchor))
      (branch (a q, r)) (branch (b q, r))
      (layerMatrixCoupling (1 : Matrix I I ℂ)
        (probe q r))
      (a q, r) (b q, r) t]
  · exact ht q r
  · apply affineBranchCharacteristicMatrix_isHermitian
    · apply affineMatrix_isHermitian_real_of_isHermitian
      · exact henergyReal
      · exact
          layerMatrixCoupling_isHermitian
            htransitionHermitian
            (anchorStarLayerEdge_isHermitian anchor)
    · exact hreal (a q, r)

end

end GaloisForLFunctions.HTGeometry
