import GaloisForLFunctions.HTGeometry.AllLayerEndpointSimultaneousResponse
import GaloisForLFunctions.HTGeometry.AllVertexEndpointPhysicalActivation
import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionChart

/-!
# One physical edge activates every layer and every old observer

The coded all-layer shift vector is combined with a real-symmetric star
matrix on the new local alphabet.  Its single affine coupling parameter
connects every nonanchor layer to the anchor.  The exact first derivative of
each old-observer transition is the corresponding two-step response packet;
all unselected layers disappear.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Real-symmetric star on a finite local alphabet, joining every
nonanchor layer to the chosen anchor and no other pair. -/
def anchorStarLayerEdge
    {ρ : Type*} [DecidableEq ρ] (anchor : ρ) :
    Matrix ρ ρ ℂ :=
  fun r s =>
    if (r = anchor ∧ s ≠ anchor) ∨
        (s = anchor ∧ r ≠ anchor)
    then 1 else 0

theorem anchorStarLayerEdge_isHermitian
    {ρ : Type*} [DecidableEq ρ] (anchor : ρ) :
    (anchorStarLayerEdge anchor).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext r s
  simp only [Matrix.conjTranspose_apply]
  simp [anchorStarLayerEdge, or_comm]

theorem anchorStarLayerEdge_entrywise_real
    {ρ : Type*} [DecidableEq ρ] (anchor : ρ) :
    ∀ r s,
      (starRingEnd ℂ) (anchorStarLayerEdge anchor r s) =
        anchorStarLayerEdge anchor r s := by
  intro r s
  simp [anchorStarLayerEdge]

/-- **Strictly local Hermitian same-layer birth.** A nonzero tensor-local
interaction channel admits a Hermitian probe on the new factor itself whose
lift `I ⊗ B` has nonzero first response between the selected same-layer
branches.  The locality of the witness is retained in the conclusion. -/
theorem exists_hermitianNewLayerProbe_sameLayer_deriv_ne_zero
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I × ρ → ℂ) (hinj : Function.Injective energy)
    (transition : Matrix I I ℂ) (edge : Matrix ρ ρ ℂ)
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
          (affineEigenbranchMatrixProbe
            energy (layerMatrixCoupling transition edge)
            branchX branchY
            (layerMatrixCoupling (1 : Matrix I I ℂ) B)
            (a, r) (b, r)) 0 ≠ 0 := by
  have hdir :
      deriv
        (affineEigenbranchMatrixProbe
          energy (layerMatrixCoupling transition edge)
          branchX branchY
          (layerMatrixCoupling (1 : Matrix I I ℂ)
            (directedLayerMatrix s r))
          (a, r) (b, r)) 0 ≠ 0 :=
    localDirectedProbe_sameLayer_deriv_ne_zero
      energy hinj transition edge a b r s hab hrs
      htransition hedge branchX branchY hbranchX hbranchY
      hbaseX hbaseY hrootX
  let BX : Matrix ρ ρ ℂ :=
    hermitianLayerCosineProbe s r
  let BY : Matrix ρ ρ ℂ :=
    hermitianLayerSineProbe s r
  let OX : Matrix (I × ρ) (I × ρ) ℂ :=
    layerMatrixCoupling (1 : Matrix I I ℂ) BX
  let OY : Matrix (I × ρ) (I × ρ) ℂ :=
    layerMatrixCoupling (1 : Matrix I I ℂ) BY
  have hquadratures :=
    affineEigenbranchMatrixProbe_directed_eq_quadratures
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
        (affineEigenbranchMatrixProbe
          energy (layerMatrixCoupling transition edge)
          branchX branchY OX (a, r) (b, r)) 0 :=
    analyticAt_affineEigenbranchMatrixProbe
      energy (layerMatrixCoupling transition edge)
      branchX branchY OX (a, r) (b, r)
      hbranchX hbranchY
  have hOYan :
      AnalyticAt ℂ
        (affineEigenbranchMatrixProbe
          energy (layerMatrixCoupling transition edge)
          branchX branchY OY (a, r) (b, r)) 0 :=
    analyticAt_affineEigenbranchMatrixProbe
      energy (layerMatrixCoupling transition edge)
      branchX branchY OY (a, r) (b, r)
      hbranchX hbranchY
  by_cases hx :
      deriv
        (affineEigenbranchMatrixProbe
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
                affineEigenbranchMatrixProbe
                  energy (layerMatrixCoupling transition edge)
                  branchX branchY OX (a, r) (b, r) g +
              (-(2 : ℂ)⁻¹ * Complex.I) *
                affineEigenbranchMatrixProbe
                  energy (layerMatrixCoupling transition edge)
                  branchX branchY OY (a, r) (b, r) g)
          ((2 : ℂ)⁻¹ *
              deriv
                (affineEigenbranchMatrixProbe
                  energy (layerMatrixCoupling transition edge)
                  branchX branchY OX (a, r) (b, r)) 0 +
            (-(2 : ℂ)⁻¹ * Complex.I) *
              deriv
                (affineEigenbranchMatrixProbe
                  energy (layerMatrixCoupling transition edge)
                  branchX branchY OY (a, r) (b, r)) 0) 0 := by
      exact
        (hOXan.differentiableAt.hasDerivAt.const_mul
          (2 : ℂ)⁻¹).add
          (hOYan.differentiableAt.hasDerivAt.const_mul
            (-(2 : ℂ)⁻¹ * Complex.I))
    rw [hsum.deriv, not_ne_iff.mp hx, hy]
    ring

/-- Partner layer used by the anchor-star edge: the fixed nonanchor partner
for the anchor and the anchor for every other layer. -/
def anchorStarCompanion
    {ρ : Type*} [DecidableEq ρ]
    (anchor other r : ρ) : ρ :=
  if r = anchor then other else anchor

theorem anchorStarCompanion_ne
    {ρ : Type*} [DecidableEq ρ]
    {anchor other : ρ} (hother : other ≠ anchor) (r : ρ) :
    anchorStarCompanion anchor other r ≠ r := by
  by_cases hr : r = anchor
  · subst r
    simpa [anchorStarCompanion] using hother
  · simp [anchorStarCompanion, hr, Ne.symm hr]

theorem anchorStarLayerEdge_companion_ne_zero
    {ρ : Type*} [DecidableEq ρ]
    {anchor other : ρ} (hother : other ≠ anchor) (r : ρ) :
    anchorStarLayerEdge anchor
        (anchorStarCompanion anchor other r) r ≠ 0 := by
  by_cases hr : r = anchor
  · subst r
    simp [anchorStarCompanion, anchorStarLayerEdge, hother]
  · simp [anchorStarCompanion, anchorStarLayerEdge, hr]

/-- Every finite family of nonzero old transition channels is born
simultaneously inside every new-factor layer, witnessed only by Hermitian
operators on the new factor. -/
theorem
    exists_eventually_all_hermitianNewLayerProbes_sameLayer_ne_zero
    {I ρ K : Type*} [Fintype I] [Fintype ρ] [Fintype K]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I × ρ → ℂ) (hinj : Function.Injective energy)
    (transition : Matrix I I ℂ)
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
        affineEigenbranchMatrixProbe
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
              (affineEigenbranchMatrixProbe
                energy
                (layerMatrixCoupling transition
                  (anchorStarLayerEdge anchor))
                (branch (a q, r)) (branch (b q, r))
                (layerMatrixCoupling (1 : Matrix I I ℂ) B)
                (a q, r) (b q, r)) 0 ≠ 0 := by
    intro q r
    exact
      exists_hermitianNewLayerProbe_sameLayer_deriv_ne_zero
        energy hinj transition (anchorStarLayerEdge anchor)
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
  apply
    eventually_affineEigenbranchMatrixProbe_ne_zero_of_deriv
      energy
      (layerMatrixCoupling transition
        (anchorStarLayerEdge anchor))
      (branch (a q, r)) (branch (b q, r))
      (layerMatrixCoupling (1 : Matrix I I ℂ)
        (probe q r))
      (a q, r) (b q, r)
      (hbranchAnalytic (a q, r))
      (hbranchAnalytic (b q, r))
      (hbranchBase (a q, r))
      (hbranchBase (b q, r))
      (by simp [layerMatrixCoupling, hab q])
      (hprobeDeriv q r)

/-- Real eigenbranches convert the simultaneous strictly local bilinear
witnesses into physical sesquilinear transitions. -/
theorem
    exists_eventually_all_hermitianNewLayerSesquilinearProbes_ne_zero
    {I ρ K : Type*} [Fintype I] [Fintype ρ] [Fintype K]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I × ρ → ℂ) (hinj : Function.Injective energy)
    (henergyReal :
      ∀ x, (starRingEnd ℂ) (energy x) = energy x)
    (transition : Matrix I I ℂ)
    (htransitionReal :
      ∀ x y,
        (starRingEnd ℂ) (transition x y) = transition x y)
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
  obtain ⟨probe, hprobeHermitian, hbilinear⟩ :=
    exists_eventually_all_hermitianNewLayerProbes_sameLayer_ne_zero
      energy hinj transition anchor other hother
      branch hbranchAnalytic hbranchBase hbranchRoot
      a b hab htransition
  refine ⟨probe, hprobeHermitian, ?_⟩
  have hbranchRealPunctured :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    Filter.Eventually.filter_mono inf_le_left hbranchReal
  filter_upwards [hbilinear, hbranchRealPunctured] with t ht hreal
  intro q r
  rw [
    affineEigenbranchSesquilinearMatrixProbe_eq_bilinear_of_left_real
      energy
      (layerMatrixCoupling transition
        (anchorStarLayerEdge anchor))
      (branch (a q, r)) (branch (b q, r))
      (layerMatrixCoupling (1 : Matrix I I ℂ)
        (probe q r))
      (a q, r) (b q, r) t]
  · exact ht q r
  · intro i
    apply star_affineEigenbranchAdjugateColumn_eq
    · exact henergyReal
    · rintro ⟨x, u⟩ ⟨y, v⟩
      simp [layerMatrixCoupling, htransitionReal,
        anchorStarLayerEdge_entrywise_real]
    · exact hreal (a q, r)
    · simp

/-- **Arbitrary-alphabet first-order endpoint law.**  For a star coupling
from one anchor layer to every other layer, the cross-layer transition
derivative sees exactly the same two-step response packet as the Boolean
model.  Every unselected layer cancels termwise. -/
theorem allLayerCrossMatrixProbe_deriv_eq_twoStepSums
    {I ρ : Type*} [Fintype I] [DecidableEq I]
    [Fintype ρ] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (hinj : Function.Injective (layeredEnergy energy shift))
    (attachment observer : Matrix I I ℂ)
    (hattachment : ∀ x y, attachment x y = attachment y x)
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
        (affineEigenbranchMatrixProbe
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
    affineEigenbranchMatrixProbe_deriv_eq_gapPackets
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
                (anchorStarLayerEdge anchor) i (a, layer) *
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
        layeredEnergy, hlayer, hattachment]
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

/-- A nonzero two-step packet therefore gives a nonzero first derivative in
the arbitrary-alphabet star family. -/
theorem allLayerCrossMatrixProbe_deriv_ne_zero_of_twoStepSums
    {I ρ : Type*} [Fintype I] [DecidableEq I]
    [Fintype ρ] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (hinj : Function.Injective (layeredEnergy energy shift))
    (attachment observer : Matrix I I ℂ)
    (hattachment : ∀ x y, attachment x y = attachment y x)
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
        (affineEigenbranchMatrixProbe
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
  rw [allLayerCrossMatrixProbe_deriv_eq_twoStepSums
    energy shift hinj attachment observer hattachment
    hlayer a b branchX branchY hbranchX hbranchY
    hbaseX hbaseY hrootX hrootY]
  exact mul_ne_zero (mul_ne_zero hPx hPy) hpacket

/-- **One-vector, one-edge, all-layer derivative law.** For every finite
local alphabet and finite set of old-observer channels assigned to
nonanchor layers, one coded onsite vector and the one anchor-star edge
direction give simultaneously nonzero transition derivatives for all
channels. -/
theorem
    exists_codedShift_allLayerCrossMatrixProbe_deriv_ne_zero
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
    (hattachmentSymm :
      ∀ x y, attachment x y = attachment y x)
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
            (affineEigenbranchMatrixProbe
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
    allLayerCrossMatrixProbe_deriv_ne_zero_of_twoStepSums
      (fun i => (energy i : ℂ)) shift hinj
      attachment (observer q) hattachmentSymm
      (hlayer q) (a q) (b q)
      (branch (a q, layer q)) (branch (b q, anchor))
      (hbranchAnalytic (a q, layer q))
      (hbranchAnalytic (b q, anchor))
      (hbranchBase (a q, layer q))
      (hbranchBase (b q, anchor))
      (hbranchRoot (a q, layer q))
      (hbranchRoot (b q, anchor))
      hpacket

/-- A real-symmetric attachment matrix is Hermitian. -/
theorem realSymmetricAttachment_isHermitian
    {I : Type*}
    (attachment : Matrix I I ℂ)
    (hsymm : ∀ x y, attachment x y = attachment y x)
    (hreal :
      ∀ x y,
        (starRingEnd ℂ) (attachment x y) = attachment x y) :
    attachment.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  simp only [Matrix.conjTranspose_apply]
  change
    (starRingEnd ℂ) (attachment y x) = attachment x y
  rw [hreal, hsymm]

/-- Every real point of the coded all-layer star family is Hermitian. -/
theorem allLayerStarAffineMatrix_isHermitian_real
    {I ρ : Type*} [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℝ) (shift : ρ → ℝ) (t : ℝ)
    (anchor : ρ)
    (attachment : Matrix I I ℂ)
    (hsymm : ∀ x y, attachment x y = attachment y x)
    (hreal :
      ∀ x y,
        (starRingEnd ℂ) (attachment x y) = attachment x y) :
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
      (layerMatrixCoupling_isHermitian
        (realSymmetricAttachment_isHermitian
          attachment hsymm hreal)
        (anchorStarLayerEdge_isHermitian anchor)).smul
        (by rw [isSelfAdjoint_iff]; simp)

/-- All labelled characteristic-root branches of the real all-layer star
family are simultaneously real on one real neighborhood. -/
theorem eventually_allLayerStarEigenbranches_real
    {I ρ : Type*} [Fintype I] [DecidableEq I]
    [Fintype ρ] [DecidableEq ρ]
    (energy : I → ℝ) (shift : ρ → ℝ)
    (anchor : ρ)
    (attachment : Matrix I I ℂ)
    (hsymm : ∀ x y, attachment x y = attachment y x)
    (hreal :
      ∀ x y,
        (starRingEnd ℂ) (attachment x y) = attachment x y)
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
      (allLayerStarAffineMatrix_isHermitian_real
        energy shift t anchor attachment hsymm hreal)
      _ ht
  apply Complex.ext
  · simp
  · simp [him]

/-- Every finite set of transitions already nonzero at a simple diagonal
base persists simultaneously under the same sufficiently small real affine
coupling. -/
theorem eventually_all_affineMatrixProbes_ne_zero_of_base_entries
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
      affineEigenbranchMatrixProbe
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
    affineEigenbranchMatrixProbe
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
    rw [affineEigenbranchMatrixProbe_zero
      energy V
      (branch (source l)) (branch (target l))
      (probe l) (source l) (target l)
      (hbranchBase (source l)) (hbranchBase (target l))]
    exact mul_ne_zero
      (mul_ne_zero hPx (hentry l)) hPy
  have hfan : AnalyticAt ℂ f 0 :=
    analyticAt_affineEigenbranchMatrixProbe
      energy V
      (branch (source l)) (branch (target l))
      (probe l) (source l) (target l)
      (hbranchAnalytic (source l))
      (hbranchAnalytic (target l))
  exact hc.eventually (hfan.continuousAt.eventually_ne hf0)

/-- **Physical arbitrary-alphabet all-observer activation law.** For every
finite new local dimension, every required old observer, and every assigned
nonanchor layer, one real coded onsite vector and one real-symmetric
anchor-star edge direction make all physical bra--ket transitions nonzero
throughout a common punctured real coupling interval. -/
theorem
    exists_eventually_allLayerCrossSesquilinearProbes_ne_zero
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
    (hattachmentSymm :
      ∀ x y, attachment x y = attachment y x)
    (hattachmentReal :
      ∀ x y,
        (starRingEnd ℂ) (attachment x y) = attachment x y)
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
    exists_codedShift_allLayerCrossMatrixProbe_deriv_ne_zero
      energy hmax anchor layer hlayer attachment observer
      a g b hag hgb hattachmentSymm hattachment hobserver
  refine ⟨n, branch, hinj, hbranchAnalytic,
    hbranchBase, hbranchRoot, ?_⟩
  let fullEnergy : I × ρ → ℂ :=
    layeredEnergy
      (fun i => (energy i : ℂ))
      (fun r => (codedIntegerLayerShift anchor n r : ℂ))
  let V : Matrix (I × ρ) (I × ρ) ℂ :=
    layerMatrixCoupling attachment (anchorStarLayerEdge anchor)
  have hbilinear :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ q,
        affineEigenbranchMatrixProbe
          fullEnergy V
          (branch (a q, layer q))
          (branch (b q, anchor))
          (layerMatrixCoupling (observer q)
            (1 : Matrix ρ ρ ℂ))
          (a q, layer q) (b q, anchor) t ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro q
    apply
      eventually_affineEigenbranchMatrixProbe_ne_zero_of_deriv
        fullEnergy V
        (branch (a q, layer q))
        (branch (b q, anchor))
        (layerMatrixCoupling (observer q)
          (1 : Matrix ρ ρ ℂ))
        (a q, layer q) (b q, anchor)
        (hbranchAnalytic (a q, layer q))
        (hbranchAnalytic (b q, anchor))
        (hbranchBase (a q, layer q))
        (hbranchBase (b q, anchor))
        (by simp [layerMatrixCoupling, hlayer q])
        (hderiv q)
  have hbranchReal :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    eventually_allLayerStarEigenbranches_real
      energy (codedIntegerLayerShift anchor n)
      anchor attachment hattachmentSymm hattachmentReal
      branch hbranchRoot
  have hbranchRealPunctured :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    Filter.Eventually.filter_mono inf_le_left hbranchReal
  filter_upwards [hbilinear, hbranchRealPunctured] with t ht hreal
  intro q
  rw [
    affineEigenbranchSesquilinearMatrixProbe_eq_bilinear_of_left_real
      fullEnergy V
      (branch (a q, layer q))
      (branch (b q, anchor))
      (layerMatrixCoupling (observer q)
        (1 : Matrix ρ ρ ℂ))
      (a q, layer q) (b q, anchor) t]
  · exact ht q
  · intro i
    apply star_affineEigenbranchAdjugateColumn_eq
    · rintro ⟨k, r⟩
      simp [fullEnergy, layeredEnergy, codedIntegerLayerShift]
    · rintro ⟨k, r⟩ ⟨l, s⟩
      simp [V, layerMatrixCoupling, hattachmentReal,
        anchorStarLayerEdge_entrywise_real]
    · exact hreal (a q, layer q)
    · simp

/-- **Birth-and-persistence assembly law.** In the same physical witness
family that creates all required cross-layer transitions, every prescribed
finite transition already nonzero at the uncoupled product spectrum remains
nonzero.  Birth and persistence use one onsite vector, one Hermitian edge
direction, and one common punctured coupling interval. -/
theorem
    exists_eventually_allLayerCrossAndPersistentProbes_ne_zero
    {I ρ J L : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype ρ] [DecidableEq ρ]
    [Fintype J] [Fintype L]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (anchor : ρ) (layer : J → ρ)
    (hlayer : ∀ q, layer q ≠ anchor)
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
    exists_eventually_allLayerCrossSesquilinearProbes_ne_zero
      energy hmax anchor layer hlayer attachment observer
      a g b hag hgb hattachmentSymm hattachmentReal
      hattachment hobserver
  refine ⟨n, branch, hinj, hbranchAnalytic,
    hbranchBase, hbranchRoot, ?_⟩
  let fullEnergy : I × ρ → ℂ :=
    layeredEnergy
      (fun i => (energy i : ℂ))
      (fun r => (codedIntegerLayerShift anchor n r : ℂ))
  let V : Matrix (I × ρ) (I × ρ) ℂ :=
    layerMatrixCoupling attachment (anchorStarLayerEdge anchor)
  have hpersistentBilinear :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ l,
        affineEigenbranchMatrixProbe
          fullEnergy V
          (branch (persistentSource l))
          (branch (persistentTarget l))
          (persistentProbe l)
          (persistentSource l) (persistentTarget l) t ≠ 0 :=
    eventually_all_affineMatrixProbes_ne_zero_of_base_entries
      fullEnergy hinj V branch hbranchAnalytic hbranchBase
      persistentProbe persistentSource persistentTarget hpersistent
  have hbranchReal :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    eventually_allLayerStarEigenbranches_real
      energy (codedIntegerLayerShift anchor n)
      anchor attachment hattachmentSymm hattachmentReal
      branch hbranchRoot
  have hpersistentBilinearPunctured :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ l,
        affineEigenbranchMatrixProbe
          fullEnergy V
          (branch (persistentSource l))
          (branch (persistentTarget l))
          (persistentProbe l)
          (persistentSource l) (persistentTarget l) t ≠ 0 :=
    Filter.Eventually.filter_mono inf_le_left hpersistentBilinear
  have hbranchRealPunctured :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    Filter.Eventually.filter_mono inf_le_left hbranchReal
  filter_upwards
    [hcross, hpersistentBilinearPunctured, hbranchRealPunctured]
      with t hcrossT hpersistentT hrealT
  refine ⟨hcrossT, ?_⟩
  intro l
  rw [
    affineEigenbranchSesquilinearMatrixProbe_eq_bilinear_of_left_real
      fullEnergy V
      (branch (persistentSource l))
      (branch (persistentTarget l))
      (persistentProbe l)
      (persistentSource l) (persistentTarget l) t]
  · exact hpersistentT l
  · intro i
    apply star_affineEigenbranchAdjugateColumn_eq
    · rintro ⟨k, r⟩
      simp [fullEnergy, layeredEnergy, codedIntegerLayerShift]
    · rintro ⟨k, r⟩ ⟨m, s⟩
      simp [V, layerMatrixCoupling, hattachmentReal,
        anchorStarLayerEdge_entrywise_real]
    · exact hrealT (persistentSource l)
    · simp

end

end GaloisForLFunctions.HTGeometry
