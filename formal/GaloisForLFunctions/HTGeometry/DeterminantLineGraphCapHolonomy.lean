import GaloisForLFunctions.HTGeometry.DeterminantLineChainIntegrality
import GaloisForLFunctions.HTGeometry.GraphCapOperatorArea

/-!
# The determinant-line holonomy of a graph cap

**Smooth projections from frames.**  For a frame `Q + Y` with invertible Gram operator `Ĝ`, the
displacement `P − Q` of the spanned projection is the Hilbert–Schmidt operator
`−QĜ⁻¹(Ĝ − 1)Q + QĜ⁻¹Y† + YĜ⁻¹(Q + Y†)`, smooth in `Y`; its orthogonal projection to the
self-adjoint part gives the smooth `SLSpace`-valued displacement `frameDisp`.

**The graph cap.**  For a Hilbert–Schmidt `A` from `ran P₊` to `ker P₊` (`P₊A = 0`, `AP₊ = A`) and
`K = A*A`, the cap `z ↦ graph(zA)` carries the global frame `P₊ + zA` with Gram operator
`1 + |z|²K`.  In polar coordinates `z = r e^{2πiθ}` the connection form along the boundary circle is
the constant `2πi Tr((1 + K)⁻¹K)` and vanishes at the centre, so

* `integral_capKahler`: `∫_D Γ_A^* ω_det = Tr(K(I + K)⁻¹) = E(A)`;
* `edgeHol_capBoundary`: the holonomy of the positively oriented boundary loop is `exp(2πi E(A))`;
* `capBoundary_unique_lift`: if `E(A) < 1`, then `E(A)` is the unique lift of this holonomy in
  `[0, 1)`.
-/

set_option autoImplicit false

open ContinuousLinearMap

attribute [local instance] InnerProductSpace.complexToReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Smooth projections from smooth frames -/

section FrameProjection

variable {Q : H →L[ℂ] H}

/-- The Gram defect `Ĝ − 1 = QY + Y†Q + Y†Y` of the frame `Q + Y`. -/
def gramDefectHS (Q : H →L[ℂ] H) (Y : HSpace ℂ H) : HSpace ℂ H :=
  HSpace.lmulL Q Y + HSpace.rmulL (HSpace.adjointL Y) Q + HSpace.lmulL (adjoint Y.op) Y

theorem frameGram_frameOf_eq (hQ : IsStarProjection Q) (Y : HSpace ℂ H) :
    frameGram Q (frameOf Q Y) = 1 + (gramDefectHS Q Y).op := by
  rw [frameGram, adjoint_frameOf hQ.isSelfAdjoint]
  simp only [gramDefectHS, HSpace.op_add, HSpace.op_lmulL, HSpace.op_rmulL, HSpace.op_adjointL,
    frameOf]
  have hQQ := hQ.isIdempotentElem.eq
  calc (Q + adjoint Y.op) * (Q + Y.op) + (1 - Q) =
      1 + (Q * Q - Q) + (Q * Y.op + adjoint Y.op * Q + adjoint Y.op * Y.op) := by noncomm_ring
    _ = _ := by rw [hQQ, sub_self, add_zero]

/-- The displacement `P − Q` of the projection spanned by the frame `Q + Y`, as a Hilbert–Schmidt
operator: `−QĜ⁻¹(Ĝ − 1)Q + QĜ⁻¹Y† + YĜ⁻¹(Q + Y†)`. -/
def frameProjHS (Q : H →L[ℂ] H) (Y : HSpace ℂ H) : HSpace ℂ H :=
  -HSpace.lmulL (Q * Ring.inverse (frameGram Q (frameOf Q Y))) (HSpace.rmulL (gramDefectHS Q Y) Q) +
    HSpace.lmulL (Q * Ring.inverse (frameGram Q (frameOf Q Y))) (HSpace.adjointL Y) +
    HSpace.rmulL Y (Ring.inverse (frameGram Q (frameOf Q Y)) * (Q + adjoint Y.op))

theorem op_frameProjHS (hQ : IsStarProjection Q) {Y : HSpace ℂ H}
    (hunit : IsUnit (frameGram Q (frameOf Q Y))) :
    (frameProjHS Q Y).op =
      frameProj (frameOf Q Y) (Ring.inverse (frameGram Q (frameOf Q Y))) - Q := by
  have hR : Ring.inverse (frameGram Q (frameOf Q Y)) * (1 + (gramDefectHS Q Y).op) = 1 := by
    rw [← frameGram_frameOf_eq hQ]; exact Ring.inverse_mul_cancel _ hunit
  simp only [frameProjHS, HSpace.op_add, HSpace.op_neg, HSpace.op_lmulL, HSpace.op_rmulL,
    HSpace.op_adjointL]
  rw [frameProj, adjoint_frameOf hQ.isSelfAdjoint, HSpace.op_adjointL]
  set R := Ring.inverse (frameGram Q (frameOf Q Y))
  set D := (gramDefectHS Q Y).op
  have hQQ := hQ.isIdempotentElem.eq
  have h0 : Q * R * Q + Q * R * (D * Q) = Q := by
    calc Q * R * Q + Q * R * (D * Q) = Q * (R * (1 + D)) * Q := by noncomm_ring
      _ = Q := by rw [hR, mul_one, hQQ]
  have key : -(Q * R * (D * Q)) = Q * R * Q - Q := by
    calc -(Q * R * (D * Q)) = Q * R * Q - (Q * R * Q + Q * R * (D * Q)) := by noncomm_ring
      _ = Q * R * Q - Q := by rw [h0]
  rw [key, show frameOf Q Y = Q + Y.op from rfl]
  noncomm_ring

theorem contDiff_adjoint_op {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun Y : HSpace ℂ H => adjoint Y.op) := by
  have : (fun Y : HSpace ℂ H => adjoint Y.op) = fun Y => (HSpace.adjointL Y).op := by
    funext Y; simp
  rw [this]
  exact ((HSpace.opCLM H).restrictScalars ℝ).contDiff.comp HSpace.adjointL.contDiff

theorem contDiff_gramDefectHS {n : WithTop ℕ∞} : ContDiff ℝ n (gramDefectHS (H := H) Q) := by
  have h1 : ContDiff ℝ n (fun Y : HSpace ℂ H => HSpace.lmulL Q Y) := (HSpace.lmulL Q).contDiff
  have h2 : ContDiff ℝ n (fun Y : HSpace ℂ H => HSpace.rmulL (HSpace.adjointL Y) Q) :=
    ((HSpace.rmulL (H := H)).flip Q).contDiff.comp HSpace.adjointL.contDiff
  have h3 : ContDiff ℝ n (fun Y : HSpace ℂ H => HSpace.lmulL (adjoint Y.op) Y) :=
    (HSpace.lmulL.contDiff.comp contDiff_adjoint_op).clm_apply contDiff_id
  exact (h1.add h2).add h3

theorem contDiffAt_frameProjHS (hQ : IsSelfAdjoint Q) {Y₀ : HSpace ℂ H}
    (hunit : IsUnit (frameGram Q (frameOf Q Y₀))) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (frameProjHS Q) Y₀ := by
  obtain ⟨x, hx⟩ := hunit
  have hR : ContDiffAt ℝ n (fun Y : HSpace ℂ H => Ring.inverse (frameGram Q (frameOf Q Y))) Y₀ := by
    have h1 : ContDiffAt ℝ n Ring.inverse (frameGram Q (frameOf Q Y₀)) := by
      rw [← hx]; exact contDiffAt_ringInverse ℝ x
    exact h1.comp Y₀ (contDiff_frameGram_frameOf hQ).contDiffAt
  have hQR : ContDiffAt ℝ n (fun Y : HSpace ℂ H =>
      HSpace.lmulL (Q * Ring.inverse (frameGram Q (frameOf Q Y)))) Y₀ :=
    (HSpace.lmulL (H := H)).contDiff.contDiffAt.comp Y₀ ((contDiffAt_const (c := Q)).mul hR)
  have t1 := hQR.clm_apply
    (((HSpace.rmulL (H := H)).flip Q).contDiff.comp (contDiff_gramDefectHS (Q := Q))).contDiffAt
  have t2 := hQR.clm_apply HSpace.adjointL.contDiff.contDiffAt
  have t3 := ((HSpace.rmulL (H := H)).contDiff.contDiffAt (x := Y₀)).clm_apply
    (hR.mul ((contDiffAt_const (c := Q)).add contDiff_adjoint_op.contDiffAt))
  exact (t1.neg.add t2).add t3

instance slSubmodule_hasOrthogonalProjection : (slSubmodule H).HasOrthogonalProjection :=
  haveI : CompleteSpace ↥(slSubmodule H) := (isClosed_slSubmodule H).completeSpace_coe
  inferInstance

/-- The displacement `P − Q ∈ SLSpace` of the projection `P` spanned by the frame `Q + Y`. -/
def frameDisp (Q : H →L[ℂ] H) (Y : HSpace ℂ H) : SLSpace H :=
  (slSubmodule H).orthogonalProjectionOnto (frameProjHS Q Y)

theorem op_frameDisp (hQ : IsStarProjection Q) {Y : HSpace ℂ H}
    (hunit : IsUnit (frameGram Q (frameOf Q Y))) :
    (frameDisp Q Y).op =
      frameProj (frameOf Q Y) (Ring.inverse (frameGram Q (frameOf Q Y))) - Q := by
  have hsa : IsSelfAdjoint (frameProjHS Q Y).op := by
    rw [op_frameProjHS hQ hunit]
    exact (frameProj_isSelfAdjoint hQ.isSelfAdjoint (Ring.mul_inverse_cancel _ hunit)).sub
      hQ.isSelfAdjoint
  have hmem : frameProjHS Q Y ∈ slSubmodule H := hsa
  have h2 : (slSubmodule H).orthogonalProjectionOnto (frameProjHS Q Y) = ⟨frameProjHS Q Y, hmem⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := slSubmodule H) ⟨_, hmem⟩
  unfold frameDisp SLSpace.op SLSpace.toHS
  rw [h2]
  exact op_frameProjHS hQ hunit

theorem contDiffAt_frameDisp (hQ : IsSelfAdjoint Q) {Y₀ : HSpace ℂ H}
    (hunit : IsUnit (frameGram Q (frameOf Q Y₀))) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (frameDisp Q) Y₀ :=
  ((slSubmodule H).orthogonalProjectionOnto.contDiff.contDiffAt).comp Y₀
    (contDiffAt_frameProjHS hQ hunit)

/-- A frame spans an orthogonal projection. -/
theorem isStarProjection_of_isFrameOf (hQ : IsStarProjection Q) {w P : H →L[ℂ] H}
    (h : IsFrameOf Q w P) : IsStarProjection P := by
  obtain ⟨hwQ, hunit, hP⟩ := h
  have hPw := frameProj_mul_frame hQ.isIdempotentElem hwQ (Ring.inverse_mul_cancel _ hunit)
  rw [← hP]
  refine ⟨?_, frameProj_isSelfAdjoint hQ.isSelfAdjoint (Ring.mul_inverse_cancel _ hunit)⟩
  change frameProj w _ * (w * Ring.inverse (frameGram Q w) * adjoint w) =
    w * Ring.inverse (frameGram Q w) * adjoint w
  rw [← mul_assoc, ← mul_assoc, hPw]

theorem isFrameOf_frameDisp (hQ : IsStarProjection Q) {Y : HSpace ℂ H}
    (hunit : IsUnit (frameGram Q (frameOf Q Y))) (hYQ : Y.op * Q = Y.op) :
    IsFrameOf Q (frameOf Q Y) (Q + (frameDisp Q Y).op) := by
  refine ⟨?_, hunit, ?_⟩
  · rw [frameOf, add_mul, hQ.isIdempotentElem.eq, hYQ]
  · rw [op_frameDisp hQ hunit]; abel

end FrameProjection

/-! ## The graph cap -/

section GraphCap

/-- The polar coordinate `z = r e^{2πiθ}` of the plane. -/
def capCoord (q : ℝ × ℝ) : ℂ := q.1 * Complex.exp (2 * Real.pi * Complex.I * q.2)

theorem capCoord_snd_one (x : ℝ) : capCoord (x, 1) = capCoord (x, 0) := by
  simp [capCoord, Complex.exp_two_pi_mul_I]

theorem normSq_capCoord_one (y : ℝ) : Complex.normSq (capCoord (1, y)) = 1 := by
  rw [capCoord, Complex.ofReal_one, one_mul, Complex.normSq_eq_norm_sq,
    show 2 * Real.pi * Complex.I * y = ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_pow]

theorem hasFDerivAt_capCoord (q : ℝ × ℝ) : HasFDerivAt capCoord
    ((q.1 : ℂ) • (Complex.exp (2 * Real.pi * Complex.I * q.2) • ((2 * Real.pi * Complex.I) •
      (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)))) +
      Complex.exp (2 * Real.pi * Complex.I * q.2) •
        Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) q := by
  have hc : HasFDerivAt (fun q : ℝ × ℝ => (q.1 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) q :=
    Complex.ofRealCLM.hasFDerivAt.comp q (hasFDerivAt_fst)
  have hl : HasFDerivAt (fun q : ℝ × ℝ => 2 * Real.pi * Complex.I * (q.2 : ℂ))
      ((2 * Real.pi * Complex.I) • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))) q :=
    (Complex.ofRealCLM.hasFDerivAt.comp q hasFDerivAt_snd).const_mul _
  exact hc.mul hl.cexp

theorem fderiv_capCoord_fst (q : ℝ × ℝ) :
    fderiv ℝ capCoord q (1, 0) = Complex.exp (2 * Real.pi * Complex.I * q.2) := by
  rw [(hasFDerivAt_capCoord q).fderiv]; simp

theorem fderiv_capCoord_snd (q : ℝ × ℝ) :
    fderiv ℝ capCoord q (0, 1) =
      q.1 * (Complex.exp (2 * Real.pi * Complex.I * q.2) * (2 * Real.pi * Complex.I)) := by
  rw [(hasFDerivAt_capCoord q).fderiv]; simp

theorem contDiff_capCoord : ContDiff ℝ ⊤ capCoord :=
  (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul (Complex.contDiff_exp.comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)))

variable {Pp A : H →L[ℂ] H}

variable (A) in
/-- The frame displacement `zA` of the graph cap `z ↦ graph(zA)`, `z = r e^{2πiθ}`. -/
def capLift (hA : IsHilbertSchmidt A) (q : ℝ × ℝ) : HSpace ℂ H := capCoord q • HSpace.mk A hA

variable (Pp A) in
/-- **The graph cap** in polar coordinates: the projection onto `graph(zA)`, `z = r e^{2πiθ}`, as a
displacement from `P₊`. -/
def capMap (hA : IsHilbertSchmidt A) (q : ℝ × ℝ) : SLSpace H := frameDisp Pp (capLift A hA q)

theorem op_capLift (hA : IsHilbertSchmidt A) (q : ℝ × ℝ) :
    (capLift A hA q).op = capCoord q • A := rfl

theorem capLift_snd_one (hA : IsHilbertSchmidt A) (x : ℝ) :
    capLift A hA (x, 1) = capLift A hA (x, 0) := by
  rw [capLift, capLift, capCoord_snd_one]

theorem hasFDerivAt_capLift (hA : IsHilbertSchmidt A) (q : ℝ × ℝ) :
    HasFDerivAt (capLift A hA) ((fderiv ℝ capCoord q).smulRight (HSpace.mk A hA)) q :=
  ((hasFDerivAt_capCoord q).differentiableAt.hasFDerivAt).smul_const _

theorem fderiv_capLift (hA : IsHilbertSchmidt A) (q v : ℝ × ℝ) :
    fderiv ℝ (capLift A hA) q v = fderiv ℝ capCoord q v • HSpace.mk A hA := by
  rw [(hasFDerivAt_capLift hA q).fderiv]; rfl

theorem contDiff_capLift (hA : IsHilbertSchmidt A) : ContDiff ℝ ⊤ (capLift A hA) :=
  contDiff_capCoord.smul contDiff_const

section Hyp

variable (hPp : IsStarProjection Pp) (hA : IsHilbertSchmidt A) (hPA : Pp * A = 0)
  (hAP : A * Pp = A)

include hPp hPA in
theorem adjoint_mul_of_mul_eq_zero : adjoint A * Pp = 0 := by
  have h := congrArg star hPA
  rwa [star_mul, hPp.isSelfAdjoint.star_eq, star_zero, star_eq_adjoint] at h

include hPp hPA in
/-- The Gram operator of the cap frame is `1 + |z|² A*A`. -/
theorem frameGram_capLift (q : ℝ × ℝ) :
    frameGram Pp (frameOf Pp (capLift A hA q)) =
      1 + ((Complex.normSq (capCoord q) : ℝ) : ℂ) • (adjoint A * A) := by
  rw [frameGram_frameOf_eq hPp]
  congr 1
  have h2 := adjoint_mul_of_mul_eq_zero hPp hPA
  simp only [gramDefectHS, HSpace.op_add, HSpace.op_lmulL, HSpace.op_rmulL, HSpace.op_adjointL,
    op_capLift, map_smulₛₗ, mul_smul_comm, smul_mul_assoc, hPA, h2, smul_zero, zero_add,
    smul_smul, Complex.normSq_eq_conj_mul_self]
  rw [mul_comm]

include hPp hPA in
theorem isUnit_frameGram_capLift (q : ℝ × ℝ) :
    IsUnit (frameGram Pp (frameOf Pp (capLift A hA q))) := by
  rw [frameGram_capLift hPp hA hPA]
  set s := Complex.normSq (capCoord q)
  have hs : 0 ≤ s := Complex.normSq_nonneg _
  have h := isUnit_one_add_adjoint_comp_self (hA.smul ((Real.sqrt s : ℝ) : ℂ))
  convert h using 2
  rw [map_smulₛₗ, Complex.conj_ofReal, ← mul_def, smul_mul_assoc, mul_smul_comm, smul_smul,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hs]

include hPp hPA hAP in
theorem isFrameOf_capLift (q : ℝ × ℝ) :
    IsFrameOf Pp (frameOf Pp (capLift A hA q)) (Pp + (capMap Pp A hA q).op) :=
  isFrameOf_frameDisp hPp (isUnit_frameGram_capLift hPp hA hPA q)
    (by rw [op_capLift, smul_mul_assoc, hAP])

include hPA hAP in
theorem capLift_mem_admissible (q : ℝ × ℝ) : capLift A hA q ∈ admissibleSubspace Pp ⊥ := by
  refine ⟨fun x => ?_, by rw [op_capLift, smul_mul_assoc, hAP]⟩
  rw [op_capLift, Submodule.mem_bot, _root_.smul_apply, map_smul,
    ← mul_apply_eq_comp, hPA, zero_apply, smul_zero]

include hPp hPA in
theorem contDiff_capMap : ContDiff ℝ ⊤ (capMap Pp A hA) :=
  contDiff_iff_contDiffAt.mpr fun q =>
    (contDiffAt_frameDisp hPp.isSelfAdjoint (isUnit_frameGram_capLift hPp hA hPA q)).comp q
      (contDiff_capLift hA).contDiffAt

include hPp hPA in
/-- The connection form of the cap frame `P₊ + zA` along `wA`:
`α = w z̄ Tr((1 + |z|²K)⁻¹K)`, `K = A*A`. -/
theorem detConnection_capLift (q : ℝ × ℝ) (w : ℂ) :
    detConnection Pp (capLift A hA q) (w • HSpace.mk A hA) =
      (w * (starRingEnd ℂ) (capCoord q)) *
        opTrace (Ring.inverse (1 + ((Complex.normSq (capCoord q) : ℝ) : ℂ) • (adjoint A * A)) *
          (adjoint A * A)) := by
  rw [detConnection, frameGram_capLift hPp hA hPA, adjoint_frameOf hPp.isSelfAdjoint,
    ← opTrace_smul']
  congr 1
  simp only [HSpace.op_adjointL, op_capLift, HSpace.op_smul, HSpace.op_mk, map_smulₛₗ, mul_assoc,
    add_mul, mul_smul_comm, smul_mul_assoc, hPA, zero_add, smul_smul]

theorem liftConnS_capLift_snd_one (x : ℝ) :
    liftConnS Pp (capLift A hA) (x, 1) = liftConnS Pp (capLift A hA) (x, 0) := by
  rw [liftConnS, liftConnS, fderiv_capLift, fderiv_capLift, fderiv_capCoord_fst,
    fderiv_capCoord_fst, capLift_snd_one]
  simp [Complex.exp_two_pi_mul_I]

include hPp hPA in
theorem liftConnT_capLift_zero (y : ℝ) : liftConnT Pp (capLift A hA) (0, y) = 0 := by
  rw [liftConnT, fderiv_capLift, fderiv_capCoord_snd, detConnection_capLift hPp hA hPA]
  simp

include hPp hPA in
theorem liftConnT_capLift_one (y : ℝ) :
    liftConnT Pp (capLift A hA) (1, y) =
      2 * Real.pi * Complex.I * opTrace (Ring.inverse (1 + adjoint A * A) * (adjoint A * A)) := by
  rw [liftConnT, fderiv_capLift, fderiv_capCoord_snd, detConnection_capLift hPp hA hPA,
    normSq_capCoord_one, Complex.ofReal_one, one_smul]
  congr 1
  have hn : capCoord (1, y) * (starRingEnd ℂ) (capCoord (1, y)) = 1 := by
    rw [Complex.mul_conj, normSq_capCoord_one, Complex.ofReal_one]
  have hz : capCoord (1, y) = Complex.exp (2 * Real.pi * Complex.I * y) := by simp [capCoord]
  rw [hz] at hn ⊢
  simp only [one_mul]
  linear_combination (2 * Real.pi * Complex.I) * hn

omit [CompleteSpace H] in
theorem ringInverse_one_add_mul_comm {K : H →L[ℂ] H} (h : IsUnit (1 + K)) :
    Ring.inverse (1 + K) * K = K * Ring.inverse (1 + K) := by
  have h1 := Ring.inverse_mul_cancel _ h
  have h2 := Ring.mul_inverse_cancel _ h
  calc Ring.inverse (1 + K) * K = Ring.inverse (1 + K) * K * ((1 + K) * Ring.inverse (1 + K)) := by
        rw [h2, mul_one]
    _ = Ring.inverse (1 + K) * (1 + K) * K * Ring.inverse (1 + K) := by noncomm_ring
    _ = K * Ring.inverse (1 + K) := by rw [h1, one_mul]

include hA in
/-- `Tr((1 + K)⁻¹K) = E(A)`, the determinant-line area of the graph cap. -/
theorem opTrace_capResolvent :
    opTrace (Ring.inverse (1 + adjoint A * A) * (adjoint A * A)) = (graphCapArea A hA : ℂ) := by
  haveI : Fact (IsCompactOperator (adjoint A ∘L A)) := ⟨isCompactOperator_adjoint_comp_self hA⟩
  have hu : IsUnit (1 + adjoint A * A) := isUnit_one_add_adjoint_comp_self hA
  rw [← (graphCapArea_eq hA).2.1, resolventRatio]
  change _ = opTrace ((adjoint A * A) * Ring.inverse (1 + adjoint A * A))
  rw [ringInverse_one_add_mul_comm hu]

/-- The graph cap as a square of the restricted Grassmannian. -/
def capSquare : GrSquare Pp where
  map := capMap Pp A hA
  smooth := contDiff_capMap hPp hA hPA
  proj q := isStarProjection_of_isFrameOf hPp (isFrameOf_capLift hPp hA hPA hAP q)

include hPp hPA hAP in
/-- **The determinant-line area of the graph cap**: in polar coordinates
`∫_D Γ_A^* ω_det = Tr(K(I + K)⁻¹) = E(A)`. -/
theorem integral_capKahler :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, squareKahler Pp (capMap Pp A hA) (x, y) =
      graphCapArea A hA := by
  have h1 : ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, squareCurvature Pp (capMap Pp A hA) (x, y) =
      2 * Real.pi * Complex.I * ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        squareKahler Pp (capMap Pp A hA) (x, y) : ℝ) : ℂ) :=
    integral_squareCurvature_eq_kahler (capSquare hPp hA hPA hAP)
  have h2 := integral_squareCurvature_eq (V := ⊥) (O := Set.univ) hPp isOpen_univ
    (fun q _ => (contDiff_capMap hPp hA hPA).contDiffAt.of_le le_top)
    (fun q _ => (contDiff_capLift hA).contDiffAt.of_le le_top)
    (fun q _ => isFrameOf_capLift hPp hA hPA hAP q) (fun q _ => capLift_mem_admissible hA hPA hAP q)
    zero_le_one zero_le_one (Set.subset_univ _)
  have hS : (∫ x in (0 : ℝ)..1, liftConnS Pp (capLift A hA) (x, 1)) =
      ∫ x in (0 : ℝ)..1, liftConnS Pp (capLift A hA) (x, 0) := by
    congr 1; funext x; exact liftConnS_capLift_snd_one hA x
  have hT0 : (∫ y in (0 : ℝ)..1, liftConnT Pp (capLift A hA) (0, y)) = 0 := by
    simp [liftConnT_capLift_zero hPp hA hPA]
  have hT1 : (∫ y in (0 : ℝ)..1, liftConnT Pp (capLift A hA) (1, y)) =
      2 * Real.pi * Complex.I * (graphCapArea A hA : ℂ) := by
    simp [liftConnT_capLift_one hPp hA hPA, opTrace_capResolvent hA]
  rw [hS, hT0, hT1] at h2
  have h3 : (2 * Real.pi * Complex.I : ℂ) * ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      squareKahler Pp (capMap Pp A hA) (x, y) : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * (graphCapArea A hA : ℂ) := by
    rw [← h1, h2]; ring
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact_mod_cast mul_left_cancel₀ h2pi h3

variable (Pp A) in
/-- The positively oriented boundary loop `θ ↦ graph(e^{2πiθ}A)` of the graph cap. -/
def capBoundary (hA : IsHilbertSchmidt A) : ℝ → SLSpace H := vLine (capMap Pp A hA) 1

/-- The global lift `θ ↦ P₊ + e^{2πiθ}A` of the boundary loop. -/
def capBoundaryLift (a b : ℝ) : PathLift Pp Pp (capBoundary Pp A hA) a b where
  U := Set.univ
  isOpen_U := isOpen_univ
  Icc_subset := Set.subset_univ _
  Y θ := capLift A hA (1, θ)
  V := ⊥
  finiteDimensional_V := inferInstance
  smooth := ((contDiff_capLift hA).comp (contDiff_const.prodMk contDiff_id)).contDiffOn.of_le le_top
  frame r _ := isFrameOf_capLift hPp hA hPA hAP (1, r)
  admissible r _ := capLift_mem_admissible hA hPA hAP (1, r)

include hPp hPA hAP in
/-- **Holonomy of the graph cap**: the determinant-line holonomy of the positively oriented
boundary loop of `Γ_A` is `exp(2πi E(A))`, `E(A) = Tr(K(I + K)⁻¹)`. -/
theorem edgeHol_capBoundary :
    edgeHol Pp Pp (capBoundary Pp A hA) =
      Complex.exp (2 * Real.pi * Complex.I * graphCapArea A hA) := by
  have hfine : FineLevel Pp Pp (capBoundary Pp A hA) 1 :=
    fun _ _ => ⟨capBoundaryLift hPp hA hPA hAP _ _⟩
  rw [edgeHol_eq hPp one_pos hfine, levelHol]
  simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero, zero_add,
    Nat.cast_one, div_one]
  set L := capBoundaryLift hPp hA hPA hAP 0 1
  have hadm := L.isAdmissibleFrame hPp (Set.mem_univ 0)
  rw [segHol_eq hPp zero_le_one L, edgeFactor]
  have hY1 : L.Y 1 = L.Y 0 := capLift_snd_one hA 1
  have he1 : capBoundary Pp A hA 1 = capBoundary Pp A hA 0 := by
    simp only [capBoundary, vLine, capMap, capLift_snd_one]
  rw [hY1, he1, mul_div_assoc, div_self (detCoord_ne_zero hPp hadm), mul_one]
  congr 1
  have hderiv : ∀ r, deriv L.Y r = fderiv ℝ (capLift A hA) (1, r) (0, 1) := fun r => by
    have h := (hasFDerivAt_capLift hA (1, r)).comp_hasDerivAt r
      ((hasDerivAt_const r (1 : ℝ)).prodMk (hasDerivAt_id r))
    rw [← (hasFDerivAt_capLift hA (1, r)).fderiv] at h
    exact h.deriv
  have hint : (∫ r in (0 : ℝ)..1, detConnection Pp (L.Y r) (deriv L.Y r)) =
      ∫ r in (0 : ℝ)..1, liftConnT Pp (capLift A hA) (1, r) := by
    congr 1; funext r; rw [hderiv]; rfl
  rw [hint]
  simp [liftConnT_capLift_one hPp hA hPA, opTrace_capResolvent hA]

include hPp hPA hAP in
/-- **The principal lift of the cap holonomy**: if `E(A) < 1`, then `E(A)` is the unique
`x ∈ [0, 1)` with `exp(2πi x) = Hol(∂Γ_A)`. -/
theorem capBoundary_unique_lift (hlt : graphCapArea A hA < 1) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hxe : Complex.exp (2 * Real.pi * Complex.I * x) = edgeHol Pp Pp (capBoundary Pp A hA)) :
    x = graphCapArea A hA := by
  haveI : Fact (IsCompactOperator (adjoint A ∘L A)) := ⟨isCompactOperator_adjoint_comp_self hA⟩
  have h0 : 0 ≤ graphCapArea A hA := (graphCapArea_eq hA).2.2.1
  rw [edgeHol_capBoundary hPp hA hPA hAP] at hxe
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((x - graphCapArea A hA : ℝ) : ℂ)) = 1 := by
    push_cast
    rw [mul_sub, Complex.exp_sub, hxe, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := exists_int_of_exp_two_pi_I_mul_eq_one h1
  have habs : |(n : ℝ)| < 1 := by
    rw [← hn, abs_lt]; constructor <;> linarith [hx.1, hx.2]
  have hn0 : n = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast habs)
  rw [hn0, Int.cast_zero, sub_eq_zero] at hn
  exact hn

end Hyp

end GraphCap

end

end GaloisForLFunctions.HTGeometry
