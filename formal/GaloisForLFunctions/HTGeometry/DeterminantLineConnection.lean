import GaloisForLFunctions.HTGeometry.HilbertSchmidtCalculus
import GaloisForLFunctions.HTGeometry.SelfAdjointHilbertSchmidtSpace
import GaloisForLFunctions.RHTower.ConnesConsaniTraceClassReduction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The determinant-line connection on admissible frame families

A frame of a subspace `W` relative to a polarization projection `Q` is an operator `w = Q + Y`
(`Y` Hilbert–Schmidt, `w Q = w`) with invertible Gram operator `Ĝ = w† w + (1 − Q)`; the orthogonal
projection onto `W` is `P = w Ĝ⁻¹ w†`.  The connection form of the determinant line is
`α(w)[Ẏ] = Tr(Ĝ⁻¹ w† Ẏ)`, defined when the `ran Q`-part of `Ẏ` has finite rank.

* `frame_curvature_trace`: the algebraic curvature identity
  `Tr(A w_s† w_t) − Tr(A Ĝ_s A w† w_t) − (s ↔ t) = Tr(P [P_s, P_t])`.
* `hasDerivAt_detConnection`, `hasDerivAt_frameProj`: derivatives of `α` and of `P` along curves,
  through the bounded trace pairing of Hilbert–Schmidt operators.
* `detConnection_curvature`: for a `C²` two-parameter admissible family,
  `∂ₛ α(∂ₜY) − ∂ₜ α(∂ₛY) = Tr(P [∂ₛP, ∂ₜP])`.
-/

set_option autoImplicit false

open ContinuousLinearMap
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Frame algebra

A frame of a subspace `W` relative to the polarization projection `Q` is an operator `w` with
`w Q = w`, injective with closed range on `ran Q`; its Gram operator is
`Ĝ = w† w + (1 − Q)` and the projection onto `W = ran w` is `P = w Ĝ⁻¹ w†`. -/

section FrameAlgebra

variable {Q w A : H →L[ℂ] H}

/-- The Gram operator of a frame. -/
def frameGram (Q w : H →L[ℂ] H) : H →L[ℂ] H := adjoint w * w + (1 - Q)

/-- The projection onto the range of a frame, `w Ĝ⁻¹ w†`, given the inverse `A = Ĝ⁻¹`. -/
def frameProj (w A : H →L[ℂ] H) : H →L[ℂ] H := w * A * adjoint w

theorem adjoint_mul_of_mul_eq (hQ : IsSelfAdjoint Q) (hwQ : w * Q = w) :
    Q * adjoint w = adjoint w := by
  have := congrArg adjoint hwQ
  rw [← star_eq_adjoint, star_mul, hQ.star_eq] at this
  rwa [star_eq_adjoint] at this

theorem frameGram_comm (hQ : IsSelfAdjoint Q) (hQi : IsIdempotentElem Q) (hwQ : w * Q = w) :
    Q * frameGram Q w = frameGram Q w * Q := by
  have h := adjoint_mul_of_mul_eq hQ hwQ
  unfold frameGram
  rw [mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, h, mul_assoc, hwQ, hQi.eq, mul_one, one_mul]

section Inverse

variable (hQ : IsSelfAdjoint Q) (hQi : IsIdempotentElem Q) (hwQ : w * Q = w)
  (hA : A * frameGram Q w = 1) (hA' : frameGram Q w * A = 1)
include hQ hQi hwQ hA hA'

theorem frameInv_comm : Q * A = A * Q := by
  have hc := frameGram_comm hQ hQi hwQ
  calc Q * A = A * frameGram Q w * (Q * A) := by rw [hA, one_mul]
    _ = A * (frameGram Q w * Q) * A := by noncomm_ring
    _ = A * (Q * frameGram Q w) * A := by rw [hc]
    _ = A * Q * (frameGram Q w * A) := by noncomm_ring
    _ = A * Q := by rw [hA', mul_one]

omit hQ hA' in
theorem frameInv_compl : A * (1 - Q) = 1 - Q := by
  have hG : frameGram Q w * (1 - Q) = 1 - Q := by
    unfold frameGram
    rw [add_mul, mul_assoc, mul_sub, mul_one, hwQ, sub_self, mul_zero, zero_add, mul_sub, mul_one,
      sub_mul, one_mul, hQi.eq, sub_self, sub_zero]
  calc A * (1 - Q) = A * (frameGram Q w * (1 - Q)) := by rw [hG]
    _ = 1 - Q := by rw [← mul_assoc, hA, one_mul]

omit hQ hA' in
theorem frameInv_adjoint_mul : A * adjoint w * w = Q := by
  have h1 : A * (adjoint w * w) = A * frameGram Q w - A * (1 - Q) := by
    unfold frameGram; noncomm_ring
  rw [mul_assoc, h1, hA, frameInv_compl hQi hwQ hA, sub_sub_cancel]

omit hQ hA' in
theorem frameProj_mul_frame : frameProj w A * w = w := by
  unfold frameProj
  calc w * A * adjoint w * w = w * (A * adjoint w * w) := by noncomm_ring
    _ = w := by rw [frameInv_adjoint_mul hQi hwQ hA, hwQ]

omit hQ hA' in
theorem compl_frameProj_mul_frame : (1 - frameProj w A) * w = 0 := by
  rw [sub_mul, one_mul, frameProj_mul_frame hQi hwQ hA, sub_self]

omit hQi hwQ hA in
theorem frameInv_isSelfAdjoint : IsSelfAdjoint A := by
  have hG : IsSelfAdjoint (frameGram Q w) := by
    unfold frameGram
    refine IsSelfAdjoint.add ?_ ((IsSelfAdjoint.one _).sub hQ)
    rw [IsSelfAdjoint, star_mul, ← star_eq_adjoint, star_star]
  have h1 : star A * frameGram Q w = 1 := by
    have := congrArg star hA'
    rwa [star_mul, hG.star_eq, star_one] at this
  rw [IsSelfAdjoint]
  calc star A = star A * (frameGram Q w * A) := by rw [hA', mul_one]
    _ = (star A * frameGram Q w) * A := by noncomm_ring
    _ = A := by rw [h1, one_mul]

omit hQi hwQ hA in
theorem frameProj_isSelfAdjoint : IsSelfAdjoint (frameProj w A) := by
  unfold frameProj
  rw [IsSelfAdjoint, star_mul, star_mul, (frameInv_isSelfAdjoint hQ hA').star_eq,
    ← star_eq_adjoint, star_star]
  noncomm_ring

theorem adjoint_frame_mul_compl : adjoint w * (1 - frameProj w A) = 0 := by
  have h := congrArg star (compl_frameProj_mul_frame hQi hwQ hA)
  rw [star_mul, star_sub, star_one, (frameProj_isSelfAdjoint hQ hA').star_eq,
    star_zero, star_eq_adjoint] at h
  exact h

/-- **The curvature of the determinant-line connection, algebraic form.**  For tangent frame
directions `w_s, w_t` (Hilbert–Schmidt, vanishing off `ran Q`),
`Tr(A w_s† w_t) − Tr(A Ĝ_s A w† w_t) − (s ↔ t) = Tr(P [P_s, P_t])`, where `A = Ĝ⁻¹`,
`Ĝ_s = w_s† w + w† w_s` and `P_s = (1 − P) w_s A w† + w A w_s† (1 − P)` are the derivatives of the
Gram operator and of `P = w A w†`. -/
theorem frame_curvature_trace {ws wt : H →L[ℂ] H} (hs : IsHilbertSchmidt ws)
    (ht : IsHilbertSchmidt wt) (hwsQ : ws * Q = ws) (hwtQ : wt * Q = wt) :
    opTrace (A * adjoint ws * wt) -
        opTrace (A * (adjoint ws * w + adjoint w * ws) * A * adjoint w * wt) -
      (opTrace (A * adjoint wt * ws) -
        opTrace (A * (adjoint wt * w + adjoint w * wt) * A * adjoint w * ws)) =
      opTrace (frameProj w A *
        (((1 - frameProj w A) * ws * A * adjoint w + w * A * adjoint ws * (1 - frameProj w A)) *
          ((1 - frameProj w A) * wt * A * adjoint w + w * A * adjoint wt * (1 - frameProj w A)) -
         ((1 - frameProj w A) * wt * A * adjoint w + w * A * adjoint wt * (1 - frameProj w A)) *
          ((1 - frameProj w A) * ws * A * adjoint w + w * A * adjoint ws * (1 - frameProj w A)))) := by
  set P := frameProj w A with hPdef
  have hPw : (1 - P) * w = 0 := compl_frameProj_mul_frame hQi hwQ hA
  have hwP : adjoint w * (1 - P) = 0 := adjoint_frame_mul_compl hQ hQi hwQ hA hA'
  have hAw : A * adjoint w * w = Q := frameInv_adjoint_mul hQi hwQ hA
  have hP : P = w * A * adjoint w := rfl
  -- Hilbert–Schmidt factors
  have hsa : IsHilbertSchmidt (adjoint ws) := hs.adjoint
  have hta : IsHilbertSchmidt (adjoint wt) := ht.adjoint
  set Bs := A * adjoint w * ws
  set Bt := A * adjoint w * wt
  have hBs : IsHilbertSchmidt Bs := hs.comp_left (A * adjoint w)
  have hBt : IsHilbertSchmidt Bt := ht.comp_left (A * adjoint w)
  -- the left-hand side
  have hLs : A * (adjoint ws * w + adjoint w * ws) * A * adjoint w * wt =
      A * adjoint ws * P * wt + Bs * Bt := by
    rw [hP]; noncomm_ring
  have hLt : A * (adjoint wt * w + adjoint w * wt) * A * adjoint w * ws =
      A * adjoint wt * P * ws + Bt * Bs := by
    rw [hP]; noncomm_ring
  have m1 : A * adjoint ws * P * wt ∈ hsTraceIdeal H :=
    mul_mem_hsTraceIdeal (hsa.comp_left A |>.comp_right P) ht
  have m2 : A * adjoint wt * P * ws ∈ hsTraceIdeal H :=
    mul_mem_hsTraceIdeal (hta.comp_left A |>.comp_right P) hs
  have m3 : Bs * Bt ∈ hsTraceIdeal H := mul_mem_hsTraceIdeal hBs hBt
  have m4 : Bt * Bs ∈ hsTraceIdeal H := mul_mem_hsTraceIdeal hBt hBs
  have m5 : A * adjoint ws * wt ∈ hsTraceIdeal H := mul_mem_hsTraceIdeal (hsa.comp_left A) ht
  have m6 : A * adjoint wt * ws ∈ hsTraceIdeal H := mul_mem_hsTraceIdeal (hta.comp_left A) hs
  have hcyc : opTrace (Bs * Bt) = opTrace (Bt * Bs) := opTrace_comp_comm hBs hBt
  -- the right-hand side
  have hPP : P * P = P := by
    rw [hP]
    calc w * A * adjoint w * (w * A * adjoint w) = w * (A * adjoint w * w) * A * adjoint w := by
          noncomm_ring
      _ = w * A * adjoint w := by rw [hAw, hwQ]
  have e1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hPP, sub_self, sub_zero]
  have e2 : P * w = w := by
    rw [hP]
    calc w * A * adjoint w * w = w * (A * adjoint w * w) := by noncomm_ring
      _ = w := by rw [hAw, hwQ]
  have hX : ∀ {u v : H →L[ℂ] H}, u * Q = u →
      P * (((1 - P) * u * A * adjoint w + w * A * adjoint u * (1 - P)) *
        ((1 - P) * v * A * adjoint w + w * A * adjoint v * (1 - P))) =
      w * (A * adjoint u * (1 - P) * v * A * adjoint w) := by
    intro u v _
    calc P * (((1 - P) * u * A * adjoint w + w * A * adjoint u * (1 - P)) *
          ((1 - P) * v * A * adjoint w + w * A * adjoint v * (1 - P)))
        = P * (1 - P) * (u * A * adjoint w * ((1 - P) * v * A * adjoint w) +
            u * A * (adjoint w * w) * A * adjoint v * (1 - P)) +
          P * w * A * adjoint u * ((1 - P) * (1 - P)) * v * A * adjoint w +
          P * w * A * adjoint u * ((1 - P) * w) * A * adjoint v * (1 - P) := by noncomm_ring
      _ = w * (A * adjoint u * (1 - P) * v * A * adjoint w) := by
          rw [e1, e2, hPw, hQQ]; noncomm_ring
  have hXs := hX (u := ws) (v := wt) hwsQ
  have hXt := hX (u := wt) (v := ws) hwtQ
  have mXs : A * adjoint ws * (1 - P) * wt * A * adjoint w ∈ hsTraceIdeal H := by
    have hU : IsHilbertSchmidt ((1 - P) * wt * A * adjoint w) :=
      ((ht.comp_left (1 - P)).comp_right A).comp_right (adjoint w)
    rw [show A * adjoint ws * (1 - P) * wt * A * adjoint w =
      (A * adjoint ws) * ((1 - P) * wt * A * adjoint w) by noncomm_ring]
    exact mul_mem_hsTraceIdeal (hsa.comp_left A) hU
  have mXt : A * adjoint wt * (1 - P) * ws * A * adjoint w ∈ hsTraceIdeal H := by
    have hU : IsHilbertSchmidt ((1 - P) * ws * A * adjoint w) :=
      ((hs.comp_left (1 - P)).comp_right A).comp_right (adjoint w)
    rw [show A * adjoint wt * (1 - P) * ws * A * adjoint w =
      (A * adjoint wt) * ((1 - P) * ws * A * adjoint w) by noncomm_ring]
    exact mul_mem_hsTraceIdeal (hta.comp_left A) hU
  have hTs : opTrace (w * (A * adjoint ws * (1 - P) * wt * A * adjoint w)) =
      opTrace (A * adjoint ws * (1 - P) * wt) := by
    rw [opTrace_mul_comm_of_mem mXs w]
    congr 1
    calc A * adjoint ws * (1 - P) * wt * A * adjoint w * w
        = A * adjoint ws * (1 - P) * wt * (A * adjoint w * w) := by noncomm_ring
      _ = A * adjoint ws * (1 - P) * wt := by rw [hAw, mul_assoc _ wt Q, hwtQ]
  have hTt : opTrace (w * (A * adjoint wt * (1 - P) * ws * A * adjoint w)) =
      opTrace (A * adjoint wt * (1 - P) * ws) := by
    rw [opTrace_mul_comm_of_mem mXt w]
    congr 1
    calc A * adjoint wt * (1 - P) * ws * A * adjoint w * w
        = A * adjoint wt * (1 - P) * ws * (A * adjoint w * w) := by noncomm_ring
      _ = A * adjoint wt * (1 - P) * ws := by rw [hAw, mul_assoc _ ws Q, hwsQ]
  have mXs' : w * (A * adjoint ws * (1 - P) * wt * A * adjoint w) ∈ hsTraceIdeal H :=
    hsTraceIdeal_mul_left mXs w
  have mXt' : w * (A * adjoint wt * (1 - P) * ws * A * adjoint w) ∈ hsTraceIdeal H :=
    hsTraceIdeal_mul_left mXt w
  have hR : opTrace (P *
      (((1 - P) * ws * A * adjoint w + w * A * adjoint ws * (1 - P)) *
          ((1 - P) * wt * A * adjoint w + w * A * adjoint wt * (1 - P)) -
       ((1 - P) * wt * A * adjoint w + w * A * adjoint wt * (1 - P)) *
          ((1 - P) * ws * A * adjoint w + w * A * adjoint ws * (1 - P)))) =
      opTrace (A * adjoint ws * (1 - P) * wt) - opTrace (A * adjoint wt * (1 - P) * ws) := by
    rw [mul_sub, hXs, hXt, opTrace_sub_of_mem mXs' mXt', hTs, hTt]
  have hL1 : opTrace (A * adjoint ws * wt) -
      opTrace (A * (adjoint ws * w + adjoint w * ws) * A * adjoint w * wt) =
      opTrace (A * adjoint ws * (1 - P) * wt) - opTrace (Bs * Bt) := by
    rw [hLs, opTrace_add_of_mem m1 m3,
      show A * adjoint ws * (1 - P) * wt = A * adjoint ws * wt - A * adjoint ws * P * wt by
        noncomm_ring, opTrace_sub_of_mem m5 m1]
    ring
  have hL2 : opTrace (A * adjoint wt * ws) -
      opTrace (A * (adjoint wt * w + adjoint w * wt) * A * adjoint w * ws) =
      opTrace (A * adjoint wt * (1 - P) * ws) - opTrace (Bt * Bs) := by
    rw [hLt, opTrace_add_of_mem m2 m4,
      show A * adjoint wt * (1 - P) * ws = A * adjoint wt * ws - A * adjoint wt * P * ws by
        noncomm_ring, opTrace_sub_of_mem m6 m2]
    ring
  rw [hL1, hL2, hR, hcyc]
  ring

end Inverse

end FrameAlgebra

/-! ## Finite-rank operators in the trace ideal -/

section FiniteRank

variable {V : Submodule ℂ H} [FiniteDimensional ℂ V]

theorem isHilbertSchmidt_of_range_le {F : H →L[ℂ] H} (hF : ∀ x, F x ∈ V) :
    IsHilbertSchmidt F :=
  RHTower.isHilbertSchmidt_of_hasRankLE ⟨V, inferInstance, le_rfl, hF⟩

theorem isHilbertSchmidt_starProjection : IsHilbertSchmidt (V.starProjection) :=
  isHilbertSchmidt_of_range_le (Submodule.starProjection_apply_mem V)

omit [CompleteSpace H] in
theorem starProjection_mul_of_range_le {F : H →L[ℂ] H} (hF : ∀ x, F x ∈ V) :
    V.starProjection * F = F := by
  ext x
  simp [Submodule.starProjection_eq_self_iff.mpr (hF x)]

theorem mem_hsTraceIdeal_of_range_le {F : H →L[ℂ] H} (hF : ∀ x, F x ∈ V) :
    F ∈ hsTraceIdeal H := by
  rw [← starProjection_mul_of_range_le hF]
  exact mul_mem_hsTraceIdeal isHilbertSchmidt_starProjection (isHilbertSchmidt_of_range_le hF)

end FiniteRank

/-! ## The connection form on admissible frame families -/

section Connection

variable {Q : H →L[ℂ] H} {V : Submodule ℂ H} [FiniteDimensional ℂ V]

/-- The frame `w = Q + Y` of a Hilbert–Schmidt displacement `Y`. -/
def frameOf (Q : H →L[ℂ] H) (Y : HSpace ℂ H) : H →L[ℂ] H := Q + Y.op

/-- The connection form of the determinant line in the frame `w = Q + Y`:
`α(w)[Ẏ] = Tr(Ĝ⁻¹ w† Ẏ)`. -/
def detConnection (Q : H →L[ℂ] H) (Y Ydot : HSpace ℂ H) : ℂ :=
  opTrace (Ring.inverse (frameGram Q (frameOf Q Y)) * adjoint (frameOf Q Y) * Ydot.op)

/-- Displacements whose `ran Q`-component lies in `V`. -/
def QPartIn (Q : H →L[ℂ] H) (V : Submodule ℂ H) (X : HSpace ℂ H) : Prop := ∀ x, Q (X.op x) ∈ V

variable (V) in
/-- The orthogonal projection onto `V` as a Hilbert–Schmidt operator. -/
def projHS : HSpace ℂ H := HSpace.mk V.starProjection isHilbertSchmidt_starProjection

theorem adjoint_frameOf (hQ : IsSelfAdjoint Q) (Y : HSpace ℂ H) :
    adjoint (frameOf Q Y) = Q + (HSpace.adjointL Y).op := by
  rw [frameOf, map_add, ← star_eq_adjoint Q, hQ.star_eq]
  rfl

/-- The trace `Tr(A w† X)` as a sum of Hilbert–Schmidt pairings, for `X` with `Q`-part in `V`. -/
theorem opTrace_frame_eq (hQ : IsSelfAdjoint Q) (A : H →L[ℂ] H) (Y X : HSpace ℂ H)
    (hX : QPartIn Q V X) :
    opTrace (A * adjoint (frameOf Q Y) * X.op) =
      HSpace.traceL (HSpace.lmulL A (projHS V)) (HSpace.lmulL Q X) +
        HSpace.traceL (HSpace.lmulL A (HSpace.adjointL Y)) X := by
  have hQX : V.starProjection * (Q * X.op) = Q * X.op := starProjection_mul_of_range_le hX
  rw [adjoint_frameOf hQ, mul_add, add_mul]
  simp only [HSpace.traceL_apply, HSpace.op_lmulL, HSpace.op_adjointL]
  have m1 : A * Q * X.op ∈ hsTraceIdeal H := by
    rw [mul_assoc, ← hQX, ← mul_assoc]
    exact mul_mem_hsTraceIdeal (isHilbertSchmidt_starProjection.comp_left A)
      (X.isHS.comp_left Q)
  have m2 : A * adjoint Y.op * X.op ∈ hsTraceIdeal H :=
    mul_mem_hsTraceIdeal (Y.isHS.adjoint.comp_left A) X.isHS
  rw [opTrace_add_of_mem m1 m2]
  congr 1
  rw [show projHS V = HSpace.mk V.starProjection isHilbertSchmidt_starProjection from rfl,
    HSpace.op_mk, mul_assoc A V.starProjection, hQX, mul_assoc]

end Connection

/-! ## Derivatives along curves -/

section Derivatives

variable {Q : H →L[ℂ] H} {V : Submodule ℂ H} [FiniteDimensional ℂ V]

theorem hasDerivAt_op {u : ℝ → HSpace ℂ H} {u' : HSpace ℂ H} {r : ℝ} (hu : HasDerivAt u u' r) :
    HasDerivAt (fun r => (u r).op) u'.op r :=
  ((HSpace.opCLM H).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r hu

theorem hasDerivAt_frameOf {u : ℝ → HSpace ℂ H} {u' : HSpace ℂ H} {r : ℝ}
    (hu : HasDerivAt u u' r) : HasDerivAt (fun r => frameOf Q (u r)) u'.op r := by
  simpa [frameOf] using (hasDerivAt_op hu).const_add Q

theorem hasDerivAt_adjoint_frameOf (hQ : IsSelfAdjoint Q) {u : ℝ → HSpace ℂ H} {u' : HSpace ℂ H}
    {r : ℝ} (hu : HasDerivAt u u' r) :
    HasDerivAt (fun r => adjoint (frameOf Q (u r))) (adjoint u'.op) r := by
  simp only [adjoint_frameOf hQ]
  have h := hasDerivAt_op (HSpace.adjointL.hasFDerivAt.comp_hasDerivAt r hu)
  simpa using h.const_add Q

theorem hasDerivAt_frameGram (hQ : IsSelfAdjoint Q) {u : ℝ → HSpace ℂ H} {u' : HSpace ℂ H}
    {r : ℝ} (hu : HasDerivAt u u' r) :
    HasDerivAt (fun r => frameGram Q (frameOf Q (u r)))
      (adjoint u'.op * frameOf Q (u r) + adjoint (frameOf Q (u r)) * u'.op) r := by
  unfold frameGram
  exact ((hasDerivAt_adjoint_frameOf hQ hu).mul (hasDerivAt_frameOf hu)).add_const _

/-- The inverse Gram operator `A = Ĝ⁻¹` along a curve: `A' = −A Ĝ' A`. -/
theorem hasDerivAt_frameInv (hQ : IsSelfAdjoint Q) {u : ℝ → HSpace ℂ H} {u' : HSpace ℂ H}
    {r : ℝ} (hu : HasDerivAt u u' r) (hunit : IsUnit (frameGram Q (frameOf Q (u r)))) :
    HasDerivAt (fun r => Ring.inverse (frameGram Q (frameOf Q (u r))))
      (-(Ring.inverse (frameGram Q (frameOf Q (u r))) *
        (adjoint u'.op * frameOf Q (u r) + adjoint (frameOf Q (u r)) * u'.op) *
          Ring.inverse (frameGram Q (frameOf Q (u r))))) r := by
  obtain ⟨x, hx⟩ := hunit
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) x).comp_hasDerivAt_of_eq r
    (hasDerivAt_frameGram hQ hu) hx
  refine (h : HasDerivAt (fun r => Ring.inverse (frameGram Q (frameOf Q (u r)))) _ r).congr_deriv ?_
  rw [← hx, Ring.inverse_unit]
  simp [mul_assoc]

/-- **Derivative of the connection form** along a curve of frames `Q + u` and directions `v`:
`d/dr Tr(A w† v) = Tr(A u'† v) − Tr(A Ĝ' A w† v) + Tr(A w† v')`. -/
theorem hasDerivAt_detConnection (hQ : IsSelfAdjoint Q) {u v : ℝ → HSpace ℂ H}
    {u' v' : HSpace ℂ H} {r : ℝ} (hu : HasDerivAt u u' r) (hv : HasDerivAt v v' r)
    (hunit : IsUnit (frameGram Q (frameOf Q (u r))))
    (hvQ : ∀ᶠ r' in nhds r, QPartIn Q V (v r')) (hv'Q : QPartIn Q V v') :
    HasDerivAt (fun r => detConnection Q (u r) (v r))
      (opTrace (Ring.inverse (frameGram Q (frameOf Q (u r))) * adjoint u'.op * (v r).op) -
        opTrace (Ring.inverse (frameGram Q (frameOf Q (u r))) *
          (adjoint u'.op * frameOf Q (u r) + adjoint (frameOf Q (u r)) * u'.op) *
          Ring.inverse (frameGram Q (frameOf Q (u r))) * adjoint (frameOf Q (u r)) * (v r).op) +
        opTrace (Ring.inverse (frameGram Q (frameOf Q (u r))) * adjoint (frameOf Q (u r)) *
          v'.op)) r := by
  set A : ℝ → H →L[ℂ] H := fun r => Ring.inverse (frameGram Q (frameOf Q (u r)))
  set A' := -(A r * (adjoint u'.op * frameOf Q (u r) + adjoint (frameOf Q (u r)) * u'.op) * A r)
  have hA : HasDerivAt A A' r := hasDerivAt_frameInv hQ hu hunit
  -- the representation as Hilbert–Schmidt pairings, valid near `r`
  set F : ℝ → ℂ := fun r => HSpace.traceL (HSpace.lmulL (A r) (projHS V)) (HSpace.lmulL Q (v r)) +
    HSpace.traceL (HSpace.lmulL (A r) (HSpace.adjointL (u r))) (v r)
  have hEq : (fun r => detConnection Q (u r) (v r)) =ᶠ[nhds r] F := by
    filter_upwards [hvQ] with r' hr'
    exact opTrace_frame_eq hQ (A r') (u r') (v r') hr'
  have hPV : HasDerivAt (fun r => HSpace.lmulL (A r) (projHS V)) (HSpace.lmulL A' (projHS V)) r := by
    have := ((HSpace.lmulL (H := H)).flip (projHS V)).hasFDerivAt.comp_hasDerivAt r hA
    simpa [Function.comp_def] using this
  have hQv : HasDerivAt (fun r => HSpace.lmulL Q (v r)) (HSpace.lmulL Q v') r :=
    (HSpace.lmulL Q).hasFDerivAt.comp_hasDerivAt r hv
  have hAdj : HasDerivAt (fun r => HSpace.adjointL (u r)) (HSpace.adjointL u') r :=
    HSpace.adjointL.hasFDerivAt.comp_hasDerivAt r hu
  have hAY : HasDerivAt (fun r => HSpace.lmulL (A r) (HSpace.adjointL (u r)))
      (HSpace.lmulL (A r) (HSpace.adjointL u') + HSpace.lmulL A' (HSpace.adjointL (u r))) r :=
    ContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => hA) (fun _ => hAdj)
  have h1 := ContinuousLinearMap.hasDerivAt_of_bilinear (B := HSpace.traceL)
    (fun _ => hPV) (fun _ => hQv)
  have h2 := ContinuousLinearMap.hasDerivAt_of_bilinear (B := HSpace.traceL)
    (fun _ => hAY) (fun _ => hv)
  refine ((h1.add h2).congr_of_eventuallyEq hEq).congr_deriv ?_
  have hvr : QPartIn Q V (v r) := hvQ.self_of_nhds
  have e1 := opTrace_frame_eq hQ (A r) (u r) v' hv'Q
  have e2 := opTrace_frame_eq hQ A' (u r) (v r) hvr
  have e3 : HSpace.traceL (HSpace.lmulL (A r) (HSpace.adjointL u')) (v r) =
      opTrace (A r * adjoint u'.op * (v r).op) := by
    simp only [HSpace.traceL_apply, HSpace.op_lmulL, HSpace.op_adjointL, mul_assoc]
  have e4 : opTrace (A' * adjoint (frameOf Q (u r)) * (v r).op) =
      -opTrace (A r * (adjoint u'.op * frameOf Q (u r) + adjoint (frameOf Q (u r)) * u'.op) *
        A r * adjoint (frameOf Q (u r)) * (v r).op) := by
    rw [← opTrace_neg']
    congr 1
  rw [map_add, _root_.add_apply, e3]
  have hAr : A r = Ring.inverse (frameGram Q (frameOf Q (u r))) := rfl
  rw [← hAr]
  linear_combination -e1 - e2 + e4

/-- **Derivative of the frame projection** `P = w A w†` along a curve:
`P' = (1 − P) u' A w† + w A u'† (1 − P)`. -/
theorem hasDerivAt_frameProj (hQ : IsSelfAdjoint Q)
    {u : ℝ → HSpace ℂ H} {u' : HSpace ℂ H} {r : ℝ} (hu : HasDerivAt u u' r)
    (hunit : IsUnit (frameGram Q (frameOf Q (u r)))) :
    HasDerivAt (fun r => frameProj (frameOf Q (u r)) (Ring.inverse (frameGram Q (frameOf Q (u r)))))
      ((1 - frameProj (frameOf Q (u r)) (Ring.inverse (frameGram Q (frameOf Q (u r))))) * u'.op *
          Ring.inverse (frameGram Q (frameOf Q (u r))) * adjoint (frameOf Q (u r)) +
        frameOf Q (u r) * Ring.inverse (frameGram Q (frameOf Q (u r))) * adjoint u'.op *
          (1 - frameProj (frameOf Q (u r)) (Ring.inverse (frameGram Q (frameOf Q (u r)))))) r := by
  have hw := hasDerivAt_frameOf (Q := Q) hu
  have hA := hasDerivAt_frameInv hQ hu hunit
  have hwa := hasDerivAt_adjoint_frameOf hQ hu
  have h := (hw.mul hA).mul hwa
  refine h.congr_deriv ?_
  set w := frameOf Q (u r)
  set A := Ring.inverse (frameGram Q w)
  simp only [frameProj]
  noncomm_ring

/-- The admissible displacements: `ran Q`-part in `V`, vanishing off `ran Q`. -/
def admissibleSubspace (Q : H →L[ℂ] H) (V : Submodule ℂ H) : Submodule ℝ (HSpace ℂ H) where
  carrier := {X | QPartIn Q V X ∧ X.op * Q = X.op}
  add_mem' := fun {X Y} hX hY => ⟨fun x => by
      simpa using V.add_mem (hX.1 x) (hY.1 x), by simp [add_mul, hX.2, hY.2]⟩
  zero_mem' := ⟨fun x => by simp, by simp⟩
  smul_mem' := fun c X hX => ⟨fun x => by
      simpa using V.smul_mem (c : ℂ) (hX.1 x), by
      simp only [HSpace.op_smul_real, smul_mul_assoc, hX.2]⟩

theorem isClosed_admissibleSubspace :
    IsClosed (admissibleSubspace Q V : Set (HSpace ℂ H)) := by
  have hV : IsClosed (V : Set H) := V.closed_of_finiteDimensional
  have h1 : IsClosed {X : HSpace ℂ H | QPartIn Q V X} := by
    simp only [QPartIn, Set.setOf_forall]
    exact isClosed_iInter fun x => hV.preimage
      (Q.continuous.comp ((ContinuousLinearMap.apply ℂ H x).continuous.comp
        (HSpace.opCLM H).continuous))
  have h2 : IsClosed {X : HSpace ℂ H | X.op * Q = X.op} :=
    isClosed_eq ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip Q |>.continuous.comp
      (HSpace.opCLM H).continuous) (HSpace.opCLM H).continuous
  exact h1.inter h2

end Derivatives

/-! ## Two-parameter families: the curvature identity -/

section Curvature

variable {Q : H →L[ℂ] H} {V : Submodule ℂ H} [FiniteDimensional ℂ V]

/-- A curve staying in a closed subspace near `r` has its derivative in that subspace. -/
theorem hasDerivAt_mem_of_eventually_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Submodule ℝ E} (hS : IsClosed (S : Set E)) {c : ℝ → E} {c' : E} {r : ℝ}
    (hc : HasDerivAt c c' r) (hmem : ∀ᶠ r' in nhds r, c r' ∈ S) : c' ∈ S := by
  refine hS.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.mp hc) ?_
  filter_upwards [nhdsWithin_le_nhds hmem] with r' hr'
  simp only [slope_def_module, SetLike.mem_coe]
  exact S.smul_mem _ (S.sub_mem hr' hmem.self_of_nhds)

/-- The derivative of a map with values in a closed subspace near `q` lies in that subspace. -/
theorem fderiv_mem_of_eventually_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Submodule ℝ E} (hS : IsClosed (S : Set E)) {f : ℝ × ℝ → E} {q : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f q) (hmem : ∀ᶠ q' in nhds q, f q' ∈ S) (v : ℝ × ℝ) :
    fderiv ℝ f q v ∈ S := by
  have hline : HasDerivAt (fun h : ℝ => q + h • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hc : HasDerivAt (fun h : ℝ => f (q + h • v)) (fderiv ℝ f q v) 0 := by
    have := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
    simpa [Function.comp_def] using this
  refine hasDerivAt_mem_of_eventually_mem hS hc ?_
  have hcont : Continuous fun h : ℝ => q + h • v := by fun_prop
  have ht : Filter.Tendsto (fun h : ℝ => q + h • v) (nhds 0) (nhds q) := by
    simpa using hcont.tendsto 0
  exact ht.eventually hmem

/-- **The curvature of the determinant-line connection** for a `C²` two-parameter family of
admissible frames `Q + Y(s, t)`: the derivatives `Dₛ = ∂ₛ α(∂ₜY)`, `Dₜ = ∂ₜ α(∂ₛY)` and the
derivatives `Pₛ, Pₜ` of the projection `P = w Ĝ⁻¹ w†` satisfy `Dₛ − Dₜ = Tr(P [Pₛ, Pₜ])`. -/
theorem detConnection_curvature (hQ : IsSelfAdjoint Q) (hQi : IsIdempotentElem Q)
    {Y : ℝ × ℝ → HSpace ℂ H} {p : ℝ × ℝ} (hY : ContDiffAt ℝ 2 Y p)
    (hadm : ∀ᶠ q in nhds p, Y q ∈ admissibleSubspace Q V)
    (hunit : IsUnit (frameGram Q (frameOf Q (Y p)))) :
    ∃ Ds Dt Ps Pt : _,
      HasDerivAt (fun s => detConnection Q (Y (s, p.2)) (fderiv ℝ Y (s, p.2) (0, 1))) Ds p.1 ∧
      HasDerivAt (fun t => detConnection Q (Y (p.1, t)) (fderiv ℝ Y (p.1, t) (1, 0))) Dt p.2 ∧
      HasDerivAt (fun s => frameProj (frameOf Q (Y (s, p.2)))
        (Ring.inverse (frameGram Q (frameOf Q (Y (s, p.2)))))) Ps p.1 ∧
      HasDerivAt (fun t => frameProj (frameOf Q (Y (p.1, t)))
        (Ring.inverse (frameGram Q (frameOf Q (Y (p.1, t)))))) Pt p.2 ∧
      Ds - Dt = opTrace (frameProj (frameOf Q (Y p)) (Ring.inverse (frameGram Q (frameOf Q (Y p)))) *
        (Ps * Pt - Pt * Ps)) := by
  obtain ⟨s₀, t₀⟩ := p
  have hS := isClosed_admissibleSubspace (Q := Q) (V := V)
  have hd : DifferentiableAt ℝ Y (s₀, t₀) := hY.differentiableAt (by norm_num)
  have hY1 : ContDiffAt ℝ 1 (fderiv ℝ Y) (s₀, t₀) := hY.fderiv_right (m := 1) (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ Y) (s₀, t₀) := hY1.differentiableAt (by norm_num)
  -- differentiability and admissibility on a neighbourhood
  have hdev : ∀ᶠ q in nhds (s₀, t₀), DifferentiableAt ℝ Y q :=
    (hY.eventually (by norm_num)).mono fun q hq => hq.differentiableAt (by norm_num)
  have hadm1 : ∀ᶠ q in nhds (s₀, t₀), ∀ v, fderiv ℝ Y q v ∈ admissibleSubspace Q V := by
    filter_upwards [hdev, hadm.eventually_nhds] with q hq hq'
    exact fun v => fderiv_mem_of_eventually_mem hS hq hq' v
  -- lines through `(s₀, t₀)`
  have hls : HasDerivAt (fun s : ℝ => (s, t₀)) ((1 : ℝ), (0 : ℝ)) s₀ :=
    (hasDerivAt_id s₀).prodMk (hasDerivAt_const s₀ t₀)
  have hlt : HasDerivAt (fun t : ℝ => (s₀, t)) ((0 : ℝ), (1 : ℝ)) t₀ :=
    (hasDerivAt_const t₀ s₀).prodMk (hasDerivAt_id t₀)
  have hus : HasDerivAt (fun s => Y (s, t₀)) (fderiv ℝ Y (s₀, t₀) (1, 0)) s₀ :=
    hd.hasFDerivAt.comp_hasDerivAt s₀ hls
  have hut : HasDerivAt (fun t => Y (s₀, t)) (fderiv ℝ Y (s₀, t₀) (0, 1)) t₀ :=
    hd.hasFDerivAt.comp_hasDerivAt t₀ hlt
  have hvs : HasDerivAt (fun s => fderiv ℝ Y (s, t₀) (0, 1))
      (fderiv ℝ (fderiv ℝ Y) (s₀, t₀) (1, 0) (0, 1)) s₀ := by
    have := hd2.hasFDerivAt.comp_hasDerivAt s₀ hls
    exact (ContinuousLinearMap.apply ℝ (HSpace ℂ H) ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt
      s₀ this
  have hvt : HasDerivAt (fun t => fderiv ℝ Y (s₀, t) (1, 0))
      (fderiv ℝ (fderiv ℝ Y) (s₀, t₀) (0, 1) (1, 0)) t₀ := by
    have := hd2.hasFDerivAt.comp_hasDerivAt t₀ hlt
    exact (ContinuousLinearMap.apply ℝ (HSpace ℂ H) ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp_hasDerivAt
      t₀ this
  have hsymm : fderiv ℝ (fderiv ℝ Y) (s₀, t₀) (1, 0) (0, 1) =
      fderiv ℝ (fderiv ℝ Y) (s₀, t₀) (0, 1) (1, 0) :=
    (ContDiffAt.isSymmSndFDerivAt hY (by simp)) _ _
  -- admissibility of the first and second derivatives
  have hlines : ∀ᶠ s in nhds s₀, ∀ v, fderiv ℝ Y (s, t₀) v ∈ admissibleSubspace Q V :=
    hls.continuousAt.eventually hadm1
  have hlinet : ∀ᶠ t in nhds t₀, ∀ v, fderiv ℝ Y (s₀, t) v ∈ admissibleSubspace Q V :=
    hlt.continuousAt.eventually hadm1
  have hvsQ : ∀ᶠ s in nhds s₀, QPartIn Q V (fderiv ℝ Y (s, t₀) (0, 1)) :=
    hlines.mono fun s hs => (hs _).1
  have hvtQ : ∀ᶠ t in nhds t₀, QPartIn Q V (fderiv ℝ Y (s₀, t) (1, 0)) :=
    hlinet.mono fun t ht => (ht _).1
  have hst : fderiv ℝ (fderiv ℝ Y) (s₀, t₀) (1, 0) (0, 1) ∈ admissibleSubspace Q V :=
    hasDerivAt_mem_of_eventually_mem hS hvs (hlines.mono fun s hs => hs _)
  have hts : fderiv ℝ (fderiv ℝ Y) (s₀, t₀) (0, 1) (1, 0) ∈ admissibleSubspace Q V :=
    hasDerivAt_mem_of_eventually_mem hS hvt (hlinet.mono fun t ht => ht _)
  have hDs := hasDerivAt_detConnection hQ hus hvs hunit hvsQ hst.1
  have hDt := hasDerivAt_detConnection hQ hut hvt hunit hvtQ hts.1
  have hPs := hasDerivAt_frameProj hQ hus hunit
  have hPt := hasDerivAt_frameProj hQ hut hunit
  refine ⟨_, _, _, _, hDs, hDt, hPs, hPt, ?_⟩
  -- the algebraic curvature identity
  have hYp : Y (s₀, t₀) ∈ admissibleSubspace Q V := hadm.self_of_nhds
  have hwQ : frameOf Q (Y (s₀, t₀)) * Q = frameOf Q (Y (s₀, t₀)) := by
    rw [frameOf, add_mul, hQi.eq, hYp.2]
  have hA := Ring.inverse_mul_cancel _ hunit
  have hA' := Ring.mul_inverse_cancel _ hunit
  have h1 : fderiv ℝ Y (s₀, t₀) (1, 0) ∈ admissibleSubspace Q V := hadm1.self_of_nhds _
  have h2 : fderiv ℝ Y (s₀, t₀) (0, 1) ∈ admissibleSubspace Q V := hadm1.self_of_nhds _
  have key := frame_curvature_trace hQ hQi hwQ hA hA' (fderiv ℝ Y (s₀, t₀) (1, 0)).isHS
    (fderiv ℝ Y (s₀, t₀) (0, 1)).isHS h1.2 h2.2
  rw [← key, hsymm]
  ring

end Curvature

end

end GaloisForLFunctions.HTGeometry
