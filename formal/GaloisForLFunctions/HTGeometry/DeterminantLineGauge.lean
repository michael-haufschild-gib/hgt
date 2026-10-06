import GaloisForLFunctions.HTGeometry.AdmissibleFrameLifts
import GaloisForLFunctions.HTGeometry.FiniteRankDeterminant

/-!
# Gauge transformations of the determinant-line connection

For two frames `u, u'` of the same subspace relative to `Q`, the gauge
`g = Ĝ(u)⁻¹ u† u' + (1 − Q)` satisfies `u g = u'`, is invertible, obeys the cocycle law, and its
defect `g − 1 = (Q u' − Q) − (Q u − Q) g` has finite rank for admissible frames.

* `detConnection_gauge` (**gauge law**): if `Ẏ' = Ẏ g + w ġ` then
  `α(w')[Ẏ'] = α(w)[Ẏ] + Tr(g⁻¹ ġ)`.
* `finiteRankDet_frameGauge_eq`: along an edge carrying two `C²` admissible lifts,
  `det g(b) = det g(a) · exp ∫ₐᵇ (α(w₂) − α(w₁))`.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Gauge transformations between frames of the same subspace -/

section Gauge

variable {Q P u u' u'' : H →L[ℂ] H}

/-- The gauge transformation from the frame `u` to the frame `u'`:
`g = Ĝ(u)⁻¹ u† u' + (1 − Q)`, so that `u' = u g`. -/
def frameGauge (Q u u' : H →L[ℂ] H) : H →L[ℂ] H :=
  Ring.inverse (frameGram Q u) * adjoint u * u' + (1 - Q)

section Basic

variable (hQ : IsStarProjection Q) (hu : IsFrameOf Q u P) (hu' : IsFrameOf Q u' P)
include hQ hu hu'

theorem frame_mul_frameGauge : u * frameGauge Q u u' = u' := by
  have hQi := hQ.isIdempotentElem
  have huQ : u * Q = u := hu.1
  have hA := Ring.inverse_mul_cancel _ hu.2.1
  have hPu' : P * u' = u' := by
    rw [← hu'.2.2]; exact frameProj_mul_frame hQi hu'.1 (Ring.inverse_mul_cancel _ hu'.2.1)
  have hcomp : u * (1 - Q) = 0 := by rw [mul_sub, mul_one, huQ, sub_self]
  unfold frameGauge
  calc u * (Ring.inverse (frameGram Q u) * adjoint u * u' + (1 - Q))
      = frameProj u (Ring.inverse (frameGram Q u)) * u' + u * (1 - Q) := by
        unfold frameProj; noncomm_ring
    _ = u' := by rw [hu.2.2, hPu', hcomp, add_zero]

end Basic

section Support

variable (hQ : IsStarProjection Q) (hu : IsFrameOf Q u P)
include hQ hu

omit hQ hu in
/-- The gauge defect `g − 1 = Ĝ(u)⁻¹ u† u' − Q`. -/
theorem frameGauge_sub_one (u' : H →L[ℂ] H) :
    frameGauge Q u u' - 1 = Ring.inverse (frameGram Q u) * adjoint u * u' - Q := by
  unfold frameGauge; noncomm_ring

/-- The gauge defect is supported in `ran Q`. -/
theorem Q_mul_frameGauge_sub_one (u' : H →L[ℂ] H) :
    Q * (frameGauge Q u u' - 1) = frameGauge Q u u' - 1 := by
  have hQi := hQ.isIdempotentElem
  have hA := Ring.inverse_mul_cancel _ hu.2.1
  have hA' := Ring.mul_inverse_cancel _ hu.2.1
  have hQA := frameInv_comm hQ.isSelfAdjoint hQi hu.1 hA hA'
  have hQu := adjoint_mul_of_mul_eq hQ.isSelfAdjoint hu.1
  rw [frameGauge_sub_one, mul_sub, ← mul_assoc, ← mul_assoc, hQA, mul_assoc _ Q, hQu,
    hQi.eq]

omit hu in
theorem frameGauge_sub_one_mul_Q (hu'Q : u' * Q = u') :
    (frameGauge Q u u' - 1) * Q = frameGauge Q u u' - 1 := by
  rw [frameGauge_sub_one, sub_mul, mul_assoc, hu'Q, hQ.isIdempotentElem.eq]

/-- The gauge from a frame to itself is the identity. -/
theorem frameGauge_self : frameGauge Q u u = 1 := by
  have hA := Ring.inverse_mul_cancel _ hu.2.1
  unfold frameGauge
  rw [frameInv_adjoint_mul hQ.isIdempotentElem hu.1 hA]
  abel

/-- **Uniqueness of the gauge**: if `u g₁ = u g₂` and `g₁ − g₂` is supported in `ran Q`, then
`g₁ = g₂`. -/
theorem eq_of_frame_mul_eq {g₁ g₂ : H →L[ℂ] H} (h : u * g₁ = u * g₂)
    (hsupp : Q * (g₁ - g₂) = g₁ - g₂) : g₁ = g₂ := by
  have hA := Ring.inverse_mul_cancel _ hu.2.1
  have hAu := frameInv_adjoint_mul hQ.isIdempotentElem hu.1 hA
  have h0 : u * (g₁ - g₂) = 0 := by rw [mul_sub, h, sub_self]
  have : Q * (g₁ - g₂) = 0 := by
    rw [← hAu, mul_assoc, h0, mul_zero]
  exact sub_eq_zero.mp (hsupp ▸ this)

end Support

/-- **Cocycle law** for gauges between three frames of the same subspace. -/
theorem frameGauge_mul (hQ : IsStarProjection Q) (hu : IsFrameOf Q u P) (hu' : IsFrameOf Q u' P)
    (hu'' : IsFrameOf Q u'' P) :
    frameGauge Q u u' * frameGauge Q u' u'' = frameGauge Q u u'' := by
  refine eq_of_frame_mul_eq hQ hu ?_ ?_
  · rw [← mul_assoc, frame_mul_frameGauge hQ hu hu', frame_mul_frameGauge hQ hu' hu'',
      frame_mul_frameGauge hQ hu hu'']
  · have e1 := Q_mul_frameGauge_sub_one hQ hu u'
    have e2 := Q_mul_frameGauge_sub_one hQ hu' u''
    have e3 := Q_mul_frameGauge_sub_one hQ hu u''
    have hdec : frameGauge Q u u' * frameGauge Q u' u'' - frameGauge Q u u'' =
        (frameGauge Q u u' - 1) + (frameGauge Q u' u'' - 1) +
          (frameGauge Q u u' - 1) * (frameGauge Q u' u'' - 1) - (frameGauge Q u u'' - 1) := by
      noncomm_ring
    rw [hdec, mul_sub, mul_add, mul_add, ← mul_assoc, e1, e2, e3]

/-- Gauges between frames of the same subspace are invertible. -/
theorem isUnit_frameGauge (hQ : IsStarProjection Q) (hu : IsFrameOf Q u P)
    (hu' : IsFrameOf Q u' P) : IsUnit (frameGauge Q u u') :=
  ⟨⟨frameGauge Q u u', frameGauge Q u' u,
    by rw [frameGauge_mul hQ hu hu' hu, frameGauge_self hQ hu],
    by rw [frameGauge_mul hQ hu' hu hu', frameGauge_self hQ hu']⟩, rfl⟩

/-- **The gauge defect has finite rank**: `g − 1 = R' − R g` with `R = Q u − Q`, `R' = Q u' − Q`. -/
theorem frameGauge_sub_one_eq (hQ : IsStarProjection Q) (hu : IsFrameOf Q u P)
    (hu' : IsFrameOf Q u' P) :
    frameGauge Q u u' - 1 = (Q * u' - Q) - (Q * u - Q) * frameGauge Q u u' := by
  have hg := frame_mul_frameGauge hQ hu hu'
  have e1 := Q_mul_frameGauge_sub_one hQ hu u'
  have hQg : Q * frameGauge Q u u' = (frameGauge Q u u' - 1) + Q := by
    rw [← e1]; noncomm_ring
  calc frameGauge Q u u' - 1 = Q * (u * frameGauge Q u u') - Q -
        (Q * u - Q) * frameGauge Q u u' := by
        rw [show Q * (u * frameGauge Q u u') = (Q * u - Q) * frameGauge Q u u' +
          Q * frameGauge Q u u' by noncomm_ring, hQg]; abel
    _ = (Q * u' - Q) - (Q * u - Q) * frameGauge Q u u' := by rw [hg]

end Gauge


/-! ## The gauge law of the connection -/

section GaugeLaw

variable {Q P : H →L[ℂ] H} {V : Submodule ℂ H} [FiniteDimensional ℂ V]

theorem mem_hsTraceIdeal_adjoint_frame_mul (hQ : IsSelfAdjoint Q) (A : H →L[ℂ] H)
    (Y X : HSpace ℂ H) (hX : QPartIn Q V X) :
    A * adjoint (frameOf Q Y) * X.op ∈ hsTraceIdeal H := by
  rw [adjoint_frameOf hQ, mul_add, add_mul]
  refine add_mem ?_ (mul_mem_hsTraceIdeal (Y.isHS.adjoint.comp_left A) X.isHS)
  rw [mul_assoc]
  exact hsTraceIdeal_mul_left (mem_hsTraceIdeal_of_range_le (F := Q * X.op) hX) A

/-- **Gauge law.**  If `w' = w g` for frames `w = Q + Y`, `w' = Q + Y'` of the same subspace,
and the velocities are related by `Ẏ' = Ẏ g + w ġ` with `ġ` trace class and supported in `ran Q`,
then `α(w')[Ẏ'] = α(w)[Ẏ] + Tr(g⁻¹ ġ)`. -/
theorem detConnection_gauge (hQ : IsStarProjection Q) {Y Y' Yd Yd' : HSpace ℂ H}
    {gd : H →L[ℂ] H} (hw : IsFrameOf Q (frameOf Q Y) P) (hw' : IsFrameOf Q (frameOf Q Y') P)
    (hYd : QPartIn Q V Yd) (hgd : gd ∈ hsTraceIdeal H) (hQgd : Q * gd = gd)
    (hrel : Yd'.op =
      Yd.op * frameGauge Q (frameOf Q Y) (frameOf Q Y') + frameOf Q Y * gd) :
    detConnection Q Y' Yd' = detConnection Q Y Yd +
      opTrace (Ring.inverse (frameGauge Q (frameOf Q Y) (frameOf Q Y')) * gd) := by
  have hQs := hQ.isSelfAdjoint
  have hQi := hQ.isIdempotentElem
  set w := frameOf Q Y
  set w' := frameOf Q Y'
  set g := frameGauge Q w w'
  have hwg : w * g = w' := frame_mul_frameGauge hQ hw hw'
  have hgu : IsUnit g := isUnit_frameGauge hQ hw hw'
  set gi := Ring.inverse g
  have hgi : gi * g = 1 := Ring.inverse_mul_cancel _ hgu
  have hgi' : g * gi = 1 := Ring.mul_inverse_cancel _ hgu
  set A := Ring.inverse (frameGram Q w)
  have hA := Ring.inverse_mul_cancel _ hw.2.1
  have hAw : A * adjoint w * w = Q := frameInv_adjoint_mul hQi hw.1 hA
  -- `(1 − Q) g = 1 − Q`
  have hsupp := Q_mul_frameGauge_sub_one hQ hw w'
  have hcg : (1 - Q) * g = 1 - Q := by
    have : (1 - Q) * (g - 1) = 0 := by rw [sub_mul, one_mul, hsupp, sub_self]
    calc (1 - Q) * g = (1 - Q) * (g - 1) + (1 - Q) := by noncomm_ring
      _ = 1 - Q := by rw [this, zero_add]
  have hcgadj : adjoint g * (1 - Q) = 1 - Q := by
    have := congrArg star hcg
    rwa [star_mul, star_sub, star_one, hQs.star_eq, star_eq_adjoint] at this
  have hw'adj : adjoint w' = adjoint g * adjoint w := by
    rw [← hwg, ← star_eq_adjoint (w * g), star_mul, star_eq_adjoint, star_eq_adjoint]
  -- the Gram operator transforms by `g† Ĝ g`
  have hGram : frameGram Q w' = adjoint g * frameGram Q w * g := by
    have h3 : adjoint g * (1 - Q) * g = 1 - Q := by rw [hcgadj, hcg]
    unfold frameGram
    rw [hw'adj, ← hwg]
    calc adjoint g * adjoint w * (w * g) + (1 - Q)
        = adjoint g * (adjoint w * w) * g + adjoint g * (1 - Q) * g := by rw [h3]; noncomm_ring
      _ = adjoint g * (adjoint w * w + (1 - Q)) * g := by noncomm_ring
  have hgadj : adjoint gi * adjoint g = 1 := by
    rw [← star_eq_adjoint, ← star_eq_adjoint, ← star_mul, hgi', star_one]
  -- the transformed inverse Gram operator
  have hA' : Ring.inverse (frameGram Q w') = gi * A * adjoint gi := by
    have hunit' := hw'.2.1
    have h1 : gi * A * adjoint gi * frameGram Q w' = 1 := by
      rw [hGram]
      calc gi * A * adjoint gi * (adjoint g * frameGram Q w * g)
          = gi * (A * frameGram Q w) * g := by
            rw [show gi * A * adjoint gi * (adjoint g * frameGram Q w * g) =
              gi * A * (adjoint gi * adjoint g) * frameGram Q w * g by noncomm_ring, hgadj]
            noncomm_ring
        _ = 1 := by rw [hA, mul_one, hgi]
    calc Ring.inverse (frameGram Q w') =
        (gi * A * adjoint gi * frameGram Q w') * Ring.inverse (frameGram Q w') := by
          rw [h1, one_mul]
      _ = gi * A * adjoint gi := by
          rw [mul_assoc, Ring.mul_inverse_cancel _ hunit', mul_one]
  -- the connection forms
  have hkey : Ring.inverse (frameGram Q w') * adjoint w' * Yd'.op =
      gi * (A * adjoint w * Yd.op) * g + gi * gd := by
    rw [hA', hw'adj, hrel]
    calc gi * A * adjoint gi * (adjoint g * adjoint w) * (Yd.op * g + w * gd)
        = gi * A * (adjoint gi * adjoint g) * adjoint w * Yd.op * g +
            gi * A * (adjoint gi * adjoint g) * (adjoint w * w) * gd := by noncomm_ring
      _ = gi * (A * adjoint w * Yd.op) * g + gi * (A * adjoint w * w) * gd := by
          rw [hgadj]; noncomm_ring
      _ = gi * (A * adjoint w * Yd.op) * g + gi * gd := by
          rw [hAw, mul_assoc gi Q gd, hQgd]
  have hmem : A * adjoint w * Yd.op ∈ hsTraceIdeal H :=
    mem_hsTraceIdeal_adjoint_frame_mul hQs A Y Yd hYd
  have hconj : opTrace (gi * (A * adjoint w * Yd.op) * g) = opTrace (A * adjoint w * Yd.op) := by
    rw [mul_assoc, opTrace_mul_comm_of_mem (hsTraceIdeal_mul_right hmem g) gi, mul_assoc, hgi',
      mul_one]
  unfold detConnection
  rw [hkey, opTrace_add_of_mem (hsTraceIdeal_mul_right (hsTraceIdeal_mul_left hmem gi) g)
    (hsTraceIdeal_mul_left hgd gi), hconj]

end GaugeLaw

/-! ## Gauge transformations along curves -/

section Curves

variable {Q : H →L[ℂ] H} {V₁ V₂ : Submodule ℂ H} [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂]

/-- The gauge between two frame curves is differentiable, with the product-rule derivative. -/
theorem hasDerivAt_frameGauge (hQ : IsStarProjection Q) {Y₁ Y₂ : ℝ → HSpace ℂ H}
    {Y₁' Y₂' : HSpace ℂ H} {r : ℝ} (h₁ : HasDerivAt Y₁ Y₁' r) (h₂ : HasDerivAt Y₂ Y₂' r)
    (hunit : IsUnit (frameGram Q (frameOf Q (Y₁ r)))) :
    HasDerivAt (fun r => frameGauge Q (frameOf Q (Y₁ r)) (frameOf Q (Y₂ r)))
      ((-(Ring.inverse (frameGram Q (frameOf Q (Y₁ r))) *
          (adjoint Y₁'.op * frameOf Q (Y₁ r) + adjoint (frameOf Q (Y₁ r)) * Y₁'.op) *
            Ring.inverse (frameGram Q (frameOf Q (Y₁ r)))) * adjoint (frameOf Q (Y₁ r)) +
          Ring.inverse (frameGram Q (frameOf Q (Y₁ r))) * adjoint Y₁'.op) *
          frameOf Q (Y₂ r) +
        Ring.inverse (frameGram Q (frameOf Q (Y₁ r))) * adjoint (frameOf Q (Y₁ r)) * Y₂'.op) r := by
  have hA := hasDerivAt_frameInv hQ.isSelfAdjoint h₁ hunit
  have hadj := hasDerivAt_adjoint_frameOf hQ.isSelfAdjoint h₁
  have hw₂ := hasDerivAt_frameOf (Q := Q) h₂
  exact ((hA.mul hadj).mul hw₂).add_const (1 - Q)

/-- **The connection along an edge, compared between two lifts.**  For two `C²` curves of
admissible frames `Q + Y₁(r)`, `Q + Y₂(r)` of the same subspaces on an open `U ⊇ [a, b]`, with
gauge `g(r)`: `det g(b) = det g(a) · exp ∫ₐᵇ (α(Y₂)[Y₂'] − α(Y₁)[Y₁'])`. -/
theorem finiteRankDet_frameGauge_eq (hQ : IsStarProjection Q) {Y₁ Y₂ Y₁' Y₂' Y₁'' Y₂'' :
    ℝ → HSpace ℂ H} {P : ℝ → H →L[ℂ] H} {a b : ℝ} (hab : a ≤ b) {U : Set ℝ} (hU : IsOpen U)
    (hIcc : Set.Icc a b ⊆ U)
    (h₁ : ∀ r ∈ U, HasDerivAt Y₁ (Y₁' r) r) (h₂ : ∀ r ∈ U, HasDerivAt Y₂ (Y₂' r) r)
    (h₁' : ∀ r ∈ U, HasDerivAt Y₁' (Y₁'' r) r) (h₂' : ∀ r ∈ U, HasDerivAt Y₂' (Y₂'' r) r)
    (hf₁ : ∀ r ∈ U, IsFrameOf Q (frameOf Q (Y₁ r)) (P r))
    (hf₂ : ∀ r ∈ U, IsFrameOf Q (frameOf Q (Y₂ r)) (P r))
    (ha₁ : ∀ r ∈ U, Y₁ r ∈ admissibleSubspace Q V₁)
    (ha₂ : ∀ r ∈ U, Y₂ r ∈ admissibleSubspace Q V₂) :
    finiteRankDet (frameGauge Q (frameOf Q (Y₁ b)) (frameOf Q (Y₂ b))) =
      finiteRankDet (frameGauge Q (frameOf Q (Y₁ a)) (frameOf Q (Y₂ a))) *
        Complex.exp (∫ r in a..b, (detConnection Q (Y₂ r) (Y₂' r) -
          detConnection Q (Y₁ r) (Y₁' r))) := by
  set g : ℝ → H →L[ℂ] H := fun r => frameGauge Q (frameOf Q (Y₁ r)) (frameOf Q (Y₂ r))
  have hS₁ := isClosed_admissibleSubspace (Q := Q) (V := V₁)
  have hS₂ := isClosed_admissibleSubspace (Q := Q) (V := V₂)
  have hev : ∀ r ∈ U, ∀ᶠ s in nhds r, s ∈ U := fun r hr => hU.mem_nhds hr
  -- admissibility of the velocities
  have hv₁ : ∀ r ∈ U, QPartIn Q V₁ (Y₁' r) := fun r hr =>
    (hasDerivAt_mem_of_eventually_mem hS₁ (h₁ r hr)
      ((hev r hr).mono fun s hs => ha₁ s hs)).1
  have hv₂ : ∀ r ∈ U, QPartIn Q V₂ (Y₂' r) := fun r hr =>
    (hasDerivAt_mem_of_eventually_mem hS₂ (h₂ r hr)
      ((hev r hr).mono fun s hs => ha₂ s hs)).1
  -- the gauge defect lies in `V₁ ⊔ V₂`
  set V := V₁ ⊔ V₂
  have hdefect : ∀ r ∈ U, ∀ x, g r x - x ∈ V := by
    intro r hr x
    have heq := frameGauge_sub_one_eq hQ (hf₁ r hr) (hf₂ r hr)
    have hx : g r x - x = (frameGauge Q (frameOf Q (Y₁ r)) (frameOf Q (Y₂ r)) - 1) x := by
      simp [g]
    rw [hx, heq, sub_apply]
    have hR : ∀ (Y : HSpace ℂ H) (W : Submodule ℂ H), QPartIn Q W Y → ∀ z,
        (Q * frameOf Q Y - Q) z ∈ W := by
      intro Y W hY z
      have : (Q * frameOf Q Y - Q) z = Q (Y.op z) := by
        simp only [frameOf, mul_add, sub_apply, add_apply, mul_apply_eq_comp,
          hQ.isIdempotentElem.eq]
        simp
      rw [this]; exact hY z
    exact V.sub_mem (Submodule.mem_sup_right (hR _ _ (ha₂ r hr).1 x))
      (Submodule.mem_sup_left (hR _ _ (ha₁ r hr).1 _))
  -- the derivative of the gauge
  have hunit₁ : ∀ r ∈ U, IsUnit (frameGram Q (frameOf Q (Y₁ r))) := fun r hr => (hf₁ r hr).2.1
  set gd : ℝ → H →L[ℂ] H := fun r =>
    (-(Ring.inverse (frameGram Q (frameOf Q (Y₁ r))) *
          (adjoint (Y₁' r).op * frameOf Q (Y₁ r) + adjoint (frameOf Q (Y₁ r)) * (Y₁' r).op) *
            Ring.inverse (frameGram Q (frameOf Q (Y₁ r)))) * adjoint (frameOf Q (Y₁ r)) +
          Ring.inverse (frameGram Q (frameOf Q (Y₁ r))) * adjoint (Y₁' r).op) *
          frameOf Q (Y₂ r) +
        Ring.inverse (frameGram Q (frameOf Q (Y₁ r))) * adjoint (frameOf Q (Y₁ r)) * (Y₂' r).op
  have hgd : ∀ r ∈ U, HasDerivAt g (gd r) r := fun r hr =>
    hasDerivAt_frameGauge hQ (h₁ r hr) (h₂ r hr) (hunit₁ r hr)
  have hdefev : ∀ r ∈ U, ∀ᶠ s in nhds r, ∀ x, g s x - x ∈ V := fun r hr =>
    (hev r hr).mono fun s hs => hdefect s hs
  have hgdV : ∀ r ∈ U, ∀ x, gd r x ∈ V := fun r hr =>
    deriv_mem_of_defect_mem (hdefev r hr) (hgd r hr)
  have hgdmem : ∀ r ∈ U, gd r ∈ hsTraceIdeal H := fun r hr =>
    mem_hsTraceIdeal_of_range_le (hgdV r hr)
  have hQgd : ∀ r ∈ U, Q * gd r = gd r := by
    intro r hr
    have hd1 : HasDerivAt (fun s => g s - 1) (gd r) r := (hgd r hr).sub_const 1
    have hd2 : HasDerivAt (fun s => Q * (g s - 1)) (Q * gd r) r := by
      simpa using hd1.const_mul Q
    have heq : (fun s => Q * (g s - 1)) =ᶠ[nhds r] fun s => g s - 1 :=
      (hev r hr).mono fun s hs => Q_mul_frameGauge_sub_one hQ (hf₁ s hs) _
    exact (hd2.congr_of_eventuallyEq heq.symm).unique hd1
  -- the velocities are related by `Y₂' = Y₁' g + w₁ ġ`
  have hrel : ∀ r ∈ U, (Y₂' r).op = (Y₁' r).op * g r + frameOf Q (Y₁ r) * gd r := by
    intro r hr
    have hd1 : HasDerivAt (fun s => frameOf Q (Y₂ s)) (Y₂' r).op r :=
      hasDerivAt_frameOf (h₂ r hr)
    have hd2 : HasDerivAt (fun s => frameOf Q (Y₁ s) * g s)
        ((Y₁' r).op * g r + frameOf Q (Y₁ r) * gd r) r :=
      (hasDerivAt_frameOf (h₁ r hr)).mul (hgd r hr)
    have heq : (fun s => frameOf Q (Y₁ s) * g s) =ᶠ[nhds r] fun s => frameOf Q (Y₂ s) :=
      (hev r hr).mono fun s hs => frame_mul_frameGauge hQ (hf₁ s hs) (hf₂ s hs)
    exact (hd2.congr_of_eventuallyEq heq.symm).unique hd1 |>.symm
  -- the gauge law along the edge
  have hlaw : ∀ r ∈ U, detConnection Q (Y₂ r) (Y₂' r) - detConnection Q (Y₁ r) (Y₁' r) =
      opTrace (Ring.inverse (g r) * gd r) := by
    intro r hr
    rw [detConnection_gauge hQ (hf₁ r hr) (hf₂ r hr) (hv₁ r hr) (hgdmem r hr) (hQgd r hr)
      (hrel r hr)]
    ring
  -- continuity of the connection forms along the edge
  have hα : ∀ (Yc Yc' Yc'' : ℝ → HSpace ℂ H) (W : Submodule ℂ H) [FiniteDimensional ℂ W],
      (∀ r ∈ U, HasDerivAt Yc (Yc' r) r) → (∀ r ∈ U, HasDerivAt Yc' (Yc'' r) r) →
      (∀ r ∈ U, IsUnit (frameGram Q (frameOf Q (Yc r)))) →
      (∀ r ∈ U, Yc r ∈ admissibleSubspace Q W) →
      ContinuousOn (fun r => detConnection Q (Yc r) (Yc' r)) U := by
    intro Yc Yc' Yc'' W _ hd hd' hu hadm r hr
    have hSW := isClosed_admissibleSubspace (Q := Q) (V := W)
    have hYc' : ∀ s ∈ U, Yc' s ∈ admissibleSubspace Q W := fun s hs =>
      hasDerivAt_mem_of_eventually_mem hSW (hd s hs) ((hev s hs).mono fun t ht => hadm t ht)
    have hYc'' : Yc'' r ∈ admissibleSubspace Q W :=
      hasDerivAt_mem_of_eventually_mem hSW (hd' r hr) ((hev r hr).mono fun t ht => hYc' t ht)
    exact (hasDerivAt_detConnection hQ.isSelfAdjoint (hd r hr) (hd' r hr) (hu r hr)
      ((hev r hr).mono fun t ht => (hYc' t ht).1) hYc''.1).continuousAt.continuousWithinAt
  have hc₁ := hα Y₁ Y₁' Y₁'' V₁ h₁ h₁' hunit₁ ha₁
  have hc₂ := hα Y₂ Y₂' Y₂'' V₂ h₂ h₂' (fun r hr => (hf₂ r hr).2.1) ha₂
  have hτ : ContinuousOn (fun r => opTrace (Ring.inverse (g r) * gd r)) (Set.Icc a b) :=
    ((hc₂.sub hc₁).mono hIcc).congr fun r hr => (hlaw r (hIcc hr)).symm
  have hmain := finiteRankDet_eq_mul_exp_integral (V := V) hab hU hIcc hdefect hgd
    (fun r hr => isUnit_frameGauge hQ (hf₁ r hr) (hf₂ r hr)) hτ
  rw [hmain]
  congr 2
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [Set.uIcc_of_le hab] at hr
  exact (hlaw r (hIcc hr)).symm

end Curves

end

end GaloisForLFunctions.HTGeometry
