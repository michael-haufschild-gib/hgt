import GaloisForLFunctions.HTGeometry.DeterminantLineGauge
import GaloisForLFunctions.HTGeometry.RestrictedGrassmannianKahlerForm
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBochner
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Stokes' theorem for the determinant-line connection over a rectangle

For a square `q ↦ P₊ + C(q)` in the restricted Grassmannian carrying a `C²` admissible lift
`Q + Y(q)` on an open set `O`, the connection forms `α(∂ₛ)`, `α(∂ₜ)` are `C¹` (they are smooth
Hilbert–Schmidt pairings of the lift and its derivatives), their divergence
`∂ₛ α(∂ₜ) − ∂ₜ α(∂ₛ)` is the curvature density `Tr(P[∂ₛP, ∂ₜP])`, and Green's theorem gives
`∫∫ Tr(P[∂ₛP, ∂ₜP]) = ∮ α` over every rectangle contained in `O`.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A smooth representation of the connection form -/

section Rep

variable {Q : H →L[ℂ] H} {V : Submodule ℂ H} [FiniteDimensional ℂ V]

variable (Q V) in
/-- The connection form as a sum of Hilbert–Schmidt pairings, smooth in `(Y, X)`. -/
def detConnectionRep (Y X : HSpace ℂ H) : ℂ :=
  HSpace.traceL (HSpace.lmulL (Ring.inverse (frameGram Q (frameOf Q Y))) (projHS V))
      (HSpace.lmulL Q X) +
    HSpace.traceL (HSpace.lmulL (Ring.inverse (frameGram Q (frameOf Q Y))) (HSpace.adjointL Y)) X

theorem detConnection_eq_rep (hQ : IsSelfAdjoint Q) (Y X : HSpace ℂ H) (hX : QPartIn Q V X) :
    detConnection Q Y X = detConnectionRep Q V Y X :=
  opTrace_frame_eq hQ _ Y X hX

theorem contDiff_frameGram_frameOf (hQ : IsSelfAdjoint Q) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun Y : HSpace ℂ H => frameGram Q (frameOf Q Y)) := by
  have hop : ContDiff ℝ n (fun Y : HSpace ℂ H => Y.op) :=
    ((HSpace.opCLM H).restrictScalars ℝ).contDiff
  have hadj : ContDiff ℝ n (fun Y : HSpace ℂ H => (HSpace.adjointL Y).op) :=
    ((HSpace.opCLM H).restrictScalars ℝ).contDiff.comp HSpace.adjointL.contDiff
  have heq : (fun Y : HSpace ℂ H => frameGram Q (frameOf Q Y)) =
      fun Y => (Q + (HSpace.adjointL Y).op) * (Q + Y.op) + (1 - Q) := by
    funext Y; unfold frameGram; rw [adjoint_frameOf hQ]; rfl
  rw [heq]
  exact ((contDiff_const.add hadj).mul (contDiff_const.add hop)).add contDiff_const

theorem contDiffAt_detConnectionRep (hQ : IsSelfAdjoint Q) {Y₀ X₀ : HSpace ℂ H}
    (hunit : IsUnit (frameGram Q (frameOf Q Y₀))) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun p : HSpace ℂ H × HSpace ℂ H => detConnectionRep Q V p.1 p.2) (Y₀, X₀) := by
  obtain ⟨x, hx⟩ := hunit
  have hA : ContDiffAt ℝ n (fun p : HSpace ℂ H × HSpace ℂ H =>
      Ring.inverse (frameGram Q (frameOf Q p.1))) (Y₀, X₀) := by
    have h1 : ContDiffAt ℝ n Ring.inverse (frameGram Q (frameOf Q Y₀)) := by
      rw [← hx]; exact contDiffAt_ringInverse ℝ x
    exact h1.comp (Y₀, X₀) ((contDiff_frameGram_frameOf hQ).comp contDiff_fst).contDiffAt
  have h1 : ContDiffAt ℝ n (fun p : HSpace ℂ H × HSpace ℂ H =>
      HSpace.traceL (HSpace.lmulL (Ring.inverse (frameGram Q (frameOf Q p.1))) (projHS V)))
      (Y₀, X₀) :=
    (HSpace.traceL.contDiff.comp ((HSpace.lmulL (H := H)).flip (projHS V)).contDiff).contDiffAt.comp
      _ hA
  have h2 : ContDiffAt ℝ n (fun p : HSpace ℂ H × HSpace ℂ H => HSpace.lmulL Q p.2) (Y₀, X₀) :=
    ((HSpace.lmulL Q).contDiff.comp contDiff_snd).contDiffAt
  have h3 : ContDiffAt ℝ n (fun p : HSpace ℂ H × HSpace ℂ H =>
      HSpace.traceL (HSpace.lmulL (Ring.inverse (frameGram Q (frameOf Q p.1)))
        (HSpace.adjointL p.1))) (Y₀, X₀) := by
    have hL : ContDiffAt ℝ n (fun p : HSpace ℂ H × HSpace ℂ H =>
        HSpace.lmulL (Ring.inverse (frameGram Q (frameOf Q p.1)))) (Y₀, X₀) :=
      (HSpace.lmulL (H := H)).contDiff.contDiffAt.comp (Y₀, X₀) hA
    have hY : ContDiffAt ℝ n (fun p : HSpace ℂ H × HSpace ℂ H => HSpace.adjointL p.1) (Y₀, X₀) :=
      (HSpace.adjointL.contDiff.comp contDiff_fst).contDiffAt
    exact HSpace.traceL.contDiff.contDiffAt.comp _ (hL.clm_apply hY)
  exact (h1.clm_apply h2).add (h3.clm_apply contDiff_snd.contDiffAt)

end Rep

/-! ## Stokes' theorem for a lifted rectangle -/

section Stokes

variable {Q : H →L[ℂ] H} {V : Submodule ℂ H} [FiniteDimensional ℂ V] {Pp : H →L[ℂ] H}
  {C : ℝ × ℝ → SLSpace H} {Y : ℝ × ℝ → HSpace ℂ H} {O : Set (ℝ × ℝ)}

/-- The connection form along `∂ₛ` of a lifted family. -/
def liftConnS (Q : H →L[ℂ] H) (Y : ℝ × ℝ → HSpace ℂ H) (q : ℝ × ℝ) : ℂ :=
  detConnection Q (Y q) (fderiv ℝ Y q (1, 0))

/-- The connection form along `∂ₜ` of a lifted family. -/
def liftConnT (Q : H →L[ℂ] H) (Y : ℝ × ℝ → HSpace ℂ H) (q : ℝ × ℝ) : ℂ :=
  detConnection Q (Y q) (fderiv ℝ Y q (0, 1))

/-- The determinant-line curvature density `Tr(P[∂ₛP, ∂ₜP])` of a square in the restricted
Grassmannian. -/
def squareCurvature (Pp : H →L[ℂ] H) (C : ℝ × ℝ → SLSpace H) (q : ℝ × ℝ) : ℂ :=
  detCurvature (Pp + (C q).op) (fderiv ℝ C q (1, 0)).op (fderiv ℝ C q (0, 1)).op

section Hyp

variable (hQ : IsStarProjection Q) (hO : IsOpen O) (hC : ∀ q ∈ O, ContDiffAt ℝ 2 C q)
  (hY : ∀ q ∈ O, ContDiffAt ℝ 2 Y q)
  (hframe : ∀ q ∈ O, IsFrameOf Q (frameOf Q (Y q)) (Pp + (C q).op))
  (hadm : ∀ q ∈ O, Y q ∈ admissibleSubspace Q V)
include hQ hO hY hframe hadm

/-- The connection forms of a `C²` admissible lift are `C¹`. -/
theorem contDiffAt_liftConn (v : ℝ × ℝ) {q : ℝ × ℝ} (hq : q ∈ O) :
    ContDiffAt ℝ 1 (fun q => detConnection Q (Y q) (fderiv ℝ Y q v)) q := by
  have hS := isClosed_admissibleSubspace (Q := Q) (V := V)
  have hev : ∀ᶠ q' in nhds q, q' ∈ O := hO.mem_nhds hq
  have hrep : (fun q => detConnectionRep Q V (Y q) (fderiv ℝ Y q v)) =ᶠ[nhds q]
      fun q => detConnection Q (Y q) (fderiv ℝ Y q v) := by
    filter_upwards [hev] with q' hq'
    refine (detConnection_eq_rep hQ.isSelfAdjoint _ _ ?_).symm
    refine (fderiv_mem_of_eventually_mem hS ((hY q' hq').differentiableAt (by norm_num))
      (Filter.eventually_of_mem (hO.mem_nhds hq') fun r hr => hadm r hr) v).1
  refine ContDiffAt.congr_of_eventuallyEq ?_ hrep.symm
  have hpair : ContDiffAt ℝ 1 (fun q => (Y q, fderiv ℝ Y q v)) q := by
    refine ((hY q hq).of_le (by norm_num)).prodMk ?_
    exact ((hY q hq).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  exact (contDiffAt_detConnectionRep (V := V) hQ.isSelfAdjoint (hframe q hq).2.1).comp q hpair

include hC in
/-- **The divergence of the lifted connection is the curvature density**:
`∂ₛ α(∂ₜ) − ∂ₜ α(∂ₛ) = Tr(P[∂ₛP, ∂ₜP])`. -/
theorem liftConn_divergence {q : ℝ × ℝ} (hq : q ∈ O) :
    fderiv ℝ (liftConnT Q Y) q (1, 0) - fderiv ℝ (liftConnS Q Y) q (0, 1) =
      squareCurvature Pp C q := by
  have hev : ∀ᶠ q' in nhds q, q' ∈ O := hO.mem_nhds hq
  obtain ⟨Ds, Dt, Ps, Pt, hDs, hDt, hPs, hPt, hid⟩ := detConnection_curvature (V := V)
    hQ.isSelfAdjoint hQ.isIdempotentElem (hY q hq) (hev.mono fun r hr => hadm r hr)
    (hframe q hq).2.1
  have hls : HasDerivAt (fun s : ℝ => (s, q.2)) ((1 : ℝ), (0 : ℝ)) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  have hlt : HasDerivAt (fun t : ℝ => (q.1, t)) ((0 : ℝ), (1 : ℝ)) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have hT : HasDerivAt (fun s => liftConnT Q Y (s, q.2)) (fderiv ℝ (liftConnT Q Y) q (1, 0)) q.1 :=
    ((contDiffAt_liftConn hQ hO hY hframe hadm (0, 1) hq).differentiableAt (by norm_num)
      |>.hasFDerivAt).comp_hasDerivAt_of_eq q.1 hls (by simp)
  have hS : HasDerivAt (fun t => liftConnS Q Y (q.1, t)) (fderiv ℝ (liftConnS Q Y) q (0, 1)) q.2 :=
    ((contDiffAt_liftConn hQ hO hY hframe hadm (1, 0) hq).differentiableAt (by norm_num)
      |>.hasFDerivAt).comp_hasDerivAt_of_eq q.2 hlt (by simp)
  have e1 : fderiv ℝ (liftConnT Q Y) q (1, 0) = Ds := hT.unique hDs
  have e2 : fderiv ℝ (liftConnS Q Y) q (0, 1) = Dt := hS.unique hDt
  -- the projection derivatives are those of the square
  have hCd : DifferentiableAt ℝ C q := (hC q hq).differentiableAt (by norm_num)
  have hPC : ∀ (l : ℝ → ℝ × ℝ) (v : ℝ × ℝ) (r : ℝ), HasDerivAt l v r → l r = q →
      HasDerivAt (fun x => Pp + (C (l x)).op) (fderiv ℝ C q v).op r := by
    intro l v r hl hlr
    have h1 := hCd.hasFDerivAt.comp_hasDerivAt_of_eq r hl hlr.symm
    have h2 := ((SLSpace.opCLM H).hasFDerivAt.comp_hasDerivAt r h1)
    simpa using h2.const_add Pp
  have eP : ∀ (l : ℝ → ℝ × ℝ) (r : ℝ), ContinuousAt l r → l r = q →
      (fun x => frameProj (frameOf Q (Y (l x))) (Ring.inverse (frameGram Q (frameOf Q (Y (l x))))))
        =ᶠ[nhds r] fun x => Pp + (C (l x)).op := by
    intro l r hl hlr
    have : ∀ᶠ x in nhds r, l x ∈ O := hl.eventually (hlr ▸ hev)
    filter_upwards [this] with x hx
    exact (hframe (l x) hx).2.2
  have e3 : Ps = (fderiv ℝ C q (1, 0)).op :=
    (hPs.congr_of_eventuallyEq (eP _ q.1 hls.continuousAt rfl).symm).unique
      (hPC _ _ q.1 hls rfl)
  have e4 : Pt = (fderiv ℝ C q (0, 1)).op :=
    (hPt.congr_of_eventuallyEq (eP _ q.2 hlt.continuousAt rfl).symm).unique
      (hPC _ _ q.2 hlt rfl)
  rw [e1, e2, hid, e3, e4, (hframe q hq).2.2]
  rfl

include hC in
/-- **Stokes' theorem for a lifted rectangle**: the integral of the curvature density over
`[a₁, b₁] × [a₂, b₂]` is the boundary integral of the connection form
(bottom + right − top − left). -/
theorem integral_squareCurvature_eq {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hrect : Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂ ⊆ O) :
    ∫ x in a₁..b₁, ∫ y in a₂..b₂, squareCurvature Pp C (x, y) =
      (∫ x in a₁..b₁, liftConnS Q Y (x, a₂)) + (∫ y in a₂..b₂, liftConnT Q Y (b₁, y)) -
        (∫ x in a₁..b₁, liftConnS Q Y (x, b₂)) - ∫ y in a₂..b₂, liftConnT Q Y (a₁, y) := by
  have hcT := fun q (hq : q ∈ O) => contDiffAt_liftConn hQ hO hY hframe hadm (0, 1) hq
  have hcS := fun q (hq : q ∈ O) => contDiffAt_liftConn hQ hO hY hframe hadm (1, 0) hq
  have hR : Set.uIcc a₁ b₁ ×ˢ Set.uIcc a₂ b₂ = Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂ := by
    rw [Set.uIcc_of_le h₁, Set.uIcc_of_le h₂]
  have hrect' : Set.uIcc a₁ b₁ ×ˢ Set.uIcc a₂ b₂ ⊆ O := hR ▸ hrect
  have hint : ∀ x ∈ Set.Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Set.Ioo (min a₂ b₂) (max a₂ b₂), x ∈ O :=
    fun x hx => hrect' ⟨Set.Ioo_subset_Icc_self hx.1, Set.Ioo_subset_Icc_self hx.2⟩
  have hGreen := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt (liftConnT Q Y)
    (fun q => -liftConnS Q Y q) (fderiv ℝ (liftConnT Q Y)) (fderiv ℝ (fun q => -liftConnS Q Y q))
    a₁ a₂ b₁ b₂
    (fun q hq => (hcT q (hrect' hq)).continuousAt.continuousWithinAt)
    (fun q hq => (hcS q (hrect' hq)).continuousAt.neg.continuousWithinAt)
    (fun q hq => ((hcT q (hint q hq)).differentiableAt (by norm_num)).hasFDerivAt)
    (fun q hq => ((hcS q (hint q hq)).differentiableAt (by norm_num)).neg.hasFDerivAt)
    (by
      refine ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) ?_
      intro q hq
      have h1 := ((hcT q (hrect' hq)).fderiv_right (m := 0) le_rfl).continuousAt
      have h2 := ((hcS q (hrect' hq)).fderiv_right (m := 0) le_rfl).continuousAt
      have h3 : ContinuousAt (fun q => fderiv ℝ (fun q => -liftConnS Q Y q) q) q := by
        have : (fun q => fderiv ℝ (fun q => -liftConnS Q Y q) q) = fun q =>
            -fderiv ℝ (liftConnS Q Y) q := funext fun q => fderiv_neg
        rw [this]; exact h2.neg
      exact ((h1.clm_apply continuousAt_const).add
        (h3.clm_apply continuousAt_const)).continuousWithinAt)
  -- the divergence is the curvature density
  have hdiv : ∀ q ∈ Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂,
      fderiv ℝ (liftConnT Q Y) q (1, 0) + fderiv ℝ (fun q => -liftConnS Q Y q) q (0, 1) =
        squareCurvature Pp C q := by
    intro q hq
    rw [show fderiv ℝ (fun q => -liftConnS Q Y q) q = -fderiv ℝ (liftConnS Q Y) q from fderiv_neg,
      _root_.neg_apply, ← sub_eq_add_neg]
    exact liftConn_divergence hQ hO hC hY hframe hadm (hrect hq)
  have hlhs : (∫ x in a₁..b₁, ∫ y in a₂..b₂,
      fderiv ℝ (liftConnT Q Y) (x, y) (1, 0) + fderiv ℝ (fun q => -liftConnS Q Y q) (x, y) (0, 1)) =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, squareCurvature Pp C (x, y) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le h₁] at hx
    rw [Set.uIcc_of_le h₂] at hy
    exact hdiv (x, y) ⟨hx, hy⟩
  rw [← hlhs, hGreen]
  simp only [intervalIntegral.integral_neg]
  ring

end Hyp

end Stokes

end

end GaloisForLFunctions.HTGeometry
