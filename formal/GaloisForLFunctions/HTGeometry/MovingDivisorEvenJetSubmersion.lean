import GaloisForLFunctions.HTGeometry.MovingDivisorRankGenericity
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalFiniteJetSubmersion

/-!
# Finite jet submersion for the even carrier of a moving divisor

The symmetric carrier `H(z) = L(z) - L(-z)` of a moving divisor is evaluated on the doubled
upper-half-plane packet, and Schwarz reflection turns the second half into the jet of `L(-z)`.  A
surjective real-linear extraction transfers the finite-jet submersion of the odd carrier.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology Filter
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ComplexConjugate

noncomputable section

namespace MovingDivisor

theorem logDerivativeB_conj (Dv : MovingDivisor) (θ : BoundedRealSequence) (z : ℂ) :
    Dv.logDerivativeB θ ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (Dv.logDerivativeB θ z) :=
  realLogDerivative_conj (Dv.zero (θ : ℕ → ℝ)) z

theorem analyticAt_logDerivativeB (Dv : MovingDivisor) (θ : BoundedRealSequence) {z : ℂ}
    (hz : 0 < z.im) : AnalyticAt ℂ (Dv.logDerivativeB θ) z :=
  Dv.analyticAt_logDerivative θ hz

def evenCarrierB (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (z : ℂ) : ℂ :=
  Dv.logDerivativeB θ z -
    Dv.logDerivativeB θ (-z)

/-- Iterated complex derivatives commute with conjugate reflection. -/
theorem iteratedDeriv_logDerivativeB_conj (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (k : ℕ) {z : ℂ} :
    iteratedDeriv k (Dv.logDerivativeB θ)
        ((starRingEnd ℂ) z) =
      (starRingEnd ℂ)
        (iteratedDeriv k (Dv.logDerivativeB θ) z) := by
  have hfun :
      (starRingEnd ℂ) ∘ Dv.logDerivativeB θ ∘
          (starRingEnd ℂ) =
        Dv.logDerivativeB θ := by
    funext w
    simp only [Function.comp_apply]
    rw [MovingDivisor.logDerivativeB_conj, Complex.conj_conj]
  have hder :=
    iteratedDeriv_star_comp_star
      (Dv.logDerivativeB θ) k
  rw [hfun] at hder
  have hz' := congrFun hder ((starRingEnd ℂ) z)
  simpa only [Function.comp_apply, Complex.conj_conj] using hz'

/-- Schwarz reflection transfers analyticity from `conj w` to `w`. -/
theorem analyticAt_logDerivativeB_of_im_ne_zero (Dv : MovingDivisor)
    (θ : BoundedRealSequence) {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ (Dv.logDerivativeB θ) z := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have hupper : 0 < ((starRingEnd ℂ) z).im := by
      simpa using neg_pos.mpr hzneg
    have h :=
      analyticAt_conj_comp_conj_evenLocal
        (Dv.analyticAt_logDerivativeB θ hupper)
    have hfun :
        (fun w => (starRingEnd ℂ)
          (Dv.logDerivativeB θ ((starRingEnd ℂ) w))) =
          Dv.logDerivativeB θ := by
      funext w
      rw [MovingDivisor.logDerivativeB_conj, Complex.conj_conj]
    rwa [hfun] at h
  · exact Dv.analyticAt_logDerivativeB θ hzpos

/-- Exact actual differential jet of the even carrier at an upper-half-plane node. -/
theorem iteratedDeriv_evenCarrierB (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (k : ℕ) {z : ℂ}
    (hz : 0 < z.im) :
    iteratedDeriv k (Dv.evenCarrierB θ) z =
      iteratedDeriv k (Dv.logDerivativeB θ) z -
        (-1 : ℂ) ^ k *
          (starRingEnd ℂ) (iteratedDeriv k
            (Dv.logDerivativeB θ)
            (-((starRingEnd ℂ) z))) := by
  change iteratedDeriv k
      (Dv.logDerivativeB θ -
        fun w => Dv.logDerivativeB θ (-w)) z = _
  rw [iteratedDeriv_sub, iteratedDeriv_comp_neg]
  · congr 1
    have href :=
      Dv.iteratedDeriv_logDerivativeB_conj
        (θ := θ) (k := k)
        (z := -((starRingEnd ℂ) z))
    have harg :
        (starRingEnd ℂ) (-((starRingEnd ℂ) z)) = -z := by
      simp
    rw [harg] at href
    rw [href, smul_eq_mul]
  · exact
      (Dv.analyticAt_logDerivativeB_of_im_ne_zero θ
        (ne_of_gt hz)).contDiffAt
  · have han :=
      Dv.analyticAt_logDerivativeB_of_im_ne_zero θ
        (z := -z) (by simp; exact ne_of_gt hz)
    have hneg : AnalyticAt ℂ (fun w : ℂ => -w) z := by
      fun_prop
    have href : Dv.logDerivativeB θ ∘
        (fun w : ℂ => -w) =
        fun w => Dv.logDerivativeB θ (-w) := rfl
    rw [← href]
    exact (han.comp hneg).contDiffAt

/-- Doubled upper-half-plane packet used to extract even jets. -/
def evenFiniteActualJetFamily (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (evenUpperNodeOrders n)) → ℝ) :
    (Σ i, Fin (n i)) → ℂ :=
  evenJetExtraction n
    (Dv.finiteActualJetFamily
      (evenUpperNodePair x) (evenUpperNodeOrders n) θ p)

/-- The finite even family evaluates the literal iterated derivatives of `H_θ`. -/
theorem evenFiniteActualJetFamily_apply (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (evenUpperNodeOrders n)) → ℝ)
    (s : Σ i, Fin (n i)) :
    Dv.evenFiniteActualJetFamily x n θ p s =
      iteratedDeriv s.2.1
        (Dv.evenCarrierB
          (movingCanonicalFiniteChart
            (movingCanonicalLocationProbeCard
              (evenUpperNodeOrders n)) θ p))
        (x s.1) := by
  rw [Dv.iteratedDeriv_evenCarrierB _ _ (hupper s.1)]
  rfl

/-- Finite-coordinate even-carrier actual jets depend smoothly on all selected locations. -/
theorem contDiff_evenFiniteActualJetFamily (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    ContDiff ℝ ⊤
      (Dv.evenFiniteActualJetFamily x n θ) := by
  exact (evenJetExtraction n).contDiff.comp
    (Dv.contDiff_finiteActualJetFamily
      (evenUpperNodePair x) (evenUpperNodePair_upper x hupper)
      (evenUpperNodeOrders n) θ)

/-- Exact Fréchet derivative of the finite even-jet family. -/
theorem evenFiniteActualJetFamily_hasFDerivAt (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (evenUpperNodeOrders n)) → ℝ) :
    HasFDerivAt
      (Dv.evenFiniteActualJetFamily x n θ)
      ((evenJetExtraction n).comp
        (Dv.finiteParameterJetCLM
          (evenUpperNodePair x) (evenUpperNodeOrders n)
          (movingCanonicalFiniteChart
            (movingCanonicalLocationProbeCard
              (evenUpperNodeOrders n)) θ p)))
      p := by
  have hactual :=
    Dv.finiteActualJetFamily_hasFDerivAt
      (evenUpperNodePair x)
      (evenUpperNodePair_upper x hupper)
      (evenUpperNodeOrders n) θ p
  exact (evenJetExtraction n).hasFDerivAt.comp p hactual

/-- On a sign-and-conjugation-separated packet, the even finite-jet differential is onto. -/
theorem fderiv_evenFiniteActualJetFamily_surjective (Dv : MovingDivisor)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hsep : EvenNodeSeparated x)
    (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (evenUpperNodeOrders n)) → ℝ) :
    Function.Surjective
      (fderiv ℝ
        (Dv.evenFiniteActualJetFamily x n θ) p) := by
  have hderiv :
      fderiv ℝ
          (Dv.evenFiniteActualJetFamily x n θ) p =
        (evenJetExtraction n).comp
          (Dv.finiteParameterJetCLM
            (evenUpperNodePair x) (evenUpperNodeOrders n)
            (movingCanonicalFiniteChart
              (movingCanonicalLocationProbeCard
                (evenUpperNodeOrders n)) θ p)) :=
    (Dv.evenFiniteActualJetFamily_hasFDerivAt
      x hupper n θ p).fderiv
  rw [hderiv]
  exact (evenJetExtraction_surjective n).comp
    (Dv.finiteParameterJetCLM_surjective
      (evenUpperNodePair x) hsep
      (evenUpperNodePair_upper x hupper)
      (evenUpperNodeOrders n)
      (movingCanonicalFiniteChart
        (movingCanonicalLocationProbeCard
          (evenUpperNodeOrders n)) θ p))

end MovingDivisor

end

end GaloisForLFunctions.HTGeometry
