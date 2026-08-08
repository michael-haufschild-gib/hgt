import GaloisForLFunctions.HTGeometry.MovingCanonicalFullTranslationFreeness
import GaloisForLFunctions.HTGeometry.CompactCauchyRowPacketAtlas
import GaloisForLFunctions.HTGeometry.CarrierCauchy
import Mathlib.Analysis.Complex.CauchyIntegral
import GaloisForLFunctions.HTGeometry.AnalyticConjReflection

/-!
# Finite-jet submersion for the even moving canonical carrier

For the moving unit-residue canonical carrier `M_θ`, define

`H_θ(z) = M_θ(z) - M_θ(-z)`.

This file proves the exact finite-dimensional submersion required by the
functional-equation-even strengthening.  The main device is to evaluate `M_θ` on the doubled
upper-half-plane packet `x_i, -conj x_i`.  Schwarz reflection then turns the second packet into
the jet of `M_θ(-z)`.  A surjective real-linear extraction transfers the already established
canonical finite-jet submersion to `H_θ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology Filter
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ComplexConjugate

noncomputable section

/-- Odd carrier associated with the symmetric canonical divisor `±Λ_j(θ)`. -/
def movingEvenCanonicalCarrier
    (θ : BoundedRealSequence) (z : ℂ) : ℂ :=
  movingCanonicalLogDerivative θ z -
    movingCanonicalLogDerivative θ (-z)

/-- The moving canonical logarithmic derivative is Schwarz-real. -/
theorem movingCanonicalLogDerivative_conj
    (θ : BoundedRealSequence) (z : ℂ) :
    movingCanonicalLogDerivative θ ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (movingCanonicalLogDerivative θ z) := by
  let f : ℕ → ℂ := fun n =>
    ((movingCanonicalZero θ n : ℂ) - z)⁻¹ -
      (movingCanonicalZero θ n : ℂ)⁻¹
  let g : ℕ → ℂ := fun n =>
    ((movingCanonicalZero θ n : ℂ) - (starRingEnd ℂ) z)⁻¹ -
      (movingCanonicalZero θ n : ℂ)⁻¹
  have hgf : g = fun n => (starRingEnd ℂ) (f n) := by
    funext n
    simp [f, g]
  rw [movingCanonicalLogDerivative, movingCanonicalLogDerivative]
  change ∑' n, g n = (starRingEnd ℂ) (∑' n, f n)
  rw [hgf]
  exact (Complex.conjCLE.map_tsum).symm

/-- Iterated complex derivatives commute with conjugate reflection. -/
theorem iteratedDeriv_star_comp_star
    (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n
        ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘
        (starRingEnd ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih,
        deriv_conj_conj]

/-- Every actual differential jet of the moving canonical carrier is Schwarz-real. -/
theorem iteratedDeriv_movingCanonicalLogDerivative_conj
    (θ : BoundedRealSequence) (k : ℕ) {z : ℂ} :
    iteratedDeriv k (movingCanonicalLogDerivative θ)
        ((starRingEnd ℂ) z) =
      (starRingEnd ℂ)
        (iteratedDeriv k (movingCanonicalLogDerivative θ) z) := by
  have hfun :
      (starRingEnd ℂ) ∘ movingCanonicalLogDerivative θ ∘
          (starRingEnd ℂ) =
        movingCanonicalLogDerivative θ := by
    funext w
    simp only [Function.comp_apply]
    rw [movingCanonicalLogDerivative_conj, Complex.conj_conj]
  have hder :=
    iteratedDeriv_star_comp_star
      (movingCanonicalLogDerivative θ) k
  rw [hfun] at hder
  have hz' := congrFun hder ((starRingEnd ℂ) z)
  simpa only [Function.comp_apply, Complex.conj_conj] using hz'

/-- Schwarz reflection transfers analyticity from `conj w` to `w`. -/
theorem analyticAt_conj_comp_conj_evenLocal
    {H : ℂ → ℂ} {w : ℂ}
    (hH : AnalyticAt ℂ H ((starRingEnd ℂ) w)) :
    AnalyticAt ℂ
      (fun z => (starRingEnd ℂ) (H ((starRingEnd ℂ) z))) w :=
  hH.conj_comp_conj

/-- The moving canonical carrier is analytic at every nonreal point, in either half-plane. -/
theorem analyticAt_movingCanonicalLogDerivative_of_im_ne_zero
    (θ : BoundedRealSequence) {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ (movingCanonicalLogDerivative θ) z := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have hupper : 0 < ((starRingEnd ℂ) z).im := by
      simpa using neg_pos.mpr hzneg
    have h :=
      analyticAt_conj_comp_conj_evenLocal
        (analyticAt_movingCanonicalLogDerivative θ hupper)
    have hfun :
        (fun w => (starRingEnd ℂ)
          (movingCanonicalLogDerivative θ ((starRingEnd ℂ) w))) =
          movingCanonicalLogDerivative θ := by
      funext w
      rw [movingCanonicalLogDerivative_conj, Complex.conj_conj]
    rwa [hfun] at h
  · exact analyticAt_movingCanonicalLogDerivative θ hzpos

/-- Exact actual differential jet of the even carrier at an upper-half-plane node. -/
theorem iteratedDeriv_movingEvenCanonicalCarrier
    (θ : BoundedRealSequence) (k : ℕ) {z : ℂ}
    (hz : 0 < z.im) :
    iteratedDeriv k (movingEvenCanonicalCarrier θ) z =
      iteratedDeriv k (movingCanonicalLogDerivative θ) z -
        (-1 : ℂ) ^ k *
          (starRingEnd ℂ) (iteratedDeriv k
            (movingCanonicalLogDerivative θ)
            (-((starRingEnd ℂ) z))) := by
  change iteratedDeriv k
      (movingCanonicalLogDerivative θ -
        fun w => movingCanonicalLogDerivative θ (-w)) z = _
  rw [iteratedDeriv_sub, iteratedDeriv_comp_neg]
  · congr 1
    have href :=
      iteratedDeriv_movingCanonicalLogDerivative_conj
        (θ := θ) (k := k)
        (z := -((starRingEnd ℂ) z))
    have harg :
        (starRingEnd ℂ) (-((starRingEnd ℂ) z)) = -z := by
      simp
    rw [harg] at href
    rw [href, smul_eq_mul]
  · exact
      (analyticAt_movingCanonicalLogDerivative_of_im_ne_zero θ
        (ne_of_gt hz)).contDiffAt
  · have han :=
      analyticAt_movingCanonicalLogDerivative_of_im_ne_zero θ
        (z := -z) (by simp; exact ne_of_gt hz)
    have hneg : AnalyticAt ℂ (fun w : ℂ => -w) z := by
      fun_prop
    have href : movingCanonicalLogDerivative θ ∘
        (fun w : ℂ => -w) =
        fun w => movingCanonicalLogDerivative θ (-w) := rfl
    rw [← href]
    exact (han.comp hneg).contDiffAt

/-- Doubled upper-half-plane packet used to extract even jets. -/
def evenUpperNodePair {ι : Type*} (x : ι → ℂ) :
    ι ⊕ ι → ℂ :=
  Sum.elim x (fun i => -(starRingEnd ℂ) (x i))

/-- Separation condition for the full sign-and-conjugation packet. -/
def EvenNodeSeparated {ι : Type*} (x : ι → ℂ) : Prop :=
  Function.Injective (evenUpperNodePair x)

/-- Both halves of the doubled packet remain in the upper half-plane. -/
theorem evenUpperNodePair_upper
    {ι : Type*} (x : ι → ℂ)
    (hupper : ∀ i, 0 < (x i).im) :
    ∀ q, 0 < (evenUpperNodePair x q).im := by
  intro q
  cases q with
  | inl i => exact hupper i
  | inr i =>
      simp [evenUpperNodePair]
      exact hupper i

/-- Duplicate each jet order across the two halves of the upper packet. -/
def evenUpperNodeOrders
    {ι : Type*} (n : ι → ℕ) : ι ⊕ ι → ℕ :=
  Sum.elim n n

/-- Real-linear extraction taking doubled canonical jets to actual even-carrier jets. -/
def evenJetExtraction
    {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    ((Σ q : ι ⊕ ι, Fin (evenUpperNodeOrders n q)) → ℂ) →L[ℝ]
      ((Σ i, Fin (n i)) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y s =>
        y ⟨Sum.inl s.1, s.2⟩ -
          (-1 : ℂ) ^ s.2.1 *
            (starRingEnd ℂ) (y ⟨Sum.inr s.1, s.2⟩)
      map_add' := by
        intro y y'
        funext s
        simp
        ring
      map_smul' := by
        intro r y
        funext s
        simp
        ring }

/-- The even-jet extraction has a right inverse and is therefore surjective. -/
theorem evenJetExtraction_surjective
    {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    Function.Surjective (evenJetExtraction n) := by
  intro y
  let y' : (Σ q : ι ⊕ ι,
      Fin (evenUpperNodeOrders n q)) → ℂ :=
    fun s => match s with
      | ⟨Sum.inl i, j⟩ => y ⟨i, j⟩
      | ⟨Sum.inr _, _⟩ => 0
  refine ⟨y', ?_⟩
  funext s
  change y' ⟨Sum.inl s.1, s.2⟩ -
      (-1 : ℂ) ^ s.2.1 *
        (starRingEnd ℂ) (y' ⟨Sum.inr s.1, s.2⟩) =
    y s
  simp [y']

/-- Finite-coordinate family of actual even-carrier differential jets. -/
def movingEvenCanonicalFiniteActualJetFamily
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (evenUpperNodeOrders n)) → ℝ) :
    (Σ i, Fin (n i)) → ℂ :=
  evenJetExtraction n
    (movingCanonicalFiniteActualJetFamily
      (evenUpperNodePair x) (evenUpperNodeOrders n) θ p)

/-- The finite even family evaluates the literal iterated derivatives of `H_θ`. -/
theorem movingEvenCanonicalFiniteActualJetFamily_apply
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (evenUpperNodeOrders n)) → ℝ)
    (s : Σ i, Fin (n i)) :
    movingEvenCanonicalFiniteActualJetFamily x n θ p s =
      iteratedDeriv s.2.1
        (movingEvenCanonicalCarrier
          (movingCanonicalFiniteChart
            (movingCanonicalLocationProbeCard
              (evenUpperNodeOrders n)) θ p))
        (x s.1) := by
  rw [iteratedDeriv_movingEvenCanonicalCarrier _ _ (hupper s.1)]
  rfl

/-- Finite-coordinate even-carrier actual jets depend smoothly on all selected locations. -/
theorem contDiff_movingEvenCanonicalFiniteActualJetFamily
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    ContDiff ℝ ⊤
      (movingEvenCanonicalFiniteActualJetFamily x n θ) := by
  exact (evenJetExtraction n).contDiff.comp
    (contDiff_movingCanonicalFiniteActualJetFamily
      (evenUpperNodePair x) (evenUpperNodePair_upper x hupper)
      (evenUpperNodeOrders n) θ)

/-- Exact Fréchet derivative of the finite even-jet family. -/
theorem movingEvenCanonicalFiniteActualJetFamily_hasFDerivAt
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (evenUpperNodeOrders n)) → ℝ) :
    HasFDerivAt
      (movingEvenCanonicalFiniteActualJetFamily x n θ)
      ((evenJetExtraction n).comp
        (movingCanonicalFiniteParameterJetCLM
          (evenUpperNodePair x) (evenUpperNodeOrders n)
          (movingCanonicalFiniteChart
            (movingCanonicalLocationProbeCard
              (evenUpperNodeOrders n)) θ p)))
      p := by
  have hactual :=
    movingCanonicalFiniteActualJetFamily_hasFDerivAt
      (evenUpperNodePair x)
      (evenUpperNodePair_upper x hupper)
      (evenUpperNodeOrders n) θ p
  exact (evenJetExtraction n).hasFDerivAt.comp p hactual

/-- On a sign-and-conjugation-separated packet, the even finite-jet differential is onto. -/
theorem fderiv_movingEvenCanonicalFiniteActualJetFamily_surjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hsep : EvenNodeSeparated x)
    (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (evenUpperNodeOrders n)) → ℝ) :
    Function.Surjective
      (fderiv ℝ
        (movingEvenCanonicalFiniteActualJetFamily x n θ) p) := by
  have hderiv :
      fderiv ℝ
          (movingEvenCanonicalFiniteActualJetFamily x n θ) p =
        (evenJetExtraction n).comp
          (movingCanonicalFiniteParameterJetCLM
            (evenUpperNodePair x) (evenUpperNodeOrders n)
            (movingCanonicalFiniteChart
              (movingCanonicalLocationProbeCard
                (evenUpperNodeOrders n)) θ p)) :=
    (movingEvenCanonicalFiniteActualJetFamily_hasFDerivAt
      x hupper n θ p).fderiv
  rw [hderiv]
  exact (evenJetExtraction_surjective n).comp
    (movingCanonicalFiniteParameterJetCLM_surjective
      (evenUpperNodePair x) hsep
      (evenUpperNodePair_upper x hupper)
      (evenUpperNodeOrders n)
      (movingCanonicalFiniteChart
        (movingCanonicalLocationProbeCard
          (evenUpperNodeOrders n)) θ p))

end

end GaloisForLFunctions.HTGeometry
