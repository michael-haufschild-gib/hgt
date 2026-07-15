import GaloisForLFunctions.RHTower.SoninSemilocalGradingBounds
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace RHTower

theorem isHilbertSchmidt_rankOne
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (x : E) (y : F) :
    ContinuousLinearMap.IsHilbertSchmidt
      (InnerProductSpace.rankOne ℂ x y) := by
  unfold ContinuousLinearMap.IsHilbertSchmidt
  have hs := (ContinuousLinearMap.hsBasis ℂ F).summable_norm_inner_sq y
  apply (hs.mul_right (‖x‖ ^ 2)).congr
  intro i
  rw [InnerProductSpace.rankOne_apply, norm_smul, mul_pow]
  rw [norm_inner_symm]

theorem isTraceClass_rankOne_lp (x y : lp (fun _ : ℕ => ℂ) 2) :
    ContinuousLinearMap.IsTraceClass
      (InnerProductSpace.rankOne ℂ x y) := by
  let e : lp (fun _ : ℕ => ℂ) 2 := lp.single 2 0 1
  have he : inner ℂ e e = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp [e]
  refine ⟨InnerProductSpace.rankOne ℂ x e,
    InnerProductSpace.rankOne ℂ e y,
    isHilbertSchmidt_rankOne x e,
    isHilbertSchmidt_rankOne e y, ?_⟩
  rw [InnerProductSpace.rankOne_comp_rankOne, he, one_smul]

def semilocalOnePrimeGroundRowCoefficient
    (p : ℕ) (alpha : ℝ) (k : ℕ) : ℝ :=
  semilocalOnePrimeGroundCommutatorRow p k *
    ((2 * k + 1 : ℕ) : ℝ) ^ (-alpha)

theorem semilocalOnePrimeGroundRowSmoothedSquare_eq
    (p : ℕ) (alpha : ℝ) (k : ℕ) :
    semilocalOnePrimeGroundRowSmoothedSquare p alpha k =
      semilocalOnePrimeGroundRowCoefficient p alpha k ^ 2 := rfl

theorem summable_norm_sq_semilocalOnePrimeGroundRowCoefficient
    {p : ℕ} (hp : p.Prime) {alpha : ℝ} (halpha : 3 / 4 < alpha) :
    Summable (fun k : ℕ =>
      ‖(semilocalOnePrimeGroundRowCoefficient p alpha k : ℂ)‖ ^ 2) := by
  have hs :=
    (summable_semilocalOnePrimeGroundRowSmoothedSquare_iff hp alpha).2 halpha
  apply hs.congr
  intro k
  rw [semilocalOnePrimeGroundRowSmoothedSquare_eq]
  norm_cast
  rw [Real.norm_eq_abs, sq_abs]

def semilocalOnePrimeGroundRowVector
    (p : ℕ) (alpha : ℝ)
    (h : Summable (fun k : ℕ =>
      ‖(semilocalOnePrimeGroundRowCoefficient p alpha k : ℂ)‖ ^ 2)) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun k => semilocalOnePrimeGroundRowCoefficient p alpha k,
    HilbertSchmidt.memℓp_of_sq h⟩

def semilocalOnePrimeGroundRowOperator
    (p : ℕ) (alpha : ℝ)
    (h : Summable (fun k : ℕ =>
      ‖(semilocalOnePrimeGroundRowCoefficient p alpha k : ℂ)‖ ^ 2)) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  InnerProductSpace.rankOne ℂ (lp.single 2 0 1)
    (semilocalOnePrimeGroundRowVector p alpha h)

theorem semilocalOnePrimeGroundRowOperator_isTraceClass
    {p : ℕ} (hp : p.Prime) {alpha : ℝ} (halpha : 3 / 4 < alpha) :
    ContinuousLinearMap.IsTraceClass
      (semilocalOnePrimeGroundRowOperator p alpha
        (summable_norm_sq_semilocalOnePrimeGroundRowCoefficient hp halpha)) := by
  apply isTraceClass_rankOne_lp

/-- Metric self-adjointness plus a bounded perturbation forces a bounded inverse-metric
commutator.  The actual Euler row contradicts that conclusion. -/
theorem no_semilocalOnePrime_boundedPerturbationRealization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : ℕ} (hp : p.Prime)
    (N : H →ₗ[ℂ] H) (A G K : H →L[ℂ] H) (e : ℕ → H)
    (hAG : A ∘L G = ContinuousLinearMap.id ℂ H)
    (hGA : G ∘L A = ContinuousLinearMap.id ℂ H)
    (hmetric : ∀ x : H,
      N (A x) - A (N x) =
        A (K x) - ContinuousLinearMap.adjoint K (A x))
    (henorm : ∀ n : ℕ, ‖e n‖ = 1)
    (hrow : ∀ k : ℕ, 0 < k →
      inner ℂ (e 0) (N (G (e (2 * k))) - G (N (e (2 * k)))) =
        (semilocalOnePrimeGroundCommutatorRow p k : ℂ)) :
    False := by
  let T : H →L[ℂ] H :=
    (-G) ∘L
      ((A ∘L K) - (ContinuousLinearMap.adjoint K ∘L A)) ∘L G
  have hAGx (x : H) : A (G x) = x := by
    have h := congrArg (fun L : H →L[ℂ] H => L x) hAG
    simpa [ContinuousLinearMap.comp_apply] using h
  have hGAx (x : H) : G (A x) = x := by
    have h := congrArg (fun L : H →L[ℂ] H => L x) hGA
    simpa [ContinuousLinearMap.comp_apply] using h
  have hcomm (x : H) : N (G x) - G (N x) = T x := by
    calc
      N (G x) - G (N x) =
          -G (N (A (G x)) - A (N (G x))) := by
        rw [hAGx, map_sub, hGAx]
        abel
      _ = -G (A (K (G x)) -
          ContinuousLinearMap.adjoint K (A (G x))) := by
        rw [hmetric]
      _ = T x := by
        simp only [T, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
  obtain ⟨k, hk, hklarge⟩ :=
    semilocalOnePrimeGroundCommutatorRow_unbounded hp ‖T‖
  have hi := norm_inner_le_norm (𝕜 := ℂ) (e 0) (T (e (2 * k)))
  have hT := T.le_opNorm (e (2 * k))
  have hrowk := hrow k hk
  rw [hcomm] at hrowk
  rw [hrowk, Complex.norm_real, Real.norm_eq_abs,
    henorm 0, one_mul] at hi
  rw [henorm (2 * k), mul_one] at hT
  exact (not_lt_of_ge (hi.trans hT)) hklarge

end RHTower
