import GaloisForLFunctions.HTGeometry.GammaIterationFirstJetDominantDescent

/-!
# Local polynomial independence for Gamma-iterate first jets

This file supplies the analytic continuation framework, the depth-one base case from Gamma's local
differential rigidity, and the nonzero dominant boundary form used by factorial descent.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

def LocallyAlgebraicallyIndependentGammaFirstJets (k : ℕ) : Prop :=
  ∀ P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ, P ≠ 0 →
    ¬ ∀ᶠ z : ℂ in 𝓝 1, MvPolynomial.eval (gammaIterateFirstJetTuple k z) P = 0

theorem analyticAt_gammaIterateFirstJetTupleEval {k : ℕ}
    (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ) {z : ℂ}
    (hz : z ∈ gammaIterateRegularSet k) :
    AnalyticAt ℂ (fun w => MvPolynomial.eval (gammaIterateFirstJetTuple k w) P) z := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) z)
  | add P Q hP hQ =>
      have heq : (fun w => MvPolynomial.eval (gammaIterateFirstJetTuple k w) (P + Q)) =
          fun w => MvPolynomial.eval (gammaIterateFirstJetTuple k w) P +
            MvPolynomial.eval (gammaIterateFirstJetTuple k w) Q := by
        funext w
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun w => MvPolynomial.eval (gammaIterateFirstJetTuple k w)
          (P * MvPolynomial.X i)) =
          fun w => MvPolynomial.eval (gammaIterateFirstJetTuple k w) P *
            gammaIterateFirstJetTuple k w i := by
        funext w
        simp
      rw [heq]
      exact hP.mul (analyticAt_gammaIterateFirstJetTupleCoordinate hz i)

theorem gammaIterateFirstJetTupleRelation_propagates
    {k : ℕ} (P : MvPolynomial (GammaIterateFirstJetIndex k) ℂ)
    (hlocal : ∀ᶠ z in 𝓝 1,
      MvPolynomial.eval (gammaIterateFirstJetTuple k z) P = 0) :
    ∀ z ∈ gammaIterateRegularSet k,
      MvPolynomial.eval (gammaIterateFirstJetTuple k z) P = 0 := by
  let E : ℂ → ℂ := fun z => MvPolynomial.eval (gammaIterateFirstJetTuple k z) P
  have han : AnalyticOnNhd ℂ E (gammaIterateRegularSet k) := by
    intro z hz
    exact analyticAt_gammaIterateFirstJetTupleEval P hz
  letI : NeBot (𝓝[≠] (1 : ℂ)) := NormedField.nhdsNE_neBot 1
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (gammaIterateRegularSet_isPreconnected k)
    (one_mem_gammaIterateRegularSet k) hfreq

def firstJetOneToJetIndex : GammaIterateFirstJetIndex 1 → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (_, slot) => Fin.cases 2 (fun _ => 1) slot

theorem firstJetOneToJetIndex_injective : Function.Injective firstJetOneToJetIndex := by
  intro i j hij
  rcases i with (i | ⟨i, si⟩) <;> rcases j with (j | ⟨j, sj⟩)
  · have h : i = j := Subsingleton.elim _ _
    subst j
    rfl
  · fin_cases sj <;> simp [firstJetOneToJetIndex] at hij
  · fin_cases si <;> simp [firstJetOneToJetIndex] at hij
  · fin_cases si <;> fin_cases sj <;> simp [firstJetOneToJetIndex] at hij
    all_goals
      have h : i = j := Subsingleton.elim _ _
      subst j
      rfl

theorem locallyAlgebraicallyIndependentGammaFirstJets_one :
    LocallyAlgebraicallyIndependentGammaFirstJets 1 := by
  intro P hP hlocal
  let R : MvPolynomial (Fin 3) ℂ := P.rename firstJetOneToJetIndex
  have hR : R ≠ 0 := by
    exact fun hzero => hP (MvPolynomial.rename_injective _
      firstJetOneToJetIndex_injective hzero)
  let G : MvPolynomial (Fin 2) (Polynomial ℂ) := reshapeJet 1 R
  have hG : G ≠ 0 := fun hzero => hR
    (reshapeJet_injective 1 (by simpa [G] using hzero))
  apply (locallyPolynomialJetRigidAt_gammaIterate 1 (by omega) 1 G hG)
  filter_upwards [hlocal] with z hz
  have hval : MvPolynomial.eval₂ (Polynomial.evalRingHom z)
      (fun j : Fin 2 => iteratedDeriv (j : ℕ) Complex.Gamma z) G = 0 := by
    rw [show G = reshapeJet 1 R from rfl, eval₂_reshapeJet]
    rw [show R = P.rename firstJetOneToJetIndex from rfl, MvPolynomial.eval_rename]
    have htuple : (fun i : GammaIterateFirstJetIndex 1 =>
        (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) Complex.Gamma z) :
          Fin 3 → ℂ) (firstJetOneToJetIndex i)) = gammaIterateFirstJetTuple 1 z := by
      funext i
      rcases i with (i | ⟨i, slot⟩)
      · simp [firstJetOneToJetIndex, gammaIterateFirstJetTuple]
      · have hi : i = 0 := Subsingleton.elim _ _
        subst i
        fin_cases slot <;> rfl
    change MvPolynomial.eval
      (fun i => (Fin.cons z
        (fun j : Fin 2 => iteratedDeriv (j : ℕ) Complex.Gamma z) : Fin 3 → ℂ)
        (firstJetOneToJetIndex i)) P = 0
    rw [htuple]
    exact hz
  simpa [gammaIterate, iteratedDeriv_zero] using hval

def firstJetDominantBoundaryForm
    (P : MvPolynomial (GammaIterateFirstJetIndex (k + 1)) ℂ) :
    MvPolynomial (GammaIterateFirstJetIndex k) ℂ :=
  firstJetHomogeneousBoundaryForm (firstJetDominantTailPolynomial P)

theorem firstJetDominantBoundaryForm_ne_zero
    {P : MvPolynomial (GammaIterateFirstJetIndex (k + 1)) ℂ} (hP : P ≠ 0) :
    firstJetDominantBoundaryForm P ≠ 0 := by
  apply firstJetHomogeneousBoundaryForm_ne_zero
  · exact firstJetDominantTailPolynomial_ne_zero hP
  · exact firstJetDominantTailPolynomial_isWeightedHomogeneous P

theorem firstJetScaleTail_gammaIterateFirstJetTuple
    (k : ℕ) (s z : ℂ) :
    firstJetScaleTail s
      (fun i => gammaIterateFirstJetTuple k z (Sum.inr i)) =
      gammaIterateScaledFirstJetTail k s z := by
  funext i
  rcases i with ⟨j, slot⟩
  fin_cases slot <;> rfl

end

end GaloisForLFunctions
