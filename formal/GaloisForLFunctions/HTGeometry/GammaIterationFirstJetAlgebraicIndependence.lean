import GaloisForLFunctions.HTGeometry.GammaIterationFirstJetLocalIndependence

/-!
# Algebraic independence of the complete first jet of the Gamma-iterate tower

Factorial descent removes one iterate at a time.  The leading derivative-homogeneous symbol cannot
enter the inhomogeneous Riccati kernel, so every nonzero relation descends to a nonzero relation on
the preceding first jet.  The depth-one case is Gamma's local differential rigidity.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

theorem locallyAlgebraicallyIndependentGammaFirstJets_succ
    {k : ℕ} (hk : 1 ≤ k)
    (hind : LocallyAlgebraicallyIndependentGammaFirstJets k) :
    LocallyAlgebraicallyIndependentGammaFirstJets (k + 1) := by
  intro P hP hlocal
  have hprop : ∀ z ∈ gammaIterateRegularSet (k + 1),
      MvPolynomial.eval (gammaIterateFirstJetTuple (k + 1) z) P = 0 :=
    gammaIterateFirstJetTupleRelation_propagates P hlocal
  let Q : MvPolynomial (GammaIterateFirstJetIndex k) ℂ :=
    firstJetDominantBoundaryForm P
  have hQ : Q ≠ 0 := firstJetDominantBoundaryForm_ne_zero hP
  apply (hind Q hQ)
  have honeRight : (1 : ℂ) ∈ rightHalfPlane := by simp [rightHalfPlane]
  filter_upwards [
    (isOpen_gammaIterateRegularSet k).mem_nhds (one_mem_gammaIterateRegularSet k),
    isOpen_rightHalfPlane.mem_nhds honeRight] with z hzreg hzRight
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp [rightHalfPlane] at hzRight
  have hx : -z⁻¹ ∈ localGammaMicroscopeDomain (gammaIterateRegularSet k) := by
    refine ⟨neg_ne_zero.mpr (inv_ne_zero hz0), ?_⟩
    rw [neg_inv_neg_inv hz0]
    exact hzreg
  have hxLeft : -z⁻¹ ∈ gammaFactorialMicroscopeDomain :=
    neg_inv_mem_gammaFactorialMicroscopeDomain_of_mem_rightHalfPlane hzRight
  let Y : ℕ → Fin (k + 1) × Fin 2 → ℂ := fun n i =>
    gammaIterateFirstJetTuple (k + 1)
      (-(n : ℂ) + reciprocalGammaFactorialScale n * (-z⁻¹)) (Sum.inr i)
  let G : ℕ → Fin (k + 1) × Fin 2 → ℂ := fun n =>
    gammaIterateScaledFirstJetTail (k + 1) (reciprocalGammaFactorialScale n)
      (-(n : ℂ) + reciprocalGammaFactorialScale n * (-z⁻¹))
  let J : Fin (k + 1) × Fin 2 → ℂ := gammaFirstJetBoundaryTail k z
  have hG : ∀ i, Tendsto (fun n => G n i) atTop (𝓝 (J i)) := by
    intro i
    have h := tendsto_gammaIterateScaledFirstJetTail_factorialBlowUp
      hk hx hxLeft i
    simpa only [G, J, neg_inv_neg_inv hz0] using h
  have hrel : ∀ᶠ n : ℕ in atTop, ∑ a ∈ P.support,
      firstJetDominantCoefficient P a n (-z⁻¹) *
        firstJetTailMonomial (G n) a = 0 := by
    filter_upwards [eventually_factorialBlowUp_input_gammaIterateRegular hk hx]
      with n hn
    have hcoords : (fun i : GammaIterateFirstJetIndex (k + 1) =>
        i.elim (fun _ =>
          -(n : ℂ) + reciprocalGammaFactorialScale n * (-z⁻¹)) (Y n)) =
        gammaIterateFirstJetTuple (k + 1)
          (-(n : ℂ) + reciprocalGammaFactorialScale n * (-z⁻¹)) := by
      funext i
      rcases i with (i | i) <;> rfl
    have hraw : MvPolynomial.eval
        (fun i => i.elim (fun _ =>
          -(n : ℂ) + reciprocalGammaFactorialScale n * (-z⁻¹)) (Y n)) P = 0 := by
      rw [hcoords]
      exact hprop (-(n : ℂ) + reciprocalGammaFactorialScale n * (-z⁻¹)) hn
    have hnormalized := firstJetDominantRelation_of_relation_at
      P n (-z⁻¹) (Y n) hraw
    have hGY : G n = firstJetScaleTail (reciprocalGammaFactorialScale n) (Y n) := by
      exact (firstJetScaleTail_gammaIterateFirstJetTuple (k + 1)
        (reciprocalGammaFactorialScale n)
        (-(n : ℂ) + reciprocalGammaFactorialScale n * (-z⁻¹))).symm
    rw [hGY]
    exact hnormalized
  have hvan := firstJetDominantTailPolynomial_vanishes_of_rescaled_relations
    P (-z⁻¹) G J hG hrel
  change MvPolynomial.eval (gammaFirstJetBoundaryTail k z)
    (firstJetDominantTailPolynomial P) = 0 at hvan
  rw [show Q = firstJetHomogeneousBoundaryForm
      (firstJetDominantTailPolynomial P) from rfl,
    eval_firstJetHomogeneousBoundaryForm_gamma]
  exact hvan

theorem locallyAlgebraicallyIndependentGammaFirstJets :
    ∀ (k : ℕ), 1 ≤ k → LocallyAlgebraicallyIndependentGammaFirstJets k
  | 0, hk => by omega
  | k + 1, _ => by
      by_cases hk0 : k = 0
      · subst k
        exact locallyAlgebraicallyIndependentGammaFirstJets_one
      · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        exact locallyAlgebraicallyIndependentGammaFirstJets_succ hk
          (locallyAlgebraicallyIndependentGammaFirstJets k hk)

def gammaIterateFirstJetFunctionTuple (k : ℕ) :
    GammaIterateFirstJetIndex k → (ℂ → ℂ) :=
  fun i z => gammaIterateFirstJetTuple k z i

/-- At every finite depth, the independent variable and the values and first derivatives of all
positive Gamma iterates are algebraically independent as meromorphic functions. -/
theorem algebraicIndependent_gammaIterateFirstJetFunctionTuple
    (k : ℕ) (hk : 1 ≤ k) :
    AlgebraicIndependent ℂ (gammaIterateFirstJetFunctionTuple k) := by
  rw [algebraicIndependent_iff]
  intro P hEval
  by_contra hP
  apply locallyAlgebraicallyIndependentGammaFirstJets k hk P hP
  filter_upwards [] with z
  have hz := congrFun hEval z
  have hz' :
      (MvPolynomial.eval₂ (algebraMap ℂ (ℂ → ℂ))
        (gammaIterateFirstJetFunctionTuple k) P) z = 0 := by
    simpa [MvPolynomial.aeval_def] using hz
  rw [eval₂_function_apply] at hz'
  simpa [gammaIterateFirstJetFunctionTuple] using hz'

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Index for the countable first jet: the point, followed by the derivative and value of every
positive Gamma iterate. -/
abbrev GammaIterateInfiniteFirstJetIndex := Unit ⊕ (ℕ × Fin 2)

def gammaIterateInfiniteFirstJetFamily :
    GammaIterateInfiniteFirstJetIndex → (ℂ → ℂ)
  | Sum.inl _ => id
  | Sum.inr (j, slot) => Fin.cases
      (iteratedDeriv 1 (gammaIterate (j + 1)))
      (fun _ => gammaIterate (j + 1)) slot

def gammaIterateInfiniteFirstJetDepth : GammaIterateInfiniteFirstJetIndex → ℕ
  | Sum.inl _ => 0
  | Sum.inr (j, _) => j + 1

def finiteFirstJetIndexToInfinite (k : ℕ) :
    GammaIterateFirstJetIndex k → GammaIterateInfiniteFirstJetIndex
  | Sum.inl _ => Sum.inl ()
  | Sum.inr (j, slot) => Sum.inr ((j : ℕ), slot)

def infiniteFirstJetIndexToFinite (k : ℕ) (i : GammaIterateInfiniteFirstJetIndex)
    (hi : gammaIterateInfiniteFirstJetDepth i ≤ k) :
    GammaIterateFirstJetIndex (k + 1) :=
  match i with
  | Sum.inl _ => Sum.inl 0
  | Sum.inr (j, slot) => Sum.inr (⟨j, by
      simp [gammaIterateInfiniteFirstJetDepth] at hi
      omega⟩, slot)

theorem finiteFirstJetIndexToInfinite_toFinite
    (k : ℕ) (i : GammaIterateInfiniteFirstJetIndex)
    (hi : gammaIterateInfiniteFirstJetDepth i ≤ k) :
    finiteFirstJetIndexToInfinite (k + 1) (infiniteFirstJetIndexToFinite k i hi) = i := by
  rcases i with (u | ⟨j, slot⟩)
  · simp [infiniteFirstJetIndexToFinite, finiteFirstJetIndexToInfinite]
  · simp [infiniteFirstJetIndexToFinite, finiteFirstJetIndexToInfinite]

theorem gammaIterateFirstJetFunctionTuple_toFinite
    (k : ℕ) (i : GammaIterateInfiniteFirstJetIndex)
    (hi : gammaIterateInfiniteFirstJetDepth i ≤ k) :
    gammaIterateFirstJetFunctionTuple (k + 1)
      (infiniteFirstJetIndexToFinite k i hi) =
      gammaIterateInfiniteFirstJetFamily i := by
  rcases i with (u | ⟨j, slot⟩)
  · rfl
  · fin_cases slot <;> rfl

/-- The independent variable together with the values and first derivatives of every positive
Gamma iterate is one countably infinite algebraically independent family over `ℂ`. -/
theorem algebraicIndependent_gammaIterateInfiniteFirstJetFamily :
    AlgebraicIndependent ℂ gammaIterateInfiniteFirstJetFamily := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  let k : ℕ := ht.toFinset.sup fun i => gammaIterateInfiniteFirstJetDepth i
  have hk (i : t) : gammaIterateInfiniteFirstJetDepth i ≤ k := by
    apply Finset.le_sup
    exact ht.mem_toFinset.mpr i.2
  let f : t → GammaIterateFirstJetIndex (k + 1) := fun i =>
    infiniteFirstJetIndexToFinite k i.1 (hk i)
  have hfleft (i : t) : finiteFirstJetIndexToInfinite (k + 1) (f i) = i.1 := by
    exact finiteFirstJetIndexToInfinite_toFinite k i.1 (hk i)
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    rw [← hfleft i, ← hfleft j, hij]
  have hprefix := algebraicIndependent_gammaIterateFirstJetFunctionTuple
    (k + 1) (Nat.le_add_left 1 k)
  have hsub := hprefix.comp f hf
  have heq : gammaIterateFirstJetFunctionTuple (k + 1) ∘ f =
      fun i : t => gammaIterateInfiniteFirstJetFamily i.1 := by
    funext i
    exact gammaIterateFirstJetFunctionTuple_toFinite k i.1 (hk i)
  rw [heq] at hsub
  exact hsub

end

end GaloisForLFunctions
