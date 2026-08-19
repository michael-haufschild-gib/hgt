import GaloisForLFunctions.HTGeometry.JetPolynomialShift

/-!
# The coboundary obstruction in the jet polynomial ring

The corpus's obstruction is stated for a quotient of jet-polynomial values in the meromorphic field.
The shift elimination produces instead a cross-multiplied identity between jet polynomials, so this
file restates the obstruction in that form.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance jetCobDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance jetCobRatAlgebra : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **No cross-multiplied multiplicative coboundary between jet polynomials.** -/
theorem no_jetPoly_multiplicative_coboundary (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ))
    {M : ℕ} (idx : Fin M → Fin r × ℕ) (hinj : Function.Injective idx)
    {P Q : MvPolynomial (Fin M) (RatFunc ℂ)} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (mm : Fin r → ℤ) (i₀ : Fin r) (hmm : mm i₀ ≠ 0)
    (heq : jetShiftPoly (fun k => familyIncrement lam (idx k).1 (idx k).2) P * Q
      = MvPolynomial.C (∏ i : Fin r, (RatFunc.X + RatFunc.C (lam i)) ^ (mm i))
        * (P * jetShiftPoly (fun k => familyIncrement lam (idx k).1 (idx k).2) Q)) :
    False := by
  classical
  set xj : Fin M → meroField (Set.univ : Set ℂ) := fun k => digammaJet lam (idx k) with hxj
  set A : meroField (Set.univ : Set ℂ) := MvPolynomial.aeval xj P with hA
  set B : meroField (Set.univ : Set ℂ) := MvPolynomial.aeval xj Q with hB
  have hindep : AlgebraicIndependent (RatFunc ℂ) (digammaJet lam) :=
    algebraicIndependent_digammaJet lam hincong
  have hinjComp : AlgebraicIndependent (RatFunc ℂ) xj := by
    rw [hxj]
    exact hindep.comp idx hinj
  have hAne : A ≠ 0 := by
    rw [hA]
    intro h0
    exact hP (hinjComp (by rw [h0, map_zero]))
  have hBne : B ≠ 0 := by
    rw [hB]
    intro h0
    exact hQ (hinjComp (by rw [h0, map_zero]))
  have hval := congrArg (MvPolynomial.aeval xj) heq
  rw [map_mul, map_mul, map_mul, MvPolynomial.aeval_C,
    aeval_jetShiftPoly lam idx P, aeval_jetShiftPoly lam idx Q] at hval
  set ρ : meroField (Set.univ : Set ℂ) :=
    algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
      (∏ i : Fin r, (RatFunc.X + RatFunc.C (lam i)) ^ (mm i)) with hρ
  have hσA : addTranslationMeroEquiv 1 A ≠ 0 := by
    intro h0
    exact hAne ((addTranslationMeroEquiv 1).injective (by rw [h0, map_zero]))
  have hσB : addTranslationMeroEquiv 1 B ≠ 0 := by
    intro h0
    exact hBne ((addTranslationMeroEquiv 1).injective (by rw [h0, map_zero]))
  refine no_multiplicative_coboundary_digammaJets lam hincong idx hinj hP hQ mm i₀ hmm ?_
  rw [map_div₀, ← hxj, ← hA, ← hB, ← hρ]
  field_simp
  linear_combination hval

end

end GaloisForLFunctions.HTGeometry
