import GaloisForLFunctions.HTGeometry.ComplexShiftJetApprox
import GaloisForLFunctions.HTGeometry.ComplexShiftJetGerm
import GaloisForLFunctions.HTGeometry.ShiftedJetFieldDatum

/-!
# The boundary datum of the complex-shifted polygamma field

Both halves of the dichotomy survive an arbitrary complex shift.  The analytic half is the
re-expansion of `ψ⁽ʲ⁾(s+λ)` in the coordinate `1/s`, valid once the recurrence has pushed the shift
into the closed right half plane.  The algebraic half is the shift elimination, which only ever
used that the shifts are pairwise incongruent modulo the integers.

Hence a nonzero polynomial in digamma jets at pairwise incongruent complex shifts has an argument
exponent, a logarithm exponent and a nonzero residue on every vertical tube — with no hypothesis on
the shifts beyond incongruence.
-/

open Filter Set Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

attribute [local instance] germRatFuncAlgebra

variable {r : ℕ}

/-- A digamma jet of arbitrary order at a complex shift, as a function. -/
def jetFieldFunC (lam : Fin r → ℂ) (pk : Fin r × ℕ) : ℂ → ℂ :=
  fun z => iteratedDeriv pk.2 Complex.digamma (z + lam pk.1)

/-- **Every complex-shifted digamma jet is approximable with logarithms.** -/
theorem hasLogRatApprox_jetFieldFunC (lam : Fin r → ℂ) (pk : Fin r × ℕ) :
    HasLogRatApprox (jetFieldFunC lam pk) := by
  obtain ⟨i, j⟩ := pk
  cases j with
  | zero =>
      refine (hasLogRatApprox_digamma_anyShift (lam i)).congr fun z => ?_
      rw [jetFieldFunC, iteratedDeriv_zero]
  | succ n =>
      exact (hasRatApprox_iteratedDeriv_digamma_anyShift (lam i) n).hasLogRatApprox

/-- The value of a jet polynomial of the complex-shifted field with polynomial coefficients. -/
def jetFieldPolyFunC (lam : Fin r → ℂ) {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ)
    (P : MvPolynomial (Fin Mm) (Polynomial ℂ)) : ℂ → ℂ :=
  MvPolynomial.eval₂ polyFunHom (fun k => jetFieldFunC lam (idx k)) P

theorem hasLogRatApprox_jetFieldPolyFunC (lam : Fin r → ℂ) {Mm : ℕ}
    (idx : Fin Mm → Fin r × ℕ) (P : MvPolynomial (Fin Mm) (Polynomial ℂ)) :
    HasLogRatApprox (jetFieldPolyFunC lam idx P) := by
  classical
  refine MvPolynomial.induction_on
    (motive := fun P => HasLogRatApprox (jetFieldPolyFunC lam idx P)) P ?_ ?_ ?_
  · intro a
    refine ((hasRatApprox_polyEval a).hasLogRatApprox).congr fun z => ?_
    simp only [jetFieldPolyFunC, MvPolynomial.eval₂_C, polyFunHom_apply]
  · intro p q hp hq
    refine (hp.add hq).congr fun z => ?_
    simp only [jetFieldPolyFunC, MvPolynomial.eval₂_add, Pi.add_apply]
  · intro p k hp
    refine (hp.mul (hasLogRatApprox_jetFieldFunC lam (idx k))).congr fun z => ?_
    simp only [jetFieldPolyFunC, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.mul_apply]

/-- The value of a complex-shifted jet polynomial is the germ the eliminator works with. -/
theorem shiftedJetEvalC_map_eq_coe_field (lam : Fin r → ℂ) {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ)
    (P : MvPolynomial (Fin Mm) (Polynomial ℂ)) :
    shiftedJetEvalC lam idx (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P)
      = ((jetFieldPolyFunC lam idx P : ℂ → ℂ) : Germ upperEndFilter ℂ) := by
  have hcoe : ((jetFieldPolyFunC lam idx P : ℂ → ℂ) : Germ upperEndFilter ℂ)
      = MvPolynomial.eval₂ ((Germ.coeRingHom upperEndFilter).comp polyFunHom)
        (fun k => ((jetFieldFunC lam (idx k) : ℂ → ℂ) : Germ upperEndFilter ℂ)) P := by
    rw [jetFieldPolyFunC]
    exact MvPolynomial.eval₂_comp_left (Germ.coeRingHom upperEndFilter) polyFunHom
      (fun k => jetFieldFunC lam (idx k)) P
  have hhom : (algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ)).comp
      (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      = (Germ.coeRingHom upperEndFilter).comp polyFunHom := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.algebraMap_toAlgebra,
      ratFuncGerm_algebraMap, polyGermHom_apply]
    rfl
  have hfun : (fun k => jetGermC lam (idx k))
      = fun k => ((jetFieldFunC lam (idx k) : ℂ → ℂ) : Germ upperEndFilter ℂ) := by
    funext k
    rw [jetGermC]
    rfl
  rw [hcoe, shiftedJetEvalC, MvPolynomial.eval₂_map, hhom, hfun]

/-- **The boundary datum of a nonzero element of the complex-shifted polygamma ring.**  For
pairwise incongruent complex shifts, the value of a nonzero polynomial in the digamma jets of any
orders, with polynomial coefficients, has an argument exponent, a logarithm exponent and a nonzero
residue on every vertical tube. -/
theorem exists_hasShiftTubeDatum_jetFieldPolyFunC (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ))
    {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ) (hinj : Function.Injective idx)
    {P : MvPolynomial (Fin Mm) (Polynomial ℂ)} (hP : P ≠ 0) {M : ℝ} (hM : 0 < M) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => jetFieldPolyFunC lam idx P ((σ : ℂ) + (t : ℂ) * Complex.I)) 0 ((a : ℝ)) b c := by
  classical
  have hPmap : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P ≠ 0 := by
    intro h0
    refine hP ?_
    have hmap : Function.Injective
        (MvPolynomial.map (σ := Fin Mm) (algebraMap (Polynomial ℂ) (RatFunc ℂ))) :=
      MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    exact hmap (by rw [h0, map_zero])
  have hgerm := not_isGermNegligible_shiftedJetEvalC lam hincong idx hinj hPmap
  rw [shiftedJetEvalC_map_eq_coe_field lam idx P] at hgerm
  have hnn : ¬ IsVerticallyNegligible (jetFieldPolyFunC lam idx P) := by
    intro hneg
    exact hgerm (isGermNegligible_coe.mpr hneg)
  exact exists_hasShiftTubeDatum_of_logRatApprox
    (hasLogRatApprox_jetFieldPolyFunC lam idx P) hnn hM

end

end GaloisForLFunctions.HTGeometry
