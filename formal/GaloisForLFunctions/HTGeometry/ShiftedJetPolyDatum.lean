import GaloisForLFunctions.HTGeometry.RatApproxDatum
import GaloisForLFunctions.HTGeometry.JetNonNegligible

/-!
# The boundary datum of a shifted jet polynomial

A polynomial in the shifted digamma jets with polynomial coefficients is approximated on every tube,
to every order, by a quotient of polynomials: each jet is, and the class is closed under the ring
operations.  If the polynomial is nonzero the Hölder elimination forbids its value from being
negligible, so the comparison of exponents produces a datum.

This is the analytic injection the shifted law needs: a nonzero element of the shifted polygamma
ring has a genuine leading order on every vertical tube.
-/

open Filter Set Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

attribute [local instance] germRatFuncAlgebra

variable {r : ℕ}

/-- Polynomials as functions on the plane. -/
def polyFunHom : Polynomial ℂ →+* (ℂ → ℂ) :=
  RingHom.pi fun z : ℂ => Polynomial.evalRingHom z

@[simp] theorem polyFunHom_apply (p : Polynomial ℂ) (z : ℂ) : polyFunHom p z = p.eval z := rfl

/-- A shifted digamma jet of positive order, as a function. -/
def jetFun (lam : Fin r → ℝ) (pk : Fin r × ℕ) : ℂ → ℂ :=
  fun z => iteratedDeriv (pk.2 + 1) Complex.digamma (z + ((lam pk.1 : ℝ) : ℂ))

/-- The value of a jet polynomial with polynomial coefficients. -/
def jetPolyFun (lam : Fin r → ℝ) {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ)
    (P : MvPolynomial (Fin Mm) (Polynomial ℂ)) : ℂ → ℂ :=
  MvPolynomial.eval₂ polyFunHom (fun k => jetFun lam (idx k)) P

theorem HasRatApprox.congr {f g : ℂ → ℂ} (hf : HasRatApprox f) (h : ∀ z, f z = g z) :
    HasRatApprox g := by
  have hfg : f = g := funext h
  rwa [hfg] at hf

theorem hasRatApprox_polyEval (a : Polynomial ℂ) : HasRatApprox (fun z => a.eval z) := by
  refine (hasRatApprox_ratEval a (q := 1) one_ne_zero).congr fun z => ?_
  rw [Polynomial.eval_one, div_one]

/-- **Every jet polynomial value is approximable.** -/
theorem hasRatApprox_jetPolyFun (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i) {Mm : ℕ}
    (idx : Fin Mm → Fin r × ℕ) (P : MvPolynomial (Fin Mm) (Polynomial ℂ)) :
    HasRatApprox (jetPolyFun lam idx P) := by
  classical
  refine MvPolynomial.induction_on (motive := fun P => HasRatApprox (jetPolyFun lam idx P))
    P ?_ ?_ ?_
  · intro a
    refine (hasRatApprox_polyEval a).congr fun z => ?_
    simp only [jetPolyFun, MvPolynomial.eval₂_C, polyFunHom_apply]
  · intro p q hp hq
    refine (hp.add hq).congr fun z => ?_
    simp only [jetPolyFun, MvPolynomial.eval₂_add, Pi.add_apply]
  · intro p k hp
    refine (hp.mul (hasRatApprox_iteratedDeriv_digamma_shift (hlam (idx k).1)
      ((idx k).2))).congr fun z => ?_
    simp only [jetPolyFun, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.mul_apply, jetFun]

/-- The value of a jet polynomial is the germ the eliminator works with. -/
theorem jetEval_map_eq_coe (lam : Fin r → ℝ) {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ)
    (P : MvPolynomial (Fin Mm) (Polynomial ℂ)) :
    jetEval lam (fun k => ((idx k).1, (idx k).2 + 1))
        (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P)
      = ((jetPolyFun lam idx P : ℂ → ℂ) : Germ upperEndFilter ℂ) := by
  have hcoe : ((jetPolyFun lam idx P : ℂ → ℂ) : Germ upperEndFilter ℂ)
      = MvPolynomial.eval₂ ((Germ.coeRingHom upperEndFilter).comp polyFunHom)
        (fun k => ((jetFun lam (idx k) : ℂ → ℂ) : Germ upperEndFilter ℂ)) P := by
    rw [jetPolyFun]
    exact MvPolynomial.eval₂_comp_left (Germ.coeRingHom upperEndFilter) polyFunHom
      (fun k => jetFun lam (idx k)) P
  have hhom : (algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ)).comp
      (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      = (Germ.coeRingHom upperEndFilter).comp polyFunHom := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.algebraMap_toAlgebra,
      ratFuncGerm_algebraMap, polyGermHom_apply]
    rfl
  have hfun : (fun k => jetGerm lam ((idx k).1, (idx k).2 + 1))
      = fun k => ((jetFun lam (idx k) : ℂ → ℂ) : Germ upperEndFilter ℂ) := by
    funext k
    rw [jetGerm]
    rfl
  rw [hcoe, jetEval, MvPolynomial.eval₂_map, hhom, hfun]

/-- **The boundary datum of a nonzero shifted jet polynomial.**  For pairwise incongruent
nonnegative shifts, the value of a nonzero polynomial in the shifted digamma jets of positive order
has an argument exponent and a nonzero residue on every vertical tube. -/
theorem exists_hasShiftTubeDatum_jetPolyFun (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ) (hinj : Function.Injective idx)
    {P : MvPolynomial (Fin Mm) (Polynomial ℂ)} (hP : P ≠ 0) {M : ℝ} (hM : 0 < M) :
    ∃ (ω : ℝ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => jetPolyFun lam idx P ((σ : ℂ) + (t : ℂ) * Complex.I)) 0 ω 0 c := by
  classical
  have hinj' : Function.Injective (fun k => ((idx k).1, (idx k).2 + 1) :
      Fin Mm → Fin r × ℕ) := by
    intro a b hab
    have hab' : ((idx a).1, (idx a).2 + 1) = ((idx b).1, (idx b).2 + 1) := hab
    simp only [Prod.mk.injEq] at hab'
    exact hinj (Prod.ext hab'.1 (by omega))
  have hPmap : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P ≠ 0 := by
    intro h0
    refine hP ?_
    have hmap : Function.Injective
        (MvPolynomial.map (σ := Fin Mm) (algebraMap (Polynomial ℂ) (RatFunc ℂ))) :=
      MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    exact hmap (by rw [h0, map_zero])
  have hgerm := not_isGermNegligible_jetEval lam hincong
    (fun k => ((idx k).1, (idx k).2 + 1)) hinj' hPmap
  rw [jetEval_map_eq_coe lam idx P] at hgerm
  have hnn : ¬ IsVerticallyNegligible (jetPolyFun lam idx P) := by
    intro hneg
    exact hgerm (isGermNegligible_coe.mpr hneg)
  exact exists_hasShiftTubeDatum_of_ratApprox (hasRatApprox_jetPolyFun lam hlam idx P) hnn hM

end

end GaloisForLFunctions.HTGeometry
