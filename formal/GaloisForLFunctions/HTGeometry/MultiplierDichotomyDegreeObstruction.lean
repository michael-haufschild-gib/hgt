import GaloisForLFunctions.HTGeometry.OrbitBalanceRationalComplete
import GaloisForLFunctions.HTGeometry.ExpPolynomialDA
import GaloisForLFunctions.HTGeometry.MultiplierDichotomy

/-!
# The multiplier dichotomy: the degree-at-infinity obstruction and the Source-A/B divide
-/

namespace GaloisForLFunctions.MultiplierDichotomyComplete

open Polynomial GaloisForLFunctions.OrbitBalanceComplete GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## (II) The degree-at-infinity obstruction -/

theorem natDegree_comp_shiftPoly (p : ℂ[X]) : (p.comp shiftPoly).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp, shiftPoly_natDegree, mul_one]

theorem shiftHom_algebraMap (p : ℂ[X]) :
    shiftHom (algebraMap ℂ[X] (RatFunc ℂ) p)
      = algebraMap ℂ[X] (RatFunc ℂ) (p.comp shiftPoly) :=
  ratFuncSubstitution_algebraMap shiftPoly_not_const p

theorem algebraMap_ne_zero_of_ne_zero' {p : ℂ[X]} (hp : p ≠ 0) :
    algebraMap ℂ[X] (RatFunc ℂ) p ≠ 0 :=
  fun h => hp (RatFunc.algebraMap_injective ℂ (by rw [h, map_zero]))

theorem intDegree_div_algebraMap {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q).intDegree
      = (p.natDegree : ℤ) - (q.natDegree : ℤ) := by
  rw [div_eq_mul_inv, RatFunc.intDegree_mul (algebraMap_ne_zero_of_ne_zero' hp)
      (inv_ne_zero (algebraMap_ne_zero_of_ne_zero' hq)),
    RatFunc.intDegree_inv, RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  ring

/-- **The shift preserves the degree at infinity.**  This is the algebraic form of the card's
`g(z+1)/g(z) → 1`. -/
theorem intDegree_shiftHom {Q : RatFunc ℂ} (hQ : Q ≠ 0) :
    (shiftHom Q).intDegree = Q.intDegree := by
  have hnum : Q.num ≠ 0 := RatFunc.num_ne_zero hQ
  have hden : Q.denom ≠ 0 := RatFunc.denom_ne_zero Q
  have hcompnum : Q.num.comp shiftPoly ≠ 0 := by
    intro h
    have := natDegree_comp_shiftPoly Q.num
    rcases Polynomial.comp_eq_zero_iff.mp h with h1 | ⟨-, h2⟩
    · exact hnum h1
    · rw [shiftPoly] at h2
      have hd : (X + C 1 : ℂ[X]).natDegree = 0 := by rw [h2, natDegree_C]
      rw [natDegree_X_add_C] at hd
      exact one_ne_zero hd
  have hcompden : Q.denom.comp shiftPoly ≠ 0 := by
    intro h
    rcases Polynomial.comp_eq_zero_iff.mp h with h1 | ⟨-, h2⟩
    · exact hden h1
    · rw [shiftPoly] at h2
      have hd : (X + C 1 : ℂ[X]).natDegree = 0 := by rw [h2, natDegree_C]
      rw [natDegree_X_add_C] at hd
      exact one_ne_zero hd
  have hQeq : Q = algebraMap ℂ[X] (RatFunc ℂ) Q.num / algebraMap ℂ[X] (RatFunc ℂ) Q.denom :=
    (RatFunc.num_div_denom Q).symm
  calc (shiftHom Q).intDegree
      = (algebraMap ℂ[X] (RatFunc ℂ) (Q.num.comp shiftPoly)
          / algebraMap ℂ[X] (RatFunc ℂ) (Q.denom.comp shiftPoly)).intDegree := by
        conv_lhs => rw [hQeq]
        rw [map_div₀, shiftHom_algebraMap, shiftHom_algebraMap]
    _ = ((Q.num.comp shiftPoly).natDegree : ℤ) - ((Q.denom.comp shiftPoly).natDegree : ℤ) :=
        intDegree_div_algebraMap hcompnum hcompden
    _ = (Q.num.natDegree : ℤ) - (Q.denom.natDegree : ℤ) := by
        rw [natDegree_comp_shiftPoly, natDegree_comp_shiftPoly]
    _ = Q.intDegree := (intDegree_div_algebraMap hnum hden).symm.trans (by conv_rhs => rw [hQeq])

theorem intDegree_ratFuncC (c : ℂ) : (RatFunc.C c : RatFunc ℂ).intDegree = 0 := by
  rw [← RatFunc.algebraMap_C, RatFunc.intDegree_polynomial, natDegree_C]
  rfl

/-- **CC forces degree zero at infinity.** -/
theorem intDegree_eq_zero_of_isCC {a : RatFunc ℂ} (h : IsCC a) : a.intDegree = 0 := by
  obtain ⟨c, g, hc, hg, rfl⟩ := h
  have hCne : (RatFunc.C c : RatFunc ℂ) ≠ 0 := by simpa using hc
  have hsh : shiftHom g ≠ 0 := shiftHom_ne_zero hg
  have hquot : shiftHom g / g ≠ 0 := div_ne_zero hsh hg
  rw [RatFunc.intDegree_mul hCne hquot, intDegree_ratFuncC, zero_add, div_eq_mul_inv,
    RatFunc.intDegree_mul hsh (inv_ne_zero hg), RatFunc.intDegree_inv, intDegree_shiftHom hg]
  ring

/-- **The degree-at-infinity obstruction.**  A nonzero degree at infinity forbids the CC class. -/
theorem not_isCC_of_intDegree_ne_zero {a : RatFunc ℂ} (h : a.intDegree ≠ 0) : ¬ IsCC a :=
  fun hcc => h (intDegree_eq_zero_of_isCC hcc)

/-- **Every non-constant polynomial multiplier is off the CC class.** -/
theorem not_isCC_polynomial {p : ℂ[X]} (hp : 0 < p.natDegree) :
    ¬ IsCC (algebraMap ℂ[X] (RatFunc ℂ) p) := by
  refine not_isCC_of_intDegree_ne_zero ?_
  rw [RatFunc.intDegree_polynomial]
  exact_mod_cast hp.ne'

end

end GaloisForLFunctions.MultiplierDichotomyComplete

namespace GaloisForLFunctions.MultiplierDichotomyComplete

open Polynomial GaloisForLFunctions.OrbitBalanceComplete GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## (I)(3) The CC solution is differentially algebraic -/

/-- **The case-(I) solution is differentially algebraic.**  For a nonzero polynomial gauge `p` the
function `f(z) = p(z)·e^{λz}` satisfies the first-order polynomial ODE `p·f' = (p' + λp)·f`, hence is
differentially algebraic. -/
theorem differentiallyAlgebraic_polynomial_mul_exp (p : ℂ[X]) (hp : p ≠ 0) (lam : ℂ) :
    DifferentiallyAlgebraic (fun z : ℂ => p.eval z * Complex.exp (lam * z)) := by
  refine differentiallyAlgebraic_of_firstOrder_poly_ode
    (Polynomial.derivative p + Polynomial.C lam * p) p hp (fun s => ?_)
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp (lam * z)) (Complex.exp (lam * s) * lam) s := by
    have h := ((hasDerivAt_id s).const_mul lam).cexp
    simpa using h
  have hf : HasDerivAt (fun z : ℂ => p.eval z * Complex.exp (lam * z))
      ((Polynomial.derivative p).eval s * Complex.exp (lam * s)
        + p.eval s * (Complex.exp (lam * s) * lam)) s :=
    (p.hasDerivAt s).mul hexp
  rw [hf.deriv]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-! ## Source-B instances -/

theorem qHom_algebraMap {q : ℂ} (hq : q ≠ 0) (p : ℂ[X]) :
    qHom q hq (algebraMap ℂ[X] (RatFunc ℂ) p)
      = algebraMap ℂ[X] (RatFunc ℂ) (p.comp (qPoly q)) :=
  ratFuncSubstitution_algebraMap (qPoly_not_const hq) p

/-- **The prime-generator multiplier is constant, hence CC.** -/
theorem isCCq_ratFuncC {q : ℂ} (hq : q ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    IsCCq q hq (RatFunc.C c) :=
  ⟨c, 1, hc, one_ne_zero, by rw [map_one, div_one, mul_one]⟩

theorem one_sub_X_ne_zero : (1 - X : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval (0 : ℂ)) h
  simp at this

theorem one_sub_qX_ne_zero (q : ℂ) : (1 - C q * X : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval (0 : ℂ)) h
  simp at this

/-- **The Euler-factor multiplier `(1−x)/(1−qx)` is a pure `q`-coboundary.**  Its gauge is the Euler
factor itself, so the case-(I) solution is rational — the strongest holonomic form. -/
theorem isCCq_eulerMultiplier {q : ℂ} (hq : q ≠ 0) :
    IsCCq q hq (algebraMap ℂ[X] (RatFunc ℂ) (1 - X)
      / algebraMap ℂ[X] (RatFunc ℂ) (1 - C q * X)) := by
  have hA : algebraMap ℂ[X] (RatFunc ℂ) (1 - X) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero' one_sub_X_ne_zero
  have hcomp : (1 - X : ℂ[X]).comp (qPoly q) = 1 - C q * X := by
    rw [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp, qPoly]
  refine ⟨1, (algebraMap ℂ[X] (RatFunc ℂ) (1 - X))⁻¹, one_ne_zero, inv_ne_zero hA, ?_⟩
  rw [map_one, one_mul, map_inv₀, qHom_algebraMap hq, hcomp, inv_div_inv]

/-! ## The Source-A / Source-B divide -/

theorem intDegree_ratFuncX : (RatFunc.X : RatFunc ℂ).intDegree = 1 := by
  rw [← RatFunc.algebraMap_X, RatFunc.intDegree_polynomial, natDegree_X]
  rfl

theorem not_isCC_ratFuncX' : ¬ IsCC (RatFunc.X : RatFunc ℂ) :=
  not_isCC_of_intDegree_ne_zero (by rw [intDegree_ratFuncX]; exact one_ne_zero)

/-- **Door-5 `F_q` shadow.**  Over a base whose every place carries a constant multiplier, every
rank-one place module is CC — there is no Source-A (non-CC) place. -/
theorem fq_shadow_all_isCC {ι : Type*} (m : ι → ℂ) (hm : ∀ i, m i ≠ 0) :
    ∀ i, IsCC (RatFunc.C (m i)) := fun i => isCC_ratFuncC (hm i)

/-- **The multiplier dichotomy, assembled.**

Constant multipliers (Source B) are CC; a nonzero degree at infinity forbids CC, so every
non-constant polynomial multiplier — in particular the `Γ` multiplier `a(z) = z` (Source A) — is off
the CC class; the case-(I) gauge solution `p(z)e^{λz}` is differentially algebraic; and on the
prime lanes both the constant generator multiplier and the Euler-factor multiplier are CC. -/
theorem multiplierDichotomy_sourceDivide :
    (∀ c : ℂ, c ≠ 0 → IsCC (RatFunc.C c)) ∧
      (∀ a : RatFunc ℂ, a.intDegree ≠ 0 → ¬ IsCC a) ∧
      (∀ p : ℂ[X], 0 < p.natDegree → ¬ IsCC (algebraMap ℂ[X] (RatFunc ℂ) p)) ∧
      ¬ IsCC (RatFunc.X : RatFunc ℂ) ∧
      (∀ p : ℂ[X], p ≠ 0 → ∀ lam : ℂ,
        DifferentiallyAlgebraic (fun z : ℂ => p.eval z * Complex.exp (lam * z))) ∧
      (∀ (q : ℂ) (hq : q ≠ 0) (c : ℂ), c ≠ 0 → IsCCq q hq (RatFunc.C c)) ∧
      (∀ (q : ℂ) (hq : q ≠ 0), IsCCq q hq (algebraMap ℂ[X] (RatFunc ℂ) (1 - X)
        / algebraMap ℂ[X] (RatFunc ℂ) (1 - C q * X))) :=
  ⟨fun _ hc => isCC_ratFuncC hc, fun _ h => not_isCC_of_intDegree_ne_zero h,
    fun _ hp => not_isCC_polynomial hp, not_isCC_ratFuncX',
    fun p hp lam => differentiallyAlgebraic_polynomial_mul_exp p hp lam,
    fun _ hq _ hc => isCCq_ratFuncC hq hc, fun _ hq => isCCq_eulerMultiplier hq⟩

end

end GaloisForLFunctions.MultiplierDichotomyComplete
