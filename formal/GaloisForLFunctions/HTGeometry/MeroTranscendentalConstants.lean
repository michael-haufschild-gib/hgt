import GaloisForLFunctions.HTGeometry.CompositionJetField
import GaloisForLFunctions.HTGeometry.ZeroFreeRadius

/-!
# A nonconstant entire function is transcendental over the constants

A polynomial relation over `ℂ` satisfied by the realization of an entire function is, by
faithfulness, a pointwise relation: every value of the function is a root of the polynomial.  The
level sets at the finitely many roots are countable unless the function is constant there, and the
plane is uncountable.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The pointwise evaluation of a univariate polynomial at an entire function is entire. -/
theorem analyticOnNhd_eval_polynomial {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Set.univ : Set ℂ)) (Q : Polynomial ℂ) :
    AnalyticOnNhd ℂ (fun z => Q.eval (F z)) (Set.univ : Set ℂ) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
      have heq : (fun z => (p + q).eval (F z))
          = fun z => p.eval (F z) + q.eval (F z) := by
        funext z
        simp
      rw [heq]
      intro x hx
      exact (hp x hx).add (hq x hx)
  | monomial m a =>
      have heq : (fun z => (Polynomial.monomial m a).eval (F z))
          = fun z => a * (F z) ^ m := by
        funext z
        simp
      rw [heq]
      intro x hx
      exact analyticAt_const.mul ((hF x hx).pow m)

/-- **Univariate polynomial evaluation transfers to the field.** -/
theorem aeval_analyticMeroElement_polynomial {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Set.univ : Set ℂ)) (Q : Polynomial ℂ) :
    Polynomial.aeval (analyticMeroElement F hF) Q
      = analyticMeroElement (fun z => Q.eval (F z)) (analyticOnNhd_eval_polynomial hF Q) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq, ← analyticMeroElement_add]
      exact analyticMeroElement_congr _ _ (by funext z; simp)
  | monomial m a =>
      rw [Polynomial.aeval_monomial]
      have hconst : (algebraMap ℂ (meroField (Set.univ : Set ℂ))) a
          = analyticMeroElement (fun _ : ℂ => a) analyticOnNhd_const :=
        (analyticMeroElement_const (Set.univ : Set ℂ) a).trans rfl
      rw [hconst, ← analyticMeroElement_pow, ← analyticMeroElement_mul]
      exact analyticMeroElement_congr _ _ (by funext z; simp)

/-- **A nonconstant entire function is transcendental over the constants.** -/
theorem transcendental_analyticMeroElement_of_nonconstant {F : ℂ → ℂ}
    (hFd : Differentiable ℂ F) (hF : AnalyticOnNhd ℂ F (Set.univ : Set ℂ))
    (hnc : ¬ ∃ c : ℂ, ∀ z, F z = c) :
    Transcendental ℂ (analyticMeroElement F hF) := by
  classical
  rintro ⟨Q, hQ0, hQ⟩
  rw [aeval_analyticMeroElement_polynomial] at hQ
  have hzero : ∀ z : ℂ, Q.eval (F z) = 0 :=
    fun z => (analyticMeroElement_eq_zero_iff _).mp hQ z (Set.mem_univ z)
  -- every value of `F` is a root of `Q`
  set R : Set ℂ := {w : ℂ | Q.eval w = 0} with hR
  have hRfin : R.Finite := Polynomial.finite_setOf_isRoot hQ0
  have hcover : (Set.univ : Set ℂ) ⊆ ⋃ r ∈ R, {z : ℂ | F z = r} := by
    intro z _
    refine Set.mem_biUnion (?_ : F z ∈ R) rfl
    exact hzero z
  -- each level set is countable unless `F` is constant there
  have hcount : ∀ r ∈ R, {z : ℂ | F z = r}.Countable := by
    intro r _
    have hdiff : Differentiable ℂ fun z => F z - r := hFd.sub (differentiable_const _)
    have horder : ∀ z, meromorphicOrderAt (fun w => F w - r) z ≠ ⊤ := by
      intro z hcon
      refine hnc ⟨r, ?_⟩
      have hfan : AnalyticOnNhd ℂ (fun w => F w - r) Set.univ :=
        hdiff.differentiableOn.analyticOnNhd isOpen_univ
      rw [meromorphicOrderAt_eq_top_iff] at hcon
      have hall := hfan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (Set.mem_univ z) hcon.frequently
      intro w
      have h := hall (Set.mem_univ w)
      simp only [Pi.zero_apply] at h
      linear_combination h
    have hset : {z : ℂ | F z = r} = {z : ℂ | (fun w => F w - r) z = 0} := by
      ext z
      simp [sub_eq_zero]
    rw [hset]
    exact countable_zeroSet hdiff horder
  have hunion : (⋃ r ∈ R, {z : ℂ | F z = r}).Countable :=
    Set.Countable.biUnion hRfin.countable hcount
  have huniv : (Set.univ : Set ℂ).Countable := hunion.mono hcover
  exact absurd huniv (Set.not_countable_univ)

end

end GaloisForLFunctions.HTGeometry
