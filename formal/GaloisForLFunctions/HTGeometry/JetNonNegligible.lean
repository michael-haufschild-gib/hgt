import GaloisForLFunctions.HTGeometry.JetIncrementFlat
import GaloisForLFunctions.HTGeometry.RationalShiftHypertranscendence

/-!
# No nonzero jet polynomial is negligible

The germs of the shifted digamma jets at the upper end, together with the germs of rational
functions, carry all the structure the Hölder eliminator needs: the negligible germs are closed
under subtraction, under rational multiples and under the unit shift, a nonzero rational function is
not negligible, and no nonzero constant charge on the increments is a rational shift coboundary.

Hence a polynomial in the jets whose value decays faster than every power of the height must be
zero.  This is the analytic replacement for the injectivity of the formal Stirling expansion.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions RationalIncrementHolder

noncomputable section

local instance germRatFuncAlgebra : Algebra (RatFunc ℂ) (Germ upperEndFilter ℂ) :=
  ratFuncGerm.toAlgebra

variable {r : ℕ}

/-- The unit shift of a rational germ is the germ of the shifted rational function. -/
theorem upperEndTranslateGerm_ratFuncGerm (k : RatFunc ℂ) :
    upperEndTranslateGerm 1 (ratFuncGerm k) = ratFuncGerm (ratShift k) := by
  have hden : k.denom ≠ 0 := RatFunc.denom_ne_zero k
  have hdenc : k.denom.comp (Polynomial.X + Polynomial.C 1) ≠ 0 :=
    comp_X_add_C_one_ne_zero hden
  have hk : k = algebraMap (Polynomial ℂ) (RatFunc ℂ) k.num
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) k.denom := (RatFunc.num_div_denom k).symm
  have hshift : ratShift k
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (k.num.comp (Polynomial.X + Polynomial.C 1))
        / algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (k.denom.comp (Polynomial.X + Polynomial.C 1)) := by
    conv_lhs => rw [hk]
    rw [map_div₀, ratShift_algebraMap, ratShift_algebraMap]
  conv_lhs => rw [hk]
  rw [ratFuncGerm_div hden, hshift, ratFuncGerm_div hdenc, upperEndTranslateGerm_coe]
  refine Germ.coe_eq.mpr ?_
  filter_upwards with z
  simp [Polynomial.eval_comp]

/-- The evaluation of a jet polynomial as a germ at the upper end. -/
def shiftedJetEval (lam : Fin r → ℝ) {M : ℕ} (idx : Fin M → Fin r × ℕ)
    (P : MvPolynomial (Fin M) (RatFunc ℂ)) : Germ upperEndFilter ℂ :=
  MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ))
    (fun k => jetGerm lam (idx k)) P

/-- **No nonzero polynomial in the shifted digamma jets is vertically negligible.** -/
theorem not_isGermNegligible_shiftedJetEval (lam : Fin r → ℝ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {M : ℕ} (idx : Fin M → Fin r × ℕ) (hinj : Function.Injective idx)
    {P : MvPolynomial (Fin M) (RatFunc ℂ)} (hP : P ≠ 0) :
    ¬ IsGermNegligible (shiftedJetEval lam idx P) := by
  classical
  intro hneg
  set lamC : Fin r → ℂ := fun i => ((lam i : ℝ) : ℂ) with hlamC
  set rj : ℕ → RatFunc ℂ := fun n =>
    if h : n < M then familyIncrement lamC (idx ⟨n, h⟩).1 (idx ⟨n, h⟩).2 else 0 with hrj
  have hrjk : ∀ k : Fin M, rj (k : ℕ) = familyIncrement lamC (idx k).1 (idx k).2 := by
    intro k
    rw [hrj]
    simp only [k.isLt, dif_pos, Fin.eta]
  set I : Set (MvPolynomial (Fin M) (RatFunc ℂ)) :=
    {G | IsGermNegligible (shiftedJetEval lam idx G)} with hI
  have hjetHom : ∀ G H : MvPolynomial (Fin M) (RatFunc ℂ),
      shiftedJetEval lam idx (G - H) = shiftedJetEval lam idx G - shiftedJetEval lam idx H := by
    intro G H
    rw [shiftedJetEval, shiftedJetEval, shiftedJetEval, MvPolynomial.eval₂_sub]
  have hsub : ∀ G H, G ∈ I → H ∈ I → G - H ∈ I := by
    intro G H hG hH
    show IsGermNegligible (shiftedJetEval lam idx (G - H))
    rw [hjetHom]
    exact hG.sub hH
  have hsmul : ∀ (k : RatFunc ℂ) (G), G ∈ I → MvPolynomial.C k * G ∈ I := by
    intro k G hG
    show IsGermNegligible (shiftedJetEval lam idx (MvPolynomial.C k * G))
    have hval : shiftedJetEval lam idx (MvPolynomial.C k * G)
        = ratFuncGerm k * shiftedJetEval lam idx G := by
      rw [shiftedJetEval, shiftedJetEval, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
      rfl
    rw [hval]
    exact hG.mul_ratFuncGerm k
  have hjetShift : ∀ k : Fin M,
      (upperEndTranslationRingEquiv 1) (jetGerm lam (idx k))
        = jetGerm lam (idx k)
          + algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ) (rj (k : ℕ)) := by
    intro k
    rw [hrjk k, upperEndTranslationRingEquiv_apply]
    exact upperEndTranslateGerm_jetGerm lam (idx k)
  have hbase : ∀ q : RatFunc ℂ,
      (upperEndTranslationRingEquiv 1) (algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ) q)
        = algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ) (ratShift q) := by
    intro q
    rw [upperEndTranslationRingEquiv_apply]
    exact upperEndTranslateGerm_ratFuncGerm q
  have hshift : ∀ G, G ∈ I → jetTranslateWith rj M G ∈ I := by
    intro G hG
    show IsGermNegligible (shiftedJetEval lam idx (jetTranslateWith rj M G))
    have hval := eval₂_jetTranslateWith (upperEndTranslationRingEquiv 1) hbase rj
      (fun k => jetGerm lam (idx k)) hjetShift G
    rw [shiftedJetEval, hval, upperEndTranslationRingEquiv_apply]
    exact hG.shift
  have hconst : ∀ k : RatFunc ℂ, MvPolynomial.C k ∈ I → k = 0 := by
    intro k hk
    by_contra hkne
    have hval : shiftedJetEval lam idx (MvPolynomial.C k) = ratFuncGerm k := by
      rw [shiftedJetEval, MvPolynomial.eval₂_C]
      rfl
    have : IsGermNegligible (ratFuncGerm k) := by
      have := hk
      rw [hI] at this
      rw [← hval]
      exact this
    exact not_isGermNegligible_ratFuncGerm hkne this
  have Hres : ∀ {w : RatFunc ℂ} {δ : Fin M → ℂ},
      ratShift w - w = ∑ j : Fin M, algebraMap ℂ (RatFunc ℂ) (δ j) * rj (j : ℕ) →
      ∀ j, δ j = 0 := by
    intro w δ hsum
    refine ratShift_sub_familyIncrement_flat lamC ?_ idx hinj (w := w) (delta := δ) ?_
    · intro i i' hii n
      exact hincong i i' hii n
    · rw [hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hrjk k]
  exact no_shift_stable_annihilatorWith rj I hsub hsmul hshift hconst Hres ⟨P, hneg, hP⟩

end

end GaloisForLFunctions.HTGeometry
