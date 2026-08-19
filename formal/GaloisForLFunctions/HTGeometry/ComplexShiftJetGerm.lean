import GaloisForLFunctions.HTGeometry.JetNonNegligible

/-!
# Digamma jet germs at complex shifts

The elimination that shows no nonzero polynomial in the digamma jets is negligible at the upper end
is driven by one law only: the unit translate of each jet germ differs from it by a fixed rational
increment.  That law holds for an arbitrary complex shift — a shift moves the imaginary part by a
bounded amount, so far up the tube the shifted argument still avoids the poles — and the
incongruence obstruction that finishes the elimination is already stated over `ℂ`.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions RationalIncrementHolder

noncomputable section

attribute [local instance] germRatFuncAlgebra

variable {r : ℕ}

/-- The germ of a digamma jet at a complex shift. -/
def jetGermC (lam : Fin r → ℂ) (p : Fin r × ℕ) : Germ upperEndFilter ℂ :=
  ((fun z : ℂ => iteratedDeriv p.2 Complex.digamma (z + lam p.1)) : Germ upperEndFilter ℂ)

/-- **The unit shift moves each complex-shifted jet germ by its rational increment.** -/
theorem upperEndTranslateGerm_jetGermC (lam : Fin r → ℂ) (p : Fin r × ℕ) :
    upperEndTranslateGerm 1 (jetGermC lam p)
      = jetGermC lam p + ratFuncGerm (familyIncrement lam p.1 p.2) := by
  have hincr : familyIncrement lam p.1 p.2
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C ((-1 : ℂ) ^ p.2 * ((p.2.factorial : ℕ) : ℂ)))
        / algebraMap (Polynomial ℂ) (RatFunc ℂ)
          ((Polynomial.X + Polynomial.C (lam p.1)) ^ (p.2 + 1)) := by
    rw [familyIncrement]
    simp [map_pow, map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hqne : ((Polynomial.X + Polynomial.C (lam p.1)) ^ (p.2 + 1)) ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_add_C_ne_zero _)
  rw [hincr, ratFuncGerm_div hqne, jetGermC, upperEndTranslateGerm_coe]
  refine Germ.coe_eq.mpr ?_
  have hmem : upperTail ‖lam p.1‖ ∈ upperEndFilter :=
    upperEndFilter_basis.mem_of_mem (i := ‖lam p.1‖) trivial
  filter_upwards [hmem] with z hz
  have hzim : ‖lam p.1‖ < z.im := hz
  have himle : |(lam p.1).im| ≤ ‖lam p.1‖ := Complex.abs_im_le_norm _
  have himge : -‖lam p.1‖ ≤ (lam p.1).im := (abs_le.mp himle).1
  have hpole : ∀ m : ℕ, z + lam p.1 ≠ -(m : ℂ) := by
    intro m hm
    have him : (z + lam p.1).im = 0 := by
      rw [hm]
      simp
    simp only [Complex.add_im] at him
    linarith
  have hrec := _root_.HTGeometry.iteratedDeriv_digamma_add_nat p.2 (z + lam p.1) hpole 1
  simp only [Nat.cast_one, Finset.sum_range_one, Nat.cast_zero, add_zero] at hrec
  have hshift : z + 1 + lam p.1 = (z + lam p.1) + 1 := by ring
  rw [hshift, hrec]
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- The evaluation of a jet polynomial at complex shifts, as a germ at the upper end. -/
def shiftedJetEvalC (lam : Fin r → ℂ) {M : ℕ} (idx : Fin M → Fin r × ℕ)
    (P : MvPolynomial (Fin M) (RatFunc ℂ)) : Germ upperEndFilter ℂ :=
  MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ))
    (fun k => jetGermC lam (idx k)) P

/-- **No nonzero polynomial in the complex-shifted digamma jets is vertically negligible.** -/
theorem not_isGermNegligible_shiftedJetEvalC (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ))
    {M : ℕ} (idx : Fin M → Fin r × ℕ) (hinj : Function.Injective idx)
    {P : MvPolynomial (Fin M) (RatFunc ℂ)} (hP : P ≠ 0) :
    ¬ IsGermNegligible (shiftedJetEvalC lam idx P) := by
  classical
  intro hneg
  set rj : ℕ → RatFunc ℂ := fun n =>
    if h : n < M then familyIncrement lam (idx ⟨n, h⟩).1 (idx ⟨n, h⟩).2 else 0 with hrj
  have hrjk : ∀ k : Fin M, rj (k : ℕ) = familyIncrement lam (idx k).1 (idx k).2 := by
    intro k
    rw [hrj]
    simp only [k.isLt, dif_pos, Fin.eta]
  set I : Set (MvPolynomial (Fin M) (RatFunc ℂ)) :=
    {G | IsGermNegligible (shiftedJetEvalC lam idx G)} with hI
  have hjetHom : ∀ G H : MvPolynomial (Fin M) (RatFunc ℂ),
      shiftedJetEvalC lam idx (G - H) = shiftedJetEvalC lam idx G - shiftedJetEvalC lam idx H := by
    intro G H
    rw [shiftedJetEvalC, shiftedJetEvalC, shiftedJetEvalC, MvPolynomial.eval₂_sub]
  have hsub : ∀ G H, G ∈ I → H ∈ I → G - H ∈ I := by
    intro G H hG hH
    show IsGermNegligible (shiftedJetEvalC lam idx (G - H))
    rw [hjetHom]
    exact hG.sub hH
  have hsmul : ∀ (k : RatFunc ℂ) (G), G ∈ I → MvPolynomial.C k * G ∈ I := by
    intro k G hG
    show IsGermNegligible (shiftedJetEvalC lam idx (MvPolynomial.C k * G))
    have hval : shiftedJetEvalC lam idx (MvPolynomial.C k * G)
        = ratFuncGerm k * shiftedJetEvalC lam idx G := by
      rw [shiftedJetEvalC, shiftedJetEvalC, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
      rfl
    rw [hval]
    exact hG.mul_ratFuncGerm k
  have hjetShift : ∀ k : Fin M,
      (upperEndTranslationRingEquiv 1) (jetGermC lam (idx k))
        = jetGermC lam (idx k)
          + algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ) (rj (k : ℕ)) := by
    intro k
    rw [hrjk k, upperEndTranslationRingEquiv_apply]
    exact upperEndTranslateGerm_jetGermC lam (idx k)
  have hbase : ∀ q : RatFunc ℂ,
      (upperEndTranslationRingEquiv 1) (algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ) q)
        = algebraMap (RatFunc ℂ) (Germ upperEndFilter ℂ) (ratShift q) := by
    intro q
    rw [upperEndTranslationRingEquiv_apply]
    exact upperEndTranslateGerm_ratFuncGerm q
  have hshift : ∀ G, G ∈ I → jetTranslateWith rj M G ∈ I := by
    intro G hG
    show IsGermNegligible (shiftedJetEvalC lam idx (jetTranslateWith rj M G))
    have hval := eval₂_jetTranslateWith (upperEndTranslationRingEquiv 1) hbase rj
      (fun k => jetGermC lam (idx k)) hjetShift G
    rw [shiftedJetEvalC, hval, upperEndTranslationRingEquiv_apply]
    exact hG.shift
  have hconst : ∀ k : RatFunc ℂ, MvPolynomial.C k ∈ I → k = 0 := by
    intro k hk
    by_contra hkne
    have hval : shiftedJetEvalC lam idx (MvPolynomial.C k) = ratFuncGerm k := by
      rw [shiftedJetEvalC, MvPolynomial.eval₂_C]
      rfl
    have hnegk : IsGermNegligible (ratFuncGerm k) := by
      have hmem := hk
      rw [hI] at hmem
      rw [← hval]
      exact hmem
    exact not_isGermNegligible_ratFuncGerm hkne hnegk
  have Hres : ∀ {w : RatFunc ℂ} {δ : Fin M → ℂ},
      ratShift w - w = ∑ j : Fin M, algebraMap ℂ (RatFunc ℂ) (δ j) * rj (j : ℕ) →
      ∀ j, δ j = 0 := by
    intro w δ hsum
    refine ratShift_sub_familyIncrement_flat lam ?_ idx hinj (w := w) (delta := δ) ?_
    · intro i i' hii n
      exact hincong i i' hii n
    · rw [hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hrjk k]
  exact no_shift_stable_annihilatorWith rj I hsub hsmul hshift hconst Hres ⟨P, hneg, hP⟩

end

end GaloisForLFunctions.HTGeometry
