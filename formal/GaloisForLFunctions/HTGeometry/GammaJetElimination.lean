import GaloisForLFunctions.HTGeometry.JetGermShift
import GaloisForLFunctions.HTGeometry.GammaMonomialGerm
import GaloisForLFunctions.HTGeometry.JetPolynomialCoboundary

/-!
# Ring lemmas for the jet germ evaluation, and the one-term elimination

`shiftedJetEval` is a ring homomorphism into the germs; and a single jet polynomial against a
balanced Gamma monomial is negligible only if the polynomial vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

local instance gammaElimRatFuncAlgebra : Algebra (RatFunc ℂ) (Germ upperEndFilter ℂ) :=
  ratFuncGerm.toAlgebra

variable {r : ℕ}

theorem shiftedJetEval_C (lam : Fin r → ℝ) {M : ℕ} (idx : Fin M → Fin r × ℕ) (a : RatFunc ℂ) :
    shiftedJetEval lam idx (MvPolynomial.C a) = ratFuncGerm a := by
  rw [shiftedJetEval, MvPolynomial.eval₂_C]
  rfl

theorem shiftedJetEval_mul (lam : Fin r → ℝ) {M : ℕ} (idx : Fin M → Fin r × ℕ)
    (P Q : MvPolynomial (Fin M) (RatFunc ℂ)) :
    shiftedJetEval lam idx (P * Q) = shiftedJetEval lam idx P * shiftedJetEval lam idx Q := by
  rw [shiftedJetEval, shiftedJetEval, shiftedJetEval, MvPolynomial.eval₂_mul]

theorem shiftedJetEval_sub (lam : Fin r → ℝ) {M : ℕ} (idx : Fin M → Fin r × ℕ)
    (P Q : MvPolynomial (Fin M) (RatFunc ℂ)) :
    shiftedJetEval lam idx (P - Q) = shiftedJetEval lam idx P - shiftedJetEval lam idx Q := by
  rw [shiftedJetEval, shiftedJetEval, shiftedJetEval, MvPolynomial.eval₂_sub]

theorem shiftedJetEval_zero (lam : Fin r → ℝ) {M : ℕ} (idx : Fin M → Fin r × ℕ) :
    shiftedJetEval lam idx 0 = 0 := by
  rw [shiftedJetEval, MvPolynomial.eval₂_zero]

/-- **The one-term elimination.** -/
theorem eq_zero_of_isGermNegligible_single (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {M : ℕ} (idx : Fin M → Fin r × ℕ) (hinj : Function.Injective idx)
    (P : MvPolynomial (Fin M) (RatFunc ℂ)) (e : Fin r → ℤ)
    (hdeg : ∑ i, e i = 0) (hmom : ∑ i, ((e i : ℤ) : ℝ) * lam i = 0)
    (hneg : IsGermNegligible (shiftedJetEval lam idx P * gammaMonomialGerm lam e)) :
    P = 0 := by
  by_contra hP
  obtain ⟨f, hf, hfg⟩ := exists_polyGrowth_rep_shiftedJetEval lam hlam idx P
  have hcoe : shiftedJetEval lam idx P * gammaMonomialGerm lam e
      = ((fun z : ℂ => f z * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) e z)
          : Germ upperEndFilter ℂ) := by
    rw [← hf, gammaMonomialGerm]
    rfl
  rw [hcoe, isGermNegligible_coe] at hneg
  have hfneg : IsVerticallyNegligible f :=
    (isVerticallyNegligible_mul_gammaMonomial_iff lam hlam e hdeg hmom).mp hneg
  have hgerm : IsGermNegligible (shiftedJetEval lam idx P) := by
    rw [← hf, isGermNegligible_coe]
    exact hfneg
  exact not_isGermNegligible_shiftedJetEval lam hincong idx hinj hP hgerm

theorem gammaShiftFactor_ne_zero (lam : Fin r → ℝ) (e : Fin r → ℤ) :
    gammaShiftFactor lam e ≠ 0 := by
  rw [gammaShiftFactor]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ ?_
  have hXC : (RatFunc.X + RatFunc.C ((lam k : ℝ) : ℂ))
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.X + Polynomial.C ((lam k : ℝ) : ℂ)) := by
    rw [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [hXC]
  exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero _)

theorem gammaShiftFactor_add (lam : Fin r → ℝ) (a b : Fin r → ℤ) :
    gammaShiftFactor lam (fun i => a i + b i)
      = gammaShiftFactor lam a * gammaShiftFactor lam b := by
  rw [gammaShiftFactor, gammaShiftFactor, gammaShiftFactor, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hne : (RatFunc.X + RatFunc.C ((lam k : ℝ) : ℂ)) ≠ 0 := by
    have hXC : (RatFunc.X + RatFunc.C ((lam k : ℝ) : ℂ))
        = algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.X + Polynomial.C ((lam k : ℝ) : ℂ)) := by
      rw [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    rw [hXC]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero _)
  rw [zpow_add₀ hne]

set_option maxHeartbeats 1000000 in
/-- **The shift elimination.**  A negligible combination of jet polynomials against Gamma monomials
with distinct balanced exponent vectors has every coefficient zero. -/
theorem eq_zero_of_isGermNegligible_gammaCombination (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {M : ℕ} (idx : Fin M → Fin r × ℕ) (hinj : Function.Injective idx)
    {ι : Type} [DecidableEq ι] (e : ι → Fin r → ℤ) (he : Function.Injective e)
    (hdeg : ∀ α, ∑ i, e α i = 0) (hmom : ∀ α, ∑ i, ((e α i : ℤ) : ℝ) * lam i = 0) :
    ∀ (S : Finset ι) (Pf : ι → MvPolynomial (Fin M) (RatFunc ℂ)),
      IsGermNegligible (∑ α ∈ S, shiftedJetEval lam idx (Pf α) * gammaMonomialGerm lam (e α)) →
      ∀ α ∈ S, Pf α = 0 := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro Pf hneg
    by_contra hcon
    push Not at hcon
    obtain ⟨α₀, hα₀S, hα₀ne⟩ := hcon
    set rj : Fin M → RatFunc ℂ :=
      fun k => familyIncrement (fun i => ((lam i : ℝ) : ℂ)) (idx k).1 (idx k).2 with hrj
    have hΨ : (∑ α ∈ S, shiftedJetEval lam idx
          (MvPolynomial.C (gammaShiftFactor lam (e α₀)) * jetShiftPoly rj (Pf α₀) * Pf α
            - MvPolynomial.C (gammaShiftFactor lam (e α)) * Pf α₀ * jetShiftPoly rj (Pf α))
          * gammaMonomialGerm lam (e α))
        = ratFuncGerm (gammaShiftFactor lam (e α₀))
            * shiftedJetEval lam idx (jetShiftPoly rj (Pf α₀))
            * (∑ α ∈ S, shiftedJetEval lam idx (Pf α) * gammaMonomialGerm lam (e α))
          - shiftedJetEval lam idx (Pf α₀)
            * upperEndTranslateGerm 1
              (∑ α ∈ S, shiftedJetEval lam idx (Pf α) * gammaMonomialGerm lam (e α)) := by
      rw [Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_mul, upperEndTranslateGerm_shiftedJetEval, upperEndTranslateGerm_gammaMonomialGerm,
        shiftedJetEval_sub, shiftedJetEval_mul, shiftedJetEval_mul, shiftedJetEval_mul,
        shiftedJetEval_mul, shiftedJetEval_C, shiftedJetEval_C, hrj]
      ring
    have hΨneg : IsGermNegligible (∑ α ∈ S, shiftedJetEval lam idx
        (MvPolynomial.C (gammaShiftFactor lam (e α₀)) * jetShiftPoly rj (Pf α₀) * Pf α
          - MvPolynomial.C (gammaShiftFactor lam (e α)) * Pf α₀ * jetShiftPoly rj (Pf α))
        * gammaMonomialGerm lam (e α)) := by
      rw [hΨ]
      refine IsGermNegligible.sub ?_ ?_
      · rw [mul_assoc]
        exact (hneg.mul_shiftedJetEval lam hlam idx (jetShiftPoly rj (Pf α₀))).mul_ratFuncGerm _
      · exact (hneg.shift).mul_shiftedJetEval lam hlam idx (Pf α₀)
    have hQ'α₀ : MvPolynomial.C (gammaShiftFactor lam (e α₀)) * jetShiftPoly rj (Pf α₀) * Pf α₀
        - MvPolynomial.C (gammaShiftFactor lam (e α₀)) * Pf α₀ * jetShiftPoly rj (Pf α₀)
        = 0 := by ring
    have hsum_erase : (∑ α ∈ S, shiftedJetEval lam idx
          (MvPolynomial.C (gammaShiftFactor lam (e α₀)) * jetShiftPoly rj (Pf α₀) * Pf α
            - MvPolynomial.C (gammaShiftFactor lam (e α)) * Pf α₀ * jetShiftPoly rj (Pf α))
          * gammaMonomialGerm lam (e α))
        = ∑ α ∈ S.erase α₀, shiftedJetEval lam idx
          (MvPolynomial.C (gammaShiftFactor lam (e α₀)) * jetShiftPoly rj (Pf α₀) * Pf α
            - MvPolynomial.C (gammaShiftFactor lam (e α)) * Pf α₀ * jetShiftPoly rj (Pf α))
          * gammaMonomialGerm lam (e α) := by
      rw [← Finset.sum_erase_add S _ hα₀S, hQ'α₀, shiftedJetEval_zero, zero_mul, add_zero]
    rw [hsum_erase] at hΨneg
    have hQzero := ih (S.erase α₀) (Finset.erase_ssubset hα₀S)
      (fun α => MvPolynomial.C (gammaShiftFactor lam (e α₀)) * jetShiftPoly rj (Pf α₀) * Pf α
        - MvPolynomial.C (gammaShiftFactor lam (e α)) * Pf α₀ * jetShiftPoly rj (Pf α)) hΨneg
    have hPzero : ∀ α ∈ S.erase α₀, Pf α = 0 := by
      intro α hα
      by_contra hPα
      have hαne : α ≠ α₀ := Finset.ne_of_mem_erase hα
      have hene : e α ≠ e α₀ := fun h0 => hαne (he h0)
      obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin r, e α i₀ - e α₀ i₀ ≠ 0 := by
        by_contra hnot
        push Not at hnot
        exact hene (funext fun i => by have := hnot i; omega)
      have hρ0 : gammaShiftFactor lam (e α₀) ≠ 0 := gammaShiftFactor_ne_zero lam (e α₀)
      have hC0 : (MvPolynomial.C (gammaShiftFactor lam (e α₀))
          : MvPolynomial (Fin M) (RatFunc ℂ)) ≠ 0 := by
        intro h0
        exact hρ0 (MvPolynomial.C_injective (Fin M) (RatFunc ℂ) (by rw [h0, map_zero]))
      have hfactor : gammaShiftFactor lam (e α)
          = gammaShiftFactor lam (e α₀) * gammaShiftFactor lam (fun i => e α i - e α₀ i) := by
        rw [← gammaShiftFactor_add]
        congr 1
        funext i
        omega
      have hCfac : (MvPolynomial.C (gammaShiftFactor lam (e α₀))
              : MvPolynomial (Fin M) (RatFunc ℂ))
          * MvPolynomial.C (gammaShiftFactor lam (fun i => e α i - e α₀ i))
          = MvPolynomial.C (gammaShiftFactor lam (e α)) := by
        rw [← map_mul, ← hfactor]
      have heq := hQzero α hα
      rw [sub_eq_zero] at heq
      refine no_jetPoly_multiplicative_coboundary (fun i => ((lam i : ℝ) : ℂ)) hincong idx hinj
        hα₀ne hPα (fun i => e α i - e α₀ i) i₀ hi₀ ?_
      have hgoal : gammaShiftFactor lam (fun i => e α i - e α₀ i)
          = ∏ i : Fin r, (RatFunc.X + RatFunc.C ((lam i : ℝ) : ℂ)) ^ (e α i - e α₀ i) := rfl
      rw [← hgoal, ← hrj]
      refine mul_left_cancel₀ hC0 ?_
      linear_combination heq - (Pf α₀ * jetShiftPoly rj (Pf α)) * hCfac
    have hΦ : (∑ α ∈ S, shiftedJetEval lam idx (Pf α) * gammaMonomialGerm lam (e α))
        = shiftedJetEval lam idx (Pf α₀) * gammaMonomialGerm lam (e α₀) := by
      rw [← Finset.sum_erase_add S _ hα₀S]
      have hz : ∑ α ∈ S.erase α₀,
          shiftedJetEval lam idx (Pf α) * gammaMonomialGerm lam (e α) = 0 :=
        Finset.sum_eq_zero fun α hα => by
          rw [hPzero α hα, shiftedJetEval_zero, zero_mul]
      rw [hz, zero_add]
    rw [hΦ] at hneg
    exact hα₀ne (eq_zero_of_isGermNegligible_single lam hlam hincong idx hinj (Pf α₀) (e α₀)
      (hdeg α₀) (hmom α₀) hneg)

end

end GaloisForLFunctions.HTGeometry
