import GaloisForLFunctions.HTGeometry.GammaBlockSumDatum
import GaloisForLFunctions.HTGeometry.GammaMonomialStripLimit
import GaloisForLFunctions.HTGeometry.JetNonNegligible

/-!
# The boundary datum of a jet polynomial against a balanced monomial

A balanced gamma monomial tends to `1` uniformly on every vertical tube, so multiplying by it
changes no growth order at all: it neither creates nor destroys negligibility.  Hence a nonzero jet
polynomial times a balanced monomial has a boundary datum, unconditionally.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {r : ℕ}

/-- **A balanced gamma monomial tends to `1` on every tube.** -/
theorem tubeLimit_gammaMonomial (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0) (hmom : ∑ i, ((g i : ℤ) : ℝ) * lam i = 0)
    {M : ℝ} (hM : 0 < M) :
    TubeLimit M (fun σ t => gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g
      ((σ : ℂ) + (t : ℂ) * Complex.I)) 1 := by
  have hef : ∀ i, ((((g i).toNat : ℤ)) - ((((-(g i)).toNat) : ℤ))) = g i := fun i =>
    toNat_sub_toNat_neg (g i)
  have hdeg' : ∑ i, ((((g i).toNat) : ℤ)) = ∑ i, ((((-(g i)).toNat) : ℤ)) := by
    have hz : ∑ i, (((((g i).toNat) : ℤ)) - ((((-(g i)).toNat) : ℤ))) = 0 := by
      rw [← hdeg]; exact Finset.sum_congr rfl fun i _ => hef i
    rw [Finset.sum_sub_distrib] at hz
    linarith
  have hmom' : ∑ i, ((((g i).toNat) : ℝ)) * lam i = ∑ i, ((((-(g i)).toNat) : ℝ)) * lam i := by
    have hstep : ∀ i : Fin r, ((((g i).toNat) : ℝ)) * lam i - ((((-(g i)).toNat) : ℝ)) * lam i
        = ((g i : ℤ) : ℝ) * lam i := by
      intro i
      have hR : ((((g i).toNat) : ℝ)) - ((((-(g i)).toNat) : ℝ)) = ((g i : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (hef i)
      calc ((((g i).toNat) : ℝ)) * lam i - ((((-(g i)).toNat) : ℝ)) * lam i
          = (((((g i).toNat) : ℝ)) - ((((-(g i)).toNat) : ℝ))) * lam i := by ring
        _ = ((g i : ℤ) : ℝ) * lam i := by rw [hR]
    have hz : ∑ i, (((((g i).toNat) : ℝ)) * lam i - ((((-(g i)).toNat) : ℝ)) * lam i) = 0 := by
      rw [← hmom]; exact Finset.sum_congr rfl fun i _ => hstep i
    rw [Finset.sum_sub_distrib] at hz
    linarith
  have htube := tubeLimit_gammaProd_ratio hM lam hlam
    (fun i => (g i).toNat) (fun i => ((-(g i)).toNat)) hdeg' hmom'
  intro ε hε
  obtain ⟨T, hT⟩ := htube ε hε
  refine ⟨T, fun σ t hσ hσM ht => ?_⟩
  have h := hT σ t hσ hσM ht
  dsimp only at h
  rwa [gammaProd_ratio_eq_gammaMonomial (σ := σ) (t := t) lam hlam g hσ] at h

/-- **A balanced monomial is bounded away from zero on every tube.** -/
theorem exists_norm_gammaMonomial_ge_half (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0) (hmom : ∑ i, ((g i : ℤ) : ℝ) * lam i = 0)
    {M : ℝ} (hM : 0 < M) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
      (1 : ℝ) / 2 ≤ ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨T, hT⟩ := tubeLimit_gammaMonomial lam hlam g hdeg hmom hM (1 / 2) (by norm_num)
  refine ⟨max T 2, le_max_right _ _, fun σ t hσ hσM ht => ?_⟩
  have h := hT σ t hσ hσM (le_trans (le_max_left _ _) ht)
  dsimp only at h
  have hrev := norm_sub_norm_le (1 : ℂ)
    (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g ((σ : ℂ) + (t : ℂ) * Complex.I))
  rw [norm_one, norm_sub_rev] at hrev
  linarith

/-- Multiplying by a balanced monomial does not create negligibility. -/
theorem not_isVerticallyNegligible_mul_gammaMonomial {f : ℂ → ℂ}
    (hf : ¬ IsVerticallyNegligible f) (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0) (hmom : ∑ i, ((g i : ℤ) : ℝ) * lam i = 0) :
    ¬ IsVerticallyNegligible
      (fun z => f z * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z) := by
  intro hneg
  refine hf fun M hM N => ?_
  obtain ⟨C, T, hC0, hT2, hb⟩ := hneg M hM N
  obtain ⟨T', hT'2, hhalf⟩ := exists_norm_gammaMonomial_ge_half lam hlam g hdeg hmom hM
  refine ⟨2 * C, max T T', by linarith, le_trans hT2 (le_max_left _ _), fun σ t hσ hσM ht => ?_⟩
  have h1 := hb σ t hσ hσM (le_trans (le_max_left _ _) ht)
  have h2 := hhalf σ t hσ hσM (le_trans (le_max_right _ _) ht)
  have htpos : (0 : ℝ) < t := by
    have : (2 : ℝ) ≤ t := le_trans hT2 (le_trans (le_max_left _ _) ht)
    linarith
  have hprod : ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      * ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ C / t ^ N := by
    rw [← norm_mul]
    exact h1
  have hfn : (0 : ℝ) ≤ ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  have hlow : ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * (1 / 2)
      ≤ ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        * ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
    mul_le_mul_of_nonneg_left h2 hfn
  have hfin : ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * (1 / 2) ≤ C / t ^ N := by linarith
  have h2C : (2 : ℝ) * C / t ^ N = 2 * (C / t ^ N) := by ring
  rw [h2C]
  linarith [hfin]

/-- A nonzero jet polynomial is not vertically negligible. -/
theorem not_isVerticallyNegligible_jetFieldPolyFun (lam : Fin r → ℝ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ) (hinj : Function.Injective idx)
    {P : MvPolynomial (Fin Mm) (Polynomial ℂ)} (hP : P ≠ 0) :
    ¬ IsVerticallyNegligible (jetFieldPolyFun lam idx P) := by
  have hPmap : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P ≠ 0 := by
    intro h0
    refine hP ?_
    have hmap : Function.Injective
        (MvPolynomial.map (σ := Fin Mm) (algebraMap (Polynomial ℂ) (RatFunc ℂ))) :=
      MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    exact hmap (by rw [h0, map_zero])
  have hgerm := not_isGermNegligible_shiftedJetEval lam hincong idx hinj hPmap
  rw [shiftedJetEval_map_eq_coe_field lam idx P] at hgerm
  intro hneg
  exact hgerm (isGermNegligible_coe.mpr hneg)

/-- **The boundary datum of a nonzero jet polynomial against a balanced monomial.** -/
theorem exists_hasShiftTubeDatum_jetGammaBalanced (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ) (hinj : Function.Injective idx)
    {P : MvPolynomial (Fin Mm) (Polynomial ℂ)} (hP : P ≠ 0)
    (e : Fin r → ℤ) (hdeg : ∑ i, e i = 0) (hmom : ∑ i, ((e i : ℤ) : ℝ) * lam i = 0)
    {M : ℝ} (hM : 0 < M) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => jetFieldPolyFun lam idx P ((σ : ℂ) + (t : ℂ) * Complex.I)
          * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) e ((σ : ℂ) + (t : ℂ) * Complex.I))
        0 ((a : ℝ)) b c := by
  refine exists_hasShiftTubeDatum_of_logRatApprox
    ((hasLogRatApprox_jetFieldPolyFun lam hlam idx P).mul
      (hasRatApprox_gammaMonomial lam hlam e hdeg hmom).hasLogRatApprox) ?_ hM
  exact not_isVerticallyNegligible_mul_gammaMonomial
    (not_isVerticallyNegligible_jetFieldPolyFun lam hincong idx hinj hP) lam hlam e hdeg hmom

end

end GaloisForLFunctions.HTGeometry
