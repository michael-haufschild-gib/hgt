import GaloisForLFunctions.HTGeometry.GammaBlockNonNegligible
import GaloisForLFunctions.HTGeometry.GammaMonomialStripLimit

/-!
# Block sums over an arbitrary finite index

The block datum, indexed by a `Finset` rather than a `Fin`, together with the two identities the
regrouping needs: additivity of a Gamma monomial in its exponent vector, and the identification of
the tube product of `gammaLine` powers with a Gamma monomial.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

local instance gammaBlockFinsetRatFuncAlgebra : Algebra (RatFunc ℂ) (Germ upperEndFilter ℂ) :=
  ratFuncGerm.toAlgebra

variable {r : ℕ}

/-- A Gamma monomial is multiplicative in its exponent vector. -/
theorem gammaMonomial_add (lam : Fin r → ℂ) (a b : Fin r → ℤ) {z : ℂ}
    (hz : ∀ k, Complex.Gamma (z + lam k) ≠ 0) :
    gammaMonomial lam (fun k => a k + b k) z
      = gammaMonomial lam a z * gammaMonomial lam b z := by
  rw [gammaMonomial, gammaMonomial, gammaMonomial, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hz k) _ _

/-- The tube product of `gammaLine` powers is a Gamma monomial. -/
theorem gammaProd_eq_gammaMonomial (lamf : Fin r → ℝ) (e : Fin r → ℕ) (σ t : ℝ) :
    (∏ k : Fin r, gammaLine (σ + lamf k) t ^ (e k))
      = gammaMonomial (fun k => ((lamf k : ℝ) : ℂ)) (fun k => (e k : ℤ))
        ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  rw [gammaMonomial]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hval : gammaLine (σ + lamf k) t
      = Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I + ((lamf k : ℝ) : ℂ)) := by
    rw [gammaLine]
    congr 1
    push_cast
    ring
  rw [hval, zpow_natCast]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The boundary datum of a nonzero balanced block, indexed by a finite set.** -/
theorem exists_hasShiftTubeDatum_balancedBlockFinset (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {K : ℕ} (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    {ι : Type} [DecidableEq ι] [Fintype ι] (P : ι → MvPolynomial (Fin K) (Polynomial ℂ))
    (e : ι → Fin r → ℤ) (he : Function.Injective e) (hdeg : ∀ α, ∑ i, e α i = 0)
    (hmom : ∀ α, ∑ i, ((e α i : ℤ) : ℝ) * lam i = 0) (S : Finset ι) (β : ι) (hβS : β ∈ S)
    (hβ : P β ≠ 0) {M : ℝ} (hM : 0 < M) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => ∑ α ∈ S,
          jetFieldPolyFun lam idx (P α) ((σ : ℂ) + (t : ℂ) * Complex.I)
            * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α)
              ((σ : ℂ) + (t : ℂ) * Complex.I)) 0 ((a : ℝ)) b c := by
  classical
  refine exists_hasShiftTubeDatum_of_logRatApprox
    (f := fun z : ℂ => ∑ α ∈ S, jetFieldPolyFun lam idx (P α) z
      * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) ?_ ?_ hM
  · refine HasLogRatApprox.finsetSum _ _ fun α _ => ?_
    exact (hasLogRatApprox_jetFieldPolyFun lam hlam idx (P α)).mul
      (hasRatApprox_gammaMonomial lam hlam (e α) (hdeg α) (hmom α)).hasLogRatApprox
  · intro hneg
    have hgerm : IsGermNegligible
        (∑ α ∈ S, shiftedJetEval lam idx
          (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (P α))
          * gammaMonomialGerm lam (e α)) := by
      have hfun : ((fun z : ℂ => ∑ α ∈ S, jetFieldPolyFun lam idx (P α) z
              * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) : ℂ → ℂ)
          = ∑ α ∈ S, (fun z : ℂ => jetFieldPolyFun lam idx (P α) z
              * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) := by
        funext z
        rw [Finset.sum_apply]
      have hcoe : (∑ α ∈ S, shiftedJetEval lam idx
            (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (P α))
            * gammaMonomialGerm lam (e α))
          = (((fun z : ℂ => ∑ α ∈ S, jetFieldPolyFun lam idx (P α) z
              * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) : ℂ → ℂ)
            : Germ upperEndFilter ℂ) := by
        have hcoesum : (((∑ α ∈ S, fun z : ℂ => jetFieldPolyFun lam idx (P α) z
                * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) : ℂ → ℂ)
              : Germ upperEndFilter ℂ)
            = ∑ α ∈ S, (((fun z : ℂ => jetFieldPolyFun lam idx (P α) z
                * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) : ℂ → ℂ)
              : Germ upperEndFilter ℂ) :=
          map_sum (Germ.coeRingHom upperEndFilter) _ S
        rw [hfun, hcoesum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [shiftedJetEval_map_eq_coe_field lam idx (P α), gammaMonomialGerm]
        rfl
      rw [hcoe, isGermNegligible_coe]
      exact hneg
    have hzero := eq_zero_of_isGermNegligible_gammaCombination lam hlam hincong idx hinj e he
      hdeg hmom S (fun α => MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (P α))
      hgerm β hβS
    have hmapinj : Function.Injective
        (MvPolynomial.map (σ := Fin K) (algebraMap (Polynomial ℂ) (RatFunc ℂ))) :=
      MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    exact hβ (hmapinj (by rw [hzero, map_zero]))

end

end GaloisForLFunctions.HTGeometry
