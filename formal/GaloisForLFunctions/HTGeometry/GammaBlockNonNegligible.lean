import GaloisForLFunctions.HTGeometry.GammaJetElimination
import GaloisForLFunctions.HTGeometry.GammaBlockSumDatum

/-!
# A nonzero balanced block is not negligible, and therefore has a boundary datum

Transporting the shift elimination from germs back to functions removes the last hypothesis from the
block datum: a block of jet polynomials against Gamma monomials with distinct balanced exponent
vectors has a boundary datum as soon as one of its coefficients is nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

local instance gammaBlockRatFuncAlgebra : Algebra (RatFunc ℂ) (Germ upperEndFilter ℂ) :=
  ratFuncGerm.toAlgebra

variable {r : ℕ}

/-- **A nonzero balanced block is not vertically negligible.** -/
theorem not_isVerticallyNegligible_balancedBlockSum (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {K : ℕ} (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    {A : ℕ} (P : Fin A → MvPolynomial (Fin K) (Polynomial ℂ)) (e : Fin A → Fin r → ℤ)
    (he : Function.Injective e) (hdeg : ∀ α, ∑ i, e α i = 0)
    (hmom : ∀ α, ∑ i, ((e α i : ℤ) : ℝ) * lam i = 0) (β : Fin A) (hβ : P β ≠ 0) :
    ¬ IsVerticallyNegligible (fun z => ∑ α : Fin A, jetFieldPolyFun lam idx (P α) z
      * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) := by
  classical
  intro hneg
  set Pf : Fin A → MvPolynomial (Fin K) (RatFunc ℂ) :=
    fun α => MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (P α) with hPf
  have hgerm : IsGermNegligible
      (∑ α : Fin A, shiftedJetEval lam idx (Pf α) * gammaMonomialGerm lam (e α)) := by
    have hcoe : (∑ α : Fin A, shiftedJetEval lam idx (Pf α) * gammaMonomialGerm lam (e α))
        = (((fun z => ∑ α : Fin A, jetFieldPolyFun lam idx (P α) z
            * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) : ℂ → ℂ)
          : Germ upperEndFilter ℂ) := by
      have hstep : (((fun z => ∑ α : Fin A, jetFieldPolyFun lam idx (P α) z
            * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) : ℂ → ℂ)
          : Germ upperEndFilter ℂ)
          = ∑ α : Fin A, (((fun z => jetFieldPolyFun lam idx (P α) z
              * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) : ℂ → ℂ)
            : Germ upperEndFilter ℂ) := by
        have hfun : ((fun z : ℂ => ∑ α : Fin A, jetFieldPolyFun lam idx (P α) z
              * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) : ℂ → ℂ)
            = ∑ α : Fin A, (fun z : ℂ => jetFieldPolyFun lam idx (P α) z
              * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) := by
          funext z
          rw [Finset.sum_apply]
        rw [hfun]
        exact map_sum (Germ.coeRingHom upperEndFilter)
          (fun α : Fin A => (fun z : ℂ => jetFieldPolyFun lam idx (P α) z
            * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z)) Finset.univ
      rw [hstep]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hPf, shiftedJetEval_map_eq_coe_field lam idx (P α), gammaMonomialGerm]
      rfl
    rw [hcoe, isGermNegligible_coe]
    exact hneg
  have hzero := eq_zero_of_isGermNegligible_gammaCombination lam hlam hincong idx hinj e he
    hdeg hmom Finset.univ Pf hgerm β (Finset.mem_univ β)
  refine hβ ?_
  have hmapinj : Function.Injective
      (MvPolynomial.map (σ := Fin K) (algebraMap (Polynomial ℂ) (RatFunc ℂ))) :=
    MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
  refine hmapinj ?_
  rw [map_zero]
  exact hzero

/-- **The boundary datum of a nonzero balanced block, unconditionally.** -/
theorem exists_hasShiftTubeDatum_balancedBlock (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    {K : ℕ} (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    {A : ℕ} (P : Fin A → MvPolynomial (Fin K) (Polynomial ℂ)) (e : Fin A → Fin r → ℤ)
    (he : Function.Injective e) (hdeg : ∀ α, ∑ i, e α i = 0)
    (hmom : ∀ α, ∑ i, ((e α i : ℤ) : ℝ) * lam i = 0) (β : Fin A) (hβ : P β ≠ 0)
    {M : ℝ} (hM : 0 < M) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => ∑ α : Fin A,
          jetFieldPolyFun lam idx (P α) ((σ : ℂ) + (t : ℂ) * Complex.I)
            * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α)
              ((σ : ℂ) + (t : ℂ) * Complex.I)) 0 ((a : ℝ)) b c :=
  exists_hasShiftTubeDatum_balancedBlockSum lam hlam idx P e hdeg hmom
    (not_isVerticallyNegligible_balancedBlockSum lam hlam hincong idx hinj P e he hdeg hmom β hβ) hM

end

end GaloisForLFunctions.HTGeometry
