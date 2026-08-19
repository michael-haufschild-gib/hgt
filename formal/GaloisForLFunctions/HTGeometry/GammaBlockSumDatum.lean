import GaloisForLFunctions.HTGeometry.GammaMonomialRatApprox
import GaloisForLFunctions.HTGeometry.ShiftedJetFieldDatum

/-!
# The boundary datum of a balanced block

Inside a dominance block every Gamma monomial ratio is balanced, hence rationally approximable, so a
block sum of jet polynomials against balanced monomials lies in the corpus's class
`HasLogRatApprox`.  Its boundary datum then follows from non-negligibility alone.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {r : ℕ}

theorem HasLogRatApprox.finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, HasLogRatApprox (f i)) : HasLogRatApprox (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hfun : (fun z : ℂ => ∑ i ∈ (∅ : Finset ι), f i z) = fun _ : ℂ => (0 : ℂ) := by
        funext z; simp
      rw [hfun]
      exact (hasRatApprox_const 0).hasLogRatApprox
  | insert a s ha ih =>
      have hfun : (fun z : ℂ => ∑ i ∈ insert a s, f i z)
          = fun z : ℂ => f a z + ∑ i ∈ s, f i z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **A balanced block sum is log-rationally approximable.** -/
theorem hasLogRatApprox_balancedBlockSum (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    {Mm K : ℕ} (idx : Fin K → Fin r × ℕ)
    (P : Fin Mm → MvPolynomial (Fin K) (Polynomial ℂ)) (e : Fin Mm → Fin r → ℤ)
    (hdeg : ∀ α, ∑ i, e α i = 0) (hmom : ∀ α, ∑ i, ((e α i : ℤ) : ℝ) * lam i = 0) :
    HasLogRatApprox (fun z => ∑ α : Fin Mm, jetFieldPolyFun lam idx (P α) z
      * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z) := by
  refine HasLogRatApprox.finsetSum _ _ fun α _ => ?_
  exact (hasLogRatApprox_jetFieldPolyFun lam hlam idx (P α)).mul
    (hasRatApprox_gammaMonomial lam hlam (e α) (hdeg α) (hmom α)).hasLogRatApprox

/-- **The boundary datum of a balanced block sum.**  The only remaining input is that the sum is not
vertically negligible. -/
theorem exists_hasShiftTubeDatum_balancedBlockSum (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    {Mm K : ℕ} (idx : Fin K → Fin r × ℕ)
    (P : Fin Mm → MvPolynomial (Fin K) (Polynomial ℂ)) (e : Fin Mm → Fin r → ℤ)
    (hdeg : ∀ α, ∑ i, e α i = 0) (hmom : ∀ α, ∑ i, ((e α i : ℤ) : ℝ) * lam i = 0)
    (hnn : ¬ IsVerticallyNegligible (fun z => ∑ α : Fin Mm, jetFieldPolyFun lam idx (P α) z
      * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α) z))
    {M : ℝ} (hM : 0 < M) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => ∑ α : Fin Mm,
          jetFieldPolyFun lam idx (P α) ((σ : ℂ) + (t : ℂ) * Complex.I)
            * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) (e α)
              ((σ : ℂ) + (t : ℂ) * Complex.I)) 0 ((a : ℝ)) b c :=
  exists_hasShiftTubeDatum_of_logRatApprox
    (hasLogRatApprox_balancedBlockSum lam hlam idx P e hdeg hmom) hnn hM

end

end GaloisForLFunctions.HTGeometry
