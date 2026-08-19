import GaloisForLFunctions.HTGeometry.GammaMonomialExpansion
import GaloisForLFunctions.HTGeometry.InverseSeriesFirstCoefficient
import GaloisForLFunctions.HTGeometry.GammaShiftLadderSeparation

/-!
# The leading deviation of a nontrivial balanced gamma monomial

A balanced gamma monomial with distinct real shifts and a nonzero exponent vector is not identically
`1`, and its deviation from `1` has an exact leading term `c·s^{-(m+1)}` with `c ≠ 0`.

The exponent `m+1` and the constant `c` come from the forced ladder; the fact that some ladder
coefficient is nonzero is the Vandermonde separation of the ladder moments.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- **A nontrivial balanced exponent vector has a nonzero ladder moment.** -/
theorem exists_gammaLadderCoeff_ne_zero {r : ℕ} (lam : Fin r → ℝ)
    (hinj : Function.Injective lam) (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0)
    (hgne : ∃ k, g k ≠ 0) : ∃ m, gammaLadderCoeff lam g m ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hinjC : Function.Injective (fun i => ((lam i : ℝ) : ℂ)) :=
    Complex.ofReal_injective.comp hinj
  have hdegC : ∑ k, ((g k : ℤ) : ℂ) = 0 := by
    have hz : ((∑ k, g k : ℤ) : ℂ) = 0 := by rw [hdeg]; simp
    rw [← hz]
    push_cast
    ring
  have hmom : ∀ m : ℕ, m + 2 ≤ r →
      ∑ k, ((g k : ℤ) : ℂ) * shiftLadderCoeff ((lam k : ℝ) : ℂ) m = 0 := by
    intro m _
    have := hcon m
    rwa [gammaLadderCoeff, balancedLadderCoeff] at this
  have hzero := eq_zero_of_ladder_moments_vanish (fun i => ((lam i : ℝ) : ℂ)) hinjC
    (fun k => ((g k : ℤ) : ℂ)) hdegC hmom
  obtain ⟨k, hk⟩ := hgne
  exact hk (by exact_mod_cast hzero k)

/-- **The exact leading deviation.** -/
theorem exists_gammaMonomial_leading_deviation {r : ℕ} (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hinj : Function.Injective lam) (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0)
    (hmom : ∑ i, (g i : ℝ) * lam i = 0) (hgne : ∃ k, g k ≠ 0) :
    ∃ (m : ℕ) (c : ℂ) (A R₀ : ℝ), c ≠ 0 ∧ 0 ≤ A ∧ 1 ≤ R₀ ∧ ∀ s : ℂ, R₀ < s.re →
      ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s - 1 - c * (s⁻¹) ^ (m + 1)‖
        ≤ A / ‖s‖ ^ (m + 2) := by
  have hmomC : ∑ i, ((g i : ℤ) : ℂ) * ((lam i : ℝ) : ℂ) = 0 := by
    have hcast : ((∑ i, (g i : ℝ) * lam i : ℝ) : ℂ) = 0 := by rw [hmom]; simp
    rw [← hcast]
    push_cast
    ring
  have hD0 : gammaLadderCoeff lam g 0 = 0 := balancedLadderCoeff_zero _ g hdeg hmomC
  obtain ⟨M, hcne, hone⟩ := exists_first_expCoeffSeq_ne_zero (gammaLadderCoeff lam g) hD0
    (exists_gammaLadderCoeff_ne_zero lam hinj g hdeg hgne)
  obtain ⟨A, R₀, hA0, hR₀, hb⟩ := exists_norm_gammaMonomial_expansion lam hlam g hdeg hmom (M + 1)
  refine ⟨M, expCoeffSeq (gammaLadderCoeff lam g) (M + 1), A, R₀, hcne, hA0, hR₀, fun s hs => ?_⟩
  have hev : (gammaExpPoly lam g (M + 1)).eval s⁻¹
      = 1 + expCoeffSeq (gammaLadderCoeff lam g) (M + 1) * (s⁻¹) ^ (M + 1) := by
    rw [gammaExpPoly_eq, expPoly_succ_eq, hone, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have h := hb s hs
  rw [hev] at h
  have hrw : gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s
      - (1 + expCoeffSeq (gammaLadderCoeff lam g) (M + 1) * (s⁻¹) ^ (M + 1))
      = gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s - 1
        - expCoeffSeq (gammaLadderCoeff lam g) (M + 1) * (s⁻¹) ^ (M + 1) := by ring
  rw [hrw] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
