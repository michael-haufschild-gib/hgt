import GaloisForLFunctions.RHTower.Sieve.BilinearCauchySchwarz
import GaloisForLFunctions.RHTower.Sieve.DifferencePhaseCurvature
import GaloisForLFunctions.RHTower.Sieve.DilatedNearDiagonalSum

/-!
# The type-II correlation sums

Pairing the dilation identity `F_{T,r}(m·d) = F_{T,r/m}(d)` with the correlation expansion turns
each off-diagonal term of the type-II energy into a single exponential sum over the LONG variable
`d`, with the difference phase `F_{T,r/m₁} − F_{T,r/m₂}`.  Its curvature scale is
`T(r/m₁ − r/m₂)`, so the abstract curved-phase estimate applies verbatim.
-/

namespace RHTower.Sieve

open Complex RHTower

noncomputable section

/-- The unimodular exponential of a phase. -/
def phaseExp (φ : ℝ) : ℂ := Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I)

theorem phaseExp_mul_conj (φ ψ : ℝ) :
    phaseExp φ * (starRingEnd ℂ) (phaseExp ψ) = phaseExp (φ - ψ) := by
  rw [phaseExp, phaseExp, phaseExp, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem curvedSum_eq_sum_phaseExp (φ : ℝ → ℝ) (A B : ℕ) :
    curvedSum φ A B = ∑ d ∈ Finset.Ico A B, phaseExp (φ d) := rfl

/-- **The correlation sum is a difference-phase sum.** -/
theorem sum_correlation_eq (T r : ℝ) (m₁ m₂ A B : ℕ) :
    (∑ d ∈ Finset.Ico A B,
        phaseExp (nearDiagonalPhase T r ((m₁ : ℝ) * (d : ℝ)))
          * (starRingEnd ℂ) (phaseExp (nearDiagonalPhase T r ((m₂ : ℝ) * (d : ℝ)))))
      = curvedSum (diffPhase T (r / m₁) (r / m₂)) A B := by
  rw [curvedSum_eq_sum_phaseExp]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [phaseExp_mul_conj, nearDiagonalPhase_mul T r (m₁ : ℝ) (d : ℝ),
    nearDiagonalPhase_mul T r (m₂ : ℝ) (d : ℝ), diffPhase]

/-- **The off-diagonal correlation bound.** -/
theorem norm_sum_correlation_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {m₁ m₂ A B : ℕ}
    (hm₁ : 1 ≤ m₁) (hm : m₁ < m₂) (hA : 1 ≤ A)
    (h4 : 4 * (r / m₁) ≤ (A : ℝ))
    (hlam : curvedLambda (T * (r / m₁ - r / m₂)) (A : ℝ) ≤ 1) :
    ‖∑ d ∈ Finset.Ico A B,
        phaseExp (nearDiagonalPhase T r ((m₁ : ℝ) * (d : ℝ)))
          * (starRingEnd ℂ) (phaseExp (nearDiagonalPhase T r ((m₂ : ℝ) * (d : ℝ))))‖
      ≤ 2500 * Real.sqrt (T * (r / m₁ - r / m₂) / (36 * Real.pi * A))
        + 22 * Real.sqrt (36 * Real.pi / (T * (r / m₁ - r / m₂)))
            * Real.sqrt (((B : ℝ)) ^ 3) := by
  have hm₁0 : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁
  have hm₂0 : (0 : ℝ) < (m₂ : ℝ) := by
    have : 1 ≤ m₂ := by omega
    exact_mod_cast this
  have hlt : (m₁ : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm
  have hs₂0 : (0 : ℝ) ≤ r / m₂ := by positivity
  have hslt : r / m₂ < r / m₁ := by
    rw [div_lt_div_iff₀ hm₂0 hm₁0]
    nlinarith [hr, hlt]
  rw [sum_correlation_eq]
  exact norm_curvedSum_le_final (curvedPhase_diffPhase hT hs₂0 hslt) A B hA h4 hlam

end

end RHTower.Sieve
