import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceEntropy

/-!
# Universal phase-coherence half-entropy law

Finite-torus recurrence supplies a clock `n ≤ (Q+1)^d` whose equal-weight phase centroid is nearly
unit. Hilbert centroid geometry independently converts near-unit coherence into one packet phase
with small total squared distance from all others. Joining them gives an exact entropy tradeoff:
dimension `d` costs exponent `d` in recurrence time while quadratic cluster energy decays with
resolution exponent `2`.
-/

open scoped BigOperators RealInnerProductSpace

namespace RHTower

noncomputable section

/-- **Universal phase-coherence half-entropy law.** Every finite real frequency packet admits a
positive recurrence clock, at the Dirichlet time cost `(Q+1)^d`, and a packet pivot whose total
squared phase dispersion is at most `8π² d/(Q+1)²`. -/
theorem exists_phaseClockPivot_halfEntropy_quantitative
    {d Q : ℕ} (hd : 0 < d) (ω : Fin d → ℝ) :
    ∃ n : ℕ, ∃ k : Fin d,
      0 < n ∧ n ≤ (Q + 1) ^ d ∧
        ∑ j : Fin d,
          ‖Complex.exp (Complex.I * (((n : ℝ) * ω j : ℝ) : ℂ)) -
            Complex.exp (Complex.I * (((n : ℝ) * ω k : ℝ) : ℂ))‖ ^ 2 ≤
          8 * Real.pi ^ 2 * (d : ℝ) / (Q + 1 : ℝ) ^ 2 := by
  letI : NeZero d := ⟨hd.ne'⟩
  let phase : ℕ → Fin d → ℂ := fun n i =>
    Complex.exp (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))
  let η : ℝ := (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 / 2
  obtain ⟨n, hnpos, hnQ, hcoh⟩ :=
    exists_phaseClockAmplitude_coherence_quantitative (Q := Q) hd ω
  have hphase : ∀ i, ‖phase n i‖ = 1 := by
    intro i
    rw [show phase n i = Complex.exp
      (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) by rfl, Complex.norm_exp]
    simp
  have hcoh' : 1 - η ≤ ‖equalPhaseAmplitude (phase n)‖ := by
    rw [← phaseClockAmplitude_eq_equalPhaseAmplitude ω n]
    exact hcoh
  obtain ⟨k, hk⟩ :=
    exists_phasePivot_sum_norm_sub_sq_le (phase n) hphase hcoh'
  refine ⟨n, k, hnpos, hnQ, ?_⟩
  change (∑ j : Fin d, ‖phase n j - phase n k‖ ^ 2) ≤ _
  calc
    _ ≤ 4 * η * (Fintype.card (Fin d) : ℝ) := hk
    _ = 8 * Real.pi ^ 2 * (d : ℝ) / (Q + 1 : ℝ) ^ 2 := by
      simp only [η, Fintype.card_fin]
      field_simp
      ring

end

end RHTower
