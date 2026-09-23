import GaloisForLFunctions.RHTower.LevinsonDetectorZeroBudget
import GaloisForLFunctions.RHTower.LevinsonWindowEdgeUnconditional

/-!
# Levinson's window count from a mollified mean square

This is the junction of the two halves of Levinson's method as they exist in this development.

* `exists_levinson_window_edge_bound_unconditional` reduces the sign-change count of Hardy's `Z`
  on a window — hence the odd-fibre count — to the zero mass of the entire detector inside
  `[½,4] × [T₁,T₂]`, with every other edge estimated.
* `levinsonGEntire_zeroMass_le_of_meanSquare` bounds that zero mass by Littlewood's identity for
  `G♯·Ψ` on the wider rectangle `[σ₀,4] × [T₁,T₂]`, in terms of the mean square of `G♯·Ψ` on the
  Levinson abscissa.

Composing them leaves exactly one analytic input: the mollified mean square.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- The Littlewood boundary budget of the mollified detector on `[σ₀,4] × [T₁,T₂]`, normalized by
the horizontal weight `½ − σ₀` carried by each counted zero. -/
def levinsonMollifiedBudget (lam : ℂ) (Ψ : ℂ → ℂ) (σ₀ T₁ T₂ Msq A : ℝ) : ℝ :=
  ((T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) - (T₂ - T₁) * Real.log A
      + (4 - σ₀) * (∫ t in T₁..T₂,
          (logDeriv (fun z => levinsonGEntire lam z * Ψ z)
            (((4 : ℝ) : ℂ) + (t : ℂ) * I)).re)
      + (∫ x in σ₀..(4 : ℝ), (x - σ₀) *
          (logDeriv (fun z => levinsonGEntire lam z * Ψ z)
            ((x : ℂ) + (T₁ : ℂ) * I)).im)
      - ∫ x in σ₀..(4 : ℝ), (x - σ₀) *
          (logDeriv (fun z => levinsonGEntire lam z * Ψ z)
            ((x : ℂ) + (T₂ : ℂ) * I)).im) / (1 / 2 - σ₀)

/-- **Levinson's window count, with the detector zero mass replaced by a mollified mean square.**
Everything except the mean square, the far-right lower bound and the two remaining boundary
integrals is unconditional. -/
theorem le_xiOddFiberCount_of_mollified_meanSquare :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, lam < 0 → |lam| ≤ 1 →
      ∀ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ Set.univ → (∃ z : ℂ, Ψ z ≠ 0) →
      ∀ σ₀ T₁ T₂ Msq A : ℝ, σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
      (∀ x ∈ uIcc σ₀ (4 : ℝ),
        levinsonGEntire (lam : ℂ) ((x : ℂ) + (T₁ : ℂ) * I)
          * Ψ ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
      (∀ x ∈ uIcc σ₀ (4 : ℝ),
        levinsonGEntire (lam : ℂ) ((x : ℂ) + (T₂ : ℂ) * I)
          * Ψ ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      (∀ t ∈ uIcc T₁ T₂,
        levinsonGEntire (lam : ℂ) (((4 : ℝ) : ℂ) + (t : ℂ) * I)
          * Ψ (((4 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0) →
      0 < A →
      (∀ t ∈ uIcc T₁ T₂,
        A ≤ ‖levinsonGEntire (lam : ℂ) (((4 : ℝ) : ℂ) + (t : ℂ) * I)
              * Ψ (((4 : ℝ) : ℂ) + (t : ℂ) * I)‖) →
      (∫ t in T₁..T₂,
        ‖levinsonGEntire (lam : ℂ) ((σ₀ : ℂ) + (t : ℂ) * I)
          * Ψ ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) ≤ Msq →
      ∀ n : ℕ,
        ((n : ℝ) + 2) * Real.pi + Real.pi + (T₂ - T₁) * (6 / T₁ ^ (2 : ℕ))
            + c * Real.log T₁ + c * Real.log T₂
            + levinsonMollifiedBudget (lam : ℂ) Ψ σ₀ T₁ T₂ Msq A
          ≤ gammaHardyTheta T₂ - gammaHardyTheta T₁ →
        n ≤ xiOddFiberCount T₂ := by
  obtain ⟨c, hc, hwin⟩ := exists_levinson_window_edge_bound_unconditional
  refine ⟨c, hc, ?_⟩
  intro lam hlam0 hlam Ψ hΨ hΨne σ₀ T₁ T₂ Msq A hσ₀ h20 hT hbot htop hrightne hA hAle hMsq n hn
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_lt hlam0
  have hσ₀4 : σ₀ < (4 : ℝ) := by linarith
  have hwidth : (0 : ℝ) < 1 / 2 - σ₀ := by linarith
  have hsub : Set.Icc (1 / 2 : ℝ) 4 ⊆ uIcc σ₀ (4 : ℝ) := by
    rw [uIcc_of_le hσ₀4.le]
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  have hbotG : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 4,
      levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Ne, ← levinsonGEntire_eq_zero_iff ((lam : ℝ) : ℂ) (hne1 x T₁ h20)]
    intro h0
    exact hbot x (hsub hx) (by simp [h0])
  have htopG : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 4,
      levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Ne, ← levinsonGEntire_eq_zero_iff ((lam : ℝ) : ℂ) (hne1 x T₂ (by linarith))]
    intro h0
    exact htop x (hsub hx) (by simp [h0])
  refine hwin lam hlam0 hlam T₁ T₂ h20 hT hbotG htopG n ?_
  intro Z hZ
  have hbudget := levinsonGEntire_zeroMass_le_of_meanSquare (lam := ((lam : ℝ) : ℂ))
    hlamC hΨ hΨne hσ₀ hT hbot htop hrightne hA hAle hMsq Z hZ
  have hmass : 2 * Real.pi *
      (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire ((lam : ℝ) : ℂ)) w).toNat : ℝ))
      ≤ levinsonMollifiedBudget ((lam : ℝ) : ℂ) Ψ σ₀ T₁ T₂ Msq A := by
    rw [levinsonMollifiedBudget, le_div_iff₀ hwidth]
    nlinarith [hbudget]
  linarith [hn, hmass]

end

end RHTower
