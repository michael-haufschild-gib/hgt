import GaloisForLFunctions.RHTower.WeilLagFunctionProgressionBaire
import GaloisForLFunctions.RHTower.AsymptoticAbscissaLawProducers

/-!
# One lag progression decides RH exactly up to the zeros approaching the line

For a spacing `ℓ` the progression `m ↦ Φ(mℓ)`, `m ∈ ℕ`, samples the Weil lag function
`Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))` on `ℓℕ`.

* **Attainment** (`exists_lag_progression_gt_of_attainedTop_of_ne`).  If the maximal real part
  `β₀ > ½` of the zeros is attained, every progression with `ℓ ≠ 0` is unbounded above.
  Simultaneous Dirichlet approximation aligns the phases of the top level, whose weights
  `1/(ρ(1−ρ))` have positive real parts, and the lower levels are dominated.  No non-resonance
  condition on `ℓ` is needed.
* **AAL producer** (`asymptoticAbscissaLaw_of_progression_bddAbove`).  One progression bounded
  above excludes an attained off-line top, hence gives the asymptotic abscissa law.
* **Split** (`riemannHypothesis_iff_zerosApproachLine_and_exists_progression_bddAbove`).
  RH ⟺ (the zeros approach the line) ∧ (some progression with `ℓ ≠ 0` is bounded above).

With the Baire criterion (`riemannHypothesis_iff_not_isMeagre_bddAbove_progression`), RH holds iff
the set of spacings with a bounded progression is not meagre.  Equivalently, that set contains a
nonzero spacing and the zeros approach the line.  The gap between one good spacing and a
non-meagre set of them is exactly the large-height statement that the zeros approach the line.
-/

namespace RHTower

noncomputable section

open BacklundConverse

/-- **Every nonzero spacing detects an attained off-line top.** -/
theorem exists_lag_progression_gt_of_attainedTop_of_ne {β₀ : ℝ} (hβ : 1 / 2 < β₀)
    (h : AttainedTop β₀) {ℓ : ℝ} (hℓ : ℓ ≠ 0) (M : ℝ) :
    ∃ m : ℕ, M < weilLagFunctionReal (m * ℓ) := by
  rcases hℓ.lt_or_gt with hneg | hpos
  · obtain ⟨m, -, hm⟩ := exists_lag_progression_gt_of_attainedTop hβ h (neg_pos.mpr hneg) M
    refine ⟨m, ?_⟩
    rw [← weilLagFunctionReal_neg, ← mul_neg]
    exact hm
  · obtain ⟨m, -, hm⟩ := exists_lag_progression_gt_of_attainedTop hβ h hpos M
    exact ⟨m, hm⟩

/-- **One progression bounded above excludes an attained off-line top.** -/
theorem not_exists_attainedTop_of_progression_bddAbove {ℓ : ℝ} (hℓ : ℓ ≠ 0) {M : ℝ}
    (hM : ∀ m : ℕ, weilLagFunctionReal (m * ℓ) ≤ M) :
    ¬ ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀ := by
  rintro ⟨β₀, hβ, h⟩
  obtain ⟨m, hm⟩ := exists_lag_progression_gt_of_attainedTop_of_ne hβ h hℓ M
  exact absurd (hM m) (not_le.mpr hm)

/-- **One progression bounded above gives the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_progression_bddAbove {ℓ : ℝ} (hℓ : ℓ ≠ 0) {M : ℝ}
    (hM : ∀ m : ℕ, weilLagFunctionReal (m * ℓ) ≤ M) : AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_not_attainedTop (not_exists_attainedTop_of_progression_bddAbove hℓ hM)

/-- **RH splits into zeros approaching the line and one lag progression bounded above.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_exists_progression_bddAbove :
    RiemannHypothesis ↔ ZerosApproachLine ∧
      ∃ ℓ : ℝ, ℓ ≠ 0 ∧ ∃ M : ℝ, ∀ m : ℕ, weilLagFunctionReal (m * ℓ) ≤ M := by
  constructor
  · intro hRH
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH, 1, one_ne_zero, poleSharpConstant,
      fun m => weilLagFunctionReal_le_poleSharpConstant hRH _⟩
  · rintro ⟨hZ, ℓ, hℓ, M, hM⟩
    by_contra hRH
    exact not_exists_attainedTop_of_progression_bddAbove hℓ hM
      (exists_attainedTop_of_zerosApproachLine hZ hRH)

end

end RHTower
