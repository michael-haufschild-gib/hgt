import GaloisForLFunctions.InfiniteRankWeilTheory.IsolatedTopExcursionDensity
import GaloisForLFunctions.InfiniteRankWeilTheory.TheTowersOfZeta

/-!
# The coefficient density forced by failure of the zeta abscissa law

Failure of AAL produces an actual isolated top layer. At every positive sampling base, its
merged lag coefficients force a quantitative lower density of excursions in every sufficiently
long window. All summability and visibility inputs are theorems about the actual zeta zeros.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- If the zeta AAL fails, every merged coefficient of its isolated top gives its own lower
density bound for sampled Weil-lag excursions. The window length is uniform in its starting
point, and every exponent below the top is allowed. -/
theorem not_asymptoticAbscissaLaw_implies_coefficient_density :
    ¬ RHTower.AsymptoticAbscissaLaw →
    ∃ (F : Finset RHTower.XiZeroCopy) (Θ Θ₂ : ℝ),
      F.Nonempty ∧ 1 / 2 < Θ ∧ Θ₂ < Θ ∧
      (∀ q ∈ F, (zetaConfig q).re = Θ) ∧
      (∀ q ∉ F, (zetaConfig q).re ≤ Θ₂) ∧
      (∀ ℓ : ℝ, ∀ j ∈ F,
        0 < ‖∑ i ∈ F with frobTower ℓ zetaConfig i = frobTower ℓ zetaConfig j, lagWeight i‖) ∧
      ∀ ℓ : ℝ, 0 < ℓ → ∀ j ∈ F, ∀ d : ℝ,
        d * mergedTopMass F (frobTower ℓ zetaConfig) lagWeight <
          ‖∑ i ∈ F with frobTower ℓ zetaConfig i = frobTower ℓ zetaConfig j, lagWeight i‖ →
        ∀ a : ℝ, a < Θ - 1 / 2 → ∀ C : ℝ, 0 ≤ C →
        ∃ N₀ : ℕ, ∀ M N : ℕ, N₀ ≤ N →
          d * N ≤ (((range N).filter fun n =>
            C * Real.exp (a * (M + n : ℕ) * ℓ) <
              ‖RHTower.weilLagFunction ((M + n : ℕ) * ℓ)‖).card : ℝ) := by
  classical
  intro hnot
  rw [asymptoticAbscissaLaw_zetaConfig_iff,
    not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨F, Θ, Θ₂, hFne, hΘ, hΘ₂, hF, hrest⟩ := hnot
  refine ⟨F, Θ, Θ₂, hFne, hΘ, hΘ₂, hF, hrest,
    fun ℓ j hj => norm_pos_iff.mpr (mergedLagWeight_ne_zero ℓ F hj), ?_⟩
  intro ℓ hℓ j hj d hd a ha C hC
  obtain ⟨htop, hlow, hlt⟩ := frobTower_isolatedTop hℓ hΘ₂ hF hrest
  have hρR : Real.exp (a * ℓ) < Real.exp (ℓ * (Θ - 1 / 2)) :=
    Real.exp_lt_exp.mpr (by nlinarith only [mul_pos (sub_pos.mpr ha) hℓ])
  obtain ⟨N₀, hN₀⟩ := isolatedTop_uniform_excursion_density (frobTower ℓ zetaConfig)
    lagWeight summable_norm_lagWeight F (Real.exp_pos _) (Real.exp_pos _).le hlt
    hlow htop (Real.exp_pos _).le hρR hC hj hd
  refine ⟨N₀, fun M N hN => ?_⟩
  have heq (n : ℕ) : Real.exp (a * (M + n : ℕ) * ℓ) =
      Real.exp (a * ℓ) ^ (M + n) := by
    rw [show a * (M + n : ℕ) * ℓ = (M + n : ℕ) * (a * ℓ) by ring,
      Real.exp_nat_mul]
  simpa only [heq, weilLagFunction_mul_eq_levelSum] using hN₀ M N hN

#print axioms not_asymptoticAbscissaLaw_implies_coefficient_density

end GaloisForLFunctions.InfiniteRankWeilTheory
