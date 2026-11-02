import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowDirichletAlgebra

/-!
# The transfer across a stage

The **stage datum** of level `N` is Weil's form of the weight `Λ·1_{n ≤ N}`:
`Q_N(H) = M_N(H) + ½⟨c,H⟩² − ½⟨s,H⟩²` (`stageForm`), with `M_N` the Markov form of level `N`. On a
window of level `N` it is Weil's form (CWS locality). Crossing the stage `N + 1` changes it by one
autocorrelation (`markovForm_succ`):

`M_{N+1}(H) = M_N(H) − 2w_{N+1}∫H(u)H(u + ℓ)`, `ℓ = log(N+1)`, `w_n = Λ(n)/√n`.

On a window of level `N + 1` this is the **transfer identity** (`weilQuad_eq_stageForm_add_fold`):

`Q(H) = Q_N(H) + w_{N+1}(fold energy of T_{N+1} − ∫ m_ℓ H²)`,

where `m_ℓ = 1_{[−A,−ℓ]} + 1_{[ℓ−A,0]}` marks the two ends of the new fold. Crossing a stage adds exactly
one fold, and its only cost is its end mass:

* **End-mass transfer** (`weilQuad_ge_stageForm_sub_endMass`): `Q(H) ≥ Q_N(H) − w_{N+1}∫ m_ℓ H²`.
* **Transfer criterion** (`weilQuad_nonneg_of_endCoercive`): if the previous stage datum pays the
  end mass of the new fold, `Q_N(H) ≥ w_{N+1}∫ m_ℓ H²`, then `Q(H) ≥ 0`.

The ends have length `A − log(N+1)`, which is `< log((N+2)/(N+1))` on the stage: positivity crosses a
stage as soon as the previous datum is coercive on two short collars at the ends of the window, with
constant `Λ(N+1)/√(N+1)`. At composite stages `w_{N+1} = 0` and positivity transfers for free
(`weilQuad_eq_stageForm_of_not_primePow`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

variable {A : ℝ} {H : ℝ → ℝ}

/-- The **stage datum** of level `N`: Weil's form of the weight truncated at `N`. -/
def stageForm (N : ℕ) (H : ℝ → ℝ) : ℝ :=
  markovForm N H + (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2)

/-- `∫(H − H(·+ℓ))² = 2∫H² − 2∫H(u)H(u + ℓ)`. -/
theorem integral_jump_sq_eq (hc : Continuous H) (hcs : HasCompactSupport H) (ℓ : ℝ) :
    ∫ u, (H u - H (u + ℓ)) ^ 2 = 2 * (∫ u, H u ^ 2) - 2 * ∫ u, H u * H (u + ℓ) := by
  have iH := integrable_sq hc hcs
  have iHs : Integrable fun u => H (u + ℓ) ^ 2 :=
    integrable_sq (hc.comp (continuous_add_const _)) (hasCompactSupport_comp_add hcs _)
  have iP := integrable_mul_shift hc hcs ℓ
  have hexp : ∀ u, (H u - H (u + ℓ)) ^ 2 = H u ^ 2 + H (u + ℓ) ^ 2 - 2 * (H u * H (u + ℓ)) :=
    fun u => by ring
  simp_rw [hexp]
  rw [integral_add_sub_two_mul iH iHs iP, integral_add_right_eq_self (fun u => H u ^ 2) ℓ]
  ring

/-- **Crossing a stage changes the Markov form by one autocorrelation**:
`M_{N+1}(H) = M_N(H) − 2w_{N+1}∫H(u)H(u + log(N+1))` for `N ≥ 1`. -/
theorem markovForm_succ (hc : Continuous H) (hcs : HasCompactSupport H) {N : ℕ} (hN : 1 ≤ N) :
    markovForm (N + 1) H = markovForm N H -
      2 * primeJumpWeight (N + 1) * ∫ u, H u * H (u + Real.log (N + 1 : ℕ)) := by
  rw [markovForm, markovForm, creationPotential, creationPotential, primeJump, primeJump,
    Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1), Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1),
    integral_jump_sq_eq hc hcs]
  ring

/-- **The transfer identity**: on a window of level `N + 1`,
`Q(H) = Q_N(H) + w_{N+1}(fold energy − ∫ m_ℓ H²)`, `ℓ = log(N+1)`. -/
theorem weilQuad_eq_stageForm_add_fold (hH : IsWindowTest A H) {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1) :
    weilQuad H = stageForm N H + primeJumpWeight (N + 1) *
      (foldEnergy A (Real.log (N + 1 : ℕ)) H -
        ∫ u, inWindowCount A (Real.log (N + 1 : ℕ)) u * H u ^ 2) := by
  have hfold := jump_sub_creation_eq_fold hH.continuous hH.hasCompactSupport hH.vanish
    (ℓ := Real.log (N + 1 : ℕ))
  rw [integral_jump_sq_eq hH.continuous hH.hasCompactSupport] at hfold
  rw [weilQuad_eq_markovForm_windowLevel hH, hA,
    markovForm_succ hH.continuous hH.hasCompactSupport hN, stageForm]
  linear_combination primeJumpWeight (N + 1) * hfold

/-- The end mass bounds the autocorrelation: `∫H(u)H(u + ℓ) ≤ ½∫ m_ℓ H²`. -/
theorem autocorr_le_half_endMass (hH : IsWindowTest A H) (ℓ : ℝ) :
    ∫ u, H u * H (u + ℓ) ≤ (∫ u, inWindowCount A ℓ u * H u ^ 2) / 2 := by
  have hfold := jump_sub_creation_eq_fold hH.continuous hH.hasCompactSupport hH.vanish (ℓ := ℓ)
  rw [integral_jump_sq_eq hH.continuous hH.hasCompactSupport] at hfold
  have := foldEnergy_nonneg A ℓ H
  linarith

/-- **End-mass transfer**: on a window of level `N + 1`, `Q(H) ≥ Q_N(H) − w_{N+1}∫ m_ℓ H²`. -/
theorem weilQuad_ge_stageForm_sub_endMass (hH : IsWindowTest A H) {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1) :
    stageForm N H - primeJumpWeight (N + 1) *
        ∫ u, inWindowCount A (Real.log (N + 1 : ℕ)) u * H u ^ 2 ≤ weilQuad H := by
  rw [weilQuad_eq_stageForm_add_fold hH hN hA]
  have := foldEnergy_nonneg A (Real.log (N + 1 : ℕ)) H
  have := primeJumpWeight_nonneg (N + 1)
  nlinarith

/-- **The transfer criterion**: if the previous stage datum pays the end mass of the new fold, the
window of the next stage is positive. -/
theorem weilQuad_nonneg_of_endCoercive (hH : IsWindowTest A H) {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1)
    (hend : primeJumpWeight (N + 1) * ∫ u, inWindowCount A (Real.log (N + 1 : ℕ)) u * H u ^ 2 ≤
      stageForm N H) : 0 ≤ weilQuad H := by
  have := weilQuad_ge_stageForm_sub_endMass hH hN hA
  linarith

/-- **Composite stages are free**: if `N + 1` is not a prime power, crossing its stage does not
change Weil's form. -/
theorem weilQuad_eq_stageForm_of_not_primePow (hH : IsWindowTest A H) {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1) (hpp : ¬ IsPrimePow (N + 1)) : weilQuad H = stageForm N H := by
  rw [weilQuad_eq_stageForm_add_fold hH hN hA, primeJumpWeight,
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  simp

end GaloisForLFunctions.WindowTowerOfSpecZ
