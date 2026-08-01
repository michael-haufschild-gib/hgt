import GaloisForLFunctions.RHTower.SoninCouplingErrorBudget
import GaloisForLFunctions.RHTower.SoninSurvivorEnergyCount
import GaloisForLFunctions.RHTower.SoninShellProductIdeal

/-!
# Coupling energy from an orthonormal family in the shell

The coupling is itself a relative-ideal element, hence Hilbert--Schmidt, so its energy is what the
mode count bounds from below.  Every vector of the shell is carried to within its error budget of
its dilate, and the dilate is again a unit vector because dilation is unitary.

So an orthonormal family in the shell whose members all have small band terms forces coupling energy
proportional to the family's size, discounted only by the fixed energies of the two relative-ideal
errors and by the squared shortfall from one.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The two relative-ideal errors of the budget, listed with the correction counted twice. -/
def soninCouplingIdealErrors (a b r : ℝ) (hr : 0 < r) :
    Fin 3 → (evenSubspace →L[ℂ] evenSubspace) :=
  ![evenSoninProjectionCorrection b, evenSoninProjectionCorrection b,
    (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) * evenDilationCLM r hr]

theorem isSoninPrincipalRelativeIdeal_soninCouplingIdealErrors
    (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (k : Fin 3) :
    IsSoninPrincipalRelativeIdeal (soninCouplingIdealErrors a b r hr k) := by
  fin_cases k
  · exact IsSoninPrincipalRelativeIdeal.projectionCorrection b hb
  · exact IsSoninPrincipalRelativeIdeal.projectionCorrection b hb
  · exact isSoninPrincipalRelativeIdeal_correctionDiff_comp_dilation a b r ha hb hr

/-- **Coupling energy from a shell family.**  An orthonormal family vanishing inside the inner
aperture and fixed by the outer one, with band terms below `β`, forces the coupling's
Hilbert--Schmidt energy above the family's size less the ideal errors' fixed discount. -/
theorem card_sub_le_hsNormSq_soninApertureCoupling
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (hcr : c ≤ r * a)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → evenSubspace} (he : Orthonormal ℂ e)
    (hlow : ∀ i, evenIndicatorCutoff b (e i) = 0)
    (hhigh : ∀ i, evenIndicatorCutoff c (e i) = e i)
    (β ε η : ℝ) (hε : 0 < ε) (hη : η ≤ 1) (hcomb : 3 * ε + β ≤ η)
    (hband : ∀ i, ‖(evenIndicatorCutoff b - evenIndicatorCutoff a)
          (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) (e i))‖ +
        (‖evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) (e i) -
            evenFourierCutoff b
              (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) (e i))‖ +
          ‖evenFourierCutoff a
            (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) (e i))‖) +
        ‖evenFourierCutoff b (e i)‖ ≤ β) :
    ((Fintype.card ι : ℝ) -
        ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b r⁻¹
          (inv_pos.mpr (zero_lt_one.trans hr)) k) / ε ^ 2) * (1 - η) ^ 2 ≤
      hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  classical
  set D := evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) with hD
  set T := soninCouplingIdealErrors a b r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) with hT
  have hZ : IsHilbertSchmidt (evenSoninApertureSuccessiveLayerTransition a b c r hr) :=
    isHilbertSchmidt_of_isSoninPrincipalRelativeIdeal
      (evenSoninApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
        ha hb hc hab hbc hr hcr)
  have hTideal : ∀ k, IsSoninPrincipalRelativeIdeal (T k) := fun k =>
    isSoninPrincipalRelativeIdeal_soninCouplingIdealErrors a b r⁻¹ ha hb
      (inv_pos.mpr (zero_lt_one.trans hr)) k
  have hu : ∀ i, ‖D (e i)‖ = 1 := by
    intro i
    rw [hD, norm_evenDilationCLM_apply]
    exact he.1 i
  have hest : ∀ i, ‖evenSoninApertureSuccessiveLayerTransition a b c r hr (e i) - D (e i)‖ ≤
      (∑ k : Fin 3, ‖T k (e i)‖) + β := by
    intro i
    have hbudget := norm_soninApertureCoupling_sub_dilate_le_budget hab hbc hr hcr
      (hlow i) (hhigh i)
    have hsum : (∑ k : Fin 3, ‖T k (e i)‖) =
        ‖evenSoninProjectionCorrection b (e i)‖ + ‖evenSoninProjectionCorrection b (e i)‖ +
          ‖((evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) * D) (e i)‖ := by
      simp [hT, soninCouplingIdealErrors, Fin.sum_univ_three, hD]
    rw [hsum]
    linarith [hbudget, hband i]
  exact card_sub_le_hsNormSq_of_ideal_errors hZ T hTideal he (fun i => D (e i)) hu
    β ε η hε hη (by simpa using hcomb) hest

end RHTower
