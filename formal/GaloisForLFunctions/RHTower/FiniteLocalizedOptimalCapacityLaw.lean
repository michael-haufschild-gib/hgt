import GaloisForLFunctions.RHTower.FiniteQuantumExpectationSectorOptimalRateDistortionLaw
import GaloisForLFunctions.RHTower.FiniteLocalizedSpectralSupportRecurrenceLaw

/-!
# Optimal capacity of a localized finite spectral packet

For a normalized nonnegative finite spectral packet, choose a nonempty
effective support `S` whose omitted probability tail is at most `α`.
The complete graph on `S`, with every outside sector isolated, is feasible
at scalar deviation

`4α + 4π/(Q+1)`.

Its exact sector phase capacity is `|S|-1`.  Since optimal capacity is the
least capacity among every feasible sector graph, the localized support
gives the canonical upper bound

`optimalCapacity ≤ |S|-1`.

The proof explicitly identifies the basis-free sector masses with the
earlier `Fin d` coefficient masses; no change of distortion functional is
hidden in the comparison.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- On `Fin d`, the basis-free sector union mass is exactly the original
ordered-index union mass. -/
theorem finiteSectorUnionCoefficientMass_eq_finiteUnionCoefficientMass
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ)
    (i j : Fin d) :
    finiteQuantumExpectationSectorUnionCoefficientMass
        lam coeff i j =
      finiteExpectationUnionCoefficientMass lam coeff i j := by
  rfl

/-- On `Fin d`, selected directed sector mass equals selected directed
index mass. -/
theorem finiteSectorSelectedDirectedMass_eq_finiteSelectedDirectedMass
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ) :
    finiteQuantumExpectationSectorSelectedDirectedMass
        G lam coeff =
      finiteExpectationSelectedDirectedMass G lam coeff := by
  classical
  unfold finiteQuantumExpectationSectorSelectedDirectedMass
    finiteExpectationSelectedDirectedMass
  rfl

/-- On `Fin d`, omitted directed sector mass equals omitted directed index
mass.  This is a propositional equality because the two definitions use
different decidable-equality instances. -/
theorem finiteSectorOmittedDirectedMass_eq_finiteOmittedDirectedMass
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ) :
    finiteQuantumExpectationSectorOmittedDirectedMass
        G lam coeff =
      finiteExpectationOmittedDirectedMass G lam coeff := by
  classical
  unfold finiteQuantumExpectationSectorOmittedDirectedMass
    finiteExpectationOmittedDirectedMass
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases homit : i ≠ j ∧ ¬ G.Adj i j
  · simp [homit,
      finiteSectorUnionCoefficientMass_eq_finiteUnionCoefficientMass]
  · simp [homit]

/-- Exact sector capacity of the localized support graph. -/
theorem finiteLocalizedSpectralSupport_sectorGraphCapacity
    {d : ℕ} (S : Finset (Fin d)) (hS : S.Nonempty) :
    finiteQuantumExpectationSectorGraphCapacity
        (finiteLocalizedSpectralSupportGraph S) =
      S.card - 1 := by
  unfold finiteQuantumExpectationSectorGraphCapacity
  simpa only [Fintype.card_fin] using
    finiteLocalizedSpectralSupportGraph_rank S hS

/--
The canonical localized support graph is feasible at target deviation
`4α + 4π/(Q+1)`.
-/
theorem finiteLocalizedSpectralSupport_sectorBudget_le
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d))
    (α : ℝ) (htail : finiteLocalizedSubsetTail p S ≤ α)
    (Q : ℕ) :
    finiteQuantumExpectationSectorGraphDistortionBudget
        (finiteLocalizedSpectralSupportGraph S)
        (fun _ : Unit => 1)
        (finiteLocalizedSpectralCoefficient p) Q ≤
      4 * α + 4 * Real.pi / (Q + 1 : ℝ) := by
  rw [finiteQuantumExpectationSectorGraphDistortionBudget,
    finiteSectorOmittedDirectedMass_eq_finiteOmittedDirectedMass,
    finiteSectorSelectedDirectedMass_eq_finiteSelectedDirectedMass]
  have homit :
      finiteExpectationOmittedDirectedMass
          (finiteLocalizedSpectralSupportGraph S)
          (fun _ : Unit => 1)
          (finiteLocalizedSpectralCoefficient p) ≤
        2 * α :=
    finiteLocalizedSpectral_omittedMass_le_two_alpha
      p hp hpSum S α htail
  have hselected :
      finiteExpectationSelectedDirectedMass
          (finiteLocalizedSpectralSupportGraph S)
          (fun _ : Unit => 1)
          (finiteLocalizedSpectralCoefficient p) ≤ 1 :=
    finiteLocalizedSpectral_selectedMass_le_one p hp hpSum S
  calc
    2 * finiteExpectationOmittedDirectedMass
          (finiteLocalizedSpectralSupportGraph S)
          (fun _ : Unit => 1)
          (finiteLocalizedSpectralCoefficient p) +
        2 * (2 * Real.pi / (Q + 1 : ℝ)) *
          finiteExpectationSelectedDirectedMass
            (finiteLocalizedSpectralSupportGraph S)
            (fun _ : Unit => 1)
            (finiteLocalizedSpectralCoefficient p) ≤
      2 * (2 * α) +
        2 * (2 * Real.pi / (Q + 1 : ℝ)) * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left homit (by norm_num))
        (mul_le_mul_of_nonneg_left hselected (by positivity))
    _ = 4 * α + 4 * Real.pi / (Q + 1 : ℝ) := by ring

/-- The localized target is feasible in the exact sense required by the
optimal-capacity definition. -/
theorem finiteLocalizedSpectralSupport_sectorTarget_feasible
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d))
    (α : ℝ) (htail : finiteLocalizedSubsetTail p S ≤ α)
    (Q : ℕ) :
    ∃ G : SimpleGraph (Fin d),
      finiteQuantumExpectationSectorGraphDistortionBudget
          G (fun _ : Unit => 1)
          (finiteLocalizedSpectralCoefficient p) Q ≤
        4 * α + 4 * Real.pi / (Q + 1 : ℝ) :=
  ⟨finiteLocalizedSpectralSupportGraph S,
    finiteLocalizedSpectralSupport_sectorBudget_le
      p hp hpSum S α htail Q⟩

/--
**Localized optimal-capacity law.**

At deviation scale `4α + 4π/(Q+1)`, the canonical optimal sector recurrence
capacity of the localized spectral packet is at most `|S|-1`.
-/
theorem finiteLocalizedSpectralSupport_optimalCapacity_le
    {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (S : Finset (Fin d)) (hS : S.Nonempty)
    (α : ℝ) (htail : finiteLocalizedSubsetTail p S ≤ α)
    (Q : ℕ) :
    finiteQuantumExpectationSectorOptimalCapacity
        (fun _ : Unit => 1)
        (finiteLocalizedSpectralCoefficient p) Q
        (4 * α + 4 * Real.pi / (Q + 1 : ℝ)) ≤
      S.card - 1 := by
  let G := finiteLocalizedSpectralSupportGraph S
  have hbudget :
      finiteQuantumExpectationSectorGraphDistortionBudget
          G (fun _ : Unit => 1)
          (finiteLocalizedSpectralCoefficient p) Q ≤
        4 * α + 4 * Real.pi / (Q + 1 : ℝ) := by
    exact finiteLocalizedSpectralSupport_sectorBudget_le
      p hp hpSum S α htail Q
  have hcapacity :
      finiteQuantumExpectationSectorGraphCapacity G =
        S.card - 1 :=
    finiteLocalizedSpectralSupport_sectorGraphCapacity S hS
  unfold finiteQuantumExpectationSectorOptimalCapacity
  apply Nat.sInf_le
  exact ⟨G, hbudget, hcapacity.symm⟩

end RHTower
