/-
# The bounded, collision-good coefficient set

Intersecting the explicit Gaussian box with the Markov complement of the quenched collision law
leaves at least half the Gaussian coefficient mass.  No measurability of the collision functional is
needed: subadditivity of the measure on the two exceptional sets already forces the bound, because
the total mass of the union of a set and its complement is one.

Main results:
* `gaussianGoodSet` — **`(5)`**: the bounded, collision-good coefficient set.
* `measureReal_gaussianGoodSet_compl_le` — **`(12)`--`(13)`**: its complement has mass at most `1/2`.
* `half_le_measureReal_gaussianGoodSet` — **`(5)`**: it has Gaussian mass at least `1/2`.
-/
import GaloisForLFunctions.HTGeometry.PauliEnsembleSimpleSpectrum
import GaloisForLFunctions.HTGeometry.GaussianBoxMass

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {n q : ℕ}

/-- The law of one Gaussian coefficient. -/
theorem map_coordinate_centredProductGaussian {ι : Type*} [Fintype ι] (a : ι) :
    (centredProductGaussian ι 1).map (fun J : ι → ℝ => J a) = gaussianReal 0 1 := by
  rw [centredProductGaussian]
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) a).map_eq

/-- **`(5)`.**  The bounded, collision-good coefficient set. -/
def gaussianGoodSet (w : (Fin n → Option (Fin 3)) → ℝ) (B L : ℝ) :
    Set ((Fin n → Option (Fin 3)) → ℝ) :=
  {J | ∀ a, |J a| ≤ B} ∩
    {J | spectralCollision
        (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
        (zeroProductState (Fin n)) < L * (2 / 3 : ℝ) ^ n}

/-- **`(12)`--`(13)`.**  Its complement carries at most half the Gaussian mass. -/
theorem measureReal_gaussianGoodSet_compl_le (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hwsupp : SupportInvariantWeight w)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0)
    (hcard : 0 < Fintype.card (Fin n → Option (Fin 3)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : 2 * Real.log (8 * Fintype.card (Fin n → Option (Fin 3))) ≤ B ^ (2 : ℕ)) :
    (centredProductGaussian (Fin n → Option (Fin 3)) 1).real ((gaussianGoodSet w B 4)ᶜ)
      ≤ 1 / 2 := by
  classical
  have hbox := measureReal_box_compl_le_quarter
    (p := centredProductGaussian (Fin n → Option (Fin 3)) 1) hcard
    (fun a J => J a) (fun a => measurable_pi_apply a)
    (fun a => map_coordinate_centredProductGaussian a) hB0 hB
  have hcoll := measureReal_collision_pauliEnsemble_zeroProductState_ge_le (q := q) w hq hwsupp hw
    (v := 1) (by norm_num) hwne (L := (4 : ℝ)) (by norm_num)
  have hsub : (gaussianGoodSet w B 4)ᶜ ⊆
      ({J : (Fin n → Option (Fin 3)) → ℝ | ∀ a, |J a| ≤ B}ᶜ) ∪
        {J | (4 : ℝ) * (2 / 3 : ℝ) ^ n ≤ spectralCollision
          (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
          (zeroProductState (Fin n))} := by
    intro J hJ
    rw [gaussianGoodSet, Set.mem_compl_iff, Set.mem_inter_iff] at hJ
    push Not at hJ
    by_cases hbox' : ∀ a, |J a| ≤ B
    · right
      have hc := hJ hbox'
      simp only [Set.mem_setOf_eq, not_lt] at hc
      exact hc
    · left
      exact hbox'
  calc (centredProductGaussian (Fin n → Option (Fin 3)) 1).real ((gaussianGoodSet w B 4)ᶜ)
      ≤ (centredProductGaussian (Fin n → Option (Fin 3)) 1).real
          (({J : (Fin n → Option (Fin 3)) → ℝ | ∀ a, |J a| ≤ B}ᶜ) ∪
            {J | (4 : ℝ) * (2 / 3 : ℝ) ^ n ≤ spectralCollision
              (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
              (zeroProductState (Fin n))}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (centredProductGaussian (Fin n → Option (Fin 3)) 1).real
          ({J : (Fin n → Option (Fin 3)) → ℝ | ∀ a, |J a| ≤ B}ᶜ)
        + (centredProductGaussian (Fin n → Option (Fin 3)) 1).real
          {J | (4 : ℝ) * (2 / 3 : ℝ) ^ n ≤ spectralCollision
            (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
            (zeroProductState (Fin n))} := measureReal_union_le _ _
    _ ≤ 1 / 4 + 1 / 4 := by
        have h2 : (1 : ℝ) / 4 = 1 / (4 : ℝ) := rfl
        exact add_le_add hbox (by simpa using hcoll)
    _ = 1 / 2 := by norm_num

/-- **`(5)`.**  The bounded, collision-good coefficient set carries at least half the Gaussian
mass.  Subadditivity replaces measurability of the collision functional. -/
theorem half_le_measureReal_gaussianGoodSet (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hwsupp : SupportInvariantWeight w)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0)
    (hcard : 0 < Fintype.card (Fin n → Option (Fin 3)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : 2 * Real.log (8 * Fintype.card (Fin n → Option (Fin 3))) ≤ B ^ (2 : ℕ)) :
    1 / 2 ≤ (centredProductGaussian (Fin n → Option (Fin 3)) 1).real (gaussianGoodSet w B 4) := by
  have hcompl := measureReal_gaussianGoodSet_compl_le w hq hwsupp hw hwne hcard hB0 hB
  have htotal : (1 : ℝ) ≤
      (centredProductGaussian (Fin n → Option (Fin 3)) 1).real (gaussianGoodSet w B 4)
        + (centredProductGaussian (Fin n → Option (Fin 3)) 1).real ((gaussianGoodSet w B 4)ᶜ) := by
    have hunion : (Set.univ : Set ((Fin n → Option (Fin 3)) → ℝ))
        = gaussianGoodSet w B 4 ∪ (gaussianGoodSet w B 4)ᶜ := (Set.union_compl_self _).symm
    have hle := measureReal_union_le (μ := centredProductGaussian (Fin n → Option (Fin 3)) 1)
      (gaussianGoodSet w B 4) ((gaussianGoodSet w B 4)ᶜ)
    have huniv : (centredProductGaussian (Fin n → Option (Fin 3)) 1).real Set.univ = 1 := by
      simp [measureReal_def]
    rw [hunion] at huniv
    linarith [hle, huniv]
  linarith

end

end GaloisForLFunctions.HTGeometry
