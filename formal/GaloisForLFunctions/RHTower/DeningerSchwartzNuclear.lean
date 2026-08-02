import GaloisForLFunctions.HTGeometry.HermiteShiftedCoefficients
import GaloisForLFunctions.RHTower.DeningerNuclearCompletedInvariance

/-!
# The Schwartz space of the line is nuclear

The oscillator seminorms `Qₘ(f) = ‖Kᵐf‖₂` present the topology of `𝒮(ℝ)`, and in that
presentation the Hermite system diagonalizes everything: the coefficient functionals are bounded
by `(4π(j+1))^{-m}Qₘ`, the normalized Hermite functions have `Qₖ`-norm `(4π(j+1))ᵏ`, and the
Hermite expansion converges in every `Qₖ`.  Raising the dominating seminorm by two orders makes the
product of the two norms summable, so the comparison map of `Qₖ` by `Q_{k+2}` is the sum of a
summable family of rank-one maps: it is nuclear.

Because the oscillator family and the family of finite suprema of Schwartz seminorms dominate each
other, nuclearity transfers to the Schwartz presentation.

* `deningerHermiteCoeffQuotient` : the coefficient functional on an oscillator quotient.
* `hasSum_hermiteExpansion_shiftedQuotient` : the expansion converges in every oscillator quotient.
* `deningerIsNuclearSpace_shiftedSeminormFamily` : **the oscillator family is nuclear.**
* `deningerIsNuclearSpaceC_schwartzSup` : **the Schwartz space of the line is a nuclear space.**
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The oscillator map into `L²` -/

/-- The `m`-th oscillator map of the Schwartz space into `L²`. -/
def deningerOscL2CLM (m : ℕ) : 𝓢(ℝ, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).comp (shiftedPowCLM m)

theorem deningerOscL2CLM_apply (m : ℕ) (f : 𝓢(ℝ, ℂ)) :
    deningerOscL2CLM m f = ((shiftedNumberCLM^[m]) f).toLp 2 (volume : Measure ℝ) := by
  show SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ) (shiftedPowCLM m f) = _
  rw [SchwartzMap.toLpCLM_apply, shiftedPowCLM_apply]

theorem norm_deningerOscL2CLM (m : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ‖deningerOscL2CLM m f‖ = shiftedSeminorm m f := by
  rw [deningerOscL2CLM_apply, shiftedSeminorm_apply]

theorem deningerOscL2CLM_hermiteUnit (m j : ℕ) :
    deningerOscL2CLM m (hermiteUnit j)
      = ((4 * (π : ℂ) * (j + 1)) ^ m) • (hermiteUnit j).toLp 2 (volume : Measure ℝ) := by
  rw [deningerOscL2CLM_apply, shiftedNumberCLM_iterate_hermiteUnit, toLp_smul]

/-! ## The expansion in the oscillator quotients -/

theorem deningerOscL2CLM_partialSum (k : ℕ) (f : 𝓢(ℝ, ℂ)) (S : Finset ℕ) :
    deningerOscL2CLM k ((∑ j ∈ S, hermiteCoeff f j • hermiteUnit j) - f)
      = (∑ j ∈ S, hermiteCoeff ((shiftedNumberCLM^[k]) f) j •
          (hermiteUnit j).toLp 2 (volume : Measure ℝ))
        - ((shiftedNumberCLM^[k]) f).toLp 2 (volume : Measure ℝ) := by
  rw [map_sub, map_sum, deningerOscL2CLM_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, deningerOscL2CLM_hermiteUnit, smul_smul, hermiteCoeff_shiftedIterate]
  congr 1
  ring

/-- **The Hermite expansion converges in every oscillator seminorm.**  The partial sums of the
expansion differ from the function by the tail of the `L²` expansion of the corresponding
iterate. -/
theorem hasSum_hermiteExpansion_shiftedQuotient (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
    HasSum (fun j : ℕ => hermiteCoeff f j •
        deningerSeminormMk (shiftedSeminorm k) (hermiteUnit j))
      (deningerSeminormMk (shiftedSeminorm k) f) := by
  have hL2 := hasSum_hermiteExpansion_toLp ((shiftedNumberCLM^[k]) f)
  rw [HasSum, tendsto_iff_norm_sub_tendsto_zero] at hL2
  rw [HasSum, tendsto_iff_norm_sub_tendsto_zero]
  refine hL2.congr fun S => ?_
  have hmk : (∑ j ∈ S, hermiteCoeff f j • deningerSeminormMk (shiftedSeminorm k) (hermiteUnit j))
      - deningerSeminormMk (shiftedSeminorm k) f
      = deningerSeminormMk (shiftedSeminorm k)
        ((∑ j ∈ S, hermiteCoeff f j • hermiteUnit j) - f) := by
    rw [map_sub, map_sum]
    congr 1
  rw [hmk, deningerSeminormMk_norm, ← norm_deningerOscL2CLM k,
    deningerOscL2CLM_partialSum k f S]

/-! ## The coefficient functionals on the oscillator quotients -/

theorem norm_hermiteCoeff_le_shiftedSeminorm (m j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ‖hermiteCoeff f j‖ ≤ ((4 * π * ((j : ℝ) + 1)) ^ m)⁻¹ * shiftedSeminorm m f := by
  have hpos : (0 : ℝ) < (4 * π * ((j : ℝ) + 1)) ^ m := by
    have := Real.pi_pos
    positivity
  have h := norm_hermiteCoeff_shifted_le m j f
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  calc ‖hermiteCoeff f j‖ * (4 * π * ((j : ℝ) + 1)) ^ m
      = (4 * π * ((j : ℝ) + 1)) ^ m * ‖hermiteCoeff f j‖ := by ring
    _ ≤ shiftedSeminorm m f := h

theorem deningerHermiteCoeff_ker_le (m j : ℕ) :
    deningerSeminormKer (shiftedSeminorm m) ≤ LinearMap.ker (hermiteCoeffLM j) := by
  intro f hf
  have hzero : shiftedSeminorm m f = 0 := hf
  have h := norm_hermiteCoeff_le_shiftedSeminorm m j f
  rw [hzero, mul_zero] at h
  have hnorm : ‖hermiteCoeff f j‖ = 0 := le_antisymm h (norm_nonneg _)
  show hermiteCoeffLM j f = 0
  exact norm_eq_zero.mp hnorm

/-- The `j`-th Hermite coefficient, as a functional on the `m`-th oscillator quotient. -/
def deningerHermiteCoeffQuotient (m j : ℕ) :
    DeningerSeminormSpace (shiftedSeminorm m) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    (Submodule.liftQ (deningerSeminormKer (shiftedSeminorm m)) (hermiteCoeffLM j)
        (deningerHermiteCoeff_ker_le m j) :
      DeningerSeminormSpace (shiftedSeminorm m) →ₗ[ℂ] ℂ)
    (((4 * π * ((j : ℝ) + 1)) ^ m)⁻¹)
    (by
      rintro ⟨a⟩
      show ‖hermiteCoeff a j‖ ≤ ((4 * π * ((j : ℝ) + 1)) ^ m)⁻¹ * shiftedSeminorm m a
      exact norm_hermiteCoeff_le_shiftedSeminorm m j a)

@[simp] theorem deningerHermiteCoeffQuotient_mk (m j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    deningerHermiteCoeffQuotient m j (deningerSeminormMk (shiftedSeminorm m) f)
      = hermiteCoeff f j := rfl

theorem norm_deningerHermiteCoeffQuotient_le (m j : ℕ) :
    ‖deningerHermiteCoeffQuotient m j‖ ≤ ((4 * π * ((j : ℝ) + 1)) ^ m)⁻¹ := by
  refine LinearMap.mkContinuous_norm_le _ ?_ _
  have := Real.pi_pos
  positivity

/-! ## Nuclearity -/

/-- **The oscillator seminorm family is nuclear.**  Two extra orders of the shifted number
operator make the coefficient functionals and the normalized Hermite functions have summable norm
products, and the Hermite expansion exhibits the comparison map as the sum of the corresponding
rank-one maps. -/
theorem deningerIsNuclearSpace_shiftedSeminormFamily :
    DeningerIsNuclearSpace (shiftedSeminorm : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ) := by
  intro k
  obtain ⟨C, hC, hdom⟩ := shiftedSeminorm_le_of_le (Nat.le_add_right k 2)
  refine ⟨k + 2, C, hdom, ?_⟩
  refine ⟨ℕ, fun j => deningerHermiteCoeffQuotient (k + 2) j,
    fun j => deningerSeminormMk (shiftedSeminorm k) (hermiteUnit j), ?_, ?_⟩
  · have hle : ∀ j : ℕ,
        ‖deningerHermiteCoeffQuotient (k + 2) j‖ *
          ‖deningerSeminormMk (shiftedSeminorm k) (hermiteUnit j)‖
        ≤ ((4 * π) ^ 2)⁻¹ * (1 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
      intro j
      have hpos : (0 : ℝ) < 4 * π * ((j : ℝ) + 1) := four_pi_mul_pos j
      have hy : ‖deningerSeminormMk (shiftedSeminorm k) (hermiteUnit j)‖
          = (4 * π * ((j : ℝ) + 1)) ^ k := by
        rw [deningerSeminormMk_norm, shiftedSeminorm_hermiteUnit]
      rw [hy]
      have hstep : ‖deningerHermiteCoeffQuotient (k + 2) j‖ * (4 * π * ((j : ℝ) + 1)) ^ k
          ≤ ((4 * π * ((j : ℝ) + 1)) ^ (k + 2))⁻¹ * (4 * π * ((j : ℝ) + 1)) ^ k :=
        mul_le_mul_of_nonneg_right (norm_deningerHermiteCoeffQuotient_le (k + 2) j)
          (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      rw [pow_add]
      push_cast
      field_simp
    refine Summable.of_nonneg_of_le (fun j => by positivity) hle ?_
    have h1 : Summable fun j : ℕ => 1 / ((j : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    have h2 : Summable fun j : ℕ => 1 / ((((j + 1 : ℕ)) : ℝ) ^ 2) := (summable_nat_add_iff 1).mpr h1
    exact h2.mul_left _
  · intro x
    obtain ⟨f, rfl⟩ := deningerSeminormMk_surjective (shiftedSeminorm (k + 2)) x
    exact hasSum_hermiteExpansion_shiftedQuotient k f

/-- **The Schwartz space of the line is a nuclear space.**  The finite suprema of the Schwartz
seminorms and the oscillator seminorms dominate each other, and the oscillator family is
nuclear. -/
theorem deningerIsNuclearSpaceC_schwartzSup :
    DeningerIsNuclearSpaceC
      (fun s : Finset (ℕ × ℕ) => s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) := by
  refine deningerIsNuclearSpaceC_of_dominating
    (shiftedSeminorm : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ) _ ?_ ?_
    (DeningerIsNuclearSpace.toC _ deningerIsNuclearSpace_shiftedSeminormFamily)
  · intro s
    obtain ⟨m, C, _, hb⟩ := schwartzSup_le_shiftedSeminorm s
    exact ⟨m, C, hb⟩
  · intro m
    obtain ⟨s, C, _, hb⟩ := shiftedSeminorm_le_schwartzSup m
    refine ⟨s, (C : ℝ), fun x => ?_⟩
    have h := hb x
    rwa [_root_.smul_apply, NNReal.smul_def, smul_eq_mul] at h

end RHTower

end
