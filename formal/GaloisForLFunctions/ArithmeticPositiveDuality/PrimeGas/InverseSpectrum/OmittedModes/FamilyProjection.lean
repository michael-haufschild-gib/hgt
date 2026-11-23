import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.RankReadings
import GaloisForLFunctions.HTGeometry.SpectralHeatKernel.TrialSpace

/-! # Projection and dimension of a finite family of omitted directions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace

variable {r : ℕ}

abbrev familySpan (v : Fin r → Gas) := Submodule.span ℂ (Set.range v)

instance familySpan_finite (v : Fin r → Gas) : FiniteDimensional ℂ (familySpan v) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range v)

/-- Projection retaining the complement of a finite family of directions. -/
def omitFamily (v : Fin r → Gas) : Projection :=
  ⟨(familySpan v)ᗮ.starProjection,isStarProjection_starProjection⟩

theorem omitFamily_ker (v : Fin r → Gas) : (omitFamily v).val.toLinearMap.ker = familySpan v := by
  change (familySpan v)ᗮ.starProjection.toLinearMap.ker = _
  rw [Submodule.ker_starProjection,Submodule.orthogonal_orthogonal]

theorem missingDimension_family {v : Fin r → Gas} (hn : ∀ i, v i ≠ 0)
    (ho : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) : MissingDimension (omitFamily v) r := by
  rw [MissingDimension,omitFamily_ker]
  exact ⟨inferInstance,HTGeometry.finrank_span_of_orthogonal hn ho⟩

/-- Projection onto a finite orthogonal span, written in its original unnormalized directions. -/
theorem family_projection_apply {v : Fin r → Gas} (hn : ∀ i, v i ≠ 0)
    (ho : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) (x : Gas) :
    (familySpan v).starProjection x =
      ∑ i, (inner ℂ (v i) x/((‖v i‖^2:ℝ):ℂ)) • v i := by
  classical
  let W := familySpan v
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (W.starProjection_apply_mem x)
  have hv (i : Fin r) : v i ∈ W := Submodule.subset_span ⟨i,rfl⟩
  have hcoeff (i : Fin r) : c i = inner ℂ (v i) x/((‖v i‖^2:ℝ):ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hn i))))).mpr
    have he : inner ℂ (v i) (W.starProjection x) = inner ℂ (v i) x := by
      rw [← W.inner_starProjection_left_eq_right,Submodule.starProjection_eq_self_iff.mpr (hv i)]
    rw [← hc,inner_sum] at he
    simp only [inner_smul_right] at he
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [ho i j hj.symm,mul_zero])
      (fun hi => (hi (Finset.mem_univ i)).elim)] at he
    have hsq : inner ℂ (v i) (v i) = ((‖v i‖^2:ℝ):ℂ) := by
      rw [Complex.ofReal_pow]
      exact inner_self_eq_norm_sq_to_K _
    rwa [hsq] at he
  rw [← hc]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun c : ℂ => c • v i) (hcoeff i))

#print axioms missingDimension_family
#print axioms family_projection_apply

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
