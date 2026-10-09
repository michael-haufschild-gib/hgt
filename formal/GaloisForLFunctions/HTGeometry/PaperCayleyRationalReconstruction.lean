import GaloisForLFunctions.HTGeometry.PaperFourierCircleConvergence
import GaloisForLFunctions.HTGeometry.HardyRealBoundaryConstant
import GaloisForLFunctions.HTGeometry.CayleyBoundaryL2Unitary

/-! # Pointwise rational reconstruction of real-line L² inputs

Cayley transport changes the proved circle endpoint into a full symmetric rational
expansion on the real line. The half-density is explicit and the limit is the
actual native L² representative. Countable families and their finite complex
mixtures share one Lebesgue-null exceptional set.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter Topology Set Complex
open scoped BigOperators ENNReal

/-- Fourier coordinates of the exact inverse Cayley unitary. -/
def paperCayleyCircleCoordinates (f : RealLineL2) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  circleLpAddCircleLinearIsometryEquiv (circleLineCayleyUnitary.symm f)

/-- Explicit rational symmetric cutoff with the native Cayley half-density. -/
def paperCayleyRationalPartialSum (f : RealLineL2) (N : ℕ) (t : ℝ) : ℂ :=
  (Real.sqrt Real.pi : ℂ)⁻¹ * ((t : ℂ) + Complex.I)⁻¹ *
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      fourierCoeff (paperCayleyCircleCoordinates f) n * (realCayley t) ^ n

private theorem pull_ae {P : AddCircle (1 : ℝ) → Prop}
    (h : ∀ᵐ x ∂AddCircle.haarAddCircle, P x) :
    ∀ᵐ t ∂volume, P (addCircleCircleEquiv.symm (circleCayley t)) := by
  have hcircle := (addCircleCircleMeasurePreserving.symm addCircleCircleEquiv).quasiMeasurePreserving.ae h
  have hweight := circleCayley_weighted_measurePreserving.quasiMeasurePreserving.ae hcircle
  have hv := (ae_withDensity_iff (measurable_realDensity measurable_standardCauchyWeight)).mp hweight
  filter_upwards [hv] with t ht
  exact ht (by simpa only [realDensity, ne_eq, ENNReal.ofReal_eq_zero, not_le] using
    standardCauchyWeight_pos t)

/-- The inverse coordinate representative reconstructs the literal line representative. -/
theorem paperCayleyCircleCoordinates_ae (f : RealLineL2) :
    f =ᵐ[volume] fun t => (Real.sqrt Real.pi : ℂ)⁻¹ * ((t : ℂ) + Complex.I)⁻¹ *
      paperCayleyCircleCoordinates f (addCircleCircleEquiv.symm (circleCayley t)) := by
  have ha := pull_ae (coeFn_circleLpAddCircleLinearIsometryEquiv (circleLineCayleyUnitary.symm f))
  have hl := circleLineCayleyIsometry_ae_explicit (circleLineCayleyUnitary.symm f)
  rw [← circleLineCayleyUnitary_apply, LinearIsometryEquiv.apply_symm_apply] at hl
  filter_upwards [ha, hl] with t ht hline
  simpa only [paperCayleyCircleCoordinates, ht, Function.comp_apply,
    MeasurableEquiv.apply_symm_apply] using hline

/-- Every Cayley Fourier character is the corresponding integer rational power. -/
theorem paperCayley_fourier_character (n : ℤ) (t : ℝ) :
    fourier n (addCircleCircleEquiv.symm (circleCayley t)) = (realCayley t) ^ n := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  have h : (addCircleCircleEquiv.symm (circleCayley t)).toCircle = circleCayley t := by
    have he := addCircleCircleEquiv.apply_symm_apply (circleCayley t)
    change (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)
      (addCircleCircleEquiv.symm (circleCayley t)) = _ at he
    rwa [AddCircle.homeomorphCircle_apply] at he
  rw [h, circleCayley_coe]

theorem paperCayleyRationalPartialSum_eq (f : RealLineL2) (N : ℕ) (t : ℝ) :
    paperCayleyRationalPartialSum f N t =
      (Real.sqrt Real.pi : ℂ)⁻¹ * ((t : ℂ) + Complex.I)⁻¹ *
        paperCircleFourierPartialSum 1 (paperCayleyCircleCoordinates f) N
          (addCircleCircleEquiv.symm (circleCayley t)) := by
  simp only [paperCayleyRationalPartialSum, paperCircleFourierPartialSum,
    paperCayley_fourier_character]

/-- Full rational cutoffs recover every member of a countable native L² family. -/
theorem paperCayleyRational_common_reconstruction {κ : Type*} [Countable κ]
    (f : κ → RealLineL2) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ j, Tendsto (fun N => paperCayleyRationalPartialSum (f j) N t)
        atTop (𝓝 (f j t)) := by
  obtain ⟨D, _, hz, hc⟩ := paperCircleLp_common_fourier_convergence 1
    (fun j => paperCayleyCircleCoordinates (f j))
  have ha : ∀ᵐ x ∂AddCircle.haarAddCircle, ∀ j,
      Tendsto (fun N => paperCircleFourierPartialSum 1 (paperCayleyCircleCoordinates (f j)) N x)
        atTop (𝓝 (paperCayleyCircleCoordinates (f j) x)) := by
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx
    exact hc x hx
  have hline : ∀ᵐ t ∂volume, ∀ j,
      Tendsto (fun N => paperCayleyRationalPartialSum (f j) N t) atTop (𝓝 (f j t)) := by
    filter_upwards [pull_ae ha, ae_all_iff.mpr (fun j => paperCayleyCircleCoordinates_ae (f j))]
      with t ht he
    intro j
    simpa only [paperCayleyRationalPartialSum_eq, he j] using
      (ht j).const_mul ((Real.sqrt Real.pi : ℂ)⁻¹ * ((t : ℂ) + Complex.I)⁻¹)
  obtain ⟨E, hsub, hm, hz⟩ := exists_measurable_superset_of_null (ae_iff.mp hline)
  refine ⟨E, hm, hz, ?_⟩
  intro t ht
  by_contra h
  exact ht (hsub h)

/-- One exceptional set serves every finite support and every complex mixture. -/
theorem paperCayleyRational_common_span_reconstruction {κ : Type*} [Countable κ]
    (f : κ → RealLineL2) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j * paperCayleyRationalPartialSum (f j) N t)
          atTop (𝓝 (∑ j ∈ S, c j * f j t)) := by
  obtain ⟨E, hm, hz, hc⟩ := paperCayleyRational_common_reconstruction f
  exact ⟨E, hm, hz, fun t ht S c =>
    tendsto_finsetSum S (fun j _ => (hc t ht j).const_mul (c j))⟩

end
end GaloisForLFunctions.HTGeometry
