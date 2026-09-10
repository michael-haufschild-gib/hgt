import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedDiskEigenchains
import GaloisForLFunctions.RHTower.FokasLenellsCauchyExtension
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Dense actual Hardy data from bounded Cauchy derivative chains.
An open upper-pole patch corresponds to rates inside the unit disk. The actual L2
Cauchy transform propagates orthogonality from this patch to every rational pole. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalCoordinateDensityLowerComplete : CompleteSpace (hardyL2ᗮ) :=
  hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalCoordinateDensityUpperComplete : CompleteSpace UpperHardyL2 :=
  isClosed_hardyL2.completeSpace_coe
local instance causalCoordinateDensityChainNormedGroup : NormedAddCommGroup causalBoundedChain :=
  causalBoundedChain.normedAddCommGroup
local instance causalCoordinateDensityChainNormedSpace : NormedSpace ℂ causalBoundedChain :=
  causalBoundedChain.normedSpace

private theorem high_pole_rate_norm {w : ℂ} (hw : 1 < w.im) : ‖causalPoleRate w‖ ≤ 1 := by
  have hn : 1 < ‖w‖ := hw.trans_le ((le_abs_self w.im).trans (Complex.abs_im_le_norm w))
  have hnp : 0 < ‖w‖ := lt_trans zero_lt_one hn
  calc
    ‖causalPoleRate w‖ = (1 / ‖w‖) / 2 := by
      simp only [causalPoleRate, norm_div, norm_neg, Complex.norm_I]
      norm_num
    _ ≤ 1 := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      apply (div_le_iff₀ hnp).2
      nlinarith

private theorem high_pole_orthogonality (f : hardyL2ᗮ)
    (hf : ∀ z : causalBoundedDiskRate, inner ℂ f (causalBoundedDiskEigenvector z).val = 0)
    {w : ℂ} (hw : 1 < w.im) :
    inner ℂ f (causalCauchyEigenvector ⟨w, lt_trans zero_lt_one hw⟩) = 0 := by
  let z : causalBoundedDiskRate :=
    ⟨causalPoleRate w, causalPoleRate_re_neg ⟨w, lt_trans zero_lt_one hw⟩, high_pole_rate_norm hw⟩
  have hp : causalEigenPole ⟨z.val, z.property.1⟩ = ⟨w, lt_trans zero_lt_one hw⟩ :=
    Subtype.ext (causalPoleRate_involution w)
  have he : (causalLeftEigenvector ⟨z.val, z.property.1⟩).val =
      causalCauchyEigenvector ⟨w, lt_trans zero_lt_one hw⟩ :=
    congrArg causalCauchyEigenvector hp
  have hn : (‖causalLeftEigenvector ⟨z.val, z.property.1⟩‖ : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (causalLeftEigenvector_ne_zero ⟨z.val, z.property.1⟩)))
  have hh := hf z
  change inner ℂ f ((‖causalLeftEigenvector ⟨z.val, z.property.1⟩‖ : ℂ)⁻¹ •
    (causalLeftEigenvector ⟨z.val, z.property.1⟩).val) = 0 at hh
  rw [inner_smul_right] at hh
  have hv := (mul_eq_zero.mp hh).resolve_left hn
  exact (congrArg (fun v : hardyL2ᗮ => inner ℂ f v) he).symm.trans hv

/-- Actual rational eigenvectors with rates in the left unit disk already span dense Hardy data. -/
theorem topologicalClosure_span_causalBoundedDiskEigenvector_eq_top :
    (Submodule.span ℂ (Set.range (fun z : causalBoundedDiskRate =>
      (causalBoundedDiskEigenvector z).val))).topologicalClosure = ⊤ := by
  rw [RHTower.topologicalClosure_span_eq_top_iff]
  intro f hf
  obtain ⟨u, rfl⟩ := causalHardyConjugation_surjective f
  have hhigh (w : ℂ) (hw : 1 < w.im) : cauchyExtension u.val w = 0 := by
    have hh := high_pole_orthogonality (causalHardyConjugation u)
      (fun z => hf _ ⟨z, rfl⟩) hw
    change inner ℂ (causalHardyConjugation u)
      (causalHardyConjugation (lowerCauchyFeatureAt w (lt_trans zero_lt_one hw))) = 0 at hh
    rw [causalHardyConjugation_inner] at hh
    have hp : inner ℂ (lowerCauchyFeatureAt w (lt_trans zero_lt_one hw)) u = 0 :=
      (inner_conj_symm (lowerCauchyFeatureAt w (lt_trans zero_lt_one hw)) u).symm.trans hh
    change (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ x : ℝ, (u.val : ℝ → ℂ) x / ((x : ℂ) - w)) = 0
    rw [← inner_lowerCauchyFeatureAt (lt_trans zero_lt_one hw) u, hp, mul_zero]
  have hana : AnalyticOnNhd ℂ (cauchyExtension u.val) {w : ℂ | 0 < w.im} :=
    (analyticOnNhd_cauchyExtension u.val).mono (fun _ hw => ne_of_gt hw)
  have hnear : cauchyExtension u.val =ᶠ[𝓝 (2 * I)] 0 := by
    have hopen : IsOpen {w : ℂ | 1 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    have hm : (2 * I : ℂ) ∈ {w : ℂ | 1 < w.im} := by norm_num
    have he : ∀ᶠ w : ℂ in 𝓝 (2 * I), 1 < w.im := hopen.mem_nhds hm
    exact he.mono (fun w hw => hhigh w hw)
  have hall : Set.EqOn (cauchyExtension u.val) 0 {w : ℂ | 0 < w.im} :=
    hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_im_gt 0).isPreconnected (by norm_num : (2 * I : ℂ).im > 0) hnear
  have hscale : (2 * (Real.pi : ℂ) * I)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  apply (RHTower.topologicalClosure_span_eq_top_iff _).mp
    topologicalClosure_span_causalCauchyEigenvector_eq_top
  rintro g ⟨w, rfl⟩
  have hh := hall w.property
  change (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ x : ℝ, (u.val : ℝ → ℂ) x / ((x : ℂ) - w.val)) = 0 at hh
  have hp : inner ℂ (lowerCauchyFeatureAt w.val w.property) u = 0 :=
    (inner_lowerCauchyFeatureAt w.property u).trans ((mul_eq_zero.mp hh).resolve_left hscale)
  have hp' : inner ℂ u (lowerCauchyFeatureAt w.val w.property) = 0 :=
    (inner_conj_symm u (lowerCauchyFeatureAt w.val w.property)).symm.trans
      ((congrArg (starRingEnd ℂ) hp).trans (map_zero _))
  change inner ℂ (causalHardyConjugation u)
    (causalHardyConjugation (lowerCauchyFeatureAt w.val w.property)) = 0
  rw [causalHardyConjugation_inner, hp', map_zero]

/-- Every fixed genuine derivative coordinate of bounded chains has dense range in actual L2 data. -/
theorem causalBoundedChainCoordinate_denseRange (j : ℕ) :
    DenseRange (causalBoundedChainCoordinate j) := by
  let P : Submodule ℂ (hardyL2ᗮ) := (causalBoundedChainCoordinate j).toLinearMap.range
  have hspan : Submodule.span ℂ (Set.range (fun z : causalBoundedDiskRate =>
      (causalBoundedDiskEigenvector z).val)) ≤ P := by
    apply Submodule.span_le.mpr
    rintro v ⟨z, rfl⟩
    have hn : z.val ≠ 0 := by
      intro hz
      have hh := z.property.1
      rw [hz] at hh
      exact (lt_irrefl 0) hh
    refine ⟨(z.val^j)⁻¹ • causalBoundedDiskEigenchain z, ?_⟩
    have he : causalBoundedChainCoordinate j (causalBoundedDiskEigenchain z) =
        z.val^j • (causalBoundedDiskEigenvector z).val := rfl
    change causalBoundedChainCoordinate j ((z.val^j)⁻¹ • causalBoundedDiskEigenchain z) = _
    exact ((causalBoundedChainCoordinate j).map_smul (z.val^j)⁻¹ _).trans
      ((congrArg (fun v : hardyL2ᗮ => (z.val^j)⁻¹ • v) he).trans
        ((smul_smul _ _ _).trans
          ((congrArg (fun c : ℂ => c • (causalBoundedDiskEigenvector z).val)
            (inv_mul_cancel₀ (pow_ne_zero j hn))).trans (one_smul _ _))))
  have hcl := Submodule.topologicalClosure_mono hspan
  rw [topologicalClosure_span_causalBoundedDiskEigenvector_eq_top] at hcl
  have hp : P.topologicalClosure = ⊤ := le_antisymm le_top hcl
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hp

end
end RHTower.FokasLenells
