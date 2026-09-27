import GaloisForLFunctions.RHTower.CCMRealGramComplexEnergy

/-!
# Literal finite superpositions of compact smooth CCM sources

Finite complex superposition commutes with both the complete form-domain
embedding and the theta ground-profile map.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators SchwartzMap

namespace RHTower

private theorem tsupport_source_finset_sum_subset {ι : Type*} {a : SuzukiPositiveAperture}
    (s : Finset ι) (u : ι → CCMComplexSmoothInteriorSource a) (z : ι → ℂ) :
    tsupport (fun x : ℝ => ∑ i ∈ s, z i * u i x) ⊆ Ioo (-a.1) a.1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (tsupport_add _ _).trans
      (union_subset (tsupport_mul_subset_right.trans (u i).tsupport_subset) ih)

def ccmSmoothFiniteSum {ι : Type*} [Fintype ι] {a : SuzukiPositiveAperture}
    (u : ι → CCMComplexSmoothInteriorSource a) (z : ι → ℂ) : CCMComplexSmoothInteriorSource a where
  toFun x := ∑ i, z i * u i x
  smooth := ContDiff.sum fun i _ => contDiff_const.mul (u i).smooth
  hasCompactSupport := by
    convert!
      (HasCompactSupport.finset_sum (s := Finset.univ)
        (fun i _ => (u i).hasCompactSupport.mul_left (f := fun _ : ℝ => z i))) using 1
    funext x
    simp only [Finset.sum_apply, Pi.mul_apply]
  tsupport_subset := tsupport_source_finset_sum_subset Finset.univ u z

@[simp] theorem ccmSmoothFiniteSum_apply {ι : Type*} [Fintype ι] {a : SuzukiPositiveAperture}
    (u : ι → CCMComplexSmoothInteriorSource a) (z : ι → ℂ) (x : ℝ) :
    ccmSmoothFiniteSum u z x = ∑ i, z i * u i x := rfl

theorem ccmSmoothFiniteSum_toCCMFormVector {ι : Type*} [Fintype ι] {a : SuzukiPositiveAperture}
    (u : ι → CCMComplexSmoothInteriorSource a) (z : ι → ℂ) :
    (ccmSmoothFiniteSum u z).toCCMFormVector = ∑ i, z i • (u i).toCCMFormVector := by
  apply ccmArchimedeanFormEmbedding_injective a
  rw [map_sum]
  apply Lp.ext
  have hi (i : ι) : ((ccmArchimedeanFormEmbedding a (z i • (u i).toCCMFormVector) : SoninL2) :
      ℝ → ℂ) =ᵐ[volume] fun x => z i * u i x := by
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (z i) (ccmArchimedeanFormEmbedding a (u i).toCCMFormVector),
      (u i).toCCMFormVector_physical_coeFn] with x hx hu
    rw [ccmArchimedeanFormToAperture_coe] at hu
    rw [hx]
    change z i * _ = z i * u i x
    rw [hu]
  have hall : ∀ᵐ x : ℝ, ∀ i : ι,
      (ccmArchimedeanFormEmbedding a (z i • (u i).toCCMFormVector) : SoninL2) x = z i * u i x :=
    (ae_all_iff).mpr hi
  filter_upwards [(ccmSmoothFiniteSum u z).toCCMFormVector_physical_coeFn,
    Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => ccmArchimedeanFormEmbedding a (z i • (u i).toCCMFormVector)), hall] with x hx hs ha
  rw [ccmArchimedeanFormToAperture_coe] at hx
  rw [hx, hs]
  exact Finset.sum_congr rfl fun i _ => (ha i).symm

theorem ccmThetaGroundProfile_finiteSum {ι : Type*} [Fintype ι] {a : SuzukiPositiveAperture}
    (u : ι → CCMComplexSmoothInteriorSource a) (z : ι → ℂ) :
    ccmThetaGroundProfile (ccmSmoothFiniteSum u z) = ∑ i, z i • ccmThetaGroundProfile (u i) := by
  ext x
  simp only [ccmThetaGroundProfile_apply, ccmSmoothFiniteSum_apply, sum_apply,
    smul_apply, smul_eq_mul]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => mul_div_assoc _ _ _

end RHTower
