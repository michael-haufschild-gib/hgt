import GaloisForLFunctions.HTGeometry.ComplexTorusProductLimit
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Finite-coordinate conditional recovery of complex torus products

Haar measure is the independent product of circle Haar measures. Consequently
conditioning a finite mean-one product on a smaller set of coordinates removes
exactly the omitted factors. The same projection is continuous on complex L².
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section

variable {ι : Type*} [Countable ι]

theorem torusHaar_eq_infinitePi :
    torusHaar ι = Measure.infinitePi (fun _ : ι => AddCircle.haarAddCircle) :=
  ((Measure.isProjectiveLimit_infinitePi (fun _ : ι => AddCircle.haarAddCircle)).unique
    (fun P => (measurePreserving_torus_restrict P).map_eq)).symm

@[reducible] def torusCoordinateSigma (P : Finset ι) : MeasurableSpace (UnitAddTorus ι) :=
  ⨆ i ∈ (P : Set ι), MeasurableSpace.comap (fun x : UnitAddTorus ι => x i) inferInstance

omit [Countable ι] in
theorem torusCoordinateSigma_le (P : Finset ι) :
    torusCoordinateSigma P ≤ (inferInstance : MeasurableSpace (UnitAddTorus ι)) := by
  apply iSup_le
  intro i
  apply iSup_le
  intro _
  exact (measurable_pi_apply i).comap_le

omit [Countable ι] in
theorem stronglyMeasurable_torusFiniteProduct_coord
    (f : ι → C(UnitAddCircle, ℂ)) (P : Finset ι) :
    StronglyMeasurable[torusCoordinateSigma P] (torusFiniteProduct f P) := by
  apply Finset.stronglyMeasurable_fun_prod
  intro i hi
  have heval : @Measurable (UnitAddTorus ι) UnitAddCircle (torusCoordinateSigma P)
      inferInstance (fun x => x i) := by
    have hle : MeasurableSpace.comap (fun x : UnitAddTorus ι => x i) inferInstance ≤
        torusCoordinateSigma P :=
      le_iSup_of_le i (le_iSup_of_le hi le_rfl)
    intro s hs
    exact hle _ ⟨s, hs, rfl⟩
  exact ((f i).continuous.measurable.comp heval).stronglyMeasurable

theorem indep_torusCoordinateSigma {P Q : Finset ι} (hPQ : Disjoint P Q) :
    Indep (torusCoordinateSigma P) (torusCoordinateSigma Q) (torusHaar ι) := by
  rw [torusHaar_eq_infinitePi]
  apply indep_iSup_of_disjoint
    (fun i : ι => (show Measurable (fun x : UnitAddTorus ι => x i)
      from measurable_pi_apply i).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ι => AddCircle.haarAddCircle)
      (X := fun (_ : ι) (θ : UnitAddCircle) => θ) (fun _ => measurable_id))
  exact Set.disjoint_left.mpr fun i hi hq => Finset.disjoint_left.mp hPQ hi hq

theorem integral_torusFiniteProduct (f : ι → C(UnitAddCircle, ℂ)) (P : Finset ι) :
    ∫ x, torusFiniteProduct f P x ∂torusHaar ι =
      ∏ i ∈ P, ∫ θ, f i θ ∂AddCircle.haarAddCircle :=
  integral_torus_finite_product P (fun i => f i) (fun i => (f i).continuous)

theorem integrable_torusFiniteProduct (f : ι → C(UnitAddCircle, ℂ)) (P : Finset ι) :
    Integrable (torusFiniteProduct f P) (torusHaar ι) :=
  (torusFiniteProduct f P).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem condExp_torusFiniteProduct_of_subset (f : ι → C(UnitAddCircle, ℂ))
    (hmean : ∀ i, ∫ θ, f i θ ∂AddCircle.haarAddCircle = 1)
    {P Q : Finset ι} (hPQ : P ⊆ Q) :
    (torusHaar ι)[torusFiniteProduct f Q | torusCoordinateSigma P] =ᵐ[torusHaar ι]
      torusFiniteProduct f P := by
  classical
  have hsplit : (fun x => torusFiniteProduct f P x * torusFiniteProduct f (Q \ P) x) =
      torusFiniteProduct f Q := by
    funext x
    change (∏ i ∈ P, f i (x i)) * (∏ i ∈ Q \ P, f i (x i)) = _
    rw [mul_comm, Finset.prod_sdiff hPQ]
    rfl
  have hdisjoint : Disjoint (Q \ P) P :=
    Finset.disjoint_left.mpr (fun _ hi hp => (Finset.mem_sdiff.mp hi).2 hp)
  have htail : (torusHaar ι)[torusFiniteProduct f (Q \ P) | torusCoordinateSigma P]
      =ᵐ[torusHaar ι] fun _ => ∫ x, torusFiniteProduct f (Q \ P) x ∂torusHaar ι :=
    condExp_indep_eq (torusCoordinateSigma_le (Q \ P))
      (torusCoordinateSigma_le P) (stronglyMeasurable_torusFiniteProduct_coord f (Q \ P))
      (indep_torusCoordinateSigma hdisjoint)
  have htailmean : ∫ x, torusFiniteProduct f (Q \ P) x ∂torusHaar ι = 1 := by
    rw [integral_torusFiniteProduct]
    simp only [hmean, Finset.prod_const_one]
  have hpull := condExp_bilin_of_stronglyMeasurable_left
    (μ := torusHaar ι) (m := torusCoordinateSigma P)
    (f := torusFiniteProduct f P) (g := torusFiniteProduct f (Q \ P))
    (ContinuousLinearMap.mul ℝ ℂ)
    (stronglyMeasurable_torusFiniteProduct_coord f P)
    (by simpa only [ContinuousLinearMap.mul_apply', hsplit] using
      integrable_torusFiniteProduct f Q)
    (integrable_torusFiniteProduct f (Q \ P))
  simp only [ContinuousLinearMap.mul_apply', hsplit] at hpull
  filter_upwards [hpull, htail] with x hx ht
  rw [hx, ht, htailmean, mul_one]

def torusConditionalL2 (P : Finset ι) :
    Lp ℂ 2 (torusHaar ι) →L[ℂ] Lp ℂ 2 (torusHaar ι) :=
  (lpMeas ℂ ℂ (torusCoordinateSigma P) 2 (torusHaar ι)).subtypeL.comp
    (condExpL2 ℂ ℂ (torusCoordinateSigma_le P))

theorem coeFn_torusConditionalL2 (P : Finset ι) (f : Lp ℂ 2 (torusHaar ι)) :
    torusConditionalL2 P f =ᵐ[torusHaar ι]
      (torusHaar ι)[f | torusCoordinateSigma P] := by
  change (condExpL2 ℂ ℂ (torusCoordinateSigma_le P) f : UnitAddTorus ι → ℂ)
    =ᵐ[torusHaar ι] _
  simpa only [Lp.toLp_coeFn] using
    (Lp.memLp f).condExpL2_ae_eq_condExp (𝕜 := ℂ) (torusCoordinateSigma_le P)

theorem torusConditionalL2_torusFiniteProduct (f : ι → C(UnitAddCircle, ℂ))
    (hmean : ∀ i, ∫ θ, f i θ ∂AddCircle.haarAddCircle = 1)
    {P Q : Finset ι} (hPQ : P ⊆ Q) :
    torusConditionalL2 P (torusFiniteProductLp f Q) = torusFiniteProductLp f P := by
  apply Lp.ext
  exact (coeFn_torusConditionalL2 P _).trans
    ((condExp_congr_ae (coeFn_torusFiniteProductLp f Q)).trans
      ((condExp_torusFiniteProduct_of_subset f hmean hPQ).trans
        (coeFn_torusFiniteProductLp f P).symm))

end

end GaloisForLFunctions.HTGeometry
