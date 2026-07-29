import GaloisForLFunctions.HTGeometry.UpperEndConstantField

/-!
# Literal linear independence from the upper-end carrier

Linear independence in the upper-end meromorphic field descends to literal complex-valued
functions whenever the analytic representatives are their upper-end germs.  This is the reusable
bridge from meromorphic differential-algebra results to finite evaluation and Hilbert geometry.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Polynomial Filter
open scoped BigOperators

noncomputable section

local instance upperEndLiteralLinearIndependenceDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance upperEndLiteralLinearIndependenceComplexAlgebra :
    Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

/-- A vanishing upper-end germ relation has zero coefficients whenever the corresponding analytic
germs are linearly independent in the upper-end meromorphic field. -/
theorem coefficients_eq_zero_of_upperEndGerm_eq_zero
    {ι : Type*} [Fintype ι]
    (u : ι → ℂ → ℂ) (analytic : ι → upperEndAnalyticSubring)
    (hcoe : ∀ i, upperEndAnalyticSubring.subtype (analytic i) =
      Germ.coeRingHom upperEndFilter (u i))
    (hmero : LinearIndependent ℂ
      (fun i => algebraMap upperEndAnalyticSubring upperEndMeroField (analytic i)))
    (c : ι → ℂ)
    (hgerm : Germ.coeRingHom upperEndFilter (∑ i, c i • u i) = 0) :
    c = 0 := by
  classical
  rw [Fintype.linearIndependent_iff] at hmero
  have hanalytic :
      (∑ j, upperEndPolyToAnalytic (Polynomial.C (c j)) * analytic j) = 0 := by
    apply Subtype.ext
    change upperEndAnalyticSubring.subtype
      (∑ j, upperEndPolyToAnalytic (Polynomial.C (c j)) * analytic j) = 0
    rw [map_sum]
    calc
      _ = ∑ j, c j • (↑(u j) : Germ upperEndFilter ℂ) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [map_mul]
        have hconst : upperEndAnalyticSubring.subtype
            (upperEndPolyToAnalytic (Polynomial.C (c j))) =
            (↑(fun _ : ℂ => c j) : Germ upperEndFilter ℂ) := by
          change (↑((RingHom.pi fun z => Polynomial.evalRingHom z)
            (Polynomial.C (c j))) : Germ upperEndFilter ℂ) = _
          congr 1
          funext z
          simp
        rw [hconst, hcoe j]
        change (↑(fun _ : ℂ => c j) : Germ upperEndFilter ℂ) *
            (↑(u j) : Germ upperEndFilter ℂ) =
          (↑(c j • u j) : Germ upperEndFilter ℂ)
        apply Germ.coe_eq.mpr
        exact Filter.Eventually.of_forall fun _ => rfl
      _ = 0 := by simpa using hgerm
  funext i
  apply hmero c
  · calc
      ∑ j, c j • algebraMap upperEndAnalyticSubring upperEndMeroField (analytic j) =
          ∑ j, algebraMap upperEndAnalyticSubring upperEndMeroField
            (upperEndPolyToAnalytic (Polynomial.C (c j)) * analytic j) := by
        apply Finset.sum_congr rfl
        intro j _
        change upperEndComplexToMero (c j) *
            algebraMap upperEndAnalyticSubring upperEndMeroField (analytic j) =
          algebraMap upperEndAnalyticSubring upperEndMeroField
            (upperEndPolyToAnalytic (Polynomial.C (c j)) * analytic j)
        rw [map_mul]
        rfl
      _ = algebraMap upperEndAnalyticSubring upperEndMeroField
          (∑ j, upperEndPolyToAnalytic (Polynomial.C (c j)) * analytic j) := by
        rw [map_sum]
      _ = 0 := by rw [hanalytic, map_zero]

/-- A finite family of literal functions is linearly independent when its upper-end analytic
germs have linearly independent images in the upper-end meromorphic field. -/
theorem linearIndependent_literal_of_upperEndMero
    {ι : Type*} [Fintype ι]
    (u : ι → ℂ → ℂ) (analytic : ι → upperEndAnalyticSubring)
    (hcoe : ∀ i, upperEndAnalyticSubring.subtype (analytic i) =
      Germ.coeRingHom upperEndFilter (u i))
    (hmero : LinearIndependent ℂ
      (fun i => algebraMap upperEndAnalyticSubring upperEndMeroField (analytic i))) :
    LinearIndependent ℂ u := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hfunction i
  have hc := coefficients_eq_zero_of_upperEndGerm_eq_zero
    u analytic hcoe hmero c (congrArg (Germ.coeRingHom upperEndFilter) hfunction)
  exact congrFun hc i

end

end GaloisForLFunctions.HTGeometry
