import GaloisForLFunctions.HTGeometry.HerglotzRegularizedUpperEnd
import GaloisForLFunctions.HTGeometry.ChamberFamilyGaugeInvariance

/-!
# Finite-atomic Herglotz chambers in the upper-end field

Finite signed real atoms are realized simultaneously as literal analytic germs and as elements of
the embedded rational coordinate field.  This identifies the chamber functions used by the exact
Krein-index theorem with rational gauges of one regularized Herglotz carrier.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory Filter Set Polynomial
open scoped BigOperators Differential

noncomputable section

/-- One real atomic summand, as an upper-end analytic germ. -/
def atomTermUpperEndAnalytic (a c : ℝ) : upperEndAnalyticSubring := by
  refine ⟨(((fun z : ℂ => (c : ℂ) / ((a : ℂ) - z)) : ℂ → ℂ) :
      Germ upperEndFilter ℂ),
    (fun z : ℂ => (c : ℂ) / ((a : ℂ) - z)), 0, ?_, rfl⟩
  refine AnalyticOnNhd.div analyticOnNhd_const
    (analyticOnNhd_const.sub analyticOnNhd_id) ?_
  intro z hz
  exact real_sub_ne_zero_of_im_ne_zero (ne_of_gt hz) a

@[simp]
theorem atomTermUpperEndAnalytic_coe (a c : ℝ) :
    ((atomTermUpperEndAnalytic a c : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      (((fun z : ℂ => (c : ℂ) / ((a : ℂ) - z)) : ℂ → ℂ) :
        Germ upperEndFilter ℂ) := rfl

/-- The rational function carried by one finite real atom. -/
def atomTermRatFunc (a c : ℝ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (c : ℂ)) /
    algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.C (a : ℂ) - Polynomial.X)

theorem polynomial_C_sub_X_ne_zero (a : ℂ) :
    Polynomial.C a - Polynomial.X ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
  simp at hcoeff

/-- The upper-end embedding of one atomic rational function is its literal analytic germ. -/
theorem upperEndRatfuncToMero_atomTerm (a c : ℝ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndRatfuncToMero (atomTermRatFunc a c) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (atomTermUpperEndAnalytic a c) := by
  letI := isDomain_upperEndAnalyticSubring
  have hdenPoly : Polynomial.C (a : ℂ) - Polynomial.X ≠ 0 :=
    polynomial_C_sub_X_ne_zero _
  have hdenMero :
      upperEndPolyToMero (Polynomial.C (a : ℂ) - Polynomial.X) ≠ 0 := by
    simpa only [map_zero] using upperEndPolyToMero_injective.ne hdenPoly
  have hmul :
      atomTermUpperEndAnalytic a c *
          upperEndPolyToAnalytic (Polynomial.C (a : ℂ) - Polynomial.X) =
        upperEndPolyToAnalytic (Polynomial.C (c : ℂ)) := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [upperEndFilter_basis.mem_iff.mpr
      ⟨0, trivial, Set.Subset.rfl⟩] with z hz
    have hne : (a : ℂ) - z ≠ 0 :=
      real_sub_ne_zero_of_im_ne_zero (ne_of_gt hz) a
    simpa [upperEndPolyToAnalytic] using (div_mul_cancel₀ (c : ℂ) hne)
  rw [atomTermRatFunc, map_div₀, upperEndRatfuncToMero_algebraMap_polynomial,
    upperEndRatfuncToMero_algebraMap_polynomial]
  apply (div_eq_iff hdenMero).2
  have hmulMero := congrArg
    (algebraMap upperEndAnalyticSubring upperEndMeroField) hmul
  simpa [upperEndPolyToMero, map_mul] using hmulMero.symm

/-- Finite real-atom correction in the abstract rational coordinate field. -/
def finiteAtomGaugeRatFunc {d : ℕ} (a c : Fin d → ℝ) : RatFunc ℂ :=
  ∑ j, atomTermRatFunc (a j) (c j)

/-- Finite atomic part as an upper-end analytic germ. -/
def atomPartUpperEndAnalytic {d : ℕ} (a c : Fin d → ℝ) :
    upperEndAnalyticSubring :=
  ∑ j, atomTermUpperEndAnalytic (a j) (c j)

@[simp]
theorem atomPartUpperEndAnalytic_coe {d : ℕ} (a c : Fin d → ℝ) :
    ((atomPartUpperEndAnalytic a c : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      ((atomPart a c : ℂ → ℂ) : Germ upperEndFilter ℂ) := by
  change (Subring.subtype upperEndAnalyticSubring)
      (∑ j, atomTermUpperEndAnalytic (a j) (c j)) = _
  rw [map_sum]
  change (∑ j, ((atomTermUpperEndAnalytic (a j) (c j) :
    upperEndAnalyticSubring) : Germ upperEndFilter ℂ)) = _
  simp_rw [atomTermUpperEndAnalytic_coe]
  change (∑ j ∈ Finset.univ,
      Germ.coeRingHom upperEndFilter
        (fun z : ℂ => (c j : ℂ) / ((a j : ℂ) - z))) = _
  rw [← map_sum (Germ.coeRingHom upperEndFilter)
    (fun j : Fin d => fun z : ℂ => (c j : ℂ) / ((a j : ℂ) - z)) Finset.univ]
  have hfun :
      (∑ j, fun z : ℂ => (c j : ℂ) / ((a j : ℂ) - z)) = atomPart a c := by
    funext z
    simp [atomPart]
  rw [hfun]
  rfl

/-- The embedded finite-atom rational correction equals its literal upper-end analytic germ. -/
theorem upperEndRatfuncToMero_finiteAtomGauge {d : ℕ} (a c : Fin d → ℝ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndRatfuncToMero (finiteAtomGaugeRatFunc a c) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (atomPartUpperEndAnalytic a c) := by
  letI := isDomain_upperEndAnalyticSubring
  unfold finiteAtomGaugeRatFunc atomPartUpperEndAnalytic
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => upperEndRatfuncToMero_atomTerm (a j) (c j)

/-- Literal chamber Herglotz function as an upper-end analytic germ. -/
def chamberHerglotzUpperEndAnalytic {d : ℕ} (nu : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight nu) (a c : Fin d → ℝ) :
    upperEndAnalyticSubring :=
  atomPartUpperEndAnalytic a c + regularizedH0UpperEndAnalytic nu hH0

@[simp]
theorem chamberHerglotzUpperEndAnalytic_coe {d : ℕ} (nu : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight nu) (a c : Fin d → ℝ) :
    ((chamberHerglotzUpperEndAnalytic nu hH0 a c : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      ((chamberHerglotz nu a c : ℂ → ℂ) : Germ upperEndFilter ℂ) := by
  change ((atomPartUpperEndAnalytic a c : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) +
      ((regularizedH0UpperEndAnalytic nu hH0 : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) = _
  rw [atomPartUpperEndAnalytic_coe, regularizedH0UpperEndAnalytic_coe]
  rfl

/-- Literal chamber Herglotz function in the upper-end meromorphic field. -/
def chamberHerglotzUpperEndMero {d : ℕ} (nu : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight nu) (a c : Fin d → ℝ) :
    upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact algebraMap upperEndAnalyticSubring upperEndMeroField
    (chamberHerglotzUpperEndAnalytic nu hH0 a c)

/-- Exact rational-gauge decomposition of every finite-atomic chamber member. -/
theorem chamberHerglotzUpperEndMero_eq_add_finiteAtomGauge
    {d : ℕ} (nu : Measure ℝ) (hH0 : Integrable nevanlinnaWeight nu)
    (a c : Fin d → ℝ) :
    letI := isDomain_upperEndAnalyticSubring
    chamberHerglotzUpperEndMero nu hH0 a c =
      regularizedH0UpperEndMero nu hH0 +
        upperEndRatfuncToMero (finiteAtomGaugeRatFunc a c) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [chamberHerglotzUpperEndMero, chamberHerglotzUpperEndAnalytic, map_add,
    upperEndRatfuncToMero_finiteAtomGauge]
  exact add_comm _ _

end

end GaloisForLFunctions.HTGeometry
