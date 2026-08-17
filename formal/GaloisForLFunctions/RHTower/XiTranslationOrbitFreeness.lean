import Mathlib
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.PrimeResidueValuationAnalyticSuperselection
import GaloisForLFunctions.HTGeometry.UpperEndDigammaShift
import GaloisForLFunctions.HTGeometry.UpperEndRationalCoordinateDifferentialAdjoin
import GaloisForLFunctions.RHTower.PrimeSourceCancellationBudget
import GaloisForLFunctions.RHTower.XiUpperEndHypertranscendence

/-!
# Full differential-translation orbit freeness of the completed logarithmic derivative

The `+2` shift of `xi'/xi`, after its explicit rational correction, exposes a prime Dirichlet
source.  Applying an arbitrary finite differential-translation filter to a relation among
translates of `xi'/xi` therefore turns it into a relation for that source with coefficients
multiplied by the filter symbol sampled at prime logarithms.  Because a nonzero exponential
polynomial leaves infinitely many prime samples nonzero, the filtered source stays
hypertranscendental, and the original relation cannot exist.

Under the rotation `s = -I z` the Dirichlet shift `s ↦ s + a` is the upper-end translation by
`I·a`, and the Dirichlet derivative `d/ds` is `I·δ`; an arbitrary polynomial in `d/ds` is
therefore an arbitrary polynomial in `δ`, and `upperEndOrbitCombination` is the general finite
differential-translation filter.
-/

namespace RHTower

open Complex Filter
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance orbitFreenessUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance orbitFreenessUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance orbitFreenessUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance orbitFreenessUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance orbitFreenessComplexDifferential : Differential ℂ where
  deriv := 0

local instance orbitFreenessDifferentialAlgebra :
    DifferentialAlgebra ℂ upperEndMeroField :=
  ⟨fun c ↦ by
    rw [upperEndMero_deriv_complexConstant c]
    change (0 : upperEndMeroField) = algebraMap ℂ upperEndMeroField 0
    rw [map_zero]⟩

theorem differentialJet_map_add (k : ℕ) (x y : upperEndMeroField) :
    differentialJet k (x + y) = differentialJet k x + differentialJet k y := by
  induction k with
  | zero => simp
  | succ k ih => simp [differentialJet_succ, ih]

theorem upperEndTranslationMeroEquiv_smul (c : ℂ) (d : ℂ) (x : upperEndMeroField) :
    upperEndTranslationMeroEquiv c (d • x) = d • upperEndTranslationMeroEquiv c x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  exact (upperEndTranslationMeroDifferentialAlgEquiv c).toAlgEquiv.commutes d

/-- A finite differential-translation filter acting on the upper-end meromorphic field.  The
Dirichlet-variable shift `s ↦ s + aⱼ` is the upper-end translation by `I·aⱼ` under `s = -I z`,
and the Dirichlet derivative `d/ds` is `I·δ`, so an arbitrary polynomial in `d/ds` is an arbitrary
polynomial in `δ`. -/
def upperEndOrbitCombination {m : ℕ} (a : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (x : upperEndMeroField) : upperEndMeroField :=
  ∑ j, ∑ k ∈ Finset.range ((P j).natDegree + 1),
    (P j).coeff k • differentialJet k (upperEndTranslationMeroEquiv (Complex.I * a j) x)

theorem upperEndOrbitCombination_add {m : ℕ} (a : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (x y : upperEndMeroField) :
    upperEndOrbitCombination a P (x + y)
      = upperEndOrbitCombination a P x + upperEndOrbitCombination a P y := by
  unfold upperEndOrbitCombination
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_add, differentialJet_map_add, smul_add]

theorem upperEndOrbitCombination_sub {m : ℕ} (a : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (x y : upperEndMeroField) :
    upperEndOrbitCombination a P (x - y)
      = upperEndOrbitCombination a P x - upperEndOrbitCombination a P y := by
  have h := upperEndOrbitCombination_add a P (x - y) y
  rw [sub_add_cancel] at h
  rw [h]
  ring

/-- Every upper-end translation commutes with every finite differential-translation filter. -/
theorem upperEndTranslationMeroEquiv_orbitCombination {m : ℕ} (a : Fin m → ℂ)
    (P : Fin m → Polynomial ℂ) (c : ℂ) (x : upperEndMeroField) :
    upperEndTranslationMeroEquiv c (upperEndOrbitCombination a P x)
      = upperEndOrbitCombination a P (upperEndTranslationMeroEquiv c x) := by
  unfold upperEndOrbitCombination
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [upperEndTranslationMeroEquiv_smul]
  congr 1
  have hjet := (upperEndTranslationMeroDifferentialAlgEquiv c).map_differentialJet k
    (upperEndTranslationMeroEquiv (Complex.I * a j) x)
  rw [show (upperEndTranslationMeroDifferentialAlgEquiv c).toAlgEquiv
      (differentialJet k (upperEndTranslationMeroEquiv (Complex.I * a j) x))
      = upperEndTranslationMeroEquiv c
        (differentialJet k (upperEndTranslationMeroEquiv (Complex.I * a j) x)) from rfl] at hjet
  rw [hjet]
  congr 1
  show upperEndTranslationMeroEquiv c (upperEndTranslationMeroEquiv (Complex.I * a j) x)
    = upperEndTranslationMeroEquiv (Complex.I * a j) (upperEndTranslationMeroEquiv c x)
  exact upperEndTranslationMeroEquiv_comm _ _ x

theorem upperEndDifferentialAlgebraicOver_complex_smul (c : ℂ) {x : upperEndMeroField}
    (hx : DifferentialAlgebraicOver ℂ x) : DifferentialAlgebraicOver ℂ (c • x) := by
  rw [Algebra.smul_def]
  exact differentialAlgebraicOver_mul (differentialAlgebraicOver_algebraMap c) hx

theorem upperEndDifferentialAlgebraicOver_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → upperEndMeroField) (hf : ∀ i ∈ s, DifferentialAlgebraicOver ℂ (f i)) :
    DifferentialAlgebraicOver ℂ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (differentialAlgebraicOver_algebraMap (F := ℂ) (E := upperEndMeroField) 0)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact differentialAlgebraicOver_add (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem upperEndDifferentialAlgebraicOver_differentialJet (k : ℕ) {x : upperEndMeroField}
    (hx : DifferentialAlgebraicOver ℂ x) : DifferentialAlgebraicOver ℂ (differentialJet k x) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      rw [differentialJet_succ]
      exact differentialAlgebraicOver_deriv ih

theorem differentialAlgebraicOver_upperEndTranslation (c : ℂ) {x : upperEndMeroField}
    (hx : DifferentialAlgebraicOver ℂ x) :
    DifferentialAlgebraicOver ℂ (upperEndTranslationMeroEquiv c x) :=
  (DifferentialAlgEquiv.differentialAlgebraicOver_map_iff
    (upperEndTranslationMeroDifferentialAlgEquiv c) x).mpr hx

/-- A finite differential-translation filter of a differentially algebraic element is again
differentially algebraic. -/
theorem differentialAlgebraicOver_upperEndOrbitCombination {m : ℕ} (a : Fin m → ℂ)
    (P : Fin m → Polynomial ℂ) {x : upperEndMeroField}
    (hx : DifferentialAlgebraicOver ℂ x) :
    DifferentialAlgebraicOver ℂ (upperEndOrbitCombination a P x) := by
  unfold upperEndOrbitCombination
  refine upperEndDifferentialAlgebraicOver_finset_sum _ _ (fun j _ => ?_)
  refine upperEndDifferentialAlgebraicOver_finset_sum _ _ (fun k _ => ?_)
  exact upperEndDifferentialAlgebraicOver_complex_smul _
    (upperEndDifferentialAlgebraicOver_differentialJet k
      (differentialAlgebraicOver_upperEndTranslation _ hx))

end

end RHTower

namespace RHTower

open Complex Filter
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.PrimeCancellation

local instance orbitFreenessUpperEndDomain' : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance orbitFreenessUpperEndComplexAlgebra' : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance orbitFreenessUpperEndDifferential' : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- The polynomial rewriting that converts a polynomial in the Dirichlet derivative `d/ds` into
the corresponding filter symbol block under the rotation `s = -I z`. -/
def dirichletTwist (P : Polynomial ℂ) : Polynomial ℂ :=
  P.comp (Polynomial.C (-Complex.I) * Polynomial.X)

theorem eval_dirichletTwist (P : Polynomial ℂ) (z : ℂ) :
    (dirichletTwist P).eval z = P.eval (-Complex.I * z) := by
  simp [dirichletTwist, Polynomial.eval_comp]

theorem dirichletTwist_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0) : dirichletTwist P ≠ 0 := by
  intro hzero
  apply hP
  have hcomp : (dirichletTwist P).comp (Polynomial.C Complex.I * Polynomial.X) = P := by
    unfold dirichletTwist
    rw [Polynomial.comp_assoc]
    have hinner : (Polynomial.C (-Complex.I) * Polynomial.X).comp
        (Polynomial.C Complex.I * Polynomial.X) = Polynomial.X := by
      rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
      rw [← mul_assoc, ← Polynomial.C_mul]
      rw [show -Complex.I * Complex.I = (1 : ℂ) by
        rw [neg_mul, Complex.I_mul_I]; ring]
      simp
    rw [hinner, Polynomial.comp_X]
  rw [← hcomp, hzero]
  simp

theorem upperEndTranslationMeroEquiv_finiteAbscissaLSeries (a : ℂ)
    (f : finiteAbscissaArithmeticSubalgebra) :
    upperEndTranslationMeroEquiv (Complex.I * a) (finiteAbscissaLSeriesToUpperEndMero f)
      = finiteAbscissaLSeriesToUpperEndMero (finiteAbscissaDirichletShift a f) := by
  change upperEndTranslationMeroEquiv (Complex.I * a)
      (algebraMap upperEndAnalyticSubring upperEndMeroField
        (finiteAbscissaLSeriesUpperEndAnalyticElement f)) = _
  rw [upperEndTranslationMeroEquiv_algebraMap]
  change _ = algebraMap upperEndAnalyticSubring upperEndMeroField
    (finiteAbscissaLSeriesUpperEndAnalyticElement (finiteAbscissaDirichletShift a f))
  congr 1
  apply Subtype.ext
  change upperEndTranslateGerm (Complex.I * a)
      (finiteAbscissaLSeriesToUpperEndGerm f) =
    finiteAbscissaLSeriesToUpperEndGerm (finiteAbscissaDirichletShift a f)
  rw [finiteAbscissaLSeriesToUpperEndGerm_dirichletShift]

theorem upperEndOrbitCombination_finiteAbscissaLSeries {m : ℕ} (a : Fin m → ℂ)
    (P : Fin m → Polynomial ℂ) (f : finiteAbscissaArithmeticSubalgebra) :
    upperEndOrbitCombination a P (finiteAbscissaLSeriesToUpperEndMero f)
      = finiteAbscissaLSeriesToUpperEndMero
          (∑ j, ∑ k ∈ Finset.range ((P j).natDegree + 1),
            (P j).coeff k •
              (finiteAbscissaRotatedDeriv^[k] (finiteAbscissaDirichletShift (a j) f))) := by
  unfold upperEndOrbitCombination
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul]
  congr 1
  rw [upperEndTranslationMeroEquiv_finiteAbscissaLSeries,
    differentialJet_finiteAbscissaLSeriesToUpperEndMero]

end

end RHTower

namespace RHTower

open Complex Filter
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.PrimeCancellation

theorem upperEndArithmeticFunction_sum_apply {ι : Type*} (S : Finset ι)
    (F : ι → ArithmeticFunction ℂ) (n : ℕ) :
    (∑ i ∈ S, F i) n = ∑ i ∈ S, F i n := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ArithmeticFunction.add_apply, ih]

theorem finiteAbscissa_val_sum {ι : Type*} (S : Finset ι)
    (g : ι → finiteAbscissaArithmeticSubalgebra) :
    (∑ i ∈ S, g i).1 = ∑ i ∈ S, (g i).1 := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
      rfl

/-- The arithmetic source produced by a finite differential-translation filter is the original
source scaled coefficientwise by the filter symbol. -/
theorem orbitSource_eq_filteredSource {m : ℕ} (a : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (f : finiteAbscissaArithmeticSubalgebra) :
    (∑ j, ∑ k ∈ Finset.range ((P j).natDegree + 1),
        (P j).coeff k •
          (finiteAbscissaRotatedDeriv^[k] (finiteAbscissaDirichletShift (a j) f))).1
      = filteredSource a (fun j => dirichletTwist (P j)) f.1 := by
  classical
  ext n
  rw [finiteAbscissa_val_sum, upperEndArithmeticFunction_sum_apply]
  rw [filteredSource_apply]
  by_cases hn : n = 0
  · subst n
    simp
  have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    have hlog' : ((Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) = Complex.log (((n : ℕ) : ℝ) : ℂ) :=
      Complex.ofReal_log (by positivity)
    rw [hlog']
    push_cast
    ring
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [filterSymbol, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [finiteAbscissa_val_sum, upperEndArithmeticFunction_sum_apply]
  rw [eval_dirichletTwist, ← cpow_neg_eq_exp (a j) hpos, hlog]
  rw [Polynomial.eval_eq_sum_range (p := P j) (-Complex.I * -((Real.log (n : ℝ) : ℝ) : ℂ))]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  show (P j).coeff k * ((finiteAbscissaRotatedDeriv^[k]
      (finiteAbscissaDirichletShift (a j) f)).1 n) = _
  rw [finiteAbscissaRotatedDeriv_iterate_apply, finiteAbscissaDirichletShift_apply, cpowWeight]
  rw [show (-Complex.I * -((Real.log (n : ℝ) : ℝ) : ℂ)) = Complex.I * ((Real.log (n : ℝ) : ℝ) : ℂ)
    by ring]
  ring

end

end RHTower

namespace RHTower

open Complex Filter
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.PrimeCancellation

local instance orbitFreenessUpperEndDomain'' : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance orbitFreenessUpperEndComplexAlgebra'' : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance orbitFreenessUpperEndCharZero'' : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance orbitFreenessUpperEndDifferential'' : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance orbitFreenessComplexDifferential'' : Differential ℂ where
  deriv := 0

local instance orbitFreenessDifferentialAlgebra'' :
    DifferentialAlgebra ℂ upperEndMeroField :=
  ⟨fun c ↦ by
    rw [upperEndMero_deriv_complexConstant c]
    change (0 : upperEndMeroField) = algebraMap ℂ upperEndMeroField 0
    rw [map_zero]⟩

local instance orbitFreenessRationalBaseDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance orbitFreenessRationalBaseAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField :=
  ⟨fun x => derivationClosedDifferential_apply
    upperEndRationalCoordinateField
    upperEndRationalCoordinateField_derivationClosed x⟩

/-- The filtered xi source produced by a finite differential-translation filter of the exposed
`+2` shift defect. -/
theorem upperEndOrbitCombination_filteredVonMangoldt {m : ℕ} (a : Fin m → ℂ)
    (P : Fin m → Polynomial ℂ) :
    upperEndOrbitCombination a P filteredVonMangoldtUpperEndCarrier
      = xiFilteredUpperEndCarrier a (fun j => dirichletTwist (P j)) := by
  change upperEndOrbitCombination a P
      (finiteAbscissaLSeriesToUpperEndMero filteredVonMangoldtFiniteAbscissaSource) = _
  rw [upperEndOrbitCombination_finiteAbscissaLSeries]
  change _ = finiteAbscissaLSeriesToUpperEndMero
    (xiFilteredFiniteAbscissaSource a (fun j => dirichletTwist (P j)))
  congr 1
  apply Subtype.ext
  rw [orbitSource_eq_filteredSource]
  rfl

/-- **Full differential-translation orbit freeness.**  For pairwise distinct complex shifts and
nonzero polynomial blocks, every finite combination `∑ⱼ Pⱼ(d/ds) (xi'/xi)(s + aⱼ)` is
hypertranscendental over the rational coordinate field. -/
theorem xiLogDerivRotatedUpperEndCarrier_orbitCombination_hypertranscendentalOver
    {m : ℕ} (a : Fin (m + 1) → ℂ) (P : Fin (m + 1) → Polynomial ℂ)
    (ha : Function.Injective a) (hP : ∀ j, P j ≠ 0) :
    HypertranscendentalOver upperEndRationalCoordinateField
      (upperEndOrbitCombination a P xiLogDerivRotatedUpperEndCarrier) := by
  have hQ : ∀ j, dirichletTwist (P j) ≠ 0 := fun j => dirichletTwist_ne_zero (hP j)
  have hHTF : HypertranscendentalOver upperEndRationalCoordinateField
      (upperEndOrbitCombination a P filteredVonMangoldtUpperEndCarrier) := by
    rw [upperEndOrbitCombination_filteredVonMangoldt]
    exact xiFilteredUpperEndCarrier_hypertranscendentalOver a
      (fun j => dirichletTwist (P j)) ha hQ
  have hDAr : DifferentialAlgebraicOver upperEndRationalCoordinateField
      (upperEndOrbitCombination a P xiShiftTwoRationalCorrectionUpperEndCarrier) := by
    intro hIndependent
    exact differentialAlgebraicOver_upperEndOrbitCombination a P
      xiShiftTwoRationalCorrectionUpperEndCarrier_differentialAlgebraicOver_complex
      (DifferentialIndependent.restrictScalars hIndependent)
  have hdefect :
      upperEndTranslationMeroEquiv (2 * I) xiLogDerivRotatedUpperEndCarrier -
          xiLogDerivRotatedUpperEndCarrier =
        filteredVonMangoldtUpperEndCarrier +
          xiShiftTwoRationalCorrectionUpperEndCarrier := by
    linear_combination xiLogDerivRotatedUpperEnd_translation_defect
  have hstep :
      upperEndTranslationMeroEquiv (2 * I)
          (upperEndOrbitCombination a P xiLogDerivRotatedUpperEndCarrier) -
        upperEndOrbitCombination a P xiLogDerivRotatedUpperEndCarrier =
      upperEndOrbitCombination a P filteredVonMangoldtUpperEndCarrier +
        upperEndOrbitCombination a P xiShiftTwoRationalCorrectionUpperEndCarrier := by
    rw [upperEndTranslationMeroEquiv_orbitCombination, ← upperEndOrbitCombination_sub,
      hdefect, upperEndOrbitCombination_add]
  apply DifferentialSemilinearEquiv.hypertranscendentalOver_of_sub_self
    (upperEndRationalCoordinateTranslationDifferentialSemilinearEquiv (2 * I))
  change HypertranscendentalOver upperEndRationalCoordinateField
    (upperEndTranslationMeroEquiv (2 * I)
        (upperEndOrbitCombination a P xiLogDerivRotatedUpperEndCarrier) -
      upperEndOrbitCombination a P xiLogDerivRotatedUpperEndCarrier)
  rw [hstep]
  exact (hypertranscendentalOver_add_differentialAlgebraic_iff hDAr).2 hHTF

end

end RHTower

namespace RHTower

open Complex Filter
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.PrimeCancellation

local instance orbitFreenessUpperEndDomain3 : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance orbitFreenessUpperEndComplexAlgebra3 : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance orbitFreenessUpperEndDifferential3 : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance orbitFreenessRationalBaseDifferential3 :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

/-- Vanishing blocks contribute nothing to a finite differential-translation filter. -/
theorem upperEndOrbitCombination_reindex {m : ℕ} (a : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (x : upperEndMeroField) {t : ℕ} (g : Fin t → Fin m) (hg : Function.Injective g)
    (hcover : ∀ j, P j ≠ 0 → j ∈ Finset.image g Finset.univ) :
    upperEndOrbitCombination a P x
      = upperEndOrbitCombination (fun i => a (g i)) (fun i => P (g i)) x := by
  classical
  unfold upperEndOrbitCombination
  rw [← Finset.sum_image (f := fun j => ∑ k ∈ Finset.range ((P j).natDegree + 1),
      (P j).coeff k • differentialJet k (upperEndTranslationMeroEquiv (Complex.I * a j) x))
      (g := g) (s := Finset.univ) (fun i _ j _ h => hg h)]
  refine (Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ?_)).symm
  have hzero : P j = 0 := by
    by_contra hne
    exact hj (hcover j hne)
  rw [hzero]
  simp

/-- **Full differential-translation orbit freeness, general form.**  For pairwise distinct complex
shifts and polynomial blocks that are not all zero, `∑ⱼ Pⱼ(d/ds) (xi'/xi)(s + aⱼ)` is
hypertranscendental over the rational coordinate field. -/
theorem xiLogDerivRotatedUpperEndCarrier_orbitCombination_hypertranscendentalOver'
    {m : ℕ} (a : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (ha : Function.Injective a) (hsome : ∃ j, P j ≠ 0) :
    HypertranscendentalOver upperEndRationalCoordinateField
      (upperEndOrbitCombination a P xiLogDerivRotatedUpperEndCarrier) := by
  classical
  set T : Finset (Fin m) := Finset.univ.filter (fun j => P j ≠ 0) with hT
  have hTne : T.Nonempty := by
    obtain ⟨j, hj⟩ := hsome
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨k, hk⟩ : ∃ k, T.card = k + 1 := by
    have := Finset.card_pos.mpr hTne
    exact ⟨T.card - 1, by omega⟩
  set g : Fin T.card → Fin m := fun i => ((T.equivFin.symm i : T) : Fin m) with hg
  have hginj : Function.Injective g := by
    intro i j hij
    have h1 : (T.equivFin.symm i : T) = T.equivFin.symm j := Subtype.ext hij
    exact T.equivFin.symm.injective h1
  have hgmem : ∀ i, g i ∈ T := fun i => (T.equivFin.symm i).2
  have hgP : ∀ i, P (g i) ≠ 0 := fun i => (Finset.mem_filter.mp (hgmem i)).2
  have hcover : ∀ j, P j ≠ 0 → j ∈ Finset.image g Finset.univ := by
    intro j hj
    have hjT : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    refine Finset.mem_image.mpr ⟨T.equivFin ⟨j, hjT⟩, Finset.mem_univ _, ?_⟩
    simp [hg]
  set g' : Fin (k + 1) → Fin m := fun i => g ((finCongr hk).symm i) with hg'
  have hg'inj : Function.Injective g' := fun i j hij =>
    (finCongr hk).symm.injective (hginj hij)
  have hcover' : ∀ j, P j ≠ 0 → j ∈ Finset.image g' Finset.univ := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hcover j hj)
    exact Finset.mem_image.mpr ⟨finCongr hk i, Finset.mem_univ _,
      by simp [hg']⟩
  rw [upperEndOrbitCombination_reindex a P _ g' hg'inj hcover']
  exact xiLogDerivRotatedUpperEndCarrier_orbitCombination_hypertranscendentalOver
    (fun i => a (g' i)) (fun i => P (g' i)) (fun i j hij => hg'inj (ha hij))
    (fun i => hgP ((finCongr hk).symm i))

/-- **No finite differential-difference equation with a differentially algebraic forcing term.**
A nonzero finite differential-translation filter of `xi'/xi` is never differentially algebraic. -/
theorem xiLogDerivRotatedUpperEndCarrier_orbitCombination_not_differentialAlgebraic
    {m : ℕ} (a : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (ha : Function.Injective a) (hsome : ∃ j, P j ≠ 0) :
    ¬ DifferentialAlgebraicOver upperEndRationalCoordinateField
      (upperEndOrbitCombination a P xiLogDerivRotatedUpperEndCarrier) :=
  xiLogDerivRotatedUpperEndCarrier_orbitCombination_hypertranscendentalOver' a P ha hsome

/-- **Trivial differentially algebraic translation stabilizer.**  For every nonzero complex shift,
the difference of the two translates of `xi'/xi` is hypertranscendental. -/
theorem xiLogDerivRotatedUpperEndCarrier_translation_difference_hypertranscendentalOver
    {h : ℂ} (hh : h ≠ 0) :
    HypertranscendentalOver upperEndRationalCoordinateField
      (upperEndTranslationMeroEquiv (Complex.I * h) xiLogDerivRotatedUpperEndCarrier -
        xiLogDerivRotatedUpperEndCarrier) := by
  classical
  have hcomb : upperEndOrbitCombination ![0, h] ![Polynomial.C (-1), Polynomial.C 1]
      xiLogDerivRotatedUpperEndCarrier
      = upperEndTranslationMeroEquiv (Complex.I * h) xiLogDerivRotatedUpperEndCarrier -
        xiLogDerivRotatedUpperEndCarrier := by
    unfold upperEndOrbitCombination
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Polynomial.natDegree_C, zero_add, Finset.sum_range_one,
      Polynomial.coeff_C_zero, mul_zero, upperEndTranslationMeroEquiv_zero,
      differentialJet_zero]
    rw [Algebra.smul_def, Algebra.smul_def]
    simp only [map_neg, map_one, neg_mul, one_mul]
    ring
  rw [← hcomb]
  refine xiLogDerivRotatedUpperEndCarrier_orbitCombination_hypertranscendentalOver' _ _ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · exact ⟨1, by simp⟩

end

end RHTower
