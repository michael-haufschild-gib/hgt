import GaloisForLFunctions.HTGeometry.LagrangeSpectralProjector
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Circuit diagonal entries in a simple, ordered eigensystem -/

open Matrix MeasureTheory ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The diagonal entry of a fixed circuit on a spectral line. Cross-weights
make the formula independent of all eigenvector phases. -/
def circuitEntry (E : I→ℝ) (H W : Matrix I I ℂ) (i : I) : ℂ :=
  ∑ a, ∑ b, W a b*spectralCrossWeight E H (Pi.single b 1) (Pi.single a 1) i

private theorem inner_basis (v : I→ℂ) (a : I) :
    finiteComplexInner v (Pi.single a 1)=conj (v a) := by
  classical
  simp [finiteComplexInner,Pi.single_apply,mul_ite]

theorem circuitEntry_eq {E : I→ℝ} {H : Matrix I I ℂ} {v : I→I→ℂ}
    (he : IsOrthoEigenBasis H v E) (hs : Function.Injective E) (W : Matrix I I ℂ) (i : I) :
    circuitEntry E H W i=finiteComplexInner (v i) (W *ᵥ v i) := by
  simp only [circuitEntry,spectralCrossWeight_eq he hs,inner_basis,Complex.conj_conj]
  unfold finiteComplexInner Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The interpolation formula is Borel on the entire coefficient space,
including the convention of inverse zero at a collision. -/
theorem measurable_circuitEntry {X : Type*} [MeasurableSpace X]
    {H : X→Matrix I I ℂ} {E : X→I→ℝ} (hH : ∀ a b, Measurable (fun x => H x a b)) (hE : Measurable E)
    (W : Matrix I I ℂ) (i : I) : Measurable (fun x => circuitEntry (E x) (H x) W i) := by
  classical
  have he (l : I) : Measurable (fun x => ((E x l:ℝ):ℂ)) :=
    Complex.continuous_ofReal.measurable.comp ((measurable_pi_apply l).comp hE)
  have hf (l a b : I) : Measurable (fun x => lagrangeFactor (E x) i (H x) l a b) := by
    simp only [lagrangeFactor,Complex.ofReal_sub]
    exact ((he i).sub (he l)).inv.mul ((hH a b).sub ((he l).mul_const ((1:Matrix I I ℂ) a b)))
  have hprod (L : List I) (a b : I) : Measurable (fun x => (L.map (lagrangeFactor (E x) i (H x))).prod a b) := by
    induction L generalizing a b with
    | nil => exact measurable_const
    | cons l L ih =>
      simp only [List.map_cons,List.prod_cons,Matrix.mul_apply]
      exact Finset.measurable_fun_sum _ fun j _ => (hf l a j).mul (ih j b)
  apply Finset.measurable_fun_sum
  intro a _
  apply Finset.measurable_fun_sum
  intro b _
  apply Measurable.const_mul
  unfold spectralCrossWeight finiteComplexInner Matrix.mulVec dotProduct
  apply Finset.measurable_fun_sum
  intro j _
  apply Measurable.const_mul
  exact Finset.measurable_fun_sum _ fun l _ => (hprod (Finset.univ.erase i).toList j l).mul_const _

/-- On the simple-spectrum locus the line diagonal is continuous even
when the chosen eigenvectors have no continuous choice of phase. -/
theorem continuousAt_circuitEntry {X : Type*} [TopologicalSpace X]
    {H : X→Matrix I I ℂ} {E : X→I→ℝ} (hH : Continuous H) (hE : Continuous E)
    {x : X} (hs : Function.Injective (E x)) (W : Matrix I I ℂ) (i : I) :
    ContinuousAt (fun y => circuitEntry (E y) (H y) W i) x := by
  exact tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
    continuousAt_const.mul (continuousAt_spectralCrossWeight hE hH _ _ i hs)

#print axioms circuitEntry_eq
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
