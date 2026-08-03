import GaloisForLFunctions.HTGeometry.InfiniteTorusKroneckerDensity
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Characters of an infinite product torus

A character of a product torus is a finite product of coordinate characters, indexed by a finitely
supported integer vector.  On a phase flow it is the single phase of the detuning of that vector
against the frequencies, and against the Haar probability measure of the compact product group it
integrates to one or to zero according to whether the vector vanishes.

The vanishing is the usual translation argument: a nontrivial character takes a value different
from one, and translation invariance of Haar measure forces its integral to be fixed by
multiplication by that value.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- Coordinate characters are multiplicative in the argument. -/
theorem fourier_add_arg {T : ℝ} (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The Haar probability measure of a compact product torus. -/
def torusHaar (ι : Type*) [Countable ι] : Measure (UnitAddTorus ι) :=
  Measure.addHaarMeasure ⊤

instance torusHaar_isAddHaarMeasure (ι : Type*) [Countable ι] :
    (torusHaar ι).IsAddHaarMeasure := by
  unfold torusHaar
  infer_instance

instance torusHaar_isProbabilityMeasure (ι : Type*) [Countable ι] :
    IsProbabilityMeasure (torusHaar ι) := by
  refine ⟨?_⟩
  have huniv : (Set.univ : Set (UnitAddTorus ι))
      = ((⊤ : TopologicalSpace.PositiveCompacts (UnitAddTorus ι)) : Set (UnitAddTorus ι)) := rfl
  rw [torusHaar, huniv, Measure.addHaarMeasure_self]

/-- The character of a finitely supported integer vector. -/
def torusCharacter (n : ι →₀ ℤ) : C(UnitAddTorus ι, ℂ) where
  toFun := fun x => ∏ i ∈ n.support, fourier (n i) (x i)
  continuous_toFun := by
    refine continuous_finsetProd _ fun i _ => ?_
    exact (fourier (n i)).continuous.comp (continuous_apply i)

theorem torusCharacter_apply (n : ι →₀ ℤ) (x : UnitAddTorus ι) :
    torusCharacter n x = ∏ i ∈ n.support, fourier (n i) (x i) := rfl

theorem torusCharacter_zero (x : UnitAddTorus ι) :
    torusCharacter (0 : ι →₀ ℤ) x = 1 := by
  rw [torusCharacter_apply]
  simp

/-- Characters are multiplicative. -/
theorem torusCharacter_add (n : ι →₀ ℤ) (x y : UnitAddTorus ι) :
    torusCharacter n (x + y) = torusCharacter n x * torusCharacter n y := by
  rw [torusCharacter_apply, torusCharacter_apply, torusCharacter_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => fourier_add_arg (n i) (x i) (y i)

/-- The detuning of an integer vector against a frequency family. -/
def characterDetuning (n : ι →₀ ℤ) (omega : ι → ℝ) : ℝ :=
  ∑ i ∈ n.support, (n i : ℝ) * omega i

/-- **A character along a phase flow is a single phase.**  Its frequency is the detuning of the
character against the frequency family. -/
theorem torusCharacter_clockPhasePoint (n : ι →₀ ℤ) (omega : ι → ℝ) (t : ℝ) :
    torusCharacter n (clockPhasePoint omega t)
      = Complex.exp (((t * characterDetuning n omega : ℝ) : ℂ) * Complex.I) := by
  rw [torusCharacter_apply]
  have hterm : ∀ i ∈ n.support,
      fourier (n i) (clockPhasePoint omega t i)
        = Complex.exp ((((n i : ℝ) * (t * omega i) : ℝ) : ℂ) * Complex.I) := by
    intro i _
    rw [clockPhasePoint, fourier_coe_apply]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  rw [Finset.prod_congr rfl hterm, ← Complex.exp_sum]
  congr 1
  rw [characterDetuning]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A nontrivial character takes a value different from one. -/
theorem exists_torusCharacter_ne_one {n : ι →₀ ℤ} (hn : n ≠ 0) :
    ∃ g : UnitAddTorus ι, torusCharacter n g ≠ 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, n i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hn (Finsupp.ext fun i => hcon i)
  refine ⟨fun i => if i = i₀ then ((1 / (2 * (n i₀ : ℝ)) : ℝ) : UnitAddCircle) else 0, ?_⟩
  rw [torusCharacter_apply]
  have hsplit : (∏ i ∈ n.support,
      fourier (n i) (if i = i₀ then ((1 / (2 * (n i₀ : ℝ)) : ℝ) : UnitAddCircle) else 0))
      = fourier (n i₀) ((1 / (2 * (n i₀ : ℝ)) : ℝ) : UnitAddCircle) := by
    rw [← Finset.prod_erase_mul _ _ (Finsupp.mem_support_iff.mpr hi₀)]
    rw [if_pos rfl]
    have hone : (∏ i ∈ n.support.erase i₀,
        fourier (n i) (if i = i₀ then ((1 / (2 * (n i₀ : ℝ)) : ℝ) : UnitAddCircle) else 0)) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      rw [if_neg (Finset.mem_erase.mp hi).1]
      have hzero : ((0 : UnitAddCircle)) = ((0 : ℝ) : UnitAddCircle) := by simp
      rw [hzero, fourier_coe_apply]
      norm_num
    rw [hone, one_mul]
  rw [hsplit, fourier_coe_apply]
  have hn₀ : (n i₀ : ℂ) ≠ 0 := by exact_mod_cast hi₀
  have hval : 2 * (Real.pi : ℂ) * Complex.I * (n i₀ : ℂ) * ((1 / (2 * (n i₀ : ℝ)) : ℝ) : ℂ)
      / ((1 : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hval, Complex.exp_pi_mul_I]
  intro hcon
  exact (by norm_num : (-1 : ℂ) ≠ 1) hcon

/-- **Character orthogonality on the product torus.**  A nontrivial character has vanishing Haar
mean; the trivial one has mean one. -/
theorem integral_torusCharacter [Countable ι] [DecidableEq ι] (n : ι →₀ ℤ) :
    (∫ x, torusCharacter n x ∂(torusHaar ι)) = if n = 0 then 1 else 0 := by
  classical
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => torusCharacter_zero x)]
    simp
  · rw [if_neg hn]
    obtain ⟨g, hg⟩ := exists_torusCharacter_ne_one hn
    have hshift : (∫ x, torusCharacter n (g + x) ∂(torusHaar ι))
        = ∫ x, torusCharacter n x ∂(torusHaar ι) :=
      MeasureTheory.integral_add_left_eq_self (fun x => torusCharacter n x) g
    have hmul : (∫ x, torusCharacter n (g + x) ∂(torusHaar ι))
        = torusCharacter n g * ∫ x, torusCharacter n x ∂(torusHaar ι) := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => torusCharacter_add n g x)
    have hfix : torusCharacter n g * (∫ x, torusCharacter n x ∂(torusHaar ι))
        = ∫ x, torusCharacter n x ∂(torusHaar ι) := by
      rw [← hmul, hshift]
    have hsub : (torusCharacter n g - 1) * (∫ x, torusCharacter n x ∂(torusHaar ι)) = 0 := by
      rw [sub_mul, one_mul, hfix, sub_self]
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hg)

end

end GaloisForLFunctions.HTGeometry
