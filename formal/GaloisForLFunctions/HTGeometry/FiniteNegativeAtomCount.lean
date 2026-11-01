import GaloisForLFunctions.HTGeometry.HausdorffQuadratureMeasure
import GaloisForLFunctions.HTGeometry.WeightedNormInjection
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-!
# Counting negative atoms by a correction space

Tests supported on mutually singular negative atoms give a positive diagonal
quadratic form dominated by the correction map. Weighted norm injectivity
bounds the number of atoms by the number of corrections.
-/

open MeasureTheory Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- A finite coordinate vector realized as a function supported on its atoms. -/
def finiteAtomTest (s : Finset X) (c : s → ℂ) : X → ℂ :=
  fun x => ∑ j : s, ({(j : X)} : Set X).indicator (fun _ => c j) x

theorem finiteAtomTest_apply (s : Finset X) (c : s → ℂ) (j : s) :
    finiteAtomTest s c j = c j := by
  classical
  unfold finiteAtomTest
  rw [sum_eq_single j]
  · exact Set.indicator_of_mem (show (j : X) ∈ ({(j : X)} : Set X) from rfl)
      (fun _ : X => c j)
  · intro i _ hij
    exact Set.indicator_of_notMem (fun h => hij (Subtype.ext h.symm)) (fun _ => c i)
  · simp

omit [MeasurableSingletonClass X] in
/-- Mutual singularity makes every positive atom of the negative measure
null for the positive measure. -/
theorem measure_singleton_eq_zero_of_mutuallySingular
    {P N : Measure X} (hmut : P ⟂ₘ N) {x : X} (hx : N {x} ≠ 0) : P {x} = 0 := by
  have hmem : x ∈ hmut.nullSet := by
    by_contra hnot
    apply hx
    exact measure_mono_null (Set.singleton_subset_iff.mpr hnot) hmut.measure_compl_nullSet
  exact measure_mono_null (Set.singleton_subset_iff.mpr hmem) hmut.measure_nullSet

/-- An exact atomic negative part injects into any finite correction space. -/
theorem finite_negative_atom_count_le
    (P N : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure N] (hmut : P ⟂ₘ N)
    (s : Finset X) (hw : ∀ x ∈ s, 0 < N.real {x})
    (hN : N = ∑ x ∈ s, ENNReal.ofReal (N.real {x}) • Measure.dirac x)
    {m : ℕ} (q : Fin m → X → ℂ)
    (hrepair : ∀ f : X → ℂ, MemLp f 2 (P + N) →
      0 ≤ (∫ x, ‖f x‖ ^ 2 ∂P) - (∫ x, ‖f x‖ ^ 2 ∂N) +
        ∑ i, ‖(∫ x, q i x * f x ∂P) - ∫ x, q i x * f x ∂N‖ ^ 2) :
    s.card ≤ m := by
  classical
  let w : s → ℝ := fun j => N.real {(j : X)}
  have hwpos (j : s) : 0 < w j := hw j j.2
  let T : (s → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun c i => ∑ j : s, (w j : ℂ) * q i j * c j
      map_add' := by intro a b; funext i; simp only [Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' := by
        intro a c
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        apply sum_congr rfl fun j _ => ?_
        ring }
  have hbound (c : s → ℂ) : (∑ j, w j * ‖c j‖ ^ 2) ≤ ∑ i, ‖T c i‖ ^ 2 := by
    let f := finiteAtomTest s c
    have hf : MemLp f 2 (P + N) := by
      exact memLp_finsetSum _ fun j _ =>
        (memLp_const (c j)).indicator (measurableSet_singleton (j : X))
    have hPj (j : s) : P {(j : X)} = 0 :=
      measure_singleton_eq_zero_of_mutuallySingular hmut (fun hz => by
        have := hwpos j
        simp only [w, Measure.real, hz, ENNReal.toReal_zero, lt_self_iff_false] at this)
    have hfae : f =ᵐ[P] fun _ => 0 := by
      have hi (j : s) : ({(j : X)} : Set X).indicator (fun _ => c j) =ᵐ[P] fun _ => 0 := by
        have hj : ∀ᵐ x ∂P, x ∉ ({(j : X)} : Set X) := by
          simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hPj j
        filter_upwards [hj] with x hx
        exact Set.indicator_of_notMem hx _
      filter_upwards [ae_all_iff.mpr hi] with x hx
      change (∑ j : s, ({(j : X)} : Set X).indicator (fun _ => c j) x) = 0
      simp only [hx, sum_const_zero]
    have henergyP : (∫ x, ‖f x‖ ^ 2 ∂P) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hfae] with x hx
      change ‖f x‖ ^ 2 = 0
      simp only [hx, norm_zero, zero_pow two_ne_zero]
    have hpairP (i : Fin m) : (∫ x, q i x * f x ∂P) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hfae] with x hx
      change q i x * f x = 0
      rw [hx, mul_zero]
    have henergyN : (∫ x, ‖f x‖ ^ 2 ∂N) = ∑ j : s, w j * ‖c j‖ ^ 2 := by
      conv_lhs => rw [hN]
      rw [integral_finsetWeightedDirac_general s _ (fun x hx => (hw x hx).le)
        (fun x : X => x) (fun x => ‖f x‖ ^ 2)]
      rw [← sum_coe_sort]
      apply sum_congr rfl fun j _ => ?_
      simp only [smul_eq_mul, f, finiteAtomTest_apply, w]
    have hpairN (i : Fin m) : (∫ x, q i x * f x ∂N) = T c i := by
      conv_lhs => rw [hN]
      rw [integral_finsetWeightedDirac_general s _ (fun x hx => (hw x hx).le)
        (fun x : X => x) (fun x => q i x * f x)]
      rw [← sum_coe_sort]
      change (∑ j : s, N.real {(j : X)} • (q i j * f j)) =
        ∑ j : s, (w j : ℂ) * q i j * c j
      apply sum_congr rfl fun j _ => ?_
      change N.real {(j : X)} • (q i j * finiteAtomTest s c j) = _
      rw [finiteAtomTest_apply, Complex.real_smul]
      exact (mul_assoc _ _ _).symm
    have hr := hrepair f hf
    simp only [henergyP, henergyN, hpairP, hpairN, zero_sub, norm_neg] at hr
    linarith only [hr]
  simpa only [Fintype.card_coe] using card_le_of_weighted_norm_sq_le w hwpos T hbound

end

end GaloisForLFunctions.HTGeometry
