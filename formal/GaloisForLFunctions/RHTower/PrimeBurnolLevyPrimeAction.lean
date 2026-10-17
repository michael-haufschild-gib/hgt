import GaloisForLFunctions.RHTower.PrimeBurnolLevyInverseGraph
import GaloisForLFunctions.HTGeometry.BurnolValuationCayleyFrame

/-! The finite-prime backward relation is an action; drift controls exactly its closability. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ComplexOrder
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

theorem linearIndependent_primeBurnolRawFeature : LinearIndependent ℂ primeBurnolRawFeature := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have hp (i : s) : 0 < Real.log ((i : Nat.Primes) : ℝ) :=
    Real.log_pos (by exact_mod_cast (i : Nat.Primes).property.one_lt)
  have hinj : Function.Injective (fun i : s => Real.log ((i : Nat.Primes) : ℝ)) := by
    intro i j hij
    have hr : ((i : Nat.Primes) : ℝ) = ((j : Nat.Primes) : ℝ) :=
      Real.log_injOn_pos
        (Set.mem_Ioi.mpr (show 0 < ((i : Nat.Primes) : ℝ) by
          exact_mod_cast (i : Nat.Primes).property.pos))
        (Set.mem_Ioi.mpr (show 0 < ((j : Nat.Primes) : ℝ) by
          exact_mod_cast (j : Nat.Primes).property.pos)) hij
    apply Subtype.ext
    apply Subtype.ext
    exact_mod_cast hr
  simpa only [Function.comp_def, primeBurnolRawFeature, burnolComplexFeature_ofReal] using!
    linearIndependent_burnolRateFeature_fintype (fun i : s => Real.log ((i : Nat.Primes) : ℝ)) hp hinj

theorem linearIndependent_primeLogCriticalLaplaceFeatureL2 :
    LinearIndependent ℂ primeLogCriticalLaplaceFeatureL2 := by
  have h := linearIndependent_primeBurnolRawFeature.units_smul
    (fun p => Units.mk0 (primeBurnolFeatureScale p : ℂ)
      (Complex.ofReal_ne_zero.mpr (primeBurnolFeatureScale_pos p).ne'))
  change LinearIndependent ℂ
    (fun p => (primeBurnolFeatureScale p : ℂ) • primeBurnolRawFeature p) at h
  have he : (fun p => (primeBurnolFeatureScale p : ℂ) • primeBurnolRawFeature p) =
      primeLogCriticalLaplaceFeatureL2 :=
    funext fun p => (primeLogCriticalLaplaceFeatureL2_eq_burnol p).symm
  rwa [he] at h

namespace BurnolLevyData
variable (D : BurnolLevyData)

theorem backwardPrimeSpan_vertical (t : ℝ≥0) {v : BurnolHalfLineL2}
    (hv : (0, v) ∈ D.backwardPrimeSpan t) : v = 0 := by
  rw [backwardPrimeSpan, ← Finsupp.range_linearCombination] at hv
  obtain ⟨c, hc⟩ := hv
  have hf := congrArg (fun q : BurnolHalfLineL2 × BurnolHalfLineL2 => q.1) hc
  change (LinearMap.fst ℂ BurnolHalfLineL2 BurnolHalfLineL2)
    (Finsupp.linearCombination ℂ _ c) = 0 at hf
  rw [Finsupp.apply_linearCombination] at hf
  have hc0 : c = 0 := by
    apply linearIndependent_primeLogCriticalLaplaceFeatureL2
    simpa only [Function.comp_def, LinearMap.fst_apply, map_zero] using hf
  subst c
  simpa using! (congrArg Prod.snd hc).symm

theorem backwardPrimeSpan_singleValued (t : ℝ≥0) {u v w : BurnolHalfLineL2}
    (hv : (u, v) ∈ D.backwardPrimeSpan t) (hw : (u, w) ∈ D.backwardPrimeSpan t) : v = w := by
  apply sub_eq_zero.mp
  apply D.backwardPrimeSpan_vertical t
  have hs := (D.backwardPrimeSpan t).sub_mem hv hw
  change (u - u, v - w) ∈ D.backwardPrimeSpan t at hs
  simpa only [sub_self] using hs

/-- The well-defined finite-prime action is closable exactly when its drift window is empty. -/
theorem backwardPrimeAction_closable_iff (t : ℝ≥0) :
    (∀ v : BurnolHalfLineL2, (0, v) ∈ D.backwardPrimeGraph t → v = 0) ↔
      D.drift * t = 0 := by
  rw [← D.evolution_injective_iff]
  constructor
  · intro h v w hvw
    apply sub_eq_zero.mp
    apply h
    apply (D.backwardPrimeGraph_mem_iff t _ _).mpr
    rw [map_sub, hvw, sub_self]
  · intro hinj v hv
    apply hinj
    rw [map_zero]
    exact (D.backwardPrimeGraph_mem_iff t _ _).mp hv

end BurnolLevyData
end RHTower
