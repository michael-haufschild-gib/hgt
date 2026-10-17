import GaloisForLFunctions.RHTower.PrimeBurnolPureJumpInjectivity
import GaloisForLFunctions.HTGeometry.BurnolWeightedShiftKernel

/-! Exact closure and information loss of the backward actual-prime relation. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ComplexOrder
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry
namespace BurnolLevyData
variable (D : BurnolLevyData)

/-- The full physical kernel is exactly the initial drift window. -/
theorem evolution_eq_zero_iff (t : ℝ≥0) (f : BurnolHalfLineL2) :
    D.evolution t f = 0 ↔
      (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi ((D.drift * t : ℝ≥0) : ℝ))] 0 := by
  rw [D.evolution_eq_zero_iff_shift, burnolWeightedShift_eq_zero_iff]

theorem evolution_injective_iff (t : ℝ≥0) :
    Function.Injective (D.evolution t) ↔ D.drift * t = 0 := by
  constructor
  · intro hE
    apply (burnolWeightedShift_injective_iff (D.drift * t)).mp
    intro f g hfg
    apply hE
    rw [D.evolution_factor, mul_apply_eq_comp, mul_apply_eq_comp, hfg]
  · intro ht f g hfg
    apply (burnolWeightedShift_injective_iff (D.drift * t)).mpr ht
    apply D.withoutDrift_evolution_injective t
    simpa only [D.evolution_factor, mul_apply_eq_comp] using hfg

def backwardPrimeSpan (t : ℝ≥0) : Submodule ℂ (BurnolHalfLineL2 × BurnolHalfLineL2) :=
  Submodule.span ℂ (Set.range fun p : Nat.Primes =>
    (primeLogCriticalLaplaceFeatureL2 p,
      Complex.exp (((t : ℝ) : ℂ) * D.exponent (Real.log (p : ℝ))) •
        primeLogCriticalLaplaceFeatureL2 p))

def backwardPrimeGraph (t : ℝ≥0) : Submodule ℂ (BurnolHalfLineL2 × BurnolHalfLineL2) :=
  (D.backwardPrimeSpan t).topologicalClosure

def backwardRelation (t : ℝ≥0) : Submodule ℂ (BurnolHalfLineL2 × BurnolHalfLineL2) :=
  ((D.evolution t).comp (ContinuousLinearMap.snd ℂ BurnolHalfLineL2 BurnolHalfLineL2) -
    ContinuousLinearMap.fst ℂ BurnolHalfLineL2 BurnolHalfLineL2).ker

theorem backwardRelation_mem_iff (t : ℝ≥0) (u v : BurnolHalfLineL2) :
    (u, v) ∈ D.backwardRelation t ↔ D.evolution t v = u := by
  change D.evolution t v - u = 0 ↔ _
  exact sub_eq_zero

theorem isClosed_backwardRelation (t : ℝ≥0) :
    IsClosed (D.backwardRelation t : Set (BurnolHalfLineL2 × BurnolHalfLineL2)) :=
  ContinuousLinearMap.isClosed_ker _

private theorem backward_exp_cancel (t : ℝ≥0) (z : ℂ) :
    Complex.exp (-((t : ℝ) : ℂ) * D.exponent z) *
      Complex.exp (((t : ℝ) : ℂ) * D.exponent z) = 1 := by
  rw [← Complex.exp_add]
  rw [show -((t : ℝ) : ℂ) * D.exponent z +
    ((t : ℝ) : ℂ) * D.exponent z = 0 by ring, Complex.exp_zero]

private theorem backwardPrimeSpan_le (t : ℝ≥0) :
    D.backwardPrimeSpan t ≤ D.backwardRelation t := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  apply (D.backwardRelation_mem_iff t _ _).mpr
  rw [map_smul, D.evolution_prime, smul_smul, mul_comm,
    D.backward_exp_cancel, one_smul]

def backwardGraphMap (t : ℝ≥0) : BurnolHalfLineL2 →L[ℂ]
    (BurnolHalfLineL2 × BurnolHalfLineL2) :=
  (D.evolution t).prod (ContinuousLinearMap.id ℂ BurnolHalfLineL2)

private theorem backwardGraphMap_prime (t : ℝ≥0) (p : Nat.Primes) :
    D.backwardGraphMap t (primeLogCriticalLaplaceFeatureL2 p) =
      Complex.exp (-((t : ℝ) : ℂ) * D.exponent (Real.log (p : ℝ))) •
        (primeLogCriticalLaplaceFeatureL2 p,
          Complex.exp (((t : ℝ) : ℂ) * D.exponent (Real.log (p : ℝ))) •
            primeLogCriticalLaplaceFeatureL2 p) := by
  apply Prod.ext
  · exact D.evolution_prime t p
  · change primeLogCriticalLaplaceFeatureL2 p = _ • (_ • primeLogCriticalLaplaceFeatureL2 p)
    rw [smul_smul, D.backward_exp_cancel, one_smul]

/-- Actual finite-prime backward graphs close to the complete inverse relation. -/
theorem backwardPrimeGraph_eq_relation (t : ℝ≥0) :
    D.backwardPrimeGraph t = D.backwardRelation t := by
  apply le_antisymm
  · exact (D.backwardPrimeSpan t).topologicalClosure_minimal (D.backwardPrimeSpan_le t)
      (D.isClosed_backwardRelation t)
  · let S := (D.backwardPrimeGraph t).comap (D.backwardGraphMap t).toLinearMap
    have hclosed : IsClosed (S : Set BurnolHalfLineL2) :=
      (D.backwardPrimeSpan t).isClosed_topologicalClosure.preimage
        (D.backwardGraphMap t).continuous
    have hspan : Submodule.span ℂ (Set.range primeLogCriticalLaplaceFeatureL2) ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨p, rfl⟩
      change D.backwardGraphMap t (primeLogCriticalLaplaceFeatureL2 p) ∈ D.backwardPrimeGraph t
      rw [D.backwardGraphMap_prime]
      apply (D.backwardPrimeGraph t).smul_mem
      exact (D.backwardPrimeSpan t).le_topologicalClosure (Submodule.subset_span ⟨p, rfl⟩)
    have hall : ∀ v : BurnolHalfLineL2, v ∈ S := by
      have h := closure_minimal hspan hclosed
      rw [dense_primeLogCriticalLaplaceFeature_span.closure_eq] at h
      exact fun v => h (Set.mem_univ v)
    rintro ⟨u, v⟩ huv
    have he := (D.backwardRelation_mem_iff t u v).mp huv
    rw [← he]
    exact hall v

theorem backwardPrimeGraph_mem_iff (t : ℝ≥0) (u v : BurnolHalfLineL2) :
    (u, v) ∈ D.backwardPrimeGraph t ↔ D.evolution t v = u := by
  rw [D.backwardPrimeGraph_eq_relation, D.backwardRelation_mem_iff]

theorem backwardPrimeGraph_vertical_iff (t : ℝ≥0) (v : BurnolHalfLineL2) :
    (0, v) ∈ D.backwardPrimeGraph t ↔
      (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioi ((D.drift * t : ℝ≥0) : ℝ))] 0 := by
  rw [D.backwardPrimeGraph_mem_iff, D.evolution_eq_zero_iff]

theorem backwardPrimeGraph_fibre_iff (t : ℝ≥0) {u v w : BurnolHalfLineL2}
    (hv : (u, v) ∈ D.backwardPrimeGraph t) :
    (u, w) ∈ D.backwardPrimeGraph t ↔
      ((w - v : BurnolHalfLineL2) : ℝ → ℂ)
        =ᵐ[volume.restrict (Ioi ((D.drift * t : ℝ≥0) : ℝ))] 0 := by
  rw [D.backwardPrimeGraph_mem_iff] at hv ⊢
  rw [← D.evolution_eq_zero_iff, map_sub, hv, sub_eq_zero]

theorem backwardPrimeGraph_singleValued_iff (t : ℝ≥0) :
    (∀ u v w : BurnolHalfLineL2,
      (u, v) ∈ D.backwardPrimeGraph t → (u, w) ∈ D.backwardPrimeGraph t → v = w) ↔
      D.drift * t = 0 := by
  rw [← D.evolution_injective_iff]
  constructor
  · intro h v w hvw
    exact h (D.evolution t v) v w
      ((D.backwardPrimeGraph_mem_iff t _ _).mpr rfl)
      ((D.backwardPrimeGraph_mem_iff t _ _).mpr hvw.symm)
  · intro hinj u v w hv hw
    exact hinj (((D.backwardPrimeGraph_mem_iff t _ _).mp hv).trans
      ((D.backwardPrimeGraph_mem_iff t _ _).mp hw).symm)

theorem dense_evolution_range (t : ℝ≥0) : Dense ((D.evolution t).range : Set BurnolHalfLineL2) := by
  apply dense_primeLogCriticalLaplaceFeature_span.mono
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  refine ⟨Complex.exp (((t : ℝ) : ℂ) * D.exponent (Real.log (p : ℝ))) •
    primeLogCriticalLaplaceFeatureL2 p, ?_⟩
  change D.evolution t (Complex.exp (((t : ℝ) : ℂ) * D.exponent (Real.log (p : ℝ))) •
    primeLogCriticalLaplaceFeatureL2 p) = primeLogCriticalLaplaceFeatureL2 p
  rw [map_smul, D.evolution_prime, smul_smul, mul_comm, D.backward_exp_cancel, one_smul]

end BurnolLevyData
end RHTower
