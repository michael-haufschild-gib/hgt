import GaloisForLFunctions.RHTower.FokasLenellsCutoffComplexCauchy
import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaWeakRobinTraceNoGo

/-!
# Fixed matrix coefficients detect cutoff instability

The corpus's two-level Banach--Steinhaus theorem applies to the actual
cutoff families along the cofinal widths -k. Weak boundedness survives
exactly at zeroth order and real time. In every other case one fixed pair
of Hilbert-space vectors already has unbounded matrix coefficients.
-/

open MeasureTheory Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem negative_nat_tendsto : Tendsto (fun k : ℕ => -(k : ℝ)) atTop atBot :=
  tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop

private theorem weak_sequence_iff (T : ℝ → SoninL2 →L[ℂ] SoninL2) (n : ℕ) (τ : ℂ)
    (hn : ∀ a, ‖T a‖ = ‖cutoffComplexOperator a n τ‖) :
    (∀ u v : SoninL2, BddAbove (Set.range fun k : ℕ => ‖inner ℂ (T (-(k:ℝ)) u) v‖)) ↔
      n = 0 ∧ τ.im = 0 := by
  constructor
  · intro hw
    obtain ⟨C,_,hC⟩ := uniformlyBounded_of_weaklyPointwiseBounded (fun k : ℕ => T (-(k:ℝ))) hw
    by_contra hbad
    have ho : n ≠ 0 ∨ τ.im ≠ 0 := by simpa only [not_and_or] using hbad
    have ht : Tendsto (fun a => ‖T a‖) atBot atTop := by
      simpa only [hn] using (cutoffComplexOperator_norm_tendsto_atBot_iff n τ).2 ho
    obtain ⟨k,hk⟩ := (tendsto_atTop.1 (ht.comp negative_nat_tendsto) (C+1)).exists
    dsimp only [Function.comp_def] at hk
    linarith [hC k]
  · rintro ⟨rfl,hi⟩ u v
    refine ⟨‖u‖ * ‖v‖,?_⟩
    rintro _ ⟨k,rfl⟩
    calc
      _ ≤ ‖T (-(k:ℝ)) u‖ * ‖v‖ := norm_inner_le_norm _ _
      _ ≤ (‖T (-(k:ℝ))‖ * ‖u‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ u) (norm_nonneg v)
      _ = _ := by rw [hn,norm_cutoffComplexOperator]; simp [hi]

/-- Exact weak boundedness criterion along cofinal integer cutoff widths for the actual multipliers. -/
theorem cutoffComplexOperator_weak_sequence_bound_iff (n : ℕ) (τ : ℂ) :
    (∀ u v : SoninL2, BddAbove (Set.range fun k : ℕ =>
      ‖inner ℂ (cutoffComplexOperator (-(k:ℝ)) n τ u) v‖)) ↔ n = 0 ∧ τ.im = 0 :=
  weak_sequence_iff (fun a => cutoffComplexOperator a n τ) n τ (fun _ => rfl)

/-- Cauchy compression preserves the same exact weak boundedness criterion. -/
theorem cutoffComplexCauchyOperator_weak_sequence_bound_iff (n : ℕ) (τ : ℂ) :
    (∀ u v : SoninL2, BddAbove (Set.range fun k : ℕ =>
      ‖inner ℂ (cutoffComplexCauchyOperator (-(k:ℝ)) n τ u) v‖)) ↔ n = 0 ∧ τ.im = 0 :=
  weak_sequence_iff (fun a => cutoffComplexCauchyOperator a n τ) n τ (fun a => by
    rw [norm_cutoffComplexCauchyOperator,norm_cutoffComplexOperator])

/-- Every forbidden order or complex time has one fixed pair of vectors with unbounded coefficients. -/
theorem cutoffComplexOperator_exists_unbounded_matrixCoefficient_iff (n : ℕ) (τ : ℂ) :
    (∃ u v : SoninL2, ¬ BddAbove (Set.range fun k : ℕ =>
      ‖inner ℂ (cutoffComplexOperator (-(k:ℝ)) n τ u) v‖)) ↔ n ≠ 0 ∨ τ.im ≠ 0 := by
  simpa only [not_forall,not_and_or] using not_congr (cutoffComplexOperator_weak_sequence_bound_iff n τ)

/-- A fixed matrix-coefficient witness still detects instability after actual Cauchy compression. -/
theorem cutoffComplexCauchyOperator_exists_unbounded_matrixCoefficient_iff (n : ℕ) (τ : ℂ) :
    (∃ u v : SoninL2, ¬ BddAbove (Set.range fun k : ℕ =>
      ‖inner ℂ (cutoffComplexCauchyOperator (-(k:ℝ)) n τ u) v‖)) ↔ n ≠ 0 ∨ τ.im ≠ 0 := by
  simpa only [not_forall,not_and_or] using not_congr (cutoffComplexCauchyOperator_weak_sequence_bound_iff n τ)

end
end RHTower.FokasLenells
