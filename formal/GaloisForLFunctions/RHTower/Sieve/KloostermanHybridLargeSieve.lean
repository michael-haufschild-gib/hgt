import GaloisForLFunctions.RHTower.Sieve.KloostermanBilinear
import GaloisForLFunctions.RHTower.Sieve.FareyHybridLargeSieve

/-!
# Kloosterman hybrid large sieve

Apply the complete finite Kloosterman transform at every physical Dirichlet height.  Its finite
operator bound and the additive hybrid large sieve give an unconditional integrated receiver
estimate.  This is the finite Kloosterman layer needed before the still-separate spectral average
over moduli in the Deshouillers--Iwaniec estimate.
-/

open Complex MeasureTheory Set Finset

noncomputable section

namespace RHTower.Sieve

/-- The physical-height additive Dirichlet polynomial is continuous. -/
theorem continuous_additiveHybridDirichletPoly (q N : ℕ) (a : ℕ → ℂ)
    (d : ZMod (q + 1)) :
    Continuous (additiveHybridDirichletPoly q N a d) := by
  unfold additiveHybridDirichletPoly
  exact (continuous_additiveHybridLogPoly q N a d).comp (by fun_prop)

/-- Complete Kloosterman transform of the additive hybrid coefficient vector at height `t`. -/
def kloostermanHybridTransform (q N : ℕ) (a : ℕ → ℂ)
    (n : ZMod (q + 1)) (t : ℝ) : ℂ :=
  kloostermanTransform (q + 1)
    (fun d : ZMod (q + 1) => additiveHybridDirichletPoly q N a d t) n

/-- The Kloosterman hybrid transform is continuous in physical height. -/
theorem continuous_kloostermanHybridTransform (q N : ℕ) (a : ℕ → ℂ)
    (n : ZMod (q + 1)) :
    Continuous (kloostermanHybridTransform q N a n) := by
  unfold kloostermanHybridTransform kloostermanTransform
  refine continuous_finsetSum _ fun d _ => ?_
  exact (continuous_additiveHybridDirichletPoly q N a d).mul_const _

/-- Integrated Kloosterman-transform energy is controlled by the physical-height additive hybrid
large sieve. -/
theorem sum_integral_normSq_kloostermanHybridTransform_le
    (q N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    ∑ n : ZMod (q + 1),
        (∫ t in Set.Icc (-T) T,
          ‖kloostermanHybridTransform q N a n t‖ ^ (2 : ℕ)) ≤
      ((q + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
        (5 * Real.pi * Real.exp 1 * (N : ℝ) +
          5 * Real.pi * ((q + 1 : ℕ) : ℝ) * T) *
        ∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ (2 : ℕ) := by
  let I : Set ℝ := Set.Icc (-T) T
  letI : NeZero (q + 1) := ⟨by omega⟩
  have hout : ∀ n : ZMod (q + 1),
      Integrable (fun t => ‖kloostermanHybridTransform q N a n t‖ ^ (2 : ℕ))
        (volume.restrict I) := by
    intro n
    exact (continuous_kloostermanHybridTransform q N a n).norm.pow 2 |>.integrableOn_Icc
  have hin : ∀ d : ZMod (q + 1),
      Integrable (fun t => ‖additiveHybridDirichletPoly q N a d t‖ ^ (2 : ℕ))
        (volume.restrict I) := by
    intro d
    exact (continuous_additiveHybridDirichletPoly q N a d).norm.pow 2 |>.integrableOn_Icc
  have houtSum :
      Integrable (fun t => ∑ n : ZMod (q + 1),
        ‖kloostermanHybridTransform q N a n t‖ ^ (2 : ℕ))
        (volume.restrict I) := by
    have hc : Continuous (fun t => ∑ n : ZMod (q + 1),
        ‖kloostermanHybridTransform q N a n t‖ ^ (2 : ℕ)) := by
      exact continuous_finsetSum _ fun n _ =>
        (continuous_kloostermanHybridTransform q N a n).norm.pow 2
    exact hc.integrableOn_Icc
  have hinSum :
      Integrable (fun t => ((q + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
        ∑ d : ZMod (q + 1), ‖additiveHybridDirichletPoly q N a d t‖ ^ (2 : ℕ))
        (volume.restrict I) := by
    have hc : Continuous (fun t => ((q + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
        ∑ d : ZMod (q + 1), ‖additiveHybridDirichletPoly q N a d t‖ ^ (2 : ℕ)) := by
      exact continuous_const.mul <| continuous_finsetSum _ fun d _ =>
        (continuous_additiveHybridDirichletPoly q N a d).norm.pow 2
    exact hc.integrableOn_Icc
  have hpoint : ∀ t : ℝ,
      (∑ n : ZMod (q + 1), ‖kloostermanHybridTransform q N a n t‖ ^ (2 : ℕ)) ≤
        ((q + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
          ∑ d : ZMod (q + 1), ‖additiveHybridDirichletPoly q N a d t‖ ^ (2 : ℕ) := by
    intro t
    simpa only [kloostermanHybridTransform] using
      sum_norm_kloostermanTransform_sq_le (q + 1)
        (fun d : ZMod (q + 1) => additiveHybridDirichletPoly q N a d t)
  have hmono :
      (∫ t in I, ∑ n : ZMod (q + 1),
          ‖kloostermanHybridTransform q N a n t‖ ^ (2 : ℕ)) ≤
        ∫ t in I, ((q + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
          ∑ d : ZMod (q + 1), ‖additiveHybridDirichletPoly q N a d t‖ ^ (2 : ℕ) :=
    MeasureTheory.integral_mono houtSum hinSum hpoint
  have hbase := sum_integral_additiveHybridDirichletPoly_le_length q N a hT
  calc
    _ = ∫ t in I, ∑ n : ZMod (q + 1),
        ‖kloostermanHybridTransform q N a n t‖ ^ (2 : ℕ) := by
      rw [MeasureTheory.integral_finsetSum Finset.univ (fun n _ => hout n)]
    _ ≤ ∫ t in I, ((q + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
        ∑ d : ZMod (q + 1), ‖additiveHybridDirichletPoly q N a d t‖ ^ (2 : ℕ) := hmono
    _ = ((q + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
        ∑ d : ZMod (q + 1),
          (∫ t in I, ‖additiveHybridDirichletPoly q N a d t‖ ^ (2 : ℕ)) := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finsetSum Finset.univ (fun d _ => hin d)]
    _ ≤ ((q + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
        ((5 * Real.pi * Real.exp 1 * (N : ℝ) +
            5 * Real.pi * ((q + 1 : ℕ) : ℝ) * T) *
          ∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = _ := by ring

end RHTower.Sieve
