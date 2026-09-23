import GaloisForLFunctions.RHTower.CCMPrimePoleFiniteCoherence
import GaloisForLFunctions.HTGeometry.ProjectionMeasurementSurvival
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Common approximate fixed vectors for finite CCM pole projections

For each positive local scale, take the closed Hilbert span of its normalized
CCM pole vectors.  Finite-place pole coherence then supplies a unit vector in a
reference pole subspace that is approximately fixed by every projection in a
finite family, with an explicit logarithmic-scale defect bound.

This is the operator form of the positive carrier law.  It uses the actual
closed spans and orthogonal projections, not a proposition-valued interface.
-/

open Set

noncomputable section

namespace RHTower

abbrev CCMPrimePoleHilbert := lp (fun _ : ℕ => ℂ) 2

def ccmPrimePoleClosedSubspace (L : ℝ) (hL : 0 < L) :
    ClosedSubmodule ℂ CCMPrimePoleHilbert :=
  (Submodule.span ℂ
    (Set.range fun n : ℤ => ccmNormalizedPrimePoleVector L hL n)).closure

theorem ccmNormalizedPrimePoleVector_mem_closedSubspace
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ccmNormalizedPrimePoleVector L hL n ∈ ccmPrimePoleClosedSubspace L hL := by
  change ccmNormalizedPrimePoleVector L hL n ∈
    (Submodule.span ℂ
      (Set.range fun m : ℤ => ccmNormalizedPrimePoleVector L hL m)).topologicalClosure
  apply subset_closure
  exact Submodule.subset_span ⟨n, rfl⟩

theorem norm_sub_ccmPrimePoleProjection_le
    {L : ℝ} (hL : 0 < L) (v : CCMPrimePoleHilbert)
    {u : CCMPrimePoleHilbert} (hu : u ∈ ccmPrimePoleClosedSubspace L hL) :
    ‖v - (ccmPrimePoleClosedSubspace L hL).starProjection v‖ ≤ ‖v - u‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
    (⟨u, hu⟩ : ccmPrimePoleClosedSubspace L hL)

set_option maxHeartbeats 1000000 in
theorem exists_fin_ccmPrimePole_projection_common_coherence
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : CCMPrimePoleHilbert, ‖v‖ = 1 ∧
      v ∈ ccmPrimePoleClosedSubspace Lref href ∧ ∀ i,
      ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection v - v‖ ^ (2 : ℕ) ≤
        2 * (2 * Real.pi * (δ / L i)) ^ (2 : ℕ) := by
  obtain ⟨n, hn, r, hcoh⟩ :=
    exists_fin_ccmPrimePole_common_coherence (δ := δ) href L hL hδ
  let v : CCMPrimePoleHilbert := ccmNormalizedPrimePoleVector Lref href n
  refine ⟨v, norm_ccmNormalizedPrimePoleVector href n,
    ccmNormalizedPrimePoleVector_mem_closedSubspace href n, ?_⟩
  intro i
  let u : CCMPrimePoleHilbert := ccmNormalizedPrimePoleVector (L i) (hL i) (r i)
  have hu : u ∈ ccmPrimePoleClosedSubspace (L i) (hL i) :=
    ccmNormalizedPrimePoleVector_mem_closedSubspace (hL i) (r i)
  have hmin :
      ‖v - (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection v‖ ≤
        ‖v - u‖ := norm_sub_ccmPrimePoleProjection_le (hL i) v hu
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hmin
  calc
    ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection v - v‖ ^ (2 : ℕ) =
        ‖v - (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection v‖ ^ (2 : ℕ) := by
      rw [norm_sub_rev]
    _ ≤ ‖v - u‖ ^ (2 : ℕ) := hsq
    _ = ‖u - v‖ ^ (2 : ℕ) := by rw [norm_sub_rev]
    _ ≤ 2 * (2 * Real.pi * (δ / L i)) ^ (2 : ℕ) := hcoh i

set_option maxHeartbeats 1000000 in
/-- The same common vector has a quantitative projective-measurement interpretation: at every
local scale, the Born probability of surviving the pole-subspace measurement is at least one
minus the existing projection-defect budget. -/
theorem exists_fin_ccmPrimePole_projection_common_born_survival
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : CCMPrimePoleHilbert, ‖v‖ = 1 ∧
      v ∈ ccmPrimePoleClosedSubspace Lref href ∧ ∀ i,
      1 - 2 * (2 * Real.pi * (δ / L i)) ^ (2 : ℕ) ≤
        Complex.re (inner ℂ v
          ((ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection v)) := by
  obtain ⟨v, hv, hvref, hdefect⟩ :=
    exists_fin_ccmPrimePole_projection_common_coherence (δ := δ) href L hL hδ
  refine ⟨v, hv, hvref, fun i => ?_⟩
  change 1 - 2 * (2 * Real.pi * (δ / L i)) ^ (2 : ℕ) ≤
    RCLike.re (inner ℂ v
      ((ccmPrimePoleClosedSubspace (L i) (hL i) :
        Submodule ℂ CCMPrimePoleHilbert).starProjection v))
  rw [HTGeometry.bornSurvivalProbability_eq_one_sub_projectionDefectSq
    (S := (ccmPrimePoleClosedSubspace (L i) (hL i) :
      Submodule ℂ CCMPrimePoleHilbert)) v hv]
  exact sub_le_sub_left (hdefect i) 1

set_option maxHeartbeats 1000000 in
/-- Cofinal operator coherence: the common approximate fixed unit vector may
be chosen with reference pole index beyond any prescribed bound. -/
theorem exists_fin_ccmPrimePole_projection_cofinal_common_coherence
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    {δ : ℝ} (hδ : 0 < δ) (B : ℕ) :
    ∃ n : ℕ, B < n ∧
      ‖ccmNormalizedPrimePoleVector Lref href n‖ = 1 ∧
      ccmNormalizedPrimePoleVector Lref href n ∈
        ccmPrimePoleClosedSubspace Lref href ∧ ∀ i,
      ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection
          (ccmNormalizedPrimePoleVector Lref href n) -
        ccmNormalizedPrimePoleVector Lref href n‖ ^ (2 : ℕ) ≤
        2 * (2 * Real.pi * (δ / L i)) ^ (2 : ℕ) := by
  obtain ⟨n, hn, r, hcoh⟩ :=
    exists_fin_ccmPrimePole_cofinal_common_coherence (δ := δ) href L hL hδ B
  let v : CCMPrimePoleHilbert := ccmNormalizedPrimePoleVector Lref href n
  refine ⟨n, hn, norm_ccmNormalizedPrimePoleVector href n,
    ccmNormalizedPrimePoleVector_mem_closedSubspace href n, ?_⟩
  intro i
  let u : CCMPrimePoleHilbert := ccmNormalizedPrimePoleVector (L i) (hL i) (r i)
  have hu : u ∈ ccmPrimePoleClosedSubspace (L i) (hL i) :=
    ccmNormalizedPrimePoleVector_mem_closedSubspace (hL i) (r i)
  have hmin :
      ‖v - (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection v‖ ≤
        ‖v - u‖ := norm_sub_ccmPrimePoleProjection_le (hL i) v hu
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hmin
  calc
    ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection
          (ccmNormalizedPrimePoleVector Lref href n) -
        ccmNormalizedPrimePoleVector Lref href n‖ ^ (2 : ℕ) =
        ‖v - (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection v‖ ^ (2 : ℕ) := by
      rw [norm_sub_rev]
    _ ≤ ‖v - u‖ ^ (2 : ℕ) := hsq
    _ = ‖u - v‖ ^ (2 : ℕ) := by rw [norm_sub_rev]
    _ ≤ 2 * (2 * Real.pi * (δ / L i)) ^ (2 : ℕ) := hcoh i

set_option maxHeartbeats 1000000 in
/-- Cofinal Born survival: the high-index pole witness may be chosen beyond every prescribed
bound while retaining the same lossless survival-probability estimate at all finite scales. -/
theorem exists_fin_ccmPrimePole_projection_cofinal_common_born_survival
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    {δ : ℝ} (hδ : 0 < δ) (B : ℕ) :
    ∃ n : ℕ, B < n ∧
      ‖ccmNormalizedPrimePoleVector Lref href n‖ = 1 ∧
      ccmNormalizedPrimePoleVector Lref href n ∈
        ccmPrimePoleClosedSubspace Lref href ∧ ∀ i,
      1 - 2 * (2 * Real.pi * (δ / L i)) ^ (2 : ℕ) ≤
        Complex.re (inner ℂ (ccmNormalizedPrimePoleVector Lref href n)
          ((ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection
            (ccmNormalizedPrimePoleVector Lref href n))) := by
  obtain ⟨n, hn, hv, hvref, hdefect⟩ :=
    exists_fin_ccmPrimePole_projection_cofinal_common_coherence
      (δ := δ) href L hL hδ B
  refine ⟨n, hn, hv, hvref, fun i => ?_⟩
  change 1 - 2 * (2 * Real.pi * (δ / L i)) ^ (2 : ℕ) ≤
    RCLike.re (inner ℂ (ccmNormalizedPrimePoleVector Lref href n)
      ((ccmPrimePoleClosedSubspace (L i) (hL i) :
        Submodule ℂ CCMPrimePoleHilbert).starProjection
          (ccmNormalizedPrimePoleVector Lref href n)))
  rw [HTGeometry.bornSurvivalProbability_eq_one_sub_projectionDefectSq
    (S := (ccmPrimePoleClosedSubspace (L i) (hL i) :
      Submodule ℂ CCMPrimePoleHilbert))
    (ccmNormalizedPrimePoleVector Lref href n) hv]
  exact sub_le_sub_left (hdefect i) 1

set_option maxHeartbeats 1000000 in
/-- Prime specialization: every finite family of CCM prime-local pole
projections has a common unit vector with arbitrarily small explicitly bounded
projection defects. -/
theorem exists_fin_prime_ccmPrimePole_projection_common_coherence
    {d pref : ℕ} (hpref : pref.Prime)
    (p : Fin d → ℕ) (hp : ∀ i, (p i).Prime)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : CCMPrimePoleHilbert, ‖v‖ = 1 ∧
      v ∈ ccmPrimePoleClosedSubspace (Real.log pref)
        (Real.log_pos (by exact_mod_cast hpref.one_lt)) ∧ ∀ i,
      ‖(ccmPrimePoleClosedSubspace (Real.log (p i))
          (Real.log_pos (by exact_mod_cast (hp i).one_lt))).starProjection v - v‖ ^ (2 : ℕ) ≤
        2 * (2 * Real.pi * (δ / Real.log (p i))) ^ (2 : ℕ) := by
  exact exists_fin_ccmPrimePole_projection_common_coherence
    (δ := δ)
    (Real.log_pos (by exact_mod_cast hpref.one_lt))
    (fun i => Real.log (p i))
    (fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)) hδ

set_option maxHeartbeats 1000000 in
/-- Prime specialization of the common Born-survival estimate. -/
theorem exists_fin_prime_ccmPrimePole_projection_common_born_survival
    {d pref : ℕ} (hpref : pref.Prime)
    (p : Fin d → ℕ) (hp : ∀ i, (p i).Prime)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : CCMPrimePoleHilbert, ‖v‖ = 1 ∧
      v ∈ ccmPrimePoleClosedSubspace (Real.log pref)
        (Real.log_pos (by exact_mod_cast hpref.one_lt)) ∧ ∀ i,
      1 - 2 * (2 * Real.pi * (δ / Real.log (p i))) ^ (2 : ℕ) ≤
        Complex.re (inner ℂ v
          ((ccmPrimePoleClosedSubspace (Real.log (p i))
            (Real.log_pos (by exact_mod_cast (hp i).one_lt))).starProjection v)) := by
  exact exists_fin_ccmPrimePole_projection_common_born_survival
    (δ := δ)
    (Real.log_pos (by exact_mod_cast hpref.one_lt))
    (fun i => Real.log (p i))
    (fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)) hδ

end RHTower
