import GaloisForLFunctions.HTGeometry.ReturnExcisedCollisionBoundedIncidence

/-!
# Circuit counting against a bounded spectral collision

At a replica order below the reciprocal collision scale the replica factor `r!` is beaten by the
`r`-th power, so the return-excised complete-target bound becomes the number of targets times
`2^{-r}`.  A dictionary of at most `M^{s+1}` targets whose logarithm is below half the replica
order then leaves `2^{-r/2}`.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance circuitCountingCollisionBoundMeasureSpace :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance circuitCountingCollisionBoundIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance circuitCountingCollisionBoundIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

section Arithmetic

/-- **The replica factor is beaten below the reciprocal collision scale.** -/
theorem factorial_mul_pow_le_two_pow_neg (r : ℕ) (hr : 1 ≤ r) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (2 * r)) : (r.factorial : ℝ) * x ^ r ≤ (1 / 2 : ℝ) ^ r := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hstep : x ^ r ≤ (1 / (2 * (r : ℝ))) ^ r := pow_le_pow_left₀ hx0 hx r
  have hfact : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
  have hprod : ((r : ℝ)) ^ r * (1 / (2 * (r : ℝ))) ^ r = (1 / 2 : ℝ) ^ r := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc (r.factorial : ℝ) * x ^ r
      ≤ ((r : ℝ)) ^ r * (1 / (2 * (r : ℝ))) ^ r := by
        refine mul_le_mul hfact hstep (by positivity) (by positivity)
    _ = (1 / 2 : ℝ) ^ r := hprod

/-- **A dictionary whose logarithm is below half the replica order leaves `2^{-r/2}`.** -/
theorem card_mul_two_pow_le_rpow {N M : ℝ} (_hN : 0 ≤ N) {s r : ℕ} (hM : 1 < M)
    (hNle : N ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    N * (1 / 2 : ℝ) ^ r ≤ (2 : ℝ) ^ (-((r : ℝ) / 2)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hMpos : (0 : ℝ) < M := lt_trans one_pos hM
  have hpowpos : (0 : ℝ) < M ^ (s + 1) := by positivity
  have hhalf : ((1 : ℝ) / 2) ^ r = (2 : ℝ) ^ (-(r : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  have hlog : Real.log (M ^ (s + 1)) ≤ Real.log ((2 : ℝ) ^ ((r : ℝ) / 2)) := by
    rw [Real.log_pow, Real.log_rpow h2]
    push_cast
    linarith
  have hMle : M ^ (s + 1) ≤ (2 : ℝ) ^ ((r : ℝ) / 2) :=
    (Real.log_le_log_iff hpowpos (by positivity)).mp hlog
  calc N * (1 / 2 : ℝ) ^ r ≤ M ^ (s + 1) * (1 / 2 : ℝ) ^ r := by
        refine mul_le_mul_of_nonneg_right hNle (by positivity)
    _ ≤ (2 : ℝ) ^ ((r : ℝ) / 2) * (2 : ℝ) ^ (-(r : ℝ)) := by
        rw [hhalf]
        exact mul_le_mul_of_nonneg_right hMle (by positivity)
    _ = (2 : ℝ) ^ (-((r : ℝ) / 2)) := by
        rw [← Real.rpow_add h2]
        congr 1
        ring

end Arithmetic

section Incidence

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {C : Type*} [Fintype C] [Nonempty C]

theorem finrank_replicaTargetSpan_le_card (r : ℕ) (target : C → d → ℂ) :
    Module.finrank ℂ (replicaTargetSpan r target) ≤ Fintype.card C := by
  classical
  rw [replicaTargetSpan]
  refine le_trans (finrank_span_le_card _) ?_
  rw [Set.toFinset_range]
  exact le_trans Finset.card_image_le (le_of_eq Finset.card_univ)

/-- **The complete-target bound at a replica order below the reciprocal collision scale.** -/
theorem measureReal_capture_le_return_add_card_mul_two_pow
    {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (d → ℂ)) (hz : ∀ c, finiteComplexInner (z c) (z c) = 1)
    (hznorm : ∀ c, ∑ j, ‖z c j‖ ^ 2 ≤ 1)
    {R Q : Set (d → ℝ)} (hR : MeasurableSet R)
    (hcap : ∀ x ∈ Q \ R, ∃ c, a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) (z c))
    {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hcoll : occupationCollision p ≤ c₀)
    (hscale : 16 * c₀ / a ^ 2 ≤ 1 / (2 * r)) :
    (volume.restrict (torusBox d)).real Q ≤
      (volume.restrict (torusBox d)).real R +
        (Fintype.card C : ℝ) * (1 / 2 : ℝ) ^ r := by
  classical
  have hbase := measureReal_capture_le_return_add_replicaMoment_of_collision_le hp hpsum ha z hz
    hznorm hR hcap r hcoll
  refine le_trans hbase (add_le_add le_rfl ?_)
  have hx0 : (0 : ℝ) ≤ 16 * c₀ / a ^ 2 := by positivity
  have hkey : (r.factorial : ℝ) * (16 * c₀ / a ^ 2) ^ r ≤ (1 / 2 : ℝ) ^ r :=
    factorial_mul_pow_le_two_pow_neg r hr hx0 hscale
  have hrank : (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) ≤ (Fintype.card C : ℝ) := by
    exact_mod_cast finrank_replicaTargetSpan_le_card r z
  have hnn : (0 : ℝ) ≤ (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) := by positivity
  calc (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * c₀ / a ^ 2) ^ r
      = (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) *
        ((r.factorial : ℝ) * (16 * c₀ / a ^ 2) ^ r) := by ring
    _ ≤ (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (1 / 2 : ℝ) ^ r :=
        mul_le_mul_of_nonneg_left hkey hnn
    _ ≤ (Fintype.card C : ℝ) * (1 / 2 : ℝ) ^ r :=
        mul_le_mul_of_nonneg_right hrank (by positivity)

/-- **The finite-alphabet circuit consequence.**  A target dictionary of at most `M^{s+1}` states
whose logarithm is below half the replica order leaves `2^{-r/2}` above the return density. -/
theorem measureReal_capture_le_return_add_two_rpow
    {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (d → ℂ)) (hz : ∀ c, finiteComplexInner (z c) (z c) = 1)
    (hznorm : ∀ c, ∑ j, ‖z c j‖ ^ 2 ≤ 1)
    {R Q : Set (d → ℝ)} (hR : MeasurableSet R)
    (hcap : ∀ x ∈ Q \ R, ∃ c, a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) (z c))
    {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hcoll : occupationCollision p ≤ c₀)
    (hscale : 16 * c₀ / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    (volume.restrict (torusBox d)).real Q ≤
      (volume.restrict (torusBox d)).real R + (2 : ℝ) ^ (-((r : ℝ) / 2)) := by
  refine le_trans (measureReal_capture_le_return_add_card_mul_two_pow hp hpsum ha z hz hznorm hR
    hcap hr hc₀ hcoll hscale) (add_le_add le_rfl ?_)
  exact card_mul_two_pow_le_rpow (by positivity) hM hcard hs

end Incidence

end GaloisForLFunctions.HTGeometry
