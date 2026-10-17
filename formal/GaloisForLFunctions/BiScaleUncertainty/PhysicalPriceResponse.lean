import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarDualPrices

/-!
# Attained physical response to bounded measurable prices

The active minimum is realized by sharing equally among all active minimizers.
This construction provides actual physical partitions, including tied prices,
and exact transport of their linear costs. Analytic bounds are proved from the
physical partition and the bounded price function.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

structure CollarPrice where
  value : ℕ → ℝ → ℝ
  measurable_value : ∀ k, Measurable (value k)
  bounds : ∀ k x, 0 ≤ value k x ∧ value k x ≤ 1

namespace CollarPrice
open PhysicalCollarPartition
variable {n : ℕ}

def masked (Q : CollarPrice) (n k : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ logarithmicPhysicalCollar n k then Q.value k x else 1

theorem measurable_masked (Q : CollarPrice) (n k : ℕ) : Measurable (Q.masked n k) := by
  classical
  exact Measurable.ite (measurableSet_Ioo.inter measurableSet_Ioo)
    (Q.measurable_value k) measurable_const

private theorem measurable_min (F : ℕ → ℝ → ℝ) (hF : ∀ k, Measurable (F k)) (r : ℕ) :
    Measurable fun x => (Finset.range (r + 1)).inf' (by exact ⟨0, by simp⟩) (fun k => F k x) := by
  induction r with
  | zero => simpa using hF 0
  | succ r ih =>
    simp only [Finset.range_add_one (n := r + 1)]
    simp only [Finset.inf'_insert (show (Finset.range (r + 1)).Nonempty from ⟨0, by simp⟩)]
    exact (hF (r + 1)).min ih

def floor (Q : CollarPrice) (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).inf' (by exact ⟨0, by simp⟩) (fun k => Q.masked n k x)

theorem measurable_floor (Q : CollarPrice) (n : ℕ) : Measurable (Q.floor n) :=
  measurable_min (Q.masked n) (Q.measurable_masked n) n

theorem floor_le_active (Q : CollarPrice) (k : ℕ) (hk : k ∈ Finset.range (n + 1))
    {x : ℝ} (hx : x ∈ logarithmicPhysicalCollar n k) : Q.floor n x ≤ Q.value k x := by
  have h := Finset.inf'_le (fun k => Q.masked n k x) hk
  change Q.floor n x ≤ Q.masked n k x at h
  simpa only [masked, if_pos hx] using h

theorem floor_eq_active_inf (Q : CollarPrice) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    Q.floor n x = (activeNodes n x).inf' (activeNodes_nonempty hx) (fun k => Q.value k x) := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro k hk
    exact Q.floor_le_active k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2
  · apply Finset.le_inf'
    intro k hk
    unfold masked
    split_ifs with hxk
    · exact Finset.inf'_le (fun k => Q.value k x) (Finset.mem_filter.mpr ⟨hk, hxk⟩)
    · obtain ⟨j, hj⟩ := activeNodes_nonempty hx
      exact (Finset.inf'_le (fun k => Q.value k x) hj).trans (Q.bounds j x).2

def minimizerCell (Q : CollarPrice) (n k : ℕ) : Set ℝ :=
  {x | k ∈ Finset.range (n + 1) ∧ x ∈ logarithmicPhysicalCollar n k ∧ Q.value k x = Q.floor n x}

theorem measurableSet_minimizerCell (Q : CollarPrice) (n k : ℕ) :
    MeasurableSet (Q.minimizerCell n k) := by
  classical
  by_cases hk : k ∈ Finset.range (n + 1)
  · have he : Q.minimizerCell n k = logarithmicPhysicalCollar n k ∩
        {x | Q.value k x = Q.floor n x} := by
      ext x
      simp only [minimizerCell, mem_setOf_eq, mem_inter_iff, hk, true_and]
    rw [he]
    exact (measurableSet_Ioo.inter measurableSet_Ioo).inter
      (measurableSet_eq_fun (Q.measurable_value k) (Q.measurable_floor n))
  · simp [minimizerCell, hk]

theorem minimizerCell_exists (Q : CollarPrice) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    ∃ k, x ∈ Q.minimizerCell n k := by
  classical
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_inf' (activeNodes_nonempty hx) (fun k => Q.value k x)
  exact ⟨k, (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2,
    ((Q.floor_eq_active_inf hx).trans he).symm⟩

theorem minimizerCell_union (Q : CollarPrice) (n : ℕ) :
    (⋃ k ∈ Finset.range (n + 1), Q.minimizerCell n k) =
      Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, hc⟩ : ∃ k ∈ Finset.range (n + 1), x ∈ Q.minimizerCell n k := by
      simpa only [mem_iUnion, exists_prop] using hx
    have hu := truncated_logarithmic_collar_union n
    change (⋃ k ∈ Finset.range (n + 1), logarithmicPhysicalCollar n k) =
      Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) at hu
    rw [← hu]
    simp only [mem_iUnion]
    exact ⟨k, hk, hc.2.1⟩
  · intro hx
    obtain ⟨k, hk⟩ := Q.minimizerCell_exists hx
    simp only [mem_iUnion]
    exact ⟨k, hk.1, hk⟩

/-- Equal sharing among actual active minimizers gives a measurable response. -/
def minimumResponse (Q : CollarPrice) (n : ℕ) : PhysicalCollarPartition n where
  share := collarPhysicalShare (Finset.range (n + 1)) (Q.minimizerCell n)
  measurable_share := by
    intro k
    exact (measurable_const.indicator (Q.measurableSet_minimizerCell n k)).div
      ((Finset.range (n + 1)).measurable_sum fun j _ =>
        measurable_const.indicator (Q.measurableSet_minimizerCell n j))
  nonneg := collarPhysicalShare_nonneg _ _
  supported := by
    intro k x hx
    have hc : x ∉ Q.minimizerCell n k := fun h => hx h.2.1
    simp only [collarPhysicalShare, indicator_of_notMem hc, zero_div]
  partition := by
    intro x
    rw [collarPhysicalShare_partition, Q.minimizerCell_union n]

theorem minimumResponse_price (Q : CollarPrice) (k : ℕ) (x : ℝ)
    (h : (Q.minimumResponse n).share k x ≠ 0) : Q.value k x = Q.floor n x := by
  by_contra he
  have hc : x ∉ Q.minimizerCell n k := fun hx => he hx.2.2
  apply h
  change collarPhysicalShare _ _ k x = 0
  simp only [collarPhysicalShare, indicator_of_notMem hc, zero_div]

def physicalCost (Q : CollarPrice) (ρ : PhysicalCollarPartition n) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ρ.density k x * Q.value k x

def linearCost (Q : CollarPrice) (ρ : PhysicalCollarPartition n) : ℝ :=
  ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), Q.physicalCost ρ x

theorem integrable_physicalCost (Q : CollarPrice) (ρ : PhysicalCollarPartition n) :
    Integrable (Q.physicalCost ρ) :=
  integrable_finsetSum _ fun k hk =>
    ρ.integrable_density_mul k hk (Q.value k) (Q.measurable_value k) (Q.bounds k)

theorem physicalCost_lower (Q : CollarPrice) (ρ : PhysicalCollarPartition n) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    archLevySinhWeight x * Q.floor n x ≤ Q.physicalCost ρ x := by
  have hm : (∑ k ∈ Finset.range (n + 1), ρ.density k x) = archLevySinhWeight x := by
    simp only [density, ← Finset.sum_mul, ρ.partition, indicator_of_mem hx, one_mul]
  rw [← hm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hc : x ∈ logarithmicPhysicalCollar n k
  · exact mul_le_mul_of_nonneg_left (Q.floor_le_active k hk hc) (ρ.density_nonneg k x)
  · simp [density, ρ.supported k x hc]

theorem physicalCost_minimumResponse (Q : CollarPrice) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    Q.physicalCost (Q.minimumResponse n) x = archLevySinhWeight x * Q.floor n x := by
  have hm : (∑ k ∈ Finset.range (n + 1), (Q.minimumResponse n).density k x) =
      archLevySinhWeight x := by
    simp only [density, ← Finset.sum_mul, (Q.minimumResponse n).partition, indicator_of_mem hx, one_mul]
  rw [← hm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hz : (Q.minimumResponse n).share k x = 0
  · simp [density, hz]
  · rw [Q.minimumResponse_price k x hz]

theorem linearCost_minimumResponse_le (Q : CollarPrice) (ρ : PhysicalCollarPartition n) :
    Q.linearCost (Q.minimumResponse n) ≤ Q.linearCost ρ := by
  apply integral_mono_ae (Q.integrable_physicalCost (Q.minimumResponse n)).integrableOn
    (Q.integrable_physicalCost ρ).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Q.physicalCost_minimumResponse hx]
  exact Q.physicalCost_lower ρ hx

def fibreCost (Q : CollarPrice) (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (ρ.weight false k y * Q.value k (logarithmicCollarNode k - y) +
      ρ.weight true k y * Q.value k (logarithmicCollarNode k + y))

theorem integrableOn_weight_price (Q : CollarPrice) (ρ : PhysicalCollarPartition n)
    (σ : Bool) (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
    IntegrableOn (fun y => ρ.weight σ k y *
      Q.value k (logarithmicCollarNode k + collarSignedOffset σ y)) (Ioo 0 logarithmicCollarRadius) := by
  have hQ : Measurable (fun y => Q.value k (logarithmicCollarNode k + collarSignedOffset σ y)) := by
    apply (Q.measurable_value k).comp
    cases σ <;> simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  apply volume.integrableOn_of_bounded (M := logarithmicCollarWeightBound n)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    ((ρ.measurable_weight σ k).mul hQ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖ρ.weight σ k y * Q.value k _‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ρ.weight_nonneg σ k y) (Q.bounds k _).1)]
    exact (mul_le_of_le_one_right (ρ.weight_nonneg σ k y) (Q.bounds k _).2).trans
      (ρ.weight_le_bound σ k hk y)

theorem integrableOn_fibreCost (Q : CollarPrice) (ρ : PhysicalCollarPartition n) :
    IntegrableOn (Q.fibreCost ρ) (Ioo 0 logarithmicCollarRadius) := by
  apply integrable_finsetSum
  intro k hk
  have h := (Q.integrableOn_weight_price ρ false k hk).add (Q.integrableOn_weight_price ρ true k hk)
  simpa only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg, Pi.add_apply] using h

theorem integral_fibreCost (Q : CollarPrice) (ρ : PhysicalCollarPartition n) :
    (∫ y in Ioo 0 logarithmicCollarRadius, Q.fibreCost ρ y) = Q.linearCost ρ := by
  have hi (σ : Bool) (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :=
    Q.integrableOn_weight_price ρ σ k hk
  simp only [collarSignedOffset] at hi
  unfold fibreCost
  rw [integral_finsetSum (Finset.range (n + 1))
    (f := fun k y => ρ.weight false k y * Q.value k (logarithmicCollarNode k - y) +
      ρ.weight true k y * Q.value k (logarithmicCollarNode k + y)) (fun k hk => (hi false k hk).add (hi true k hk))]
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        ((∫ y in Ioo 0 logarithmicCollarRadius, ρ.weight false k y * Q.value k (logarithmicCollarNode k - y)) +
          ∫ y in Ioo 0 logarithmicCollarRadius, ρ.weight true k y * Q.value k (logarithmicCollarNode k + y)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact integral_add (hi false k hk) (hi true k hk)
    _ = _ := ρ.integral_signed_cost_transport Q.value Q.measurable_value (fun k _ => Q.bounds k)

end CollarPrice
end
end GaloisForLFunctions.BiScaleUncertainty
