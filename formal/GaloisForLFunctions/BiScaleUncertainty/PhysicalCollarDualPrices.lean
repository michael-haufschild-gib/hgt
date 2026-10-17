import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition

/-!
# Physical marginal prices and exact dual-cost transport

The canonical fibre prices are pulled back to each physical point using its signed distance
from the node. The resulting measurable bounded prices transport the finite-block dual pairing
exactly. Their measurable finite minimum is proved equal to the minimum over active collars.
All integrability statements follow from physical admissibility and the verified price bounds.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
namespace PhysicalCollarPartition
variable {n : ℕ}

def dualSlope (ρ : PhysicalCollarPartition n) (j : ℕ × Bool) (k : ℕ) (y : ℝ) : ℝ :=
  collarDualSlope (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => ρ.weight j.2 k y) (archLevySinhWeight y) j k

theorem measurable_dualSlope (ρ : PhysicalCollarPartition n) (j : ℕ × Bool) (k : ℕ) :
    Measurable (ρ.dualSlope j k) :=
  measurable_collarDualSlope (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun y j k => ρ.weight j.2 k y) archLevySinhWeight
    (fun j k => ρ.measurable_weight j.2 k) measurable_archLevySinhWeight j k

theorem dualSlope_nonneg (ρ : PhysicalCollarPartition n) (j : ℕ × Bool) (k : ℕ) (y : ℝ) :
    0 ≤ ρ.dualSlope j k y :=
  collarDualSlope_nonneg _ _ _ _ _ _ (ρ.weight_nonneg j.2 k y)

theorem dualSlope_le_one (ρ : PhysicalCollarPartition n) (j : ℕ × Bool) (k : ℕ)
    (hk : k ∈ logarithmicCosetNodes n j.1) (y : ℝ) : ρ.dualSlope j k y ≤ 1 := by
  let M := logarithmicSignedCosets n
  let s := fun j : ℕ × Bool => logarithmicCosetNodes n j.1
  let a := fun (j : ℕ × Bool) k => ρ.weight j.2 k y
  apply (collarDualSlope_le_radius M s a (archLevySinhWeight y) j k hk).trans
  apply div_le_one_of_le₀ _ (Real.sqrt_nonneg _)
  exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))

theorem node_mem_own_coset (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
    k ∈ logarithmicCosetNodes n (logNodeOddPart k) := by
  simp [logarithmicCosetNodes, hk]

/-- Marginal prices compared at one physical point, using its actual offset from each node. -/
def physicalPrice (ρ : PhysicalCollarPartition n) (k : ℕ) (x : ℝ) : ℝ :=
  if x < logarithmicCollarNode k then
    ρ.dualSlope (logNodeOddPart k, false) k (logarithmicCollarNode k - x)
  else ρ.dualSlope (logNodeOddPart k, true) k (x - logarithmicCollarNode k)

theorem measurable_physicalPrice (ρ : PhysicalCollarPartition n) (k : ℕ) :
    Measurable (ρ.physicalPrice k) := by
  exact Measurable.ite measurableSet_Iio
    ((ρ.measurable_dualSlope (logNodeOddPart k, false) k).comp (measurable_const.sub measurable_id))
    ((ρ.measurable_dualSlope (logNodeOddPart k, true) k).comp (measurable_id.sub measurable_const))

theorem physicalPrice_bounds (ρ : PhysicalCollarPartition n) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (x : ℝ) :
    0 ≤ ρ.physicalPrice k x ∧ ρ.physicalPrice k x ≤ 1 := by
  unfold physicalPrice
  split_ifs <;> exact ⟨ρ.dualSlope_nonneg _ _ _, ρ.dualSlope_le_one _ _ (node_mem_own_coset k hk) _⟩

theorem physicalPrice_left (ρ : PhysicalCollarPartition n) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    ρ.physicalPrice k (logarithmicCollarNode k - y) = ρ.dualSlope (logNodeOddPart k, false) k y := by
  unfold physicalPrice
  rw [if_pos (by linarith)]
  congr 1
  ring

theorem physicalPrice_right (ρ : PhysicalCollarPartition n) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    ρ.physicalPrice k (logarithmicCollarNode k + y) = ρ.dualSlope (logNodeOddPart k, true) k y := by
  unfold physicalPrice
  rw [if_neg (by linarith)]
  congr 1
  ring

def fibreCost (ρ η : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (η.weight false k y * ρ.dualSlope (logNodeOddPart k, false) k y +
      η.weight true k y * ρ.dualSlope (logNodeOddPart k, true) k y)

def physicalCost (ρ η : PhysicalCollarPartition n) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), η.density k x * ρ.physicalPrice k x

theorem fibreCost_eq_signed_sum (ρ η : PhysicalCollarPartition n) (y : ℝ) :
    ρ.fibreCost η y = ∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1,
      η.weight j.2 k y * ρ.dualSlope j k y := by
  symm
  calc
    _ = ∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1,
        η.weight j.2 k y * ρ.dualSlope (logNodeOddPart k, j.2) k y := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    _ = _ := sum_logarithmicSignedCosets n
      (fun σ k => η.weight σ k y * ρ.dualSlope (logNodeOddPart k, σ) k y)

theorem integrableOn_weight_mul_dualSlope (ρ η : PhysicalCollarPartition n)
    (σ : Bool) (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
    IntegrableOn (fun y => η.weight σ k y * ρ.dualSlope (logNodeOddPart k, σ) k y)
      (Ioo 0 logarithmicCollarRadius) := by
  apply volume.integrableOn_of_bounded (M := logarithmicCollarWeightBound n)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    ((η.measurable_weight σ k).mul (ρ.measurable_dualSlope (logNodeOddPart k, σ) k)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖η.weight σ k y * ρ.dualSlope (logNodeOddPart k, σ) k y‖ ≤ logarithmicCollarWeightBound n
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (η.weight_nonneg σ k y) (ρ.dualSlope_nonneg _ _ _))]
    exact (mul_le_of_le_one_right (η.weight_nonneg σ k y)
      (ρ.dualSlope_le_one _ _ (node_mem_own_coset k hk) y)).trans (η.weight_le_bound σ k hk y)

theorem integrableOn_fibreCost (ρ η : PhysicalCollarPartition n) :
    IntegrableOn (ρ.fibreCost η) (Ioo 0 logarithmicCollarRadius) := by
  exact integrable_finsetSum _ fun k hk =>
    (ρ.integrableOn_weight_mul_dualSlope η false k hk).add
      (ρ.integrableOn_weight_mul_dualSlope η true k hk)

theorem integrable_physicalCost (ρ η : PhysicalCollarPartition n) : Integrable (ρ.physicalCost η) := by
  exact integrable_finsetSum _ fun k hk => η.integrable_density_mul k hk
    (ρ.physicalPrice k) (ρ.measurable_physicalPrice k) (ρ.physicalPrice_bounds k hk)

/-- The actual dual pairing is transported exactly to physical marginal costs. -/
theorem integral_fibreCost (ρ η : PhysicalCollarPartition n) :
    (∫ y in Ioo 0 logarithmicCollarRadius, ρ.fibreCost η y) =
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), ρ.physicalCost η x := by
  have htrans := η.integral_signed_cost_transport ρ.physicalPrice ρ.measurable_physicalPrice
    (fun k hk => ρ.physicalPrice_bounds k hk)
  unfold fibreCost physicalCost
  rw [integral_finsetSum (Finset.range (n + 1))
    (f := fun k y => η.weight false k y * ρ.dualSlope (logNodeOddPart k, false) k y +
      η.weight true k y * ρ.dualSlope (logNodeOddPart k, true) k y) (fun k hk =>
    (ρ.integrableOn_weight_mul_dualSlope η false k hk).add
      (ρ.integrableOn_weight_mul_dualSlope η true k hk))]
  rw [← htrans]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_add (ρ.integrableOn_weight_mul_dualSlope η false k hk)
    (ρ.integrableOn_weight_mul_dualSlope η true k hk)]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    dsimp only
    rw [ρ.physicalPrice_left k hy.1]
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    dsimp only
    rw [ρ.physicalPrice_right k hy.1]

/-- Nonactive collars receive the harmless upper price one when forming the finite minimum. -/
def maskedPrice (ρ : PhysicalCollarPartition n) (k : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ logarithmicPhysicalCollar n k then ρ.physicalPrice k x else 1

theorem measurable_maskedPrice (ρ : PhysicalCollarPartition n) (k : ℕ) :
    Measurable (ρ.maskedPrice k) := by
  classical
  exact Measurable.ite (measurableSet_Ioo.inter measurableSet_Ioo)
    (ρ.measurable_physicalPrice k) measurable_const

private theorem measurable_range_inf (F : ℕ → ℝ → ℝ) (hF : ∀ k, Measurable (F k)) (r : ℕ) :
    Measurable fun x => (Finset.range (r + 1)).inf' (by exact ⟨0, by simp⟩) (fun k => F k x) := by
  induction r with
  | zero => simpa using hF 0
  | succ r ih =>
    simp only [Finset.range_add_one (n := r + 1)]
    simp only [Finset.inf'_insert (show (Finset.range (r + 1)).Nonempty from ⟨0, by simp⟩)]
    exact (hF (r + 1)).min ih

/-- Minimum active physical marginal price; its outside-interval value is irrelevant to all costs. -/
def priceFloor (ρ : PhysicalCollarPartition n) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).inf' (by exact ⟨0, by simp⟩) (fun k => ρ.maskedPrice k x)

theorem measurable_priceFloor (ρ : PhysicalCollarPartition n) : Measurable ρ.priceFloor :=
  measurable_range_inf ρ.maskedPrice ρ.measurable_maskedPrice n

theorem priceFloor_nonneg (ρ : PhysicalCollarPartition n) (x : ℝ) : 0 ≤ ρ.priceFloor x := by
  apply Finset.le_inf'
  intro k hk
  unfold maskedPrice
  split_ifs
  · exact (ρ.physicalPrice_bounds k hk x).1
  · norm_num

theorem priceFloor_le_one (ρ : PhysicalCollarPartition n) (x : ℝ) : ρ.priceFloor x ≤ 1 := by
  apply (Finset.inf'_le (fun k => ρ.maskedPrice k x) (by simp : 0 ∈ Finset.range (n + 1))).trans
  unfold maskedPrice
  split_ifs
  · exact (ρ.physicalPrice_bounds 0 (by simp) x).2
  · rfl

theorem priceFloor_le_active (ρ : PhysicalCollarPartition n) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) {x : ℝ} (hx : x ∈ logarithmicPhysicalCollar n k) :
    ρ.priceFloor x ≤ ρ.physicalPrice k x := by
  have h := Finset.inf'_le (fun k => ρ.maskedPrice k x) hk
  change ρ.priceFloor x ≤ ρ.maskedPrice k x at h
  simpa only [maskedPrice, if_pos hx] using h

def activeNodes (n : ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (fun k => x ∈ logarithmicPhysicalCollar n k)

theorem activeNodes_nonempty {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    (activeNodes n x).Nonempty := by
  classical
  have hc := truncated_logarithmic_collar_union n
  change (⋃ k ∈ Finset.range (n + 1), logarithmicPhysicalCollar n k) =
    Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) at hc
  rw [← hc] at hx
  obtain ⟨k, hk, hxk⟩ : ∃ k ∈ Finset.range (n + 1), x ∈ logarithmicPhysicalCollar n k := by
    simpa only [mem_iUnion, exists_prop] using hx
  exact ⟨k, Finset.mem_filter.mpr ⟨hk, hxk⟩⟩

/-- The masked finite formula really is the minimum over active physical collars. -/
theorem priceFloor_eq_active_inf (ρ : PhysicalCollarPartition n) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    ρ.priceFloor x = (activeNodes n x).inf' (activeNodes_nonempty hx) (fun k => ρ.physicalPrice k x) := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro k hk
    exact ρ.priceFloor_le_active k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2
  · apply Finset.le_inf'
    intro k hk
    unfold maskedPrice
    split_ifs with hxk
    · exact Finset.inf'_le (fun k => ρ.physicalPrice k x) (Finset.mem_filter.mpr ⟨hk, hxk⟩)
    · obtain ⟨j, hj⟩ := activeNodes_nonempty hx
      exact (Finset.inf'_le (fun k => ρ.physicalPrice k x) hj).trans
        (ρ.physicalPrice_bounds j (Finset.mem_filter.mp hj).1 x).2

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
