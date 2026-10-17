import GaloisForLFunctions.BiScaleUncertainty.SignedGramPhysicalPrices

/-!
# A measurable pure response to actual signed-Gram prices

At each physical point select the least active collar attaining the actual
finite price minimum. The resulting measurable cells partition the physical
interval, so they define an admissible allocation with shares in `{0, 1}`.
The construction includes ties and the zero source.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section
variable {n : ℕ}

def gramMinimizerCell (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (k : ℕ) : Set ℝ :=
  {x | k ∈ Finset.range (n + 1) ∧ x ∈ logarithmicPhysicalCollar n k ∧
    ρ.gramPhysicalPrice f k x = ρ.gramPriceFloor f x}

theorem measurableSet_gramMinimizerCell (ρ : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) (k : ℕ) : MeasurableSet (ρ.gramMinimizerCell f k) := by
  classical
  by_cases hk : k ∈ Finset.range (n + 1)
  · have hC : MeasurableSet (logarithmicPhysicalCollar n k) :=
      measurableSet_Ioo.inter measurableSet_Ioo
    have he : ρ.gramMinimizerCell f k = logarithmicPhysicalCollar n k ∩
        {x | ρ.gramPhysicalPrice f k x = ρ.gramPriceFloor f x} := by
      ext x
      simp only [gramMinimizerCell, mem_setOf_eq, mem_inter_iff, hk, true_and]
    rw [he]
    exact hC.inter
      (measurableSet_eq_fun (ρ.measurable_gramPhysicalPrice f k) (ρ.measurable_gramPriceFloor f))
  · simp [gramMinimizerCell, hk]

theorem gramMinimizerCell_exists (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {x : ℝ} (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    ∃ k, x ∈ ρ.gramMinimizerCell f k := by
  classical
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_inf' (activeNodes_nonempty hx)
    (fun k => ρ.gramPhysicalPrice f k x)
  refine ⟨k, (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2, ?_⟩
  exact ((ρ.gramPriceFloor_eq_active_inf f hx).trans he).symm

/-- Tie-breaking removes every earlier minimizing cell. -/
def gramFirstMinimizerCell (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (k : ℕ) : Set ℝ :=
  ρ.gramMinimizerCell f k ∩ ⋂ j ∈ Finset.range k, (ρ.gramMinimizerCell f j)ᶜ

theorem mem_gramFirstMinimizerCell (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (k : ℕ) (x : ℝ) :
    x ∈ ρ.gramFirstMinimizerCell f k ↔
      x ∈ ρ.gramMinimizerCell f k ∧ ∀ j < k, x ∉ ρ.gramMinimizerCell f j := by
  simp [gramFirstMinimizerCell]

theorem measurableSet_gramFirstMinimizerCell (ρ : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) (k : ℕ) : MeasurableSet (ρ.gramFirstMinimizerCell f k) :=
  (ρ.measurableSet_gramMinimizerCell f k).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (ρ.measurableSet_gramMinimizerCell f j).compl)

theorem gramFirstMinimizerCell_unique (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {i j : ℕ} {x : ℝ} (hi : x ∈ ρ.gramFirstMinimizerCell f i)
    (hj : x ∈ ρ.gramFirstMinimizerCell f j) : i = j := by
  have hi' := (ρ.mem_gramFirstMinimizerCell f i x).mp hi
  have hj' := (ρ.mem_gramFirstMinimizerCell f j x).mp hj
  by_contra h
  rcases lt_or_gt_of_ne h with hij | hji
  · exact hj'.2 i hij hi'.1
  · exact hi'.2 j hji hj'.1

theorem gramFirstMinimizerCell_exists (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {x : ℝ} (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    ∃ k, x ∈ ρ.gramFirstMinimizerCell f k := by
  classical
  have h := ρ.gramMinimizerCell_exists f hx
  refine ⟨Nat.find h, (ρ.mem_gramFirstMinimizerCell f (Nat.find h) x).mpr ?_⟩
  exact ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

theorem gramFirstMinimizerCell_union (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    (⋃ k ∈ Finset.range (n + 1), ρ.gramFirstMinimizerCell f k) =
      Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, hcell⟩ : ∃ k ∈ Finset.range (n + 1),
        x ∈ ρ.gramFirstMinimizerCell f k := by simpa only [mem_iUnion, exists_prop] using hx
    have hC := ((ρ.mem_gramFirstMinimizerCell f k x).mp hcell).1.2.1
    have hu := truncated_logarithmic_collar_union n
    change (⋃ k ∈ Finset.range (n + 1), logarithmicPhysicalCollar n k) =
      Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) at hu
    rw [← hu]
    simp only [mem_iUnion]
    exact ⟨k, hk, hC⟩
  · intro hx
    obtain ⟨k, hk⟩ := ρ.gramFirstMinimizerCell_exists f hx
    simp only [mem_iUnion]
    exact ⟨k, ((ρ.mem_gramFirstMinimizerCell f k x).mp hk).1.1, hk⟩

/-- An actual admissible partition, selecting the least active minimum-price collar. -/
def gramMinimumResponse (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    PhysicalCollarPartition n where
  share := collarPhysicalShare (Finset.range (n + 1)) (ρ.gramFirstMinimizerCell f)
  measurable_share := by
    intro k
    exact (measurable_const.indicator (ρ.measurableSet_gramFirstMinimizerCell f k)).div
      ((Finset.range (n + 1)).measurable_sum fun j _ =>
        measurable_const.indicator (ρ.measurableSet_gramFirstMinimizerCell f j))
  nonneg := collarPhysicalShare_nonneg _ _
  supported := by
    intro k x hx
    have hc : x ∉ ρ.gramFirstMinimizerCell f k := by
      intro h
      exact hx ((ρ.mem_gramFirstMinimizerCell f k x).mp h).1.2.1
    simp only [collarPhysicalShare, indicator_of_notMem hc, zero_div]
  partition := by
    intro x
    rw [collarPhysicalShare_partition, ρ.gramFirstMinimizerCell_union f]

private theorem minimumMultiplicity_eq_one (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {k : ℕ} {x : ℝ} (hx : x ∈ ρ.gramFirstMinimizerCell f k) :
    collarMultiplicity (Finset.range (n + 1)) (ρ.gramFirstMinimizerCell f) x = 1 := by
  classical
  unfold collarMultiplicity
  rw [Finset.sum_eq_single k]
  · exact indicator_of_mem hx _
  · intro j _ hj
    apply indicator_of_notMem
    intro h
    exact hj (ρ.gramFirstMinimizerCell_unique f h hx)
  · intro hk
    exact (hk ((ρ.mem_gramFirstMinimizerCell f k x).mp hx).1.1).elim

/-- Every response share is the characteristic function of its selection cell. -/
theorem gramMinimumResponse_share (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (k : ℕ) (x : ℝ) :
    (ρ.gramMinimumResponse f).share k x =
      (ρ.gramFirstMinimizerCell f k).indicator (fun _ => (1 : ℝ)) x := by
  classical
  change collarPhysicalShare _ _ _ _ = _
  by_cases hx : x ∈ ρ.gramFirstMinimizerCell f k
  · rw [collarPhysicalShare, ρ.minimumMultiplicity_eq_one f hx, div_one]
  · simp only [collarPhysicalShare, indicator_of_notMem hx, zero_div]

theorem gramMinimumResponse_pure (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (k : ℕ) (x : ℝ) :
    (ρ.gramMinimumResponse f).share k x = 0 ∨ (ρ.gramMinimumResponse f).share k x = 1 := by
  rw [ρ.gramMinimumResponse_share f k x]
  by_cases hx : x ∈ ρ.gramFirstMinimizerCell f k <;> simp [hx]

theorem gramMinimumResponse_share_eq_one_iff (ρ : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) (k : ℕ) (x : ℝ) :
    (ρ.gramMinimumResponse f).share k x = 1 ↔ x ∈ ρ.gramFirstMinimizerCell f k := by
  rw [ρ.gramMinimumResponse_share f k x]
  by_cases hx : x ∈ ρ.gramFirstMinimizerCell f k <;> simp [hx]

theorem gramMinimumResponse_unique_selected (ρ : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    ∃! k, k ∈ Finset.range (n + 1) ∧ (ρ.gramMinimumResponse f).share k x = 1 := by
  obtain ⟨k, hk⟩ := ρ.gramFirstMinimizerCell_exists f hx
  refine ⟨k, ⟨((ρ.mem_gramFirstMinimizerCell f k x).mp hk).1.1,
    (ρ.gramMinimumResponse_share_eq_one_iff f k x).mpr hk⟩, ?_⟩
  intro j hj
  exact ρ.gramFirstMinimizerCell_unique f
    ((ρ.gramMinimumResponse_share_eq_one_iff f j x).mp hj.2) hk

theorem gramMinimumResponse_price (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (k : ℕ) (x : ℝ) (hx : 0 < (ρ.gramMinimumResponse f).share k x) :
    ρ.gramPhysicalPrice f k x = ρ.gramPriceFloor f x := by
  have hm : x ∈ ρ.gramFirstMinimizerCell f k := by
    by_contra h
    rw [ρ.gramMinimumResponse_share f k x, indicator_of_notMem h] at hx
    exact (lt_irrefl 0) hx
  exact ((ρ.mem_gramFirstMinimizerCell f k x).mp hm).1.2.2

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
