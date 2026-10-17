import GaloisForLFunctions.BiScaleUncertainty.SignedGramDualSupport

/-!
# Physical prices from actual signed translation packets

Bounded full-Gram prices pull back along both signed collar branches. Their
physical costs transport exactly, and the masked finite minimum agrees with the
minimum over active collars. Every measurability and integrability obligation is
discharged from the actual compact source and physical partition.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section
variable {n : ℕ}

def gramDualPrice (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (σ : Bool) (k : ℕ) (y : ℝ) : ℝ :=
  AnchoredGram.price f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
    signedGramShift (archLevySinhWeight y) (signedGramShift (σ, k))

theorem measurable_gramDualPrice (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (σ : Bool) (k : ℕ) :
    Measurable (ρ.gramDualPrice f σ k) :=
  AnchoredGram.measurable_price f (signedGramNodes n) (fun y p => ρ.weight p.1 p.2 y)
    signedGramShift archLevySinhWeight (fun p => ρ.measurable_weight p.1 p.2)
    measurable_archLevySinhWeight (signedGramShift (σ, k))

theorem gramDualPrice_bounds (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (σ : Bool) (k : ℕ) (y : ℝ) :
    0 ≤ ρ.gramDualPrice f σ k y ∧ ρ.gramDualPrice f σ k y ≤ 1 :=
  AnchoredGram.price_bounds f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
    signedGramShift (archLevySinhWeight y) (signedGramShift (σ, k))

def gramPhysicalPrice (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (k : ℕ) (x : ℝ) : ℝ :=
  if x < logarithmicCollarNode k then ρ.gramDualPrice f false k (logarithmicCollarNode k - x)
  else ρ.gramDualPrice f true k (x - logarithmicCollarNode k)

theorem measurable_gramPhysicalPrice (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (k : ℕ) :
    Measurable (ρ.gramPhysicalPrice f k) :=
  Measurable.ite measurableSet_Iio
    ((ρ.measurable_gramDualPrice f false k).comp (measurable_const.sub measurable_id))
    ((ρ.measurable_gramDualPrice f true k).comp (measurable_id.sub measurable_const))

theorem gramPhysicalPrice_bounds (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (k : ℕ) (x : ℝ) :
    0 ≤ ρ.gramPhysicalPrice f k x ∧ ρ.gramPhysicalPrice f k x ≤ 1 := by
  unfold gramPhysicalPrice
  split_ifs <;> exact ρ.gramDualPrice_bounds f _ _ _

theorem gramPhysicalPrice_left (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (k : ℕ)
    {y : ℝ} (hy : 0 < y) :
    ρ.gramPhysicalPrice f k (logarithmicCollarNode k - y) = ρ.gramDualPrice f false k y := by
  unfold gramPhysicalPrice
  rw [if_pos (by linarith)]
  congr 1
  ring

theorem gramPhysicalPrice_right (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (k : ℕ)
    {y : ℝ} (hy : 0 < y) :
    ρ.gramPhysicalPrice f k (logarithmicCollarNode k + y) = ρ.gramDualPrice f true k y := by
  unfold gramPhysicalPrice
  rw [if_neg (by linarith)]
  congr 1
  ring

def gramFibreCost (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (η.weight false k y * ρ.gramDualPrice f false k y + η.weight true k y * ρ.gramDualPrice f true k y)

def gramPhysicalCost (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), η.density k x * ρ.gramPhysicalPrice f k x

theorem gramFibreCost_eq_signed_sum (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    ρ.gramFibreCost η f y = ∑ p ∈ signedGramNodes n,
      η.weight p.1 p.2 y * AnchoredGram.price f (signedGramNodes n)
        (fun q => ρ.weight q.1 q.2 y) signedGramShift (archLevySinhWeight y) (signedGramShift p) := by
  simp [gramFibreCost, gramDualPrice, signedGramNodes, Finset.sum_product, Finset.sum_add_distrib, add_comm]

theorem integrableOn_weight_mul_gramDualPrice (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (σ : Bool) (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
    IntegrableOn (fun y => η.weight σ k y * ρ.gramDualPrice f σ k y) (Ioo 0 logarithmicCollarRadius) := by
  apply volume.integrableOn_of_bounded (M := logarithmicCollarWeightBound n)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    ((η.measurable_weight σ k).mul (ρ.measurable_gramDualPrice f σ k)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖η.weight σ k y * ρ.gramDualPrice f σ k y‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (η.weight_nonneg σ k y) (ρ.gramDualPrice_bounds f σ k y).1)]
    exact (mul_le_of_le_one_right (η.weight_nonneg σ k y) (ρ.gramDualPrice_bounds f σ k y).2).trans
      (η.weight_le_bound σ k hk y)

theorem integrableOn_gramFibreCost (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    IntegrableOn (ρ.gramFibreCost η f) (Ioo 0 logarithmicCollarRadius) :=
  integrable_finsetSum _ fun k hk => (ρ.integrableOn_weight_mul_gramDualPrice η f false k hk).add
    (ρ.integrableOn_weight_mul_gramDualPrice η f true k hk)

theorem integrable_gramPhysicalCost (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    Integrable (ρ.gramPhysicalCost η f) :=
  integrable_finsetSum _ fun k hk => η.integrable_density_mul k hk
    (ρ.gramPhysicalPrice f k) (ρ.measurable_gramPhysicalPrice f k) (ρ.gramPhysicalPrice_bounds f k)

/-- Both signed packet prices transport to their actual physical collar locations. -/
theorem integral_gramFibreCost (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    (∫ y in Ioo 0 logarithmicCollarRadius, ρ.gramFibreCost η f y) =
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), ρ.gramPhysicalCost η f x := by
  have htrans := η.integral_signed_cost_transport (ρ.gramPhysicalPrice f)
    (ρ.measurable_gramPhysicalPrice f) (fun k _ => ρ.gramPhysicalPrice_bounds f k)
  unfold gramFibreCost gramPhysicalCost
  rw [integral_finsetSum (Finset.range (n + 1))
    (f := fun k y => η.weight false k y * ρ.gramDualPrice f false k y +
      η.weight true k y * ρ.gramDualPrice f true k y) (fun k hk =>
    (ρ.integrableOn_weight_mul_gramDualPrice η f false k hk).add
      (ρ.integrableOn_weight_mul_gramDualPrice η f true k hk))]
  rw [← htrans]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_add (ρ.integrableOn_weight_mul_gramDualPrice η f false k hk)
    (ρ.integrableOn_weight_mul_gramDualPrice η f true k hk)]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    dsimp only
    rw [ρ.gramPhysicalPrice_left f k hy.1]
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    dsimp only
    rw [ρ.gramPhysicalPrice_right f k hy.1]

def gramMaskedPrice (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (k : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ logarithmicPhysicalCollar n k then ρ.gramPhysicalPrice f k x else 1

theorem measurable_gramMaskedPrice (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (k : ℕ) :
    Measurable (ρ.gramMaskedPrice f k) := by
  classical
  exact Measurable.ite (measurableSet_Ioo.inter measurableSet_Ioo)
    (ρ.measurable_gramPhysicalPrice f k) measurable_const

private theorem measurable_finite_min (F : ℕ → ℝ → ℝ) (hF : ∀ k, Measurable (F k)) (r : ℕ) :
    Measurable fun x => (Finset.range (r + 1)).inf' (by exact ⟨0, by simp⟩) (fun k => F k x) := by
  induction r with
  | zero => simpa using hF 0
  | succ r ih =>
    simp only [Finset.range_add_one (n := r + 1)]
    simp only [Finset.inf'_insert (show (Finset.range (r + 1)).Nonempty from ⟨0, by simp⟩)]
    exact (hF (r + 1)).min ih

def gramPriceFloor (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).inf' (by exact ⟨0, by simp⟩) (fun k => ρ.gramMaskedPrice f k x)

theorem measurable_gramPriceFloor (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    Measurable (ρ.gramPriceFloor f) :=
  measurable_finite_min (ρ.gramMaskedPrice f) (ρ.measurable_gramMaskedPrice f) n

theorem gramPriceFloor_nonneg (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (x : ℝ) :
    0 ≤ ρ.gramPriceFloor f x := by
  apply Finset.le_inf'
  intro k _
  unfold gramMaskedPrice
  split_ifs
  · exact (ρ.gramPhysicalPrice_bounds f k x).1
  · norm_num

theorem gramPriceFloor_le_one (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (x : ℝ) :
    ρ.gramPriceFloor f x ≤ 1 := by
  apply (Finset.inf'_le (fun k => ρ.gramMaskedPrice f k x) (by simp : 0 ∈ Finset.range (n + 1))).trans
  unfold gramMaskedPrice
  split_ifs
  · exact (ρ.gramPhysicalPrice_bounds f 0 x).2
  · rfl

theorem gramPriceFloor_le_active (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) {x : ℝ} (hx : x ∈ logarithmicPhysicalCollar n k) :
    ρ.gramPriceFloor f x ≤ ρ.gramPhysicalPrice f k x := by
  have h := Finset.inf'_le (fun k => ρ.gramMaskedPrice f k x) hk
  change ρ.gramPriceFloor f x ≤ ρ.gramMaskedPrice f k x at h
  simpa only [gramMaskedPrice, if_pos hx] using h

theorem gramPriceFloor_eq_active_inf (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    ρ.gramPriceFloor f x = (activeNodes n x).inf' (activeNodes_nonempty hx) (fun k => ρ.gramPhysicalPrice f k x) := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro k hk
    exact ρ.gramPriceFloor_le_active f k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2
  · apply Finset.le_inf'
    intro k hk
    unfold gramMaskedPrice
    split_ifs with hxk
    · exact Finset.inf'_le (fun k => ρ.gramPhysicalPrice f k x) (Finset.mem_filter.mpr ⟨hk, hxk⟩)
    · obtain ⟨j, hj⟩ := activeNodes_nonempty hx
      exact (Finset.inf'_le (fun k => ρ.gramPhysicalPrice f k x) hj).trans (ρ.gramPhysicalPrice_bounds f j x).2

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
