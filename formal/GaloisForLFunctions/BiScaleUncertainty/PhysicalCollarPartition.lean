import GaloisForLFunctions.BiScaleUncertainty.CollarAllocationDuality

/-!
# General physical collar partitions

Admissibility contains only measurable nonnegative shares, collar support, and exact physical
mass conservation. The equal-multiplicity partition is an explicit inhabitant. Uniform density
bounds discharge integrability; affine collar substitutions then prove exact transport for
every bounded measurable collar-dependent price and independence of total collar mass.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

def logarithmicPhysicalCollar (n k : ℕ) : Set ℝ :=
  truncatedPhysicalCollar (logarithmicCollarNode k) logarithmicCollarRadius (logarithmicCollarEndpoint n)

/-- The defining physical admissibility conditions. No transport or integrability estimate is a field. -/
structure PhysicalCollarPartition (n : ℕ) where
  share : ℕ → ℝ → ℝ
  measurable_share : ∀ k, Measurable (share k)
  nonneg : ∀ k x, 0 ≤ share k x
  supported : ∀ k x, x ∉ logarithmicPhysicalCollar n k → share k x = 0
  partition : ∀ x, (∑ k ∈ Finset.range (n + 1), share k x) =
    (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)).indicator (fun _ => 1) x

/-- Real-valued left affine substitution, with no hidden source regularity condition. -/
theorem integral_collar_left (F : ℝ → ℝ) (t δ : ℝ) :
    (∫ y in Ioo 0 δ, F (t - y)) = ∫ x in Ioo (t - δ) t, F x := by
  rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo]
  have heq : (Ioo 0 δ).indicator (fun y => F (t - y)) =
      fun y => (Ioo (t - δ) t).indicator F (t - y) := by
    funext y
    have hm : t - y ∈ Ioo (t - δ) t ↔ y ∈ Ioo 0 δ := by
      simp only [mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [indicator_apply, hm]
  rw [heq, integral_sub_left_eq_self]

theorem integral_collar_right (F : ℝ → ℝ) (t δ : ℝ) :
    (∫ y in Ioo 0 δ, F (t + y)) = ∫ x in Ioo t (t + δ), F x := by
  rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo]
  have heq : (Ioo 0 δ).indicator (fun y => F (t + y)) =
      fun y => (Ioo t (t + δ)).indicator F (t + y) := by
    funext y
    have hm : t + y ∈ Ioo t (t + δ) ↔ y ∈ Ioo 0 δ := by
      simp only [mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [indicator_apply, hm]
  rw [heq, integral_add_left_eq_self]

theorem integral_collar_both (F : ℝ → ℝ) (hF : Integrable F) (t δ : ℝ) :
    (∫ y in Ioo 0 δ, F (t - y)) + (∫ y in Ioo 0 δ, F (t + y)) =
      ∫ x in Ioo (t - δ) (t + δ), F x := by
  rw [integral_collar_left, integral_collar_right]
  have hd : Disjoint (Ioo (t - δ) t) (Ioo t (t + δ)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2.le) hy.1
  rw [← setIntegral_union hd measurableSet_Ioo hF.integrableOn hF.integrableOn]
  apply setIntegral_congr_set
  filter_upwards [volume.ae_ne t] with x hxt
  apply propext
  change ((t - δ < x ∧ x < t) ∨ (t < x ∧ x < t + δ)) ↔ (t - δ < x ∧ x < t + δ)
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hxt with hlt | hgt
    · exact Or.inl ⟨h1, hlt⟩
    · exact Or.inr ⟨hgt, h2⟩

namespace PhysicalCollarPartition
variable {n : ℕ}

/-- The previously verified equal-multiplicity allocation inhabits the general admissible class. -/
def equalMultiplicity (n : ℕ) : PhysicalCollarPartition n where
  share := logarithmicCollarShare n
  measurable_share := measurable_logarithmicCollarShare n
  nonneg := logarithmicCollarShare_nonneg n
  supported := by
    intro k x hx
    change (logarithmicPhysicalCollar n k).indicator (fun _ => (1 : ℝ)) x / _ = 0
    rw [indicator_of_notMem hx, zero_div]
  partition := by
    intro x
    rw [show (∑ k ∈ Finset.range (n + 1), logarithmicCollarShare n k x) =
      (⋃ k ∈ Finset.range (n + 1), logarithmicPhysicalCollar n k).indicator (fun _ => (1 : ℝ)) x
      from collarPhysicalShare_partition _ _ _]
    have h := truncated_logarithmic_collar_union n
    change (⋃ k ∈ Finset.range (n + 1), logarithmicPhysicalCollar n k) =
      Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) at h
    rw [h]

theorem share_le_one (ρ : PhysicalCollarPartition n) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (x : ℝ) : ρ.share k x ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ => ρ.nonneg j x) hk
  rw [ρ.partition] at h
  by_cases hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)
  · simpa [hx] using h
  · have hzero : ρ.share k x ≤ 0 := by simpa [hx] using h
    linarith

theorem share_zero_outside (ρ : PhysicalCollarPartition n) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) {x : ℝ}
    (hx : x ∉ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) : ρ.share k x = 0 := by
  have h := Finset.single_le_sum (fun j _ => ρ.nonneg j x) hk
  rw [ρ.partition, indicator_of_notMem hx] at h
  exact le_antisymm h (ρ.nonneg k x)

/-- Physical density allotted to one collar. -/
def density (ρ : PhysicalCollarPartition n) (k : ℕ) (x : ℝ) : ℝ :=
  ρ.share k x * archLevySinhWeight x

/-- Signed affine pullback of the actual allotted Lévy density. -/
def weight (ρ : PhysicalCollarPartition n) (σ : Bool) (k : ℕ) (y : ℝ) : ℝ :=
  ρ.density k (logarithmicCollarNode k + collarSignedOffset σ y)

theorem density_nonneg (ρ : PhysicalCollarPartition n) (k : ℕ) (x : ℝ) : 0 ≤ ρ.density k x := by
  by_cases hx : x ∈ logarithmicPhysicalCollar n k
  · exact mul_nonneg (ρ.nonneg k x) (archLevySinhWeight_pos hx.2.1).le
  · simp [density, ρ.supported k x hx]

theorem weight_nonneg (ρ : PhysicalCollarPartition n) (σ : Bool) (k : ℕ) (y : ℝ) :
    0 ≤ ρ.weight σ k y := ρ.density_nonneg k _

theorem measurable_density (ρ : PhysicalCollarPartition n) (k : ℕ) : Measurable (ρ.density k) :=
  (ρ.measurable_share k).mul measurable_archLevySinhWeight

theorem measurable_weight (ρ : PhysicalCollarPartition n) (σ : Bool) (k : ℕ) :
    Measurable (ρ.weight σ k) := by
  apply (ρ.measurable_density k).comp
  cases σ <;> simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte] <;> fun_prop

theorem density_le_bound (ρ : PhysicalCollarPartition n) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (x : ℝ) : ρ.density k x ≤ logarithmicCollarWeightBound n := by
  by_cases hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)
  · have hw : archLevySinhWeight x ≤ logarithmicCollarWeightBound n := by
      apply div_le_div₀ (Real.exp_pos _).le
      · apply Real.exp_le_exp.mpr
        linarith [hx.2]
      · exact Real.sinh_pos_iff.mpr logarithmicCollarRadius_pos
      · exact Real.sinh_le_sinh.mpr hx.1.le
    exact (mul_le_of_le_one_left
      (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx.1)).le
      (ρ.share_le_one k hk x)).trans hw
  · simp only [density, ρ.share_zero_outside k hk hx, zero_mul]
    exact (logarithmicCollarWeightBound_pos n).le

theorem weight_le_bound (ρ : PhysicalCollarPartition n) (σ : Bool) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (y : ℝ) : ρ.weight σ k y ≤ logarithmicCollarWeightBound n :=
  ρ.density_le_bound k hk _

def mass (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (ρ.weight false k y + ρ.weight true k y)

def blockNorm (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  blockWeightNorm (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => ρ.weight j.2 k y)

def kernel (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  archLevySinhWeight y + ρ.mass y - Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2)

def coefficient (ρ : PhysicalCollarPartition n) : ℝ :=
  ∫ y in Ioo 0 logarithmicCollarRadius, ρ.kernel y

theorem sum_signed_weights (ρ : PhysicalCollarPartition n) (y : ℝ) :
    (∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1, ρ.weight j.2 k y) =
      ρ.mass y := sum_logarithmicSignedCosets n (fun σ k => ρ.weight σ k y)

theorem kernel_eq_allocationKernel (ρ : PhysicalCollarPartition n) (y : ℝ) :
    ρ.kernel y = collarAllocationKernel (logarithmicSignedCosets n)
      (fun j => logarithmicCosetNodes n j.1) (fun j k => ρ.weight j.2 k y) (archLevySinhWeight y) := by
  unfold collarAllocationKernel collarDualScale
  rw [ρ.sum_signed_weights]
  rfl

theorem blockNorm_nonneg (ρ : PhysicalCollarPartition n) (y : ℝ) : 0 ≤ ρ.blockNorm y :=
  blockWeightNorm_nonneg _ _ _

theorem blockNorm_le_mass (ρ : PhysicalCollarPartition n) (y : ℝ) : ρ.blockNorm y ≤ ρ.mass y := by
  calc
    _ ≤ ∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1, ρ.weight j.2 k y := by
      apply Finset.sum_le_sum
      intro j _
      apply Real.sqrt_le_iff.mpr
      exact ⟨Finset.sum_nonneg (fun k _ => ρ.weight_nonneg j.2 k y),
        Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => ρ.weight_nonneg j.2 k y)⟩
    _ = _ := ρ.sum_signed_weights y

theorem mass_le_bound (ρ : PhysicalCollarPartition n) (y : ℝ) :
    ρ.mass y ≤ ((n + 1 : ℕ) : ℝ) * (2 * logarithmicCollarWeightBound n) := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), (2 * logarithmicCollarWeightBound n) := by
      apply Finset.sum_le_sum
      intro k hk
      have h1 := ρ.weight_le_bound false k hk y
      have h2 := ρ.weight_le_bound true k hk y
      linarith
    _ = _ := by simp [nsmul_eq_mul]

theorem kernel_bounds (ρ : PhysicalCollarPartition n) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ ρ.kernel y ∧ ρ.kernel y ≤ ρ.mass y := by
  have hW := archLevySinhWeight_nonneg hy
  have hA := ρ.blockNorm_nonneg y
  have hAB := ρ.blockNorm_le_mass y
  have hupper : Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2) ≤
      archLevySinhWeight y + ρ.blockNorm y := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨add_nonneg hW hA, by nlinarith [mul_nonneg hW hA]⟩
  have hlower : archLevySinhWeight y ≤ Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2) :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
  unfold kernel
  constructor <;> linarith

theorem measurable_mass (ρ : PhysicalCollarPartition n) : Measurable ρ.mass :=
  (Finset.range (n + 1)).measurable_sum fun k _ =>
    (ρ.measurable_weight false k).add (ρ.measurable_weight true k)

theorem measurable_blockNorm (ρ : PhysicalCollarPartition n) : Measurable ρ.blockNorm := by
  apply (logarithmicSignedCosets n).measurable_sum
  intro j _
  exact Real.continuous_sqrt.measurable.comp
    ((logarithmicCosetNodes n j.1).measurable_sum fun k _ => (ρ.measurable_weight j.2 k).pow_const 2)

theorem measurable_kernel (ρ : PhysicalCollarPartition n) : Measurable ρ.kernel :=
  (measurable_archLevySinhWeight.add ρ.measurable_mass).sub
    (Real.continuous_sqrt.measurable.comp
      ((measurable_archLevySinhWeight.pow_const 2).add (ρ.measurable_blockNorm.pow_const 2)))

theorem integrableOn_weight (ρ : PhysicalCollarPartition n) (σ : Bool) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) :
    IntegrableOn (ρ.weight σ k) (Ioo 0 logarithmicCollarRadius) := by
  apply volume.integrableOn_of_bounded (M := logarithmicCollarWeightBound n)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    (ρ.measurable_weight σ k).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (ρ.weight_nonneg σ k y)] using ρ.weight_le_bound σ k hk y

theorem integrableOn_kernel (ρ : PhysicalCollarPartition n) :
    IntegrableOn ρ.kernel (Ioo 0 logarithmicCollarRadius) := by
  apply volume.integrableOn_of_bounded (M := ((n + 1 : ℕ) : ℝ) * (2 * logarithmicCollarWeightBound n))
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) ρ.measurable_kernel.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have h := ρ.kernel_bounds hy.1.le
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.trans (ρ.mass_le_bound y)

/-- Every bounded measurable physical price has an integrable allotted density. -/
theorem integrable_density_mul (ρ : PhysicalCollarPartition n) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (Q : ℝ → ℝ) (hQ : Measurable Q)
    (hQb : ∀ x, 0 ≤ Q x ∧ Q x ≤ 1) : Integrable (fun x => ρ.density k x * Q x) := by
  have hi : IntegrableOn (fun x => ρ.density k x * Q x)
      (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) := by
    apply volume.integrableOn_of_bounded (M := logarithmicCollarWeightBound n)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      ((ρ.measurable_density k).mul hQ).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      change ‖ρ.density k x * Q x‖ ≤ logarithmicCollarWeightBound n
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ρ.density_nonneg k x) (hQb x).1)]
      exact (mul_le_of_le_one_right (ρ.density_nonneg k x) (hQb x).2).trans
        (ρ.density_le_bound k hk x)
  have heq : (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)).indicator
      (fun x => ρ.density k x * Q x) = fun x => ρ.density k x * Q x := by
    funext x
    by_cases hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)
    · exact indicator_of_mem hx _
    · simp [hx, density, ρ.share_zero_outside k hk hx]
  simpa only [heq] using hi.integrable_indicator measurableSet_Ioo

/-- Exact affine transport for any bounded measurable, collar-dependent physical price. -/
theorem integral_signed_cost_transport (ρ : PhysicalCollarPartition n) (Q : ℕ → ℝ → ℝ)
    (hQ : ∀ k, Measurable (Q k))
    (hQb : ∀ k ∈ Finset.range (n + 1), ∀ x, 0 ≤ Q k x ∧ Q k x ≤ 1) :
    (∑ k ∈ Finset.range (n + 1),
      ((∫ y in Ioo 0 logarithmicCollarRadius,
        ρ.weight false k y * Q k (logarithmicCollarNode k - y)) +
       (∫ y in Ioo 0 logarithmicCollarRadius,
        ρ.weight true k y * Q k (logarithmicCollarNode k + y)))) =
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n),
        ∑ k ∈ Finset.range (n + 1), ρ.density k x * Q k x := by
  have hi (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :=
    ρ.integrable_density_mul k hk (Q k) (hQ k) (hQb k hk)
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      ((∫ y in Ioo 0 logarithmicCollarRadius,
        ρ.weight false k y * Q k (logarithmicCollarNode k - y)) +
       (∫ y in Ioo 0 logarithmicCollarRadius,
        ρ.weight true k y * Q k (logarithmicCollarNode k + y))) =
        ∫ x, ρ.density k x * Q k x := by
    simp only [weight, collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg]
    rw [integral_collar_both _ (hi k hk), ← integral_indicator measurableSet_Ioo]
    congr 1
    funext x
    by_cases hx : x ∈ Ioo (logarithmicCollarNode k - logarithmicCollarRadius)
        (logarithmicCollarNode k + logarithmicCollarRadius)
    · exact indicator_of_mem hx _
    · have he : x ∉ logarithmicPhysicalCollar n k := fun h => hx h.1
      simp [hx, density, ρ.supported k x he]
  rw [Finset.sum_congr rfl hterm, ← integral_finsetSum _ hi,
    ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)
    · simp only [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      apply Finset.sum_eq_zero
      intro k hk
      simp [density, ρ.share_zero_outside k hk hx]

/-- Every full physical partition transports the same total collar mass. -/
theorem integral_mass (ρ : PhysicalCollarPartition n) :
    (∫ y in Ioo 0 logarithmicCollarRadius, ρ.mass y) =
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x := by
  have htrans := ρ.integral_signed_cost_transport (fun _ _ => 1)
    (fun _ => measurable_const) (fun _ _ _ => ⟨by norm_num, le_rfl⟩)
  simp only [mul_one] at htrans
  unfold mass
  rw [integral_finsetSum (Finset.range (n + 1))
    (f := fun k y => ρ.weight false k y + ρ.weight true k y)
    (fun k hk => (ρ.integrableOn_weight false k hk).add (ρ.integrableOn_weight true k hk))]
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        ((∫ y in Ioo 0 logarithmicCollarRadius, ρ.weight false k y) +
         (∫ y in Ioo 0 logarithmicCollarRadius, ρ.weight true k y)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact integral_add (ρ.integrableOn_weight false k hk) (ρ.integrableOn_weight true k hk)
    _ = ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n),
        ∑ k ∈ Finset.range (n + 1), ρ.density k x := htrans
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      simp only [density, ← Finset.sum_mul, ρ.partition, indicator_of_mem hx, one_mul]

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
