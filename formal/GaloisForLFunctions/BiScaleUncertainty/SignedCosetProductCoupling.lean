import GaloisForLFunctions.BiScaleUncertainty.PairedCosetSphereDuality
import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarSourceEnergy

/-!
# Product-zero coupling between signed physical collars

Grid zeros through `K²` make every positive-node odd coset through `K` orthogonal
to every negative-node odd coset through `K`. Paired clique spheres therefore
give a stronger physical allocation kernel for actual compact continuous sources.
The same signed transport controls overlap and spends the origin interval once.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

/-- Opposite signed logarithmic nodes are orthogonal once their product is pinned. -/
theorem LogarithmicGridSource.product_zero {m : ℕ} (f : LogarithmicGridSource m)
    {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a * b ≤ m + 2) :
    autocorr f.1 (Real.log (a : ℝ) + Real.log (b : ℝ)) = 0 := by
  have hp : 2 ≤ a * b := by nlinarith
  have h := f.2 (a * b - 2) (Finset.mem_range.mpr (by omega))
  have heq : a * b - 2 + 2 = a * b := Nat.sub_add_cancel hp
  unfold logarithmicCollarNode at h
  rw [heq, Nat.cast_mul, Real.log_mul
    (Nat.cast_pos.mpr (by omega : 0 < a)).ne'
    (Nat.cast_pos.mpr (by omega : 0 < b)).ne'] at h
  exact h

/-- Every pair of opposite-sign odd cosets shares an origin-anchored Bessel sphere. -/
theorem autocorr_paired_logarithmicCoset_sphere {n m : ℕ} (f : LogarithmicGridSource m)
    (hcut : (n + 2) ^ 2 ≤ m + 2) (p q : ℕ) (y : ℝ) :
    autocorr f.1 y ^ 2 +
      (∑ k ∈ logarithmicCosetNodes n p, autocorr f.1 (logarithmicCollarNode k - y) ^ 2) +
      (∑ k ∈ logarithmicCosetNodes n q, autocorr f.1 (logarithmicCollarNode k + y) ^ 2) ≤
        autocorr f.1 0 ^ 2 := by
  have hnm : n ≤ m := by nlinarith
  have hgrid : ∀ a ∈ Finset.Icc 2 (m + 2), autocorr f.1 (Real.log (a : ℝ)) = 0 := by
    intro a ha
    have hab := Finset.mem_Icc.mp ha
    have heq : a - 2 + 2 = a := Nat.sub_add_cancel hab.1
    have h := f.2 (a - 2) (Finset.mem_range.mpr (by omega))
    simpa only [logarithmicCollarNode, heq] using h
  have hbound (r k : ℕ) (hk : k ∈ logarithmicCosetNodes n r) : k + 2 ≤ n + 2 := by
    have h := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    omega
  have hzero (r k : ℕ) (hk : k ∈ logarithmicCosetNodes n r) :
      autocorr f.1 (logarithmicCollarNode k) = 0 := by
    apply hgrid (k + 2)
    exact Finset.mem_Icc.mpr ⟨by omega, (hbound r k hk).trans (by omega)⟩
  have hsame (r i : ℕ) (hi : i ∈ logarithmicCosetNodes n r)
      (j : ℕ) (hj : j ∈ logarithmicCosetNodes n r) (hij : i ≠ j) :
      autocorr f.1 (logarithmicCollarNode i - logarithmicCollarNode j) = 0 := by
    apply autocorr_log_divisibility_pair_orth hgrid (by omega) (by omega)
      ((hbound r i hi).trans (by omega)) ((hbound r j hj).trans (by omega))
    have hcmp := logNode_oddPart_comparable
      ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    rcases hcmp with hdiv | hdiv
    · exact Or.inl ⟨lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdiv) (by omega), hdiv⟩
    · exact Or.inr ⟨lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdiv) (by omega), hdiv⟩
  have hcross (i : ℕ) (hi : i ∈ logarithmicCosetNodes n p)
      (j : ℕ) (hj : j ∈ logarithmicCosetNodes n q) :
      autocorr f.1 (logarithmicCollarNode i + logarithmicCollarNode j) = 0 := by
    apply f.product_zero (by omega) (by omega)
    exact (Nat.mul_le_mul (hbound p i hi) (hbound q j hj)).trans (by
      simpa only [pow_two] using hcut)
  let S := (logarithmicCosetNodes n p).disjSum (logarithmicCosetNodes n q)
  let t : ℕ ⊕ ℕ → ℝ := Sum.elim logarithmicCollarNode (fun k => -logarithmicCollarNode k)
  have hz : ∀ i ∈ S, autocorr f.1 (t i) = 0 := by
    intro i hi
    cases i with
    | inl k => exact hzero p k (by simpa [S] using hi)
    | inr k =>
        change autocorr f.1 (-logarithmicCollarNode k) = 0
        rw [autocorr_neg]
        exact hzero q k (by simpa [S] using hi)
  have ho : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → autocorr f.1 (t i - t j) = 0 := by
    intro i hi j hj hij
    cases i with
    | inl i =>
        have hip : i ∈ logarithmicCosetNodes n p := by simpa [S] using hi
        cases j with
        | inl j =>
            exact hsame p i hip j (by simpa [S] using hj) (by simpa using hij)
        | inr j =>
            change autocorr f.1 (logarithmicCollarNode i - -logarithmicCollarNode j) = 0
            simpa only [sub_neg_eq_add] using hcross i hip j (by simpa [S] using hj)
    | inr i =>
        have hiq : i ∈ logarithmicCosetNodes n q := by simpa [S] using hi
        cases j with
        | inl j =>
            change autocorr f.1 (-logarithmicCollarNode i - logarithmicCollarNode j) = 0
            rw [show -logarithmicCollarNode i - logarithmicCollarNode j =
              -(logarithmicCollarNode j + logarithmicCollarNode i) by ring, autocorr_neg]
            exact hcross j (by simpa [S] using hj) i hiq
        | inr j =>
            change autocorr f.1 (-logarithmicCollarNode i - -logarithmicCollarNode j) = 0
            rw [show -logarithmicCollarNode i - -logarithmicCollarNode j =
              -(logarithmicCollarNode i - logarithmicCollarNode j) by ring, autocorr_neg]
            exact hsame q i hiq j (by simpa [S] using hj) (by simpa using hij)
  have h := autocorr_origin_chain_sphere_sub_le f.1.hasCompactSupport f.1.continuous S t hz ho y
  simp only [S, Finset.sum_disjSum, t, Sum.elim_inl, Sum.elim_inr] at h
  have he (k : ℕ) : autocorr f.1 (-logarithmicCollarNode k - y) =
      autocorr f.1 (logarithmicCollarNode k + y) := by
    rw [show -logarithmicCollarNode k - y = -(logarithmicCollarNode k + y) by ring, autocorr_neg]
  simpa only [he, add_assoc] using h

namespace PhysicalCollarPartition
variable {n : ℕ}

/-- Sum of Euclidean coset norms on one collar sign. -/
def signBlockNorm (ρ : PhysicalCollarPartition n) (σ : Bool) (y : ℝ) : ℝ :=
  blockWeightNorm (logarithmicOddCosets n) (logarithmicCosetNodes n) (fun _ k => ρ.weight σ k y)

/-- The product-coupled kernel uses the Euclidean norm of the two sign sums. -/
def pairedKernel (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  archLevySinhWeight y + ρ.mass y -
    Real.sqrt (archLevySinhWeight y ^ 2 + ρ.signBlockNorm false y ^ 2 + ρ.signBlockNorm true y ^ 2)

/-- Physical allocation coefficient with all opposite-sign coset pairs coupled. -/
def pairedCoefficient (ρ : PhysicalCollarPartition n) : ℝ :=
  ∫ y in Ioo 0 logarithmicCollarRadius, ρ.pairedKernel y

theorem signBlockNorm_nonneg (ρ : PhysicalCollarPartition n) (σ : Bool) (y : ℝ) :
    0 ≤ ρ.signBlockNorm σ y := blockWeightNorm_nonneg _ _ _

theorem blockNorm_eq_signBlockNorm_add (ρ : PhysicalCollarPartition n) (y : ℝ) :
    ρ.blockNorm y = ρ.signBlockNorm false y + ρ.signBlockNorm true y := by
  simp only [blockNorm, blockWeightNorm, logarithmicSignedCosets, Finset.sum_product,
    Fintype.sum_bool, Finset.sum_add_distrib, signBlockNorm]
  exact add_comm _ _

theorem kernel_le_pairedKernel (ρ : PhysicalCollarPartition n) (y : ℝ) :
    ρ.kernel y ≤ ρ.pairedKernel y := by
  have h := pairedSphereScale_le_independent (logarithmicOddCosets n)
    (logarithmicCosetNodes n) (fun σ _ k => ρ.weight σ k y) (archLevySinhWeight y)
  change Real.sqrt (archLevySinhWeight y ^ 2 + ρ.signBlockNorm false y ^ 2 +
    ρ.signBlockNorm true y ^ 2) ≤
      Real.sqrt (archLevySinhWeight y ^ 2 + (ρ.signBlockNorm false y + ρ.signBlockNorm true y) ^ 2) at h
  rw [← ρ.blockNorm_eq_signBlockNorm_add] at h
  exact sub_le_sub_left h _

theorem pairedKernel_bounds (ρ : PhysicalCollarPartition n) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ ρ.pairedKernel y ∧ ρ.pairedKernel y ≤ ρ.mass y := by
  refine ⟨(ρ.kernel_bounds hy).1.trans (ρ.kernel_le_pairedKernel y), ?_⟩
  have h : archLevySinhWeight y ≤ Real.sqrt (archLevySinhWeight y ^ 2 +
      ρ.signBlockNorm false y ^ 2 + ρ.signBlockNorm true y ^ 2) :=
    Real.le_sqrt_of_sq_le (by
      have hfalse := sq_nonneg (ρ.signBlockNorm false y)
      have htrue := sq_nonneg (ρ.signBlockNorm true y)
      linarith)
  unfold pairedKernel
  linarith

/-- The gain is exactly the cross-sign interaction of the allocated block norms. -/
theorem pairedKernel_sub_kernel (ρ : PhysicalCollarPartition n) {y : ℝ} (hy : 0 < y) :
    ρ.pairedKernel y - ρ.kernel y =
      2 * ρ.signBlockNorm false y * ρ.signBlockNorm true y /
        (Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2) +
          Real.sqrt (archLevySinhWeight y ^ 2 +
            ρ.signBlockNorm false y ^ 2 + ρ.signBlockNorm true y ^ 2)) := by
  have h := pairedSphereScale_gain (logarithmicOddCosets n) (logarithmicCosetNodes n)
    (fun σ _ k => ρ.weight σ k y) (archLevySinhWeight_pos hy)
  change Real.sqrt (archLevySinhWeight y ^ 2 +
      (ρ.signBlockNorm false y + ρ.signBlockNorm true y) ^ 2) -
    Real.sqrt (archLevySinhWeight y ^ 2 + ρ.signBlockNorm false y ^ 2 + ρ.signBlockNorm true y ^ 2) =
      2 * ρ.signBlockNorm false y * ρ.signBlockNorm true y /
        (Real.sqrt (archLevySinhWeight y ^ 2 + (ρ.signBlockNorm false y + ρ.signBlockNorm true y) ^ 2) +
          Real.sqrt (archLevySinhWeight y ^ 2 + ρ.signBlockNorm false y ^ 2 + ρ.signBlockNorm true y ^ 2)) at h
  rw [← ρ.blockNorm_eq_signBlockNorm_add] at h
  calc
    _ = Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2) -
        Real.sqrt (archLevySinhWeight y ^ 2 + ρ.signBlockNorm false y ^ 2 +
          ρ.signBlockNorm true y ^ 2) := by unfold pairedKernel kernel; ring
    _ = _ := h

theorem measurable_signBlockNorm (ρ : PhysicalCollarPartition n) (σ : Bool) :
    Measurable (ρ.signBlockNorm σ) := by
  apply (logarithmicOddCosets n).measurable_sum
  intro p _
  exact Real.continuous_sqrt.measurable.comp
    ((logarithmicCosetNodes n p).measurable_sum fun k _ => (ρ.measurable_weight σ k).pow_const 2)

theorem measurable_pairedKernel (ρ : PhysicalCollarPartition n) : Measurable ρ.pairedKernel :=
  (measurable_archLevySinhWeight.add ρ.measurable_mass).sub
    (Real.continuous_sqrt.measurable.comp
      (((measurable_archLevySinhWeight.pow_const 2).add
        ((ρ.measurable_signBlockNorm false).pow_const 2)).add
          ((ρ.measurable_signBlockNorm true).pow_const 2)))

theorem integrableOn_pairedKernel (ρ : PhysicalCollarPartition n) :
    IntegrableOn ρ.pairedKernel (Ioo 0 logarithmicCollarRadius) := by
  apply volume.integrableOn_of_bounded (M := ((n + 1 : ℕ) : ℝ) * (2 * logarithmicCollarWeightBound n))
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) ρ.measurable_pairedKernel.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have h := ρ.pairedKernel_bounds hy.1.le
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.trans (ρ.mass_le_bound y)

theorem coefficient_le_pairedCoefficient (ρ : PhysicalCollarPartition n) :
    ρ.coefficient ≤ ρ.pairedCoefficient :=
  integral_mono_ae ρ.integrableOn_kernel ρ.integrableOn_pairedKernel
    (Filter.Eventually.of_forall (ρ.kernel_le_pairedKernel))

/-- The stronger kernel applies to actual sources pinned through the product cutoff. -/
theorem pairedKernel_source_pointwise (ρ : PhysicalCollarPartition n) {m : ℕ}
    (f : LogarithmicGridSource m) (hcut : (n + 2) ^ 2 ≤ m + 2) (y : ℝ) :
    ρ.pairedKernel y * autocorr f.1 0 ≤
      archLevySinhWeight y * (autocorr f.1 0 - autocorr f.1 y) +
      ∑ k ∈ Finset.range (n + 1),
        (ρ.weight false k y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode k - y)) +
         ρ.weight true k y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode k + y))) := by
  have h := paired_sphere_leverage_bound (logarithmicOddCosets n) (logarithmicOddCosets_nonempty n)
    (logarithmicCosetNodes n) (fun σ _ k => ρ.weight σ k y)
    (fun σ _ k => autocorr f.1 (logarithmicCollarNode k + collarSignedOffset σ y))
    (archLevySinhWeight y) (autocorr f.1 y) (autocorr f.1 0) (autocorr_zero_nonneg f.1)
    (by
      intro p _ q _
      simpa only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] using
        autocorr_paired_logarithmicCoset_sphere f hcut p q y)
  simp only [sum_logarithmicCosetNodes, collarSignedOffset, Bool.false_eq_true,
    ↓reduceIte, ← sub_eq_add_neg] at h
  simp only [pairedKernel, mass, Finset.sum_add_distrib, pairedSphereScale, signBlockNorm,
    add_assoc] at h ⊢
  exact h

/-- The finite signed source cost is exactly its extended nonnegative fibre. -/
theorem sourceFibre_eq_ofReal (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {y : ℝ} (hy : 0 ≤ y) :
    ρ.sourceFibre f y = ENNReal.ofReal
      (archLevySinhWeight y * (autocorr f 0 - autocorr f y) +
        ∑ k ∈ Finset.range (n + 1),
          (ρ.weight false k y * (autocorr f 0 - autocorr f (logarithmicCollarNode k - y)) +
           ρ.weight true k y * (autocorr f 0 - autocorr f (logarithmicCollarNode k + y)))) := by
  have hD (x : ℝ) : 0 ≤ autocorr f 0 - autocorr f x :=
    autocorr_sub_nonneg f.hasCompactSupport f.continuous x
  have hn (σ : Bool) (k : ℕ) (x : ℝ) :
      0 ≤ ρ.weight σ k y * (autocorr f 0 - autocorr f x) :=
    mul_nonneg (ρ.weight_nonneg σ k y) (hD x)
  have hb (σ : Bool) (k : ℕ) :
      ENNReal.ofReal (ρ.weight σ k y *
        (autocorr f 0 - autocorr f (logarithmicCollarNode k + collarSignedOffset σ y))) =
        ρ.allocated (continuousArchIncrementDensity (compactAutocorrKernel f)) k
          (logarithmicCollarNode k + collarSignedOffset σ y) := by
    unfold allocated continuousArchIncrementDensity compactAutocorrKernel
    rw [← ENNReal.ofReal_mul (ρ.nonneg k _)]
    congr 1
    unfold weight density archLevySinhWeight
    dsimp only [ContinuousMap.coe_mk]
    ring
  symm
  rw [ENNReal.ofReal_add (mul_nonneg (archLevySinhWeight_nonneg hy) (hD y))
    (Finset.sum_nonneg fun k _ => add_nonneg (hn false k _) (hn true k _)),
    ENNReal.ofReal_sum_of_nonneg (fun k _ => add_nonneg (hn false k _) (hn true k _))]
  unfold sourceFibre
  congr 1
  · change ENNReal.ofReal (_ * _) = ENNReal.ofReal (_ * _)
    congr 1
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro k _
    rw [ENNReal.ofReal_add (hn false k _) (hn true k _)]
    have hl := hb false k
    have hr := hb true k
    simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] at hl hr
    rw [hl, hr]

theorem pairedKernel_source_extended (ρ : PhysicalCollarPartition n) {m : ℕ}
    (f : LogarithmicGridSource m) (hcut : (n + 2) ^ 2 ≤ m + 2) {y : ℝ} (hy : 0 ≤ y) :
    ENNReal.ofReal (ρ.pairedKernel y * autocorr f.1 0) ≤ ρ.sourceFibre f.1 y := by
  rw [ρ.sourceFibre_eq_ofReal f.1 hy]
  exact ENNReal.ofReal_le_ofReal (ρ.pairedKernel_source_pointwise f hcut y)

/-- Literal product-grid zeros give the coupled allocation energy bound,
including sources whose extended energy is infinite. -/
theorem pairedCoefficient_source_energy (ρ : PhysicalCollarPartition n) {m : ℕ}
    (f : LogarithmicGridSource m) (hcut : (n + 2) ^ 2 ≤ m + 2) :
    ENNReal.ofReal (ρ.pairedCoefficient * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  have hint := ρ.integrableOn_pairedKernel.mul_const (autocorr f.1 0)
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 logarithmicCollarRadius)]
      (fun y => ρ.pairedKernel y * autocorr f.1 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact mul_nonneg (ρ.pairedKernel_bounds hy.1.le).1 (autocorr_zero_nonneg f.1)
  change ENNReal.ofReal ((∫ y in Ioo 0 logarithmicCollarRadius, ρ.pairedKernel y) * _) ≤ _
  rw [← integral_mul_const, ofReal_integral_eq_lintegral_ofReal hint hn]
  calc
    _ ≤ ∫⁻ y in Ioo 0 logarithmicCollarRadius, ρ.sourceFibre f.1 y :=
      setLIntegral_mono' measurableSet_Ioo (fun y hy => ρ.pairedKernel_source_extended f hcut hy.1.le)
    _ = _ := ρ.lintegral_sourceFibre f.1

theorem pairedCoefficient_le_normalized_energy (ρ : PhysicalCollarPartition n) {m : ℕ}
    (f : SmoothLogarithmicGridSource m) (hcut : (n + 2) ^ 2 ≤ m + 2) :
    ρ.pairedCoefficient ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 := by
  have hb := (ρ.pairedCoefficient_source_energy f.1 hcut).trans
    (lintegral_mono_set (show Ioo 0 (logarithmicCollarEndpoint n) ⊆ Ioi 0 from fun _ hx => hx.1))
  have hi := integrableOn_biScaleLevyIntegrand f.2.1 f.1.1.hasCompactSupport
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun x => (autocorr f.1.1 0 - autocorr f.1.1 x) * archLevySinhWeight x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (autocorr_sub_nonneg f.1.1.hasCompactSupport f.1.1.continuous x)
      (archLevySinhWeight_pos hx).le
  have he : ENNReal.ofReal (biScaleLevyEnergy f.1.1) =
      ∫⁻ x in Ioi 0, continuousArchIncrementDensity (compactAutocorrKernel f.1.1) x :=
    ofReal_integral_eq_lintegral_ofReal hi hn
  rw [← he] at hb
  exact (le_div_iff₀ f.2.2).2
    ((ENNReal.ofReal_le_ofReal_iff (biScaleLevyEnergy_nonneg
      f.1.1.hasCompactSupport f.1.1.continuous)).1 hb)

/-- An unconditional actual-source specialization on the squared logarithmic grid. -/
theorem pairedCoefficient_le_squared_grid_energy (ρ : PhysicalCollarPartition n)
    (f : SmoothLogarithmicGridSource (n * (n + 4) + 2)) :
    ρ.pairedCoefficient ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 :=
  ρ.pairedCoefficient_le_normalized_energy f (by nlinarith)

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
