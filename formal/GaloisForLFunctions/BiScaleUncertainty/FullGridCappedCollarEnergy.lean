import GaloisForLFunctions.BiScaleUncertainty.CappedCosetSphereDuality
import GaloisForLFunctions.BiScaleUncertainty.PairedCollarCutoffStability

/-!
# Full-grid collar energy with capped low-node coupling

Every signed odd coset keeps its full sphere through the physical grid endpoint.
Product-zero constraints couple only the low subblocks. The exact capped support
therefore improves the original physical coefficient without discarding high
nodes. Compact maximization supplies measurability for arbitrary physical shares.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

/-- Nodes above the low cutoff, inside the original whole coset. -/
def logarithmicHighCosetNodes (n k p : ℕ) : Finset ℕ :=
  logarithmicCosetNodes n p \ logarithmicCosetNodes k p

theorem sum_logarithmic_low_high {n k : ℕ} (hk : k ≤ n) (p : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ logarithmicCosetNodes k p, a j) +
      (∑ j ∈ logarithmicHighCosetNodes n k p, a j) =
        ∑ j ∈ logarithmicCosetNodes n p, a j := by
  have h := Finset.sum_sdiff (logarithmicCosetNodes_subset hk p) (f := a)
  dsimp [logarithmicHighCosetNodes]
  linarith

theorem collarBlockSize_sq (s : Finset ℕ) (a : ℕ → ℝ) :
    collarBlockSize s a ^ 2 = ∑ j ∈ s, a j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem collarBlock_pairing_le (s : Finset ℕ) (a u : ℕ → ℝ) :
    (∑ j ∈ s, a j * u j) ≤ collarBlockSize s a * collarBlockSize s u := by
  have h := sphere_weighted_sum_le_sqrt_mul s 0 a u 0 (collarBlockSize s u)
    (Real.sqrt_nonneg _) (by
      simp only [zero_pow (by decide : 2 ≠ 0), zero_add, collarBlockSize_sq, le_refl])
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add, collarBlockSize] using h

namespace PhysicalCollarPartition
variable {n : ℕ}

def lowBlockSize (ρ : PhysicalCollarPartition n) (k : ℕ) (y : ℝ) (σ : Bool) (p : ℕ) : ℝ :=
  collarBlockSize (logarithmicCosetNodes k p) (fun j => ρ.weight σ j y)

def highBlockSize (ρ : PhysicalCollarPartition n) (k : ℕ) (y : ℝ) (σ : Bool) (p : ℕ) : ℝ :=
  collarBlockSize (logarithmicHighCosetNodes n k p) (fun j => ρ.weight σ j y)

def cappedAngularSupport (ρ : PhysicalCollarPartition n) (k : ℕ) (y : ℝ) : ℝ :=
  cappedCosetSupport (logarithmicOddCosets n) (ρ.lowBlockSize k y) (ρ.highBlockSize k y)

def cappedKernel (ρ : PhysicalCollarPartition n) (k : ℕ) (y : ℝ) : ℝ :=
  archLevySinhWeight y + ρ.mass y -
    Real.sqrt (archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2)

def cappedCoefficient (ρ : PhysicalCollarPartition n) (k : ℕ) : ℝ :=
  ∫ y in Ioo 0 logarithmicCollarRadius, ρ.cappedKernel k y

theorem cappedAngularSupport_nonneg (ρ : PhysicalCollarPartition n) (k : ℕ) (y : ℝ) :
    0 ≤ ρ.cappedAngularSupport k y :=
  cappedCosetSupport_nonneg _ _ _ (fun _ _ => Real.sqrt_nonneg _)

/-- The exact low/high split recovers the original whole-block weight norm. -/
theorem low_high_blockSize_sq (ρ : PhysicalCollarPartition n) {k : ℕ} (hk : k ≤ n)
    (y : ℝ) (σ : Bool) (p : ℕ) :
    ρ.lowBlockSize k y σ p ^ 2 + ρ.highBlockSize k y σ p ^ 2 =
      ∑ j ∈ logarithmicCosetNodes n p, ρ.weight σ j y ^ 2 := by
  unfold lowBlockSize highBlockSize
  rw [collarBlockSize_sq, collarBlockSize_sq]
  exact sum_logarithmic_low_high hk p _

theorem cappedAngularSupport_le_blockNorm (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) (y : ℝ) : ρ.cappedAngularSupport k y ≤ ρ.blockNorm y := by
  have h := cappedCosetSupport_le_independent (logarithmicOddCosets n)
    (ρ.lowBlockSize k y) (ρ.highBlockSize k y)
  simp_rw [ρ.low_high_blockSize_sq hk] at h
  rw [ρ.blockNorm_eq_signBlockNorm_add]
  simpa only [cappedAngularSupport, Fintype.sum_bool, signBlockNorm, blockWeightNorm,
    add_comm] using h

theorem kernel_le_cappedKernel (ρ : PhysicalCollarPartition n) {k : ℕ} (hk : k ≤ n) (y : ℝ) :
    ρ.kernel y ≤ ρ.cappedKernel k y := by
  have ha := ρ.cappedAngularSupport_nonneg k y
  have hb := ρ.cappedAngularSupport_le_blockNorm hk y
  have hs : Real.sqrt (archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2) ≤
      Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  unfold kernel cappedKernel
  linarith

theorem cappedKernel_bounds (ρ : PhysicalCollarPartition n) {k : ℕ} (hk : k ≤ n)
    {y : ℝ} (hy : 0 ≤ y) : 0 ≤ ρ.cappedKernel k y ∧ ρ.cappedKernel k y ≤ ρ.mass y := by
  refine ⟨(ρ.kernel_bounds hy).1.trans (ρ.kernel_le_cappedKernel hk y), ?_⟩
  have h : archLevySinhWeight y ≤ Real.sqrt
      (archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (ρ.cappedAngularSupport k y)])
  unfold cappedKernel
  linarith

theorem measurable_lowBlockSize (ρ : PhysicalCollarPartition n) (k : ℕ) :
    Measurable (ρ.lowBlockSize k) := by
  refine measurable_pi_lambda _ (fun σ => measurable_pi_lambda _ (fun p => ?_))
  exact Real.continuous_sqrt.measurable.comp
    ((logarithmicCosetNodes k p).measurable_sum fun j _ => (ρ.measurable_weight σ j).pow_const 2)

theorem measurable_highBlockSize (ρ : PhysicalCollarPartition n) (k : ℕ) :
    Measurable (ρ.highBlockSize k) := by
  refine measurable_pi_lambda _ (fun σ => measurable_pi_lambda _ (fun p => ?_))
  exact Real.continuous_sqrt.measurable.comp
    ((logarithmicHighCosetNodes n k p).measurable_sum fun j _ => (ρ.measurable_weight σ j).pow_const 2)

private theorem measurable_angularSupport_map (n : ℕ) :
    Measurable (fun p : (Bool → ℕ → ℝ) × (Bool → ℕ → ℝ) =>
      cappedCosetSupport (logarithmicOddCosets n) p.1 p.2) :=
  (continuous_cappedCosetSupport (logarithmicOddCosets n)).measurable

theorem measurable_cappedAngularSupport (ρ : PhysicalCollarPartition n) (k : ℕ) :
    Measurable (ρ.cappedAngularSupport k) := by
  change Measurable ((fun p : (Bool → ℕ → ℝ) × (Bool → ℕ → ℝ) =>
    cappedCosetSupport (logarithmicOddCosets n) p.1 p.2) ∘
      (fun y : ℝ => (ρ.lowBlockSize k y, ρ.highBlockSize k y)))
  exact (measurable_angularSupport_map n).comp
    ((ρ.measurable_lowBlockSize k).prodMk (ρ.measurable_highBlockSize k))

theorem measurable_cappedKernel (ρ : PhysicalCollarPartition n) (k : ℕ) :
    Measurable (ρ.cappedKernel k) :=
  (measurable_archLevySinhWeight.add ρ.measurable_mass).sub
    (Real.continuous_sqrt.measurable.comp
      ((measurable_archLevySinhWeight.pow_const 2).add
        ((ρ.measurable_cappedAngularSupport k).pow_const 2)))

theorem integrableOn_cappedKernel (ρ : PhysicalCollarPartition n) {k : ℕ} (hk : k ≤ n) :
    IntegrableOn (ρ.cappedKernel k) (Ioo 0 logarithmicCollarRadius) := by
  apply volume.integrableOn_of_bounded (M := ((n + 1 : ℕ) : ℝ) * (2 * logarithmicCollarWeightBound n))
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    (ρ.measurable_cappedKernel k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have h := ρ.cappedKernel_bounds hk hy.1.le
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.trans (ρ.mass_le_bound y)

theorem coefficient_le_cappedCoefficient (ρ : PhysicalCollarPartition n) {k : ℕ} (hk : k ≤ n) :
    ρ.coefficient ≤ ρ.cappedCoefficient k :=
  integral_mono_ae ρ.integrableOn_kernel (ρ.integrableOn_cappedKernel hk)
    (Filter.Eventually.of_forall (ρ.kernel_le_cappedKernel hk))

/-- Actual grid zeros supply both the full spheres and low product-pair spheres. -/
theorem cappedKernel_source_pointwise (ρ : PhysicalCollarPartition n) {k : ℕ}
    (f : LogarithmicGridSource n) (hcut : (k + 2) ^ 2 ≤ n + 2) (y : ℝ) :
    ρ.cappedKernel k y * autocorr f.1 0 ≤
      archLevySinhWeight y * (autocorr f.1 0 - autocorr f.1 y) +
      ∑ j ∈ Finset.range (n + 1),
        (ρ.weight false j y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode j - y)) +
         ρ.weight true j y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode j + y))) := by
  have hk : k ≤ n := by nlinarith
  let u (σ : Bool) (j : ℕ) := autocorr f.1 (logarithmicCollarNode j + collarSignedOffset σ y)
  let x (σ : Bool) (p : ℕ) := collarBlockSize (logarithmicCosetNodes k p) (u σ)
  let z (σ : Bool) (p : ℕ) := collarBlockSize (logarithmicHighCosetNodes n k p) (u σ)
  have hwhole (σ : Bool) (p : ℕ) :
      autocorr f.1 y ^ 2 + x σ p ^ 2 + z σ p ^ 2 ≤ autocorr f.1 0 ^ 2 := by
    have he : x σ p ^ 2 + z σ p ^ 2 = ∑ j ∈ logarithmicCosetNodes n p, u σ j ^ 2 := by
      dsimp [x, z]
      rw [collarBlockSize_sq, collarBlockSize_sq]
      exact sum_logarithmic_low_high hk p _
    have h := autocorr_logarithmicCoset_sphere f.1 n p f.2 σ y
    change autocorr f.1 y ^ 2 + (∑ j ∈ logarithmicCosetNodes n p, u σ j ^ 2) ≤ _ at h
    linarith
  have hpair (p q : ℕ) :
      autocorr f.1 y ^ 2 + x false p ^ 2 + x true q ^ 2 ≤ autocorr f.1 0 ^ 2 := by
    dsimp [x]
    rw [collarBlockSize_sq, collarBlockSize_sq]
    simpa only [u, collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg]
      using autocorr_paired_logarithmicCoset_sphere f hcut p q y
  have h := capped_spheres_weighted_sum_le (logarithmicOddCosets n)
    (logarithmicOddCosets_nonempty n) (ρ.lowBlockSize k y) (ρ.highBlockSize k y) x z
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ _ => Real.sqrt_nonneg _)
    (archLevySinhWeight y) (autocorr f.1 y) (autocorr f.1 0) (autocorr_zero_nonneg f.1)
    (fun σ p _ => hwhole σ p) (fun p _ q _ => hpair p q)
  have hblock (σ : Bool) (p : ℕ) :
      (∑ j ∈ logarithmicCosetNodes n p, ρ.weight σ j y * u σ j) ≤
        ρ.lowBlockSize k y σ p * x σ p + ρ.highBlockSize k y σ p * z σ p := by
    rw [← sum_logarithmic_low_high hk p]
    exact add_le_add (collarBlock_pairing_le _ _ _) (collarBlock_pairing_le _ _ _)
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset Bool)) =>
    Finset.sum_le_sum (fun p (_ : p ∈ logarithmicOddCosets n) => hblock σ p))
  have he : (∑ σ : Bool, ∑ p ∈ logarithmicOddCosets n,
      ∑ j ∈ logarithmicCosetNodes n p, ρ.weight σ j y * u σ j) =
        ∑ j ∈ Finset.range (n + 1),
          (ρ.weight false j y * u false j + ρ.weight true j y * u true j) := by
    simp only [sum_logarithmicCosetNodes, Fintype.sum_bool, Finset.sum_add_distrib, add_comm]
  rw [he] at hsum
  change archLevySinhWeight y * autocorr f.1 y + _ ≤
    Real.sqrt (archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2) * autocorr f.1 0 at h
  have hh : archLevySinhWeight y * autocorr f.1 y +
      (∑ j ∈ Finset.range (n + 1),
        (ρ.weight false j y * u false j + ρ.weight true j y * u true j)) ≤
      Real.sqrt (archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2) * autocorr f.1 0 := by
    linarith
  simp only [u, collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] at hh
  change (archLevySinhWeight y +
    (∑ j ∈ Finset.range (n + 1), (ρ.weight false j y + ρ.weight true j y)) -
    Real.sqrt (archLevySinhWeight y ^ 2 + ρ.cappedAngularSupport k y ^ 2)) * autocorr f.1 0 ≤ _
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul] at hh ⊢
  nlinarith

/-- The full physical interval survives the stronger pointwise coupling. -/
theorem cappedCoefficient_source_energy (ρ : PhysicalCollarPartition n) {k : ℕ}
    (f : LogarithmicGridSource n) (hcut : (k + 2) ^ 2 ≤ n + 2) :
    ENNReal.ofReal (ρ.cappedCoefficient k * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  have hk : k ≤ n := by nlinarith
  have hint := (ρ.integrableOn_cappedKernel hk).mul_const (autocorr f.1 0)
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 logarithmicCollarRadius)]
      (fun y => ρ.cappedKernel k y * autocorr f.1 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact mul_nonneg (ρ.cappedKernel_bounds hk hy.1.le).1 (autocorr_zero_nonneg f.1)
  change ENNReal.ofReal ((∫ y in Ioo 0 logarithmicCollarRadius, ρ.cappedKernel k y) * _) ≤ _
  rw [← integral_mul_const, ofReal_integral_eq_lintegral_ofReal hint hn]
  calc
    _ ≤ ∫⁻ y in Ioo 0 logarithmicCollarRadius, ρ.sourceFibre f.1 y := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro y hy
      rw [ρ.sourceFibre_eq_ofReal f.1 hy.1.le]
      exact ENNReal.ofReal_le_ofReal (ρ.cappedKernel_source_pointwise f hcut y)
    _ = _ := ρ.lintegral_sourceFibre f.1

theorem cappedCoefficient_le_normalized_energy (ρ : PhysicalCollarPartition n) {k : ℕ}
    (f : SmoothLogarithmicGridSource n) (hcut : (k + 2) ^ 2 ≤ n + 2) :
    ρ.cappedCoefficient k ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 := by
  have hb := (ρ.cappedCoefficient_source_energy f.1 hcut).trans
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

/-- Full-grid source certificate with the largest product-admitted low cutoff. -/
theorem fullGrid_capped_energy {n : ℕ} (hn : 2 ≤ n) (ρ : PhysicalCollarPartition n)
    (f : SmoothLogarithmicGridSource n) :
    ρ.coefficient ≤ ρ.cappedCoefficient (productAdmittedCutoff n) ∧
      ρ.cappedCoefficient (productAdmittedCutoff n) ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 := by
  have hcut : (productAdmittedCutoff n + 2) ^ 2 ≤ n + 2 := by
    have hs : 2 ≤ Nat.sqrt (n + 2) := (Nat.le_sqrt').2 (by omega)
    unfold productAdmittedCutoff
    rw [Nat.sub_add_cancel hs]
    exact Nat.sqrt_le' _
  exact ⟨ρ.coefficient_le_cappedCoefficient (by nlinarith),
    ρ.cappedCoefficient_le_normalized_energy f hcut⟩

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
