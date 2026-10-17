import GaloisForLFunctions.BiScaleUncertainty.SignedDyadicCollarPartition
import GaloisForLFunctions.BiScaleUncertainty.OptimalOriginAllocation
import GaloisForLFunctions.BiScaleUncertainty.LogarithmicCollarCoverage
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional

/-!
# Integrated origin-to-collar leverage

The nodes are `log 2` through `log (n + 2)`. Equal-multiplicity physical collar shares
avoid overlap double counting; measurable signed-coset shares minimize the origin penalty.
Their joint coefficient has a finite, strictly positive real integral despite the origin
singularity. The final bound holds for every compact-continuous scalar source satisfying
the literal grid zeros, and permits infinite source energy.

Optimality concerns origin allocation for this fixed physical partition. No global
optimality over physical partitions or autocorrelation extremizers is asserted.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

/-- Fixed radius for origin-to-logarithmic-collar transport. -/
def logarithmicCollarRadius : ℝ := Real.log 2 / 2

/-- Upper endpoint of the finite physical interval. -/
def logarithmicCollarEndpoint (n : ℕ) : ℝ := Real.log ((n + 2 : ℕ) : ℝ)

/-- Logarithmic node with zero-based index k. -/
def logarithmicCollarNode (k : ℕ) : ℝ := Real.log ((k + 2 : ℕ) : ℝ)

/-- Equal-multiplicity physical share on the complete finite logarithmic grid. -/
def logarithmicCollarShare (n k : ℕ) (x : ℝ) : ℝ :=
  collarPhysicalShare (Finset.range (n + 1))
    (fun j => truncatedPhysicalCollar (logarithmicCollarNode j)
      logarithmicCollarRadius (logarithmicCollarEndpoint n)) k x

/-- Pulled-back archimedean density on one signed collar. -/
def logarithmicCollarWeight (n : ℕ) (σ : Bool) (k : ℕ) (y : ℝ) : ℝ :=
  logarithmicCollarShare n k (logarithmicCollarNode k + collarSignedOffset σ y) *
    archLevySinhWeight (logarithmicCollarNode k + collarSignedOffset σ y)

/-- Total collar density on an offset fibre. -/
def logarithmicCollarMass (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (logarithmicCollarWeight n false k y + logarithmicCollarWeight n true k y)

/-- Sum of the signed coset Euclidean norms. -/
def logarithmicCollarBlockNorm (n : ℕ) (y : ℝ) : ℝ :=
  blockWeightNorm (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => logarithmicCollarWeight n j.2 k y)

/-- Exact optimized shared-origin coefficient, kept as one expression at the singular endpoint. -/
def logarithmicCollarKernel (n : ℕ) (y : ℝ) : ℝ :=
  archLevySinhWeight y + logarithmicCollarMass n y -
    Real.sqrt (archLevySinhWeight y ^ 2 + logarithmicCollarBlockNorm n y ^ 2)

/-- Integrated finite-grid transport coefficient. -/
def logarithmicCollarConstant (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y in Ioo 0 logarithmicCollarRadius, ENNReal.ofReal (logarithmicCollarKernel n y)

/-- Compactly supported continuous sources whose correlation vanishes at all grid nodes.
This is precisely the source regularity and zero set defining the finite-grid problem. -/
def LogarithmicGridSource (n : ℕ) :=
  {f : C_c(ℝ, ℝ) // ∀ k ∈ Finset.range (n + 1), autocorr f (logarithmicCollarNode k) = 0}

theorem logarithmicCollarShare_nonneg (n k : ℕ) (x : ℝ) :
    0 ≤ logarithmicCollarShare n k x := collarPhysicalShare_nonneg _ _ _ _

theorem measurable_logarithmicCollarShare (n k : ℕ) :
    Measurable (logarithmicCollarShare n k) := by
  exact measurable_collarPhysicalShare _ _
    (fun _ => measurableSet_Ioo.inter measurableSet_Ioo) _

theorem measurable_archLevySinhWeight : Measurable archLevySinhWeight :=
  (Real.continuous_exp.measurable.comp (measurable_id.div_const 2)).div
    Real.continuous_sinh.measurable

theorem measurable_logarithmicCollarWeight (n k : ℕ) (σ : Bool) :
    Measurable (logarithmicCollarWeight n σ k) := by
  have hs : Measurable (fun y => logarithmicCollarNode k + collarSignedOffset σ y) := by
    cases σ <;> simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  exact ((measurable_logarithmicCollarShare n k).comp hs).mul
    (measurable_archLevySinhWeight.comp hs)

/-- The physical cutoff forces all collar densities to be nonnegative globally. -/
theorem logarithmicCollarWeight_nonneg (n k : ℕ) (σ : Bool) (y : ℝ) :
    0 ≤ logarithmicCollarWeight n σ k y := by
  let x := logarithmicCollarNode k + collarSignedOffset σ y
  by_cases hx : x ∈ truncatedPhysicalCollar (logarithmicCollarNode k)
      logarithmicCollarRadius (logarithmicCollarEndpoint n)
  · exact mul_nonneg (logarithmicCollarShare_nonneg n k x)
      (archLevySinhWeight_pos hx.2.1).le
  · simp [logarithmicCollarWeight, logarithmicCollarShare, collarPhysicalShare, x] at hx ⊢
    simp [hx]

/-- All signed cosets together spend the origin density only once. -/
theorem logarithmicCollarKernel_pointwise (n : ℕ) (f : LogarithmicGridSource n) (y : ℝ) :
    logarithmicCollarKernel n y * autocorr f.1 0 ≤
      archLevySinhWeight y * (autocorr f.1 0 - autocorr f.1 y) +
      ∑ k ∈ Finset.range (n + 1),
        (logarithmicCollarWeight n false k y *
            (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode k - y)) +
         logarithmicCollarWeight n true k y *
            (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode k + y))) := by
  have h := shared_origin_leverage_bound (logarithmicSignedCosets n)
    (logarithmicSignedCosets_nonempty n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => logarithmicCollarWeight n j.2 k y)
    (fun j k => autocorr f.1 (logarithmicCollarNode k + collarSignedOffset j.2 y))
    (archLevySinhWeight y) (autocorr f.1 y) (autocorr f.1 0) (autocorr_zero_nonneg f.1)
    (fun j _ => autocorr_logarithmicCoset_sphere f.1 n j.1 f.2 j.2 y)
  rw [sum_logarithmicSignedCosets n (fun σ k => logarithmicCollarWeight n σ k y),
    sum_logarithmicSignedCosets n (fun σ k => logarithmicCollarWeight n σ k y *
      (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode k + collarSignedOffset σ y)))] at h
  simpa only [logarithmicCollarKernel, logarithmicCollarMass, logarithmicCollarBlockNorm,
    collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] using h

/-- The physical energy density after pulling both collar branches to the origin interval. -/
def logarithmicCollarFibreDensity (n : ℕ) (f : C_c(ℝ, ℝ)) (y : ℝ) : ℝ≥0∞ :=
  continuousArchIncrementDensity (compactAutocorrKernel f) y +
    ∑ k ∈ Finset.range (n + 1),
      (allocatedCollarDensity (Finset.range (n + 1)) logarithmicCollarNode
          logarithmicCollarRadius (logarithmicCollarEndpoint n)
          (continuousArchIncrementDensity (compactAutocorrKernel f)) k
          (logarithmicCollarNode k - y) +
       allocatedCollarDensity (Finset.range (n + 1)) logarithmicCollarNode
          logarithmicCollarRadius (logarithmicCollarEndpoint n)
          (continuousArchIncrementDensity (compactAutocorrKernel f)) k
          (logarithmicCollarNode k + y))

private theorem logarithmicCollar_branch_density (n k : ℕ) (σ : Bool)
    (f : C_c(ℝ, ℝ)) (y : ℝ) :
    ENNReal.ofReal (logarithmicCollarWeight n σ k y *
      (autocorr f 0 - autocorr f (logarithmicCollarNode k + collarSignedOffset σ y))) =
      allocatedCollarDensity (Finset.range (n + 1)) logarithmicCollarNode
        logarithmicCollarRadius (logarithmicCollarEndpoint n)
        (continuousArchIncrementDensity (compactAutocorrKernel f)) k
        (logarithmicCollarNode k + collarSignedOffset σ y) := by
  unfold allocatedCollarDensity continuousArchIncrementDensity compactAutocorrKernel
  change ENNReal.ofReal (_ * _) = ENNReal.ofReal (logarithmicCollarShare n k _) * _
  rw [← ENNReal.ofReal_mul (logarithmicCollarShare_nonneg n k _)]
  congr 1
  unfold logarithmicCollarWeight archLevySinhWeight
  dsimp only [ContinuousMap.coe_mk]
  ring

private theorem logarithmicCollar_pointwise_extended (n : ℕ) (f : LogarithmicGridSource n)
    {y : ℝ} (hy : 0 ≤ y) :
    ENNReal.ofReal (logarithmicCollarKernel n y * autocorr f.1 0) ≤
      logarithmicCollarFibreDensity n f.1 y := by
  have hD (x : ℝ) : 0 ≤ autocorr f.1 0 - autocorr f.1 x :=
    autocorr_sub_nonneg f.1.hasCompactSupport f.1.continuous x
  have hn (σ : Bool) (k : ℕ) (x : ℝ) :
      0 ≤ logarithmicCollarWeight n σ k y * (autocorr f.1 0 - autocorr f.1 x) :=
    mul_nonneg (logarithmicCollarWeight_nonneg n k σ y) (hD x)
  refine (ENNReal.ofReal_le_ofReal (logarithmicCollarKernel_pointwise n f y)).trans_eq ?_
  rw [ENNReal.ofReal_add (mul_nonneg (archLevySinhWeight_nonneg hy) (hD y))
    (Finset.sum_nonneg fun k _ => add_nonneg (hn false k _) (hn true k _)),
    ENNReal.ofReal_sum_of_nonneg (fun k _ => add_nonneg (hn false k _) (hn true k _))]
  unfold logarithmicCollarFibreDensity
  congr 1
  · change ENNReal.ofReal (_ * _) = ENNReal.ofReal (_ * _)
    congr 1
    change archLevySinhWeight y * (autocorr f.1 0 - autocorr f.1 y) =
      (autocorr f.1 0 - autocorr f.1 y) * archLevySinhWeight y
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro k _
    rw [ENNReal.ofReal_add (hn false k _) (hn true k _)]
    have hl := logarithmicCollar_branch_density n k false f.1 y
    have hr := logarithmicCollar_branch_density n k true f.1 y
    simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] at hl hr
    rw [hl, hr]

private theorem logarithmicCollarFibreDensity_integral (n : ℕ) (f : C_c(ℝ, ℝ)) :
    (∫⁻ y in Ioo 0 logarithmicCollarRadius, logarithmicCollarFibreDensity n f y) =
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f) x := by
  have hF := measurable_continuousArchIncrementDensity (compactAutocorrKernel f)
  have ha (k : ℕ) := measurable_allocatedCollarDensity (Finset.range (n + 1))
    logarithmicCollarNode logarithmicCollarRadius (logarithmicCollarEndpoint n)
    (continuousArchIncrementDensity (compactAutocorrKernel f)) hF k
  have hl (k : ℕ) : Measurable (fun y => allocatedCollarDensity (Finset.range (n + 1))
      logarithmicCollarNode logarithmicCollarRadius (logarithmicCollarEndpoint n)
      (continuousArchIncrementDensity (compactAutocorrKernel f)) k
      (logarithmicCollarNode k - y)) :=
    (ha k).comp (measurable_const.sub measurable_id)
  have hr (k : ℕ) : Measurable (fun y => allocatedCollarDensity (Finset.range (n + 1))
      logarithmicCollarNode logarithmicCollarRadius (logarithmicCollarEndpoint n)
      (continuousArchIncrementDensity (compactAutocorrKernel f)) k
      (logarithmicCollarNode k + y)) :=
    (ha k).comp (measurable_const.add measurable_id)
  unfold logarithmicCollarFibreDensity
  rw [lintegral_add_left hF]
  rw [lintegral_finsetSum (Finset.range (n + 1))
    (f := fun k y =>
      allocatedCollarDensity (Finset.range (n + 1)) logarithmicCollarNode
        logarithmicCollarRadius (logarithmicCollarEndpoint n)
        (continuousArchIncrementDensity (compactAutocorrKernel f)) k (logarithmicCollarNode k - y) +
      allocatedCollarDensity (Finset.range (n + 1)) logarithmicCollarNode
        logarithmicCollarRadius (logarithmicCollarEndpoint n)
        (continuousArchIncrementDensity (compactAutocorrKernel f)) k (logarithmicCollarNode k + y))
    (fun k _ => (hl k).add (hr k))]
  simp_rw [lintegral_add_left (hl _)]
  exact (arch_logarithmic_origin_collar_decomposition n (compactAutocorrKernel f)).symm

/-- Integrated origin-to-collar leverage on the entire finite interval. The source
has only the defining compact-continuous regularity and literal logarithmic-grid zeros;
no differentiability, finite-energy, or analytic bridge is assumed. -/
theorem integrated_logarithmic_origin_collar_bound (n : ℕ) (f : LogarithmicGridSource n) :
    logarithmicCollarConstant n * ENNReal.ofReal (autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  rw [logarithmicCollarConstant, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have heq : (fun y => ENNReal.ofReal (logarithmicCollarKernel n y) *
      ENNReal.ofReal (autocorr f.1 0)) =
      fun y => ENNReal.ofReal (logarithmicCollarKernel n y * autocorr f.1 0) := by
    funext y
    exact (ENNReal.ofReal_mul' (autocorr_zero_nonneg f.1)).symm
  rw [heq]
  calc
    _ ≤ ∫⁻ y in Ioo 0 logarithmicCollarRadius, logarithmicCollarFibreDensity n f.1 y :=
      setLIntegral_mono' measurableSet_Ioo (fun y hy => logarithmicCollar_pointwise_extended n f hy.1.le)
    _ = _ := logarithmicCollarFibreDensity_integral n f.1

/-- The fixed collar radius lies strictly above zero. -/
theorem logarithmicCollarRadius_pos : 0 < logarithmicCollarRadius :=
  div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- Every node lies at or beyond log 2. -/
theorem logarithmicCollarNode_ge_log_two (k : ℕ) : Real.log 2 ≤ logarithmicCollarNode k :=
  Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ k + 2 by omega))

theorem logarithmicCollarBlockNorm_le_mass (n : ℕ) (y : ℝ) :
    logarithmicCollarBlockNorm n y ≤ logarithmicCollarMass n y := by
  have hterm (j : ℕ × Bool) :
      Real.sqrt (∑ k ∈ logarithmicCosetNodes n j.1, logarithmicCollarWeight n j.2 k y ^ 2) ≤
        ∑ k ∈ logarithmicCosetNodes n j.1, logarithmicCollarWeight n j.2 k y := by
    apply (Real.sqrt_le_iff).2
    exact ⟨Finset.sum_nonneg (fun k _ => logarithmicCollarWeight_nonneg n k j.2 y),
      Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => logarithmicCollarWeight_nonneg n k j.2 y)⟩
  calc
    _ ≤ ∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1,
        logarithmicCollarWeight n j.2 k y := Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := sum_logarithmicSignedCosets n (fun σ k => logarithmicCollarWeight n σ k y)

/-- The singular coefficient is nonnegative and bounded above by collar mass. -/
theorem logarithmicCollarKernel_bounds (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ logarithmicCollarKernel n y ∧ logarithmicCollarKernel n y ≤ logarithmicCollarMass n y := by
  have hW := archLevySinhWeight_nonneg hy
  have hA : 0 ≤ logarithmicCollarBlockNorm n y := blockWeightNorm_nonneg _ _ _
  have hAB := logarithmicCollarBlockNorm_le_mass n y
  have hupper : Real.sqrt (archLevySinhWeight y ^ 2 + logarithmicCollarBlockNorm n y ^ 2) ≤
      archLevySinhWeight y + logarithmicCollarBlockNorm n y := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg hW hA, ?_⟩
    nlinarith [mul_nonneg hW hA]
  have hlower : archLevySinhWeight y ≤
      Real.sqrt (archLevySinhWeight y ^ 2 + logarithmicCollarBlockNorm n y ^ 2) :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
  unfold logarithmicCollarKernel
  constructor <;> linarith

/-- The exact coefficient is measurable despite collar cutoffs and zero blocks. -/
theorem measurable_logarithmicCollarKernel (n : ℕ) : Measurable (logarithmicCollarKernel n) := by
  have hB : Measurable (logarithmicCollarMass n) :=
    (Finset.range (n + 1)).measurable_sum fun k _ =>
      (measurable_logarithmicCollarWeight n k false).add (measurable_logarithmicCollarWeight n k true)
  have hA : Measurable (logarithmicCollarBlockNorm n) := by
    apply (logarithmicSignedCosets n).measurable_sum
    intro j _
    apply Real.continuous_sqrt.measurable.comp
    exact (logarithmicCosetNodes n j.1).measurable_sum fun k _ =>
      (measurable_logarithmicCollarWeight n k j.2).pow_const 2
  exact (measurable_archLevySinhWeight.add hB).sub
    (Real.continuous_sqrt.measurable.comp
      ((measurable_archLevySinhWeight.pow_const 2).add (hA.pow_const 2)))

/-- A uniform upper bound for the archimedean weight on all truncated collars. -/
def logarithmicCollarWeightBound (n : ℕ) : ℝ :=
  Real.exp (logarithmicCollarEndpoint n / 2) / Real.sinh logarithmicCollarRadius

theorem logarithmicCollarWeightBound_pos (n : ℕ) : 0 < logarithmicCollarWeightBound n :=
  div_pos (Real.exp_pos _) (Real.sinh_pos_iff.mpr logarithmicCollarRadius_pos)

/-- No signed collar reaches the origin interval. -/
theorem logarithmicCollar_point_ge_radius (k : ℕ) (σ : Bool)
    {y : ℝ} (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    logarithmicCollarRadius ≤ logarithmicCollarNode k + collarSignedOffset σ y := by
  have hn := logarithmicCollarNode_ge_log_two k
  have hr : 0 < logarithmicCollarRadius := logarithmicCollarRadius_pos
  have heq : Real.log 2 = 2 * logarithmicCollarRadius := by unfold logarithmicCollarRadius; ring
  cases σ <;> simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte] <;> linarith [hy.1, hy.2]

theorem logarithmicCollarWeight_le_bound (n k : ℕ) (hk : k ∈ Finset.range (n + 1)) (σ : Bool)
    {y : ℝ} (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    logarithmicCollarWeight n σ k y ≤ logarithmicCollarWeightBound n := by
  let x := logarithmicCollarNode k + collarSignedOffset σ y
  let E := fun j => truncatedPhysicalCollar (logarithmicCollarNode j)
    logarithmicCollarRadius (logarithmicCollarEndpoint n)
  by_cases hx : x ∈ E k
  · have hs : logarithmicCollarShare n k x ≤ 1 :=
      (Finset.single_le_sum (fun j _ => logarithmicCollarShare_nonneg n j x) hk).trans
        (collarPhysicalShare_capacity (Finset.range (n + 1)) E x)
    have hw : archLevySinhWeight x ≤ logarithmicCollarWeightBound n := by
      apply div_le_div₀ (Real.exp_pos _).le
      · apply Real.exp_le_exp.mpr
        linarith [hx.2.2]
      · exact Real.sinh_pos_iff.mpr logarithmicCollarRadius_pos
      · exact Real.sinh_le_sinh.mpr (logarithmicCollar_point_ge_radius k σ hy)
    exact (mul_le_of_le_one_left (archLevySinhWeight_pos hx.2.1).le hs).trans hw
  · have hs : logarithmicCollarShare n k x = 0 := by
      unfold logarithmicCollarShare collarPhysicalShare
      rw [indicator_of_notMem hx, zero_div]
    change logarithmicCollarShare n k x * archLevySinhWeight x ≤ _
    rw [hs, zero_mul]
    exact (logarithmicCollarWeightBound_pos n).le

/-- The integrated coefficient is finite without assuming finite source energy. -/
theorem logarithmicCollarConstant_lt_top (n : ℕ) : logarithmicCollarConstant n < ∞ := by
  have hbound {y : ℝ} (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
      logarithmicCollarKernel n y ≤ ((n + 1 : ℕ) : ℝ) * (2 * logarithmicCollarWeightBound n) := by
    apply (logarithmicCollarKernel_bounds n hy.1.le).2.trans
    calc
      logarithmicCollarMass n y ≤ ∑ k ∈ Finset.range (n + 1),
          (2 * logarithmicCollarWeightBound n) := by
        apply Finset.sum_le_sum
        intro k hk
        have h1 := logarithmicCollarWeight_le_bound n k hk false hy
        have h2 := logarithmicCollarWeight_le_bound n k hk true hy
        linarith
      _ = _ := by simp [nsmul_eq_mul]
  have hi : logarithmicCollarConstant n ≤
      ∫⁻ _y in Ioo 0 logarithmicCollarRadius,
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * (2 * logarithmicCollarWeightBound n)) :=
    setLIntegral_mono' measurableSet_Ioo (fun y hy => ENNReal.ofReal_le_ofReal (hbound hy))
  apply lt_of_le_of_lt hi
  rw [setLIntegral_const, Real.volume_Ioo]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The first left collar always carries strictly positive physical mass. -/
theorem logarithmicCollarWeight_first_left_pos (n : ℕ) {y : ℝ}
    (hy : y ∈ Ioo 0 logarithmicCollarRadius) : 0 < logarithmicCollarWeight n false 0 y := by
  let x := logarithmicCollarNode 0 - y
  let E := fun j => truncatedPhysicalCollar (logarithmicCollarNode j)
    logarithmicCollarRadius (logarithmicCollarEndpoint n)
  have hL : Real.log 2 ≤ logarithmicCollarEndpoint n := logarithmicCollarNode_ge_log_two n
  have hd := logarithmicCollarRadius_pos
  have hnode : logarithmicCollarNode 0 = Real.log 2 := by simp [logarithmicCollarNode]
  have heq : Real.log 2 = 2 * logarithmicCollarRadius := by unfold logarithmicCollarRadius; ring
  have hx : x ∈ E 0 := by
    change (logarithmicCollarNode 0 - logarithmicCollarRadius < x ∧
        x < logarithmicCollarNode 0 + logarithmicCollarRadius) ∧
      (0 < x ∧ x < logarithmicCollarEndpoint n)
    dsimp [x]
    rw [hnode]
    constructor <;> constructor <;> linarith [hy.1, hy.2]
  have hM : 0 < collarMultiplicity (Finset.range (n + 1)) E x := by
    have hsum := Finset.single_le_sum (s := Finset.range (n + 1))
      (f := fun j => (E j).indicator (fun _ => (1 : ℝ)) x)
      (fun j _ => by by_cases hj : x ∈ E j <;> simp [hj]) (by simp : 0 ∈ Finset.range (n + 1))
    exact lt_of_lt_of_le (by simp [hx]) hsum
  have hs : 0 < logarithmicCollarShare n 0 x := by
    change 0 < (E 0).indicator (fun _ => (1 : ℝ)) x / _
    rw [indicator_of_mem hx]
    exact div_pos zero_lt_one hM
  have hw := archLevySinhWeight_pos hx.2.1
  simpa only [logarithmicCollarWeight, collarSignedOffset, Bool.false_eq_true,
    ↓reduceIte, ← sub_eq_add_neg] using mul_pos hs hw

/-- A positive first collar makes the complete coefficient strictly positive. -/
theorem logarithmicCollarKernel_pos (n : ℕ) {y : ℝ}
    (hy : y ∈ Ioo 0 logarithmicCollarRadius) : 0 < logarithmicCollarKernel n y := by
  have hW := archLevySinhWeight_pos hy.1
  have hfirst := logarithmicCollarWeight_first_left_pos n hy
  have hB : 0 < logarithmicCollarMass n y := by
    apply lt_of_lt_of_le (add_pos_of_pos_of_nonneg hfirst (logarithmicCollarWeight_nonneg n 0 true y))
    exact Finset.single_le_sum
      (fun k _ => add_nonneg (logarithmicCollarWeight_nonneg n k false y)
        (logarithmicCollarWeight_nonneg n k true y)) (by simp : 0 ∈ Finset.range (n + 1))
  have hA : 0 ≤ logarithmicCollarBlockNorm n y := blockWeightNorm_nonneg _ _ _
  have hAB := logarithmicCollarBlockNorm_le_mass n y
  have hs : Real.sqrt (archLevySinhWeight y ^ 2 + logarithmicCollarBlockNorm n y ^ 2) <
      archLevySinhWeight y + logarithmicCollarMass n y := by
    apply (Real.sqrt_lt' (add_pos hW hB)).2
    nlinarith [mul_pos hW hB]
  exact sub_pos.mpr hs

/-- The explicit integrated transport coefficient is strictly positive. -/
theorem logarithmicCollarConstant_pos (n : ℕ) : 0 < logarithmicCollarConstant n := by
  rw [logarithmicCollarConstant, setLIntegral_pos_iff (measurable_logarithmicCollarKernel n).ennreal_ofReal]
  have heq : Function.support (fun y => ENNReal.ofReal (logarithmicCollarKernel n y)) ∩
      Ioo 0 logarithmicCollarRadius = Ioo 0 logarithmicCollarRadius := by
    ext y
    constructor
    · exact fun hy => hy.2
    · intro hy
      exact ⟨(ENNReal.ofReal_pos.mpr (logarithmicCollarKernel_pos n hy)).ne', hy⟩
  rw [heq, Real.volume_Ioo, sub_zero]
  exact ENNReal.ofReal_pos.mpr logarithmicCollarRadius_pos

/-- Rationalization cancels the nonintegrable origin terms before integration. -/
theorem logarithmicCollarKernel_rationalized (n : ℕ) {y : ℝ} (hy : 0 < y) :
    logarithmicCollarKernel n y = logarithmicCollarMass n y -
      logarithmicCollarBlockNorm n y ^ 2 /
        (Real.sqrt (archLevySinhWeight y ^ 2 + logarithmicCollarBlockNorm n y ^ 2) +
          archLevySinhWeight y) := by
  have hW := archLevySinhWeight_pos hy
  have hS := Real.sq_sqrt (add_nonneg (sq_nonneg (archLevySinhWeight y))
    (sq_nonneg (logarithmicCollarBlockNorm n y)))
  have hden : Real.sqrt (archLevySinhWeight y ^ 2 + logarithmicCollarBlockNorm n y ^ 2) +
      archLevySinhWeight y ≠ 0 := (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hW).ne'
  unfold logarithmicCollarKernel
  field_simp
  nlinarith only [hS]

/-- Euclidean norm of the prescribed densities on one signed odd coset. -/
def logarithmicCosetWeightNorm (n : ℕ) (j : ℕ × Bool) (y : ℝ) : ℝ :=
  Real.sqrt (∑ k ∈ logarithmicCosetNodes n j.1, logarithmicCollarWeight n j.2 k y ^ 2)

/-- Optimal origin share matched to the physical Lévy density of a signed coset. -/
def logarithmicOptimalCosetShare (n : ℕ) (j : ℕ × Bool) (y : ℝ) : ℝ :=
  logarithmicCosetWeightNorm n j y / logarithmicCollarBlockNorm n y

/-- The optimal density shares can be chosen measurably on the complete fibre interval. -/
theorem measurable_logarithmicOptimalCosetShare (n : ℕ) (j : ℕ × Bool) :
    Measurable (logarithmicOptimalCosetShare n j) := by
  have hq (j : ℕ × Bool) : Measurable (logarithmicCosetWeightNorm n j) :=
    Real.continuous_sqrt.measurable.comp
      ((logarithmicCosetNodes n j.1).measurable_sum
        (fun k _ => (measurable_logarithmicCollarWeight n k j.2).pow_const 2))
  have hA : Measurable (logarithmicCollarBlockNorm n) :=
    (logarithmicSignedCosets n).measurable_sum (fun j _ => hq j)
  exact (hq j).div hA

/-- A surviving first left collar makes the aggregate block norm positive. -/
theorem logarithmicCollarBlockNorm_pos (n : ℕ) {y : ℝ}
    (hy : y ∈ Ioo 0 logarithmicCollarRadius) : 0 < logarithmicCollarBlockNorm n y := by
  have h0 : 0 ∈ logarithmicCosetNodes n (logNodeOddPart 0) := by
    simp [logarithmicCosetNodes]
  have h1 : (logNodeOddPart 0, false) ∈ logarithmicSignedCosets n := by
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_image.mpr ⟨0, by simp, rfl⟩, Finset.mem_univ _⟩
  have hl : logarithmicCollarWeight n false 0 y ≤
      logarithmicCosetWeightNorm n (logNodeOddPart 0, false) y :=
    Real.le_sqrt_of_sq_le (Finset.single_le_sum
      (f := fun k => logarithmicCollarWeight n false k y ^ 2) (fun k _ => sq_nonneg _) h0)
  have hu : logarithmicCosetWeightNorm n (logNodeOddPart 0, false) y ≤
      logarithmicCollarBlockNorm n y :=
    Finset.single_le_sum (f := fun j => logarithmicCosetWeightNorm n j y)
      (fun j _ => Real.sqrt_nonneg _) h1
  exact (logarithmicCollarWeight_first_left_pos n hy).trans_le (hl.trans hu)

/-- The density-matched coset shares form a probability vector and attain the
smallest aggregate sphere penalty among every allocation of the same origin density. -/
theorem logarithmicOptimalCosetShare_optimal (n : ℕ) {y : ℝ}
    (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    (∑ j ∈ logarithmicSignedCosets n, logarithmicOptimalCosetShare n j y) = 1 ∧
    (∀ j, 0 ≤ logarithmicOptimalCosetShare n j y) ∧
    (∑ j ∈ logarithmicSignedCosets n,
      Real.sqrt ((archLevySinhWeight y * logarithmicOptimalCosetShare n j y) ^ 2 +
        logarithmicCosetWeightNorm n j y ^ 2)) =
      Real.sqrt (archLevySinhWeight y ^ 2 + logarithmicCollarBlockNorm n y ^ 2) ∧
    ∀ α : ℕ × Bool → ℝ, (∑ j ∈ logarithmicSignedCosets n, α j) = archLevySinhWeight y →
      Real.sqrt (archLevySinhWeight y ^ 2 + logarithmicCollarBlockNorm n y ^ 2) ≤
        ∑ j ∈ logarithmicSignedCosets n, Real.sqrt (α j ^ 2 + logarithmicCosetWeightNorm n j y ^ 2) := by
  have hA := logarithmicCollarBlockNorm_pos n hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [logarithmicOptimalCosetShare, ← Finset.sum_div]
    change logarithmicCollarBlockNorm n y / logarithmicCollarBlockNorm n y = 1
    exact div_self hA.ne'
  · intro j
    exact div_nonneg (Real.sqrt_nonneg _) hA.le
  · exact origin_allocation_proportional_cost (logarithmicSignedCosets n)
      (archLevySinhWeight y) (fun j => logarithmicCosetWeightNorm n j y)
      (fun j _ => Real.sqrt_nonneg _) hA.ne'
  · intro α hα
    have h := origin_allocation_cost_lower (logarithmicSignedCosets n) α
      (fun j => logarithmicCosetWeightNorm n j y)
    rw [hα] at h
    exact h

private theorem logarithmicCollarKernel_ae_nonneg (n : ℕ) :
    0 ≤ᵐ[volume.restrict (Ioo 0 logarithmicCollarRadius)] logarithmicCollarKernel n := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact (logarithmicCollarKernel_bounds n hy.1.le).1

/-- The optimized coefficient has an ordinary real Lebesgue integral across the origin. -/
theorem integrableOn_logarithmicCollarKernel (n : ℕ) :
    IntegrableOn (logarithmicCollarKernel n) (Ioo 0 logarithmicCollarRadius) := by
  exact ⟨(measurable_logarithmicCollarKernel n).aestronglyMeasurable.restrict,
    (hasFiniteIntegral_iff_ofReal (logarithmicCollarKernel_ae_nonneg n)).2
      (logarithmicCollarConstant_lt_top n)⟩

/-- The real, strictly positive finite-interval uncertainty coefficient. -/
def logarithmicCollarRealConstant (n : ℕ) : ℝ :=
  ∫ y in Ioo 0 logarithmicCollarRadius, logarithmicCollarKernel n y

theorem logarithmicCollarRealConstant_eq_toReal (n : ℕ) :
    logarithmicCollarRealConstant n = (logarithmicCollarConstant n).toReal :=
  integral_eq_lintegral_of_nonneg_ae (logarithmicCollarKernel_ae_nonneg n)
    (integrableOn_logarithmicCollarKernel n).aestronglyMeasurable

theorem logarithmicCollarRealConstant_pos (n : ℕ) : 0 < logarithmicCollarRealConstant n := by
  rw [logarithmicCollarRealConstant_eq_toReal]
  exact ENNReal.toReal_pos (logarithmicCollarConstant_pos n).ne'
    (logarithmicCollarConstant_lt_top n).ne

/-- The finite positive real coefficient bounds every admissible correlation energy,
including correlations of infinite energy, with no unproved input assumptions. -/
theorem integrated_logarithmic_origin_collar_real_bound (n : ℕ) (f : LogarithmicGridSource n) :
    ENNReal.ofReal (logarithmicCollarRealConstant n * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  rw [ENNReal.ofReal_mul (logarithmicCollarRealConstant_pos n).le,
    logarithmicCollarRealConstant_eq_toReal,
    ENNReal.ofReal_toReal (logarithmicCollarConstant_lt_top n).ne]
  exact integrated_logarithmic_origin_collar_bound n f

end
end GaloisForLFunctions.BiScaleUncertainty
