import GaloisForLFunctions.BiScaleUncertainty.PairedCollarCapacity
import GaloisForLFunctions.BiScaleUncertainty.ProductCoupledCollarHierarchy
import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarCutoffStability
import Mathlib.Data.Nat.Sqrt

/-!
# Quantitative saturation of product-coupled collar certificates

The paired physical optimum is monotone and loses at most the physical retention
tail under cutoff retraction. Its supremum is exactly the limit of the
product-admitted source hierarchy. The largest admissible collar grid has size
`floor(sqrt(N))`, giving an explicit fourth-root cutoff error for that hierarchy.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

namespace PhysicalCollarPartition
variable {n m : ℕ}

theorem pairedKernel_le_extend (ρ : PhysicalCollarPartition n) (hm : n ≤ m) (y : ℝ) :
    ρ.pairedKernel y ≤ (ρ.extend hm).pairedKernel y := by
  rw [ρ.pairedKernel_eq_array, (ρ.extend hm).pairedKernel_eq_array,
    ← logarithmicPairedArrayKernel_pad hm]
  apply logarithmicPairedArrayKernel_mono
  · intro σ k
    by_cases hk : k < n + 1
    · simpa only [collarArrayPad, if_pos hk] using ρ.weight_nonneg σ k y
    · simp only [collarArrayPad, if_neg hk, le_refl]
  · exact fun σ k => ρ.pad_weight_le_extend hm σ k y

theorem pairedCoefficient_le_extend (ρ : PhysicalCollarPartition n) (hm : n ≤ m) :
    ρ.pairedCoefficient ≤ (ρ.extend hm).pairedCoefficient :=
  integral_mono_ae ρ.integrableOn_pairedKernel (ρ.extend hm).integrableOn_pairedKernel
    (Filter.Eventually.of_forall (ρ.pairedKernel_le_extend hm))

theorem pairedOptimalCoefficient_monotone : Monotone pairedOptimalCoefficient := by
  intro n m hnm
  apply csSup_le
  · exact ⟨(equalMultiplicity n).pairedCoefficient, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (ρ.pairedCoefficient_le_extend hnm).trans (ρ.extend hnm).pairedCoefficient_le_optimal

theorem pairedKernel_sub_retract_le_retentionFibre (η : PhysicalCollarPartition m) (hm : n ≤ m)
    (y : ℝ) : η.pairedKernel y - (η.retract hm).pairedKernel y ≤ η.retentionFibre n y := by
  let a := collarArrayPad n (fun σ k => (η.retract hm).weight σ k y)
  let e := fun σ k => η.weight σ k y *
    collarRetentionPrice n (logarithmicCollarNode k + collarSignedOffset σ y)
  have ha (σ : Bool) (k : ℕ) : 0 ≤ a σ k := by
    dsimp [a, collarArrayPad]
    split_ifs
    · exact (η.retract hm).weight_nonneg σ k y
    · exact le_rfl
  have he (σ : Bool) (k : ℕ) : 0 ≤ e σ k :=
    mul_nonneg (η.weight_nonneg σ k y) (collarRetentionPrice_bounds n _).1
  have hab (σ : Bool) (k : ℕ) : η.weight σ k y ≤ a σ k + e σ k := by
    by_cases hx : logarithmicCollarNode k + collarSignedOffset σ y < logarithmicCollarRetention n
    · have heq : a σ k = η.weight σ k y := η.pad_retract_weight_eq hm σ k y hx
      rw [heq]
      exact le_add_of_nonneg_right (he σ k)
    · have hp : collarRetentionPrice n (logarithmicCollarNode k + collarSignedOffset σ y) = 1 :=
        indicator_of_mem (show logarithmicCollarNode k + collarSignedOffset σ y ∈
          Ici (logarithmicCollarRetention n) from le_of_not_gt hx) (fun _ => (1 : ℝ))
      dsimp only [e]
      rw [hp, mul_one]
      exact le_add_of_nonneg_left (ha σ k)
  have h := logarithmicPairedArrayKernel_error_bound m a (fun σ k => η.weight σ k y) e
    (archLevySinhWeight y) ha (fun σ k => η.weight_nonneg σ k y) he hab
  dsimp only [a] at h
  rw [logarithmicPairedArrayKernel_pad hm] at h
  rw [η.pairedKernel_eq_array, (η.retract hm).pairedKernel_eq_array]
  simpa only [e, retentionFibre, collarSignedOffset, Bool.false_eq_true,
    ↓reduceIte, ← sub_eq_add_neg] using h

theorem pairedCoefficient_sub_retract_le_tail (η : PhysicalCollarPartition m) (hm : n ≤ m) :
    η.pairedCoefficient - (η.retract hm).pairedCoefficient ≤ collarCutoffTailMass n := by
  have h := integral_mono_ae (η.integrableOn_pairedKernel.sub (η.retract hm).integrableOn_pairedKernel)
    (η.integrableOn_retentionFibre n)
    (Filter.Eventually.of_forall (η.pairedKernel_sub_retract_le_retentionFibre hm))
  change (∫ y in Ioo 0 logarithmicCollarRadius, η.pairedKernel y - (η.retract hm).pairedKernel y) ≤
    ∫ y in Ioo 0 logarithmicCollarRadius, η.retentionFibre n y at h
  rw [integral_sub η.integrableOn_pairedKernel (η.retract hm).integrableOn_pairedKernel] at h
  exact h.trans (η.integral_retentionFibre_le_tail n)

/-- The optimized coupled coefficients have the same physical-tail stability bound. -/
theorem pairedOptimalCoefficient_sub_le_tail {n m : ℕ} (hm : n ≤ m) :
    pairedOptimalCoefficient m - pairedOptimalCoefficient n ≤ collarCutoffTailMass n := by
  have h : pairedOptimalCoefficient m ≤ pairedOptimalCoefficient n + collarCutoffTailMass n := by
    apply csSup_le
    · exact ⟨(equalMultiplicity m).pairedCoefficient, equalMultiplicity m, rfl⟩
    · rintro c ⟨η, rfl⟩
      have hc := η.pairedCoefficient_sub_retract_le_tail hm
      have hp := (η.retract hm).pairedCoefficient_le_optimal
      linarith
  linarith

theorem pairedOptimalCoefficient_bddAbove : BddAbove (Set.range pairedOptimalCoefficient) :=
  ⟨collarTailMass, by rintro c ⟨n, rfl⟩; exact pairedOptimalCoefficient_le_collarTailMass n⟩

end PhysicalCollarPartition

/-- Delayed product admission changes finite cutoffs, but not the supremum of paired optima. -/
theorem limitingProductCoupledCoefficient_eq_iSup_paired :
    limitingProductCoupledCoefficient = ⨆ n, PhysicalCollarPartition.pairedOptimalCoefficient n := by
  apply le_antisymm
  · apply ciSup_le
    intro n
    apply max_le
    · exact (PhysicalCollarPartition.optimalCoefficient_le_pairedOptimalCoefficient n).trans
        (le_ciSup PhysicalCollarPartition.pairedOptimalCoefficient_bddAbove n)
    · apply Finset.sup'_le
      intro k _
      unfold productAdmittedCoefficient
      split_ifs
      · exact le_ciSup PhysicalCollarPartition.pairedOptimalCoefficient_bddAbove k
      · exact ((PhysicalCollarPartition.pairedOptimalCoefficient_pos 0).trans_le
          (le_ciSup PhysicalCollarPartition.pairedOptimalCoefficient_bddAbove 0)).le
  · apply ciSup_le
    intro k
    have h := pairedOptimalCoefficient_le_productCoupled
      (n := k * (k + 4) + 2) (k := k) (by nlinarith)
    exact h.trans (le_ciSup productCoupledCollarCoefficient_bddAbove _)

theorem pairedOptimalCoefficient_le_limit (n : ℕ) :
    PhysicalCollarPartition.pairedOptimalCoefficient n ≤ limitingProductCoupledCoefficient := by
  rw [limitingProductCoupledCoefficient_eq_iSup_paired]
  exact le_ciSup PhysicalCollarPartition.pairedOptimalCoefficient_bddAbove n

theorem limitingCollarCoefficient_le_limitingProductCoupled :
    limitingCollarCoefficient ≤ limitingProductCoupledCoefficient := by
  apply ciSup_le
  intro n
  rw [monotoneCollarCoefficient_eq_optimalCoefficient]
  exact (PhysicalCollarPartition.optimalCoefficient_le_pairedOptimalCoefficient n).trans
    (pairedOptimalCoefficient_le_limit n)

theorem pairedOptimalCoefficient_tendsto :
    Filter.Tendsto PhysicalCollarPartition.pairedOptimalCoefficient Filter.atTop
      (nhds limitingProductCoupledCoefficient) := by
  rw [limitingProductCoupledCoefficient_eq_iSup_paired]
  exact tendsto_atTop_ciSup PhysicalCollarPartition.pairedOptimalCoefficient_monotone
    PhysicalCollarPartition.pairedOptimalCoefficient_bddAbove

theorem limitingProductCoupledCoefficient_sub_paired_bounds (n : ℕ) :
    0 ≤ limitingProductCoupledCoefficient - PhysicalCollarPartition.pairedOptimalCoefficient n ∧
      limitingProductCoupledCoefficient - PhysicalCollarPartition.pairedOptimalCoefficient n ≤
        collarCutoffTailMass n := by
  have hl := pairedOptimalCoefficient_le_limit n
  have hu : limitingProductCoupledCoefficient ≤
      PhysicalCollarPartition.pairedOptimalCoefficient n + collarCutoffTailMass n := by
    rw [limitingProductCoupledCoefficient_eq_iSup_paired]
    apply ciSup_le
    intro m
    rcases le_total n m with hnm | hmn
    · have h := PhysicalCollarPartition.pairedOptimalCoefficient_sub_le_tail hnm
      linarith
    · exact (PhysicalCollarPartition.pairedOptimalCoefficient_monotone hmn).trans
        (le_add_of_nonneg_right (collarCutoffTailMass_nonneg n))
  constructor <;> linarith

theorem pairedOptimalCoefficient_quantitative_saturation (n : ℕ) :
    0 ≤ limitingProductCoupledCoefficient - PhysicalCollarPartition.pairedOptimalCoefficient n ∧
      limitingProductCoupledCoefficient - PhysicalCollarPartition.pairedOptimalCoefficient n ≤
        4 * Real.exp (logarithmicCollarRadius / 2) /
          (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2))) :=
  ⟨(limitingProductCoupledCoefficient_sub_paired_bounds n).1,
    (limitingProductCoupledCoefficient_sub_paired_bounds n).2.trans (collarCutoffTailMass_le_inverse_sqrt n)⟩

/-- Every product-admitted frame gives an explicit error bound for the full hierarchy. -/
theorem productCoupled_error_of_admitted {n k : ℕ} (hcut : (k + 2) ^ 2 ≤ n + 2) :
    0 ≤ limitingProductCoupledCoefficient - productCoupledCollarCoefficient n ∧
      limitingProductCoupledCoefficient - productCoupledCollarCoefficient n ≤
        4 * Real.exp (logarithmicCollarRadius / 2) /
          (Real.sqrt ((k + 2 : ℕ) : ℝ) * (1 - 2 / (((k + 2 : ℕ) : ℝ) ^ 2))) := by
  have hlo : productCoupledCollarCoefficient n ≤ limitingProductCoupledCoefficient :=
    le_ciSup productCoupledCollarCoefficient_bddAbove n
  have hframe := pairedOptimalCoefficient_le_productCoupled hcut
  have htail := pairedOptimalCoefficient_quantitative_saturation k
  constructor <;> linarith

/-- Largest collar-grid index whose products fit the source cutoff. -/
def productAdmittedCutoff (n : ℕ) : ℕ := Nat.sqrt (n + 2) - 2

theorem productAdmittedCutoff_add_two {n : ℕ} (hn : 2 ≤ n) :
    productAdmittedCutoff n + 2 = Nat.sqrt (n + 2) := by
  have h : 2 ≤ Nat.sqrt (n + 2) := Nat.le_sqrt'.2 (by omega)
  exact Nat.sub_add_cancel h

theorem productAdmittedCutoff_admitted {n : ℕ} (hn : 2 ≤ n) :
    (productAdmittedCutoff n + 2) ^ 2 ≤ n + 2 := by
  rw [productAdmittedCutoff_add_two hn]
  exact Nat.sqrt_le' _

/-- Monotonicity of the paired optimum removes the finite search over smaller frames. -/
theorem productCoupledCollarCoefficient_eq_max {n : ℕ} (hn : 2 ≤ n) :
    productCoupledCollarCoefficient n =
      max (PhysicalCollarPartition.optimalCoefficient n)
        (PhysicalCollarPartition.pairedOptimalCoefficient (productAdmittedCutoff n)) := by
  apply le_antisymm
  · apply max_le (le_max_left _ _)
    apply Finset.sup'_le
    intro k _
    unfold productAdmittedCoefficient
    split_ifs with hcut
    · have hks := Nat.le_sqrt'.2 hcut
      have hk : k ≤ productAdmittedCutoff n := by unfold productAdmittedCutoff; omega
      exact (PhysicalCollarPartition.pairedOptimalCoefficient_monotone hk).trans (le_max_right _ _)
    · exact (PhysicalCollarPartition.optimalCoefficient_pos n).le.trans (le_max_left _ _)
  · exact max_le (optimalCoefficient_le_productCoupled n)
      (pairedOptimalCoefficient_le_productCoupled (productAdmittedCutoff_admitted hn))

/-- Exact floor-square-root version of the coupled cutoff error. -/
theorem productCoupled_quantitative_saturation_floor {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ limitingProductCoupledCoefficient - productCoupledCollarCoefficient n ∧
      limitingProductCoupledCoefficient - productCoupledCollarCoefficient n ≤
        4 * Real.exp (logarithmicCollarRadius / 2) /
          (Real.sqrt (Nat.sqrt (n + 2) : ℝ) * (1 - 2 / ((Nat.sqrt (n + 2) : ℝ) ^ 2))) := by
  have h := productCoupled_error_of_admitted (productAdmittedCutoff_admitted hn)
  simpa only [productAdmittedCutoff_add_two hn] using h

/-- A uniform fourth-root error bound in the actual source-grid cutoff. -/
theorem productCoupled_quantitative_saturation {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ limitingProductCoupledCoefficient - productCoupledCollarCoefficient n ∧
      limitingProductCoupledCoefficient - productCoupledCollarCoefficient n ≤
        16 * Real.exp (logarithmicCollarRadius / 2) /
          Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) := by
  let s : ℝ := (Nat.sqrt (n + 2) : ℝ)
  let X : ℝ := ((n + 2 : ℕ) : ℝ)
  let S := Real.sqrt s
  let T := Real.sqrt (Real.sqrt X)
  let d := Real.exp (logarithmicCollarRadius / 2)
  have hsNat : 2 ≤ Nat.sqrt (n + 2) := Nat.le_sqrt'.2 (by omega)
  have hs : 2 ≤ s := by
    dsimp [s]
    exact_mod_cast hsNat
  have hsp : 0 < s := by linarith
  have hS : 0 < S := Real.sqrt_pos.2 hsp
  have hT : 0 < T := by dsimp [T, X]; positivity
  have hd : 0 < d := Real.exp_pos _
  have hden : (1 / 2 : ℝ) ≤ 1 - 2 / s ^ 2 := by
    have hf : 2 / s ^ 2 ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ (sq_pos_of_pos hsp)).2 (by nlinarith)
    linarith
  have hdenp : 0 < 1 - 2 / s ^ 2 := by linarith
  have hX : X < (s + 1) ^ 2 := by
    dsimp [X, s]
    exact_mod_cast Nat.lt_succ_sqrt' (n + 2)
  have hroot : Real.sqrt X ≤ 2 * s := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by linarith, by nlinarith [sq_nonneg (s - 1)]⟩
  have hSsq : S ^ 2 = s := Real.sq_sqrt hsp.le
  have hTS : T ≤ 2 * S := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith⟩
  have hfirst : 4 * d / (S * (1 - 2 / s ^ 2)) ≤ 8 * d / S := by
    apply (div_le_div_iff₀ (mul_pos hS hdenp) hS).2
    have hm := mul_le_mul_of_nonneg_left hden (show 0 ≤ 8 * d * S by positivity)
    nlinarith
  have hsecond : 8 * d / S ≤ 16 * d / T := by
    apply (div_le_div_iff₀ hS hT).2
    nlinarith [mul_le_mul_of_nonneg_left hTS (show 0 ≤ 8 * d by positivity)]
  have h := productCoupled_quantitative_saturation_floor hn
  refine ⟨h.1, h.2.trans ?_⟩
  change 4 * d / (S * (1 - 2 / s ^ 2)) ≤ 16 * d / T
  exact hfirst.trans hsecond

/-- The limiting coupled constant gives a quantitative lower bound for actual source energy. -/
theorem productCoupled_limit_sub_error_le_normalized_energy {n : ℕ} (hn : 2 ≤ n)
    (f : SmoothLogarithmicGridSource n) :
    limitingProductCoupledCoefficient -
      16 * Real.exp (logarithmicCollarRadius / 2) / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) ≤
        biScaleLevyEnergy f.1.1 / RHTower.ArchimedeanAnomaly.autocorr f.1.1 0 := by
  have htail := productCoupled_quantitative_saturation hn
  have hsource := productCoupledCollarCoefficient_le_normalized_energy n f
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty
