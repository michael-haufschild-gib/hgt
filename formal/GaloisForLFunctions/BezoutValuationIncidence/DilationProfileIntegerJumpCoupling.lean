import GaloisForLFunctions.BezoutValuationIncidence.ReciprocalJumpKernelAndDilationLagSectors
import GaloisForLFunctions.RHTower.PMRamanujanNearbyPrimeResonance
/-!
# Integer jump coupling for rational dilation profiles

The existing continuous Hilbert profile equals the reciprocal integer-cell
pairing for every pair of positive integer scales. Finite Diophantine lag
sectors approximate it with an explicit uniform tail bound. At quadratic
physical horizon Q², every scale pair bounded by Q has error at most B²/Q.
The successor sector retains its exact reciprocal successor kernel.
-/

open scoped BigOperators Topology
open MeasureTheory Set Filter RHTower Finset
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

private theorem dilated_step_source_ae {r p : ℕ} (hr : 1 < r) (hp : 0 < p) :
    (dilation (p : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hp))
      (pmRamanujanStepVector r hr) : ℝ → ℂ) =ᵐ[volume]
        fun x => (Real.sqrt (p : ℝ) : ℂ) *
          stepFun (fun N => (pmRamanujanPrimitive r (N / p)).re) x := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hcomp := (memLp_pmRamanujanStepSource hr).coeFn_toLp.comp_tendsto
    (realMul_quasiMeasurePreserving (p : ℝ)⁻¹ (inv_ne_zero hpR.ne')).tendsto_ae
  filter_upwards [dilation_ae (p : ℝ)⁻¹ (inv_pos.mpr hpR)
    (pmRamanujanStepVector r hr), hcomp] with x hd hc
  change (pmRamanujanStepVector r hr : ℝ → ℂ) ((p : ℝ)⁻¹ * x) =
    pmRamanujanStepSource r ((p : ℝ)⁻¹ * x) at hc
  rw [hd, hc, pmRamanujanStepSource, stepFun, stepFun]
  rw [show (p : ℝ)⁻¹ * x = x / p by ring, Nat.floor_div_natCast]
  have hs : ((Real.sqrt (p : ℝ))⁻¹ : ℂ) * (p : ℂ) =
      (Real.sqrt (p : ℝ) : ℂ) := by
    have hsR : (Real.sqrt (p : ℝ))⁻¹ * (p : ℝ) = Real.sqrt (p : ℝ) := by
      calc
        _ = (Real.sqrt (p : ℝ))⁻¹ * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) := by
          rw [← sq, Real.sq_sqrt hpR.le]
        _ = _ := inv_mul_cancel_left₀ (Real.sqrt_ne_zero'.mpr hpR) _
    exact_mod_cast hsR
  push_cast
  rw [inv_div, Real.sqrt_inv]
  push_cast
  linear_combination (pmRamanujanPrimitive r (⌊x⌋₊ / p)).re * (x : ℂ)⁻¹ * hs

/-- Integer dilations of the actual Hilbert vector retain their literal floor sequences. -/
theorem pmRamanujanDilationProfile_eq_stepGram {r p q : ℕ}
    (hr : 1 < r) (hp : 0 < p) (hq : 0 < q) :
    pmRamanujanDilationProfile r hr ((p : ℝ) / q) =
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        stepGram (fun N => (pmRamanujanPrimitive r (N / p)).re)
          (fun N => (pmRamanujanPrimitive r (N / q)).re) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let f := pmRamanujanStepVector r hr
  let u := dilation (p : ℝ)⁻¹ (inv_pos.mpr hpR) f
  let v := dilation (q : ℝ)⁻¹ (inv_pos.mpr hqR) f
  have huv : (inner ℂ u v).re = pmRamanujanDilationProfile r hr ((p : ℝ) / q) := by
    have h := (dilation (p : ℝ) hpR).inner_map_map u v
    rw [dilation_dilation_inv, dilation_dilation] at h
    have hray : rayDilate ((p : ℝ) / q) f =
        dilation ((p : ℝ) * (q : ℝ)⁻¹) (mul_pos hpR (inv_pos.mpr hqR)) f := by
      simpa only [div_eq_mul_inv] using rayDilate_of_pos (div_pos hpR hqR) f
    rw [pmRamanujanDilationProfile, hray, ← h]
  rw [← huv, MeasureTheory.L2.inner_def]
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    rw [Filter.eventually_iff, mem_ae_iff]
    simp
  have hi : (fun x => inner ℂ (u x) (v x)) =ᵐ[volume]
      (Ioi (1 : ℝ)).indicator (fun x =>
        ((Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          ((pmRamanujanPrimitive r (⌊x⌋₊ / p)).re *
            (pmRamanujanPrimitive r (⌊x⌋₊ / q)).re * (x⁻¹)^2) : ℝ) : ℂ)) := by
    filter_upwards [dilated_step_source_ae hr hp, dilated_step_source_ae hr hq, hne]
      with x hpx hqx hx
    change u x = _ at hpx
    change v x = _ at hqx
    rw [hpx, hqx]
    by_cases h1 : 1 < x
    · rw [indicator_of_mem (show x ∈ Ioi (1 : ℝ) from h1)]
      simp only [stepFun, RCLike.inner_apply, map_mul, map_inv₀, Complex.conj_ofReal]
      push_cast
      ring
    · have hx1 : x < 1 := lt_of_le_of_ne (le_of_not_gt h1) hx
      simp [stepFun, Nat.floor_eq_zero.mpr hx1, pmRamanujanPrimitive, h1]
  rw [integral_congr_ae hi, integral_indicator measurableSet_Ioi,
    integral_complex_ofReal, Complex.ofReal_re, integral_const_mul]
  rfl

/-- The absolutely convergent integer-cell realization of a rational dilation profile. -/
def ramanujanIntegerDilationGram (r p q : ℕ) : ℝ :=
  ∑' n : ℕ, ((pmRamanujanPrimitive r (n / p)).re *
    (pmRamanujanPrimitive r (n / q)).re) / (pronicSeq n : ℝ)

private theorem dilation_product_bound {r : ℕ} (hr : 1 < r) (p q n : ℕ) :
    |(pmRamanujanPrimitive r (n / p)).re * (pmRamanujanPrimitive r (n / q)).re| ≤
      pmRamanujanPrimitiveBound r ^ 2 := by
  rw [abs_mul, sq]
  exact mul_le_mul
    ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _))
    ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _))
    (abs_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem ramanujanIntegerDilationGram_eq_stepGram {r : ℕ} (hr : 1 < r) (p q : ℕ) :
    ramanujanIntegerDilationGram r p q =
      stepGram (fun N => (pmRamanujanPrimitive r (N / p)).re)
        (fun N => (pmRamanujanPrimitive r (N / q)).re) := by
  have hb (d N : ℕ) : |(pmRamanujanPrimitive r (N / d)).re| ≤
      pmRamanujanPrimitiveBound r :=
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
  have ht := (hasSum_stepGram (hb p) (hb q)).tsum_eq
  have hs := (summable_div_pronicSeq_of_bounded (dilation_product_bound hr p q)).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, div_cast_pronicSeq_zero, zero_add] at hs
  rw [ramanujanIntegerDilationGram, ← hs, ← ht]
  apply tsum_congr
  intro n
  rw [cast_pronicSeq_eq]
  push_cast
  ring

/-- A rational profile is exactly its original integer-cell series at all positive scales. -/
theorem pmRamanujanDilationProfile_eq_integerDilationGram {r p q : ℕ}
    (hr : 1 < r) (hp : 0 < p) (hq : 0 < q) :
    pmRamanujanDilationProfile r hr ((p : ℝ) / q) =
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) * ramanujanIntegerDilationGram r p q := by
  rw [pmRamanujanDilationProfile_eq_stepGram hr hp hq,
    ramanujanIntegerDilationGram_eq_stepGram hr]


/-- A uniform cutoff error for the original profile, with every additive lag retained. -/
theorem abs_dilationProfile_sub_finite_lag_sectors_le {r p q : ℕ}
    (hr : 1 < r) (hp : 0 < p) (hq : 0 < q) (H : ℕ) :
    |pmRamanujanDilationProfile r hr ((p : ℝ) / q) -
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        (∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
          ramanujanDilationLagSector r p q H h)| ≤
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        (pmRamanujanPrimitiveBound r ^ 2 / ((H : ℝ) + 1)) := by
  have htail := abs_tsum_div_pronicSeq_sub_sum_Icc_le
    (dilation_product_bound hr p q) H
  simp only [cast_pronicSeq_eq] at htail
  have hseries : (∑' n : ℕ,
      (pmRamanujanPrimitive r (n / p)).re * (pmRamanujanPrimitive r (n / q)).re /
        ((n : ℝ) * ((n : ℝ) + 1))) = ramanujanIntegerDilationGram r p q := by
    simp only [ramanujanIntegerDilationGram, cast_pronicSeq_eq]
  rw [hseries, ramanujan_dilation_finite_lag_sectors hp hq] at htail
  rw [pmRamanujanDilationProfile_eq_integerDilationGram hr hp hq, ← mul_sub,
    abs_mul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_left htail
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Unconditional integer-jump coupling, with positive scales and nontrivial modulus by construction. -/
theorem dilationProfile_integer_jump_coupling (r p q H : ℕ) :
    |pmRamanujanDilationProfile (r + 2) (by omega)
        (((p + 1 : ℕ) : ℝ) / (q + 1 : ℕ)) -
      Real.sqrt (p + 1 : ℕ) * Real.sqrt (q + 1 : ℕ) *
        (∑ h ∈ (dilationJumpPairs H (p + 1) (q + 1)).image
          (dilationJumpGap (p + 1) (q + 1)),
          ramanujanDilationLagSector (r + 2) (p + 1) (q + 1) H h)| ≤
      Real.sqrt (p + 1 : ℕ) * Real.sqrt (q + 1 : ℕ) *
        (pmRamanujanPrimitiveBound (r + 2) ^ 2 / ((H : ℝ) + 1)) :=
  abs_dilationProfile_sub_finite_lag_sectors_le (by omega) (by omega) (by omega) H

/-- The pair kernel at a successor gap is the reciprocal successor weight. -/
theorem ramanujanJumpPairTerm_at_successor {r p q H : ℕ} {ab : ℕ × ℕ}
    (hp : 0 < p) (hq : 0 < q) (hab : ab ∈ dilationJumpPairs H p q)
    (hgap : dilationJumpGap p q ab = 1) :
    ramanujanJumpPairTerm r p q H ab =
      (d4BMRamanujanNaturalCoefficient ab.1 r).re *
        (d4BMRamanujanNaturalCoefficient ab.2 r).re *
          (1 / ((q * ab.2 + 1 : ℕ) : ℝ) - 1 / ((H : ℝ) + 1)) := by
  have hm := mem_product.mp hab
  have hi : p * ab.1 ∈ Finset.Icc 1 H := by
    apply Finset.mem_Icc.mpr
    constructor
    · have := (Finset.mem_Icc.mp hm.1).1
      exact Nat.mul_pos hp (by omega)
    · simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hp).mp (Finset.mem_Icc.mp hm.1).2
  have hj : q * ab.2 ∈ Finset.Icc 1 H := by
    apply Finset.mem_Icc.mpr
    constructor
    · have := (Finset.mem_Icc.mp hm.2).1
      exact Nat.mul_pos hq (by omega)
    · simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hq).mp (Finset.mem_Icc.mp hm.2).2
  have hcast : ((p * ab.1 : ℕ) : ℤ) - ((q * ab.2 : ℕ) : ℤ) = 1 := by
    simpa only [dilationJumpGap, Nat.cast_mul] using hgap
  have he : p * ab.1 = q * ab.2 + 1 := by omega
  unfold ramanujanJumpPairTerm
  rw [reciprocalJumpKernel_eq hi hj, max_eq_left (by omega), he]


/-- A quadratic physical horizon resolves every pair of scales up to Q with error at most B²/Q. -/
theorem dilationProfile_quadratic_horizon_coupling (r p q : ℕ) :
    let Q := max (p + 1) (q + 1)
    |pmRamanujanDilationProfile (r + 2) (by omega)
        (((p + 1 : ℕ) : ℝ) / (q + 1 : ℕ)) -
      Real.sqrt (p + 1 : ℕ) * Real.sqrt (q + 1 : ℕ) *
        (∑ h ∈ (dilationJumpPairs (Q * Q) (p + 1) (q + 1)).image
          (dilationJumpGap (p + 1) (q + 1)),
          ramanujanDilationLagSector (r + 2) (p + 1) (q + 1) (Q * Q) h)| ≤
      pmRamanujanPrimitiveBound (r + 2) ^ 2 / (Q : ℝ) := by
  dsimp only
  let Q := max (p + 1) (q + 1)
  have hQ : (0 : ℝ) < Q := by
    have : 0 < Q := by dsimp [Q]; omega
    exact_mod_cast this
  have hpQ : ((p + 1 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast le_max_left (p + 1) (q + 1)
  have hqQ : ((q + 1 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast le_max_right (p + 1) (q + 1)
  have hscale : Real.sqrt (p + 1 : ℕ) * Real.sqrt (q + 1 : ℕ) ≤ (Q : ℝ) := by
    calc
      _ ≤ Real.sqrt (Q : ℝ) * Real.sqrt (Q : ℝ) :=
        mul_le_mul (Real.sqrt_le_sqrt hpQ) (Real.sqrt_le_sqrt hqQ)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hQ.le
  have htail := dilationProfile_integer_jump_coupling r p q (Q * Q)
  apply htail.trans
  calc
    _ ≤ (Q : ℝ) * (pmRamanujanPrimitiveBound (r + 2) ^ 2 / ((Q : ℝ) ^ 2)) := by
      apply mul_le_mul hscale
      · apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hQ)
        push_cast
        nlinarith
      · positivity
      · exact hQ.le
    _ = pmRamanujanPrimitiveBound (r + 2) ^ 2 / (Q : ℝ) := by
      field_simp

end GaloisForLFunctions.BezoutValuationIncidence
