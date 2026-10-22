import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixIntegralColumnLaw
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Complete integral Abel reader and retained physical first variation

The actual complete Gamma-six integral operator belongs to the reciprocal
principal class with a summable correction. Along admitted positive Abel
parameters its normalized Gibbs reader converges to the retained Xi
coefficient. Every fixed ordinary dilation has a vanishing limiting
compression defect, while the first parameter variation retains that
coefficient times log(n)/n.

The full source agrees to first order with the existing physical BV
boundary on this critical path. At multiplicity-top sources the retained
slope is nonzero. The regulator is independent of the spectral parameter;
this does not identify the reader at a divisor's original horizontal
position and is not an RH proof.
-/

open Complex Real Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

/-- The actual open Gibbs reader along the critical Abel path. Only positive
parameters are used as physical reader values; no endpoint series is assigned. -/
def deningerOrdinaryIntegerAbelReader (ε : ℝ) (T : DeningerOrdinaryIntegerEnd) : ℂ :=
  (deningerOrdinaryIntegerGibbsPartition ((1 + ε) / 2) : ℂ)⁻¹ *
    ∑' k : PNat, deningerOrdinaryIntegerGibbsDiagonal ((1 + ε) / 2) k T

theorem deningerOrdinaryIntegerAbelReader_eq_gibbs
    {ε : ℝ} (hε : 0 < ε) (T : deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2)) :
    deningerOrdinaryIntegerAbelReader ε T.val =
      deningerOrdinaryIntegerGibbsReader ((1 + ε) / 2) (by linarith) T := rfl

theorem deningerOrdinaryIntegerGibbsPartition_abel_eq {ε : ℝ} (hε : 0 < ε) :
    deningerOrdinaryIntegerGibbsPartition ((1 + ε) / 2) =
      ∑' k : ℕ, 1 / (k : ℝ) ^ (1 + ε) := by
  unfold deningerOrdinaryIntegerGibbsPartition deningerOrdinaryIntegerGibbsMass
  simp only [show 2 * ((1 + ε) / 2) = 1 + ε by ring, Real.rpow_neg (Nat.cast_nonneg _), one_div]
  apply tsum_pnat_eq_tsum_of_eq_zero (f := fun k : ℕ => ((k : ℝ) ^ (1 + ε))⁻¹)
  simp only [Nat.cast_zero, Real.zero_rpow (by linarith : 1 + ε ≠ 0), inv_zero]

theorem tendsto_deningerOrdinaryIntegerGibbsPartition_abel_residue :
    Tendsto (fun ε : ℝ => ε * deningerOrdinaryIntegerGibbsPartition ((1 + ε) / 2))
      (𝓝[>] 0) (𝓝 1) := by
  have hpath : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝[>] 1) := by
    have hc : ContinuousWithinAt (fun ε : ℝ => 1 + ε) (Set.Ioi 0) 0 := by fun_prop
    simpa only [add_zero] using hc.tendsto_nhdsWithin (t := Set.Ioi 1)
      (fun ε hε => by simpa only [Set.mem_Ioi, lt_add_iff_pos_right] using hε)
  apply (tendsto_sub_mul_tsum_nat_rpow.comp hpath).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  simp only [Function.comp_apply, add_sub_cancel_left,
    deningerOrdinaryIntegerGibbsPartition_abel_eq hε]

theorem tendsto_deningerOrdinaryIntegerGibbsPartition_abel_inv :
    Tendsto (fun ε : ℝ => (deningerOrdinaryIntegerGibbsPartition ((1 + ε) / 2))⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := hid.div tendsto_deningerOrdinaryIntegerGibbsPartition_abel_residue
    (by norm_num : (1 : ℝ) ≠ 0)
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  have hZ := (deningerOrdinaryIntegerGibbsPartition_pos (by linarith : 1 / 2 < (1 + ε) / 2)).ne'
  change ε / (ε * deningerOrdinaryIntegerGibbsPartition ((1 + ε) / 2)) = _
  field_simp [hε.ne']

theorem norm_deningerOrdinaryIntegerGibbsDiagonal_le
    {sigma : ℝ} (h : 1 / 2 ≤ sigma) (T : DeningerOrdinaryIntegerEnd) (k : PNat) :
    ‖deningerOrdinaryIntegerGibbsDiagonal sigma k T‖ ≤
      ‖deningerOrdinaryIntegerDiagonalCoefficient k T‖ := by
  change ‖((deningerOrdinaryIntegerGibbsMass sigma k : ℂ) * ((k : ℕ) : ℂ)) *
    deningerOrdinaryIntegerDiagonalCoefficient k T‖ ≤ _
  rw [norm_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (deningerOrdinaryIntegerGibbsMass_pos sigma k)
      (by exact_mod_cast k.pos))]
  exact mul_le_of_le_one_left (norm_nonneg _) (deningerOrdinaryIntegerGibbsWeight_le_one h k)

theorem deningerOrdinaryIntegerSummableDiagonal_mem_gibbsDomain
    {sigma : ℝ} (h : 1 / 2 ≤ sigma) (T : DeningerOrdinaryIntegerEnd)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k T)) :
    T ∈ deningerOrdinaryIntegerGibbsDomain sigma :=
  Summable.of_norm_bounded hs.norm (norm_deningerOrdinaryIntegerGibbsDiagonal_le h T)

theorem norm_deningerOrdinaryIntegerAbelReader_le
    {ε : ℝ} (hε : 0 < ε) (T : DeningerOrdinaryIntegerEnd)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k T)) :
    ‖deningerOrdinaryIntegerAbelReader ε T‖ ≤
      (deningerOrdinaryIntegerGibbsPartition ((1 + ε) / 2))⁻¹ *
        ∑' k : PNat, ‖deningerOrdinaryIntegerDiagonalCoefficient k T‖ := by
  have hσ : 1 / 2 < (1 + ε) / 2 := by linarith
  have hZ := deningerOrdinaryIntegerGibbsPartition_pos hσ
  have hw : Summable (fun k : PNat => ‖deningerOrdinaryIntegerGibbsDiagonal ((1 + ε) / 2) k T‖) :=
    hs.norm.of_nonneg_of_le (fun k => norm_nonneg _)
      (norm_deningerOrdinaryIntegerGibbsDiagonal_le hσ.le T)
  rw [deningerOrdinaryIntegerAbelReader, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hZ]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hZ.le)
  exact (norm_tsum_le_tsum_norm hw).trans
    (hw.tsum_le_tsum (norm_deningerOrdinaryIntegerGibbsDiagonal_le hσ.le T) hs.norm)

theorem tendsto_deningerOrdinaryIntegerAbelReader_summable
    (T : DeningerOrdinaryIntegerEnd)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k T)) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelReader ε T) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' _ (by
    simpa only [zero_mul] using tendsto_deningerOrdinaryIntegerGibbsPartition_abel_inv.mul_const
      (∑' k : PNat, ‖deningerOrdinaryIntegerDiagonalCoefficient k T‖))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_deningerOrdinaryIntegerAbelReader_le hε T hs

theorem deningerOrdinaryIntegerAbelReader_smul
    (ε : ℝ) (c : ℂ) (T : DeningerOrdinaryIntegerEnd) :
    deningerOrdinaryIntegerAbelReader ε (c • T) = c * deningerOrdinaryIntegerAbelReader ε T := by
  simp only [deningerOrdinaryIntegerAbelReader, map_smul, smul_eq_mul, tsum_mul_left]
  ring

theorem deningerOrdinaryIntegerAbelReader_sub
    {ε : ℝ} (T U : deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2)) :
    deningerOrdinaryIntegerAbelReader ε (T.val - U.val) =
      deningerOrdinaryIntegerAbelReader ε T.val - deningerOrdinaryIntegerAbelReader ε U.val := by
  simp only [deningerOrdinaryIntegerAbelReader, map_sub,
    Summable.tsum_sub T.property U.property, mul_sub]

theorem deningerOrdinaryIntegerAbelReader_green {ε : ℝ} (hε : 0 < ε) :
    deningerOrdinaryIntegerAbelReader ε deningerOrdinaryIntegerReciprocalGreen = 1 := by
  exact deningerOrdinaryIntegerGibbsReader_reciprocalGreen (by linarith)

theorem deningerOrdinaryIntegerPrincipalClass_mem_gibbsDomain
    {sigma : ℝ} (h : 1 / 2 < sigma) (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) :
    T ∈ deningerOrdinaryIntegerGibbsDomain sigma := by
  have hR := deningerOrdinaryIntegerSummableDiagonal_mem_gibbsDomain h.le _ hs
  have hQ := (deningerOrdinaryIntegerGibbsDomain sigma).smul_mem c
    ((deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff sigma).2 h)
  simpa only [sub_add_cancel] using (deningerOrdinaryIntegerGibbsDomain sigma).add_mem hR hQ

theorem deningerOrdinaryIntegerAbelReader_principal_decomposition
    {ε : ℝ} (hε : 0 < ε) (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) :
    deningerOrdinaryIntegerAbelReader ε T = c + deningerOrdinaryIntegerAbelReader ε
      (T - c • deningerOrdinaryIntegerReciprocalGreen) := by
  have hσ : 1 / 2 < (1 + ε) / 2 := by linarith
  have hT := deningerOrdinaryIntegerPrincipalClass_mem_gibbsDomain hσ T c hs
  have hQ := (deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2)).smul_mem c
    ((deningerOrdinaryIntegerReciprocalGreen_mem_gibbsDomain_iff _).2 hσ)
  have hx := deningerOrdinaryIntegerAbelReader_sub (⟨T, hT⟩) (⟨_, hQ⟩)
  dsimp only at hx
  rw [deningerOrdinaryIntegerAbelReader_smul, deningerOrdinaryIntegerAbelReader_green hε, mul_one] at hx
  linear_combination -hx

/-- The full summable correction disappears in the normalized critical limit,
while the actual reciprocal coefficient survives. -/
theorem tendsto_deningerOrdinaryIntegerAbelReader_principal
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelReader ε T) (𝓝[>] 0) (𝓝 c) := by
  have ht := (tendsto_deningerOrdinaryIntegerAbelReader_summable _ hs).const_add c
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (deningerOrdinaryIntegerAbelReader_principal_decomposition hε T c hs).symm

theorem deningerOrdinaryIntegerPrincipalClass_compression
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) (n : PNat) :
    Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      ((deningerOrdinaryIntegerWoldBackward n * (T * deningerOrdinaryIntegerWoldShift n)) -
        (c / ((n : ℕ) : ℂ)) • deningerOrdinaryIntegerReciprocalGreen)) := by
  have hx := hs.comp_injective (i := fun k : PNat => n * k)
    (fun a b h => mul_left_cancel h)
  apply hx.congr
  intro k
  simp only [Function.comp_apply, map_sub, map_smul, smul_eq_mul,
    deningerOrdinaryIntegerDiagonalCoefficient_compression,
    deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen,
    PNat.mul_coe, Nat.cast_mul, mul_inv_rev, div_eq_mul_inv]
  ring

theorem tendsto_deningerOrdinaryIntegerAbelReader_compression
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) (n : PNat) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelReader ε
      (deningerOrdinaryIntegerWoldBackward n * (T * deningerOrdinaryIntegerWoldShift n)))
      (𝓝[>] 0) (𝓝 (c / ((n : ℕ) : ℂ))) :=
  tendsto_deningerOrdinaryIntegerAbelReader_principal _ _
    (deningerOrdinaryIntegerPrincipalClass_compression T c hs n)

theorem deningerOrdinaryIntegerGibbsWeight_abel (ε : ℝ) (n : PNat) :
    deningerOrdinaryIntegerGibbsMass ((1 + ε) / 2) n * ((n : ℕ) : ℝ) =
      ((n : ℕ) : ℝ) ^ (-ε) := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  unfold deningerOrdinaryIntegerGibbsMass
  conv_lhs => rhs; rw [← Real.rpow_one (((n : ℕ) : ℝ))]
  rw [← Real.rpow_add hn]
  congr 1
  ring

theorem deningerOrdinaryIntegerAbelReader_compression_exchange
    {ε : ℝ} (T : deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2)) (n : PNat) :
    deningerOrdinaryIntegerAbelReader ε
      (deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n)) =
      ((((n : ℕ) : ℝ) ^ ε : ℝ) : ℂ) *
        deningerOrdinaryIntegerAbelReader ε (T.val * deningerOrdinaryIntegerDivisibilityProjection n) := by
  have hx := deningerOrdinaryIntegerGibbsTrace_compression T n
  change (∑' k, deningerOrdinaryIntegerGibbsDiagonal ((1 + ε) / 2) k
    (deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n))) =
      _ * (∑' k, deningerOrdinaryIntegerGibbsDiagonal ((1 + ε) / 2) k
        (T.val * deningerOrdinaryIntegerDivisibilityProjection n)) at hx
  have hw : (deningerOrdinaryIntegerGibbsMass ((1 + ε) / 2) n : ℂ) * ((n : ℕ) : ℂ) =
      ((((n : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) := by
    exact_mod_cast deningerOrdinaryIntegerGibbsWeight_abel ε n
  rw [hw, ← Complex.ofReal_inv, Real.rpow_neg (by positivity), inv_inv] at hx
  simp only [deningerOrdinaryIntegerAbelReader, hx]
  ring

theorem deningerOrdinaryIntegerAbelReader_projection_exchange
    {ε : ℝ} (T : deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2)) (n : PNat) :
    deningerOrdinaryIntegerAbelReader ε (T.val * deningerOrdinaryIntegerDivisibilityProjection n) =
      ((((n : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) *
        deningerOrdinaryIntegerAbelReader ε
          (deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n)) := by
  rw [deningerOrdinaryIntegerAbelReader_compression_exchange T n, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.rpow_add (by exact_mod_cast n.pos : (0 : ℝ) < ((n : ℕ) : ℝ))]
  simp

theorem tendsto_deningerOrdinaryIntegerAbelReader_projection
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) (n : PNat) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelReader ε
      (T * deningerOrdinaryIntegerDivisibilityProjection n))
      (𝓝[>] 0) (𝓝 (c / ((n : ℕ) : ℂ))) := by
  have hp : Tendsto (fun ε : ℝ => ((((n : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun ε : ℝ => ((((n : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ)) 0 := by
      fun_prop (disch := positivity)
    simpa only [neg_zero, Real.rpow_zero, Complex.ofReal_one] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht := hp.mul (tendsto_deningerOrdinaryIntegerAbelReader_compression T c hs n)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hT := deningerOrdinaryIntegerPrincipalClass_mem_gibbsDomain
    (by change 0 < ε at hε; linarith : 1 / 2 < (1 + ε) / 2) T c hs
  exact (deningerOrdinaryIntegerAbelReader_projection_exchange ⟨T, hT⟩ n).symm

/-- The literal compression-minus-projection response, before taking any limit. -/
def deningerOrdinaryIntegerAbelDefect (ε : ℝ) (n : PNat) (T : DeningerOrdinaryIntegerEnd) : ℂ :=
  deningerOrdinaryIntegerAbelReader ε
    (deningerOrdinaryIntegerWoldBackward n * (T * deningerOrdinaryIntegerWoldShift n)) -
  deningerOrdinaryIntegerAbelReader ε (T * deningerOrdinaryIntegerDivisibilityProjection n)

theorem deningerOrdinaryIntegerAbelDefect_eq
    {ε : ℝ} (T : deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2)) (n : PNat) :
    deningerOrdinaryIntegerAbelDefect ε n T.val =
      (((((n : ℕ) : ℝ) ^ ε - 1 : ℝ) : ℂ)) *
        deningerOrdinaryIntegerAbelReader ε (T.val * deningerOrdinaryIntegerDivisibilityProjection n) := by
  rw [deningerOrdinaryIntegerAbelDefect, deningerOrdinaryIntegerAbelReader_compression_exchange T n]
  push_cast
  ring

theorem tendsto_deningerOrdinaryIntegerAbelDefect_zero
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) (n : PNat) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelDefect ε n T) (𝓝[>] 0) (𝓝 0) := by
  simpa only [deningerOrdinaryIntegerAbelDefect, sub_self] using
    (tendsto_deningerOrdinaryIntegerAbelReader_compression T c hs n).sub
      (tendsto_deningerOrdinaryIntegerAbelReader_projection T c hs n)

theorem tendsto_deningerOrdinaryIntegerAbelGain_slope (n : PNat) :
    Tendsto (fun ε : ℝ => (((n : ℕ) : ℝ) ^ ε - 1) / ε) (𝓝[>] 0)
      (𝓝 (Real.log ((n : ℕ) : ℝ))) := by
  have hd : HasDerivAt (fun ε : ℝ => ((n : ℕ) : ℝ) ^ ε)
      (Real.log ((n : ℕ) : ℝ)) 0 := by
    simpa only [id_eq, Real.rpow_zero, mul_one] using
      (hasDerivAt_id (0 : ℝ)).const_rpow (by exact_mod_cast n.pos : (0 : ℝ) < ((n : ℕ) : ℝ))
  simpa only [zero_add, Real.rpow_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hd.tendsto_slope_zero_right

/-- The critical cyclic limit retains a nontrivial first horizontal variation. -/
theorem tendsto_deningerOrdinaryIntegerAbelDefect_slope
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) (n : PNat) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelDefect ε n T / (ε : ℂ))
      (𝓝[>] 0) (𝓝 ((Real.log ((n : ℕ) : ℝ) : ℂ) * (c / ((n : ℕ) : ℂ)))) := by
  have hp := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_deningerOrdinaryIntegerAbelGain_slope n)
  have ht := hp.mul (tendsto_deningerOrdinaryIntegerAbelReader_projection T c hs n)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hT := deningerOrdinaryIntegerPrincipalClass_mem_gibbsDomain
    (by change 0 < ε at hε; linarith : 1 / 2 < (1 + ε) / 2) T c hs
  rw [deningerOrdinaryIntegerAbelDefect_eq ⟨T, hT⟩ n]
  simp only [Function.comp_apply]
  push_cast
  ring

/-- The principal-class premise is discharged by the literal complete integral source. -/
theorem deningerGammaSixIntegralOperator_principal_class
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) :
    Summable (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a
      (deningerGammaSixIntegralOperator k l w z -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC z) • deningerOrdinaryIntegerReciprocalGreen)) := by
  simpa only [map_sub, map_smul, smul_eq_mul,
    deningerOrdinaryIntegerDiagonalCoefficient_integralOperator,
    deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen] using
    summable_deningerGammaSixIntegralDiagonal_sub_principal k l hw hz hrw hrz

theorem tendsto_deningerGammaSixIntegral_abel_reader
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelReader ε
      (deningerGammaSixIntegralOperator k l w z)) (𝓝[>] 0)
      (𝓝 (iteratedDeriv k XiC w * iteratedDeriv l XiC z)) :=
  tendsto_deningerOrdinaryIntegerAbelReader_principal _ _
    (deningerGammaSixIntegralOperator_principal_class k l hw hz hrw hrz)

theorem tendsto_deningerGammaSixIntegral_abel_projection
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) (n : PNat) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelReader ε
      (deningerGammaSixIntegralOperator k l w z * deningerOrdinaryIntegerDivisibilityProjection n))
      (𝓝[>] 0) (𝓝 ((iteratedDeriv k XiC w * iteratedDeriv l XiC z) / ((n : ℕ) : ℂ))) :=
  tendsto_deningerOrdinaryIntegerAbelReader_projection _ _
    (deningerGammaSixIntegralOperator_principal_class k l hw hz hrw hrz) n

theorem tendsto_deningerGammaSixIntegral_abel_defect_zero
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) (n : PNat) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelDefect ε n
      (deningerGammaSixIntegralOperator k l w z)) (𝓝[>] 0) (𝓝 0) :=
  tendsto_deningerOrdinaryIntegerAbelDefect_zero _ _
    (deningerGammaSixIntegralOperator_principal_class k l hw hz hrw hrz) n

theorem tendsto_deningerGammaSixIntegral_abel_defect_slope
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) (n : PNat) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelDefect ε n
      (deningerGammaSixIntegralOperator k l w z) / (ε : ℂ)) (𝓝[>] 0)
      (𝓝 ((Real.log ((n : ℕ) : ℝ) : ℂ) *
        ((iteratedDeriv k XiC w * iteratedDeriv l XiC z) / ((n : ℕ) : ℂ)))) :=
  tendsto_deningerOrdinaryIntegerAbelDefect_slope _ _
    (deningerGammaSixIntegralOperator_principal_class k l hw hz hrw hrz) n

/-- The retained coefficient in the first horizontal variation at each top-jet source. -/
def deningerGammaSixIntegralAbelTopSlope (rho : XiDivisorSupport) (n : PNat) : ℂ :=
  (Real.log ((n : ℕ) : ℝ) : ℂ) *
    ((iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho) *
      iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho)) / ((n : ℕ) : ℂ))

theorem deningerGammaSixIntegralAbelTopSlope_ne_zero
    (rho : XiDivisorSupport) (n : PNat) (hn : 1 < (n : ℕ)) :
    deningerGammaSixIntegralAbelTopSlope rho n ≠ 0 := by
  have hlog : Real.log ((n : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hlog)
    (div_ne_zero (mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)) (by exact_mod_cast n.ne_zero))

theorem tendsto_deningerGammaSixIntegral_abel_top_slope
    (rho : XiDivisorSupport) (hrho : (1 / 3 : ℝ) < (rho : ℂ).re) (n : PNat) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelDefect ε n
      (deningerGammaSixIntegralOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
        (xiSpectralPointSupport rho) (xiSpectralPointSupport rho)) / (ε : ℂ))
      (𝓝[>] 0) (𝓝 (deningerGammaSixIntegralAbelTopSlope rho n)) :=
  tendsto_deningerGammaSixIntegral_abel_defect_slope _ _
    (abs_im_xiSpectralPointSupport_lt_one rho) (abs_im_xiSpectralPointSupport_lt_one rho)
    (by simpa only [mobiusThetaCenteredParameter_xiSpectralPointSupport] using hrho)
    (by simpa only [mobiusThetaCenteredParameter_xiSpectralPointSupport] using hrho) n

/-- Although its critical value is zero, each top-jet boundary remains nonzero
throughout a sufficiently small positive Abel interval, for every fixed n>1. -/
theorem eventually_deningerGammaSixIntegral_abel_top_defect_ne_zero
    (rho : XiDivisorSupport) (hrho : (1 / 3 : ℝ) < (rho : ℂ).re)
    (n : PNat) (hn : 1 < (n : ℕ)) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, deningerOrdinaryIntegerAbelDefect ε n
      (deningerGammaSixIntegralOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
        (xiSpectralPointSupport rho) (xiSpectralPointSupport rho)) ≠ 0 := by
  have ht := (tendsto_deningerGammaSixIntegral_abel_top_slope rho hrho n).eventually_ne
    (deningerGammaSixIntegralAbelTopSlope_ne_zero rho n hn)
  filter_upwards [ht] with ε hε
  intro hz
  exact hε (by rw [hz, zero_div])

/-- The complete source's first variation cannot be replaced by a zero response. -/
theorem not_tendsto_deningerGammaSixIntegral_abel_top_slope_zero
    (rho : XiDivisorSupport) (hrho : (1 / 3 : ℝ) < (rho : ℂ).re)
    (n : PNat) (hn : 1 < (n : ℕ)) :
    ¬ Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelDefect ε n
      (deningerGammaSixIntegralOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
        (xiSpectralPointSupport rho) (xiSpectralPointSupport rho)) / (ε : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  intro hz
  exact deningerGammaSixIntegralAbelTopSlope_ne_zero rho n hn
    (tendsto_nhds_unique (tendsto_deningerGammaSixIntegral_abel_top_slope rho hrho n) hz)

theorem tendsto_deningerOrdinaryIntegerGibbsPartition_abel_atTop :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerGibbsPartition ((1 + ε) / 2))
      (𝓝[>] 0) atTop := by
  have ht := tendsto_deningerOrdinaryIntegerGibbsPartition_abel_residue.pos_mul_atTop
    (by norm_num : (0 : ℝ) < 1) tendsto_inv_nhdsGT_zero
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  field_simp [hε.ne']

theorem deningerHalfDensityMateGain_abel (ε : ℝ) (n : PNat) :
    deningerHalfDensityMateGain n (((1 + ε) / 2 : ℝ) : ℂ) = ((n : ℕ) : ℝ) ^ ε := by
  rw [deningerHalfDensityMateGain, Complex.ofReal_re,
    Real.rpow_def_of_pos (by exact_mod_cast n.pos : (0 : ℝ) < ((n : ℕ) : ℝ))]
  congr 1
  ring

theorem deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_abel
    (ε : ℝ) (n : PNat) :
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) =
      ((n : ℕ) : ℝ)⁻¹ * (1 - ((n : ℕ) : ℝ) ^ (-ε)) := by
  rw [deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation,
    deningerHalfDensityMateGain_abel, Real.rpow_neg (by positivity)]

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_abel_slope (n : PNat) :
    Tendsto (fun ε : ℝ =>
      (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) : ℂ) /
        (ε : ℂ)) (𝓝[>] 0) (𝓝 ((Real.log ((n : ℕ) : ℝ) : ℂ) / ((n : ℕ) : ℂ))) := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hneg : HasDerivAt (fun ε : ℝ => -ε) (-1) 0 := by
    simpa only [id_eq, Pi.neg_apply] using! (hasDerivAt_id (0 : ℝ)).neg
  have hd : HasDerivAt (fun ε : ℝ => ((n : ℕ) : ℝ)⁻¹ * (1 - ((n : ℕ) : ℝ) ^ (-ε)))
      (Real.log ((n : ℕ) : ℝ) / ((n : ℕ) : ℝ)) 0 := by
    simpa [Pi.sub_apply, div_eq_mul_inv, mul_comm] using!
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hneg.const_rpow hn)).const_mul (((n : ℕ) : ℝ)⁻¹)
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp hd.tendsto_slope_zero_right
  convert ht using 1
  · funext ε
    rw [deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_abel]
    simp only [Function.comp_apply, zero_add, neg_zero, Real.rpow_zero, sub_self,
      mul_zero, sub_zero, smul_eq_mul]
    push_cast
    ring
  · push_cast
    rfl

/-- First-order agreement with the existing physical BV reader is derived for
the full integral class. The unscaled, off-endpoint comparison is not asserted. -/
theorem tendsto_deningerOrdinaryIntegerAbelDefect_sub_physical_slope
    (T : DeningerOrdinaryIntegerEnd) (c : ℂ)
    (hs : Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (T - c • deningerOrdinaryIntegerReciprocalGreen))) (n : PNat) :
    Tendsto (fun ε : ℝ => (deningerOrdinaryIntegerAbelDefect ε n T -
      c * (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) : ℂ)) /
        (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_deningerOrdinaryIntegerAbelDefect_slope T c hs n).sub
    ((tendsto_deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_abel_slope n).const_mul c)
  convert ht using 1
  · funext ε
    ring
  · congr 1
    ring

theorem tendsto_deningerGammaSixIntegral_abel_physical_comparison
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) (n : PNat) :
    Tendsto (fun ε : ℝ => (deningerOrdinaryIntegerAbelDefect ε n
      (deningerGammaSixIntegralOperator k l w z) -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC z) *
        (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (((1 + ε) / 2 : ℝ) : ℂ) : ℂ)) /
          (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=
  tendsto_deningerOrdinaryIntegerAbelDefect_sub_physical_slope _ _
    (deningerGammaSixIntegralOperator_principal_class k l hw hz hrw hrz) n

end
end RHTower
