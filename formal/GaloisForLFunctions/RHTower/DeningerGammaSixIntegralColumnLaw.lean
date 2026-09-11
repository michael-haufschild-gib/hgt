import GaloisForLFunctions.RHTower.DeningerGammaSixTensorRemainderXiJets
import GaloisForLFunctions.RHTower.DeningerGammaSixBoundedSoninProbe

/-!
# Literal integral columns and exact prime-test classification

The complete internally promoted Gamma-six tensor is evaluated on its
proved every-depth complex domain. An exact source-coefficient estimate
makes its strict spectral tail geometrically summable in depth. Literal
shell multiplicity cancels the forced tensor half-density, yielding a
summable correction across every ordinary-integer source column.

The full diagonal is summable exactly when its retained Xi-derivative
product is zero. It is admitted by every open Gibbs domain and passes all
prime-pair cyclicity tests exactly in that same zero-coefficient case.
The multiplicity-top integral reader therefore fails these tests on its
actual domain, without any bounded Hilbert-reader assumption.

This is a source-domain classification, not a source-to-Burnol comparison
or an RH proof. The critical Gibbs endpoint is not included.
-/

open Complex Real MeasureTheory Filter Topology
open scoped BigOperators
namespace RHTower
set_option maxHeartbeats 800000
noncomputable section

/-- The complete source majorant, retaining all ordinary-integer labels. -/
def mobiusThetaSpectralTailConstant (p : ℕ) : ℝ :=
  ∑' j : ℕ, mobiusThetaPrimeNormalSpectralTailMajorant p j

def mobiusThetaSpectralTailDepthRate (p m : ℕ) (w : ℂ) : ℝ :=
  ((p : ℝ) / (p + 1 : ℕ)) ^
    ((m : ℝ) * (mobiusThetaCenteredParameter w).re - 3 / 2)

theorem norm_mobiusThetaPrimeNormalSpectralTailCoefficient_le_depthRate
    {p m : ℕ} (hp : 0 < p) {w : ℂ}
    (he : (3 / 2 : ℝ) ≤ (m : ℝ) * (mobiusThetaCenteredParameter w).re) (j : ℕ) :
    ‖mobiusThetaPrimeNormalSpectralTailCoefficient p m w j‖ ≤
      mobiusThetaSpectralTailDepthRate p m w * mobiusThetaPrimeNormalSpectralTailMajorant p j := by
  have hbase : (0 : ℝ) < (p : ℝ) / (p + j + 1 : ℕ) := by positivity
  have hle : (p : ℝ) / (p + j + 1 : ℕ) ≤ (p : ℝ) / (p + 1 : ℕ) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast (by omega : p + 1 ≤ p + j + 1)
  have hmu : |(ArithmeticFunction.moebius (p + j + 1) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p + j + 1)
  rw [norm_mobiusThetaPrimeNormalSpectralTailCoefficient hp]
  calc
    _ ≤ ((p : ℝ) / (p + j + 1 : ℕ)) ^
        ((m : ℝ) * (mobiusThetaCenteredParameter w).re) :=
      mul_le_of_le_one_left (by positivity) hmu
    _ = ((p : ℝ) / (p + j + 1 : ℕ)) ^
          ((m : ℝ) * (mobiusThetaCenteredParameter w).re - 3 / 2) *
        mobiusThetaPrimeNormalSpectralTailMajorant p j := by
      rw [mobiusThetaPrimeNormalSpectralTailMajorant, ← Real.rpow_add hbase]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hbase.le hle (sub_nonneg.mpr he)) (by
        unfold mobiusThetaPrimeNormalSpectralTailMajorant
        positivity)

theorem norm_mobiusThetaStrictTailMultiplier_le_depthRate
    {p m : ℕ} (hp : 0 < p) (hm : m ≠ 0) {w : ℂ}
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (he : (3 / 2 : ℝ) ≤ (m : ℝ) * (mobiusThetaCenteredParameter w).re) :
    ‖mobiusThetaStrictTailMultiplier p m w‖ ≤
      mobiusThetaSpectralTailConstant p * mobiusThetaSpectralTailDepthRate p m w := by
  have hmajor := (summable_mobiusThetaPrimeNormalSpectralTailMajorant p).mul_left
    (mobiusThetaSpectralTailDepthRate p m w)
  have hs : Summable (fun j : ℕ => ‖mobiusThetaPrimeNormalSpectralTailCoefficient p m w j‖) :=
    hmajor.of_nonneg_of_le (fun j => norm_nonneg _) (fun j =>
      norm_mobiusThetaPrimeNormalSpectralTailCoefficient_le_depthRate hp he j)
  rw [mobiusThetaStrictTailMultiplier,
    mobiusThetaPrimeNormalResidualMultiplier_eq_asymptoticMultiplier hp hm hms,
    mobiusThetaPrimeNormalAsymptoticMultiplier, add_sub_cancel_left]
  calc
    _ ≤ ∑' j : ℕ, ‖mobiusThetaPrimeNormalSpectralTailCoefficient p m w j‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, mobiusThetaSpectralTailDepthRate p m w *
        mobiusThetaPrimeNormalSpectralTailMajorant p j :=
      hs.tsum_le_tsum (fun j => norm_mobiusThetaPrimeNormalSpectralTailCoefficient_le_depthRate hp he j) hmajor
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

theorem summable_mobiusThetaSpectralTailDepthRate
    {p : ℕ} (hp : 0 < p) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Summable (fun m : ℕ => mobiusThetaSpectralTailDepthRate p m w) := by
  have hbase : (0 : ℝ) < (p : ℝ) / (p + 1 : ℕ) := by positivity
  have hlt : (p : ℝ) / (p + 1 : ℕ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast (by omega : p < p + 1)
  have hgeom := summable_geometric_of_lt_one
    (Real.rpow_nonneg hbase.le (mobiusThetaCenteredParameter w).re)
    (Real.rpow_lt_one hbase.le hlt hw)
  refine (hgeom.mul_right (((p : ℝ) / (p + 1 : ℕ)) ^ (-(3 / 2 : ℝ)))).congr (fun m => ?_)
  rw [mobiusThetaSpectralTailDepthRate, Real.rpow_sub hbase,
    mul_comm (m : ℝ), Real.rpow_mul hbase.le, Real.rpow_natCast, Real.rpow_neg hbase.le,
    div_eq_mul_inv]
  simp only [div_eq_mul_inv]

theorem summable_norm_mobiusThetaStrictTailMultiplier_depth
    {p : ℕ} (hp : 0 < p) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Summable (fun m : ℕ => ‖mobiusThetaStrictTailMultiplier p m w‖) := by
  have hs := (summable_mobiusThetaSpectralTailDepthRate hp hw).mul_left
    (mobiusThetaSpectralTailConstant p)
  apply hs.of_norm_bounded_eventually_nat
  have he := (tendsto_natCast_atTop_atTop.atTop_mul_const hw).eventually_ge_atTop (3 / 2 : ℝ)
  filter_upwards [eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hw, he] with m hm hlarge
  simpa only [norm_norm] using norm_mobiusThetaStrictTailMultiplier_le_depthRate hp hm.1 hm.2 hlarge

/-- Pointwise products preserve an absolutely summable correction to the unit sequence. -/
theorem summable_norm_mul_sub_one_of_summable_corrections
    (f g : ℕ → ℂ) (hf : Summable (fun m => ‖f m - 1‖))
    (hg : Summable (fun m => ‖g m - 1‖)) :
    Summable (fun m => ‖f m * g m - 1‖) := by
  have hdouble : Summable (fun a : ℕ × ℕ => ‖(f a.1 - 1) * (g a.2 - 1)‖) :=
    Summable.mul_norm (f := fun m : ℕ => f m - 1) (g := fun m : ℕ => g m - 1) hf hg
  have hprod : Summable (fun m : ℕ => ‖(f m - 1) * (g m - 1)‖) :=
    hdouble.comp_injective (i := fun m : ℕ => (m, m))
      (fun a b h => congrArg Prod.fst h)
  apply ((hf.add hg).add hprod).of_nonneg_of_le (fun m => norm_nonneg _)
  intro m
  have hid : f m * g m - 1 = (f m - 1) + (g m - 1) + (f m - 1) * (g m - 1) := by ring
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

/-- Absolute depth summability of the full two-variable tensor multiplier. -/
theorem summable_norm_deningerGammaSixTensorRemainderMultiplier_depth
    {w z : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re)
    (hz : 0 < (mobiusThetaCenteredParameter z).re) :
    Summable (fun m : ℕ => ‖deningerGammaSixTensorRemainderMultiplier m w z‖) := by
  have hW : Summable (fun m : ℕ => ‖mobiusThetaPrimeNormalResidualMultiplier 6 m w - 1‖) := by
    simpa only [mobiusThetaStrictTailMultiplier, moebius_six, Int.cast_one] using
      (summable_norm_mobiusThetaStrictTailMultiplier_depth (by omega : 0 < 6) hw)
  have hZ : Summable (fun m : ℕ => ‖mobiusThetaPrimeNormalResidualMultiplier 6 m z - 1‖) := by
    simpa only [mobiusThetaStrictTailMultiplier, moebius_six, Int.cast_one] using
      (summable_norm_mobiusThetaStrictTailMultiplier_depth (by omega : 0 < 6) hz)
  exact summable_norm_mul_sub_one_of_summable_corrections
    (fun m => mobiusThetaPrimeNormalResidualMultiplier 6 m w)
    (fun m => mobiusThetaPrimeNormalResidualMultiplier 6 m z) hW hZ

/-- Each full arithmetic depth fibre has its exact ordinary-integer multiplicity. -/
theorem deningerGammaSixDepthFiber_tsum_const {m : ℕ} (hm : 3 ≤ m) (c : ℝ) :
    (∑' _n : deningerGammaSixDepthFiber m, c) = 5 * (6 : ℝ) ^ m * c := by
  rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm, tsum_fintype,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : Fintype.card ((deningerGammaSixShellCoordinates m : Set ℕ)) =
      (deningerGammaSixShellCoordinates m).card := by
    calc
      Fintype.card ((deningerGammaSixShellCoordinates m : Set ℕ)) =
          Nat.card ((deningerGammaSixShellCoordinates m : Set ℕ)) := Nat.card_eq_fintype_card.symm
      _ = (deningerGammaSixShellCoordinates m : Set ℕ).ncard := Nat.card_coe_set_eq _
      _ = (deningerGammaSixShellCoordinates m).card := Set.ncard_coe_finset _
  rw [hcard, deningerGammaSixShellCoordinates_card hm]
  push_cast
  ring

/-- Shell multiplicity cancels the forced tensor half-density for every summable depth profile. -/
theorem summable_deningerGammaSixShellEigenvalue_profile
    (b : ℕ → ℝ) (hb : ∀ m, 0 ≤ b m) (hs : Summable b) :
    Summable (fun n : ℕ => deningerGammaSixShellEigenvalue n * b (deningerGammaSixShellDepth n)) := by
  rw [summable_partition (fun n => mul_nonneg (by
      unfold deningerGammaSixShellEigenvalue
      positivity) (hb _)) existsUnique_mem_deningerGammaSixDepthFiber]
  constructor
  · intro m
    by_cases hm : 3 ≤ m
    · rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
      exact (hasSum_fintype _).summable
    · rw [deningerGammaSixDepthFiber_eq_empty (by omega)]
      exact summable_empty
  · apply (summable_nat_add_iff 3).1
    refine ((summable_nat_add_iff 3).2 (hs.mul_left 5)).congr (fun j => ?_)
    have hconst : (fun n : deningerGammaSixDepthFiber (j + 3) =>
        deningerGammaSixShellEigenvalue n * b (deningerGammaSixShellDepth n)) =
        fun _ => (1 / 6 : ℝ) ^ (j + 3) * b (j + 3) := by
      funext n
      have hd : deningerGammaSixShellDepth n = j + 3 := n.property
      rw [deningerGammaSixShellEigenvalue, hd]
    rw [hconst, deningerGammaSixDepthFiber_tsum_const (by omega)]
    have hcancel : (6 : ℝ) ^ (j + 3) * (1 / 6 : ℝ) ^ (j + 3) = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      5 * b (j + 3) = 5 * ((6 : ℝ) ^ (j + 3) * (1 / 6 : ℝ) ^ (j + 3)) * b (j + 3) := by rw [hcancel, mul_one]
      _ = _ := by ring

/-- Every honest depth is admitted on this fixed, pre-divisor spectral region. -/
theorem deningerGammaSixIntegral_every_depth_admitted
    (m : MobiusHonestDepth) {w : ℂ}
    (hw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re) :
    1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re := by
  have hm : (3 : ℝ) ≤ m := by exact_mod_cast m.property
  exact (one_div_le_one_div_of_le (by norm_num) hm).trans_lt hw

/-- Literal full tensor source, evaluated on an independently specified spectral region. -/
theorem deningerGammaSixInternalJetTensor_full_fourierLaplace_data
    (k l : ℕ) (m : MobiusHonestDepth) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) :
    Integrable (deningerGammaSixTensorFourierLaplaceIntegrand
      (l2SeparatedProduct (deningerGammaSixInternalJetSource k m)
        (deningerGammaSixInternalJetSource l m)) w z) (volume.prod volume) ∧
    deningerGammaSixTensorFourierLaplace
      (l2SeparatedProduct (deningerGammaSixInternalJetSource k m)
        (deningerGammaSixInternalJetSource l m)) w z =
      (deningerGammaSixHalfWeight m : ℂ) ^ 2 *
        (mobiusThetaPrimeNormalResidualMultiplier 6 m w * mobiusThetaPrimeNormalResidualMultiplier 6 m z) *
        (iteratedDeriv k XiC w * iteratedDeriv l XiC z) := by
  have hW := deningerGammaSixInternalJetSource_fourierLaplace_data k m hw
    (deningerGammaSixIntegral_every_depth_admitted m hrw)
  have hZ := deningerGammaSixInternalJetSource_fourierLaplace_data l m hz
    (deningerGammaSixIntegral_every_depth_admitted m hrz)
  have hP := deningerGammaSixTensorFourierLaplace_product_data _ _ w z hW.1 hZ.1
  refine ⟨hP.1, ?_⟩
  rw [hP.2, hW.2, hZ.2]
  ring

def deningerGammaSixIntegralColumn (k l : ℕ) (w z : ℂ) (n : ℕ) : ℂ :=
  (deningerGammaSixShellFlattening n : ℂ) *
    deningerGammaSixTensorFourierLaplace
      (l2SeparatedProduct (deningerGammaSixInternalJetSource k (deningerGammaSixShellHonestDepth n))
        (deningerGammaSixInternalJetSource l (deningerGammaSixShellHonestDepth n))) w z

def deningerGammaSixIntegralRemainder (k l : ℕ) (w z : ℂ) (n : ℕ) : ℂ :=
  (deningerGammaSixShellFlattening n : ℂ) *
    deningerGammaSixTensorFourierLaplace
      (deningerGammaSixInternalJetTensorRemainder k l (deningerGammaSixShellHonestDepth n)) w z

theorem deningerGammaSixShellHalfWeight_sq (n : ℕ) :
    (deningerGammaSixHalfWeight (deningerGammaSixShellHonestDepth n) : ℂ) ^ 2 =
      (deningerGammaSixShellEigenvalue n : ℂ) := by
  have h : (deningerGammaSixHalfWeight (deningerGammaSixShellHonestDepth n)) ^ 2 =
      deningerGammaSixShellEigenvalue n := by
    rw [pow_two, deningerGammaSixHalfWeight_sq]
    rfl
  exact_mod_cast h

theorem deningerGammaSixIntegralColumn_decomposition
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) (n : ℕ) :
    deningerGammaSixIntegralColumn k l w z n =
      (iteratedDeriv k XiC w * iteratedDeriv l XiC z) * ((n : ℂ) + 216)⁻¹ +
        deningerGammaSixIntegralRemainder k l w z n := by
  have hW := deningerGammaSixIntegral_every_depth_admitted (deningerGammaSixShellHonestDepth n) hrw
  have hZ := deningerGammaSixIntegral_every_depth_admitted (deningerGammaSixShellHonestDepth n) hrz
  rw [deningerGammaSixIntegralColumn, deningerGammaSixIntegralRemainder,
    (deningerGammaSixInternalJetTensor_full_fourierLaplace_data k l _ hw hz hrw hrz).2,
    (deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data k l _ hw hz hW hZ).2,
    deningerGammaSixShellHalfWeight_sq]
  have hp : (deningerGammaSixShellFlattening n : ℂ) *
      (deningerGammaSixShellEigenvalue n : ℂ) = ((n : ℂ) + 216)⁻¹ := by
    have hh := congrArg Complex.ofReal (deningerGammaSixShellFlattening_principal n)
    push_cast at hh
    exact hh
  linear_combination (iteratedDeriv k XiC w * iteratedDeriv l XiC z) * hp

/-- Source-derived norm control of the entire, literally evaluated tensor correction. -/
theorem norm_deningerGammaSixIntegralRemainder_le
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) (n : ℕ) :
    ‖deningerGammaSixIntegralRemainder k l w z n‖ ≤
      (deningerGammaSixShellEigenvalue n *
        ‖deningerGammaSixTensorRemainderMultiplier (deningerGammaSixShellDepth n) w z‖) *
          ‖iteratedDeriv k XiC w * iteratedDeriv l XiC z‖ := by
  have hW := deningerGammaSixIntegral_every_depth_admitted (deningerGammaSixShellHonestDepth n) hrw
  have hZ := deningerGammaSixIntegral_every_depth_admitted (deningerGammaSixShellHonestDepth n) hrz
  have hnon : 0 ≤ deningerGammaSixShellEigenvalue n := by
    unfold deningerGammaSixShellEigenvalue
    positivity
  have hval : ‖deningerGammaSixTensorFourierLaplace
      (deningerGammaSixInternalJetTensorRemainder k l (deningerGammaSixShellHonestDepth n)) w z‖ =
      (deningerGammaSixShellEigenvalue n *
        ‖deningerGammaSixTensorRemainderMultiplier (deningerGammaSixShellDepth n) w z‖) *
          ‖iteratedDeriv k XiC w * iteratedDeriv l XiC z‖ := by
    rw [(deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data k l _ hw hz hW hZ).2,
      deningerGammaSixShellHalfWeight_sq, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hnon]
    rfl
  rw [deningerGammaSixIntegralRemainder, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (deningerGammaSixShellFlattening_pos n)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (deningerGammaSixShellFlattening_bounds n).2).trans hval.le

/-- The literal integral reader produces a summable full-source correction. -/
theorem summable_deningerGammaSixIntegralRemainder
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) :
    Summable (deningerGammaSixIntegralRemainder k l w z) := by
  have hs := summable_deningerGammaSixShellEigenvalue_profile
    (fun m => ‖deningerGammaSixTensorRemainderMultiplier m w z‖) (fun m => norm_nonneg _)
    (summable_norm_deningerGammaSixTensorRemainderMultiplier_depth (by linarith) (by linarith))
  exact (hs.mul_right ‖iteratedDeriv k XiC w * iteratedDeriv l XiC z‖).of_norm_bounded
    (norm_deningerGammaSixIntegralRemainder_le k l hw hz hrw hrz)

def deningerGammaSixIntegralNatColumn (k l : ℕ) (w z : ℂ) (a : ℕ) : ℂ :=
  if 216 ≤ a then deningerGammaSixIntegralColumn k l w z (a - 216) else 0

def deningerGammaSixIntegralDiagonal (k l : ℕ) (w z : ℂ) (a : PNat) : ℂ :=
  deningerGammaSixIntegralNatColumn k l w z a

/-- Exact ordinary-integer placement includes every omitted finite head coordinate as a correction. -/
theorem summable_deningerGammaSixIntegralDiagonal_sub_principal
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) :
    Summable (fun a : PNat => deningerGammaSixIntegralDiagonal k l w z a -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC z) * (((a : ℕ) : ℂ))⁻¹) := by
  apply (summable_pnat_iff_summable_nat
    (f := fun a : ℕ => deningerGammaSixIntegralNatColumn k l w z a -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC z) * (a : ℂ)⁻¹)).2
  apply (summable_nat_add_iff 216).1
  refine (summable_deningerGammaSixIntegralRemainder k l hw hz hrw hrz).congr (fun n => ?_)
  rw [deningerGammaSixIntegralNatColumn, if_pos (by omega : 216 ≤ n + 216),
    Nat.add_sub_cancel, deningerGammaSixIntegralColumn_decomposition k l hw hz hrw hrz]
  push_cast
  ring

/-- Sharp integral-source summability criterion, without a bounded Hilbert probe hypothesis. -/
theorem summable_deningerGammaSixIntegralDiagonal_iff
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re) :
    Summable (deningerGammaSixIntegralDiagonal k l w z) ↔
      iteratedDeriv k XiC w * iteratedDeriv l XiC z = 0 := by
  have hs := summable_deningerGammaSixIntegralDiagonal_sub_principal k l hw hz hrw hrz
  constructor
  · intro h
    have hc := h.sub hs
    by_contra hn
    apply not_summable_deningerOrdinaryIntegerReciprocal
    refine (hc.mul_left (iteratedDeriv k XiC w * iteratedDeriv l XiC z)⁻¹).congr (fun a => ?_)
    simp only [sub_sub_cancel, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · intro h
    simpa only [h, zero_mul, sub_zero] using hs

def deningerGammaSixIntegralOperator (k l : ℕ) (w z : ℂ) : DeningerOrdinaryIntegerEnd where
  toFun x a := deningerGammaSixIntegralDiagonal k l w z a * x a
  map_add' x y := by funext a; exact mul_add _ _ _
  map_smul' c x := by funext a; change _ * (c * x a) = c * (_ * x a); ring

theorem deningerOrdinaryIntegerDiagonalCoefficient_integralOperator
    (k l : ℕ) (w z : ℂ) (a : PNat) :
    deningerOrdinaryIntegerDiagonalCoefficient a (deningerGammaSixIntegralOperator k l w z) =
      deningerGammaSixIntegralDiagonal k l w z a := by
  change deningerGammaSixIntegralDiagonal k l w z a * deningerOrdinaryIntegerBasisVector a a = _
  rw [deningerOrdinaryIntegerBasisVector_self, mul_one]

theorem deningerGammaSixIntegralOperator_mem_gibbsDomain
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re)
    {sigma : ℝ} (h : 1 / 2 < sigma) :
    deningerGammaSixIntegralOperator k l w z ∈ deningerOrdinaryIntegerGibbsDomain sigma := by
  have hs := summable_deningerGammaSixIntegralDiagonal_sub_principal k l hw hz hrw hrz
  have hweighted : Summable (fun a : PNat =>
      ((deningerOrdinaryIntegerGibbsMass sigma a : ℂ) * ((a : ℕ) : ℂ)) *
        (deningerGammaSixIntegralDiagonal k l w z a -
          (iteratedDeriv k XiC w * iteratedDeriv l XiC z) * (((a : ℕ) : ℂ))⁻¹)) := by
    apply Summable.of_norm_bounded hs.norm
    intro a
    rw [norm_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (mul_pos (deningerOrdinaryIntegerGibbsMass_pos sigma a)
        (by exact_mod_cast a.pos))]
    exact mul_le_of_le_one_left (norm_nonneg _) (deningerOrdinaryIntegerGibbsWeight_le_one h.le a)
  have hq : Summable (fun a : PNat => (deningerOrdinaryIntegerGibbsMass sigma a : ℂ)) :=
    Complex.summable_ofReal.mpr ((summable_deningerOrdinaryIntegerGibbsMass_iff sigma).2 h)
  refine ((hq.mul_left (iteratedDeriv k XiC w * iteratedDeriv l XiC z)).add hweighted).congr (fun a => ?_)
  change (iteratedDeriv k XiC w * iteratedDeriv l XiC z) * (deningerOrdinaryIntegerGibbsMass sigma a : ℂ) + _ =
    ((deningerOrdinaryIntegerGibbsMass sigma a : ℂ) * ((a : ℕ) : ℂ)) *
      deningerOrdinaryIntegerDiagonalCoefficient a (deningerGammaSixIntegralOperator k l w z)
  rw [deningerOrdinaryIntegerDiagonalCoefficient_integralOperator]
  have ha : (((a : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast a.ne_zero
  field_simp
  ring

/-- The prime-incidence obstruction applies to any admitted operator with this exact scalar asymptotic. -/
theorem deningerOrdinaryIntegerGibbs_prime_cyclic_principal_zero
    (sigma : ℝ) (h : 1 / 2 < sigma) (T : deningerOrdinaryIntegerGibbsDomain sigma) (c : ℂ)
    (hs : Summable (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a T.val -
      c * (((a : ℕ) : ℂ))⁻¹))
    (hc : DeningerOrdinaryIntegerGibbsPrimePairCyclic sigma h T) : c = 0 := by
  by_contra hn
  apply deningerOrdinaryIntegerGibbs_no_summable_prime_cyclic_green_repair sigma h
  refine ⟨c⁻¹ • T, ?_, deningerOrdinaryIntegerGibbsPrimePairCyclic_smul h T hc c⁻¹⟩
  refine (hs.mul_left c⁻¹).congr (fun a => ?_)
  simp only [Submodule.coe_smul, map_sub, map_smul,
    deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen, smul_eq_mul]
  field_simp

/-- A zero retained Xi coefficient makes the whole admitted integral column vanish. -/
theorem deningerGammaSixIntegralColumn_eq_zero
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC z = 0) (n : ℕ) :
    deningerGammaSixIntegralColumn k l w z n = 0 := by
  rw [deningerGammaSixIntegralColumn,
    (deningerGammaSixInternalJetTensor_full_fourierLaplace_data k l _ hw hz hrw hrz).2,
    hc, mul_zero, mul_zero]

theorem deningerGammaSixIntegralOperator_eq_zero
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC z = 0) :
    deningerGammaSixIntegralOperator k l w z = 0 := by
  ext x a
  change deningerGammaSixIntegralNatColumn k l w z a * x a = 0
  unfold deningerGammaSixIntegralNatColumn
  split_ifs
  · rw [deningerGammaSixIntegralColumn_eq_zero k l hw hz hrw hrz hc, zero_mul]
  · exact zero_mul _

/-- Exact prime-test classification of the literal integral source, independent of boundedness. -/
theorem deningerGammaSixIntegralOperator_prime_cyclic_iff
    (k l : ℕ) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hrz : (1 / 3 : ℝ) < (mobiusThetaCenteredParameter z).re)
    (sigma : ℝ) (h : 1 / 2 < sigma) :
    DeningerOrdinaryIntegerGibbsPrimePairCyclic sigma h
      ⟨deningerGammaSixIntegralOperator k l w z,
        deningerGammaSixIntegralOperator_mem_gibbsDomain k l hw hz hrw hrz h⟩ ↔
      iteratedDeriv k XiC w * iteratedDeriv l XiC z = 0 := by
  constructor
  · intro hc
    apply deningerOrdinaryIntegerGibbs_prime_cyclic_principal_zero sigma h
      ⟨deningerGammaSixIntegralOperator k l w z,
        deningerGammaSixIntegralOperator_mem_gibbsDomain k l hw hz hrw hrz h⟩ _ _ hc
    simpa only [deningerOrdinaryIntegerDiagonalCoefficient_integralOperator] using
      summable_deningerGammaSixIntegralDiagonal_sub_principal k l hw hz hrw hrz
  · intro hc
    have hT : (⟨deningerGammaSixIntegralOperator k l w z,
        deningerGammaSixIntegralOperator_mem_gibbsDomain k l hw hz hrw hrz h⟩ :
        deningerOrdinaryIntegerGibbsDomain sigma) = 0 :=
      Subtype.ext (deningerGammaSixIntegralOperator_eq_zero k l hw hz hrw hrz hc)
    rw [hT]
    intro n hn
    simp only [ZeroMemClass.coe_zero, mul_zero, zero_mul]

/-- In the every-depth domain, a retained divisor top jet fails the actual prime tests. -/
theorem deningerGammaSixIntegral_top_jet_not_prime_cyclic
    (rho : XiDivisorSupport) (hrho : (1 / 3 : ℝ) < (rho : ℂ).re)
    (sigma : ℝ) (h : 1 / 2 < sigma) :
    ¬ DeningerOrdinaryIntegerGibbsPrimePairCyclic sigma h
      ⟨deningerGammaSixIntegralOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
          (xiSpectralPointSupport rho) (xiSpectralPointSupport rho),
        deningerGammaSixIntegralOperator_mem_gibbsDomain _ _
          (abs_im_xiSpectralPointSupport_lt_one rho) (abs_im_xiSpectralPointSupport_lt_one rho)
          (by simpa only [mobiusThetaCenteredParameter_xiSpectralPointSupport] using hrho)
          (by simpa only [mobiusThetaCenteredParameter_xiSpectralPointSupport] using hrho) h⟩ := by
  intro hc
  have hz := (deningerGammaSixIntegralOperator_prime_cyclic_iff _ _
    (abs_im_xiSpectralPointSupport_lt_one rho) (abs_im_xiSpectralPointSupport_lt_one rho)
    (by simpa only [mobiusThetaCenteredParameter_xiSpectralPointSupport] using hrho)
    (by simpa only [mobiusThetaCenteredParameter_xiSpectralPointSupport] using hrho) sigma h).1 hc
  exact (mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
    (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)) hz

end
end RHTower
