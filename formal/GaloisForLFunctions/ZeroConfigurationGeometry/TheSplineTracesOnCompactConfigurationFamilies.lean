import GaloisForLFunctions.ZeroConfigurationGeometry.TheCompactCoordinatesOfTemperedConfigurations
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import GaloisForLFunctions.SquareRootThreshold.TwoBumpLagStructureLaw
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries

/-!
# Continuity of spline traces on compact configuration families

The two Fourier factors of an autocorrelation give fourth-order inverse-ordinate decay.
This controls the tails uniformly on compact charts and identifies the coordinate sum with
the actual lag structure, including collisions and zeros escaping to infinity.
-/

open Set Finset Filter Topology Complex
open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry.CompactCoordinates
open Zeta23 SquareRootThreshold

/-- One zero's contribution to the autocorrelation trace. -/
def pointKernel (β : ℝ → ℂ) (v : ℝ) (z : ℂ) : ℂ :=
  paperFT (EF.weilTest β β) (gammaOf z) * Complex.exp (I * gammaOf z * v)

/-- Compactly supported continuous tests give continuous kernels at every finite zero. -/
theorem continuous_pointKernel {β : ℝ → ℂ} (hβ : Continuous β)
    (hbc : HasCompactSupport β) (v : ℝ) : Continuous (pointKernel β v) := by
  have hf := (RHTower.EvenSector.differentiable_paperFT_of_compact hβ hbc).continuous
  have hg : Continuous gammaOf := by unfold gammaOf; fun_prop
  have he : pointKernel β v = fun z =>
      paperFT β (gammaOf z) * conj (paperFT β (conj (gammaOf z))) *
        Complex.exp (I * gammaOf z * v) := by
    funext z
    rw [pointKernel, EF.paperFT_weilTest hβ hβ hbc hbc]
  rw [he]
  fun_prop

private theorem inverse_normWeight_le (z : ℂ) (hz : z.im ≠ 0) :
    1 / (1 + ‖gammaOf z‖ ^ 2) ≤ z.im⁻¹ ^ 2 := by
  have hγ : (gammaOf z).re = z.im := by simp [gammaOf]
  have habs : |z.im| ≤ ‖gammaOf z‖ := by simpa only [hγ] using Complex.abs_re_le_norm (gammaOf z)
  have hsq : z.im ^ 2 ≤ ‖gammaOf z‖ ^ 2 := by
    nlinarith only [habs, norm_nonneg (gammaOf z), abs_nonneg z.im, sq_abs z.im]
  have hid : z.im⁻¹ ^ 2 * z.im ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
  apply (div_le_iff₀ (by positivity : 0 < 1 + ‖gammaOf z‖ ^ 2)).mpr
  have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg z.im⁻¹)
  nlinarith only [hh, hid, sq_nonneg z.im⁻¹]

/-- Two Fourier factors give fourth-order decay in the inverse ordinate. -/
theorem exists_pointKernel_bound {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    (hbc : HasCompactSupport β) (v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → z.im ≠ 0 →
      ‖pointKernel β v z‖ ≤ C * z.im⁻¹ ^ 4 := by
  obtain ⟨N, hN, hbound⟩ :=
    RHTower.EvenSector.exists_norm_paperFT_le_of_compact hβ hbc (1 / 2)
  refine ⟨N ^ 2 * Real.exp |v|, by positivity, ?_⟩
  intro z hz0 hz1 hzim
  have hγ : |(gammaOf z).im| ≤ 1 / 2 := by
    have him : (gammaOf z).im = 1 / 2 - z.re := by simp [gammaOf]
    rw [him, abs_le]
    constructor <;> linarith
  have hF : ‖paperFT β (gammaOf z)‖ ≤ N * z.im⁻¹ ^ 2 := by
    calc
      _ ≤ N / (1 + ‖gammaOf z‖ ^ 2) := hbound _ hγ
      _ = N * (1 / (1 + ‖gammaOf z‖ ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (inverse_normWeight_le z hzim) hN
  have hF' : ‖conj (paperFT β (conj (gammaOf z)))‖ ≤ N * z.im⁻¹ ^ 2 := by
    have hh := hbound (conj (gammaOf z)) (by simpa using hγ)
    simp only [norm_conj] at hh ⊢
    exact hh.trans (by simpa only [div_eq_mul_inv, one_div] using
      mul_le_mul_of_nonneg_left (inverse_normWeight_le z hzim) hN)
  have he : ‖Complex.exp (I * gammaOf z * v)‖ ≤ Real.exp |v| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have him : (I * gammaOf z * v).re = -(gammaOf z).im * v := by simp [Complex.mul_re]
    rw [him]
    have hh := mul_le_mul_of_nonneg_right hγ (abs_nonneg v)
    have hp : -((gammaOf z).im) * v ≤ |(gammaOf z).im| * |v| := by
      simpa only [abs_mul, abs_neg] using le_abs_self (-((gammaOf z).im) * v)
    linarith [abs_nonneg v]
  rw [pointKernel, EF.paperFT_weilTest hβ.continuous hβ.continuous hbc hbc,
    norm_mul, norm_mul]
  calc
    _ ≤ (N * z.im⁻¹ ^ 2) * (N * z.im⁻¹ ^ 2) * Real.exp |v| :=
      mul_le_mul (mul_le_mul hF hF' (norm_nonneg _) (by positivity)) he
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A zero inverse ordinate is the missing point at infinity. -/
def slotKernel (β : ℝ → ℂ) (v : ℝ) (a : Slot) : ℂ :=
  if a.2 = 0 then 0 else pointKernel β v (slotPoint a) +
    pointKernel β v (reflect (slotPoint a))

/-- Reflection does not change the inverse ordinate or its fourth-order bound. -/
theorem exists_slotKernel_bound {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    (hbc : HasCompactSupport β) (v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : Slot, ‖slotKernel β v a‖ ≤ C * a.2 ^ 4 := by
  obtain ⟨C, hC, hb⟩ := exists_pointKernel_bound hβ hbc v
  refine ⟨2 * C, by positivity, ?_⟩
  intro a
  by_cases ht : a.2 = 0
  · simp [slotKernel, ht]
  · have ht' : (slotPoint a).im ≠ 0 := inv_ne_zero ht
    have h0 := hb (slotPoint a) a.1.property.1 a.1.property.2 ht'
    have hr0 : 0 ≤ (reflect (slotPoint a)).re := by
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re, slotPoint]
      linarith [a.1.property.2]
    have hr1 : (reflect (slotPoint a)).re ≤ 1 := by
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re, slotPoint]
      linarith [a.1.property.1]
    have h1 := hb (reflect (slotPoint a)) hr0 hr1 (by simpa [reflect] using ht')
    have hi0 : (slotPoint a).im⁻¹ = a.2 := by simp [slotPoint]
    have hi1 : (reflect (slotPoint a)).im⁻¹ = a.2 := by simp [reflect, slotPoint]
    rw [hi0] at h0
    rw [hi1] at h1
    rw [slotKernel, if_neg ht]
    calc
      _ ≤ ‖pointKernel β v (slotPoint a)‖ + ‖pointKernel β v (reflect (slotPoint a))‖ :=
        norm_add_le _ _
      _ ≤ C * a.2 ^ 4 + C * a.2 ^ 4 := add_le_add h0 h1
      _ = _ := by ring
/-- The trace contribution vanishes continuously when an ordinate escapes to infinity. -/
theorem continuous_slotKernel {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    (hbc : HasCompactSupport β) (v : ℝ) : Continuous (slotKernel β v) := by
  obtain ⟨C, hC, hb⟩ := exists_slotKernel_bound hβ hbc v
  apply continuous_iff_continuousAt.mpr
  intro a
  by_cases ha : a.2 = 0
  · have hzero : slotKernel β v a = 0 := by simp only [slotKernel, if_pos ha]
    change Tendsto (slotKernel β v) (𝓝 a) (𝓝 (slotKernel β v a))
    rw [hzero]
    apply squeeze_zero_norm (fun b => hb b)
    have hc : Continuous (fun b : Slot => C * b.2 ^ 4) := by fun_prop
    simpa only [ha, zero_pow (by norm_num : 4 ≠ 0), mul_zero] using hc.tendsto a
  · have hc : ContinuousAt slotPoint a := by
      unfold slotPoint
      fun_prop
    have hr : Continuous (reflect : ℂ → ℂ) := by unfold reflect; fun_prop
    have hk := continuous_pointKernel hβ.continuous hbc v
    have hp := (hk.continuousAt.comp hc).add (hk.continuousAt.comp (hr.continuousAt.comp hc))
    have he : slotKernel β v =ᶠ[𝓝 a] (fun b =>
        pointKernel β v (slotPoint b) + pointKernel β v (reflect (slotPoint b))) := by
      filter_upwards [(continuous_snd.tendsto a).eventually_ne ha] with b hb
      exact if_neg hb
    exact hp.congr_of_eventuallyEq he

/-- The label bound gives a summable fourth-power envelope. -/
theorem summable_fourthPower {C : ℝ} {p : ℕ → Slot} (h : CoordinateBound C p) :
    Summable (fun n => (p n).2 ^ 4) := by
  have hs : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ)))
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hs.mul_left (C ^ 2))
  intro n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have h2 : (p n).2 ^ 2 ≤ C / ((n : ℝ) + 1) := by
    apply (le_div_iff₀ hn).mpr
    simpa only [mul_comm] using h n
  have h4 := pow_le_pow_left₀ (sq_nonneg (p n).2) h2 2
  simpa only [← pow_mul, div_pow, div_eq_mul_inv, mul_pow, inv_pow] using h4

private theorem fourthPower_le {C : ℝ} {p : ℕ → Slot} (h : CoordinateBound C p) (n : ℕ) :
    (p n).2 ^ 4 ≤ C ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
  have h2 : (p n).2 ^ 2 ≤ C / ((n : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    simpa only [mul_comm] using h n
  have h4 := pow_le_pow_left₀ (sq_nonneg (p n).2) h2 2
  simpa only [← pow_mul, div_pow, div_eq_mul_inv, mul_pow, inv_pow] using h4

/-- The reflected trace in compact coordinates. -/
def traceSum (β : ℝ → ℂ) (v : ℝ) (p : ℕ → Slot) : ℂ := ∑' n, slotKernel β v (p n)

theorem summable_slotKernel {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    (hbc : HasCompactSupport β) (v : ℝ) {C : ℝ} {p : ℕ → Slot}
    (h : CoordinateBound C p) : Summable (fun n => slotKernel β v (p n)) := by
  obtain ⟨M, _, hM⟩ := exists_slotKernel_bound hβ hbc v
  exact Summable.of_norm_bounded ((summable_fourthPower h).mul_left M) (fun n => hM (p n))

/-- Fixed-lag traces are continuous on each compact chart, with a uniform summable envelope. -/
theorem continuous_traceSum_family {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    (hbc : HasCompactSupport β) (v : ℝ) (K : ℕ) :
    Continuous (fun p : family K => traceSum β v p) := by
  obtain ⟨M, hM, hb⟩ := exists_slotKernel_bound hβ hbc v
  have hs : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ)))
  apply continuous_tsum (fun n => (continuous_slotKernel hβ hbc v).comp
    ((continuous_apply n).comp continuous_subtype_val)) (hs.mul_left (M * (K : ℝ) ^ 2))
  intro n p
  calc
    _ ≤ M * (p.val n).2 ^ 4 := hb (p.val n)
    _ ≤ M * ((K : ℝ) ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left (fourthPower_le p.property.1 n) hM
    _ = _ := by ring
/-- The decay envelope controls the labelled zero sum before collisions are combined. -/
theorem summable_pointKernel_occurrence {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    (hbc : HasCompactSupport β) (v : ℝ) {C : ℝ} {p : ℕ → Slot}
    (h : CoordinateBound C p) : Summable (fun i : Occurrence p => pointKernel β v (node p i)) := by
  obtain ⟨M, _, hb⟩ := exists_pointKernel_bound hβ hbc v
  have hs := (summable_fourthPower h).subtype (fun n => (p n).2 ≠ 0)
  have ho : Summable (fun i : Occurrence p => (p i.1).2 ^ 4) := by
    apply (summable_prod_of_nonneg (f := fun i : Occurrence p => (p i.1).2 ^ 4)
      (fun _ => by positivity)).mpr
    refine ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
    simpa only [tsum_bool, ← two_mul, Function.comp_apply] using hs.mul_left 2
  apply Summable.of_norm_bounded (ho.mul_left M)
  intro i
  have hz := (config p h).strip (node p i) ⟨i, rfl⟩
  have hzi : (node p i).im ≠ 0 := by rw [node_im]; exact inv_ne_zero i.1.property
  simpa only [node_im, inv_inv] using hb (node p i) hz.1 hz.2 hzi

/-- Slot sums are the actual multiplicity-weighted lag structure of their configurations. -/
theorem traceSum_eq_lagStructure {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    (hbc : HasCompactSupport β) (v : ℝ) {C : ℝ} {p : ℕ → Slot}
    (h : CoordinateBound C p) : traceSum β v p = lagStructure (config p h) β v := by
  have hs := summable_pointKernel_occurrence hβ hbc v h
  have hsupport : Function.support (fun n => slotKernel β v (p n)) ⊆
      {n : ℕ | (p n).2 ≠ 0} := by
    intro n hn ht
    exact hn (by simp only [slotKernel, if_pos ht])
  have hsum : traceSum β v p = ∑' i : Occurrence p, pointKernel β v (node p i) := by
    rw [traceSum, ← tsum_subtype_eq_of_support_subset hsupport, hs.tsum_prod]
    apply tsum_congr
    intro n
    rw [tsum_bool, slotKernel, if_neg n.property]
    rfl
  rw [hsum, ← (hasSum_node h (pointKernel β v) hs).tsum_eq]
  apply tsum_congr
  intro z
  simp only [nsmul_eq_mul, pointKernel]
  ring

/-- Encoding followed by horizontal reflection doubles every actual lag trace. -/
theorem traceSum_encoding {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    (hbc : HasCompactSupport β) (v : ℝ) (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) :
    traceSum β v (encoding Z) = 2 * lagStructure Z β v := by
  have hc := coordinateBound_encoding Z hZ hnoreal
  have hs := summable_pointKernel_occurrence hβ hbc v hc
  rw [traceSum_eq_lagStructure hβ hbc v hc]
  have hh := tsum_encoding_eq_double Z hZ hnoreal hc (pointKernel β v) hs
  have hleft : (∑' z : (config (encoding Z) hc).carrier,
      (config (encoding Z) hc).mult z • pointKernel β v z) =
      lagStructure (config (encoding Z) hc) β v := by
    apply tsum_congr
    intro z
    simp only [nsmul_eq_mul, pointKernel]
    ring
  have hright : (∑' z : Z.carrier, Z.mult z • pointKernel β v z) = lagStructure Z β v := by
    apply tsum_congr
    intro z
    simp only [nsmul_eq_mul, pointKernel]
    ring
  rw [hleft, hright, nsmul_eq_mul, Nat.cast_ofNat] at hh
  exact hh

#print axioms continuous_traceSum_family
#print axioms traceSum_eq_lagStructure
#print axioms traceSum_encoding

end GaloisForLFunctions.ZeroConfigurationGeometry.CompactCoordinates
