import GaloisForLFunctions.RHTower.MobiusCriticalPrimeBlockResonance
import GaloisForLFunctions.RHTower.SoninSemilocalGammaMeasureCharacteristic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Positive-width Gamma-visible Möbius prime-block resonance

The synchronized critical prime-block resonance is not confined to the single frequency
`pi / log y`.  Every frequency in the one-sided band

`[pi / log y, 4 * pi / (3 * log y)]`

keeps all terminal-window prime phases in `[2*pi/3, 4*pi/3]`.  Hence every local cosine remains
at most `-1/2`, and the same exponential block lower bound holds throughout a band of width
`pi / (3*log y)`.  This is the finite algebraic/trigonometric core needed to show that any fixed
positive Gamma density sees the resonance after integration; pointwise spikes cannot be discarded
as null sets.
-/

open Complex Filter Finset MeasureTheory Set
open scoped Topology

noncomputable section
namespace RHTower

/-- Cosine remains at most `-1/2` throughout the full negative chamber
`[2*pi/3, 4*pi/3]`. -/
theorem cos_le_neg_half_of_two_pi_div_three_le_of_le_four_pi_div_three
    {theta : ℝ} (hlower : 2 * Real.pi / 3 ≤ theta)
    (hupper : theta ≤ 4 * Real.pi / 3) :
    Real.cos theta ≤ -(1 / 2 : ℝ) := by
  have htwoThird0 : 0 ≤ 2 * Real.pi / 3 := by positivity
  have htwoThirdPi : 2 * Real.pi / 3 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hcosTwoThird : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  by_cases htheta : theta ≤ Real.pi
  · have htheta0 : 0 ≤ theta := htwoThird0.trans hlower
    have hcos := Real.antitoneOn_cos
      ⟨htwoThird0, htwoThirdPi⟩ ⟨htheta0, htheta⟩ hlower
    exact hcos.trans_eq hcosTwoThird
  · have hpiTheta : Real.pi ≤ theta := le_of_not_ge htheta
    have hmirrorLower : 2 * Real.pi / 3 ≤ 2 * Real.pi - theta := by
      nlinarith
    have hmirrorUpper : 2 * Real.pi - theta ≤ Real.pi := by
      nlinarith
    have hmirror0 : 0 ≤ 2 * Real.pi - theta :=
      htwoThird0.trans hmirrorLower
    have hcos := Real.antitoneOn_cos
      ⟨htwoThird0, htwoThirdPi⟩ ⟨hmirror0, hmirrorUpper⟩ hmirrorLower
    rw [Real.cos_two_pi_sub] at hcos
    exact hcos.trans_eq hcosTwoThird

/-- Every terminal-window prime stays in the negative cosine chamber throughout the complete
Gamma-visible resonance band. -/
theorem mobiusCriticalPrimeWindow_cos_le_neg_half_on_gammaBand
    {y t : ℝ} (hy : 27 ≤ y)
    (htLower : Real.pi / Real.log y ≤ t)
    (htUpper : t ≤ 4 * Real.pi / (3 * Real.log y))
    {p : ℕ} (hpmem : p ∈ mobiusCriticalPrimeWindow y) :
    Real.cos (t * Real.log p) ≤ -(1 / 2 : ℝ) := by
  have hy0 : 0 < y := by linarith
  have hy1 : 1 < y := by linarith
  have hx0 : 0 ≤ y / 3 := by positivity
  obtain ⟨hpprime, hplower, hpupper⟩ :=
    (mem_windowPrimes hx0 hy0.le).mp hpmem
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hlogp0 : 0 ≤ Real.log p := (Real.log_pos (by exact_mod_cast hpprime.one_lt)).le
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hlog27 : Real.log (27 : ℝ) ≤ Real.log y :=
    Real.log_le_log (by norm_num) hy
  have hlog27eq : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog3budget : 3 * Real.log 3 ≤ Real.log y := by
    rw [← hlog27eq]
    exact hlog27
  have hloglower : Real.log (y / 3) < Real.log p :=
    Real.log_lt_log (div_pos hy0 (by norm_num)) hplower
  rw [Real.log_div hy0.ne' (by norm_num : (3 : ℝ) ≠ 0)] at hloglower
  have hlogpLower : (2 / 3 : ℝ) * Real.log y ≤ Real.log p := by
    nlinarith
  have hlogpUpper : Real.log p ≤ Real.log y :=
    Real.log_le_log hp0 hpupper
  have ht0 : 0 ≤ t := by
    exact (div_nonneg Real.pi_pos.le hlogy.le).trans htLower
  have hbandUpper0 : 0 ≤ 4 * Real.pi / (3 * Real.log y) := by positivity
  have hthetaLower : 2 * Real.pi / 3 ≤ t * Real.log p := by
    calc
      2 * Real.pi / 3 =
          (Real.pi / Real.log y) * ((2 / 3 : ℝ) * Real.log y) := by
            field_simp
      _ ≤ t * Real.log p :=
        mul_le_mul htLower hlogpLower (by positivity) ht0
  have hthetaUpper : t * Real.log p ≤ 4 * Real.pi / 3 := by
    calc
      t * Real.log p ≤
          (4 * Real.pi / (3 * Real.log y)) * Real.log y :=
        mul_le_mul htUpper hlogpUpper hlogp0 hbandUpper0
      _ = 4 * Real.pi / 3 := by
        field_simp
  exact cos_le_neg_half_of_two_pi_div_three_le_of_le_four_pi_div_three
    hthetaLower hthetaUpper

/-- **Positive-width forward resonance.** The terminal critical prime block obeys the same
exponential squared-modulus lower bound at every frequency in the Gamma-visible band. -/
theorem mobiusCriticalPrimeBlock_norm_sq_lower_on_gammaBand
    {y t : ℝ} (hy : 27 ≤ y)
    (htLower : Real.pi / Real.log y ≤ t)
    (htUpper : t ≤ 4 * Real.pi / (3 * Real.log y)) :
    (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card ≤
      ‖mobiusCriticalPrimeBlock y t‖ ^ 2 := by
  rw [mobiusCriticalPrimeBlock, norm_prod, ← Finset.prod_pow,
    ← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    rw [← Complex.normSq_eq_norm_sq]
    have hx0 : 0 ≤ y / 3 := by linarith
    have hy0 : 0 ≤ y := by linarith
    obtain ⟨hpprime, _hplower, hpupper⟩ :=
      (mem_windowPrimes hx0 hy0).mp hp
    exact one_add_one_div_sqrt_le_normSq_mobiusCriticalPrimeFactor
      hpprime.one_lt hpupper
      (mobiusCriticalPrimeWindow_cos_le_neg_half_on_gammaBand
        hy htLower htUpper hp)

/-- Exact width of the Gamma-visible resonance band. -/
theorem mobiusCriticalPrimeGammaBand_width {y : ℝ} (hy : 1 < y) :
    4 * Real.pi / (3 * Real.log y) - Real.pi / Real.log y =
      Real.pi / (3 * Real.log y) := by
  have hlogy : Real.log y ≠ 0 := (Real.log_pos hy).ne'
  field_simp
  norm_num

/-- A positive weight lower bound on the resonance band transfers directly to an integrated
energy lower bound.  This rules out the possibility that synchronized block resonance disappears
as a measure-zero spike after applying any locally positive Gamma weight. -/
theorem integral_weight_mul_mobiusCriticalPrimeBlock_norm_sq_lower_on_gammaBand
    (w : ℝ → ℝ) (hw : Continuous w) {c y : ℝ}
    (hc : 0 ≤ c) (hy : 27 ≤ y)
    (hwLower : ∀ t ∈ Icc (Real.pi / Real.log y)
        (4 * Real.pi / (3 * Real.log y)), c ≤ w t) :
    (Real.pi / (3 * Real.log y)) *
        (c * (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card) ≤
      ∫ t in Real.pi / Real.log y..4 * Real.pi / (3 * Real.log y),
        w t * ‖mobiusCriticalPrimeBlock y t‖ ^ 2 := by
  have hy1 : 1 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hab : Real.pi / Real.log y ≤ 4 * Real.pi / (3 * Real.log y) := by
    rw [show 4 * Real.pi / (3 * Real.log y) =
      (4 * Real.pi / 3) / Real.log y by field_simp]
    exact (div_le_div_iff_of_pos_right hlogy).2 (by nlinarith [Real.pi_pos])
  have hblockContinuous : Continuous
      (fun t : ℝ => ‖mobiusCriticalPrimeBlock y t‖ ^ 2) := by
    unfold mobiusCriticalPrimeBlock mobiusCriticalPrimeFactor
    fun_prop
  have hIntegrable : IntervalIntegrable
      (fun t : ℝ => w t * ‖mobiusCriticalPrimeBlock y t‖ ^ 2)
      volume (Real.pi / Real.log y) (4 * Real.pi / (3 * Real.log y)) :=
    by
      have hproduct := hw.mul hblockContinuous
      change Continuous (fun t : ℝ =>
        w t * ‖mobiusCriticalPrimeBlock y t‖ ^ 2) at hproduct
      exact hproduct.intervalIntegrable
        (Real.pi / Real.log y) (4 * Real.pi / (3 * Real.log y))
  have hconstIntegrable : IntervalIntegrable
      (fun _ : ℝ => c *
        (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card)
      volume (Real.pi / Real.log y) (4 * Real.pi / (3 * Real.log y)) :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hab hconstIntegrable hIntegrable
    (fun t ht => by
      have hblock := mobiusCriticalPrimeBlock_norm_sq_lower_on_gammaBand hy ht.1 ht.2
      have hbase : 0 ≤
          (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card := by
        positivity
      exact mul_le_mul (hwLower t ht) hblock hbase (hc.trans (hwLower t ht)))
  calc
    (Real.pi / (3 * Real.log y)) *
          (c * (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card) =
        (4 * Real.pi / (3 * Real.log y) - Real.pi / Real.log y) *
          (c * (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card) := by
      rw [mobiusCriticalPrimeGammaBand_width hy1]
    _ = ∫ _t in Real.pi / Real.log y..4 * Real.pi / (3 * Real.log y),
          c * (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ _ := hmono

/-- Any continuous weight positive at zero has a uniform half-height floor on some neighborhood
of zero. -/
theorem exists_local_half_floor_of_continuousAt_of_pos
    {w : ℝ → ℝ} (hw : ContinuousAt w 0) (hw0 : 0 < w 0) :
    ∃ delta > 0, ∀ t : ℝ, |t| < delta → w 0 / 2 ≤ w t := by
  have hhalf : w 0 / 2 < w 0 := by linarith
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), w 0 / 2 < w t :=
    hw.eventually (Ioi_mem_nhds hhalf)
  obtain ⟨delta, hdelta, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨delta, hdelta, fun t ht => (hnear ?_).le⟩
  simpa [Real.dist_eq] using ht

/-- The normalized semilocal Gamma density is strictly positive at the resonance limit point. -/
theorem semilocalArchimedeanGammaDensity_zero_pos :
    0 < semilocalArchimedeanGammaDensity 0 := by
  unfold semilocalArchimedeanGammaDensity
  apply mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) Real.pi_pos) _)
  exact Complex.normSq_pos.mpr <| Complex.Gamma_ne_zero fun n hn => by
    have hre := congrArg Complex.re hn
    norm_num at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The actual normalized semilocal Gamma density has a fixed positive floor on all sufficiently
small resonance bands. -/
theorem exists_semilocalGammaFloor_on_mobiusCriticalPrimeGammaBand :
    ∃ delta > 0, ∀ {y : ℝ}, 27 ≤ y →
      4 * Real.pi / (3 * Real.log y) < delta →
      ∀ t ∈ Icc (Real.pi / Real.log y) (4 * Real.pi / (3 * Real.log y)),
        semilocalArchimedeanGammaDensity 0 / 2 ≤
          semilocalArchimedeanGammaDensity t := by
  obtain ⟨delta, hdelta, hfloor⟩ :=
    exists_local_half_floor_of_continuousAt_of_pos
      continuous_semilocalArchimedeanGammaDensity.continuousAt
      semilocalArchimedeanGammaDensity_zero_pos
  refine ⟨delta, hdelta, ?_⟩
  intro y hy hupper t ht
  have hy1 : 1 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have ht0 : 0 ≤ t :=
    (div_nonneg Real.pi_pos.le hlogy.le).trans ht.1
  apply hfloor t
  rw [abs_of_nonneg ht0]
  exact ht.2.trans_lt hupper

/-- **Concrete Gamma-visible energy lower bound.** Once the moving resonance band lies in the
fixed local Gamma neighborhood, its integrated energy has the explicit exponential block floor. -/
theorem exists_semilocalGamma_mobiusCriticalPrimeBlock_energy_lower :
    ∃ delta > 0, ∀ {y : ℝ}, 27 ≤ y →
      4 * Real.pi / (3 * Real.log y) < delta →
      (Real.pi / (3 * Real.log y)) *
          ((semilocalArchimedeanGammaDensity 0 / 2) *
            (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card) ≤
        ∫ t in Real.pi / Real.log y..4 * Real.pi / (3 * Real.log y),
          semilocalArchimedeanGammaDensity t *
            ‖mobiusCriticalPrimeBlock y t‖ ^ 2 := by
  obtain ⟨delta, hdelta, hfloor⟩ :=
    exists_semilocalGammaFloor_on_mobiusCriticalPrimeGammaBand
  refine ⟨delta, hdelta, ?_⟩
  intro y hy hband
  exact integral_weight_mul_mobiusCriticalPrimeBlock_norm_sq_lower_on_gammaBand
    semilocalArchimedeanGammaDensity
    continuous_semilocalArchimedeanGammaDensity
    (by linarith [semilocalArchimedeanGammaDensity_zero_pos]) hy
    (hfloor hy hband)

end RHTower
