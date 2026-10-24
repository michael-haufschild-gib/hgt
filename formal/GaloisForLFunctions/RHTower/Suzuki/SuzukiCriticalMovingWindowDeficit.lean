import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalMovingPrimaryEnergy
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2FirstVariation
import Mathlib.Topology.Sequences

/-!
# Joint Compact-Window Limits, Extended Weil Γ-Lower Semicontinuity, and Deficit Inheritance

For real `L²` sources converging strongly inside a common compact support window while the
positive shift `w n` tends to `0⁺`, the literal Suzuki difference quotient
`(autocorr (f n) 0 - suzukiCriticalSourcePairing (f n) (w n)) / w n` splits into the
nonnegative primary compensated energy and a finite signed remainder containing the Gamma
mass derivative, the growing polar branch, and all prime powers below the window cutoff.

Strong `L²` convergence makes every fixed-lag correlation converge, dominated convergence on
the common correlation cutoff passes the growing polar branch and finite prime-power sum
jointly to their limits, and Fatou's lemma preserves the extended primary energy (including
`⊤`). Consequently:
1. The extended Weil energy `suzukiCriticalExtendedWeilEnergy` is sequentially lower
   semicontinuous along joint `(f n, w n) → (g, 0⁺)` limits on any almost-everywhere common
   support window `[a, b]`, with constant-source recovery at every extended value;
2. Strict extended-Weil positivity of a limit source `g` is automatically inherited as an
   explicit finite-shift literal Suzuki deficit along every strongly convergent compact-window
   approximation `(f n, w n) → (g, 0⁺)` with no rate coupling between `f n → g` and `w n → 0⁺`;
3. Over any compact parameter set `K` of `L²`-continuously varying compact-window sources
   satisfying a uniform Weil floor `c`, sequential compactness yields a single uniform shift
   threshold `ω₀ > 0` without `C²` smoothness or Lipschitz increment envelopes.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ENNReal RealInnerProductSpace
open GaloisForLFunctions.BiScaleUncertainty.SobolevShear
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower
noncomputable section

/-- Extended complete Weil energy of a real `L²` source, retaining infinite Lévy energy in `EReal`
together with the archimedean Gamma bracket and the signed prime–polar pairing. -/
def suzukiCriticalExtendedWeilEnergy (f : ℝ → ℝ) : EReal :=
  (sourceLevyEnergy f : EReal) +
    ((EF.gammaBracket 0 * autocorr f 0 - 2 * fullPairing (autocorr f) : ℝ) : EReal)

/-- Almost-everywhere equality preserves the literal Suzuki source pairing at every shift. -/
theorem suzukiCriticalSourcePairing_ae_eq {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume] g) (omega : ℝ) :
    suzukiCriticalSourcePairing f omega = suzukiCriticalSourcePairing g omega := by
  have hc : autocorr f = autocorr g := funext (autocorr_congr_ae hfg)
  unfold suzukiCriticalSourcePairing
  rw [hc]

/-- Almost-everywhere equality preserves the extended complete Weil energy. -/
theorem suzukiCriticalExtendedWeilEnergy_ae_eq {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume] g) :
    suzukiCriticalExtendedWeilEnergy f = suzukiCriticalExtendedWeilEnergy g := by
  have hc : autocorr f = autocorr g := funext (autocorr_congr_ae hfg)
  have hs (t : ℝ) : sourceAutocorrelation f t = sourceAutocorrelation g t := by
    simpa only [sourceAutocorrelation, autocorr, sub_eq_add_neg] using
      autocorr_congr_ae hfg (-t)
  unfold suzukiCriticalExtendedWeilEnergy sourceLevyEnergy
  simp only [hc, hs]

private theorem tendsto_autocorr_of_toLp_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) (u : ℝ) :
    Tendsto (fun n => autocorr (f n) u) atTop (𝓝 (autocorr g u)) := by
  have h := ((continuous_autocorr_L2_source u).tendsto (hg.toLp g)).comp hfg
  rw [autocorr_congr_ae hg.coeFn_toLp u] at h
  exact h.congr fun n => autocorr_congr_ae (hf n).coeFn_toLp u

/-- Joint convergence of the primary translated cusp under strong `L²` source convergence and
`w n → 0⁺`. -/
theorem tendsto_suzukiCriticalPrimaryCusp_joint_L2
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0)) (u : ℝ) :
    Tendsto (fun n => suzukiCriticalPrimaryCusp (f n) (w n) u) atTop
      (𝓝 (autocorr g u)) := by
  let q (n : ℕ) : Velocity := (hf n).toLp (f n)
  let r : Velocity := hg.toLp g
  have hq_conv : Tendsto q atTop (𝓝 r) := hfg
  have herror : Tendsto (fun n => (‖q n‖ + ‖r‖) * ‖q n - r‖) atTop (𝓝 0) := by
    have h := (hq_conv.norm.add_const ‖r‖).mul (hq_conv.sub (tendsto_const_nhds (x := r))).norm
    simpa only [sub_self, norm_zero, mul_zero] using h
  have hmass : Tendsto (fun n => suzukiCriticalPrimaryMass (w n)) atTop (𝓝 1) :=
    (tendsto_suzukiCriticalPrimaryMass.mono_left nhdsWithin_le_nhds).comp hw
  have hbound : ∀ᶠ n in atTop,
      ‖suzukiCriticalPrimaryCusp (f n) (w n) u - suzukiCriticalPrimaryCusp g (w n) u‖ ≤
        suzukiCriticalPrimaryMass (w n) * ((‖q n‖ + ‖r‖) * ‖q n - r‖) := by
    have ho : ∀ᶠ omega : ℝ in 𝓝[>] 0, omega < 2 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
    filter_upwards [hw.eventually self_mem_nhdsWithin, hw.eventually ho] with n hn hn2
    have h := abs_suzukiCriticalPrimaryCusp_sub_le_L2_norms (q n) r hn (by linarith) u
    rw [suzukiCriticalPrimaryCusp_congr_ae (hf n).coeFn_toLp,
      suzukiCriticalPrimaryCusp_congr_ae hg.coeFn_toLp] at h
    simpa only [Real.norm_eq_abs] using h
  have herr : Tendsto (fun n => suzukiCriticalPrimaryCusp (f n) (w n) u -
      suzukiCriticalPrimaryCusp g (w n) u) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [mul_zero] using hmass.mul herror)
      (Eventually.of_forall fun _ => norm_nonneg _) hbound
  have hfixed : Tendsto (fun n => suzukiCriticalPrimaryCusp g (w n) u) atTop (𝓝 (autocorr g u)) :=
    ((tendstoUniformly_suzukiCriticalPrimaryCusp_of_memLp hg).tendsto_at u).comp hw
  simpa only [sub_add_cancel, zero_add] using herr.add hfixed

private theorem integrable_indicator_Ioo_const (A R : ℝ) :
    Integrable ((Ioo (0 : ℝ) A).indicator (fun _ => R)) := by
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  exact continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-- Joint convergence of the translated growing polar cusp on a common correlation cutoff `A`. -/
theorem tendsto_suzukiCriticalPoleCusp_joint_cutoff_L2
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {A : ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hcut : ∀ n t, A ≤ t → autocorr (f n) t = 0) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n => suzukiCriticalPoleCusp (f n) (w n) u) atTop
      (𝓝 (∫ t in Ioi 0, autocorr g (u + t) * Real.exp (t / 2))) := by
  have hR : 0 ≤ autocorr g 0 := by rw [autocorr_zero_eq_norm_toLp_sq hg]; positivity
  have hRn := (tendsto_autocorr_of_toLp_tendsto hf hg hfg 0).eventually
    (Iio_mem_nhds (show autocorr g 0 < autocorr g 0 + 1 by linarith))
  have hM : ∀ᶠ n in atTop, suzukiCriticalPrimaryMass (w n) < 2 :=
    ((tendsto_suzukiCriticalPrimaryMass.mono_left nhdsWithin_le_nhds).comp hw).eventually
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have ho : ∀ᶠ n in atTop, w n < 1 / 2 := hw.eventually
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  apply tendsto_integral_filter_of_dominated_convergence
    ((Ioo (0 : ℝ) A).indicator (fun _ => (autocorr g 0 + 1) * 2 * Real.exp (A / 2)))
  · exact Eventually.of_forall fun n =>
      (((continuous_autocorr_of_memLp (hf n)).measurable.comp
        (measurable_const.add measurable_id)).mul
          (measurable_suzukiCriticalPoleDensity (w n))).aestronglyMeasurable
  · filter_upwards [hw.eventually self_mem_nhdsWithin, ho, hM, hRn] with n hn ho hM hRn
    apply Eventually.of_forall
    intro t
    by_cases ht : 0 < t
    · by_cases htA : t < A
      · rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) A from ⟨ht, htA⟩)]
        have hP := suzukiCriticalPoleDensity_bounds hn ho.le ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP.1]
        have hexp := Real.exp_le_exp.mpr (show t / 2 ≤ A / 2 by linarith)
        calc
          _ ≤ (autocorr g 0 + 1) * (suzukiCriticalPrimaryMass (w n) * Real.exp (t / 2)) :=
            mul_le_mul ((abs_autocorr_le_zero_of_memLp (hf n) (u + t)).trans hRn.le)
              hP.2 hP.1 (by linarith)
          _ ≤ (autocorr g 0 + 1) * (2 * Real.exp (A / 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hM.le hexp (Real.exp_pos _).le (by norm_num)) (by linarith)
          _ = _ := by ring
      · rw [indicator_of_notMem (show t ∉ Ioo (0 : ℝ) A from fun h => htA h.2),
          hcut n (u + t) (by linarith), zero_mul, norm_zero]
    · rw [indicator_of_notMem (show t ∉ Ioo (0 : ℝ) A from fun h => ht h.1),
        suzukiCriticalPoleDensity_eq_zero_of_nonpos (le_of_not_gt ht), mul_zero, norm_zero]
  · exact (integrable_indicator_Ioo_const A _).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (tendsto_autocorr_of_toLp_tendsto hf hg hfg (u + t)).mul
      ((tendsto_suzukiCriticalPoleDensity ht).comp hw)

/-- Joint convergence of the translated signed source cusp on a common correlation cutoff `A`. -/
theorem tendsto_suzukiCriticalSourceCusp_joint_cutoff_L2
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {A : ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hfc : ∀ n, HasCompactSupport (f n))
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hcut : ∀ n t, A ≤ t → autocorr (f n) t = 0) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n => suzukiCriticalSourceCusp (f n) (w n) u) atTop
      (𝓝 (autocorr g u)) := by
  have hp := tendsto_suzukiCriticalPoleCusp_joint_cutoff_L2 hf hg hfg hw hcut hu
  have hi : Tendsto w atTop (𝓝 0) := hw.mono_right nhdsWithin_le_nhds
  have h := (tendsto_suzukiCriticalPrimaryCusp_joint_L2 hf hg hfg hw u).sub
    ((hi.const_mul 2).mul hp)
  simp only [mul_zero, zero_mul, sub_zero] at h
  apply h.congr'
  have ho : ∀ᶠ n in atTop, w n < 1 / 2 := hw.eventually
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  filter_upwards [hw.eventually self_mem_nhdsWithin, ho] with n hn ho
  exact (suzukiCriticalSourceCusp_eq_of_memLp (hf n) (hfc n) hu hn ho.le).symm

private theorem shiftedCoefficient_zero {n : ℕ} (hn : 2 ≤ n) :
    suzukiShiftedCoefficient 0 n = 0 := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
  rw [suzukiShiftedCoefficient,
    Finset.prod_eq_zero hp (by simp : 1 - (p : ℝ) ^ (-2 * (0 : ℝ)) = 0)]
  simp

private theorem tendsto_shiftedCoefficient_div {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun omega : ℝ => suzukiShiftedCoefficient omega n / omega) (𝓝[>] 0)
      (𝓝 (2 * ArithmeticFunction.vonMangoldt n)) := by
  simpa only [zero_add, shiftedCoefficient_zero hn, sub_zero, smul_eq_mul, div_eq_mul_inv,
    mul_comm] using
    (hasDerivAt_suzukiShiftedCoefficient (by omega : 1 ≤ n)).tendsto_slope_zero_right

/-- Finite signed remainder of the Suzuki difference quotient on a correlation cutoff `A`,
combining the Gamma mass secant, the growing polar branch, and all prime-power terms below `e^A`. -/
def suzukiCriticalWindowSignedRemainder (A : ℝ) (f : ℝ → ℝ) (omega : ℝ) : ℝ :=
  -((suzukiCriticalPrimaryMass omega - 1) / omega) * autocorr f 0 +
    2 * suzukiCriticalPoleCusp f omega 0 -
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        (suzukiShiftedCoefficient omega n / omega * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n)

/-- Joint convergence of the finite signed remainder under strong `L²` convergence on a common
correlation cutoff `A`. -/
theorem tendsto_suzukiCriticalWindowSignedRemainder_joint_L2
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {A : ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hfc : ∀ n, HasCompactSupport (f n))
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hcut : ∀ n t, A ≤ t → autocorr (f n) t = 0) :
    Tendsto (fun n => suzukiCriticalWindowSignedRemainder A (f n) (w n)) atTop
      (𝓝 (((Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi) * autocorr g 0 +
        2 * (∫ t in Ioi 0, autocorr g t * Real.exp (t / 2)) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
          (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
            autocorr g (Real.log n))) := by
  have hM := (tendsto_suzukiCriticalPrimaryMass_secant.neg.comp hw).mul
    (tendsto_autocorr_of_toLp_tendsto hf hg hfg 0)
  have hp := (tendsto_suzukiCriticalPoleCusp_joint_cutoff_L2 hf hg hfg hw hcut
    (le_refl (0 : ℝ))).const_mul 2
  simp only [zero_add] at hp
  have hprime : Tendsto (fun j => ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
      (suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp (f j) (w j) (Real.log n)) atTop
      (𝓝 (∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
          autocorr g (Real.log n))) := by
    apply tendsto_finsetSum
    intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    exact (((tendsto_shiftedCoefficient_div hn2).comp hw).mul_const _).mul
      (tendsto_suzukiCriticalSourceCusp_joint_cutoff_L2 hf hg hfc hfg hw hcut hlog)
  have hneg : -(Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) =
      (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi := by ring
  rw [hneg] at hM
  exact (hM.add hp).sub hprime

/-- Exact finite-shift decomposition of the Suzuki difference quotient into the nonnegative
compensated primary energy and the finite signed remainder on cutoff `A`. -/
theorem suzukiCriticalSourcePairing_div_eq_energy_add_windowRemainder
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    {A omega : ℝ} (hA : 0 < A) (hcut : ∀ t, A ≤ t → autocorr f t = 0)
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) :
    (((autocorr f 0 - suzukiCriticalSourcePairing f omega) / omega : ℝ) : EReal) =
      (suzukiCriticalCompensatedEnergy (fun t => autocorr f 0 - autocorr f t) omega : EReal) +
        ((suzukiCriticalWindowSignedRemainder A f omega : ℝ) : EReal) := by
  rw [coe_suzukiCriticalCompensatedEnergy_autocorr hf homega (by linarith), ← EReal.coe_add]
  congr 1
  have hN : 1 ≤ ⌊Real.exp A⌋₊ := by
    simpa using Nat.floor_mono (Real.one_le_exp_iff.mpr hA.le)
  have hsplit : (∑ n ∈ Finset.Icc 1 ⌊Real.exp A⌋₊,
      (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log n)) =
      suzukiCriticalSourceCusp f omega 0 +
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n) := by
    have hset : Finset.Icc 1 ⌊Real.exp A⌋₊ = insert 1 (Finset.Icc 2 ⌊Real.exp A⌋₊) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp [suzukiShiftedCoefficient]
  have hdiv : (∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
      (suzukiShiftedCoefficient omega n / omega * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log n)) =
      (∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n)) / omega := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [suzukiCriticalWindowSignedRemainder, hdiv,
    suzukiCriticalSourcePairing_eq_finite_of_memLp hf hfc hA hcut homega homega2,
    hsplit, suzukiCriticalSourceCusp_eq_of_memLp hf hfc (le_refl (0 : ℝ)) homega homega2]
  field_simp [ne_of_gt homega]
  ring

private theorem coe_primaryEnergy_le_liminf {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0)) :
    (suzukiCriticalLimitingCompensatedEnergy (fun t => autocorr g 0 - autocorr g t) : EReal) ≤
      liminf (fun n => (suzukiCriticalCompensatedEnergy
        (fun t => autocorr (f n) 0 - autocorr (f n) t) (w n) : EReal)) atTop := by
  have h := suzukiCriticalLimitingEnergy_le_liminf_of_L2_tendsto hfg hw
  have hc (n : ℕ) : autocorr ((hf n).toLp (f n)) = autocorr (f n) :=
    funext (autocorr_congr_ae (hf n).coeFn_toLp)
  have hr : autocorr (hg.toLp g) = autocorr g := funext (autocorr_congr_ae hg.coeFn_toLp)
  simp only [hc, hr] at h
  have hmono : Monotone ENNReal.toEReal := fun _ _ hab =>
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr hab
  change ENNReal.toEReal (suzukiCriticalLimitingCompensatedEnergy
    (fun t => autocorr g 0 - autocorr g t)) ≤
    liminf (ENNReal.toEReal ∘ fun n => suzukiCriticalCompensatedEnergy
      (fun t => autocorr (f n) 0 - autocorr (f n) t) (w n)) atTop
  rw [← hmono.map_liminf_of_continuousAt _ continuous_coe_ennreal_ereal.continuousAt]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr h

private theorem finiteEnergy_eq_extendedWeilEnergy {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) {A : ℝ}
    (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0) :
    (suzukiCriticalLimitingCompensatedEnergy (fun t => autocorr f 0 - autocorr f t) : EReal) +
      ((((Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi) * autocorr f 0 +
        2 * (∫ t in Ioi 0, autocorr f t * Real.exp (t / 2)) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
          (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
            autocorr f (Real.log n)) : ℝ) =
      suzukiCriticalExtendedWeilEnergy f := by
  simpa only [suzukiCriticalExtendedWeilEnergy] using
    suzukiCriticalFiniteEnergy_eq_extendedWeilEnergy hf hfc hcut

/-- **Joint Γ-Liminf Inequality on a Common Correlation Cutoff.**
Under strong `L²` convergence `f n → g` and `w n → 0⁺` with common correlation cutoff `A > 0`,
`suzukiCriticalExtendedWeilEnergy g` bounds the lower limit of the finite-shift Suzuki difference
quotients in `EReal`, retaining all signed Gamma, prime, and polar terms as well as `⊤`. -/
theorem suzukiCriticalExtendedWeilEnergy_le_liminf_joint_cutoff
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {A : ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hfc : ∀ n, HasCompactSupport (f n)) (hgc : HasCompactSupport g)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0)) (hA : 0 < A)
    (hcut : ∀ n t, A ≤ t → autocorr (f n) t = 0)
    (hgcut : ∀ t, A ≤ t → autocorr g t = 0) :
    suzukiCriticalExtendedWeilEnergy g ≤
      liminf (fun n => (((autocorr (f n) 0 - suzukiCriticalSourcePairing (f n) (w n)) / w n : ℝ) :
        EReal)) atTop := by
  set R_lim : ℝ := ((Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi) * autocorr g 0 +
    2 * (∫ t in Ioi 0, autocorr g t * Real.exp (t / 2)) -
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
      (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        autocorr g (Real.log n)
  have hc : Tendsto (fun n => ((suzukiCriticalWindowSignedRemainder A (f n) (w n) : ℝ) : EReal))
      atTop (𝓝 (R_lim : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp
      (tendsto_suzukiCriticalWindowSignedRemainder_joint_L2 hf hg hfc hfg hw hcut)
  have h1 : (suzukiCriticalLimitingCompensatedEnergy
      (fun t => autocorr g 0 - autocorr g t) : EReal) + (R_lim : EReal) ≤
      liminf (fun n => (suzukiCriticalCompensatedEnergy
        (fun t => autocorr (f n) 0 - autocorr (f n) t) (w n) : EReal) +
          ((suzukiCriticalWindowSignedRemainder A (f n) (w n) : ℝ) : EReal)) atTop := by
    calc (suzukiCriticalLimitingCompensatedEnergy
          (fun t => autocorr g 0 - autocorr g t) : EReal) + (R_lim : EReal)
        ≤ liminf (fun n => (suzukiCriticalCompensatedEnergy
            (fun t => autocorr (f n) 0 - autocorr (f n) t) (w n) : EReal)) atTop +
          liminf (fun n => ((suzukiCriticalWindowSignedRemainder A (f n) (w n) : ℝ) : EReal))
            atTop := by
          rw [hc.liminf_eq]
          exact add_le_add (coe_primaryEnergy_le_liminf hf hg hfg hw) le_rfl
      _ ≤ _ := EReal.le_liminf_add
  rw [finiteEnergy_eq_extendedWeilEnergy hg hgc hgcut] at h1
  refine h1.trans_eq ?_
  apply Filter.liminf_congr
  have ho : ∀ᶠ n in atTop, w n < 1 / 2 := hw.eventually
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  filter_upwards [hw.eventually self_mem_nhdsWithin, ho] with n hn ho
  exact (suzukiCriticalSourcePairing_div_eq_energy_add_windowRemainder
    (hf n) (hfc n) hA (hcut n) hn ho.le).symm

private theorem hasCompactSupport_of_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hs : ∀ x ∉ Icc a b, f x = 0) : HasCompactSupport f := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := a) (b := b)) isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  exact hx (hs x hnot)

private theorem autocorr_eq_zero_of_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hs : ∀ x ∉ Icc a b, f x = 0) {t : ℝ} (ht : b - a < |t|) :
    autocorr f t = 0 := by
  unfold autocorr
  have hzero : (fun u => f u * f (u + t)) = fun _ => 0 := by
    funext u
    by_cases hu : u ∈ Icc a b
    · have hut : u + t ∉ Icc a b := by
        intro hut
        have habs : |t| ≤ b - a := abs_le.mpr ⟨by linarith [hu.2, hut.1], by linarith [hu.1, hut.2]⟩
        linarith
      rw [hs (u + t) hut, mul_zero]
    · rw [hs u hu, zero_mul]
  rw [hzero, integral_zero]

/-- **Joint Γ-Liminf Inequality on a Common Support Window `[a, b]`.** -/
theorem suzukiCriticalExtendedWeilEnergy_le_liminf_joint_window
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {a b : ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hs : ∀ n x, x ∉ Icc a b → f n x = 0) (hgs : ∀ x, x ∉ Icc a b → g x = 0)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0)) :
    suzukiCriticalExtendedWeilEnergy g ≤
      liminf (fun n => (((autocorr (f n) 0 - suzukiCriticalSourcePairing (f n) (w n)) / w n : ℝ) :
        EReal)) atTop := by
  set A : ℝ := max (b - a) 0 + 1
  have hA : 0 < A := by
    have := le_max_right (b - a) 0
    linarith
  apply suzukiCriticalExtendedWeilEnergy_le_liminf_joint_cutoff hf hg
    (fun n => hasCompactSupport_of_Icc (hs n)) (hasCompactSupport_of_Icc hgs) hfg hw hA
  · intro n t ht
    refine autocorr_eq_zero_of_Icc (hs n) ?_
    have hba : b - a ≤ max (b - a) 0 := le_max_left _ _
    have habs : t ≤ |t| := le_abs_self t
    linarith
  · intro t ht
    refine autocorr_eq_zero_of_Icc hgs ?_
    have hba : b - a ≤ max (b - a) 0 := le_max_left _ _
    have habs : t ≤ |t| := le_abs_self t
    linarith

private theorem indicator_Icc_ae_eq {f : ℝ → ℝ} {a b : ℝ}
    (hs : ∀ᵐ x ∂volume, x ∉ Icc a b → f x = 0) :
    (Icc a b).indicator f =ᵐ[volume] f := by
  classical
  filter_upwards [hs] with x hx
  by_cases hi : x ∈ Icc a b
  · rw [indicator_of_mem hi]
  · rw [indicator_of_notMem hi, hx hi]

/-- **Joint Γ-Liminf Inequality on an Almost-Everywhere Common Support Window `[a, b]`.**
Every `L²` representative vanishing almost everywhere outside `[a, b]` obeys the exact extended
Weil lower bound along joint `(f n, w n) → (g, 0⁺)` convergence. -/
theorem suzukiCriticalExtendedWeilEnergy_le_liminf_joint_ae_window
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {a b : ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hs : ∀ n, ∀ᵐ x ∂volume, x ∉ Icc a b → f n x = 0)
    (hgs : ∀ᵐ x ∂volume, x ∉ Icc a b → g x = 0)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0)) :
    suzukiCriticalExtendedWeilEnergy g ≤
      liminf (fun n => (((autocorr (f n) 0 - suzukiCriticalSourcePairing (f n) (w n)) / w n : ℝ) :
        EReal)) atTop := by
  classical
  let F (n : ℕ) := (Icc a b).indicator (f n)
  let G := (Icc a b).indicator g
  have hF (n : ℕ) : MemLp (F n) 2 volume := (hf n).indicator measurableSet_Icc
  have hG : MemLp G 2 volume := hg.indicator measurableSet_Icc
  have hFe (n : ℕ) : F n =ᵐ[volume] f n := indicator_Icc_ae_eq (hs n)
  have hGe : G =ᵐ[volume] g := indicator_Icc_ae_eq hgs
  have hFLp (n : ℕ) : (hF n).toLp (F n) = (hf n).toLp (f n) :=
    (hF n).toLp_congr (hf n) (hFe n)
  have hGLp : hG.toLp G = hg.toLp g := hG.toLp_congr hg hGe
  have hconv : Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hG.toLp G)) := by
    simpa only [hFLp, hGLp] using hfg
  have h := suzukiCriticalExtendedWeilEnergy_le_liminf_joint_window hF hG
    (fun n x hx => indicator_of_notMem hx (f n))
    (fun x hx => indicator_of_notMem hx g) hconv hw
  have hFC (n : ℕ) : autocorr (F n) 0 = autocorr (f n) 0 := autocorr_congr_ae (hFe n) 0
  have hpair (n : ℕ) := suzukiCriticalSourcePairing_ae_eq (hFe n) (w n)
  simpa only [suzukiCriticalExtendedWeilEnergy_ae_eq hGe, hFC, hpair] using h

/-- **Constant-Source Γ-Recovery on `[a, b]`.**
Along any positive shift sequence `w n → 0⁺`, the constant sequence `f n = g` recovers the exact
extended Weil energy `suzukiCriticalExtendedWeilEnergy g` (including `⊤`) for every `L²` class
supported almost everywhere in `[a, b]`. -/
theorem tendsto_suzukiCriticalSourcePairing_joint_ae_constant_source
    {g : ℝ → ℝ} {w : ℕ → ℝ} {a b : ℝ} (hg : MemLp g 2 volume)
    (hgs : ∀ᵐ x ∂volume, x ∉ Icc a b → g x = 0)
    (hw : Tendsto w atTop (𝓝[>] 0)) :
    Tendsto (fun n => (((autocorr g 0 - suzukiCriticalSourcePairing g (w n)) / w n : ℝ) : EReal))
      atTop (𝓝 (suzukiCriticalExtendedWeilEnergy g)) := by
  classical
  let G := (Icc a b).indicator g
  have hG : MemLp G 2 volume := hg.indicator measurableSet_Icc
  have hGe : G =ᵐ[volume] g := indicator_Icc_ae_eq hgs
  have hGc : HasCompactSupport G :=
    hasCompactSupport_of_Icc (fun _ hx => indicator_of_notMem hx g)
  have h : Tendsto (fun n => (((autocorr G 0 - suzukiCriticalSourcePairing G (w n)) / w n : ℝ) :
      EReal)) atTop (𝓝 (suzukiCriticalExtendedWeilEnergy G)) :=
    (tendsto_suzukiCriticalSourcePairing_extended_firstVariation hG hGc).comp hw
  have hGC : autocorr G 0 = autocorr g 0 := autocorr_congr_ae hGe 0
  have hpair (n : ℕ) := suzukiCriticalSourcePairing_ae_eq hGe (w n)
  simpa only [suzukiCriticalExtendedWeilEnergy_ae_eq hGe, hGC, hpair] using h

/-- **General Deficit Inheritance from an Extended-Real Lower Limit.**
Whenever `((c : ℝ) : EReal)` bounds the `EReal` lower limit of the finite-shift Suzuki difference
quotients along `w j → 0⁺`, every positive slack `δ > 0` yields an eventual linear finite-shift
deficit `w j * (c - δ) < autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j)`. -/
theorem eventually_suzukiCriticalDeficit_of_le_liminf {α : Type*} {l : Filter α}
    {f : α → ℝ → ℝ} {w : α → ℝ} {c δ : ℝ} (hδ : 0 < δ)
    (hw : Tendsto w l (𝓝[>] 0))
    (hlim : ((c : ℝ) : EReal) ≤
      liminf (fun j => (((autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j)) / w j : ℝ) :
        EReal)) l) :
    ∀ᶠ j in l, w j * (c - δ) < autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j) := by
  have hlt : (((c - δ : ℝ) : EReal) <
      liminf (fun j => (((autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j)) / w j : ℝ) :
        EReal)) l) :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith)) hlim
  filter_upwards [hw.eventually self_mem_nhdsWithin, eventually_lt_of_lt_liminf hlt] with j hwj hqj
  change 0 < w j at hwj
  have hq : c - δ < (autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j)) / w j :=
    EReal.coe_lt_coe_iff.mp hqj
  simpa only [mul_comm] using (lt_div_iff₀ hwj).mp hq

/-- **Uncoupled Joint-Window Positive-Deficit Inheritance.**
If `g` has extended Weil energy at least `c` (and in particular if `c > 0`, giving half-margin
`c / 2 > 0`), then **every** sequence `f n → g` in `L²(ℝ)` supported a.e. in `[a, b]` and **every**
shift sequence `w n → 0⁺` — with no prescribed rate between `‖f n - g‖₂` and `w n` — eventually
satisfy the literal Suzuki deficit `w n * (c - δ) < autocorr (f n) 0 - suzukiCriticalSourcePairing (f n) (w n)`. -/
theorem eventually_suzukiCriticalDeficit_of_joint_window_L2
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {a b c δ : ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hs : ∀ n, ∀ᵐ x ∂volume, x ∉ Icc a b → f n x = 0)
    (hgs : ∀ᵐ x ∂volume, x ∉ Icc a b → g x = 0)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hweil : ((c : ℝ) : EReal) ≤ suzukiCriticalExtendedWeilEnergy g)
    (hδ : 0 < δ) :
    ∀ᶠ n in atTop, w n * (c - δ) <
      autocorr (f n) 0 - suzukiCriticalSourcePairing (f n) (w n) :=
  eventually_suzukiCriticalDeficit_of_le_liminf hδ hw
    (hweil.trans (suzukiCriticalExtendedWeilEnergy_le_liminf_joint_ae_window hf hg hs hgs hfg hw))

/-- **Infinite Extended-Weil Energy Divergence on a Common Window.**
If `suzukiCriticalExtendedWeilEnergy g = ⊤`, then along every `f n → g` in `L²(ℝ)` inside `[a, b]`
and every `w n → 0⁺`, the normalized Suzuki difference quotients diverge to `⊤` with no rate
assumption on `f n → g`. -/
theorem tendsto_suzukiCriticalQuotient_top_of_joint_window_L2
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {a b : ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hs : ∀ n, ∀ᵐ x ∂volume, x ∉ Icc a b → f n x = 0)
    (hgs : ∀ᵐ x ∂volume, x ∉ Icc a b → g x = 0)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (htop : suzukiCriticalExtendedWeilEnergy g = ⊤) :
    Tendsto (fun n => (((autocorr (f n) 0 - suzukiCriticalSourcePairing (f n) (w n)) / w n : ℝ) :
      EReal)) atTop (𝓝 ⊤) := by
  have h := suzukiCriticalExtendedWeilEnergy_le_liminf_joint_ae_window hf hg hs hgs hfg hw
  rw [htop] at h
  exact tendsto_of_le_liminf_of_limsup_le h le_top

/-- **Compact-Family Uniform Shift Theorem Without `C²` Regularity.**
Let `{f p}_{p ∈ K}` be a compact family of `L²` sources parameterized over a first-countable
topological space `P`, varying continuously in `L²(ℝ)` on `K`, vanishing a.e. outside a common
window `[a, b]`, and satisfying a uniform extended-Weil lower bound `c ≤ W_ext(f p)`. Then for
every `δ > 0` there exists a **single positive shift threshold `ω₀ > 0` uniform over `p ∈ K`** on
which `ω * (c - δ) < autocorr (f p) 0 - suzukiCriticalSourcePairing (f p) ω` holds simultaneously
for all `p ∈ K` and `ω ∈ (0, ω₀)`. -/
theorem exists_suzukiCriticalUniformShift_of_compact_window_family
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {K : Set P} (hK : IsCompact K) (f : P → ℝ → ℝ)
    (hf : ∀ p, MemLp (f p) 2 volume)
    (hcont : ContinuousOn (fun p => (hf p).toLp (f p)) K)
    {a b c δ : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ p ∈ K, ∀ᵐ x ∂volume, x ∉ Icc a b → f p x = 0)
    (hweil : ∀ p ∈ K, ((c : ℝ) : EReal) ≤ suzukiCriticalExtendedWeilEnergy (f p)) :
    ∃ omega₀ : ℝ, 0 < omega₀ ∧ ∀ omega : ℝ, 0 < omega → omega < omega₀ →
      ∀ p ∈ K, omega * (c - δ) < autocorr (f p) 0 - suzukiCriticalSourcePairing (f p) omega := by
  suffices hev : ∀ᶠ omega : ℝ in 𝓝[>] 0,
      ∀ p ∈ K, omega * (c - δ) < autocorr (f p) 0 - suzukiCriticalSourcePairing (f p) omega by
    obtain ⟨omega₀, homega₀, hball⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
    refine ⟨omega₀, homega₀, fun omega homega homega_lt p hp => ?_⟩
    have hmem := hball (by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos homega]
      exact homega_lt)
    exact hmem homega p hp
  by_contra hnot
  have hex : ∀ n : ℕ, ∃ omega : ℝ, ∃ p : P,
      (0 < omega ∧ omega < 1 / ((n : ℝ) + 1)) ∧ p ∈ K ∧
      autocorr (f p) 0 - suzukiCriticalSourcePairing (f p) omega ≤ omega * (c - δ) := by
    intro n
    by_contra hn
    push Not at hn
    apply hnot
    have h0_lt : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hmem : Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin.mpr ⟨Iio (1 / ((n : ℝ) + 1)), isOpen_Iio, mem_Iio.mpr h0_lt,
        fun x hx => ⟨hx.2, hx.1⟩⟩
    filter_upwards [hmem] with omega homega p hp
    exact hn omega p ⟨homega.1, homega.2⟩ hp
  choose w p hwp using hex
  have hw_pos : ∀ n, 0 < w n := fun n => (hwp n).1.1
  have hw_lt : ∀ n, w n < 1 / ((n : ℝ) + 1) := fun n => (hwp n).1.2
  have hp_mem : ∀ n, p n ∈ K := fun n => (hwp n).2.1
  have hp_le : ∀ n,
      autocorr (f (p n)) 0 - suzukiCriticalSourcePairing (f (p n)) (w n) ≤ w n * (c - δ) :=
    fun n => (hwp n).2.2
  have hw0 : Tendsto w atTop (𝓝 0) :=
    squeeze_zero (fun n => (hw_pos n).le) (fun n => (hw_lt n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : Tendsto w atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hw0, Eventually.of_forall hw_pos⟩
  obtain ⟨p₀, hp₀, φ, hφ, hp_conv⟩ := hK.tendsto_subseq hp_mem
  have hp_within : Tendsto (p ∘ φ) atTop (𝓝[K] p₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hp_conv, Eventually.of_forall fun k => hp_mem (φ k)⟩
  have hLp_conv : Tendsto (fun k => (hf (p (φ k))).toLp (f (p (φ k)))) atTop
      (𝓝 ((hf p₀).toLp (f p₀))) :=
    (hcont p₀ hp₀).tendsto.comp hp_within
  have hw_sub : Tendsto (w ∘ φ) atTop (𝓝[>] 0) := hw.comp hφ.tendsto_atTop
  have hev_gt := eventually_suzukiCriticalDeficit_of_joint_window_L2
    (f := fun k => f (p (φ k))) (g := f p₀) (w := w ∘ φ) (c := c) (δ := δ / 2)
    (fun k => hf (p (φ k))) (hf p₀)
    (fun k => hsupp (p (φ k)) (hp_mem (φ k))) (hsupp p₀ hp₀)
    hLp_conv hw_sub (hweil p₀ hp₀) (by positivity)
  obtain ⟨k, hk_gt⟩ := hev_gt.exists
  have hk_le := hp_le (φ k)
  have hwk : 0 < w (φ k) := hw_pos (φ k)
  have hmul : w (φ k) * (c - δ / 2) < w (φ k) * (c - δ) := lt_of_lt_of_le hk_gt hk_le
  have hdiv : c - δ / 2 < c - δ := lt_of_mul_lt_mul_left hmul hwk.le
  linarith

end
end RHTower

#print axioms RHTower.suzukiCriticalExtendedWeilEnergy
#print axioms RHTower.suzukiCriticalSourcePairing_ae_eq
#print axioms RHTower.suzukiCriticalExtendedWeilEnergy_ae_eq
#print axioms RHTower.tendsto_suzukiCriticalPrimaryCusp_joint_L2
#print axioms RHTower.tendsto_suzukiCriticalPoleCusp_joint_cutoff_L2
#print axioms RHTower.tendsto_suzukiCriticalSourceCusp_joint_cutoff_L2
#print axioms RHTower.suzukiCriticalWindowSignedRemainder
#print axioms RHTower.tendsto_suzukiCriticalWindowSignedRemainder_joint_L2
#print axioms RHTower.suzukiCriticalSourcePairing_div_eq_energy_add_windowRemainder
#print axioms RHTower.suzukiCriticalExtendedWeilEnergy_le_liminf_joint_cutoff
#print axioms RHTower.suzukiCriticalExtendedWeilEnergy_le_liminf_joint_window
#print axioms RHTower.suzukiCriticalExtendedWeilEnergy_le_liminf_joint_ae_window
#print axioms RHTower.tendsto_suzukiCriticalSourcePairing_joint_ae_constant_source
#print axioms RHTower.eventually_suzukiCriticalDeficit_of_le_liminf
#print axioms RHTower.eventually_suzukiCriticalDeficit_of_joint_window_L2
#print axioms RHTower.tendsto_suzukiCriticalQuotient_top_of_joint_window_L2
#print axioms RHTower.exists_suzukiCriticalUniformShift_of_compact_window_family
