import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalMovingWindowDeficit
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# General Moving-Aperture Control, Divided-Coefficient Domination, and Supercritical Correlation Decay

Removing a fixed compact support window from the literal Suzuki source pairing
`suzukiCriticalSourcePairing f ω` introduces two distinct analytic obstacles:
1. The polar branch `suzukiCriticalPoleDensity ω t` grows as `e^{(1/2 - ω) t}` (`≤ M(ω) e^{t/2}`),
   so the naive `L²` envelope `|autocorr f t| ≤ autocorr f 0` fails to integrate;
2. The arithmetic sum over `1 ≤ n ≤ e^t` becomes an infinite series of translated cusps as `t → ∞`,
   whose divided coefficients `suzukiShiftedCoefficient ω n / ω` must be dominated uniformly in
   `ω > 0` across all `n ≥ 2`.

This module resolves both obstacles unconditionally and establishes moving-aperture control in two
complementary regimes:

1. **Uniform Divided-Coefficient Domination (`suzukiShiftedCoefficient_div_bounds`):**
   For every `n ≥ 2` and every `ω > 0`, selecting one prime factor `p ∣ n` bounds
   `1 - p^{-2ω} ≤ 2 ω log n` while all remaining Euler factors lie in `[0, 1]`, giving
   `0 ≤ suzukiShiftedCoefficient ω n / ω ≤ 2 * (n : ℝ) ^ ω * Real.log n`.

2. **Supercritical Correlation Decay (`β > 1/2`) and Exact Infinite Arithmetic Fubini
   (`suzukiCriticalSourcePairing_eq_tsum_of_exp_decay`,
   `tendsto_suzukiCriticalSourcePairing_extended_firstVariation_of_exp_decay`):**
   Whenever `f ∈ L²(ℝ)` satisfies `|autocorr f t| ≤ K e^{-β t}` (`t ≥ 0`, `β > 1/2`), the `L¹` norm
   of the `n`-th translated source cusp decays as `O(n^{-β})`. Combined with divided-coefficient
   domination, the `n ≥ 2` series is uniformly majorized by `O(log n · n^{-(β + 1/2 - ω)})` for
   `0 < ω ≤ min(1/4, (β - 1/2)/2)`, justifying both Fubini (`integral_tsum_of_summable_integral_norm`)
   and Tannery dominated convergence (`tendsto_tsum_of_dominated_convergence`) and yielding the
   exact extended Weil first variation `suzukiCriticalExtendedWeilEnergy f` without compact support.

3. **Uncoupled Moving/Infinite-Aperture Γ-Liminf Under Supercritical Decay
   (`suzukiCriticalExtendedWeilEnergy_le_liminf_of_exp_decay_tendsto`,
   `eventually_suzukiCriticalDeficit_of_exp_decay_tendsto`):**
   Along any sequence `f j → g` in `L²(ℝ)` and `w j → 0⁺` sharing a uniform supercritical
   correlation bound `|autocorr (f j) t| ≤ K e^{-β t}` (`β > 1/2`), `W_ext(g) ≤ liminf_j Q_{w_j}(f_j)`
   holds with **no compact support and no growth-rate coupling** between the apertures and `w j`.

4. **Coupled General Moving-Aperture Γ-Liminf Without Correlation Decay on Approximants
   (`suzukiCriticalExtendedWeilEnergy_le_liminf_of_coupled_moving_aperture`,
   `eventually_suzukiCriticalDeficit_of_coupled_moving_aperture`):**
   For arbitrary compact `L²` approximants `f j` with growing correlation cutoffs `A j → ∞` (and no
   correlation decay assumption on `f j`) converging in `L²(ℝ)` to a supercritical-decay target `g`
   under `e^{2 A_j} ‖f_j - g‖₂ → 0`, explicit finite-aperture perturbation bounds establish
   `W_ext(g) ≤ liminf_j Q_{w_j}(f_j)` and positive-deficit inheritance.
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

/-! ## Section 1: Uniform Divided-Coefficient Domination -/

/-- **Divided-Coefficient Domination for Shifted Jordan–Euler Coefficients.**
For every integer `n ≥ 2` and every positive shift `ω > 0`,
`0 ≤ suzukiShiftedCoefficient ω n / ω ≤ 2 * (n : ℝ) ^ ω * Real.log n`. -/
theorem suzukiShiftedCoefficient_div_bounds {n : ℕ} (hn : 2 ≤ n) {omega : ℝ} (homega : 0 < omega) :
    0 ≤ suzukiShiftedCoefficient omega n / omega ∧
    suzukiShiftedCoefficient omega n / omega ≤ 2 * (n : ℝ) ^ omega * Real.log n := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_le : p ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfac_nn : ∀ q ∈ n.primeFactors, 0 ≤ 1 - (q : ℝ) ^ (-2 * omega) := by
    intro q hq
    have hq_prime := Nat.prime_of_mem_primeFactors hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq_prime.one_lt.le
    have hrpow : (q : ℝ) ^ (-2 * omega) ≤ (q : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    rw [Real.rpow_zero] at hrpow
    linarith
  have hfac_le : ∀ q ∈ n.primeFactors, 1 - (q : ℝ) ^ (-2 * omega) ≤ 1 := by
    intro q hq
    have hq_prime := Nat.prime_of_mem_primeFactors hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq_prime.pos
    linarith [Real.rpow_pos_of_pos hq0 (-2 * omega)]
  refine ⟨div_nonneg (mul_nonneg (Real.rpow_nonneg hn0 _) (Finset.prod_nonneg hfac_nn)) homega.le,
    ?_⟩
  have hp_bound : 1 - (p : ℝ) ^ (-2 * omega) ≤ 2 * omega * Real.log n := by
    have hexp := Real.add_one_le_exp (Real.log p * (-2 * omega))
    have h1 : 1 - (p : ℝ) ^ (-2 * omega) ≤ 2 * omega * Real.log p := by
      rw [Real.rpow_def_of_pos hp0]
      linarith
    have hlog : Real.log p ≤ Real.log n := Real.log_le_log hp0 (by exact_mod_cast hp_le)
    exact h1.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
  have herase_le : ∏ q ∈ n.primeFactors.erase p, (1 - (q : ℝ) ^ (-2 * omega)) ≤ 1 :=
    Finset.prod_le_one (fun q hq => hfac_nn q (Finset.mem_of_mem_erase hq))
      (fun q hq => hfac_le q (Finset.mem_of_mem_erase hq))
  have herase_nn : 0 ≤ ∏ q ∈ n.primeFactors.erase p, (1 - (q : ℝ) ^ (-2 * omega)) :=
    Finset.prod_nonneg fun q hq => hfac_nn q (Finset.mem_of_mem_erase hq)
  have hprod_le : ∏ q ∈ n.primeFactors, (1 - (q : ℝ) ^ (-2 * omega)) ≤
      2 * omega * Real.log n := by
    rw [← Finset.mul_prod_erase n.primeFactors _ hp]
    calc (1 - (p : ℝ) ^ (-2 * omega)) * ∏ q ∈ n.primeFactors.erase p, (1 - (q : ℝ) ^ (-2 * omega))
        ≤ (2 * omega * Real.log n) * 1 :=
          mul_le_mul hp_bound herase_le herase_nn
            (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))))
      _ = 2 * omega * Real.log n := mul_one _
  calc suzukiShiftedCoefficient omega n / omega
      = ((n : ℝ) ^ omega * ∏ q ∈ n.primeFactors, (1 - (q : ℝ) ^ (-2 * omega))) / omega := rfl
    _ ≤ ((n : ℝ) ^ omega * (2 * omega * Real.log n)) / omega :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod_le (Real.rpow_nonneg hn0 _)) homega.le
    _ = 2 * (n : ℝ) ^ omega * Real.log n := by field_simp [homega.ne']

private theorem summable_log_mul_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable fun n : ℕ => Real.log n * (n : ℝ) ^ (-p) := by
  set η := (p - 1) / 2
  have hη : 0 < η := by simp only [η]; linarith
  refine ((Real.summable_nat_rpow.mpr (by simp only [η]; linarith : -(p - η) < -1)).mul_left
    η⁻¹).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hn))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, Real.log_zero, zero_mul]
      positivity
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      calc Real.log n * (n : ℝ) ^ (-p)
          ≤ ((n : ℝ) ^ η / η) * (n : ℝ) ^ (-p) :=
            mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hn0.le hη)
              (Real.rpow_nonneg hn0.le _)
        _ = η⁻¹ * (n : ℝ) ^ (-(p - η)) := by
            rw [div_eq_mul_inv, mul_comm ((n : ℝ) ^ η) η⁻¹, mul_assoc, ← Real.rpow_add hn0]
            congr 2
            ring

/-! ## Section 2: Supercritical Correlation Decay (`β > 1/2`), Cusps, and Infinite Arithmetic Fubini -/

private theorem integrableOn_exp_neg_gap {β : ℝ} (hβ : 1 / 2 < β) :
    IntegrableOn (fun t : ℝ => Real.exp (-(β - 1 / 2) * t)) (Ioi 0) :=
  integrableOn_exp_mul_Ioi (by linarith : -(β - 1 / 2) < 0) 0

private theorem integral_exp_neg_gap {β : ℝ} (hβ : 1 / 2 < β) :
    (∫ t : ℝ in Ioi 0, Real.exp (-(β - 1 / 2) * t)) = (β - 1 / 2)⁻¹ := by
  rw [integral_exp_mul_Ioi (by linarith : -(β - 1 / 2) < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp [show β - 1 / 2 ≠ 0 by linarith]

private theorem pole_exp_decay_bound {f : ℝ → ℝ} {β K u omega : ℝ}
    (_hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) {t : ℝ} (ht : 0 < t) :
    ‖autocorr f (u + t) * suzukiCriticalPoleDensity omega t‖ ≤
      (K * suzukiCriticalPrimaryMass omega * Real.exp (-β * u)) *
        Real.exp (-(β - 1 / 2) * t) := by
  have hP := suzukiCriticalPoleDensity_bounds homega homega2 ht
  have hut : 0 ≤ u + t := by linarith
  have hK_exp : 0 ≤ K * Real.exp (-β * (u + t)) := (abs_nonneg _).trans (hdec (u + t) hut)
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left hK_exp (Real.exp_pos _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP.1]
  calc |autocorr f (u + t)| * suzukiCriticalPoleDensity omega t
      ≤ (K * Real.exp (-β * (u + t))) * (suzukiCriticalPrimaryMass omega * Real.exp (t / 2)) :=
        mul_le_mul (hdec (u + t) hut) hP.2 hP.1 hK_exp
    _ = (K * suzukiCriticalPrimaryMass omega * Real.exp (-β * u)) *
          Real.exp (-(β - 1 / 2) * t) := by
        have hexp : Real.exp (-β * (u + t)) * Real.exp (t / 2) =
            Real.exp (-β * u) * Real.exp (-(β - 1 / 2) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        linear_combination K * suzukiCriticalPrimaryMass omega * hexp

/-- Supercritical correlation decay (`β > 1/2`) makes the growing polar cusp absolutely integrable
without compact support. -/
theorem integrableOn_suzukiCriticalPoleCusp_of_exp_decay {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {β K u omega : ℝ} (hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) :
    IntegrableOn (fun t => autocorr f (u + t) * suzukiCriticalPoleDensity omega t) (Ioi 0) := by
  refine ((integrableOn_exp_neg_gap hβ).const_mul
    (K * suzukiCriticalPrimaryMass omega * Real.exp (-β * u))).mono' ?_ ?_
  · exact (((continuous_autocorr_of_memLp hf).measurable.comp
      (measurable_const.add measurable_id)).mul
        (measurable_suzukiCriticalPoleDensity omega)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact pole_exp_decay_bound hβ hu hdec homega homega2 ht

/-- Explicit `O(e^{-β u})` norm integral bound for the translated polar cusp under supercritical
correlation decay. -/
theorem integral_norm_suzukiCriticalPoleCusp_le_of_exp_decay {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {β K u omega : ℝ} (hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) :
    (∫ t in Ioi 0, ‖autocorr f (u + t) * suzukiCriticalPoleDensity omega t‖) ≤
      (K * suzukiCriticalPrimaryMass omega / (β - 1 / 2)) * Real.exp (-β * u) := by
  have hi := (integrableOn_suzukiCriticalPoleCusp_of_exp_decay hf hβ hu hdec homega homega2).norm
  have hmaj := (integrableOn_exp_neg_gap hβ).const_mul
    (K * suzukiCriticalPrimaryMass omega * Real.exp (-β * u))
  calc (∫ t in Ioi 0, ‖autocorr f (u + t) * suzukiCriticalPoleDensity omega t‖)
      ≤ ∫ t in Ioi 0, (K * suzukiCriticalPrimaryMass omega * Real.exp (-β * u)) *
          Real.exp (-(β - 1 / 2) * t) := by
        refine integral_mono_ae hi hmaj ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact pole_exp_decay_bound hβ hu hdec homega homega2 ht
    _ = (K * suzukiCriticalPrimaryMass omega / (β - 1 / 2)) * Real.exp (-β * u) := by
        rw [integral_const_mul, integral_exp_neg_gap hβ]
        ring

/-- Supercritical correlation decay makes the signed source cusp absolutely integrable without
compact support. -/
theorem integrableOn_suzukiCriticalSourceCusp_of_exp_decay {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {β K u omega : ℝ} (hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) :
    IntegrableOn (fun t => autocorr f (u + t) * suzukiCriticalSourceDensity omega t) (Ioi 0) := by
  have hB := integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp hf homega
    (by linarith : omega < 5 / 2) u
  have hP := integrableOn_suzukiCriticalPoleCusp_of_exp_decay hf hβ hu hdec homega homega2
  refine (hB.sub (hP.const_mul (2 * omega))).congr_fun ?_ measurableSet_Ioi
  intro t ht
  dsimp only [Pi.sub_apply]
  rw [suzukiCriticalSourceDensity_eq omega ht]
  ring

/-- Noncompact primary–polar decomposition of `suzukiCriticalSourceCusp` under supercritical
correlation decay. -/
theorem suzukiCriticalSourceCusp_eq_of_exp_decay {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {β K u omega : ℝ} (hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) :
    suzukiCriticalSourceCusp f omega u =
      suzukiCriticalPrimaryCusp f omega u - 2 * omega * suzukiCriticalPoleCusp f omega u := by
  have hB := integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp hf homega
    (by linarith : omega < 5 / 2) u
  have hP := integrableOn_suzukiCriticalPoleCusp_of_exp_decay hf hβ hu hdec homega homega2
  unfold suzukiCriticalSourceCusp suzukiCriticalPrimaryCusp suzukiCriticalPoleCusp
  calc (∫ t in Ioi 0, autocorr f (u + t) * suzukiCriticalSourceDensity omega t)
      = ∫ t in Ioi 0, autocorr f (u + t) * suzukiCriticalPrimaryDensity omega t -
          (2 * omega) * (autocorr f (u + t) * suzukiCriticalPoleDensity omega t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [suzukiCriticalSourceDensity_eq omega ht]
        ring
    _ = _ := by rw [integral_sub hB (hP.const_mul _), integral_const_mul]

/-- Explicit `O(e^{-β u})` `L¹` norm bound for the translated signed source cusp under supercritical
correlation decay. -/
theorem integral_norm_suzukiCriticalSourceCusp_le_of_exp_decay {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {β K u omega : ℝ} (hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) :
    (∫ t in Ioi 0, ‖autocorr f (u + t) * suzukiCriticalSourceDensity omega t‖) ≤
      K * suzukiCriticalPrimaryMass omega * (1 + 2 * omega / (β - 1 / 2)) * Real.exp (-β * u) := by
  have hK : 0 ≤ K := by
    have h0 := (abs_nonneg _).trans (hdec 0 le_rfl)
    simpa using h0
  have hB := integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp hf homega
    (by linarith : omega < 5 / 2) u
  have hP := integrableOn_suzukiCriticalPoleCusp_of_exp_decay hf hβ hu hdec homega homega2
  have hS := integrableOn_suzukiCriticalSourceCusp_of_exp_decay hf hβ hu hdec homega homega2
  have hprim_le : (∫ t in Ioi 0, ‖autocorr f (u + t) * suzukiCriticalPrimaryDensity omega t‖) ≤
      K * Real.exp (-β * u) * suzukiCriticalPrimaryMass omega := by
    calc (∫ t in Ioi 0, ‖autocorr f (u + t) * suzukiCriticalPrimaryDensity omega t‖)
        ≤ ∫ t in Ioi 0, (K * Real.exp (-β * u)) * suzukiCriticalPrimaryDensity omega t := by
          refine integral_mono_ae hB.norm
            ((integrableOn_suzukiCriticalPrimaryDensity homega (by linarith)).const_mul _) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have hd_pos := suzukiCriticalPrimaryDensity_pos homega ht
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd_pos.le]
          refine mul_le_mul_of_nonneg_right ?_ hd_pos.le
          refine (hdec (u + t) (by linarith)).trans ?_
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by nlinarith : -β * (u + t) ≤ -β * u)) hK
      _ = K * Real.exp (-β * u) * suzukiCriticalPrimaryMass omega := by
          rw [integral_const_mul, integral_suzukiCriticalPrimaryDensity homega (by linarith)]
  have hpole_le := integral_norm_suzukiCriticalPoleCusp_le_of_exp_decay hf hβ hu hdec homega homega2
  calc (∫ t in Ioi 0, ‖autocorr f (u + t) * suzukiCriticalSourceDensity omega t‖)
      ≤ ∫ t in Ioi 0, (‖autocorr f (u + t) * suzukiCriticalPrimaryDensity omega t‖ +
          (2 * omega) * ‖autocorr f (u + t) * suzukiCriticalPoleDensity omega t‖) := by
        refine integral_mono_ae hS.norm (hB.norm.add (hP.norm.const_mul (2 * omega))) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        dsimp only
        rw [suzukiCriticalSourceDensity_eq omega ht, mul_sub]
        refine (norm_sub_le _ _).trans ?_
        rw [show autocorr f (u + t) * (2 * omega * suzukiCriticalPoleDensity omega t) =
            (2 * omega) * (autocorr f (u + t) * suzukiCriticalPoleDensity omega t) by ring,
          norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ = (∫ t in Ioi 0, ‖autocorr f (u + t) * suzukiCriticalPrimaryDensity omega t‖) +
          (2 * omega) * ∫ t in Ioi 0, ‖autocorr f (u + t) * suzukiCriticalPoleDensity omega t‖ := by
        rw [integral_add hB.norm (hP.norm.const_mul _), integral_const_mul]
    _ ≤ K * Real.exp (-β * u) * suzukiCriticalPrimaryMass omega +
          (2 * omega) * ((K * suzukiCriticalPrimaryMass omega / (β - 1 / 2)) * Real.exp (-β * u)) :=
        add_le_add hprim_le (mul_le_mul_of_nonneg_left hpole_le (by positivity))
    _ = K * suzukiCriticalPrimaryMass omega * (1 + 2 * omega / (β - 1 / 2)) *
          Real.exp (-β * u) := by ring

/-- Pointwise bound on `suzukiCriticalSourceCusp f ω u` under supercritical correlation decay. -/
theorem abs_suzukiCriticalSourceCusp_le_of_exp_decay {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {β K u omega : ℝ} (hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) :
    |suzukiCriticalSourceCusp f omega u| ≤
      K * suzukiCriticalPrimaryMass omega * (1 + 2 * omega / (β - 1 / 2)) * Real.exp (-β * u) := by
  have hnorm : |suzukiCriticalSourceCusp f omega u| ≤
      ∫ t in Ioi 0, ‖autocorr f (u + t) * suzukiCriticalSourceDensity omega t‖ := by
    unfold suzukiCriticalSourceCusp
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (fun t => autocorr f (u + t) * suzukiCriticalSourceDensity omega t)
        (μ := volume.restrict (Ioi 0))
  exact hnorm.trans (integral_norm_suzukiCriticalSourceCusp_le_of_exp_decay hf hβ hu hdec homega homega2)

private theorem shifted_source_integrable_of_exp_decay {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {β K u omega : ℝ} (hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) :
    IntegrableOn (fun t => autocorr f t * suzukiCriticalSourceDensity omega (t - u)) (Ioi 0) ∧
    (∫ t in Ioi 0, ‖autocorr f t * suzukiCriticalSourceDensity omega (t - u)‖) ≤
      K * suzukiCriticalPrimaryMass omega * (1 + 2 * omega / (β - 1 / 2)) * Real.exp (-β * u) := by
  have hfull : Integrable (fun s => autocorr f (u + s) * suzukiCriticalSourceDensity omega s) := by
    have hi := (integrable_indicator_iff measurableSet_Ioi).mpr
      (integrableOn_suzukiCriticalSourceCusp_of_exp_decay hf hβ hu hdec homega homega2)
    refine hi.congr (Eventually.of_forall fun s => ?_)
    by_cases hs : 0 < s
    · rw [indicator_of_mem (show s ∈ Ioi 0 from hs)]
    · rw [indicator_of_notMem (show s ∉ Ioi 0 from hs),
        suzukiCriticalSourceDensity_eq_zero_of_nonpos (le_of_not_gt hs), mul_zero]
  have hshift : Integrable (fun t => autocorr f t * suzukiCriticalSourceDensity omega (t - u)) := by
    refine (hfull.comp_add_left (-u)).congr (Eventually.of_forall fun t => ?_)
    change autocorr f (u + (-u + t)) * suzukiCriticalSourceDensity omega (-u + t) = _
    rw [show u + (-u + t) = t by ring, show -u + t = t - u by ring]
  refine ⟨hshift.integrableOn, ?_⟩
  have hnorm_eq : (∫ t in Ioi 0, ‖autocorr f t * suzukiCriticalSourceDensity omega (t - u)‖) =
      ∫ s in Ioi 0, ‖autocorr f (u + s) * suzukiCriticalSourceDensity omega s‖ := by
    have hl : (∫ t in Ioi 0, ‖autocorr f t * suzukiCriticalSourceDensity omega (t - u)‖) =
        ∫ t, ‖autocorr f t * suzukiCriticalSourceDensity omega (t - u)‖ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have ht0 : t ≤ 0 := le_of_not_gt ht
      rw [suzukiCriticalSourceDensity_eq_zero_of_nonpos (by linarith : t - u ≤ 0), mul_zero,
        norm_zero]
    have hr : (∫ s in Ioi 0, ‖autocorr f (u + s) * suzukiCriticalSourceDensity omega s‖) =
        ∫ s, ‖autocorr f (u + s) * suzukiCriticalSourceDensity omega s‖ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro s hs
      rw [suzukiCriticalSourceDensity_eq_zero_of_nonpos (le_of_not_gt hs), mul_zero, norm_zero]
    rw [hl, hr, ← integral_add_left_eq_self
      (fun t => ‖autocorr f t * suzukiCriticalSourceDensity omega (t - u)‖) u]
    exact integral_congr_ae (Eventually.of_forall fun s => by rw [add_sub_cancel_left])
  rw [hnorm_eq]
  exact integral_norm_suzukiCriticalSourceCusp_le_of_exp_decay hf hβ hu hdec homega homega2

private theorem shifted_source_integral_eq {f : ℝ → ℝ} {omega u : ℝ} (hu : 0 ≤ u) :
    (∫ t in Ioi 0, autocorr f t * suzukiCriticalSourceDensity omega (t - u)) =
      suzukiCriticalSourceCusp f omega u := by
  have hl : (∫ t in Ioi 0, autocorr f t * suzukiCriticalSourceDensity omega (t - u)) =
      ∫ t, autocorr f t * suzukiCriticalSourceDensity omega (t - u) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have ht0 : t ≤ 0 := le_of_not_gt ht
    rw [suzukiCriticalSourceDensity_eq_zero_of_nonpos (by linarith : t - u ≤ 0), mul_zero]
  have hr : (∫ s in Ioi 0, autocorr f (u + s) * suzukiCriticalSourceDensity omega s) =
      ∫ s, autocorr f (u + s) * suzukiCriticalSourceDensity omega s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    rw [suzukiCriticalSourceDensity_eq_zero_of_nonpos (le_of_not_gt hs), mul_zero]
  rw [hl, suzukiCriticalSourceCusp, hr, ← integral_add_left_eq_self
    (fun t => autocorr f t * suzukiCriticalSourceDensity omega (t - u)) u]
  exact integral_congr_ae (Eventually.of_forall fun s => by rw [add_sub_cancel_left])

private theorem source_pairing_pointwise_tsum (f : ℝ → ℝ) (omega t : ℝ) :
    autocorr f t * (Real.exp (t / 2) * (suzukiSourceHFinite omega (Real.exp t)).re) =
      ∑' n : ℕ, if 1 ≤ n then
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          (autocorr f t * suzukiCriticalSourceDensity omega (t - Real.log n))
      else 0 := by
  have hts : (∑' n : ℕ, if 1 ≤ n then
      (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
        (autocorr f t * suzukiCriticalSourceDensity omega (t - Real.log n))
      else 0) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          (autocorr f t * suzukiCriticalSourceDensity omega (t - Real.log n)) := by
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp t⌋₊)]
    · refine Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_Icc.mp hn).1
    · intro n hn
      by_cases h1 : 1 ≤ n
      · have hgt : ⌊Real.exp t⌋₊ < n := by
          simp only [Finset.mem_Icc] at hn
          omega
        have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
        have hexp_lt : Real.exp t < n :=
          (Nat.lt_floor_add_one (Real.exp t)).trans_le
            (by exact_mod_cast Nat.succ_le_iff.mpr hgt)
        have hlog : t < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hexp_lt
        rw [if_pos h1, suzukiCriticalSourceDensity_eq_zero_of_nonpos (by linarith),
          mul_zero, mul_zero]
      · rw [if_neg h1]
  rw [hts, suzukiSourceHFinite_eq_fixedSum (Real.exp_pos t) le_rfl]
  rw [show (1 / (Real.exp t : ℂ)) = ((1 / Real.exp t : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum]
  rw [← mul_assoc (Real.exp (t / 2)), mul_one_div, ← Real.exp_sub,
    show t / 2 - t = -t / 2 by ring, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hx : (n : ℝ) / Real.exp t = Real.exp (-(t - Real.log n)) := by
    rw [neg_sub, Real.exp_sub, Real.exp_log hn0]
  have he : Real.exp (-Real.log n / 2) * Real.exp (-(t - Real.log n) / 2) =
      Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hatom : Real.exp (-t / 2) * (suzukiSourceG omega (n / Real.exp t)).re =
      Real.exp (-Real.log n / 2) * suzukiCriticalSourceDensity omega (t - Real.log n) := by
    rw [hx, suzukiCriticalSourceDensity, ← mul_assoc, he]
  linear_combination autocorr f t * suzukiShiftedCoefficient omega n * hatom

private theorem exp_neg_mul_log_nat {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    Real.exp (a * Real.log n) = (n : ℝ) ^ a := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hn0, mul_comm]

/-- **Exact Infinite Arithmetic Fubini for Supercritical-Decay `L²` Sources.**
If `|autocorr f t| ≤ K e^{-β t}` (`β > 1/2`), then for every `0 < ω < min(1/2, β - 1/2)` (and in
particular `ω ≤ 1/2` with `ω < β - 1/2`), the literal Suzuki source pairing is absolutely
integrable on `(0, ∞)` and expands into the absolutely convergent infinite series of translated
signed cusps across all `n ≥ 1`. -/
theorem suzukiCriticalSourcePairing_eq_tsum_of_exp_decay {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {β K omega : ℝ} (hβ : 1 / 2 < β)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) (homega_gap : omega < β - 1 / 2) :
    IntegrableOn (fun t => autocorr f t *
      (Real.exp (t / 2) * (suzukiSourceHFinite omega (Real.exp t)).re)) (Ioi 0) ∧
    suzukiCriticalSourcePairing f omega =
      suzukiCriticalSourceCusp f omega 0 +
      ∑' n : ℕ, if 2 ≤ n then
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n)
      else 0 := by
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hdec 0 le_rfl)
  let F : ℕ → ℝ → ℝ := fun n t => if 1 ≤ n then
    (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
      (autocorr f t * suzukiCriticalSourceDensity omega (t - Real.log n))
    else 0
  have hF_int : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := by
    intro n
    by_cases hn1 : 1 ≤ n
    · have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      have hi := (shifted_source_integrable_of_exp_decay hf hβ hlog hdec homega homega2).1
      simpa only [F, if_pos hn1] using hi.const_mul _
    · simp only [F, if_neg hn1]
      exact integrable_zero _ _ _
  set C_cusp := K * suzukiCriticalPrimaryMass omega * (1 + 2 * omega / (β - 1 / 2))
  have hM_nn : 0 ≤ suzukiCriticalPrimaryMass omega := by
    rw [← integral_suzukiCriticalPrimaryDensity homega (by linarith)]
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact (suzukiCriticalPrimaryDensity_pos homega hr).le)
  have hC_nn : 0 ≤ C_cusp := by unfold C_cusp; positivity
  set p := β + 1 / 2 - omega
  have hp1 : 1 < p := by unfold p; linarith
  have hF_sum : Summable (fun n : ℕ => ∫ t in Ioi 0, ‖F n t‖) := by
    let B : ℕ → ℝ := fun n =>
      if n = 1 then C_cusp else 2 * omega * C_cusp * (Real.log n * (n : ℝ) ^ (-p))
    have hB_sum : Summable B := by
      have hbase := (summable_log_mul_rpow_neg hp1).mul_left (2 * omega * C_cusp)
      refine hbase.congr_cofinite ?_
      filter_upwards [Filter.mem_cofinite.mpr (Set.finite_singleton 1)] with n hn
      exact (if_neg hn).symm
    refine hB_sum.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    rcases lt_trichotomy n 1 with hn0 | rfl | hn2_lt
    · have hn_z : n = 0 := by omega
      subst hn_z
      simp only [F, show ¬(1 ≤ 0) by omega, ↓reduceIte, norm_zero, integral_zero, B,
        show (0 : ℕ) ≠ 1 by omega, Nat.cast_zero, Real.log_zero, zero_mul, mul_zero, le_refl]
    · simp only [F, le_refl, ↓reduceIte, suzukiShiftedCoefficient, Nat.cast_one, Real.one_rpow,
        Nat.primeFactors_one, Finset.prod_empty, mul_one, Real.log_one, neg_zero, zero_div,
        Real.exp_zero, one_mul, sub_zero, B]
      have hb1 := (shifted_source_integrable_of_exp_decay hf hβ (u := 0) le_rfl hdec
        homega homega2).2
      simpa only [mul_zero, Real.exp_zero, mul_one, sub_zero] using hb1
    · have hn2 : 2 ≤ n := by omega
      have hn1 : 1 ≤ n := by omega
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      obtain ⟨hdiv_nn, hdiv_le⟩ := suzukiShiftedCoefficient_div_bounds hn2 homega
      have hc_nn : 0 ≤ suzukiShiftedCoefficient omega n :=
        (div_nonneg_iff.mp hdiv_nn).resolve_right (by linarith)
      have hc_le : suzukiShiftedCoefficient omega n ≤ 2 * omega * (n : ℝ) ^ omega * Real.log n := by
        have := (div_le_iff₀ homega).mp hdiv_le
        linarith
      have hcusp := (shifted_source_integrable_of_exp_decay hf hβ hlog hdec homega homega2).2
      simp only [F, if_pos hn1, B, show n ≠ 1 by omega, ↓reduceIte, norm_mul, Real.norm_eq_abs,
        integral_const_mul, abs_of_nonneg hc_nn, abs_of_pos (Real.exp_pos _)]
      have hexp_n : Real.exp (-Real.log n / 2) * Real.exp (-β * Real.log n) =
          (n : ℝ) ^ (-(1 / 2 + β)) := by
        rw [← Real.exp_add, show -Real.log n / 2 + -β * Real.log n =
            -(1 / 2 + β) * Real.log n by ring, exp_neg_mul_log_nat hn1]
      calc suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2) *
            ∫ t in Ioi 0, ‖autocorr f t * suzukiCriticalSourceDensity omega (t - Real.log n)‖
          ≤ (2 * omega * (n : ℝ) ^ omega * Real.log n) * Real.exp (-Real.log n / 2) *
              (C_cusp * Real.exp (-β * Real.log n)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hc_le (Real.exp_pos _).le) hcusp
              (integral_nonneg fun _ => norm_nonneg _) (by positivity)
        _ = 2 * omega * C_cusp * Real.log n *
              ((n : ℝ) ^ omega * (Real.exp (-Real.log n / 2) * Real.exp (-β * Real.log n))) := by
            ring
        _ = 2 * omega * C_cusp * (Real.log n * (n : ℝ) ^ (-p)) := by
            rw [hexp_n, ← Real.rpow_add hn_pos]
            unfold p
            ring_nf
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  have hpt : ∀ t : ℝ, autocorr f t * (Real.exp (t / 2) * (suzukiSourceHFinite omega (Real.exp t)).re) =
      ∑' n : ℕ, F n t := source_pairing_pointwise_tsum f omega
  have hint_tot : IntegrableOn (fun t => autocorr f t *
      (Real.exp (t / 2) * (suzukiSourceHFinite omega (Real.exp t)).re)) (Ioi 0) := by
    have hnorm_sum : HasSum (fun n => ∫ t in Ioi 0, ‖F n t‖) (∑' n, ∫ t in Ioi 0, ‖F n t‖) :=
      hF_sum.hasSum
    have htsum_int : Integrable (fun t => ∑' n, F n t) (volume.restrict (Ioi 0)) := by
      refine ⟨AEStronglyMeasurable.tsum fun n => (hF_int n).1, ?_⟩
      rw [HasFiniteIntegral]
      calc (∫⁻ t in Ioi 0, ‖∑' n, F n t‖ₑ)
          ≤ ∫⁻ t in Ioi 0, ∑' n, ‖F n t‖ₑ := by
            refine lintegral_mono fun t => ?_
            exact enorm_tsum_le_tsum_enorm
        _ = ∑' n, ∫⁻ t in Ioi 0, ‖F n t‖ₑ :=
            lintegral_tsum fun n => (hF_int n).1.enorm
        _ = ∑' n, ENNReal.ofReal (∫ t in Ioi 0, ‖F n t‖) := by
            congr 1; funext n
            rw [ofReal_integral_norm_eq_lintegral_enorm (hF_int n)]
        _ = ENNReal.ofReal (∑' n, ∫ t in Ioi 0, ‖F n t‖) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => norm_nonneg _)
              hF_sum).symm
        _ < ⊤ := ENNReal.ofReal_lt_top
    exact htsum_int.congr (Eventually.of_forall fun t => (hpt t).symm)
  refine ⟨hint_tot, ?_⟩
  rw [suzukiCriticalSourcePairing]
  simp_rw [hpt]
  rw [← hswap]
  have hterm : ∀ n : ℕ, (∫ t in Ioi 0, F n t) =
      if 1 ≤ n then
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n)
      else 0 := by
    intro n
    by_cases hn1 : 1 ≤ n
    · have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      simp only [F, if_pos hn1, integral_const_mul, shifted_source_integral_eq hlog]
    · simp only [F, if_neg hn1, integral_zero]
  simp_rw [hterm]
  have hsum_int : Summable (fun n : ℕ => if 1 ≤ n then
      (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log n) else 0) := by
    refine hF_sum.of_norm_bounded fun n => ?_
    rw [ ← hterm n]
    exact norm_integral_le_integral_norm (F n)
  rw [tsum_eq_zero_add' hsum_int, tsum_eq_zero_add' (hsum_int.comp_injective Nat.succ_injective)]
  simp only [show ¬(1 ≤ 0) by omega, ↓reduceIte, zero_add, Nat.reduceAdd, le_refl,
    suzukiShiftedCoefficient, Nat.cast_one, Real.one_rpow, Nat.primeFactors_one, Finset.prod_empty,
    mul_one, Real.log_one, neg_zero, zero_div, Real.exp_zero, one_mul]
  congr 1
  have htail_sum : Summable (fun k : ℕ =>
      (suzukiShiftedCoefficient omega (k + 2) * Real.exp (-Real.log ((k + 2 : ℕ) : ℝ) / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log ((k + 2 : ℕ) : ℝ))) := by
    simpa only [Function.comp_def, show ∀ k : ℕ, 1 ≤ k + 1 + 1 by omega, ↓reduceIte] using
      (hsum_int.comp_injective Nat.succ_injective).comp_injective Nat.succ_injective
  have hfull2 : Summable (fun n : ℕ => if 2 ≤ n then
      (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log n) else 0) := by
    refine (summable_nat_add_iff 2).mp ?_
    simpa only [show ∀ k : ℕ, 2 ≤ k + 2 by omega, ↓reduceIte] using htail_sum
  rw [tsum_eq_zero_add' hfull2, tsum_eq_zero_add' (hfull2.comp_injective Nat.succ_injective)]
  simp only [show ¬(2 ≤ 0) by omega, show ¬(2 ≤ 1) by omega, ↓reduceIte, zero_add]
  exact tsum_congr fun k => by simp only [show 1 ≤ k + 1 + 1 by omega, show 2 ≤ k + 1 + 1 by omega,
    ↓reduceIte, Nat.add_assoc]

/-! ## Section 3: Noncompact Extended Weil Normalization & Uncoupled Moving-Aperture Γ-Liminf -/

/-- Supercritical correlation decay extends `suzukiCriticalL2Weil_normalization` without compact
support. -/
theorem suzukiCriticalL2Weil_normalization_of_exp_decay {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {β K : ℝ} (hβ : 1 / 2 < β)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t)) :
    (suzukiCriticalLimitingCompensatedEnergy (fun t => autocorr f 0 - autocorr f t) : EReal) +
      ((((Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi) * autocorr f 0 +
        2 * ∫ t in Ioi 0, autocorr f t * Real.exp (t / 2) : ℝ) : EReal) =
      (sourceLevyEnergy f : EReal) +
        ((EF.gammaBracket 0 * autocorr f 0 +
          4 * ∫ t in Ioi 0, autocorr f t * Real.cosh (t / 2) : ℝ) : EReal) := by
  have hp : IntegrableOn (fun t => autocorr f t * Real.exp (t / 2)) (Ioi 0) := by
    refine ((integrableOn_exp_neg_gap hβ).const_mul K).mono'
      (((continuous_autocorr_of_memLp hf).mul (by fun_prop)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |autocorr f t| * Real.exp (t / 2)
        ≤ (K * Real.exp (-β * t)) * Real.exp (t / 2) :=
          mul_le_mul_of_nonneg_right (hdec t ht.le) (Real.exp_pos _).le
      _ = K * Real.exp (-(β - 1 / 2) * t) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hm : IntegrableOn (fun t => autocorr f t * Real.exp (-t / 2)) (Ioi 0) := by
    have hdec_half : IntegrableOn (fun t : ℝ => Real.exp (-t / 2)) (Ioi 0) := by
      refine (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0).congr_fun ?_
        measurableSet_Ioi
      intro t _; change Real.exp ((-1 / 2) * t) = Real.exp (-t / 2); congr 1; ring
    exact hdec_half.bdd_mul (continuous_autocorr_of_memLp hf).aestronglyMeasurable
      (Eventually.of_forall fun t => by
        simpa only [Real.norm_eq_abs] using abs_autocorr_le_zero_of_memLp hf t)
  have hpolar : 4 * (∫ t in Ioi 0, autocorr f t * Real.cosh (t / 2)) =
      2 * (∫ t in Ioi 0, autocorr f t * Real.exp (t / 2)) +
      2 * (∫ t in Ioi 0, autocorr f t * Real.exp (-t / 2)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hp.const_mul 2) (hm.const_mul 2)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    rw [Real.cosh_eq, neg_div]
    ring
  have hdigamma : (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re =
      (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re + 4 := by
    have hp_ne : ∀ n : ℕ, ((1 / 4 : ℝ) : ℂ) ≠ -(n : ℂ) := by
      intro n h
      have hr := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h := congrArg Complex.re (Complex.digamma_apply_add_one ((1 / 4 : ℝ) : ℂ) hp_ne)
    norm_num at h ⊢
    exact h
  have hg := gammaBracket_eq_re_digamma 0
  simp only [zero_div, Complex.ofReal_zero, zero_mul, add_zero] at hg
  rw [coe_sourceLevyEnergy_eq_suzukiCriticalEnergy hf, add_assoc, ← EReal.coe_add]
  congr 1; congr 1
  rw [hpolar, hdigamma, hg]
  ring

/-- Noncompact identification of the infinite prime–polar combination with `-2 * fullPairing (autocorr f)`. -/
theorem suzukiCriticalInfinitePrimePolar_eq_fullPairing {f : ℝ → ℝ} :
    4 * (∫ t in Ioi 0, autocorr f t * Real.cosh (t / 2)) -
      (∑' n : ℕ, if 2 ≤ n then
        (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
          autocorr f (Real.log n) else 0) =
      -2 * fullPairing (autocorr f) := by
  have hprime : (∑' n : ℕ, if 2 ≤ n then
      (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        autocorr f (Real.log n) else 0) =
      2 * ∑' n : ℕ, primeTerm (autocorr f) n := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    by_cases h2 : 2 ≤ n
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      rw [if_pos h2, primeTerm, if_pos h2, primeWeight, RHTower.exp_neg_half_log hn0]
      ring
    · rw [if_neg h2, primeTerm, if_neg h2, mul_zero]
  have hpolar : (∫ t in Ici (0 : ℝ), polarDensity t * autocorr f t) =
      2 * ∫ t in Ioi 0, autocorr f t * Real.cosh (t / 2) := by
    rw [integral_Ici_eq_integral_Ioi, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    unfold polarDensity
    ring
  rw [fullPairing, hpolar, hprime]
  ring

/-- Noncompact extended Weil energy identity under supercritical correlation decay. -/
theorem suzukiCriticalInfiniteEnergy_eq_extendedWeilEnergy_of_exp_decay {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) {β K : ℝ} (hβ : 1 / 2 < β)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t)) :
    (suzukiCriticalLimitingCompensatedEnergy (fun t => autocorr f 0 - autocorr f t) : EReal) +
      ((((Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi) * autocorr f 0 +
        2 * (∫ t in Ioi 0, autocorr f t * Real.exp (t / 2)) -
        ∑' n : ℕ, if 2 ≤ n then
          (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
            autocorr f (Real.log n) else 0 : ℝ) : EReal) =
      suzukiCriticalExtendedWeilEnergy f := by
  have h := congrArg (fun z : EReal => z +
    ((-(∑' n : ℕ, if 2 ≤ n then
      (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        autocorr f (Real.log n) else 0) : ℝ) : EReal))
    (suzukiCriticalL2Weil_normalization_of_exp_decay hf hβ hdec)
  simp only [add_assoc, ← EReal.coe_add, ← sub_eq_add_neg] at h
  have hreal : EF.gammaBracket 0 * autocorr f 0 +
      4 * (∫ t in Ioi 0, autocorr f t * Real.cosh (t / 2)) -
      (∑' n : ℕ, if 2 ≤ n then
        (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
          autocorr f (Real.log n) else 0) =
      EF.gammaBracket 0 * autocorr f 0 - 2 * fullPairing (autocorr f) := by
    linarith [suzukiCriticalInfinitePrimePolar_eq_fullPairing (f := f)]
  rw [hreal] at h
  exact h

/-- Infinite signed remainder of the Suzuki difference quotient on noncompact sources. -/
def suzukiCriticalInfiniteSignedRemainder (f : ℝ → ℝ) (omega : ℝ) : ℝ :=
  -((suzukiCriticalPrimaryMass omega - 1) / omega) * autocorr f 0 +
    2 * suzukiCriticalPoleCusp f omega 0 -
      ∑' n : ℕ, if 2 ≤ n then
        (suzukiShiftedCoefficient omega n / omega * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n)
      else 0

/-- Exact finite-shift quotient decomposition on noncompact supercritical-decay `L²` sources. -/
theorem suzukiCriticalSourcePairing_div_eq_energy_add_infiniteRemainder {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) {β K omega : ℝ} (hβ : 1 / 2 < β)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) (homega_gap : omega < β - 1 / 2) :
    (((autocorr f 0 - suzukiCriticalSourcePairing f omega) / omega : ℝ) : EReal) =
      (suzukiCriticalCompensatedEnergy (fun t => autocorr f 0 - autocorr f t) omega : EReal) +
        ((suzukiCriticalInfiniteSignedRemainder f omega : ℝ) : EReal) := by
  rw [coe_suzukiCriticalCompensatedEnergy_autocorr hf homega (by linarith), ← EReal.coe_add]
  congr 1
  have htsum := (suzukiCriticalSourcePairing_eq_tsum_of_exp_decay hf hβ hdec homega homega2
    homega_gap).2
  have hdiv : (∑' n : ℕ, if 2 ≤ n then
      (suzukiShiftedCoefficient omega n / omega * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log n) else 0) =
      (∑' n : ℕ, if 2 ≤ n then
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n) else 0) / omega := by
    rw [← tsum_div_const]
    refine tsum_congr fun n => ?_
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2, if_pos h2]; ring
    · rw [if_neg h2, if_neg h2, zero_div]
  rw [suzukiCriticalInfiniteSignedRemainder, hdiv, htsum,
    suzukiCriticalSourceCusp_eq_of_exp_decay hf hβ le_rfl hdec homega homega2]
  field_simp [ne_of_gt homega]
  ring

private theorem tendsto_autocorr_joint {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) (u : ℝ) :
    Tendsto (fun n => autocorr (f n) u) atTop (𝓝 (autocorr g u)) := by
  have h := ((continuous_autocorr_L2_source u).tendsto (hg.toLp g)).comp hfg
  rw [autocorr_congr_ae hg.coeFn_toLp u] at h
  exact h.congr fun n => autocorr_congr_ae (hf n).coeFn_toLp u

/-- Joint convergence of the growing polar cusp under uniform supercritical correlation decay. -/
theorem tendsto_suzukiCriticalPoleCusp_joint_of_exp_decay
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {β K u : ℝ}
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume)
    (hfg : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hdec : ∀ j t, 0 ≤ t → |autocorr (f j) t| ≤ K * Real.exp (-β * t)) :
    Tendsto (fun j => suzukiCriticalPoleCusp (f j) (w j) u) atTop
      (𝓝 (∫ t in Ioi 0, autocorr g (u + t) * Real.exp (t / 2))) := by
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hdec 0 0 le_rfl)
  have hM : ∀ᶠ j in atTop, suzukiCriticalPrimaryMass (w j) < 2 :=
    ((tendsto_suzukiCriticalPrimaryMass.mono_left nhdsWithin_le_nhds).comp hw).eventually
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have ho : ∀ᶠ j in atTop, w j < 1 / 2 := hw.eventually
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t => (K * 2 * Real.exp (-β * u)) * Real.exp (-(β - 1 / 2) * t))
  · exact Eventually.of_forall fun j =>
      (((continuous_autocorr_of_memLp (hf j)).measurable.comp
        (measurable_const.add measurable_id)).mul
          (measurable_suzukiCriticalPoleDensity (w j))).aestronglyMeasurable
  · filter_upwards [hw.eventually self_mem_nhdsWithin, ho, hM] with j hwj ho hM
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    refine (pole_exp_decay_bound hβ hu (hdec j) hwj ho.le ht).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM.le hK) (Real.exp_pos _).le)
      (Real.exp_pos _).le
  · exact (integrableOn_exp_neg_gap hβ).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (tendsto_autocorr_joint hf hg hfg (u + t)).mul
      ((tendsto_suzukiCriticalPoleDensity ht).comp hw)

/-- Joint convergence of the signed source cusp under uniform supercritical correlation decay. -/
theorem tendsto_suzukiCriticalSourceCusp_joint_of_exp_decay
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {β K u : ℝ}
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume)
    (hfg : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hdec : ∀ j t, 0 ≤ t → |autocorr (f j) t| ≤ K * Real.exp (-β * t)) :
    Tendsto (fun j => suzukiCriticalSourceCusp (f j) (w j) u) atTop
      (𝓝 (autocorr g u)) := by
  have hp := tendsto_suzukiCriticalPoleCusp_joint_of_exp_decay hf hg hfg hw hβ hu hdec
  have hi : Tendsto w atTop (𝓝 0) := hw.mono_right nhdsWithin_le_nhds
  have h := (tendsto_suzukiCriticalPrimaryCusp_joint_L2 hf hg hfg hw u).sub
    ((hi.const_mul 2).mul hp)
  simp only [mul_zero, zero_mul, sub_zero] at h
  apply h.congr'
  have ho : ∀ᶠ j in atTop, w j < 1 / 2 := hw.eventually
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  filter_upwards [hw.eventually self_mem_nhdsWithin, ho] with j hwj ho
  exact (suzukiCriticalSourceCusp_eq_of_exp_decay (hf j) hβ hu (hdec j) hwj ho.le).symm

private theorem coeff_tangent_at_zero {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun omega : ℝ => suzukiShiftedCoefficient omega n / omega) (𝓝[>] 0)
      (𝓝 (2 * ArithmeticFunction.vonMangoldt n)) := by
  have h0 : suzukiShiftedCoefficient 0 n = 0 := by
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
    rw [suzukiShiftedCoefficient,
      Finset.prod_eq_zero hp (by simp : 1 - (p : ℝ) ^ (-2 * (0 : ℝ)) = 0)]
    simp
  simpa only [zero_add, h0, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (hasDerivAt_suzukiShiftedCoefficient (by omega : 1 ≤ n)).tendsto_slope_zero_right

/-- Joint convergence of the infinite signed remainder under uniform supercritical correlation
decay (`β > 1/2`), using divided-coefficient domination and Tannery's theorem. -/
theorem tendsto_suzukiCriticalInfiniteSignedRemainder_joint_of_exp_decay
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {β K : ℝ}
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume)
    (hfg : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hβ : 1 / 2 < β)
    (hdec : ∀ j t, 0 ≤ t → |autocorr (f j) t| ≤ K * Real.exp (-β * t)) :
    Tendsto (fun j => suzukiCriticalInfiniteSignedRemainder (f j) (w j)) atTop
      (𝓝 (((Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi) * autocorr g 0 +
        2 * (∫ t in Ioi 0, autocorr g t * Real.exp (t / 2)) -
        ∑' n : ℕ, if 2 ≤ n then
          (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
            autocorr g (Real.log n) else 0)) := by
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hdec 0 0 le_rfl)
  have hM_sec := (tendsto_suzukiCriticalPrimaryMass_secant.neg.comp hw).mul
    (tendsto_autocorr_joint hf hg hfg 0)
  have hneg : -(Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) =
      (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi := by ring
  rw [hneg] at hM_sec
  have hp := (tendsto_suzukiCriticalPoleCusp_joint_of_exp_decay hf hg hfg hw hβ le_rfl
    hdec).const_mul 2
  simp only [zero_add] at hp
  set δ := min (1 / 2 : ℝ) ((β - 1 / 2) / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  set p := β + 1 / 2 - δ
  have hp1 : 1 < p := by
    have : δ ≤ (β - 1 / 2) / 2 := min_le_right _ _
    unfold p; linarith
  set C_dom := 4 * K * (1 + 1 / (β - 1 / 2))
  have hC_dom : 0 ≤ C_dom := by unfold C_dom; positivity
  have hB_sum : Summable (fun n : ℕ => C_dom * (Real.log n * (n : ℝ) ^ (-p))) :=
    (summable_log_mul_rpow_neg hp1).mul_left C_dom
  have hM2 : ∀ᶠ j in atTop, suzukiCriticalPrimaryMass (w j) < 2 :=
    ((tendsto_suzukiCriticalPrimaryMass.mono_left nhdsWithin_le_nhds).comp hw).eventually
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hw_δ : ∀ᶠ j in atTop, w j < δ := hw.eventually
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ))
  have hprime : Tendsto (fun j => ∑' n : ℕ, if 2 ≤ n then
      (suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp (f j) (w j) (Real.log n) else 0) atTop
      (𝓝 (∑' n : ℕ, if 2 ≤ n then
        (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
          autocorr g (Real.log n) else 0)) := by
    apply tendsto_tsum_of_dominated_convergence hB_sum
    · intro n
      by_cases hn2 : 2 ≤ n
      · simp only [if_pos hn2]
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
        exact (((coeff_tangent_at_zero hn2).comp hw).mul_const _).mul
          (tendsto_suzukiCriticalSourceCusp_joint_of_exp_decay hf hg hfg hw hβ hlog hdec)
      · simp only [if_neg hn2]
        exact tendsto_const_nhds
    · filter_upwards [hw.eventually self_mem_nhdsWithin, hw_δ, hM2] with j hwj hwj_δ hMj n
      change 0 < w j at hwj
      have hwj2 : w j ≤ 1 / 2 := hwj_δ.le.trans (min_le_left _ _)
      by_cases hn2 : 2 ≤ n
      · simp only [if_pos hn2]
        have hn1 : 1 ≤ n := by omega
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
        obtain ⟨hdiv_nn, hdiv_le⟩ := suzukiShiftedCoefficient_div_bounds hn2 hwj
        have hcusp := abs_suzukiCriticalSourceCusp_le_of_exp_decay (hf j) hβ hlog (hdec j)
          hwj hwj2
        have hcusp' : |suzukiCriticalSourceCusp (f j) (w j) (Real.log n)| ≤
            2 * K * (1 + 1 / (β - 1 / 2)) * (n : ℝ) ^ (-β) := by
          have h1 : 1 + 2 * w j / (β - 1 / 2) ≤ 1 + 1 / (β - 1 / 2) := by
            have : 2 * w j ≤ 1 := by linarith
            gcongr
          have hM_nn : 0 ≤ suzukiCriticalPrimaryMass (w j) := by
            rw [← integral_suzukiCriticalPrimaryDensity hwj (by linarith)]
            exact integral_nonneg_of_ae (by
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
              exact (suzukiCriticalPrimaryDensity_pos hwj hr).le)
          rw [← exp_neg_mul_log_nat hn1 (-β)]
          refine hcusp.trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          calc K * suzukiCriticalPrimaryMass (w j) * (1 + 2 * w j / (β - 1 / 2))
              ≤ K * 2 * (1 + 1 / (β - 1 / 2)) := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left hMj.le hK) h1 ?_ (by positivity)
                positivity
            _ = 2 * K * (1 + 1 / (β - 1 / 2)) := by ring
        have hrpow_le : (n : ℝ) ^ (w j) ≤ (n : ℝ) ^ δ :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hwj_δ.le
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hdiv_nn,
          abs_of_pos (Real.exp_pos _), show -Real.log n / 2 = (-1 / 2 : ℝ) * Real.log n by ring,
          exp_neg_mul_log_nat hn1]
        calc suzukiShiftedCoefficient (w j) n / w j * (n : ℝ) ^ (-1 / 2 : ℝ) *
              |suzukiCriticalSourceCusp (f j) (w j) (Real.log n)|
            ≤ (2 * (n : ℝ) ^ δ * Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ) *
                (2 * K * (1 + 1 / (β - 1 / 2)) * (n : ℝ) ^ (-β)) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right
                (hdiv_le.trans (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hrpow_le zero_le_two) hlog))
                (Real.rpow_nonneg hn_pos.le _)) hcusp' (abs_nonneg _) (by positivity)
          _ = C_dom * (Real.log n * ((n : ℝ) ^ δ * (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ) ^ (-β))) := by
              unfold C_dom; ring
          _ = C_dom * (Real.log n * (n : ℝ) ^ (-p)) := by
              rw [← Real.rpow_add hn_pos, ← Real.rpow_add hn_pos]
              unfold p
              ring_nf
      · simp only [if_neg hn2, norm_zero]
        rcases Nat.eq_zero_or_pos n with rfl | hn_pos
        · simp
        · exact mul_nonneg hC_dom (mul_nonneg (Real.log_nonneg (by exact_mod_cast hn_pos))
            (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  exact (hM_sec.add hp).sub hprime

/-- **Uncoupled Moving/Infinite-Aperture Γ-Liminf Under Uniform Supercritical Correlation Decay.**
If `f j → g` in `L²(ℝ)` and `w j → 0⁺` with `|autocorr (f j) t| ≤ K e^{-β t}` (`β > 1/2`), then
`suzukiCriticalExtendedWeilEnergy g ≤ liminf_j ((autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j)) / w j)`
holds unconditionally with **no compact support and no growth-rate coupling** between the apertures
and `w j`. -/
theorem suzukiCriticalExtendedWeilEnergy_le_liminf_of_exp_decay_tendsto
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {β K : ℝ}
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume)
    (hfg : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hβ : 1 / 2 < β)
    (hdec : ∀ j t, 0 ≤ t → |autocorr (f j) t| ≤ K * Real.exp (-β * t)) :
    suzukiCriticalExtendedWeilEnergy g ≤
      liminf (fun j => (((autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j)) / w j : ℝ) :
        EReal)) atTop := by
  have hg_dec : ∀ t : ℝ, 0 ≤ t → |autocorr g t| ≤ K * Real.exp (-β * t) := fun t ht =>
    le_of_tendsto (tendsto_autocorr_joint hf hg hfg t).abs
      (Eventually.of_forall fun j => hdec j t ht)
  have hprim : (suzukiCriticalLimitingCompensatedEnergy
      (fun t => autocorr g 0 - autocorr g t) : EReal) ≤
      liminf (fun j => (suzukiCriticalCompensatedEnergy
        (fun t => autocorr (f j) 0 - autocorr (f j) t) (w j) : EReal)) atTop := by
    have h := suzukiCriticalLimitingEnergy_le_liminf_of_L2_tendsto hfg hw
    have hc (j : ℕ) : autocorr ((hf j).toLp (f j)) = autocorr (f j) :=
      funext (autocorr_congr_ae (hf j).coeFn_toLp)
    have hr : autocorr (hg.toLp g) = autocorr g := funext (autocorr_congr_ae hg.coeFn_toLp)
    simp only [hc, hr] at h
    have hmono : Monotone ENNReal.toEReal := fun _ _ hab =>
      EReal.coe_ennreal_le_coe_ennreal_iff.mpr hab
    change ENNReal.toEReal (suzukiCriticalLimitingCompensatedEnergy
      (fun t => autocorr g 0 - autocorr g t)) ≤
      liminf (ENNReal.toEReal ∘ fun j => suzukiCriticalCompensatedEnergy
        (fun t => autocorr (f j) 0 - autocorr (f j) t) (w j)) atTop
    rw [← hmono.map_liminf_of_continuousAt _ continuous_coe_ennreal_ereal.continuousAt]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  set R_lim : ℝ := ((Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi) * autocorr g 0 +
    2 * (∫ t in Ioi 0, autocorr g t * Real.exp (t / 2)) -
    ∑' n : ℕ, if 2 ≤ n then
      (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        autocorr g (Real.log n) else 0
  have hc : Tendsto (fun j => ((suzukiCriticalInfiniteSignedRemainder (f j) (w j) : ℝ) : EReal))
      atTop (𝓝 (R_lim : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp
      (tendsto_suzukiCriticalInfiniteSignedRemainder_joint_of_exp_decay hf hg hfg hw hβ hdec)
  have h : (suzukiCriticalLimitingCompensatedEnergy
      (fun t => autocorr g 0 - autocorr g t) : EReal) + (R_lim : EReal) ≤
      liminf (fun j => (suzukiCriticalCompensatedEnergy
        (fun t => autocorr (f j) 0 - autocorr (f j) t) (w j) : EReal) +
          ((suzukiCriticalInfiniteSignedRemainder (f j) (w j) : ℝ) : EReal)) atTop := by
    calc (suzukiCriticalLimitingCompensatedEnergy
          (fun t => autocorr g 0 - autocorr g t) : EReal) + (R_lim : EReal)
        ≤ liminf (fun j => (suzukiCriticalCompensatedEnergy
            (fun t => autocorr (f j) 0 - autocorr (f j) t) (w j) : EReal)) atTop +
          liminf (fun j => ((suzukiCriticalInfiniteSignedRemainder (f j) (w j) : ℝ) : EReal))
            atTop := by
          rw [hc.liminf_eq]
          exact add_le_add hprim le_rfl
      _ ≤ _ := EReal.le_liminf_add
  rw [suzukiCriticalInfiniteEnergy_eq_extendedWeilEnergy_of_exp_decay hg hβ hg_dec] at h
  refine h.trans_eq ?_
  apply Filter.liminf_congr
  have ho : ∀ᶠ j in atTop, w j < min (1 / 2) (β - 1 / 2) := hw.eventually
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min (by norm_num) (by linarith))))
  filter_upwards [hw.eventually self_mem_nhdsWithin, ho] with j hwj ho
  exact (suzukiCriticalSourcePairing_div_eq_energy_add_infiniteRemainder (hf j) hβ (hdec j) hwj
    (ho.le.trans (min_le_left _ _)) (lt_of_lt_of_le ho (min_le_right _ _))).symm

/-- **Uncoupled Moving/Infinite-Aperture Positive-Deficit Inheritance.** -/
theorem eventually_suzukiCriticalDeficit_of_exp_decay_tendsto
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w : ℕ → ℝ} {β K c δ : ℝ}
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume)
    (hfg : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hβ : 1 / 2 < β)
    (hdec : ∀ j t, 0 ≤ t → |autocorr (f j) t| ≤ K * Real.exp (-β * t))
    (hweil : ((c : ℝ) : EReal) ≤ suzukiCriticalExtendedWeilEnergy g)
    (hδ : 0 < δ) :
    ∀ᶠ j in atTop, w j * (c - δ) <
      autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j) :=
  eventually_suzukiCriticalDeficit_of_le_liminf hδ hw
    (hweil.trans (suzukiCriticalExtendedWeilEnergy_le_liminf_of_exp_decay_tendsto hf hg hfg hw
      hβ hdec))

/-- **Extended Complete First Variation on Noncompact `L²` Sources with Supercritical Correlation
Decay.**
Every real `L²` source `f` satisfying `|autocorr f t| ≤ K e^{-β t}` (`β > 1/2`) has exact extended
Weil first variation `suzukiCriticalExtendedWeilEnergy f` (retaining `⊤`) as `ω → 0⁺`, with no
compact-support assumption. -/
theorem tendsto_suzukiCriticalSourcePairing_extended_firstVariation_of_exp_decay
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) {β K : ℝ} (hβ : 1 / 2 < β)
    (hdec : ∀ t : ℝ, 0 ≤ t → |autocorr f t| ≤ K * Real.exp (-β * t)) :
    Tendsto (fun omega : ℝ =>
      (((autocorr f 0 - suzukiCriticalSourcePairing f omega) / omega : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 (suzukiCriticalExtendedWeilEnergy f)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro w hw
  refine ⟨id, ?_⟩
  simp only [Function.comp_id]
  have hprim := (tendsto_suzukiCriticalCompensatedEnergy_autocorr hf).comp hw
  have hprimE := continuous_coe_ennreal_ereal.continuousAt.tendsto.comp hprim
  have hrem := tendsto_suzukiCriticalInfiniteSignedRemainder_joint_of_exp_decay
    (f := fun _ => f) (g := f) (fun _ => hf) hf tendsto_const_nhds hw hβ (fun _ => hdec)
  have hremE := continuous_coe_real_ereal.continuousAt.tendsto.comp hrem
  have hsum := (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _))).tendsto.comp (hprimE.prodMk_nhds hremE)
  change Tendsto _ atTop (𝓝 ((suzukiCriticalLimitingCompensatedEnergy
    (fun t => autocorr f 0 - autocorr f t) : EReal) + _)) at hsum
  rw [suzukiCriticalInfiniteEnergy_eq_extendedWeilEnergy_of_exp_decay hf hβ hdec] at hsum
  refine hsum.congr' ?_
  have ho : ∀ᶠ j in atTop, w j < min (1 / 2) (β - 1 / 2) := hw.eventually
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min (by norm_num) (by linarith))))
  filter_upwards [hw.eventually self_mem_nhdsWithin, ho] with j hwj ho
  exact (suzukiCriticalSourcePairing_div_eq_energy_add_infiniteRemainder hf hβ hdec hwj
    (ho.le.trans (min_le_left _ _)) (lt_of_lt_of_le ho (min_le_right _ _))).symm

/-! ## Section 4: Coupled General Moving Apertures Without Correlation Decay on Approximants -/

private theorem sq_le_sixteen_exp_half {A : ℝ} (hA : 0 ≤ A) :
    A ^ 2 ≤ 16 * Real.exp (A / 2) := by
  have h1 : A / 4 ≤ Real.exp (A / 4) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (A / 4))
  have hsq : (A / 4) ^ 2 ≤ (Real.exp (A / 4)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have hexp : (Real.exp (A / 4)) ^ 2 = Real.exp (A / 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [hexp] at hsq
  linarith

private theorem pole_cusp_sub_le_moving_cutoff {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hfc : HasCompactSupport f)
    {A β K u omega : ℝ} (hA : 0 < A) (hcut : ∀ t, A ≤ t → autocorr f t = 0)
    (hβ : 1 / 2 < β) (hu : 0 ≤ u)
    (hg_dec : ∀ t : ℝ, 0 ≤ t → |autocorr g t| ≤ K * Real.exp (-β * t))
    (homega : 0 < omega) (homega2 : omega ≤ 1 / 2) :
    |suzukiCriticalPoleCusp f omega u - suzukiCriticalPoleCusp g omega u| ≤
      A * suzukiCriticalPrimaryMass omega * Real.exp (A / 2) *
        ((‖hf.toLp f‖ + ‖hg.toLp g‖) * ‖hf.toLp f - hg.toLp g‖) +
      (K * suzukiCriticalPrimaryMass omega / (β - 1 / 2)) *
        Real.exp (-β * u) * Real.exp (-(β - 1 / 2) * A) := by
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hg_dec 0 le_rfl)
  have hM : 0 ≤ suzukiCriticalPrimaryMass omega := by
    rw [← integral_suzukiCriticalPrimaryDensity homega (by linarith)]
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact (suzukiCriticalPrimaryDensity_pos homega hr).le)
  set E := (‖hf.toLp f‖ + ‖hg.toLp g‖) * ‖hf.toLp f - hg.toLp g‖
  have hcorr_sub : ∀ t : ℝ, |autocorr f t - autocorr g t| ≤ E := fun t => by
    have h := autocorr_sub_le_L2_norms (hf.toLp f) (hg.toLp g) t
    rwa [autocorr_congr_ae hf.coeFn_toLp t, autocorr_congr_ae hg.coeFn_toLp t] at h
  have hif := (integrable_suzukiCriticalPoleCusp_integrand_of_memLp hf hfc hu homega
    homega2).integrableOn (s := Ioi 0)
  have hig := integrableOn_suzukiCriticalPoleCusp_of_exp_decay hg hβ hu hg_dec homega homega2
  have hisub : IntegrableOn (fun t => (autocorr f (u + t) - autocorr g (u + t)) *
      suzukiCriticalPoleDensity omega t) (Ioi 0) := by
    refine (hif.sub hig).congr_fun ?_ measurableSet_Ioi
    intro t _; dsimp only [Pi.sub_apply]; ring
  have hdiff_eq : suzukiCriticalPoleCusp f omega u - suzukiCriticalPoleCusp g omega u =
      ∫ t in Ioi 0, (autocorr f (u + t) - autocorr g (u + t)) *
        suzukiCriticalPoleDensity omega t := by
    unfold suzukiCriticalPoleCusp
    rw [← integral_sub hif hig]
    exact integral_congr_ae (Eventually.of_forall fun t => (sub_mul _ _ _).symm)
  have hunion : Ioc (0 : ℝ) A ∪ Ioi A = Ioi 0 := Ioc_union_Ioi_eq_Ioi hA.le
  have hdisj : Disjoint (Ioc (0 : ℝ) A) (Ioi A) := Ioc_disjoint_Ioi_same
  rw [hdiff_eq, ← hunion, setIntegral_union hdisj measurableSet_Ioi
    (hisub.mono_set Ioc_subset_Ioi_self) (hisub.mono_set (Ioi_subset_Ioi hA.le))]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have hnorm1 : |∫ t in Ioc 0 A, (autocorr f (u + t) - autocorr g (u + t)) *
        suzukiCriticalPoleDensity omega t| ≤
        ∫ t in Ioc 0 A, E * (suzukiCriticalPrimaryMass omega * Real.exp (A / 2)) := by
      refine (Real.norm_eq_abs _ ▸ norm_integral_le_integral_norm _).trans ?_
      refine setIntegral_mono_on (hisub.mono_set Ioc_subset_Ioi_self).norm
        (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc ?_
      intro t ht
      have hP := suzukiCriticalPoleDensity_bounds homega homega2 ht.1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP.1]
      exact mul_le_mul (hcorr_sub (u + t))
        (hP.2.trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith [ht.2])) hM)) hP.1 (abs_nonneg _)
    calc |∫ t in Ioc 0 A, (autocorr f (u + t) - autocorr g (u + t)) *
          suzukiCriticalPoleDensity omega t|
        ≤ ∫ _t in Ioc 0 A, E * (suzukiCriticalPrimaryMass omega * Real.exp (A / 2)) := hnorm1
      _ = A * suzukiCriticalPrimaryMass omega * Real.exp (A / 2) * E := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hA.le, smul_eq_mul]
          ring
  · have htail_eq : (∫ t in Ioi A, (autocorr f (u + t) - autocorr g (u + t)) *
        suzukiCriticalPoleDensity omega t) =
        -(∫ t in Ioi A, autocorr g (u + t) * suzukiCriticalPoleDensity omega t) := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      change A < t at ht
      rw [hcut (u + t) (by linarith), zero_sub, neg_mul]
    rw [htail_eq, abs_neg]
    have hnorm2 : |∫ t in Ioi A, autocorr g (u + t) * suzukiCriticalPoleDensity omega t| ≤
        ∫ t in Ioi A, (K * suzukiCriticalPrimaryMass omega * Real.exp (-β * u)) *
          Real.exp (-(β - 1 / 2) * t) := by
      refine (Real.norm_eq_abs _ ▸ norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_ae (hig.mono_set (Ioi_subset_Ioi hA.le)).norm
        ((integrableOn_exp_mul_Ioi (by linarith : -(β - 1 / 2) < 0) A).const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact pole_exp_decay_bound hβ hu hg_dec homega homega2 (hA.trans ht)
    calc |∫ t in Ioi A, autocorr g (u + t) * suzukiCriticalPoleDensity omega t|
        ≤ ∫ t in Ioi A, (K * suzukiCriticalPrimaryMass omega * Real.exp (-β * u)) *
            Real.exp (-(β - 1 / 2) * t) := hnorm2
      _ = (K * suzukiCriticalPrimaryMass omega / (β - 1 / 2)) *
            Real.exp (-β * u) * Real.exp (-(β - 1 / 2) * A) := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(β - 1 / 2) < 0) A]
          field_simp [show β - 1 / 2 ≠ 0 by linarith]

/-- **Coupled General Moving-Aperture Γ-Liminf Without Correlation Decay on Approximants.**
Let `f j` be arbitrary compact `L²` approximants with correlation cutoffs `A j → ∞` (with no
correlation decay assumed on `f j`) converging in `L²(ℝ)` to a supercritical-decay target `g`
(`|autocorr g t| ≤ K e^{-β t}`, `β > 1/2`) along `w j → 0⁺`. Whenever the moving cutoff satisfies
`e^{2 A_j} ‖f_j - g‖₂ → 0`, the extended Weil energy obeys
`suzukiCriticalExtendedWeilEnergy g ≤ liminf_j ((autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j)) / w j)`. -/
theorem suzukiCriticalExtendedWeilEnergy_le_liminf_of_coupled_moving_aperture
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w A : ℕ → ℝ} {β K : ℝ}
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume)
    (hfc : ∀ j, HasCompactSupport (f j))
    (hA_pos : ∀ j, 0 < A j) (hA_top : Tendsto A atTop atTop)
    (hcut : ∀ j t, A j ≤ t → autocorr (f j) t = 0)
    (hfg : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hβ : 1 / 2 < β)
    (hg_dec : ∀ t : ℝ, 0 ≤ t → |autocorr g t| ≤ K * Real.exp (-β * t))
    (hrate : Tendsto (fun j => Real.exp (2 * A j) * ‖(hf j).toLp (f j) - hg.toLp g‖)
      atTop (𝓝 0)) :
    suzukiCriticalExtendedWeilEnergy g ≤
      liminf (fun j => (((autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j)) / w j : ℝ) :
        EReal)) atTop := by
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hg_dec 0 le_rfl)
  let q (j : ℕ) : Velocity := (hf j).toLp (f j)
  let r : Velocity := hg.toLp g
  let E (j : ℕ) : ℝ := (‖q j‖ + ‖r‖) * ‖q j - r‖
  have hrate_E : Tendsto (fun j => Real.exp (2 * A j) * E j) atTop (𝓝 0) := by
    have hnorm_sum : Tendsto (fun j => ‖q j‖ + ‖r‖) atTop (𝓝 (‖r‖ + ‖r‖)) :=
      hfg.norm.add_const ‖r‖
    have hprod := hnorm_sum.mul hrate
    rw [mul_zero] at hprod
    exact hprod.congr fun j => by unfold E; ring
  -- 1. Convergence of the Gamma mass secant and growing pole cusp of `f j`:
  have hM_sec := (tendsto_suzukiCriticalPrimaryMass_secant.neg.comp hw).mul
    (tendsto_autocorr_joint hf hg hfg 0)
  have hneg : -(Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) =
      (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi := by ring
  rw [hneg] at hM_sec
  have hp_g := tendsto_suzukiCriticalPoleCusp_joint_of_exp_decay
    (f := fun _ => g) (g := g) (fun _ => hg) hg tendsto_const_nhds hw hβ le_rfl (fun _ => hg_dec)
  simp only [zero_add] at hp_g
  have hp_diff : Tendsto (fun j => suzukiCriticalPoleCusp (f j) (w j) 0 -
      suzukiCriticalPoleCusp g (w j) 0) atTop (𝓝 0) := by
    have hM2 : ∀ᶠ j in atTop, suzukiCriticalPrimaryMass (w j) < 2 :=
      ((tendsto_suzukiCriticalPrimaryMass.mono_left nhdsWithin_le_nhds).comp hw).eventually
        (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
    have ho : ∀ᶠ j in atTop, w j < 1 / 2 := hw.eventually
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
    have htail0 : Tendsto (fun j => (2 * K / (β - 1 / 2)) * Real.exp (-(β - 1 / 2) * A j))
        atTop (𝓝 0) := by
      have hexp0 : Tendsto (fun j => Real.exp (-(β - 1 / 2) * A j)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (Tendsto.neg_const_mul_atTop (by linarith : -(β - 1 / 2) < 0) hA_top)
      simpa only [mul_zero] using hexp0.const_mul (2 * K / (β - 1 / 2))
    have hub : Tendsto (fun j => 2 * (Real.exp (2 * A j) * E j) +
        (2 * K / (β - 1 / 2)) * Real.exp (-(β - 1 / 2) * A j)) atTop (𝓝 0) := by
      simpa using (hrate_E.const_mul 2).add htail0
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [hw.eventually self_mem_nhdsWithin, ho, hM2] with j hwj ho hMj
    rw [Real.norm_eq_abs]
    have hb := pole_cusp_sub_le_moving_cutoff (hf j) hg (hfc j) (hA_pos j) (hcut j) hβ le_rfl
      hg_dec hwj ho.le
    simp only [mul_zero, Real.exp_zero, mul_one] at hb
    refine hb.trans (add_le_add ?_ ?_)
    · have hA_exp : A j * Real.exp (A j / 2) ≤ Real.exp (2 * A j) := by
        have h1 : A j ≤ Real.exp (A j) :=
          (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (A j))
        calc A j * Real.exp (A j / 2)
            ≤ Real.exp (A j) * Real.exp (A j / 2) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = Real.exp (3 * A j / 2) := by rw [← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (2 * A j) := Real.exp_le_exp.mpr (by linarith [hA_pos j])
      have hE_nn : 0 ≤ E j := by unfold E; positivity
      calc A j * suzukiCriticalPrimaryMass (w j) * Real.exp (A j / 2) * E j
          ≤ 2 * (A j * Real.exp (A j / 2)) * E j := by
            have := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hMj.le (hA_pos j).le) (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right (by linarith) hE_nn
        _ ≤ 2 * (Real.exp (2 * A j) * E j) := by
            nlinarith [mul_le_mul_of_nonneg_right hA_exp hE_nn]
    · gcongr
      linarith [hMj.le]
  have hp_f : Tendsto (fun j => 2 * suzukiCriticalPoleCusp (f j) (w j) 0) atTop
      (𝓝 (2 * ∫ t in Ioi 0, autocorr g t * Real.exp (t / 2))) := by
    have := (hp_diff.add hp_g).const_mul 2
    simpa only [sub_add_cancel, zero_add] using this
  -- 2. Convergence of the truncated `g`-sum via Tannery:
  set δ := min (1 / 2 : ℝ) ((β - 1 / 2) / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  set p := β + 1 / 2 - δ
  have hp1 : 1 < p := by
    have : δ ≤ (β - 1 / 2) / 2 := min_le_right _ _
    unfold p; linarith
  set C_dom := 4 * K * (1 + 1 / (β - 1 / 2))
  have hC_dom : 0 ≤ C_dom := by unfold C_dom; positivity
  have hB_sum : Summable (fun n : ℕ => C_dom * (Real.log n * (n : ℝ) ^ (-p))) :=
    (summable_log_mul_rpow_neg hp1).mul_left C_dom
  have hM2 : ∀ᶠ j in atTop, suzukiCriticalPrimaryMass (w j) < 2 :=
    ((tendsto_suzukiCriticalPrimaryMass.mono_left nhdsWithin_le_nhds).comp hw).eventually
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hw_δ : ∀ᶠ j in atTop, w j < δ := hw.eventually
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ))
  have hg_trunc_tendsto : Tendsto (fun j => ∑ n ∈ Finset.Icc 2 ⌊Real.exp (A j)⌋₊,
      (suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp g (w j) (Real.log n)) atTop
      (𝓝 (∑' n : ℕ, if 2 ≤ n then
        (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
          autocorr g (Real.log n) else 0)) := by
    have hts_eq : ∀ j, (∑ n ∈ Finset.Icc 2 ⌊Real.exp (A j)⌋₊,
        (suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp g (w j) (Real.log n)) =
        ∑' n : ℕ, if 2 ≤ n ∧ n ≤ ⌊Real.exp (A j)⌋₊ then
          (suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
            suzukiCriticalSourceCusp g (w j) (Real.log n) else 0 := by
      intro j
      rw [tsum_eq_sum (s := Finset.Icc 2 ⌊Real.exp (A j)⌋₊)]
      · refine Finset.sum_congr rfl fun n hn => (if_pos (Finset.mem_Icc.mp hn)).symm
      · intro n hn
        rw [if_neg]
        simpa only [Finset.mem_Icc] using hn
    simp_rw [hts_eq]
    apply tendsto_tsum_of_dominated_convergence hB_sum
    · intro n
      by_cases hn2 : 2 ≤ n
      · have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
        have hlim_n := (((coeff_tangent_at_zero hn2).comp hw).mul_const
          (Real.exp (-Real.log n / 2))).mul
          (tendsto_suzukiCriticalSourceCusp_joint_of_exp_decay
            (f := fun _ => g) (g := g) (fun _ => hg) hg tendsto_const_nhds hw hβ hlog
            (fun _ => hg_dec))
        simp only [if_pos hn2]
        refine hlim_n.congr' ?_
        have hAj_gt : ∀ᶠ j in atTop, Real.log n + 1 < A j := hA_top.eventually_gt_atTop _
        filter_upwards [hAj_gt] with j hAj
        have hn_le : n ≤ ⌊Real.exp (A j)⌋₊ := by
          apply Nat.le_floor
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
          rw [← Real.exp_log hn0]
          exact Real.exp_le_exp.mpr (by linarith)
        rw [if_pos ⟨hn2, hn_le⟩]
      · simp only [show ∀ j, ¬(2 ≤ n ∧ n ≤ ⌊Real.exp (A j)⌋₊) from fun _ h => hn2 h.1,
          if_neg hn2, ↓reduceIte]
        exact tendsto_const_nhds
    · filter_upwards [hw.eventually self_mem_nhdsWithin, hw_δ, hM2] with j hwj hwj_δ hMj n
      change 0 < w j at hwj
      have hwj2 : w j ≤ 1 / 2 := hwj_δ.le.trans (min_le_left _ _)
      by_cases hcond : 2 ≤ n ∧ n ≤ ⌊Real.exp (A j)⌋₊
      · rw [if_pos hcond]
        have hn2 := hcond.1
        have hn1 : 1 ≤ n := by omega
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
        obtain ⟨hdiv_nn, hdiv_le⟩ := suzukiShiftedCoefficient_div_bounds hn2 hwj
        have hcusp := abs_suzukiCriticalSourceCusp_le_of_exp_decay hg hβ hlog hg_dec hwj hwj2
        have h1 : 1 + 2 * w j / (β - 1 / 2) ≤ 1 + 1 / (β - 1 / 2) := by
          have : 2 * w j ≤ 1 := by linarith
          gcongr
        have hM_nn : 0 ≤ suzukiCriticalPrimaryMass (w j) := by
          rw [← integral_suzukiCriticalPrimaryDensity hwj (by linarith)]
          exact integral_nonneg_of_ae (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
            exact (suzukiCriticalPrimaryDensity_pos hwj hr).le)
        have hcusp' : |suzukiCriticalSourceCusp g (w j) (Real.log n)| ≤
            2 * K * (1 + 1 / (β - 1 / 2)) * (n : ℝ) ^ (-β) := by
          rw [← exp_neg_mul_log_nat hn1 (-β)]
          refine hcusp.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
          calc K * suzukiCriticalPrimaryMass (w j) * (1 + 2 * w j / (β - 1 / 2))
              ≤ K * 2 * (1 + 1 / (β - 1 / 2)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hMj.le hK) h1 (by positivity) (by positivity)
            _ = 2 * K * (1 + 1 / (β - 1 / 2)) := by ring
        have hrpow_le : (n : ℝ) ^ (w j) ≤ (n : ℝ) ^ δ :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hwj_δ.le
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hdiv_nn,
          abs_of_pos (Real.exp_pos _), show -Real.log n / 2 = (-1 / 2 : ℝ) * Real.log n by ring,
          exp_neg_mul_log_nat hn1]
        calc suzukiShiftedCoefficient (w j) n / w j * (n : ℝ) ^ (-1 / 2 : ℝ) *
              |suzukiCriticalSourceCusp g (w j) (Real.log n)|
            ≤ (2 * (n : ℝ) ^ δ * Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ) *
                (2 * K * (1 + 1 / (β - 1 / 2)) * (n : ℝ) ^ (-β)) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right
                (hdiv_le.trans (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hrpow_le zero_le_two) hlog))
                (Real.rpow_nonneg hn_pos.le _)) hcusp' (abs_nonneg _) (by positivity)
          _ = C_dom * (Real.log n * (n : ℝ) ^ (-p)) := by
              have hrp : (n : ℝ) ^ δ * (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ) ^ (-β) =
                  (n : ℝ) ^ (-p) := by
                rw [← Real.rpow_add hn_pos, ← Real.rpow_add hn_pos]
                unfold p; ring_nf
              unfold C_dom
              linear_combination 4 * K * (1 + 1 / (β - 1 / 2)) * Real.log n * hrp
      · rw [if_neg hcond, norm_zero]
        rcases Nat.eq_zero_or_pos n with rfl | hn_pos
        · simp
        · exact mul_nonneg hC_dom (mul_nonneg (Real.log_nonneg (by exact_mod_cast hn_pos))
            (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  -- 3. Perturbation bound between the `f j` finite sum and the `g` finite sum on `Icc 2 ⌊e^{A j}⌋₊`:
  have hsum_diff : Tendsto (fun j =>
      (∑ n ∈ Finset.Icc 2 ⌊Real.exp (A j)⌋₊,
        (suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp (f j) (w j) (Real.log n)) -
      (∑ n ∈ Finset.Icc 2 ⌊Real.exp (A j)⌋₊,
        (suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp g (w j) (Real.log n))) atTop (𝓝 0) := by
    have htail_sum : Summable (fun n : ℕ =>
        (8 * K / (β - 1 / 2)) * (Real.log n * (n : ℝ) ^ (-p))) :=
      (summable_log_mul_rpow_neg hp1).mul_left _
    have hw0 : Tendsto w atTop (𝓝 0) := hw.mono_right nhdsWithin_le_nhds
    have hub : Tendsto (fun j => 132 * (Real.exp (2 * A j) * E j) +
        w j * (∑' n : ℕ, (8 * K / (β - 1 / 2)) * (Real.log n * (n : ℝ) ^ (-p)))) atTop (𝓝 0) := by
      simpa using (hrate_E.const_mul 132).add (hw0.mul_const _)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [hw.eventually self_mem_nhdsWithin, hw_δ, hM2] with j hwj hwj_δ hMj
    change 0 < w j at hwj
    have hwj2 : w j ≤ 1 / 2 := hwj_δ.le.trans (min_le_left _ _)
    have hAj0 : 0 ≤ A j := (hA_pos j).le
    have hE_nn : 0 ≤ E j := by unfold E; positivity
    rw [Real.norm_eq_abs, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    set S_j := Finset.Icc 2 ⌊Real.exp (A j)⌋₊
    have hterm_le : ∀ n ∈ S_j,
        |(suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
            suzukiCriticalSourceCusp (f j) (w j) (Real.log n) -
          (suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
            suzukiCriticalSourceCusp g (w j) (Real.log n)| ≤
          (4 * A j + 8 * A j ^ 2 * Real.exp (A j / 2)) * E j +
            w j * ((8 * K / (β - 1 / 2)) * (Real.log n * (n : ℝ) ^ (-p))) := by
      intro n hn
      have hn2 := (Finset.mem_Icc.mp hn).1
      have hn_fl := (Finset.mem_Icc.mp hn).2
      have hn1 : 1 ≤ n := by omega
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      have hn_exp : (n : ℝ) ≤ Real.exp (A j) :=
        Nat.le_floor_iff (Real.exp_pos _).le |>.mp hn_fl
      have hlog_le_A : Real.log n ≤ A j := by
        simpa [Real.log_exp] using Real.log_le_log hn_pos hn_exp
      obtain ⟨hdiv_nn, hdiv_le⟩ := suzukiShiftedCoefficient_div_bounds hn2 hwj
      have hα_nn : 0 ≤ suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2) :=
        mul_nonneg hdiv_nn (Real.exp_pos _).le
      have hα_A : suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2) ≤
          2 * A j := by
        rw [show -Real.log n / 2 = (-1 / 2 : ℝ) * Real.log n by ring, exp_neg_mul_log_nat hn1]
        have hrp_le1 : (n : ℝ) ^ (w j) * (n : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by
          rw [← Real.rpow_add hn_pos]
          exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1)
            (by linarith : w j + (-1 / 2 : ℝ) ≤ 0)).trans_eq (Real.rpow_zero _)
        calc suzukiShiftedCoefficient (w j) n / w j * (n : ℝ) ^ (-1 / 2 : ℝ)
            ≤ (2 * (n : ℝ) ^ (w j) * Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_right hdiv_le (Real.rpow_nonneg hn_pos.le _)
          _ = 2 * Real.log n * ((n : ℝ) ^ (w j) * (n : ℝ) ^ (-1 / 2 : ℝ)) := by ring
          _ ≤ 2 * Real.log n * 1 := mul_le_mul_of_nonneg_left hrp_le1 (by positivity)
          _ ≤ 2 * A j := by linarith
      have hα_δ : suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2) ≤
          2 * Real.log n * (n : ℝ) ^ (δ - 1 / 2) := by
        rw [show -Real.log n / 2 = (-1 / 2 : ℝ) * Real.log n by ring, exp_neg_mul_log_nat hn1]
        have hrpow_le : (n : ℝ) ^ (w j) ≤ (n : ℝ) ^ δ :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hwj_δ.le
        calc suzukiShiftedCoefficient (w j) n / w j * (n : ℝ) ^ (-1 / 2 : ℝ)
            ≤ (2 * (n : ℝ) ^ δ * Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_right
                (hdiv_le.trans (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hrpow_le zero_le_two) hlog))
                (Real.rpow_nonneg hn_pos.le _)
          _ = 2 * Real.log n * (n : ℝ) ^ (δ - 1 / 2) := by
              rw [show (2 * (n : ℝ) ^ δ * Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ) =
                  2 * Real.log n * ((n : ℝ) ^ δ * (n : ℝ) ^ (-1 / 2 : ℝ)) by ring,
                ← Real.rpow_add hn_pos]
              ring_nf
      rw [← mul_sub, abs_mul, abs_of_nonneg hα_nn,
        suzukiCriticalSourceCusp_eq_of_memLp (hf j) (hfc j) hlog hwj hwj2,
        suzukiCriticalSourceCusp_eq_of_exp_decay hg hβ hlog hg_dec hwj hwj2]
      have hsplit_c : suzukiCriticalPrimaryCusp (f j) (w j) (Real.log n) -
            2 * w j * suzukiCriticalPoleCusp (f j) (w j) (Real.log n) -
          (suzukiCriticalPrimaryCusp g (w j) (Real.log n) -
            2 * w j * suzukiCriticalPoleCusp g (w j) (Real.log n)) =
          (suzukiCriticalPrimaryCusp (f j) (w j) (Real.log n) -
            suzukiCriticalPrimaryCusp g (w j) (Real.log n)) -
          2 * w j * (suzukiCriticalPoleCusp (f j) (w j) (Real.log n) -
            suzukiCriticalPoleCusp g (w j) (Real.log n)) := by ring
      rw [hsplit_c]
      have hprim_sub : |suzukiCriticalPrimaryCusp (f j) (w j) (Real.log n) -
          suzukiCriticalPrimaryCusp g (w j) (Real.log n)| ≤ 2 * E j := by
        have h := abs_suzukiCriticalPrimaryCusp_sub_le_L2_norms (q j) r hwj (by linarith)
          (Real.log n)
        rw [suzukiCriticalPrimaryCusp_congr_ae (hf j).coeFn_toLp,
          suzukiCriticalPrimaryCusp_congr_ae hg.coeFn_toLp] at h
        exact h.trans (mul_le_mul_of_nonneg_right hMj.le hE_nn)
      have hpole_sub := pole_cusp_sub_le_moving_cutoff (hf j) hg (hfc j) (hA_pos j) (hcut j)
        hβ hlog hg_dec hwj hwj2
      have hexp_A_le1 : Real.exp (-(β - 1 / 2) * A j) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      have hM_nn : 0 ≤ suzukiCriticalPrimaryMass (w j) := by
        rw [← integral_suzukiCriticalPrimaryDensity hwj (by linarith)]
        exact integral_nonneg_of_ae (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          exact (suzukiCriticalPrimaryDensity_pos hwj hs).le)
      have hpole_sub' : |suzukiCriticalPoleCusp (f j) (w j) (Real.log n) -
          suzukiCriticalPoleCusp g (w j) (Real.log n)| ≤
          2 * A j * Real.exp (A j / 2) * E j +
            (2 * K / (β - 1 / 2)) * (n : ℝ) ^ (-β) := by
        rw [← exp_neg_mul_log_nat hn1 (-β)]
        refine hpole_sub.trans (add_le_add ?_ ?_)
        · have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hMj.le hAj0) (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right (by linarith) hE_nn
        · calc (K * suzukiCriticalPrimaryMass (w j) / (β - 1 / 2)) *
                Real.exp (-β * Real.log n) * Real.exp (-(β - 1 / 2) * A j)
              ≤ (K * 2 / (β - 1 / 2)) * Real.exp (-β * Real.log n) * 1 := by
                refine mul_le_mul (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
                  hexp_A_le1 (Real.exp_pos _).le (by positivity)
                gcongr
                linarith [hMj.le]
            _ = (2 * K / (β - 1 / 2)) * Real.exp (-β * Real.log n) := by ring
      have h2w_le1 : 2 * w j ≤ 1 := by linarith
      set α := suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)
      have htri : α * |(suzukiCriticalPrimaryCusp (f j) (w j) (Real.log n) -
            suzukiCriticalPrimaryCusp g (w j) (Real.log n)) -
          2 * w j * (suzukiCriticalPoleCusp (f j) (w j) (Real.log n) -
            suzukiCriticalPoleCusp g (w j) (Real.log n))| ≤
          α * (2 * E j + (2 * A j * Real.exp (A j / 2) * E j)) +
            α * (2 * w j * ((2 * K / (β - 1 / 2)) * (n : ℝ) ^ (-β))) := by
        have h1 := (abs_sub _ _).trans (add_le_add hprim_sub (by
          rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * w j)]
          exact mul_le_mul_of_nonneg_left hpole_sub' (by positivity)))
        have h2 : 2 * w j * (2 * A j * Real.exp (A j / 2) * E j +
            (2 * K / (β - 1 / 2)) * (n : ℝ) ^ (-β)) ≤
            2 * A j * Real.exp (A j / 2) * E j +
            2 * w j * ((2 * K / (β - 1 / 2)) * (n : ℝ) ^ (-β)) := by
          have := mul_le_mul_of_nonneg_right h2w_le1
            (show 0 ≤ 2 * A j * Real.exp (A j / 2) * E j by positivity)
          linarith
        have h3 := mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hα_nn
        linarith
      refine htri.trans (add_le_add ?_ ?_)
      · calc α * (2 * E j + 2 * A j * Real.exp (A j / 2) * E j)
            ≤ (2 * A j) * (2 * E j + 2 * A j * Real.exp (A j / 2) * E j) :=
              mul_le_mul_of_nonneg_right hα_A (by positivity)
          _ = (4 * A j + 4 * A j ^ 2 * Real.exp (A j / 2)) * E j := by ring
          _ ≤ (4 * A j + 8 * A j ^ 2 * Real.exp (A j / 2)) * E j := by
              nlinarith [sq_nonneg (A j), Real.exp_pos (A j / 2)]
      · calc α * (2 * w j * ((2 * K / (β - 1 / 2)) * (n : ℝ) ^ (-β)))
            ≤ (2 * Real.log n * (n : ℝ) ^ (δ - 1 / 2)) *
                (2 * w j * ((2 * K / (β - 1 / 2)) * (n : ℝ) ^ (-β))) :=
              mul_le_mul_of_nonneg_right hα_δ (by positivity)
          _ = w j * ((4 * K / (β - 1 / 2)) * (Real.log n *
                ((n : ℝ) ^ (δ - 1 / 2) * (n : ℝ) ^ (-β)))) := by ring
          _ = w j * ((4 * K / (β - 1 / 2)) * (Real.log n * (n : ℝ) ^ (-p))) := by
              rw [← Real.rpow_add hn_pos]; unfold p; ring_nf
          _ ≤ w j * ((8 * K / (β - 1 / 2)) * (Real.log n * (n : ℝ) ^ (-p))) := by
              gcongr; linarith [div_nonneg hK (show 0 ≤ β - 1 / 2 by linarith)]
    have hcard_le : (S_j.card : ℝ) ≤ Real.exp (A j) := by
      have hcard_nat : S_j.card ≤ ⌊Real.exp (A j)⌋₊ := by
        simp only [S_j, Nat.card_Icc]
        omega
      exact (Nat.cast_le.mpr hcard_nat).trans (Nat.floor_le (Real.exp_pos _).le)
    have hsum1 : ∑ _n ∈ S_j, (4 * A j + 8 * A j ^ 2 * Real.exp (A j / 2)) * E j ≤
        132 * (Real.exp (2 * A j) * E j) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hA_exp : A j * Real.exp (A j) ≤ Real.exp (2 * A j) := by
        have h1 : A j ≤ Real.exp (A j) :=
          (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (A j))
        calc A j * Real.exp (A j) ≤ Real.exp (A j) * Real.exp (A j) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = Real.exp (2 * A j) := by rw [← Real.exp_add]; congr 1; ring
      have hA2_exp : A j ^ 2 * Real.exp (A j / 2) * Real.exp (A j) ≤
          16 * Real.exp (2 * A j) := by
        calc A j ^ 2 * Real.exp (A j / 2) * Real.exp (A j)
            ≤ (16 * Real.exp (A j / 2)) * Real.exp (A j / 2) * Real.exp (A j) := by
              gcongr; exact sq_le_sixteen_exp_half hAj0
          _ = 16 * Real.exp (2 * A j) := by
              rw [mul_assoc 16, mul_assoc 16, ← Real.exp_add, ← Real.exp_add]
              congr 2; ring
      calc (S_j.card : ℝ) * ((4 * A j + 8 * A j ^ 2 * Real.exp (A j / 2)) * E j)
          ≤ Real.exp (A j) * ((4 * A j + 8 * A j ^ 2 * Real.exp (A j / 2)) * E j) :=
            mul_le_mul_of_nonneg_right hcard_le (by positivity)
        _ = (4 * (A j * Real.exp (A j)) +
              8 * (A j ^ 2 * Real.exp (A j / 2) * Real.exp (A j))) * E j := by ring
        _ ≤ (4 * Real.exp (2 * A j) + 8 * (16 * Real.exp (2 * A j))) * E j :=
            mul_le_mul_of_nonneg_right (by linarith) hE_nn
        _ = 132 * (Real.exp (2 * A j) * E j) := by ring
    have hsum2 : ∑ n ∈ S_j, w j * ((8 * K / (β - 1 / 2)) * (Real.log n * (n : ℝ) ^ (-p))) ≤
        w j * ∑' n : ℕ, (8 * K / (β - 1 / 2)) * (Real.log n * (n : ℝ) ^ (-p)) := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (htail_sum.sum_le_tsum S_j fun m _ => ?_) hwj.le
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · exact mul_nonneg (by positivity) (mul_nonneg (Real.log_nonneg (by exact_mod_cast hm))
          (Real.rpow_nonneg (Nat.cast_nonneg m) _))
    calc ∑ n ∈ S_j,
          |(suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
              suzukiCriticalSourceCusp (f j) (w j) (Real.log n) -
            (suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
              suzukiCriticalSourceCusp g (w j) (Real.log n)|
        ≤ ∑ n ∈ S_j, ((4 * A j + 8 * A j ^ 2 * Real.exp (A j / 2)) * E j +
            w j * ((8 * K / (β - 1 / 2)) * (Real.log n * (n : ℝ) ^ (-p)))) :=
          Finset.sum_le_sum hterm_le
      _ = (∑ _n ∈ S_j, (4 * A j + 8 * A j ^ 2 * Real.exp (A j / 2)) * E j) +
          (∑ n ∈ S_j, w j * ((8 * K / (β - 1 / 2)) * (Real.log n * (n : ℝ) ^ (-p)))) :=
          Finset.sum_add_distrib
      _ ≤ 132 * (Real.exp (2 * A j) * E j) +
          w j * ∑' n : ℕ, (8 * K / (β - 1 / 2)) * (Real.log n * (n : ℝ) ^ (-p)) :=
          add_le_add hsum1 hsum2
  -- 4. Assemble signed remainder convergence + Fatou primary energy:
  have hprime_f : Tendsto (fun j => ∑ n ∈ Finset.Icc 2 ⌊Real.exp (A j)⌋₊,
      (suzukiShiftedCoefficient (w j) n / w j * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp (f j) (w j) (Real.log n)) atTop
      (𝓝 (∑' n : ℕ, if 2 ≤ n then
        (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
          autocorr g (Real.log n) else 0)) := by
    simpa only [sub_add_cancel, zero_add] using hsum_diff.add hg_trunc_tendsto
  have hrem : Tendsto (fun j => suzukiCriticalWindowSignedRemainder (A j) (f j) (w j)) atTop
      (𝓝 (((Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi) * autocorr g 0 +
        2 * (∫ t in Ioi 0, autocorr g t * Real.exp (t / 2)) -
        ∑' n : ℕ, if 2 ≤ n then
          (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
            autocorr g (Real.log n) else 0)) :=
    (hM_sec.add hp_f).sub hprime_f
  have hprim : (suzukiCriticalLimitingCompensatedEnergy
      (fun t => autocorr g 0 - autocorr g t) : EReal) ≤
      liminf (fun j => (suzukiCriticalCompensatedEnergy
        (fun t => autocorr (f j) 0 - autocorr (f j) t) (w j) : EReal)) atTop := by
    have h := suzukiCriticalLimitingEnergy_le_liminf_of_L2_tendsto hfg hw
    have hc (j : ℕ) : autocorr ((hf j).toLp (f j)) = autocorr (f j) :=
      funext (autocorr_congr_ae (hf j).coeFn_toLp)
    have hr : autocorr (hg.toLp g) = autocorr g := funext (autocorr_congr_ae hg.coeFn_toLp)
    simp only [hc, hr] at h
    have hmono : Monotone ENNReal.toEReal := fun _ _ hab =>
      EReal.coe_ennreal_le_coe_ennreal_iff.mpr hab
    change ENNReal.toEReal (suzukiCriticalLimitingCompensatedEnergy
      (fun t => autocorr g 0 - autocorr g t)) ≤
      liminf (ENNReal.toEReal ∘ fun j => suzukiCriticalCompensatedEnergy
        (fun t => autocorr (f j) 0 - autocorr (f j) t) (w j)) atTop
    rw [← hmono.map_liminf_of_continuousAt _ continuous_coe_ennreal_ereal.continuousAt]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  set R_lim : ℝ := ((Complex.digamma ((5 / 4 : ℝ) : ℂ)).re - Real.log Real.pi) * autocorr g 0 +
    2 * (∫ t in Ioi 0, autocorr g t * Real.exp (t / 2)) -
    ∑' n : ℕ, if 2 ≤ n then
      (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        autocorr g (Real.log n) else 0
  have hc : Tendsto (fun j => ((suzukiCriticalWindowSignedRemainder (A j) (f j) (w j) : ℝ) : EReal))
      atTop (𝓝 (R_lim : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hrem
  have h : (suzukiCriticalLimitingCompensatedEnergy
      (fun t => autocorr g 0 - autocorr g t) : EReal) + (R_lim : EReal) ≤
      liminf (fun j => (suzukiCriticalCompensatedEnergy
        (fun t => autocorr (f j) 0 - autocorr (f j) t) (w j) : EReal) +
          ((suzukiCriticalWindowSignedRemainder (A j) (f j) (w j) : ℝ) : EReal)) atTop := by
    calc (suzukiCriticalLimitingCompensatedEnergy
          (fun t => autocorr g 0 - autocorr g t) : EReal) + (R_lim : EReal)
        ≤ liminf (fun j => (suzukiCriticalCompensatedEnergy
            (fun t => autocorr (f j) 0 - autocorr (f j) t) (w j) : EReal)) atTop +
          liminf (fun j => ((suzukiCriticalWindowSignedRemainder (A j) (f j) (w j) : ℝ) : EReal))
            atTop := by
          rw [hc.liminf_eq]
          exact add_le_add hprim le_rfl
      _ ≤ _ := EReal.le_liminf_add
  rw [suzukiCriticalInfiniteEnergy_eq_extendedWeilEnergy_of_exp_decay hg hβ hg_dec] at h
  refine h.trans_eq ?_
  apply Filter.liminf_congr
  have ho : ∀ᶠ j in atTop, w j < 1 / 2 := hw.eventually
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  filter_upwards [hw.eventually self_mem_nhdsWithin, ho] with j hwj ho
  exact (suzukiCriticalSourcePairing_div_eq_energy_add_windowRemainder
    (hf j) (hfc j) (hA_pos j) (hcut j) hwj ho.le).symm

/-- **Coupled General Moving-Aperture Positive-Deficit Inheritance.** -/
theorem eventually_suzukiCriticalDeficit_of_coupled_moving_aperture
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {w A : ℕ → ℝ} {β K c δ : ℝ}
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume)
    (hfc : ∀ j, HasCompactSupport (f j))
    (hA_pos : ∀ j, 0 < A j) (hA_top : Tendsto A atTop atTop)
    (hcut : ∀ j t, A j ≤ t → autocorr (f j) t = 0)
    (hfg : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)))
    (hw : Tendsto w atTop (𝓝[>] 0))
    (hβ : 1 / 2 < β)
    (hg_dec : ∀ t : ℝ, 0 ≤ t → |autocorr g t| ≤ K * Real.exp (-β * t))
    (hrate : Tendsto (fun j => Real.exp (2 * A j) * ‖(hf j).toLp (f j) - hg.toLp g‖)
      atTop (𝓝 0))
    (hweil : ((c : ℝ) : EReal) ≤ suzukiCriticalExtendedWeilEnergy g)
    (hδ : 0 < δ) :
    ∀ᶠ j in atTop, w j * (c - δ) <
      autocorr (f j) 0 - suzukiCriticalSourcePairing (f j) (w j) :=
  eventually_suzukiCriticalDeficit_of_le_liminf hδ hw
    (hweil.trans (suzukiCriticalExtendedWeilEnergy_le_liminf_of_coupled_moving_aperture
      hf hg hfc hA_pos hA_top hcut hfg hw hβ hg_dec hrate))

end
end RHTower

#print axioms RHTower.suzukiShiftedCoefficient_div_bounds
#print axioms RHTower.integrableOn_suzukiCriticalPoleCusp_of_exp_decay
#print axioms RHTower.integral_norm_suzukiCriticalPoleCusp_le_of_exp_decay
#print axioms RHTower.integrableOn_suzukiCriticalSourceCusp_of_exp_decay
#print axioms RHTower.suzukiCriticalSourceCusp_eq_of_exp_decay
#print axioms RHTower.integral_norm_suzukiCriticalSourceCusp_le_of_exp_decay
#print axioms RHTower.abs_suzukiCriticalSourceCusp_le_of_exp_decay
#print axioms RHTower.suzukiCriticalSourcePairing_eq_tsum_of_exp_decay
#print axioms RHTower.suzukiCriticalL2Weil_normalization_of_exp_decay
#print axioms RHTower.suzukiCriticalInfinitePrimePolar_eq_fullPairing
#print axioms RHTower.suzukiCriticalInfiniteEnergy_eq_extendedWeilEnergy_of_exp_decay
#print axioms RHTower.suzukiCriticalInfiniteSignedRemainder
#print axioms RHTower.suzukiCriticalSourcePairing_div_eq_energy_add_infiniteRemainder
#print axioms RHTower.tendsto_suzukiCriticalPoleCusp_joint_of_exp_decay
#print axioms RHTower.tendsto_suzukiCriticalSourceCusp_joint_of_exp_decay
#print axioms RHTower.tendsto_suzukiCriticalInfiniteSignedRemainder_joint_of_exp_decay
#print axioms RHTower.suzukiCriticalExtendedWeilEnergy_le_liminf_of_exp_decay_tendsto
#print axioms RHTower.eventually_suzukiCriticalDeficit_of_exp_decay_tendsto
#print axioms RHTower.tendsto_suzukiCriticalSourcePairing_extended_firstVariation_of_exp_decay
#print axioms RHTower.suzukiCriticalExtendedWeilEnergy_le_liminf_of_coupled_moving_aperture
#print axioms RHTower.eventually_suzukiCriticalDeficit_of_coupled_moving_aperture
