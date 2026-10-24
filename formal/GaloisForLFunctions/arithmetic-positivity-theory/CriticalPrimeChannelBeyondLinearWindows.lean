import GaloisForLFunctions.«arithmetic-positivity-theory».TheLinearWindowOfTheCriticalPrimeChannel
import GaloisForLFunctions.«arithmetic-positivity-theory».LacunaryCriticalBlockPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeSingletonNegative
import GaloisForLFunctions.HTGeometry.RpowHarmonicTailAsymptotic
import Mathlib.NumberTheory.ZetaValues

/-!
# The Critical Prime Channel Beyond Linear Windows

On a narrow linear window `[N, (1 + δ)N]` (`0 < δ ≤ 1` small, `N` large), the uncollared critical
prime channel `criticalPrimeEnergy` is strictly negative definite, turning `-2 P` into a strictly
positive subsidy inside `criticalCompleteEnergy`. This module resolves the sign geometry and
multi-scale coupling of `criticalPrimeEnergy` beyond narrow linear windows across both regimes:

1. **Commensurable Scale-Ratio Correlation Limit and Dyadic First-Harmonic Resonance.**
   For arbitrary positive integers `a, c, r ≥ 1`, as `N → ∞`, the physical cross-correlation of
   factorial phase profiles at scales `a N` and `c N` at integer dilation `r` converges to the
   exact slow-phase polarization series
   `(4 / π⁴) ∑_{a k = c r l} w_k w_l (J_k + J_{r l} - J_{|k - r l|}) / 2`.
   At the dyadic endpoint ratio `2 : 1` (`dyadicPairSupport M = {M - 1, 2 M - 1}` with unit
   coefficients), the `r = 2` upward cross-correlation has `2 k = 2 l`, whose `k = l = 1` first
   harmonic contributes `+(log 2 / π⁴) J_2`. This cancels the unique negative harmonic
   `-(log 2 / π⁴) J_2` of `2 · factorialCriticalPrimeLimit` identically to zero, leaving the
   strictly positive odd-prime diagonal harmonics (`m = 3, 5, …`) dominant over all remaining
   dyadic cross-correlations:
   `criticalPrimeEnergy (dyadicPairSupport M) (fun _ => 1) → dyadicPairPrimeLimit ≥ (1/8)(log 2 / π⁴) > 0`.
   Consequently, negative semidefiniteness of `criticalPrimeEnergy` fails on dyadic blocks
   `[M, 2M]`, on `ScaleWindow S M L` for every `L ≥ 2`, on wide linear windows `[N, (1 + δ)N]` for
   every `δ ≥ 1`, on polynomial windows `[N, N^{1 + δ}]` for every `δ > 0`, and on all scales at
   once.

2. **Spaced-Hilbert Schur Cross-Block Decay for the Uncollared Critical Prime Channel.**
   Although `weightCosineTransform criticalWindowWeight` decays only as `O(1 / |f|)` due to the
   unit jump of the critical source at `x = 0`, combining `L²` harmonic Cauchy–Schwarz on
   sub-resonant dilations, a `1 / |f|` spaced-summation inequality on resonant bands, and a
   Mean-Value-Theorem `r^{-15/8}` tail bound on `∑_{r ≥ X} Λ(r) / r²` yields explicit polynomial
   off-diagonal decay `O(M^{-1/64} (M')^{-1/64} ‖b_S‖₂ ‖b_{S'}‖₂)` between any two dyadic blocks
   with `3 ≤ M` and `M⁸ ≤ M'`.

3. **Unbounded Lacunary Multi-Window Negativity and Uncollared Lacunary Positivity.**
   Because `∑_{i < J} M_i^{-1/32} ≤ 5 M_0^{-1/32} → 0` uniformly in the number of blocks `J` on
   any lacunary family (`M_{i+1} ≥ M_i⁸`), the uncollared cross-block law yields two unconditional
   multi-scale consequences across arbitrarily many scales `[M_0, M_0^{8^{J-1}}]`:
   * On any unbounded lacunary family of narrow linear windows `W_i ⊆ [M_i, (1 + δ₀) M_i]`
     (`M_0 ≥ M_*`), `criticalPrimeEnergy ((Finset.range J).biUnion W) b ≤ -(1 / (7000 π⁴)) ∑ b_n²`,
     so `-2 P` provides a strictly positive prime subsidy across arbitrarily many lacunary scales.
   * On any unbounded lacunary family of full dyadic blocks `S_i ⊆ [M_i, 2 M_i]`, the uncollared
     `criticalPrimeEnergy` is `ℓ²`-uniformly bounded independently of `J`, and the uncollared
     `criticalCompleteEnergy` is strictly positive definite for all `M_0 ≥ M_pos` and all `J : ℕ`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Commensurable Scale-Ratio Limits and Dyadic Sign Reversal -/

/-- Critical physical cosine integral `∫_{v > 1} v^{-2} cos(2π u v) dv`. -/
private def criticalCosineIntegral (u : ℝ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * Real.cos (2 * Real.pi * u * v)

private theorem criticalCosineIntegral_zero : criticalCosineIntegral 0 = 1 := by
  unfold criticalCosineIntegral
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
  norm_num

private theorem criticalCosineIntegral_neg (u : ℝ) :
    criticalCosineIntegral (-u) = criticalCosineIntegral u := by
  unfold criticalCosineIntegral
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [show 2 * Real.pi * -u * v = -(2 * Real.pi * u * v) by ring, Real.cos_neg]

private theorem factorialCriticalHarmonicDefect_eq_sub_cos (m : ℕ) :
    factorialCriticalHarmonicDefect m = 1 - criticalCosineIntegral ((m : ℝ) / 12) := by
  unfold factorialCriticalHarmonicDefect criticalCosineIntegral
  have h1 : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have h2 : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ) *
      Real.cos (2 * Real.pi * ((m : ℝ) / 12) * v)) (Ioi 1) :=
    h1.mul_bdd (by fun_prop) (Eventually.of_forall fun v => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  simp_rw [mul_sub, mul_one]
  rw [integral_sub h1 h2, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
  norm_num

private theorem factorialCriticalHarmonicDefect_zero :
    factorialCriticalHarmonicDefect 0 = 0 := by
  rw [factorialCriticalHarmonicDefect_eq_sub_cos]
  simp [criticalCosineIntegral_zero]

/-- Slow-phase polarization kernel `(J_k + J_q - J_{|k - q|}) / 2` arising from the resonant
limit of `(cos(2π k λ_{aN} v) - cos(2π k a N v))(cos(2π l λ_{cN} r v) - cos(2π l c N r v))`
when `a k = c q` (`q = r l`). -/
def slowPhasePolarization (k q : ℕ) : ℝ :=
  (factorialCriticalHarmonicDefect k + factorialCriticalHarmonicDefect q -
    factorialCriticalHarmonicDefect (Int.natAbs ((k : ℤ) - (q : ℤ)))) / 2

theorem slowPhasePolarization_self (k : ℕ) :
    slowPhasePolarization k k = factorialCriticalHarmonicDefect k := by
  unfold slowPhasePolarization
  simp only [sub_self, Int.natAbs_zero, factorialCriticalHarmonicDefect_zero, sub_zero]
  ring

theorem slowPhasePolarization_double_right (k : ℕ) :
    slowPhasePolarization k (2 * k) = factorialCriticalHarmonicDefect (2 * k) / 2 := by
  unfold slowPhasePolarization
  have h : Int.natAbs ((k : ℤ) - ((2 * k : ℕ) : ℤ)) = k := by omega
  rw [h]
  ring

theorem slowPhasePolarization_double_left (q : ℕ) :
    slowPhasePolarization (2 * q) q = factorialCriticalHarmonicDefect (2 * q) / 2 := by
  unfold slowPhasePolarization
  have h : Int.natAbs (((2 * q : ℕ) : ℤ) - (q : ℤ)) = q := by omega
  rw [h]
  ring

theorem abs_slowPhasePolarization_le (k q : ℕ) :
    |slowPhasePolarization k q| ≤ 2 := by
  unfold slowPhasePolarization
  obtain ⟨hk0, hk2⟩ := factorialCriticalHarmonicDefect_bounds k
  obtain ⟨hq0, hq2⟩ := factorialCriticalHarmonicDefect_bounds q
  obtain ⟨hd0, hd2⟩ := factorialCriticalHarmonicDefect_bounds (Int.natAbs ((k : ℤ) - (q : ℤ)))
  rw [abs_le]
  constructor <;> linarith

private theorem criticalCosineIntegral_polarization (k q : ℕ) :
    criticalCosineIntegral ((k : ℝ) / 12 - (q : ℝ) / 12) / 2 -
      criticalCosineIntegral ((k : ℝ) / 12 - 0) / 2 -
      criticalCosineIntegral (0 - (q : ℝ) / 12) / 2 +
      criticalCosineIntegral (0 - 0) / 2 =
    slowPhasePolarization k q := by
  set d : ℕ := Int.natAbs ((k : ℤ) - (q : ℤ))
  have hd : criticalCosineIntegral ((k : ℝ) / 12 - (q : ℝ) / 12) =
      criticalCosineIntegral ((d : ℝ) / 12) := by
    rcases le_total q k with hqk | hkq
    · have h1 : d = k - q := by omega
      rw [h1, Nat.cast_sub hqk]
      congr 1
      ring
    · have h1 : d = q - k := by omega
      rw [h1, Nat.cast_sub hkq, ← criticalCosineIntegral_neg]
      congr 1
      ring
  rw [hd, show (0 : ℝ) - (q : ℝ) / 12 = -((q : ℝ) / 12) by ring,
    criticalCosineIntegral_neg, sub_zero, sub_self, criticalCosineIntegral_zero]
  unfold slowPhasePolarization
  rw [factorialCriticalHarmonicDefect_eq_sub_cos k,
    factorialCriticalHarmonicDefect_eq_sub_cos q,
    factorialCriticalHarmonicDefect_eq_sub_cos d]
  ring

private def scaledHarmonicLayer (N k : ℕ) (v : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * (k : ℝ) * factorialShiftedFreq N * v) -
    Real.cos (2 * Real.pi * (k : ℝ) * (N : ℝ) * v)

private theorem abs_scaledHarmonicLayer_le (N k : ℕ) (v : ℝ) :
    |scaledHarmonicLayer N k v| ≤ 2 := by
  unfold scaledHarmonicLayer
  have h1 := abs_le.mp (Real.abs_cos_le_one (2 * Real.pi * (k : ℝ) * factorialShiftedFreq N * v))
  have h2 := abs_le.mp (Real.abs_cos_le_one (2 * Real.pi * (k : ℝ) * (N : ℝ) * v))
  rw [abs_le]
  constructor <;> linarith

private theorem scaledHarmonicLayer_hasSum (N : ℕ) (v : ℝ) :
    HasSum (fun k : ℕ => dyadicHarmonicWeight k * scaledHarmonicLayer N k v)
      (-(Real.pi ^ 2 / 2) * factorialPhaseProfile N v) := by
  refine (factorialPhaseProfile_hasSum N v).congr_fun fun k => ?_
  unfold dyadicHarmonicWeight scaledHarmonicLayer
  ring_nf

private def scaledLayerCrossCorr (a c n k l r : ℕ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
    scaledHarmonicLayer (a * (n + 1)) k v *
    scaledHarmonicLayer (c * (n + 1)) l ((r : ℝ) * v)

private theorem abs_scaledLayerCrossCorr_le (a c n k l r : ℕ) :
    |scaledLayerCrossCorr a c n k l r| ≤ 4 := by
  unfold scaledLayerCrossCorr
  have hw : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hc : Continuous (fun v : ℝ =>
      scaledHarmonicLayer (a * (n + 1)) k v *
        scaledHarmonicLayer (c * (n + 1)) l ((r : ℝ) * v)) := by
    unfold scaledHarmonicLayer
    fun_prop
  have hprod : ∀ v : ℝ, |scaledHarmonicLayer (a * (n + 1)) k v *
      scaledHarmonicLayer (c * (n + 1)) l ((r : ℝ) * v)| ≤ 4 := fun v => by
    rw [abs_mul]
    exact (mul_le_mul (abs_scaledHarmonicLayer_le _ _ _) (abs_scaledHarmonicLayer_le _ _ _)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hint : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ) *
      scaledHarmonicLayer (a * (n + 1)) k v *
      scaledHarmonicLayer (c * (n + 1)) l ((r : ℝ) * v)) (Ioi 1) := by
    refine (hw.const_mul 4).mono' (hw.aestronglyMeasurable.mul hc.aestronglyMeasurable |>.congr
      (Eventually.of_forall fun v => by dsimp only [Pi.mul_apply]; ring)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hv.le) _
    rw [show v ^ (-2 : ℝ) * scaledHarmonicLayer (a * (n + 1)) k v *
      scaledHarmonicLayer (c * (n + 1)) l ((r : ℝ) * v) =
      v ^ (-2 : ℝ) * (scaledHarmonicLayer (a * (n + 1)) k v *
        scaledHarmonicLayer (c * (n + 1)) l ((r : ℝ) * v)) by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hv0]
    linarith [mul_le_mul_of_nonneg_left (hprod v) hv0]
  calc |∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
        scaledHarmonicLayer (a * (n + 1)) k v *
        scaledHarmonicLayer (c * (n + 1)) l ((r : ℝ) * v)|
      ≤ ∫ v in Ioi (1 : ℝ), ‖v ^ (-2 : ℝ) *
          scaledHarmonicLayer (a * (n + 1)) k v *
          scaledHarmonicLayer (c * (n + 1)) l ((r : ℝ) * v)‖ :=
        Real.norm_eq_abs _ ▸ norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioi (1 : ℝ), 4 * v ^ (-2 : ℝ) := by
        refine setIntegral_mono_on hint.norm (hw.const_mul 4) measurableSet_Ioi fun v hv => ?_
        have hv0 : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hv.le) _
        rw [show v ^ (-2 : ℝ) * scaledHarmonicLayer (a * (n + 1)) k v *
          scaledHarmonicLayer (c * (n + 1)) l ((r : ℝ) * v) =
          v ^ (-2 : ℝ) * (scaledHarmonicLayer (a * (n + 1)) k v *
            scaledHarmonicLayer (c * (n + 1)) l ((r : ℝ) * v)) by ring,
          Real.norm_eq_abs, abs_mul, abs_of_nonneg hv0]
        linarith [mul_le_mul_of_nonneg_left (hprod v) hv0]
    _ = 4 := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
        norm_num

private theorem tendsto_factorialAffineDefect_mul_scale {a : ℕ} (ha : 1 ≤ a) :
    Tendsto (fun n : ℕ => factorialAffineDefect (a * (n + 1))) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun n : ℕ => 1 / (140 * ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, div_div] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 / 140 : ℝ)).comp (tendsto_add_atTop_nat 1)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hmaj
  · have hpos : 1 ≤ a * (n + 1) := Nat.mul_pos ha (Nat.succ_pos n)
    have hb := (factorialAffineDefect_bounds (a * (n + 1) - 1)).1
    rw [Nat.sub_add_cancel hpos] at hb
    exact le_trans (by positivity) hb
  · have hpos : 1 ≤ a * (n + 1) := Nat.mul_pos ha (Nat.succ_pos n)
    have hb := (factorialAffineDefect_bounds (a * (n + 1) - 1)).2
    have hcast : ((a * (n + 1) - 1 : ℕ) : ℝ) + 1 = ((a * (n + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hpos
    rw [Nat.sub_add_cancel hpos, hcast] at hb
    have hn1_pos : (0 : ℝ) < 140 * ((n + 1 : ℕ) : ℝ) := by positivity
    refine hb.trans (div_le_div_of_nonneg_left zero_le_one hn1_pos ?_)
    have hle : n + 1 ≤ a * (n + 1) := Nat.le_mul_of_pos_left (n + 1) ha
    have hleR : ((n + 1 : ℕ) : ℝ) ≤ ((a * (n + 1) : ℕ) : ℝ) := by exact_mod_cast hle
    linarith

private theorem scaledLayerCrossCorr_tendsto {a c k l r : ℕ}
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hk : 1 ≤ k) (hl : 1 ≤ l) (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => scaledLayerCrossCorr a c n k l r) atTop
      (𝓝 (if k * a = r * l * c then slowPhasePolarization k (r * l) else 0)) := by
  set α : ℝ := ((k * a : ℕ) : ℝ)
  set β : ℝ := ((r * l * c : ℕ) : ℝ)
  have hα : 0 < α := by
    have : 0 < k * a := Nat.mul_pos hk ha
    dsimp only [α]
    exact_mod_cast this
  have hβ : 0 < β := by
    have : 0 < r * l * c := Nat.mul_pos (Nat.mul_pos hr hl) hc
    dsimp only [β]
    exact_mod_cast this
  have hs : Tendsto (fun n : ℕ => (k : ℝ) * (1 / 12 - factorialAffineDefect (a * (n + 1))))
      atTop (𝓝 ((k : ℝ) / 12)) := by
    have h := ((tendsto_const_nhds (x := (1 / 12 : ℝ))).sub
      (tendsto_factorialAffineDefect_mul_scale ha)).const_mul (k : ℝ)
    simpa [sub_zero, div_eq_mul_inv] using h
  have ht : Tendsto (fun n : ℕ => ((r * l : ℕ) : ℝ) *
      (1 / 12 - factorialAffineDefect (c * (n + 1)))) atTop (𝓝 (((r * l : ℕ) : ℝ) / 12)) := by
    have h := ((tendsto_const_nhds (x := (1 / 12 : ℝ))).sub
      (tendsto_factorialAffineDefect_mul_scale hc)).const_mul (((r * l : ℕ) : ℝ))
    simpa [sub_zero, div_eq_mul_inv] using h
  have h11 := factorialCriticalCosineProduct_tendsto hα hβ hs ht
  have h10 := factorialCriticalCosineProduct_tendsto hα hβ hs (tendsto_const_nhds (x := (0 : ℝ)))
  have h01 := factorialCriticalCosineProduct_tendsto hα hβ (tendsto_const_nhds (x := (0 : ℝ))) ht
  have h00 := factorialCriticalCosineProduct_tendsto hα hβ
    (tendsto_const_nhds (x := (0 : ℝ))) (tendsto_const_nhds (x := (0 : ℝ)))
  have hcomb := ((h11.sub h10).sub h01).add h00
  have hlim_eq :
      (if α = β then (∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) *
          Real.cos (2 * Real.pi * ((k : ℝ) / 12 - ((r * l : ℕ) : ℝ) / 12) * x)) / 2 else 0) -
      (if α = β then (∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) *
          Real.cos (2 * Real.pi * ((k : ℝ) / 12 - 0) * x)) / 2 else 0) -
      (if α = β then (∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) *
          Real.cos (2 * Real.pi * (0 - ((r * l : ℕ) : ℝ) / 12) * x)) / 2 else 0) +
      (if α = β then (∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) *
          Real.cos (2 * Real.pi * (0 - 0) * x)) / 2 else 0) =
      if k * a = r * l * c then slowPhasePolarization k (r * l) else 0 := by
    have hiff : (α = β) ↔ (k * a = r * l * c) := Nat.cast_inj
    by_cases hres : k * a = r * l * c
    · have hresR : α = β := hiff.mpr hres
      simp only [hres, hresR, ite_true]
      exact criticalCosineIntegral_polarization k (r * l)
    · have hresR : α ≠ β := fun h => hres (hiff.mp h)
      simp [hres, hresR]
  rw [hlim_eq] at hcomb
  refine hcomb.congr fun n => ?_
  have hw : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hint (x y : ℝ) : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ) *
      Real.cos (2 * Real.pi * x * v) * Real.cos (2 * Real.pi * y * v)) (Ioi 1) := by
    refine hw.mono' (hw.aestronglyMeasurable.mul
      ((by fun_prop : Continuous fun v => Real.cos (2 * Real.pi * x * v) *
        Real.cos (2 * Real.pi * y * v)).aestronglyMeasurable) |>.congr
      (Eventually.of_forall fun v => by dsimp only [Pi.mul_apply]; ring)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hv.le) _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hv0]
    have hc1 := Real.abs_cos_le_one (2 * Real.pi * x * v)
    have hc2 := Real.abs_cos_le_one (2 * Real.pi * y * v)
    nlinarith [mul_le_one₀ hc1 (abs_nonneg _) hc2]
  set x1 := α * ((n + 1 : ℕ) : ℝ) + (k : ℝ) * (1 / 12 - factorialAffineDefect (a * (n + 1)))
  set x0 := α * ((n + 1 : ℕ) : ℝ) + (0 : ℝ)
  set y1 := β * ((n + 1 : ℕ) : ℝ) +
    ((r * l : ℕ) : ℝ) * (1 / 12 - factorialAffineDefect (c * (n + 1)))
  set y0 := β * ((n + 1 : ℕ) : ℝ) + (0 : ℝ)
  have hx1 (v : ℝ) : 2 * Real.pi * x1 * v =
      2 * Real.pi * (k : ℝ) * factorialShiftedFreq (a * (n + 1)) * v := by
    simp only [x1, α, factorialAffineDefect]
    push_cast
    ring
  have hx0 (v : ℝ) : 2 * Real.pi * x0 * v =
      2 * Real.pi * (k : ℝ) * ((a * (n + 1) : ℕ) : ℝ) * v := by
    simp only [x0, α]
    push_cast
    ring
  have hy1 (v : ℝ) : 2 * Real.pi * y1 * v =
      2 * Real.pi * (l : ℝ) * factorialShiftedFreq (c * (n + 1)) * ((r : ℝ) * v) := by
    simp only [y1, β, factorialAffineDefect]
    push_cast
    ring
  have hy0 (v : ℝ) : 2 * Real.pi * y0 * v =
      2 * Real.pi * (l : ℝ) * ((c * (n + 1) : ℕ) : ℝ) * ((r : ℝ) * v) := by
    simp only [y0, β]
    push_cast
    ring
  unfold scaledLayerCrossCorr
  have hsub1 := integral_sub (hint x1 y1) (hint x1 y0)
  have hsub2 := integral_sub (hint x1 y1 |>.sub (hint x1 y0)) (hint x0 y1)
  have hadd3 := integral_add ((hint x1 y1 |>.sub (hint x1 y0)).sub (hint x0 y1)) (hint x0 y0)
  simp only [Pi.sub_apply] at hsub1 hsub2 hadd3
  rw [← hsub1, ← hsub2, ← hadd3]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  unfold scaledHarmonicLayer
  rw [hx1 v, hx0 v, hy1 v, hy0 v]
  ring

/-- Physical cross-correlation of factorial phase profiles at scales `a(n+1)` and `c(n+1)` at
integer dilation `r`. -/
def scaleRatioCorrelation (a c n r : ℕ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
    factorialPhaseProfile (a * (n + 1)) v *
    factorialPhaseProfile (c * (n + 1)) ((r : ℝ) * v)

/-- Limiting cross-correlation of factorial phase profiles at scale ratio `a : c` and integer
dilation `r`. -/
def scaleRatioCorrelationLimit (a c r : ℕ) : ℝ :=
  (4 / Real.pi ^ 4) * ∑' p : ℕ × ℕ,
    if p.1 * a = r * p.2 * c then
      dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 * slowPhasePolarization p.1 (r * p.2)
    else 0

private def harmonicPairMajorant (p : ℕ × ℕ) : ℝ :=
  (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) * 4

private theorem summable_harmonicPairMajorant : Summable harmonicPairMajorant :=
  (summable_abs_dyadicHarmonicWeight.mul_of_nonneg summable_abs_dyadicHarmonicWeight
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)).mul_right 4

private theorem scaleRatioCorrelation_hasSum (a c n r : ℕ) :
    HasSum (fun p : ℕ × ℕ => dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      scaledLayerCrossCorr a c n p.1 p.2 r)
      ((Real.pi ^ 4 / 4) * scaleRatioCorrelation a c n r) := by
  have hw : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hpt_bd (p : ℕ × ℕ) (v : ℝ) :
      |(dyadicHarmonicWeight p.1 * scaledHarmonicLayer (a * (n + 1)) p.1 v) *
        (dyadicHarmonicWeight p.2 * scaledHarmonicLayer (c * (n + 1)) p.2 ((r : ℝ) * v))| ≤
        harmonicPairMajorant p := by
    unfold harmonicPairMajorant
    have hprod : |scaledHarmonicLayer (a * (n + 1)) p.1 v *
        scaledHarmonicLayer (c * (n + 1)) p.2 ((r : ℝ) * v)| ≤ 4 := by
      rw [abs_mul]
      exact (mul_le_mul (abs_scaledHarmonicLayer_le _ _ _) (abs_scaledHarmonicLayer_le _ _ _)
        (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    calc |(dyadicHarmonicWeight p.1 * scaledHarmonicLayer (a * (n + 1)) p.1 v) *
          (dyadicHarmonicWeight p.2 * scaledHarmonicLayer (c * (n + 1)) p.2 ((r : ℝ) * v))|
        = (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) *
            |scaledHarmonicLayer (a * (n + 1)) p.1 v *
              scaledHarmonicLayer (c * (n + 1)) p.2 ((r : ℝ) * v)| := by
          simp only [abs_mul]; ring
      _ ≤ (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) * 4 :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
  have hs (v : ℝ) : Summable (fun p : ℕ × ℕ =>
      (dyadicHarmonicWeight p.1 * scaledHarmonicLayer (a * (n + 1)) p.1 v) *
        (dyadicHarmonicWeight p.2 * scaledHarmonicLayer (c * (n + 1)) p.2 ((r : ℝ) * v))) :=
    summable_harmonicPairMajorant.of_norm_bounded fun p => by
      rw [Real.norm_eq_abs]; exact hpt_bd p v
  have h := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun (p : ℕ × ℕ) (v : ℝ) => v ^ (-2 : ℝ) *
      ((dyadicHarmonicWeight p.1 * scaledHarmonicLayer (a * (n + 1)) p.1 v) *
        (dyadicHarmonicWeight p.2 * scaledHarmonicLayer (c * (n + 1)) p.2 ((r : ℝ) * v))))
    (f := fun v : ℝ => v ^ (-2 : ℝ) *
      ((-(Real.pi ^ 2 / 2) * factorialPhaseProfile (a * (n + 1)) v) *
        (-(Real.pi ^ 2 / 2) * factorialPhaseProfile (c * (n + 1)) ((r : ℝ) * v))))
    (fun p v => harmonicPairMajorant p * v ^ (-2 : ℝ))
    (fun p => hw.aestronglyMeasurable.mul
      ((by unfold scaledHarmonicLayer; fun_prop : Continuous fun v =>
        (dyadicHarmonicWeight p.1 * scaledHarmonicLayer (a * (n + 1)) p.1 v) *
          (dyadicHarmonicWeight p.2 * scaledHarmonicLayer (c * (n + 1)) p.2 ((r : ℝ) * v))).aestronglyMeasurable))
    (by
      intro p
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hv.le) _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hv0, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hpt_bd p v) hv0)
    (Eventually.of_forall fun v => summable_harmonicPairMajorant.mul_right (v ^ (-2 : ℝ)))
    (by simpa only [tsum_mul_right] using hw.const_mul (∑' p, harmonicPairMajorant p))
    (Eventually.of_forall fun v =>
      ((scaledHarmonicLayer_hasSum (a * (n + 1)) v).mul
        (scaledHarmonicLayer_hasSum (c * (n + 1)) ((r : ℝ) * v)) (hs v)).mul_left (v ^ (-2 : ℝ)))
  have hfun : HasSum (fun p : ℕ × ℕ => dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      scaledLayerCrossCorr a c n p.1 p.2 r)
      (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
        ((-(Real.pi ^ 2 / 2) * factorialPhaseProfile (a * (n + 1)) v) *
          (-(Real.pi ^ 2 / 2) * factorialPhaseProfile (c * (n + 1)) ((r : ℝ) * v)))) := by
    refine h.congr_fun fun p => ?_
    unfold scaledLayerCrossCorr
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    ring
  have hval : (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
      ((-(Real.pi ^ 2 / 2) * factorialPhaseProfile (a * (n + 1)) v) *
        (-(Real.pi ^ 2 / 2) * factorialPhaseProfile (c * (n + 1)) ((r : ℝ) * v)))) =
      (Real.pi ^ 4 / 4) * scaleRatioCorrelation a c n r := by
    unfold scaleRatioCorrelation
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    ring
  rwa [hval] at hfun

/-- **Commensurable Scale-Ratio Correlation Limit Theorem.**
For any positive integers `a, c, r ≥ 1`, as `n → ∞`, the critical physical cross-correlation
between scales `a(n+1)` and `c(n+1)` at dilation `r` converges to `scaleRatioCorrelationLimit a c r`. -/
theorem scaleRatioCorrelation_tendsto {a c r : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => scaleRatioCorrelation a c n r) atTop
      (𝓝 (scaleRatioCorrelationLimit a c r)) := by
  have hterm (p : ℕ × ℕ) : Tendsto (fun n : ℕ =>
      dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
        scaledLayerCrossCorr a c n p.1 p.2 r) atTop
      (𝓝 (if p.1 * a = r * p.2 * c then
        dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
          slowPhasePolarization p.1 (r * p.2) else 0)) := by
    rcases Nat.eq_zero_or_pos p.1 with hk0 | hk
    · simp only [hk0, dyadicHarmonicWeight_zero, zero_mul, ite_self]
      exact tendsto_const_nhds
    rcases Nat.eq_zero_or_pos p.2 with hl0 | hl
    · simp only [hl0, dyadicHarmonicWeight_zero, mul_zero, zero_mul, ite_self]
      exact tendsto_const_nhds
    have ht := (scaledLayerCrossCorr_tendsto ha hc hk hl hr).const_mul
      (dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2)
    simpa only [mul_ite, mul_zero] using ht
  have hdom (n : ℕ) (p : ℕ × ℕ) :
      ‖dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
        scaledLayerCrossCorr a c n p.1 p.2 r‖ ≤ harmonicPairMajorant p := by
    unfold harmonicPairMajorant
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_scaledLayerCrossCorr_le a c n p.1 p.2 r) (by positivity)
  have h := (tendsto_tsum_of_dominated_convergence summable_harmonicPairMajorant hterm
    (Eventually.of_forall hdom)).const_mul (4 / Real.pi ^ 4)
  refine h.congr fun n => ?_
  rw [(scaleRatioCorrelation_hasSum a c n r).tsum_eq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- Endpoint pair `{M - 1, 2M - 1}` of the dyadic block `[M, 2M]`. -/
def dyadicPairSupport (M : ℕ) : Finset ℕ := {M - 1, 2 * M - 1}

theorem dyadicPairSupport_dyadicScaleBlock {M : ℕ} (hM : 1 ≤ M) :
    DyadicScaleBlock (dyadicPairSupport M) M := by
  intro n hn
  simp only [dyadicPairSupport, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl <;> omega

/-- Limiting correlation of the dyadic endpoint pair `{M - 1, 2M - 1}` with unit weights at
integer dilation `r`. -/
def dyadicPairCorrelationLimit (r : ℕ) : ℝ :=
  2 * factorialCriticalCorrelationLimit r +
    scaleRatioCorrelationLimit 2 1 r + scaleRatioCorrelationLimit 1 2 r

/-- Limiting uncollared critical prime energy of the dyadic endpoint pair `{M - 1, 2M - 1}` with
unit weights. -/
def dyadicPairPrimeLimit : ℝ :=
  ∑' r : ℕ, if 2 ≤ r then
    (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) * dyadicPairCorrelationLimit r else 0

private theorem dyadicPairCorrelation_tendsto {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ =>
      ∫ v in Ioi (1 : ℝ), criticalWindowWeight v *
        (realPhaseCombination (dyadicPairSupport (n + 2)) (fun _ => 1) v *
          realPhaseCombination (dyadicPairSupport (n + 2)) (fun _ => 1) ((r : ℝ) * v)))
      atTop (𝓝 (dyadicPairCorrelationLimit r)) := by
  have h1 : Tendsto (fun n : ℕ => factorialCriticalCorrelation (n + 1) r) atTop
      (𝓝 (factorialCriticalCorrelationLimit r)) :=
    (factorialCriticalCorrelation_tendsto r hr).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => factorialCriticalCorrelation (2 * n + 3) r) atTop
      (𝓝 (factorialCriticalCorrelationLimit r)) := by
    have hinj : Tendsto (fun n : ℕ => 2 * n + 3) atTop atTop :=
      (tendsto_add_atTop_nat 3).comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    exact (factorialCriticalCorrelation_tendsto r hr).comp hinj
  have h21 : Tendsto (fun n : ℕ => scaleRatioCorrelation 2 1 (n + 1) r) atTop
      (𝓝 (scaleRatioCorrelationLimit 2 1 r)) :=
    (scaleRatioCorrelation_tendsto (by norm_num) le_rfl hr).comp (tendsto_add_atTop_nat 1)
  have h12 : Tendsto (fun n : ℕ => scaleRatioCorrelation 1 2 (n + 1) r) atTop
      (𝓝 (scaleRatioCorrelationLimit 1 2 r)) :=
    (scaleRatioCorrelation_tendsto le_rfl (by norm_num) hr).comp (tendsto_add_atTop_nat 1)
  have hsum := ((h1.add h2).add h21).add h12
  have hlim_eq : factorialCriticalCorrelationLimit r + factorialCriticalCorrelationLimit r +
      scaleRatioCorrelationLimit 2 1 r + scaleRatioCorrelationLimit 1 2 r =
      dyadicPairCorrelationLimit r := by
    unfold dyadicPairCorrelationLimit; ring
  rw [hlim_eq] at hsum
  refine hsum.congr fun n => ?_
  have hpair : dyadicPairSupport (n + 2) = {n + 1, 2 * n + 3} := by
    ext m; simp only [dyadicPairSupport, Finset.mem_insert, Finset.mem_singleton]; omega
  have hne : n + 1 ≠ 2 * n + 3 := by omega
  have hcomb (w : ℝ) : realPhaseCombination (dyadicPairSupport (n + 2)) (fun _ => 1) w =
      factorialPhaseProfile (n + 2) w + factorialPhaseProfile (2 * (n + 2)) w := by
    rw [hpair]
    unfold realPhaseCombination
    rw [Finset.sum_pair hne]
    simp only [one_mul, show n + 1 + 1 = n + 2 by omega,
      show 2 * n + 3 + 1 = 2 * (n + 2) by omega]
  have hw : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hint (N1 N2 : ℕ) : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ) *
      factorialPhaseProfile N1 v * factorialPhaseProfile N2 ((r : ℝ) * v)) (Ioi 1) := by
    have hc : Continuous (fun v : ℝ =>
        factorialPhaseProfile N1 v * factorialPhaseProfile N2 ((r : ℝ) * v)) :=
      (continuous_factorialPhaseProfile N1).mul
        ((continuous_factorialPhaseProfile N2).comp (continuous_const.mul continuous_id))
    refine (hw.const_mul 4).mono' (hw.aestronglyMeasurable.mul hc.aestronglyMeasurable |>.congr
      (Eventually.of_forall fun v => by dsimp only [Pi.mul_apply]; ring)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hv.le) _
    rw [show v ^ (-2 : ℝ) * factorialPhaseProfile N1 v * factorialPhaseProfile N2 ((r : ℝ) * v) =
      v ^ (-2 : ℝ) * (factorialPhaseProfile N1 v * factorialPhaseProfile N2 ((r : ℝ) * v)) by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hv0, abs_mul]
    have hb1 := abs_factorialPhaseProfile_le N1 v
    have hb2 := abs_factorialPhaseProfile_le N2 ((r : ℝ) * v)
    have h4 : |factorialPhaseProfile N1 v| * |factorialPhaseProfile N2 ((r : ℝ) * v)| ≤ 4 :=
      (mul_le_mul hb1 hb2 (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    linarith [mul_le_mul_of_nonneg_left h4 hv0]
  have hi11 := hint (n + 2) (n + 2)
  have hi22 := hint (2 * (n + 2)) (2 * (n + 2))
  have hi21 := hint (2 * (n + 2)) (n + 2)
  have hi12 := hint (n + 2) (2 * (n + 2))
  have ha1 := integral_add hi11 hi22
  have ha2 := integral_add (hi11.add hi22) hi21
  have ha3 := integral_add ((hi11.add hi22).add hi21) hi12
  simp only [Pi.add_apply] at ha1 ha2 ha3
  unfold factorialCriticalCorrelation scaleRatioCorrelation criticalWindowWeight
  simp only [show n + 1 + 1 = n + 2 by omega, show 2 * n + 3 + 1 = 2 * (n + 2) by omega,
    one_mul]
  rw [← ha1, ← ha2, ← ha3]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [hcomb v, hcomb ((r : ℝ) * v)]
  ring

/-- **Convergence of the Uncollared Critical Prime Channel on Dyadic Endpoint Pairs.**
As `M → ∞`, `criticalPrimeEnergy (dyadicPairSupport M) (fun _ => 1)` converges unconditionally
to `dyadicPairPrimeLimit`. -/
theorem tendsto_criticalPrimeEnergy_dyadicPair :
    Tendsto (fun M : ℕ => criticalPrimeEnergy (dyadicPairSupport M) (fun _ => 1))
      atTop (𝓝 dyadicPairPrimeLimit) := by
  suffices hshift : Tendsto (fun n : ℕ =>
      criticalPrimeEnergy (dyadicPairSupport (n + 2)) (fun _ => 1))
      atTop (𝓝 dyadicPairPrimeLimit) by
    exact (tendsto_add_atTop_iff_nat 2).mp hshift
  have hdom (n r : ℕ) : ‖criticalPrimeAtom (dyadicPairSupport (n + 2)) (fun _ => 1) r‖ ≤
      1536 * envelopePrimeMajorant (3 / 2) r := by
    rw [Real.norm_eq_abs]
    have hdyad := dyadicPairSupport_dyadicScaleBlock (M := n + 2) (by omega)
    have hK := criticalFactorialPrimeConstant_le_of_dyadic (dyadicPairSupport (n + 2))
      (fun _ => 1) (M := n + 2) (by omega) hdyad
    have hcard : (∑ m ∈ dyadicPairSupport (n + 2), |(1 : ℝ)|) ≤ 2 := by
      have hp : dyadicPairSupport (n + 2) = {n + 1, 2 * n + 3} := by
        ext m; simp only [dyadicPairSupport, Finset.mem_insert, Finset.mem_singleton]; omega
      rw [hp, Finset.sum_pair (by omega)]
      norm_num
    have hK1536 : criticalFactorialPrimeConstant (dyadicPairSupport (n + 2)) (fun _ => 1) ≤ 1536 := by
      have hsq : (∑ m ∈ dyadicPairSupport (n + 2), |(1 : ℝ)|) ^ 2 ≤ 4 := by
        have h0 : 0 ≤ ∑ m ∈ dyadicPairSupport (n + 2), |(1 : ℝ)| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        nlinarith
      linarith
    exact (abs_criticalPrimeAtom_le _ _ r).trans
      (mul_le_mul_of_nonneg_right hK1536 (envelopePrimeMajorant_nonneg (3 / 2) r))
  have hterm (r : ℕ) : Tendsto (fun n : ℕ =>
      criticalPrimeAtom (dyadicPairSupport (n + 2)) (fun _ => 1) r) atTop
      (𝓝 (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        dyadicPairCorrelationLimit r else 0)) := by
    by_cases hr : 2 ≤ r
    · simp only [if_pos hr]
      have hc := (dyadicPairCorrelation_tendsto (by omega : 1 ≤ r)).const_mul
        ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ))
      exact hc.congr fun n => (criticalPrimeAtom_eq _ _ hr).symm
    · simp only [if_neg hr]
      refine tendsto_const_nhds.congr fun n => ?_
      unfold criticalPrimeAtom
      rw [if_neg hr, zero_mul]
  exact tendsto_tsum_of_dominated_convergence
    (summable_canonicalPrimeMajorant.mul_left 1536) hterm (Eventually.of_forall hdom)

/-! ### Exact Cancellation of the Negative Second Harmonic and Strict Positivity of the Dyadic Limit -/

private theorem dyadicHarmonicWeight_of_four_dvd {k : ℕ} (hk : 4 ∣ k) :
    dyadicHarmonicWeight k = 0 := by
  unfold dyadicHarmonicWeight
  rw [dyadicHarmonicChi_eq_indicator]
  have h2 : 2 ∣ k := dvd_trans (by norm_num : 2 ∣ 4) hk
  simp only [h2, hk, ite_true]
  norm_num

private theorem tsum_inv_pow_four_le :
    (∑' l : ℕ, (1 : ℝ) / (l : ℝ) ^ 4) ≤ 11 / 10 := by
  rw [hasSum_zeta_four.tsum_eq]
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos.le
  have h4 : Real.pi ^ 4 ≤ (3.15 : ℝ) ^ 4 := pow_le_pow_left₀ hpi0 hpi.le 4
  linarith

private theorem summable_cross21_term (r : ℕ) :
    Summable (fun p : ℕ × ℕ =>
      if p.1 * 2 = r * p.2 * 1 then
        dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
          slowPhasePolarization p.1 (r * p.2)
      else 0) := by
  refine summable_harmonicPairMajorant.of_norm_bounded fun p => ?_
  unfold harmonicPairMajorant
  split_ifs
  · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have hb := abs_slowPhasePolarization_le p.1 (r * p.2)
    have hw : 0 ≤ |dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2| := by positivity
    nlinarith
  · simp; positivity

private theorem scaleRatioCorrelationLimit_12_eq (r : ℕ) :
    scaleRatioCorrelationLimit 1 2 r = (4 / Real.pi ^ 4) * ∑' l : ℕ,
      dyadicHarmonicWeight (2 * r * l) * dyadicHarmonicWeight l *
        (factorialCriticalHarmonicDefect (2 * r * l) / 2) := by
  unfold scaleRatioCorrelationLimit
  congr 1
  set e : ℕ → ℕ × ℕ := fun l => (2 * r * l, l)
  have he : Function.Injective e := fun x y h => (Prod.ext_iff.mp h).2
  rw [← he.tsum_eq]
  · refine tsum_congr fun l => ?_
    dsimp only [e]
    have hres : 2 * r * l * 1 = r * l * 2 := by ring
    rw [if_pos hres, show 2 * r * l = 2 * (r * l) by ring, slowPhasePolarization_double_left]
  · intro p hp
    rw [Function.mem_support] at hp
    by_contra hnr
    apply hp
    rw [if_neg]
    intro hres
    exact hnr ⟨p.2, Prod.ext (by dsimp only [e]; linarith) rfl⟩

/-- At `r = 2`, the upward dyadic cross-correlation `scaleRatioCorrelationLimit 2 1 2` is at least
`(2 / π⁴) J_2`: all diagonal resonances `2 k = 2 l` (`k = l`) are nonnegative, and `k = l = 1`
contributes `(4 / π⁴) · 1² · (J_2 / 2) = (2 / π⁴) J_2`. -/
private theorem scaleRatioCorrelationLimit_21_two_ge :
    (2 / Real.pi ^ 4) * factorialCriticalHarmonicDefect 2 ≤
      scaleRatioCorrelationLimit 2 1 2 := by
  unfold scaleRatioCorrelationLimit
  have hs := summable_cross21_term 2
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ (if p.1 * 2 = 2 * p.2 * 1 then
      dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
        slowPhasePolarization p.1 (2 * p.2) else 0) := fun p => by
    split_ifs with h
    · have hp : p.1 = p.2 := by omega
      rw [hp, slowPhasePolarization_double_right]
      have hJ := (factorialCriticalHarmonicDefect_bounds (2 * p.2)).1
      nlinarith [sq_nonneg (dyadicHarmonicWeight p.2)]
    · exact le_rfl
  have h11 := hs.le_tsum ((1 : ℕ), (1 : ℕ)) fun p _ => hnn p
  simp only [ite_true, dyadicHarmonicWeight_one, one_mul,
    slowPhasePolarization_double_right 1] at h11
  have h4 : 0 ≤ 4 / Real.pi ^ 4 := by positivity
  calc (2 / Real.pi ^ 4) * factorialCriticalHarmonicDefect 2
      = (4 / Real.pi ^ 4) * (factorialCriticalHarmonicDefect 2 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h11 h4

private theorem scaleRatioCorrelationLimit_12_even_eq_zero {r : ℕ} (hr : 2 ∣ r) :
    scaleRatioCorrelationLimit 1 2 r = 0 := by
  rw [scaleRatioCorrelationLimit_12_eq]
  obtain ⟨m, rfl⟩ := hr
  have hz : ∀ l : ℕ, dyadicHarmonicWeight (2 * (2 * m) * l) * dyadicHarmonicWeight l *
      (factorialCriticalHarmonicDefect (2 * (2 * m) * l) / 2) = 0 := fun l => by
    rw [dyadicHarmonicWeight_of_four_dvd ⟨m * l, by ring⟩, zero_mul, zero_mul]
  simp [hz]

private theorem abs_scaleRatioCorrelationLimit_21_four_le :
    |scaleRatioCorrelationLimit 2 1 4| ≤ (11 / 10) / Real.pi ^ 4 := by
  unfold scaleRatioCorrelationLimit
  have hprod : (∑' p : ℕ × ℕ, if p.1 * 2 = 4 * p.2 * 1 then
      dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
        slowPhasePolarization p.1 (4 * p.2) else 0) =
      ∑' l : ℕ, dyadicHarmonicWeight (2 * l) * dyadicHarmonicWeight l *
        (factorialCriticalHarmonicDefect (4 * l) / 2) := by
    set e : ℕ → ℕ × ℕ := fun l => (2 * l, l)
    have he : Function.Injective e := fun x y h => (Prod.ext_iff.mp h).2
    rw [← he.tsum_eq]
    · refine tsum_congr fun l => ?_
      dsimp only [e]
      have hres : 2 * l * 2 = 4 * l * 1 := by ring
      rw [if_pos hres, show 4 * l = 2 * (2 * l) by ring, slowPhasePolarization_double_right]
    · intro p hp
      rw [Function.mem_support] at hp
      by_contra hnr
      apply hp
      rw [if_neg]
      intro hres
      exact hnr ⟨p.2, Prod.ext (by dsimp only [e]; omega) rfl⟩
  rw [hprod, abs_mul, abs_of_pos (by positivity : 0 < 4 / Real.pi ^ 4)]
  have hterm (l : ℕ) : ‖dyadicHarmonicWeight (2 * l) * dyadicHarmonicWeight l *
      (factorialCriticalHarmonicDefect (4 * l) / 2)‖ ≤ (1 / 4 : ℝ) * ((1 : ℝ) / (l : ℝ) ^ 4) := by
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hw1 := abs_dyadicHarmonicWeight_le (2 * l)
    have hw2 := abs_dyadicHarmonicWeight_le l
    have hJ : |factorialCriticalHarmonicDefect (4 * l) / 2| ≤ 1 := by
      obtain ⟨h0, h2⟩ := factorialCriticalHarmonicDefect_bounds (4 * l)
      rw [abs_of_nonneg (by linarith)]
      linarith
    calc |dyadicHarmonicWeight (2 * l)| * |dyadicHarmonicWeight l| *
          |factorialCriticalHarmonicDefect (4 * l) / 2|
        ≤ (1 / ((2 * l : ℕ) : ℝ) ^ 2) * (1 / (l : ℝ) ^ 2) * 1 := by
          gcongr
      _ = (1 / 4 : ℝ) * ((1 : ℝ) / (l : ℝ) ^ 4) := by push_cast; ring
  have hmaj : Summable (fun l : ℕ => (1 / 4 : ℝ) * ((1 : ℝ) / (l : ℝ) ^ 4)) :=
    hasSum_zeta_four.summable.mul_left (1 / 4)
  have hnorm : Summable (fun l : ℕ => ‖dyadicHarmonicWeight (2 * l) * dyadicHarmonicWeight l *
      (factorialCriticalHarmonicDefect (4 * l) / 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmaj
  have htsum : |∑' l : ℕ, dyadicHarmonicWeight (2 * l) * dyadicHarmonicWeight l *
      (factorialCriticalHarmonicDefect (4 * l) / 2)| ≤
      (1 / 4 : ℝ) * ∑' l : ℕ, (1 : ℝ) / (l : ℝ) ^ 4 := by
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hnorm).trans ?_
    refine (hnorm.tsum_le_tsum hterm hmaj).trans_eq ?_
    rw [tsum_mul_left]
  calc (4 / Real.pi ^ 4) * |∑' l : ℕ, dyadicHarmonicWeight (2 * l) * dyadicHarmonicWeight l *
        (factorialCriticalHarmonicDefect (4 * l) / 2)|
      ≤ (4 / Real.pi ^ 4) * ((1 / 4 : ℝ) * (11 / 10)) := by
        gcongr
        exact htsum.trans (mul_le_mul_of_nonneg_left tsum_inv_pow_four_le (by norm_num))
    _ = (11 / 10) / Real.pi ^ 4 := by ring

private theorem scaleRatioCorrelationLimit_21_eight_dvd_eq_zero {r : ℕ} (hr : 8 ∣ r) :
    scaleRatioCorrelationLimit 2 1 r = 0 := by
  unfold scaleRatioCorrelationLimit
  obtain ⟨q, rfl⟩ := hr
  have hz : ∀ p : ℕ × ℕ, (if p.1 * 2 = 8 * q * p.2 * 1 then
      dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
        slowPhasePolarization p.1 (8 * q * p.2) else 0) = 0 := fun p => by
    split_ifs with h
    · have h4 : 4 ∣ p.1 := ⟨q * p.2, by linarith⟩
      rw [dyadicHarmonicWeight_of_four_dvd h4, zero_mul, zero_mul]
    · rfl
  rw [tsum_congr hz, tsum_zero, mul_zero]

private theorem abs_scaleRatioCorrelationLimit_odd_le {r : ℕ} (hodd : ¬ 2 ∣ r) :
    |scaleRatioCorrelationLimit 2 1 r| + |scaleRatioCorrelationLimit 1 2 r| ≤
      (11 / (5 * (r : ℝ) ^ 2)) / Real.pi ^ 4 := by
  have hpi4 : 0 < 4 / Real.pi ^ 4 := by positivity
  -- Bound 1:2 cross-correlation
  have h12 : |scaleRatioCorrelationLimit 1 2 r| ≤ (11 / (10 * (r : ℝ) ^ 2)) / Real.pi ^ 4 := by
    rw [scaleRatioCorrelationLimit_12_eq, abs_mul, abs_of_pos hpi4]
    have hterm (l : ℕ) : ‖dyadicHarmonicWeight (2 * r * l) * dyadicHarmonicWeight l *
        (factorialCriticalHarmonicDefect (2 * r * l) / 2)‖ ≤
        (1 / (4 * (r : ℝ) ^ 2)) * ((1 : ℝ) / (l : ℝ) ^ 4) := by
      rcases Nat.eq_zero_or_pos l with rfl | hl
      · simp
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hw1 := abs_dyadicHarmonicWeight_le (2 * r * l)
      have hw2 := abs_dyadicHarmonicWeight_le l
      have hJ : |factorialCriticalHarmonicDefect (2 * r * l) / 2| ≤ 1 := by
        obtain ⟨h0, h2⟩ := factorialCriticalHarmonicDefect_bounds (2 * r * l)
        rw [abs_of_nonneg (by linarith)]; linarith
      calc |dyadicHarmonicWeight (2 * r * l)| * |dyadicHarmonicWeight l| *
            |factorialCriticalHarmonicDefect (2 * r * l) / 2|
          ≤ (1 / ((2 * r * l : ℕ) : ℝ) ^ 2) * (1 / (l : ℝ) ^ 2) * 1 := by gcongr
        _ = (1 / (4 * (r : ℝ) ^ 2)) * ((1 : ℝ) / (l : ℝ) ^ 4) := by push_cast; ring
    have hmaj : Summable (fun l : ℕ => (1 / (4 * (r : ℝ) ^ 2)) * ((1 : ℝ) / (l : ℝ) ^ 4)) :=
      hasSum_zeta_four.summable.mul_left _
    have hnorm : Summable (fun l : ℕ => ‖dyadicHarmonicWeight (2 * r * l) * dyadicHarmonicWeight l *
        (factorialCriticalHarmonicDefect (2 * r * l) / 2)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmaj
    have hts : |∑' l : ℕ, dyadicHarmonicWeight (2 * r * l) * dyadicHarmonicWeight l *
        (factorialCriticalHarmonicDefect (2 * r * l) / 2)| ≤
        (1 / (4 * (r : ℝ) ^ 2)) * (11 / 10) := by
      rw [← Real.norm_eq_abs]
      refine (norm_tsum_le_tsum_norm hnorm).trans ?_
      refine (hnorm.tsum_le_tsum hterm hmaj).trans ?_
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left tsum_inv_pow_four_le (by positivity)
    calc (4 / Real.pi ^ 4) * |_| ≤ (4 / Real.pi ^ 4) * ((1 / (4 * (r : ℝ) ^ 2)) * (11 / 10)) :=
          mul_le_mul_of_nonneg_left hts hpi4.le
      _ = (11 / (10 * (r : ℝ) ^ 2)) / Real.pi ^ 4 := by ring
  -- Bound 2:1 cross-correlation: when `¬ 2 ∣ r`, `k * 2 = r * l` forces `l = 2 * m` and `k = r * m`.
  have h21 : |scaleRatioCorrelationLimit 2 1 r| ≤ (11 / (10 * (r : ℝ) ^ 2)) / Real.pi ^ 4 := by
    unfold scaleRatioCorrelationLimit
    have hsub : (∑' p : ℕ × ℕ, if p.1 * 2 = r * p.2 * 1 then
        dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
          slowPhasePolarization p.1 (r * p.2) else 0) =
        ∑' m : ℕ, dyadicHarmonicWeight (r * m) * dyadicHarmonicWeight (2 * m) *
          (factorialCriticalHarmonicDefect (2 * r * m) / 2) := by
      set e : ℕ → ℕ × ℕ := fun m => (r * m, 2 * m)
      have he : Function.Injective e := fun x y h => by
        have h2 := (Prod.ext_iff.mp h).2
        dsimp only [e] at h2
        omega
      rw [← he.tsum_eq]
      · refine tsum_congr fun m => ?_
        dsimp only [e]
        have hres : r * m * 2 = r * (2 * m) * 1 := by ring
        rw [if_pos hres, show r * (2 * m) = 2 * (r * m) by ring,
          slowPhasePolarization_double_right, show 2 * (r * m) = 2 * r * m by ring]
      · intro p hp
        rw [Function.mem_support] at hp
        by_contra hnr
        apply hp
        rw [if_neg]
        intro hres
        have h2rl : 2 ∣ r * p.2 := ⟨p.1, by linarith⟩
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2rl with h2r | ⟨m, hm⟩
        · exact hodd h2r
        · exact hnr ⟨m, Prod.ext (by dsimp only [e]; rw [hm] at hres; linarith) hm.symm⟩
    rw [hsub, abs_mul, abs_of_pos hpi4]
    have hterm (m : ℕ) : ‖dyadicHarmonicWeight (r * m) * dyadicHarmonicWeight (2 * m) *
        (factorialCriticalHarmonicDefect (2 * r * m) / 2)‖ ≤
        (1 / (4 * (r : ℝ) ^ 2)) * ((1 : ℝ) / (m : ℝ) ^ 4) := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hw1 := abs_dyadicHarmonicWeight_le (r * m)
      have hw2 := abs_dyadicHarmonicWeight_le (2 * m)
      have hJ : |factorialCriticalHarmonicDefect (2 * r * m) / 2| ≤ 1 := by
        obtain ⟨h0, h2⟩ := factorialCriticalHarmonicDefect_bounds (2 * r * m)
        rw [abs_of_nonneg (by linarith)]; linarith
      calc |dyadicHarmonicWeight (r * m)| * |dyadicHarmonicWeight (2 * m)| *
            |factorialCriticalHarmonicDefect (2 * r * m) / 2|
          ≤ (1 / ((r * m : ℕ) : ℝ) ^ 2) * (1 / ((2 * m : ℕ) : ℝ) ^ 2) * 1 := by gcongr
        _ = (1 / (4 * (r : ℝ) ^ 2)) * ((1 : ℝ) / (m : ℝ) ^ 4) := by push_cast; ring
    have hmaj : Summable (fun m : ℕ => (1 / (4 * (r : ℝ) ^ 2)) * ((1 : ℝ) / (m : ℝ) ^ 4)) :=
      hasSum_zeta_four.summable.mul_left _
    have hnorm : Summable (fun m : ℕ => ‖dyadicHarmonicWeight (r * m) * dyadicHarmonicWeight (2 * m) *
        (factorialCriticalHarmonicDefect (2 * r * m) / 2)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmaj
    have hts : |∑' m : ℕ, dyadicHarmonicWeight (r * m) * dyadicHarmonicWeight (2 * m) *
        (factorialCriticalHarmonicDefect (2 * r * m) / 2)| ≤
        (1 / (4 * (r : ℝ) ^ 2)) * (11 / 10) := by
      rw [← Real.norm_eq_abs]
      refine (norm_tsum_le_tsum_norm hnorm).trans ?_
      refine (hnorm.tsum_le_tsum hterm hmaj).trans ?_
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left tsum_inv_pow_four_le (by positivity)
    calc (4 / Real.pi ^ 4) * |_| ≤ (4 / Real.pi ^ 4) * ((1 / (4 * (r : ℝ) ^ 2)) * (11 / 10)) :=
          mul_le_mul_of_nonneg_left hts hpi4.le
      _ = (11 / (10 * (r : ℝ) ^ 2)) / Real.pi ^ 4 := by ring
  calc |scaleRatioCorrelationLimit 2 1 r| + |scaleRatioCorrelationLimit 1 2 r|
      ≤ (11 / (10 * (r : ℝ) ^ 2)) / Real.pi ^ 4 + (11 / (10 * (r : ℝ) ^ 2)) / Real.pi ^ 4 :=
        add_le_add h21 h12
    _ = (11 / (5 * (r : ℝ) ^ 2)) / Real.pi ^ 4 := by ring

private theorem harmonicDefect_three_five_ge :
    13 / 10 ≤ factorialCriticalHarmonicDefect 3 ∧
      6 / 5 ≤ factorialCriticalHarmonicDefect 5 := by
  have hp_lo := Real.pi_gt_d2
  have hp_hi := Real.pi_lt_d2
  have hp0 := Real.pi_pos.le
  have ht3 := factorialCriticalHarmonicDefect_lower_taylor 3
  have ht5 := factorialCriticalHarmonicDefect_lower_taylor 5
  norm_num only [Nat.cast_ofNat] at ht3 ht5
  have hp2_lo : (3.14 : ℝ) ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) hp_lo.le 2
  have hp2_hi : Real.pi ^ 2 ≤ (3.15 : ℝ) ^ 2 := pow_le_pow_left₀ hp0 hp_hi.le 2
  have hp4_lo : (3.14 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) hp_lo.le 4
  have hp6_hi : Real.pi ^ 6 ≤ (3.15 : ℝ) ^ 6 := pow_le_pow_left₀ hp0 hp_hi.le 6
  have h3_alg : Real.pi ^ 2 * 3 / 12 - (Real.pi * 3 / 6) ^ 2 / 2 +
      (Real.pi * 3 / 6) ^ 4 / 72 - (Real.pi * 3 / 6) ^ 6 / 3600 =
      Real.pi ^ 2 / 8 + Real.pi ^ 4 / 1152 - Real.pi ^ 6 / 230400 := by ring
  have h5_alg : Real.pi ^ 2 * 5 / 12 - (Real.pi * 5 / 6) ^ 2 / 2 +
      (Real.pi * 5 / 6) ^ 4 / 72 - (Real.pi * 5 / 6) ^ 6 / 3600 =
      5 * Real.pi ^ 2 / 72 + 625 * Real.pi ^ 4 / 93312 -
        15625 * Real.pi ^ 6 / 167961600 := by ring
  rw [h3_alg] at ht3
  rw [h5_alg] at ht5
  constructor <;> linarith

private theorem even_ge_six_cross_vanish {r : ℕ} (hr6 : 6 ≤ r) (h2 : 2 ∣ r) :
    (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
      (scaleRatioCorrelationLimit 2 1 r + scaleRatioCorrelationLimit 1 2 r) = 0 := by
  by_cases hpp : IsPrimePow r
  · obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp_nat : Nat.Prime p := hp.nat_prime
    have hp2 : p = 2 := by
      have hdvd : 2 ∣ p ^ k := h2
      have h2p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
      exact ((hp_nat.eq_one_or_self_of_dvd 2 h2p).resolve_left (by norm_num)).symm
    subst hp2
    have hk3 : 3 ≤ k := by
      by_contra hlt
      have : 2 ^ k ≤ 4 := by interval_cases k <;> norm_num
      omega
    have h8 : 8 ∣ 2 ^ k := by
      obtain ⟨d, rfl⟩ : ∃ d, k = 3 + d := ⟨k - 3, by omega⟩
      rw [pow_add]
      exact ⟨2 ^ d, by ring⟩
    rw [scaleRatioCorrelationLimit_21_eight_dvd_eq_zero h8,
      scaleRatioCorrelationLimit_12_even_eq_zero h2, add_zero, mul_zero]
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, zero_div, zero_mul]

private theorem summable_and_tsum_cross_tail_seven_le :
    Summable (fun m : ℕ =>
      |((ArithmeticFunction.vonMangoldt (m + 7) : ℝ) / ((m + 7 : ℕ) : ℝ)) *
        (scaleRatioCorrelationLimit 2 1 (m + 7) + scaleRatioCorrelationLimit 1 2 (m + 7))|) ∧
    (∑' m : ℕ, |((ArithmeticFunction.vonMangoldt (m + 7) : ℝ) / ((m + 7 : ℕ) : ℝ)) *
      (scaleRatioCorrelationLimit 2 1 (m + 7) + scaleRatioCorrelationLimit 1 2 (m + 7))|) ≤
      (11 / 5) * (18 / 49 + 3 / 32) * (1 / 6) * (Real.log 2 / Real.pi ^ 4) := by
  have hlog2_lo : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_hi : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi4 : 0 < Real.pi ^ 4 := by positivity
  set C : ℝ := (11 / 5) * (18 / 49 + 3 / 32) * (Real.log 2 / Real.pi ^ 4)
  have hC : 0 ≤ C := by positivity
  have hterm (m : ℕ) :
      |((ArithmeticFunction.vonMangoldt (m + 7) : ℝ) / ((m + 7 : ℕ) : ℝ)) *
        (scaleRatioCorrelationLimit 2 1 (m + 7) + scaleRatioCorrelationLimit 1 2 (m + 7))| ≤
        C * (1 / ((m + 6 : ℕ) : ℝ) - 1 / ((m + 7 : ℕ) : ℝ)) ∧
      C * (1 / ((m + 6 : ℕ) : ℝ) - 1 / ((m + 7 : ℕ) : ℝ)) ≤
        C * (1 / ((m + 6 : ℕ) : ℝ) ^ 2) := by
    set r : ℕ := m + 7
    have hr7 : 7 ≤ r := by omega
    have hrR : (7 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr7
    have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
    have hm6 : (0 : ℝ) < ((m + 6 : ℕ) : ℝ) := by positivity
    have hm7 : ((m + 7 : ℕ) : ℝ) = ((m + 6 : ℕ) : ℝ) + 1 := by push_cast; ring
    have htele : 1 / (r : ℝ) ^ 2 ≤ 1 / ((m + 6 : ℕ) : ℝ) - 1 / ((m + 7 : ℕ) : ℝ) := by
      have hr_eq : (r : ℝ) = ((m + 6 : ℕ) : ℝ) + 1 := hm7
      have hdiff : 1 / ((m + 6 : ℕ) : ℝ) - 1 / (((m + 6 : ℕ) : ℝ) + 1) =
          1 / (((m + 6 : ℕ) : ℝ) * (((m + 6 : ℕ) : ℝ) + 1)) := by field_simp; ring
      rw [hr_eq, hdiff]
      refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
      nlinarith
    have htele_up : 1 / ((m + 6 : ℕ) : ℝ) - 1 / ((m + 7 : ℕ) : ℝ) ≤
        1 / ((m + 6 : ℕ) : ℝ) ^ 2 := by
      have hdiff : 1 / ((m + 6 : ℕ) : ℝ) - 1 / (((m + 6 : ℕ) : ℝ) + 1) =
          1 / (((m + 6 : ℕ) : ℝ) * (((m + 6 : ℕ) : ℝ) + 1)) := by field_simp; ring
      rw [hm7, hdiff]
      refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
      nlinarith
    refine ⟨?_, mul_le_mul_of_nonneg_left htele_up hC⟩
    by_cases h2 : 2 ∣ r
    · rw [even_ge_six_cross_vanish (by omega : 6 ≤ r) h2, abs_zero]
      exact mul_nonneg hC (le_trans (by positivity : (0 : ℝ) ≤ 1 / (r : ℝ) ^ 2) htele)
    · rw [abs_mul, abs_of_nonneg (vonMangoldt_div_nonneg r)]
      have hcr := (abs_add_le _ _).trans (abs_scaleRatioCorrelationLimit_odd_le h2)
      have hvm := vonMangoldt_div_le_log_div r
      have hlogr : Real.log (r : ℝ) ≤ (18 / 7 + (3 / 32) * (r : ℝ)) * Real.log 2 := by
        have hdiv : Real.log ((r : ℝ) / 16) ≤ (r : ℝ) / 16 - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have hsplit : Real.log (r : ℝ) = 4 * Real.log 2 + Real.log ((r : ℝ) / 16) := by
          rw [Real.log_div hr0.ne' (by norm_num),
            show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
          push_cast; ring
        have h1 : (10 / 7 : ℝ) * Real.log 2 ≤ 1 := by linarith
        have h2' : (1 / 16 : ℝ) ≤ (3 / 32) * Real.log 2 := by linarith
        nlinarith [mul_le_mul_of_nonneg_right h2' hr0.le]
      have hlog_div : Real.log (r : ℝ) / (r : ℝ) ^ 3 ≤
          (18 / 49 + 3 / 32) * Real.log 2 * (1 / (r : ℝ) ^ 2) := by
        rw [div_le_iff₀ (by positivity)]
        have h_alg : (18 / 49 + 3 / 32) * Real.log 2 * (1 / (r : ℝ) ^ 2) * (r : ℝ) ^ 3 =
            ((18 / 49) * (r : ℝ) + (3 / 32) * (r : ℝ)) * Real.log 2 := by
          field_simp
        rw [h_alg]
        have hr_ge : (18 / 7 : ℝ) ≤ (18 / 49) * (r : ℝ) := by linarith
        nlinarith
      calc (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
            |scaleRatioCorrelationLimit 2 1 r + scaleRatioCorrelationLimit 1 2 r|
          ≤ (Real.log (r : ℝ) / (r : ℝ)) * ((11 / (5 * (r : ℝ) ^ 2)) / Real.pi ^ 4) :=
            mul_le_mul hvm hcr (abs_nonneg _) (by positivity)
        _ = (11 / (5 * Real.pi ^ 4)) * (Real.log (r : ℝ) / (r : ℝ) ^ 3) := by ring
        _ ≤ (11 / (5 * Real.pi ^ 4)) *
            ((18 / 49 + 3 / 32) * Real.log 2 * (1 / (r : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hlog_div (by positivity)
        _ = C * (1 / (r : ℝ) ^ 2) := by simp only [C]; ring
        _ ≤ C * (1 / ((m + 6 : ℕ) : ℝ) - 1 / ((m + 7 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left htele hC
  have hsq_sum : Summable (fun m : ℕ => C * (1 / ((m + 6 : ℕ) : ℝ) ^ 2)) :=
    ((summable_nat_add_iff 6).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left C
  have hs : Summable (fun m : ℕ =>
      |((ArithmeticFunction.vonMangoldt (m + 7) : ℝ) / ((m + 7 : ℕ) : ℝ)) *
        (scaleRatioCorrelationLimit 2 1 (m + 7) + scaleRatioCorrelationLimit 1 2 (m + 7))|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun m => (hterm m).1.trans (hterm m).2) hsq_sum
  have htele_id : ∀ K : ℕ, (∑ m ∈ Finset.range K,
      (1 / ((m + 6 : ℕ) : ℝ) - 1 / ((m + 7 : ℕ) : ℝ))) =
      1 / 6 - 1 / ((K + 6 : ℕ) : ℝ) := by
    intro K
    induction K with
    | zero => norm_num
    | succ K ihK =>
      rw [Finset.sum_range_succ, ihK]
      push_cast; ring
  refine ⟨hs, hs.tsum_le_of_sum_range_le fun N => ?_⟩
  have htele_le : (∑ m ∈ Finset.range N,
      (1 / ((m + 6 : ℕ) : ℝ) - 1 / ((m + 7 : ℕ) : ℝ))) ≤ 1 / 6 := by
    rw [htele_id N]
    have : 0 ≤ 1 / ((N + 6 : ℕ) : ℝ) := by positivity
    linarith
  calc (∑ m ∈ Finset.range N, _)
      ≤ ∑ m ∈ Finset.range N, C * (1 / ((m + 6 : ℕ) : ℝ) - 1 / ((m + 7 : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun m _ => (hterm m).1
    _ = C * ∑ m ∈ Finset.range N, (1 / ((m + 6 : ℕ) : ℝ) - 1 / ((m + 7 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ C * (1 / 6) := mul_le_mul_of_nonneg_left htele_le hC
    _ = (11 / 5) * (18 / 49 + 3 / 32) * (1 / 6) * (Real.log 2 / Real.pi ^ 4) := by
        simp only [C]; ring

/-- **Strict Positivity of the Dyadic Endpoint-Pair Prime Limit.**
The limiting uncollared critical prime energy of `{M - 1, 2M - 1}` with unit weights satisfies
`dyadicPairPrimeLimit ≥ (1 / 8) * (Real.log 2 / Real.pi ^ 4) > 0`. -/
theorem dyadicPairPrimeLimit_ge :
    (1 / 8) * (Real.log 2 / Real.pi ^ 4) ≤ dyadicPairPrimeLimit ∧
      0 < dyadicPairPrimeLimit := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi4_pos : 0 < Real.pi ^ 4 := by positivity
  suffices hge : (1 / 8) * (Real.log 2 / Real.pi ^ 4) ≤ dyadicPairPrimeLimit by
    exact ⟨hge, lt_of_lt_of_le (by positivity) hge⟩
  -- 1. Split `dyadicPairPrimeLimit` into `2 * factorialCriticalPrimeLimit` plus the cross series
  have hs_diag : Summable (fun r : ℕ => if 2 ≤ r then
      (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        factorialCriticalCorrelationLimit r else 0) :=
    summable_abs_iff.mp summable_factorialCriticalPrimeLimit_atoms
  have hs_pair : Summable (fun r : ℕ => if 2 ≤ r then
      (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        dyadicPairCorrelationLimit r else 0) := by
    have hdom (r : ℕ) : ‖if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        dyadicPairCorrelationLimit r else 0‖ ≤ 1536 * envelopePrimeMajorant (3 / 2) r := by
      have hlim : Tendsto (fun n : ℕ =>
          criticalPrimeAtom (dyadicPairSupport (n + 2)) (fun _ => 1) r) atTop
          (𝓝 (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
            dyadicPairCorrelationLimit r else 0)) := by
        by_cases hr : 2 ≤ r
        · simp only [if_pos hr]
          exact ((dyadicPairCorrelation_tendsto (by omega)).const_mul _).congr
            fun n => (criticalPrimeAtom_eq _ _ hr).symm
        · simp only [if_neg hr]
          refine tendsto_const_nhds.congr fun n => ?_
          unfold criticalPrimeAtom; rw [if_neg hr, zero_mul]
      refine le_of_tendsto hlim.norm (Eventually.of_forall fun n => ?_)
      rw [Real.norm_eq_abs]
      have hdyad := dyadicPairSupport_dyadicScaleBlock (M := n + 2) (by omega)
      have hK := criticalFactorialPrimeConstant_le_of_dyadic (dyadicPairSupport (n + 2))
        (fun _ => 1) (M := n + 2) (by omega) hdyad
      have hcard : (∑ m ∈ dyadicPairSupport (n + 2), |(1 : ℝ)|) ≤ 2 := by
        have hp : dyadicPairSupport (n + 2) = {n + 1, 2 * n + 3} := by
          ext m; simp only [dyadicPairSupport, Finset.mem_insert, Finset.mem_singleton]; omega
        rw [hp, Finset.sum_pair (by omega)]
        norm_num
      have hsq : (∑ m ∈ dyadicPairSupport (n + 2), |(1 : ℝ)|) ^ 2 ≤ 4 := by
        have h0 : 0 ≤ ∑ m ∈ dyadicPairSupport (n + 2), |(1 : ℝ)| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        nlinarith
      exact (abs_criticalPrimeAtom_le _ _ r).trans
        (mul_le_mul_of_nonneg_right (by linarith) (envelopePrimeMajorant_nonneg (3 / 2) r))
    exact (summable_canonicalPrimeMajorant.mul_left 1536).of_norm_bounded hdom
  set crossAtom : ℕ → ℝ := fun r => if 2 ≤ r then
    (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
      (scaleRatioCorrelationLimit 2 1 r + scaleRatioCorrelationLimit 1 2 r) else 0
  have hcross_eq : ∀ r : ℕ, crossAtom r =
      (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        dyadicPairCorrelationLimit r else 0) -
      2 * (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        factorialCriticalCorrelationLimit r else 0) := fun r => by
    unfold crossAtom dyadicPairCorrelationLimit
    split_ifs <;> ring
  have hs_cross : Summable crossAtom :=
    (hs_pair.sub (hs_diag.mul_left 2)).congr fun r => (hcross_eq r).symm
  have hsplit_limit : dyadicPairPrimeLimit =
      2 * factorialCriticalPrimeLimit + ∑' r : ℕ, crossAtom r := by
    unfold dyadicPairPrimeLimit factorialCriticalPrimeLimit
    rw [← tsum_mul_left, ← (hs_diag.mul_left 2).tsum_add hs_cross]
    refine tsum_congr fun r => ?_
    rw [hcross_eq r]
    ring
  -- 2. Lower bound `2 * factorialCriticalPrimeLimit` retaining `m = 2, 3, 5` and dropping `m ≥ 6` (`≥ 0`)
  have hdiag_ge : 2 * factorialCriticalPrimeLimit ≥
      -(Real.log 2 / Real.pi ^ 4) * factorialCriticalHarmonicDefect 2 +
      (88 / 189 * (13 / 10) + 128 / 875 * (6 / 5)) * (Real.log 2 / Real.pi ^ 4) := by
    rw [factorialCriticalPrimeLimit_eq_harmonic_diagonal]
    have hs_harm : Summable (fun m : ℕ =>
        factorialCriticalPrimeHarmonicCharge m *
          factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4) :=
      summable_abs_iff.mp summable_factorialCriticalPrimeHarmonicCharge
    rw [← hs_harm.sum_add_tsum_nat_add 6]
    have htail_nn : 0 ≤ ∑' m : ℕ,
        factorialCriticalPrimeHarmonicCharge (m + 6) *
          factorialCriticalHarmonicDefect (m + 6) / ((m + 6 : ℕ) : ℝ) ^ 4 := by
      refine tsum_nonneg fun m => div_nonneg (mul_nonneg ?_
        (factorialCriticalHarmonicDefect_bounds (m + 6)).1) (by positivity)
      exact le_of_not_gt fun h =>
        (by omega : m + 6 ≠ 2) ((factorialCriticalPrimeHarmonicCharge_sign (m + 6)).1.mp h)
    have hA0 : factorialCriticalPrimeHarmonicCharge 0 = 0 :=
      (factorialCriticalPrimeHarmonicCharge_sign 0).2.1.mpr (Or.inr (by norm_num))
    have hA1 : factorialCriticalPrimeHarmonicCharge 1 = 0 :=
      (factorialCriticalPrimeHarmonicCharge_sign 1).2.1.mpr (Or.inl rfl)
    have hA2 := factorialCriticalPrimeHarmonicCharge_two
    have hA3 : factorialCriticalPrimeHarmonicCharge 3 = 3 * Real.log 3 :=
      factorialCriticalPrimeHarmonicCharge_odd_prime (by norm_num) (by norm_num)
    have hA4 : factorialCriticalPrimeHarmonicCharge 4 = 0 :=
      (factorialCriticalPrimeHarmonicCharge_sign 4).2.1.mpr (Or.inr (by norm_num))
    have hA5 : factorialCriticalPrimeHarmonicCharge 5 = 5 * Real.log 5 :=
      factorialCriticalPrimeHarmonicCharge_odd_prime (by norm_num) (by norm_num)
    have hlog3 : (11 / 7) * Real.log 2 ≤ Real.log 3 := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 11)
        (by norm_num : (2 : ℝ) ^ 11 ≤ 3 ^ 7)
      simp only [Real.log_pow, Nat.cast_ofNat] at h
      linarith
    have hlog5 : (16 / 7) * Real.log 2 ≤ Real.log 5 := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 16)
        (by norm_num : (2 : ℝ) ^ 16 ≤ 5 ^ 7)
      simp only [Real.log_pow, Nat.cast_ofNat] at h
      linarith
    obtain ⟨hJ3, hJ5⟩ := harmonicDefect_three_five_ge
    have hm3 : 3 * Real.log 3 * factorialCriticalHarmonicDefect 3 / (3 : ℝ) ^ 4 ≥
        (11 / 189) * (13 / 10) * Real.log 2 := by
      have h1 : 3 * ((11 / 7) * Real.log 2) * (13 / 10) ≤
          3 * Real.log 3 * factorialCriticalHarmonicDefect 3 := by
        nlinarith [mul_le_mul hlog3 hJ3 (by norm_num) (by linarith)]
      norm_num only
      linarith
    have hm5 : 5 * Real.log 5 * factorialCriticalHarmonicDefect 5 / (5 : ℝ) ^ 4 ≥
        (16 / 875) * (6 / 5) * Real.log 2 := by
      have h1 : 5 * ((16 / 7) * Real.log 2) * (6 / 5) ≤
          5 * Real.log 5 * factorialCriticalHarmonicDefect 5 := by
        nlinarith [mul_le_mul hlog5 hJ5 (by norm_num) (by linarith)]
      norm_num only
      linarith
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, hA0, hA1, hA2, hA3, hA4, hA5,
      zero_mul, zero_div, zero_add, add_zero, Nat.cast_ofNat]
    have hsum6 : -2 * Real.log 2 * factorialCriticalHarmonicDefect 2 / 16 +
        3 * Real.log 3 * factorialCriticalHarmonicDefect 3 / 81 +
        5 * Real.log 5 * factorialCriticalHarmonicDefect 5 / 625 +
        ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge (m + 6) *
          factorialCriticalHarmonicDefect (m + 6) / ((m + 6 : ℕ) : ℝ) ^ 4 ≥
        -(1 / 8) * Real.log 2 * factorialCriticalHarmonicDefect 2 +
        ((11 / 189) * (13 / 10) + (16 / 875) * (6 / 5)) * Real.log 2 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum6 (show 0 ≤ 2 * (4 / Real.pi ^ 4) by positivity)
    have h_alg_rhs : 2 * ((4 / Real.pi ^ 4) *
        (-2 * Real.log 2 * factorialCriticalHarmonicDefect 2 / 16 +
          3 * Real.log 3 * factorialCriticalHarmonicDefect 3 / 81 +
          5 * Real.log 5 * factorialCriticalHarmonicDefect 5 / 625 +
          ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge (m + 6) *
            factorialCriticalHarmonicDefect (m + 6) / ((m + 6 : ℕ) : ℝ) ^ 4)) =
        2 * (4 / Real.pi ^ 4) *
        (-2 * Real.log 2 * factorialCriticalHarmonicDefect 2 / 16 +
          3 * Real.log 3 * factorialCriticalHarmonicDefect 3 / 81 +
          5 * Real.log 5 * factorialCriticalHarmonicDefect 5 / 625 +
          ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge (m + 6) *
            factorialCriticalHarmonicDefect (m + 6) / ((m + 6 : ℕ) : ℝ) ^ 4) := by ring
    change _ ≤ _
    rw [h_alg_rhs]
    refine le_trans ?_ hmul
    exact le_of_eq (by ring)
  -- 3. Lower bound `∑' r, crossAtom r` splitting at `r = 7`
  have hcross_ge : ∑' r : ℕ, crossAtom r ≥
      (Real.log 2 / Real.pi ^ 4) * factorialCriticalHarmonicDefect 2 -
      (11 / 40 + 88 / 675 + 77 / 1875 +
        (11 / 5) * (18 / 49 + 3 / 32) * (1 / 6)) * (Real.log 2 / Real.pi ^ 4) := by
    rw [← hs_cross.sum_add_tsum_nat_add 7]
    have hc0 : crossAtom 0 = 0 := by simp [crossAtom]
    have hc1 : crossAtom 1 = 0 := by simp [crossAtom]
    have hc6 : crossAtom 6 = 0 := by
      simp only [crossAtom, show (2 : ℕ) ≤ 6 by norm_num, ite_true]
      exact even_ge_six_cross_vanish le_rfl ⟨3, rfl⟩
    have hc2 : crossAtom 2 ≥ (Real.log 2 / Real.pi ^ 4) * factorialCriticalHarmonicDefect 2 := by
      simp only [crossAtom, le_rfl, ite_true,
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
        scaleRatioCorrelationLimit_12_even_eq_zero (dvd_refl 2), add_zero, Nat.cast_ofNat]
      have h21 := scaleRatioCorrelationLimit_21_two_ge
      calc (Real.log 2 / Real.pi ^ 4) * factorialCriticalHarmonicDefect 2
          = (Real.log 2 / 2) * ((2 / Real.pi ^ 4) * factorialCriticalHarmonicDefect 2) := by ring
        _ ≤ (Real.log 2 / 2) * scaleRatioCorrelationLimit 2 1 2 :=
            mul_le_mul_of_nonneg_left h21 (by positivity)
    have hc3 : crossAtom 3 ≥ -(88 / 675) * (Real.log 2 / Real.pi ^ 4) := by
      have hlog3 : Real.log 3 ≤ (8 / 5) * Real.log 2 := by
        have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 5)
          (by norm_num : (3 : ℝ) ^ 5 ≤ 2 ^ 8)
        simp only [Real.log_pow, Nat.cast_ofNat] at h; linarith
      have habs : |crossAtom 3| ≤ (88 / 675) * (Real.log 2 / Real.pi ^ 4) := by
        simp only [crossAtom, show (2 : ℕ) ≤ 3 by norm_num, ite_true,
          ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3), Nat.cast_ofNat]
        rw [abs_mul, abs_of_nonneg (by positivity)]
        have hodd := (abs_add_le _ _).trans (abs_scaleRatioCorrelationLimit_odd_le (r := 3) (by omega))
        push_cast at hodd
        have hdiv3 : Real.log 3 / 3 ≤ (8 / 5 * Real.log 2) / 3 :=
          div_le_div_of_nonneg_right hlog3 (by norm_num)
        calc (Real.log 3 / 3) * |scaleRatioCorrelationLimit 2 1 3 + scaleRatioCorrelationLimit 1 2 3|
            ≤ ((8 / 5 * Real.log 2) / 3) * ((11 / (5 * 3 ^ 2)) / Real.pi ^ 4) :=
              mul_le_mul hdiv3 hodd (abs_nonneg _) (by positivity)
          _ = (88 / 675) * (Real.log 2 / Real.pi ^ 4) := by ring
      linarith [neg_abs_le (crossAtom 3)]
    have hc4 : crossAtom 4 ≥ -(11 / 40) * (Real.log 2 / Real.pi ^ 4) := by
      have v4 : (ArithmeticFunction.vonMangoldt 4 : ℝ) = Real.log 2 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
          ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
          ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        norm_num
      have habs : |crossAtom 4| ≤ (11 / 40) * (Real.log 2 / Real.pi ^ 4) := by
        simp only [crossAtom, show (2 : ℕ) ≤ 4 by norm_num, ite_true, v4,
          scaleRatioCorrelationLimit_12_even_eq_zero ⟨2, rfl⟩, add_zero, Nat.cast_ofNat]
        rw [abs_mul, abs_of_nonneg (by positivity)]
        calc (Real.log 2 / 4) * |scaleRatioCorrelationLimit 2 1 4|
            ≤ (Real.log 2 / 4) * ((11 / 10) / Real.pi ^ 4) :=
              mul_le_mul_of_nonneg_left abs_scaleRatioCorrelationLimit_21_four_le (by positivity)
          _ = (11 / 40) * (Real.log 2 / Real.pi ^ 4) := by ring
      linarith [neg_abs_le (crossAtom 4)]
    have hc5 : crossAtom 5 ≥ -(77 / 1875) * (Real.log 2 / Real.pi ^ 4) := by
      have hlog5 : Real.log 5 ≤ (7 / 3) * Real.log 2 := by
        have h := Real.log_le_log (by norm_num : (0 : ℝ) < 5 ^ 3)
          (by norm_num : (5 : ℝ) ^ 3 ≤ 2 ^ 7)
        simp only [Real.log_pow, Nat.cast_ofNat] at h; linarith
      have habs : |crossAtom 5| ≤ (77 / 1875) * (Real.log 2 / Real.pi ^ 4) := by
        simp only [crossAtom, show (2 : ℕ) ≤ 5 by norm_num, ite_true,
          ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5), Nat.cast_ofNat]
        rw [abs_mul, abs_of_nonneg (by positivity)]
        have hodd := (abs_add_le _ _).trans (abs_scaleRatioCorrelationLimit_odd_le (r := 5) (by omega))
        push_cast at hodd
        have hdiv5 : Real.log 5 / 5 ≤ (7 / 3 * Real.log 2) / 5 :=
          div_le_div_of_nonneg_right hlog5 (by norm_num)
        calc (Real.log 5 / 5) * |scaleRatioCorrelationLimit 2 1 5 + scaleRatioCorrelationLimit 1 2 5|
            ≤ ((7 / 3 * Real.log 2) / 5) * ((11 / (5 * 5 ^ 2)) / Real.pi ^ 4) :=
              mul_le_mul hdiv5 hodd (abs_nonneg _) (by positivity)
          _ = (77 / 1875) * (Real.log 2 / Real.pi ^ 4) := by ring
      linarith [neg_abs_le (crossAtom 5)]
    obtain ⟨hs7_abs, hts7⟩ := summable_and_tsum_cross_tail_seven_le
    have hnorm_eq : ∀ m : ℕ, ‖crossAtom (m + 7)‖ =
        |((ArithmeticFunction.vonMangoldt (m + 7) : ℝ) / ((m + 7 : ℕ) : ℝ)) *
          (scaleRatioCorrelationLimit 2 1 (m + 7) + scaleRatioCorrelationLimit 1 2 (m + 7))| := by
      intro m
      rw [Real.norm_eq_abs]
      simp only [crossAtom, show 2 ≤ m + 7 by omega, ite_true]
    have hs7_norm : Summable (fun m : ℕ => ‖crossAtom (m + 7)‖) :=
      hs7_abs.congr fun m => (hnorm_eq m).symm
    have htail_abs : |∑' m : ℕ, crossAtom (m + 7)| ≤
        (11 / 5) * (18 / 49 + 3 / 32) * (1 / 6) * (Real.log 2 / Real.pi ^ 4) := by
      rw [← Real.norm_eq_abs]
      refine (norm_tsum_le_tsum_norm hs7_norm).trans ?_
      rw [tsum_congr hnorm_eq]
      exact hts7
    have htail_ge := neg_abs_le (∑' m : ℕ, crossAtom (m + 7))
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, hc0, hc1, hc6, zero_add, add_zero]
    linarith
  -- 4. Combine: `-(log 2 / π⁴) J_2` cancels `+(log 2 / π⁴) J_2` identically!
  rw [hsplit_limit]
  have hmargin : (1 / 8 : ℝ) ≤
      (88 / 189 * (13 / 10) + 128 / 875 * (6 / 5)) -
      (11 / 40 + 88 / 675 + 77 / 1875 + (11 / 5) * (18 / 49 + 3 / 32) * (1 / 6)) := by
    norm_num
  have hfac : 0 < Real.log 2 / Real.pi ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hmargin hfac.le]

/-- **Eventual Strict Positivity of `criticalPrimeEnergy` on Dyadic Endpoint Pairs.**
There exists `M₀ ≥ 2` such that for every `M ≥ M₀`, the uncollared critical prime channel on
`dyadicPairSupport M = {M - 1, 2M - 1}` with unit weights is strictly positive:
`criticalPrimeEnergy (dyadicPairSupport M) (fun _ => 1) ≥ (1 / 16) * (Real.log 2 / Real.pi ^ 4) > 0`. -/
theorem exists_dyadicPair_criticalPrimeEnergy_pos :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      (1 / 16) * (Real.log 2 / Real.pi ^ 4) ≤
        criticalPrimeEnergy (dyadicPairSupport M) (fun _ => 1) ∧
      0 < criticalPrimeEnergy (dyadicPairSupport M) (fun _ => 1) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi4_pos : 0 < Real.pi ^ 4 := by positivity
  have hlt : (1 / 16) * (Real.log 2 / Real.pi ^ 4) < dyadicPairPrimeLimit := by
    have hge := dyadicPairPrimeLimit_ge.1
    have hpos : 0 < Real.log 2 / Real.pi ^ 4 := by positivity
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (tendsto_criticalPrimeEnergy_dyadicPair.eventually (lt_mem_nhds hlt))
  refine ⟨max N₀ 2, le_max_right _ _, fun M hM => ?_⟩
  have hgt := hN₀ M ((le_max_left _ _).trans hM)
  exact ⟨hgt.le, lt_trans (by positivity) hgt⟩

/-- **Sign Reversal on Dyadic Scale Blocks (`[M, 2M]`).**
Negative semidefiniteness of `criticalPrimeEnergy` fails on dyadic scale blocks at every large
scale: there exists `M₀ ≥ 2` such that for every `M ≥ M₀`, some `S` with `DyadicScaleBlock S M`
and coefficient vector `b` satisfy `0 < criticalPrimeEnergy S b`. -/
theorem not_criticalPrimeEnergy_nonpos_of_dyadicBlock :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∃ (S : Finset ℕ) (b : ℕ → ℝ), DyadicScaleBlock S M ∧ 0 < criticalPrimeEnergy S b := by
  obtain ⟨M₀, hM₀, hpos⟩ := exists_dyadicPair_criticalPrimeEnergy_pos
  exact ⟨M₀, hM₀, fun M hM =>
    ⟨dyadicPairSupport M, fun _ => 1,
      dyadicPairSupport_dyadicScaleBlock (by omega), (hpos M hM).2⟩⟩

/-- **Sign Reversal on Multiplicative Scale Windows (`[M, L M]`, `L ≥ 2`).**
For every multiplicative aspect ratio `L ≥ 2`, negative semidefiniteness of `criticalPrimeEnergy`
fails on `ScaleWindow S M L` for all `M ≥ M₀`. -/
theorem not_criticalPrimeEnergy_nonpos_of_scaleWindow :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ L : ℕ, 2 ≤ L → ∀ M : ℕ, M₀ ≤ M →
      ∃ (S : Finset ℕ) (b : ℕ → ℝ), ScaleWindow S M L ∧ 0 < criticalPrimeEnergy S b := by
  obtain ⟨M₀, hM₀, hpos⟩ := exists_dyadicPair_criticalPrimeEnergy_pos
  refine ⟨M₀, hM₀, fun L hL M hM => ⟨dyadicPairSupport M, fun _ => 1, ?_, (hpos M hM).2⟩⟩
  intro n hn
  obtain ⟨h1, h2⟩ := dyadicPairSupport_dyadicScaleBlock (by omega : 1 ≤ M) n hn
  exact ⟨h1, h2.trans (Nat.mul_le_mul_right M hL)⟩

/-- **Sign Reversal on Wide Linear Windows (`[N, (1 + δ)N]`, `δ ≥ 1`).**
Whereas `criticalPrimeEnergy` is negative definite on `[N, (1 + δ)N]` for sufficiently small
`δ > 0`, negative semidefiniteness fails at every width `δ ≥ 1` and every large scale `N`. -/
theorem not_criticalPrimeEnergy_nonpos_of_wideLinearWindow :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ δ : ℝ, 1 ≤ δ → ∀ N : ℕ, N₀ ≤ N →
      ∃ (T : Finset ℕ) (b : ℕ → ℝ),
        (∀ m ∈ T, N ≤ m + 1 ∧ ((m : ℝ) + 1) ≤ (1 + δ) * N) ∧ 0 < criticalPrimeEnergy T b := by
  obtain ⟨M₀, hM₀, hpos⟩ := exists_dyadicPair_criticalPrimeEnergy_pos
  refine ⟨M₀, hM₀, fun δ hδ N hN => ⟨dyadicPairSupport N, fun _ => 1, ?_, (hpos N hN).2⟩⟩
  intro m hm
  obtain ⟨h1, h2⟩ := dyadicPairSupport_dyadicScaleBlock (by omega : 1 ≤ N) m hm
  refine ⟨h1, ?_⟩
  have h2R : ((m : ℝ) + 1) ≤ 2 * (N : ℝ) := by exact_mod_cast h2
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- **Sign Reversal on Polynomial Windows (`[N, N^{1 + δ}]`, `δ > 0`).**
For every positive exponent `δ > 0` and every threshold `N₁`, there exist `N ≥ N₁`, a finite
support `T` in `N ≤ m + 1 ≤ N ^ (1 + δ)`, and a coefficient vector `b` such that
`0 < criticalPrimeEnergy T b`. Thus negative semidefiniteness of `criticalPrimeEnergy` never
persists on polynomial windows `[N, N^{1 + δ}]`. -/
theorem not_criticalPrimeEnergy_nonpos_of_polynomialWindow (δ : ℝ) (hδ : 0 < δ) :
    ∀ N₁ : ℕ, ∃ N : ℕ, N₁ ≤ N ∧ ∃ (T : Finset ℕ) (b : ℕ → ℝ),
      (∀ m ∈ T, (N : ℝ) ≤ (m : ℝ) + 1 ∧ (m : ℝ) + 1 ≤ (N : ℝ) ^ (1 + δ)) ∧
        0 < criticalPrimeEnergy T b := by
  obtain ⟨M₀, _, hpos⟩ := exists_dyadicPair_criticalPrimeEnergy_pos
  intro N₁
  have htend : Tendsto (fun N : ℕ => (N : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (htend.eventually_ge_atTop (2 : ℝ))
  set N : ℕ := max (max N₁ M₀) (max N₂ 2)
  have hN_N1 : N₁ ≤ N := (le_max_left _ _).trans (le_max_left _ _)
  have hN_M0 : M₀ ≤ N := (le_max_right _ _).trans (le_max_left _ _)
  have hN_N2 : N₂ ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN_2 : 2 ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨N, hN_N1, dyadicPairSupport N, fun _ => 1, ?_, (hpos N hN_M0).2⟩
  intro m hm
  obtain ⟨h1, h2⟩ := dyadicPairSupport_dyadicScaleBlock (by omega : 1 ≤ N) m hm
  refine ⟨by exact_mod_cast h1, ?_⟩
  have h2R : (m : ℝ) + 1 ≤ 2 * (N : ℝ) := by exact_mod_cast h2
  have hpow2 : (2 : ℝ) ≤ (N : ℝ) ^ δ := hN₂ N hN_N2
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  calc (m : ℝ) + 1 ≤ 2 * (N : ℝ) := h2R
    _ ≤ (N : ℝ) ^ δ * (N : ℝ) := mul_le_mul_of_nonneg_right hpow2 hN0.le
    _ = (N : ℝ) ^ (1 + δ) := by rw [Real.rpow_add hN0, Real.rpow_one, mul_comm]

/-- **Refutation of All-Scale Negative Semidefiniteness.**
The uncollared critical prime channel `criticalPrimeEnergy` is not negative semidefinite across
all scales, nor above any high-scale cutoff `N₁`. -/
theorem not_criticalPrimeEnergy_nonpos_all_scales :
    ∀ N₁ : ℕ, ∃ (T : Finset ℕ) (b : ℕ → ℝ),
      (∀ m ∈ T, N₁ ≤ m + 1) ∧ 0 < criticalPrimeEnergy T b := by
  obtain ⟨M₀, _, hpos⟩ := exists_dyadicPair_criticalPrimeEnergy_pos
  intro N₁
  set M := max N₁ M₀
  refine ⟨dyadicPairSupport M, fun _ => 1, ?_, (hpos M (le_max_right _ _)).2⟩
  intro m hm
  exact (le_max_left _ _).trans (dyadicPairSupport_dyadicScaleBlock
    (by have := (le_max_right N₁ M₀); omega) m hm).1

end GaloisForLFunctions.ArithmeticPositivityTheory
