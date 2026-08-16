import GaloisForLFunctions.RHTower.SuzukiWardAtomicContinuousLightWeld
import GaloisForLFunctions.RHTower.SuzukiNaturalApertureCauchyEnergyEscape
import GaloisForLFunctions.HTGeometry.AbstractSpectralDefect
import GaloisForLFunctions.RHTower.MassBesselDyadicAperture

/-!
# Phase leakage obstruction for the fixed two-light Suzuki Ward completion

The exact positive-light sine split has a quadratic phase defect.  At aperture `8n`, choose the
height `-π / (2 log (8n))`, which aligns the outer endpoint with the negative light direction.
Every prime-power cell in `(2n,4n]` still retains at least a fixed multiple of
`(log 2 / log (8n))²` in the positive channel.  The PNT-sized dyadic von-Mangoldt mass then forces
the reporter-weighted positive-light mass to diverge.

Thus no fixed two-channel wall-light completion can itself supply the uniformly bounded SP-E Ward
residual.  A viable endpoint must use increasing signed-permutation/Eulerian order or an additional
signed Schur subtraction that cancels this explicit dyadic leakage.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

private def suzukiUnitRieszPositiveLightNaturalCell
    (N : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  if k ∈ Finset.Icc 2 N then
    criticalMellinAtomWeight k *
      unitRieszSuzukiReporter (Real.log N) (Real.log k) *
      (1 + Real.sin (t * Real.log k)) / 2
  else 0

private theorem summable_suzukiUnitRieszPositiveLightNaturalCell
    (N : ℕ) (t : ℝ) :
    Summable (suzukiUnitRieszPositiveLightNaturalCell N t) := by
  refine summable_of_ne_finset_zero (s := Finset.Icc 2 N) ?_
  intro k hk
  simp [suzukiUnitRieszPositiveLightNaturalCell, hk]

private theorem suzukiUnitRieszPositiveLightNaturalCell_support_primePower
    (N : ℕ) (t : ℝ) :
    Function.support (suzukiUnitRieszPositiveLightNaturalCell N t) ⊆
      {k : ℕ | IsPrimePow k} := by
  intro k hk
  by_contra hpow
  have hzero : ArithmeticFunction.vonMangoldt k = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
  exact hk (by simp [suzukiUnitRieszPositiveLightNaturalCell,
    criticalMellinAtomWeight, hzero])

private theorem tsum_suzukiUnitRieszPositiveLightNaturalCell_valuation
    (N : ℕ) (t : ℝ) :
    (∑' pe : Nat.Primes × ℕ,
      suzukiUnitRieszPositiveLightNaturalCell N t
        (xiGammaEulerValuationNat pe)) =
      ∑' k : ℕ, suzukiUnitRieszPositiveLightNaturalCell N t k := by
  have hs := summable_suzukiUnitRieszPositiveLightNaturalCell N t
  have hreindex := tsum_eq_tsum_primes_of_support_subset_prime_powers hs
    (suzukiUnitRieszPositiveLightNaturalCell_support_primePower N t)
  have hcomp : Summable (fun pe : Nat.Primes × ℕ =>
      suzukiUnitRieszPositiveLightNaturalCell N t
        (xiGammaEulerValuationNat pe)) :=
    hs.comp_injective xiGammaEulerValuationNat_injective_commonTest
  calc
    (∑' pe : Nat.Primes × ℕ,
        suzukiUnitRieszPositiveLightNaturalCell N t
          (xiGammaEulerValuationNat pe)) =
        ∑' p : Nat.Primes, ∑' e : ℕ,
          suzukiUnitRieszPositiveLightNaturalCell N t (p.1 ^ (e + 1)) := by
      simpa [xiGammaEulerValuationNat] using hcomp.tsum_prod
    _ = _ := hreindex.symm

private theorem suzukiUnitRieszPositiveLightNaturalCell_valuation_eq
    (N : ℕ) (t : ℝ) (pe : Nat.Primes × ℕ) :
    suzukiUnitRieszPositiveLightNaturalCell N t
        (xiGammaEulerValuationNat pe) =
      if xiGammaEulerValuationNat pe ≤ N then
        unitRieszSuzukiReporter (Real.log N)
            (Real.log (xiGammaEulerValuationNat pe)) *
          normSq (suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2)
      else 0 := by
  have hval : 2 ≤ xiGammaEulerValuationNat pe := by
    rw [xiGammaEulerValuationNat]
    exact pe.1.property.two_le.trans (Nat.le_pow (by omega))
  by_cases hle : xiGammaEulerValuationNat pe ≤ N
  · rw [if_pos hle]
    simp only [suzukiUnitRieszPositiveLightNaturalCell,
      if_pos (Finset.mem_Icc.mpr ⟨hval, hle⟩)]
    rw [normSq_suzukiCriticalWallPositiveLightAmplitude_eq_sine,
      criticalMellinAtomWeight_eq_vonMangoldt_div_sqrt]
    ring
  · rw [if_neg hle]
    simp [suzukiUnitRieszPositiveLightNaturalCell, hle]

/-- Natural-number occurrence of the exact positive-light mass. -/
theorem suzukiUnitRieszReporterWeightedPositiveLightMass_eq_naturalSum
    (N : ℕ) (t : ℝ) :
    suzukiUnitRieszReporterWeightedPositiveLightMass N t =
      ∑ k ∈ Finset.Icc 2 N,
        criticalMellinAtomWeight k *
          unitRieszSuzukiReporter (Real.log N) (Real.log k) *
          (1 + Real.sin (t * Real.log k)) / 2 := by
  rw [suzukiUnitRieszReporterWeightedPositiveLightMass]
  calc
    (∑' pe : Nat.Primes × ℕ,
        if xiGammaEulerValuationNat pe ≤ N then
          unitRieszSuzukiReporter (Real.log N)
              (Real.log (xiGammaEulerValuationNat pe)) *
            normSq (suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2)
        else 0) =
        ∑' pe : Nat.Primes × ℕ,
          suzukiUnitRieszPositiveLightNaturalCell N t
            (xiGammaEulerValuationNat pe) := by
      apply tsum_congr
      intro pe
      exact (suzukiUnitRieszPositiveLightNaturalCell_valuation_eq N t pe).symm
    _ = ∑' k : ℕ, suzukiUnitRieszPositiveLightNaturalCell N t k :=
      tsum_suzukiUnitRieszPositiveLightNaturalCell_valuation N t
    _ = ∑ k ∈ Finset.Icc 2 N,
        suzukiUnitRieszPositiveLightNaturalCell N t k := by
      rw [tsum_eq_sum (s := Finset.Icc 2 N) (by
        intro k hk
        simp [suzukiUnitRieszPositiveLightNaturalCell, hk])]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [suzukiUnitRieszPositiveLightNaturalCell, hk]

/-- Universal quadratic leakage floor for a phase aligned at `-π/2`. -/
theorem phaseAlignedSineLeakage_ge
    {L x c : ℝ} (hL : 0 < L) (hx0 : 0 ≤ x) (hxL : x ≤ L)
    (hc0 : 0 ≤ c) (hgap : c ≤ L - x) :
    c ^ 2 / (4 * L ^ 2) ≤
      (1 + Real.sin ((-Real.pi / (2 * L)) * x)) / 2 := by
  let δ : ℝ := Real.pi * (L - x) / (2 * L)
  have hden : 0 < 2 * L := by positivity
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    exact div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hxL)) hden.le
  have hδpi : δ ≤ Real.pi := by
    dsimp only [δ]
    rw [div_le_iff₀ hden]
    have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
    have hdiff : L - x ≤ 2 * L := by linarith
    exact mul_le_mul_of_nonneg_left hdiff hpi0
  have habs : |δ| ≤ Real.pi := by rw [abs_of_nonneg hδ0]; exact hδpi
  have hδlower : Real.pi * c / (2 * L) ≤ δ := by
    dsimp only [δ]
    rw [div_le_div_iff_of_pos_right hden]
    exact mul_le_mul_of_nonneg_left hgap Real.pi_pos.le
  have hlower0 : 0 ≤ Real.pi * c / (2 * L) := by positivity
  have hδsq : (Real.pi * c / (2 * L)) ^ 2 ≤ δ ^ 2 :=
    pow_le_pow_left₀ hlower0 hδlower 2
  have hscaled := mul_le_mul_of_nonneg_left hδsq
    (by positivity : 0 ≤ 2 / Real.pi ^ 2)
  have hjordan :=
    HTGeometry.AbstractSpectralFamily.two_div_pi_sq_mul_sq_le_one_sub_cos habs
  have hscale :
      2 / Real.pi ^ 2 * (Real.pi * c / (2 * L)) ^ 2 =
        c ^ 2 / (2 * L ^ 2) := by
    field_simp [Real.pi_ne_zero, hL.ne']
  rw [hscale] at hscaled
  have hdefect : c ^ 2 / (2 * L ^ 2) ≤ 1 - Real.cos δ :=
    hscaled.trans hjordan
  have hphase :
      (-Real.pi / (2 * L)) * x = -(Real.pi / 2 - δ) := by
    dsimp only [δ]
    field_simp [hL.ne']
    ring
  have htrig :
      1 + Real.sin ((-Real.pi / (2 * L)) * x) = 1 - Real.cos δ := by
    rw [hphase, Real.sin_neg, Real.sin_pi_div_two_sub]
    ring
  rw [htrig]
  calc
    c ^ 2 / (4 * L ^ 2) = (c ^ 2 / (2 * L ^ 2)) / 2 := by ring
    _ ≤ (1 - Real.cos δ) / 2 := div_le_div_of_nonneg_right hdefect (by norm_num)

/-- On `(2n,4n]`, alignment at aperture `8n` leaves a uniform logarithmic-square phase floor. -/
theorem dyadic_phaseAlignedSineLeakage_ge
    {n k : ℕ} (hn : 1 ≤ n) (hk : k ∈ Finset.Ioc (2 * n) (4 * n)) :
    Real.log 2 ^ 2 / (4 * Real.log (8 * n : ℕ) ^ 2) ≤
      (1 + Real.sin
        ((-Real.pi / (2 * Real.log (8 * n : ℕ))) * Real.log k)) / 2 := by
  have hkIoc := Finset.mem_Ioc.mp hk
  have hk1 : 1 ≤ k := by omega
  have hM1 : 1 < 8 * n := by omega
  have hMpos : (0 : ℝ) < (8 * n : ℕ) := by positivity
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hL : 0 < Real.log (8 * n : ℕ) := Real.log_pos (by exact_mod_cast hM1)
  have hx0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  have hkM : k ≤ 8 * n := by omega
  have hxL : Real.log k ≤ Real.log (8 * n : ℕ) :=
    Real.strictMonoOn_log.monotoneOn hkpos hMpos (by exact_mod_cast hkM)
  have hc0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have htwok : (2 : ℝ) * k ≤ (8 * n : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact_mod_cast (show 2 * k ≤ 8 * n by omega)
  have htwokpos : (0 : ℝ) < (2 : ℝ) * k := mul_pos (by norm_num) hkpos
  have hlogtwok : Real.log ((2 : ℝ) * k) ≤ Real.log (8 * n : ℕ) :=
    Real.strictMonoOn_log.monotoneOn htwokpos hMpos htwok
  have hgap : Real.log 2 ≤ Real.log (8 * n : ℕ) - Real.log k := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hkpos.ne'] at hlogtwok
    linarith
  exact phaseAlignedSineLeakage_ge hL hx0 hxL hc0 hgap

private theorem dyadicSqrtVonMangoldtMass_two_nat_eq_sum (n : ℕ) :
    dyadicSqrtVonMangoldtMass (2 * (n : ℝ)) =
      ∑ k ∈ Finset.Ioc (2 * n) (4 * n),
        (ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k := by
  have hfloorTwo : ⌊2 * (n : ℝ)⌋₊ = 2 * n := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.floor_natCast (2 * n) : ⌊((2 * n : ℕ) : ℝ)⌋₊ = 2 * n)
  have hfloorFour : ⌊2 * (2 * (n : ℝ))⌋₊ = 4 * n := by
    calc
      ⌊2 * (2 * (n : ℝ))⌋₊ = 2 * (2 * n) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          (Nat.floor_natCast (2 * (2 * n)) :
            ⌊((2 * (2 * n) : ℕ) : ℝ)⌋₊ = 2 * (2 * n))
      _ = 4 * n := by omega
  rw [dyadicSqrtVonMangoldtMass, hfloorTwo, hfloorFour]

/-- Quantitative dyadic lower bound for the phase-aligned positive-light mass. -/
theorem phaseAlignedPositiveLightMass_ge_dyadic
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log 2 ^ 2 / (32 * Real.log (8 * n : ℕ) ^ 2) *
        dyadicSqrtVonMangoldtMass (2 * (n : ℝ)) ≤
      suzukiUnitRieszReporterWeightedPositiveLightMass (8 * n)
        (-Real.pi / (2 * Real.log (8 * n : ℕ))) := by
  rw [suzukiUnitRieszReporterWeightedPositiveLightMass_eq_naturalSum,
    dyadicSqrtVonMangoldtMass_two_nat_eq_sum, Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun k hk => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · rw [← criticalMellinAtomWeight_eq_vonMangoldt_div_sqrt]
    have hrep := one_eighth_le_unitRieszSuzukiReporter_neg_naturalLag hn hk
    have hrepEq :
        unitRieszSuzukiReporter (Real.log (8 * n : ℕ)) (Real.log k) =
          unitRieszSuzukiReporter 0
            (-(suzukiNaturalApertureLag (8 * n) k : ℝ)) := by
      rw [unitRieszSuzukiReporter_neg_naturalLag_eq
        (by have := (Finset.mem_Ioc.mp hk).1; omega)
        (by have := (Finset.mem_Ioc.mp hk).2; omega)]
      rw [unitRieszSuzukiReporter]
      have hkpos : (0 : ℝ) < k := by
        exact_mod_cast (show 0 < k by have := (Finset.mem_Ioc.mp hk).1; omega)
      have hNpos : (0 : ℝ) < (8 * n : ℕ) := by positivity
      have hkN : (k : ℝ) ≤ (8 * n : ℕ) := by
        exact_mod_cast (show k ≤ 8 * n by have := (Finset.mem_Ioc.mp hk).2; omega)
      have hlog : 0 ≤ Real.log (8 * n : ℕ) - Real.log k :=
        sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn hkpos hNpos hkN)
      have hfull :
          Real.exp (-(Real.log (8 * n : ℕ) - Real.log k)) =
            (k : ℝ) / (8 * n : ℕ) := by
        rw [neg_sub, Real.exp_sub, Real.exp_log hkpos, Real.exp_log hNpos]
      have hhalfSq :
          Real.exp (-(Real.log (8 * n : ℕ) - Real.log k) / 2) ^ 2 =
            (k : ℝ) / (8 * n : ℕ) := by
        rw [pow_two, ← Real.exp_add]
        convert hfull using 1
        ring
      have hratio : 0 ≤ (k : ℝ) / (8 * n : ℕ) := by positivity
      have hsqrtSq : Real.sqrt ((k : ℝ) / (8 * n : ℕ)) ^ 2 =
          (k : ℝ) / (8 * n : ℕ) := Real.sq_sqrt hratio
      have hhalf :
          Real.exp (-(Real.log (8 * n : ℕ) - Real.log k) / 2) =
            Real.sqrt ((k : ℝ) / (8 * n : ℕ)) := by
        nlinarith [Real.exp_pos (-(Real.log (8 * n : ℕ) - Real.log k) / 2),
          Real.sqrt_nonneg ((k : ℝ) / (8 * n : ℕ))]
      rw [show (Real.log k - Real.log (8 * n : ℕ)) / 2 =
          -(Real.log (8 * n : ℕ) - Real.log k) / 2 by ring,
        show Real.log k - Real.log (8 * n : ℕ) =
          -(Real.log (8 * n : ℕ) - Real.log k) by ring,
        hhalf, hfull]
    rw [hrepEq]
    have hphase := dyadic_phaseAlignedSineLeakage_ge hn hk
    have hatom : 0 ≤ criticalMellinAtomWeight k := criticalMellinAtomWeight_nonneg k
    have hrep0 : 0 ≤ unitRieszSuzukiReporter 0
        (-(suzukiNaturalApertureLag (8 * n) k : ℝ)) := by
      linarith
    have hphase0 : 0 ≤
        Real.log 2 ^ 2 / (4 * Real.log (8 * n : ℕ) ^ 2) := by positivity
    calc
      Real.log 2 ^ 2 / (32 * Real.log (8 * n : ℕ) ^ 2) *
          criticalMellinAtomWeight k =
          criticalMellinAtomWeight k * (1 / 8) *
            (Real.log 2 ^ 2 / (4 * Real.log (8 * n : ℕ) ^ 2)) := by ring
      _ ≤ criticalMellinAtomWeight k *
          unitRieszSuzukiReporter 0
            (-(suzukiNaturalApertureLag (8 * n) k : ℝ)) *
          (Real.log 2 ^ 2 / (4 * Real.log (8 * n : ℕ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrep hatom) hphase0
      _ ≤ criticalMellinAtomWeight k *
          unitRieszSuzukiReporter 0
            (-(suzukiNaturalApertureLag (8 * n) k : ℝ)) *
          ((1 + Real.sin
            ((-Real.pi / (2 * Real.log (8 * n : ℕ))) * Real.log k)) / 2) := by
        exact mul_le_mul_of_nonneg_left hphase (mul_nonneg hatom hrep0)
      _ = criticalMellinAtomWeight k *
          unitRieszSuzukiReporter 0
            (-(suzukiNaturalApertureLag (8 * n) k : ℝ)) *
          (1 + Real.sin
            ((-Real.pi / (2 * Real.log (8 * n : ℕ))) * Real.log k)) / 2 := by ring
  · intro k hk
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
    omega
  · intro k hkIcc hkBlock
    simp only [Finset.mem_Icc] at hkIcc
    have hatom : 0 ≤ criticalMellinAtomWeight k := criticalMellinAtomWeight_nonneg k
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hNpos : (0 : ℝ) < (8 * n : ℕ) := by positivity
    have hkN : (k : ℝ) ≤ (8 * n : ℕ) := by exact_mod_cast hkIcc.2
    have hrep : 0 ≤ unitRieszSuzukiReporter
        (Real.log (8 * n : ℕ)) (Real.log k) :=
      unitRieszSuzukiReporter_nonneg_of_mem
        (Real.strictMonoOn_log.monotoneOn hkpos hNpos hkN)
    have hphase : 0 ≤ 1 + Real.sin
        ((-Real.pi / (2 * Real.log (8 * n : ℕ))) * Real.log k) := by
      linarith [Real.neg_one_le_sin
        ((-Real.pi / (2 * Real.log (8 * n : ℕ))) * Real.log k)]
    positivity

/-- **Fixed two-light phase-leakage obstruction.**  Along natural apertures `8n`, even the height
that aligns the outer endpoint with the negative light channel leaves positive-light mass tending
to infinity. -/
theorem tendsto_phaseAlignedPositiveLightMass_atTop :
    Tendsto (fun n : ℕ =>
      suzukiUnitRieszReporterWeightedPositiveLightMass (8 * n)
        (-Real.pi / (2 * Real.log (8 * n : ℕ)))) atTop atTop := by
  have h8nat : Tendsto (fun n : ℕ => (8 : ℝ) * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hbase : Tendsto (fun n : ℕ =>
      Real.sqrt ((8 : ℝ) * n) / Real.log ((8 : ℝ) * n) ^ 2) atTop atTop :=
    tendsto_sqrt_div_log_sq_atTop.comp h8nat
  have hconst : 0 < Real.log 2 ^ 2 / 192 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hgrow : Tendsto (fun n : ℕ =>
      (Real.log 2 ^ 2 / 192) *
        (Real.sqrt ((8 : ℝ) * n) / Real.log ((8 : ℝ) * n) ^ 2)) atTop atTop :=
    hbase.const_mul_atTop hconst
  have h2nat : Tendsto (fun n : ℕ => (2 : ℝ) * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hmassNat : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (2 * (n : ℝ)) / 3 ≤
        dyadicSqrtVonMangoldtMass (2 * (n : ℝ)) :=
    h2nat.eventually eventually_dyadicSqrtVonMangoldtMass_ge
  have hbound : ∀ᶠ n : ℕ in atTop,
      (Real.log 2 ^ 2 / 192) *
          (Real.sqrt ((8 : ℝ) * n) / Real.log ((8 : ℝ) * n) ^ 2) ≤
        suzukiUnitRieszReporterWeightedPositiveLightMass (8 * n)
          (-Real.pi / (2 * Real.log (8 * n : ℕ))) := by
    filter_upwards [hmassNat, eventually_ge_atTop 1] with n hmass hn
    have hsqrt : Real.sqrt ((8 : ℝ) * n) = 2 * Real.sqrt (2 * (n : ℝ)) := by
      rw [show (8 : ℝ) * n = 4 * (2 * (n : ℝ)) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    have hcast : Real.log ((8 : ℝ) * n) = Real.log (8 * n : ℕ) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (Real.log 2 ^ 2 / 192) *
          (Real.sqrt ((8 : ℝ) * n) / Real.log ((8 : ℝ) * n) ^ 2) =
          Real.log 2 ^ 2 / (32 * Real.log (8 * n : ℕ) ^ 2) *
            (Real.sqrt (2 * (n : ℝ)) / 3) := by
        rw [hsqrt, hcast]
        ring
      _ ≤ Real.log 2 ^ 2 / (32 * Real.log (8 * n : ℕ) ^ 2) *
          dyadicSqrtVonMangoldtMass (2 * (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ _ := phaseAlignedPositiveLightMass_ge_dyadic hn
  exact tendsto_atTop_mono' atTop hbound hgrow

end

end GaloisForLFunctions.RHTower
