import GaloisForLFunctions.RHTower.GaussSampleQuantitativeRatio
import GaloisForLFunctions.RHTower.GaussSampleTranslationL2
import GaloisForLFunctions.HTGeometry.ShiftSumLimits

/-!
# Cubic-rate summation for the Gauss moving-translation defect

Pointwise Gamma-ratio asymptotics do not by themselves survive the infinite
Fourier sum used by the CCM Gauss fold.  This module combines the quantitative
two-sided parabolic law with the earlier qualitative power-weight theorem.

Inside 2|j|² ≤ I, quadratic clock curvature cancels the amplitude's
(1+|j|)⁻² weight and is dominated by the summable exponent 4/3.  Outside
that band, the scale I^(1/3) is absorbed into 2(1+|j|)^(2/3), reducing the
same weight to exponent 4/3; the existing moving-translation theorem then
forces the total outer contribution to zero.

Consequently I^(1/3) · E_I² → 0, and hence I^(1/m) · E_I² → 0 at every Gauss
depth m ≥ 3.  This is the first quantitative infinite-mode rate in the corpus.
It isolates depth two as the true summability endpoint rather than treating
every higher depth as one undifferentiated gap.
-/

namespace RHTower

open Filter Topology
open scoped ENNReal NNReal
open GaloisForLFunctions

noncomputable section

private theorem central_cubic_kernel_le (a L : ℕ) (ha : 0 < a) (hband : a ^ 2 ≤ L) :
    (L : ℝ) ^ (1 / 3 : ℝ) *
        (((a : ℝ) + (a : ℝ) ^ 2) ^ 2 /
          ((1 + (a : ℝ)) ^ 2 * (L : ℝ) ^ 2)) ≤
      4 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have ha1R : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hLR : 0 < (L : ℝ) := by
    have : 0 < L := lt_of_lt_of_le (by positivity : 0 < a ^ 2) hband
    exact_mod_cast this
  have hbandR : (a : ℝ) ^ 2 ≤ (L : ℝ) := by exact_mod_cast hband
  have hsimp :
      (L : ℝ) ^ (1 / 3 : ℝ) *
          (((a : ℝ) + (a : ℝ) ^ 2) ^ 2 /
            ((1 + (a : ℝ)) ^ 2 * (L : ℝ) ^ 2)) =
        (a : ℝ) ^ 2 * ((L : ℝ) ^ (1 / 3 : ℝ) / (L : ℝ) ^ 2) := by
    field_simp
  have hpow : (L : ℝ) ^ (1 / 3 : ℝ) / (L : ℝ) ^ 2 =
      (L : ℝ) ^ (-(5 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast (L : ℝ) 2, ← Real.rpow_sub hLR]
    congr 1
    norm_num
  rw [hsimp, hpow]
  have hmono : (L : ℝ) ^ (-(5 / 3 : ℝ)) ≤
      ((a : ℝ) ^ 2) ^ (-(5 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbandR (by norm_num)
  have hcollapse : (a : ℝ) ^ 2 * ((a : ℝ) ^ 2) ^ (-(5 / 3 : ℝ)) =
      (a : ℝ) ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast (a : ℝ) 2, ← Real.rpow_mul haR.le,
      ← Real.rpow_add haR]
    congr 1
    norm_num
  calc
    (a : ℝ) ^ 2 * (L : ℝ) ^ (-(5 / 3 : ℝ))
        ≤ (a : ℝ) ^ 2 * ((a : ℝ) ^ 2) ^ (-(5 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (a : ℝ) ^ (-(4 / 3 : ℝ)) := hcollapse
    _ ≤ 4 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ) := by
      have hbase : 1 + (a : ℝ) ≤ 2 * (a : ℝ) := by linarith
      have hpowbase : (1 + (a : ℝ)) ^ (4 / 3 : ℝ) ≤
          (2 * (a : ℝ)) ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase (by norm_num)
      have htwo : (2 : ℝ) ^ (4 / 3 : ℝ) ≤ 4 := by
        calc
          (2 : ℝ) ^ (4 / 3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := by norm_num
      have hmul : (2 * (a : ℝ)) ^ (4 / 3 : ℝ) =
          (2 : ℝ) ^ (4 / 3 : ℝ) * (a : ℝ) ^ (4 / 3 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) haR.le]
      have hden : (1 + (a : ℝ)) ^ (4 / 3 : ℝ) ≤
          4 * (a : ℝ) ^ (4 / 3 : ℝ) := by
        rw [hmul] at hpowbase
        exact hpowbase.trans (mul_le_mul_of_nonneg_right htwo (by positivity))
      rw [Real.rpow_neg haR.le]
      calc
        ((a : ℝ) ^ (4 / 3 : ℝ))⁻¹ = 1 / (a : ℝ) ^ (4 / 3 : ℝ) := by rw [one_div]
        _ ≤ 4 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hden]

private theorem outer_cubic_scale_le (I a : ℕ) (houter : I < 2 * a ^ 2) :
    (I : ℝ) ^ (1 / 3 : ℝ) ≤
      2 * (1 + (a : ℝ)) ^ (2 / 3 : ℝ) := by
  have hIR : (0 : ℝ) ≤ (I : ℝ) := by positivity
  have haR : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have houterR : (I : ℝ) ≤ 2 * (a : ℝ) ^ 2 := by exact_mod_cast houter.le
  calc
    (I : ℝ) ^ (1 / 3 : ℝ) ≤ (2 * (a : ℝ) ^ 2) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow hIR houterR (by norm_num)
    _ = (2 : ℝ) ^ (1 / 3 : ℝ) * (a : ℝ) ^ (2 / 3 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (sq_nonneg _), ← Real.rpow_natCast (a : ℝ) 2,
        ← Real.rpow_mul haR]
      congr 2
      norm_num
    _ ≤ 2 * (1 + (a : ℝ)) ^ (2 / 3 : ℝ) := by
      have htwo : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
        calc
          (2 : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := by simp
      have ha : (a : ℝ) ^ (2 / 3 : ℝ) ≤
          (1 + (a : ℝ)) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow haR (by linarith) (by norm_num)
      exact mul_le_mul htwo ha (by positivity) (by positivity)

private theorem cubic_scaled_term_le_central
    (A D x : ℝ) (a L : ℕ) (hL : 0 < L) (ha : 0 < a) (hband : a ^ 2 ≤ L)
    (hx : 0 ≤ x)
    (hdef : x ≤ D * ((a : ℝ) + (a : ℝ) ^ 2) / (L : ℝ)) :
    (L : ℝ) ^ (1 / 3 : ℝ) *
        (A ^ 2 / (1 + (a : ℝ)) ^ 2 * x ^ 2) ≤
      4 * D ^ 2 * A ^ 2 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ) := by
  have hsq := pow_le_pow_left₀ hx hdef 2
  have hweight : 0 ≤ A ^ 2 / (1 + (a : ℝ)) ^ 2 := by positivity
  have hscale : 0 ≤ (L : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  calc
    (L : ℝ) ^ (1 / 3 : ℝ) * (A ^ 2 / (1 + (a : ℝ)) ^ 2 * x ^ 2)
        ≤ (L : ℝ) ^ (1 / 3 : ℝ) *
          (A ^ 2 / (1 + (a : ℝ)) ^ 2 *
            (D * ((a : ℝ) + (a : ℝ) ^ 2) / (L : ℝ)) ^ 2) := by
          gcongr
    _ = D ^ 2 * A ^ 2 *
        ((L : ℝ) ^ (1 / 3 : ℝ) *
          (((a : ℝ) + (a : ℝ) ^ 2) ^ 2 /
            ((1 + (a : ℝ)) ^ 2 * (L : ℝ) ^ 2))) := by
          field_simp
    _ ≤ D ^ 2 * A ^ 2 * (4 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ)) := by
          gcongr
          exact central_cubic_kernel_le a L ha hband
    _ = 4 * D ^ 2 * A ^ 2 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ) := by ring

private theorem cubic_scaled_term_le_pointwise
    (A D x : ℝ) (a L : ℕ) (hL : 0 < L) (hx : 0 ≤ x)
    (hdef : x ≤ D * ((a : ℝ) + (a : ℝ) ^ 2) / (L : ℝ)) :
    (L : ℝ) ^ (1 / 3 : ℝ) *
        (A ^ 2 / (1 + (a : ℝ)) ^ 2 * x ^ 2) ≤
      D ^ 2 * A ^ 2 * (a : ℝ) ^ 2 * (L : ℝ) ^ (-(5 / 3 : ℝ)) := by
  have hsq := pow_le_pow_left₀ hx hdef 2
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hpow : (L : ℝ) ^ (1 / 3 : ℝ) / (L : ℝ) ^ 2 =
      (L : ℝ) ^ (-(5 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast (L : ℝ) 2, ← Real.rpow_sub hLR]
    congr 1
    norm_num
  calc
    (L : ℝ) ^ (1 / 3 : ℝ) * (A ^ 2 / (1 + (a : ℝ)) ^ 2 * x ^ 2)
        ≤ (L : ℝ) ^ (1 / 3 : ℝ) *
          (A ^ 2 / (1 + (a : ℝ)) ^ 2 *
            (D * ((a : ℝ) + (a : ℝ) ^ 2) / (L : ℝ)) ^ 2) := by
          gcongr
    _ = D ^ 2 * A ^ 2 * (a : ℝ) ^ 2 *
        ((L : ℝ) ^ (1 / 3 : ℝ) / (L : ℝ) ^ 2) := by
          field_simp
    _ = D ^ 2 * A ^ 2 * (a : ℝ) ^ 2 * (L : ℝ) ^ (-(5 / 3 : ℝ)) := by rw [hpow]

private theorem cubic_scaled_term_le_outer
    (A x : ℝ) (a I : ℕ) (houter : I < 2 * a ^ 2) :
    (I : ℝ) ^ (1 / 3 : ℝ) *
        (A ^ 2 / (1 + (a : ℝ)) ^ 2 * x ^ 2) ≤
      2 * (A ^ 2 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ) * x ^ 2) := by
  have hscale := outer_cubic_scale_le I a houter
  have hrest : 0 ≤ A ^ 2 / (1 + (a : ℝ)) ^ 2 * x ^ 2 := by positivity
  calc
    (I : ℝ) ^ (1 / 3 : ℝ) * (A ^ 2 / (1 + (a : ℝ)) ^ 2 * x ^ 2)
        ≤ (2 * (1 + (a : ℝ)) ^ (2 / 3 : ℝ)) *
          (A ^ 2 / (1 + (a : ℝ)) ^ 2 * x ^ 2) :=
            mul_le_mul_of_nonneg_right hscale hrest
    _ = 2 * (A ^ 2 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ) * x ^ 2) := by
      have hb : 0 < 1 + (a : ℝ) := by positivity
      have hratio :
          (1 + (a : ℝ)) ^ (2 / 3 : ℝ) / (1 + (a : ℝ)) ^ 2 =
            1 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ) := by
        rw [← Real.rpow_natCast (1 + (a : ℝ)) 2, ← Real.rpow_sub hb,
          show ((2 : ℕ) : ℝ) = 2 by norm_num]
        norm_num
        rw [Real.rpow_neg hb.le]
      calc
        2 * (1 + (a : ℝ)) ^ (2 / 3 : ℝ) *
            (A ^ 2 / (1 + (a : ℝ)) ^ 2 * x ^ 2)
            = 2 * A ^ 2 * x ^ 2 *
              ((1 + (a : ℝ)) ^ (2 / 3 : ℝ) /
                (1 + (a : ℝ)) ^ 2) := by ring
        _ = 2 * A ^ 2 * x ^ 2 *
              (1 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ)) := by rw [hratio]
        _ = 2 * (A ^ 2 / (1 + (a : ℝ)) ^ (4 / 3 : ℝ) * x ^ 2) := by ring

/-- Cubically scaled two-sided translation defect. -/
def gaussTranslationL2CubicScaledDefectBound {m : ℕ}
    (k : Fin m) (p : Nat.Primes) (A : ℝ) (I : ℕ) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal
    ((I : ℝ) ^ (1 / 3 : ℝ) *
      (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2 *
        ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2))

theorem tendsto_gaussTranslationL2CubicScaledDefectBound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (A : ℝ) :
    Tendsto (gaussTranslationL2CubicScaledDefectBound k p A) atTop (nhds 0) := by
  obtain ⟨D, hD, hcentral⟩ :=
    exists_gaussSampleRatioDefect_signed_central_bound hm k p
  have hhalf : Tendsto (fun I : ℕ => (I / 2 : ℕ)) atTop atTop :=
    GaloisForLFunctions.HTGeometry.tendsto_natDiv_two_atTop
  have hhalfR : Tendsto (fun I : ℕ => ((I / 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hhalf
  have hheightTop : Tendsto
      (fun I : ℕ => gaussPrimeSampleHeightInt p ((I / 2 : ℕ) : ℤ)) atTop atTop := by
    have hmul := Filter.Tendsto.const_mul_atTop (gaussPrimeSampleSpacing_pos p) hhalfR
    simpa only [gaussPrimeSampleHeightInt_nat_eq_spacing_mul] using hmul
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hheightTop.eventually_ge_atTop (2 * (m : ℝ)))
  rw [← Filter.tendsto_add_atTop_iff_nat N]
  refine GaloisForLFunctions.tendsto_tsum_zero_of_dominated
    (F := fun j I => ENNReal.ofReal
      (((I + N : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
        (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2 *
          ‖gaussSampleRatioDefect k p j ((I + N : ℕ) : ℤ)‖ ^ 2)))
    (G := fun j _ => ENNReal.ofReal (4 * D ^ 2 * A ^ 2) *
      GaloisForLFunctions.intPowWeight (4 / 3 : ℝ) j)
    (H := fun j I => if I + N < 2 * j.natAbs ^ 2 then
      ENNReal.ofReal 2 * ENNReal.ofReal
        (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ (4 / 3 : ℝ) *
          ‖gaussSampleRatioDefect k p j ((I + N : ℕ) : ℤ)‖ ^ 2) else 0)
    ?_ ?_ ?_ ?_
  · intro j
    set a : ℕ := j.natAbs with ha
    have hLtop : Tendsto (fun I : ℕ => (((I + N : ℕ) : ℕ) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp
        ((Filter.tendsto_add_atTop_iff_nat N).2 tendsto_id)
    have hdecayR : Tendsto (fun I : ℕ =>
        D ^ 2 * A ^ 2 * (a : ℝ) ^ 2 *
          (((I + N : ℕ) : ℝ) ^ (-(5 / 3 : ℝ)))) atTop (nhds 0) := by
      have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 3)).comp hLtop
      simpa using hpow.const_mul (D ^ 2 * A ^ 2 * (a : ℝ) ^ 2)
    have hdecay : Tendsto (fun I : ℕ => ENNReal.ofReal
        (D ^ 2 * A ^ 2 * (a : ℝ) ^ 2 *
          (((I + N : ℕ) : ℝ) ^ (-(5 / 3 : ℝ))))) atTop (nhds 0) :=
      by
        simpa only [Function.comp_def, ENNReal.ofReal_zero] using
          (ENNReal.continuous_ofReal.tendsto 0).comp hdecayR
    rw [ENNReal.tendsto_nhds_zero] at hdecay ⊢
    intro ε hε
    filter_upwards [hdecay ε hε, Filter.eventually_ge_atTop (max 1 (2 * a ^ 2))]
      with I hmajor hI
    have hINpos : 0 < I + N := by omega
    have hheight : 2 * (m : ℝ) ≤
        gaussPrimeSampleHeightInt p ((((I + N) / 2 : ℕ)) : ℤ) :=
      hN (I + N) (by omega)
    have hband : 2 * a ^ 2 ≤ I + N := by omega
    have hdef := hcentral (I + N) j hINpos hheight (by simpa [ha] using hband)
    refine (ENNReal.ofReal_le_ofReal ?_).trans hmajor
    exact cubic_scaled_term_le_pointwise A D
      ‖gaussSampleRatioDefect k p j ((I + N : ℕ) : ℤ)‖ a (I + N)
      hINpos (norm_nonneg _) (by simpa [ha] using hdef)
  · intro j I
    set a : ℕ := j.natAbs with ha
    by_cases hband : 2 * a ^ 2 ≤ I + N
    · rw [if_neg (not_lt_of_ge hband), add_zero]
      by_cases hL0 : I + N = 0
      · have ha0 : a = 0 := by nlinarith
        subst a
        simp [hL0]
      have hINpos : 0 < I + N := Nat.pos_of_ne_zero hL0
      by_cases ha0 : a = 0
      · subst a
        have hj0 : j = 0 := by omega
        subst j
        have hdef := hcentral (I + N) (0 : ℤ) hINpos
          (hN (I + N) (by omega)) (by simp)
        have hz : ‖gaussSampleRatioDefect k p (0 : ℤ) ((I + N : ℕ) : ℤ)‖ = 0 := by
          have hnorm : ‖gaussSampleRatioDefect k p (0 : ℤ) ((I + N : ℕ) : ℤ)‖ ≤ 0 := by
            simpa using hdef
          exact le_antisymm hnorm (norm_nonneg _)
        rw [hz]
        simp
      · have haPos : 0 < a := Nat.pos_of_ne_zero ha0
        have hdef := hcentral (I + N) j hINpos
          (hN (I + N) (by omega)) (by simpa [ha] using hband)
        have hreal := cubic_scaled_term_le_central A D
          ‖gaussSampleRatioDefect k p j ((I + N : ℕ) : ℤ)‖ a (I + N)
          hINpos haPos (by omega) (norm_nonneg _) (by simpa [ha] using hdef)
        have habs : |(j : ℝ)| = (a : ℝ) := by
          rw [ha, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
        have hG : ENNReal.ofReal (4 * D ^ 2 * A ^ 2) *
            GaloisForLFunctions.intPowWeight (4 / 3 : ℝ) j =
          ENNReal.ofReal (4 * D ^ 2 * A ^ 2 /
            (1 + (a : ℝ)) ^ (4 / 3 : ℝ)) := by
          rw [GaloisForLFunctions.intPowWeight, habs,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
        rw [hG]
        exact ENNReal.ofReal_le_ofReal hreal
    · rw [if_pos (lt_of_not_ge hband)]
      refine le_add_of_le_right ?_
      have hreal := cubic_scaled_term_le_outer A
        ‖gaussSampleRatioDefect k p j ((I + N : ℕ) : ℤ)‖ a (I + N)
        (lt_of_not_ge hband)
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal hreal
  · intro ε hε
    obtain ⟨S, hS⟩ :=
      GaloisForLFunctions.exists_finset_tsum_compl_intPowWeight_le
        (s := (4 / 3 : ℝ)) (by norm_num)
        (C := ENNReal.ofReal (4 * D ^ 2 * A ^ 2)) ENNReal.ofReal_ne_top hε
    exact ⟨S, fun _ => hS⟩
  · have hbase : Tendsto (fun I : ℕ =>
        gaussTranslationL2PowDefectBound k p A (4 / 3 : ℝ)
          ((I + N : ℕ) : ℤ)) atTop (nhds 0) := by
      simpa only [Function.comp_def, id_eq] using
        (tendsto_gaussTranslationL2PowDefectBound hm k p A
          (s := (4 / 3 : ℝ)) (by norm_num)).comp
            ((Filter.tendsto_add_atTop_iff_nat N).2 tendsto_id)
    have hmajor : Tendsto (fun I : ℕ => ENNReal.ofReal 2 *
        gaussTranslationL2PowDefectBound k p A (4 / 3 : ℝ)
          ((I + N : ℕ) : ℤ)) atTop (nhds 0) := by
      simpa only [ENNReal.ofReal_ofNat, mul_zero] using
        ENNReal.Tendsto.const_mul hbase
          (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 : ℝ) ≠ ∞))
    rw [ENNReal.tendsto_nhds_zero] at hmajor ⊢
    intro ε hε
    filter_upwards [hmajor ε hε] with I hI
    refine le_trans ?_ hI
    rw [gaussTranslationL2PowDefectBound, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun j => by
      split_ifs
      · exact le_rfl
      · exact bot_le

theorem gaussTranslationL2CubicScaledDefectBound_eq
    {m : ℕ} (k : Fin m) (p : Nat.Primes) (A : ℝ) (I : ℕ) :
    gaussTranslationL2CubicScaledDefectBound k p A I =
      ENNReal.ofReal ((I : ℝ) ^ (1 / 3 : ℝ)) *
        gaussTranslationL2DefectBound k p A (I : ℤ) := by
  rw [gaussTranslationL2CubicScaledDefectBound, gaussTranslationL2DefectBound,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg I) _)]

/-- The existing quadratic Fourier defect is little-o of `I⁻¹ᐟ³`. -/
theorem tendsto_gaussTranslationL2DefectBound_cubic_scale
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (A : ℝ) :
    Tendsto (fun I : ℕ => ENNReal.ofReal ((I : ℝ) ^ (1 / 3 : ℝ)) *
      gaussTranslationL2DefectBound k p A (I : ℤ)) atTop (nhds 0) := by
  simpa only [← gaussTranslationL2CubicScaledDefectBound_eq] using
    tendsto_gaussTranslationL2CubicScaledDefectBound hm k p A

/-- At every depth `m ≥ 3`, the translation defect beats the exact critical
relative scale `I⁻¹ᐟᵐ`. -/
theorem tendsto_gaussTranslationL2DefectBound_depth_scale
    {m : ℕ} (hm3 : 3 ≤ m) (k : Fin m) (p : Nat.Primes) (A : ℝ) :
    Tendsto (fun I : ℕ => ENNReal.ofReal ((I : ℝ) ^ (1 / (m : ℝ))) *
      gaussTranslationL2DefectBound k p A (I : ℤ)) atTop (nhds 0) := by
  have hm : 1 ≤ m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by positivity
  have hexp : (1 / (m : ℝ) : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hmR (by norm_num : (0 : ℝ) < 3)]
    norm_num
    exact_mod_cast hm3
  have hbase := tendsto_gaussTranslationL2DefectBound_cubic_scale hm k p A
  rw [ENNReal.tendsto_nhds_zero] at hbase ⊢
  intro ε hε
  filter_upwards [hbase ε hε, Filter.eventually_ge_atTop 1] with I hI hI1
  have hscale : (I : ℝ) ^ (1 / (m : ℝ)) ≤ (I : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hI1) hexp
  refine le_trans ?_ hI
  gcongr

end

end RHTower
