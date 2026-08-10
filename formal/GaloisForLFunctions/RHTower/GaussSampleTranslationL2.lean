import GaloisForLFunctions.RHTower.GaussSampleIntegerLattice
import GaloisForLFunctions.RHTower.GaussPrimeScaleFourier
import GaloisForLFunctions.HTGeometry.BandSplitVanishingSum
import GaloisForLFunctions.HTGeometry.FarBandRatioTail

/-!
# The moving-translation estimate in `ℓ²`

The `ℓ²` defect of the moving-translation estimate at the lattice index `i` is

`∑_(j ∈ ℤ) ‖b̂(j)‖² ‖d_(i+j)/d_i - e^(2π i j δ_i)‖²`,

which is the squared `L²(ℝ/ℤ)` distance between the normalized shifted block and the translate
`b(· - δ_i)` of the prime-scale amplitude.  It tends to zero.

The estimate is the band split: every single mode vanishes by the lattice ratio law, the modes
with `2|j| ≤ i` are dominated by the fixed quadratic weight because `i/|i+j| ≤ 2` there, and the
modes with `2|j| > i` are dominated by the far-band ratio weight, which vanishes.
-/

namespace RHTower

open Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ## The archimedean constant relating magnitude and value -/

/-- The `2m`-th power of the archimedean prefactor of a Gauss component. -/
def gaussArchConst (m : ℕ) : ℝ :=
  ((Real.pi / (m : ℝ)) ^ gaussComponentDelta m) ^ (2 * m)

theorem gaussArchConst_pos {m : ℕ} (hm : 1 ≤ m) : 0 < gaussArchConst m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hbase : (0 : ℝ) < Real.pi / (m : ℝ) := by positivity
  exact pow_pos (Real.rpow_pos_of_pos hbase _) _

/-- The sampled energy is the archimedean constant times the `2m`-th power of the sampled value. -/
theorem gaussComponentPrimeMagnitudeEnergy_eq {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (n : ℕ) :
    gaussComponentPrimeMagnitudeEnergy k p n =
      gaussArchConst m * ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m) := by
  have hheight : gaussPrimeSampleHeight p n
      = 2 * Real.pi * ((n : ℝ) + 1) / Real.log (p : ℝ) := rfl
  rw [gaussComponentPrimeMagnitudeEnergy, gaussSampleValue_natSucc, ← hheight,
    gaussComponentVerticalMagnitude_eq_norm_value hm k (gaussPrimeSampleHeight_pos p n),
    mul_pow, gaussArchConst]

/-- The `2m`-th power of the sampled value at an arbitrary nonzero frequency. -/
theorem norm_gaussSampleValue_pow_eq {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {i : ℤ} (hi : i ≠ 0) :
    gaussArchConst m * ‖gaussSampleValue k p i‖ ^ (2 * m) =
      gaussComponentPrimeMagnitudeEnergy k p (i.natAbs - 1) := by
  have hkey : ∀ a : ℤ, 0 < a →
      gaussArchConst m * ‖gaussSampleValue k p a‖ ^ (2 * m) =
        gaussComponentPrimeMagnitudeEnergy k p (a.natAbs - 1) := by
    intro a ha
    have hcast : ((a.natAbs - 1 : ℕ) : ℤ) + 1 = a := by omega
    rw [gaussComponentPrimeMagnitudeEnergy_eq hm k p (a.natAbs - 1), hcast]
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · have hpos' : 0 < -i := by omega
    have habs : (-i).natAbs = i.natAbs := by omega
    rw [← habs, ← hkey (-i) hpos', gaussSampleValue_neg]
    congr 2
    exact (Complex.norm_conj _).symm
  · exact hkey i hpos

/-! ## The ratio bound on the lattice -/

/-- **Uniform lattice ratio bound.**  The `2m`-th power of the sampled value at a shifted
frequency is controlled by its value at the base frequency, with the harmonic factor. -/
theorem exists_norm_gaussSampleValue_pow_ratio_bound {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_gaussComponentPrimeMagnitudeEnergy_bounds hm k p
  refine ⟨C / c, div_pos hC hc, fun a b ha hb' => ?_⟩
  have harch := gaussArchConst_pos hm
  have haabs : 1 ≤ a.natAbs := by omega
  have hbabs : 1 ≤ b.natAbs := by omega
  have haR : ((a.natAbs - 1 : ℕ) : ℝ) + 1 = (a.natAbs : ℝ) := by
    have : ((a.natAbs - 1 : ℕ) : ℝ) = (a.natAbs : ℝ) - 1 := by
      have : (a.natAbs - 1 : ℕ) + 1 = a.natAbs := by omega
      have hcast : (((a.natAbs - 1 : ℕ) + 1 : ℕ) : ℝ) = (a.natAbs : ℝ) := by exact_mod_cast this
      push_cast at hcast
      linarith
    rw [this]
    ring
  have hbR : ((b.natAbs - 1 : ℕ) : ℝ) + 1 = (b.natAbs : ℝ) := by
    have : ((b.natAbs - 1 : ℕ) : ℝ) = (b.natAbs : ℝ) - 1 := by
      have : (b.natAbs - 1 : ℕ) + 1 = b.natAbs := by omega
      have hcast : (((b.natAbs - 1 : ℕ) + 1 : ℕ) : ℝ) = (b.natAbs : ℝ) := by exact_mod_cast this
      push_cast at hcast
      linarith
    rw [this]
    ring
  have hupper : gaussArchConst m * ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ) ≤ C := by
    rw [norm_gaussSampleValue_pow_eq hm k p ha, ← haR]
    have hstep := (hb (a.natAbs - 1)).2
    have hden : (0 : ℝ) < ((a.natAbs - 1 : ℕ) : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hden] at hstep
    exact hstep
  have hlower : c ≤ gaussArchConst m * ‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ) := by
    rw [norm_gaussSampleValue_pow_eq hm k p hb', ← hbR]
    have hstep := (hb (b.natAbs - 1)).1
    have hden : (0 : ℝ) < ((b.natAbs - 1 : ℕ) : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hden] at hstep
    exact hstep
  have hXpos : 0 < gaussArchConst m := harch
  set X : ℝ := gaussArchConst m * ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ) with hX
  set Y : ℝ := gaussArchConst m * ‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ) with hY
  have hXY : X ≤ C / c * Y := by
    calc X ≤ C := hupper
      _ = C / c * c := by field_simp
      _ ≤ C / c * Y := mul_le_mul_of_nonneg_left hlower (by positivity)
  have hXe : X = gaussArchConst m * (‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)) := by
    rw [hX]; ring
  have hYe : Y = gaussArchConst m * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)) := by
    rw [hY]; ring
  rw [hXe, hYe] at hXY
  refine le_of_mul_le_mul_left ?_ hXpos
  calc gaussArchConst m * (‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ))
      ≤ C / c * (gaussArchConst m * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ))) := hXY
    _ = gaussArchConst m * (C / c * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ))) := by
        ring

/-! ## The defect bound -/

theorem norm_gaussSampleRotation {m : ℕ} (p : Nat.Primes) (j i : ℤ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
      ((gaussSamplePhase m p i : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hform : (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
      ((gaussSamplePhase m p i : ℝ) : ℂ))
      = ((2 * Real.pi * (j : ℝ) * gaussSamplePhase m p i : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hform]
  simp

/-- **Pointwise defect bound.**  The squared lattice defect is at most `4 + 2K·I/|I+j|`. -/
theorem norm_gaussSampleRatioDefect_sq_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ}
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (j : ℤ) :
    ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2
      ≤ 4 + 2 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) := by
  set R : ℝ := ‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖ with hR
  have hR0 : 0 ≤ R := by positivity
  have htri : ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ≤ R + 1 := by
    rw [gaussSampleRatioDefect]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_gaussSampleRotation]
  have hsq : ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 ≤ 2 * R ^ 2 + 2 := by
    have hnn : (0 : ℝ) ≤ ‖gaussSampleRatioDefect k p j (I : ℤ)‖ := norm_nonneg _
    nlinarith [sq_nonneg (R - 1), htri, hnn]
  have hpow : R ^ 2 ≤ 1 + R ^ (2 * m) := by
    rcases le_or_gt R 1 with h | h
    · have h1 : R ^ 2 ≤ 1 := by nlinarith
      have h2 : (0 : ℝ) ≤ R ^ (2 * m) := by positivity
      linarith
    · have h1 : R ^ 2 ≤ R ^ (2 * m) := by
        exact pow_le_pow_right₀ h.le (by omega)
      linarith
  have hratio : R ^ (2 * m) ≤ 2 * K * (I : ℝ) / (2 * (((I : ℤ) + j).natAbs : ℝ)) := by
    by_cases hI : (I : ℤ) = 0
    · have hzero : ‖gaussSampleValue k p (I : ℤ)‖ = 0 := by
        rw [hI, gaussSampleValue_zero, norm_zero]
      have hR' : R = 0 := by rw [hR, hzero, div_zero]
      have hInat : (I : ℝ) = 0 := by
        have : I = 0 := by omega
        simp [this]
      rw [hR', hInat]
      simp [zero_pow (show 2 * m ≠ 0 by omega)]
    by_cases hn : ((I : ℤ) + j) = 0
    · have hzero : ‖gaussSampleValue k p ((I : ℤ) + j)‖ = 0 := by
        rw [hn, gaussSampleValue_zero, norm_zero]
      have hR' : R = 0 := by rw [hR, hzero, zero_div]
      have hnat : ((((I : ℤ) + j).natAbs : ℕ) : ℝ) = 0 := by
        rw [hn]
        simp
      rw [hR', hnat]
      simp [zero_pow (show 2 * m ≠ 0 by omega)]
    have hIpos : ‖gaussSampleValue k p (I : ℤ)‖ > 0 :=
      norm_pos_iff.mpr (gaussSampleValue_ne_zero hm k p hI)
    have hnpos : (0 : ℝ) < (((I : ℤ) + j).natAbs : ℝ) := by
      have : 0 < ((I : ℤ) + j).natAbs := by omega
      exact_mod_cast this
    have hbase := hKb ((I : ℤ) + j) (I : ℤ) hn hI
    have hIabs : (((I : ℤ)).natAbs : ℝ) = (I : ℝ) := by
      simp
    rw [hIabs] at hbase
    have hRpow : R ^ (2 * m)
        = ‖gaussSampleValue k p ((I : ℤ) + j)‖ ^ (2 * m) /
          ‖gaussSampleValue k p (I : ℤ)‖ ^ (2 * m) := by
      rw [hR, div_pow]
    rw [hRpow]
    have hdenpos : (0 : ℝ) < ‖gaussSampleValue k p (I : ℤ)‖ ^ (2 * m) := by positivity
    rw [div_le_div_iff₀ hdenpos (by positivity)]
    nlinarith [hbase, hdenpos, hnpos]
  have hfinal : 2 * K * (I : ℝ) / (2 * (((I : ℤ) + j).natAbs : ℝ)) * 2
      ≤ 2 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (((I : ℤ) + j).natAbs : ℝ) from by positivity) with h | h
    · rw [← h]
      simp
    · rw [div_mul_eq_mul_div,
        div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * (((I : ℤ) + j).natAbs : ℝ)) h]
      apply le_of_eq
      ring
  nlinarith [hsq, hpow, hratio, hfinal]

/-! ## The `ℓ²` moving-translation estimate -/

theorem tendsto_gaussSampleRatioDefect_nat
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (j : ℤ) :
    Tendsto (fun I : ℕ => gaussSampleRatioDefect k p j (I : ℤ)) atTop (nhds 0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  have h := tendsto_gaussSampleRatioDefect hm k p j
  refine h.congr fun n => ?_
  rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring]

/-- The `ℓ²` defect of the moving-translation estimate at the lattice index `i`. -/
def gaussTranslationL2Defect {m : ℕ} (k : Fin m) (p : Nat.Primes) (i : ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal
    (‖gaussPrimeScaleFourierCoefficient (p : ℝ) j‖ ^ 2 * ‖gaussSampleRatioDefect k p j i‖ ^ 2)

/-- The `ℓ²` moving-translation defect with the universal decay weight `A/(1+|j|)`. -/
def gaussTranslationL2DefectBound {m : ℕ} (k : Fin m) (p : Nat.Primes) (A : ℝ) (i : ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal
    (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2 * ‖gaussSampleRatioDefect k p j i‖ ^ 2)

/-- **The moving-translation estimate, in its uniform form.**  For every decay constant the
weighted `ℓ²` defect vanishes; the weight does not involve the amplitude, so the estimate is
uniform over every family of amplitudes with a common decay constant. -/
theorem tendsto_gaussTranslationL2DefectBound {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (A : ℝ) :
    Tendsto (fun I : ℕ => gaussTranslationL2DefectBound k p A (I : ℤ)) atTop (nhds 0) := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_gaussSampleValue_pow_ratio_bound hm k p
  refine GaloisForLFunctions.tendsto_tsum_zero_of_dominated
    (F := fun j I => ENNReal.ofReal
      (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2 *
        ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2))
    (G := fun j _ => ENNReal.ofReal ((4 + 4 * K) * A ^ 2) * GaloisForLFunctions.intQuadWeight j)
    (H := fun j I => if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
        ENNReal.ofReal (2 * K * A ^ 2 * (I : ℝ) /
          ((1 + (j.natAbs : ℝ)) ^ 2 * (((I : ℤ) + j).natAbs : ℝ))) else 0)
    ?_ ?_ ?_ ?_
  · -- every mode vanishes
    intro j
    have hdef := tendsto_gaussSampleRatioDefect_nat hm k p j
    have hnorm : Tendsto (fun I : ℕ => ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2)
        atTop (nhds 0) := by
      have h1 : Tendsto (fun I : ℕ => ‖gaussSampleRatioDefect k p j (I : ℤ)‖)
          atTop (nhds 0) := by simpa using hdef.norm
      simpa using h1.pow 2
    have hmul := hnorm.const_mul (A ^ 2 / (1 + (j.natAbs : ℝ)) ^ 2)
    rw [mul_zero] at hmul
    have hcont := (ENNReal.continuous_ofReal.tendsto 0).comp hmul
    simpa [Function.comp_def] using hcont
  · -- the pointwise domination
    intro j I
    set a : ℕ := j.natAbs with ha
    set n : ℕ := ((I : ℤ) + j).natAbs with hn
    have hbound := norm_gaussSampleRatioDefect_sq_le hm k p hKb I j
    have hden : (0 : ℝ) < (1 + (a : ℝ)) ^ 2 := by positivity
    have hquad : GaloisForLFunctions.intQuadWeight j
        = ENNReal.ofReal (1 / (1 + (a : ℝ)) ^ 2) := by
      rw [GaloisForLFunctions.intQuadWeight, ha]
      congr 2
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have hGval : ENNReal.ofReal ((4 + 4 * K) * A ^ 2) *
        GaloisForLFunctions.intQuadWeight j
        = ENNReal.ofReal ((4 + 4 * K) * A ^ 2 / (1 + (a : ℝ)) ^ 2) := by
      rw [hquad, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hnn : 0 ≤ ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 := by positivity
    have hAsq : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    have hstep : A ^ 2 / (1 + (a : ℝ)) ^ 2 *
        ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2
        ≤ A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 2 * K * (I : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    by_cases hcase : I < 2 * a
    · by_cases hn0 : n = 0
      · rw [if_neg (by simp [hn0])]
        rw [add_zero, hGval]
        refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
        have hzero : ((n : ℕ) : ℝ) = 0 := by rw [hn0]; simp
        rw [hzero, div_zero, add_zero]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hden hden]
        nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 4 * K) hAsq) hden.le]
      · rw [if_pos ⟨hcase, hn0⟩, hGval, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
        have hnpos : (0 : ℝ) < (n : ℝ) := by
          have : 0 < n := Nat.pos_of_ne_zero hn0
          exact_mod_cast this
        have hexp : A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 2 * K * (I : ℝ) / (n : ℝ))
            = 4 * A ^ 2 / (1 + (a : ℝ)) ^ 2 +
              2 * K * A ^ 2 * (I : ℝ) / ((1 + (a : ℝ)) ^ 2 * (n : ℝ)) := by
          field_simp
        rw [hexp]
        have h1 : 4 * A ^ 2 / (1 + (a : ℝ)) ^ 2 ≤ (4 + 4 * K) * A ^ 2 / (1 + (a : ℝ)) ^ 2 := by
          rw [div_le_div_iff₀ hden hden]
          nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 4 * K) hAsq) hden.le]
        linarith
    · rw [if_neg (by simp [hcase]), add_zero, hGval]
      refine le_trans (ENNReal.ofReal_le_ofReal hstep) (ENNReal.ofReal_le_ofReal ?_)
      have hIn : (I : ℝ) ≤ 2 * (n : ℝ) := by
        have : I ≤ 2 * n := by omega
        exact_mod_cast this
      have hratio : 2 * K * (I : ℝ) / (n : ℝ) ≤ 4 * K := by
        rcases Nat.eq_zero_or_pos n with h | h
        · have : ((n : ℕ) : ℝ) = 0 := by rw [h]; simp
          rw [this, div_zero]
          positivity
        · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
          rw [div_le_iff₀ hnpos]
          nlinarith [hK.le, hIn]
      have hle : A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 2 * K * (I : ℝ) / (n : ℝ))
          ≤ A ^ 2 / (1 + (a : ℝ)) ^ 2 * (4 + 4 * K) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      refine hle.trans (le_of_eq ?_)
      field_simp
  · -- uniformly small `G`-tails
    intro ε hε
    obtain ⟨S, hS⟩ := GaloisForLFunctions.exists_finset_tsum_compl_intQuadWeight_le
      (C := ENNReal.ofReal ((4 + 4 * K) * A ^ 2)) ENNReal.ofReal_ne_top hε
    exact ⟨S, fun _ => hS⟩
  · -- the far-band totals vanish
    have hc : (0 : ℝ) ≤ 2 * K * A ^ 2 := by positivity
    exact GaloisForLFunctions.tendsto_tsum_farBandRatio_zero hc

/-- **Uniform moving-translation estimate.**  Every coefficient family with decay `A/(1+|j|)` has
vanishing weighted `ℓ²` defect, with a rate depending only on `A`. -/
theorem tendsto_gaussTranslationL2Defect_of_decay {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) {A : ℝ} {c : ℤ → ℂ} (hc : ∀ j : ℤ, ‖c j‖ ≤ A / (1 + (j.natAbs : ℝ))) :
    Tendsto (fun I : ℕ => ∑' j : ℤ,
      ENNReal.ofReal (‖c j‖ ^ 2 * ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2))
      atTop (nhds 0) := by
  have hbase := tendsto_gaussTranslationL2DefectBound hm k p A
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hbase ε hε] with I hI
  refine le_trans ?_ hI
  rw [gaussTranslationL2DefectBound]
  refine ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal ?_
  have hnn : 0 ≤ ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 := by positivity
  refine mul_le_mul_of_nonneg_right ?_ hnn
  have h2 := pow_le_pow_left₀ (norm_nonneg (c j)) (hc j) 2
  rwa [div_pow] at h2

/-- **The moving-translation estimate.**  The `ℓ²` defect between the normalized shifted block and
the translate of the prime-scale amplitude vanishes. -/
theorem tendsto_gaussTranslationL2Defect {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun I : ℕ => gaussTranslationL2Defect k p (I : ℤ)) atTop (nhds 0) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  refine tendsto_gaussTranslationL2Defect_of_decay hm k p
    (A := 2 * (Real.sqrt (p : ℝ) - 1) / min (Real.log (p : ℝ) / 2) (2 * Real.pi))
    (c := fun j => gaussPrimeScaleFourierCoefficient (p : ℝ) j) fun j => ?_
  have habs : |(j : ℝ)| = (j.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hbase := norm_gaussPrimeScaleFourierCoefficient_le hp j
  rwa [habs] at hbase

end

end RHTower
