import GaloisForLFunctions.RHTower.BurnolAlternatingHarmonic
import GaloisForLFunctions.RHTower.BurnolReflectedRawSource

/-!
# The improper mass of the reflected Burnol source

Truncating the reflected source at `R` and integrating the fixed finite co-Poisson window gives the
exact staircase formula

`∫_0^R f₀^∨ = (2⌊R/2⌋ - ⌊R⌋) + R (H_{⌊R⌋} - H_{⌊R/2⌋} - log 2)`.

With `b = ⌊R⌋`, `c = ⌊R/2⌋` and `j = b - 2c ∈ {0,1}`, the alternating-series identity gives
`H_b - H_c - log 2 = -I_{2c} + j/(2c+1)`, and `I_{2c} = 1/(2(2c+1)) + O(c^{-2})`.  The oscillating
terms `2c - b` and `R j/(2c+1)` cancel against the leading `1/(2(2c+1))`, leaving

`∫_0^R f₀^∨ → ζ(0) = -1/2`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## Windows of the indicator -/

theorem burnolWindowIntegral_full {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b ≤ R) :
    (∫ t in (0 : ℝ)..R, Set.indicator (Icc a b) (fun _ => (1 : ℂ)) t) = ((b - a : ℝ) : ℂ) := by
  have hR : (0 : ℝ) ≤ R := le_trans (le_trans ha.le hab) hbR
  have hinter : Ioc (0 : ℝ) R ∩ Icc a b = Icc a b := by
    refine Set.inter_eq_right.mpr fun x hx => ⟨lt_of_lt_of_le ha hx.1, le_trans hx.2 hbR⟩
  rw [intervalIntegral.integral_of_le hR, MeasureTheory.setIntegral_indicator measurableSet_Icc,
    hinter, setIntegral_const, Real.volume_real_Icc, Complex.real_smul]
  rw [max_eq_left (by linarith)]
  ring

theorem burnolWindowIntegral_cut {a b R : ℝ} (ha : 0 < a) (haR : a ≤ R) (hRb : R ≤ b) :
    (∫ t in (0 : ℝ)..R, Set.indicator (Icc a b) (fun _ => (1 : ℂ)) t) = ((R - a : ℝ) : ℂ) := by
  have hR : (0 : ℝ) ≤ R := le_trans ha.le haR
  have hinter : Ioc (0 : ℝ) R ∩ Icc a b = Icc a R := by
    ext x
    constructor
    · rintro ⟨⟨-, hxR⟩, hxa, -⟩
      exact ⟨hxa, hxR⟩
    · rintro ⟨hxa, hxR⟩
      exact ⟨⟨lt_of_lt_of_le ha hxa, hxR⟩, hxa, le_trans hxR hRb⟩
  rw [intervalIntegral.integral_of_le hR, MeasureTheory.setIntegral_indicator measurableSet_Icc,
    hinter, setIntegral_const, Real.volume_real_Icc, Complex.real_smul]
  rw [max_eq_left (by linarith)]
  ring

theorem burnolWindowIntegral_zero {a b R : ℝ} (hR0 : 0 ≤ R) (hRa : R < a) :
    (∫ t in (0 : ℝ)..R, Set.indicator (Icc a b) (fun _ => (1 : ℂ)) t) = 0 := by
  have hinter : Ioc (0 : ℝ) R ∩ Icc a b = ∅ := by
    ext x
    constructor
    · rintro ⟨⟨-, hxR⟩, hxa, -⟩
      exact absurd (lt_of_le_of_lt (le_trans hxa hxR) hRa) (lt_irrefl _)
    · exact fun h => absurd h (Set.notMem_empty x)
  rw [intervalIntegral.integral_of_le hR0, MeasureTheory.setIntegral_indicator measurableSet_Icc,
    hinter]
  simp

theorem burnolSeedDilate_eq_indicator {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    coPoissonWindowIndicatorSeed 1 2 (t / (k : ℝ)) =
      Set.indicator (Icc (k : ℝ) (2 * (k : ℝ))) (fun _ => (1 : ℂ)) t := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  by_cases hmem : t ∈ Icc (k : ℝ) (2 * (k : ℝ))
  · have hdiv : t / (k : ℝ) ∈ Icc (1 : ℝ) 2 := by
      constructor
      · rw [le_div_iff₀ hkR, one_mul]
        exact hmem.1
      · rw [div_le_iff₀ hkR]
        linarith [hmem.2]
    rw [coPoissonWindowIndicatorSeed_of_mem hdiv, Set.indicator_of_mem hmem]
  · have hdiv : t / (k : ℝ) ∉ Icc (1 : ℝ) 2 := by
      intro hc
      obtain ⟨hc1, hc2⟩ := hc
      rw [le_div_iff₀ hkR, one_mul] at hc1
      rw [div_le_iff₀ hkR] at hc2
      exact hmem ⟨hc1, by linarith⟩
    rw [coPoissonWindowIndicatorSeed_of_notMem hdiv, Set.indicator_of_notMem hmem]

theorem burnolIntervalIntegrable_seedDilate {k : ℕ} (hk : 1 ≤ k) (R : ℝ) :
    IntervalIntegrable (fun t : ℝ => coPoissonWindowIndicatorSeed 1 2 (t / (k : ℝ)))
      volume 0 R := by
  constructor <;>
  · refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      (((measurable_coPoissonWindowIndicatorSeed 1 2).comp
        (measurable_id.div_const (k : ℝ))).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [burnolSeedDilate_eq_indicator hk]
    by_cases hmem : x ∈ Icc (k : ℝ) (2 * (k : ℝ))
    · rw [Set.indicator_of_mem hmem, norm_one]
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      norm_num

/-! ## The exact truncated mass -/

theorem integral_burnolReflectedRawSource_eq {R : ℝ} (hR : 0 < R) :
    (∫ t in (0 : ℝ)..R, burnolReflectedRawSource t) =
      (((2 * (⌊R / 2⌋₊ : ℝ) - (⌊R⌋₊ : ℝ)) +
        R * (((harmonic ⌊R⌋₊ : ℚ) : ℝ) - ((harmonic ⌊R / 2⌋₊ : ℚ) : ℝ) -
          Real.log 2) : ℝ) : ℂ) := by
  set N : ℕ := ⌊R / (1 / 2 : ℝ)⌋₊ with hNdef
  set b : ℕ := ⌊R⌋₊ with hbdef
  set c : ℕ := ⌊R / 2⌋₊ with hcdef
  have hcb : c ≤ b := Nat.floor_le_floor (by linarith)
  have hbN : b ≤ N := Nat.floor_le_floor (by rw [show R / (1 / 2 : ℝ) = 2 * R by ring]; linarith)
  have hcR : (c : ℝ) ≤ R / 2 := Nat.floor_le (by linarith)
  have hbR : (b : ℝ) ≤ R := Nat.floor_le hR.le
  -- pointwise reduction to a fixed finite window sum
  have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) R, burnolReflectedRawSource t =
      (∑ k ∈ Finset.Icc 1 N, (((k : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ))) - ((Real.log 2 : ℝ) : ℂ) := by
    intro t ht
    rw [Set.uIoc_of_le hR.le] at ht
    rw [burnolReflectedRawSource, burnolCoPoissonRightSum_eq_sub_correction,
      burnolReflectedCorrection, abs_of_pos ht.1,
      coPoissonSum_eq_fixed_finset_sum (b := 1 / 2) (by norm_num) burnolReflectedSeedSupport
        ht.1 ht.2]
  have hintSum : IntervalIntegrable
      (fun t : ℝ => ∑ k ∈ Finset.Icc 1 N, (((k : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ))) volume 0 R := by
    have h := IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := R) (Finset.Icc 1 N)
      (f := fun (k : ℕ) (t : ℝ) => (((k : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ)))
      (fun k hk => (burnolIntervalIntegrable_seedDilate (Finset.mem_Icc.mp hk).1 R).const_mul _)
    have heq : (∑ x ∈ Finset.Icc 1 N, fun t : ℝ => (((x : ℕ) : ℝ) : ℂ)⁻¹ *
        coPoissonWindowIndicatorSeed 1 2 (t / ((x : ℕ) : ℝ))) =
        fun t : ℝ => ∑ x ∈ Finset.Icc 1 N, (((x : ℕ) : ℝ) : ℂ)⁻¹ *
          coPoissonWindowIndicatorSeed 1 2 (t / ((x : ℕ) : ℝ)) := by
      funext t
      rw [Finset.sum_apply]
    rwa [heq] at h
  rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hpt),
    intervalIntegral.integral_sub hintSum intervalIntegrable_const,
    intervalIntegral.integral_finsetSum
      (fun k hk => (burnolIntervalIntegrable_seedDilate (Finset.mem_Icc.mp hk).1 R).const_mul _),
    intervalIntegral.integral_const]
  -- split the window sum into the three regimes
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := (Finset.Ico_add_one_right_eq_Icc 1 N).symm
  have hsplit1 := Finset.sum_Ico_consecutive
    (fun k : ℕ => (((k : ℕ) : ℝ) : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..R, coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ)))
    (by omega : 1 ≤ c + 1) (by omega : c + 1 ≤ N + 1)
  have hsplit2 := Finset.sum_Ico_consecutive
    (fun k : ℕ => (((k : ℕ) : ℝ) : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..R, coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ)))
    (by omega : c + 1 ≤ b + 1) (by omega : b + 1 ≤ N + 1)
  have hlow : (∑ k ∈ Finset.Ico 1 (c + 1), (((k : ℕ) : ℝ) : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..R, coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ))) = (c : ℂ) := by
    have hterm : ∀ k ∈ Finset.Ico 1 (c + 1), (((k : ℕ) : ℝ) : ℂ)⁻¹ *
        (∫ t in (0 : ℝ)..R, coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ))) = 1 := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
      have hkc : k ≤ c := by omega
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hkcR : (k : ℝ) ≤ (c : ℝ) := by exact_mod_cast hkc
      have hfull : 2 * (k : ℝ) ≤ R := by linarith
      have hkne : (((k : ℕ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hkR)
      rw [intervalIntegral.integral_congr (fun t _ => burnolSeedDilate_eq_indicator hk1 t),
        burnolWindowIntegral_full hkR (by linarith) hfull,
        show 2 * ((k : ℕ) : ℝ) - ((k : ℕ) : ℝ) = ((k : ℕ) : ℝ) by ring]
      exact inv_mul_cancel₀ hkne
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico]
    simp
  have hmid : (∑ k ∈ Finset.Ico (c + 1) (b + 1), (((k : ℕ) : ℝ) : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..R, coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ))) =
      (R : ℂ) * (((harmonic b : ℚ) : ℝ) - ((harmonic c : ℚ) : ℝ) : ℝ) - ((b : ℂ) - (c : ℂ)) := by
    have hterm : ∀ k ∈ Finset.Ico (c + 1) (b + 1), (((k : ℕ) : ℝ) : ℂ)⁻¹ *
        (∫ t in (0 : ℝ)..R, coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ))) =
        (R : ℂ) * (((1 : ℝ) / (k : ℝ) : ℝ) : ℂ) - 1 := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
      have hk0 : 1 ≤ k := by omega
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
      have hkb : k ≤ b := by omega
      have hkbR : (k : ℝ) ≤ R := le_trans (by exact_mod_cast hkb) hbR
      have hck : c < k := by omega
      have hcut : R ≤ 2 * (k : ℝ) := by
        have : R / 2 < (k : ℝ) := (Nat.floor_lt (by linarith)).mp hck
        linarith
      have hkne : ((k : ℕ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      rw [intervalIntegral.integral_congr (fun t _ => burnolSeedDilate_eq_indicator hk0 t),
        burnolWindowIntegral_cut hkR hkbR hcut]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hsum : (∑ k ∈ Finset.Ico (c + 1) (b + 1), (((1 : ℝ) / (k : ℝ) : ℝ) : ℂ)) =
        ((((harmonic b : ℚ) : ℝ) - ((harmonic c : ℚ) : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum, Finset.Ico_add_one_right_eq_Icc (c + 1) b,
        burnolHarmonicWindow_eq_sub (by omega) (by omega)]
      norm_num
    have hcard : (∑ _k ∈ Finset.Ico (c + 1) (b + 1), (1 : ℂ)) = (b : ℂ) - (c : ℂ) := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
        show b + 1 - (c + 1) = b - c by omega, Nat.cast_sub hcb]
    rw [hsum, hcard]

  have hhigh : (∑ k ∈ Finset.Ico (b + 1) (N + 1), (((k : ℕ) : ℝ) : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..R, coPoissonWindowIndicatorSeed 1 2 (t / ((k : ℕ) : ℝ))) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hk1, -⟩ := Finset.mem_Ico.mp hk
    have hk0 : 1 ≤ k := by omega
    have hbk : b < k := by omega
    have hRk : R < (k : ℝ) := (Nat.floor_lt hR.le).mp hbk
    rw [intervalIntegral.integral_congr (fun t _ => burnolSeedDilate_eq_indicator hk0 t),
      burnolWindowIntegral_zero hR.le hRk, mul_zero]
  have hpull : (∑ i ∈ Finset.Icc 1 N, ∫ x in (0 : ℝ)..R,
        (((i : ℕ) : ℝ) : ℂ)⁻¹ * coPoissonWindowIndicatorSeed 1 2 (x / ((i : ℕ) : ℝ))) =
      ∑ i ∈ Finset.Icc 1 N, (((i : ℕ) : ℝ) : ℂ)⁻¹ *
        ∫ x in (0 : ℝ)..R, coPoissonWindowIndicatorSeed 1 2 (x / ((i : ℕ) : ℝ)) :=
    Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
  rw [hpull, hIcc, ← hsplit1, ← hsplit2, hlow, hmid, hhigh]
  simp only [sub_zero, Complex.real_smul]
  push_cast
  ring

/-! ## The improper mass -/

/-- The truncated mass of the reflected source, as a real staircase. -/
def burnolReflectedTruncMass (R : ℝ) : ℝ :=
  (2 * (⌊R / 2⌋₊ : ℝ) - (⌊R⌋₊ : ℝ)) +
    R * (((harmonic ⌊R⌋₊ : ℚ) : ℝ) - ((harmonic ⌊R / 2⌋₊ : ℚ) : ℝ) - Real.log 2)

theorem integral_burnolReflectedRawSource_eq_truncMass {R : ℝ} (hR : 0 < R) :
    (∫ t in (0 : ℝ)..R, burnolReflectedRawSource t) = ((burnolReflectedTruncMass R : ℝ) : ℂ) :=
  integral_burnolReflectedRawSource_eq hR

/-- The integer part is either twice the half-integer part or one more. -/
theorem burnolFloorPair {R : ℝ} (hR : 0 ≤ R) :
    ⌊R⌋₊ = 2 * ⌊R / 2⌋₊ ∨ ⌊R⌋₊ = 2 * ⌊R / 2⌋₊ + 1 := by
  set c : ℕ := ⌊R / 2⌋₊ with hc
  have hcR : (c : ℝ) ≤ R / 2 := Nat.floor_le (by linarith)
  have hlow : 2 * c ≤ ⌊R⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    linarith
  have hhigh : ⌊R⌋₊ ≤ 2 * c + 1 := by
    by_contra hcon
    have h2 : 2 * c + 2 ≤ ⌊R⌋₊ := by omega
    have h2R : ((2 * c + 2 : ℕ) : ℝ) ≤ R := le_trans (by exact_mod_cast h2) (Nat.floor_le hR)
    have hcc : c + 1 ≤ ⌊R / 2⌋₊ := by
      refine Nat.le_floor ?_
      push_cast at h2R ⊢
      linarith
    omega
  omega

/-- **The reflected truncated mass converges to `ζ(0) = -1/2`.** -/
theorem abs_burnolReflectedTruncMass_add_half_le {R : ℝ} (hR : 2 ≤ R) :
    |burnolReflectedTruncMass R + 1 / 2| ≤ 1 / (R - 1) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  set c : ℕ := ⌊R / 2⌋₊ with hc
  set b : ℕ := ⌊R⌋₊ with hb
  have hcR : (c : ℝ) ≤ R / 2 := Nat.floor_le (by linarith)
  have hcR' : R / 2 < (c : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbR : (b : ℝ) ≤ R := Nat.floor_le hR0
  have hbR' : R < (b : ℝ) + 1 := Nat.lt_floor_add_one _
  have hden : (0 : ℝ) < 2 * (c : ℝ) + 1 := by linarith
  have hRc : R - 1 ≤ 2 * (c : ℝ) + 1 := by linarith
  have hR1 : (0 : ℝ) < R - 1 := by linarith
  -- the alternating identity at the even index
  have halt : ((harmonic (2 * c) : ℚ) : ℝ) - ((harmonic c : ℚ) : ℝ) - Real.log 2 =
      -burnolAltTail (2 * c) := by
    have h1 := burnolAlternatingHarmonic_two_mul c
    have h2 := burnolAlternatingHarmonic_eq (2 * c)
    have hpar : (-1 : ℝ) ^ (2 * c) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hpar, one_mul] at h2
    linarith [h1, h2]
  have htail := abs_burnolAltTail_sub_le (2 * c)
  have hcast : ((2 * c : ℕ) : ℝ) = 2 * (c : ℝ) := by push_cast; ring
  rw [hcast] at htail
  have htailB : |burnolAltTail (2 * c) - 1 / (2 * (2 * (c : ℝ) + 1))| ≤
      1 / (2 * (2 * (c : ℝ) + 1) * (2 * (c : ℝ) + 2)) := by
    have h1 : 2 * ((2 * (c : ℝ)) + 1) = 2 * (2 * (c : ℝ) + 1) := by ring
    have h2 : 2 * ((2 * (c : ℝ)) + 1) * ((2 * (c : ℝ)) + 2) =
        2 * (2 * (c : ℝ) + 1) * (2 * (c : ℝ) + 2) := by ring
    rw [h1, h2] at htail
    exact htail
  obtain ⟨hlo, hhi⟩ := abs_le.mp htailB
  have hRbound : R ≤ 2 * (c : ℝ) + 2 := by linarith
  have hkey : |burnolReflectedTruncMass R + 1 / 2| ≤ 1 / (2 * (c : ℝ) + 1) := by
    rcases burnolFloorPair hR0 with hcase | hcase
    · have hbc : (b : ℝ) = 2 * (c : ℝ) := by
        rw [hb, hcase]
        push_cast
        ring
      have hRlt : R < 2 * (c : ℝ) + 1 := by linarith [hbR']
      rw [burnolReflectedTruncMass, ← hb, ← hc, hbc]
      have hharm : ((harmonic b : ℚ) : ℝ) = ((harmonic (2 * c) : ℚ) : ℝ) := by rw [hb, hcase]
      rw [hharm, halt, abs_le]
      constructor <;> nlinarith [hlo, hhi, hden, hRbound, hbR, hRlt, hR1]
    · have hbc : (b : ℝ) = 2 * (c : ℝ) + 1 := by
        rw [hb, hcase]
        push_cast
        ring
      have hRge : 2 * (c : ℝ) + 1 ≤ R := by rw [← hbc]; exact hbR
      have hharm : ((harmonic b : ℚ) : ℝ) =
          ((harmonic (2 * c) : ℚ) : ℝ) + 1 / (2 * (c : ℝ) + 1) := by
        rw [hb, hcase, harmonic_succ]
        push_cast
        ring
      rw [burnolReflectedTruncMass, ← hb, ← hc, hbc, hharm]
      have hexp : ((harmonic (2 * c) : ℚ) : ℝ) + 1 / (2 * (c : ℝ) + 1) -
          ((harmonic c : ℚ) : ℝ) - Real.log 2 =
          -burnolAltTail (2 * c) + 1 / (2 * (c : ℝ) + 1) := by linarith [halt]
      rw [hexp, abs_le]
      constructor <;> nlinarith [hlo, hhi, hden, hRbound, hRge, hbR', hR1]
  refine le_trans hkey ?_
  rw [div_le_div_iff₀ hden hR1]
  linarith

theorem tendsto_burnolReflectedTruncMass :
    Tendsto burnolReflectedTruncMass atTop (𝓝 (-(1 : ℝ) / 2)) := by
  have hdom : Tendsto (fun R : ℝ => 1 / (R - 1)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have hsq : Tendsto (fun R : ℝ => |burnolReflectedTruncMass R - (-(1 : ℝ) / 2)|) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ hdom
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    have h := abs_burnolReflectedTruncMass_add_half_le hR
    rwa [show burnolReflectedTruncMass R - (-(1 : ℝ) / 2) = burnolReflectedTruncMass R + 1 / 2 by
      ring]
  exact tendsto_iff_dist_tendsto_zero.mpr hsq

/-- **The improper mass of the reflected source is `ζ(0) = -1/2`.** -/
theorem tendsto_integral_burnolReflectedRawSource :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, burnolReflectedRawSource t) atTop
      (𝓝 (-(1 : ℂ) / 2)) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp tendsto_burnolReflectedTruncMass
  have hval : ((-(1 : ℝ) / 2 : ℝ) : ℂ) = -(1 : ℂ) / 2 := by norm_num
  rw [Function.comp_def, hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (integral_burnolReflectedRawSource_eq_truncMass hR).symm

end RHTower
