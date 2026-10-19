import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCollarIrrationalityAndSpacing
import GaloisForLFunctions.«arithmetic-positivity-theory».DyadicBernoulliFilterAndBohrCoercivity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Exact affine arithmetic of the factorial cubic clock.

Small shifted-harmonic gaps in the admitted band are classified by the integer
clock `12 N + 1`; exact collisions force identical scale and harmonic labels.
The dyadic stencil excludes mixed integer aliases, with an explicit defect budget.
Prime-thirteen pairs have positive shrinking gaps whose critical inverse-square
correlation tends to one, although each fixed-scale Bohr mean vanishes.
The correlation statement concerns this shifted-frequency channel.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

/-- Distance from the factorial cubic clock to its affine asymptote. -/
def factorialAffineDefect (N : ℕ) : ℝ :=
  (N : ℝ) + 1 / 12 - factorialShiftedFreq N

private theorem affineDefect_eq (N : ℕ) :
    factorialAffineDefect N = 1 / 12 - factorialCollarShift N := by
  rw [factorialAffineDefect, factorialShiftedFreq_eq_add_shift]
  ring

private theorem affineDefect_identity {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * factorialAffineDefect N =
      factorialCollarShift N ^ 2 + factorialCollarShift N ^ 3 / (3 * (N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hc := four_mul_factorialShiftedFreq_cube hN
  rw [factorialShiftedFreq_eq_add_shift] at hc
  rw [affineDefect_eq]
  apply (mul_left_cancel₀ hN0)
  field_simp [hN0]
  nlinarith [hc]

private theorem affineDefect_scaled_bounds {N : ℕ} (hN : 1 ≤ N) :
    (1 / 225 : ℝ) ≤ (N : ℝ) * factorialAffineDefect N ∧
      (N : ℝ) * factorialAffineDefect N ≤ 1 / 140 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hl, hu⟩ := factorialCollarShift_bounds hN
  have hd : 0 ≤ factorialCollarShift N := by linarith
  have hsqL : (1 / 225 : ℝ) ≤ factorialCollarShift N ^ 2 := by nlinarith
  have hsqU : factorialCollarShift N ^ 2 ≤ (1 / 144 : ℝ) := by nlinarith
  have hcube0 : 0 ≤ factorialCollarShift N ^ 3 := pow_nonneg hd _
  have hcubeU : factorialCollarShift N ^ 3 ≤ (1 / 1728 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg (factorialCollarShift N + 1 / 12))]
  have hdiv0 : 0 ≤ factorialCollarShift N ^ 3 / (3 * (N : ℝ)) := by positivity
  have hdivU : factorialCollarShift N ^ 3 / (3 * (N : ℝ)) ≤ (1 / 5184 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * N)).mpr
    nlinarith
  rw [affineDefect_identity hN]
  constructor <;> linarith

/-- The exact factorial collar has a positive inverse-scale affine defect. -/
theorem factorialAffineDefect_bounds (n : ℕ) :
    1 / (225 * (n + 1 : ℝ)) ≤ factorialAffineDefect (n + 1) ∧
      factorialAffineDefect (n + 1) ≤ 1 / (140 * (n + 1 : ℝ)) := by
  have h := affineDefect_scaled_bounds (N := n + 1) (by omega)
  push_cast at h
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 225 * (n + 1))).mpr
    nlinarith [h.1]
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 140 * (n + 1))).mpr
    nlinarith [h.2]

/-- Every dilation gap splits into an integer residue and the exact collar defects. -/
theorem factorialShiftedFreq_affine_gap (r M N : ℕ) :
    factorialShiftedFreq N - (r : ℝ) * factorialShiftedFreq M =
      ((12 * (N : ℝ) + 1) - (r : ℝ) * (12 * (M : ℝ) + 1)) / 12 +
        (r : ℝ) * factorialAffineDefect M - factorialAffineDefect N := by
  unfold factorialAffineDefect
  ring

private theorem affine_resonant_bounds {r M N : ℕ} (hr : 2 ≤ r) (hM : 1 ≤ M)
    (hN : 1 ≤ N) (hres : 12 * N + 1 = r * (12 * M + 1)) :
    (r : ℝ) / (400 * (M : ℝ)) ≤
        factorialShiftedFreq N - (r : ℝ) * factorialShiftedFreq M ∧
      factorialShiftedFreq N - (r : ℝ) * factorialShiftedFreq M ≤
        (r : ℝ) / (140 * (M : ℝ)) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hresR : 12 * (N : ℝ) + 1 = (r : ℝ) * (12 * (M : ℝ) + 1) := by
    exact_mod_cast hres
  have hrM : (r : ℝ) * M ≤ N := by nlinarith
  have h2M : 2 * (M : ℝ) ≤ N := by nlinarith
  obtain ⟨hML, hMU⟩ := affineDefect_scaled_bounds hM
  obtain ⟨hNL, hNU⟩ := affineDefect_scaled_bounds hN
  have heN : 0 ≤ factorialAffineDefect N := by nlinarith
  have hsmall : (M : ℝ) * factorialAffineDefect N ≤ 1 / 280 := by
    nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) - 2 * M by linarith) heN]
  rw [factorialShiftedFreq_affine_gap, hresR, sub_self, zero_div, zero_add]
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 400 * M)).mpr
    nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by linarith)
      (show 0 ≤ (M : ℝ) * factorialAffineDefect M - 1 / 225 by linarith)]
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 140 * M)).mpr
    nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by linarith)
      (show 0 ≤ 1 / 140 - (M : ℝ) * factorialAffineDefect M by linarith),
      mul_nonneg (show 0 ≤ (M : ℝ) by linarith) heN]

/-- Dilations congruent to one modulo twelve have positive, inverse-scale detuning
along their exact affine arithmetic relation. -/
theorem factorial_affine_dilation_detuning (q m : ℕ) :
    ((12 * q + 13 : ℕ) : ℝ) / (400 * (m + 1 : ℝ)) ≤
      factorialShiftedFreq ((12 * q + 13) * (m + 1) + q + 1) -
        (12 * q + 13 : ℝ) * factorialShiftedFreq (m + 1) ∧
    factorialShiftedFreq ((12 * q + 13) * (m + 1) + q + 1) -
        (12 * q + 13 : ℝ) * factorialShiftedFreq (m + 1) ≤
      (12 * q + 13 : ℝ) / (140 * (m + 1 : ℝ)) := by
  have h := affine_resonant_bounds (r := 12 * q + 13) (M := m + 1)
    (N := (12 * q + 13) * (m + 1) + q + 1) (by omega) (by omega)
    (by omega) (by ring)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

/-- The prime-thirteen shifted-frequency gap tends to zero while remaining positive. -/
def factorialThirteenGap (m : ℕ) : ℝ :=
  factorialShiftedFreq (13 * (m + 1) + 1) - 13 * factorialShiftedFreq (m + 1)

theorem factorialThirteenGap_bounds (m : ℕ) :
    13 / (400 * (m + 1 : ℝ)) ≤ factorialThirteenGap m ∧
      factorialThirteenGap m ≤ 13 / (140 * (m + 1 : ℝ)) := by
  simpa [factorialThirteenGap] using factorial_affine_dilation_detuning 0 m

theorem factorialThirteenGap_pos (m : ℕ) : 0 < factorialThirteenGap m :=
  lt_of_lt_of_le (by positivity) (factorialThirteenGap_bounds m).1

private theorem affine_nonresonant_gap {r M N : ℕ} (hr : 2 ≤ r) (hM : r ≤ M)
    (hN : 1 ≤ N) (hne : 12 * N + 1 ≠ r * (12 * M + 1)) :
    (1 / 15 : ℝ) ≤ |factorialShiftedFreq N - (r : ℝ) * factorialShiftedFreq M| := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hMR : (r : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hML, hMU⟩ := affineDefect_scaled_bounds (show 1 ≤ M by omega)
  obtain ⟨hNL, hNU⟩ := affineDefect_scaled_bounds hN
  have heM : 0 ≤ factorialAffineDefect M := by nlinarith
  have heN : 0 ≤ factorialAffineDefect N := by nlinarith
  have hleft : (r : ℝ) * factorialAffineDefect M ≤ 1 / 140 := by
    nlinarith [mul_nonneg (show 0 ≤ (M : ℝ) - r by linarith) heM]
  have hright : factorialAffineDefect N ≤ 1 / 140 := by
    nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) - 1 by linarith) heN]
  rw [factorialShiftedFreq_affine_gap]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hg : 12 * (N : ℝ) + 1 + 1 ≤ (r : ℝ) * (12 * (M : ℝ) + 1) := by
      exact_mod_cast (show 12 * N + 1 + 1 ≤ r * (12 * M + 1) by omega)
    apply le_trans _ (neg_le_abs _)
    linarith
  · have hg : (r : ℝ) * (12 * (M : ℝ) + 1) + 1 ≤ 12 * (N : ℝ) + 1 := by
      exact_mod_cast (show r * (12 * M + 1) + 1 ≤ 12 * N + 1 by omega)
    apply le_trans _ (le_abs_self _)
    have hnn : 0 ≤ (r : ℝ) * factorialAffineDefect M := mul_nonneg (by linarith) heM
    linarith

/-- Above the dilation scale, every small shifted-frequency gap is detected exactly
by the integer relation between the affine clocks `12 N + 1`. -/
theorem factorial_small_dilation_gap_iff_affine (q m n : ℕ) :
    |factorialShiftedFreq (n + 1) - (q + 2 : ℝ) * factorialShiftedFreq (q + 2 + m)| <
        (1 / 15 : ℝ) ↔
      12 * (n + 1) + 1 = (q + 2) * (12 * (q + 2 + m) + 1) := by
  have hr : 2 ≤ q + 2 := by omega
  have hM : q + 2 ≤ q + 2 + m := by omega
  have hN : 1 ≤ n + 1 := by omega
  constructor
  · intro h
    by_contra hne
    have hg := affine_nonresonant_gap hr hM hN hne
    push_cast at hg
    linarith
  · intro hres
    have hb := affine_resonant_bounds hr (show 1 ≤ q + 2 + m by omega) hN hres
    push_cast at hb
    have hg0 : 0 ≤ factorialShiftedFreq (n + 1) -
        (q + 2 : ℝ) * factorialShiftedFreq (q + 2 + m) := by
      exact le_trans (by positivity) hb.1
    rw [abs_of_nonneg hg0]
    have hrat : (q + 2 : ℝ) / (140 * (q + 2 + m : ℝ)) ≤ 1 / 140 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 140 * (q + 2 + m))).mpr
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    linarith [hb.2]

/-- A prime dilation has arbitrarily small positive gaps across source scales. -/
theorem tendsto_factorialThirteenGap_zero :
    Tendsto factorialThirteenGap atTop (𝓝 0) := by
  have hmaj : Tendsto (fun m : ℕ => 13 / (140 * (m + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, div_div] using
      (tendsto_const_div_atTop_nhds_zero_nat (13 / 140 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun m => (factorialThirteenGap_pos m).le)
    (fun m => (factorialThirteenGap_bounds m).2) hmaj

/-- The inverse-square physical measure sees this exact shifted-frequency pair. -/
def factorialThirteenPhysicalCorrelation (m : ℕ) : ℝ :=
  ∫ v in Ioi (1 : ℝ),
    v ^ (-2 : ℝ) * Real.cos (2 * Real.pi * factorialThirteenGap m * v)

/-- Physical correlation approaches its full mass despite exact nonresonance. -/
theorem tendsto_factorialThirteenPhysicalCorrelation_one :
    Tendsto factorialThirteenPhysicalCorrelation atTop (𝓝 1) := by
  change Tendsto (fun m : ℕ => ∫ v in Ioi (1 : ℝ),
    v ^ (-2 : ℝ) * Real.cos (2 * Real.pi * factorialThirteenGap m * v)) atTop (𝓝 1)
  have hi : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun m v => v ^ (-2 : ℝ) *
      Real.cos (2 * Real.pi * factorialThirteenGap m * v))
    (f := fun v => v ^ (-2 : ℝ)) (fun v => v ^ (-2 : ℝ))
    (fun m => hi.aestronglyMeasurable.mul
      (show Continuous (fun v : ℝ =>
        Real.cos (2 * Real.pi * factorialThirteenGap m * v)) by
          fun_prop).aestronglyMeasurable) hi
    (by
      intro m
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 ≤ v := le_trans zero_le_one hv.le
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hv0 _),
        Real.norm_eq_abs]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hv0 _) (Real.abs_cos_le_one _))
    (by
      filter_upwards [] with v
      have harg : Tendsto (fun m => 2 * Real.pi * factorialThirteenGap m * v)
          atTop (𝓝 0) := by
        simpa using (tendsto_factorialThirteenGap_zero.const_mul (2 * Real.pi)).mul_const v
      have hc := Real.continuous_cos.continuousAt.tendsto.comp harg
      simpa using hc.const_mul (v ^ (-2 : ℝ)))
  have hmass : (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ)) = 1 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
    norm_num
  simpa only [hmass] using hlim

/-- At each fixed source scale the Bohr mean is nevertheless zero. -/
theorem tendsto_factorialThirteenGap_bohr_zero (m : ℕ) :
    Tendsto (fun L : ℝ => ((1 / L : ℝ) : ℂ) *
      ∫ v in (0 : ℝ)..L,
        Complex.exp ((Complex.I * ((2 * Real.pi * factorialThirteenGap m : ℝ) : ℂ)) *
          (v : ℂ))) atTop (𝓝 0) := by
  exact tendsto_bohr_mean_cexp_zero_of_ne_zero (by
    have := factorialThirteenGap_pos m
    have := Real.pi_pos
    positivity)

private theorem affineDefect_weighted_bounds {k N : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    0 ≤ (k : ℝ) * factorialAffineDefect N ∧
      (k : ℝ) * factorialAffineDefect N ≤ 1 / 140 := by
  obtain ⟨hl, hu⟩ := affineDefect_scaled_bounds hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
  have he : 0 ≤ factorialAffineDefect N := by nlinarith
  constructor
  · exact mul_nonneg (Nat.cast_nonneg k) he
  · nlinarith [mul_nonneg (sub_nonneg.mpr hkR) he]

private theorem affine_small_harmonic_gap_iff {a b N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (ha : a ≤ N) (hb : b ≤ M) :
    |(a : ℝ) * factorialShiftedFreq N - (b : ℝ) * factorialShiftedFreq M| <
        (1 / 15 : ℝ) ↔ a * (12 * N + 1) = b * (12 * M + 1) := by
  obtain ⟨ha0, ha1⟩ := affineDefect_weighted_bounds hN ha
  obtain ⟨hb0, hb1⟩ := affineDefect_weighted_bounds hM hb
  have hgap : (a : ℝ) * factorialShiftedFreq N - (b : ℝ) * factorialShiftedFreq M =
      ((a : ℝ) * (12 * (N : ℝ) + 1) - (b : ℝ) * (12 * (M : ℝ) + 1)) / 12 +
        (b : ℝ) * factorialAffineDefect M - (a : ℝ) * factorialAffineDefect N := by
    unfold factorialAffineDefect
    ring
  rw [hgap]
  constructor
  · intro h
    obtain ⟨hl, hu⟩ := abs_lt.mp h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hh : (a : ℝ) * (12 * (N : ℝ) + 1) + 1 ≤
          (b : ℝ) * (12 * (M : ℝ) + 1) := by
        exact_mod_cast (show a * (12 * N + 1) + 1 ≤ b * (12 * M + 1) by omega)
      linarith
    · have hh : (b : ℝ) * (12 * (M : ℝ) + 1) + 1 ≤
          (a : ℝ) * (12 * (N : ℝ) + 1) := by
        exact_mod_cast (show b * (12 * M + 1) + 1 ≤ a * (12 * N + 1) by omega)
      linarith
  · intro h
    have heq : (a : ℝ) * (12 * (N : ℝ) + 1) =
        (b : ℝ) * (12 * (M : ℝ) + 1) := by exact_mod_cast h
    rw [heq, sub_self, zero_div, zero_add, abs_lt]
    constructor <;> linarith

/-- Every admitted pair of harmonic layers has small gap exactly on an affine-clock relation. -/
theorem factorial_small_harmonic_gap_iff_affine (a b n m : ℕ) :
    |(a + 1 : ℝ) * factorialShiftedFreq (a + 1 + n) -
        (b + 1 : ℝ) * factorialShiftedFreq (b + 1 + m)| < (1 / 15 : ℝ) ↔
      (a + 1) * (12 * (a + 1 + n) + 1) =
        (b + 1) * (12 * (b + 1 + m) + 1) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    affine_small_harmonic_gap_iff (a := a + 1) (b := b + 1)
      (N := a + 1 + n) (M := b + 1 + m) (by omega) (by omega) (by omega) (by omega)

private theorem mixed_residue_ne_zero {k N : ℕ} (J : ℤ)
    (hk : dyadicHarmonicChi k ≠ 0) :
    (k : ℤ) * (12 * (N : ℤ) + 1) - 12 * J ≠ 0 := by
  intro heq
  have heq' : (k : ℤ) = 12 * (J - (k : ℤ) * N) := by nlinarith [heq]
  have hk4Z : (k : ℤ) % 4 = 0 := by omega
  have hk4 : k % 4 = 0 := by exact_mod_cast hk4Z
  have hk2 : k % 2 ≠ 1 := by omega
  apply hk
  simp [dyadicHarmonicChi, hk2, hk4]

/-- The dyadic stencil excludes affine aliases to the integer lattice, with the exact
inverse-scale defect retained when the harmonic exceeds the source scale. -/
theorem factorial_dyadic_mixed_gap_with_defect (k n : ℕ) (J : ℤ) :
    |dyadicHarmonicChi k| / 12 ≤
      |(k : ℝ) * factorialShiftedFreq (n + 1) - (J : ℝ)| +
        (k : ℝ) / (140 * (n + 1 : ℝ)) := by
  by_cases hk : dyadicHarmonicChi k = 0
  · simp only [hk, abs_zero, zero_div]
    positivity
  let B : ℤ := (k : ℤ) * (12 * ((n + 1 : ℕ) : ℤ) + 1) - 12 * J
  have hB : B ≠ 0 := mixed_residue_ne_zero J hk
  have hB1 : (1 : ℤ) ≤ |B| := by
    have := abs_pos.mpr hB
    omega
  have hB1R : (1 : ℝ) ≤ |(B : ℝ)| := by exact_mod_cast hB1
  have hchi : |dyadicHarmonicChi k| ≤ |(B : ℝ)| :=
    le_trans (abs_dyadicHarmonicChi_le_one k) hB1R
  have he := factorialAffineDefect_bounds n
  have he0 : 0 ≤ factorialAffineDefect (n + 1) := le_trans (by positivity) he.1
  have hke0 : 0 ≤ (k : ℝ) * factorialAffineDefect (n + 1) :=
    mul_nonneg (Nat.cast_nonneg k) he0
  have hke : (k : ℝ) * factorialAffineDefect (n + 1) ≤
      (k : ℝ) / (140 * (n + 1 : ℝ)) := by
    calc
      _ ≤ (k : ℝ) * (1 / (140 * (n + 1 : ℝ))) :=
        mul_le_mul_of_nonneg_left he.2 (Nat.cast_nonneg k)
      _ = _ := by ring
  have hBR : (B : ℝ) = 12 *
      ((k : ℝ) * factorialShiftedFreq (n + 1) - (J : ℝ) +
        (k : ℝ) * factorialAffineDefect (n + 1)) := by
    dsimp [B, factorialAffineDefect]
    push_cast
    ring
  rw [hBR, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)] at hchi
  have habs := abs_add_le ((k : ℝ) * factorialShiftedFreq (n + 1) - (J : ℝ))
    ((k : ℝ) * factorialAffineDefect (n + 1))
  rw [abs_of_nonneg hke0] at habs
  linarith

/-- Every surviving dyadic harmonic below the source scale stays uniformly away
from every integer frequency. -/
theorem factorial_dyadic_mixed_gap (k n : ℕ) (J : ℤ) :
    dyadicHarmonicChi (k + 1) = 0 ∨
      (1 / 15 : ℝ) ≤
        |(k + 1 : ℝ) * factorialShiftedFreq (k + 1 + n) - (J : ℝ)| := by
  by_cases hk : dyadicHarmonicChi (k + 1) = 0
  · exact Or.inl hk
  right
  have hchi : |dyadicHarmonicChi (k + 1)| = 1 := by
    unfold dyadicHarmonicChi at hk ⊢
    split_ifs at hk ⊢ <;> norm_num at *
  have h := factorial_dyadic_mixed_gap_with_defect (k + 1) (k + n) J
  rw [hchi] at h
  have horder : k + n + 1 = k + 1 + n := by omega
  rw [horder] at h
  push_cast at h
  have hfrac : (k + 1 : ℝ) / (140 * (k + n + 1 : ℝ)) ≤ 1 / 140 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 140 * (k + n + 1))).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  linarith

private theorem affine_resonance_rigid {a b N M : ℕ}
    (ha : 1 ≤ a) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hfreq : (a : ℝ) * factorialShiftedFreq N = (b : ℝ) * factorialShiftedFreq M)
    (haff : a * (12 * N + 1) = b * (12 * M + 1)) : N = M ∧ a = b := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have haffR : (a : ℝ) * (12 * (N : ℝ) + 1) =
      (b : ℝ) * (12 * (M : ℝ) + 1) := by exact_mod_cast haff
  have hclock : factorialShiftedFreq N * (12 * (M : ℝ) + 1) =
      factorialShiftedFreq M * (12 * (N : ℝ) + 1) := by
    apply mul_left_cancel₀ ha0
    calc
      _ = ((a : ℝ) * factorialShiftedFreq N) * (12 * (M : ℝ) + 1) := by ring
      _ = ((b : ℝ) * factorialShiftedFreq M) * (12 * (M : ℝ) + 1) := by rw [hfreq]
      _ = factorialShiftedFreq M * ((b : ℝ) * (12 * (M : ℝ) + 1)) := by ring
      _ = factorialShiftedFreq M * ((a : ℝ) * (12 * (N : ℝ) + 1)) := by rw [haffR]
      _ = _ := by ring
  have hc := congrArg (fun x : ℝ => 4 * x ^ 3) hclock
  have hNc := four_mul_factorialShiftedFreq_cube hN
  have hMc := four_mul_factorialShiftedFreq_cube hM
  have hpoly : (N : ℝ) ^ 2 * (4 * (N : ℝ) + 1) * (12 * (M : ℝ) + 1) ^ 3 -
      (M : ℝ) ^ 2 * (4 * (M : ℝ) + 1) * (12 * (N : ℝ) + 1) ^ 3 = 0 := by
    calc
      _ = (4 * factorialShiftedFreq N ^ 3) * (12 * (M : ℝ) + 1) ^ 3 -
          (4 * factorialShiftedFreq M ^ 3) * (12 * (N : ℝ) + 1) ^ 3 := by rw [hNc, hMc]
      _ = 0 := by nlinarith only [hc]
  have hfactor : ((N : ℝ) - M) *
      (144 * (N : ℝ) * M * ((N : ℝ) + M) + 4 * (N : ℝ) ^ 2 +
        40 * (N : ℝ) * M + 4 * (M : ℝ) ^ 2 + (N : ℝ) + M) = 0 := by
    calc
      _ = (N : ℝ) ^ 2 * (4 * (N : ℝ) + 1) * (12 * (M : ℝ) + 1) ^ 3 -
          (M : ℝ) ^ 2 * (4 * (M : ℝ) + 1) * (12 * (N : ℝ) + 1) ^ 3 := by ring
      _ = 0 := hpoly
  have hpos : 0 < 144 * (N : ℝ) * M * ((N : ℝ) + M) + 4 * (N : ℝ) ^ 2 +
      40 * (N : ℝ) * M + 4 * (M : ℝ) ^ 2 + (N : ℝ) + M := by positivity
  have hNM : N = M := by
    have heq := sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hpos))
    exact_mod_cast heq
  refine ⟨hNM, ?_⟩
  rw [hNM] at hfreq
  have hlam : factorialShiftedFreq M ≠ 0 := ne_of_gt (factorialShiftedFreq_pos hM)
  exact_mod_cast (mul_right_cancel₀ hlam hfreq)

/-- Below their source scales, distinct shifted harmonic labels never coincide,
even when the harmonic orders differ. -/
theorem factorial_admitted_harmonic_resonance_iff (a b n m : ℕ) :
    (a + 1 : ℝ) * factorialShiftedFreq (a + 1 + n) =
        (b + 1 : ℝ) * factorialShiftedFreq (b + 1 + m) ↔ a = b ∧ n = m := by
  constructor
  · intro hfreq
    have hsmall : |(a + 1 : ℝ) * factorialShiftedFreq (a + 1 + n) -
        (b + 1 : ℝ) * factorialShiftedFreq (b + 1 + m)| < (1 / 15 : ℝ) := by
      rw [hfreq, sub_self, abs_zero]
      norm_num
    have haff := (factorial_small_harmonic_gap_iff_affine a b n m).mp hsmall
    have hfreq' : ((a + 1 : ℕ) : ℝ) * factorialShiftedFreq (a + 1 + n) =
        ((b + 1 : ℕ) : ℝ) * factorialShiftedFreq (b + 1 + m) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hfreq
    obtain ⟨hNM, hab⟩ := affine_resonance_rigid (by omega) (by omega) (by omega) hfreq' haff
    constructor <;> omega
  · rintro ⟨rfl, rfl⟩
    rfl

end
end GaloisForLFunctions.ArithmeticPositivityTheory
