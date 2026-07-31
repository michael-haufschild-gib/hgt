import GaloisForLFunctions.RHTower.CCMRectangularAutocorrelation
import GaloisForLFunctions.RHTower.CCMSharpRectangularSewing

/-!
# Rectangular Stieltjes autocorrelation law

The moving triangular von-Mangoldt value in the rectangular autocorrelation is exactly the
adjacent logarithmic Stieltjes block of the cumulative critical Mellin prime mass.  The polar
second difference has a matching exact two-edge expansion.  Combining both identities shows that
the complete rectangular prime--polar source coefficient is one fixed width-dependent constant
plus twice the completed critical-Mellin adjacent block.

This is the exact source-side value identification at the piecewise-linear rectangular
autocorrelation regularity.  It does not identify this source value with the Xi spectral Weil
polarization; that separate Guinand--Weil extension remains a distinct theorem obligation.
-/

open MeasureTheory Set
open ArithmeticFunction

noncomputable section

namespace RHTower

private def criticalMellinStieltjesWeight (k : ℕ) : ℝ :=
  ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k

/-- The cumulative critical Mellin prime mass has no contributions at zero or one. -/
theorem criticalMellinPrimeMass_eq_sum_Icc_two (h : ℝ) :
    criticalMellinPrimeMass h =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp h⌋₊, criticalMellinStieltjesWeight k := by
  rw [criticalMellinPrimeMass]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    exact ⟨by omega, hk.2⟩
  · intro k hk hnot
    simp only [Finset.mem_Icc] at hk
    have hklt : k < 2 := Nat.lt_of_not_ge fun hk2 =>
      hnot (Finset.mem_Icc.mpr ⟨hk2, hk.2⟩)
    interval_cases k <;> norm_num [criticalMellinStieltjesWeight]

private theorem criticalMellinPrimeMass_eq_common_step
    {h x : ℝ} (hhx : h ≤ x) :
    criticalMellinPrimeMass h =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp x⌋₊,
        if Real.log k ≤ h then criticalMellinStieltjesWeight k else 0 := by
  rw [criticalMellinPrimeMass_eq_sum_Icc_two]
  let s : Finset ℕ := Finset.Icc 2 ⌊Real.exp x⌋₊
  let p : ℕ → Prop := fun k => Real.log k ≤ h
  have hfin : (Finset.Icc 2 ⌊Real.exp h⌋₊ : Finset ℕ) = s.filter p := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_filter, s, p]
    constructor
    · intro hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkexp : (k : ℝ) ≤ Real.exp h :=
        (Nat.le_floor_iff (Real.exp_pos h).le).mp hk.2
      have hlog : Real.log k ≤ h :=
        (Real.log_le_iff_le_exp hkpos).mpr hkexp
      have hfloor : ⌊Real.exp h⌋₊ ≤ ⌊Real.exp x⌋₊ :=
        Nat.floor_mono (Real.exp_le_exp.mpr hhx)
      exact ⟨⟨hk.1, hk.2.trans hfloor⟩, hlog⟩
    · intro hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkexp : (k : ℝ) ≤ Real.exp h :=
        (Real.log_le_iff_le_exp hkpos).mp hk.2
      exact ⟨hk.1.1, (Nat.le_floor_iff (Real.exp_pos h).le).mpr hkexp⟩
  rw [hfin]
  exact Finset.sum_filter p criticalMellinStieltjesWeight

/-- Integral of a cumulative step over one half-open interval. -/
private theorem setIntegral_step_Ioc (a b y c : ℝ) (hab : a ≤ b) :
    (∫ h in Ioc a b, if y ≤ h then c else 0) =
      max 0 (b - max a y) * c := by
  have hfun : (fun h : ℝ => if y ≤ h then c else 0) =
      (Ici y).indicator (fun _ => c) := by
    funext h
    by_cases hyh : y ≤ h <;> simp [Set.indicator, hyh]
  rw [hfun, ← MeasureTheory.integral_indicator measurableSet_Ioc,
    Set.indicator_indicator,
    MeasureTheory.integral_indicator_const c
      (measurableSet_Ioc.inter measurableSet_Ici)]
  by_cases hya : y ≤ a
  · have hset : Ioc a b ∩ Ici y = Ioc a b := by
      ext h
      simp only [mem_inter_iff, mem_Ioc, mem_Ici]
      constructor
      · exact fun hh => hh.1
      · intro hh
        exact ⟨hh, hya.trans hh.1.le⟩
    rw [hset, Measure.real, Real.volume_Ioc]
    simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]
    rw [max_eq_left hya, max_eq_right (sub_nonneg.mpr hab)]
  · have hay : a < y := lt_of_not_ge hya
    by_cases hyb : y ≤ b
    · have hset : Ioc a b ∩ Ici y = Icc y b := by
        ext h
        simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
        constructor
        · intro hh
          exact ⟨hh.2, hh.1.2⟩
        · intro hh
          exact ⟨⟨hay.trans_le hh.1, hh.2⟩, hh.1⟩
      rw [hset, Measure.real, Real.volume_Icc]
      simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr hyb), smul_eq_mul]
      rw [max_eq_right hay.le, max_eq_right (sub_nonneg.mpr hyb)]
    · have hby : b < y := lt_of_not_ge hyb
      have hset : Ioc a b ∩ Ici y = ∅ := by
        ext h
        simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_empty_iff_false, iff_false]
        intro hh
        linarith [hh.1.2, hh.2]
      rw [hset]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero, zero_smul,
        max_eq_right hay.le]
      rw [max_eq_left (by linarith : b - y ≤ 0), zero_mul]

private theorem integrable_step_Ioc (a b y c : ℝ) :
    Integrable (fun h : ℝ => if y ≤ h then c else 0)
      (volume.restrict (Ioc a b)) := by
  have hg : Integrable (fun _ : ℝ => ‖c‖)
      (volume.restrict (Ioc a b)) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  apply hg.mono'
  · have hfun : (fun h : ℝ => if y ≤ h then c else 0) =
        (Ici y).indicator (fun _ => c) := by
        funext h
        by_cases hyh : y ≤ h <;> simp [Set.indicator, hyh]
    rw [hfun]
    exact (measurable_const.indicator measurableSet_Ici).aestronglyMeasurable
  · filter_upwards with h
    by_cases hyh : y ≤ h
    · rw [if_pos hyh]
    · rw [if_neg hyh, norm_zero]
      exact norm_nonneg c

private theorem integrableOn_polarSinh_Ioc (a b : ℝ) :
    IntegrableOn (fun h : ℝ => 4 * Real.sinh (h / 2)) (Ioc a b) := by
  exact (continuous_const.mul
    (Real.continuous_sinh.comp
      (continuous_id.div_const 2))).continuousOn.integrableOn_Icc.mono_set
        (fun h hh => ⟨hh.1.le, hh.2⟩)

/-- Adjacent difference of two equal-width cumulative steps is the triangular tent centered at
their common boundary. -/
private theorem setIntegral_step_adjacent_eq_tent
    (x L y c : ℝ) (hL : 0 ≤ L) (hy : y ≤ x) :
    (∫ h in Ioc (x - L) x, if y ≤ h then c else 0) -
      (∫ h in Ioc (x - 2 * L) (x - L), if y ≤ h then c else 0) =
        max 0 (L - |y - (x - L)|) * c := by
  rw [setIntegral_step_Ioc _ _ _ _ (by linarith),
    setIntegral_step_Ioc _ _ _ _ (by linarith)]
  by_cases hy0 : y ≤ x - 2 * L
  · have h1 : max (x - L) y = x - L := max_eq_left (by linarith)
    have h2 : max (x - 2 * L) y = x - 2 * L := max_eq_left hy0
    have habs : y - (x - L) ≤ 0 := by linarith
    rw [h1, h2, abs_of_nonpos habs]
    ring_nf
    rw [max_eq_left (by linarith : -x + L * 2 + y ≤ 0)]
    ring
  · have hy0' : x - 2 * L < y := lt_of_not_ge hy0
    by_cases hy1 : y ≤ x - L
    · have h1 : max (x - L) y = x - L := max_eq_left hy1
      have h2 : max (x - 2 * L) y = y := max_eq_right hy0'.le
      have habs : y - (x - L) ≤ 0 := by linarith
      rw [h1, h2, abs_of_nonpos habs]
      ring_nf
      rw [max_eq_right hL,
        max_eq_right (by linarith : 0 ≤ x - L - y),
        max_eq_right (by linarith : 0 ≤ -x + L * 2 + y)]
      ring
    · have hy1' : x - L < y := lt_of_not_ge hy1
      have h1 : max (x - L) y = y := max_eq_right hy1'.le
      have h2 : max (x - 2 * L) y = y := max_eq_right (by linarith)
      have habs : 0 ≤ y - (x - L) := by linarith
      rw [h1, h2, abs_of_nonneg habs]
      ring_nf
      rw [max_eq_right (by linarith : 0 ≤ x - y),
        max_eq_left (by linarith : x - y - L ≤ 0)]
      ring

/-- **Stieltjes tent law.**  The adjacent logarithmic block of the cumulative critical Mellin
prime mass is exactly the moving triangular von-Mangoldt value. -/
theorem criticalMellinPrimeMass_adjacent_eq_movingTentSum
    (x L : ℝ) (hL : 0 ≤ L) :
    (∫ h in Ioc (x - L) x, criticalMellinPrimeMass h) -
      (∫ h in Ioc (x - 2 * L) (x - L), criticalMellinPrimeMass h) =
        rectangularMovingPrimeTentSum L (Real.exp x) ⌊Real.exp x⌋₊ := by
  let K : Finset ℕ := Finset.Icc 2 ⌊Real.exp x⌋₊
  have hright :
      (∫ h in Ioc (x - L) x, criticalMellinPrimeMass h) =
        ∫ h in Ioc (x - L) x,
          ∑ k ∈ K, if Real.log k ≤ h then criticalMellinStieltjesWeight k else 0 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    rw [criticalMellinPrimeMass_eq_common_step hh.2]
  have hleft :
      (∫ h in Ioc (x - 2 * L) (x - L), criticalMellinPrimeMass h) =
        ∫ h in Ioc (x - 2 * L) (x - L),
          ∑ k ∈ K, if Real.log k ≤ h then criticalMellinStieltjesWeight k else 0 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    rw [criticalMellinPrimeMass_eq_common_step
      (hh.2.trans (sub_le_self x hL))]
  rw [hright, hleft]
  rw [MeasureTheory.integral_finsetSum K (fun k _ =>
      integrable_step_Ioc (x - L) x (Real.log k) (criticalMellinStieltjesWeight k)),
    MeasureTheory.integral_finsetSum K (fun k _ =>
      integrable_step_Ioc (x - 2 * L) (x - L) (Real.log k)
        (criticalMellinStieltjesWeight k)),
    ← Finset.sum_sub_distrib]
  rw [rectangularMovingPrimeTentSum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkmem : k ∈ Finset.Icc 2 ⌊Real.exp x⌋₊ := by simpa only [K] using hk
  have hkposNat : 0 < k := by
    exact (Finset.mem_Icc.mp hkmem).1.trans' (by norm_num)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hkexp : (k : ℝ) ≤ Real.exp x :=
    (Nat.le_floor_iff (Real.exp_pos x).le).mp (Finset.mem_Icc.mp hkmem).2
  have hlog : Real.log k ≤ x :=
    (Real.log_le_iff_le_exp hkpos).mpr hkexp
  rw [setIntegral_step_adjacent_eq_tent x L (Real.log k)
    (criticalMellinStieltjesWeight k) hL hlog]
  have hmoving :
      rectangularMovingPrimeTent L (Real.exp x) k =
        max 0 (L - |Real.log k - (x - L)|) := by
    rw [rectangularMovingPrimeTent, Real.log_div hkpos.ne' (Real.exp_pos x).ne',
      Real.log_exp]
    congr 3
    ring
  rw [hmoving, criticalMellinStieltjesWeight]
  rw [Real.sqrt_eq_rpow]
  have hpow : (k : ℝ) ^ (-1 / 2 : ℝ) =
      ((k : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
    convert Real.rpow_neg hkpos.le (1 / 2 : ℝ) using 1 ; ring
  rw [hpow]
  change max 0 (L - |Real.log k - (x - L)|) *
      (((k : ℝ) ^ (1 / 2 : ℝ))⁻¹ * ArithmeticFunction.vonMangoldt k) =
    (ArithmeticFunction.vonMangoldt k * ((k : ℝ) ^ (1 / 2 : ℝ))⁻¹) *
      max 0 (L - |Real.log k - (x - L)|)
  ring

/-- Adjacent difference of the polar profile in the same two-edge coordinates. -/
theorem polarSinh_adjacent_eq_alpha_beta
    (x L : ℝ) (hL : 0 ≤ L) :
    (∫ h in Ioc (x - L) x, 4 * Real.sinh (h / 2)) -
      (∫ h in Ioc (x - 2 * L) (x - L), 4 * Real.sinh (h / 2)) =
        4 * rectangularPolarAlpha L ^ 2 * Real.exp (x / 2) +
          4 * rectangularPolarBeta L ^ 2 * Real.exp (-x / 2) := by
  rw [← intervalIntegral.integral_of_le (by linarith : x - L ≤ x),
    ← intervalIntegral.integral_of_le (by linarith : x - 2 * L ≤ x - L)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral_sinh_half,
    intervalIntegral_sinh_half]
  rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq,
    rectangularPolarAlpha, rectangularPolarBeta]
  have h1 : Real.exp ((x - L) / 2) =
      Real.exp (x / 2) * Real.exp (-L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-((x - L) / 2)) =
      Real.exp (-x / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp ((x - 2 * L) / 2) =
      Real.exp (x / 2) * Real.exp (-L / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h4 : Real.exp (-((x - 2 * L) / 2)) =
      Real.exp (-x / 2) * Real.exp (L / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h1, h2, h3, h4]
  ring

/-- The completed adjacent block is the moving prime tent subtracted from the exact two-edge
polar values. -/
theorem criticalMellinAdjacentBlock_eq_movingTent_polar
    (x L : ℝ) (hL : 0 ≤ L) :
    criticalMellinAdjacentBlock L x =
      -rectangularMovingPrimeTentSum L (Real.exp x) ⌊Real.exp x⌋₊ +
        4 * rectangularPolarAlpha L ^ 2 * Real.exp (x / 2) +
        4 * rectangularPolarBeta L ^ 2 * Real.exp (-x / 2) := by
  rw [criticalMellinAdjacentBlock]
  change
    (∫ h in Ioc (x - L) x,
      (fun u => 4 * Real.sinh (u / 2) - criticalMellinPrimeMass u) h) -
    (∫ h in Ioc (x - 2 * L) (x - L),
      (fun u => 4 * Real.sinh (u / 2) - criticalMellinPrimeMass u) h) = _
  rw [MeasureTheory.integral_sub
      (integrableOn_polarSinh_Ioc (x - L) x)
      (integrableOn_criticalMellinPrimeMass_Ioc (a := x - L) (b := x)),
    MeasureTheory.integral_sub
      (integrableOn_polarSinh_Ioc (x - 2 * L) (x - L))
      (integrableOn_criticalMellinPrimeMass_Ioc (a := x - 2 * L) (b := x - L))]
  have hp := polarSinh_adjacent_eq_alpha_beta x L hL
  have hm := criticalMellinPrimeMass_adjacent_eq_movingTentSum x L hL
  linear_combination hp - hm

/-- The rectangular prime--polar source differs from twice the completed adjacent block only by
the fixed small-prime and polar-cross values. -/
theorem rectangularPrimePolarSourceCoefficient_eq_fixed_add_adjacentBlock
    {x L : ℝ} (hL : 0 ≤ L) (hx : 2 * L ≤ x) :
    rectangularPrimePolarSourceCoefficient L (x / 2) =
      -4 * rectangularFixedPrimeTentSum L ⌊Real.exp x⌋₊ +
        16 * rectangularPolarAlpha L * rectangularPolarBeta L +
        2 * criticalMellinAdjacentBlock L x := by
  have hcoeff := rectangularPrimePolarSourceCoefficient_logAperture_expanded
    hL (Real.exp_pos x) (by simpa only [Real.log_exp] using hx)
  rw [Real.log_exp] at hcoeff
  have hsqrt : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    rw [← Real.exp_half]
  have hinv : (Real.exp (x / 2))⁻¹ = Real.exp (-x / 2) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hterm :
      8 * rectangularPolarBeta L ^ 2 / Real.sqrt (Real.exp x) =
        8 * rectangularPolarBeta L ^ 2 * Real.exp (-x / 2) := by
    rw [hsqrt, div_eq_mul_inv, hinv]
  rw [hterm, hsqrt] at hcoeff
  have hadj := criticalMellinAdjacentBlock_eq_movingTent_polar x L hL
  linear_combination hcoeff - 2 * hadj

/-- Once the aperture passes the fixed tent support, its small-prime contribution stabilizes. -/
theorem rectangularFixedPrimeTentSum_floorExp_stable
    {x L : ℝ} (hLx : L ≤ x) :
    rectangularFixedPrimeTentSum L ⌊Real.exp x⌋₊ =
      rectangularFixedPrimeTentSum L ⌊Real.exp L⌋₊ := by
  rw [rectangularFixedPrimeTentSum, rectangularFixedPrimeTentSum]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans (Nat.floor_mono (Real.exp_le_exp.mpr hLx))⟩
  · intro k hk hnot
    simp only [Finset.mem_Icc] at hk
    have hkfloor : ⌊Real.exp L⌋₊ < k := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨hk.1, by omega⟩)
    have hkexp : Real.exp L < (k : ℝ) :=
      (Nat.floor_lt (Real.exp_pos L).le).mp hkfloor
    have hkpos : (0 : ℝ) < k := (Real.exp_pos L).trans hkexp
    have hlog : L < Real.log k :=
      (Real.lt_log_iff_exp_lt hkpos).mpr hkexp
    rw [max_eq_left (by linarith : L - Real.log k ≤ 0), mul_zero]

/-- The fixed source value left after the moving rectangular aperture is sewn into the completed
adjacent block. -/
def rectangularFixedPrimePolarConstant (L : ℝ) : ℝ :=
  -4 * rectangularFixedPrimeTentSum L ⌊Real.exp L⌋₊ +
    16 * rectangularPolarAlpha L * rectangularPolarBeta L

/-- **Rectangular source sewing law.**  At every sufficiently separated aperture, the complete
piecewise-linear rectangular prime--Gamma-polar source is a fixed width-dependent value plus twice
the completed critical-Mellin adjacent block. -/
theorem rectangularPrimePolarSourceCoefficient_eq_fixedConstant_add_adjacentBlock
    {x L : ℝ} (hL : 0 ≤ L) (hx : 2 * L ≤ x) :
    rectangularPrimePolarSourceCoefficient L (x / 2) =
      rectangularFixedPrimePolarConstant L +
        2 * criticalMellinAdjacentBlock L x := by
  rw [rectangularPrimePolarSourceCoefficient_eq_fixed_add_adjacentBlock hL hx,
    rectangularFixedPrimeTentSum_floorExp_stable (by linarith),
    rectangularFixedPrimePolarConstant]

/-- The one-sided all-epsilon subpower problem for the complete rectangular prime--polar source
is exactly the same problem for the completed adjacent block.  The fixed width-dependent source
value is absorbed without changing the exponent or the eventual quantifiers. -/
theorem rectangularPrimePolarSource_subpowerLower_iff_adjacentBlock
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ 2 * L ≤ Real.log n) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ rectangularPrimePolarSourceCoefficient L (Real.log n / 2) +
          C * (n : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ criticalMellinAdjacentBlock L (Real.log n) +
          D * (n : ℝ) ^ epsilon) := by
  let B : ℝ := rectangularFixedPrimePolarConstant L
  constructor
  · intro hsource epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hsource epsilon hepsilon
    let D : ℝ := (C + |B|) / 2
    have hD : 0 ≤ D := by
      dsimp only [D]
      positivity
    refine ⟨D, hD, fun n hn => ?_⟩
    obtain ⟨hn1, hnL⟩ := hN n hn
    have hp : 1 ≤ (n : ℝ) ^ epsilon :=
      Real.one_le_rpow (by exact_mod_cast hn1) hepsilon.le
    have hB : B ≤ |B| := le_abs_self B
    have hs := htail n hn
    rw [rectangularPrimePolarSourceCoefficient_eq_fixedConstant_add_adjacentBlock
      hL hnL] at hs
    dsimp only [B, D] at hB hs ⊢
    nlinarith [mul_le_mul_of_nonneg_left hp (abs_nonneg B)]
  · intro hadj epsilon hepsilon
    obtain ⟨D, hD, htail⟩ := hadj epsilon hepsilon
    let C : ℝ := 2 * D + |B|
    have hC : 0 ≤ C := by
      dsimp only [C]
      positivity
    refine ⟨C, hC, fun n hn => ?_⟩
    obtain ⟨hn1, hnL⟩ := hN n hn
    have hp : 1 ≤ (n : ℝ) ^ epsilon :=
      Real.one_le_rpow (by exact_mod_cast hn1) hepsilon.le
    have hB : -|B| ≤ B := neg_abs_le B
    have ha := htail n hn
    rw [rectangularPrimePolarSourceCoefficient_eq_fixedConstant_add_adjacentBlock
      hL hnL]
    dsimp only [B, C] at hB ha ⊢
    nlinarith [mul_le_mul_of_nonneg_left hp (abs_nonneg B)]

end RHTower
