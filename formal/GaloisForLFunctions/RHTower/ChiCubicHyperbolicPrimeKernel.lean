import GaloisForLFunctions.RHTower.Sieve.RamareCofactorBlock
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicMain
import GaloisForLFunctions.RHTower.ChiCubicPrimeWindowLogRate

/-!
# The prime kernel on a hyperbolic phase cell

Grouping by the nonzero integer gap bounds the complete kernel uniformly in
its real interpolation variable. This controls the exceptional intervals in
the replacement of one prime variable by its continuous density.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.RHTower

private def hyperbolicGapWindow (d : ℕ) (Y x : ℝ) : Finset ℕ :=
  Finset.Icc ⌈x - Y / d⌉₊ ⌊x + Y / d⌋₊

private theorem card_hyperbolicGapWindow (d : ℕ) {Y x : ℝ} (hY : 0 ≤ Y) (hx : 0 ≤ x) :
    ((hyperbolicGapWindow d Y x).card : ℝ) ≤ 2 * Y / d + 1 := by
  have hrad : 0 ≤ Y / (d : ℝ) := div_nonneg hY (Nat.cast_nonneg d)
  have h := Sieve.card_Icc_cast_le (Nat.le_ceil (x - Y / d))
    (Nat.floor_le (show 0 ≤ x + Y / d by positivity))
    (show 0 ≤ (x + Y / d) - (x - Y / d) + 1 by linarith)
  change ((Finset.Icc ⌈x - Y / d⌉₊ ⌊x + Y / d⌋₊).card : ℝ) ≤ _
  convert h using 1
  ring

private def hyperbolicGapCover (B : ℕ) (Y x : ℝ) (f : ℕ → ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 B).biUnion fun d =>
    (hyperbolicGapWindow d Y x).image fun r => (f d r, r)

private theorem card_hyperbolicGapCover (B : ℕ) {Y x : ℝ} (hY : 0 ≤ Y) (hx : 0 ≤ x)
    (f : ℕ → ℕ → ℕ) :
    ((hyperbolicGapCover B Y x f).card : ℝ) ≤ 2 * Y * (1 + Real.log B) + B := by
  classical
  have hcard : (hyperbolicGapCover B Y x f).card ≤
      ∑ d ∈ Finset.Icc 1 B, (hyperbolicGapWindow d Y x).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
  have hcardR : ((hyperbolicGapCover B Y x f).card : ℝ) ≤
      ∑ d ∈ Finset.Icc 1 B, ((hyperbolicGapWindow d Y x).card : ℝ) := by exact_mod_cast hcard
  refine hcardR.trans ((Finset.sum_le_sum fun d _ => card_hyperbolicGapWindow d hY hx).trans ?_)
  calc ∑ d ∈ Finset.Icc 1 B, (2 * Y / (d : ℝ) + 1)
      = 2 * Y * (∑ d ∈ Finset.Icc 1 B, 1 / (d : ℝ)) + B := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
          Nat.card_Icc, Nat.add_sub_cancel]
        rw [Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun d _ => by ring
    _ ≤ 2 * Y * (1 + Real.log B) + B := by
      gcongr
      exact Sieve.sum_Icc_one_div_le_one_add_log B

/-- Integer pairs in a full hyperbolic strip, with the zero gap removed. -/
def chiCubicHyperbolicIntegerPairs (B : ℕ) (Y x : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (B + 1)).product (Finset.range (B + 1))).filter fun pr =>
    pr.1 ≠ pr.2 ∧ |(pr.1 : ℝ) - pr.2| * |x - pr.2| ≤ Y

private theorem mem_hyperbolicGapWindow {d r : ℕ} {Y x : ℝ} (hd : 0 < d)
    (h : (d : ℝ) * |x - r| ≤ Y) : r ∈ hyperbolicGapWindow d Y x := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hb : |x - r| ≤ Y / d := (le_div_iff₀ hdR).2 (by nlinarith)
  rw [abs_le] at hb
  exact Finset.mem_Icc.2 ⟨Nat.ceil_le.2 (by linarith), Nat.le_floor (by linarith)⟩

/-- Uniform counting in the real anchor, by the two signs of the integer gap. -/
theorem card_chiCubicHyperbolicIntegerPairs (B : ℕ) {Y x : ℝ} (hY : 0 ≤ Y) (hx : 0 ≤ x) :
    ((chiCubicHyperbolicIntegerPairs B Y x).card : ℝ) ≤
      4 * Y * (1 + Real.log B) + 2 * B := by
  classical
  let P := hyperbolicGapCover B Y x (fun d r => r + d)
  let Q := hyperbolicGapCover B Y x (fun d r => r - d)
  have hsub : chiCubicHyperbolicIntegerPairs B Y x ⊆ P ∪ Q := by
    rintro ⟨p, r⟩ hpr
    obtain ⟨hmem, hne, hprod⟩ := Finset.mem_filter.1 hpr
    obtain ⟨hp, hr⟩ := Finset.mem_product.1 hmem
    have hpB : p ≤ B := by have := Finset.mem_range.1 hp; omega
    have hrB : r ≤ B := by have := Finset.mem_range.1 hr; omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hd : 0 < r - p := Nat.sub_pos_of_lt hlt
      have hdR : ((r - p : ℕ) : ℝ) = (r : ℝ) - p := Nat.cast_sub hlt.le
      have hprR : (p : ℝ) ≤ r := by exact_mod_cast hlt.le
      have hgap : |(p : ℝ) - r| = ((r - p : ℕ) : ℝ) := by
        rw [abs_of_nonpos (by linarith), hdR]; ring
      rw [hgap] at hprod
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.2
      refine ⟨r - p, Finset.mem_Icc.2 ⟨hd, by omega⟩, ?_⟩
      apply Finset.mem_image.2
      refine ⟨r, mem_hyperbolicGapWindow hd hprod, ?_⟩
      dsimp
      congr 1
      omega
    · have hd : 0 < p - r := Nat.sub_pos_of_lt hgt
      have hdR : ((p - r : ℕ) : ℝ) = (p : ℝ) - r := Nat.cast_sub hgt.le
      have hprR : (r : ℝ) ≤ p := by exact_mod_cast hgt.le
      have hgap : |(p : ℝ) - r| = ((p - r : ℕ) : ℝ) := by
        rw [abs_of_nonneg (by linarith), hdR]
      rw [hgap] at hprod
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.2
      refine ⟨p - r, Finset.mem_Icc.2 ⟨hd, by omega⟩, ?_⟩
      apply Finset.mem_image.2
      refine ⟨r, mem_hyperbolicGapWindow hd hprod, ?_⟩
      dsimp
      congr 1
      omega
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le P Q)
  have hcardR : ((chiCubicHyperbolicIntegerPairs B Y x).card : ℝ) ≤
      (P.card : ℝ) + Q.card := by exact_mod_cast hcard
  have hP := card_hyperbolicGapCover B hY hx (fun d r => r + d)
  have hQ := card_hyperbolicGapCover B hY hx (fun d r => r - d)
  change (P.card : ℝ) ≤ _ at hP
  change (Q.card : ℝ) ≤ _ at hQ
  linarith

/-- Literal sharp ordered hyperbolic support for one prime pair. -/
def chiCubicHyperbolicPrimeSupport (N : ℝ) (M : ℕ) (pr : ℕ × ℕ) : Set ℝ :=
  Set.Ioc N (2 * N) ∩ {x : ℝ | |(pr.1 : ℝ) - pr.2| < |x - pr.2| ∧
    |(pr.1 : ℝ) - pr.2| * |x - pr.2| ≤ (M : ℝ) * pr.2}

/-- Actual recentered cubic amplitude with the logarithmic prime density. -/
def chiCubicHyperbolicPrimeAmplitude (N : ℝ) (pr : ℕ × ℕ) (x : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) * smoothAFECutoff ((pr.1 : ℝ) / N) *
    smoothAFECutoff (x / N) * (starRingEnd ℂ) (smoothAFECutoff ((pr.2 : ℝ) / N)) /
      (pr.2 : ℂ) * (bagPhysicalHeightWindow ((pr.1 : ℝ) * x / ((pr.2 : ℝ) * N)) : ℂ) *
        bourgainOscillation (2 * Real.pi * (((pr.1 : ℝ) - pr.2) * (x - pr.2) / pr.2)) /
          (Real.log x : ℂ)

/-- The actual ordered hyperbolic prime kernel, including the sharp band,
both noncontraction conditions, the physical window and the logarithmic density. -/
def chiCubicHyperbolicPrimeKernel (N : ℝ) (M : ℕ) (x : ℝ) : ℂ :=
  ∑ pr ∈ ((primeProfileBand N).product (primeProfileBand N)).filter (fun pr => pr.1 ≠ pr.2),
    (chiCubicHyperbolicPrimeSupport N M pr).indicator (chiCubicHyperbolicPrimeAmplitude N pr) x

/-- Uniform norm bound for the actual interpolating prime-pair amplitude. -/
theorem norm_chiCubicHyperbolicPrimeAmplitude_le {N x : ℝ} (hN : 1 < N) {p r : ℕ}
    (hp : p ∈ primeProfileBand N) (hr : r ∈ primeProfileBand N)
    (hx : x ∈ Set.Icc N (2 * N)) :
    ‖chiCubicHyperbolicPrimeAmplitude N (p, r) x‖ ≤ 2 * Real.pi / (N * Real.log N) := by
  have hN0 : 0 < N := by linarith
  obtain ⟨_, hpN, _⟩ := primeProfileBand_mem hN0.le hp
  obtain ⟨_, hrN, _⟩ := primeProfileBand_mem hN0.le hr
  have hx0 : 0 < x := by linarith [hx.1]
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
  have hlogs := Real.log_le_log hN0 hx.1
  have hpV := norm_smoothAFECutoff_le_one (div_pos (hN0.trans hpN) hN0)
  have hrV := norm_smoothAFECutoff_le_one (div_pos (hN0.trans hrN) hN0)
  have hxV := norm_smoothAFECutoff_le_one (div_pos hx0 hN0)
  simp only [chiCubicHyperbolicPrimeAmplitude, norm_div, norm_mul, Complex.norm_conj,
    Complex.norm_natCast, norm_bourgainOscillation, mul_one]
  rw [Complex.norm_of_nonneg (show 0 ≤ 2 * Real.pi by positivity),
    Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg, Complex.norm_of_nonneg hlogx.le]
  calc
    _ ≤ (2 * Real.pi) * 1 * 1 * 1 / (r : ℝ) * 1 / Real.log x := by
      gcongr
      · exact bagPhysicalHeightWindow.nonneg
      · exact bagPhysicalHeightWindow.le_one
    _ ≤ (2 * Real.pi) * 1 * 1 * 1 / N * 1 / Real.log N := by gcongr
    _ = _ := by ring

/-- The literal sharp support, including both ordered exclusions, is measurable. -/
theorem chiCubicHyperbolicPrimeSupport_measurable (N : ℝ) (M : ℕ) (pr : ℕ × ℕ) :
    MeasurableSet (chiCubicHyperbolicPrimeSupport N M pr) :=
  measurableSet_Ioc.inter
    ((measurableSet_lt measurable_const ((measurable_id.sub_const (pr.2 : ℝ)).abs)).inter
      (measurableSet_le (measurable_const.mul ((measurable_id.sub_const (pr.2 : ℝ)).abs))
        measurable_const))

/-- The actual interpolated amplitude is continuous throughout its positive band. -/
theorem chiCubicHyperbolicPrimeAmplitude_continuousOn {N : ℝ} (hN : 1 < N) (pr : ℕ × ℕ) :
    ContinuousOn (chiCubicHyperbolicPrimeAmplitude N pr) (Set.Icc N (2 * N)) := by
  have hN0 : 0 < N := by linarith
  have hV : ContinuousOn (fun x : ℝ => smoothAFECutoff (x / N)) (Set.Icc N (2 * N)) :=
    contDiffOn_smoothAFECutoff_pos.continuousOn.comp
      (continuous_id.div_const N).continuousOn
      (fun x hx => div_pos (by linarith [hx.1]) hN0)
  have hW : Continuous (fun x : ℝ =>
      (bagPhysicalHeightWindow ((pr.1 : ℝ) * x / ((pr.2 : ℝ) * N)) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((bagPhysicalHeightWindow.contDiff (n := 1)).continuous.comp
        ((continuous_const.mul continuous_id).div_const _))
  have he : Continuous (fun x : ℝ =>
      bourgainOscillation (2 * Real.pi * (((pr.1 : ℝ) - pr.2) * (x - pr.2) / pr.2))) := by
    unfold bourgainOscillation
    fun_prop
  have hl : ContinuousOn (fun x : ℝ => (Real.log x : ℂ)) (Set.Icc N (2 * N)) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (by linarith [hx.1] : 0 < x)
    exact (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx0)).continuousWithinAt
  exact (((((continuousOn_const.mul hV).mul continuousOn_const).div_const _).mul
    hW.continuousOn).mul he.continuousOn).div hl (fun x hx => by
      exact_mod_cast (ne_of_gt (Real.log_pos (by linarith [hx.1] : 1 < x))))

/-- The literal kernel, including all sharp inequalities, is integrable on its band. -/
theorem integrableOn_chiCubicHyperbolicPrimeKernel {N : ℝ} (hN : 1 < N) (M : ℕ) :
    IntegrableOn (chiCubicHyperbolicPrimeKernel N M) (Set.Icc N (2 * N)) volume := by
  classical
  apply integrable_finsetSum
  intro pr _
  exact (chiCubicHyperbolicPrimeAmplitude_continuousOn hN pr).integrableOn_Icc.indicator
    (chiCubicHyperbolicPrimeSupport_measurable N M pr)

/-- At every prime q in the original band, interpolation recovers the original cubic entry. -/
theorem chiCubicHyperbolicPrimeKernel_nat {N : ℝ} (hN : 0 ≤ N) (M : ℕ) {q : ℕ}
    (hq : q ∈ primeProfileBand N) :
    chiCubicHyperbolicPrimeKernel N M q =
      ∑ p ∈ primeProfileBand N, ∑ r ∈ primeProfileBand N,
        if p ≠ r ∧ |(p : ℝ) - r| < |(q : ℝ) - r| ∧
          |(p : ℝ) - r| * |(q : ℝ) - r| ≤ (M : ℝ) * r
        then primeGaussianCubicMainEntry N p q r / (Real.log q : ℂ) else 0 := by
  classical
  have hqband : (q : ℝ) ∈ Set.Ioc N (2 * N) := (primeProfileBand_mem hN hq).2
  unfold chiCubicHyperbolicPrimeKernel
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r hr => ?_
  have hr0 : 0 < r := (primeProfileBand_mem hN hr).1.pos
  have heq : chiCubicHyperbolicPrimeAmplitude N (p, r) q =
      primeGaussianCubicMainEntry N p q r / (Real.log q : ℂ) := by
    unfold chiCubicHyperbolicPrimeAmplitude primeGaussianCubicMainEntry
    rw [primeGaussianCubic_phase_recenter p q hr0]
    push_cast
    ring
  by_cases hpr : p = r
  · simp [hpr]
  · simp [hpr, chiCubicHyperbolicPrimeSupport, Set.indicator_apply, hqband, heq]

/-- The complete prime kernel is uniformly bounded in the real interpolation point. -/
theorem norm_chiCubicHyperbolicPrimeKernel_le {N x : ℝ} (hN : 4 ≤ N)
    (hlog : 1 ≤ Real.log N) (M : ℕ) (hx : x ∈ Set.Icc N (2 * N)) :
    ‖chiCubicHyperbolicPrimeKernel N M x‖ ≤ 64 * Real.pi * ((M : ℝ) + 1) := by
  classical
  have hN0 : 0 < N := by linarith
  have hN1 : 1 < N := by linarith
  let S := ((primeProfileBand N).product (primeProfileBand N)).filter
    (fun pr => pr.1 ≠ pr.2 ∧ x ∈ chiCubicHyperbolicPrimeSupport N M pr)
  have heq : chiCubicHyperbolicPrimeKernel N M x = ∑ pr ∈ S, chiCubicHyperbolicPrimeAmplitude N pr x := by
    unfold chiCubicHyperbolicPrimeKernel
    simp only [S, Finset.sum_filter]
    refine Finset.sum_congr rfl fun pr _ => ?_
    by_cases hpr : pr.1 = pr.2 <;> simp [hpr, Set.indicator_apply]
  let B := ⌊2 * N⌋₊
  have hsub : S ⊆ chiCubicHyperbolicIntegerPairs B (2 * (M : ℝ) * N) x := by
    rintro ⟨p, r⟩ hpr
    obtain ⟨hmem, hne, hsupp⟩ := Finset.mem_filter.1 hpr
    obtain ⟨hp, hr⟩ := Finset.mem_product.1 hmem
    have hpB := Nat.le_floor (primeProfileBand_mem hN0.le hp).2.2
    have hrB := Nat.le_floor (primeProfileBand_mem hN0.le hr).2.2
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2
      ⟨Finset.mem_range.2 (by dsimp [B]; omega), Finset.mem_range.2 (by dsimp [B]; omega)⟩, hne, ?_⟩
    have hprod := hsupp.2.2
    have hmul := mul_le_mul_of_nonneg_left (primeProfileBand_mem hN0.le hr).2.2 (Nat.cast_nonneg M)
    exact hprod.trans (by nlinarith)
  have hcard : (S.card : ℝ) ≤ 4 * (2 * (M : ℝ) * N) * (1 + Real.log B) + 2 * B :=
    (show (S.card : ℝ) ≤ (chiCubicHyperbolicIntegerPairs B (2 * (M : ℝ) * N) x).card by
      exact_mod_cast Finset.card_le_card hsub).trans
        (card_chiCubicHyperbolicIntegerPairs B (by positivity) (by linarith [hx.1]))
  have hB0 : (0 : ℝ) < B := by
    exact_mod_cast (Nat.floor_pos.2 (show 1 ≤ 2 * N by linarith))
  have hB : (B : ℝ) ≤ 2 * N := Nat.floor_le (by positivity)
  have hlogB : 1 + Real.log B ≤ 3 * Real.log N := by
    have h := Real.log_le_log hB0 hB
    rw [Real.log_mul (by norm_num) hN0.ne'] at h
    have htwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    linarith
  have hcard' : (S.card : ℝ) ≤ (24 * (M : ℝ) + 4) * N * Real.log N := by
    have hh := mul_le_mul_of_nonneg_left hlogB (show 0 ≤ 4 * (2 * (M : ℝ) * N) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4 * N by positivity)
    nlinarith
  rw [heq]
  calc ‖∑ pr ∈ S, chiCubicHyperbolicPrimeAmplitude N pr x‖
      ≤ ∑ _pr ∈ S, 2 * Real.pi / (N * Real.log N) := by
        apply norm_sum_le_of_le
        intro pr hpr
        have hp := Finset.mem_product.1 (Finset.mem_filter.1 hpr).1
        exact norm_chiCubicHyperbolicPrimeAmplitude_le hN1 hp.1 hp.2 hx
    _ = (S.card : ℝ) * (2 * Real.pi / (N * Real.log N)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((24 * (M : ℝ) + 4) * N * Real.log N) * (2 * Real.pi / (N * Real.log N)) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = 2 * Real.pi * (24 * (M : ℝ) + 4) := by field_simp
    _ ≤ 64 * Real.pi * ((M : ℝ) + 1) := by nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) M]

/-- Actual von Mangoldt density in the multiplicative window of length x N⁻⁴/⁵. -/
def chiCubicPrimeWindowDensity (N x : ℝ) : ℝ :=
  (Chebyshev.psi (x + N ^ ((1 : ℝ) / 5 - 1) * x) - Chebyshev.psi x) /
    (N ^ ((1 : ℝ) / 5 - 1) * x)

private theorem primeWindowDensity_measurable (N : ℝ) :
    Measurable (chiCubicPrimeWindowDensity N) := by
  unfold chiCubicPrimeWindowDensity
  exact ((Chebyshev.psi_mono.measurable.comp
    (measurable_id.add (measurable_const.mul measurable_id))).sub
      Chebyshev.psi_mono.measurable).div (measurable_const.mul measurable_id)

private theorem primeWindowDensity_error_norm {N x : ℝ} (hN : 0 < N) (hx : 0 < x) :
    ‖((chiCubicPrimeWindowDensity N x - 1 : ℝ) : ℂ)‖ =
      chiCubicPrimeWindowError (1 / 5) N x := by
  have hd : 0 < N ^ ((1 : ℝ) / 5 - 1) * x := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold chiCubicPrimeWindowDensity chiCubicPrimeWindowError
  rw [div_sub_one hd.ne', abs_div, abs_of_pos hd]

/-- Signed error of replacing the actual prime-window density by one, paired with
the literal hyperbolic kernel. No exceptional subset is removed. -/
def chiCubicHyperbolicPrimeDensityError (N : ℝ) (M : ℕ) : ℂ :=
  ∫ x in Set.Icc N (2 * N), ((chiCubicPrimeWindowDensity N x - 1 : ℝ) : ℂ) *
    chiCubicHyperbolicPrimeKernel N M x

private theorem hyperbolicPrimeDensityError_control {N : ℝ} (hN : 4 ≤ N)
    (hlog : 1 ≤ Real.log N) (M : ℕ)
    (hR : IntegrableOn (chiCubicPrimeWindowError (1 / 5) N) (Set.Icc N (2 * N)) volume) :
    IntegrableOn (fun x => ((chiCubicPrimeWindowDensity N x - 1 : ℝ) : ℂ) *
      chiCubicHyperbolicPrimeKernel N M x) (Set.Icc N (2 * N)) volume ∧
    ‖chiCubicHyperbolicPrimeDensityError N M‖ ≤
      (64 * Real.pi * ((M : ℝ) + 1)) *
        ∫ x in Set.Icc N (2 * N), chiCubicPrimeWindowError (1 / 5) N x := by
  have hN0 : 0 < N := by linarith
  have hi : IntegrableOn (fun x => ((chiCubicPrimeWindowDensity N x - 1 : ℝ) : ℂ))
      (Set.Icc N (2 * N)) volume := by
    refine hR.mono' (Complex.measurable_ofReal.comp
      ((primeWindowDensity_measurable N).sub measurable_const)).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (primeWindowDensity_error_norm hN0 (by linarith [hx.1])).le
  have hK := integrableOn_chiCubicHyperbolicPrimeKernel (show 1 < N by linarith) M
  have hprod := hi.mul_bdd hK.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact norm_chiCubicHyperbolicPrimeKernel_le hN hlog M hx)
  refine ⟨hprod, ?_⟩
  calc
    ‖chiCubicHyperbolicPrimeDensityError N M‖ ≤
        ∫ x in Set.Icc N (2 * N), ‖((chiCubicPrimeWindowDensity N x - 1 : ℝ) : ℂ) *
          chiCubicHyperbolicPrimeKernel N M x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Icc N (2 * N),
        (64 * Real.pi * ((M : ℝ) + 1)) * chiCubicPrimeWindowError (1 / 5) N x := by
      apply setIntegral_mono_on hprod.norm (hR.const_mul _) measurableSet_Icc
      intro x hx
      rw [norm_mul, ← primeWindowDensity_error_norm hN0 (by linarith [hx.1])]
      exact (mul_le_mul_of_nonneg_left
        (norm_chiCubicHyperbolicPrimeKernel_le hN hlog M hx) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

/-- At every fixed integer hyperbolic radius, replacing the actual short prime-window
density by one costs o(N / log² N), with the entire exceptional set retained. -/
theorem chiCubicHyperbolicPrimeDensityError_tendsto (M : ℕ) :
    (∀ᶠ N : ℝ in atTop, IntegrableOn
      (fun x => ((chiCubicPrimeWindowDensity N x - 1 : ℝ) : ℂ) *
        chiCubicHyperbolicPrimeKernel N M x) (Set.Icc N (2 * N)) volume) ∧
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N *
      ‖chiCubicHyperbolicPrimeDensityError N M‖) atTop (𝓝 0) := by
  have hrate := chiCubicPrimeWindowError_logRate 2
    (θ := (1 : ℝ) / 5) (by norm_num) (by norm_num)
  have hlogs : ∀ᶠ N : ℝ in atTop, 1 ≤ Real.log N :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  constructor
  · filter_upwards [eventually_ge_atTop (4 : ℝ), hlogs, hrate.1] with N hN hlog hR
    exact (hyperbolicPrimeDensityError_control hN hlog M hR).1
  · have hlim := hrate.2.const_mul (64 * Real.pi * ((M : ℝ) + 1))
    simp only [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with N hN
      exact mul_nonneg (div_nonneg (sq_nonneg _) (by linarith)) (norm_nonneg _)
    · filter_upwards [eventually_ge_atTop (4 : ℝ), hlogs, hrate.1] with N hN hlog hR
      have hN0 : 0 < N := by linarith
      have hR0 : 0 ≤ ∫ x in Set.Icc N (2 * N), chiCubicPrimeWindowError (1 / 5) N x := by
        apply setIntegral_nonneg measurableSet_Icc
        intro x hx
        rw [← primeWindowDensity_error_norm hN0 (by linarith [hx.1])]
        exact norm_nonneg _
      have hL : Real.log N ^ 2 ≤ (Real.log (N ^ 2) + 2) ^ 2 := by
        have := Real.log_le_log hN0 (show N ≤ N ^ 2 by nlinarith)
        nlinarith
      calc
        Real.log N ^ 2 / N * ‖chiCubicHyperbolicPrimeDensityError N M‖ ≤
            Real.log N ^ 2 / N * ((64 * Real.pi * ((M : ℝ) + 1)) *
              ∫ x in Set.Icc N (2 * N), chiCubicPrimeWindowError (1 / 5) N x) :=
          mul_le_mul_of_nonneg_left (hyperbolicPrimeDensityError_control hN hlog M hR).2
            (by positivity)
        _ ≤ (Real.log (N ^ 2) + 2) ^ 2 / N * ((64 * Real.pi * ((M : ℝ) + 1)) *
              ∫ x in Set.Icc N (2 * N), chiCubicPrimeWindowError (1 / 5) N x) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hL hN0.le)
            (mul_nonneg (by positivity) hR0)
        _ = _ := by ring

end RHTower

end
