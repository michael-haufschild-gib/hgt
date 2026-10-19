import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateOddProfileCoordinates
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateInfinityFailure

/-!
# The Collar Deficit Law: Origin Prime-2 Removal and Infinity Peak-Band Absorption

In `ShiftedGroundStateOriginFailure` and `ShiftedGroundStateInfinityFailure`, the raw reflected
collar mass `shiftedCollarMass a x` (`C_a(x)`) fails the pointwise folded supersolution bound
`C_a(x) ≤ sinh(a/2) sinh(x/2)` in two asymptotic regimes:
1. **Near the origin (`x → 0⁺`, `a > log 2`):** the `n = 2` prime atom contributes
   `Λ(2)/√2 · m_a(log 2 − x)⁺ > 0`, while the target `sinh(a/2) sinh(x/2)` vanishes at `x = 0`.
2. **Near infinity (`x ≥ a`):** the theta harmonic identity forces `C_a(x) ≥ 2 sinh(a/2) sinh(x/2) − K`,
   exceeding the single-source target `sinh(a/2) sinh(x/2)` because the collar retains the entire
   peak band `t ∈ (x, x + a]` around `t = x + a` where `Φ(t − x − a)` attains `Φ(0)`.

By contrast, `ShiftedGroundStateMonotoneFoldDomination` replaces the pointwise collar test by the
monotone fold-domination criterion `foldExcessWeight a x ≤ 2 sinh(a/2) sinh(x/2)`, which both doubles
the available source budget and replaces `m_a(t − x)⁺` by `foldExcessDensity a t x`.

This module proves the **Collar Deficit Law** quantifying the exact mass removed when passing from
`shiftedCollarMass a x` to `foldExcessWeight a x`:

1. **Discarded Dual-Threshold Collar Density and Mass
   (`discardedThresholdCollarDensity`, `discardedThresholdCollarMass`,
   `foldExcessDensity_add_discardedThresholdCollarDensity_le`,
   `foldExcessWeight_add_discardedThresholdCollarMass_le_shiftedCollarMass`):**
   On the sub-threshold region `t ≤ max(2x, a − x)`, `foldExcessDensity a t x = 0` while the raw
   collar retains `m_a(t − x)⁺`. Consequently, for all `a > 0` and `x > 0`,
   `foldExcessWeight a x + discardedThresholdCollarMass a x ≤ shiftedCollarMass a x`.

2. **Exact Far-Field Subtraction (`foldExcessDensity_add_shiftDifference_eq_of_gt`):**
   Even on the surviving region `t > 2x`, whenever `m_a(x + t) ≤ m_a(t − x)`, the fold-excess
   density is smaller than the raw collar density by the strictly positive reflected tail
   `m_a(x + t) > 0`.

3. **Quantitative Origin Prime-2 Obstruction Removal
   (`foldExcessWeight_add_prime_two_collar_le_shiftedCollarMass`):**
   Whenever `log 2 ≤ max(2x, a − x)` (which holds on the origin collar `0 < x ≤ a − log 2` for every
   `a > log 2`, and globally for all `x > 0` when `a ≥ (3/2) log 2`), the entire `n = 2` prime collar
   contribution `Λ(2)/√2 · m_a(log 2 − x)⁺` is absorbed into `discardedThresholdCollarMass a x`:
   `foldExcessWeight a x + vonMangoldtAtom 2 * max (shiftDifference a (log 2 − x)) 0 ≤ shiftedCollarMass a x`.

4. **Infinity Peak-Band Absorption (`peak_point_le_max_threshold`,
   `sum_subthreshold_primes_le_discardedThresholdCollarMass`,
   `foldExcessWeight_add_peak_band_primes_le_shiftedCollarMass`):**
   For every `x ≥ a > 0`, the peak point `t = x + a` of `Φ(t − x − a)` satisfies
   `x < x + a ≤ 2x = max(2x, a − x)`. Thus the entire peak band `t ∈ (x, 2x]` (including every
   prime power `n` with `log n ≤ 2x`, and in particular the peak window `e^x < n ≤ e^{x+a}`) lies
   inside the discarded threshold region where `foldExcessDensity a t x = 0`. Every finite sum of
   prime-power collar terms in `log n ≤ max(2x, a − x)` is therefore subtracted from
   `shiftedCollarMass a x` in `foldExcessWeight a x`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped BigOperators
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ## §1. Discarded Dual-Threshold Collar Density and Pointwise Deficit -/

/-- The portion of the raw collar density `max (shiftDifference a (t - x)) 0` that lies in the
dual-threshold annihilation region `t ≤ max (2 * x) (a - x)`, where `foldExcessDensity a t x = 0`. -/
def discardedThresholdCollarDensity (a t x : ℝ) : ℝ :=
  if t ≤ max (2 * x) (a - x) then max (shiftDifference a (t - x)) 0 else 0

theorem discardedThresholdCollarDensity_nonneg (a t x : ℝ) :
    0 ≤ discardedThresholdCollarDensity a t x := by
  unfold discardedThresholdCollarDensity
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem discardedThresholdCollarDensity_le_max (a t x : ℝ) :
    discardedThresholdCollarDensity a t x ≤ max (shiftDifference a (t - x)) 0 := by
  unfold discardedThresholdCollarDensity
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem discardedThresholdCollarDensity_eq_of_le {a t x : ℝ}
    (ht : t ≤ max (2 * x) (a - x)) :
    discardedThresholdCollarDensity a t x = max (shiftDifference a (t - x)) 0 := by
  unfold discardedThresholdCollarDensity
  exact if_pos ht

private theorem foldExcessDensity_eq_zero_of_le_max' {a t x : ℝ} (hx : 0 ≤ x)
    (ht : t ≤ max (2 * x) (a - x)) :
    foldExcessDensity a t x = 0 := by
  rcases le_or_gt t (2 * x) with h2x | h2x
  · exact foldExcessDensity_of_le h2x
  · have hsub : t ≤ a - x := by
      rcases le_max_iff.mp ht with h | h
      · linarith
      · exact h
    exact foldExcessDensity_eq_zero_of_add_le hx (by linarith) (by linarith)

/-- **Pointwise Dual-Threshold Collar Deficit Inequality
(`foldExcessDensity_add_discardedThresholdCollarDensity_le`):**
For all `a ≥ 0`, `t ≥ 0`, and `x ≥ 0`, the sum of `foldExcessDensity a t x` and the discarded
sub-threshold collar density is bounded by the raw collar density `max (shiftDifference a (t - x)) 0`. -/
theorem foldExcessDensity_add_discardedThresholdCollarDensity_le
    {a t x : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    foldExcessDensity a t x + discardedThresholdCollarDensity a t x ≤
      max (shiftDifference a (t - x)) 0 := by
  unfold discardedThresholdCollarDensity
  split_ifs with hle
  · rw [foldExcessDensity_eq_zero_of_le_max' hx hle, zero_add]
  · rw [add_zero]
    exact foldExcessDensity_le_max ha ht hx

/-- **Exact Far-Field Subtraction (`foldExcessDensity_add_shiftDifference_eq_of_gt`):**
On the region `2 * x < t`, whenever `shiftDifference a (x + t) ≤ shiftDifference a (t - x)`, the
fold-excess density plus the reflected tail `shiftDifference a (x + t)` equals the raw collar
density `max (shiftDifference a (t - x)) 0`. -/
theorem foldExcessDensity_add_shiftDifference_eq_of_gt
    {a t x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (ht : 2 * x < t)
    (hle : shiftDifference a (x + t) ≤ shiftDifference a (t - x)) :
    foldExcessDensity a t x + shiftDifference a (x + t) =
      max (shiftDifference a (t - x)) 0 := by
  have hpos : 0 < shiftDifference a (x + t) := shiftDifference_pos ha (by linarith)
  have hmax : max (shiftDifference a (t - x)) 0 = shiftDifference a (t - x) :=
    max_eq_left (by linarith)
  unfold foldExcessDensity
  rw [if_pos ht, max_eq_left (sub_nonneg.mpr hle), hmax, sub_add_cancel]

/-! ## §2. Integrability, Summability, and the Global Collar Deficit Law -/

/-- The total collar mass discarded by the dual threshold `t ≤ max(2x, a - x)`, combining the
archimedean continuum integral and the discrete von Mangoldt prime-power sum. -/
def discardedThresholdCollarMass (a x : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * discardedThresholdCollarDensity a t x) +
    ∑' n : ℕ, vonMangoldtAtom n * discardedThresholdCollarDensity a (Real.log n) x

theorem discardedThresholdCollarMass_nonneg (a x : ℝ) :
    0 ≤ discardedThresholdCollarMass a x := by
  unfold discardedThresholdCollarMass
  refine add_nonneg ?_ ?_
  · exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le
        (discardedThresholdCollarDensity_nonneg a t x)
  · exact tsum_nonneg fun n =>
      mul_nonneg (vonMangoldtAtom_nonneg n)
        (discardedThresholdCollarDensity_nonneg a (Real.log n) x)

private theorem integrableOn_archLevy_foldExcessDensity' {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    IntegrableOn (fun t => archLevyDensity t * foldExcessDensity a t x) (Ioi 0) := by
  have hm : Measurable fun t => foldExcessDensity a t x :=
    (measurable_foldExcessDensity_uncurry a).comp (measurable_id.prodMk measurable_const)
  refine (integrableOn_archLevy_max_shiftDifference ha hx).mono'
    (measurable_archLevyDensity.mul hm).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 := (mem_Ioi.mp ht).le
  have hL := (archLevyDensity_pos (mem_Ioi.mp ht)).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hL,
    abs_of_nonneg (foldExcessDensity_nonneg a t x)]
  exact mul_le_mul_of_nonneg_left (foldExcessDensity_le_max ha.le ht0 hx.le) hL

theorem integrableOn_archLevy_discardedThresholdCollarDensity
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    IntegrableOn (fun t => archLevyDensity t * discardedThresholdCollarDensity a t x) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_archLevy_max_shiftDifference ha hx) ?_ ?_
  · have hm : Measurable fun t => discardedThresholdCollarDensity a t x := by
      unfold discardedThresholdCollarDensity
      exact Measurable.ite measurableSet_Iic
        (((continuous_shiftDifference a).comp (continuous_id.sub continuous_const)).max
          continuous_const).measurable
        measurable_const
    exact (measurable_archLevyDensity.mul hm).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos ht0).le
      (discardedThresholdCollarDensity_nonneg a t x))]
    exact mul_le_mul_of_nonneg_left (discardedThresholdCollarDensity_le_max a t x)
      (archLevyDensity_pos ht0).le

theorem summable_atom_discardedThresholdCollarDensity (a x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * discardedThresholdCollarDensity a (Real.log n) x :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (vonMangoldtAtom_nonneg n)
      (discardedThresholdCollarDensity_nonneg a (Real.log n) x))
    (fun n => mul_le_mul_of_nonneg_left
      (discardedThresholdCollarDensity_le_max a (Real.log n) x) (vonMangoldtAtom_nonneg n))
    (summable_atom_max_shiftDifference a x)

/-- **Global Collar Deficit Law
(`foldExcessWeight_add_discardedThresholdCollarMass_le_shiftedCollarMass`):**
For every shift `a > 0` and position `x > 0`, the monotone fold-domination weight `foldExcessWeight a x`
plus the discarded dual-threshold collar mass is bounded by `shiftedCollarMass a x`. -/
theorem foldExcessWeight_add_discardedThresholdCollarMass_le_shiftedCollarMass
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    foldExcessWeight a x + discardedThresholdCollarMass a x ≤ shiftedCollarMass a x := by
  unfold foldExcessWeight discardedThresholdCollarMass shiftedCollarMass
  have harch :
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessDensity a t x) +
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * discardedThresholdCollarDensity a t x) ≤
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0 := by
    rw [← integral_add (integrableOn_archLevy_foldExcessDensity' ha hx)
      (integrableOn_archLevy_discardedThresholdCollarDensity ha hx)]
    refine setIntegral_mono_on
      ((integrableOn_archLevy_foldExcessDensity' ha hx).add
        (integrableOn_archLevy_discardedThresholdCollarDensity ha hx))
      (integrableOn_archLevy_max_shiftDifference ha hx) measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (foldExcessDensity_add_discardedThresholdCollarDensity_le ha.le ht0.le hx.le)
      (archLevyDensity_pos ht0).le
  have hprime :
      (∑' n : ℕ, vonMangoldtAtom n * foldExcessDensity a (Real.log n) x) +
        (∑' n : ℕ, vonMangoldtAtom n * discardedThresholdCollarDensity a (Real.log n) x) ≤
      ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 := by
    rw [← (summable_atom_mul_foldExcessDensity ha.le hx.le).tsum_add
      (summable_atom_discardedThresholdCollarDensity a x)]
    refine Summable.tsum_le_tsum (fun n => ?_)
      ((summable_atom_mul_foldExcessDensity ha.le hx.le).add
        (summable_atom_discardedThresholdCollarDensity a x))
      (summable_atom_max_shiftDifference a x)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (foldExcessDensity_add_discardedThresholdCollarDensity_le ha.le
        (Real.log_natCast_nonneg n) hx.le)
      (vonMangoldtAtom_nonneg n)
  linarith

/-! ## §3. Finite Sub-Threshold Prime-Power Lower Bounds: Origin & Infinity Peak Removal -/

/-- Any finite sum of prime-power collar terms whose logarithms lie below `max(2x, a - x)` is
bounded by the discrete part of `discardedThresholdCollarMass a x`, and hence by
`discardedThresholdCollarMass a x` itself. -/
theorem sum_subthreshold_primes_le_discardedThresholdCollarMass
    (a x : ℝ) (S : Finset ℕ) (hS : ∀ n ∈ S, Real.log n ≤ max (2 * x) (a - x)) :
    ∑ n ∈ S, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 ≤
      discardedThresholdCollarMass a x := by
  have harch0 :
      0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * discardedThresholdCollarDensity a t x :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le
        (discardedThresholdCollarDensity_nonneg a t x)
  have hsum :
      ∑ n ∈ S, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 =
        ∑ n ∈ S, vonMangoldtAtom n * discardedThresholdCollarDensity a (Real.log n) x := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [discardedThresholdCollarDensity_eq_of_le (hS n hn)]
  have hle :
      ∑ n ∈ S, vonMangoldtAtom n * discardedThresholdCollarDensity a (Real.log n) x ≤
        ∑' n : ℕ, vonMangoldtAtom n * discardedThresholdCollarDensity a (Real.log n) x :=
    (summable_atom_discardedThresholdCollarDensity a x).sum_le_tsum S fun n _ =>
      mul_nonneg (vonMangoldtAtom_nonneg n)
        (discardedThresholdCollarDensity_nonneg a (Real.log n) x)
  unfold discardedThresholdCollarMass
  linarith

/-- **Quantitative Origin Prime-2 Obstruction Removal
(`foldExcessWeight_add_prime_two_collar_le_shiftedCollarMass`):**
Whenever `log 2 ≤ max(2x, a - x)` (in particular on the origin collar `0 < x ≤ a - log 2` for any
`a > log 2`, and globally for all `x > 0` when `a ≥ (3/2) log 2`), the `n = 2` prime collar atom
`vonMangoldtAtom 2 * max (shiftDifference a (log 2 - x)) 0` that causes the origin failure of
`shiftedCollarMass a x` is subtracted out when passing to `foldExcessWeight a x`. -/
theorem foldExcessWeight_add_prime_two_collar_le_shiftedCollarMass
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (h2 : Real.log 2 ≤ max (2 * x) (a - x)) :
    foldExcessWeight a x +
        vonMangoldtAtom 2 * max (shiftDifference a (Real.log 2 - x)) 0 ≤
      shiftedCollarMass a x := by
  have hsingle :
      vonMangoldtAtom 2 * max (shiftDifference a (Real.log 2 - x)) 0 ≤
        discardedThresholdCollarMass a x := by
    have h := sum_subthreshold_primes_le_discardedThresholdCollarMass a x {2}
      (fun n hn => by
        rw [Finset.mem_singleton.mp hn]
        exact_mod_cast h2)
    simpa using h
  linarith [foldExcessWeight_add_discardedThresholdCollarMass_le_shiftedCollarMass ha hx]

/-- For `(3/2) log 2 ≤ a`, the prime-2 collar deficit holds globally for every `x > 0`. -/
theorem foldExcessWeight_add_prime_two_collar_le_shiftedCollarMass_of_three_halves_log_two_le
    {a x : ℝ} (ha : 3 / 2 * Real.log 2 ≤ a) (hx : 0 < x) :
    foldExcessWeight a x +
        vonMangoldtAtom 2 * max (shiftDifference a (Real.log 2 - x)) 0 ≤
      shiftedCollarMass a x := by
  have ha0 : 0 < a := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have h2 : Real.log 2 ≤ max (2 * x) (a - x) := by
    by_cases hx2 : Real.log 2 ≤ 2 * x
    · exact le_max_of_le_left hx2
    · exact le_max_of_le_right (by linarith)
  exact foldExcessWeight_add_prime_two_collar_le_shiftedCollarMass ha0 hx h2

/-- **Infinity Peak-Band Inclusion (`peak_point_le_max_threshold`):**
In the large-`x` regime `x ≥ a > 0`, the peak point `t = x + a` of `Φ(t - x - a)` satisfies
`x < x + a ≤ 2x = max(2x, a - x)`, so `foldExcessDensity a (x + a) x = 0` while the raw collar
evaluates to `Φ(0) - Φ(2a) > 0`. -/
theorem peak_point_le_max_threshold {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) :
    x + a ≤ max (2 * x) (a - x) ∧
      foldExcessDensity a (x + a) x = 0 ∧
      discardedThresholdCollarDensity a (x + a) x = riemannKernelReal 0 - riemannKernelReal (2 * a) := by
  have hle : x + a ≤ max (2 * x) (a - x) := le_max_of_le_left (by linarith)
  refine ⟨hle, foldExcessDensity_eq_zero_of_le_max' (by linarith) hle, ?_⟩
  rw [discardedThresholdCollarDensity_eq_of_le hle]
  have hpos : 0 < shiftDifference a ((x + a) - x) :=
    shiftDifference_pos ha (by linarith)
  rw [max_eq_left hpos.le]
  unfold shiftDifference
  rw [show x + a - x - a = 0 by ring, show x + a - x + a = 2 * a by ring]

/-- **Infinity Peak-Band Prime Absorption (`foldExcessWeight_add_peak_band_primes_le_shiftedCollarMass`):**
For every `x ≥ a > 0` and every finite set `S` of integers with `log n ≤ 2x` (which includes all
prime powers up to `⌊e^{2x}⌋`, and in particular the entire peak band `e^x < n ≤ e^{x+a}`), the sum
of their reflected collar contributions is absorbed into the gap between `shiftedCollarMass a x`
and `foldExcessWeight a x`. -/
theorem foldExcessWeight_add_peak_band_primes_le_shiftedCollarMass
    {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) (S : Finset ℕ)
    (hS : ∀ n ∈ S, Real.log n ≤ 2 * x) :
    foldExcessWeight a x +
        (∑ n ∈ S, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0) ≤
      shiftedCollarMass a x := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  have hsub := sum_subthreshold_primes_le_discardedThresholdCollarMass a x S
    (fun n hn => le_trans (hS n hn) (le_max_left _ _))
  linarith [foldExcessWeight_add_discardedThresholdCollarMass_le_shiftedCollarMass ha hx0]

/-- **Surviving Far-Field Kernel Decay Bound (`foldExcessDensity_le_kernel_sub_of_ge`):**
For `x ≥ a ≥ 0` and any `t ≥ 0`, `foldExcessDensity a t x` vanishes on `t ≤ 2x` and on `t > 2x`
is bounded above by `riemannKernelReal (t - x - a)`, where the argument `t - x - a > x - a ≥ 0` is
strictly separated from the peak `0` of Riemann's kernel by at least `x - a`. -/
theorem foldExcessDensity_le_kernel_sub_of_ge
    {a t x : ℝ} (ha : 0 ≤ a) (hx : a ≤ x) :
    (foldExcessDensity a t x ≤
      if 2 * x < t then riemannKernelReal (t - x - a) else 0) ∧
      (2 * x < t → riemannKernelReal (t - x - a) ≤ riemannKernelReal (x - a)) := by
  refine ⟨?_, fun ht => riemannKernelReal_antitone_of_nonneg (by linarith) (by linarith)⟩
  split_ifs with ht
  · exact (foldExcessDensity_le_max ha (by linarith) (by linarith)).trans
      (max_shiftDifference_le a (t - x))
  · exact (foldExcessDensity_of_le (not_lt.mp ht)).le

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
