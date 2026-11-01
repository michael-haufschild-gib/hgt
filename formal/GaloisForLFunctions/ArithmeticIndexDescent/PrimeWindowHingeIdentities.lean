import GaloisForLFunctions.ArithmeticIndexDescent.TheFullPrimeWindowCancelsTheGrowingHeadPole
import GaloisForLFunctions.RHTower.Suzuki.SuzukiExplicitScrewRegularKernel

/-!
# Prime windows as hinge differences

The correlation of two interval indicators is a four-hinge difference.
This retains the exact window endpoints when transferring prime-source rates.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
open RHTower
open GaloisForLFunctions.RHTower
namespace GaloisForLFunctions.ArithmeticIndexDescent

private theorem clipped_overlap_eq_hinges {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    max 0 (min b d - max a c) =
      max 0 (c - b) - max 0 (c - a) - max 0 (d - b) + max 0 (d - a) := by
  by_cases hbc : b ≤ c
  · have hac : a ≤ c := hab.trans hbc
    have hbd : b ≤ d := hbc.trans hcd
    have had : a ≤ d := hab.trans hbd
    simp only [min_eq_left hbd, max_eq_right hac,
      max_eq_left (sub_nonpos.mpr hbc), max_eq_right (sub_nonneg.mpr hbc),
      max_eq_right (sub_nonneg.mpr hac), max_eq_right (sub_nonneg.mpr hbd),
      max_eq_right (sub_nonneg.mpr had)]
    ring
  by_cases hda : d ≤ a
  · have hca : c ≤ a := hcd.trans hda
    have hdb : d ≤ b := hda.trans hab
    have hcb : c ≤ b := hca.trans hab
    simp only [min_eq_right hdb, max_eq_left hca,
      max_eq_left (sub_nonpos.mpr hda), max_eq_left (sub_nonpos.mpr hca),
      max_eq_left (sub_nonpos.mpr hdb), max_eq_left (sub_nonpos.mpr hcb),
      sub_zero, add_zero]
  have hcb : c ≤ b := (lt_of_not_ge hbc).le
  have had : a ≤ d := (lt_of_not_ge hda).le
  by_cases hac : a ≤ c
  · by_cases hbd : b ≤ d
    · simp only [min_eq_left hbd, max_eq_right hac,
        max_eq_right (sub_nonneg.mpr hcb), max_eq_left (sub_nonpos.mpr hcb),
        max_eq_right (sub_nonneg.mpr hac), max_eq_right (sub_nonneg.mpr hbd),
        max_eq_right (sub_nonneg.mpr had)]
      ring
    · have hdb : d ≤ b := (lt_of_not_ge hbd).le
      simp only [min_eq_right hdb, max_eq_right hac,
        max_eq_right (sub_nonneg.mpr hcd), max_eq_left (sub_nonpos.mpr hcb),
        max_eq_right (sub_nonneg.mpr hac), max_eq_left (sub_nonpos.mpr hdb),
        max_eq_right (sub_nonneg.mpr had)]
      ring
  · have hca : c ≤ a := (lt_of_not_ge hac).le
    by_cases hbd : b ≤ d
    · simp only [min_eq_left hbd, max_eq_left hca,
        max_eq_right (sub_nonneg.mpr hab), max_eq_left (sub_nonpos.mpr hcb),
        max_eq_left (sub_nonpos.mpr hca), max_eq_right (sub_nonneg.mpr hbd),
        max_eq_right (sub_nonneg.mpr had)]
      ring
    · have hdb : d ≤ b := (lt_of_not_ge hbd).le
      simp only [min_eq_right hdb, max_eq_left hca,
        max_eq_right (sub_nonneg.mpr had), max_eq_left (sub_nonpos.mpr hcb),
        max_eq_left (sub_nonpos.mpr hca), max_eq_left (sub_nonpos.mpr hdb),
        sub_zero, zero_add]

/-- Unequal interval correlations retain all four endpoint hinges exactly. -/
theorem intervalCorrelation_eq_four_hinges {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (s : ℝ) :
    (∫ u : ℝ, (Set.Ico a b).indicator (fun _ => (1 : ℝ)) u *
      (Set.Ico c d).indicator (fun _ => (1 : ℝ)) (u + s)) =
      max 0 (c - b - s) - max 0 (c - a - s) -
        max 0 (d - b - s) + max 0 (d - a - s) := by
  have heq : (fun u : ℝ => (Set.Ico a b).indicator (fun _ => (1 : ℝ)) u *
      (Set.Ico c d).indicator (fun _ => (1 : ℝ)) (u + s)) =
      (Set.Ico (max a (c - s)) (min b (d - s))).indicator (1 : ℝ → ℝ) := by
    funext u
    have hm : u ∈ Set.Ico (max a (c - s)) (min b (d - s)) ↔
        u ∈ Set.Ico a b ∧ u + s ∈ Set.Ico c d := by
      simp only [Set.mem_Ico, max_le_iff, lt_min_iff]
      constructor
      · rintro ⟨⟨ha, hc⟩, hb, hd⟩
        exact ⟨⟨ha, hb⟩, ⟨by linarith only [hc], by linarith only [hd]⟩⟩
      · rintro ⟨⟨ha, hb⟩, hc, hd⟩
        exact ⟨⟨ha, by linarith only [hc]⟩, hb, by linarith only [hd]⟩
    by_cases h1 : u ∈ Set.Ico a b <;> by_cases h2 : u + s ∈ Set.Ico c d
    all_goals simp [hm, h1, h2]
  rw [heq, integral_indicator_one measurableSet_Ico, Measure.real,
    Real.volume_Ico, ENNReal.toReal_ofReal', max_comm]
  have h1 : c - s - b = c - b - s := by ring
  have h2 : c - s - a = c - a - s := by ring
  have h3 : d - s - b = d - b - s := by ring
  have h4 : d - s - a = d - a - s := by ring
  simpa only [h1, h2, h3, h4] using
    clipped_overlap_eq_hinges hab (by linarith only [hcd] : c - s ≤ d - s)


/-- The mixed endpoint difference of a scalar primitive on two intervals. -/
def intervalMixedDifference (F : ℝ → ℝ) (l r p q : ℝ) : ℝ :=
  F (p - r) - F (p - l) - F (q - r) + F (q - l)


/-- Exponential endpoint differences factor into the two polar interval moments. -/
theorem intervalMixedDifference_exp_half (L l r p q : ℝ) :
    intervalMixedDifference (fun z => Real.exp ((L + z) / 2)) l r p q =
      Real.exp (L / 2) * (Real.exp (-l / 2) - Real.exp (-r / 2)) *
        (Real.exp (q / 2) - Real.exp (p / 2)) := by
  have he (x y : ℝ) : Real.exp ((L + (x - y)) / 2) =
      Real.exp (L / 2) * Real.exp (x / 2) * Real.exp (-y / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [intervalMixedDifference, he p r, he p l, he q r, he q l]
  ring

/-- Four endpoint errors bound their mixed difference. -/
theorem abs_intervalMixedDifference_le {F : ℝ → ℝ} {l r p q E : ℝ}
    (hpr : |F (p - r)| ≤ E) (hpl : |F (p - l)| ≤ E)
    (hqr : |F (q - r)| ≤ E) (hql : |F (q - l)| ≤ E) :
    |intervalMixedDifference F l r p q| ≤ 4 * E := by
  have h1 := abs_sub (F (p - r)) (F (p - l))
  have h2 := abs_sub (F (p - r) - F (p - l)) (F (q - r))
  have h3 := abs_add_le (F (p - r) - F (p - l) - F (q - r)) (F (q - l))
  dsimp only [intervalMixedDifference]
  linarith only [h1, h2, h3, hpr, hpl, hqr, hql]

private theorem integrable_rawCell_mul_coarseProfile (k : ℕ) {b : ℕ}
    (hb : 1 ≤ b) (s : ℝ) :
    Integrable (fun u => rawCell k u * coarseProfile b (u + s)) :=
  (integrable_rawCell k).mul_bdd ((measurable_coarseProfile b).comp
    (measurable_add_const s)).aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact abs_coarseProfile_le hb (u + s))

/-- A raw logarithmic cell and a coarse pair have an exact four-hinge correlation. -/
theorem rawCell_coarseProfile_correlation_eq_hinges {k b : ℕ}
    (hk : 1 ≤ k) (hb : 1 ≤ b) (s : ℝ) :
    (∫ u, rawCell k u * coarseProfile b (u + s)) =
      intervalMixedDifference (fun z => max 0 (z - s))
        (Real.log k) (Real.log ((k + 1 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)) := by
  have hlr : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast Nat.le_succ k)
  have hpq : Real.log ((2 * b : ℕ) : ℝ) ≤ Real.log ((2 * b + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * b ≤ 2 * b + 2 by omega))
  simp_rw [rawCell, coarseProfile_eq_indicator hb]
  exact intervalCorrelation_eq_four_hinges hlr hpq s

private theorem sum_primeHinge_Icc_one_eq {t : ℝ} {N : ℕ}
    (hN : ⌊Real.exp t⌋₊ ≤ N) :
    (∑ n ∈ Icc 1 N, screwPrimeWeight n * max 0 (t - Real.log n)) = screwPrimeSum t := by
  rw [screwPrimeSum_eq_sum_max hN]
  symm
  apply sum_subset (Icc_subset_Icc_left (by norm_num : 1 ≤ (2 : ℕ)))
  intro n hn hnot
  have hn1 : n = 1 := by
    simp only [mem_Icc] at hn hnot
    omega
  subst n
  simp only [screwPrimeWeight, ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul]

private theorem primeHinge_corner_cutoff_le {Y b i j : ℕ}
    (hY : 1 ≤ Y) (hi : 2 ≤ i) (hj : 1 ≤ j) (hjb : j ≤ 2 * (b + 1)) :
    ⌊Real.exp (Real.log (Y : ℝ) + (Real.log j - Real.log i))⌋₊ ≤ (b + 1) * Y := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hratio : (j : ℝ) / i ≤ (b : ℝ) + 1 := by
    apply (div_le_iff₀ hi0).mpr
    have hjb' : (j : ℝ) ≤ 2 * ((b : ℝ) + 1) := by exact_mod_cast hjb
    have hi' : (2 : ℝ) ≤ i := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_left hi' (show (0 : ℝ) ≤ (b : ℝ) + 1 by positivity)
    nlinarith only [hjb', hm]
  have he : Real.exp (Real.log (Y : ℝ) + (Real.log j - Real.log i)) ≤
      (((b + 1) * Y : ℕ) : ℝ) := by
    rw [Real.exp_add, Real.exp_sub, Real.exp_log hY0, Real.exp_log hj0, Real.exp_log hi0]
    push_cast
    calc
      (Y : ℝ) * ((j : ℝ) / i) ≤ (Y : ℝ) * ((b : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hratio hY0.le
      _ = ((b : ℝ) + 1) * (Y : ℝ) := mul_comm _ _
  simpa only [Nat.floor_natCast] using Nat.floor_mono he


/-- The full prime coupling of a raw cell is exactly a mixed prime-hinge difference. -/
theorem fullPrimeWindowCoupling_rawCell_eq_hinges {Y k b : ℕ}
    (hY : 1 ≤ Y) (hk : 2 ≤ k) (hb : 1 ≤ b) :
    fullPrimeWindowCoupling (rawCell k) Y b =
      2 * intervalMixedDifference (fun z => screwPrimeSum (Real.log Y + z))
        (Real.log k) (Real.log ((k + 1 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)) := by
  let S := Icc 1 ((b + 1) * Y)
  let l := Real.log (k : ℝ)
  let r := Real.log ((k + 1 : ℕ) : ℝ)
  let p := Real.log ((2 * b : ℕ) : ℝ)
  let q := Real.log ((2 * b + 2 : ℕ) : ℝ)
  have heq : (fun u => rawCell k u * fullPrimeWindowTrace Y b u) =
      (fun u => ∑ m ∈ S, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        (rawCell k u * coarseProfile b (u + (Real.log m - Real.log Y)))) := by
    funext u
    rw [fullPrimeWindowTrace_eq hY, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hsource : fullPrimeWindowCoupling (rawCell k) Y b =
      ∑ m ∈ S, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        intervalMixedDifference (fun z => max 0 (z - (Real.log m - Real.log Y))) l r p q := by
    rw [fullPrimeWindowCoupling, heq,
      integral_finsetSum S (fun m _ =>
        (integrable_rawCell_mul_coarseProfile k hb (Real.log m - Real.log Y)).const_mul
          (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m))]
    apply sum_congr rfl
    intro m _
    rw [integral_const_mul, rawCell_coarseProfile_correlation_eq_hinges (by omega : 1 ≤ k) hb]
  have hlinear :
      (∑ m ∈ S, screwPrimeWeight m *
        intervalMixedDifference (fun z => max 0 (z - (Real.log m - Real.log Y))) l r p q) =
      intervalMixedDifference (fun z => ∑ m ∈ S,
        screwPrimeWeight m * max 0 (z - (Real.log m - Real.log Y))) l r p q := by
    simp only [intervalMixedDifference, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  have hhinge (z : ℝ) (m : ℕ) :
      max 0 (z - (Real.log m - Real.log (Y : ℝ))) =
        max 0 ((Real.log Y + z) - Real.log m) := by
    congr 1
    ring
  have hpr := sum_primeHinge_Icc_one_eq
    (primeHinge_corner_cutoff_le hY (by omega : 2 ≤ k + 1)
      (by omega : 1 ≤ 2 * b) (by omega : 2 * b ≤ 2 * (b + 1)))
  have hpl := sum_primeHinge_Icc_one_eq
    (primeHinge_corner_cutoff_le hY hk
      (by omega : 1 ≤ 2 * b) (by omega : 2 * b ≤ 2 * (b + 1)))
  have hqr := sum_primeHinge_Icc_one_eq
    (primeHinge_corner_cutoff_le hY (by omega : 2 ≤ k + 1)
      (by omega : 1 ≤ 2 * b + 2) (by omega : 2 * b + 2 ≤ 2 * (b + 1)))
  have hql := sum_primeHinge_Icc_one_eq
    (primeHinge_corner_cutoff_le hY hk
      (by omega : 1 ≤ 2 * b + 2) (by omega : 2 * b + 2 ≤ 2 * (b + 1)))
  calc
    fullPrimeWindowCoupling (rawCell k) Y b =
        2 * ∑ m ∈ S, screwPrimeWeight m *
          intervalMixedDifference (fun z => max 0 (z - (Real.log m - Real.log Y))) l r p q := by
      rw [hsource, mul_sum]
      apply sum_congr rfl
      intro m _
      rw [screwPrimeWeight]
      ring
    _ = _ := by
      rw [hlinear]
      simp_rw [intervalMixedDifference, hhinge]
      dsimp only [S, l, r, p, q]
      rw [hpr, hpl, hqr, hql]


private theorem integrable_profile_mul_fullPrimeWindowTrace {f : ℝ → ℝ}
    (hf : Integrable f) {Y b : ℕ} (hY : 1 ≤ Y) (hb : 1 ≤ b) :
    Integrable (fun u => f u * fullPrimeWindowTrace Y b u) := by
  have hNY : 1 ≤ (b + 1) * Y := by nlinarith only [hY, Nat.zero_le (b * Y)]
  have hbound : ∀ u : ℝ, |fullPrimeWindowTrace Y b u| ≤
      4 * RHTower.FreeLagTrace.chebyshevConst * Real.sqrt (((b + 1) * Y : ℕ) : ℝ) := by
    intro u
    obtain ⟨h0, h1⟩ := headTrace_nonneg_le hNY hb (u + Real.log ((b : ℝ) + 1))
    change |headTrace ((b + 1) * Y) b (u + Real.log ((b : ℝ) + 1))| ≤ _
    rw [abs_of_nonneg h0]
    exact h1
  exact hf.mul_bdd (((measurable_headTrace ((b + 1) * Y) b).comp
    (measurable_add_const (Real.log ((b : ℝ) + 1)))).aestronglyMeasurable)
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hbound u)

/-- The full prime trace preserves the exact two-cell decomposition of a Haar detail. -/
theorem fullPrimeWindowCoupling_haar_eq_raw_difference {Y b : ℕ}
    (hY : 1 ≤ Y) (hb : 1 ≤ b) (a : ℕ) :
    fullPrimeWindowCoupling (haarProfile a) Y b =
      haarLeftCoeff a * fullPrimeWindowCoupling (rawCell (2 * a)) Y b -
        haarRightCoeff a * fullPrimeWindowCoupling (rawCell (2 * a + 1)) Y b := by
  have hl := integrable_profile_mul_fullPrimeWindowTrace (integrable_rawCell (2 * a)) hY hb
  have hr := integrable_profile_mul_fullPrimeWindowTrace (integrable_rawCell (2 * a + 1)) hY hb
  have heq : (fun u => haarProfile a u * fullPrimeWindowTrace Y b u) =
      (fun u => haarLeftCoeff a * (rawCell (2 * a) u * fullPrimeWindowTrace Y b u) -
        haarRightCoeff a * (rawCell (2 * a + 1) u * fullPrimeWindowTrace Y b u)) := by
    funext u
    rw [haarProfile]
    ring
  simp only [fullPrimeWindowCoupling]
  rw [heq, integral_sub (hl.const_mul _) (hr.const_mul _),
    integral_const_mul, integral_const_mul]

/-- The complete Haar-window prime source is a balanced pair of four-hinge differences. -/
theorem fullPrimeWindowCoupling_haar_eq_hinges {Y a b : ℕ}
    (hY : 1 ≤ Y) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    fullPrimeWindowCoupling (haarProfile a) Y b =
      2 * (haarLeftCoeff a * intervalMixedDifference (fun z => screwPrimeSum (Real.log Y + z))
        (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 1 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)) -
      haarRightCoeff a * intervalMixedDifference (fun z => screwPrimeSum (Real.log Y + z))
        (Real.log ((2 * a + 1 : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ))) := by
  rw [fullPrimeWindowCoupling_haar_eq_raw_difference hY hb a,
    fullPrimeWindowCoupling_rawCell_eq_hinges hY (by omega : 2 ≤ 2 * a) hb,
    fullPrimeWindowCoupling_rawCell_eq_hinges hY (by omega : 2 ≤ 2 * a + 1) hb]
  ring

/-- The negative exponential moment of a detail is its balanced raw-cell moment. -/
theorem integral_haarProfile_exp_neg_half (a : ℕ) :
    (∫ u, haarProfile a u * Real.exp (-u / 2)) = haarExpMoment a := by
  have heq : (fun u => haarProfile a u * Real.exp (-u / 2)) =
      (fun u => haarLeftCoeff a * (rawCell (2 * a) u * Real.exp (-u / 2)) -
        haarRightCoeff a * (rawCell (2 * a + 1) u * Real.exp (-u / 2))) := by
    funext u
    rw [haarProfile]
    ring
  rw [heq, integral_sub ((integrable_rawCell_mul_exp _).const_mul _)
    ((integrable_rawCell_mul_exp _).const_mul _), integral_const_mul, integral_const_mul]
  rfl

/-- The exponential hinge main term is exactly the raw-cell polar product. -/
theorem intervalMixedDifference_prime_main {Y k b : ℕ}
    (hY : 1 ≤ Y) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    intervalMixedDifference (fun z => 4 * Real.exp ((Real.log Y + z) / 2))
      (Real.log k) (Real.log ((k + 1 : ℕ) : ℝ))
      (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)) =
      2 * Real.sqrt Y * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) * cellExpMass k := by
  have hs (F : ℝ → ℝ) (l r p q : ℝ) :
      intervalMixedDifference (fun z => 4 * F z) l r p q =
        4 * intervalMixedDifference F l r p q := by
    dsimp only [intervalMixedDifference]
    ring
  rw [hs, intervalMixedDifference_exp_half, exp_half_log_eq_sqrt hY,
    exp_half_log_eq_sqrt (by omega : 1 ≤ 2 * b + 2),
    exp_half_log_eq_sqrt (by omega : 1 ≤ 2 * b), cellExpMass_eq hk]
  push_cast
  ring

/-- Subtracting the first mixed pole leaves precisely the eight prime-hinge errors. -/
theorem fullPrimeWindowCoupling_haar_sub_main_eq {Y a b : ℕ}
    (hY : 1 ≤ Y) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    fullPrimeWindowCoupling (haarProfile a) Y b -
      4 * Real.sqrt Y * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) *
        (∫ u, haarProfile a u * Real.exp (-u / 2)) =
      2 * (haarLeftCoeff a * intervalMixedDifference
        (fun z => screwPrimeSum (Real.log Y + z) - 4 * Real.exp ((Real.log Y + z) / 2))
        (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 1 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)) -
      haarRightCoeff a * intervalMixedDifference
        (fun z => screwPrimeSum (Real.log Y + z) - 4 * Real.exp ((Real.log Y + z) / 2))
        (Real.log ((2 * a + 1 : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ))) := by
  have hs (k : ℕ) (hk : 1 ≤ k) :
      intervalMixedDifference (fun z => screwPrimeSum (Real.log Y + z))
        (Real.log k) (Real.log ((k + 1 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)) =
      intervalMixedDifference
        (fun z => screwPrimeSum (Real.log Y + z) - 4 * Real.exp ((Real.log Y + z) / 2))
        (Real.log k) (Real.log ((k + 1 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)) +
      2 * Real.sqrt Y * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) * cellExpMass k := by
    rw [← intervalMixedDifference_prime_main hY hk hb]
    dsimp only [intervalMixedDifference]
    ring
  rw [fullPrimeWindowCoupling_haar_eq_hinges hY ha hb,
    integral_haarProfile_exp_neg_half, haarExpMoment,
    hs (2 * a) (by omega),
    show 2 * a + 2 = (2 * a + 1) + 1 by omega,
    hs (2 * a + 1) (by omega)]
  ring

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.intervalCorrelation_eq_four_hinges

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.rawCell_coarseProfile_correlation_eq_hinges

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.intervalMixedDifference_exp_half
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_intervalMixedDifference_le

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.fullPrimeWindowCoupling_rawCell_eq_hinges

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.fullPrimeWindowCoupling_haar_eq_raw_difference
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.fullPrimeWindowCoupling_haar_eq_hinges
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integral_haarProfile_exp_neg_half
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.intervalMixedDifference_prime_main
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.fullPrimeWindowCoupling_haar_sub_main_eq
