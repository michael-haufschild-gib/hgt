import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellPrimeCompression
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SmoothCompleteWeilTransfer
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellRealization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompletePrimeSourceTransfer

/-!
# Literal balanced logarithmic profiles

Balanced cell vectors have compact, bounded-variation representatives with
exact zero mean. Their full prime energy and square mass agree with the
corresponding integrals on the original real source space.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry HTGeometry

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-- The literal jump-one balanced profile on two complete adjacent cells. -/
def haarProfile (a : ℕ) (x : ℝ) : ℝ :=
  haarLeftCoeff a * rawCell (2 * a) x - haarRightCoeff a * rawCell (2 * a + 1) x

def haarSectionProfile (c : ℕ → ℝ) (X : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, c a * haarProfile a x

theorem measurable_haarProfile (a : ℕ) : Measurable (haarProfile a) :=
  (measurable_const.mul (measurable_rawCell _)).sub
    (measurable_const.mul (measurable_rawCell _))

theorem measurable_haarSectionProfile (c : ℕ → ℝ) (X : ℕ) :
    Measurable (haarSectionProfile c X) :=
  Finset.measurable_sum _ fun a _ => measurable_const.mul (measurable_haarProfile a)

theorem integrable_rawCell (a : ℕ) : Integrable (rawCell a) := by
  simpa only [mul_one] using
    integrable_compact_bv_mul (rawCell_bv a) (rawCell_compact a)
      (show Continuous (fun _ : ℝ => (1 : ℝ)) from continuous_const)

theorem integral_rawCell {a : ℕ} (ha : 1 ≤ a) : ∫ x, rawCell a x = logCellWidth a := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hlo : Real.log (a : ℝ) ≤ Real.log ((a + 1 : ℕ) : ℝ) :=
    Real.log_le_log ha0 (by exact_mod_cast Nat.le_succ a)
  rw [rawCell, integral_indicator_const 1 measurableSet_Ico, Real.volume_real_Ico_of_le hlo]
  simp only [smul_eq_mul, mul_one, logCellWidth, Nat.cast_add, Nat.cast_one]

theorem haarProfile_bv (a : ℕ) : BoundedVariationOn (haarProfile a) univ :=
  boundedVariationOn_sub (bv_const_mul _ (rawCell_bv _)) (bv_const_mul _ (rawCell_bv _))

theorem haarProfile_compact (a : ℕ) : HasCompactSupport (haarProfile a) := by
  have hl : HasCompactSupport (fun x => haarLeftCoeff a * rawCell (2 * a) x) :=
    (rawCell_compact _).mul_left
  have hr : HasCompactSupport (fun x => haarRightCoeff a * rawCell (2 * a + 1) x) :=
    (rawCell_compact _).mul_left
  exact hl.sub hr

theorem integrable_haarProfile (a : ℕ) : Integrable (haarProfile a) :=
  ((integrable_rawCell _).const_mul _).sub ((integrable_rawCell _).const_mul _)

/-- Balance is exact in the physical source integral. -/
theorem integral_haarProfile {a : ℕ} (ha : 1 ≤ a) : ∫ x, haarProfile a x = 0 := by
  unfold haarProfile
  rw [integral_sub ((integrable_rawCell _).const_mul _)
    ((integrable_rawCell _).const_mul _), integral_const_mul, integral_const_mul,
    integral_rawCell (show 1 ≤ 2 * a by omega),
    integral_rawCell (show 1 ≤ 2 * a + 1 by omega),
    (haarCoeff_mass a).1, (haarCoeff_mass a).2, sub_self]

private theorem rawCell_zero_neg (a : ℕ) {x : ℝ} (hx : x < 0) : rawCell a x = 0 := by
  by_cases ha : a = 0
  · subst a
    simp only [rawCell, Nat.cast_zero, zero_add, Nat.cast_one, Real.log_zero,
      Real.log_one, Ico_self, indicator_empty]
  · apply indicator_of_notMem
    intro hmem
    have hlo : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha)
    exact (not_lt_of_ge (hlo.trans hmem.1)) hx

theorem haarSectionProfile_zero_neg (c : ℕ → ℝ) (X : ℕ) {x : ℝ} (hx : x < 0) :
    haarSectionProfile c X x = 0 := by
  unfold haarSectionProfile
  apply Finset.sum_eq_zero
  intro a _ha
  simp only [haarProfile, rawCell_zero_neg _ hx, mul_zero, sub_zero]

theorem integrable_haarSectionProfile (c : ℕ → ℝ) (X : ℕ) :
    Integrable (haarSectionProfile c X) :=
  integrable_finsetSum _ fun a _ => (integrable_haarProfile a).const_mul (c a)

theorem integral_haarSectionProfile (c : ℕ → ℝ) (X : ℕ) :
    ∫ x, haarSectionProfile c X x = 0 := by
  unfold haarSectionProfile
  rw [integral_finsetSum _
    (fun a _ => (integrable_haarProfile a).const_mul (c a))]
  apply Finset.sum_eq_zero
  intro a ha
  rw [integral_const_mul, integral_haarProfile (Finset.mem_Icc.mp ha).1, mul_zero]

theorem haarSectionProfile_bv (c : ℕ → ℝ) (X : ℕ) :
    BoundedVariationOn (haarSectionProfile c X) univ := by
  have hsum (s : Finset ℕ) :
      BoundedVariationOn (fun x => ∑ a ∈ s, c a * haarProfile a x) univ := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        ((monotone_const : Monotone (fun _ : ℝ => (0 : ℝ))).monotoneOn univ).boundedVariationOn
          (C := 0) (fun x _ => by simp)
    | @insert a s ha ih =>
      have h := boundedVariationOn_sub (bv_const_mul (c a) (haarProfile_bv a))
        (bv_const_mul (-1) ih)
      simpa only [Finset.sum_insert ha, neg_one_mul, sub_neg_eq_add] using h
  exact hsum _

theorem haarSectionProfile_eq_zero_outside (c : ℕ → ℝ) (X : ℕ) {x : ℝ}
    (hx : x ∉ Icc (0 : ℝ) (Real.log ((2 * X + 2 : ℕ) : ℝ))) :
    haarSectionProfile c X x = 0 := by
  have hraw (n : ℕ) (hn : 1 ≤ n) (hnX : n ≤ 2 * X + 1) : rawCell n x = 0 := by
    apply indicator_of_notMem
    intro hi
    have hlo : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hhi : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log ((2 * X + 2 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show n + 1 ≤ 2 * X + 2 by omega))
    exact hx ⟨hlo.trans hi.1, hi.2.le.trans hhi⟩
  unfold haarSectionProfile
  apply Finset.sum_eq_zero
  intro a ha
  have ha1 := (Finset.mem_Icc.mp ha).1
  have haX := (Finset.mem_Icc.mp ha).2
  simp only [haarProfile, hraw (2 * a) (by omega) (by omega),
    hraw (2 * a + 1) (by omega) (by omega), mul_zero, sub_zero]

theorem haarSectionProfile_compact (c : ℕ → ℝ) (X : ℕ) :
    HasCompactSupport (haarSectionProfile c X) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => haarSectionProfile_eq_zero_outside c X hx)

theorem memLp_haarSectionProfile (c : ℕ → ℝ) (X : ℕ) :
    MemLp (haarSectionProfile c X) 2 volume :=
  memLp_compact_bv (haarSectionProfile_bv c X) (haarSectionProfile_compact c X)

theorem haarSectionProfile_supported (c : ℕ → ℝ) (X : ℕ) :
    SpacingScaleHarmonicAnalysis.SupportedIn (Real.log ((2 * X + 2 : ℕ) : ℝ)) (haarSectionProfile c X) := by
  intro x hx
  apply haarSectionProfile_eq_zero_outside c X
  intro hi
  rw [abs_of_nonneg hi.1] at hx
  exact (not_lt_of_ge hi.2) hx

private theorem cellAtom_coeFn_rawCell (a : ℕ) :
    (cellAtom a : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => (rawCell a x : ℂ) := by
  refine (cellAtom_coeFn a).trans (Eventually.of_forall ?_)
  intro x
  simp only [rawCell, indicator_apply]
  split_ifs <;> rfl

theorem haarAtom_coeFn (a : ℕ) :
    (haarAtom a : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => (haarProfile a x : ℂ) := by
  unfold haarAtom
  filter_upwards [Lp.coeFn_sub ((haarLeftCoeff a : ℂ) • cellAtom (2 * a))
      ((haarRightCoeff a : ℂ) • cellAtom (2 * a + 1)),
    Lp.coeFn_smul (haarLeftCoeff a : ℂ) (cellAtom (2 * a)),
    Lp.coeFn_smul (haarRightCoeff a : ℂ) (cellAtom (2 * a + 1)),
    cellAtom_coeFn_rawCell (2 * a), cellAtom_coeFn_rawCell (2 * a + 1)]
      with x hsub hl hr hal har
  rw [hsub]
  simp only [Pi.sub_apply, hl, hr, Pi.smul_apply, smul_eq_mul, hal, har,
    haarProfile, Complex.ofReal_sub, Complex.ofReal_mul]

theorem haarSection_coeFn (c : ℕ → ℝ) (X : ℕ) :
    (haarSection c X : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (haarSectionProfile c X x : ℂ) := by
  have hs := coeFn_finset_sum_smul (Finset.Icc 1 X) (fun a => (c a : ℂ)) haarAtom
  have ha : ∀ᵐ x ∂halfLineMeasure, ∀ a : ℕ,
      (haarAtom a : ℝ → ℂ) x = (haarProfile a x : ℂ) := ae_all_iff.mpr haarAtom_coeFn
  unfold haarSection
  filter_upwards [hs, ha] with x hx ha
  rw [hx, haarSectionProfile, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [ha a, Complex.ofReal_mul]

theorem halfLineExtend_haarSectionProfile (c : ℕ → ℝ) (X : ℕ) :
    (halfLineExtend (haarSection c X) : ℝ → ℂ) =ᵐ[volume]
      fun x => (haarSectionProfile c X x : ℂ) := by
  refine (halfLineExtend_coeFn _).trans
    ((indicator_ae_eq_of_halfLine (haarSection_coeFn c X)).trans ?_)
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ Ici (0 : ℝ)
  · exact indicator_of_mem hx _
  · simp only [indicator_of_notMem hx,
      haarSectionProfile_zero_neg c X (lt_of_not_ge hx), Complex.ofReal_zero]

/-- Actual Hilbert translations are exactly the correlations of the physical profiles. -/
theorem inner_shift_haarSectionProfile (c : ℕ → ℝ) (X : ℕ) (t : ℝ) :
    (inner ℂ (halfLineRightShift t (haarSection c X)) (haarSection c X)).re =
      ∫ x, haarSectionProfile c X x * haarSectionProfile c X (x + t) := by
  let u := haarSection c X
  have hu := haarSection_coeFn c X
  have he := halfLineExtend_haarSectionProfile c X
  have ht : ∀ᵐ x ∂halfLineMeasure,
      (halfLineExtend (haarSection c X) : ℝ → ℂ) (x - t) =
        (haarSectionProfile c X (x - t) : ℂ) :=
    ae_restrict_of_ae ((measurePreserving_sub_right volume t).quasiMeasurePreserving.ae he)
  have hinner : Integrable (fun x =>
      inner ℂ ((halfLineRightShift t u : ℝ → ℂ) x) (u x)) halfLineMeasure :=
    L2.integrable_inner (halfLineRightShift t u) u
  have hre := integral_re hinner
  simp only [RCLike.re_to_complex] at hre
  rw [L2.inner_def, ← hre]
  have hi : (∫ x, (inner ℂ ((halfLineRightShift t u : ℝ → ℂ) x) (u x)).re ∂halfLineMeasure) =
      ∫ x, haarSectionProfile c X (x - t) * haarSectionProfile c X x ∂halfLineMeasure := by
    apply integral_congr_ae
    filter_upwards [halfLineRightShift_coeFn t u, hu, ht] with x hshift hx hxt
    rw [hshift, hx, hxt, RCLike.inner_apply]
    simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]
  rw [hi]
  have hall : (∫ x, haarSectionProfile c X (x - t) * haarSectionProfile c X x ∂halfLineMeasure) =
      ∫ x, haarSectionProfile c X (x - t) * haarSectionProfile c X x := by
    rw [halfLineMeasure, ← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ici (0 : ℝ)
    · exact indicator_of_mem hx _
    · simp only [indicator_of_notMem hx, haarSectionProfile_zero_neg c X (lt_of_not_ge hx), mul_zero]
  rw [hall]
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun x => haarSectionProfile c X x * haarSectionProfile c X (x + t)) t
  simpa only [sub_add_cancel] using h

theorem haarPrimeEnergy_eq_primeSum (c : ℕ → ℝ) (X : ℕ) :
    haarPrimeEnergy c X = primeSum (haarSectionProfile c X) := by
  rw [← smoothPrimePair_self_eq_primeSum]
  unfold haarPrimeEnergy smoothPrimePair
  apply tsum_congr
  intro m
  rw [inner_shift_haarSectionProfile]

private theorem halfLineRightShift_zero_apply (u : L²₊) : halfLineRightShift 0 u = u := by
  apply Lp.ext
  have he : (halfLineExtend u : ℝ → ℂ) =ᵐ[halfLineMeasure]
      (Ici (0 : ℝ)).indicator (fun x => u x) := ae_restrict_of_ae (halfLineExtend_coeFn u)
  filter_upwards [halfLineRightShift_coeFn 0 u, he,
    (ae_restrict_mem measurableSet_Ici : ∀ᵐ x ∂halfLineMeasure, x ∈ Ici (0 : ℝ))]
      with x hx he hx0
  rw [hx, sub_zero, he, indicator_of_mem hx0]

/-- Square mass is the same on the physical profile and the actual Hilbert section. -/
theorem integral_haarSectionProfile_sq (c : ℕ → ℝ) (X : ℕ) :
    ∫ x, haarSectionProfile c X x ^ 2 =
      ∑ a ∈ Finset.Icc 1 X, haarMass a * c a ^ 2 := by
  have h := inner_shift_haarSectionProfile c X 0
  simp only [halfLineRightShift_zero_apply, add_zero, ← pow_two,
    re_inner_haarSection_self] at h
  exact h.symm


/-- The balanced profile vanishes outside its two complete cells. -/
theorem haarProfile_zero_outside_pair {a : ℕ} (ha : 1 ≤ a) {x : ℝ}
    (hx : x ∉ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
    haarProfile a x = 0 := by
  have hlo : Real.log ((2 * a : ℕ) : ℝ) ≤ Real.log ((2 * a + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a ≤ 2 * a + 1 by omega))
  have hhi : Real.log ((2 * a + 1 : ℕ) : ℝ) ≤ Real.log ((2 * a + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 1 ≤ 2 * a + 2 by omega))
  have hl : x ∉ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 1 : ℕ) : ℝ)) :=
    fun h => hx ⟨h.1, h.2.trans_le hhi⟩
  have hr : x ∉ Ico (Real.log ((2 * a + 1 : ℕ) : ℝ))
      (Real.log ((2 * a + 1 + 1 : ℕ) : ℝ)) := by
    intro h
    apply hx
    exact ⟨hlo.trans h.1, by simpa only [Nat.add_assoc] using h.2⟩
  simp only [haarProfile, rawCell, indicator_of_notMem hl, indicator_of_notMem hr,
    mul_zero, sub_zero]

private theorem haarProfile_zero_on_other {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hba : b ≠ a) {x : ℝ}
    (hx : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
    haarProfile b x = 0 := by
  apply haarProfile_zero_outside_pair hb
  intro hxB
  rcases lt_or_gt_of_ne hba with hlt | hgt
  · have he : Real.log ((2 * b + 2 : ℕ) : ℝ) ≤ Real.log ((2 * a : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * b + 2 ≤ 2 * a by omega))
    linarith only [hx.1, hxB.2, he]
  · have he : Real.log ((2 * a + 2 : ℕ) : ℝ) ≤ Real.log ((2 * b : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 2 ≤ 2 * b by omega))
    linarith only [hx.2, hxB.1, he]

/-- On one open pair interval, only its own source coefficient remains. -/
theorem haarSectionProfile_on_pair (c : ℕ → ℝ) {X a : ℕ} (ha : 1 ≤ a) (haX : a ≤ X)
    {x : ℝ} (hx : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
    haarSectionProfile c X x = c a * haarProfile a x := by
  classical
  unfold haarSectionProfile
  apply Finset.sum_eq_single a
  · intro b hb hba
    rw [haarProfile_zero_on_other ha (Finset.mem_Icc.mp hb).1 hba hx, mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_Icc.mpr ⟨ha, haX⟩))

private theorem indicator_open_pair_haarProfile {a : ℕ} (ha : 1 ≤ a) :
    (Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))).indicator
      (haarProfile a) =ᵐ[volume] haarProfile a := by
  filter_upwards [Measure.ae_ne volume (Real.log ((2 * a : ℕ) : ℝ))] with x hx
  by_cases hm : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
  · exact indicator_of_mem hm _
  · rw [indicator_of_notMem hm]
    symm
    apply haarProfile_zero_outside_pair ha
    intro hi
    apply hm
    refine ⟨?_, hi.2⟩
    rcases lt_or_eq_of_le hi.1 with hl | he
    · exact hl
    · exact False.elim (hx he.symm)

theorem setIntegral_haarProfile_pair {a : ℕ} (ha : 1 ≤ a) :
    ∫ x in Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
      haarProfile a x = 0 := by
  rw [← integral_indicator measurableSet_Ioo,
    integral_congr_ae (indicator_open_pair_haarProfile ha), integral_haarProfile ha]

private theorem haarProfile_sq (a : ℕ) (x : ℝ) :
    haarProfile a x ^ 2 = haarLeftCoeff a ^ 2 * rawCell (2 * a) x +
      haarRightCoeff a ^ 2 * rawCell (2 * a + 1) x := by
  unfold haarProfile rawCell
  simp only [indicator_apply]
  split_ifs with hl hr hr
  · exact False.elim ((not_lt_of_ge hr.1) hl.2)
  all_goals ring

theorem integral_haarProfile_sq {a : ℕ} (ha : 1 ≤ a) :
    ∫ x, haarProfile a x ^ 2 = haarMass a := by
  simp_rw [haarProfile_sq]
  rw [integral_add ((integrable_rawCell _).const_mul _) ((integrable_rawCell _).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_rawCell (show 1 ≤ 2 * a by omega),
    integral_rawCell (show 1 ≤ 2 * a + 1 by omega)]
  have hl := (haarCoeff_mass a).1
  have hr := (haarCoeff_mass a).2
  have hs := haarCoeff_sum ha
  linear_combination haarLeftCoeff a * hl + haarRightCoeff a * hr + haarMass a * hs

theorem setIntegral_haarProfile_pair_sq {a : ℕ} (ha : 1 ≤ a) :
    ∫ x in Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
      haarProfile a x ^ 2 = haarMass a := by
  rw [← integral_indicator measurableSet_Ioo]
  have he : (Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))).indicator
      (fun x => haarProfile a x ^ 2) =ᵐ[volume] fun x => haarProfile a x ^ 2 := by
    filter_upwards [indicator_open_pair_haarProfile ha] with x hx
    by_cases hm : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
    · exact indicator_of_mem hm _
    · have hz : haarProfile a x = 0 := by
        simpa only [indicator_of_notMem hm] using hx.symm
      simp only [indicator_of_notMem hm, hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [integral_congr_ae he, integral_haarProfile_sq ha]

/-- Each actual source pair has zero mean, independently of every other signed coefficient. -/
theorem setIntegral_haarSectionProfile_pair (c : ℕ → ℝ) {X a : ℕ} (ha : 1 ≤ a) (haX : a ≤ X) :
    ∫ x in Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
      haarSectionProfile c X x = 0 := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => haarSectionProfile_on_pair c ha haX hx),
    integral_const_mul, setIntegral_haarProfile_pair ha, mul_zero]

theorem setIntegral_haarSectionProfile_pair_sq (c : ℕ → ℝ) {X a : ℕ} (ha : 1 ≤ a) (haX : a ≤ X) :
    ∫ x in Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
      haarSectionProfile c X x ^ 2 = haarMass a * c a ^ 2 := by
  have he : ∀ x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
      haarSectionProfile c X x ^ 2 = c a ^ 2 * haarProfile a x ^ 2 := by
    intro x hx
    rw [haarSectionProfile_on_pair c ha haX hx, mul_pow]
  rw [setIntegral_congr_fun measurableSet_Ioo he, integral_const_mul,
    setIntegral_haarProfile_pair_sq ha, mul_comm]

#print axioms setIntegral_haarSectionProfile_pair
#print axioms setIntegral_haarSectionProfile_pair_sq

#print axioms integral_haarProfile
#print axioms haarPrimeEnergy_eq_primeSum
#print axioms integral_haarSectionProfile_sq

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
