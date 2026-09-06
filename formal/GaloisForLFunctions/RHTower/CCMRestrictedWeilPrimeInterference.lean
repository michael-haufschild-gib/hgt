import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeOuterShell
import GaloisForLFunctions.HTGeometry.NilpotentContractionInterference
import Mathlib.NumberTheory.Bertrand

/-!
# Distinct-prime interference on the actual aperture

For outer lags `a < h < k`, the product of the two actual symmetric translations
shrinks support by `k-h` on every iterate. It is nilpotent when the accumulated drift
crosses the overlap width `2a-h`. The resulting quantitative interference bound applies
to the literal von Mangoldt pair and makes the full separate-atom source budget strict
whenever two positive outer atoms occur. Bertrand supplies such a pair for every
`a >= log 5`.

A nonzero pole-constrained vector can nevertheless preserve both individual norms.
The strict joint gain therefore measures incompatible output directions. It does not
establish the sign of the complete prime-Gamma Weil form.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct
noncomputable section
namespace RHTower

private theorem aperture_zero_outside (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    ∀ᵐ x, x ∉ centralInterval a.1 → f.1 x = 0 := by
  have hc := indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hc
  filter_upwards [hc] with x hx hn
  rw [hx, indicator_of_notMem hn]

/-- The product of two distinct outer shifts drifts each endpoint piece by their lag difference. -/
theorem ccmOuterShiftProduct_coeFn (a : SuzukiPositiveAperture)
    {h k : ℝ} (hh : a.1 < h) (hk : a.1 < k) (f : suzukiApertureHilbert a) :
    (((ccmApertureCompression a (ccmSymmetricLogTranslation h) *
      ccmApertureCompression a (ccmSymmetricLogTranslation k)) f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Icc (-a.1) (a.1-h)).indicator (fun y => f.1 (y-(k-h))) x +
        (Icc (-a.1+h) a.1).indicator (fun y => f.1 (y+(k-h))) x := by
  let B := ccmApertureCompression a (ccmSymmetricLogTranslation k)
  have hb := ccmApertureSymmetricTranslation_coeFn a k f
  have hbp := hb.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have hbm := hb.comp_tendsto
    (MellinL2.realTranslation_measurePreserving (-h)).quasiMeasurePreserving.tendsto_ae
  have hz := aperture_zero_outside a f
  have hzp := (MellinL2.realTranslation_measurePreserving (h+k)).quasiMeasurePreserving.tendsto_ae.eventually hz
  have hzm := (MellinL2.realTranslation_measurePreserving (-(h+k))).quasiMeasurePreserving.tendsto_ae.eventually hz
  filter_upwards [ccmApertureSymmetricTranslation_coeFn a h (B f),
    hbp, hbm, hzp, hzm] with x hc hp hm hzp hzm
  change (ccmApertureCompression a (ccmSymmetricLogTranslation h) (B f) : SoninL2) x = _
  change (B f : SoninL2) (x+h) = (centralInterval a.1).indicator
    (fun y => f.1 (y+k)+f.1 (y-k)) (x+h) at hp
  change (B f : SoninL2) (x+ -h) = (centralInterval a.1).indicator
    (fun y => f.1 (y+k)+f.1 (y-k)) (x+ -h) at hm
  rw [hc]
  have hpos : 0 < h := lt_trans a.property hh
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx]
    change -a.1 ≤ x ∧ x ≤ a.1 at hx
    have hleft : x+h ∈ centralInterval a.1 ↔ x ∈ Icc (-a.1) (a.1-h) := by
      change (-a.1 ≤ x+h ∧ x+h ≤ a.1) ↔ (-a.1 ≤ x ∧ x ≤ a.1-h)
      constructor <;> intro hc <;> constructor <;> linarith [hc.1, hc.2]
    have hright : x+ -h ∈ centralInterval a.1 ↔ x ∈ Icc (-a.1+h) a.1 := by
      change (-a.1 ≤ x+ -h ∧ x+ -h ≤ a.1) ↔ (-a.1+h ≤ x ∧ x ≤ a.1)
      constructor <;> intro hc <;> constructor <;> linarith [hc.1, hc.2]
    have hzp' : f.1 (x+(h+k)) = 0 := hzp (by
      change ¬ (-a.1 ≤ x+(h+k) ∧ x+(h+k) ≤ a.1)
      intro hn; linarith [hn.2])
    have hzm' : f.1 (x+ -(h+k)) = 0 := hzm (by
      change ¬ (-a.1 ≤ x+ -(h+k) ∧ x+ -(h+k) ≤ a.1)
      intro hn; linarith [hn.1])
    rw [hp, show x-h=x+ -h by ring, hm]
    by_cases hl : x ∈ Icc (-a.1) (a.1-h) <;>
      by_cases hr : x ∈ Icc (-a.1+h) a.1
    · exfalso; linarith [hl.2, hr.1]
    · rw [indicator_of_mem (hleft.mpr hl), indicator_of_notMem (by simpa [hr] using hright),
        indicator_of_mem hl, indicator_of_notMem hr]
      simp only [show x+h+k=x+(h+k) by ring, show x+h-k=x-(k-h) by ring,
        hzp', zero_add, add_zero]
    · rw [indicator_of_notMem (by simpa [hl] using hleft), indicator_of_mem (hright.mpr hr),
        indicator_of_notMem hl, indicator_of_mem hr]
      simp only [show x+ -h-k=x+ -(h+k) by ring, show x+ -h+k=x+(k-h) by ring,
        hzm', zero_add, add_zero]
    · rw [indicator_of_notMem (by simpa [hl] using hleft),
        indicator_of_notMem (by simpa [hr] using hright),
        indicator_of_notMem hl, indicator_of_notMem hr]
  · have hl : x ∉ Icc (-a.1) (a.1-h) := by
      intro hl; apply hx
      change -a.1 ≤ x ∧ x ≤ a.1
      constructor <;> linarith [hl.1, hl.2]
    have hr : x ∉ Icc (-a.1+h) a.1 := by
      intro hr; apply hx
      change -a.1 ≤ x ∧ x ≤ a.1
      constructor <;> linarith [hr.1, hr.2]
    rw [indicator_of_notMem hx, indicator_of_notMem hl, indicator_of_notMem hr, zero_add]

/-- Every product iterate loses one lag difference from its support radius. -/
theorem ccmOuterShiftProduct_pow_shrinking_support (a : SuzukiPositiveAperture)
    {h k : ℝ} (hh : a.1 < h) (hk : a.1 < k) (horder : h < k)
    (f : suzukiApertureHilbert a) (N : ℕ) :
    ∀ᵐ x, a.1-(N : ℝ)*(k-h) < |x| →
      ((((ccmApertureCompression a (ccmSymmetricLogTranslation h) *
        ccmApertureCompression a (ccmSymmetricLogTranslation k))^N) f : SoninL2) : ℝ → ℂ) x = 0 := by
  let C := ccmApertureCompression a (ccmSymmetricLogTranslation h) *
    ccmApertureCompression a (ccmSymmetricLogTranslation k)
  change ∀ᵐ x, a.1-(N : ℝ)*(k-h) < |x| → ((C^N) f : SoninL2) x = 0
  induction N with
  | zero =>
    have hz := aperture_zero_outside a f
    filter_upwards [hz] with x hx hbound
    simp only [pow_zero, one_apply_eq_self]
    apply hx
    intro hmem
    have habs : |x| ≤ a.1 := abs_le.mpr hmem
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hbound
    linarith
  | succ n ih =>
    have hp := (MellinL2.realTranslation_measurePreserving (k-h)).quasiMeasurePreserving.tendsto_ae.eventually ih
    have hm := (MellinL2.realTranslation_measurePreserving (-(k-h))).quasiMeasurePreserving.tendsto_ae.eventually ih
    filter_upwards [ccmOuterShiftProduct_coeFn a hh hk ((C^n) f), hp, hm]
      with x hc hp hm hbound
    rw [pow_succ', mul_apply_eq_comp]
    rw [hc]
    by_cases hl : x ∈ Icc (-a.1) (a.1-h)
    · have hr : x ∉ Icc (-a.1+h) a.1 := by
        intro hr; linarith [hl.2, hr.1]
      rw [indicator_of_mem hl, indicator_of_notMem hr, add_zero]
      have hxneg : x < 0 := by linarith [hl.2]
      have hyneg : x-(k-h) < 0 := by linarith
      have hb : a.1-(n : ℝ)*(k-h) < |x-(k-h)| := by
        rw [abs_of_neg hxneg] at hbound
        rw [abs_of_neg hyneg]
        push_cast at hbound
        nlinarith
      change a.1-(n : ℝ)*(k-h) < |x+ -(k-h)| →
        ((C^n) f : SoninL2) (x+ -(k-h)) = 0 at hm
      simpa only [sub_eq_add_neg] using hm (by simpa only [sub_eq_add_neg] using hb)
    · by_cases hr : x ∈ Icc (-a.1+h) a.1
      · rw [indicator_of_notMem hl, indicator_of_mem hr, zero_add]
        have hxpos : 0 < x := by linarith [hr.1]
        have hypos : 0 < x+(k-h) := by linarith
        have hb : a.1-(n : ℝ)*(k-h) < |x+(k-h)| := by
          rw [abs_of_pos hxpos] at hbound
          rw [abs_of_pos hypos]
          push_cast at hbound
          nlinarith
        exact hp hb
      · rw [indicator_of_notMem hl, indicator_of_notMem hr, zero_add]

/-- Crossing the endpoint-overlap width makes the actual product exactly nilpotent. -/
theorem ccmOuterShiftProduct_pow_eq_zero (a : SuzukiPositiveAperture)
    {h k : ℝ} (hh : a.1 < h) (hk : a.1 < k) (horder : h < k)
    (N : ℕ) (hN : 0 < N) (hwidth : 2*a.1-h < (N : ℝ)*(k-h)) :
    (ccmApertureCompression a (ccmSymmetricLogTranslation h) *
      ccmApertureCompression a (ccmSymmetricLogTranslation k))^N = 0 := by
  let C := ccmApertureCompression a (ccmSymmetricLogTranslation h) *
    ccmApertureCompression a (ccmSymmetricLogTranslation k)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [ccmOuterShiftProduct_pow_shrinking_support a hh hk horder f (n+1),
    ccmOuterShiftProduct_coeFn a hh hk ((C^n) f),
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with x hs hc hz
  change ((C^(n+1)) f : SoninL2) x = (0 : SoninL2) x
  rw [hz]
  change ((C^(n+1)) f : SoninL2) x = 0
  by_cases hl : x ∈ Icc (-a.1) (a.1-h)
  · apply hs
    have hxneg : x < 0 := by linarith [hl.2]
    rw [abs_of_neg hxneg]
    linarith [hl.2]
  · by_cases hr : x ∈ Icc (-a.1+h) a.1
    · apply hs
      have hxpos : 0 < x := by linarith [hr.1]
      rw [abs_of_pos hxpos]
      linarith [hr.1]
    · rw [pow_succ', mul_apply_eq_comp, hc,
        indicator_of_notMem hl, indicator_of_notMem hr, zero_add]


/-- Quantitative interference for the actual outer-prime aperture operators. -/
theorem ccmOuterShiftPair_opNorm_sq_bound (a : SuzukiPositiveAperture)
    {h k : ℝ} (hh : a.1 < h) (horder : h < k)
    (N : ℕ) (hN : 0 < N) (hwidth : 2*a.1-h < (N : ℝ)*(k-h))
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (N : ℝ)^2 * ‖(u : ℂ) • ccmApertureCompression a (ccmSymmetricLogTranslation h) +
      (v : ℂ) • ccmApertureCompression a (ccmSymmetricLogTranslation k)‖^2 ≤
        (N : ℝ)^2*(u+v)^2-u*v :=
  HTGeometry.selfAdjoint_pair_opNorm_sq_bound_of_nilpotent_product _ _
    (ccmApertureCompression_isSelfAdjoint a (ccmSymmetricLogTranslation_isSelfAdjoint h)).isSymmetric
    (norm_ccmApertureSymmetricTranslation_le_one a hh)
    (norm_ccmApertureSymmetricTranslation_le_one a (lt_trans hh horder)) N hN
    (ccmOuterShiftProduct_pow_eq_zero a hh (lt_trans hh horder) horder N hN hwidth) u v hu hv

/-- Distinct outer shifts have strict norm subadditivity for every pair of positive weights. -/
theorem ccmOuterShiftPair_norm_lt_sum (a : SuzukiPositiveAperture)
    {h k : ℝ} (hh : a.1 < h) (horder : h < k)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    ‖(u : ℂ) • ccmApertureCompression a (ccmSymmetricLogTranslation h) +
      (v : ℂ) • ccmApertureCompression a (ccmSymmetricLogTranslation k)‖ < u+v := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((2*a.1-h)/(k-h))
  have hM : (2*a.1-h)/(k-h) < ((N+1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hwidth : 2*a.1-h < ((N+1 : ℕ) : ℝ)*(k-h) :=
    (div_lt_iff₀ (sub_pos.mpr horder)).mp hM
  exact HTGeometry.selfAdjoint_pair_norm_lt_sum_of_nilpotent_product _ _
    (ccmApertureCompression_isSelfAdjoint a (ccmSymmetricLogTranslation_isSelfAdjoint h)).isSymmetric
    (norm_ccmApertureSymmetricTranslation_le_one a hh)
    (norm_ccmApertureSymmetricTranslation_le_one a (lt_trans hh horder)) (N+1) (by omega)
    (ccmOuterShiftProduct_pow_eq_zero a hh (lt_trans hh horder) horder (N+1) (by omega) hwidth)
    u v hu hv

/-- Literal arithmetic scalar normalization of one prime transport. -/
theorem ccmWeightedPrimeTransport_eq (a : SuzukiPositiveAperture) (n : ℕ) (w : ℝ) :
    (w : ℂ) • ccmPrimeTransportOperator a n =
      ((w / Real.sqrt n : ℝ) : ℂ) •
        ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n)) := by
  apply ContinuousLinearMap.ext
  intro f
  change (w : ℂ) • (((1/Real.sqrt n : ℝ) : ℂ) •
    ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n)) f) = _
  rw [smul_smul]
  have heq : (w : ℂ) * ((1/Real.sqrt n : ℝ) : ℂ) = ((w/Real.sqrt n : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq]
  rfl

/-- Explicit squared-norm gain for two literal von Mangoldt source atoms. -/
theorem ccmPrimeSourcePair_opNorm_sq_bound (a : SuzukiPositiveAperture)
    (n m : ℕ) (hn : a.1 < Real.log n) (hnm : Real.log n < Real.log m)
    (N : ℕ) (hN : 0 < N)
    (hwidth : 2*a.1-Real.log n < (N : ℝ)*(Real.log m-Real.log n)) :
    (N : ℝ)^2 * ‖(ArithmeticFunction.vonMangoldt n : ℂ) • ccmPrimeTransportOperator a n +
      (ArithmeticFunction.vonMangoldt m : ℂ) • ccmPrimeTransportOperator a m‖^2 ≤
      (N : ℝ)^2 * (ArithmeticFunction.vonMangoldt n/Real.sqrt n +
        ArithmeticFunction.vonMangoldt m/Real.sqrt m)^2 -
      (ArithmeticFunction.vonMangoldt n/Real.sqrt n)*
        (ArithmeticFunction.vonMangoldt m/Real.sqrt m) := by
  rw [ccmWeightedPrimeTransport_eq, ccmWeightedPrimeTransport_eq]
  exact ccmOuterShiftPair_opNorm_sq_bound a hn hnm N hN hwidth _ _
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))

/-- Positive, distinct outer prime-power atoms improve the separate source norm bound strictly. -/
theorem ccmPrimeSourcePair_norm_lt_separate (a : SuzukiPositiveAperture)
    (n m : ℕ) (hn : a.1 < Real.log n) (hnm : Real.log n < Real.log m)
    (hnp : 0 < ArithmeticFunction.vonMangoldt n)
    (hmp : 0 < ArithmeticFunction.vonMangoldt m) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) • ccmPrimeTransportOperator a n +
      (ArithmeticFunction.vonMangoldt m : ℂ) • ccmPrimeTransportOperator a m‖ <
        ArithmeticFunction.vonMangoldt n/Real.sqrt n +
          ArithmeticFunction.vonMangoldt m/Real.sqrt m := by
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero, Real.log_zero] at hn
    linarith [a.property]
  have hm0 : m ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero, Real.log_zero] at hnm
    linarith [a.property]
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero hn0)
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero hm0)
  rw [ccmWeightedPrimeTransport_eq, ccmWeightedPrimeTransport_eq]
  exact ccmOuterShiftPair_norm_lt_sum a hn hnm _ _ (div_pos hnp hsn) (div_pos hmp hsm)


/-- A distinct positive outer prime-power pair makes the full atomwise source budget strict. -/
theorem norm_ccmFinitePrimeOperator_lt_outerShellBudget_of_pair
    (a : SuzukiPositiveAperture) (n m : ℕ)
    (hnmem : n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2*a.1))))
    (hmmem : m ∈ Finset.Icc 2 (Nat.floor (Real.exp (2*a.1))))
    (hn : a.1 < Real.log n) (hnm : Real.log n < Real.log m)
    (hnp : 0 < ArithmeticFunction.vonMangoldt n)
    (hmp : 0 < ArithmeticFunction.vonMangoldt m) :
    ‖ccmFinitePrimeOperator a‖ < ccmPrimeOuterShellBudget a := by
  classical
  let s := Finset.Icc 2 (Nat.floor (Real.exp (2*a.1)))
  let A : ℕ → (suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a) :=
    fun j => (ArithmeticFunction.vonMangoldt j : ℂ) • ccmPrimeTransportOperator a j
  let w : ℕ → ℝ := fun j => (if a.1 < Real.log j then 1 else 2) *
    (ArithmeticFunction.vonMangoldt j/Real.sqrt j)
  have hne : m ≠ n := by intro heq; rw [heq] at hnm; exact lt_irrefl _ hnm
  have hmerase : m ∈ s.erase n := Finset.mem_erase.mpr ⟨hne, hmmem⟩
  have hsumA : ccmFinitePrimeOperator a = A n + A m + ∑ j ∈ (s.erase n).erase m, A j := by
    change (∑ j ∈ s, A j) = _
    rw [← Finset.add_sum_erase s A hnmem,
      ← Finset.add_sum_erase (s.erase n) A hmerase, add_assoc]
  have hsumw : ccmPrimeOuterShellBudget a = w n + w m + ∑ j ∈ (s.erase n).erase m, w j := by
    change (∑ j ∈ s, w j) = _
    rw [← Finset.add_sum_erase s w hnmem,
      ← Finset.add_sum_erase (s.erase n) w hmerase, add_assoc]
  have hp : ‖A n+A m‖ < w n+w m := by
    dsimp [A, w]
    rw [if_pos hn, if_pos (lt_trans hn hnm), one_mul, one_mul]
    exact ccmPrimeSourcePair_norm_lt_separate a n m hn hnm hnp hmp
  have hterm : ∀ j ∈ s, ‖A j‖ ≤ w j := by
    intro j hj
    have hv := ArithmeticFunction.vonMangoldt_nonneg (n := j)
    have hnorm : ‖(ArithmeticFunction.vonMangoldt j : ℂ)‖ = ArithmeticFunction.vonMangoldt j := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    dsimp [A, w]
    calc
      _ ≤ ‖(ArithmeticFunction.vonMangoldt j : ℂ)‖ * ‖ccmPrimeTransportOperator a j‖ :=
        norm_smul_continuousLinearMap_le _ _
      _ = ArithmeticFunction.vonMangoldt j * ‖ccmPrimeTransportOperator a j‖ := by rw [hnorm]
      _ ≤ _ := by
        by_cases hlag : a.1 < Real.log j
        · rw [if_pos hlag, one_mul]
          have hb := mul_le_mul_of_nonneg_left
            (norm_ccmPrimeTransportOperator_le_outerShell a j hlag) hv
          have heq : ArithmeticFunction.vonMangoldt j*(1/Real.sqrt j) =
              ArithmeticFunction.vonMangoldt j/Real.sqrt j := by ring
          rw [heq] at hb
          exact hb
        · rw [if_neg hlag]
          have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
          have hb := mul_le_mul_of_nonneg_left (norm_ccmPrimeTransportOperator_le a hj1) hv
          have heq : ArithmeticFunction.vonMangoldt j*(2/Real.sqrt j) =
              2*(ArithmeticFunction.vonMangoldt j/Real.sqrt j) := by ring
          rw [heq] at hb
          exact hb
  have hrest : ‖∑ j ∈ (s.erase n).erase m, A j‖ ≤ ∑ j ∈ (s.erase n).erase m, w j := by
    refine (norm_sum_le _ A).trans (Finset.sum_le_sum ?_)
    intro j hj
    exact hterm j (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj))
  rw [hsumA, hsumw]
  have htri := norm_add_le (A n+A m) (∑ j ∈ (s.erase n).erase m, A j)
  linarith


/-- Bertrand supplies two distinct positive atoms in every outer shell above `log 5`. -/
theorem exists_two_outer_primes_of_log_five_le (a : SuzukiPositiveAperture)
    (ha : Real.log 5 ≤ a.1) :
    ∃ n m : ℕ, n.Prime ∧ m.Prime ∧
      n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2*a.1))) ∧
      m ∈ Finset.Icc 2 (Nat.floor (Real.exp (2*a.1))) ∧
      a.1 < Real.log n ∧ Real.log n < Real.log m := by
  let X := Real.exp a.1
  let b := Nat.ceil X
  have hXpos : 0 < X := Real.exp_pos _
  have hX : 5 ≤ X := by
    have he := Real.exp_le_exp.mpr ha
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 5)] at he
    exact he
  have hb0 : b ≠ 0 := (Nat.ceil_pos.mpr hXpos).ne'
  obtain ⟨p, hp, hbp, hp2b⟩ := Nat.exists_prime_lt_and_le_two_mul b hb0
  obtain ⟨q, hq, hpq, hq2p⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have hbX : X ≤ (b : ℝ) := Nat.le_ceil _
  have hbUpper : (b : ℝ) < X+1 := Nat.ceil_lt_add_one hXpos.le
  have hbpR : (b : ℝ) < p := by exact_mod_cast hbp
  have hp2bR : (p : ℝ) ≤ 2*(b : ℝ) := by exact_mod_cast hp2b
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hq2pR : (q : ℝ) ≤ 2*(p : ℝ) := by exact_mod_cast hq2p
  have hqX : (q : ℝ) < X^2 := by nlinarith [sq_nonneg (X-5)]
  have hXp : X < (p : ℝ) := lt_of_le_of_lt hbX hbpR
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hXsq : X^2 = Real.exp (2*a.1) := by
    dsimp [X]
    rw [show 2*a.1=a.1+a.1 by ring, Real.exp_add]
    ring
  rw [hXsq] at hqX
  have hpX : (p : ℝ) < Real.exp (2*a.1) := lt_trans hpqR hqX
  have hnmem : p ∈ Finset.Icc 2 (Nat.floor (Real.exp (2*a.1))) :=
    Finset.mem_Icc.mpr ⟨hp.two_le, Nat.le_floor hpX.le⟩
  have hmmem : q ∈ Finset.Icc 2 (Nat.floor (Real.exp (2*a.1))) :=
    Finset.mem_Icc.mpr ⟨hq.two_le, Nat.le_floor hqX.le⟩
  have hap : a.1 < Real.log p := by
    have hl := Real.log_lt_log hXpos hXp
    change Real.log (Real.exp a.1) < Real.log p at hl
    rwa [Real.log_exp] at hl
  exact ⟨p, q, hp, hq, hnmem, hmmem, hap, Real.log_lt_log hppos hpqR⟩

/-- The full literal source has a strict joint-prime improvement at every aperture `a≥log 5`. -/
theorem norm_ccmFinitePrimeOperator_lt_outerShellBudget_of_log_five_le
    (a : SuzukiPositiveAperture) (ha : Real.log 5 ≤ a.1) :
    ‖ccmFinitePrimeOperator a‖ < ccmPrimeOuterShellBudget a := by
  obtain ⟨n, m, hnp, hmp, hnmem, hmmem, hn, hnm⟩ := exists_two_outer_primes_of_log_five_le a ha
  apply norm_ccmFinitePrimeOperator_lt_outerShellBudget_of_pair a n m hnmem hmmem hn hnm
  · rw [ArithmeticFunction.vonMangoldt_apply_prime hnp]
    exact lt_trans a.property hn
  · rw [ArithmeticFunction.vonMangoldt_apply_prime hmp]
    exact lt_trans (lt_trans a.property hn) hnm


/-- Common norm preservation remains possible: strict pair gain comes from output incompatibility. -/
theorem exists_polarConstrained_common_outerShift_norm (a : SuzukiPositiveAperture)
    {h k : ℝ} (hh : a.1 < h) (horder : h < k) (hkhi : k < 2*a.1) :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      ccmArchimedeanFormToAperture a u ≠ 0 ∧
      ‖ccmApertureCompression a (ccmSymmetricLogTranslation h)
        (ccmArchimedeanFormToAperture a u)‖ = ‖ccmArchimedeanFormToAperture a u‖ ∧
      ‖ccmApertureCompression a (ccmSymmetricLogTranslation k)
        (ccmArchimedeanFormToAperture a u)‖ = ‖ccmArchimedeanFormToAperture a u‖ := by
  have hk := lt_trans hh horder
  obtain ⟨u, v, hu, hv, hun, hvn, hue, hve⟩ :=
    exists_polarConstrained_outerShell_eigenvectors a hk hkhi
  let f := ccmArchimedeanFormToAperture a u
  let S := ccmApertureCompression a (ccmSymmetricLogTranslation h)
  have hcutk : indicatorCutoff (ccmOuterShiftSupport a k)
      (measurableSet_ccmOuterShiftSupport a k) f.1 = f.1 := by
    rw [← ccmApertureSymmetricTranslation_sq_val a hk f]
    change ccmApertureCompression a (ccmSymmetricLogTranslation k) f = f at hue
    rw [hue, hue]
  have hsub : ccmOuterShiftSupport a k ⊆ ccmOuterShiftSupport a h := by
    intro x hx
    rcases hx with hl | hr
    · exact Or.inl ⟨hl.1, by linarith [hl.2]⟩
    · exact Or.inr ⟨by linarith [hr.1], hr.2⟩
  have hcuth : indicatorCutoff (ccmOuterShiftSupport a h)
      (measurableSet_ccmOuterShiftSupport a h) f.1 = f.1 := by
    have hfae := indicatorCutoff_ae (ccmOuterShiftSupport a k)
      (measurableSet_ccmOuterShiftSupport a k) f.1
    rw [hcutk] at hfae
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (ccmOuterShiftSupport a h)
        (measurableSet_ccmOuterShiftSupport a h) f.1, hfae] with x hc hf
    rw [hc]
    by_cases hx : x ∈ ccmOuterShiftSupport a h
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hf, indicator_of_notMem (fun hkx => hx (hsub hkx))]
  have hsq : S (S f) = f := by
    apply Subtype.ext
    exact (ccmApertureSymmetricTranslation_sq_val a hh f).trans hcuth
  have hsa := (ccmApertureCompression_isSelfAdjoint a
    (ccmSymmetricLogTranslation_isSelfAdjoint h)).isSymmetric
  have heq : inner ℂ (S f) (S f) = inner ℂ f (S (S f)) := hsa f (S f)
  rw [hsq] at heq
  have hnormsq : ‖S f‖^2 = ‖f‖^2 := by
    calc
      _ = (inner ℂ (S f) (S f)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = (inner ℂ f f).re := congrArg Complex.re heq
      _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
  have hnorm : ‖S f‖ = ‖f‖ := by nlinarith [norm_nonneg (S f), norm_nonneg f]
  refine ⟨u, hu, hun, hnorm, ?_⟩
  rw [hue]

end RHTower
