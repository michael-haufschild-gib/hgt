import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry

/-!
# Sharp countable renewals for cofinal geometry

This module constructs explicit probability mass functions with polynomial renewal tails over
strictly positive geometric baselines.  Absolute summability of the logarithmic density ratio
proves finite relative entropy without numerical certificates.  The construction supplies the
sharp side of the global cubic renewal wall and can be embedded into literal recovery species.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory Set
open scoped ENNReal

noncomputable section

/-- A probability mass function built from a nonnegative extended-real series of total mass one. -/
def pmfOfHasSum (p : ℕ → ℝ≥0∞) (hp : HasSum p 1) : PMF ℕ := ⟨p, hp⟩

@[simp] theorem pmfOfHasSum_apply (p : ℕ → ℝ≥0∞) (hp : HasSum p 1) (n : ℕ) :
    pmfOfHasSum p hp n = p n := rfl

/-- On a countable full-support baseline, the pointwise mass ratio is a density for the renewed
probability law. -/
theorem pmf_withDensity_ratio_eq
    (p q : ℕ → ℝ≥0∞) (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ n, p n ≠ 0) :
    (pmfOfHasSum p hp).toMeasure.withDensity (fun n => q n / p n) =
      (pmfOfHasSum q hq).toMeasure := by
  apply Measure.ext_of_singleton
  intro n
  rw [MeasureTheory.withDensity_apply', MeasureTheory.lintegral_singleton]
  rw [PMF.toMeasure_apply_singleton, PMF.toMeasure_apply_singleton]
  · exact ENNReal.div_mul_cancel (hp0 n) (PMF.apply_ne_top (pmfOfHasSum p hp) n)
  · exact MeasurableSet.singleton _
  · exact MeasurableSet.singleton _

/-- Absolute summability against a countable probability mass function gives integrability. -/
theorem integrable_pmf_of_summable_weighted_abs
    (q : ℕ → ℝ≥0∞) (hq : HasSum q 1) (f : ℕ → ℝ)
    (hsum : Summable (fun n => (q n).toReal * |f n|)) :
    Integrable f (pmfOfHasSum q hq).toMeasure := by
  constructor
  · exact StronglyMeasurable.of_discrete.aestronglyMeasurable
  · rw [HasFiniteIntegral, MeasureTheory.lintegral_countable']
    have hterm : (fun n => ‖f n‖ₑ * (pmfOfHasSum q hq).toMeasure {n}) =
        fun n => ENNReal.ofReal ((q n).toReal * |f n|) := by
      funext n
      rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
      rw [← ofReal_norm, Real.norm_eq_abs,
        ← ENNReal.ofReal_toReal (PMF.apply_ne_top (pmfOfHasSum q hq) n),
        ← ENNReal.ofReal_mul (abs_nonneg (f n))]
      congr 1
      simp [pmfOfHasSum_apply, mul_comm]
    rw [hterm]
    exact hsum.tsum_ofReal_lt_top

/-- A symbolic absolute-log-ratio test for finite KL divergence between countable laws. -/
theorem discretePMF_klDiv_ne_top
    (p q : ℕ → ℝ≥0∞) (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ n, p n ≠ 0)
    (hsum : Summable (fun n => (q n).toReal *
      |Real.log ((q n).toReal / (p n).toReal)|)) :
    klDiv (pmfOfHasSum q hq).toMeasure (pmfOfHasSum p hp).toMeasure ≠ ⊤ := by
  let P := (pmfOfHasSum p hp).toMeasure
  let Q := (pmfOfHasSum q hq).toMeasure
  let density : ℕ → ℝ≥0∞ := fun n => q n / p n
  have hQP : P.withDensity density = Q := by
    exact pmf_withDensity_ratio_eq p q hp hq hp0
  have hac : Q ≪ P := by
    rw [← hQP]
    exact withDensity_absolutelyContinuous P density
  have hrn : Q.rnDeriv P =ᵐ[P] density := by
    rw [← hQP]
    exact Measure.rnDeriv_withDensity P Measurable.of_discrete
  have hllr : llr Q P =ᵐ[Q] fun n =>
      Real.log ((q n).toReal / (p n).toReal) := by
    filter_upwards [hac.ae_le hrn] with n hn
    rw [llr, hn, ENNReal.toReal_div]
  have hint : Integrable (fun n =>
      Real.log ((q n).toReal / (p n).toReal)) Q := by
    apply integrable_pmf_of_summable_weighted_abs q hq
    exact hsum
  apply klDiv_ne_top hac
  exact hint.congr hllr.symm

/-- The logarithmic density ratio of a degree-`d` polynomial tail against a geometric law is
absolutely summable precisely in the range needed for the cubic sharpness construction. -/
theorem summable_polynomial_geometric_logRatio
    (a r d : ℝ) (ha : 0 < a) (hr0 : 0 < r) (hr1 : r < 1) (hd : 2 < d) :
    Summable (fun n : ℕ =>
      (a * (((n + 1 : ℕ) : ℝ) ^ (-d))) *
        |Real.log ((a * (((n + 1 : ℕ) : ℝ) ^ (-d)) /
          ((1 - r) * r ^ (n + 1))))|) := by
  let C : ℝ := |Real.log a| + |Real.log (1 - r)|
  let D : ℝ := d + |Real.log r|
  have hsum0base : Summable (fun n : ℕ => (n : ℝ) ^ (-d)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsum0 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-d))) :=
    (summable_nat_add_iff 1).mpr hsum0base
  have hsum1base : Summable (fun n : ℕ => (n : ℝ) ^ (1 - d)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsum1 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (1 - d))) :=
    (summable_nat_add_iff 1).mpr hsum1base
  have hmajor : Summable (fun n : ℕ =>
      a * C * (((n + 1 : ℕ) : ℝ) ^ (-d)) +
        a * D * (((n + 1 : ℕ) : ℝ) ^ (1 - d))) :=
    (hsum0.mul_left (a * C)).add (hsum1.mul_left (a * D))
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg ha.le (Real.rpow_nonneg (by positivity) _)) (abs_nonneg _))
    (fun n => ?_) hmajor
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogNle : Real.log N ≤ N := Real.log_le_self hN0.le
  have hrpow : 0 < N ^ (-d) := Real.rpow_pos_of_pos hN0 _
  have hrpowN : 0 < r ^ (n + 1) := pow_pos hr0 _
  have hden : 0 < (1 - r) * r ^ (n + 1) :=
    mul_pos (sub_pos.mpr hr1) hrpowN
  have hlogeq :
      Real.log ((a * N ^ (-d)) / ((1 - r) * r ^ (n + 1))) =
        Real.log a - d * Real.log N - Real.log (1 - r) -
          (n + 1 : ℕ) * Real.log r := by
    rw [Real.log_div (mul_ne_zero ha.ne' hrpow.ne') hden.ne',
      Real.log_mul ha.ne' hrpow.ne', Real.log_rpow hN0 (-d),
      Real.log_mul (sub_pos.mpr hr1).ne' hrpowN.ne', Real.log_pow]
    push_cast
    ring
  have habs :
      |Real.log ((a * N ^ (-d)) / ((1 - r) * r ^ (n + 1)))| ≤ C + D * N := by
    rw [hlogeq]
    calc
      |Real.log a - d * Real.log N - Real.log (1 - r) - N * Real.log r| ≤
          |Real.log a| + |d * Real.log N| + |Real.log (1 - r)| +
            |N * Real.log r| := by
        linarith [
          abs_sub (Real.log a - d * Real.log N - Real.log (1 - r)) (N * Real.log r),
          abs_sub (Real.log a - d * Real.log N) (Real.log (1 - r)),
          abs_sub (Real.log a) (d * Real.log N)]
      _ = C + d * Real.log N + N * |Real.log r| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ d),
          abs_of_nonneg hlogN0, abs_of_nonneg hN0.le]
        dsimp [C]
        ring
      _ ≤ C + D * N := by
        dsimp [D]
        nlinarith
  have hfactor : a * N ^ (-d) * (C + D * N) =
      a * C * N ^ (-d) + a * D * N ^ (1 - d) := by
    have hrpow_shift : N ^ (1 - d) = N * N ^ (-d) := by
      calc
        N ^ (1 - d) = N ^ (1 + (-d)) := by ring_nf
        _ = N ^ 1 * N ^ (-d) := Real.rpow_add hN0 1 (-d)
        _ = N * N ^ (-d) := by rw [Real.rpow_one]
    rw [hrpow_shift]
    ring
  calc
    (a * N ^ (-d)) *
        |Real.log ((a * N ^ (-d)) / ((1 - r) * r ^ (n + 1)))| ≤
        (a * N ^ (-d)) * (C + D * N) :=
      mul_le_mul_of_nonneg_left habs
        (mul_nonneg ha.le (Real.rpow_nonneg hN0.le _))
    _ = _ := hfactor

/-- Geometric baseline atom mass. -/
def geometricBaselineMass (r : ℝ) (n : ℕ) : ℝ := (1 - r) * r ^ n

theorem exp_neg_mem_Ioo_zero_one {beta : ℝ} (hbeta : 0 < beta) :
    Real.exp (-beta) ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩

/-- Geometric baseline written in its ordinary-exponential evacuation chart. -/
theorem geometricBaselineMass_exp_neg (beta : ℝ) (n : ℕ) :
    geometricBaselineMass (Real.exp (-beta)) n =
      (1 - Real.exp (-beta)) * Real.exp (-beta * (n : ℝ)) := by
  rw [geometricBaselineMass, ← Real.exp_nat_mul]
  congr 2
  ring

/-- Polynomial renewal mass at positive depth `n + 1`. -/
def polynomialRenewalTail (a d : ℝ) (n : ℕ) : ℝ :=
  a * (((n + 1 : ℕ) : ℝ) ^ (-d))

/-- Polynomial renewal law, with unused probability mass reserved at depth zero. -/
def polynomialRenewalMass (a d : ℝ) : ℕ → ℝ
  | 0 => 1 - ∑' n : ℕ, polynomialRenewalTail a d n
  | n + 1 => polynomialRenewalTail a d n

theorem summable_geometricBaselineMass {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (geometricBaselineMass r) := by
  exact (summable_geometric_of_lt_one hr0 hr1).mul_left (1 - r)

theorem tsum_geometricBaselineMass {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n, geometricBaselineMass r n = 1 := by
  change ∑' n : ℕ, (1 - r) * r ^ n = 1
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1]
  field_simp [ne_of_gt (sub_pos.mpr hr1)]

theorem geometricBaselineMass_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    0 ≤ geometricBaselineMass r n := by
  exact mul_nonneg (sub_nonneg.mpr hr1) (pow_nonneg hr0 n)

theorem summable_polynomialRenewalTail {a d : ℝ} (hd : 1 < d) :
    Summable (polynomialRenewalTail a d) := by
  apply Summable.mul_left
  exact (summable_nat_add_iff 1).mpr
    (Real.summable_nat_rpow.mpr (by linarith))

theorem polynomialRenewalTail_nonneg {a d : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ polynomialRenewalTail a d n := by
  exact mul_nonneg ha (Real.rpow_nonneg (by positivity) _)

theorem polynomialRenewalMass_nonneg {a d : ℝ} (ha : 0 ≤ a)
    (htotal : ∑' n, polynomialRenewalTail a d n < 1) (n : ℕ) :
    0 ≤ polynomialRenewalMass a d n := by
  cases n with
  | zero => simp only [polynomialRenewalMass]; linarith
  | succ n => exact polynomialRenewalTail_nonneg ha n

theorem summable_polynomialRenewalMass {a d : ℝ} (hd : 1 < d) :
    Summable (polynomialRenewalMass a d) := by
  apply (summable_nat_add_iff 1).mp
  simpa [polynomialRenewalMass] using summable_polynomialRenewalTail (a := a) hd

theorem tsum_polynomialRenewalMass {a d : ℝ} (hd : 1 < d) :
    ∑' n, polynomialRenewalMass a d n = 1 := by
  have hsum := summable_polynomialRenewalMass (a := a) hd
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have htail : (∑' n, polynomialRenewalMass a d (n + 1)) =
      ∑' n, polynomialRenewalTail a d n := by
    congr
  rw [htail] at hsplit
  simpa [polynomialRenewalMass] using hsplit.symm

/-- Extended-real geometric baseline atom mass. -/
def geometricBaselineENNMass (r : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (geometricBaselineMass r n)

/-- Extended-real polynomial renewal atom mass. -/
def polynomialRenewalENNMass (a d : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (polynomialRenewalMass a d n)

theorem hasSum_geometricBaselineENNMass {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (geometricBaselineENNMass r) 1 := by
  rw [ENNReal.summable.hasSum_iff]
  change (∑' n, ENNReal.ofReal (geometricBaselineMass r n)) = 1
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (geometricBaselineMass_nonneg hr0 hr1.le)
    (summable_geometricBaselineMass hr0 hr1)]
  rw [tsum_geometricBaselineMass hr0 hr1]
  simp

theorem hasSum_polynomialRenewalENNMass {a d : ℝ} (ha : 0 ≤ a) (hd : 1 < d)
    (htotal : ∑' n, polynomialRenewalTail a d n < 1) :
    HasSum (polynomialRenewalENNMass a d) 1 := by
  rw [ENNReal.summable.hasSum_iff]
  change (∑' n, ENNReal.ofReal (polynomialRenewalMass a d n)) = 1
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (polynomialRenewalMass_nonneg ha htotal)
    (summable_polynomialRenewalMass (a := a) hd)]
  rw [tsum_polynomialRenewalMass (a := a) hd]
  simp

/-- Geometric baseline PMF with ratio strictly below one. -/
def geometricBaselinePMF (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : PMF ℕ :=
  pmfOfHasSum (geometricBaselineENNMass r)
    (hasSum_geometricBaselineENNMass hr0 hr1)

/-- Polynomial-tail renewal PMF with its unused mass placed at depth zero. -/
def polynomialRenewalPMF (a d : ℝ) (ha : 0 ≤ a) (hd : 1 < d)
    (htotal : ∑' n, polynomialRenewalTail a d n < 1) : PMF ℕ :=
  pmfOfHasSum (polynomialRenewalENNMass a d)
    (hasSum_polynomialRenewalENNMass ha hd htotal)

@[simp] theorem geometricBaselinePMF_apply
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    geometricBaselinePMF r hr0 hr1 n =
      ENNReal.ofReal ((1 - r) * r ^ n) := rfl

@[simp] theorem polynomialRenewalPMF_zero
    (a d : ℝ) (ha : 0 ≤ a) (hd : 1 < d)
    (htotal : ∑' n, polynomialRenewalTail a d n < 1) :
    polynomialRenewalPMF a d ha hd htotal 0 =
      ENNReal.ofReal (1 - ∑' n, polynomialRenewalTail a d n) := rfl

@[simp] theorem polynomialRenewalPMF_succ
    (a d : ℝ) (ha : 0 ≤ a) (hd : 1 < d)
    (htotal : ∑' n, polynomialRenewalTail a d n < 1) (n : ℕ) :
    polynomialRenewalPMF a d ha hd htotal (n + 1) =
      ENNReal.ofReal (a * (((n + 1 : ℕ) : ℝ) ^ (-d))) := rfl

/-- Polynomial-tail renewal has finite KL action over every positive geometric baseline when
`d > 2`.  This is the shared analytic core of global and Hasse cubic sharpness. -/
theorem polynomialRenewalPMF_klDiv_geometricBaselinePMF_ne_top
    {a r d : ℝ} (ha : 0 < a) (hr0 : 0 < r) (hr1 : r < 1) (hd : 2 < d)
    (htotal : ∑' n, polynomialRenewalTail a d n < 1) :
    klDiv (polynomialRenewalPMF a d ha.le (by linarith) htotal).toMeasure
      (geometricBaselinePMF r hr0.le hr1).toMeasure ≠ ⊤ := by
  apply discretePMF_klDiv_ne_top
  · intro n
    exact (ENNReal.ofReal_pos.mpr
      (mul_pos (sub_pos.mpr hr1) (pow_pos hr0 n))).ne'
  · apply (summable_nat_add_iff 1).mp
    have hrenewed (n : ℕ) :
        (ENNReal.ofReal (a * (((n + 1 : ℕ) : ℝ) ^ (-d)))).toReal =
          a * (((n + 1 : ℕ) : ℝ) ^ (-d)) :=
      ENNReal.toReal_ofReal
        (mul_nonneg ha.le (Real.rpow_nonneg (by positivity) _))
    have hbaseline (n : ℕ) :
        (ENNReal.ofReal ((1 - r) * r ^ (n + 1))).toReal =
          (1 - r) * r ^ (n + 1) :=
      ENNReal.toReal_ofReal
        (mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg hr0.le _))
    simpa only [polynomialRenewalENNMass, polynomialRenewalMass,
      polynomialRenewalTail, geometricBaselineENNMass, geometricBaselineMass,
      hrenewed, hbaseline] using
        summable_polynomial_geometric_logRatio a r d ha hr0 hr1 hd

/-- Exact constant current carried by the polynomial renewal tail against degree-`d` work. -/
theorem polynomialRenewalPMF_constantCurrent
    {K c d : ℝ} (hK : 0 < K) (hc : 0 < c) (hd : 1 < d)
    (htotal : ∑' n, polynomialRenewalTail (c / K) d n < 1) (n : ℕ) :
    ((polynomialRenewalPMF (c / K) d (div_nonneg hc.le hK.le) hd htotal)
        (n + 1)).toReal *
      (K * (((n + 1 : ℕ) : ℝ) ^ d)) = c := by
  have ha : 0 < c / K := div_pos hc hK
  rw [polynomialRenewalPMF_succ,
    ENNReal.toReal_ofReal (mul_nonneg ha.le (Real.rpow_nonneg (by positivity) _))]
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 0 < N := by positivity
  have hcancel : N ^ (-d) * N ^ d = 1 := by
    rw [← Real.rpow_add hN]
    simp
  calc
    (c / K * N ^ (-d)) * (K * N ^ d) = c * (N ^ (-d) * N ^ d) := by
      field_simp [hK.ne']
    _ = c := by rw [hcancel, mul_one]

/-- Complete class-sharp model above the quadratic wall: exact geometric baseline, exact
polynomial renewed atoms, finite global KL action, and constant mass-weighted work current. -/
theorem geometricPolynomialRenewal_cubicSharp
    {r K c d : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hK : 0 < K) (hc : 0 < c) (hd : 2 < d)
    (htotal : ∑' n, polynomialRenewalTail (c / K) d n < 1) :
    let P := geometricBaselinePMF r hr0.le hr1
    let Q := polynomialRenewalPMF (c / K) d (div_nonneg hc.le hK.le)
      (by linarith) htotal
    (∀ n, P n = ENNReal.ofReal (geometricBaselineMass r n)) ∧
      (∀ n, Q (n + 1) =
        ENNReal.ofReal ((c / K) * (((n + 1 : ℕ) : ℝ) ^ (-d)))) ∧
      klDiv Q.toMeasure P.toMeasure ≠ ⊤ ∧
      ∀ n, (Q (n + 1)).toReal *
        (K * (((n + 1 : ℕ) : ℝ) ^ d)) = c := by
  dsimp only
  have ha : 0 < c / K := div_pos hc hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    rfl
  · exact polynomialRenewalPMF_klDiv_geometricBaselinePMF_ne_top
      ha hr0 hr1 hd htotal
  · intro n
    exact polynomialRenewalPMF_constantCurrent hK hc (by linarith) htotal n

end

end GaloisForLFunctions.HTGeometry
