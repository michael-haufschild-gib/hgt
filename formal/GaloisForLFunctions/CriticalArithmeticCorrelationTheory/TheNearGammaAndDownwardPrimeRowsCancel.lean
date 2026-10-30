import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNearAtomsHaveALogarithmicPairing
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheDownwardPrimeRowIsAnExactLogarithmicDivisorJet
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap
import GaloisForLFunctions.BiScaleUncertainty.SieveCoordinateSupNorm
import GaloisForLFunctions.RHTower.CriticalGibbsPerronPolarization
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineKeepsAGammaReserveAtEveryOverlap

/-!
# Cancellation of near Gamma and downward prime rows

At every fixed overlap, near off-diagonal Gamma entries have the leading
coefficient `log(N/c)` times the profile autocorrelation. The downward
Mangoldt convolution on a Ramanujan profile has exactly the matching
`log j` coefficient, with a bounded finite divisor correction.

The signed difference has bounded squared row norm: distinct near indices
lie in a fixed top fraction of the horizon, and each row has bounded
cardinality. Its norm tends to zero after logarithmic normalization.
The downward row is the literal prime-power product sum with products
inside the horizon. Exterior products and upward rows are separate terms.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Real
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics BezoutValuationIncidence

/-- An integer-distance bound for the two-width logarithmic neighbourhood. -/
def nearRowRadius (c : ℝ) : ℝ := 2 * c * Real.exp (2 * c)

/-- Distinct indices at log-distance at most twice the physical atom width. -/
def nearRowIndices (c : ℝ) (N n : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun j => j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * c / N)

/-- Integer separation confines every near pair to a fixed top fraction of the horizon. -/
theorem nearRow_geometry {c : ℝ} (hc : 0 < c) {N n j : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ nearRowIndices c N n) :
    |(j : ℝ) - n| ≤ nearRowRadius c ∧
      (N : ℝ) ≤ nearRowRadius c * n ∧ (N : ℝ) ≤ nearRowRadius c * j := by
  obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by linarith only [hN1]
  have he : Real.exp (2 * c / N) - 1 ≤ nearRowRadius c / N := by
    calc
      _ ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
      _ ≤ 2 * c / N * Real.exp (2 * c) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (div_le_self (by positivity) hN1)) (by positivity)
      _ = _ := by unfold nearRowRadius; ring
  have hdist := (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans
    (mul_le_mul_of_nonneg_left he hn0.le)
  have hdist' := (abs_sub_le_of_abs_log_le hn0 hj0
    (by simpa only [abs_sub_comm] using hlog)).trans
    (mul_le_mul_of_nonneg_left he hj0.le)
  have hone : (1 : ℝ) ≤ |(j : ℝ) - n| := by
    rcases lt_or_gt_of_ne hjn with h | h
    · have hstep : (j : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_iff.mpr h
      rw [abs_of_neg (by linarith only [hstep])]
      linarith only [hstep]
    · have hstep : (n : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_iff.mpr h
      rw [abs_of_pos (by linarith only [hstep])]
      linarith only [hstep]
  have hrad : 0 ≤ nearRowRadius c := by unfold nearRowRadius; positivity
  refine ⟨hdist.trans ?_, ?_, ?_⟩
  · calc (n : ℝ) * (nearRowRadius c / N)
        ≤ N * (nearRowRadius c / N) := mul_le_mul_of_nonneg_right
          (by exact_mod_cast (mem_Icc.mp hn).2) (div_nonneg hrad hN0.le)
      _ = nearRowRadius c := by field_simp
  · have h := hone.trans hdist
    rw [← mul_div_assoc, le_div_iff₀ hN0] at h
    simpa only [one_mul, mul_one, mul_comm] using h
  · have h := (show (1 : ℝ) ≤ |(n : ℝ) - j| by simpa only [abs_sub_comm] using hone).trans hdist'
    rw [← mul_div_assoc, le_div_iff₀ hN0] at h
    simpa only [one_mul, mul_one, mul_comm] using h

theorem card_nearRowIndices_le {c : ℝ} (hc : 0 < c) {N n : ℕ} (hn : n ∈ Icc 1 N) :
    ((nearRowIndices c N n).card : ℝ) ≤ 2 * nearRowRadius c := by
  have hsub : nearRowIndices c N n ⊆
      (Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ nearRowRadius c) := by
    intro j hj
    exact mem_filter.mpr ⟨(mem_filter.mp hj).1, (mem_filter.mp hj).2.1,
      (nearRow_geometry hc hn hj).1⟩
  exact (show ((nearRowIndices c N n).card : ℝ) ≤
      (((Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ nearRowRadius c)).card : ℝ)
      by exact_mod_cast card_le_card hsub).trans
    (card_near_le (Icc 1 N) n (by unfold nearRowRadius; positivity))

/-- Bounded near-pair numerators give a horizon-independent squared row bound. -/
theorem sum_near_div_sqrt_sq_le {c K : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (F : ℕ → ℕ → ℝ)
    (hF : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |F n j| ≤ K) :
    (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2) ≤
      4 * nearRowRadius c ^ 3 * K ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : 0 ≤ nearRowRadius c := by unfold nearRowRadius; positivity
  have hrow : ∀ n ∈ Icc 1 N,
      (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2 ≤
        4 * nearRowRadius c ^ 3 * K ^ 2 / N := by
    intro n hn
    have hpoint : ∀ j ∈ nearRowIndices c N n,
        (F n j / Real.sqrt j) ^ 2 ≤ K ^ 2 * nearRowRadius c / N := by
      intro j hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hj).1).1
      have hsq : F n j ^ 2 ≤ K ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg (F n j)) (hF n hn j hj)
        simpa only [← sq, sq_abs] using h
      rw [div_pow, Real.sq_sqrt hj0.le]
      calc F n j ^ 2 / j ≤ K ^ 2 / j := div_le_div_of_nonneg_right hsq hj0.le
        _ ≤ K ^ 2 * nearRowRadius c / N := by
          rw [div_le_div_iff₀ hj0 hN0]
          have h := mul_le_mul_of_nonneg_left (nearRow_geometry hc hn hj).2.2 (sq_nonneg K)
          nlinarith only [h]
    have hsum := sum_le_sum hpoint
    rw [sum_const, nsmul_eq_mul] at hsum
    have hcard := card_nearRowIndices_le hc hn
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (nearRowIndices c N n)
      (fun j => F n j / Real.sqrt j) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
    calc
      _ ≤ ((nearRowIndices c N n).card : ℝ) *
          ∑ j ∈ nearRowIndices c N n, (F n j / Real.sqrt j) ^ 2 := by
        simpa only [mul_comm] using hcs
      _ ≤ (2 * nearRowRadius c) * ((2 * nearRowRadius c) *
          (K ^ 2 * nearRowRadius c / N)) :=
        mul_le_mul hcard (hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity)))
          (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Icc 1 N, 4 * nearRowRadius c ^ 3 * K ^ 2 / N := sum_le_sum hrow
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
      simp only [Nat.add_sub_cancel]
      field_simp

/-- Absolute mass of the finite logarithmic divisor jet. -/
def ramanujanJetBound (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors, |(ArithmeticFunction.moebius (m / d) : ℝ) * d * Real.log d|

theorem abs_ramanujanLogDivisorJet_le (m n : ℕ) :
    |ramanujanLogDivisorJet m n| ≤ ramanujanJetBound m := by
  unfold ramanujanLogDivisorJet ramanujanJetBound
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => by
    split_ifs <;> simp only [abs_zero, le_refl, abs_nonneg])

/-- Gamma minus the exact downward Mangoldt convolution, before the square-root row weight. -/
def nearGammaDownwardCoefficient (φ : ℝ → ℝ) (c : ℝ) (N m n j : ℕ) : ℝ :=
  atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) *
      ramanujanLagCoefficient m j -
    shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
      ∑ d ∈ j.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) * ramanujanLagCoefficient m (j / d)

/-- The signed near row acting on the unnormalized conductor coefficient `c_m(j)/√j`. -/
def nearGammaDownwardRow (φ : ℝ → ℝ) (c : ℝ) (N m n : ℕ) : ℝ :=
  ∑ j ∈ nearRowIndices c N n, nearGammaDownwardCoefficient φ c N m n j / Real.sqrt j

/-- The shared logarithm cancels, leaving bounded near-pair coefficients. -/
theorem exists_nearGammaDownwardCoefficient_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
      ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
        |nearGammaDownwardCoefficient φ c N m n j| ≤ E := by
  obtain ⟨K, hK, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let B := nearRowRadius c
  let A : ℝ := m.totient
  let J := ramanujanJetBound m
  have hB : 0 ≤ B := by dsimp only [B, nearRowRadius]; positivity
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hJ : 0 ≤ J := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(K + B + |Real.log c|) * A + J, by positivity, ?_⟩
  intro N hN hw1 n hn j hj
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hjN := (mem_filter.mp hj).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
  have hw0 : 0 < c / N := div_pos hc hN0
  have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
    have h := (mem_filter.mp hj).2.2
    change |Real.log j - Real.log n| ≤ 2 * c / N at h
    simpa only [mul_div_assoc] using h
  let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)
  let a := atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2)
  have hrem : |a - Real.log (1 / (c / N)) * q| ≤ K := by
    simpa only [a, q, mul_div_assoc] using hpair (c / N) hw0 hw1 n j hs
  have hq : |q| ≤ 1 := by
    have h := abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp)
      (|Real.log j - Real.log n| / (c / N))
    change |shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ ∫ u, φ u ^ 2 at h
    dsimp only [q]
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact h
  have hcm : |ramanujanLagCoefficient m j| ≤ A :=
    BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j
  have hjb : |ramanujanLogDivisorJet m j| ≤ J := abs_ramanujanLogDivisorJet_le m j
  have hquot : (N : ℝ) / j ≤ B :=
    (div_le_iff₀ hj0).mpr (nearRow_geometry hc hn hj).2.2
  have hloglow : 0 ≤ Real.log N - Real.log j := sub_nonneg.mpr
    (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
  have hloghigh : Real.log N - Real.log j ≤ B := by
    have h := Real.log_le_sub_one_of_pos (div_pos hN0 hj0)
    rw [Real.log_div hN0.ne' hj0.ne'] at h
    linarith only [h, hquot]
  have hlogeq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc.ne' hN0.ne']
    ring
  have hlog : |Real.log (1 / (c / N)) - Real.log j| ≤ B + |Real.log c| := by
    rw [hlogeq, show Real.log N - Real.log c - Real.log j =
      (Real.log N - Real.log j) - Real.log c by ring]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hloglow]; linarith only [hloghigh])
  have heq : nearGammaDownwardCoefficient φ c N m n j =
      (a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j +
      (Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j +
      q * ramanujanLogDivisorJet m j := by
    rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m
      (mem_Icc.mp hjN).1]
    dsimp only [a, q]
    ring
  rw [heq]
  calc
    _ ≤ |(a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j| +
        |(Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j| +
        |q * ramanujanLogDivisorJet m j| := abs_add_three _ _ _
    _ ≤ K * A + (B + |Real.log c|) * A + J := by
      simp only [abs_mul]
      have h1 := mul_le_mul hrem hcm (abs_nonneg _) hK
      have h2 := mul_le_mul (mul_le_mul hlog hq (abs_nonneg _) (by positivity))
        hcm (abs_nonneg _) (by positivity)
      have h3 := mul_le_mul hq hjb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simp only [mul_one, one_mul] at h2 h3
      linarith only [h1, h2, h3]
    _ = _ := by ring

/-- The complete interior near-row difference has bounded squared norm at every fixed overlap. -/
theorem exists_nearGammaDownwardRow_sq_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
      (∑ n ∈ Icc 1 N, nearGammaDownwardRow φ c N m n ^ 2) ≤ C := by
  obtain ⟨E, hE, hbound⟩ := exists_nearGammaDownwardCoefficient_bound hφ hsupp hM hc m
  refine ⟨4 * nearRowRadius c ^ 3 * E ^ 2, by unfold nearRowRadius; positivity, ?_⟩
  intro N hN hw
  exact sum_near_div_sqrt_sq_le hc hN (nearGammaDownwardCoefficient φ c N m)
    (hbound N hN hw)

/-- Literal downward prime powers with product inside the horizon; exact ratio lags are removed. -/
def interiorDownwardPrimeRow (g : ℝ → ℝ) (N m n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 N, ∑ j ∈ Icc 1 N, if k * j ≤ N then
    _root_.RHTower.vonMangoldtAtom k * (ramanujanLagCoefficient m j / Real.sqrt j) *
      (if k * j = n then 0 else bumpCorr g (Real.log (k * j : ℕ) - Real.log n)) /
        (∫ u, g u ^ 2) else 0

/-- Grouping the literal product `k*j` gives the full Mangoldt divisor convolution. -/
theorem interiorDownwardPrimeRow_eq_divisors (g : ℝ → ℝ) (N m n : ℕ) :
    interiorDownwardPrimeRow g N m n =
      ∑ j ∈ Icc 1 N,
        (if j = n then 0 else bumpCorr g (Real.log j - Real.log n)) / (∫ u, g u ^ 2) *
          (∑ d ∈ j.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) *
            ramanujanLagCoefficient m (j / d)) / Real.sqrt j := by
  let H : ℕ → ℝ := fun j =>
    (if j = n then 0 else bumpCorr g (Real.log j - Real.log n)) / (∫ u, g u ^ 2)
  let F : ℕ → ℕ → ℝ := fun k j =>
    (ArithmeticFunction.vonMangoldt k : ℝ) * ramanujanLagCoefficient m (j / k) /
      Real.sqrt j * H j
  have hfactor : ∀ k j : ℕ, 1 ≤ k → 1 ≤ j →
      _root_.RHTower.vonMangoldtAtom k * (ramanujanLagCoefficient m j / Real.sqrt j) =
        (ArithmeticFunction.vonMangoldt k : ℝ) * ramanujanLagCoefficient m j /
          Real.sqrt (k * j : ℕ) := by
    intro k j hk hj
    by_cases hk2 : 2 ≤ k
    · rw [_root_.RHTower.vonMangoldtAtom, if_pos hk2, Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg k)]
      ring
    · have hk1 : k = 1 := by omega
      subst k
      simp only [_root_.RHTower.vonMangoldtAtom, if_neg (by omega : ¬ 2 ≤ 1),
        ArithmeticFunction.vonMangoldt_apply_one, zero_mul, zero_div]
  calc
    interiorDownwardPrimeRow g N m n =
        ∑ k ∈ Icc 1 N, ∑ j ∈ Icc 1 N, if k * j ≤ N then F k (k * j) else 0 := by
      unfold interiorDownwardPrimeRow
      refine sum_congr rfl fun k hk => sum_congr rfl fun j hj => ?_
      by_cases hprod : k * j ≤ N
      · simp only [if_pos hprod]
        rw [hfactor k j (mem_Icc.mp hk).1 (mem_Icc.mp hj).1]
        dsimp only [F, H]
        rw [Nat.mul_div_cancel_left j (mem_Icc.mp hk).1]
        ring
      · simp only [if_neg hprod]
    _ = ∑ j ∈ Icc 1 N, ∑ k ∈ j.divisors, F k j :=
      _root_.RHTower.CriticalGibbs.sum_mulPairs_eq_sum_divisors N F
    _ = _ := by
      refine sum_congr rfl fun j _ => ?_
      dsimp only [F, H]
      rw [← sum_mul, ← sum_div]
      ring

/-- Normalized autocorrelation depends only on the log-gap in units of the atom width. -/
theorem normalized_bumpCorr_atomDilate {φ : ℝ → ℝ} {w : ℝ} (hw : 0 < w) (s : ℝ) :
    bumpCorr (atomDilate φ w) s / (∫ u, atomDilate φ w u ^ 2) =
      shellAutocorr φ (|s| / w) / (∫ u, φ u ^ 2) := by
  have h := integral_atomDilate_mul_shift (φ := φ) hw (-s)
  simp only [sub_neg_eq_add, neg_div, shellAutocorr_neg] at h
  change bumpCorr (atomDilate φ w) s = w * shellAutocorr φ (s / w) at h
  have heven : shellAutocorr φ (s / w) = shellAutocorr φ (|s| / w) := by
    rcases le_or_gt 0 s with hs | hs
    · rw [abs_of_nonneg hs]
    · rw [abs_of_neg hs, neg_div, shellAutocorr_neg]
  rw [h, heven, integral_atomDilate_sq hw, mul_div_mul_left _ _ hw.ne']

/-- The bounded row is exactly near Gamma minus the literal interior downward prime row. -/
theorem nearGammaDownwardRow_eq_actual_difference {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (m n : ℕ) :
    nearGammaDownwardRow φ c N m n =
      (∑ j ∈ nearRowIndices c N n,
        atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) *
          ramanujanLagCoefficient m j / Real.sqrt j) -
        interiorDownwardPrimeRow (atomDilate φ (c / N)) N m n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨-, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw
  have hprime : interiorDownwardPrimeRow (atomDilate φ (c / N)) N m n =
      ∑ j ∈ nearRowIndices c N n,
        shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
          (∑ d ∈ j.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) *
            ramanujanLagCoefficient m (j / d)) / Real.sqrt j := by
    rw [interiorDownwardPrimeRow_eq_divisors, nearRowIndices, sum_filter]
    refine sum_congr rfl fun j _ => ?_
    by_cases hnear : j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * c / N
    · rw [if_pos hnear, if_neg hnear.1, normalized_bumpCorr_atomDilate hw]
    · rw [if_neg hnear]
      by_cases hjeq : j = n
      · rw [if_pos hjeq, zero_div, zero_mul, zero_div]
      · rw [if_neg hjeq]
        have hgap : c / N < |Real.log j - Real.log n| := by
          have hgt : 2 * c / N < |Real.log j - Real.log n| :=
            lt_of_not_ge (fun h => hnear ⟨hjeq, h⟩)
          have : 2 * c / N = 2 * (c / N) := by ring
          linarith only [hgt, this, hw]
        rw [bumpCorr_eq_zero hgsupp hgap, zero_div, zero_mul, zero_div]
  rw [hprime, ← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by unfold nearGammaDownwardCoefficient; ring

/-- Logarithmic normalization removes the entire signed interior near-row residual. -/
theorem tendsto_nearGammaDownwardRow_sq_div_log {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, nearGammaDownwardRow φ c N m n ^ 2) / Real.log N) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_nearGammaDownwardRow_sq_bound hφ hsupp hM hc m
  have hlim : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Real.log_natCast_nonneg N)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈3 * c⌉₊] with N hN hNbig
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcN : 3 * c ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNbig)
  have hw : c / N ≤ 1 / 3 := (div_le_iff₀ hN0).mpr (by linarith only [hcN])
  exact div_le_div_of_nonneg_right (hbound N hN hw) (Real.log_natCast_nonneg N)

/-- The signed row difference on the logarithmically normalized conductor profile. -/
def normalizedNearGammaDownwardVector (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N))

theorem normalizedNearGammaDownwardVector_norm_sq (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    ‖normalizedNearGammaDownwardVector φ c N m‖ ^ 2 =
      (∑ n ∈ Icc 1 N, nearGammaDownwardRow φ c N m n ^ 2) / Real.log N := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ n : PrimeHorizonIndex N,
    (nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N)) ^ 2) = _
  simp only [div_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← sum_div]
  congr 1
  exact sum_coe_sort (Icc 1 N) (fun n => nearGammaDownwardRow φ c N m n ^ 2)

/-- Near Gamma and interior downward prime terms cancel in coefficient norm. -/
theorem tendsto_normalizedNearGammaDownwardVector_norm {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Tendsto (fun N : ℕ => ‖normalizedNearGammaDownwardVector φ c N m‖) atTop (𝓝 0) := by
  have h := (tendsto_nearGammaDownwardRow_sq_div_log hφ hsupp hM hc m).sqrt
  simpa only [← normalizedNearGammaDownwardVector_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using h

/-- The explicit boosted spline has the signed near-row cancellation at every fixed overlap. -/
theorem tendsto_tiltedUnitSpline_nearGammaDownward_norm {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Tendsto (fun N : ℕ => ‖normalizedNearGammaDownwardVector tiltedUnitSpline c N m‖)
      atTop (𝓝 0) :=
  tendsto_normalizedNearGammaDownwardVector_norm contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc m

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.interiorDownwardPrimeRow_eq_divisors
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.nearGammaDownwardRow_eq_actual_difference
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_nearGammaDownwardRow_sq_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_tiltedUnitSpline_nearGammaDownward_norm
