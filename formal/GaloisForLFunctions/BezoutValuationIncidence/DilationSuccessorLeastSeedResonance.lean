import GaloisForLFunctions.BezoutValuationIncidence.DilationSuccessorSectorHarmonicClassification
import GaloisForLFunctions.RHTower.Sieve.StadlmannReciprocalPhaseApplications

/-!
# Least-successor resonance inside the actual dilation profile

The existing finite successor-fiber formula and CGL totient bound isolate the
least positive solution of `p*a = q*b+1` at horizon `r*p*q`. Its normalized
contribution has error at most `r*phi(r)^2/sqrt(p*q)`. The original profile
retains this arithmetic seed with uniform inverse-scale error, while every
other lag remains in the signed finite complement at the same physical horizon.
No estimate for that complement or for an unmodified prime packet is asserted.
-/

open Finset RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- The existing CGL totient bound controls every affine successor amplitude. -/
theorem abs_successorFiberAmplitude_le_totient_sq
    (Q : CGLPositiveModulus) (p q a b t : ℕ) :
    |successorFiberAmplitude Q.value p q a b t| ≤ (Q.value.totient : ℝ) ^ 2 := by
  have hc (n : ℕ) : |(d4BMRamanujanNaturalCoefficient n Q.value).re| ≤
      (Q.value.totient : ℝ) := by
    apply (Complex.abs_re_le_norm _).trans
    simpa only [d4BMRamanujanNaturalCoefficient, dif_pos Q.positive] using
      Sieve.norm_cglRamanujanAdditiveSum_le_totient Q.value (n : ZMod Q.value)
  rw [successorFiberAmplitude, abs_mul]
  calc
    _ ≤ (Q.value.totient : ℝ) * Q.value.totient :=
      mul_le_mul (hc _) (hc _) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- At one complete block, the scaled sector has literal reciprocal seed weights. -/
theorem successor_sector_one_block_scaled
    (Q : CGLPositiveModulus) {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ha : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (hab : p * a = q * b + 1) :
    (p : ℝ) * ramanujanDilationLagSector Q.value p q (p * q * Q.value) 1 =
      (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t /
        ((a : ℝ) + q * t)) -
      (p : ℝ) * (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t) /
        (((p * q * Q.value : ℕ) : ℝ) + 1) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have h := ramanujanDilationLagSector_one_eq_period_blocks Q hp hq ha haq hb hab 1
  simp only [Nat.mul_one, Nat.cast_one, one_mul] at h
  have ht (t : ℕ) : (p : ℝ) * (successorFiberAmplitude Q.value p q a b t *
      progressionHarmonicSum (p * q * Q.value) (p * (a + q * t)) 1) =
      successorFiberAmplitude Q.value p q a b t / ((a : ℝ) + q * t) := by
    simp only [progressionHarmonicSum, Finset.sum_range_one, Nat.cast_zero,
      zero_mul, zero_add, Nat.cast_mul, Nat.cast_add]
    have hden : (a : ℝ) + q * t ≠ 0 := by positivity
    field_simp [hpR.ne', hden]
  rw [h, mul_sub, Finset.mul_sum]
  simp_rw [ht]
  ring

/-- The least positive solution controls the whole successor sector at quadratic horizon. -/
theorem abs_scaled_successor_sector_sub_seed_le
    (Q : CGLPositiveModulus) {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ha : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (hab : p * a = q * b + 1) :
    |(p : ℝ) * ramanujanDilationLagSector Q.value p q (p * q * Q.value) 1 -
      successorFiberAmplitude Q.value p q a b 0 / (a : ℝ)| ≤
      (Q.value : ℝ) * (Q.value.totient : ℝ) ^ 2 / (q : ℝ) := by
  let A : ℕ → ℝ := successorFiberAmplitude Q.value p q a b
  let M : ℝ := (Q.value.totient : ℝ) ^ 2
  have hM : 0 ≤ M := sq_nonneg _
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < Q.value := by exact_mod_cast Q.positive
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hA (t : ℕ) : |A t| ≤ M := abs_successorFiberAmplitude_le_totient_sq Q p q a b t
  have h0 : 0 ∈ range Q.value := Finset.mem_range.mpr Q.positive
  have htail : |∑ t ∈ (range Q.value).erase 0, A t / ((a : ℝ) + q * t)| ≤
      (((range Q.value).erase 0).card : ℝ) * M / q := by
    calc
      _ ≤ ∑ t ∈ (range Q.value).erase 0, |A t / ((a : ℝ) + q * t)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ (range Q.value).erase 0, M / q := by
        apply Finset.sum_le_sum
        intro t ht
        have htN : 1 ≤ t := by have := (Finset.mem_erase.mp ht).1; omega
        have htR : (1 : ℝ) ≤ t := by exact_mod_cast htN
        have hd : (q : ℝ) ≤ (a : ℝ) + q * t := by
          nlinarith [mul_le_mul_of_nonneg_left htR hqR.le]
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (a : ℝ) + q * t)]
        exact (div_le_div_of_nonneg_right (hA t) (by positivity)).trans
          (div_le_div_of_nonneg_left hM hqR hd)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hsum : |∑ t ∈ range Q.value, A t| ≤ (Q.value : ℝ) * M := by
    calc
      _ ≤ ∑ t ∈ range Q.value, |A t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ range Q.value, M := Finset.sum_le_sum fun t _ => hA t
      _ = _ := by simp
  have hboundary : |(p : ℝ) * (∑ t ∈ range Q.value, A t) /
      (((p * q * Q.value : ℕ) : ℝ) + 1)| ≤ M / q := by
    rw [abs_div, abs_mul, abs_of_pos hpR,
      abs_of_pos (by positivity : (0 : ℝ) < ((p * q * Q.value : ℕ) : ℝ) + 1)]
    calc
      _ ≤ (p : ℝ) * ((Q.value : ℝ) * M) /
          (((p * q * Q.value : ℕ) : ℝ) + 1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsum hpR.le) (by positivity)
      _ ≤ M / q := by
        apply (div_le_div_iff₀ (by positivity) hqR).mpr
        push_cast
        nlinarith
  have hsplit := Finset.sum_erase_add
    (s := range Q.value) (f := fun t => A t / ((a : ℝ) + q * t)) h0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hsplit
  have hcard : (((range Q.value).erase 0).card : ℝ) + 1 = (Q.value : ℝ) := by
    exact_mod_cast (show ((range Q.value).erase 0).card + 1 = Q.value from by
      simpa only [Finset.card_range] using Finset.card_erase_add_one h0)
  rw [successor_sector_one_block_scaled Q hp hq ha haq hb hab]
  change |(∑ t ∈ range Q.value, A t / ((a : ℝ) + q * t)) -
    (p : ℝ) * (∑ t ∈ range Q.value, A t) / (((p * q * Q.value : ℕ) : ℝ) + 1) -
    A 0 / a| ≤ (Q.value : ℝ) * M / q
  rw [← hsplit]
  have he : (∑ t ∈ (range Q.value).erase 0, A t / ((a : ℝ) + q * t)) + A 0 / a -
      (p : ℝ) * (∑ t ∈ range Q.value, A t) / (((p * q * Q.value : ℕ) : ℝ) + 1) - A 0 / a =
      (∑ t ∈ (range Q.value).erase 0, A t / ((a : ℝ) + q * t)) -
        (p : ℝ) * (∑ t ∈ range Q.value, A t) / (((p * q * Q.value : ℕ) : ℝ) + 1) := by ring
  rw [he]
  calc
    _ ≤ |∑ t ∈ (range Q.value).erase 0, A t / ((a : ℝ) + q * t)| +
        |(p : ℝ) * (∑ t ∈ range Q.value, A t) / (((p * q * Q.value : ℕ) : ℝ) + 1)| :=
      by simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (∑ t ∈ (range Q.value).erase 0, A t / ((a : ℝ) + q * t))
          (-((p : ℝ) * (∑ t ∈ range Q.value, A t) / (((p * q * Q.value : ℕ) : ℝ) + 1)))
    _ ≤ (((range Q.value).erase 0).card : ℝ) * M / q + M / q :=
      add_le_add htail hboundary
    _ = _ := by rw [← hcard]; ring

private theorem exists_successor_seed_pair {p q : ℕ}
    (h : 1 < p ∧ 1 < q ∧ Nat.Coprime p q) :
    ∃ ab : ℕ × ℕ, 1 ≤ ab.1 ∧ ab.1 ≤ q ∧ 1 ≤ ab.2 ∧ p * ab.1 = q * ab.2 + 1 := by
  obtain ⟨a, b, ha, haq, hb, hab⟩ := exists_successor_seed h.1 h.2.1 h.2.2
  exact ⟨(a, b), ha, haq, hb, hab⟩

/-- The intrinsic bounded positive successor seed; zero denotes a forbidden scale pair. -/
def leastSuccessorSeed (p q : ℕ) : ℕ × ℕ :=
  if h : 1 < p ∧ 1 < q ∧ Nat.Coprime p q then
    Classical.choose (exists_successor_seed_pair h)
  else (0, 0)

/-- The selected seed is the bounded positive solution supplied by the existing CRT theorem. -/
theorem leastSuccessorSeed_spec {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q) :
    1 ≤ (leastSuccessorSeed p q).1 ∧ (leastSuccessorSeed p q).1 ≤ q ∧
      1 ≤ (leastSuccessorSeed p q).2 ∧
      p * (leastSuccessorSeed p q).1 = q * (leastSuccessorSeed p q).2 + 1 := by
  rw [leastSuccessorSeed, dif_pos ⟨hp, hq, hpq⟩]
  exact Classical.choose_spec (exists_successor_seed_pair ⟨hp, hq, hpq⟩)

/-- The arithmetic resonance carried by the least positive successor pair. -/
def successorLeastSeedResonance (r p q : ℕ) : ℝ :=
  (d4BMRamanujanNaturalCoefficient (leastSuccessorSeed p q).1 r).re *
    (d4BMRamanujanNaturalCoefficient (leastSuccessorSeed p q).2 r).re /
      ((leastSuccessorSeed p q).1 : ℝ)

/-- Seed isolation also covers noncoprime scales, whose successor sector is empty. -/
theorem abs_scaled_successor_sector_sub_leastSeed_le
    (Q : CGLPositiveModulus) {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    |(p : ℝ) * ramanujanDilationLagSector Q.value p q (p * q * Q.value) 1 -
      successorLeastSeedResonance Q.value p q| ≤
      (Q.value : ℝ) * (Q.value.totient : ℝ) ^ 2 / (q : ℝ) := by
  by_cases hpq : Nat.Coprime p q
  · obtain ⟨ha, haq, hb, hab⟩ := leastSuccessorSeed_spec hp hq hpq
    have h := abs_scaled_successor_sector_sub_seed_le Q
      (by omega : 0 < p) (by omega : 0 < q) ha haq hb hab
    simpa only [successorLeastSeedResonance, successorFiberAmplitude,
      Nat.mul_zero, Nat.add_zero] using h
  · have hd : ¬(Nat.gcd p q : ℤ) ∣ 1 := by
      intro h
      have hN : Nat.gcd p q ∣ 1 := by exact_mod_cast h
      exact hpq (Nat.dvd_one.mp hN)
    rw [ramanujanDilationLagSector_eq_zero_of_not_dvd Q.value p q (p * q * Q.value) 1 hd]
    have hbad : ¬(1 < p ∧ 1 < q ∧ Nat.Coprime p q) := fun h => hpq h.2.2
    simpa [successorLeastSeedResonance, leastSuccessorSeed, hbad] using
      (show (0 : ℝ) ≤ (Q.value : ℝ) * (Q.value.totient : ℝ) ^ 2 / (q : ℝ) by positivity)

/-- The actual Hilbert normalization retains the least-seed resonance with inverse-scale error. -/
theorem abs_normalized_successor_sector_sub_leastSeed_le
    (Q : CGLPositiveModulus) {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    |Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        ramanujanDilationLagSector Q.value p q (p * q * Q.value) 1 -
      (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) * successorLeastSeedResonance Q.value p q| ≤
      (Q.value : ℝ) * (Q.value.totient : ℝ) ^ 2 /
        (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpS : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpR
  have hqS : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqR
  have hpSq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := by
    nlinarith [Real.sq_sqrt hpR.le]
  have hqSq : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) := by
    nlinarith [Real.sq_sqrt hqR.le]
  have hfac : 0 ≤ Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ) := div_nonneg hqS.le hpS.le
  have hfacp : (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) * (p : ℝ) =
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) := by
    calc
      _ = (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
          (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) := congrArg
            (fun x : ℝ => (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) * x) hpSq.symm
      _ = _ := by field_simp [hpS.ne']
  have he : Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        ramanujanDilationLagSector Q.value p q (p * q * Q.value) 1 -
      (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) * successorLeastSeedResonance Q.value p q =
      (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
        ((p : ℝ) * ramanujanDilationLagSector Q.value p q (p * q * Q.value) 1 -
          successorLeastSeedResonance Q.value p q) := by
    rw [mul_sub, ← mul_assoc, hfacp]
  rw [he, abs_mul, abs_of_nonneg hfac]
  calc
    _ ≤ (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
        ((Q.value : ℝ) * (Q.value.totient : ℝ) ^ 2 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left (abs_scaled_successor_sector_sub_leastSeed_le Q hp hq) hfac
    _ = (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
        ((Q.value : ℝ) * (Q.value.totient : ℝ) ^ 2 /
          (Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ))) := congrArg
            (fun x : ℝ => (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
              ((Q.value : ℝ) * (Q.value.totient : ℝ) ^ 2 / x)) hqSq.symm
    _ = _ := by field_simp [hpS.ne', hqS.ne']

/-- Replace exactly the successor sector inside the original profile; retain every other signed lag. -/
theorem abs_dilationProfile_sub_leastSeed_and_other_sectors_le
    {r p q : ℕ} (hr : 1 < r) (hp : 1 < p) (hq : 1 < q) :
    |pmRamanujanDilationProfile r hr ((p : ℝ) / q) -
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          ((∑ h ∈ (dilationJumpPairs (p * q * r) p q).image (dilationJumpGap p q),
            ramanujanDilationLagSector r p q (p * q * r) h) -
              ramanujanDilationLagSector r p q (p * q * r) 1) -
        (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) * successorLeastSeedResonance r p q| ≤
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          (pmRamanujanPrimitiveBound r ^ 2 / (((p * q * r : ℕ) : ℝ) + 1)) +
        (r : ℝ) * (r.totient : ℝ) ^ 2 / (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by
  have hprofile := abs_dilationProfile_sub_finite_lag_sectors_le hr
    (by omega : 0 < p) (by omega : 0 < q) (p * q * r)
  have hsector := abs_normalized_successor_sector_sub_leastSeed_le
    ⟨r, by omega⟩ hp hq
  have he : pmRamanujanDilationProfile r hr ((p : ℝ) / q) -
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          ((∑ h ∈ (dilationJumpPairs (p * q * r) p q).image (dilationJumpGap p q),
            ramanujanDilationLagSector r p q (p * q * r) h) -
              ramanujanDilationLagSector r p q (p * q * r) 1) -
        (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) * successorLeastSeedResonance r p q =
      (pmRamanujanDilationProfile r hr ((p : ℝ) / q) -
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          (∑ h ∈ (dilationJumpPairs (p * q * r) p q).image (dilationJumpGap p q),
            ramanujanDilationLagSector r p q (p * q * r) h)) +
      (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        ramanujanDilationLagSector r p q (p * q * r) 1 -
        (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) * successorLeastSeedResonance r p q) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hprofile hsector)

/-- No-hypothesis coupling for arbitrary integer scales above one, including all large prime pairs. -/
theorem dilation_profile_least_successor_seed_coupling (r n m : ℕ) :
    let R := r + 2
    let p := n + 2
    let q := m + 2
    let H := p * q * R
    |pmRamanujanDilationProfile R (by dsimp [R]; omega) ((p : ℝ) / q) -
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          ((∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
            ramanujanDilationLagSector R p q H h) - ramanujanDilationLagSector R p q H 1) -
        (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) * successorLeastSeedResonance R p q| ≤
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          (pmRamanujanPrimitiveBound R ^ 2 / ((H : ℝ) + 1)) +
        (R : ℝ) * (R.totient : ℝ) ^ 2 / (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by
  dsimp only
  exact abs_dilationProfile_sub_leastSeed_and_other_sectors_le (by omega) (by omega) (by omega)

private theorem profile_seed_error_le_div_sqrt
    {r p q : ℕ} (hr : 1 < r) (hp : 1 < p) (hq : 1 < q) :
    Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        (pmRamanujanPrimitiveBound r ^ 2 / (((p * q * r : ℕ) : ℝ) + 1)) +
      (r : ℝ) * (r.totient : ℝ) ^ 2 / (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) ≤
    (pmRamanujanPrimitiveBound r ^ 2 / (r : ℝ) + (r : ℝ) * (r.totient : ℝ) ^ 2) /
      (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  let w := Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)
  have hw : 0 < w := mul_pos (Real.sqrt_pos.mpr hpR) (Real.sqrt_pos.mpr hqR)
  have hH : ((p * q * r : ℕ) : ℝ) = (r : ℝ) * w ^ 2 := by
    dsimp only [w]
    rw [mul_pow, Real.sq_sqrt hpR.le, Real.sq_sqrt hqR.le]
    push_cast
    ring
  have ht : w * (pmRamanujanPrimitiveBound r ^ 2 / (((p * q * r : ℕ) : ℝ) + 1)) ≤
      pmRamanujanPrimitiveBound r ^ 2 / ((r : ℝ) * w) := by
    rw [hH, ← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (mul_pos hrR hw)).mpr
    nlinarith [sq_nonneg (pmRamanujanPrimitiveBound r)]
  change w * (pmRamanujanPrimitiveBound r ^ 2 / (((p * q * r : ℕ) : ℝ) + 1)) +
    (r : ℝ) * (r.totient : ℝ) ^ 2 / w ≤
    (pmRamanujanPrimitiveBound r ^ 2 / (r : ℝ) + (r : ℝ) * (r.totient : ℝ) ^ 2) / w
  calc
    _ ≤ pmRamanujanPrimitiveBound r ^ 2 / ((r : ℝ) * w) +
      (r : ℝ) * (r.totient : ℝ) ^ 2 / w := add_le_add ht le_rfl
    _ = _ := by field_simp [hrR.ne', hw.ne']

/-- Uniform inverse-scale error for the actual profile, with its arithmetic seed and signed complement. -/
theorem dilation_profile_least_successor_seed_uniform (r k n m : ℕ) :
    let R := r + 2
    let p := k + n + 2
    let q := k + m + 2
    let H := p * q * R
    |pmRamanujanDilationProfile R (by dsimp [R]; omega) ((p : ℝ) / q) -
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          ((∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
            ramanujanDilationLagSector R p q H h) - ramanujanDilationLagSector R p q H 1) -
        (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) * successorLeastSeedResonance R p q| ≤
      (pmRamanujanPrimitiveBound R ^ 2 / (R : ℝ) + (R : ℝ) * (R.totient : ℝ) ^ 2) /
        ((k + 2 : ℕ) : ℝ) := by
  dsimp only
  have hr : 1 < r + 2 := by omega
  have hp : 1 < k + n + 2 := by omega
  have hq : 1 < k + m + 2 := by omega
  have h := (abs_dilationProfile_sub_leastSeed_and_other_sectors_le hr hp hq).trans
    (profile_seed_error_le_div_sqrt hr hp hq)
  apply h.trans
  have hpmin : ((k + 2 : ℕ) : ℝ) ≤ ((k + n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show k + 2 ≤ k + n + 2 by omega)
  have hqmin : ((k + 2 : ℕ) : ℝ) ≤ ((k + m + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show k + 2 ≤ k + m + 2 by omega)
  have hden : ((k + 2 : ℕ) : ℝ) ≤
      Real.sqrt ((k + n + 2 : ℕ) : ℝ) * Real.sqrt ((k + m + 2 : ℕ) : ℝ) := by
    calc
      _ = Real.sqrt ((k + 2 : ℕ) : ℝ) * Real.sqrt ((k + 2 : ℕ) : ℝ) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) by positivity)]
      _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt hpmin) (Real.sqrt_le_sqrt hqmin)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

end
end GaloisForLFunctions.BezoutValuationIncidence
