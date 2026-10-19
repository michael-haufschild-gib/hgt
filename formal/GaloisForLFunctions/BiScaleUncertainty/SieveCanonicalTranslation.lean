import GaloisForLFunctions.BiScaleUncertainty.SieveValuationPhaseRecovery
import GaloisForLFunctions.BiScaleUncertainty.SieveHalfPeriodTranslation
import GaloisForLFunctions.BezoutValuationIncidence.TrueTranslationPredictionAndExactCompression

/-!
# The canonical remaining sieve translation

The odd part of the factorial period gives a shift which reverses precisely
the greatest positive active two-adic class. Existing gcd projection constructs
its actual divisor weights. The companion is an involution on the cutoff,
preserves every translated moment, and exhausts the fifth-and-sixth data fibre.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ValuationPhase
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false

/-- Retain the common odd period and prescribe its two-adic depth. -/
def dyadicPeriod (N k : ℕ) : ℕ :=
  2^k * (N.factorial / 2^(N.factorial.factorization 2))

/-- Divisibility by this period tests precisely the two-adic exponent. -/
theorem dvd_dyadicPeriod_iff {N q k : ℕ} (hq : q ∈ Finset.Icc 1 N) :
    q ∣ dyadicPeriod N k ↔ q.factorization 2 ≤ k := by
  have hq0 : q ≠ 0 := (show 0 < q from (Finset.mem_Icc.mp hq).1).ne'
  have hO : N.factorial / 2^(N.factorial.factorization 2) ≠ 0 :=
    (Nat.ordCompl_pos 2 (Nat.factorial_ne_zero N)).ne'
  have hpow : 2^k ≠ 0 := pow_ne_zero _ Nat.prime_two.ne_zero
  have hD : dyadicPeriod N k ≠ 0 := mul_ne_zero hpow hO
  have hdepth : (dyadicPeriod N k).factorization 2 = k := by
    unfold dyadicPeriod
    rw [Nat.factorization_mul hpow hO, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd
        (Nat.not_dvd_ordCompl Nat.prime_two (Nat.factorial_ne_zero N))]
    exact Nat.add_zero k
  constructor
  · intro hd
    simpa only [hdepth] using ((Nat.factorization_le_iff_dvd hq0 hD).mpr hd 2)
  · intro hk
    have hqN : q ∣ N.factorial :=
      Nat.dvd_factorial (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
    have ho := Nat.ordCompl_dvd_ordCompl_of_dvd hqN 2
    have hd := Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 hk) ho
    simpa only [Nat.ordProj_mul_ordCompl_eq_self, dyadicPeriod] using hd

/-- The half-period which changes the highest active valuation class. -/
def canonicalShift (N : ℕ) (c : ℕ → ℝ) : ℕ :=
  dyadicPeriod N (activeDepth N c - 1)

/-- Actual divisor weights of the remaining translated companion. -/
def companion (N : ℕ) (c : ℕ → ℝ) : ℕ → ℝ :=
  HalfPeriod.reflection N (canonicalShift N c) c

private theorem periodic_of_coordinate_orders (N h : ℕ) (c : ℕ → ℝ)
    (hc : ∀ q ∈ Finset.Icc 1 N, selbergMultiplesCoord N c q ≠ 0 → q ∣ h) :
    Function.Periodic (sieveSeq N c) h := by
  apply (sieveGcdProjection_eq_zero_stride_iff N h c).mp
  have he : ∀ q ∈ Finset.Icc 1 N,
      selbergMultiplesCoord N (sieveGcdProjection N h c) q =
        selbergMultiplesCoord N (sieveGcdProjection N 0 c) q := by
    intro q hq
    rw [selbergMultiplesCoord_gcdProjection, selbergMultiplesCoord_gcdProjection,
      if_pos (dvd_zero q)]
    by_cases hz : selbergMultiplesCoord N c q = 0
    · simp [hz]
    · rw [if_pos (hc q hq hz)]
  have hw := (sieve_active_coefficients_eq_iff N _ _).mpr he
  funext d
  by_cases hd : d ∈ Finset.Icc 1 N
  · exact hw d hd
  · simp only [sieveGcdProjection, if_neg hd]

/-- Twice the canonical shift is always a true period, including zero support. -/
theorem periodic_twice_canonicalShift (N : ℕ) (c : ℕ → ℝ) :
    Function.Periodic (sieveSeq N c) (2 * canonicalShift N c) := by
  apply periodic_of_coordinate_orders
  intro q hq hc
  have he : 2 * canonicalShift N c = dyadicPeriod N (activeDepth N c - 1 + 1) := by
    unfold canonicalShift dyadicPeriod
    rw [pow_succ]
    ring
  rw [he, dvd_dyadicPeriod_iff hq]
  have hb := depth_le_activeDepth N q c hq hc
  omega

/-- The companion flips exactly the greatest positive active valuation class. -/
theorem coordinate_companion (N : ℕ) (c : ℕ → ℝ) (q : ℕ)
    (hq : q ∈ Finset.Icc 1 N) :
    selbergMultiplesCoord N (companion N c) q =
      if 0 < activeDepth N c ∧ q.factorization 2 = activeDepth N c
        then -selbergMultiplesCoord N c q else selbergMultiplesCoord N c q := by
  rw [companion, HalfPeriod.coordinate_reflection]
  change (if q ∣ dyadicPeriod N (activeDepth N c - 1) then _ else _) = _
  simp only [dvd_dyadicPeriod_iff hq]
  by_cases hc : selbergMultiplesCoord N c q = 0
  · simp [hc]
  · have hb := depth_le_activeDepth N q c hq hc
    split_ifs <;> first | rfl | omega

/-- Odd or empty active support has no second representative. -/
theorem companion_eq_of_depth_zero (N : ℕ) (c : ℕ → ℝ) (hV : activeDepth N c = 0) :
    ∀ d ∈ Finset.Icc 1 N, companion N c d = c d := by
  apply (sieve_active_coefficients_eq_iff N _ _).mpr
  intro q hq
  rw [coordinate_companion N c q hq, hV]
  simp

/-- The companion preserves the entire active coordinate support. -/
theorem activeModes_companion (N : ℕ) (c : ℕ → ℝ) :
    activeModes N (companion N c) = activeModes N c := by
  ext q
  by_cases hq : q ∈ Finset.Icc 1 N
  · simp only [activeModes, Finset.mem_filter, hq, true_and,
      coordinate_companion N c q hq]
    split_ifs <;> simp
  · simp only [activeModes, Finset.mem_filter, hq, false_and]

/-- The active depth, hence the chosen shift, is invariant under taking companions. -/
theorem activeDepth_companion (N : ℕ) (c : ℕ → ℝ) :
    activeDepth N (companion N c) = activeDepth N c := by
  unfold activeDepth
  rw [activeModes_companion]

/-- The two representatives form an involution on actual coefficients inside the cutoff. -/
theorem companion_involution (N : ℕ) (c : ℕ → ℝ) :
    ∀ d ∈ Finset.Icc 1 N, companion N (companion N c) d = c d := by
  apply (sieve_active_coefficients_eq_iff N _ _).mpr
  intro q hq
  rw [coordinate_companion N (companion N c) q hq, activeDepth_companion,
    coordinate_companion N c q hq]
  split_ifs <;> simp

/-- The coordinate companion is a literal translation of the original response. -/
theorem sieveSeq_companion (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq N (companion N c) k = sieveSeq N c (k + canonicalShift N c) :=
  HalfPeriod.sieveSeq_reflection N (canonicalShift N c) k c
    (periodic_twice_canonicalShift N c)

/-- The remaining companion preserves every translated moment, not only orders five and six. -/
theorem translatedMoment_companion (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (h : Fin m → ℕ) :
    translatedMoment N (companion N c) h = translatedMoment N c h :=
  HalfPeriod.translatedMoment_reflection N (canonicalShift N c) c
    (periodic_twice_canonicalShift N c) h

/-- Positive active depth makes the companion differ on the cutoff. -/
theorem companion_ne_of_depth_pos (N : ℕ) (c : ℕ → ℝ) (hV : 0 < activeDepth N c) :
    ∃ d ∈ Finset.Icc 1 N, companion N c d ≠ c d := by
  obtain ⟨q, hq, hc, hqV⟩ := exists_at_activeDepth N c hV
  by_contra hn
  have hw : ∀ d ∈ Finset.Icc 1 N, companion N c d = c d := by
    intro d hd
    by_contra he
    exact hn ⟨d, hd, he⟩
  have he := (sieve_active_coefficients_eq_iff N _ _).mp hw q hq
  rw [coordinate_companion N c q hq, if_pos ⟨hV, hqV⟩] at he
  exact hc (by linarith)

/-- Fifth and sixth data determine actual weights up to this one explicit companion. -/
theorem coefficients_eq_or_companion_of_moments (N : ℕ) (c e : ℕ → ℝ)
    (h5 : ∀ v : Fin 5 → ℕ, translatedMoment N c v = translatedMoment N e v)
    (h6 : ∀ v : Fin 6 → ℕ, translatedMoment N c v = translatedMoment N e v) :
    (∀ d ∈ Finset.Icc 1 N, e d = c d) ∨
      (∀ d ∈ Finset.Icc 1 N, e d = companion N c d) := by
  rcases coordinates_eq_or_highest_flip N c e h5 h6 with he | ⟨hV, he⟩
  · exact Or.inl ((sieve_active_coefficients_eq_iff N e c).mpr he)
  · right
    apply (sieve_active_coefficients_eq_iff N e (companion N c)).mpr
    intro q hq
    rw [he q hq, coordinate_companion N c q hq]
    simp only [hV, true_and]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ValuationPhase
