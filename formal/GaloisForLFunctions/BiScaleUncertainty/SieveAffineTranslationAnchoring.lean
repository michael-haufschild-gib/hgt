import GaloisForLFunctions.BiScaleUncertainty.SieveCanonicalTranslation

/-!
# Exact arithmetic anchoring of sieve translations

Fifth and sixth translated moments leave only the explicit canonical companion.
Labelled affine moments remove it exactly when an active divisor edge joins the
highest two-adic class to a lower one. This classifies the complete observation
fibre and absolute recovery for every real sieve, including vanishing modes.
Every surviving nontrivial ambiguity has an actual indistinguishable witness.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ValuationPhase
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false

/-- An active divisibility edge crossing from the greatest valuation to a lower one. -/
def HasAnchor (N : ℕ) (c : ℕ → ℝ) : Prop :=
  ∃ q ∈ Finset.Icc 1 N, ∃ d ∈ q.divisors,
    q.factorization 2 = activeDepth N c ∧ d.factorization 2 < activeDepth N c ∧
      selbergMultiplesCoord N c q ≠ 0 ∧ selbergMultiplesCoord N c d ≠ 0

/-- Literal affine data together with translated moments of orders five and six. -/
def SameObservations (N : ℕ) (c e : ℕ → ℝ) : Prop :=
  (∀ a b, affineMoment N c a b = affineMoment N e a b) ∧
    (∀ h : Fin 5 → ℕ, translatedMoment N c h = translatedMoment N e h) ∧
    (∀ h : Fin 6 → ℕ, translatedMoment N c h = translatedMoment N e h)

private theorem divisor_in_cutoff {N q d : ℕ} (hq : q ∈ Finset.Icc 1 N)
    (hd : d ∈ q.divisors) : d ∈ Finset.Icc 1 N :=
  Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
    (Nat.le_of_dvd (Finset.mem_Icc.mp hq).1 (Nat.mem_divisors.mp hd).1).trans
      (Finset.mem_Icc.mp hq).2⟩

/-- Affine observations remove the canonical ambiguity exactly when a crossing edge is active. -/
theorem affineMoment_companion_iff (N : ℕ) (c : ℕ → ℝ) :
    (∀ a b, affineMoment N c a b = affineMoment N (companion N c) a b) ↔
      ¬HasAnchor N c := by
  rw [companion, HalfPeriod.affineMoment_reflection_iff]
  constructor
  · intro hdata ha
    obtain ⟨q, hq, d, hd, hqV, hdV, hcq, hcd⟩ := ha
    have hV : 0 < activeDepth N c := by omega
    have hqnot : ¬q ∣ canonicalShift N c := by
      rw [canonicalShift, dvd_dyadicPeriod_iff hq]
      omega
    have hdyes : d ∣ canonicalShift N c := by
      rw [canonicalShift, dvd_dyadicPeriod_iff (divisor_in_cutoff hq hd)]
      omega
    exact (mul_ne_zero hcq hcd) (hdata q hq d hd hqnot hdyes)
  · intro hno q hq d hd hqnot hdyes
    by_cases hcq : selbergMultiplesCoord N c q = 0
    · rw [hcq, zero_mul]
    by_cases hcd : selbergMultiplesCoord N c d = 0
    · rw [hcd, mul_zero]
    exfalso
    apply hno
    have hb := depth_le_activeDepth N q c hq hcq
    rw [canonicalShift, dvd_dyadicPeriod_iff hq] at hqnot
    rw [canonicalShift, dvd_dyadicPeriod_iff (divisor_in_cutoff hq hd)] at hdyes
    exact ⟨q, hq, d, hd, by omega, by omega, hcq, hcd⟩

private theorem moments_of_coefficients (N : ℕ) (c e : ℕ → ℝ)
    (he : ∀ d ∈ Finset.Icc 1 N, c d = e d) :
    (∀ a b, affineMoment N c a b = affineMoment N e a b) ∧
      ∀ (m : ℕ) (h : Fin m → ℕ), translatedMoment N c h = translatedMoment N e h := by
  have hs : sieveSeq N c = sieveSeq N e := by
    funext k
    unfold sieveSeq
    apply Finset.sum_congr rfl
    intro d hd
    exact he d (Finset.mem_filter.mp hd).1
  constructor
  · intro a b
    unfold affineMoment
    rw [hs]
  · intro m h
    unfold translatedMoment
    rw [hs]

private theorem observations_of_coefficients (N : ℕ) (c e : ℕ → ℝ)
    (he : ∀ d ∈ Finset.Icc 1 N, c d = e d) : SameObservations N c e := by
  obtain ⟨ha, hm⟩ := moments_of_coefficients N c e he
  exact ⟨ha, hm 5, hm 6⟩

private theorem observations_trans {N : ℕ} {c e b : ℕ → ℝ}
    (hce : SameObservations N c e) (heb : SameObservations N e b) :
    SameObservations N c b :=
  ⟨fun a z => (hce.1 a z).trans (heb.1 a z),
    fun v => (hce.2.1 v).trans (heb.2.1 v),
    fun v => (hce.2.2 v).trans (heb.2.2 v)⟩

/-- Fifth and sixth translated moments characterize the complete translation fibre. -/
theorem fifth_sixth_eq_iff (N : ℕ) (c e : ℕ → ℝ) :
    ((∀ h : Fin 5 → ℕ, translatedMoment N c h = translatedMoment N e h) ∧
      (∀ h : Fin 6 → ℕ, translatedMoment N c h = translatedMoment N e h)) ↔
      (∀ d ∈ Finset.Icc 1 N, e d = c d) ∨
        (∀ d ∈ Finset.Icc 1 N, e d = companion N c d) := by
  constructor
  · rintro ⟨h5, h6⟩
    exact coefficients_eq_or_companion_of_moments N c e h5 h6
  · intro he
    have hm : ∀ (m : ℕ) (h : Fin m → ℕ), translatedMoment N c h = translatedMoment N e h := by
      rcases he with he | he
      · exact (moments_of_coefficients N c e (fun d hd => (he d hd).symm)).2
      · intro m h
        exact (translatedMoment_companion N c h).symm.trans
          ((moments_of_coefficients N (companion N c) e
            (fun d hd => (he d hd).symm)).2 m h)
    exact ⟨hm 5, hm 6⟩

/-- Every translated order is already determined by orders five and six. -/
theorem all_translated_eq_iff_fifth_sixth (N : ℕ) (c e : ℕ → ℝ) :
    (∀ (m : ℕ) (h : Fin m → ℕ), translatedMoment N c h = translatedMoment N e h) ↔
      ((∀ h : Fin 5 → ℕ, translatedMoment N c h = translatedMoment N e h) ∧
        (∀ h : Fin 6 → ℕ, translatedMoment N c h = translatedMoment N e h)) := by
  constructor
  · intro h
    exact ⟨h 5, h 6⟩
  · intro h
    rcases (fifth_sixth_eq_iff N c e).mp h with he | he
    · exact (moments_of_coefficients N c e (fun d hd => (he d hd).symm)).2
    · intro m v
      exact (translatedMoment_companion N c v).symm.trans
        ((moments_of_coefficients N (companion N c) e
          (fun d hd => (he d hd).symm)).2 m v)

/-- Exact joint-data fibre: the original weights and, only without an anchor, their companion. -/
theorem sameObservations_iff (N : ℕ) (c e : ℕ → ℝ) :
    SameObservations N c e ↔
      (∀ d ∈ Finset.Icc 1 N, e d = c d) ∨
        (¬HasAnchor N c ∧ ∀ d ∈ Finset.Icc 1 N, e d = companion N c d) := by
  constructor
  · intro h
    rcases coefficients_eq_or_companion_of_moments N c e h.2.1 h.2.2 with he | he
    · exact Or.inl he
    · right
      refine ⟨(affineMoment_companion_iff N c).mp ?_, he⟩
      have hm := (moments_of_coefficients N e (companion N c) he).1
      exact fun a b => (h.1 a b).trans (hm a b)
  · rintro (he | ⟨hno, he⟩)
    · exact observations_of_coefficients N c e (fun d hd => (he d hd).symm)
    · apply observations_trans (e := companion N c)
      · exact ⟨(affineMoment_companion_iff N c).mpr hno,
          fun v => (translatedMoment_companion N c v).symm,
          fun v => (translatedMoment_companion N c v).symm⟩
      · exact observations_of_coefficients N (companion N c) e
          (fun d hd => (he d hd).symm)

/-- Absolute recovery holds exactly for odd support or an active arithmetic anchor. -/
theorem absolute_observability_iff (N : ℕ) (c : ℕ → ℝ) :
    (∀ e : ℕ → ℝ, SameObservations N c e → ∀ d ∈ Finset.Icc 1 N, e d = c d) ↔
      activeDepth N c = 0 ∨ HasAnchor N c := by
  constructor
  · intro h
    by_cases hV : activeDepth N c = 0
    · exact Or.inl hV
    · right
      by_contra hno
      have hdata := (sameObservations_iff N c (companion N c)).mpr
        (Or.inr ⟨hno, fun _ _ => rfl⟩)
      obtain ⟨d, hd, hne⟩ := companion_ne_of_depth_pos N c (Nat.pos_of_ne_zero hV)
      exact hne (h _ hdata d hd)
  · intro ha e hdata d hd
    rcases (sameObservations_iff N c e).mp hdata with he | ⟨hno, he⟩
    · exact he d hd
    · rcases ha with hV | ha
      · exact (he d hd).trans (companion_eq_of_depth_zero N c hV d hd)
      · exact (hno ha).elim

/-- The same fibre classification holds even with every translated moment available. -/
theorem same_all_observations_iff (N : ℕ) (c e : ℕ → ℝ) :
    ((∀ a b, affineMoment N c a b = affineMoment N e a b) ∧
      ∀ (m : ℕ) (h : Fin m → ℕ), translatedMoment N c h = translatedMoment N e h) ↔
      (∀ d ∈ Finset.Icc 1 N, e d = c d) ∨
        (¬HasAnchor N c ∧ ∀ d ∈ Finset.Icc 1 N, e d = companion N c d) := by
  rw [all_translated_eq_iff_fifth_sixth]
  exact sameObservations_iff N c e

/-- Complete affine and translated observations have the same exact recovery criterion. -/
theorem absolute_all_observability_iff (N : ℕ) (c : ℕ → ℝ) :
    (∀ e : ℕ → ℝ,
      ((∀ a b, affineMoment N c a b = affineMoment N e a b) ∧
        ∀ (m : ℕ) (h : Fin m → ℕ), translatedMoment N c h = translatedMoment N e h) →
      ∀ d ∈ Finset.Icc 1 N, e d = c d) ↔
      activeDepth N c = 0 ∨ HasAnchor N c := by
  simp only [all_translated_eq_iff_fifth_sixth]
  exact absolute_observability_iff N c

/-- A distinct actual sieve survives all observations exactly at positive unanchored depth. -/
theorem distinct_indistinguishable_iff (N : ℕ) (c : ℕ → ℝ) :
    (∃ e : ℕ → ℝ, (∃ d ∈ Finset.Icc 1 N, e d ≠ c d) ∧
      (∀ a b, affineMoment N c a b = affineMoment N e a b) ∧
      ∀ (m : ℕ) (h : Fin m → ℕ), translatedMoment N c h = translatedMoment N e h) ↔
      0 < activeDepth N c ∧ ¬HasAnchor N c := by
  constructor
  · rintro ⟨e, ⟨d, hd, hne⟩, ha, hm⟩
    have hno : ¬(activeDepth N c = 0 ∨ HasAnchor N c) := by
      intro hc
      exact hne ((absolute_all_observability_iff N c).mpr hc e ⟨ha, hm⟩ d hd)
    exact ⟨Nat.pos_of_ne_zero (fun hv => hno (Or.inl hv)),
      fun h => hno (Or.inr h)⟩
  · rintro ⟨hV, hno⟩
    exact ⟨companion N c, companion_ne_of_depth_pos N c hV,
      (affineMoment_companion_iff N c).mpr hno,
      fun _ h => (translatedMoment_companion N c h).symm⟩

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ValuationPhase
