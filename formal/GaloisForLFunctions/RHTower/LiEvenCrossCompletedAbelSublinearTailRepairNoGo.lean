import GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelFiniteCriticalPrefixOscillationNoGo

/-!
# Sublinear-tail repair no-go for the even Li completed-Abel current

This module strengthens finite critical-prefix sign oscillation to a linear-scale obstruction.
Every nonempty finite packet of genuine critical-line Xi copies has completed-Abel adjacent-current
excursions larger than `c (n+1)` in both signs, cofinally in the Li mode, for some packet-dependent
`c > 0`. Consequently no real correction `R` with `R(n)/(n+1) → 0` can make the repaired current
nonnegative in every mode.

Exact RH proof strategy killed:

finite critical prefix plus an `o(n)` tail repair
`=>` LI-CAB5 completed-Abel current nonnegativity
`=>` LI-CAB3
`=>` RH.

Positive survivor: any viable infinite LI-CAB5 tail must supply cofinal linear-size countercurrent
against every fixed nonempty critical prefix. Infinite-tail cancellation is quantitatively
essential, not merely nonuniform.

All statements are unconditional. Repeated zeros and arbitrary rational relations among their
phases are allowed. No zero ordinate, RH assumption, or numerical computation is used.
-/

open Polynomial Real Filter Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A nonempty finite positive sine packet has excursions separated uniformly from zero in both
signs above every mode threshold. Delayed simultaneous recurrence needs no rational independence. -/
theorem cofinal_uniform_excursions_finitePositiveSinePacket
    {d : ℕ} (hd : 0 < d) {a omega : Fin d → ℝ}
    (ha : ∀ i, 0 < a i) (homega0 : ∀ i, 0 < omega i)
    (homegaPi : ∀ i, omega i < Real.pi) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ,
      (∃ m : ℕ, N ≤ m ∧ c < finitePositiveSinePacket a omega m) ∧
        ∃ m : ℕ, N ≤ m ∧ finitePositiveSinePacket a omega m < -c := by
  let delta := finitePositiveSinePacket a omega 1
  let A := ∑ i, a i
  have hdelta : 0 < delta := finitePositiveSinePacket_one_pos hd ha homega0 homegaPi
  have hA : 0 < A := finitePositiveSinePacket_weightSum_pos hd ha
  refine ⟨delta / 2, by positivity, ?_⟩
  intro N
  have hepsilon : 0 < delta / (4 * Real.pi * A) := by positivity
  obtain ⟨Q, hQ⟩ := exists_nat_one_div_lt hepsilon
  obtain ⟨k, hkL, hkU, r, hphase⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative
      (d := d) (Q := Q) (L := N + 2) omega
  have hk1 : 1 ≤ k := by omega
  have hbudget : A * (2 * Real.pi / (Q + 1 : ℝ)) < delta / 2 := by
    have hmul := mul_lt_mul_of_pos_left hQ
      (show 0 < 4 * Real.pi * A by positivity)
    field_simp at hmul ⊢
    nlinarith [Real.pi_pos, hA]
  have hplus := finitePositiveSinePacket_phase_recurrence_close
    (a := a) (ω := omega) (r := r) (ε := 2 * Real.pi / (Q + 1 : ℝ))
    (fun i => (ha i).le) hphase
  have hminus := finitePositiveSinePacket_phase_recurrence_close_neg hk1
    (a := a) (ω := omega) (r := r) (ε := 2 * Real.pi / (Q + 1 : ℝ))
    (fun i => (ha i).le) hphase
  constructor
  · refine ⟨k + 1, by omega, ?_⟩
    have hlower := (abs_le.mp hplus).1
    dsimp [delta, A] at hbudget hlower ⊢
    linarith
  · refine ⟨k - 1, by omega, ?_⟩
    have hupper := (abs_le.mp hminus).2
    dsimp [delta, A] at hbudget hupper ⊢
    linarith

/-- Every nonempty finite critical packet has cofinal positive and negative excursions of linear
size in the Li mode. -/
theorem cofinal_linear_excursions_liEvenCrossCriticalPacketCurrent
    {d : ℕ} (hd : 0 < d) {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : Fin d → XiCriticalLineResolventCopy) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ,
      (∃ n : ℕ, N ≤ n ∧
        c * ((n : ℝ) + 1) < liEvenCrossCriticalPacketCurrent v q n) ∧
      ∃ n : ℕ, N ≤ n ∧
        liEvenCrossCriticalPacketCurrent v q n < -c * ((n : ℝ) + 1) := by
  let a : Fin d → ℝ := fun i => liEvenCrossCriticalAtomAmplitude v (q i)
  let omega : Fin d → ℝ := fun i => liEvenCrossCriticalAtomFrequency v (q i)
  have ha : ∀ i, 0 < a i := fun i => liEvenCrossCriticalAtomAmplitude_pos hv0 hv4 (q i)
  have homega0 : ∀ i, 0 < omega i := fun i =>
    (liEvenCrossCriticalAtomFrequency_mem hv0 hv4 (q i)).1
  have homegaPi : ∀ i, omega i < Real.pi := fun i =>
    (liEvenCrossCriticalAtomFrequency_mem hv0 hv4 (q i)).2
  obtain ⟨c, hc, hexc⟩ :=
    cofinal_uniform_excursions_finitePositiveSinePacket hd ha homega0 homegaPi
  refine ⟨c, hc, ?_⟩
  intro N
  obtain ⟨⟨mpos, hmposN, hmpos⟩, ⟨mneg, hmnegN, hmneg⟩⟩ := hexc (N + 1)
  have hmpos1 : 1 ≤ mpos := by omega
  have hmneg1 : 1 ≤ mneg := by omega
  constructor
  · refine ⟨mpos - 1, by omega, ?_⟩
    rw [liEvenCrossCriticalPacketCurrent_eq_sinePacket hv0 hv4]
    have hindex : mpos - 1 + 1 = mpos := Nat.sub_add_cancel hmpos1
    rw [hindex]
    have hcast : (((mpos - 1 : ℕ) : ℝ) + 1) = (mpos : ℝ) := by
      rw [Nat.cast_sub hmpos1]
      push_cast
      ring
    rw [hcast]
    have hmposReal : 0 < (mpos : ℝ) := by exact_mod_cast hmpos1
    have hmpos' : c < finitePositiveSinePacket a omega mpos := hmpos
    simpa only [a, omega, mul_comm] using mul_lt_mul_of_pos_left hmpos' hmposReal
  · refine ⟨mneg - 1, by omega, ?_⟩
    rw [liEvenCrossCriticalPacketCurrent_eq_sinePacket hv0 hv4]
    have hindex : mneg - 1 + 1 = mneg := Nat.sub_add_cancel hmneg1
    rw [hindex]
    have hcast : (((mneg - 1 : ℕ) : ℝ) + 1) = (mneg : ℝ) := by
      rw [Nat.cast_sub hmneg1]
      push_cast
      ring
    rw [hcast]
    have hmnegReal : 0 < (mneg : ℝ) := by exact_mod_cast hmneg1
    have hmneg' : finitePositiveSinePacket a omega mneg < -c := hmneg
    simpa only [a, omega, mul_comm] using mul_lt_mul_of_pos_left hmneg' hmnegReal

/-- **Positive survivor.** Every all-mode nonnegative repair of a nonempty critical packet must
supply cofinal linear-size positive countercurrent. -/
theorem cofinal_linear_tail_forced_of_all_nonnegative
    {d : ℕ} (hd : 0 < d) {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : Fin d → XiCriticalLineResolventCopy) (R : ℕ → ℝ)
    (hnonneg : ∀ n : ℕ, 0 ≤ liEvenCrossCriticalPacketCurrent v q n + R n) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      c * ((n : ℝ) + 1) < R n := by
  obtain ⟨c, hc, hexc⟩ :=
    cofinal_linear_excursions_liEvenCrossCriticalPacketCurrent hd hv0 hv4 q
  refine ⟨c, hc, ?_⟩
  intro N
  obtain ⟨n, hnN, hnneg⟩ := (hexc N).2
  refine ⟨n, hnN, ?_⟩
  linarith [hnonneg n]

/-- No sublinear real correction can make a nonempty finite critical packet nonnegative in every
Li mode. -/
theorem not_exists_sublinearCorrection_all_nonnegative
    {d : ℕ} (hd : 0 < d) {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : Fin d → XiCriticalLineResolventCopy) :
    ¬ ∃ R : ℕ → ℝ,
      Tendsto (fun n : ℕ => R n / ((n : ℝ) + 1)) atTop (nhds 0) ∧
        ∀ n : ℕ, 0 ≤ liEvenCrossCriticalPacketCurrent v q n + R n := by
  rintro ⟨R, hR, hnonneg⟩
  obtain ⟨c, hc, hforced⟩ :=
    cofinal_linear_tail_forced_of_all_nonnegative hd hv0 hv4 q R hnonneg
  have heventually : ∀ᶠ n : ℕ in atTop, R n / ((n : ℝ) + 1) < c :=
    hR.eventually (Iio_mem_nhds hc)
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  obtain ⟨n, hnN, hnlarge⟩ := hforced N
  have hratio := hN n hnN
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hsmall : R n < c * ((n : ℝ) + 1) := (div_lt_iff₀ hden).mp hratio
  linarith

/-- **Closed LI-CAB8 route kill.** No admissible completed-Abel mass, nonempty genuine critical
packet, and sublinear real correction can produce all-mode nonnegativity. -/
theorem not_exists_nonempty_finiteCriticalPacket_sublinearRepair_all_nonnegative :
    ¬ ∃ v : ℝ, ∃ d : ℕ, ∃ q : Fin d → XiCriticalLineResolventCopy,
      0 < v ∧ v ≤ 1 / 4 ∧ 0 < d ∧
      ∃ R : ℕ → ℝ,
        Tendsto (fun n : ℕ => R n / ((n : ℝ) + 1)) atTop (nhds 0) ∧
          ∀ n : ℕ, 0 ≤ liEvenCrossCriticalPacketCurrent v q n + R n := by
  rintro ⟨v, d, q, hv0, hv4, hd, R, hR, hnonneg⟩
  exact not_exists_sublinearCorrection_all_nonnegative hd hv0 hv4 q
    ⟨R, hR, hnonneg⟩

end

end RHTower
