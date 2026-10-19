import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiCompleteTraceValuationStability
import GaloisForLFunctions.TransHorizonIncidenceMechanics.RadicalCheckpointSignRigidityAndGaugeLaw

/-!
# Odd-trace centering and restrictions on physical Fermi extremizers

For `N ≥ 2`, the coefficient direction `e₂ - e₁` fixes every even sieve
reading and every selected even Fermi jump. Both complete physical energies
therefore change by the same quadratic in the odd pronic mean. Centering
minimizes this common quadratic and uniquely maximizes the energy ratio on
its shift orbit whenever the sieve energy exceeds the selected energy.

For nonnegative coefficients the admissible shift interval is exactly
`[-c 2, c 1]`; removing the unit coefficient cannot lower such a ratio.
The odd mean attains its unit-coefficient lower bound exactly when all
admitted odd coefficients above one vanish. Consequently a nonnegative
extremizer over all signed coefficients, with ratio greater than one,
must have every admitted odd coefficient zero.

The projection algebra is classical. The assertions here concern the
literal coefficient shift and the two existing physical trace energies.
-/

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

set_option autoImplicit false

open BezoutValuationIncidence
open scoped BigOperators

/-- Move weight from coefficient one to coefficient two. -/
noncomputable def fermiOddShiftWeight (c : ℕ → ℝ) (t : ℝ) : ℕ → ℝ :=
  sieveUnitShiftWeight (fun d => c d + if d = 2 then t else 0) (-t)

/-- Total reciprocal-pronic mass on positive odd integers. -/
noncomputable def fermiOddPronicMass : ℝ :=
  ∑' m : ℕ, 1 / (pronicSeq (2 * m + 1) : ℝ)

/-- Unnormalized odd pronic mean of the finite-horizon sieve response. -/
noncomputable def fermiOddPronicMean (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑' m : ℕ, sieveSeq N c (2 * m + 1) / (pronicSeq (2 * m + 1) : ℝ)

private theorem odd_mass_summable :
    Summable (fun m : ℕ => (1 : ℝ) / (pronicSeq (2 * m + 1) : ℝ)) := by
  have h := summable_div_pronicSeq_of_bounded (g := fun _ => (1 : ℝ))
    (B := 1) (by intro m; norm_num)
  exact h.comp_injective (i := fun m => 2 * m + 1)
    (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)

private theorem odd_mean_summable (N : ℕ) (c : ℕ → ℝ) :
    Summable (fun m : ℕ => sieveSeq N c (2 * m + 1) /
      (pronicSeq (2 * m + 1) : ℝ)) := by
  have h := summable_div_pronicSeq_of_bounded (abs_sieveSeq_le_sum_abs N c)
  exact h.comp_injective (i := fun m => 2 * m + 1)
    (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)

theorem fermiOddPronicMass_pos : 0 < fermiOddPronicMass := by
  have hs := odd_mass_summable.sum_le_tsum ({0} : Finset ℕ)
    (fun m _ => by positivity)
  have h : (1 : ℝ) / (pronicSeq 1 : ℝ) ≤ fermiOddPronicMass := by
    simpa only [Finset.sum_singleton, Nat.mul_zero, Nat.zero_add,
      fermiOddPronicMass] using hs
  exact lt_of_lt_of_le (by norm_num [pronicSeq]) h

theorem sieveSeq_fermiOddShiftWeight {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    sieveSeq N (fermiOddShiftWeight c t) n =
      sieveSeq N c n + (if 2 ∣ n then t else 0) - t := by
  unfold fermiOddShiftWeight
  rw [sieveSeq_unitShiftWeight (by omega : 1 ≤ N)]
  simp [sieveSeq, Finset.sum_add_distrib, hN, sub_eq_add_neg]

private theorem shifted_odd {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (t : ℝ) (m : ℕ) :
    sieveSeq N (fermiOddShiftWeight c t) (2 * m + 1) =
      sieveSeq N c (2 * m + 1) - t := by
  rw [sieveSeq_fermiOddShiftWeight hN]
  simp

private theorem shifted_even {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (t : ℝ) (m : ℕ) :
    sieveSeq N (fermiOddShiftWeight c t) (2 * m + 2) =
      sieveSeq N c (2 * m + 2) := by
  rw [sieveSeq_fermiOddShiftWeight hN]
  simp [show 2 ∣ 2 * m + 2 by omega]

private theorem shifted_selected_even {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (t : ℝ) (m : ℕ) :
    fermiBoundaryJump N (fermiOddShiftWeight c t) (4 * m + 4) =
      fermiBoundaryJump N c (4 * m + 4) := by
  rw [show 4 * m + 4 = 2 * (2 * m + 1) + 2 by omega]
  simp only [fermiBoundaryJump_even]
  rw [show 2 * m + 1 + 1 = 2 * m + 2 by omega]
  rw [shifted_even hN, shifted_even hN]

private theorem shifted_pair_energies {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (t : ℝ) (m : ℕ) :
    sievePairedPronicEnergy N (fermiOddShiftWeight c t) {m} =
        sievePairedPronicEnergy N c {m} -
          (2 * t) * (sieveSeq N c (2 * m + 1) / (pronicSeq (2 * m + 1) : ℝ)) +
          t^2 * (1 / (pronicSeq (2 * m + 1) : ℝ)) ∧
      fermiSelectedPronicEnergy N (fermiOddShiftWeight c t) {m} =
        fermiSelectedPronicEnergy N c {m} -
          (2 * t) * (sieveSeq N c (2 * m + 1) / (pronicSeq (2 * m + 1) : ℝ)) +
          t^2 * (1 / (pronicSeq (2 * m + 1) : ℝ)) := by
  constructor
  · simp only [sievePairedPronicEnergy, Finset.sum_singleton, shifted_odd hN, shifted_even hN]
    ring
  · simp only [fermiSelectedPronicEnergy, Finset.sum_singleton,
      fermiBoundaryJump_odd, shifted_odd hN, shifted_selected_even hN]
    ring

/-- Both complete physical energies receive the same exact quadratic correction. -/
theorem fermiOddShiftWeight_physical_energies {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (t : ℝ) :
    sieveTotalPronicEnergy N (fermiOddShiftWeight c t) =
        sieveTotalPronicEnergy N c - 2 * t * fermiOddPronicMean N c +
          t^2 * fermiOddPronicMass ∧
      fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t) =
        fermiSelectedTotalPronicEnergy N c - 2 * t * fermiOddPronicMean N c +
          t^2 * fermiOddPronicMass := by
  have hP := (sieve_fermi_pronic_summable N c).1
  have hQ := (sieve_fermi_pronic_summable N c).2
  have hA := (odd_mean_summable N c).mul_left (2 * t)
  have hT := odd_mass_summable.mul_left (t^2)
  constructor
  · change (∑' m, sievePairedPronicEnergy N (fermiOddShiftWeight c t) {m}) = _
    rw [tsum_congr (fun m => (shifted_pair_energies hN c t m).1),
      (hP.sub hA).tsum_add hT, hP.tsum_sub hA, tsum_mul_left, tsum_mul_left]
    rfl
  · change (∑' m, fermiSelectedPronicEnergy N (fermiOddShiftWeight c t) {m}) = _
    rw [tsum_congr (fun m => (shifted_pair_energies hN c t m).2),
      (hQ.sub hA).tsum_add hT, hQ.tsum_sub hA, tsum_mul_left, tsum_mul_left]
    rfl

/-- The physical energy difference is invariant along the shift orbit. -/
theorem fermiOddShiftWeight_energy_difference {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (t : ℝ) :
    sieveTotalPronicEnergy N (fermiOddShiftWeight c t) -
        fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t) =
      sieveTotalPronicEnergy N c - fermiSelectedTotalPronicEnergy N c := by
  obtain ⟨hP, hQ⟩ := fermiOddShiftWeight_physical_energies hN c t
  rw [hP, hQ]
  ring

theorem fermiOddPronicMean_shift {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) (t : ℝ) :
    fermiOddPronicMean N (fermiOddShiftWeight c t) =
      fermiOddPronicMean N c - t * fermiOddPronicMass := by
  change (∑' m : ℕ, sieveSeq N (fermiOddShiftWeight c t) (2 * m + 1) /
    (pronicSeq (2 * m + 1) : ℝ)) = _
  have hterm (m : ℕ) : sieveSeq N (fermiOddShiftWeight c t) (2 * m + 1) /
      (pronicSeq (2 * m + 1) : ℝ) =
    sieveSeq N c (2 * m + 1) / (pronicSeq (2 * m + 1) : ℝ) -
      t * (1 / (pronicSeq (2 * m + 1) : ℝ)) := by
    rw [shifted_odd hN]
    ring
  rw [tsum_congr hterm, (odd_mean_summable N c).tsum_sub (odd_mass_summable.mul_left t),
    tsum_mul_left]
  rfl

/-- The unique shift whose odd pronic mean vanishes. -/
noncomputable def fermiOddCenteredWeight (N : ℕ) (c : ℕ → ℝ) : ℕ → ℝ :=
  fermiOddShiftWeight c (fermiOddPronicMean N c / fermiOddPronicMass)

theorem fermiOddCenteredWeight_mean_zero {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    fermiOddPronicMean N (fermiOddCenteredWeight N c) = 0 := by
  rw [fermiOddCenteredWeight, fermiOddPronicMean_shift hN,
    div_mul_cancel₀ _ fermiOddPronicMass_pos.ne']
  ring

theorem fermiOddCenteredWeight_physical_energies {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    sieveTotalPronicEnergy N (fermiOddCenteredWeight N c) =
        sieveTotalPronicEnergy N c - (fermiOddPronicMean N c)^2 / fermiOddPronicMass ∧
      fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) =
        fermiSelectedTotalPronicEnergy N c -
          (fermiOddPronicMean N c)^2 / fermiOddPronicMass := by
  obtain ⟨hP, hQ⟩ := fermiOddShiftWeight_physical_energies hN c
    (fermiOddPronicMean N c / fermiOddPronicMass)
  constructor
  · rw [fermiOddCenteredWeight, hP]
    field_simp [fermiOddPronicMass_pos.ne']
    ring
  · rw [fermiOddCenteredWeight, hQ]
    field_simp [fermiOddPronicMass_pos.ne']
    ring

theorem fermiOddShiftWeight_centered_squares {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (t : ℝ) :
    sieveTotalPronicEnergy N (fermiOddShiftWeight c t) =
        sieveTotalPronicEnergy N (fermiOddCenteredWeight N c) +
          fermiOddPronicMass * (t - fermiOddPronicMean N c / fermiOddPronicMass)^2 ∧
      fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t) =
        fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) +
          fermiOddPronicMass * (t - fermiOddPronicMean N c / fermiOddPronicMass)^2 := by
  obtain ⟨hP, hQ⟩ := fermiOddShiftWeight_physical_energies hN c t
  obtain ⟨hPc, hQc⟩ := fermiOddCenteredWeight_physical_energies hN c
  constructor
  · rw [hP, hPc]
    field_simp [fermiOddPronicMass_pos.ne']
    ring
  · rw [hQ, hQc]
    field_simp [fermiOddPronicMass_pos.ne']
    ring

private theorem selected_pos_of_sieve_gt (N : ℕ) (c : ℕ → ℝ)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c) :
    0 < fermiSelectedTotalPronicEnergy N c := by
  have hQ : 0 ≤ fermiSelectedTotalPronicEnergy N c := by
    apply tsum_nonneg
    intro m
    simp only [fermiSelectedPronicEnergy, Finset.sum_singleton]
    positivity
  by_contra hn
  have hz : fermiSelectedTotalPronicEnergy N c = 0 := le_antisymm (le_of_not_gt hn) hQ
  have hbound := sieveTotalPronicEnergy_le_depth_selected N c
  dsimp only at hbound
  rw [hz, mul_zero] at hbound
  linarith

private theorem shifted_selected_pos {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c) (t : ℝ) :
    0 < fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t) := by
  apply selected_pos_of_sieve_gt
  have hd := fermiOddShiftWeight_energy_difference hN c t
  linarith

theorem fermiOddShiftWeight_selected_pos {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c) (t : ℝ) :
    0 < fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t) :=
  shifted_selected_pos hN c h t

theorem fermiOddCenteredWeight_selected_pos {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c) :
    0 < fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) :=
  shifted_selected_pos hN c h _

private theorem scalar_ratio_gap (p q x : ℝ) (hq : q ≠ 0) (hqx : q + x ≠ 0) :
    p / q - (p + x) / (q + x) = (p - q) * x / (q * (q + x)) := by
  field_simp
  ring

/-- Exact loss from the centered ratio at any other point of the shift orbit. -/
theorem fermiOddShiftWeight_ratio_gap {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c) (t : ℝ) :
    sieveTotalPronicEnergy N (fermiOddCenteredWeight N c) /
        fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) -
      sieveTotalPronicEnergy N (fermiOddShiftWeight c t) /
        fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t) =
      (sieveTotalPronicEnergy N c - fermiSelectedTotalPronicEnergy N c) *
        (fermiOddPronicMass * (t - fermiOddPronicMean N c / fermiOddPronicMass)^2) /
        (fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) *
          fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t)) := by
  have hc := fermiOddCenteredWeight_selected_pos hN c h
  have ht := shifted_selected_pos hN c h t
  obtain ⟨hP, hQ⟩ := fermiOddShiftWeight_centered_squares hN c t
  have hd := fermiOddShiftWeight_energy_difference hN c
    (fermiOddPronicMean N c / fermiOddPronicMass)
  change sieveTotalPronicEnergy N (fermiOddCenteredWeight N c) -
    fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) = _ at hd
  rw [hQ] at ht
  rw [hP, hQ, ← hd]
  exact scalar_ratio_gap _ _ _ hc.ne' ht.ne'

theorem fermiOddShiftWeight_ratio_le_centered {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c) (t : ℝ) :
    sieveTotalPronicEnergy N (fermiOddShiftWeight c t) /
        fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t) ≤
      sieveTotalPronicEnergy N (fermiOddCenteredWeight N c) /
        fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) := by
  have hg := fermiOddShiftWeight_ratio_gap hN c h t
  have hnonneg : 0 ≤
      (sieveTotalPronicEnergy N c - fermiSelectedTotalPronicEnergy N c) *
        (fermiOddPronicMass * (t - fermiOddPronicMean N c / fermiOddPronicMass)^2) /
        (fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) *
          fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t)) := by
    apply div_nonneg
    · exact mul_nonneg (sub_nonneg.mpr h.le)
        (mul_nonneg fermiOddPronicMass_pos.le (sq_nonneg _))
    · exact mul_nonneg (fermiOddCenteredWeight_selected_pos hN c h).le
        (shifted_selected_pos hN c h t).le
  linarith

theorem fermiOddShiftWeight_ratio_lt_centered {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c)
    {t : ℝ} (ht : t ≠ fermiOddPronicMean N c / fermiOddPronicMass) :
    sieveTotalPronicEnergy N (fermiOddShiftWeight c t) /
        fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t) <
      sieveTotalPronicEnergy N (fermiOddCenteredWeight N c) /
        fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) := by
  have hg := fermiOddShiftWeight_ratio_gap hN c h t
  have hpos : 0 <
      (sieveTotalPronicEnergy N c - fermiSelectedTotalPronicEnergy N c) *
        (fermiOddPronicMass * (t - fermiOddPronicMean N c / fermiOddPronicMass)^2) /
        (fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) *
          fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c t)) := by
    apply div_pos
    · exact mul_pos (sub_pos.mpr h)
        (mul_pos fermiOddPronicMass_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr ht)))
    · exact mul_pos (fermiOddCenteredWeight_selected_pos hN c h)
        (shifted_selected_pos hN c h t)
  linarith

@[simp] theorem fermiOddShiftWeight_zero (c : ℕ → ℝ) :
    fermiOddShiftWeight c 0 = c := by
  funext d
  simp [fermiOddShiftWeight, sieveUnitShiftWeight]

/-- Exact gain over the original physical ratio after odd-trace centering. -/
theorem fermiOddCenteredWeight_ratio_gain {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c) :
    sieveTotalPronicEnergy N (fermiOddCenteredWeight N c) /
        fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) -
      sieveTotalPronicEnergy N c / fermiSelectedTotalPronicEnergy N c =
      (sieveTotalPronicEnergy N c - fermiSelectedTotalPronicEnergy N c) *
        (fermiOddPronicMean N c)^2 /
        (fermiOddPronicMass * fermiSelectedTotalPronicEnergy N c *
          fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c)) := by
  have hg := fermiOddShiftWeight_ratio_gap hN c h 0
  simp only [fermiOddShiftWeight_zero, zero_sub, neg_sq] at hg
  rw [hg]
  field_simp [fermiOddPronicMass_pos.ne']

theorem fermiOddCenteredWeight_strict_improves {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c)
    (hA : fermiOddPronicMean N c ≠ 0) :
    sieveTotalPronicEnergy N c / fermiSelectedTotalPronicEnergy N c <
      sieveTotalPronicEnergy N (fermiOddCenteredWeight N c) /
        fermiSelectedTotalPronicEnergy N (fermiOddCenteredWeight N c) := by
  have ht : (0 : ℝ) ≠ fermiOddPronicMean N c / fermiOddPronicMass :=
    (div_ne_zero hA fermiOddPronicMass_pos.ne').symm
  simpa only [fermiOddShiftWeight_zero] using
    fermiOddShiftWeight_ratio_lt_centered hN c h ht

/-- The full interval of shifts preserving pointwise nonnegativity. -/
theorem fermiOddShiftWeight_nonneg_iff (c : ℕ → ℝ) (hc : ∀ d, 0 ≤ c d) (t : ℝ) :
    (∀ d, 0 ≤ fermiOddShiftWeight c t d) ↔ -c 2 ≤ t ∧ t ≤ c 1 := by
  constructor
  · intro h
    have h1 := h 1
    have h2 := h 2
    norm_num [fermiOddShiftWeight, sieveUnitShiftWeight] at h1 h2
    constructor <;> linarith
  · rintro ⟨h2, h1⟩ d
    by_cases hd1 : d = 1
    · subst d
      norm_num [fermiOddShiftWeight, sieveUnitShiftWeight]
      linarith
    · by_cases hd2 : d = 2
      · subst d
        norm_num [fermiOddShiftWeight, sieveUnitShiftWeight]
        linarith
      · simpa [fermiOddShiftWeight, sieveUnitShiftWeight, hd1, hd2] using hc d

private theorem coefficient_le_sieve_of_nonneg (N n d : ℕ) (c : ℕ → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hd : d ∈ Finset.Icc 1 N) (hdn : d ∣ n) :
    c d ≤ sieveSeq N c n := by
  apply Finset.single_le_sum (fun k _ => hc k)
  exact Finset.mem_filter.mpr ⟨hd, hdn⟩

theorem fermiOddPronicMean_ge_unit {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (hc : ∀ d, 0 ≤ c d) :
    fermiOddPronicMass * c 1 ≤ fermiOddPronicMean N c := by
  have hterm (m : ℕ) : c 1 * (1 / (pronicSeq (2 * m + 1) : ℝ)) ≤
      sieveSeq N c (2 * m + 1) / (pronicSeq (2 * m + 1) : ℝ) := by
    have h := coefficient_le_sieve_of_nonneg N (2 * m + 1) 1 c hc
      (by simp; omega) (one_dvd _)
    simpa only [mul_one_div] using div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
  have h := (odd_mass_summable.mul_left (c 1)).tsum_le_tsum hterm
    (odd_mean_summable N c)
  simpa only [tsum_mul_left, fermiOddPronicMass, fermiOddPronicMean, mul_comm] using h

private theorem odd_mean_positive_of_coefficient {N d : ℕ} (c : ℕ → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hd : d ∈ Finset.Icc 1 N) (hodd : ¬ 2 ∣ d)
    (hpos : 0 < c d) : 0 < fermiOddPronicMean N c := by
  have heq : 2 * (d / 2) + 1 = d := by omega
  have hterm (m : ℕ) : 0 ≤ sieveSeq N c (2 * m + 1) /
      (pronicSeq (2 * m + 1) : ℝ) := by
    apply div_nonneg
    · exact Finset.sum_nonneg (fun k _ => hc k)
    · positivity
  have hsingle := (odd_mean_summable N c).le_tsum (d / 2) (fun m _ => hterm m)
  have hsieve : c d ≤ sieveSeq N c d :=
    coefficient_le_sieve_of_nonneg N d d c hc hd (dvd_refl d)
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hpr : 0 < (pronicSeq d : ℝ) := by
    exact_mod_cast (show 0 < pronicSeq d by unfold pronicSeq; positivity)
  rw [heq] at hsingle
  exact lt_of_lt_of_le (div_pos (lt_of_lt_of_le hpos hsieve) hpr) hsingle

theorem fermiOddPronicMean_gt_unit_of_odd_coefficient {N d : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hd1 : 1 < d) (hdN : d ≤ N)
    (hodd : ¬ 2 ∣ d) (hpos : 0 < c d) :
    fermiOddPronicMass * c 1 < fermiOddPronicMean N c := by
  have hshift : ∀ k, 0 ≤ fermiOddShiftWeight c (c 1) k :=
    (fermiOddShiftWeight_nonneg_iff c hc _).2 ⟨by linarith [hc 1, hc 2], le_rfl⟩
  have hd2 : d ≠ 2 := by intro hd; subst d; omega
  have hval : fermiOddShiftWeight c (c 1) d = c d := by
    simp [fermiOddShiftWeight, sieveUnitShiftWeight, ne_of_gt hd1, hd2]
  have hpos' := odd_mean_positive_of_coefficient (N := N) (d := d)
    (fermiOddShiftWeight c (c 1))
    hshift (by simp; omega) hodd (by rwa [hval])
  rw [fermiOddPronicMean_shift hN] at hpos'
  nlinarith

/-- Equality in the odd-mean lower bound detects all admitted nonunit odd coefficients. -/
theorem fermiOddPronicMean_eq_unit_iff {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (hc : ∀ d, 0 ≤ c d) :
    fermiOddPronicMean N c = fermiOddPronicMass * c 1 ↔
      ∀ d, 1 < d → d ≤ N → ¬ 2 ∣ d → c d = 0 := by
  constructor
  · intro heq d hd1 hdN hodd
    by_contra hn
    have hpos : 0 < c d := lt_of_le_of_ne (hc d) (Ne.symm hn)
    have hlt := fermiOddPronicMean_gt_unit_of_odd_coefficient hN c hc hd1 hdN hodd hpos
    linarith
  · intro hz
    have hs (m : ℕ) : sieveSeq N c (2 * m + 1) = c 1 := by
      unfold sieveSeq
      calc
        _ = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ 2 * m + 1),
            if d = 1 then c 1 else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          obtain ⟨hdN, hdiv⟩ := Finset.mem_filter.mp hd
          by_cases hd1 : d = 1
          · simp [hd1]
          · have hodd : ¬ 2 ∣ d := by
              intro h2
              have := dvd_trans h2 hdiv
              omega
            have hv := hz d (by have := (Finset.mem_Icc.mp hdN).1; omega)
              (Finset.mem_Icc.mp hdN).2 hodd
            simp [hd1, hv]
        _ = c 1 := by simp; omega
    unfold fermiOddPronicMean
    simp only [hs, div_eq_mul_inv, tsum_mul_left, fermiOddPronicMass, one_mul]
    ring

/-- Removing the unit coefficient does not lower a nonnegative input ratio above one. -/
theorem fermiOddShiftWeight_unit_ratio_ge {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (hc : ∀ d, 0 ≤ c d)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c) :
    sieveTotalPronicEnergy N c / fermiSelectedTotalPronicEnergy N c ≤
      sieveTotalPronicEnergy N (fermiOddShiftWeight c (c 1)) /
        fermiSelectedTotalPronicEnergy N (fermiOddShiftWeight c (c 1)) := by
  have hQ := selected_pos_of_sieve_gt N c h
  have htQ := shifted_selected_pos hN c h (c 1)
  have hA := fermiOddPronicMean_ge_unit hN c hc
  have hc1 := hc 1
  have hcorr : (c 1)^2 * fermiOddPronicMass - 2 * c 1 * fermiOddPronicMean N c ≤ 0 := by
    nlinarith [mul_nonneg hc1 (sub_nonneg.mpr hA),
      mul_nonneg (sq_nonneg (c 1)) fermiOddPronicMass_pos.le]
  rw [div_le_div_iff₀ hQ htQ]
  obtain ⟨hP, hQ⟩ := fermiOddShiftWeight_physical_energies hN c (c 1)
  rw [hP, hQ]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h.le) hcorr]

theorem fermiSignedExtremal_odd_mean_zero {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c)
    (hmax : ∀ b : ℕ → ℝ, 0 < fermiSelectedTotalPronicEnergy N b →
      sieveTotalPronicEnergy N b / fermiSelectedTotalPronicEnergy N b ≤
        sieveTotalPronicEnergy N c / fermiSelectedTotalPronicEnergy N c) :
    fermiOddPronicMean N c = 0 := by
  by_contra hA
  have hlt := fermiOddCenteredWeight_strict_improves hN c h hA
  have hle := hmax (fermiOddCenteredWeight N c)
    (fermiOddCenteredWeight_selected_pos hN c h)
  linarith

/-- A nonnegative signed extremizer above ratio one has no admitted odd coefficients. -/
theorem fermiNonnegativeSignedExtremal_odd_coefficients_zero {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (hc : ∀ d, 0 ≤ c d)
    (h : fermiSelectedTotalPronicEnergy N c < sieveTotalPronicEnergy N c)
    (hmax : ∀ b : ℕ → ℝ, 0 < fermiSelectedTotalPronicEnergy N b →
      sieveTotalPronicEnergy N b / fermiSelectedTotalPronicEnergy N b ≤
        sieveTotalPronicEnergy N c / fermiSelectedTotalPronicEnergy N c) :
    ∀ d ∈ Finset.Icc 1 N, ¬ 2 ∣ d → c d = 0 := by
  have hA := fermiSignedExtremal_odd_mean_zero hN c h hmax
  have hunit := fermiOddPronicMean_ge_unit hN c hc
  have hc1 : c 1 = 0 := by
    have hT := fermiOddPronicMass_pos
    have h1 := hc 1
    nlinarith
  have hother := (fermiOddPronicMean_eq_unit_iff hN c hc).1 (by rw [hA, hc1, mul_zero])
  intro d hd hodd
  by_cases hd1 : d = 1
  · simpa only [hd1] using hc1
  · exact hother d (by have := (Finset.mem_Icc.mp hd).1; omega)
      (Finset.mem_Icc.mp hd).2 hodd

end GaloisForLFunctions.TransHorizonIncidenceMechanics
