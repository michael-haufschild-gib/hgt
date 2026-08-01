import GaloisForLFunctions.RHTower.SoninCouplingEnergyLowerBound
import GaloisForLFunctions.RHTower.SoninCompletionUnboundedRequirement

/-!
# The threshold a per-scale counterterm must clear

A completion that contributes a fixed amount per scale of the source packet turns the packet
channel into a sum of per-scale differences: the contribution minus that scale's coupling energy.
So the completed channel has a lower floor as soon as the contribution dominates every scale's
energy, and it has none as soon as the contribution falls below the uniform energy floor that the
escaping wavepacket forces.

The threshold is therefore the coupling energy itself, and the uniform floor `1/4` makes it
explicit: a per-scale contribution below `1/4` cannot work at any flag, whatever else it does.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap Filter
open scoped Topology

/-- The unit-weight packet curvature trace corrected by a fixed contribution per scale. -/
def soninCompletedPacketValue (s : Finset ℕ) (a b c : ℝ) (p : ℕ → ℝ) (hp : ∀ i, 1 < p i)
    (κ : ℝ) : ℝ :=
  (opTrace (soninAperturePacketCurvature s a b c p hp (fun _ => 1))).re + κ * s.card

/-- **Per-scale form.**  The completed value is the sum over the packet of the contribution minus
that scale's coupling energy. -/
theorem soninCompletedPacketValue_eq_sum
    (s : Finset ℕ) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ℕ → ℝ) (hp : ∀ i, 1 < p i) (hcp : ∀ i ∈ s, c < p i * a) (κ : ℝ) :
    soninCompletedPacketValue s a b c p hp κ =
      ∑ i ∈ s, (κ - hsNormSq
        (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) := by
  rw [soninCompletedPacketValue, re_opTrace_soninAperturePacketCurvature s ha hab hbc p hp _ hcp,
    Finset.sum_sub_distrib]
  have hconst : ∑ _i ∈ s, κ = κ * s.card := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hconst]
  have hone : ∑ i ∈ s, (1 : ℝ) * hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) =
      ∑ i ∈ s, hsNormSq
        (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) :=
    Finset.sum_congr rfl fun i _ => one_mul _
  rw [hone]
  ring

/-- **A dominating contribution restores the floor.**  If the per-scale contribution is at least
the coupling energy at every scale, the completed channel is bounded below by zero. -/
theorem soninCompletedPacketValue_nonneg
    (s : Finset ℕ) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ℕ → ℝ) (hp : ∀ i, 1 < p i) (hcp : ∀ i ∈ s, c < p i * a) (κ : ℝ)
    (hκ : ∀ i, hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) ≤ κ) :
    0 ≤ soninCompletedPacketValue s a b c p hp κ := by
  rw [soninCompletedPacketValue_eq_sum s ha hab hbc p hp hcp κ]
  exact Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hκ i)

/-- **A contribution below the energy floor fails.**  Along the crossing clock the coupling energy
is eventually at least `1/4`, so a per-scale contribution below `1/4` drives the completed value
below every level. -/
theorem exists_soninCompletedPacketValue_lt
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) {κ : ℝ} (hκ : κ < (4 : ℝ)⁻¹) (M : ℝ) :
    ∃ s : Finset ℕ,
      soninCompletedPacketValue s a b c (soninCrossingClock a c)
        (one_lt_soninCrossingClock a c) κ < M := by
  have hfloor := eventually_le_hsNormSq_soninApertureCoupling a b c ha hb hab hbc q haq hqb
    (soninCrossingClock a c) (soninCrossingClock_pos a c) (one_lt_soninCrossingClock a c)
    (fun n => lt_soninCrossingClock_mul a c ha n) (tendsto_soninCrossingClock a c)
  rw [eventually_atTop] at hfloor
  obtain ⟨N, hN⟩ := hfloor
  have hgap : 0 < (4 : ℝ)⁻¹ - κ := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((-M) / ((4 : ℝ)⁻¹ - κ))
  refine ⟨Finset.Ico N (N + m), ?_⟩
  have hmem : ∀ i ∈ Finset.Ico N (N + m), N ≤ i := fun i hi => (Finset.mem_Ico.mp hi).1
  rw [soninCompletedPacketValue_eq_sum _ ha hab hbc _ _
    (fun i _ => lt_soninCrossingClock_mul a c ha i) κ]
  have hterm : ∀ i ∈ Finset.Ico N (N + m),
      κ - hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
        (soninCrossingClock a c i) (one_lt_soninCrossingClock a c i)) ≤ κ - (4 : ℝ)⁻¹ := by
    intro i hi
    have := hN i (hmem i hi)
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hcard : ((N + m - N : ℕ) : ℝ) = (m : ℝ) := by
    rw [Nat.add_sub_cancel_left]
  rw [hcard] at hsum
  have hlt : (m : ℝ) * (κ - (4 : ℝ)⁻¹) < M := by
    have hmpos : (-M) / ((4 : ℝ)⁻¹ - κ) < (m : ℝ) := hm
    have h := (div_lt_iff₀ hgap).mp hmpos
    nlinarith [hgap]
  exact lt_of_le_of_lt hsum hlt

/-- **No floor below the threshold.** -/
theorem not_exists_lower_bound_soninCompletedPacketValue
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) {κ : ℝ} (hκ : κ < (4 : ℝ)⁻¹) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValue s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c) κ := by
  rintro ⟨M, hM⟩
  obtain ⟨s, hs⟩ := exists_soninCompletedPacketValue_lt a b c ha hb hab hbc q haq hqb hκ M
  exact absurd (hM s) (not_le.mpr hs)

/-- The logarithmic aperture counterterm is below the threshold on a short flag: `log(6/5) < 1/4`
because `5/4 <= exp(1/4)`. -/
theorem log_six_fifths_lt_quarter : Real.log (6 / 5) < (4 : ℝ)⁻¹ := by
  have hexp : (5 : ℝ) / 4 ≤ Real.exp ((4 : ℝ)⁻¹) := by
    have h := Real.add_one_le_exp ((4 : ℝ)⁻¹)
    norm_num at h ⊢
    linarith
  have hlt : (6 : ℝ) / 5 < Real.exp ((4 : ℝ)⁻¹) := by linarith
  exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr hlt

/-- **The logarithmic per-scale counterterm fails on a short flag.**  At the flag
`1 < 11/10 < 6/5 < 5/4` the aperture logarithm `log(b/a) = log(6/5)` is below the uniform energy
floor, so contributing it once per scale leaves the completed channel unbounded below. -/
theorem not_exists_lower_bound_soninCompletedPacketValue_logCounterterm :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValue s 1 (6 / 5) (5 / 4)
          (soninCrossingClock 1 (5 / 4)) (one_lt_soninCrossingClock 1 (5 / 4))
          (Real.log (6 / 5 / 1)) := by
  have hlog : Real.log (6 / 5 / 1) < (4 : ℝ)⁻¹ := by
    rw [div_one]
    exact log_six_fifths_lt_quarter
  exact not_exists_lower_bound_soninCompletedPacketValue 1 (6 / 5) (5 / 4) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (11 / 10) (by norm_num) (by norm_num) hlog

end RHTower
