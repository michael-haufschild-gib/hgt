import GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelSublinearTailRepairNoGo

/-!
# Coefficient-recovering finite-prefix regularization cannot repair the LI current

This file closes route branch **LI-CAB9**.  The branch attempted to obtain the all-mode
nonnegativity needed by the completed-Abel Li chain by replacing a genuine finite critical packet
with adaptive, mode-dependent weights.  The only consistency condition imposed is coefficientwise
recovery: every weight tends to `1`.  The weights may otherwise be unbounded at early modes,
transiently signed, and unrelated across atoms.

For a finite packet, coefficientwise recovery makes the weighted sine packet differ from the
unweighted packet by `o(1)`.  Delayed simultaneous recurrence therefore preserves uniform cofinal
excursions of both signs.  After multiplication by the Li mode, the weighted critical current has
cofinal linear excursions.  Consequently:

* every all-mode nonnegative repair supplies cofinal positive countercurrent of linear size;
* no sublinear residual can provide that repair;
* no nonempty finite critical packet admits coefficient-recovering regularization plus an `o(n)`
  residual which is nonnegative in every Li mode.

Thus the killed proof chain is

`coefficient-recovering finite-prefix regularization + o(n) residual`
`→ interior completed-Abel current nonnegative → LI-CAB5 → LI-CAB3 → RH`.

The sharp survivor is structural: any viable cancellation must remain genuinely infinite before
the mode limit, or must contribute cofinally linear countercurrent.
-/

open Polynomial Real Filter Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A finite positive sine packet with adaptive mode-dependent coefficient weights. -/
def coefficientWeightedFinitePositiveSinePacket {d : ℕ}
    (a omega : Fin d → ℝ) (w : ℕ → Fin d → ℝ) (m : ℕ) : ℝ :=
  ∑ i, a i * w m i * Real.sin ((m : ℝ) * omega i)

private theorem tendsto_bounded_mul_zero_nat
    {B : ℝ} {f g : ℕ → ℝ} (hB : ∀ n, |f n| ≤ B)
    (hg : Tendsto g atTop (nhds 0)) :
    Tendsto (fun n => f n * g n) atTop (nhds 0) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (f 0)) (hB 0)
  have hmaj : Tendsto (fun n => B * |g n|) atTop (nhds 0) := by
    have h := (hg.abs).const_mul B
    simpa using h
  refine squeeze_zero_norm (fun n => ?_) hmaj
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)

/-- Coefficientwise recovery is automatically uniform on a finite packet: the weighted packet
differs from the original packet by a quantity tending to zero. -/
theorem tendsto_coefficientWeightedFinitePositiveSinePacket_sub
    {d : ℕ} (a omega : Fin d → ℝ) (w : ℕ → Fin d → ℝ)
    (hw : ∀ i, Tendsto (fun m => w m i) atTop (nhds 1)) :
    Tendsto
      (fun m => coefficientWeightedFinitePositiveSinePacket a omega w m -
        finitePositiveSinePacket a omega m)
      atTop (nhds 0) := by
  have hterm (i : Fin d) :
      Tendsto
        (fun m : ℕ =>
          Real.sin ((m : ℝ) * omega i) * (a i * (w m i - 1)))
        atTop (nhds 0) := by
    apply tendsto_bounded_mul_zero_nat (B := 1)
    · intro m
      exact abs_sin_le_one _
    · have hsub : Tendsto (fun m : ℕ => w m i - 1) atTop (nhds 0) :=
        by simpa using (hw i).sub_const 1
      simpa using hsub.const_mul (a i)
  have hsum :
      Tendsto
        (fun m : ℕ => ∑ i, Real.sin ((m : ℝ) * omega i) *
          (a i * (w m i - 1)))
        atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _hi => hterm i)
  apply hsum.congr'
  filter_upwards with m
  rw [coefficientWeightedFinitePositiveSinePacket, finitePositiveSinePacket,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Uniform cofinal excursions survive arbitrary adaptive weights which recover every coefficient. -/
theorem cofinal_uniform_excursions_coefficientWeightedFinitePositiveSinePacket
    {d : ℕ} (hd : 0 < d) {a omega : Fin d → ℝ}
    (ha : ∀ i, 0 < a i) (homega0 : ∀ i, 0 < omega i)
    (homegaPi : ∀ i, omega i < Real.pi)
    (w : ℕ → Fin d → ℝ)
    (hw : ∀ i, Tendsto (fun m => w m i) atTop (nhds 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ,
      (∃ m : ℕ, N ≤ m ∧
        c < coefficientWeightedFinitePositiveSinePacket a omega w m) ∧
      ∃ m : ℕ, N ≤ m ∧
        coefficientWeightedFinitePositiveSinePacket a omega w m < -c := by
  obtain ⟨c, hc, hexc⟩ :=
    cofinal_uniform_excursions_finitePositiveSinePacket hd ha homega0 homegaPi
  have hdiff := tendsto_coefficientWeightedFinitePositiveSinePacket_sub a omega w hw
  have hsmall : ∀ᶠ m : ℕ in atTop,
      |coefficientWeightedFinitePositiveSinePacket a omega w m -
        finitePositiveSinePacket a omega m| < c / 2 := by
    have habs : Tendsto
        (fun m : ℕ => |coefficientWeightedFinitePositiveSinePacket a omega w m -
          finitePositiveSinePacket a omega m|) atTop (nhds 0) := by
      simpa using hdiff.abs
    have := habs.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < c / 2))
    simpa using this
  obtain ⟨M, hM⟩ := eventually_atTop.1 hsmall
  refine ⟨c / 2, by positivity, ?_⟩
  intro N
  obtain ⟨⟨mpos, hmpos, hpos⟩, ⟨mneg, hmneg, hneg⟩⟩ := hexc (max N M)
  constructor
  · refine ⟨mpos, (le_max_left _ _).trans hmpos, ?_⟩
    have hclose := abs_lt.mp (hM mpos ((le_max_right _ _).trans hmpos))
    linarith
  · refine ⟨mneg, (le_max_left _ _).trans hmneg, ?_⟩
    have hclose := abs_lt.mp (hM mneg ((le_max_right _ _).trans hmneg))
    linarith

/-- The actual completed-Abel critical-packet current with adaptive coefficient weights. -/
def liEvenCrossCriticalPacketCoefficientRegularizedCurrent {d : ℕ}
    (v : ℝ) (q : Fin d → XiCriticalLineResolventCopy)
    (w : ℕ → Fin d → ℝ) (n : ℕ) : ℝ :=
  ∑ i, w (n + 1) i * (liEvenCrossSquareMassAdjacentFlux v n (q i).1).re

/-- Exact reduction of the regularized critical current to the weighted positive sine packet. -/
theorem liEvenCrossCriticalPacketCoefficientRegularizedCurrent_eq_sinePacket
    {d : ℕ} {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : Fin d → XiCriticalLineResolventCopy) (w : ℕ → Fin d → ℝ) (n : ℕ) :
    liEvenCrossCriticalPacketCoefficientRegularizedCurrent v q w n =
      ((n : ℝ) + 1) * coefficientWeightedFinitePositiveSinePacket
        (fun i => liEvenCrossCriticalAtomAmplitude v (q i))
        (fun i => liEvenCrossCriticalAtomFrequency v (q i)) w (n + 1) := by
  rw [liEvenCrossCriticalPacketCoefficientRegularizedCurrent,
    coefficientWeightedFinitePositiveSinePacket, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hatom := congrArg Complex.re
    (liEvenCrossSquareMassAdjacentFlux_criticalAtom_sine hv0 hv4 n (q i))
  have hatom' : (liEvenCrossSquareMassAdjacentFlux v n (q i).1).re =
      ((n : ℝ) + 1) * liEvenCrossCriticalAtomAmplitude v (q i) *
        Real.sin (((n : ℝ) + 1) * liEvenCrossCriticalAtomFrequency v (q i)) := by
    simpa only [Complex.ofReal_re, Nat.cast_add, Nat.cast_one, mul_assoc] using hatom
  rw [hatom']
  push_cast
  ring

/-- A coefficient-recovering regularized nonempty critical packet has cofinal linear excursions of
both signs.  No sign, boundedness, or rate assumption is imposed on the weights. -/
theorem cofinal_linear_excursions_liEvenCrossCriticalPacketCoefficientRegularizedCurrent
    {d : ℕ} (hd : 0 < d) {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : Fin d → XiCriticalLineResolventCopy) (w : ℕ → Fin d → ℝ)
    (hw : ∀ i, Tendsto (fun m => w m i) atTop (nhds 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ,
      (∃ n : ℕ, N ≤ n ∧ c * ((n : ℝ) + 1) <
        liEvenCrossCriticalPacketCoefficientRegularizedCurrent v q w n) ∧
      ∃ n : ℕ, N ≤ n ∧
        liEvenCrossCriticalPacketCoefficientRegularizedCurrent v q w n <
          -c * ((n : ℝ) + 1) := by
  let a : Fin d → ℝ := fun i => liEvenCrossCriticalAtomAmplitude v (q i)
  let omega : Fin d → ℝ := fun i => liEvenCrossCriticalAtomFrequency v (q i)
  have ha : ∀ i, 0 < a i := fun i => liEvenCrossCriticalAtomAmplitude_pos hv0 hv4 (q i)
  have homega0 : ∀ i, 0 < omega i := fun i =>
    (liEvenCrossCriticalAtomFrequency_mem hv0 hv4 (q i)).1
  have homegaPi : ∀ i, omega i < Real.pi := fun i =>
    (liEvenCrossCriticalAtomFrequency_mem hv0 hv4 (q i)).2
  obtain ⟨c, hc, hexc⟩ :=
    cofinal_uniform_excursions_coefficientWeightedFinitePositiveSinePacket
      hd ha homega0 homegaPi w hw
  refine ⟨c, hc, ?_⟩
  intro N
  obtain ⟨⟨mpos, hmposN, hmpos⟩, ⟨mneg, hmnegN, hmneg⟩⟩ := hexc (N + 1)
  have hmpos1 : 1 ≤ mpos := by omega
  have hmneg1 : 1 ≤ mneg := by omega
  constructor
  · refine ⟨mpos - 1, by omega, ?_⟩
    rw [liEvenCrossCriticalPacketCoefficientRegularizedCurrent_eq_sinePacket hv0 hv4]
    have hindex : mpos - 1 + 1 = mpos := Nat.sub_add_cancel hmpos1
    rw [hindex]
    have hcast : (((mpos - 1 : ℕ) : ℝ) + 1) = (mpos : ℝ) := by
      rw [Nat.cast_sub hmpos1]
      push_cast
      ring
    rw [hcast]
    have hmposReal : 0 < (mpos : ℝ) := by exact_mod_cast hmpos1
    have h := mul_lt_mul_of_pos_left (by simpa [a, omega] using hmpos) hmposReal
    calc
      c * (mpos : ℝ) = (mpos : ℝ) * c := by ring
      _ < (mpos : ℝ) * coefficientWeightedFinitePositiveSinePacket
          (fun i => liEvenCrossCriticalAtomAmplitude v (q i))
          (fun i => liEvenCrossCriticalAtomFrequency v (q i)) w mpos := h
  · refine ⟨mneg - 1, by omega, ?_⟩
    rw [liEvenCrossCriticalPacketCoefficientRegularizedCurrent_eq_sinePacket hv0 hv4]
    have hindex : mneg - 1 + 1 = mneg := Nat.sub_add_cancel hmneg1
    rw [hindex]
    have hcast : (((mneg - 1 : ℕ) : ℝ) + 1) = (mneg : ℝ) := by
      rw [Nat.cast_sub hmneg1]
      push_cast
      ring
    rw [hcast]
    have hmnegReal : 0 < (mneg : ℝ) := by exact_mod_cast hmneg1
    have h := mul_lt_mul_of_pos_left (by simpa [a, omega] using hmneg) hmnegReal
    nlinarith

/-- Any all-mode nonnegative repair of a coefficient-recovering regularized critical packet must
supply cofinal positive countercurrent of linear size. -/
theorem cofinal_linear_tail_forced_of_coefficientRegularized_all_nonnegative
    {d : ℕ} (hd : 0 < d) {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : Fin d → XiCriticalLineResolventCopy) (w : ℕ → Fin d → ℝ)
    (hw : ∀ i, Tendsto (fun m => w m i) atTop (nhds 1))
    (R : ℕ → ℝ)
    (hnonneg : ∀ n : ℕ,
      0 ≤ liEvenCrossCriticalPacketCoefficientRegularizedCurrent v q w n + R n) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      c * ((n : ℝ) + 1) < R n := by
  obtain ⟨c, hc, hexc⟩ :=
    cofinal_linear_excursions_liEvenCrossCriticalPacketCoefficientRegularizedCurrent
      hd hv0 hv4 q w hw
  refine ⟨c, hc, ?_⟩
  intro N
  obtain ⟨n, hnN, hnneg⟩ := (hexc N).2
  exact ⟨n, hnN, by linarith [hnonneg n]⟩

/-- No sublinear correction makes a coefficient-recovering regularization of a nonempty genuine
critical packet nonnegative in every Li mode. -/
theorem not_exists_sublinearCorrection_coefficientRegularized_all_nonnegative
    {d : ℕ} (hd : 0 < d) {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4)
    (q : Fin d → XiCriticalLineResolventCopy) (w : ℕ → Fin d → ℝ)
    (hw : ∀ i, Tendsto (fun m => w m i) atTop (nhds 1)) :
    ¬ ∃ R : ℕ → ℝ,
      Tendsto (fun n : ℕ => R n / ((n : ℝ) + 1)) atTop (nhds 0) ∧
        ∀ n : ℕ,
          0 ≤ liEvenCrossCriticalPacketCoefficientRegularizedCurrent v q w n + R n := by
  rintro ⟨R, hR, hnonneg⟩
  obtain ⟨c, hc, hforced⟩ :=
    cofinal_linear_tail_forced_of_coefficientRegularized_all_nonnegative
      hd hv0 hv4 q w hw R hnonneg
  have heventually : ∀ᶠ n : ℕ in atTop, R n / ((n : ℝ) + 1) < c :=
    hR.eventually (Iio_mem_nhds hc)
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  obtain ⟨n, hnN, hnlarge⟩ := hforced N
  have hratio := hN n hnN
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hsmall : R n < c * ((n : ℝ) + 1) := (div_lt_iff₀ hden).mp hratio
  linarith

/-- **LI-CAB9 route kill.** Even arbitrary transiently signed, adaptive weights cannot repair a
finite genuine critical prefix when they recover every coefficient and leave only a sublinear
residual. -/
theorem not_exists_nonempty_finiteCriticalPacket_coefficientRecoveringRegularization_sublinearRepair_all_nonnegative :
    ¬ ∃ v : ℝ, ∃ d : ℕ, ∃ q : Fin d → XiCriticalLineResolventCopy,
      0 < v ∧ v ≤ 1 / 4 ∧ 0 < d ∧
      ∃ w : ℕ → Fin d → ℝ,
        (∀ i, Tendsto (fun m => w m i) atTop (nhds 1)) ∧
        ∃ R : ℕ → ℝ,
          Tendsto (fun n : ℕ => R n / ((n : ℝ) + 1)) atTop (nhds 0) ∧
          ∀ n : ℕ,
            0 ≤ liEvenCrossCriticalPacketCoefficientRegularizedCurrent v q w n + R n := by
  rintro ⟨v, d, q, hv0, hv4, hd, w, hw, R, hR, hnonneg⟩
  exact not_exists_sublinearCorrection_coefficientRegularized_all_nonnegative
    hd hv0 hv4 q w hw ⟨R, hR, hnonneg⟩

end

end RHTower
