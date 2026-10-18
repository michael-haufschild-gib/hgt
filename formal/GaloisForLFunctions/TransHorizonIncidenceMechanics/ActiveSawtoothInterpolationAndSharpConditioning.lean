import GaloisForLFunctions.TransHorizonIncidenceMechanics.ActiveSawtoothPowerSamplingAndCalibratedRecovery

/-!
# Active sawtooth interpolation and sharp conditioning

Every prescribed vector of squarefree nonunit self-endpoint samples is realized by
an explicit squarefree-supported weight. An independent unit shift prescribes any
finite harmonic sum at positive horizon. All samples may simultaneously be moved
beyond any observation scale by taking a common positive power.

No coordinate in this canonical sampling scheme is redundant. The exact worst-case
coefficient-error constant at a squarefree target d is
`(2*d/(d-1)) * (d.divisors.erase 1).card`. The bound is attained by a Mobius-sign
sample vector, even between two weights with the same prescribed harmonic scalar.
Increasing the common power changes observation positions but not this constant.

These results concern general squarefree-supported weights. They impose no extra
sign or multiplicativity constraints from a particular Mobius or damped family.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- Explicit synthesis of arbitrary squarefree nonunit sample data at a fixed horizon. -/
def activeSquarefreeInterpolant (N : ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d ∈ Finset.Icc 2 N ∧ Squarefree d then
    activeSawtoothMobiusLift (fun j => if j = 1 then 0 else a j) d else 0

/-- The synthesized weight vanishes off the squarefree integers. -/
theorem activeSquarefreeInterpolant_support (N : ℕ) (a : ℕ → ℝ) :
    ∀ d : ℕ, ¬ Squarefree d → activeSquarefreeInterpolant N a d = 0 := by
  intro d hd
  simp [activeSquarefreeInterpolant, hd]

/-- Every visible squarefree nonunit coefficient is given by the existing Mobius inverse. -/
theorem activeSquarefreeInterpolant_coefficient (N : ℕ) (a : ℕ → ℝ)
    {d : ℕ} (hd : d ∈ Finset.Icc 2 N) (hs : Squarefree d) :
    activeSquarefreeInterpolant N a d =
      activeSawtoothMobiusLift (fun j => if j = 1 then 0 else a j) d := by
  simp [activeSquarefreeInterpolant, hd, hs]

private theorem interpolant_transform (N : ℕ) (a : ℕ → ℝ) {d : ℕ}
    (hd : 0 < d) (hs : Squarefree d) (hdN : d ≤ N) :
    truncatedSieveWeight N (fun j => activeSquarefreeInterpolant N a j -
      activeSquarefreeInterpolant N a j / (j : ℝ)) d =
        ∑ x ∈ d.divisorsAntidiagonal, (μ x.1 : ℝ) *
          (2 * (if x.2 = 1 then 0 else a x.2)) := by
  have hdI : d ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hd, hdN⟩
  simp only [truncatedSieveWeight, if_pos hdI]
  by_cases hd1 : d = 1
  · subst d
    simp
  · have hd2 : d ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨by omega, hdN⟩
    rw [activeSquarefreeInterpolant_coefficient N a hd2 hs]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hdR1 : (d : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd2).1
      linarith
    have hsum : (∑ x ∈ d.divisorsAntidiagonal,
        (μ x.1 : ℝ) * (2 * (if x.2 = 1 then 0 else a x.2))) =
        2 * ∑ x ∈ d.divisorsAntidiagonal,
          (μ x.1 : ℝ) * (if x.2 = 1 then 0 else a x.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hsum]
    unfold activeSawtoothMobiusLift
    field_simp [hdR, hdR1]

/-- Arbitrary prescribed squarefree self-endpoint samples are realized exactly. -/
theorem activeSquarefreeInterpolant_realizes (N : ℕ) (a : ℕ → ℝ)
    {j : ℕ} (hj : j ∈ Finset.Icc 2 N) (hs : Squarefree j) :
    activeCenteredSawtoothSum N (activeSquarefreeInterpolant N a) j j = a j := by
  let S : Set ℕ := {n | Squarefree n ∧ n ≤ N}
  have hclosed : ∀ m n : ℕ, m ∣ n → n ∈ S → m ∈ S := by
    intro m n hmn hn
    exact ⟨hn.1.squarefree_of_dvd hmn,
      (Nat.le_of_dvd hn.1.ne_zero.bot_lt hmn).trans hn.2⟩
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
    (f := truncatedSieveWeight N (fun d => activeSquarefreeInterpolant N a d -
      activeSquarefreeInterpolant N a d / (d : ℝ)))
    (g := fun d => 2 * (if d = 1 then 0 else a d)) S hclosed).mpr
      (fun d hd hs => (interpolant_transform N a hd hs.1 hs.2).symm)
  have h := hinv j (by have := (Finset.mem_Icc.mp hj).1; omega)
    ⟨hs, (Finset.mem_Icc.mp hj).2⟩
  rw [← two_mul_active_self_eq_divisor_transform N _
    (by have := (Finset.mem_Icc.mp hj).1; omega)] at h
  rw [if_neg (by have := (Finset.mem_Icc.mp hj).1; omega : j ≠ 1)] at h
  linarith only [h]

/-- Prescribe a harmonic scalar without altering any synthesized active observation. -/
def calibratedActiveInterpolant (N : ℕ) (H : ℝ) (a : ℕ → ℝ) : ℕ → ℝ :=
  sieveUnitShiftWeight (activeSquarefreeInterpolant N a)
    (H - finiteHarmonicSum N (activeSquarefreeInterpolant N a))

/-- Harmonic calibration preserves squarefree support. -/
theorem calibratedActiveInterpolant_support (N : ℕ) (H : ℝ) (a : ℕ → ℝ) :
    ∀ d : ℕ, ¬ Squarefree d → calibratedActiveInterpolant N H a d = 0 :=
  sieveUnitShiftWeight_squarefree_support (activeSquarefreeInterpolant_support N a) _

/-- The calibrated interpolant has the prescribed harmonic scalar at every positive horizon. -/
theorem calibratedActiveInterpolant_harmonic {N : ℕ} (hN : 1 ≤ N)
    (H : ℝ) (a : ℕ → ℝ) : finiteHarmonicSum N (calibratedActiveInterpolant N H a) = H := by
  have h := finiteHarmonicSum_sub_of_tail_eq hN
    (calibratedActiveInterpolant N H a) (activeSquarefreeInterpolant N a) (by
      intro d hd
      have hd1 : d ≠ 1 := by have := (Finset.mem_Icc.mp hd).1; omega
      simp [calibratedActiveInterpolant, sieveUnitShiftWeight, hd1])
  have hright : calibratedActiveInterpolant N H a 1 - activeSquarefreeInterpolant N a 1 =
      H - finiteHarmonicSum N (activeSquarefreeInterpolant N a) := by
    simp [calibratedActiveInterpolant, sieveUnitShiftWeight]
  rw [hright] at h
  linarith only [h]

/-- The same prescribed data appear at every positive common power of the sampling bases. -/
theorem calibratedActiveInterpolant_realizes_powers (N : ℕ) (H : ℝ) (a : ℕ → ℝ)
    {m j : ℕ} (hm : 1 ≤ m) (hj : j ∈ Finset.Icc 2 N) (hs : Squarefree j) :
    activeCenteredSawtoothSum N (calibratedActiveInterpolant N H a) (j ^ m) (j ^ m) =
      a j := by
  rw [(activeCenteredSawtoothSum_pow_of_squarefree_support N
    (calibratedActiveInterpolant_support N H a)
    (by have := (Finset.mem_Icc.mp hj).1; omega) hm).2]
  rw [calibratedActiveInterpolant, activeCenteredSawtoothSum_unitShiftWeight]
  exact activeSquarefreeInterpolant_realizes N a hj hs

/-- Harmonic calibration leaves all nonunit coefficients unchanged. -/
theorem calibratedActiveInterpolant_coefficient (N : ℕ) (H : ℝ) (a : ℕ → ℝ)
    {d : ℕ} (hd : d ∈ Finset.Icc 2 N) (hs : Squarefree d) :
    calibratedActiveInterpolant N H a d =
      activeSawtoothMobiusLift (fun j => if j = 1 then 0 else a j) d := by
  have hd1 : d ≠ 1 := by have := (Finset.mem_Icc.mp hd).1; omega
  simp only [calibratedActiveInterpolant, sieveUnitShiftWeight, if_neg hd1, add_zero]
  exact activeSquarefreeInterpolant_coefficient N a hd hs

/-- Arbitrary squarefree sample data and an arbitrary harmonic scalar are jointly realizable. -/
theorem exists_calibrated_active_power_interpolant {N : ℕ} (hN : 1 ≤ N)
    (H : ℝ) (a : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) ∧
      finiteHarmonicSum N c = H ∧
      ∀ j ∈ Finset.Icc 2 N, Squarefree j →
        activeCenteredSawtoothSum N c (j ^ m) (j ^ m) = a j := by
  exact ⟨calibratedActiveInterpolant N H a, calibratedActiveInterpolant_support N H a,
    calibratedActiveInterpolant_harmonic hN H a,
    fun _ hj hs => calibratedActiveInterpolant_realizes_powers N H a hm hj hs⟩

/-- Arbitrary data can be realized with every sample beyond any prescribed observation scale. -/
theorem exists_distant_calibrated_active_interpolant {N : ℕ} (hN : 1 ≤ N)
    (B : ℕ) (H : ℝ) (a : ℕ → ℝ) :
    ∃ m : ℕ, ∃ c : ℕ → ℝ, 1 ≤ m ∧
      (∀ j ∈ Finset.Icc 2 N, B < j ^ m) ∧
      (∀ d : ℕ, ¬ Squarefree d → c d = 0) ∧ finiteHarmonicSum N c = H ∧
      ∀ j ∈ Finset.Icc 2 N, Squarefree j →
        activeCenteredSawtoothSum N c (j ^ m) (j ^ m) = a j := by
  obtain ⟨m, hm, hfar, _⟩ := exists_calibrated_power_recovery_above N B
  obtain ⟨c, hc, hH, hdata⟩ := exists_calibrated_active_power_interpolant hN H a hm
  exact ⟨m, c, hm, hfar, hc, hH, hdata⟩

/-- Interpolation is a right and left inverse on the visible squarefree coefficient space. -/
theorem calibratedActiveInterpolant_recovers (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) {m : ℕ} (hm : 1 ≤ m) :
    ∀ d ∈ Finset.Icc 1 N,
      calibratedActiveInterpolant N (finiteHarmonicSum N c)
        (fun j => activeCenteredSawtoothSum N c (j ^ m) (j ^ m)) d = c d := by
  intro d hd
  have hN := (Finset.mem_Icc.mp hd).1.trans (Finset.mem_Icc.mp hd).2
  apply (calibrated_active_power_samples_eq_iff_weight_eq N
    (calibratedActiveInterpolant_support N _ _) hc hm).mp
      ⟨calibratedActiveInterpolant_harmonic hN _ _,
        fun _ hj hs => calibratedActiveInterpolant_realizes_powers N _ _ hm hj hs⟩ d hd

/-- Deleting any one canonical squarefree sample loses information, even at fixed harmonic scalar. -/
theorem active_squarefree_power_sample_indispensable (N : ℕ) (H : ℝ)
    {m r : ℕ} (hm : 1 ≤ m) (hr : r ∈ Finset.Icc 2 N) (hs : Squarefree r) :
    ∃ c b : ℕ → ℝ,
      (∀ d : ℕ, ¬ Squarefree d → c d = 0) ∧
      (∀ d : ℕ, ¬ Squarefree d → b d = 0) ∧
      finiteHarmonicSum N c = H ∧ finiteHarmonicSum N b = H ∧
      (∀ j ∈ Finset.Icc 2 N, Squarefree j → j ≠ r →
        activeCenteredSawtoothSum N c (j ^ m) (j ^ m) =
          activeCenteredSawtoothSum N b (j ^ m) (j ^ m)) ∧
      activeCenteredSawtoothSum N c (r ^ m) (r ^ m) -
        activeCenteredSawtoothSum N b (r ^ m) (r ^ m) = 1 := by
  let a : ℕ → ℝ := fun j => if j = r then 1 else 0
  have hN : 1 ≤ N := by have := Finset.mem_Icc.mp hr; omega
  refine ⟨calibratedActiveInterpolant N H a, calibratedActiveInterpolant N H (fun _ => 0),
    calibratedActiveInterpolant_support N H a, calibratedActiveInterpolant_support N H _,
    calibratedActiveInterpolant_harmonic hN H a, calibratedActiveInterpolant_harmonic hN H _,
    ?_, ?_⟩
  · intro j hj hsj hjr
    rw [calibratedActiveInterpolant_realizes_powers N H a hm hj hsj,
      calibratedActiveInterpolant_realizes_powers N H (fun _ => 0) hm hj hsj]
    simp [a, hjr]
  · rw [calibratedActiveInterpolant_realizes_powers N H a hm hr hs,
      calibratedActiveInterpolant_realizes_powers N H (fun _ => 0) hm hr hs]
    simp [a]

/-- Unit-normalized data remove the unit divisor from the inverse row. -/
theorem activeSawtoothMobiusLift_eq_sum_erase_one (a : ℕ → ℝ) (ha : a 1 = 0) (d : ℕ) :
    activeSawtoothMobiusLift a d =
      (2 * (d : ℝ) / ((d : ℝ) - 1)) *
        ∑ j ∈ d.divisors.erase 1, (μ (d / j) : ℝ) * a j := by
  unfold activeSawtoothMobiusLift
  rw [Nat.sum_divisorsAntidiagonal' (fun u v => (μ u : ℝ) * a v)]
  congr 1
  exact (Finset.sum_erase _ (by simp [ha])).symm

/-- Exact sup-norm amplification for a squarefree coefficient row. -/
def activeSampleAmplification (d : ℕ) : ℝ :=
  (2 * (d : ℝ) / ((d : ℝ) - 1)) * ((d.divisors.erase 1).card : ℝ)

/-- The coefficient amplification factor is nonnegative on nonunit targets. -/
theorem activeSampleAmplification_nonneg {d : ℕ} (hd : 2 ≤ d) :
    0 ≤ activeSampleAmplification d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold activeSampleAmplification
  exact mul_nonneg (div_nonneg (by positivity) (by linarith)) (by positivity)

/-- Sup-norm control retains the exact inverse-row scale instead of replacing it by four. -/
theorem activeSawtoothMobiusLift_abs_le (a : ℕ → ℝ) (ha : a 1 = 0)
    {d : ℕ} (hd : 2 ≤ d) (E : ℝ)
    (h : ∀ j ∈ d.divisors.erase 1, |a j| ≤ E) :
    |activeSawtoothMobiusLift a d| ≤ activeSampleAmplification d * E := by
  let K : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 1)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : 0 ≤ K := div_nonneg (by positivity) (by linarith)
  rw [activeSawtoothMobiusLift_eq_sum_erase_one a ha d, abs_mul, abs_of_nonneg hK]
  change K * |∑ j ∈ d.divisors.erase 1, (μ (d / j) : ℝ) * a j| ≤ _
  calc
    _ ≤ K * ∑ j ∈ d.divisors.erase 1, |(μ (d / j) : ℝ) * a j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hK
    _ ≤ K * ∑ _j ∈ d.divisors.erase 1, E := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply Finset.sum_le_sum
      intro j hj
      have hmu : |(μ (d / j) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d / j))
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hmu (abs_nonneg (a j))).trans (by simpa using h j hj)
    _ = _ := by simp [activeSampleAmplification, K, mul_assoc]

/-- Actual squarefree power samples obey the divisor-count conditioning bound. -/
theorem active_power_samples_abs_coefficient_le (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) {m d : ℕ}
    (hm : 1 ≤ m) (hd : 2 ≤ d) (hdN : d ≤ N) (hs : Squarefree d) (E : ℝ)
    (hobs : ∀ j ∈ Finset.Icc 2 N, Squarefree j →
      |activeCenteredSawtoothSum N c (j ^ m) (j ^ m)| ≤ E) :
    |c d| ≤ activeSampleAmplification d * E := by
  rw [← activeSawtoothMobiusLift_recovers_from_powers N hc hm hd hdN]
  apply activeSawtoothMobiusLift_abs_le _ (by simp) hd E
  intro j hj
  have hjd := (Finset.mem_erase.mp hj).2
  have hj1 := (Finset.mem_erase.mp hj).1
  have hjpos := Nat.pos_of_mem_divisors hjd
  have hjdvd := Nat.dvd_of_mem_divisors hjd
  exact hobs j (Finset.mem_Icc.mpr ⟨by omega, (Nat.le_of_dvd (by omega) hjdvd).trans hdN⟩)
    (hs.squarefree_of_dvd hjdvd)

/-- The same sharp row bound controls coefficient errors between two squarefree profiles. -/
theorem active_power_samples_coefficient_error_le (N : ℕ) {c b : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hb : ∀ d : ℕ, ¬ Squarefree d → b d = 0) {m d : ℕ}
    (hm : 1 ≤ m) (hd : 2 ≤ d) (hdN : d ≤ N) (hs : Squarefree d) (E : ℝ)
    (hobs : ∀ j ∈ Finset.Icc 2 N, Squarefree j →
      |activeCenteredSawtoothSum N c (j ^ m) (j ^ m) -
        activeCenteredSawtoothSum N b (j ^ m) (j ^ m)| ≤ E) :
    |c d - b d| ≤ activeSampleAmplification d * E := by
  apply active_power_samples_abs_coefficient_le N
    (c := fun j => c j - b j) (fun j hj => by rw [hc j hj, hb j hj, sub_self])
    hm hd hdN hs E
  intro j hj hsj
  have heq : activeCenteredSawtoothSum N (fun k => c k - b k) (j ^ m) (j ^ m) =
      activeCenteredSawtoothSum N c (j ^ m) (j ^ m) -
        activeCenteredSawtoothSum N b (j ^ m) (j ^ m) := by
    simp only [activeCenteredSawtoothSum, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact hobs j hj hsj

/-- A Möbius-sign data vector attains the complete absolute row sum for squarefree targets. -/
theorem activeSawtoothMobiusLift_sign_eq_amplification {d : ℕ}
    (hs : Squarefree d) :
    activeSawtoothMobiusLift (fun j => if j = 1 then 0 else (μ (d / j) : ℝ)) d =
      activeSampleAmplification d := by
  rw [activeSawtoothMobiusLift_eq_sum_erase_one _ (by simp) d]
  unfold activeSampleAmplification
  congr 1
  calc
    _ = ∑ _j ∈ d.divisors.erase 1, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj1 := (Finset.mem_erase.mp hj).1
      have hjdvd := Nat.dvd_of_mem_divisors (Finset.mem_erase.mp hj).2
      have hsq := hs.squarefree_of_dvd (Nat.div_dvd_of_dvd hjdvd)
      have hmu : (μ (d / j) : ℝ) ^ 2 = 1 := by
        exact_mod_cast (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq)
      simp only [if_neg hj1]
      nlinarith only [hmu]
    _ = _ := by simp

/-- Sharpness is realized by actual squarefree weights, at any fixed harmonic scalar. -/
theorem exists_active_power_samples_amplification_attainer (N : ℕ) (H : ℝ)
    {m d : ℕ} (hm : 1 ≤ m) (hd : 2 ≤ d) (hdN : d ≤ N) (hs : Squarefree d) :
    ∃ c : ℕ → ℝ, (∀ j : ℕ, ¬ Squarefree j → c j = 0) ∧
      finiteHarmonicSum N c = H ∧
      (∀ j ∈ Finset.Icc 2 N, Squarefree j →
        |activeCenteredSawtoothSum N c (j ^ m) (j ^ m)| ≤ 1) ∧
      c d = activeSampleAmplification d := by
  let a : ℕ → ℝ := fun j => (μ (d / j) : ℝ)
  have hN : 1 ≤ N := by omega
  refine ⟨calibratedActiveInterpolant N H a, calibratedActiveInterpolant_support N H a,
    calibratedActiveInterpolant_harmonic hN H a, ?_, ?_⟩
  · intro j hj hsj
    rw [calibratedActiveInterpolant_realizes_powers N H a hm hj hsj]
    change |(μ (d / j) : ℝ)| ≤ 1
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d / j))
  · rw [calibratedActiveInterpolant_coefficient N H a (Finset.mem_Icc.mpr ⟨hd, hdN⟩) hs]
    exact activeSawtoothMobiusLift_sign_eq_amplification hs

/-- The stated divisor-count constant is optimal, even after fixing the harmonic scalar. -/
theorem active_power_samples_sharp_constant_iff (N : ℕ) (H C : ℝ)
    {m d : ℕ} (hm : 1 ≤ m) (hd : 2 ≤ d) (hdN : d ≤ N) (hs : Squarefree d) :
    (∀ c : ℕ → ℝ, (∀ j : ℕ, ¬ Squarefree j → c j = 0) →
      finiteHarmonicSum N c = H →
      (∀ j ∈ Finset.Icc 2 N, Squarefree j →
        |activeCenteredSawtoothSum N c (j ^ m) (j ^ m)| ≤ 1) → |c d| ≤ C) ↔
      activeSampleAmplification d ≤ C := by
  constructor
  · intro h
    obtain ⟨c, hc, hH, hobs, hdval⟩ :=
      exists_active_power_samples_amplification_attainer N H hm hd hdN hs
    have hbound := h c hc hH hobs
    rwa [hdval, abs_of_nonneg (activeSampleAmplification_nonneg hd)] at hbound
  · intro h c hc _ hobs
    have hbound : |c d| ≤ activeSampleAmplification d := by
      simpa using active_power_samples_abs_coefficient_le N hc hm hd hdN hs 1 hobs
    exact hbound.trans h

/-- Calibration does not improve the optimal coefficient-error constant between two weights. -/
theorem calibrated_active_power_samples_sharp_error_iff (N : ℕ) (H C : ℝ)
    {m d : ℕ} (hm : 1 ≤ m) (hd : 2 ≤ d) (hdN : d ≤ N) (hs : Squarefree d) :
    (∀ c b : ℕ → ℝ, (∀ j : ℕ, ¬ Squarefree j → c j = 0) →
      (∀ j : ℕ, ¬ Squarefree j → b j = 0) →
      finiteHarmonicSum N c = H → finiteHarmonicSum N b = H →
      (∀ j ∈ Finset.Icc 2 N, Squarefree j →
        |activeCenteredSawtoothSum N c (j ^ m) (j ^ m) -
          activeCenteredSawtoothSum N b (j ^ m) (j ^ m)| ≤ 1) → |c d - b d| ≤ C) ↔
      activeSampleAmplification d ≤ C := by
  constructor
  · intro h
    obtain ⟨c, hc, hH, hobs, hdval⟩ :=
      exists_active_power_samples_amplification_attainer N H hm hd hdN hs
    let b := calibratedActiveInterpolant N H (fun _ => 0)
    have hb : b d = 0 := by
      dsimp only [b]
      rw [calibratedActiveInterpolant_coefficient N H (fun _ => 0)
        (Finset.mem_Icc.mpr ⟨hd, hdN⟩) hs]
      simp [activeSawtoothMobiusLift]
    have hbound := h c b hc (calibratedActiveInterpolant_support N H _)
      hH (calibratedActiveInterpolant_harmonic (by omega) H _) (by
        intro j hj hsj
        dsimp only [b]
        rw [calibratedActiveInterpolant_realizes_powers N H (fun _ => 0) hm hj hsj,
          sub_zero]
        exact hobs j hj hsj)
    rwa [hdval, hb, sub_zero, abs_of_nonneg (activeSampleAmplification_nonneg hd)] at hbound
  · intro h c b hc hb _ _ hobs
    have hbound : |c d - b d| ≤ activeSampleAmplification d := by
      simpa using active_power_samples_coefficient_error_le N hc hb hm hd hdN hs 1 hobs
    exact hbound.trans h

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
