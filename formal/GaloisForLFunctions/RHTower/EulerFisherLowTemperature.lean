import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.RHTower.LowTemperatureCurvature

/-!
# Low-temperature prime-gap law for the Euler Fisher spectrum

This file specializes the universal two-level curvature mechanism to the bottom of the Euler
prime-power spectrum.  The unique ground and first-excited modes are `2` and `3`; hence the
curvature exponent is `2 * log 2 - log 3 = log (4 / 3) > 0`.
-/

noncomputable section

open Filter Topology

namespace RHTower

/-- Temperature-independent coefficient of an Euler prime-power mode. -/
def eulerPrimePowerCoefficient (z : Nat.Primes × ℕ) : ℝ :=
  (z.2 + 1 : ℝ)⁻¹

private def lowPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
private def lowPrimeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

private def eulerGroundMode : Nat.Primes × ℕ := (lowPrimeTwo, 0)
private def eulerFirstExcitedMode : Nat.Primes × ℕ := (lowPrimeThree, 0)

/-- Every Euler prime power is at least two. -/
theorem two_le_eulerPrimePowerNat (z : Nat.Primes × ℕ) :
    2 ≤ eulerPrimePowerNat z := by
  dsimp [eulerPrimePowerNat]
  exact (z.1.2.two_le).trans (Nat.le_pow (by omega))

/-- The prime-power parametrization has a unique mode at the integer two. -/
theorem eulerPrimePowerNat_eq_two_iff (z : Nat.Primes × ℕ) :
    eulerPrimePowerNat z = 2 ↔ z = eulerGroundMode := by
  constructor
  · intro h
    apply eulerPrimePowerNat_injective
    simpa [eulerGroundMode, lowPrimeTwo, eulerPrimePowerNat] using h
  · rintro rfl
    simp [eulerGroundMode, lowPrimeTwo, eulerPrimePowerNat]

/-- Every Euler mode other than the ground mode is at least three. -/
theorem three_le_eulerPrimePowerNat_of_ne_ground
    (z : Nat.Primes × ℕ) (hz : z ≠ eulerGroundMode) :
    3 ≤ eulerPrimePowerNat z := by
  have htwo := two_le_eulerPrimePowerNat z
  have hne : eulerPrimePowerNat z ≠ 2 := by
    intro h
    exact hz ((eulerPrimePowerNat_eq_two_iff z).1 h)
  omega

/-- The prime-power parametrization has a unique mode at the integer three. -/
theorem eulerPrimePowerNat_eq_three_iff (z : Nat.Primes × ℕ) :
    eulerPrimePowerNat z = 3 ↔ z = eulerFirstExcitedMode := by
  constructor
  · intro h
    apply eulerPrimePowerNat_injective
    simpa [eulerFirstExcitedMode, lowPrimeThree, eulerPrimePowerNat] using h
  · rintro rfl
    simp [eulerFirstExcitedMode, lowPrimeThree, eulerPrimePowerNat]

/-- `log 2` is the unique ground energy of the Euler prime-power spectrum. -/
theorem eulerPrimePowerEnergy_eq_log_two_iff (z : Nat.Primes × ℕ) :
    eulerPrimePowerEnergy z = Real.log 2 ↔ z = eulerGroundMode := by
  have hnpos : 0 < (eulerPrimePowerNat z : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_eulerPrimePowerNat z))
  have h2pos : (0 : ℝ) < 2 := by norm_num
  rw [eulerPrimePowerEnergy]
  constructor
  · intro h
    have hn : (eulerPrimePowerNat z : ℝ) = 2 :=
      Real.strictMonoOn_log.injOn hnpos h2pos h
    exact (eulerPrimePowerNat_eq_two_iff z).1 (by exact_mod_cast hn)
  · intro h
    exact congrArg (fun n : ℕ => Real.log n)
      ((eulerPrimePowerNat_eq_two_iff z).2 h)

/-- Every Euler prime-power energy lies above the ground energy `log 2`. -/
theorem log_two_le_eulerPrimePowerEnergy (z : Nat.Primes × ℕ) :
    Real.log 2 ≤ eulerPrimePowerEnergy z := by
  rw [eulerPrimePowerEnergy]
  exact Real.strictMonoOn_log.monotoneOn
    (by norm_num)
    (by
      show 0 < (eulerPrimePowerNat z : ℝ)
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_eulerPrimePowerNat z)))
    (by exact_mod_cast two_le_eulerPrimePowerNat z)

/-- Every non-ground Euler energy is at least `log 3`. -/
theorem log_three_le_eulerPrimePowerEnergy_of_ne_ground
    (z : Nat.Primes × ℕ) (hz : z ≠ eulerGroundMode) :
    Real.log 3 ≤ eulerPrimePowerEnergy z := by
  rw [eulerPrimePowerEnergy]
  exact Real.strictMonoOn_log.monotoneOn
    (by norm_num)
    (by
      show 0 < (eulerPrimePowerNat z : ℝ)
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_eulerPrimePowerNat z)))
    (by exact_mod_cast three_le_eulerPrimePowerNat_of_ne_ground z hz)

/-- `log 3` is the unique first-excited energy. -/
theorem eulerPrimePowerEnergy_eq_log_three_iff (z : Nat.Primes × ℕ) :
    eulerPrimePowerEnergy z = Real.log 3 ↔ z = eulerFirstExcitedMode := by
  have hnpos : 0 < (eulerPrimePowerNat z : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_eulerPrimePowerNat z))
  have h3pos : (0 : ℝ) < 3 := by norm_num
  rw [eulerPrimePowerEnergy]
  constructor
  · intro h
    have hn : (eulerPrimePowerNat z : ℝ) = 3 :=
      Real.strictMonoOn_log.injOn hnpos h3pos h
    exact (eulerPrimePowerNat_eq_three_iff z).1 (by exact_mod_cast hn)
  · intro h
    exact congrArg (fun n : ℕ => Real.log n)
      ((eulerPrimePowerNat_eq_three_iff z).2 h)

/-- The first-excited Euler energy lies below twice the ground energy because `3 < 4`. -/
theorem log_three_lt_two_mul_log_two :
    Real.log 3 < 2 * Real.log 2 := by
  calc
    Real.log 3 < Real.log 4 :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    _ = Real.log ((2 : ℝ) ^ 2) := by norm_num
    _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num

/-- The Euler low-temperature curvature coefficient is strictly positive. -/
theorem eulerLowTemperatureCurvatureCoefficient_pos :
    0 < (Real.log 3) ^ 2 * (Real.log 3 - Real.log 2) ^ 2 / (Real.log 2) ^ 4 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  positivity

/-- The Euler prime-gap curvature profile belongs to the divergent branch of the universal
two-level law. -/
theorem eulerPrimeGapCurvatureProfile_tendsto_atBot :
    Tendsto
      (lowTemperatureCurvatureProfile
        ((Real.log 3) ^ 2 * (Real.log 3 - Real.log 2) ^ 2 / (Real.log 2) ^ 4)
        (2 * Real.log 2 - Real.log 3))
      atTop atBot := by
  exact lowTemperatureCurvatureProfile_tendsto_atBot
    eulerLowTemperatureCurvatureCoefficient_pos log_three_lt_two_mul_log_two

/-- Rewriting a ground-rescaled exponential summand as the corresponding Euler prime-power
summand times the common factor `exp (β log 2)`. -/
theorem lowTemperatureMomentTerm_euler_eq
    (m : ℕ) (β : ℝ) (z : Nat.Primes × ℕ) :
    lowTemperatureMomentTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
        (Real.log 2) m β z =
      Real.exp (β * Real.log 2) *
        (eulerPrimePowerWeight β z * eulerPrimePowerEnergy z ^ m) := by
  have hnpos : 0 < (eulerPrimePowerNat z : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_eulerPrimePowerNat z))
  rw [eulerPrimePowerWeight, Real.rpow_def_of_pos hnpos]
  dsimp [lowTemperatureMomentTerm, eulerPrimePowerCoefficient, eulerPrimePowerEnergy]
  have hexp :
      Real.exp (-β * (Real.log (eulerPrimePowerNat z) - Real.log 2)) =
        Real.exp (β * Real.log 2) *
          Real.exp (Real.log (eulerPrimePowerNat z) * -β) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, div_eq_mul_inv]
  ring

/-- The norms of the ground-rescaled Euler moment summands decrease once `β ≥ 2`. -/
theorem lowTemperatureEulerMomentTerm_norm_le_at_two
    (m : ℕ) {β : ℝ} (hβ : 2 ≤ β) (z : Nat.Primes × ℕ) :
    ‖lowTemperatureMomentTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
        (Real.log 2) m β z‖ ≤
      ‖lowTemperatureMomentTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
        (Real.log 2) m 2 z‖ := by
  have hgap : 0 ≤ eulerPrimePowerEnergy z - Real.log 2 :=
    sub_nonneg.mpr (log_two_le_eulerPrimePowerEnergy z)
  have hexp : Real.exp (-β * (eulerPrimePowerEnergy z - Real.log 2)) ≤
      Real.exp (-2 * (eulerPrimePowerEnergy z - Real.log 2)) := by
    rw [Real.exp_le_exp]
    nlinarith
  dsimp only [lowTemperatureMomentTerm]
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  gcongr

/-- The bound obtained by freezing a ground-rescaled Euler moment summand at `β = 2` is
summable. -/
theorem summable_lowTemperatureEulerMomentTerm_norm_at_two (m : ℕ) :
    Summable (fun z : Nat.Primes × ℕ =>
      ‖lowTemperatureMomentTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
        (Real.log 2) m 2 z‖) := by
  have hs := summable_abs_eulerPrimePower_moment m 2 (by norm_num)
  have hscaled := hs.mul_left ‖Real.exp ((2 : ℝ) * Real.log 2)‖
  apply hscaled.congr
  intro z
  rw [lowTemperatureMomentTerm_euler_eq]
  simp only [norm_mul, Real.norm_eq_abs, abs_mul]

/-- Exact ground-state selection for every Euler prime-power moment:
`2^β M_m(β) → (log 2)^m`. -/
theorem eulerPrimePowerMoment_scaled_tendsto (m : ℕ) :
    Tendsto (fun β : ℝ => (2 : ℝ) ^ β *
        fisherWeightedTsumMoment
          (eulerPrimePowerWeight β) eulerPrimePowerEnergy m)
      atTop (𝓝 ((Real.log 2) ^ m)) := by
  let bound : Nat.Primes × ℕ → ℝ := fun z =>
    ‖lowTemperatureMomentTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
      (Real.log 2) m 2 z‖
  have hlow := lowTemperatureMoment_tendsto
    eulerPrimePowerCoefficient eulerPrimePowerEnergy eulerGroundMode
    (Real.log 2) m bound
    log_two_le_eulerPrimePowerEnergy eulerPrimePowerEnergy_eq_log_two_iff
    (by simpa [bound] using summable_lowTemperatureEulerMomentTerm_norm_at_two m)
    (by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with β hβ
      intro z
      exact lowTemperatureEulerMomentTerm_norm_le_at_two m hβ z)
  have hc : eulerPrimePowerCoefficient eulerGroundMode = 1 := by
    simp [eulerPrimePowerCoefficient, eulerGroundMode, lowPrimeTwo]
  rw [hc, one_mul] at hlow
  apply hlow.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with β hβ
  have hβone : 1 < β := by linarith
  have hsabs := summable_abs_eulerPrimePower_moment m β hβone
  have hs : Summable (fun z : Nat.Primes × ℕ =>
      eulerPrimePowerWeight β z * eulerPrimePowerEnergy z ^ m) :=
    Summable.of_norm (by simpa [Real.norm_eq_abs] using hsabs)
  have hexp : Real.exp (β * Real.log 2) = (2 : ℝ) ^ β := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [← hexp, fisherWeightedTsumMoment, ← hs.tsum_mul_left]
  exact tsum_congr (lowTemperatureMomentTerm_euler_eq m β)

/-- Ordered-pair dispersion summand in the physical Euler spectrum. -/
def eulerPairDispersionTerm (β : ℝ)
    (z : (Nat.Primes × ℕ) × (Nat.Primes × ℕ)) : ℝ :=
  eulerPrimePowerWeight β z.1 * eulerPrimePowerWeight β z.2 *
    eulerPrimePowerEnergy z.1 ^ 2 * eulerPrimePowerEnergy z.2 ^ 2 *
      (eulerPrimePowerEnergy z.1 - eulerPrimePowerEnergy z.2) ^ 2

/-- Absolute summability of the Euler ordered-pair dispersion at every physical inverse
temperature. -/
theorem summable_abs_eulerPairDispersionTerm
    (β : ℝ) (hβ : 1 < β) :
    Summable (fun z => |eulerPairDispersionTerm β z|) := by
  let a2 : Nat.Primes × ℕ → ℝ := fun i =>
    eulerPrimePowerWeight β i * eulerPrimePowerEnergy i ^ 2
  let a4 : Nat.Primes × ℕ → ℝ := fun i =>
    eulerPrimePowerWeight β i * eulerPrimePowerEnergy i ^ 4
  have h2 : Summable (fun i => ‖a2 i‖) := by
    simpa [a2, Real.norm_eq_abs] using summable_abs_eulerPrimePower_moment 2 β hβ
  have h4 : Summable (fun i => ‖a4 i‖) := by
    simpa [a4, Real.norm_eq_abs] using summable_abs_eulerPrimePower_moment 4 β hβ
  have h24 : Summable (fun z : (Nat.Primes × ℕ) × (Nat.Primes × ℕ) =>
      a2 z.1 * a4 z.2) := summable_mul_of_summable_norm h2 h4
  have h42 : Summable (fun z : (Nat.Primes × ℕ) × (Nat.Primes × ℕ) =>
      a4 z.1 * a2 z.2) := summable_mul_of_summable_norm h4 h2
  have hmajor : Summable (fun z : (Nat.Primes × ℕ) × (Nat.Primes × ℕ) =>
      2 * (a2 z.1 * a4 z.2 + a4 z.1 * a2 z.2)) :=
    (h24.add h42).mul_left 2
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) ?_ hmajor
  rintro ⟨i, j⟩
  have hwi : 0 ≤ eulerPrimePowerWeight β i := by
    dsimp [eulerPrimePowerWeight]
    positivity
  have hwj : 0 ≤ eulerPrimePowerWeight β j := by
    dsimp [eulerPrimePowerWeight]
    positivity
  have hEi : 0 ≤ eulerPrimePowerEnergy i := by
    exact (Real.log_pos (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (two_le_eulerPrimePowerNat i)))).le
  have hEj : 0 ≤ eulerPrimePowerEnergy j := by
    exact (Real.log_pos (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (two_le_eulerPrimePowerNat j)))).le
  have hsq : (eulerPrimePowerEnergy i - eulerPrimePowerEnergy j) ^ 2 ≤
      2 * (eulerPrimePowerEnergy i ^ 2 + eulerPrimePowerEnergy j ^ 2) := by
    nlinarith [sq_nonneg (eulerPrimePowerEnergy i + eulerPrimePowerEnergy j)]
  rw [abs_of_nonneg]
  · dsimp [eulerPairDispersionTerm, a2, a4]
    calc
      eulerPrimePowerWeight β i * eulerPrimePowerWeight β j *
            eulerPrimePowerEnergy i ^ 2 * eulerPrimePowerEnergy j ^ 2 *
            (eulerPrimePowerEnergy i - eulerPrimePowerEnergy j) ^ 2
          ≤ eulerPrimePowerWeight β i * eulerPrimePowerWeight β j *
            eulerPrimePowerEnergy i ^ 2 * eulerPrimePowerEnergy j ^ 2 *
            (2 * (eulerPrimePowerEnergy i ^ 2 + eulerPrimePowerEnergy j ^ 2)) := by
              gcongr
      _ = 2 *
          (eulerPrimePowerWeight β i * eulerPrimePowerEnergy i ^ 2 *
              (eulerPrimePowerWeight β j * eulerPrimePowerEnergy j ^ 4) +
            eulerPrimePowerWeight β i * eulerPrimePowerEnergy i ^ 4 *
              (eulerPrimePowerWeight β j * eulerPrimePowerEnergy j ^ 2)) := by ring
  · dsimp [eulerPairDispersionTerm]
    positivity

/-- Rewriting a first-two-level-rescaled pair summand as the physical Euler dispersion summand
times the common factor `exp (β (log 2 + log 3))`. -/
theorem lowTemperaturePairTerm_euler_eq
    (β : ℝ) (z : (Nat.Primes × ℕ) × (Nat.Primes × ℕ)) :
    lowTemperaturePairTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
        (Real.log 2) (Real.log 3) β z =
      Real.exp (β * (Real.log 2 + Real.log 3)) * eulerPairDispersionTerm β z := by
  rcases z with ⟨i, j⟩
  have hipos : 0 < (eulerPrimePowerNat i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_eulerPrimePowerNat i))
  have hjpos : 0 < (eulerPrimePowerNat j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_eulerPrimePowerNat j))
  rw [eulerPairDispersionTerm, eulerPrimePowerWeight, eulerPrimePowerWeight,
    Real.rpow_def_of_pos hipos, Real.rpow_def_of_pos hjpos]
  dsimp [lowTemperaturePairTerm, eulerPrimePowerCoefficient, eulerPrimePowerEnergy]
  have hexp :
      Real.exp (-β * ((Real.log (eulerPrimePowerNat i) +
          Real.log (eulerPrimePowerNat j)) - (Real.log 2 + Real.log 3))) =
        Real.exp (β * (Real.log 2 + Real.log 3)) *
          (Real.exp (Real.log (eulerPrimePowerNat i) * -β) *
            Real.exp (Real.log (eulerPrimePowerNat j) * -β)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hexp, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The norms of the first-two-level-rescaled Euler pair summands decrease once `β ≥ 2`. -/
theorem lowTemperatureEulerPairTerm_norm_le_at_two
    {β : ℝ} (hβ : 2 ≤ β)
    (z : (Nat.Primes × ℕ) × (Nat.Primes × ℕ)) :
    ‖lowTemperaturePairTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
        (Real.log 2) (Real.log 3) β z‖ ≤
      ‖lowTemperaturePairTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
        (Real.log 2) (Real.log 3) 2 z‖ := by
  rcases z with ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    simp [lowTemperaturePairTerm]
  · have hgap : 0 ≤ (eulerPrimePowerEnergy i + eulerPrimePowerEnergy j) -
        (Real.log 2 + Real.log 3) := by
      by_cases hi : i = eulerGroundMode
      · subst i
        have hj : j ≠ eulerGroundMode := fun h => hij h.symm
        have hEi : eulerPrimePowerEnergy eulerGroundMode = Real.log 2 :=
          (eulerPrimePowerEnergy_eq_log_two_iff eulerGroundMode).2 rfl
        have hEj := log_three_le_eulerPrimePowerEnergy_of_ne_ground j hj
        linarith
      · have hEi := log_three_le_eulerPrimePowerEnergy_of_ne_ground i hi
        have hEj := log_two_le_eulerPrimePowerEnergy j
        linarith
    have hexp :
        Real.exp (-β * ((eulerPrimePowerEnergy i + eulerPrimePowerEnergy j) -
            (Real.log 2 + Real.log 3))) ≤
          Real.exp (-2 * ((eulerPrimePowerEnergy i + eulerPrimePowerEnergy j) -
            (Real.log 2 + Real.log 3))) := by
      rw [Real.exp_le_exp]
      nlinarith
    dsimp only [lowTemperaturePairTerm]
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    gcongr

/-- Freezing the first-two-level-rescaled Euler pair summands at `β = 2` gives a summable
Tannery majorant. -/
theorem summable_lowTemperatureEulerPairTerm_norm_at_two :
    Summable (fun z : (Nat.Primes × ℕ) × (Nat.Primes × ℕ) =>
      ‖lowTemperaturePairTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
        (Real.log 2) (Real.log 3) 2 z‖) := by
  have hs := summable_abs_eulerPairDispersionTerm 2 (by norm_num)
  have hscaled := hs.mul_left
    ‖Real.exp ((2 : ℝ) * (Real.log 2 + Real.log 3))‖
  apply hscaled.congr
  intro z
  rw [lowTemperaturePairTerm_euler_eq]
  simp only [norm_mul, Real.norm_eq_abs]

/-- Exact first-two-level selection for the rescaled Euler pair dispersion. -/
theorem eulerPairDispersion_scaled_tendsto :
    Tendsto (fun β : ℝ => (2 : ℝ)⁻¹ *
        ∑' z, lowTemperaturePairTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
          (Real.log 2) (Real.log 3) β z)
      atTop (𝓝 ((Real.log 2) ^ 2 * (Real.log 3) ^ 2 *
        (Real.log 3 - Real.log 2) ^ 2)) := by
  let bound : (Nat.Primes × ℕ) × (Nat.Primes × ℕ) → ℝ := fun z =>
    ‖lowTemperaturePairTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
      (Real.log 2) (Real.log 3) 2 z‖
  have h23 : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have h := lowTemperaturePairDispersion_tendsto
    eulerPrimePowerCoefficient eulerPrimePowerEnergy
    eulerGroundMode eulerFirstExcitedMode (Real.log 2) (Real.log 3) bound
    h23 eulerPrimePowerEnergy_eq_log_two_iff
    log_three_le_eulerPrimePowerEnergy_of_ne_ground
    eulerPrimePowerEnergy_eq_log_three_iff
    (by simpa [bound] using summable_lowTemperatureEulerPairTerm_norm_at_two)
    (by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with β hβ
      intro z
      exact lowTemperatureEulerPairTerm_norm_le_at_two hβ z)
  have hc1 : eulerPrimePowerCoefficient eulerGroundMode = 1 := by
    simp [eulerPrimePowerCoefficient, eulerGroundMode, lowPrimeTwo]
  have hc2 : eulerPrimePowerCoefficient eulerFirstExcitedMode = 1 := by
    simp [eulerPrimePowerCoefficient, eulerFirstExcitedMode, lowPrimeThree]
  simpa [lowTemperatureDetLeading, hc1, hc2] using h

/-- Exact determinant asymptotic for the Euler Fisher spectrum:
`6^β (M₂ M₄ - M₃²)` converges to the `2,3` prime-gap coefficient. -/
theorem eulerPrimePowerMoment_det_scaled_tendsto :
    Tendsto (fun β : ℝ => (6 : ℝ) ^ β *
      (fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2 *
          fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 4 -
        fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 3 ^ 2))
      atTop (𝓝 ((Real.log 2) ^ 2 * (Real.log 3) ^ 2 *
        (Real.log 3 - Real.log 2) ^ 2)) := by
  apply eulerPairDispersion_scaled_tendsto.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with β hβ
  have hβone : 1 < β := by linarith
  have h2 := summable_abs_eulerPrimePower_moment 2 β hβone
  have h3 := summable_abs_eulerPrimePower_moment 3 β hβone
  have h4 := summable_abs_eulerPrimePower_moment 4 β hβone
  have hQabs := summable_abs_eulerPairDispersionTerm β hβone
  have hQ : Summable (eulerPairDispersionTerm β) :=
    Summable.of_norm (by simpa [Real.norm_eq_abs] using hQabs)
  have hpair :
      (∑' z, lowTemperaturePairTerm eulerPrimePowerCoefficient eulerPrimePowerEnergy
          (Real.log 2) (Real.log 3) β z) =
        Real.exp (β * (Real.log 2 + Real.log 3)) *
          ∑' z, eulerPairDispersionTerm β z := by
    rw [← hQ.tsum_mul_left]
    exact tsum_congr (lowTemperaturePairTerm_euler_eq β)
  have hdisp := two_mul_fisherWeightedTsumMoment_det
    (eulerPrimePowerWeight β) eulerPrimePowerEnergy h2 h3 h4
  have hdisp' :
      2 * (fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2 *
          fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 4 -
        fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 3 ^ 2) =
        ∑' z, eulerPairDispersionTerm β z := by
    simpa [eulerPairDispersionTerm] using hdisp
  have hlog : Real.log 2 + Real.log 3 = Real.log 6 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hexp : Real.exp (β * (Real.log 2 + Real.log 3)) = (6 : ℝ) ^ β := by
    rw [hlog, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [hpair, ← hdisp', hexp]
  ring

/-- Exact low-temperature curvature coefficient.  After multiplication by `(3/4)^β`, the
magnitude of the Euler Fisher scalar curvature converges to the positive `2,3` prime-gap
constant. -/
theorem eulerFisherScalarCurvature_neg_scaled_tendsto :
    Tendsto (fun β : ℝ => ((3 : ℝ) / 4) ^ β *
        (-eulerFisherScalarCurvature β))
      atTop (𝓝 ((Real.log 3) ^ 2 * (Real.log 3 - Real.log 2) ^ 2 /
        (Real.log 2) ^ 4)) := by
  let M : ℝ → ℝ := fun β =>
    (2 : ℝ) ^ β * fisherWeightedTsumMoment
      (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2
  let D : ℝ → ℝ := fun β =>
    (6 : ℝ) ^ β *
      (fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2 *
          fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 4 -
        fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 3 ^ 2)
  have hM : Tendsto M atTop (𝓝 ((Real.log 2) ^ 2)) := by
    simpa [M] using eulerPrimePowerMoment_scaled_tendsto 2
  have hD : Tendsto D atTop (𝓝 ((Real.log 2) ^ 2 * (Real.log 3) ^ 2 *
      (Real.log 3 - Real.log 2) ^ 2)) := by
    simpa [D] using eulerPrimePowerMoment_det_scaled_tendsto
  have hA : (Real.log 2) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (ne_of_gt (Real.log_pos (by norm_num)))
  have hquot := hD.div (hM.pow 3) (pow_ne_zero 3 hA)
  have hconst :
      ((Real.log 2) ^ 2 * (Real.log 3) ^ 2 *
          (Real.log 3 - Real.log 2) ^ 2) / ((Real.log 2) ^ 2) ^ 3 =
        (Real.log 3) ^ 2 * (Real.log 3 - Real.log 2) ^ 2 /
          (Real.log 2) ^ 4 := by
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  rw [hconst] at hquot
  apply hquot.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with β hβ
  have hβone : 1 < β := by linarith
  let m2 := fisherWeightedTsumMoment
    (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2
  let det :=
    fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2 *
        fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 4 -
      fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 3 ^ 2
  have hm2 : m2 ≠ 0 := ne_of_gt (eulerPrimePowerMoment_two_pos β hβone)
  have htwo : ((2 : ℝ) ^ β) ^ 3 = (8 : ℝ) ^ β := by
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hratio : (6 : ℝ) ^ β / (8 : ℝ) ^ β = ((3 : ℝ) / 4) ^ β := by
    rw [← Real.div_rpow (by norm_num : (0 : ℝ) ≤ 6) (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  dsimp [M, D]
  rw [eulerFisherScalarCurvature]
  simp only [neg_div, neg_neg]
  rw [mul_pow, htwo]
  rw [← hratio]
  field_simp

/-- The cold end of the actual Euler Fisher surface is a curvature singularity: its scalar
curvature tends to `-∞`. -/
theorem eulerFisherScalarCurvature_tendsto_atBot :
    Tendsto eulerFisherScalarCurvature atTop atBot := by
  let C : ℝ := (Real.log 3) ^ 2 * (Real.log 3 - Real.log 2) ^ 2 /
    (Real.log 2) ^ 4
  let S : ℝ → ℝ := fun β => ((3 : ℝ) / 4) ^ β *
    (-eulerFisherScalarCurvature β)
  have hC : 0 < C := by
    exact eulerLowTemperatureCurvatureCoefficient_pos
  have hS : Tendsto S atTop (𝓝 C) := by
    simpa [S, C] using eulerFisherScalarCurvature_neg_scaled_tendsto
  have hlog : 0 < Real.log ((4 : ℝ) / 3) :=
    Real.log_pos (by norm_num)
  have hgrow : Tendsto (fun β : ℝ => ((4 : ℝ) / 3) ^ β) atTop atTop := by
    have hlin : Tendsto (fun β : ℝ => Real.log ((4 : ℝ) / 3) * β) atTop atTop :=
      tendsto_id.const_mul_atTop hlog
    have hexp := Real.tendsto_exp_atTop.comp hlin
    simpa [Function.comp_def, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
      using hexp
  have hprod : Tendsto (fun β : ℝ => ((4 : ℝ) / 3) ^ β * S β) atTop atTop :=
    hgrow.atTop_mul_pos hC hS
  have hmag : Tendsto (fun β : ℝ => -eulerFisherScalarCurvature β) atTop atTop := by
    apply hprod.congr'
    filter_upwards with β
    dsimp [S]
    rw [← mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4 / 3)
      (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    norm_num
  have hneg := tendsto_neg_atTop_atBot.comp hmag
  convert hneg using 1
  funext β
  simp

/-- The exact exponential blow-up rate of the cold scalar curvature is `log (4/3)`. -/
theorem eulerFisherScalarCurvature_log_rate_tendsto :
    Tendsto (fun β : ℝ => Real.log (-eulerFisherScalarCurvature β) / β)
      atTop (𝓝 (Real.log ((4 : ℝ) / 3))) := by
  let C : ℝ := (Real.log 3) ^ 2 * (Real.log 3 - Real.log 2) ^ 2 /
    (Real.log 2) ^ 4
  let S : ℝ → ℝ := fun β => ((3 : ℝ) / 4) ^ β *
    (-eulerFisherScalarCurvature β)
  have hC : 0 < C := eulerLowTemperatureCurvatureCoefficient_pos
  have hS : Tendsto S atTop (𝓝 C) := by
    simpa [S, C] using eulerFisherScalarCurvature_neg_scaled_tendsto
  have hlogS : Tendsto (fun β => Real.log (S β)) atTop (𝓝 (Real.log C)) :=
    hS.log (ne_of_gt hC)
  have hsmall : Tendsto (fun β => Real.log (S β) / β) atTop (𝓝 0) :=
    hlogS.div_atTop tendsto_id
  have htarget : Tendsto
      (fun β : ℝ => Real.log ((4 : ℝ) / 3) + Real.log (S β) / β)
      atTop (𝓝 (Real.log ((4 : ℝ) / 3))) := by
    simpa using (tendsto_const_nhds (x := Real.log ((4 : ℝ) / 3))).add hsmall
  apply htarget.congr'
  have hSpos : ∀ᶠ β : ℝ in atTop, 0 < S β :=
    hS.eventually (Ioi_mem_nhds hC)
  filter_upwards [eventually_ge_atTop (2 : ℝ), hSpos] with β hβ hSβ
  have hβ0 : β ≠ 0 := by linarith
  have hfactor : ((4 : ℝ) / 3) ^ β * S β =
      -eulerFisherScalarCurvature β := by
    dsimp [S]
    rw [← mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4 / 3)
      (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    norm_num
  rw [← hfactor, Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) β))
    (ne_of_gt hSβ), Real.log_rpow (by norm_num : (0 : ℝ) < 4 / 3)]
  field_simp

end RHTower
