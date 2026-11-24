import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.DivisorSieve
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.ClockAliases

/-! # Recovery of the pure prime ray from a single return event -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology MeasureTheory
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Probability of the exact return event at the D-block clock. -/
def primeReturnMass (v : MissingWave) (p : Nat.Primes) (D : ℕ+) : ℝ :=
  ((occupationPhaseLaw v (primeClockTime p D) : Measure Circle) {1}).toReal

theorem primeReturnMass_eq (v : MissingWave) (p : Nat.Primes) (D : ℕ+) :
    primeReturnMass v p D =
      selectedMass (fun e => occupationProbability v (primeRayLabel p e)) (fun e => D.val ∣ e) := by
  rw [primeReturnMass,phaseLaw_as_labelReport,labelReportLaw_atom]
  let f (n : ℕ+) := if occupationPhase (primeClockTime p D) n = 1 then occupationProbability v n else 0
  have hsupport : Function.support f ⊆ Set.range (primeRayLabel p) := by
    intro n hn
    by_cases he : occupationPhase (primeClockTime p D) n = 1
    · obtain ⟨e,rfl,_⟩ := (primeClock_phase_one p D n).mp he
      exact ⟨e,rfl⟩
    · exact False.elim (hn (if_neg he))
  change ∑' n, f n = _
  rw [← (primeRayLabel_injective p).tsum_eq hsupport]
  apply tsum_congr
  intro e
  have h : occupationPhase (primeClockTime p D) (primeRayLabel p e) = 1 ↔ D.val ∣ e := by
    rw [primeClock_phase_one]
    constructor
    · rintro ⟨k,hk,hd⟩
      exact ((primeRayLabel_injective p) hk).symm ▸ hd
    · exact fun hd => ⟨e,rfl,hd⟩
  simp only [f,h]

private theorem ray_summable (v : MissingWave) (p : Nat.Primes) :
    Summable (fun e => occupationProbability v (primeRayLabel p e)) :=
  (occupationLaw_hasSum v).summable.comp_injective (primeRayLabel_injective p)

/-- Denominators tending to infinity isolate the exponent zero, the vacuum. -/
theorem primeReturnMass_vacuum (v : MissingWave) (p : Nat.Primes) :
    Tendsto (fun j : ℕ => primeReturnMass v p j.succPNat) atTop (𝓝 (occupationProbability v 1)) := by
  simp_rw [primeReturnMass_eq]
  rw [← show primeRayLabel p 0 = 1 from pow_zero _]
  apply selectedMass_limit_singleton (fun e => occupationLaw_nonneg v (primeRayLabel p e))
    (ray_summable v p) _ 0
  intro e
  filter_upwards [eventually_gt_atTop e] with j hj
  change (j+1 ∣ e) ↔ e = 0
  constructor
  · intro hd
    by_contra hn
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
    omega
  · rintro rfl
    exact dvd_zero _

theorem primeReturnMass_sieve (v : MissingWave) (p : Nat.Primes) (h : ℕ+) :
    Tendsto (fun N => sieveReading (primeReturnMass v p) (multipleExclusions h N) h)
      atTop (𝓝 (occupationProbability v (primeRayLabel p h.val))) := by
  rw [funext (primeReturnMass_eq v p)]
  exact sieveReading_limit (fun e => occupationLaw_nonneg v (primeRayLabel p e)) (ray_summable v p) h

theorem primeReturnMass_sieve_antitone (v : MissingWave) (p : Nat.Primes) (h : ℕ+) :
    Antitone (fun N => sieveReading (primeReturnMass v p) (multipleExclusions h N) h) := by
  rw [funext (primeReturnMass_eq v p)]
  exact sieveReading_antitone (fun e => occupationLaw_nonneg v (primeRayLabel p e)) (ray_summable v p) h

/-- Scalar return probabilities at one clock identify exactly the probabilities on its prime ray. -/
theorem primeReturnMass_identifies_ray (p : Nat.Primes) (v w : MissingWave) :
    primeReturnMass v p = primeReturnMass w p ↔
      ∀ e, occupationProbability v (primeRayLabel p e) = occupationProbability w (primeRayLabel p e) := by
  constructor
  · intro he e
    cases e with
    | zero =>
      have hv := primeReturnMass_vacuum v p
      rw [he] at hv
      simpa [primeRayLabel] using tendsto_nhds_unique hv (primeReturnMass_vacuum w p)
    | succ k =>
      have hv := primeReturnMass_sieve v p k.succPNat
      rw [he] at hv
      exact tendsto_nhds_unique hv (primeReturnMass_sieve w p k.succPNat)
  · intro he
    funext D
    rw [primeReturnMass_eq,primeReturnMass_eq,funext he]

#print axioms primeReturnMass_eq
#print axioms primeReturnMass_vacuum
#print axioms primeReturnMass_sieve
#print axioms primeReturnMass_sieve_antitone
#print axioms primeReturnMass_identifies_ray

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
