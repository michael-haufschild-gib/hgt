import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Radix
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Marginal
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.CyclicPhase
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp

/-! # A finite-order prime occupation clock and its measured Gibbs law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift

/-- The number-operator phase of the selected prime in a full occupation. -/
def digitPhase (q : Nat.Primes) (d : ℕ+) (n : ℕ+) : ℂ :=
  (clockRoot d:ℂ)^(primeCoordinates q n).1

theorem digitPhase_norm (q : Nat.Primes) (d : ℕ+) (n : ℕ+) : ‖digitPhase q d n‖ = 1 := by
  rw [digitPhase,norm_pow,Circle.norm_coe,one_pow]

/-- A bounded diagonal clock on the undeformed Hilbert space. -/
def digitClock (q : Nat.Primes) (d : ℕ+) : Gas →L[ℂ] Gas :=
  HTGeometry.LpDiagonal.lpDiag (digitPhase q d) 1 zero_le_one (fun n => (digitPhase_norm q d n).le)

theorem digitClock_pow_apply (q : Nat.Primes) (d : ℕ+) (k : ℕ) (f : Gas) (n : ℕ+) :
    ((digitClock q d)^k) f n = (digitPhase q d n)^k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp]
    change digitPhase q d n * (((digitClock q d)^k) f n) = _
    rw [ih,pow_succ',mul_assoc]

theorem digitClock_norm (q : Nat.Primes) (d : ℕ+) (f : Gas) : ‖digitClock q d f‖ = ‖f‖ := by
  have hs : ‖digitClock q d f‖^2 = ‖f‖^2 := by
    rw [HTGeometry.lp_norm_sq_eq_tsum,HTGeometry.lp_norm_sq_eq_tsum]
    apply tsum_congr
    intro n
    change ‖digitPhase q d n * f n‖^2 = _
    rw [norm_mul,digitPhase_norm,one_mul]
  nlinarith only [hs,norm_nonneg (digitClock q d f),norm_nonneg f]

/-- Its exact order is d, witnessed by a single quantum at q. -/
theorem digitClock_power_iff (q : Nat.Primes) (d : ℕ+) (k : ℕ) :
    (digitClock q d)^k = 1 ↔ d.val ∣ k := by
  constructor
  · intro he
    let n := primeRayLabel q 1
    let v : Gas := lp.single 2 n 1
    have hh := congrArg (fun T : Gas →L[ℂ] Gas => T v n) he
    apply ((clockRoot_primitive d).pow_eq_one_iff_dvd k).mp
    simpa only [digitClock_pow_apply,n,v,digitPhase,primeCoordinates_ray,pow_one,
      lp.single_apply,Pi.single_eq_same,mul_one,one_apply_eq_self] using hh
  · intro hd
    have hr := ((clockRoot_primitive d).pow_eq_one_iff_dvd k).mpr hd
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext n
    rw [digitClock_pow_apply,digitPhase,← pow_mul,Nat.mul_comm _ k,pow_mul,hr,one_pow,one_mul]
    rfl

private theorem phase_pair (q : Nat.Primes) (d : ℕ+) (i : Fin d.val) (b : radixComplement q d) :
    digitPhase q d (primeRayLabel q i.val * b.val) = (clockRoot d:ℂ)^i.val := by
  obtain ⟨k,hk⟩ := b.property
  rw [digitPhase,primeCoordinates_mul_ray]
  change (clockRoot d:ℂ)^(i.val+(primeCoordinates q b.val).1) = _
  rw [hk,pow_add,pow_mul,(clockRoot_primitive d).pow_eq_one,one_pow,mul_one]

/-- The measured eigenspace of a digit is exactly its tensor fiber. -/
theorem digitPhase_fiber (q : Nat.Primes) (d : ℕ+) (i : Fin d.val) (n : ℕ+) :
    digitPhase q d n = (clockRoot d:ℂ)^i.val ↔
      n ∈ Set.range (fun b : radixComplement q d => primeRayLabel q i.val*b.val) := by
  constructor
  · intro he
    obtain ⟨⟨j,b⟩,hj⟩ := (radix_exact q d).2 n
    change primeRayLabel q j.val*b.val = n at hj
    rw [← hj,phase_pair] at he
    have hji : j = i := Fin.ext ((clockRoot_primitive d).pow_inj j.isLt i.isLt he)
    subst j
    exact ⟨b,hj⟩
  · rintro ⟨b,rfl⟩
    exact phase_pair q d i b

/-- The clock on the full Gibbs wave has the finite geometric distribution of the extracted digit. -/
theorem digitClock_probability (χ : ℕ+ → Circle) (β : TraceTemperature) (q : Nat.Primes) (d : ℕ+) (i : Fin d.val) :
    selectedMass (fun n => ‖coherentVector χ β n‖^2) (fun n => digitPhase q d n = (clockRoot d:ℂ)^i.val) =
      (thermalWeight β (primePNat q))^i.val / ∑ j : Fin d.val, (thermalWeight β (primePNat q))^j.val := by
  rw [selectedMass_congr _ (digitPhase_fiber q d i)]
  change marginal χ β (fun j : Fin d.val => primeRayLabel q j.val) (fun b : radixComplement q d => b.val) i = _
  rw [marginal_eq_gibbs χ β (radix_exact q d)]
  change thermalWeight β (primeRayLabel q i.val) / (∑ j : Fin d.val, thermalWeight β (primeRayLabel q j.val)) = _
  have hw (k : ℕ) : thermalWeight β (primeRayLabel q k) = (thermalWeight β (primePNat q))^k := by
    rw [thermalWeight,energy_primeRayLabel,thermalWeight,← Real.exp_nat_mul]
    congr 1
    ring
  simp only [hw]

#print axioms digitPhase_norm
#print axioms digitClock_pow_apply
#print axioms digitClock_norm
#print axioms digitClock_power_iff
#print axioms digitPhase_fiber
#print axioms digitClock_probability

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
