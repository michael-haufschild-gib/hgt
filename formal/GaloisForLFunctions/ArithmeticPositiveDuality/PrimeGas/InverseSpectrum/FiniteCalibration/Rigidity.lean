import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Triple
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Scale

/-! # A three-mode calibration identifies the unknown Hamiltonian and its partition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration

open Repeated

def statistic (P : Fin 3 ↪ Nat.Primes) (E : ℕ+ → ℝ) := surprisalCubic (law (sample P E))

def coincidences (P : Fin 3 ↪ Nat.Primes) (E : ℕ+ → ℝ) :=
  moment (law (sample P E)) 2=moment (law (sample P energy)) 2 ∧
  moment (law (sample P E)) 3=moment (law (sample P energy)) 3

/-- The signed cube of twice the real splitting temperature is read from the
canonical and observed centered cubics at independent unit temperature. -/
theorem signed_scale (P : Fin 3 ↪ Nat.Primes) (E : ℕ+ → ℝ) (s : ℂ) (h : Isometric E s) :
    statistic P energy=(2*s.re)^3*statistic P E := by
  have eqn : sample P energy = (fun i => (2*s.re)*sample P E i) :=
    funext fun i => ((isometric_iff_energy E s).mp h (mode (P i))).symm
  rw [statistic,statistic,cubic_gibbs,cubic_gibbs,eqn,cubic_scale]

/-- Agreement of a single symmetric statistic fixes the energies on every
integer, including those outside the measured triple. -/
theorem statistic_iff (P : Fin 3 ↪ Nat.Primes) (E : ℕ+ → ℝ) (s : ℂ) :
    Isometric E s ∧ statistic P E=statistic P energy ↔ E=energy ∧ s.re=1/2 := by
  constructor
  · rintro ⟨iso,reading⟩
    have lawScale := signed_scale P E s iso
    rw [reading] at lawScale
    have nonzero : statistic P energy≠0 := by
      rw [statistic,cubic_gibbs]
      exact prime_cubic_ne_zero P
    have cube : (2*s.re)^3=1 :=
      mul_right_cancel₀ nonzero (lawScale.symm.trans (one_mul _).symm)
    have odd : Odd (3:ℕ) := ⟨1,rfl⟩
    have one : 2*s.re=1 := odd.pow_inj.mp (cube.trans (one_pow 3).symm)
    have terms := (isometric_iff_energy E s).mp iso
    rw [one] at terms
    exact ⟨funext fun n => (one_mul (E n)).symm.trans (terms n),by linarith only [one]⟩
  · rintro ⟨rfl,hs⟩
    exact ⟨(split_isometric_iff s).mpr hs,rfl⟩

/-- Two- and three-copy equality events on any distinct prime triple
identify both the full logarithmic Hamiltonian and the critical line. -/
theorem coincidences_iff (P : Fin 3 ↪ Nat.Primes) (E : ℕ+ → ℝ) (s : ℂ) :
    Isometric E s ∧ coincidences P E ↔ E=energy ∧ s.re=1/2 := by
  constructor
  · rintro ⟨iso,readings⟩
    exact (statistic_iff P E s).mp ⟨iso,cubic_matches ((copies_iff _ _).mp readings)⟩
  · rintro ⟨rfl,hs⟩
    exact ⟨(split_isometric_iff s).mpr hs,rfl,rfl⟩

theorem full_partition (P : Fin 3 ↪ Nat.Primes) (E : ℕ+ → ℝ) (s : ℂ) :
    Isometric E s ∧ coincidences P E ↔ Isometric E s ∧
      ∀ z : {w : ℂ // 1<w.re}, HasSum (fun n => Complex.exp (-z.val*(E n:ℂ))) (riemannZeta z.val) := by
  rw [←one_trace_iff_all (⟨2,by norm_num⟩ : TraceTemperature) E s,
    isometry_and_trace_iff,coincidences_iff]

/-- All coincidence orders with two modes leave two opposite isometric
Hamiltonians indistinguishable. -/
theorem two_mode_ambiguity (P : Fin 2 ↪ Nat.Primes) :
    Isometric energy (1/2) ∧ Isometric (fun n => -energy n) (-(1/2)) ∧
    ∀ j, moment (law (sample P (fun n => -energy n))) j=moment (law (sample P energy)) j := by
  refine ⟨(split_isometric_iff _).mpr (by rw [Complex.div_ofNat_re,Complex.one_re]),
    (isometric_iff_energy _ _).mpr (fun n => ?_),fun j => moment_congr (two_reversed (sample P energy)) j⟩
  rw [Complex.neg_re,Complex.div_ofNat_re,Complex.one_re]
  ring

#print axioms signed_scale
#print axioms statistic_iff
#print axioms coincidences_iff
#print axioms full_partition
#print axioms two_mode_ambiguity

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration
