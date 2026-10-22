import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorBoundaryFlux
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaurentPhysicalRadiation

/-!
# Horizon values of the `++` Laurent particulars at the fundamental harmonic

The undressed `++` Laurent particulars `r + A/r + B/r³` (scalar–scalar) and `A/r + B/r³`
(vector–vector) take at the horizon `r = 1` the values `1 + A + B` and `A + B`. For a source
regular at the horizon the retarded response is the Laurent particular itself and the advanced
response is the particular corrected by the normalizable doubled-rate solution `h` so as to vanish
at the horizon, `y − (y(1)/h(1))·h`; the difference of the two, the causal cut of the response, is
therefore `(y(1)/h(1))·h`, and the horizon value `y(1)` is the radiation amplitude of the source.
At the fundamental harmonic `μ = (s+1)(s+2)` these values are the rational functions recorded here;
at the physical rates `s = ρ − 2` and `s = −ρ − 1` of an `Ξ` copy they are polynomials or simple
rational functions of `ρ`.
-/

set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section

/-- Horizon value of the scalar–scalar Laurent particular `r + A/r + B/r³` at the fundamental harmonic. -/
def laurentHorizonSS (s : ℂ) : ℂ :=
  1 + laurentMasterA s ((s + 1) * (s + 2)) + laurentMasterB s ((s + 1) * (s + 2))

/-- Horizon value of the vector–vector Laurent particular `A/r + B/r³` at the fundamental harmonic. -/
def laurentHorizonVV (s : ℂ) : ℂ :=
  vvLaurentMasterA s ((s + 1) * (s + 2)) + vvLaurentMasterB s ((s + 1) * (s + 2))

theorem laurentHorizonSS_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    laurentHorizonSS s = (s ^ (4 : ℕ) + 2 * s ^ (3 : ℕ) + 5 * s ^ (2 : ℕ) - 24 * s - 8) / 8 := by
  unfold laurentHorizonSS
  rw [ssLaurentA_lam s hs hs3 hs1, ssLaurentB_lam s hs hs3]
  field_simp
  ring

theorem laurentHorizonVV_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    laurentHorizonVV s = -(s * (12 * s ^ (4 : ℕ) + 87 * s ^ (3 : ℕ) + 230 * s ^ (2 : ℕ) + 229 * s + 18)) / (6 * (s + 3)) := by
  unfold laurentHorizonVV
  rw [vvLaurentA_lam s hs hs3 hs1, vvLaurentB_lam s hs hs3]
  field_simp
  ring

/-- The physical rates of an `Ξ` copy satisfy the three non-degeneracy conditions. -/
theorem physicalRate_ne_zero (q : XiZeroCopy) (branch : Bool) : physicalRate q branch ≠ 0 := by
  cases branch <;> simp only [physicalRate, Bool.false_eq_true, if_false, if_true]
  · have := xiCopy_add_real_ne_zero q 1; push_cast at this; intro h; apply this; linear_combination -h
  · simpa using xiCopy_sub_real_ne_zero q 2

theorem physicalRate_add_three_ne_zero (q : XiZeroCopy) (branch : Bool) : physicalRate q branch + 3 ≠ 0 := by
  cases branch <;> simp only [physicalRate, Bool.false_eq_true, if_false, if_true]
  · have := xiCopy_sub_real_ne_zero q 2; push_cast at this; intro h; apply this; linear_combination -h
  · have := xiCopy_add_real_ne_zero q 1; push_cast at this; intro h; apply this; linear_combination h

theorem physicalRate_add_one_ne_zero (q : XiZeroCopy) (branch : Bool) : physicalRate q branch + 1 ≠ 0 := by
  cases branch <;> simp only [physicalRate, Bool.false_eq_true, if_false, if_true]
  · have := xiCopy_sub_real_ne_zero q 0; push_cast at this; intro h; apply this; linear_combination -h
  · have := xiCopy_sub_real_ne_zero q 1; push_cast at this; intro h; apply this; linear_combination h

/-- Scalar–scalar radiation amplitude on the `+` branch `s = ρ − 2`. -/
theorem laurentHorizonSS_physical_plus (q : XiZeroCopy) :
    laurentHorizonSS (physicalRate q true) =
      ((q.1 : ℂ) ^ (4 : ℕ) - 6 * (q.1 : ℂ) ^ (3 : ℕ) + 17 * (q.1 : ℂ) ^ (2 : ℕ) - 52 * (q.1 : ℂ) + 60) / 8 := by
  rw [laurentHorizonSS_eq _ (physicalRate_ne_zero q true) (physicalRate_add_three_ne_zero q true)
    (physicalRate_add_one_ne_zero q true)]
  simp only [physicalRate, if_true]
  ring

/-- Scalar–scalar radiation amplitude on the `−` branch `s = −ρ − 1`, the reflection `ρ ↦ 1 − ρ` of the `+` branch. -/
theorem laurentHorizonSS_physical_minus (q : XiZeroCopy) :
    laurentHorizonSS (physicalRate q false) =
      ((q.1 : ℂ) ^ (4 : ℕ) + 2 * (q.1 : ℂ) ^ (3 : ℕ) + 5 * (q.1 : ℂ) ^ (2 : ℕ) + 32 * (q.1 : ℂ) + 20) / 8 := by
  rw [laurentHorizonSS_eq _ (physicalRate_ne_zero q false) (physicalRate_add_three_ne_zero q false)
    (physicalRate_add_one_ne_zero q false)]
  simp only [physicalRate, Bool.false_eq_true, if_false]
  ring

/-- Vector–vector radiation amplitude on the `+` branch. -/
theorem laurentHorizonVV_physical_plus (q : XiZeroCopy) :
    laurentHorizonVV (physicalRate q true) =
      -(((q.1 : ℂ) - 2) * (12 * (q.1 : ℂ) ^ (4 : ℕ) - 9 * (q.1 : ℂ) ^ (3 : ℕ) - 4 * (q.1 : ℂ) ^ (2 : ℕ) - 31 * (q.1 : ℂ) - 24)) /
        (6 * ((q.1 : ℂ) + 1)) := by
  rw [laurentHorizonVV_eq _ (physicalRate_ne_zero q true) (physicalRate_add_three_ne_zero q true)
    (physicalRate_add_one_ne_zero q true)]
  simp only [physicalRate, if_true]
  have h1 : (q.1 : ℂ) + 1 ≠ 0 := by simpa using xiCopy_add_real_ne_zero q 1
  have h3 : (q.1 : ℂ) - 2 + 3 ≠ 0 := by intro h; apply h1; linear_combination h
  field_simp
  ring

/-- Vector–vector radiation amplitude on the `−` branch. -/
theorem laurentHorizonVV_physical_minus (q : XiZeroCopy) :
    laurentHorizonVV (physicalRate q false) =
      (((q.1 : ℂ) + 1) * (-12 * (q.1 : ℂ) ^ (4 : ℕ) + 39 * (q.1 : ℂ) ^ (3 : ℕ) - 41 * (q.1 : ℂ) ^ (2 : ℕ) - 18 * (q.1 : ℂ) + 56)) /
        (6 * ((q.1 : ℂ) - 2)) := by
  rw [laurentHorizonVV_eq _ (physicalRate_ne_zero q false) (physicalRate_add_three_ne_zero q false)
    (physicalRate_add_one_ne_zero q false)]
  simp only [physicalRate, Bool.false_eq_true, if_false]
  have h2 : (q.1 : ℂ) - 2 ≠ 0 := by simpa using xiCopy_sub_real_ne_zero q 2
  have h3 : -(q.1 : ℂ) - 1 + 3 ≠ 0 := by intro h; apply h2; linear_combination -h
  field_simp
  ring

end
end RHTower.D4BMScalarStream
