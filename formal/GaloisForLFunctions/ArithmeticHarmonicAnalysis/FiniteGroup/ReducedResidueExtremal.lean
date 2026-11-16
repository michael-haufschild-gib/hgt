import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResidueConductor

/-!
# The extremal residue as a small-divisor condition

The residues of `(N-1)R` and `R` sum to `N` unless both vanish.
Consequently the extremal conductor criterion says exactly that the
least nonnegative residue of `R` is zero or a divisor of `N`.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The last multiplication residue is maximal exactly when the first residue is zero or the common divisor. -/
theorem last_mul_residue_max_iff (N R : ℕ) (hN : 0 < N) :
    (N - 1) * R % N = N - Nat.gcd N R ↔
      R % N = 0 ∨ R % N = Nat.gcd N R := by
  let a := (N - 1) * R % N
  let b := R % N
  have ha : a < N := Nat.mod_lt _ hN
  have hb : b < N := Nat.mod_lt _ hN
  have hprod : (N - 1) * R + R = N * R := by
    calc
      (N - 1) * R + R = (N - 1 + 1) * R := by ring
      _ = N * R := by rw [Nat.sub_add_cancel hN]
  have hsum : (a + b) % N = 0 := by
    calc
      (a + b) % N = ((N - 1) * R + R) % N := (Nat.add_mod _ _ _).symm
      _ = 0 := by rw [hprod]; simp only [Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod]
  by_cases hbzero : b = 0
  · have hazero : a = 0 := by rwa [hbzero, add_zero, Nat.mod_eq_of_lt ha] at hsum
    have hd : N ∣ R := Nat.dvd_iff_mod_eq_zero.mpr hbzero
    change a = N - Nat.gcd N R ↔ b = 0 ∨ b = Nat.gcd N R
    simp only [hazero, hbzero, Nat.gcd_eq_left hd, Nat.sub_self, true_or]
  · have hdiv : N ∣ a + b := Nat.dvd_iff_mod_eq_zero.mpr hsum
    have hle : N ≤ a + b := Nat.le_of_dvd (by omega) hdiv
    have hupper : a + b ≤ N := by
      by_contra h
      have hpos : 0 < a + b - N := Nat.sub_pos_of_lt (by omega)
      have hsub : N ∣ a + b - N := Nat.dvd_sub hdiv (dvd_refl N)
      have hbound := Nat.le_of_dvd hpos hsub
      omega
    have he : a + b = N := le_antisymm hupper hle
    have hg : Nat.gcd N R ≤ N := Nat.le_of_dvd hN (Nat.gcd_dvd_left N R)
    change a = N - Nat.gcd N R ↔ b = 0 ∨ b = Nat.gcd N R
    omega

/-- A nonzero residue equals the common divisor exactly when it divides the modulus. -/
theorem residue_eq_gcd_iff_dvd (N R : ℕ) :
    R % N = Nat.gcd N R ↔ R % N ∣ N := by
  constructor
  · intro h
    rw [h]
    exact Nat.gcd_dvd_left N R
  · intro h
    apply Nat.dvd_antisymm
    · exact Nat.dvd_gcd h ((Nat.dvd_mod_iff h).mp (dvd_refl (R % N)))
    · exact (Nat.dvd_mod_iff (Nat.gcd_dvd_left N R)).mpr (Nat.gcd_dvd_right N R)

/-- The extremal conductor residue is characterized by a zero residue or a small divisor of the covering degree. -/
theorem last_mul_residue_max_iff_dvd (N R : ℕ) (hN : 0 < N) :
    (N - 1) * R % N = N - Nat.gcd N R ↔ R % N = 0 ∨ R % N ∣ N := by
  rw [last_mul_residue_max_iff N R hN, residue_eq_gcd_iff_dvd]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
