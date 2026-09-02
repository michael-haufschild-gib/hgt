import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionCoefficientMass

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

/-!
# Principal and original Barban--Vehov bivariate coefficients

The principal coefficient is a diagonal reciprocal series convolved with two copies of the
reciprocal--Möbius amplitude.  The original coefficient is the literal Möbius/gcd kernel.
-/

namespace RHTower.Sieve

noncomputable section

def selbergDiagonalReciprocalCoeff (m n : ℕ) : ℝ :=
  if m = n then reciprocalNatArithmetic m else 0

def selbergMoebiusReciprocalCoeff (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)

@[simp] theorem selbergMoebiusReciprocalCoeff_one :
    selbergMoebiusReciprocalCoeff 1 = 1 := by
  simp [selbergMoebiusReciprocalCoeff]

theorem selbergMoebiusReciprocalCoeff_mul_of_coprime {m n : ℕ}
    (h : Nat.Coprime m n) :
    selbergMoebiusReciprocalCoeff (m * n) =
      selbergMoebiusReciprocalCoeff m * selbergMoebiusReciprocalCoeff n := by
  rw [selbergMoebiusReciprocalCoeff, selbergMoebiusReciprocalCoeff,
    selbergMoebiusReciprocalCoeff,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
  push_cast
  ring

def selbergMoebiusReciprocalPair (m n : ℕ) : ℝ :=
  selbergMoebiusReciprocalCoeff m * selbergMoebiusReciprocalCoeff n

private theorem pair_product_eq_iff_of_pair_coprime
    {a b c d : ℕ} (ha : 0 < a)
    (h : Nat.Coprime (a * b) (c * d)) :
    a * c = b * d ↔ a = b ∧ c = d := by
  have had : Nat.Coprime a d :=
    (h.of_dvd_left (dvd_mul_right a b)).of_dvd_right (dvd_mul_left d c)
  have hbc : Nat.Coprime b c :=
    (h.of_dvd_left (dvd_mul_left b a)).of_dvd_right (dvd_mul_right c d)
  constructor
  · intro heq
    have hab : a ∣ b := by
      apply had.dvd_of_dvd_mul_left
      refine ⟨c, ?_⟩
      simpa [Nat.mul_comm] using heq.symm
    have hba : b ∣ a := by
      apply hbc.dvd_of_dvd_mul_left
      refine ⟨d, ?_⟩
      simpa [Nat.mul_comm] using heq
    have habEq : a = b := Nat.dvd_antisymm hab hba
    subst b
    constructor
    · rfl
    · exact Nat.mul_left_cancel ha heq
  · rintro ⟨rfl, rfl⟩
    rfl

theorem bivariateMultiplicative_selbergDiagonalReciprocalCoeff :
    BivariateMultiplicative selbergDiagonalReciprocalCoeff := by
  constructor
  · simp [selbergDiagonalReciprocalCoeff]
  · intro a b c d h
    by_cases hab0 : a * b = 0
    · have hcd1 : c * d = 1 := by
        rw [Nat.Coprime, hab0] at h
        simpa using h
      have hc1 : c = 1 := Nat.dvd_one.mp ⟨d, hcd1.symm⟩
      have hd1 : d = 1 := Nat.dvd_one.mp ⟨c, by simpa [Nat.mul_comm] using hcd1.symm⟩
      subst c
      subst d
      rcases Nat.mul_eq_zero.mp hab0 with rfl | rfl <;>
        simp [selbergDiagonalReciprocalCoeff, reciprocalNatArithmetic]
    by_cases hcd0 : c * d = 0
    · have hab1 : a * b = 1 := by
        rw [Nat.Coprime, hcd0] at h
        simpa using h
      have ha1 : a = 1 := Nat.dvd_one.mp ⟨b, hab1.symm⟩
      have hb1 : b = 1 := Nat.dvd_one.mp ⟨a, by simpa [Nat.mul_comm] using hab1.symm⟩
      subst a
      subst b
      rcases Nat.mul_eq_zero.mp hcd0 with rfl | rfl <;>
        simp [selbergDiagonalReciprocalCoeff, reciprocalNatArithmetic]
    have ha : 0 < a := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hb : 0 < b := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hc : 0 < c := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    have hd : 0 < d := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    have hac : Nat.Coprime a c :=
      (h.of_dvd_left (dvd_mul_right a b)).of_dvd_right (dvd_mul_right c d)
    have heq := pair_product_eq_iff_of_pair_coprime ha h
    by_cases hab : a = b <;> by_cases hcd : c = d
    · subst b
      subst d
      simp [selbergDiagonalReciprocalCoeff,
        isMultiplicative_reciprocalNatArithmetic.map_mul_of_coprime hac]
    · subst b
      have hne : a * c ≠ a * d := fun he => hcd (heq.mp he).2
      simp [selbergDiagonalReciprocalCoeff, hcd, hne]
    · subst d
      have hne : a * c ≠ b * c := fun he => hab (heq.mp he).1
      simp [selbergDiagonalReciprocalCoeff, hab, hne]
    · have hne : a * c ≠ b * d := fun he => hab (heq.mp he).1
      simp [selbergDiagonalReciprocalCoeff, hab, hcd, hne]

theorem bivariateMultiplicative_selbergMoebiusReciprocalPair :
    BivariateMultiplicative selbergMoebiusReciprocalPair := by
  constructor
  · simp [selbergMoebiusReciprocalPair]
  · intro a b c d h
    have hac : Nat.Coprime a c :=
      (h.of_dvd_left (dvd_mul_right a b)).of_dvd_right (dvd_mul_right c d)
    have hbd : Nat.Coprime b d :=
      (h.of_dvd_left (dvd_mul_left b a)).of_dvd_right (dvd_mul_left d c)
    rw [selbergMoebiusReciprocalPair, selbergMoebiusReciprocalPair,
      selbergMoebiusReciprocalPair,
      selbergMoebiusReciprocalCoeff_mul_of_coprime hac,
      selbergMoebiusReciprocalCoeff_mul_of_coprime hbd]
    ring

/-- Principal bivariate Euler coefficient
`((1-X/p)(1-Y/p))/(1-XY/p)` at every prime. -/
def selbergPrincipalCoeff : ℕ → ℕ → ℝ :=
  bivariateDirichletConvolution selbergDiagonalReciprocalCoeff
    selbergMoebiusReciprocalPair

theorem bivariateMultiplicative_selbergPrincipalCoeff :
  BivariateMultiplicative selbergPrincipalCoeff :=
  bivariateMultiplicative_selbergDiagonalReciprocalCoeff.convolution
    bivariateMultiplicative_selbergMoebiusReciprocalPair

/-- Literal Möbius/gcd coefficient of the Barban--Vehov lcm quadratic form. -/
def selbergOriginalCoeff (m n : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ)) *
    (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)) *
      (Nat.gcd m n : ℝ)

@[simp] theorem selbergOriginalCoeff_one : selbergOriginalCoeff 1 1 = 1 := by
  simp [selbergOriginalCoeff]

theorem selbergOriginalCoeff_comm (m n : ℕ) :
    selbergOriginalCoeff m n = selbergOriginalCoeff n m := by
  rw [selbergOriginalCoeff, selbergOriginalCoeff, Nat.gcd_comm]
  ring

theorem bivariateMultiplicative_selbergOriginalCoeff :
    BivariateMultiplicative selbergOriginalCoeff := by
  constructor
  · exact selbergOriginalCoeff_one
  · intro a b c d h
    by_cases hab0 : a * b = 0
    · rcases Nat.mul_eq_zero.mp hab0 with rfl | rfl <;>
        simp [selbergOriginalCoeff]
    by_cases hcd0 : c * d = 0
    · rcases Nat.mul_eq_zero.mp hcd0 with rfl | rfl <;>
        simp [selbergOriginalCoeff]
    have hac : Nat.Coprime a c :=
      (h.of_dvd_left (dvd_mul_right a b)).of_dvd_right (dvd_mul_right c d)
    have hbd : Nat.Coprime b d :=
      (h.of_dvd_left (dvd_mul_left b a)).of_dvd_right (dvd_mul_left d c)
    have hmua := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hac
    have hmub := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hbd
    rw [selbergOriginalCoeff, selbergOriginalCoeff, selbergOriginalCoeff,
      hmua, hmub, gcd_pair_mul_of_pair_coprime h]
    push_cast
    ring

end

end RHTower.Sieve
