import GaloisForLFunctions.RHTower.ChiRamanujanPrimeOnlySieve

/-!
# Literal prime-only finite rational atoms

Convolve the compensated divisor source with its finite Möbius square-divisor
sieve. Every rational atom is retained, and finite torsion orthogonality gives
the exact prime-only multiplier before taking either limit.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

/-- Literal square-divisor torsion atoms. Repeated rational nodes are retained. -/
abbrev RamanujanSquareSieveAtomIndex (P : Finset ℕ) :=
  (d : (ramanujanPrimeRadical P).divisors) × Fin (d.val^2)

def ramanujanSquareSieveAtomNode {P : Finset ℕ} (a : RamanujanSquareSieveAtomIndex P) : ℝ :=
  (a.2.val : ℝ) / ((a.1.val^2 : ℕ) : ℝ)

def ramanujanSquareSieveAtomWeight {P : Finset ℕ} (a : RamanujanSquareSieveAtomIndex P) : ℝ :=
  (ArithmeticFunction.moebius a.1.val : ℝ) / ((a.1.val^2 : ℕ) : ℝ)

/-- The finite square-divisor filter is represented by actual rational atoms. -/
theorem sum_ramanujanSquareSieveAtomWeight_fourier (P : Finset ℕ) (n : ℤ) :
    (∑ a : RamanujanSquareSieveAtomIndex P,
      (ramanujanSquareSieveAtomWeight a : ℂ) *
        ramanujanFourierPhase n (ramanujanSquareSieveAtomNode a)) =
      (ramanujanSquareSieveWeight P n.natAbs : ℂ) := by
  classical
  rw [ramanujanSquareSieveWeight_eq_sum, Complex.ofReal_sum, Finset.sum_filter,
    Fintype.sum_sigma]
  conv_rhs => rw [← Finset.sum_attach]
  simp only [Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℕ) ≠ 0 := ne_zero_of_dvd_ne_zero
    (Nat.ne_zero_of_mem_divisors d.property) (Nat.dvd_of_mem_divisors d.property)
  have hd2 : (d : ℕ)^2 ≠ 0 := pow_ne_zero 2 hd0
  dsimp only [ramanujanSquareSieveAtomWeight, ramanujanSquareSieveAtomNode]
  rw [← Finset.mul_sum, sum_ramanujanFourierPhase_torsion hd2]
  split_ifs with hn
  · push_cast
    exact div_mul_cancel₀ _ (by exact_mod_cast hd2)
  · simp

/-- Finite convolution uses every pair of atoms and adds their rational nodes. -/
abbrev RamanujanPrimeOnlyAtomIndex (P : Finset ℕ) :=
  RamanujanAtomIndex P × RamanujanSquareSieveAtomIndex P

def ramanujanPrimeOnlyAtomNode {P : Finset ℕ} (a : RamanujanPrimeOnlyAtomIndex P) : ℝ :=
  ramanujanAtomNode a.1 + ramanujanSquareSieveAtomNode a.2

def ramanujanPrimeOnlyAtomWeight (P : Finset ℕ) (ε : ℝ)
    (a : RamanujanPrimeOnlyAtomIndex P) : ℝ :=
  ramanujanSquareSieveAtomWeight a.2 * ramanujanCompensatedAtomWeight P ε a.1

private theorem fourierPhase_add (n : ℤ) (x y : ℝ) :
    ramanujanFourierPhase n (x+y) = ramanujanFourierPhase n x * ramanujanFourierPhase n y := by
  unfold ramanujanFourierPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact Fourier coefficient of the full prime-only finite rational source. -/
theorem sum_ramanujanPrimeOnlyAtomWeight_fourier (P : Finset ℕ) (ε : ℝ) (n : ℤ) :
    (∑ a : RamanujanPrimeOnlyAtomIndex P,
      (ramanujanPrimeOnlyAtomWeight P ε a : ℂ) * ramanujanFourierPhase n (ramanujanPrimeOnlyAtomNode a)) =
      (ramanujanPrimeOnlyMultiplier P ε n.natAbs : ℂ) := by
  classical
  rw [ramanujanPrimeOnlyMultiplier, Complex.ofReal_mul,
    ← sum_ramanujanSquareSieveAtomWeight_fourier P n,
    ← sum_ramanujanCompensatedAtomWeight_fourier P ε n]
  conv_rhs => rw [mul_comm]
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  dsimp [ramanujanPrimeOnlyAtomWeight, ramanujanPrimeOnlyAtomNode]
  rw [fourierPhase_add]
  push_cast
  ring

end RHTower.BAGTrace
