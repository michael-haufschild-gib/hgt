import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.Localization.MovingPrimeWindow
import GaloisForLFunctions.BiScaleUncertainty.Localization.LatticeFragments

/-!
# Exact lattice fragments with no diagonal prime interaction

Choosing the lattice scale beyond `6/log 2` puts every fragment below the
first prime aperture. Every diagonal prime sum then vanishes identically,
while the finite lattice decomposition still reconstructs the source exactly.
This links smooth fragmentation to the arithmetic part of short-window energy.
-/

noncomputable section
open Set RHTower
open scoped NNReal
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open BiScaleUncertainty

/-- An explicit scale at which every lattice fragment misses all prime shifts. -/
def primeBlindFragmentScale (n : ℕ) : ℕ := ⌈6 / Real.log 2⌉₊ + n

theorem primeBlindFragmentScale_width (n : ℕ) :
    6 / ((primeBlindFragmentScale n : ℝ) + 1) < Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (6 / Real.log 2)
  have hm : 6 / Real.log 2 < (primeBlindFragmentScale n : ℝ) + 1 := by
    simp only [primeBlindFragmentScale, Nat.cast_add]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hc, hn]
  have h := (div_lt_iff₀ hl).mp hm
  apply (div_lt_iff₀ (by positivity : 0 < (primeBlindFragmentScale n : ℝ) + 1)).mpr
  linarith only [h]

/-- Every fragment at the explicit scale has identically zero diagonal prime interaction. -/
theorem latticeFragment_diagonal_prime_eq_zero (n : ℕ) (j : ℤ) (f : ℝ → ℝ) :
    (∑' k : ℕ, vonMangoldtAtom k *
      crossCorr (latticeFragment (primeBlindFragmentScale n) j f)
        (latticeFragment (primeBlindFragmentScale n) j f) (Real.log k)) = 0 := by
  let m := primeBlindFragmentScale n
  let a : ℝ := (-(j : ℝ) - 3) / ((m : ℝ) + 1)
  let w : ℝ := 6 / ((m : ℝ) + 1)
  have hab : a + w = (-(j : ℝ) + 3) / ((m : ℝ) + 1) := by
    dsimp [a, w]
    ring
  have hs : intervalSource a (a + w) (latticeFragment m j f) = latticeFragment m j f := by
    funext x
    by_cases hx : x ∈ Icc a (a + w)
    · exact indicator_of_mem hx _
    · have hz : latticeFragment m j f x = 0 :=
        latticeFragment_eq_zero_of_outside m j f x (by simpa only [hab] using hx)
      simp only [intervalSource, indicator_of_notMem hx, hz]
  have h := diagonal_interval_prime_interaction_eq_zero a w (latticeFragment m j f)
    (primeBlindFragmentScale_width n)
  simpa only [hs] using h

/-- Finite reconstruction and vanishing diagonal prime sums hold simultaneously at every scale. -/
theorem primeBlind_lattice_decomposition (A : ℝ≥0) (n : ℕ) (f : ℝ → ℝ) :
    (∀ x : ℝ,
      (∑ j ∈ Finset.Icc (-(⌈(A : ℝ) * (primeBlindFragmentScale n + 1) + 3⌉₊ : ℤ))
        (⌈(A : ℝ) * (primeBlindFragmentScale n + 1) + 3⌉₊ : ℤ),
        latticeFragment (primeBlindFragmentScale n) j ((Icc (-(A : ℝ)) A).indicator f) x) =
          (Icc (-(A : ℝ)) A).indicator f x) ∧
    (∀ j : ℤ, (∑' k : ℕ, vonMangoldtAtom k *
      crossCorr (latticeFragment (primeBlindFragmentScale n) j ((Icc (-(A : ℝ)) A).indicator f))
        (latticeFragment (primeBlindFragmentScale n) j ((Icc (-(A : ℝ)) A).indicator f))
          (Real.log k)) = 0) :=
  ⟨sum_latticeFragment_interval A (primeBlindFragmentScale n) f,
    fun j => latticeFragment_diagonal_prime_eq_zero n j _⟩

#print axioms latticeFragment_diagonal_prime_eq_zero
#print axioms primeBlind_lattice_decomposition
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
