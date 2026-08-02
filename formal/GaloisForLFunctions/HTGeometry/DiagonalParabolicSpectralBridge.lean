import GaloisForLFunctions.HTGeometry.PolynomialMatrixSimpleSpectrumTransport
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# A universal label-preserving bridge between finite real spectra

Two injectively labelled real spectra `a,b : J → ℝ` are joined by

`(1-t)a + tb + i t(1-t)b`.

At the endpoints this is exactly `a` and `b`.  In the open interval, equality
of two branches would force equality of their imaginary parts and therefore
equality of their `b` labels.  Thus the bridge has simple spectrum throughout
and preserves every label globally.

This explicit parabolic imaginary shear is the common-base mechanism needed
when arbitrary transport would otherwise conjugate a named local monodromy
generator by an unknown permutation.
-/

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

/-- Explicit complex bridge between two real labelled spectra. -/
noncomputable def diagonalParabolicSpectralBridge
    {J : Type*} (a b : J → ℝ) (s : I) (x : J) : ℂ :=
  (1 - (s : ℝ)) * (a x : ℂ) +
    (s : ℝ) * (b x : ℂ) +
    Complex.I * ((s : ℝ) * (1 - (s : ℝ))) * (b x : ℂ)

theorem continuous_diagonalParabolicSpectralBridge
    {J : Type*} (a b : J → ℝ) (x : J) :
    Continuous fun s : I =>
      diagonalParabolicSpectralBridge a b s x := by
  unfold diagonalParabolicSpectralBridge
  fun_prop

@[simp] theorem diagonalParabolicSpectralBridge_zero
    {J : Type*} (a b : J → ℝ) (x : J) :
    diagonalParabolicSpectralBridge a b 0 x = a x := by
  simp [diagonalParabolicSpectralBridge]

@[simp] theorem diagonalParabolicSpectralBridge_one
    {J : Type*} (a b : J → ℝ) (x : J) :
    diagonalParabolicSpectralBridge a b 1 x = b x := by
  simp [diagonalParabolicSpectralBridge]

/-- The parabolic imaginary shear is collision-free for every finite or
infinite label type whenever both endpoint labellings are injective. -/
theorem diagonalParabolicSpectralBridge_injective
    {J : Type*} (a b : J → ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (s : I) :
    Function.Injective
      (diagonalParabolicSpectralBridge a b s) := by
  intro x y hxy
  let t : ℝ := s
  have ht0 : 0 ≤ t := s.2.1
  have ht1 : t ≤ 1 := s.2.2
  by_cases hzero : t = 0
  · apply ha
    have hre := congrArg Complex.re hxy
    norm_num [diagonalParabolicSpectralBridge, t,
      hzero, Complex.mul_re] at hre
    exact hre
  by_cases hone : t = 1
  · apply hb
    have hre := congrArg Complex.re hxy
    norm_num [diagonalParabolicSpectralBridge, t,
      hone, Complex.mul_re] at hre
    exact hre
  have htPos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hzero)
  have htLt : t < 1 := lt_of_le_of_ne ht1 hone
  have hfactor :
      t * (1 - t) ≠ 0 :=
    mul_ne_zero (ne_of_gt htPos)
      (ne_of_gt (sub_pos.mpr htLt))
  apply hb
  have him := congrArg Complex.im hxy
  norm_num [diagonalParabolicSpectralBridge, t,
    Complex.mul_im] at him
  rcases him with hbeq | htzero | htone
  · exact hbeq
  · exact (hzero (by simpa [t] using htzero)).elim
  · exfalso
    apply hone
    linarith

/-- Each labelled branch is a characteristic root of the diagonal bridge
matrix. -/
theorem diagonalParabolicSpectralBridge_charpoly_root
    {J : Type*} [Fintype J] [DecidableEq J]
    (a b : J → ℝ) (s : I) (x : J) :
    (Matrix.diagonal
      (diagonalParabolicSpectralBridge a b s)).charpoly.eval
        (diagonalParabolicSpectralBridge a b s x) = 0 := by
  rw [Matrix.charpoly_diagonal, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ x)
  simp

/-- The bridge has nonzero characteristic resultant at every point. -/
theorem diagonalParabolicSpectralBridge_resultant_ne_zero
    {J : Type*} [Fintype J] [DecidableEq J]
    (a b : J → ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (s : I) :
    Polynomial.resultant
        (Matrix.diagonal
          (diagonalParabolicSpectralBridge a b s)).charpoly
        (Matrix.diagonal
          (diagonalParabolicSpectralBridge a b s)).charpoly.derivative
        (Fintype.card J) (Fintype.card J - 1) ≠ 0 := by
  exact
    matrixCharacteristicResultant_ne_zero_of_complete_injective_roots
      (Matrix.diagonal
        (diagonalParabolicSpectralBridge a b s))
      (diagonalParabolicSpectralBridge a b s)
      (diagonalParabolicSpectralBridge_injective a b ha hb s)
      (diagonalParabolicSpectralBridge_charpoly_root a b s)

/-- Coordinatewise coefficient version of the same bridge. -/
noncomputable def parabolicCoefficientBridge
    {θ : Type*} (p q : θ → ℂ) (s : I) (k : θ) : ℂ :=
  (1 - (s : ℝ)) * p k +
    (s : ℝ) * q k +
    Complex.I * ((s : ℝ) * (1 - (s : ℝ))) * q k

theorem continuous_parabolicCoefficientBridge
    {θ : Type*} (p q : θ → ℂ) :
    Continuous fun s : I => parabolicCoefficientBridge p q s := by
  apply continuous_pi
  intro k
  unfold parabolicCoefficientBridge
  fun_prop

@[simp] theorem parabolicCoefficientBridge_zero
    {θ : Type*} (p q : θ → ℂ) :
    parabolicCoefficientBridge p q 0 = p := by
  funext k
  simp [parabolicCoefficientBridge]

@[simp] theorem parabolicCoefficientBridge_one
    {θ : Type*} (p q : θ → ℂ) :
    parabolicCoefficientBridge p q 1 = q := by
  funext k
  simp [parabolicCoefficientBridge]

end GaloisForLFunctions.HTGeometry
