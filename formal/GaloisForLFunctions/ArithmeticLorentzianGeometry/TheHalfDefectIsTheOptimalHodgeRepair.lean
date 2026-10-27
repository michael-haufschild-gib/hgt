import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanDefectCountsTheOuterEigenvalues
import GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia

/-!
# The half-defect is the optimal Hodge repair

Split Frobenius evaluation into its even and odd parts under circle reflection. The reflected
Gram is the even Gram minus the odd Gram. Adding the odd Gram therefore restores positivity;
its quadratic form is one half of the usual reflection defect. Once the window contains the
spectrum, this correction has the least possible rank, the number of distinct outer eigenvalues.
The construction preserves the pole couplings of the completed intersection form.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Complex Finset Matrix
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The reflection-even part of Frobenius evaluation. -/
def frobeniusEven (n : ℕ) : Matrix ι (Fin n) ℂ :=
  fun j k => (D.β j ^ (k : ℕ) + circleReflect (D.β j) ^ (k : ℕ)) / 2

/-- The reflection-odd part of Frobenius evaluation. -/
def frobeniusOdd (n : ℕ) : Matrix ι (Fin n) ℂ :=
  fun j k => (D.β j ^ (k : ℕ) - circleReflect (D.β j) ^ (k : ℕ)) / 2

/-- The Gram of the odd evaluation: one half of the reflection defect. -/
def halfDefectRepair (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (frobeniusOdd D n)ᴴ * frobeniusOdd D n

private theorem spanGram_entry (n : ℕ) (k l : Fin n) :
    D.spanGram n k l = ∑ j, conj (D.β j ^ (k : ℕ)) *
      circleReflect (D.β j) ^ (l : ℕ) := by
  simpa [dotProduct, mulVec, windowEval_apply] using
    D.spanGram_sesq n (Pi.single k 1) (Pi.single l 1)

/-- The reflected Gram splits into positive even and negative odd evaluation Grams. -/
theorem spanGram_add_halfDefectRepair (n : ℕ) :
    D.spanGram n + halfDefectRepair D n = (frobeniusEven D n)ᴴ * frobeniusEven D n := by
  have hdiff : (frobeniusEven D n)ᴴ * frobeniusEven D n - halfDefectRepair D n =
      D.spanGram n := by
    ext k l
    have hflip : (∑ j, conj (circleReflect (D.β j) ^ (k : ℕ)) * D.β j ^ (l : ℕ)) =
        ∑ j, conj (D.β j ^ (k : ℕ)) * circleReflect (D.β j) ^ (l : ℕ) := by
      rw [← Equiv.sum_comp D.reflPerm]
      simp only [D.β_reflPerm, circleReflect_circleReflect]
    simp only [Matrix.sub_apply, Matrix.mul_apply, halfDefectRepair,
      Matrix.conjTranspose_apply, frobeniusEven, frobeniusOdd, Complex.star_def,
      map_div₀, map_add, map_sub, map_ofNat]
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ j, (conj (D.β j ^ (k : ℕ)) * circleReflect (D.β j) ^ (l : ℕ) +
          conj (circleReflect (D.β j) ^ (k : ℕ)) * D.β j ^ (l : ℕ)) / 2 := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = D.spanGram n k l := by
        rw [Finset.sum_div, Finset.sum_add_distrib, hflip, spanGram_entry]
        ring
  exact (sub_eq_iff_eq_add.mp hdiff).symm

/-- The correction is positive semidefinite on every window. -/
theorem halfDefectRepair_posSemidef (n : ℕ) : (halfDefectRepair D n).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- Half the reflection defect already suffices for positivity. -/
theorem spanGram_halfDefectRepair_posSemidef (n : ℕ) :
    (D.spanGram n + halfDefectRepair D n).PosSemidef := by
  rw [spanGram_add_halfDefectRepair]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Window restriction commutes with the correction. -/
theorem halfDefectRepair_submatrix {m n : ℕ} (h : m ≤ n) :
    (halfDefectRepair D n).submatrix (Fin.castLE h) (Fin.castLE h) =
      halfDefectRepair D m := by
  ext k l
  simp only [halfDefectRepair, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, frobeniusOdd, Fin.coe_castLE]

private theorem gram_hermQuad {a b : Type*} [Fintype a] [Fintype b]
    (A : Matrix a b ℂ) (x : b → ℂ) :
    hermQuad (Aᴴ * A) x = ∑ j, normSq ((A *ᵥ x) j) := by
  rw [hermQuad, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.re_sum, Complex.ofReal_re]

/-- Odd evaluation is half the difference of the two reflected evaluations. -/
theorem frobeniusOdd_mulVec (n : ℕ) (x : Fin n → ℂ) (j : ι) :
    (frobeniusOdd D n *ᵥ x) j =
      (windowEval n (D.β j) x - windowEval n (circleReflect (D.β j)) x) / 2 := by
  simp only [mulVec, dotProduct, frobeniusOdd, windowEval_apply,
    ← Finset.sum_sub_distrib, ← Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Even evaluation is half the sum of the two reflected evaluations. -/
theorem frobeniusEven_mulVec (n : ℕ) (x : Fin n → ℂ) (j : ι) :
    (frobeniusEven D n *ᵥ x) j =
      (windowEval n (D.β j) x + windowEval n (circleReflect (D.β j)) x) / 2 := by
  simp only [mulVec, dotProduct, frobeniusEven, windowEval_apply,
    ← Finset.sum_add_distrib, ← Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The repair energy is a quarter of the sum of squared reflection differences. -/
theorem halfDefectRepair_energy (n : ℕ) (x : Fin n → ℂ) :
    hermQuad (halfDefectRepair D n) x =
      ∑ j, normSq ((windowEval n (D.β j) x -
        windowEval n (circleReflect (D.β j)) x) / 2) := by
  rw [halfDefectRepair, gram_hermQuad]
  simp_rw [frobeniusOdd_mulVec]

end GaloisForLFunctions.ArithmeticLorentzianGeometry
