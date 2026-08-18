import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic
import GaloisForLFunctions.HTGeometry.PowerSeriesRootLift

/-!
# The rectangular Schur caustic divisor

`ProjectiveHorizonSchurCaustic` identifies the critical low-to-high differential of the
raw/reciprocal horizon map with a finite Toeplitz section of the coefficients of `Y²`.  This module
completes the ramification equation.

* `criticalReciprocalJacobian_det_eq_rectangularSchur_normalized` — normalizing `Y = y₀ Z` with
  `Z(0) = 1` and `h_k = [t^k] Z²` factors `y₀²` out of each of the `m` rows:
  `det J = (−1)^m y₀^{2m} s_{(n^m)}[h]`.
* `jacobiTrudiRect`, `rectangularSchur` — the Toeplitz section is the transpose of the rectangular
  Jacobi--Trudi matrix `(h_{n−i+j})`, so its determinant is the rectangular Schur function.
* `det_fullObservationDifferential` — the displayed raw tail differentiates to an identity block,
  so the complete observation differential has the same determinant as the critical block;
  `det_fullObservationDifferential_eq_zero_iff` states that it is singular exactly on
  `s_{(n^m)}[h] = 0`.
* `rectangularSchur_unipotentJetCoeff` — the divisor is *proper*: at `h = 1 + t^n` the Toeplitz
  section is upper unitriangular, so the determinant is one.  That point is realized by an honest
  unit jet: `exists_unitJet_with_unipotentSquare` produces a polynomial `Z` with `Z(0) = 1` whose
  square matches `1 + t^n` to any prescribed order, via Hensel lifting of the simple root `u = 1`
  of `u² − W` (`PowerSeriesRootLift.exists_isRoot_powerSeries`).

The geometric monodromy of the resulting cover is *not* claimed here.
-/

noncomputable section

open Polynomial Matrix

namespace GaloisForLFunctions.HTGeometry

/-! ## Row scaling of the Toeplitz section -/

theorem rectangularSchurToeplitz_smul {K : Type*} [CommRing K] (c : K) (h : ℕ → K) (n m : ℕ) :
    rectangularSchurToeplitz (fun k => c * h k) n m = c • rectangularSchurToeplitz h n m := by
  ext r i
  simp only [rectangularSchurToeplitz, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **Equation (4), first equality.**  Normalizing `Y = y₀ Z` factors `y₀²` out of every row. -/
theorem criticalReciprocalJacobian_det_normalized {K : Type*} [CommRing K]
    (y0 : K) (Z : K[X]) (n m : ℕ) :
    (criticalReciprocalJacobian (Polynomial.C y0 * Z) n m).det
      = (-1 : K) ^ m * y0 ^ (2 * m)
        * (rectangularSchurToeplitz (fun k => (Z * Z).coeff k) n m).det := by
  rw [criticalReciprocalJacobian_det_eq_rectangularSchur]
  have hsq : (fun k => ((Polynomial.C y0 * Z) * (Polynomial.C y0 * Z)).coeff k)
      = fun k => y0 ^ 2 * (Z * Z).coeff k := by
    funext k
    rw [show (Polynomial.C y0 * Z) * (Polynomial.C y0 * Z)
        = Polynomial.C (y0 ^ 2) * (Z * Z) by rw [Polynomial.C_pow]; ring,
      Polynomial.coeff_C_mul]
  rw [hsq, rectangularSchurToeplitz_smul, Matrix.det_smul]
  rw [Fintype.card_fin, ← pow_mul]
  ring_nf

/-! ## The rectangular Jacobi--Trudi determinant -/

/-- The rectangular Jacobi--Trudi matrix `(h_{n-i+j})` of shape `(n^m)`, with `h_k = 0` for
`k < 0`. -/
def jacobiTrudiRect {K : Type*} [Zero K] (h : ℕ → K) (n m : ℕ) : Matrix (Fin m) (Fin m) K :=
  fun i j => if (i : ℕ) ≤ n + j then h (n + j - i) else 0

/-- The Toeplitz section of the caustic is the transpose of the Jacobi--Trudi matrix. -/
theorem jacobiTrudiRect_eq_transpose {K : Type*} [Zero K] (h : ℕ → K) (n m : ℕ) :
    jacobiTrudiRect h n m = (rectangularSchurToeplitz h n m)ᵀ := rfl

/-- The rectangular Schur function `s_{(n^m)}[h]`, defined by Jacobi--Trudi. -/
def rectangularSchur {K : Type*} [CommRing K] (h : ℕ → K) (n m : ℕ) : K :=
  (jacobiTrudiRect h n m).det

theorem rectangularSchurToeplitz_det_eq_rectangularSchur {K : Type*} [CommRing K]
    (h : ℕ → K) (n m : ℕ) :
    (rectangularSchurToeplitz h n m).det = rectangularSchur h n m := by
  rw [rectangularSchur, jacobiTrudiRect_eq_transpose, Matrix.det_transpose]

/-- **Equation (4).**  The critical caustic determinant of a normalized unit jet is
`(-1)^m y₀^{2m} s_{(n^m)}[h]`, with `h_k = [t^k] Z²`. -/
theorem criticalReciprocalJacobian_det_eq_rectangularSchur_normalized {K : Type*} [CommRing K]
    (y0 : K) (Z : K[X]) (n m : ℕ) :
    (criticalReciprocalJacobian (Polynomial.C y0 * Z) n m).det
      = (-1 : K) ^ m * y0 ^ (2 * m)
        * rectangularSchur (fun k => (Z * Z).coeff k) n m := by
  rw [criticalReciprocalJacobian_det_normalized,
    rectangularSchurToeplitz_det_eq_rectangularSchur]

/-! ## The caustic divisor is proper -/

/-- The unipotent jet point `h = 1 + t^n`. -/
def unipotentJetCoeff {K : Type*} [Zero K] [One K] (n : ℕ) : ℕ → K :=
  fun k => if k = 0 then 1 else if k = n then 1 else 0

theorem rectangularSchurToeplitz_upperTriangular {K : Type*} [CommRing K] (n m : ℕ) :
    (rectangularSchurToeplitz (unipotentJetCoeff (K := K) n) n m).BlockTriangular id := by
  intro r i h
  have hir : (i : ℕ) < (r : ℕ) := by exact_mod_cast h
  simp only [rectangularSchurToeplitz, unipotentJetCoeff]
  have hpos : n < n + (r : ℕ) - (i : ℕ) := by omega
  split_ifs with h1 h2 h3
  · exact absurd h2 (by omega)
  · exact absurd h3 (by omega)
  · rfl
  · rfl

/-- **The caustic divisor is proper.**  At the unipotent jet point the rectangular Schur
determinant equals one, so `s_{(n^m)}[h]` is not identically zero on the unit-jet chart. -/
theorem rectangularSchur_unipotentJetCoeff {K : Type*} [CommRing K] (n m : ℕ) :
    rectangularSchur (unipotentJetCoeff (K := K) n) n m = 1 := by
  rw [← rectangularSchurToeplitz_det_eq_rectangularSchur,
    Matrix.det_of_upperTriangular (rectangularSchurToeplitz_upperTriangular n m)]
  refine Finset.prod_eq_one (fun r _ => ?_)
  simp only [rectangularSchurToeplitz, unipotentJetCoeff]
  have : n + (r : ℕ) - (r : ℕ) = n := by omega
  rw [this]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

/-- The unipotent point is realized by an honest unit jet: a polynomial `Z` with `Z(0) = 1` whose
square agrees with `1 + t^n` to order `L`. -/
theorem exists_unitJet_with_unipotentSquare {n L : ℕ} (hn : 1 ≤ n) (hL : 0 < L) :
    ∃ Z : ℚ[X], Z.coeff 0 = 1 ∧
      ∀ k < L, (Z * Z).coeff k = unipotentJetCoeff (K := ℚ) n k := by
  classical
  set W : PowerSeries ℚ := 1 + PowerSeries.X ^ n with hW
  set f : (PowerSeries ℚ)[X] := Polynomial.X ^ 2 - Polynomial.C W with hf
  have hmonic : f.Monic := by
    rw [hf]
    exact Polynomial.monic_X_pow_sub_C W (by norm_num)
  have hXn : (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X ^ n) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_X_pow]
    exact if_neg (by omega)
  have hWconst : (PowerSeries.constantCoeff (R := ℚ)) W = 1 := by
    rw [hW, map_add, map_one, hXn, add_zero]
  have hmapf : f.map ((PowerSeries.constantCoeff (R := ℚ)))
      = Polynomial.X ^ 2 - Polynomial.C (1 : ℚ) := by
    rw [hf]
    simp [hWconst]
  have hroot : (f.map ((PowerSeries.constantCoeff (R := ℚ)))).eval (1 : ℚ) = 0 := by
    rw [hmapf]
    simp
  have hsimple : (f.map ((PowerSeries.constantCoeff (R := ℚ)))).derivative.eval (1 : ℚ) ≠ 0 := by
    rw [hmapf]
    simp
  obtain ⟨z, hzroot, hzconst⟩ := exists_isRoot_powerSeries f hmonic 1 hroot hsimple
  have hzsq : z * z = W := by
    have := hzroot
    rw [Polynomial.IsRoot, hf] at this
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at this
    rw [← this]
    ring
  refine ⟨PowerSeries.trunc L z, ?_, ?_⟩
  · rw [PowerSeries.coeff_trunc]
    simp [hL, hzconst]
  · intro k hk
    have hcoeff : (PowerSeries.trunc L z * PowerSeries.trunc L z).coeff k
        = (PowerSeries.coeff (R := ℚ) k) (z * z) := by
      rw [Polynomial.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hpsum := Finset.mem_antidiagonal.mp hp
      rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos (by omega), if_pos (by omega)]
    rw [hcoeff, hzsq, hW]
    simp only [unipotentJetCoeff, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    by_cases hk0 : k = 0
    · subst hk0
      simp [show (0 : ℕ) ≠ n by omega]
    · by_cases hkn : k = n
      · subst hkn
        simp [hk0]
      · simp [hk0, hkn]

/-! ## The full observation differential -/

/-- **The full differential.**  The displayed raw tail differentiates to an identity block, so the
determinant of the complete observation differential is the caustic determinant. -/
theorem det_fullObservationDifferential {K : Type*} [CommRing K] (Y : K[X]) (n m k : ℕ)
    (B : Matrix (Fin k) (Fin m) K) :
    (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) K) B 0
      (criticalReciprocalJacobian Y n m)).det = (criticalReciprocalJacobian Y n m).det := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

/-- **Equation (5).**  The complete critical observation map loses rank exactly on the rectangular
Schur divisor. -/
theorem det_fullObservationDifferential_eq_zero_iff {K : Type*} [Field K] {y0 : K} (hy0 : y0 ≠ 0)
    (Z : K[X]) (n m k : ℕ) (B : Matrix (Fin k) (Fin m) K) :
    (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) K) B 0
        (criticalReciprocalJacobian (Polynomial.C y0 * Z) n m)).det = 0
      ↔ rectangularSchur (fun j => (Z * Z).coeff j) n m = 0 := by
  rw [det_fullObservationDifferential,
    criticalReciprocalJacobian_det_eq_rectangularSchur_normalized]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 (pow_ne_zero _ (by norm_num))
      · exact absurd h4 (pow_ne_zero _ hy0)
    · exact h2
  · intro h
    rw [h, mul_zero]

end GaloisForLFunctions.HTGeometry
