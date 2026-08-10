import GaloisForLFunctions.HTGeometry.PowerSeriesEndpointExpansion
import GaloisForLFunctions.HTGeometry.DeterminantDegreeOne
import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Determinant contact under the Hankel mass-shift flow

For a finite-atomic flat Hankel shadow, the negative-binomial mass-shift keeps every
`(n+1) × (n+1)` shadow block singular.  If the actual moments first differ from that shadow at
index `2n+d`, then the first determinant coefficient is exactly

`det(Hₙ) · (-1)^d · choose(2n+d,d) · defect(2n+d)`.

Thus no off-terminal matrix entry or nonlinear determinant term can alter first-contact parity.
-/

open Matrix MvPolynomial PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Universal determinant polynomial in square-matrix entry variables. -/
def matrixDetPolynomial (N : ℕ) : MvPolynomial (Fin N × Fin N) ℝ :=
  (Matrix.of fun i j : Fin N => MvPolynomial.X (i, j)).det

theorem aeval_matrixDetPolynomial {A : Type*} [CommRing A] [Algebra ℝ A]
    (N : ℕ) (M : Matrix (Fin N) (Fin N) A) :
    MvPolynomial.aeval (fun ij => M ij.1 ij.2) (matrixDetPolynomial N) = M.det := by
  rw [matrixDetPolynomial, AlgHom.map_det]
  congr 1
  ext i j
  simp

/-- Terminal partial derivative of the universal determinant is the head determinant. -/
theorem pderiv_matrixDetPolynomial_terminal {n : ℕ} :
    MvPolynomial.pderiv (Fin.last n, Fin.last n) (matrixDetPolynomial (n + 1)) =
      (Matrix.of fun i j : Fin n =>
        MvPolynomial.X (Fin.castSucc i, Fin.castSucc j)).det := by
  classical
  let U : Matrix (Fin (n + 1)) (Fin (n + 1))
      (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℝ) :=
    Matrix.of fun i j => MvPolynomial.X (i, j)
  rw [matrixDetPolynomial, show (Matrix.of fun i j : Fin (n + 1) =>
      MvPolynomial.X (i, j)) = U by rfl, Matrix.det_succ_row U (Fin.last n), map_sum]
  rw [Finset.sum_eq_single (Fin.last n)]
  · have hminor : MvPolynomial.pderiv (Fin.last n, Fin.last n)
        ((U.submatrix (Fin.last n).succAbove (Fin.last n).succAbove).det) = 0 := by
      apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
      rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
      push Not
      apply degreeOf_det_eq_zero
      intro a b
      have hne : (Fin.last n, Fin.last n) ≠
          ((Fin.last n).succAbove a, (Fin.last n).succAbove b) := by
        intro h
        have hfst := congrArg Prod.fst h
        simp only [Fin.succAbove_last] at hfst
        exact Fin.castSucc_ne_last a hfst.symm
      exact MvPolynomial.degreeOf_X_of_ne hne
    have hsign : MvPolynomial.pderiv (Fin.last n, Fin.last n)
        ((-1 : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℝ) ^
          ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 0 := by simp
    rw [Derivation.leibniz, Derivation.leibniz, hsign, hminor]
    simp only [U, Matrix.of_apply, MvPolynomial.pderiv_X_self, smul_eq_mul]
    simp only [zero_add, mul_zero, add_zero]
    have hpow : (-1 : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℝ) ^
        ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
      simp only [Fin.val_last]
      rw [← two_mul n, pow_mul]
      simp
    rw [hpow, one_mul]
    simp only [Fin.succAbove_last, mul_one]
    apply congrArg Matrix.det
    ext i j
    rfl
  · intro j _ hj
    have hX : MvPolynomial.pderiv (Fin.last n, Fin.last n)
        (U (Fin.last n) j) = 0 := by
      simp [U, MvPolynomial.pderiv_X, hj]
    have hminor : MvPolynomial.pderiv (Fin.last n, Fin.last n)
        ((U.submatrix (Fin.last n).succAbove j.succAbove).det) = 0 := by
      apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
      rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
      push Not
      apply degreeOf_det_eq_zero
      intro a b
      have hne : (Fin.last n, Fin.last n) ≠
          ((Fin.last n).succAbove a, j.succAbove b) := by
        intro h
        have hfst := congrArg Prod.fst h
        simp only [Fin.succAbove_last] at hfst
        exact Fin.castSucc_ne_last a hfst.symm
      exact MvPolynomial.degreeOf_X_of_ne hne
    have hsign : MvPolynomial.pderiv (Fin.last n, Fin.last n)
        ((-1 : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℝ) ^
          ((Fin.last n : ℕ) + (j : ℕ))) = 0 := by simp
    rw [Derivation.leibniz, Derivation.leibniz, hsign, hX, hminor]
    ring
  · simp

theorem coeff_mul_eq_coeff_zero_mul_of_right_vanish_below
    {k : Type*} [CommRing k] {d : ℕ} (H D : PowerSeries k)
    (hD : ∀ r < d, PowerSeries.coeff r D = 0) :
    PowerSeries.coeff d (H * D) =
      PowerSeries.coeff 0 H * PowerSeries.coeff d D := by
  classical
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro q hq hq0
    have hqd : q ≤ d := by simpa using Finset.mem_range.mp hq
    have hdq : d - q < d := Nat.sub_lt (by omega) (Nat.zero_lt_of_ne_zero hq0)
    rw [hD (d - q) hdq, mul_zero]
  · simp

/-- First determinant contact is the terminal defect times the head cofactor. -/
theorem coeff_det_add_eq_terminal_of_common_contact
    {n d : ℕ} (hd : 0 < d)
    (Q D : Matrix (Fin (n + 1)) (Fin (n + 1)) (PowerSeries ℝ))
    (hQdet : Q.det = 0)
    (hDzero : ∀ i j r, r < d → PowerSeries.coeff r (D i j) = 0)
    (hDtop : ∀ i j, (i, j) ≠ (Fin.last n, Fin.last n) →
      PowerSeries.coeff d (D i j) = 0) :
    PowerSeries.coeff d (Q + D).det =
      PowerSeries.coeff 0
          ((Q.submatrix (Fin.last n).succAbove (Fin.last n).succAbove).det) *
        PowerSeries.coeff d (D (Fin.last n) (Fin.last n)) := by
  classical
  let P := matrixDetPolynomial (n + 1)
  let S : Fin (n + 1) × Fin (n + 1) → PowerSeries ℝ := fun ij => Q ij.1 ij.2
  let L : Fin (n + 1) × Fin (n + 1) → PowerSeries ℝ := fun ij => D ij.1 ij.2
  let J : Ideal (PowerSeries ℝ) :=
    Ideal.span {(PowerSeries.X : PowerSeries ℝ) ^ d}
  have hLmem : ∀ ij, L ij ∈ J := by
    intro ij
    change L ij ∈ Ideal.span {(PowerSeries.X : PowerSeries ℝ) ^ d}
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro r hr
    exact hDzero ij.1 ij.2 r hr
  have hexp := aeval_add_eq_add_sum_pderiv_mod_sq S L P
  have hdef := taylorDefect_mem_sq J S L hLmem P
  have hsqspan : J ^ 2 =
      Ideal.span {(PowerSeries.X : PowerSeries ℝ) ^ (2 * d)} := by
    change Ideal.span {(PowerSeries.X : PowerSeries ℝ) ^ d} ^ 2 = _
    rw [pow_two, Ideal.span_singleton_mul_span_singleton, ← pow_add]
    congr 2
    ring
  rw [hsqspan] at hdef
  have hdefzero : PowerSeries.coeff d (taylorDefect S L P) = 0 := by
    exact coeff_eq_zero_of_mem_span_X_pow (by omega) hdef
  have hdetExpand : (Q + D).det =
      Q.det + (∑ ij, (MvPolynomial.aeval S (MvPolynomial.pderiv ij P)) * L ij) +
        taylorDefect S L P := by
    calc
      (Q + D).det = MvPolynomial.aeval (S + L) P := by
        dsimp only [P]
        have hSL : S + L = fun ij => (Q + D) ij.1 ij.2 := by
          funext ij
          rfl
        rw [hSL, aeval_matrixDetPolynomial]
      _ = MvPolynomial.aeval S P +
          (∑ ij, (MvPolynomial.aeval S (MvPolynomial.pderiv ij P)) * L ij) +
            taylorDefect S L P := hexp
      _ = Q.det +
          (∑ ij, (MvPolynomial.aeval S (MvPolynomial.pderiv ij P)) * L ij) +
            taylorDefect S L P := by
        congr 2
        dsimp only [P]
        have hS : S = fun ij => Q ij.1 ij.2 := rfl
        rw [hS, aeval_matrixDetPolynomial]
  rw [hdetExpand, hQdet, zero_add, map_add, hdefzero, add_zero, map_sum]
  rw [Finset.sum_eq_single (Fin.last n, Fin.last n)]
  · rw [coeff_mul_eq_coeff_zero_mul_of_right_vanish_below _ _
      (fun r hr => hDzero (Fin.last n) (Fin.last n) r hr)]
    change PowerSeries.coeff 0
        (MvPolynomial.aeval S
          (MvPolynomial.pderiv (Fin.last n, Fin.last n)
            (matrixDetPolynomial (n + 1)))) * _ = _
    rw [pderiv_matrixDetPolynomial_terminal]
    rw [AlgHom.map_det]
    congr 3
    ext i j
    simp [S, Fin.succAbove_last]
  · intro ij _ hij
    rw [coeff_mul_eq_coeff_zero_mul_of_right_vanish_below _ _
      (fun r hr => hDzero ij.1 ij.2 r hr), hDtop ij.1 ij.2 hij, mul_zero]
  · simp

/-- Formal geometric factor `(1+xX)⁻¹` used by one mass-shifted atom. -/
def massShiftGeometricSeries (x : ℝ) : PowerSeries ℝ :=
  PowerSeries.rescale (-x) (PowerSeries.invOneSubPow ℝ 1).val

theorem massShiftGeometricSeries_pow (x : ℝ) (m : ℕ) :
    massShiftGeometricSeries x ^ (m + 1) =
      PowerSeries.rescale (-x) (PowerSeries.invOneSubPow ℝ (m + 1)).val := by
  rw [massShiftGeometricSeries, ← map_pow]
  congr 1
  rw [← Units.val_pow_eq_pow_val]
  congr 1
  simp only [PowerSeries.invOneSubPow_eq_inv_one_sub_pow]
  rw [← pow_mul]
  congr 1
  omega

theorem coeff_massShiftGeometricSeries_pow (x : ℝ) (m r : ℕ) :
    PowerSeries.coeff r (massShiftGeometricSeries x ^ (m + 1)) =
      (-1 : ℝ) ^ r * (Nat.choose (m + r) m : ℝ) * x ^ r := by
  rw [massShiftGeometricSeries_pow, PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]
  ring

/-- Negative-binomial power series for one moment under mass shift. -/
def massShiftMomentPowerSeries (s : ℕ → ℝ) (m : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun r =>
    (-1 : ℝ) ^ r * (Nat.choose (m + r) m : ℝ) * s (m + r)

@[simp] theorem coeff_massShiftMomentPowerSeries (s : ℕ → ℝ) (m r : ℕ) :
    PowerSeries.coeff r (massShiftMomentPowerSeries s m) =
      (-1 : ℝ) ^ r * (Nat.choose (m + r) m : ℝ) * s (m + r) := by
  simp [massShiftMomentPowerSeries]

theorem massShiftMomentPowerSeries_finiteAtomic
    (S : Finset ℝ) (w : ℝ → ℝ) (m : ℕ) :
    massShiftMomentPowerSeries (fun k => ∑ x ∈ S, w x * x ^ k) m =
      ∑ x ∈ S, PowerSeries.C (w x * x ^ m) * massShiftGeometricSeries x ^ (m + 1) := by
  ext r
  rw [coeff_massShiftMomentPowerSeries, map_sum]
  simp_rw [PowerSeries.coeff_C_mul, coeff_massShiftGeometricSeries_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [pow_add]
  ring

theorem massShiftAtomic_factorization (w x : ℝ) (m : ℕ) :
    PowerSeries.C (w * x ^ m) * massShiftGeometricSeries x ^ (m + 1) =
      (PowerSeries.C w * massShiftGeometricSeries x) *
        (PowerSeries.C x * massShiftGeometricSeries x) ^ m := by
  rw [mul_pow, ← map_pow]
  rw [map_mul]
  ring

/-- Finite spectral moment sequence over an arbitrary commutative coefficient ring. -/
def finiteSpectralMomentOver {R : Type*} [CommRing R]
    {d : ℕ} (mass node : Fin d → R) (k : ℕ) : R :=
  ∑ i, mass i * node i ^ k

/-- Finite Hankel matrix over an arbitrary commutative coefficient ring. -/
def finiteHankelMatrixOver {R : Type*} [CommRing R]
    (s : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i j => s ((i : ℕ) + (j : ℕ))

theorem finiteHankelMatrixOver_mulVec_nodePolynomial_eq_zero
    {R : Type*} [CommRing R] [Nontrivial R] {d : ℕ} (mass node : Fin d → R) :
    finiteHankelMatrixOver (finiteSpectralMomentOver mass node) (d + 1) *ᵥ
        (fun j : Fin (d + 1) =>
          (∏ i : Fin d, (Polynomial.X - Polynomial.C (node i))).coeff (j : ℕ)) = 0 := by
  let p : Polynomial R := ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i))
  have hpmon : p.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (node i))
  have hpdeg : p.natDegree = d := by
    rw [show p = ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i)) by rfl,
      Polynomial.natDegree_prod_of_monic _ _
        (fun i _ => Polynomial.monic_X_sub_C (node i))]
    simp
  have hroot : ∀ i : Fin d, p.eval (node i) = 0 := by
    intro i
    rw [show p = ∏ k : Fin d, (Polynomial.X - Polynomial.C (node k)) by rfl,
      Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  funext r
  simp only [Matrix.mulVec, finiteHankelMatrixOver, Matrix.of_apply, Pi.zero_apply]
  change ∑ j : Fin (d + 1),
      finiteSpectralMomentOver mass node ((r : ℕ) + (j : ℕ)) * p.coeff (j : ℕ) = 0
  calc
    _ = ∑ j : Fin (d + 1), ∑ i : Fin d,
        (mass i * node i ^ (r : ℕ)) * (p.coeff (j : ℕ) * node i ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [finiteSpectralMomentOver, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]
      ring
    _ = ∑ i : Fin d, ∑ j : Fin (d + 1),
        (mass i * node i ^ (r : ℕ)) * (p.coeff (j : ℕ) * node i ^ (j : ℕ)) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin d, (mass i * node i ^ (r : ℕ)) *
        (∑ j : Fin (d + 1), p.coeff (j : ℕ) * node i ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i : Fin d, (mass i * node i ^ (r : ℕ)) * p.eval (node i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < d + 1)]
      rw [Finset.sum_range fun j => p.coeff j * node i ^ j]
    _ = 0 := by simp [hroot]

/-- A `d`-atomic Hankel matrix over any nontrivial commutative ring is singular in size `d+1`. -/
theorem det_finiteHankelMatrixOver_finiteSpectralMoment_succ_eq_zero
    {R : Type*} [CommRing R] [Nontrivial R] {d : ℕ} (mass node : Fin d → R) :
    (finiteHankelMatrixOver (finiteSpectralMomentOver mass node) (d + 1)).det = 0 := by
  let p : Polynomial R := ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i))
  have hpmon : p.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (node i))
  have hpdeg : p.natDegree = d := by
    rw [show p = ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i)) by rfl,
      Polynomial.natDegree_prod_of_monic _ _
        (fun i _ => Polynomial.monic_X_sub_C (node i))]
    simp
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (finiteHankelMatrixOver_mulVec_nodePolynomial_eq_zero mass node)
    (i := Fin.last d)
  change p.coeff d ∈ nonZeroDivisors R
  have hp1 : p.coeff d = 1 := by
    rw [← hpdeg]
    exact hpmon.coeff_natDegree
  simp [hp1]

/-- Hankel matrix whose entries are formal mass-shift moment series. -/
def massShiftHankelPowerSeries (s : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℝ) :=
  finiteHankelMatrixOver (massShiftMomentPowerSeries s) N

/-- Constant determinant coefficient of the mass-shift orbit is the original Hankel determinant. -/
theorem coeff_zero_det_massShiftHankelPowerSeries (s : ℕ → ℝ) (N : ℕ) :
    PowerSeries.coeff 0 (massShiftHankelPowerSeries s N).det =
      (HTGeometry.momentHankelMatrix s N).det := by
  have hmap := (PowerSeries.constantCoeff (R := ℝ)).map_det
    (massShiftHankelPowerSeries s N)
  have hconst : (PowerSeries.constantCoeff (R := ℝ)).mapMatrix
      (massShiftHankelPowerSeries s N) = HTGeometry.momentHankelMatrix s N := by
    apply Matrix.ext
    intro i j
    simp only [RingHom.mapMatrix_apply, massShiftHankelPowerSeries,
      finiteHankelMatrixOver, Matrix.map_apply, Matrix.of_apply,
      HTGeometry.momentHankelMatrix]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_massShiftMomentPowerSeries]
    simp
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hmap, hconst]

/-- Finite atomic shadows remain rank-deficient along the complete formal mass-shift orbit. -/
theorem det_massShiftHankelPowerSeries_finiteAtomic_eq_zero
    (S : Finset ℝ) (w : ℝ → ℝ) {n : ℕ} (hcard : S.card = n) :
    (massShiftHankelPowerSeries (fun k => ∑ x ∈ S, w x * x ^ k) (n + 1)).det = 0 := by
  let e : Fin n ≃ ↥S := (Finset.equivFinOfCardEq hcard).symm
  let mass : Fin n → PowerSeries ℝ := fun i =>
    PowerSeries.C (w (e i)) * massShiftGeometricSeries (e i)
  let node : Fin n → PowerSeries ℝ := fun i =>
    PowerSeries.C ((e i).1) * massShiftGeometricSeries ((e i).1)
  have hmatrix :
      massShiftHankelPowerSeries (fun k => ∑ x ∈ S, w x * x ^ k) (n + 1) =
        finiteHankelMatrixOver (finiteSpectralMomentOver mass node) (n + 1) := by
    apply Matrix.ext
    intro i j
    rw [massShiftHankelPowerSeries, finiteHankelMatrixOver, Matrix.of_apply,
      massShiftMomentPowerSeries_finiteAtomic]
    simp_rw [massShiftAtomic_factorization]
    change (∑ x ∈ S, (PowerSeries.C (w x) * massShiftGeometricSeries x) *
        (PowerSeries.C x * massShiftGeometricSeries x) ^ ((i : ℕ) + (j : ℕ))) =
      ∑ k : Fin n, mass k * node k ^ ((i : ℕ) + (j : ℕ))
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
    rw [← e.sum_comp]
  rw [hmatrix]
  exact det_finiteHankelMatrixOver_finiteSpectralMoment_succ_eq_zero mass node

/-- Exact first determinant coefficient above a finite atomic flat shadow. -/
theorem coeff_det_massShiftHankelPowerSeries_at_first_flat_defect
    (s : ℕ → ℝ) (S : Finset ℝ) (w : ℝ → ℝ) {n d : ℕ}
    (hcard : S.card = n) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d, s k = ∑ x ∈ S, w x * x ^ k) :
    PowerSeries.coeff d (massShiftHankelPowerSeries s (n + 1)).det =
      (HTGeometry.momentHankelMatrix s n).det *
        ((-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
          (s (2 * n + d) - ∑ x ∈ S, w x * x ^ (2 * n + d))) := by
  let q : ℕ → ℝ := fun k => ∑ x ∈ S, w x * x ^ k
  let a : ℕ → ℝ := fun k => s k - q k
  let Q := massShiftHankelPowerSeries q (n + 1)
  let D := massShiftHankelPowerSeries a (n + 1)
  have hsplit : massShiftHankelPowerSeries s (n + 1) = Q + D := by
    apply Matrix.ext
    intro i j
    ext r
    simp only [massShiftHankelPowerSeries, finiteHankelMatrixOver, Matrix.of_apply,
      coeff_massShiftMomentPowerSeries, Matrix.add_apply, map_add, Q, D, a, q]
    ring
  have hQdet : Q.det = 0 := by
    exact det_massShiftHankelPowerSeries_finiteAtomic_eq_zero S w hcard
  have hDzero : ∀ i j r, r < d → PowerSeries.coeff r (D i j) = 0 := by
    intro i j r hr
    have hk : (i : ℕ) + (j : ℕ) + r < 2 * n + d := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    simp only [D, massShiftHankelPowerSeries, finiteHankelMatrixOver, Matrix.of_apply,
      coeff_massShiftMomentPowerSeries, a]
    rw [hzero _ hk]
    simp [q]
  have hDtop : ∀ i j, (i, j) ≠ (Fin.last n, Fin.last n) →
      PowerSeries.coeff d (D i j) = 0 := by
    intro i j hij
    have hsum : (i : ℕ) + (j : ℕ) < 2 * n := by
      by_contra hnot
      have hi : (i : ℕ) = n := by
        have hil := i.isLt
        have hjl := j.isLt
        omega
      have hj : (j : ℕ) = n := by
        have hil := i.isLt
        have hjl := j.isLt
        omega
      apply hij
      apply Prod.ext
      · exact Fin.ext (by simp [hi])
      · exact Fin.ext (by simp [hj])
    have hk : (i : ℕ) + (j : ℕ) + d < 2 * n + d := by omega
    simp only [D, massShiftHankelPowerSeries, finiteHankelMatrixOver, Matrix.of_apply,
      coeff_massShiftMomentPowerSeries, a]
    rw [hzero _ hk]
    simp [q]
  have hcoeff := coeff_det_add_eq_terminal_of_common_contact hd Q D hQdet hDzero hDtop
  rw [← hsplit] at hcoeff
  have hheadSub : Q.submatrix (Fin.last n).succAbove (Fin.last n).succAbove =
      massShiftHankelPowerSeries q n := by
    apply Matrix.ext
    intro i j
    simp [Q, massShiftHankelPowerSeries, finiteHankelMatrixOver, Fin.succAbove_last]
  have hheadCoeff : PowerSeries.coeff 0
      ((Q.submatrix (Fin.last n).succAbove (Fin.last n).succAbove).det) =
        (HTGeometry.momentHankelMatrix s n).det := by
    rw [hheadSub]
    have hmap := (PowerSeries.constantCoeff (R := ℝ)).map_det
      (massShiftHankelPowerSeries q n)
    have hqs : HTGeometry.momentHankelMatrix q n =
        HTGeometry.momentHankelMatrix s n := by
      apply Matrix.ext
      intro i j
      simp only [HTGeometry.momentHankelMatrix]
      have hk : (i : ℕ) + (j : ℕ) < 2 * n + d := by
        have hi := i.isLt
        have hj := j.isLt
        omega
      exact (hzero _ hk).symm
    have hconstMatrix : (PowerSeries.constantCoeff (R := ℝ)).mapMatrix
        (massShiftHankelPowerSeries q n) = HTGeometry.momentHankelMatrix q n := by
      apply Matrix.ext
      intro i j
      simp only [RingHom.mapMatrix_apply, massShiftHankelPowerSeries,
        finiteHankelMatrixOver, Matrix.map_apply, Matrix.of_apply,
        HTGeometry.momentHankelMatrix]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        coeff_massShiftMomentPowerSeries]
      simp
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hmap, hconstMatrix, hqs]
  rw [hheadCoeff] at hcoeff
  have hterminal : PowerSeries.coeff d (D (Fin.last n) (Fin.last n)) =
      (-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
        (s (2 * n + d) - ∑ x ∈ S, w x * x ^ (2 * n + d)) := by
    simp only [D, massShiftHankelPowerSeries, finiteHankelMatrixOver, Matrix.of_apply,
      coeff_massShiftMomentPowerSeries, Fin.val_last, a, q]
    rw [show n + n + d = 2 * n + d by omega,
      show n + n = 2 * n by omega, Nat.add_comm (2 * n) d, Nat.choose_symm_add]
  rw [hterminal] at hcoeff
  exact hcoeff

end

end GaloisForLFunctions.HTGeometry

namespace PowerSeries

noncomputable section

/-- Absolute convergence of a real power series at a real argument. -/
def RealAbsoluteSummableAt (f : PowerSeries ℝ) (u : ℝ) : Prop :=
  Summable fun n : ℕ => ‖PowerSeries.coeff n f * u ^ n‖

/-- Absolutely convergent real evaluation. -/
def realAbsoluteEval (f : PowerSeries ℝ) (u : ℝ) : ℝ :=
  ∑' n : ℕ, PowerSeries.coeff n f * u ^ n

theorem realAbsoluteSummableAt_C (c u : ℝ) :
    (PowerSeries.C c).RealAbsoluteSummableAt u := by
  rw [RealAbsoluteSummableAt]
  apply (hasSum_single 0 (fun n hn => ?_)).summable
  simp [PowerSeries.coeff_C, hn]

@[simp] theorem realAbsoluteEval_C (c u : ℝ) :
    (PowerSeries.C c).realAbsoluteEval u = c := by
  rw [realAbsoluteEval, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [PowerSeries.coeff_C, hn]

theorem RealAbsoluteSummableAt.add {f g : PowerSeries ℝ} {u : ℝ}
    (hf : f.RealAbsoluteSummableAt u) (hg : g.RealAbsoluteSummableAt u) :
    (f + g).RealAbsoluteSummableAt u := by
  rw [RealAbsoluteSummableAt] at hf hg ⊢
  simpa only [map_add, add_mul] using (hf.of_norm.add hg.of_norm).norm

theorem realAbsoluteEval_add {f g : PowerSeries ℝ} {u : ℝ}
    (hf : f.RealAbsoluteSummableAt u) (hg : g.RealAbsoluteSummableAt u) :
    (f + g).realAbsoluteEval u = f.realAbsoluteEval u + g.realAbsoluteEval u := by
  rw [realAbsoluteEval, realAbsoluteEval, realAbsoluteEval]
  simpa [map_add, add_mul] using hf.of_norm.tsum_add hg.of_norm

theorem realCoeff_mul_term (f g : PowerSeries ℝ) (u : ℝ) (n : ℕ) :
    PowerSeries.coeff n (f * g) * u ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) *
          (PowerSeries.coeff kl.2 g * u ^ kl.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [show n = kl.1 + kl.2 from
    (Finset.HasAntidiagonal.mem_antidiagonal.mp hkl).symm, pow_add]
  ring

theorem RealAbsoluteSummableAt.mul {f g : PowerSeries ℝ} {u : ℝ}
    (hf : f.RealAbsoluteSummableAt u) (hg : g.RealAbsoluteSummableAt u) :
    (f * g).RealAbsoluteSummableAt u := by
  rw [RealAbsoluteSummableAt]
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  convert h using 1
  ext n
  rw [realCoeff_mul_term]

theorem realAbsoluteEval_mul {f g : PowerSeries ℝ} {u : ℝ}
    (hf : f.RealAbsoluteSummableAt u) (hg : g.RealAbsoluteSummableAt u) :
    (f * g).realAbsoluteEval u = f.realAbsoluteEval u * g.realAbsoluteEval u := by
  rw [realAbsoluteEval, realAbsoluteEval, realAbsoluteEval]
  rw [show (fun n => PowerSeries.coeff n (f * g) * u ^ n) =
      fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) *
          (PowerSeries.coeff kl.2 g * u ^ kl.2) by
    funext n
    exact realCoeff_mul_term f g u n]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg).symm

/-- Absolute evaluation commutes with every multivariate polynomial. -/
theorem realAbsoluteSummableAt_aeval_and_eval
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (f : σ → PowerSeries ℝ) (u : ℝ)
    (hf : ∀ i, (f i).RealAbsoluteSummableAt u) :
    (MvPolynomial.aeval f P).RealAbsoluteSummableAt u ∧
      (MvPolynomial.aeval f P).realAbsoluteEval u =
        MvPolynomial.eval (fun i => (f i).realAbsoluteEval u) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [realAbsoluteSummableAt_C]
  | add P Q hP hQ =>
      rw [map_add, MvPolynomial.eval_add]
      exact ⟨hP.1.add hQ.1,
        (realAbsoluteEval_add hP.1 hQ.1).trans (congrArg₂ _ hP.2 hQ.2)⟩
  | mul_X P i hP =>
      rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_mul, MvPolynomial.eval_X]
      exact ⟨hP.1.mul (hf i),
        (realAbsoluteEval_mul hP.1 (hf i)).trans (congrArg₂ _ hP.2 rfl)⟩

end


end PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Absolute evaluation commutes with a finite matrix determinant. -/
theorem massShiftHankelDet_realAbsoluteSummableAt_and_eval
    {N : ℕ} (A : Matrix (Fin N) (Fin N) (PowerSeries ℝ)) (u : ℝ)
    (hA : ∀ i j, (A i j).RealAbsoluteSummableAt u) :
    A.det.RealAbsoluteSummableAt u ∧
      A.det.realAbsoluteEval u = (Matrix.of fun i j => (A i j).realAbsoluteEval u).det := by
  let f : Fin N × Fin N → PowerSeries ℝ := fun ij => A ij.1 ij.2
  have h := PowerSeries.realAbsoluteSummableAt_aeval_and_eval
    (matrixDetPolynomial N) f u (fun ij => hA ij.1 ij.2)
  rw [aeval_matrixDetPolynomial N A] at h
  have heval : MvPolynomial.eval (fun ij => (f ij).realAbsoluteEval u)
      (matrixDetPolynomial N) = (Matrix.of fun i j => (A i j).realAbsoluteEval u).det := by
    have hm := aeval_matrixDetPolynomial N
      (Matrix.of fun i j => (A i j).realAbsoluteEval u)
    simpa [f, MvPolynomial.aeval_def] using hm
  rwa [heval] at h

end

end GaloisForLFunctions.HTGeometry
