import GaloisForLFunctions.HTGeometry.RootOfUnityPacketFilter
import Mathlib.RingTheory.Nilpotent.Exp

/-!
# Kammeyer determinant-approximation mechanisms

Finite-dimensional algebraic mechanisms extracted from Kammeyer,
*A counterexample to the determinant approximation conjecture* (arXiv:2609.15567):

* nilpotent blocks are invisible to determinants of `1 - zM`;
* the cyclotomic product used to prove root-block nilpotence;
* integral matrices congruent to the identity modulo two have odd determinant.

These statements make no approximation or analytic assumptions.
-/

open Matrix Polynomial Finset

namespace GaloisForLFunctions.HTGeometry.Kammeyer

/-- A finite nilpotent block contributes exactly one to every determinant `det(1 - zM)`.
This is the finite-dimensional algebraic core of the paper's primitive-root block argument. -/
theorem det_one_sub_smul_of_isNilpotent
    {K ι : Type*} [CommRing K] [IsDomain K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (hM : IsNilpotent M) (z : K) :
    ((1 : Matrix ι ι K) - z • M).det = 1 := by
  have hunit : IsUnit M.charpolyRev :=
    Matrix.isUnit_charpolyRev_of_isNilpotent hM
  obtain ⟨r, _, hrM⟩ := Polynomial.isUnit_iff.mp hunit
  have hrone : r = 1 := by
    have h := congrArg (Polynomial.eval 0) hrM
    simpa using h
  have hrev : M.charpolyRev = 1 := by
    rw [← hrM, hrone, Polynomial.C_1]
  have h := congrArg (Polynomial.eval z) hrev
  simpa [Matrix.charpolyRev, eval_det, ← Matrix.smul_eq_mul_diagonal] using h

/-- Power-vanishing interface, avoiding repeated packaging into `IsNilpotent`. -/
theorem det_one_sub_smul_of_pow_eq_zero
    {K ι : Type*} [CommRing K] [IsDomain K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (n : ℕ) (hM : M ^ n = 0) (z : K) :
    ((1 : Matrix ι ι K) - z • M).det = 1 :=
  det_one_sub_smul_of_isNilpotent M ⟨n, hM⟩ z

/-- Square-zero interface used by two-level residue and BRST models. -/
theorem det_one_sub_smul_of_mul_self_eq_zero
    {K ι : Type*} [CommRing K] [IsDomain K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (hM : M * M = 0) (z : K) :
    ((1 : Matrix ι ι K) - z • M).det = 1 :=
  det_one_sub_smul_of_pow_eq_zero M 2 (by simpa [pow_two] using hM) z

/-- Exponentiating a nilpotent finite block preserves determinant exactly. -/
theorem det_nilpotent_exp
    {K ι : Type*} [Field K] [Algebra ℚ K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (hM : IsNilpotent M) :
    (IsNilpotent.exp M).det = 1 := by
  have hd := det_one_sub_smul_of_isNilpotent
    (IsNilpotent.exp M - 1) hM.isNilpotent_exp_sub_one (-1 : K)
  simpa [sub_eq_add_neg] using hd

/-- For finite complex matrices the analytic exponential of a nilpotent matrix is its terminating
algebraic exponential. -/
theorem normed_exp_eq_nilpotent_exp_of_pow_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (n : ℕ) (hM : M ^ n = 0) :
    NormedSpace.exp M = IsNilpotent.exp M := by
  rw [NormedSpace.exp_eq_tsum_rat]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
    have hnk : n ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
    rw [pow_eq_zero_of_le hnk hM, smul_zero])]
  exact (IsNilpotent.exp_eq_sum hM).symm

/-- Complex analytic exponentials of nilpotent matrices have determinant one. -/
theorem det_normed_exp_of_pow_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (n : ℕ) (hM : M ^ n = 0) :
    (NormedSpace.exp M).det = 1 := by
  rw [normed_exp_eq_nilpotent_exp_of_pow_eq_zero M n hM]
  exact det_nilpotent_exp M ⟨n, hM⟩

/-- Basis-independent form for finite-dimensional endomorphisms. -/
theorem linearMap_det_one_sub_smul_of_isNilpotent
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (hN : IsNilpotent N) (z : K) :
    LinearMap.det ((1 : Module.End K V) - z • N) = 1 := by
  let b := Module.Free.chooseBasis K V
  rw [← LinearMap.det_toMatrix b]
  simpa using det_one_sub_smul_of_isNilpotent
    (LinearMap.toMatrix b b N) ((LinearMap.isNilpotent_toMatrix_iff b N).mpr hN) z

/-- Power-vanishing interface for finite-dimensional endomorphisms. -/
theorem linearMap_det_one_sub_smul_of_pow_eq_zero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (n : ℕ) (hN : N ^ n = 0) (z : K) :
    LinearMap.det ((1 : Module.End K V) - z • N) = 1 :=
  linearMap_det_one_sub_smul_of_isNilpotent N ⟨n, hN⟩ z

/-- Square-zero interface for finite-dimensional endomorphisms. -/
theorem linearMap_det_one_sub_smul_of_mul_self_eq_zero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) (hN : N * N = 0) (z : K) :
    LinearMap.det ((1 : Module.End K V) - z • N) = 1 :=
  linearMap_det_one_sub_smul_of_pow_eq_zero N 2 (by simpa [pow_two] using hN) z

/-- Algebraic exponentials of nilpotent finite-dimensional endomorphisms have determinant one. -/
theorem linearMap_det_nilpotent_exp
    {K V : Type*} [Field K] [Algebra ℚ K] [AddCommGroup V] [Module K V]
    [Module ℚ V] [IsScalarTower ℚ K V] [FiniteDimensional K V]
    (N : Module.End K V) (hN : IsNilpotent N) :
    LinearMap.det (IsNilpotent.exp N) = 1 := by
  have hd := linearMap_det_one_sub_smul_of_isNilpotent
    (IsNilpotent.exp N - 1) hN.isNilpotent_exp_sub_one (-1 : K)
  simpa [sub_eq_add_neg] using hd

/-- Continuous finite-dimensional form, retaining the normed-space API used by corpus operators. -/
theorem continuousLinearMap_det_one_sub_smul_of_isNilpotent
    {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]
    [FiniteDimensional K V] (N : V →L[K] V) (hN : IsNilpotent N) (z : K) :
    ContinuousLinearMap.det ((1 : V →L[K] V) - z • N) = 1 := by
  apply linearMap_det_one_sub_smul_of_isNilpotent N.toLinearMap
  obtain ⟨n, hn⟩ := hN
  exact ⟨n, by simpa using congrArg ContinuousLinearMap.toLinearMap hn⟩

/-- Power-vanishing interface for finite-dimensional continuous endomorphisms. -/
theorem continuousLinearMap_det_one_sub_smul_of_pow_eq_zero
    {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]
    [FiniteDimensional K V] (N : V →L[K] V) (n : ℕ) (hN : N ^ n = 0) (z : K) :
    ContinuousLinearMap.det ((1 : V →L[K] V) - z • N) = 1 :=
  continuousLinearMap_det_one_sub_smul_of_isNilpotent N ⟨n, hN⟩ z

/-- Square-zero interface for finite-dimensional continuous endomorphisms. -/
theorem continuousLinearMap_det_one_sub_smul_of_mul_self_eq_zero
    {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]
    [FiniteDimensional K V] (N : V →L[K] V) (hN : N * N = 0) (z : K) :
    ContinuousLinearMap.det ((1 : V →L[K] V) - z • N) = 1 :=
  continuousLinearMap_det_one_sub_smul_of_pow_eq_zero N 2
    (by simpa [pow_two] using hN) z

/-- Paper's root-of-unity factorization, obtained from the corpus packet filter after inversion.
The identity is stronger than the paper needs: no oddness restriction on `q`. -/
theorem prod_one_sub_inverse_primitiveRoot_pow_mul
    {q : ℕ} {ω : ℂ} (hq : 0 < q) (hω : IsPrimitiveRoot ω q) (u : ℂ) :
    ∏ j ∈ Finset.range q, (1 - (ω⁻¹) ^ j * u) = 1 - u ^ q := by
  simpa [sub_eq_add_neg] using
    _root_.HTGeometry.prod_one_add_primitiveRoot_pow_mul hq hω.inv (-u)

private theorem det_one_sub_double_odd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℤ) : Odd (((1 : Matrix ι ι ℤ) - (T + T)).det) := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  change (Int.castRingHom (ZMod 2))
      (((1 : Matrix ι ι ℤ) - (T + T)).det) = 1
  rw [(Int.castRingHom (ZMod 2)).map_det]
  have hmatrix :
      (Int.castRingHom (ZMod 2)).mapMatrix
        ((1 : Matrix ι ι ℤ) - (T + T)) = 1 := by
    ext i j
    simp [Matrix.one_apply, CharTwo.add_self_eq_zero]
  rw [hmatrix, Matrix.det_one]

/-- Integral core of Proposition 9: `I - 2T` has odd determinant for every square integer matrix. -/
theorem det_one_sub_two_smul_odd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℤ) : Odd (((1 : Matrix ι ι ℤ) - 2 • T).det) := by
  simpa [two_smul] using det_one_sub_double_odd T

/-- Consequently every integral `I - 2T` has nonzero determinant. -/
theorem det_one_sub_two_smul_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℤ) : (((1 : Matrix ι ι ℤ) - 2 • T).det) ≠ 0 := by
  intro hzero
  have hodd := det_one_sub_two_smul_odd T
  rw [hzero] at hodd
  simp at hodd

end GaloisForLFunctions.HTGeometry.Kammeyer
