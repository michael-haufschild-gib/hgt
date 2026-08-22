import GaloisForLFunctions.HTGeometry.TwoLocalLacunaryWitness
import GaloisForLFunctions.HTGeometry.TwoLocalIntegerWitness
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Theorem C's selection: an integer two-local Hamiltonian with all three properties

The lacunary witness supplies a rational two-local Hamiltonian whose characteristic polynomial has
the full symmetric Galois group and whose spectral collision at the all-zero product state is below
`4(2/3)ⁿ`.  Clearing denominators makes it integral; the Galois group and the collision are both
scale invariant, and the symmetric Galois group makes the characteristic polynomial irreducible,
hence every nonzero rational vector cyclic and every eigenvector overlap nonzero.

## Main results

* `isOrthoEigenBasis_realSmul` — scaling by a nonzero real keeps an eigenbasis.
* `spectralCollision_realSmul_eq` — the spectral collision is scale invariant.
* `exists_integer_twoLocal_theoremC` — **Theorem C's selection.**
-/

open Matrix Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace TwoLocalWitness

set_option linter.unusedSectionVars false

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Scaling a matrix by a real number keeps an orthonormal eigenbasis, scaling the eigenvalues. -/
theorem isOrthoEigenBasis_realSmul {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (a : ℝ) :
    IsOrthoEigenBasis (((a : ℝ) : ℂ) • H) e (fun j => a * lam j) := by
  refine ⟨heb.orth, fun j => ?_, heb.complete⟩
  rw [Matrix.smul_mulVec, heb.eigen j, smul_smul]
  congr 1
  push_cast
  ring

/-- **The spectral collision is scale invariant.** -/
theorem spectralCollision_realSmul_eq {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam) {a : ℝ} (ha : a ≠ 0)
    {e' : α → α → ℂ} {lam' : α → ℝ}
    (heb' : IsOrthoEigenBasis (((a : ℝ) : ℂ) • H) e' lam') (hinj' : Function.Injective lam')
    (ψ : α → ℂ) :
    spectralCollision e' ψ = spectralCollision e ψ := by
  have hinja : Function.Injective (fun j => a * lam j) := by
    intro x y hxy
    exact hinj (by
      have : a * lam x = a * lam y := hxy
      exact mul_left_cancel₀ ha this)
  exact spectralCollision_eq_of_isOrthoEigenBasis heb' hinj'
    (isOrthoEigenBasis_realSmul heb a) hinja ψ

/-! ### Theorem C's selection -/

/-- Eigenvalues of a Hermitian matrix whose characteristic polynomial comes from an irreducible
rational polynomial are pairwise distinct. -/
theorem injective_eigenvalues_of_irreducible {H : Matrix α α ℂ} (hH : H.IsHermitian)
    {p : Polynomial ℚ} (hirr : Irreducible p) (hmap : p.map (algebraMap ℚ ℂ) = H.charpoly) :
    Function.Injective hH.eigenvalues := by
  have hprod : p.map (algebraMap ℚ ℂ) = ∏ i, (X - C ((hH.eigenvalues i : ℝ) : ℂ)) := by
    rw [hmap, hH.charpoly_eq]
    rfl
  have hEinj : Function.Injective (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    refine Polynomial.separable_prod_X_sub_C_iff.mp ?_
    rw [← hprod]
    exact (Polynomial.separable_map _).mpr hirr.separable
  exact fun a b hab => hEinj (by
    show ((hH.eigenvalues a : ℝ) : ℂ) = ((hH.eigenvalues b : ℝ) : ℂ)
    exact congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hab)

variable {m : ℕ}

theorem walsh_zeroState_eq_map (n : ℕ) (i : Fin n → Bool) :
    algebraMap ℚ ℂ ((Pi.single (fun _ => false) (1 : ℚ) : (Fin n → Bool) → ℚ) i)
      = Walsh.zeroState n i := by
  classical
  rw [Walsh.zeroState]
  by_cases h : i = (fun _ => false)
  · rw [h, Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

/-- **Theorem C's selection.**  An explicit traceless *integer* two-local Hamiltonian whose
characteristic polynomial has the full symmetric Galois group, whose all-zero product state
overlaps every eigenvector, and whose spectral collision at that state is below `4(2/3)ⁿ`. -/
theorem exists_integer_twoLocal_theoremC (m : ℕ) :
    ∃ (u : Fin (m + 1) → ℚ) (Nn : ℕ)
      (Hz : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℤ)
      (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian),
      0 < Nn ∧ Hz.trace = 0 ∧
      Hz.map (Int.castRingHom ℚ)
        = (Nn : ℚ) • twoLocalHam (witnessConstant m) 0 witnessCoupling u ∧
      Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal = (2 ^ (m + 1)).factorial ∧
      Irreducible (Hz.charpoly.map (Int.castRingHom ℚ)) ∧
      Function.Injective hH.eigenvalues ∧
      (∀ j, finiteComplexInner (hermitianEigenBasis _ hH j) (Walsh.zeroState (m + 1)) ≠ 0) ∧
      spectralCollision (hermitianEigenBasis _ hH) (Walsh.zeroState (m + 1))
        < 4 * (2 / 3 : ℝ) ^ (m + 1) := by
  classical
  set c : ℚ := witnessConstant m with hc
  obtain ⟨u, hHermQ, -, hgalQ, hcoll⟩ :=
    exists_twoLocal_lacunary_smallCollision m c (g := (1 : MvPolynomial (Fin (m + 1)) ℚ))
      one_ne_zero
  set Hq : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℚ :=
    twoLocalHam c 0 witnessCoupling u with hHq
  set Hc : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℂ :=
    transverseFamilyHam (fun x => ((witnessDiagonal c x : ℚ) : ℂ))
      (fun i => ((u i : ℚ) : ℂ)) with hHc
  have hHcmap : Hq.map (algebraMap ℚ ℂ) = Hc := map_transverseFamilyHam _ _ _
  -- the integer scaling
  obtain ⟨Nn, hNn, hint⟩ := exists_integral_scaling c u
  choose zz hzz using hint
  set Hz : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℤ := Matrix.of zz with hHz
  have hA : Hz.map (Int.castRingHom ℚ) = (Nn : ℚ) • Hq := by
    ext x y
    rw [Matrix.map_apply]
    exact (hzz x y).symm
  have hNQ : ((Nn : ℚ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hcharmap : Hz.charpoly.map (Int.castRingHom ℚ) = ((Nn : ℚ) • Hq).charpoly := by
    rw [← Matrix.charpoly_map, ← hA]
  have hgal : Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal = (2 ^ (m + 1)).factorial := by
    rw [hcharmap, card_gal_charpoly_smul hNQ]
    exact hgalQ
  have hdegcard : (Hz.charpoly.map (Int.castRingHom ℚ)).natDegree = 2 ^ (m + 1) := by
    rw [hcharmap, Matrix.charpoly_natDegree_eq_dim]
    simp
  have hirr : Irreducible (Hz.charpoly.map (Int.castRingHom ℚ)) := by
    refine irreducible_of_card_gal_eq_factorial ?_ ?_ ?_
    · rw [hcharmap]
      exact (Matrix.charpoly_monic _).ne_zero
    · rw [hdegcard]
      exact Nat.one_le_two_pow
    · rw [hgal, hdegcard]
  -- the complex integer matrix is a real multiple of the rational one
  set HzC : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℂ :=
    Hz.map (Int.castRingHom ℂ) with hHzC
  have hcharC : (Hz.charpoly.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) = HzC.charpoly := by
    rw [Polynomial.map_map, hHzC, Matrix.charpoly_map]
    congr 1
  have hscal : HzC = (((Nn : ℝ)) : ℂ) • Hc := by
    ext x y
    have hq : ((Nn : ℚ)) * Hq x y = ((zz x y : ℤ) : ℚ) := by
      have hz0 := hzz x y
      simpa [Matrix.smul_apply, smul_eq_mul] using hz0
    have hqC : ((Nn : ℂ)) * ((Hq x y : ℚ) : ℂ) = ((zz x y : ℤ) : ℂ) := by
      have hcong := congrArg (fun q : ℚ => ((q : ℚ) : ℂ)) hq
      push_cast at hcong
      exact hcong
    simp only [hHzC, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← hHcmap, Matrix.map_apply]
    show ((zz x y : ℤ) : ℂ) = (((Nn : ℝ)) : ℂ) * ((Hq x y : ℚ) : ℂ)
    rw [← hqC]
    push_cast
    ring
  have hHerm : HzC.IsHermitian := by
    rw [hscal, Matrix.IsHermitian, Matrix.conjTranspose_smul, hHermQ.eq]
    congr 1
    exact Complex.conj_ofReal _
  refine ⟨u, Nn, Hz, hHerm, hNn, ?_, hA, hgal, hirr, ?_, ?_, ?_⟩
  · -- tracelessness
    have htraceQ : Hq.trace = 0 := by
      rw [hHq, twoLocalHam, trace_transverseFamilyHam]
      have hsw := sum_witnessDiagonal m
      rw [witnessDiagonal] at hsw
      rw [hc]
      exact hsw
    have hcast : (Int.castRingHom ℚ) Hz.trace = (Hz.map (Int.castRingHom ℚ)).trace := by
      show (Int.castRingHom ℚ) (∑ i, Hz.diag i) = ∑ i, (Hz.map (Int.castRingHom ℚ)).diag i
      rw [map_sum]
      rfl
    rw [hA, Matrix.trace_smul, htraceQ, smul_zero] at hcast
    have hz : ((Hz.trace : ℤ) : ℚ) = 0 := hcast
    exact_mod_cast hz
  · -- distinct eigenvalues
    exact injective_eigenvalues_of_irreducible hHerm hirr hcharC
  · -- every eigenvector overlap is nonzero
    intro j
    set Ωq : (Fin (m + 1) → Bool) → ℚ := Pi.single (fun _ => false) 1 with hΩq
    have hΩqne : Ωq ≠ 0 := by
      intro h0
      have := congrFun h0 (fun _ => false)
      rw [hΩq, Pi.single_eq_same] at this
      exact one_ne_zero this
    have hqzchar : (Hz.map (Int.castRingHom ℚ)).charpoly
        = Hz.charpoly.map (Int.castRingHom ℚ) := Matrix.charpoly_map _ _
    have hirrQ : Irreducible (Hz.map (Int.castRingHom ℚ)).charpoly := by
      rw [hqzchar]
      exact hirr
    have hcycQ := linearIndependent_krylov_of_irreducible (Hz.map (Int.castRingHom ℚ)) hirrQ hΩqne
    have hbase := BaseChange.linearIndependent_krylov_map (L := ℂ) hcycQ
    have hmapeq : (Hz.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) = HzC := by
      ext x y
      rw [Matrix.map_apply, Matrix.map_apply, hHzC, Matrix.map_apply]
      push_cast
      rfl
    have hOmeq : (fun i => algebraMap ℚ ℂ (Ωq i)) = Walsh.zeroState (m + 1) :=
      funext (walsh_zeroState_eq_map (m + 1))
    rw [hmapeq, hOmeq] at hbase
    exact AlgebraicOrbit.finiteComplexInner_ne_zero_of_linearIndependent
      (isOrthoEigenBasis_hermitian _ hHerm) hbase j
  · -- the collision is scale invariant
    have hQirr : Irreducible Hq.charpoly := by
      have hcard : Fintype.card (Fin (m + 1) → Bool) = 2 ^ (m + 1) := by simp
      refine irreducible_of_card_gal_eq_factorial (Matrix.charpoly_monic _).ne_zero ?_ ?_
      · rw [Matrix.charpoly_natDegree_eq_dim, hcard]
        exact Nat.one_le_two_pow
      · rw [hgalQ, Matrix.charpoly_natDegree_eq_dim, hcard]
    have hQinj : Function.Injective hHermQ.eigenvalues := by
      refine injective_eigenvalues_of_irreducible hHermQ hQirr ?_
      rw [← hHcmap, Matrix.charpoly_map]
    have hZinj : Function.Injective hHerm.eigenvalues :=
      injective_eigenvalues_of_irreducible hHerm hirr hcharC
    have hane : ((Nn : ℝ)) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hebZ : IsOrthoEigenBasis ((((Nn : ℝ)) : ℂ) • Hc)
        (hermitianEigenBasis _ hHerm) hHerm.eigenvalues := by
      rw [← hscal]
      exact isOrthoEigenBasis_hermitian _ hHerm
    have htrans := spectralCollision_realSmul_eq (isOrthoEigenBasis_hermitian _ hHermQ) hQinj
      hane hebZ hZinj (Walsh.zeroState (m + 1))
    rw [htrans]
    exact hcoll

end

end TwoLocalWitness

end GaloisForLFunctions.HTGeometry
