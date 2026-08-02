import GaloisForLFunctions.HTGeometry.OccupationFactorInjective

/-!
# The deformed fibre has binomially many points

Every point of the pure critical fibre deforms, along the universal deformation of the critical
observation, to a point of the deformed fibre; distinct pure points deform to distinct ones, because
they already differ modulo the deformation ideal; and all of them share the same deformed
observation, because the deformation is added to the same monic data.

So the fibre over the deformed observation has at least as many points as there are occupation
states — the critical binomial multiplicity.  This is the lower bound that no count at the special
fibre can supply on its own.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **The pure fibre injects into the deformed fibre, over a single observation.** -/
theorem exists_injective_deformed_fibre (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃ g : criticalHorizonOccupationStates m n →
        (deformBase K m n)[X] × (deformBase K m n)[X],
      Function.Injective g ∧
      (∀ S, (X : (deformBase K m n)[X]) ^ (m + n) ∣ inversionError (g S).1 (g S).2) ∧
      (∀ S T, ∀ i, m ≤ i → (g S).1.coeff i = (g T).1.coeff i) ∧
      (∀ S T, ∀ j, n ≤ j → (g S).2.coeff j = (g T).2.coeff j) := by
  classical
  haveI : IsAdicComplete (deformIdeal K m n) (deformBase K m n) := inferInstanceAs
    (IsAdicComplete (Ideal.span (Set.range (MvPowerSeries.X :
      Fin n ⊕ Fin m ⊕ Unit → MvPowerSeries (Fin n ⊕ Fin m ⊕ Unit) K)))
      (MvPowerSeries (Fin n ⊕ Fin m ⊕ Unit) K))
  set φ : K →+* deformBase K m n := algebraMap K (deformBase K m n) with hφ
  set root := pureCriticalRootLabeling (K := K) (by omega : 0 < m + n) with hroot
  set AA : criticalHorizonOccupationStates m n → K[X] :=
    fun S => criticalHorizonLeftFactorFromRoots root S with hAA
  set BB : criticalHorizonOccupationStates m n → K[X] :=
    fun S => criticalHorizonRightFactorFromRoots root S with hBB
  have hL : ((m + n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hfac : ∀ S, AA S * BB S = 1 + X ^ (m + n) :=
    fun S => pureCriticalRootFactors_mul (by omega) S
  have hmapfac : ∀ S, (X : (deformBase K m n)[X]) ^ (m + n)
      ∣ inversionError ((AA S).map φ) ((BB S).map φ) := by
    intro S
    have hrw : inversionError ((AA S).map φ) ((BB S).map φ)
        = (X : (deformBase K m n)[X]) ^ (m + n) := by
      rw [inversionError, ← Polynomial.map_mul, hfac S, Polynomial.map_add, Polynomial.map_one,
        Polynomial.map_pow, Polynomial.map_X, add_sub_cancel_left]
    rw [hrw]
  -- lift every pure point
  have hlift : ∀ S, ∃ p : (deformBase K m n)[X] × (deformBase K m n)[X],
      p.1.natDegree < m ∧ p.2.natDegree < n ∧
      CoeffMem (deformIdeal K m n) p.1 ∧ CoeffMem (deformIdeal K m n) p.2 ∧
      (X : (deformBase K m n)[X]) ^ (m + n)
        ∣ inversionError ((AA S).map φ + rawDeformation K m n + p.1)
          ((BB S).map φ + reciprocalDeformation K m n + p.2) := by
    intro S
    obtain ⟨P, Q, hP, hQ, hPmem, hQmem, hfacS⟩ :=
      exists_deformed_factorisation (deformIdeal K m n) hm hn
        (((monic_criticalHorizonLeftFactorFromRoots root S).map φ))
        (by rw [(monic_criticalHorizonLeftFactorFromRoots root S).natDegree_map φ,
          natDegree_criticalHorizonLeftFactorFromRoots root S])
        (le_of_eq (by rw [(monic_criticalHorizonRightFactorFromRoots root S).natDegree_map φ,
          natDegree_criticalHorizonRightFactorFromRoots root S]))
        (show IsCoprime ((AA S).map φ) ((BB S).map φ) from
          (isCoprime_of_pureFactorisation hL (hfac S)).map (Polynomial.mapRingHom φ))
        (coeffMem_rawDeformation K m n) (coeffMem_reciprocalDeformation K m n) (hmapfac S)
    exact ⟨(P, Q), hP, hQ, hPmem, hQmem, hfacS⟩
  choose p hpdeg hqdeg hpmem hqmem hpfac using hlift
  refine ⟨fun S => ((AA S).map φ + rawDeformation K m n + (p S).1,
    (BB S).map φ + reciprocalDeformation K m n + (p S).2), ?_, hpfac, ?_, ?_⟩
  · intro S T hST
    have hfst := congrArg Prod.fst hST
    simp only at hfst
    -- the pure parts agree modulo the deformation ideal, hence exactly
    have hcoeff : ∀ i, ((AA S).coeff i - (AA T).coeff i) = 0 := by
      intro i
      by_contra hne
      refine notMem_deformIdeal_of_ne_zero K m n hne ?_
      have hd : φ ((AA S).coeff i) - φ ((AA T).coeff i)
          = (p T).1.coeff i - (p S).1.coeff i := by
        have := congrArg (fun q : (deformBase K m n)[X] => q.coeff i) hfst
        simp only [Polynomial.coeff_add, Polynomial.coeff_map] at this
        linear_combination this
      rw [map_sub]
      rw [hd]
      exact Submodule.sub_mem _ (hpmem T i) (hpmem S i)
    have hAeq : AA S = AA T :=
      Polynomial.ext (fun i => sub_eq_zero.1 (hcoeff i))
    exact criticalHorizonLeftFactorFromRoots_injective
      (pureCriticalRootLabeling_injective (by omega)) hAeq
  · intro S T i hi
    simp only [Polynomial.coeff_add, Polynomial.coeff_map,
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hpdeg S) hi),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hpdeg T) hi)]
    rw [coeff_eq_of_monic_natDegree (monic_criticalHorizonLeftFactorFromRoots root S)
      (natDegree_criticalHorizonLeftFactorFromRoots root S)
      (monic_criticalHorizonLeftFactorFromRoots root T)
      (natDegree_criticalHorizonLeftFactorFromRoots root T) hi]
  · intro S T j hj
    simp only [Polynomial.coeff_add, Polynomial.coeff_map,
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hqdeg S) hj),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hqdeg T) hj)]
    rw [coeff_eq_of_monic_natDegree (monic_criticalHorizonRightFactorFromRoots root S)
      (natDegree_criticalHorizonRightFactorFromRoots root S)
      (monic_criticalHorizonRightFactorFromRoots root T)
      (natDegree_criticalHorizonRightFactorFromRoots root T) hj]

end GaloisForLFunctions.HTGeometry
