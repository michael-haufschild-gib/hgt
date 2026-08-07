import GaloisForLFunctions.HTGeometry.CriticalReciprocalInvolution

/-!
# Actual reciprocal-coordinate divisorial valuations

The reciprocal rational presentation supplies the coordinate divisor `y_j=0`.  For `m,n ≥ 2`,
the divisor `y_n=0` sees the marked reciprocal coordinate once and the marked raw coordinate not at
all.  Together with the raw-coordinate valuation this gives the two independent order vectors used
in the Kummer obstruction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

set_option maxHeartbeats 1000000

/-- Reciprocal polynomial-coordinate ring of the actual source field. -/
abbrev criticalRecipCoordinateRing (K : Type*) [Field K] (m n : ℕ) :=
  MvPolynomial (Fin (m + n - 1 + 1)) K

/-- DVR obtained by localizing the reciprocal coordinate ring at `y_i=0`. -/
abbrev criticalRecipCoordinateLocalRing
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n - 1 + 1)) :=
  Localization.AtPrime (coordDivisor (k := K) i).1

/-- Adic valuation of the reciprocal rational function field along `y_i=0`. -/
noncomputable def criticalRecipCoordinateFieldValuation
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n - 1 + 1)) :
    Valuation (FractionRing (criticalRecipCoordinateRing K m n))
      (WithZero (Multiplicative ℤ)) :=
  let A := criticalRecipCoordinateLocalRing K m n i
  (IsDiscreteValuationRing.maximalIdeal A).valuation
    (FractionRing (criticalRecipCoordinateRing K m n))

/-- Transported reciprocal coordinate valuation on the actual critical source field. -/
noncomputable def criticalSourceRecipCoordinateValuation
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin (m + n - 1 + 1)) :
    Valuation (criticalSourceField K m n) (WithZero (Multiplicative ℤ)) :=
  Valuation.comap (criticalSourceRecipFieldEquiv K hm hn).symm.toRingHom
    (criticalRecipCoordinateFieldValuation K m n i)

/-- Integer order homomorphism on source-field units along a reciprocal coordinate divisor. -/
noncomputable def criticalSourceRecipCoordinateOrderHom
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin (m + n - 1 + 1)) :
    (criticalSourceField K m n)ˣ →* Multiplicative ℤ :=
  valuationOrderHom (criticalSourceRecipCoordinateValuation K hm hn i)

/-- The reciprocal-coordinate field presentation evaluates coordinate polynomials at the actual
reciprocal source coordinates. -/
theorem criticalSourceRecipFieldEquiv_algebraMap_apply
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p : criticalRecipCoordinateRing K m n) :
    criticalSourceRecipFieldEquiv K hm hn
        (algebraMap (criticalRecipCoordinateRing K m n)
          (FractionRing (criticalRecipCoordinateRing K m n)) p) =
      MvPolynomial.aeval (criticalSourceRecipReindexed K hm hn) p := by
  let hAI := algebraicIndependent_criticalSourceRecip K hm hn
  have h := hAI.aevalEquivField_algebraMap_apply_coe p
  rw [criticalSourceRecipFieldEquiv, AlgEquiv.trans_apply]
  change (((algebraicIndependent_criticalSourceRecip K hm hn).aevalEquivField
      (algebraMap _ (FractionRing (criticalRecipCoordinateRing K m n)) p) :
        IntermediateField.adjoin K
          (Set.range (criticalSourceRecipReindexed K hm hn))) :
      criticalSourceField K m n) = _
  exact h

/-- Inverse form of `criticalSourceRecipFieldEquiv_algebraMap_apply`. -/
theorem criticalSourceRecipFieldEquiv_symm_aeval
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p : criticalRecipCoordinateRing K m n) :
    (criticalSourceRecipFieldEquiv K hm hn).symm
        (MvPolynomial.aeval (criticalSourceRecipReindexed K hm hn) p) =
      algebraMap (criticalRecipCoordinateRing K m n)
        (FractionRing (criticalRecipCoordinateRing K m n)) p := by
  apply (criticalSourceRecipFieldEquiv K hm hn).injective
  rw [(criticalSourceRecipFieldEquiv K hm hn).apply_symm_apply]
  exact (criticalSourceRecipFieldEquiv_algebraMap_apply K hm hn p).symm

/-- A reciprocal coordinate polynomial outside `y_i=0` has valuation one. -/
theorem criticalRecipCoordinateFieldValuation_algebraMap_eq_one
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n - 1 + 1))
    {p : criticalRecipCoordinateRing K m n}
    (hp : p ∉ (coordDivisor (k := K) i).1) :
    criticalRecipCoordinateFieldValuation K m n i
        (algebraMap (criticalRecipCoordinateRing K m n)
          (FractionRing (criticalRecipCoordinateRing K m n)) p) = 1 := by
  let R := criticalRecipCoordinateRing K m n
  let A := criticalRecipCoordinateLocalRing K m n i
  let v := IsDiscreteValuationRing.maximalIdeal A
  change v.valuation (FractionRing R) (algebraMap R (FractionRing R) p) = 1
  have hmap : algebraMap R (FractionRing R) p =
      algebraMap A (FractionRing R) (algebraMap R A p) :=
    IsScalarTower.algebraMap_apply R A (FractionRing R) p
  rw [hmap, v.valuation_of_algebraMap]
  apply intValuation_eq_one_iff.mpr
  change algebraMap R A p ∉ IsLocalRing.maximalIdeal A
  rw [IsLocalRing.mem_maximalIdeal]
  intro hnonunit
  exact hnonunit ((IsLocalization.AtPrime.isUnit_to_map_iff A
    (coordDivisor (k := K) i).1 p).2 hp)

/-- The defining reciprocal coordinate has valuation `exp(-1)`. -/
theorem criticalRecipCoordinateFieldValuation_X_self
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n - 1 + 1)) :
    criticalRecipCoordinateFieldValuation K m n i
        (algebraMap (criticalRecipCoordinateRing K m n)
          (FractionRing (criticalRecipCoordinateRing K m n)) (X i)) =
      WithZero.exp (-1 : ℤ) := by
  let R := criticalRecipCoordinateRing K m n
  let A := criticalRecipCoordinateLocalRing K m n i
  let v := IsDiscreteValuationRing.maximalIdeal A
  change v.valuation (FractionRing R) (algebraMap R (FractionRing R) (X i)) = _
  have hmap : algebraMap R (FractionRing R) (X i) =
      algebraMap A (FractionRing R) (algebraMap R A (X i)) :=
    IsScalarTower.algebraMap_apply R A (FractionRing R) (X i)
  rw [hmap, v.valuation_of_algebraMap]
  apply v.intValuation_singleton
  · intro hzero
    have hinj : Function.Injective (algebraMap R A) :=
      IsLocalization.injective A
        (coordDivisor (k := K) i).1.primeCompl_le_nonZeroDivisors
    exact MvPolynomial.X_ne_zero i (hinj (by simpa using hzero))
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
      (irreducible_algebraMap_X i)

/-- A reciprocal coordinate, indexed in the reciprocal rational presentation, as a source-field
unit. -/
noncomputable def criticalSourceRecipReindexedUnit
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin (m + n - 1 + 1)) :
    (criticalSourceField K m n)ˣ :=
  Units.mk0 (criticalSourceRecipReindexed K hm hn i) (by
    intro hzero
    exact ((algebraicIndependent_criticalSourceRecip K hm hn).transcendental i)
      (hzero ▸ isAlgebraic_zero))

/-- The `y_n=0` order sees the marked reciprocal coordinate exactly once. -/
theorem criticalSourceRecipCoordinateOrderHom_recip_self
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSourceRecipCoordinateOrderHom K hm hn ⟨n, by omega⟩
        (criticalSourceRecipReindexedUnit K hm hn ⟨n, by omega⟩) =
      Multiplicative.ofAdd (1 : ℤ) := by
  let R := criticalRecipCoordinateRing K m n
  let F := FractionRing R
  let i : Fin (m + n - 1 + 1) := ⟨n, by omega⟩
  change criticalSourceRecipCoordinateOrderHom K hm hn i
      (criticalSourceRecipReindexedUnit K hm hn i) = Multiplicative.ofAdd (1 : ℤ)
  have hpre : (criticalSourceRecipFieldEquiv K hm hn).symm
      (criticalSourceRecipReindexed K hm hn i) = algebraMap R F (X i) := by
    simpa only [MvPolynomial.aeval_X] using
      (criticalSourceRecipFieldEquiv_symm_aeval K hm hn (X i))
  have hval : criticalSourceRecipCoordinateValuation K hm hn i
      (criticalSourceRecipReindexed K hm hn i) = WithZero.exp (-1 : ℤ) := by
    rw [criticalSourceRecipCoordinateValuation, Valuation.comap_apply]
    change criticalRecipCoordinateFieldValuation K m n i
      ((criticalSourceRecipFieldEquiv K hm hn).symm
        (criticalSourceRecipReindexed K hm hn i)) = _
    rw [hpre, criticalRecipCoordinateFieldValuation_X_self]
  apply WithZero.coe_injective
  change (↑((criticalSourceRecipCoordinateValuation K hm hn i
    (criticalSourceRecipReindexed K hm hn i)).unzero _)⁻¹ :
      WithZero (Multiplicative ℤ)) = _
  rw [WithZero.coe_inv, WithZero.coe_unzero, hval]
  rfl

/-- For `m,n ≥ 2`, the `y_n=0` order does not see the marked raw coordinate `x_m`. -/
theorem criticalSourceRecipCoordinateOrderHom_raw_eq_zero
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    criticalSourceRecipCoordinateOrderHom K (by omega) (by omega) ⟨n, by omega⟩
        (criticalSourceRawUnit K m n ⟨m, by omega⟩) = 1 := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  let R := criticalRecipCoordinateRing K m n
  let F := FractionRing R
  let i : Fin (m + n - 1 + 1) := ⟨n, by omega⟩
  let j : Fin (m + n) := ⟨m, by omega⟩
  let P := criticalReciprocalNumerator K (m + n - 1 + 1) m
  change criticalSourceRecipCoordinateOrderHom K hm0 hn0 i
      (criticalSourceRawUnit K m n j) = 1
  have hP : P ∉ (coordDivisor (k := K) i).1 := by
    simpa [P, i] using
      (criticalReciprocalNumerator_not_mem_coordDivisor K
        (L := m + n - 1 + 1) (k := m) (m := n) (by omega) hn (by omega))
  have hY0 : (X (⟨0, by omega⟩ : Fin (m + n - 1 + 1)) : R) ∉
      (coordDivisor (k := K) i).1 := by
    intro hmem
    have hzero := (orderAt_ne_zero_iff (coordDivisor (k := K) i)
      (X (⟨0, by omega⟩ : Fin (m + n - 1 + 1)))).mpr hmem
    have hne : (⟨0, by omega⟩ : Fin (m + n - 1 + 1)) ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      simp [i] at this
      omega
    exact hzero (orderAt_coordDivisor_X_of_ne hne)
  have hPval := criticalRecipCoordinateFieldValuation_algebraMap_eq_one K m n i hP
  have hYval := criticalRecipCoordinateFieldValuation_algebraMap_eq_one K m n i hY0
  have hformula : criticalSourceRaw K m n j =
      MvPolynomial.aeval (criticalSourceRecipReindexed K hm0 hn0) P /
        criticalSourceRecipReindexed K hm0 hn0 ⟨0, by omega⟩ ^ (m + 1) := by
    simpa [j, P, hm0, hn0] using
      (criticalSourceRaw_eq_reciprocalNumerator_div K hm0 hn0
        (k := m) (by omega))
  have hPpre : (criticalSourceRecipFieldEquiv K hm0 hn0).symm
      (MvPolynomial.aeval (criticalSourceRecipReindexed K hm0 hn0) P) =
        algebraMap R F P :=
    criticalSourceRecipFieldEquiv_symm_aeval K hm0 hn0 P
  have hYpre : (criticalSourceRecipFieldEquiv K hm0 hn0).symm
      (criticalSourceRecipReindexed K hm0 hn0 ⟨0, by omega⟩) =
        algebraMap R F (X (⟨0, by omega⟩ : Fin (m + n - 1 + 1))) := by
    simpa only [MvPolynomial.aeval_X] using
      (criticalSourceRecipFieldEquiv_symm_aeval K hm0 hn0
        (X (⟨0, by omega⟩ : Fin (m + n - 1 + 1))))
  have hval : criticalSourceRecipCoordinateValuation K hm0 hn0 i
      (criticalSourceRaw K m n j) = 1 := by
    rw [criticalSourceRecipCoordinateValuation, Valuation.comap_apply]
    change criticalRecipCoordinateFieldValuation K m n i
      ((criticalSourceRecipFieldEquiv K hm0 hn0).symm
        (criticalSourceRaw K m n j)) = 1
    rw [hformula, map_div₀ (criticalSourceRecipFieldEquiv K hm0 hn0).symm,
      map_pow (criticalSourceRecipFieldEquiv K hm0 hn0).symm,
      hPpre, hYpre, Valuation.map_div, Valuation.map_pow, hPval, hYval]
    simp
  apply WithZero.coe_injective
  change (↑((criticalSourceRecipCoordinateValuation K hm0 hn0 i
    (criticalSourceRaw K m n j)).unzero _)⁻¹ :
      WithZero (Multiplicative ℤ)) = 1
  rw [WithZero.coe_inv, WithZero.coe_unzero, hval]
  simp

end

end GaloisForLFunctions.HTGeometry
