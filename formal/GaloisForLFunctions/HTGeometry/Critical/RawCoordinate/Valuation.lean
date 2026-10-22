import GaloisForLFunctions.HTGeometry.Critical.Reciprocal.Numerator
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Actual raw-coordinate divisorial valuations

The coordinate divisor `x_i=0` in the rational raw presentation supplies an integer-valued
divisorial order on the actual critical source field.  For `m,n ≥ 2`, the divisor `x_m=0` sees the
marked raw coordinate once and the marked reciprocal coordinate not at all.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum


/-- An adic valuation on a field induces the additive integer order on its unit group; inversion
changes mathlib's `exp (-ord)` convention into the usual positive order convention. -/
noncomputable def valuationOrderHom {F : Type*} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ))) : Fˣ →* Multiplicative ℤ :=
  MonoidHom.mk'
    (fun u => ((v (u : F)).unzero ((Valuation.ne_zero_iff v).2 u.ne_zero))⁻¹)
    (fun a b => by
      simp only [Units.val_mul, Valuation.map_mul]
      rw [WithZero.unzero_mul]
      exact (mul_inv_rev _ _).trans (mul_comm _ _))

/-- Raw polynomial-coordinate ring of the actual source field. -/
abbrev criticalRawCoordinateRing (K : Type*) [Field K] (m n : ℕ) :=
  MvPolynomial (Fin (m + n)) K

/-- DVR obtained by localizing the raw coordinate ring at `x_i=0`. -/
abbrev criticalRawCoordinateLocalRing
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n)) :=
  Localization.AtPrime (coordDivisor (k := K) i).1

/-- Adic valuation of the raw rational function field along `x_i=0`. -/
noncomputable def criticalRawCoordinateFieldValuation
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n)) :
    Valuation (FractionRing (criticalRawCoordinateRing K m n))
      (WithZero (Multiplicative ℤ)) :=
  let A := criticalRawCoordinateLocalRing K m n i
  (IsDiscreteValuationRing.maximalIdeal A).valuation
    (FractionRing (criticalRawCoordinateRing K m n))

/-- Transported raw coordinate valuation on the actual critical source field. -/
noncomputable def criticalSourceRawCoordinateValuation
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n)) :
    Valuation (criticalSourceField K m n) (WithZero (Multiplicative ℤ)) :=
  Valuation.comap (criticalSourceFieldEquiv K m n).symm.toRingHom
    (criticalRawCoordinateFieldValuation K m n i)

/-- Integer order homomorphism on nonzero elements of the actual source field along `x_i=0`. -/
noncomputable def criticalSourceRawCoordinateOrderHom
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n)) :
    (criticalSourceField K m n)ˣ →* Multiplicative ℤ :=
  valuationOrderHom (criticalSourceRawCoordinateValuation K m n i)

/-- The raw-coordinate field presentation evaluates embedded coordinate polynomials at the actual
raw source coordinates. -/
theorem criticalSourceFieldEquiv_algebraMap_apply
    (K : Type*) [Field K] (m n : ℕ)
    (p : criticalRawCoordinateRing K m n) :
    criticalSourceFieldEquiv K m n
        (algebraMap (criticalRawCoordinateRing K m n)
          (FractionRing (criticalRawCoordinateRing K m n)) p) =
      MvPolynomial.aeval (criticalSourceRaw K m n) p := by
  apply Subtype.ext
  have h := (algebraicIndependent_criticalAmbientRaw K m n).aevalEquivField_algebraMap_apply_coe p
  have hright : ((MvPolynomial.aeval (criticalSourceRaw K m n) p :
      criticalSourceField K m n) : genericJetField K (m + n)) =
      MvPolynomial.aeval
        (fun j : Fin (m + n) => criticalAmbientRaw K m n (j : ℕ)) p := by
    change (criticalSourceField K m n).val.toRingHom
        (MvPolynomial.aeval (criticalSourceRaw K m n) p) = _
    rw [MvPolynomial.map_aeval]
    rfl
  rw [hright]
  change (criticalSourceFieldEquiv K m n
      (algebraMap (criticalRawCoordinateRing K m n)
        (FractionRing (criticalRawCoordinateRing K m n)) p) :
      genericJetField K (m + n)) =
    MvPolynomial.aeval
      (fun j : Fin (m + n) => criticalAmbientRaw K m n (j : ℕ)) p
  simpa [criticalSourceFieldEquiv] using h

/-- Inverse form of `criticalSourceFieldEquiv_algebraMap_apply`. -/
theorem criticalSourceFieldEquiv_symm_aeval
    (K : Type*) [Field K] (m n : ℕ)
    (p : criticalRawCoordinateRing K m n) :
    (criticalSourceFieldEquiv K m n).symm
        (MvPolynomial.aeval (criticalSourceRaw K m n) p) =
      algebraMap (criticalRawCoordinateRing K m n)
        (FractionRing (criticalRawCoordinateRing K m n)) p := by
  apply (criticalSourceFieldEquiv K m n).injective
  rw [(criticalSourceFieldEquiv K m n).apply_symm_apply]
  exact (criticalSourceFieldEquiv_algebraMap_apply K m n p).symm

/-- A coordinate polynomial outside `x_i=0` has adic valuation one (divisorial order zero). -/
theorem criticalRawCoordinateFieldValuation_algebraMap_eq_one
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n))
    {p : criticalRawCoordinateRing K m n}
    (hp : p ∉ (coordDivisor (k := K) i).1) :
    criticalRawCoordinateFieldValuation K m n i
        (algebraMap (criticalRawCoordinateRing K m n)
          (FractionRing (criticalRawCoordinateRing K m n)) p) = 1 := by
  let R := criticalRawCoordinateRing K m n
  let P := coordDivisor (k := K) i
  let A := criticalRawCoordinateLocalRing K m n i
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

/-- The defining coordinate has valuation `exp(-1)`, hence divisorial order one. -/
theorem criticalRawCoordinateFieldValuation_X_self
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n)) :
    criticalRawCoordinateFieldValuation K m n i
        (algebraMap (criticalRawCoordinateRing K m n)
          (FractionRing (criticalRawCoordinateRing K m n)) (X i)) =
      WithZero.exp (-1 : ℤ) := by
  let R := criticalRawCoordinateRing K m n
  let P := coordDivisor (k := K) i
  let A := criticalRawCoordinateLocalRing K m n i
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

/-- Actual raw source coordinates are nonzero units of the source field. -/
noncomputable def criticalSourceRawUnit
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n)) :
    (criticalSourceField K m n)ˣ :=
  Units.mk0 (criticalSourceRaw K m n i) (by
    intro hzero
    exact ((algebraicIndependent_criticalSourceRaw K m n).transcendental i)
      (hzero ▸ isAlgebraic_zero))

/-- Actual reciprocal source coordinates are nonzero units of the source field. -/
noncomputable def criticalSourceRecipUnit
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin (m + n)) :
    (criticalSourceField K m n)ˣ :=
  Units.mk0 (criticalSourceRecip K m n i) (by
    let j : Fin (m + n - 1 + 1) := Fin.cast (by omega) i
    have hj : Transcendental K (criticalSourceRecipReindexed K hm hn j) :=
      (algebraicIndependent_criticalSourceRecip K hm hn).transcendental j
    intro hzero
    apply hj
    have heq : criticalSourceRecipReindexed K hm hn j = 0 := by
      simpa [criticalSourceRecipReindexed, j] using hzero
    exact heq ▸ isAlgebraic_zero)

/-- The `x_m=0` order sees the marked raw coordinate exactly once. -/
theorem criticalSourceRawCoordinateOrderHom_raw_self
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSourceRawCoordinateOrderHom K m n ⟨m, by omega⟩
        (criticalSourceRawUnit K m n ⟨m, by omega⟩) =
      Multiplicative.ofAdd (1 : ℤ) := by
  let R := criticalRawCoordinateRing K m n
  let F := FractionRing R
  let i : Fin (m + n) := ⟨m, by omega⟩
  change criticalSourceRawCoordinateOrderHom K m n i
      (criticalSourceRawUnit K m n i) = Multiplicative.ofAdd (1 : ℤ)
  have hpre : (criticalSourceFieldEquiv K m n).symm
      (criticalSourceRaw K m n i) = algebraMap R F (X i) := by
    simpa only [MvPolynomial.aeval_X] using
      (criticalSourceFieldEquiv_symm_aeval K m n (X i))
  have hval : criticalSourceRawCoordinateValuation K m n i
      (criticalSourceRaw K m n i) = WithZero.exp (-1 : ℤ) := by
    rw [criticalSourceRawCoordinateValuation, Valuation.comap_apply]
    change criticalRawCoordinateFieldValuation K m n i
      ((criticalSourceFieldEquiv K m n).symm (criticalSourceRaw K m n i)) = _
    rw [hpre,
      criticalRawCoordinateFieldValuation_X_self]
  apply WithZero.coe_injective
  change (↑((criticalSourceRawCoordinateValuation K m n i
    (criticalSourceRaw K m n i)).unzero _)⁻¹ :
      WithZero (Multiplicative ℤ)) = _
  rw [WithZero.coe_inv, WithZero.coe_unzero, hval]
  rfl

/-- For `m,n ≥ 2`, the `x_m=0` order does not see the marked reciprocal coordinate `y_n`. -/
theorem criticalSourceRawCoordinateOrderHom_recip_eq_zero
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    criticalSourceRawCoordinateOrderHom K m n ⟨m, by omega⟩
        (criticalSourceRecipUnit K (by omega) (by omega) ⟨n, by omega⟩) = 1 := by
  let R := criticalRawCoordinateRing K m n
  let F := FractionRing R
  let i : Fin (m + n) := ⟨m, by omega⟩
  let j : Fin (m + n) := ⟨n, by omega⟩
  let P := criticalReciprocalNumerator K (m + n) n
  change criticalSourceRawCoordinateOrderHom K m n i
      (criticalSourceRecipUnit K (by omega) (by omega) j) = 1
  have hP : P ∉ (coordDivisor (k := K) i).1 := by
    simpa [P, i] using
      (criticalReciprocalNumerator_not_mem_coordDivisor K
        (L := m + n) (k := n) (m := m) (by omega) hm (by omega))
  have hX0 : (X (⟨0, by omega⟩ : Fin (m + n)) : R) ∉
      (coordDivisor (k := K) i).1 := by
    intro hmem
    have hzero := (orderAt_ne_zero_iff (coordDivisor (k := K) i)
      (X (⟨0, by omega⟩ : Fin (m + n)))).mpr hmem
    have hne : (⟨0, by omega⟩ : Fin (m + n)) ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      simp [i] at this
      omega
    exact hzero (orderAt_coordDivisor_X_of_ne hne)
  have hPval := criticalRawCoordinateFieldValuation_algebraMap_eq_one K m n i hP
  have hXval := criticalRawCoordinateFieldValuation_algebraMap_eq_one K m n i hX0
  have hformula : criticalSourceRecip K m n j =
      MvPolynomial.aeval (criticalSourceRaw K m n) P /
        criticalSourceRaw K m n ⟨0, by omega⟩ ^ (n + 1) := by
    simpa [j, P] using
      (criticalSourceRecip_eq_numerator_div K (m := m) (n := n) (k := n) (by omega))
  have hPpre : (criticalSourceFieldEquiv K m n).symm
      (MvPolynomial.aeval (criticalSourceRaw K m n) P) = algebraMap R F P := by
    exact criticalSourceFieldEquiv_symm_aeval K m n P
  have hXpre : (criticalSourceFieldEquiv K m n).symm
      (criticalSourceRaw K m n ⟨0, by omega⟩) =
        algebraMap R F (X (⟨0, by omega⟩ : Fin (m + n))) := by
    simpa only [MvPolynomial.aeval_X] using
      (criticalSourceFieldEquiv_symm_aeval K m n
        (X (⟨0, by omega⟩ : Fin (m + n))))
  have hval : criticalSourceRawCoordinateValuation K m n i
      (criticalSourceRecip K m n j) = 1 := by
    rw [criticalSourceRawCoordinateValuation, Valuation.comap_apply]
    change criticalRawCoordinateFieldValuation K m n i
      ((criticalSourceFieldEquiv K m n).symm (criticalSourceRecip K m n j)) = 1
    rw [hformula,
      map_div₀ (criticalSourceFieldEquiv K m n).symm,
      map_pow (criticalSourceFieldEquiv K m n).symm,
      hPpre, hXpre, Valuation.map_div, Valuation.map_pow, hPval, hXval]
    simp
  apply WithZero.coe_injective
  change (↑((criticalSourceRawCoordinateValuation K m n i
    (criticalSourceRecip K m n j)).unzero _)⁻¹ :
      WithZero (Multiplicative ℤ)) = 1
  rw [WithZero.coe_inv, WithZero.coe_unzero, hval]
  simp

end

end GaloisForLFunctions.HTGeometry
