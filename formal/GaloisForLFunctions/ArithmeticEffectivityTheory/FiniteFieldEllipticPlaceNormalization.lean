import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticProductFormula
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLocalFields
import GaloisForLFunctions.HTGeometry.FinitePlaceTransport

/-!
# Product normalization on the actual adelic places

The canonical affine-ring equivalence transports ideal divisibility, adic
valuations and residue cardinalities. Thus the curve product formula uses
exactly the finite completions occurring in its adele ring.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open IsDedekindDomain Function
open scoped NNReal WithZero WithZeroMulInt
noncomputable section

private theorem ideal_map_symm {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    Ideal.map e.symm (Ideal.map e I) = I := by
  change Ideal.map e.symm.toRingHom (Ideal.map e.toRingHom I) = I
  rw [Ideal.map_map]
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by ext x; simp
  rw [he, Ideal.map_id]

private theorem ideal_map_dvd {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {I J : Ideal R} (h : I ∣ J) : Ideal.map e I ∣ Ideal.map e J := by
  obtain ⟨C, rfl⟩ := h
  exact ⟨Ideal.map e C, Ideal.map_mul _ _ _⟩

private theorem intValuation_comap_equiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S) (v : HeightOneSpectrum S) (a : R) :
    (heightOneSpectrumComap e v).intValuation a = v.intValuation (e a) := by
  classical
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero, map_zero]
  have hea : e a ≠ 0 := fun h => ha (e.injective (h.trans (map_zero e).symm))
  have hmap : Ideal.map e (heightOneSpectrumComap e v).asIdeal = v.asIdeal :=
    Ideal.map_comap_of_surjective _ e.surjective _
  have hkey (n : ℕ) :
      (heightOneSpectrumComap e v).intValuation a ≤ WithZero.exp (-(n : ℤ)) ↔
        v.intValuation (e a) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd,
      HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    constructor
    · intro h
      have hh := ideal_map_dvd e h
      rwa [Ideal.map_pow, hmap, Ideal.map_span, Set.image_singleton] at hh
    · intro h
      have hh : Ideal.map e ((heightOneSpectrumComap e v).asIdeal ^ n) ∣
          Ideal.map e (Ideal.span {a}) := by
        rwa [Ideal.map_pow, hmap, Ideal.map_span, Set.image_singleton]
      have hback := ideal_map_dvd e.symm hh
      rwa [ideal_map_symm, ideal_map_symm] at hback
  obtain ⟨m, hm⟩ : ∃ m : ℕ,
      (heightOneSpectrumComap e v).intValuation a = WithZero.exp (-(m : ℤ)) :=
    ⟨_, (heightOneSpectrumComap e v).intValuation_if_neg ha⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v.intValuation (e a) = WithZero.exp (-(n : ℤ)) :=
    ⟨_, v.intValuation_if_neg hea⟩
  have h₁ := (hkey m).mp (le_of_eq hm)
  have h₂ := (hkey n).mpr (le_of_eq hn)
  rw [hn] at h₁
  rw [hm] at h₂
  rw [hm, hn]
  exact le_antisymm h₂ h₁

/-- Canonical identification of the adelic finite places with affine prime ideals. -/
def finitePlaceAffineEquiv : FinitePlace ≃ HeightOneSpectrum A :=
  heightOneSpectrumEquiv coordinateRingEquivRingOfIntegers.toRingEquiv.symm

/-- Both presentations have identical adic valuations on the actual function field. -/
theorem finitePlaceAffineEquiv_valuation (v : FinitePlace) (z : K) :
    (finitePlaceAffineEquiv v).valuation K z = v.valuation K z := by
  have hring (a : A) : (finitePlaceAffineEquiv v).valuation K (algebraMap A K a) =
      v.valuation K (algebraMap A K a) := by
    conv_rhs => rw [← coordinateRingEquivRingOfIntegers_algebraMap a]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact intValuation_comap_equiv coordinateRingEquivRingOfIntegers.toRingEquiv v a
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A z
  rw [map_div₀, map_div₀, hring, hring]

/-- Residue rings agree through the same canonical affine-ring map. -/
def finitePlaceAffineResidueEquiv (v : FinitePlace) :
    (A ⧸ (finitePlaceAffineEquiv v).asIdeal) ≃+* (RingOfIntegers ⧸ v.asIdeal) :=
  Ideal.quotientEquiv _ _ coordinateRingEquivRingOfIntegers.toRingEquiv
    (Ideal.map_comap_of_surjective _ coordinateRingEquivRingOfIntegers.surjective _).symm

theorem finitePlaceAffineEquiv_residue_card (v : FinitePlace) :
    affineIdealNorm (finitePlaceAffineEquiv v).asIdeal =
      Nat.card (RingOfIntegers ⧸ v.asIdeal) :=
  Nat.card_congr (finitePlaceAffineResidueEquiv v).toEquiv

private theorem finitePlace_residue_card_ne_zero (v : FinitePlace) :
    (Nat.card (RingOfIntegers ⧸ v.asIdeal) : ℝ≥0) ≠ 0 := by
  rw [← finitePlaceAffineEquiv_residue_card]
  exact_mod_cast (affineIdealNorm_pos _ (finitePlaceAffineEquiv v).ne_bot).ne'

/-- Actual finite completion normalized by its actual residue cardinality. -/
def finiteCompletionMagnitude (v : FinitePlace) : v.adicCompletion K →*₀ ℝ≥0 :=
  (WithZeroMulInt.toNNReal (finitePlace_residue_card_ne_zero v)).comp
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).toMonoidWithZeroHom

/-- On diagonal functions the completed magnitude is the affine-place magnitude. -/
theorem finiteCompletionMagnitude_algebraMap (v : FinitePlace) (z : K) :
    finiteCompletionMagnitude v (algebraMap K (v.adicCompletion K) z) =
      affinePlaceMagnitude (finitePlaceAffineEquiv v) z := by
  have he : Valued.v (algebraMap K (v.adicCompletion K) z) = v.valuation K z :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) z
  change WithZeroMulInt.toNNReal (finitePlace_residue_card_ne_zero v)
    (Valued.v (algebraMap K (v.adicCompletion K) z)) = _
  rw [he, ← finitePlaceAffineEquiv_valuation]
  change WithZeroMulInt.toNNReal (finitePlace_residue_card_ne_zero v)
    ((finitePlaceAffineEquiv v).valuation K z) =
    WithZeroMulInt.toNNReal (show (affineIdealNorm (finitePlaceAffineEquiv v).asIdeal :
      ℝ≥0) ≠ 0 from by
        exact_mod_cast (affineIdealNorm_pos _ (finitePlaceAffineEquiv v).ne_bot).ne')
      ((finitePlaceAffineEquiv v).valuation K z)
  congr 2
  exact_mod_cast (finitePlaceAffineEquiv_residue_card v).symm

/-- The infinity completion carries residue normalization three. -/
def infinityCompletionMagnitude : InfinityCompletion →*₀ ℝ≥0 :=
  (WithZeroMulInt.toNNReal (by norm_num : (3 : ℝ≥0) ≠ 0)).comp
    (Valued.v : Valuation InfinityCompletion ℤᵐ⁰).toMonoidWithZeroHom

theorem infinityCompletionMagnitude_embedding (z : K) :
    infinityCompletionMagnitude (infinityEmbedding z) = infinityMagnitude z := by
  change WithZeroMulInt.toNNReal (by norm_num : (3 : ℝ≥0) ≠ 0)
    (Valued.v (infinityEmbedding z)) = _
  rw [infinityEmbedding_valuation]
  rfl

/-- The diagonal product formula uses exactly the completions in the actual adele ring. -/
theorem adelic_product_formula {z : K} (hz : z ≠ 0) :
    infinityCompletionMagnitude (adeleEmbedding z).2 *
      (∏ᶠ v : FinitePlace, finiteCompletionMagnitude v ((adeleEmbedding z).1 v)) = 1 := by
  change infinityCompletionMagnitude (infinityEmbedding z) *
    (∏ᶠ v : FinitePlace,
      finiteCompletionMagnitude v (algebraMap K (v.adicCompletion K) z)) = 1
  simp only [infinityCompletionMagnitude_embedding, finiteCompletionMagnitude_algebraMap]
  rw [finprod_comp_equiv finitePlaceAffineEquiv (f := fun v => affinePlaceMagnitude v z)]
  exact product_formula hz

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.finitePlaceAffineEquiv_valuation
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelic_product_formula
