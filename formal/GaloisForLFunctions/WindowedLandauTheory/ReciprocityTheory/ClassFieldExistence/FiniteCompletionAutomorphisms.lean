import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionBaseChange
import GaloisForLFunctions.HTGeometry.ABHN.ValuationCoordinateTransport
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! The stabilizer of a finite prime acts by valuation-preserving maps on the completion. -/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

section Stabilizer

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))

omit [NumberField L] in
private theorem smul_mem_asIdeal_pow_iff {σ : L ≃ₐ[K] L} (hσ : σ • w.asIdeal = w.asIdeal) (r : 𝓞 L)
    (n : ℕ) : σ • r ∈ w.asIdeal ^ n ↔ r ∈ w.asIdeal ^ n := by
  have h : σ • (w.asIdeal ^ n) = w.asIdeal ^ n := by
    rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def, hσ]
  conv_lhs => rw [← h]
  exact Ideal.smul_mem_pointwise_smul_iff

private theorem intValuation_smul {σ : L ≃ₐ[K] L} (hσ : σ • w.asIdeal = w.asIdeal)
    (r : 𝓞 L) : w.intValuation (σ • r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have hr' : σ • r ≠ 0 := fun h => hr (by rw [← inv_smul_smul σ r, h, smul_zero])
  have h (n : ℕ) : w.intValuation (σ • r) ≤ exp (-(n : ℤ)) ↔
      w.intValuation r ≤ exp (-(n : ℤ)) := by
    rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem,
      smul_mem_asIdeal_pow_iff w hσ]
  rw [intValuation_eq_exp_neg_multiplicity _ hr',
    intValuation_eq_exp_neg_multiplicity _ hr] at h ⊢
  simp only [exp_le_exp, neg_le_neg_iff, Nat.cast_le] at h
  rw [le_antisymm ((h _).mp le_rfl) ((h _).mpr le_rfl)]

private theorem valuation_algEquiv_apply_of_smul_eq {σ : L ≃ₐ[K] L} (hσ : σ • w.asIdeal = w.asIdeal)
    (x : L) : w.valuation L (σ x) = w.valuation L x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hs : ∀ c : 𝓞 L, σ (algebraMap (𝓞 L) L c) = algebraMap (𝓞 L) L (σ • c) := fun c ↦ rfl
  rw [map_div₀, map_div₀, map_div₀, hs, hs, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_smul w hσ,
    intValuation_smul w hσ]

end Stabilizer

section CompletionMap

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))

/-- An automorphism stabilizing the prime extends to its completion. -/
def adicCompletionRingHomOf (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal) :
    w.adicCompletion L →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (WithVal.congr (w.valuation L) (w.valuation L) σ.toRingEquiv).toRingHom
      (GaloisForLFunctions.HTGeometry.ABHN.uniformContinuous_congr_of_valuation_eq
        _ _ σ.toRingEquiv (valuation_algEquiv_apply_of_smul_eq w hσ)).continuous).comp
      (adicCompletion.equiv L w).toRingHom)

theorem continuous_adicCompletionRingHomOf (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal) :
    Continuous (adicCompletionRingHomOf w σ hσ) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion L w)

theorem adicCompletionRingHomOf_algebraMap (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal)
    (x : L) : adicCompletionRingHomOf w σ hσ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) (σ x) := by
  apply adicCompletion.ext
  change UniformSpace.Completion.mapRingHom
    (WithVal.congr (w.valuation L) (w.valuation L) σ.toRingEquiv).toRingHom
    (GaloisForLFunctions.HTGeometry.ABHN.uniformContinuous_congr_of_valuation_eq
      _ _ σ.toRingEquiv (valuation_algEquiv_apply_of_smul_eq w hσ)).continuous
    ((algebraMap L (WithVal (w.valuation L)) x : WithVal (w.valuation L)) :
      UniformSpace.Completion (WithVal (w.valuation L))) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

theorem ringHom_ext_adicCompletion {f g : w.adicCompletion L →+* w.adicCompletion L}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g :=
  RingHom.ext (congrFun ((denseRange_algebraMap (R := 𝓞 L) (K := L) w).equalizer hf hg
    (funext h)))

theorem valued_adicCompletionRingHomOf (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal)
    (y : w.adicCompletion L) : Valued.v (adicCompletionRingHomOf w σ hσ y) = Valued.v y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hz : Valued.v (adicCompletionRingHomOf w σ hσ y) ≠ 0 := by simpa using hy
  have h1 := Valued.locally_const hy'
  have h2 := (continuous_adicCompletionRingHomOf w σ hσ).continuousAt.preimage_mem_nhds
    (Valued.locally_const hz)
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 L) (K := L) w).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hk1 hk2
  rw [← hk1, ← hk2, adicCompletionRingHomOf_algebraMap]
  erw [valuedAdicCompletion_eq_valuation' w, valuedAdicCompletion_eq_valuation' w]
  exact valuation_algEquiv_apply_of_smul_eq w hσ k

end CompletionMap

end GlobalTheory.Reciprocity
