import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexOfAVirtualConfigurationCountsItsZerosAndItsPoles
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheHodgeIndexOfANumberRingCountsTheZerosOfItsZetaFunction
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfANumberRingThroughItsIdealsHasTheIndexOfItsDedekindZetaFunction

/-!
# The index of a quotient of `L`-functions counts its zeros and its poles

The index law of a virtual configuration, on the configurations of the programme.

* **Quotients of products** (`exists_le_negIndex_quotient_iff`). For two finite families of
  tempered configurations, the form `Σ_k W_{Z_k} − Σ_k W_{Z'_k}` has `n` negative squares on some
  family of `n` tests iff the quotient has at least `n` defect points: points right of the line
  where the net multiplicity `Σ_k m_k(ρ) − Σ_k m'_k(ρ)` is not zero, and points on the line where
  it is negative (`mem_virtualDefect_superposeFamily`). With the zeros of Hecke `L`-functions as
  members this is the index of a virtual character of ray class characters, with repetition; an
  Artin character is one by Brauer's theorem (not in the corpus).
* **The relative square of a number ring** (`exists_le_negIndex_relativeSquare_iff`,
  `forall_negIndex_relativeSquare_eq_zero_iff`). For two number fields `K`, `L` the form
  `W_{ζ_L} − W_{ζ_K}` has no negative square iff `ζ_L` and `ζ_K` have the same zeros right of the
  line, with multiplicities, and on the line every zero of `ζ_K` is a zero of `ζ_L` of at least
  the same multiplicity. For `K ⊆ L` the second condition is Dedekind's conjecture on the line.
-/

open Finset Matrix
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri

/-! ### Quotients of products -/

section Families

variable {κ κ' : Type*} [Fintype κ] [Fintype κ']

/-- The multiplicity of a superposition is the sum of the multiplicities. -/
theorem extMult_superposeFamily (Z : κ → ZeroConfig) (ρ : ℂ) :
    extMult (superposeFamily Z) ρ = ∑ k, extMult (Z k) ρ := by
  classical
  unfold extMult
  by_cases h : ρ ∈ (superposeFamily Z).carrier
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun k _ =>
      if_neg fun hk => h (Set.mem_iUnion.mpr ⟨k, hk⟩)).symm

/-- **The index of a quotient of products.** -/
theorem exists_le_negIndex_quotient_iff (Z : κ → ZeroConfig) (Z' : κ' → ZeroConfig)
    (hZ : ∀ k, SquareRootThreshold.TemperedConfig (Z k))
    (hZ' : ∀ k, SquareRootThreshold.TemperedConfig (Z' k)) (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (∑ k, zeroGram (Z k) f - ∑ k, zeroGram (Z' k) f)) ↔
      (n : ℕ∞) ≤ (virtualDefect (superposeFamily Z) (superposeFamily Z')).encard := by
  rw [← exists_le_negIndex_sub_zeroGram_iff _ _ (temperedConfig_superposeFamily Z hZ)
    (temperedConfig_superposeFamily Z' hZ') n]
  refine exists_congr fun f => ⟨?_, ?_⟩
  · rintro ⟨hf, hfc, h⟩
    exact ⟨hf, hfc, by
      rwa [zeroGram_superposeFamily Z hZ f hf hfc, zeroGram_superposeFamily Z' hZ' f hf hfc]⟩
  · rintro ⟨hf, hfc, h⟩
    exact ⟨hf, hfc, by
      rwa [← zeroGram_superposeFamily Z hZ f hf hfc,
        ← zeroGram_superposeFamily Z' hZ' f hf hfc]⟩

/-- The defect points of a quotient of products, through the net multiplicity. -/
theorem mem_virtualDefect_superposeFamily (Z : κ → ZeroConfig) (Z' : κ' → ZeroConfig) (ρ : ℂ) :
    ρ ∈ virtualDefect (superposeFamily Z) (superposeFamily Z') ↔
      (1 / 2 < ρ.re ∧ ∑ k, extMult (Z k) ρ ≠ ∑ k, extMult (Z' k) ρ) ∨
        (ρ.re = 1 / 2 ∧ ∑ k, extMult (Z k) ρ < ∑ k, extMult (Z' k) ρ) := by
  rw [virtualDefect, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq,
    extMult_superposeFamily, extMult_superposeFamily]

end Families

/-! ### The relative square of a number ring -/

section Relative

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]

/-- **The index of the relative square.** The difference of Weil's forms of two number rings has
`n` negative squares on some family of `n` tests iff the quotient of their Dedekind zeta
functions has at least `n` zeros or poles right of the critical line or poles on it. -/
theorem exists_le_negIndex_relativeSquare_iff (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (zeroGram (dedekindZeros L) f - zeroGram (dedekindZeros K) f)) ↔
      (n : ℕ∞) ≤ (virtualDefect (dedekindZeros L) (dedekindZeros K)).encard :=
  exists_le_negIndex_sub_zeroGram_iff _ _ (temperedConfig_classZeros L 1)
    (temperedConfig_classZeros K 1) n

/-- **Castelnuovo and Severi on the relative square.** The difference of Weil's forms of two
number rings has no negative square iff their zeta functions have the same zeros right of the
critical line, with multiplicities, and every zero of the second on the line is a zero of the
first of at least the same multiplicity. -/
theorem forall_negIndex_relativeSquare_eq_zero_iff :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
        (∀ i, HasCompactSupport (f i)) →
        hermNegIndex (zeroGram (dedekindZeros L) f - zeroGram (dedekindZeros K) f) = 0) ↔
      (∀ ρ : ℂ, 1 / 2 < ρ.re → extMult (dedekindZeros L) ρ = extMult (dedekindZeros K) ρ) ∧
        ∀ ρ : ℂ, ρ.re = 1 / 2 → extMult (dedekindZeros K) ρ ≤ extMult (dedekindZeros L) ρ :=
  forall_negIndex_sub_zeroGram_eq_zero_iff _ _ (temperedConfig_classZeros L 1)
    (temperedConfig_classZeros K 1)

end Relative

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
