import GaloisForLFunctions.HTGeometry.TranscendentalMobius
import Mathlib.Data.Complex.Basic

/-!
# The anharmonic substitution of the rational function field

The Möbius transformation `r z = 1/(1-z)` has order three; it generates the anharmonic action on
the three-point orbit `{0, 1, ∞}`.  Substituting it into a rational function is a `ℂ`-algebra
automorphism of `ℂ(z)`, because `r` generates the coordinate back: `z = 1 - r(z)⁻¹`.

The module also records the ring-hom extensionality of `ℂ(z)`: a ring homomorphism out of the
rational function field into a field is determined by its values on the constants and on the
coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open RatFunc

noncomputable section

/-- The anharmonic coordinate `1/(1 - z)`. -/
def anharmonicRatFunc : RatFunc ℂ := (1 - RatFunc.X)⁻¹

theorem transcendental_anharmonicRatFunc : Transcendental ℂ anharmonicRatFunc := by
  intro halg
  have h1 : IsAlgebraic ℂ (anharmonicRatFunc)⁻¹ := halg.inv
  rw [anharmonicRatFunc, inv_inv] at h1
  have hone : IsAlgebraic ℂ (1 : RatFunc ℂ) := isAlgebraic_one
  have hX : IsAlgebraic ℂ (RatFunc.X : RatFunc ℂ) := by
    have h2 := hone.sub h1
    simpa using h2
  exact RatFunc.transcendental_X hX

theorem adjoin_anharmonicRatFunc_eq_top :
    IntermediateField.adjoin ℂ {anharmonicRatFunc} = ⊤ := by
  have ht : anharmonicRatFunc ∈ IntermediateField.adjoin ℂ ({anharmonicRatFunc} : Set (RatFunc ℂ)) :=
    IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have hX : (RatFunc.X : RatFunc ℂ)
      ∈ IntermediateField.adjoin ℂ ({anharmonicRatFunc} : Set (RatFunc ℂ)) := by
    have hmem : (1 : RatFunc ℂ) - anharmonicRatFunc⁻¹
        ∈ IntermediateField.adjoin ℂ ({anharmonicRatFunc} : Set (RatFunc ℂ)) :=
      sub_mem (one_mem _) (inv_mem ht)
    simpa [anharmonicRatFunc] using hmem
  rw [← top_le_iff, ← RatFunc.adjoin_X]
  exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hX)

/-- **The anharmonic substitution.**  Substituting `1/(1-z)` for the coordinate is a `ℂ`-algebra
automorphism of the rational function field. -/
def anharmonicRatFuncEquiv : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ :=
  ((RatFunc.algEquivOfTranscendental anharmonicRatFunc
      transcendental_anharmonicRatFunc).trans
    (IntermediateField.equivOfEq adjoin_anharmonicRatFunc_eq_top)).trans
    IntermediateField.topEquiv

@[simp] theorem anharmonicRatFuncEquiv_X :
    anharmonicRatFuncEquiv RatFunc.X = anharmonicRatFunc :=
  RatFunc.algEquivOfTranscendental_X anharmonicRatFunc transcendental_anharmonicRatFunc

/-- **Extensionality for the rational function field.**  A ring homomorphism into a field is
determined by its values on the constants and on the coordinate. -/
theorem ratFunc_ringHom_ext {L : Type*} [Field L] {f g : RatFunc ℂ →+* L}
    (hC : ∀ c : ℂ, f (RatFunc.C c) = g (RatFunc.C c))
    (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  have hpoly : f.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      = g.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · exact hC c
    · exact hX
  ext x
  induction x using RatFunc.induction_on with
  | _ p q hq =>
      rw [map_div₀, map_div₀]
      have hp : f (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
          = g (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) :=
        RingHom.congr_fun hpoly p
      have hq' : f (algebraMap (Polynomial ℂ) (RatFunc ℂ) q)
          = g (algebraMap (Polynomial ℂ) (RatFunc ℂ) q) :=
        RingHom.congr_fun hpoly q
      rw [hp, hq']

end

end GaloisForLFunctions.HTGeometry
