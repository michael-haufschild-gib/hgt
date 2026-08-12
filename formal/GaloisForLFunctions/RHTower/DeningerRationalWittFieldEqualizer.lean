import GaloisForLFunctions.RHTower.DeningerRationalWittFatouIntersection
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Field equalizer descent for literal rational Witt vectors

This module proves Deninger 2025, Corollary 1.12(1) (source label `t1.10`).  For every field extension `L/K`, literal
rational Witt vectors over `K` are exactly the equalizer of the two maps from `W_rat(L)` to
`W_rat(L ⊗[K] L)`.

The proof is coefficientwise fpqc descent, not an appeal to a rational-Witt sheaf premise.
Faithful flatness identifies the equalizer of `x ↦ x ⊗ 1` and `x ↦ 1 ⊗ x` on `L` with the image
of `K`.  Applying this to every coefficient of the literal power series produces a series over
`K`; the already proved field-intersection theorem then descends its rational presentation.
-/

namespace RHTower

noncomputable section

open scoped TensorProduct

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The two tensor-square pullbacks of a rational Witt vector agree exactly when the vector
descends to the base field. -/
theorem deningerRationalWittFieldEqualizer_iff
    (w : DeningerRationalWittAdditive L) :
    deningerRationalWittAdditiveMap
        (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L)) w =
      deningerRationalWittAdditiveMap
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom w ↔
      ∃ w0 : DeningerRationalWittAdditive K,
        deningerRationalWittAdditiveMap (algebraMap K L) w0 = w := by
  constructor
  · intro hw
    let S : PowerSeries L :=
      deningerRationalWittLocalizationToPowerSeries L (w.1 : _)
    have hloc : deningerRationalWittLocalizationMap
          (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L)) (w.1 : _) =
        deningerRationalWittLocalizationMap
          (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom
          (w.1 : _) := by
      exact congrArg (fun z : DeningerRationalWittAdditive (L ⊗[K] L) =>
        (((z.1 : (DeningerRationalWittLocalization (L ⊗[K] L))ˣ) :
          DeningerRationalWittLocalization (L ⊗[K] L)))) hw
    have hseries : PowerSeries.map
          (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L)) S =
        PowerSeries.map
          (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom S := by
      have hleft := RingHom.congr_fun
        (deningerRationalWittLocalizationToPowerSeries_natural
          (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L)))
        (w.1 : DeningerRationalWittLocalization L)
      have hright := RingHom.congr_fun
        (deningerRationalWittLocalizationToPowerSeries_natural
          (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom)
        (w.1 : DeningerRationalWittLocalization L)
      change deningerRationalWittLocalizationToPowerSeries (L ⊗[K] L)
          (deningerRationalWittLocalizationMap
            (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L))
            (w.1 : _)) =
        PowerSeries.map
          (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L)) S at hleft
      change deningerRationalWittLocalizationToPowerSeries (L ⊗[K] L)
          (deningerRationalWittLocalizationMap
            (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom
            (w.1 : _)) =
        PowerSeries.map
          (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom S at hright
      rw [← hleft, ← hright, hloc]
    have hcoeff : ∀ n : ℕ, ∃ a : K, algebraMap K L a = PowerSeries.coeff n S := by
      intro n
      have hn := congrArg (PowerSeries.coeff n) hseries
      simp only [PowerSeries.coeff_map] at hn
      have hmem : PowerSeries.coeff n S ∈
          Algebra.TensorProduct.includeLeftRingHom.eqLocus
            (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom := hn
      have hmemSet : PowerSeries.coeff n S ∈
          (↑(Algebra.TensorProduct.includeLeftRingHom.eqLocus
            (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom) :
            Set L) := hmem
      rw [Algebra.IsEffective.eqLocus_includeLeft_includeRight
        (Algebra.IsEffective.of_faithfullyFlat K L)] at hmemSet
      exact hmemSet
    choose a ha using hcoeff
    let F : PowerSeries K := PowerSeries.mk a
    have hF : PowerSeries.map (algebraMap K L) F = S := by
      apply PowerSeries.ext
      intro n
      simp [F, ha]
    exact deningerRationalWittFieldIntersection_exists_base K L w F hF
  · rintro ⟨w0, rfl⟩
    have hmaps :
        (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L)).comp
            (algebraMap K L) =
          (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom.comp
            (algebraMap K L) := by
      ext a
      simp
    calc
      deningerRationalWittAdditiveMap
          (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L))
          (deningerRationalWittAdditiveMap (algebraMap K L) w0) =
        deningerRationalWittAdditiveMap
          ((Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L)).comp
            (algebraMap K L)) w0 := by
              rw [deningerRationalWittAdditiveMap_comp]
              rfl
      _ = deningerRationalWittAdditiveMap
          ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom.comp
            (algebraMap K L)) w0 := by rw [hmaps]
      _ = deningerRationalWittAdditiveMap
          (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom
          (deningerRationalWittAdditiveMap (algebraMap K L) w0) := by
            rw [deningerRationalWittAdditiveMap_comp]
            rfl

end

end RHTower
