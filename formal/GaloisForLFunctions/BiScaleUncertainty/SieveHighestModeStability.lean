import GaloisForLFunctions.BiScaleUncertainty.SieveHighestDyadicCoordinate
import GaloisForLFunctions.BiScaleUncertainty.SieveCubicAnchorEstimate
import GaloisForLFunctions.BiScaleUncertainty.SieveCoordinateSupNorm
import GaloisForLFunctions.BiScaleUncertainty.SieveCanonicalTranslation
import GaloisForLFunctions.BiScaleUncertainty.SieveRawMomentPerturbation

/-! Sharp cube-root physical-translation stability on the highest-mode stratum. Lower coordinates may vanish or be unbounded. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor
open GaloisForLFunctions.BezoutValuationIncidence ValuationPhase
set_option autoImplicit false

/-- One retained top mode gives cubic stability for every other coordinate, including zero support. -/
theorem exists_translate_error (N : ℕ) (hN : 2 ≤ N) (c e : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hc : 1 ≤ |selbergMultiplesCoord N c (topOrder N)|)
    (he : 1 ≤ |selbergMultiplesCoord N e (topOrder N)|)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^3)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^3) :
    ∃ t : ℕ, ∀ n : ℕ, |sieveSeq N e n-sieveSeq N c (n+t)| ≤
      2*(∑ q ∈ Icc 1 N, (q.totient : ℝ))*δ := by
  have hp := topOrder_mem N hN
  have ha := coordinate_sixth_error N c e (δ^3) h6 (topOrder N) hp
  have hδ3 : δ^3 ≤ 2*δ := by
    have h₁ := mul_nonneg hδ (sub_nonneg.mpr hδ1)
    have h₂ := mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδ1)
    nlinarith only [h₁, h₂, hδ]
  have hlow (q : ℕ) (hq : q ∈ Icc 1 N) (hne : q ≠ topOrder N) :
      |selbergMultiplesCoord N e q-selbergMultiplesCoord N c q| ≤ 2*δ := by
    have hdepth : q.factorization 2 < (topOrder N).factorization 2 := by
      rw [topOrder_depth]
      exact depth_lt_top hq hne
    have hh := lower_error (selbergMultiplesCoord N c q) (selbergMultiplesCoord N e q)
      (selbergMultiplesCoord N c (topOrder N)) (selbergMultiplesCoord N e (topOrder N))
      δ hc he hδ hδ1 ha (coordinate_sixth_error N c e (δ^3) h6 q hq)
      (lower_product_error N c e (δ^3) h5 hq hp hdepth)
    simpa only [abs_sub_comm] using hh
  rcases upper_error (selbergMultiplesCoord N c (topOrder N))
    (selbergMultiplesCoord N e (topOrder N)) (δ^3) hc ha with hs | hs
  · have hcoord (q : ℕ) (hq : q ∈ Icc 1 N) :
        |selbergMultiplesCoord N e q-selbergMultiplesCoord N c q| ≤ 2*δ := by
      by_cases hqtop : q = topOrder N
      · subst q
        exact hs.trans hδ3
      · exact hlow q hq hqtop
    refine ⟨0, fun n => ?_⟩
    simpa only [Nat.add_zero, mul_comm, mul_left_comm, mul_assoc] using
      sieveSeq_error_le_totient_sum N e c (2*δ) hcoord n
  · have hc0 : selbergMultiplesCoord N c (topOrder N) ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hc
      linarith
    have hcoord (q : ℕ) (hq : q ∈ Icc 1 N) :
        |selbergMultiplesCoord N e q-selbergMultiplesCoord N (companion N c) q| ≤ 2*δ := by
      rw [coordinate_companion_top N hN c hc0 q hq]
      by_cases hqtop : q = topOrder N
      · rw [if_pos hqtop, hqtop, sub_neg_eq_add]
        exact hs.trans hδ3
      · rw [if_neg hqtop]
        exact hlow q hq hqtop
    refine ⟨canonicalShift N c, fun n => ?_⟩
    have hh := sieveSeq_error_le_totient_sum N e (companion N c) (2*δ) hcoord n
    rw [sieveSeq_companion] at hh
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hh

/-- Explicit cube-root modulus in the original fifth/sixth raw-error scale. -/
theorem exists_translate_error_rpow (N : ℕ) (hN : 2 ≤ N) (c e : ℕ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hc : 1 ≤ |selbergMultiplesCoord N c (topOrder N)|)
    (he : 1 ≤ |selbergMultiplesCoord N e (topOrder N)|)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε) :
    ∃ t : ℕ, ∀ n : ℕ, |sieveSeq N e n-sieveSeq N c (n+t)| ≤
      2*(∑ q ∈ Icc 1 N, (q.totient : ℝ))*ε^(1/3 : ℝ) := by
  let δ : ℝ := ε^(1/3 : ℝ)
  have hδ : 0 ≤ δ := Real.rpow_nonneg hε _
  have hδ1 : δ ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow hε hε1 (by norm_num : (0 : ℝ) ≤ 1/3)
  have hd3 : δ^3 = ε := by
    dsimp [δ]
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hε]
    norm_num
  exact exists_translate_error N hN c e δ hδ hδ1 hc he
    (fun v => by rw [hd3]; exact h5 v) (fun v => by rw [hd3]; exact h6 v)

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor
