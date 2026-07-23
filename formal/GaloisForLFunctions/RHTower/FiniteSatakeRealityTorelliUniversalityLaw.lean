import GaloisForLFunctions.HTGeometry.PowerSumTorelli
import GaloisForLFunctions.RHTower.SatakeReality

/-!
# Finite Satake reality--Torelli universality

Conjugation closure makes every secular power sum real.  Conversely, power-sum Torelli shows that
for an `n`-point complex spectrum the first `n` real secular moments already reconstruct the
conjugate multiset and hence force conjugation closure.  Thus finite self-duality is exactly a
finite moment condition, without labelled conjugate pairs.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions

noncomputable section

/-- **Sharp finite Satake reality criterion.**  An enumerated `n`-point complex spectrum is closed
under conjugation exactly when its secular power sums of orders at most `n` are real. -/
theorem finiteSatake_conjugationClosed_iff_firstMoments_real {n : ℕ} (f : Fin n → ℂ) :
    (univ.val.map f).map (starRingEnd ℂ) = univ.val.map f ↔
      ∀ k ≤ n,
        (starRingEnd ℂ) ((univ.val.map (fun i => f i ^ k)).sum) =
          (univ.val.map (fun i => f i ^ k)).sum := by
  constructor
  · intro hclosed k _
    simpa only [Multiset.map_map, Function.comp_apply] using
      selfDual_moment_real (univ.val.map f) hclosed k
  · intro hmoment
    let g : Fin n → ℂ := fun i => (starRingEnd ℂ) (f i)
    have hconjPower (k : ℕ) :
        (univ.val.map (fun i => g i ^ k)).sum =
          (starRingEnd ℂ) ((univ.val.map (fun i => f i ^ k)).sum) := by
      rw [map_multiset_sum, Multiset.map_map]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro i _
      simp only [g, Function.comp_apply, map_pow]
    have hp : ∀ k, k ≤ n →
        (univ.val.map (fun i => f i ^ k)).sum =
          (univ.val.map (fun i => g i ^ k)).sum := by
      intro k hk
      exact (hmoment k hk).symm.trans (hconjPower k).symm
    have hfg : univ.val.map f = univ.val.map g :=
      powerSum_torelli_finite f g hp
    rw [Multiset.map_map]
    simpa only [g, Function.comp_apply] using hfg.symm

/-- Equivalently, failure of conjugation closure is detected by one nonreal secular moment whose
order is no larger than the number of spectral points. -/
theorem exists_nonreal_firstMoment_of_not_conjugationClosed {n : ℕ} (f : Fin n → ℂ)
    (h : (univ.val.map f).map (starRingEnd ℂ) ≠ univ.val.map f) :
    ∃ k, k ≤ n ∧
      (starRingEnd ℂ) ((univ.val.map (fun i => f i ^ k)).sum) ≠
        (univ.val.map (fun i => f i ^ k)).sum := by
  by_contra hnone
  apply h
  rw [finiteSatake_conjugationClosed_iff_firstMoments_real]
  intro k hk
  by_contra hnonreal
  exact hnone ⟨k, hk, hnonreal⟩

end

end GaloisForLFunctions
