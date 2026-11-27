import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.PowerCongruenceRelativeIndex
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IntegerIdealNormProduct
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionPowerIndex
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ArchimedeanPowerIndex

/-! The norm factor in the finite power indices cancels the weights from
the archimedean indices, leaving one factor of n² per place. -/

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.Reciprocity.IdeleGroup

variable {K : Type} [Field K] [NumberField K] (n : ℕ)
  [NeZero n] [HasEnoughRootsOfUnity K n]

theorem relIndex_powerCongruence_eq_pow (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerCongruence (K := K) n S).relIndex (supportedIdeles (K := K) (S : Set _)) =
      n ^ (2 * (Fintype.card (InfinitePlace K) + S.card)) := by
  let A (w : InfinitePlace K) := (powMonoidHom n : (w.Completion)ˣ →* _).range.index
  have hA (w : InfinitePlace K) : A w * n ^ w.mult = n ^ 2 := by
    have hnorm : ‖(n : w.Completion)‖ = n := by
      rw [← map_natCast (algebraMap K w.Completion) n]
      change ‖((WithAbs.equiv w.1).symm (n : K) : w.Completion)‖ = n
      rw [InfinitePlace.Completion.norm_coe]
      exact (congrArg (fun x : K => w x) ((WithAbs.equiv w.1).apply_symm_apply (n : K))).trans
        (w.map_natCast n)
    have h := index_power_infiniteCompletion_mul_norm (n := n) w
    rw [hnorm] at h
    exact_mod_cast h
  have harch : (∏ w, A w) * n ^ Module.finrank ℚ K = (n ^ 2) ^ Fintype.card (InfinitePlace K) := by
    rw [← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    simp only [hA, Finset.prod_const, Finset.card_univ]
  let B (v : HeightOneSpectrum (𝓞 K)) := (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index
  have hB : (∏ v : S, B v.val) = ∏ v ∈ S, B v := Finset.prod_coe_sort S B
  rw [relIndex_powerCongruence]
  change (∏ v : S, B v.val) * (∏ w, A w) = _
  rw [hB]
  dsimp only [B]
  simp_rw [index_power_adicCompletion (n := n), Finset.prod_mul_distrib, Finset.prod_const]
  rw [prod_ideal_norm_pow_multiplicity_natCast (NeZero.ne n) S hS]
  rw [mul_assoc, mul_comm (n ^ Module.finrank ℚ K), harch, ← pow_add, ← pow_mul, add_comm S.card]

end GlobalTheory.Reciprocity.IdeleGroup
