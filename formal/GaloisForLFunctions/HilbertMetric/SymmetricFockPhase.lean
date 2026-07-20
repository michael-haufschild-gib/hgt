import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow
import GaloisForLFunctions.HilbertMetric.TransverseDegreePhase

/-!
# Symmetric-Fock transverse phase law

This module combines the sharp lowering-shadow charge law with the transverse channel-square
law.  For an annihilation-closed graded family with top dimension `k`, top degree `M`, and `r`
transverse singular channels, it proves a rank-sensitive lower bound for the mean-minus-variance
margin.  Eliminating `r ≤ k` gives the universal phase threshold

`(e + 1) * (M - 4) ≤ 4 * (M - 1)`,

or equivalently `(e - 3) * M ≤ 4 * e`.  In particular, every such completion on at most three
modes is sub-Poisson at every phase.  The full symmetric top at the balancing phase crosses the
bound exactly when the strict reverse inequality holds.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

/-- Mean-minus-variance margin of a graded Fock lowering skeleton with one single-top transverse
completion.  `J` indexes the nonzero singular channels; unmatched top directions remain at degree
`M` and contribute the deterministic charge `(k - card J) * M`. -/
def gradedFockTransverseFanoMargin
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (p : J → ℝ) : ℝ :=
  transverseChannelFanoMargin
    (gradedFockLoweringCharge M U +
      ((Module.finrank ℝ (U M) : ℝ) - (Fintype.card J : ℝ)) * (M : ℝ))
    (M : ℝ) p

/-- **Rank-sensitive Fock phase law.**  The charge bound and every transverse channel square
survive simultaneously; no full-rank assumption is made. -/
theorem gradedFockTransverseFanoMargin_rank_bound
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n)
    (p : J → ℝ) :
    (M : ℝ) * ((M : ℝ) - 1) * (Module.finrank ℝ (U M) : ℝ) +
        ((Fintype.card I + 1 : ℕ) : ℝ) *
          (((Module.finrank ℝ (U M) : ℝ) - (Fintype.card J : ℝ)) * (M : ℝ) -
            (Fintype.card J : ℝ) * ((M : ℝ) * ((M : ℝ) - 4) / 4)) ≤
      ((Fintype.card I + 1 : ℕ) : ℝ) *
        gradedFockTransverseFanoMargin M U p := by
  have hcharge := gradedFockLoweringCharge_lower_bound M U hshadow
  have hmargin := transverseChannelFanoMargin_lower_bound
    (ι := J)
    (gradedFockLoweringCharge M U +
      ((Module.finrank ℝ (U M) : ℝ) - (Fintype.card J : ℝ)) * (M : ℝ))
    (M : ℝ) p
  unfold gradedFockTransverseFanoMargin
  have hc : 0 ≤ (((Fintype.card I + 1 : ℕ) : ℝ)) := by positivity
  nlinarith

/-- **Universal single-top Fock phase bound.**  Among all transverse ranks at most `k`, full rank
minimizes the universal margin; the discarded rank-sensitive remainder is
`(e + 1) * (k - r) * M^2 / 4`. -/
theorem gradedFockTransverseFanoMargin_universal_bound
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n)
    (p : J → ℝ)
    (hrank : Fintype.card J ≤ Module.finrank ℝ (U M)) :
    (Module.finrank ℝ (U M) : ℝ) *
        ((M : ℝ) * ((M : ℝ) - 1) -
          ((Fintype.card I + 1 : ℕ) : ℝ) *
            ((M : ℝ) * ((M : ℝ) - 4) / 4)) ≤
      ((Fintype.card I + 1 : ℕ) : ℝ) *
        gradedFockTransverseFanoMargin M U p := by
  have hrank' : (Fintype.card J : ℝ) ≤ (Module.finrank ℝ (U M) : ℝ) := by
    exact_mod_cast hrank
  have hsq : 0 ≤ ((M : ℝ) ^ 2) := sq_nonneg _
  have hmissing : 0 ≤
      ((Module.finrank ℝ (U M) : ℝ) - (Fintype.card J : ℝ)) * (M : ℝ) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hrank') hsq
  have hc : 0 ≤ (((Fintype.card I + 1 : ℕ) : ℝ)) := by positivity
  have h := gradedFockTransverseFanoMargin_rank_bound M U hshadow p
  nlinarith

/-- **Ambient-completion rank budget.**  A negative margin forces the transverse rank to occupy
the explicit fraction `4 * k * (M + e) / ((e + 1) * M)` of the top space. -/
theorem gradedFockTransverse_negative_forces_rank_budget
    (M : ℕ) (hM : 0 < M)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n)
    (p : J → ℝ)
    (hneg : gradedFockTransverseFanoMargin M U p < 0) :
    4 * (Module.finrank ℝ (U M) : ℝ) *
        ((M : ℝ) + (Fintype.card I : ℝ)) <
      ((Fintype.card I + 1 : ℕ) : ℝ) * (Fintype.card J : ℝ) * (M : ℝ) := by
  have h := gradedFockTransverseFanoMargin_rank_bound M U hshadow p
  have hc : 0 < (((Fintype.card I + 1 : ℕ) : ℝ)) := by positivity
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hscaled :
      ((Fintype.card I + 1 : ℕ) : ℝ) *
          gradedFockTransverseFanoMargin M U p < 0 :=
    mul_neg_of_pos_of_neg hc hneg
  have hbase :
      (M : ℝ) * ((M : ℝ) - 1) * (Module.finrank ℝ (U M) : ℝ) +
          ((Fintype.card I + 1 : ℕ) : ℝ) *
            (((Module.finrank ℝ (U M) : ℝ) - (Fintype.card J : ℝ)) * (M : ℝ) -
              (Fintype.card J : ℝ) * ((M : ℝ) * ((M : ℝ) - 4) / 4)) < 0 :=
    lt_of_le_of_lt h hscaled
  push_cast at hbase ⊢
  have hidentity :
      4 * ((M : ℝ) * ((M : ℝ) - 1) * (Module.finrank ℝ (U M) : ℝ) +
          ((Fintype.card I : ℝ) + 1) *
            (((Module.finrank ℝ (U M) : ℝ) - (Fintype.card J : ℝ)) * (M : ℝ) -
              (Fintype.card J : ℝ) * ((M : ℝ) * ((M : ℝ) - 4) / 4))) =
        (M : ℝ) *
          (4 * (Module.finrank ℝ (U M) : ℝ) *
              ((M : ℝ) + (Fintype.card I : ℝ)) -
            ((Fintype.card I : ℝ) + 1) * (Fintype.card J : ℝ) * (M : ℝ)) := by
    ring
  have hprod : (M : ℝ) *
      (4 * (Module.finrank ℝ (U M) : ℝ) *
          ((M : ℝ) + (Fintype.card I : ℝ)) -
        ((Fintype.card I : ℝ) + 1) * (Fintype.card J : ℝ) * (M : ℝ)) < 0 := by
    rw [← hidentity]
    linarith
  rcases (mul_neg_iff.mp hprod) with hcase | hcase
  · linarith [hcase.2]
  · linarith [hcase.1]

/-- A negative phase with actual transverse rank at most the top dimension forces the strict
mode-degree threshold `4e < (e - 3)M`. -/
theorem gradedFockTransverse_negative_forces_phase
    (M : ℕ) (hM : 0 < M)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n)
    (p : J → ℝ)
    (hrank : Fintype.card J ≤ Module.finrank ℝ (U M))
    (htop : 0 < Module.finrank ℝ (U M))
    (hneg : gradedFockTransverseFanoMargin M U p < 0) :
    4 * (Fintype.card I : ℝ) <
      ((Fintype.card I : ℝ) - 3) * (M : ℝ) := by
  have hbudget := gradedFockTransverse_negative_forces_rank_budget M hM U hshadow p hneg
  have hrank' : (Fintype.card J : ℝ) ≤ (Module.finrank ℝ (U M) : ℝ) := by
    exact_mod_cast hrank
  have htop' : 0 < (Module.finrank ℝ (U M) : ℝ) := by exact_mod_cast htop
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hc : 0 < (((Fintype.card I + 1 : ℕ) : ℝ)) := by positivity
  have hcompare :
      ((Fintype.card I + 1 : ℕ) : ℝ) * (Fintype.card J : ℝ) * (M : ℝ) ≤
        ((Fintype.card I + 1 : ℕ) : ℝ) *
          (Module.finrank ℝ (U M) : ℝ) * (M : ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrank' (le_of_lt hc)) (le_of_lt hM')
  have hcombined := lt_of_lt_of_le hbudget hcompare
  push_cast at hcombined ⊢
  have hfactored :
      (Module.finrank ℝ (U M) : ℝ) *
          (4 * ((M : ℝ) + (Fintype.card I : ℝ))) <
        (Module.finrank ℝ (U M) : ℝ) *
          (((Fintype.card I : ℝ) + 1) * (M : ℝ)) := by
    nlinarith
  have hcancel := lt_of_mul_lt_mul_left hfactored (le_of_lt htop')
  nlinarith

/-- The universal phase inequality forces a nonnegative margin for every channel parameter. -/
theorem gradedFockTransverseFanoMargin_nonnegative_of_phase
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n)
    (p : J → ℝ)
    (hrank : Fintype.card J ≤ Module.finrank ℝ (U M))
    (hphase : ((Fintype.card I + 1 : ℕ) : ℝ) * ((M : ℝ) - 4) ≤
      4 * ((M : ℝ) - 1)) :
    0 ≤ gradedFockTransverseFanoMargin M U p := by
  have h := gradedFockTransverseFanoMargin_universal_bound M U hshadow p hrank
  have hgap : 0 ≤ 4 * ((M : ℝ) - 1) -
      ((Fintype.card I + 1 : ℕ) : ℝ) * ((M : ℝ) - 4) := by linarith
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hbracket : 0 ≤ (M : ℝ) * ((M : ℝ) - 1) -
      ((Fintype.card I + 1 : ℕ) : ℝ) *
        ((M : ℝ) * ((M : ℝ) - 4) / 4) := by
    have hnonneg := mul_nonneg hM hgap
    nlinarith
  have hk : 0 ≤ (Module.finrank ℝ (U M) : ℝ) := by positivity
  have hlower := mul_nonneg hk hbracket
  have hc : 0 < (((Fintype.card I + 1 : ℕ) : ℝ)) := by positivity
  nlinarith

/-- **Three-mode stability law.**  Every annihilation-closed single-top transverse completion on
at most three modes has nonnegative mean-minus-variance margin at every phase. -/
theorem threeMode_gradedFockTransverseFanoMargin_nonnegative
    (hI : Fintype.card I ≤ 3)
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n)
    (p : J → ℝ)
    (hrank : Fintype.card J ≤ Module.finrank ℝ (U M)) :
    0 ≤ gradedFockTransverseFanoMargin M U p := by
  apply gradedFockTransverseFanoMargin_nonnegative_of_phase M U hshadow p hrank
  have he : (Fintype.card I : ℝ) ≤ 3 := by exact_mod_cast hI
  have hM : 0 ≤ (M : ℝ) := by positivity
  have hprod : ((Fintype.card I : ℝ) - 3) * (M : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr he) hM
  push_cast
  nlinarith

/-- The full symmetric top crosses the universal phase bound exactly at the strict reverse
inequality. -/
theorem fullTopTransverse_phase_at_balance_lt_zero_iff
    (e M : ℝ) (he : -1 < e) (hM : 0 < M) (hM1 : M ≠ 1) :
    transverseDegreeFanoMargin (fullTopLoweringChargeDensity e M) 1 M
        ((M - 2) / (2 * (M - 1))) < 0 ↔
      4 * (M - 1) < (e + 1) * (M - 4) := by
  rw [fullTopTransverse_phase_at_balance e M hM1]
  have hc : 0 < e + 1 := by linarith
  have hfour : (0 : ℝ) < 4 := by norm_num
  have heq : M * (M - 1) / (e + 1) - M * (M - 4) / 4 =
      M * ((M - 1) / (e + 1) - (M - 4) / 4) := by ring
  rw [heq]
  constructor
  · intro h
    have hf : (M - 1) / (e + 1) - (M - 4) / 4 < 0 := by nlinarith
    have hd : (M - 1) / (e + 1) < (M - 4) / 4 := by linarith
    have hcross := (div_lt_div_iff₀ hc hfour).mp hd
    nlinarith
  · intro h
    have hd : (M - 1) / (e + 1) < (M - 4) / 4 := by
      apply (div_lt_div_iff₀ hc hfour).mpr
      nlinarith
    have hf : (M - 1) / (e + 1) - (M - 4) / 4 < 0 := by linarith
    exact mul_neg_of_pos_of_neg hM hf

/-- Equivalent affine form of the exact single-top phase threshold. -/
theorem singleTopFock_phase_threshold_rewrite (e M : ℝ) :
    4 * (M - 1) < (e + 1) * (M - 4) ↔ 4 * e < (e - 3) * M := by
  constructor <;> intro h <;> nlinarith

end

end GaloisForLFunctions.HilbertMetric
