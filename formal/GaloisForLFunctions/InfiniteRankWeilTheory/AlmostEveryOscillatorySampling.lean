import GaloisForLFunctions.InfiniteRankWeilTheory.OscillatoryExceptionalTimes
import GaloisForLFunctions.RHTower.WeilLagAlmostEverySpacingBlind

/-!
# Almost every sampling base avoids exponentially small finite sums

Finite measure of exponentially small values combines with the progression Borel–Cantelli
theorem. A countable family of decay rates suffices to obtain every positive rate simultaneously
outside one null set of sampling bases.
-/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The finite-measure progression theorem on the whole positive half-line of bases. -/
theorem ae_eventually_mult_notMem_positive {B : Set ℝ} (hB : volume B < ⊤) :
    ∀ᵐ ℓ ∂volume, 0 < ℓ → ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) * ℓ ∉ B := by
  rw [ae_iff]
  have hcover : {ℓ : ℝ | ¬ (0 < ℓ → ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) * ℓ ∉ B)} ⊆
      ⋃ j : ℤ, {ℓ : ℝ | ¬ (∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) * ℓ ∉ B)} ∩
        Icc ((2 : ℝ) ^ j) (2 * 2 ^ j) := by
    intro ℓ hℓ
    simp only [mem_setOf_eq, Classical.not_imp] at hℓ
    obtain ⟨j, hj1, hj2⟩ := exists_mem_Ico_zpow hℓ.1 (show (1 : ℝ) < 2 by norm_num)
    refine mem_iUnion.mpr ⟨j, hℓ.2, hj1, ?_⟩
    rw [zpow_add_one₀ (by norm_num)] at hj2
    linarith only [hj2]
  refine measure_mono_null hcover (measure_iUnion_null fun j => ?_)
  have h := RHTower.AlmostEverySpacing.ae_eventually_mult_notMem hB
    (L := (2 : ℝ) ^ j) (by positivity)
  rw [ae_iff, Measure.restrict_apply' measurableSet_Icc] at h
  exact h

/-- Almost every positive base eventually detects a finite nonzero oscillatory sum above every
exponentially decaying threshold. The exceptional null set is independent of the decay rate. -/
theorem ae_eventually_oscillatory_exp_lower {k : ℕ} (γ : Fin k → ℝ)
    (hγ : Function.Injective γ) (c : Fin k → ℂ) (hc : c ≠ 0) :
    ∀ᵐ ℓ ∂volume, 0 < ℓ → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop,
        Real.exp (-δ * ((n : ℝ) * ℓ)) < ‖oscillatoryJet γ c 0 ((n : ℝ) * ℓ)‖ := by
  have hall : ∀ᵐ ℓ ∂volume, ∀ m : ℕ, 0 < ℓ → ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) * ℓ ∉ {t : ℝ | 0 ≤ t ∧
        ‖oscillatoryJet γ c 0 t‖ ≤ Real.exp (-(1 / ((m : ℝ) + 1)) * t)} := by
    apply ae_all_iff.mpr
    intro m
    exact ae_eventually_mult_notMem_positive
      (volume_oscillatory_exp_small_lt_top γ hγ c hc (by positivity))
  filter_upwards [hall] with ℓ hℓ
  intro hℓpos δ hδ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hℓ m hℓpos)
  refine eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
  have hbad := hN (n - 1) (by omega)
  have hncast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
  rw [hncast] at hbad
  have ht : 0 ≤ (n : ℝ) * ℓ := mul_nonneg (Nat.cast_nonneg _) hℓpos.le
  have hlow : Real.exp (-(1 / ((m : ℝ) + 1)) * ((n : ℝ) * ℓ)) <
      ‖oscillatoryJet γ c 0 ((n : ℝ) * ℓ)‖ :=
    lt_of_not_ge (fun h => hbad ⟨ht, h⟩)
  refine lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) hlow
  exact mul_le_mul_of_nonneg_right (neg_le_neg hm.le) ht

#print axioms ae_eventually_oscillatory_exp_lower

/-- The same metric detection law with repeated frequencies merged. Only one merged
coefficient needs to be nonzero. -/
theorem ae_eventually_finset_oscillatory_exp_lower {ι : Type*} (F : Finset ι)
    (γ : ι → ℝ) (c : ι → ℂ)
    (hvis : ∃ j ∈ F, (∑ i ∈ F with γ i = γ j, c i) ≠ 0) :
    ∀ᵐ ℓ ∂volume, 0 < ℓ → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      Real.exp (-δ * ((n : ℝ) * ℓ)) < ‖TrigSum.trigSum F c γ ((n : ℝ) * ℓ)‖ := by
  classical
  let P := F.image γ
  let e : Fin P.card ≃ P := P.equivFin.symm
  let d : ℝ → ℂ := fun w => ∑ i ∈ F with γ i = w, c i
  have hγ : Function.Injective (fun j : Fin P.card => (e j : ℝ)) := by
    intro i j h
    exact e.injective (Subtype.ext h)
  have hd : (fun j : Fin P.card => d (e j)) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hvis
    intro h
    have h0 := congrFun h (e.symm ⟨γ j, Finset.mem_image_of_mem γ hj⟩)
    simp only [Equiv.apply_symm_apply, Pi.zero_apply] at h0
    exact hne h0
  have heq (t : ℝ) : TrigSum.trigSum F c γ t =
      oscillatoryJet (fun j => (e j : ℝ)) (fun j => d (e j)) 0 t := by
    have hmerge : TrigSum.trigSum F c γ t =
        ∑ w ∈ P, d w * Complex.exp (Complex.I * (w * t)) := by
      unfold TrigSum.trigSum
      rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := P) (g := γ)
        (fun i hi => Finset.mem_image_of_mem γ hi)]
      refine Finset.sum_congr rfl fun w _ => ?_
      dsimp only [d]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    rw [hmerge, ← Finset.sum_coe_sort P, ← Equiv.sum_comp e]
    simp only [oscillatoryJet, TrigSum.trigSum, pow_zero, mul_one]
  simpa only [← heq] using ae_eventually_oscillatory_exp_lower
    (fun j => (e j : ℝ)) hγ (fun j => d (e j)) hd

#print axioms ae_eventually_finset_oscillatory_exp_lower

end GaloisForLFunctions.InfiniteRankWeilTheory
