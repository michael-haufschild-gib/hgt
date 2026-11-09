import GaloisForLFunctions.InfiniteRankWeilTheory.SampledSublevelCover
import GaloisForLFunctions.InfiniteRankWeilTheory.ExponentialCoverDimension

/-!
# Dimension-zero exceptional bases for finite oscillatory sums

Uniform finite sublevel covers imply that bases with infinitely many exponentially small
readings have Hausdorff dimension zero. Frequencies need no Diophantine separation: equal
frequencies are merged, and one nonzero merged coefficient suffices.
-/

open Set Filter

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- Positive bases with infinitely many readings below a fixed exponentially decaying threshold. -/
def exponentiallySmallSamplingBases (f : ℝ → ℂ) (δ : ℝ) : Set ℝ :=
  {ℓ | 0 < ℓ ∧ ∃ᶠ n : ℕ in atTop, ‖f ((n : ℝ) * ℓ)‖ ≤ Real.exp (-δ * ((n : ℝ) * ℓ))}

private theorem frequently_succ_sampling {P : ℝ → Prop} {ℓ : ℝ}
    (h : ∃ᶠ n : ℕ in atTop, P ((n : ℝ) * ℓ)) :
    ∃ᶠ n : ℕ in atTop, P (((n : ℝ) + 1) * ℓ) := by
  apply frequently_atTop.mpr
  intro N
  obtain ⟨n, hn, hP⟩ := frequently_atTop.mp h (N + 1)
  refine ⟨n - 1, by omega, ?_⟩
  have heq : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
  rwa [heq]

/-- A uniform finite power-law sublevel cover excludes exponential cancellation outside a
set of bases of Hausdorff dimension zero. -/
theorem dimH_exponentiallySmallSamplingBases_eq_zero_of_uniform_covers
    {f : ℝ → ℂ} {k : ℕ} {r K p : ℝ} (hr : 0 < r) (hK : 0 < K) (hp : 0 < p)
    (hsub : ∀ x ε : ℝ, 0 < ε → ∃ T : Finset ℝ, T.card ≤ k ∧
      ∀ y ∈ Ioo (x - r) (x + r), ‖f y‖ < ε → ∃ z ∈ T, |y - z| ≤ K * ε ^ p)
    {δ : ℝ} (hδ : 0 < δ) : dimH (exponentiallySmallSamplingBases f δ) = 0 := by
  classical
  let S (j : ℤ) (n : ℕ) : Set ℝ := {ℓ | ℓ ∈ Icc ((2 : ℝ) ^ j) (2 * 2 ^ j) ∧
    ‖f (((n : ℝ) + 1) * ℓ)‖ ≤ Real.exp (-δ * (((n : ℝ) + 1) * ℓ))}
  have hlocal (j : ℤ) : dimH {ℓ : ℝ | ∃ᶠ n : ℕ in atTop, ℓ ∈ S j n} = 0 := by
    obtain ⟨M, R, b, hM, hR, hb, hcov⟩ := exists_exponential_sampled_sublevel_covers
      hr hK hp hsub (U := 2 * (2 : ℝ) ^ j) (by positivity : 0 < (2 : ℝ) ^ j) hδ
    choose G hGc hGcover using hcov
    exact dimH_frequently_eq_zero_of_exponential_covers (S j) G hM hR hb hGc
      (fun n ℓ hℓ => hGcover n ℓ hℓ.1 hℓ.2)
  have hcover : exponentiallySmallSamplingBases f δ ⊆
      ⋃ j : ℤ, {ℓ : ℝ | ∃ᶠ n : ℕ in atTop, ℓ ∈ S j n} := by
    rintro ℓ ⟨hℓ, hsmall⟩
    obtain ⟨j, hj1, hj2⟩ := exists_mem_Ico_zpow hℓ (show (1 : ℝ) < 2 by norm_num)
    rw [zpow_add_one₀ (by norm_num)] at hj2
    refine mem_iUnion.mpr ⟨j, ?_⟩
    have hf : ∃ᶠ n : ℕ in atTop,
        ‖f (((n : ℝ) + 1) * ℓ)‖ ≤ Real.exp (-δ * (((n : ℝ) + 1) * ℓ)) :=
      frequently_succ_sampling (ℓ := ℓ) (P := fun t => ‖f t‖ ≤ Real.exp (-δ * t)) hsmall
    exact hf.mono fun n hn => ⟨⟨hj1, by linarith only [hj2]⟩, hn⟩
  apply le_antisymm ((dimH_mono hcover).trans ?_) (show (0 : ENNReal) ≤ _ from zero_le)
  rw [dimH_iUnion]
  simp only [hlocal, iSup_const, le_refl]

/-- A nonzero finite sum of distinct real frequencies has a dimension-zero exceptional base
set at every positive exponential decay rate. -/
theorem dimH_oscillatory_exp_small_eq_zero {k : ℕ} (γ : Fin k → ℝ)
    (hγ : Function.Injective γ) (c : Fin k → ℂ) (hc : c ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    dimH (exponentiallySmallSamplingBases (oscillatoryJet γ c 0) δ) = 0 := by
  obtain ⟨r, K, hr, hK, hsub⟩ := exists_uniform_oscillatory_sublevel_cover γ hγ c hc
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    exact hc (funext fun i => Fin.elim0 i)
  exact dimH_exponentiallySmallSamplingBases_eq_zero_of_uniform_covers
    hr hK (inv_pos.mpr (by exact_mod_cast hk)) hsub hδ

/-- Merging repeated frequencies preserves the dimension-zero conclusion whenever one merged
coefficient remains nonzero. -/
theorem dimH_finset_oscillatory_exp_small_eq_zero {ι : Type*} (F : Finset ι)
    (γ : ι → ℝ) (c : ι → ℂ)
    (hvis : ∃ j ∈ F, (∑ i ∈ F with γ i = γ j, c i) ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    dimH (exponentiallySmallSamplingBases (TrigSum.trigSum F c γ) δ) = 0 := by
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
  have heq : TrigSum.trigSum F c γ =
      oscillatoryJet (fun j => (e j : ℝ)) (fun j => d (e j)) 0 := by
    funext t
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
  rw [heq]
  exact dimH_oscillatory_exp_small_eq_zero _ hγ _ hd hδ

/-- One dimension-zero set contains exceptional bases for every positive decay rate. -/
theorem dimH_all_finset_oscillatory_exp_small_eq_zero {ι : Type*} (F : Finset ι)
    (γ : ι → ℝ) (c : ι → ℂ)
    (hvis : ∃ j ∈ F, (∑ i ∈ F with γ i = γ j, c i) ≠ 0) :
    dimH {ℓ : ℝ | ∃ δ : ℝ, 0 < δ ∧
      ℓ ∈ exponentiallySmallSamplingBases (TrigSum.trigSum F c γ) δ} = 0 := by
  have hsub : {ℓ : ℝ | ∃ δ : ℝ, 0 < δ ∧
      ℓ ∈ exponentiallySmallSamplingBases (TrigSum.trigSum F c γ) δ} ⊆
      ⋃ m : ℕ, exponentiallySmallSamplingBases (TrigSum.trigSum F c γ) (1 / ((m : ℝ) + 1)) := by
    rintro ℓ ⟨δ, hδ, hℓ, hsmall⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine mem_iUnion.mpr ⟨m, hℓ, hsmall.mono fun n hn => hn.trans ?_⟩
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hm.le) (mul_nonneg (Nat.cast_nonneg _) hℓ.le)
  apply le_antisymm ((dimH_mono hsub).trans ?_) (show (0 : ENNReal) ≤ _ from zero_le)
  rw [dimH_iUnion]
  have hz (m : ℕ) := dimH_finset_oscillatory_exp_small_eq_zero F γ c hvis
    (by positivity : 0 < 1 / ((m : ℝ) + 1))
  simp only [hz, iSup_const, le_refl]

#print axioms dimH_finset_oscillatory_exp_small_eq_zero
#print axioms dimH_all_finset_oscillatory_exp_small_eq_zero

end GaloisForLFunctions.InfiniteRankWeilTheory
