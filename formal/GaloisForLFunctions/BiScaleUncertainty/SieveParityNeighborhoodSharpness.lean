import GaloisForLFunctions.BiScaleUncertainty.SieveParityNeighborhoodStability

/-! Optimal local exponents from explicit all-cutoff perturbation families. -/

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false

private theorem small_power_contradiction (β K M : ℝ) (hβ : 1 < β) (hM : 0 < M)
    (h : ∀ t : ℝ, 0 < t → t ≤ M → t ≤ K*t^β) : False := by
  have hg : 0 < β-1 := by linarith
  let x : ℝ := (|K|+1)/(β-1)+M⁻¹
  let t : ℝ := Real.exp (-x)
  have ht : 0 < t := Real.exp_pos _
  have htM : t ≤ M := by
    have hMx : M⁻¹ ≤ x := by
      have hb : 0 ≤ (|K|+1)/(β-1) := by positivity
      dsimp [x]
      linarith
    have hMe : M⁻¹ ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hmul := mul_le_mul_of_nonneg_left hMe hM.le
    rw [mul_inv_cancel₀ hM.ne'] at hmul
    change Real.exp (-x) ≤ M
    rw [Real.exp_neg, ← one_div]
    exact (div_le_iff₀ (Real.exp_pos x)).mpr hmul
  have hp : 0 < t^β := by positivity
  have hb : t^(1-β) ≤ K := by
    rw [Real.rpow_sub ht, Real.rpow_one]
    exact (div_le_iff₀ hp).mpr (h t ht htM)
  have he : t^(1-β) = Real.exp (|K|+1+M⁻¹*(β-1)) := by
    rw [Real.rpow_def_of_pos ht]
    change Real.exp (Real.log (Real.exp (-x))*(1-β)) = _
    rw [Real.log_exp]
    congr 1
    dsimp [x]
    field_simp [hg.ne', hM.ne']
    ring
  rw [he] at hb
  have hnonneg : 0 ≤ M⁻¹*(β-1) := mul_nonneg (inv_nonneg.mpr hM.le) hg.le
  linarith [Real.add_one_le_exp (|K|+1+M⁻¹*(β-1)), le_abs_self K]

/-- Polynomial raw errors and linear orbit separation bound every local inverse exponent. -/
theorem not_holder_of_witnesses (N d : ℕ) (hd : 0 < d) (b : ℕ → ℝ)
    (f g : ℝ → ℕ → ℝ) (L W k α : ℝ) (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hα : 1/(d : ℝ) < α)
    (hnear : ∀ t, 0 ≤ t → t ≤ 1 → ∀ n,
      |sieveSeq N (f t) n-sieveSeq N b n| ≤ W*t ∧
      |sieveSeq N (g t) n-sieveSeq N b n| ≤ W*t)
    (hraw : ∀ t, 0 ≤ t → t ≤ 1 →
      (∀ v : Fin 5 → ℕ, |translatedMoment N (f t) v-translatedMoment N (g t) v| ≤ L*t^d) ∧
      (∀ v : Fin 6 → ℕ, |translatedMoment N (f t) v-translatedMoment N (g t) v| ≤ L*t^d))
    (hsep : ∀ t, 0 ≤ t → t ≤ 1 → ∀ h D,
      (∀ n, |sieveSeq N (g t) n-sieveSeq N (f t) (n+h)| ≤ D) → 2*t ≤ k*D) :
    ¬LocalPairwiseHolder N b α := by
  rintro ⟨R, hR, C, _hC, hlocal⟩
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hg : 1 < (d : ℝ)*α := by
    have hh := (div_lt_iff₀ hdR).mp hα
    nlinarith only [hh]
  let M : ℝ := min (R/(W+1)) 1
  have hM : 0 < M := by dsimp [M]; positivity
  apply small_power_contradiction ((d : ℝ)*α) (k*C*L^α/2) M hg hM
  intro t ht htM
  have ht1 : t ≤ 1 := htM.trans (min_le_right _ _)
  have htR : W*t ≤ R := by
    have hh := htM.trans (min_le_left _ _)
    have hp := (le_div_iff₀ (by linarith : 0 < W+1)).mp hh
    nlinarith only [hp, ht]
  have hn := hnear t ht.le ht1
  have hr := hraw t ht.le ht1
  obtain ⟨h, hh⟩ := hlocal (f t) (g t) (L*t^d) (by positivity)
    (fun n => (hn n).1.trans htR) (fun n => (hn n).2.trans htR) hr.1 hr.2
  have hs := hsep t ht.le ht1 h (C*(L*t^d)^α) hh
  rw [Real.mul_rpow hL (pow_nonneg ht.le d),
    ← Real.rpow_natCast_mul ht.le d α] at hs
  nlinarith only [hs]

theorem not_local_holder_three (N : ℕ) (hN : 3 ≤ N) (α : ℝ) (hα : 1/3 < α) :
    ¬LocalPairwiseHolder N (parityWeights N) α := by
  apply not_holder_of_witnesses N 3 (by decide) (parityWeights N)
    (sharpWeights N 3 3) (sharpFlippedWeights N 3 3)
    (128*(N.factorial : ℝ)^6) (∑ q ∈ Icc 1 N, (q.totient : ℝ)) 3 α
    (by positivity) (by positivity) hα
  · intro t ht _ n
    exact sharp_near_parity N 3 3 (by omega) (by simp; omega) (by simp; omega) (by decide) t ht n
  · intro t ht ht1
    exact ⟨sharp_raw_three N hN t 5 (by decide) ht ht1,
      sharp_raw_three N hN t 6 (by decide) ht ht1⟩
  · intro t ht _ h D herr
    exact sharp_separation_three N hN t ht h D herr

theorem not_local_holder_five (N : ℕ) (hN : 12 ≤ N) (α : ℝ) (hα : 1/5 < α) :
    ¬LocalPairwiseHolder N (parityWeights N) α := by
  apply not_holder_of_witnesses N 5 (by decide) (parityWeights N)
    (sharpWeights N 8 12) (sharpFlippedWeights N 8 12)
    (128*(N.factorial : ℝ)^6) (∑ q ∈ Icc 1 N, (q.totient : ℝ)) 5 α
    (by positivity) (by positivity) hα
  · intro t ht _ n
    exact sharp_near_parity N 8 12 (by omega) (by simp; omega) (by simp; omega) (by decide) t ht n
  · intro t ht ht1
    exact ⟨sharp_raw_five N hN t 5 (by decide) ht ht1,
      sharp_raw_five N hN t 6 (by decide) ht ht1⟩
  · intro t ht _ h D herr
    exact sharp_separation_five N hN t ht h D herr

theorem not_local_holder_six (N : ℕ) (hN : 20 ≤ N) (α : ℝ) (hα : 1/6 < α) :
    ¬LocalPairwiseHolder N (parityWeights N) α := by
  apply not_holder_of_witnesses N 6 (by decide) (parityWeights N)
    (sharpWeights N 12 20) (sharpFlippedWeights N 12 20)
    (128*(N.factorial : ℝ)^6) (∑ q ∈ Icc 1 N, (q.totient : ℝ)) 8 α
    (by positivity) (by positivity) hα
  · intro t ht _ n
    exact sharp_near_parity N 12 20 (by omega) (by simp; omega) (by simp; omega) (by decide) t ht n
  · intro t ht ht1
    exact ⟨sharp_raw_six N hN t 5 (by decide) ht ht1,
      sharp_raw_six N hN t 6 (by decide) ht ht1⟩
  · intro t ht _ h D herr
    exact sharp_separation_six N hN t ht h D herr

/-- The same explicit family, with a constant perturbation, covers the linear endpoint. -/
theorem not_local_holder_two (α : ℝ) (hα : 1 < α) :
    ¬LocalPairwiseHolder 2 (parityWeights 2) α := by
  apply not_holder_of_witnesses 2 1 (by decide) (parityWeights 2)
    (sharpWeights 2 1 1) (sharpFlippedWeights 2 1 1)
    (128*((2 : ℕ).factorial : ℝ)^6) (∑ q ∈ Icc 1 2, (q.totient : ℝ)) 1 α
    (by positivity) (by positivity) (by simpa using hα)
  · intro t ht _ n
    exact sharp_near_parity 2 1 1 (by decide) (by decide) (by decide) (by decide) t ht n
  · intro t ht ht1
    have hraw (m : ℕ) (hm : m ≤ 6) (v : Fin m → ℕ) :
        |translatedMoment 2 (sharpWeights 2 1 1 t) v-
          translatedMoment 2 (sharpFlippedWeights 2 1 1 t) v| ≤
          128*((2 : ℕ).factorial : ℝ)^6*t^1 := by
      apply sharp_raw_bound 2 1 1 t 1 m (by decide) (by decide) (by decide) hm ht ht1
      intro r _ hs ho
      have he : smallCount r = orderCount r 1 := by
        unfold smallCount orderCount
        congr 1
        ext i
        simp only [mem_filter, mem_univ, true_and]
        rcases hs i with h2 | h1 | h1
        · rw [h2]
          norm_num
        · rw [h1]
          norm_num
        · rw [h1]
          norm_num
      obtain ⟨j, hj⟩ := ho
      omega
    exact ⟨hraw 5 (by decide), hraw 6 (by decide)⟩
  · intro t ht _ h D herr
    have hh := sharp_flipped_phase_bound 2 1 1 t (by decide) (by decide) (by decide)
      (by decide) ht h D herr
    have hp : translationPhase 2 1 h = 1 := by
      simpa only [pow_one] using translationPhase_order 2 1 h (by decide)
    norm_num [hp] at hh ⊢
    linarith only [hh]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
