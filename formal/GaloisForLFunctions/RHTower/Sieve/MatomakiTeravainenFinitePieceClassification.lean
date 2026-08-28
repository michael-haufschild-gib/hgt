import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPaperDilation
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPieceClassification

/-!
# Proposition 2.2 classification over arbitrary finite index types

Recursive blocks are indexed by `Fin t`, while the original scalar classification was stated for
natural indices.  These type-generic forms preserve the same proof and avoid any lossy reindexing.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Greedy accumulation over an arbitrary finite carrier. -/
private theorem exists_subset_sum_between_finite
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℝ) {target step : ℝ}
    (htarget : 0 ≤ target) (hstep : 0 ≤ step)
    (hw0 : ∀ i ∈ S, 0 ≤ w i) (hwstep : ∀ i ∈ S, w i ≤ step)
    (htotal : target ≤ ∑ i ∈ S, w i) :
    ∃ I ⊆ S, target ≤ ∑ i ∈ I, w i ∧ ∑ i ∈ I, w i ≤ target + step := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty] at htotal
      exact ⟨∅, Finset.Subset.rfl, by simpa using htotal, by simp; linarith⟩
  | @insert i S hi ih =>
      by_cases hS : target ≤ ∑ j ∈ S, w j
      · obtain ⟨I, hIS, hlo, hhi⟩ := ih
          (fun j hj => hw0 j (Finset.mem_insert_of_mem hj))
          (fun j hj => hwstep j (Finset.mem_insert_of_mem hj)) hS
        exact ⟨I, fun _ hj => Finset.mem_insert_of_mem (hIS hj), hlo, hhi⟩
      · refine ⟨insert i S, Finset.Subset.rfl, htotal, ?_⟩
        rw [Finset.sum_insert hi]
        have hiStep := hwstep i (Finset.mem_insert_self i S)
        linarith

/-- Exact subset-product lemma over an arbitrary finite index type. -/
theorem exists_subset_product_between_threshold_and_cap_finite
    {ι : Type*} [DecidableEq ι] {Q : ι → ℝ} {S : Finset ι} {tau z : ℝ}
    (htau : 1 ≤ tau)
    (hQone : ∀ i ∈ S, 1 ≤ Q i)
    (hQcap : ∀ i ∈ S, Q i ≤ z)
    (htotal : tau ≤ ∏ i ∈ S, Q i)
    (htauSq : tau ^ 2 ≤ z) :
    ∃ I ⊆ S, tau ≤ ∏ i ∈ I, Q i ∧ ∏ i ∈ I, Q i ≤ z := by
  by_cases hlarge : ∃ i ∈ S, tau ≤ Q i
  · obtain ⟨i, hiS, hitau⟩ := hlarge
    refine ⟨{i}, Finset.singleton_subset_iff.mpr hiS, ?_, ?_⟩
    · simpa using hitau
    · simpa using hQcap i hiS
  · have hsmall : ∀ i ∈ S, Q i < tau := by
      intro i hi
      exact lt_of_not_ge (fun hitau => hlarge ⟨i, hi, hitau⟩)
    have htauPos : 0 < tau := zero_lt_one.trans_le htau
    have hlogTotal : Real.log tau ≤ ∑ i ∈ S, Real.log (Q i) := by
      rw [← Real.log_prod (fun i hi => (zero_lt_one.trans_le (hQone i hi)).ne')]
      exact Real.log_le_log htauPos htotal
    obtain ⟨I, hIS, hlo, hhi⟩ := exists_subset_sum_between_finite
      S (fun i => Real.log (Q i)) (Real.log_nonneg htau) (Real.log_nonneg htau)
      (fun i hi => Real.log_nonneg (hQone i hi))
      (fun i hi => Real.log_le_log
        (zero_lt_one.trans_le (hQone i hi)) (hsmall i hi).le)
      hlogTotal
    have hprodPos : 0 < ∏ i ∈ I, Q i :=
      Finset.prod_pos fun i hi => zero_lt_one.trans_le (hQone i (hIS hi))
    refine ⟨I, hIS, ?_, ?_⟩
    · calc
        tau = Real.exp (Real.log tau) := (Real.exp_log htauPos).symm
        _ ≤ Real.exp (Real.log (∏ i ∈ I, Q i)) := by
          apply Real.exp_le_exp.mpr
          rw [Real.log_prod
            (fun i hi => (zero_lt_one.trans_le (hQone i (hIS hi))).ne')]
          exact hlo
        _ = ∏ i ∈ I, Q i := Real.exp_log hprodPos
    · calc
        ∏ i ∈ I, Q i = Real.exp (Real.log (∏ i ∈ I, Q i)) :=
          (Real.exp_log hprodPos).symm
        _ ≤ Real.exp (Real.log tau + Real.log tau) := by
          apply Real.exp_le_exp.mpr
          rw [Real.log_prod
            (fun i hi => (zero_lt_one.trans_le (hQone i (hIS hi))).ne')]
          exact hhi
        _ = tau ^ 2 := by rw [Real.exp_add, Real.exp_log htauPos]; ring
        _ ≤ z := htauSq

/-- Source Type-II subset range over an arbitrary finite index type. -/
theorem exists_subset_product_in_matomakiTeravainen_typeII_range_finite
    {ι : Type*} [DecidableEq ι] {Q : ι → ℝ} {S : Finset ι} {X epsilon : ℝ}
    (hX : 1 ≤ X) (hepsilon0 : 0 ≤ epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hQone : ∀ i ∈ S, 1 ≤ Q i)
    (hQcap : ∀ i ∈ S, Q i ≤ X ^ (2 / 11 : ℝ))
    (htotal : X ^ (epsilon / 2) ≤ ∏ i ∈ S, Q i) :
    ∃ I ⊆ S,
      X ^ (epsilon / 2) ≤ ∏ i ∈ I, Q i ∧
        ∏ i ∈ I, Q i ≤ X ^ (2 / 11 : ℝ) := by
  apply exists_subset_product_between_threshold_and_cap_finite
      (htau := Real.one_le_rpow hX (div_nonneg hepsilon0 (by norm_num)))
      hQone hQcap htotal
  calc
    (X ^ (epsilon / 2)) ^ 2 = (X ^ (epsilon / 2)) ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = X ^ ((epsilon / 2) * 2) :=
      (Real.rpow_mul (zero_le_one.trans hX) (epsilon / 2) 2).symm
    _ = X ^ epsilon := by congr 1; ring
    _ ≤ X ^ (2 / 11 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hepsilon

/-- Exact small-product/Type-II split over an arbitrary finite index type. -/
theorem matomakiTeravainen_primeBlockProduct_dichotomy_finite
    {ι : Type*} [DecidableEq ι] {Q : ι → ℝ} {S : Finset ι} {X epsilon : ℝ}
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hQone : ∀ i ∈ S, 1 ≤ Q i)
    (hQcap : ∀ i ∈ S, Q i ≤ X ^ (2 / 11 : ℝ)) :
    (∏ i ∈ S, Q i) < X ^ (epsilon / 2) ∨
      ∃ I ⊆ S, I.Nonempty ∧
        X ^ (epsilon / 2) ≤ ∏ i ∈ I, Q i ∧
          ∏ i ∈ I, Q i ≤ X ^ (2 / 11 : ℝ) := by
  by_cases hsmall : (∏ i ∈ S, Q i) < X ^ (epsilon / 2)
  · exact Or.inl hsmall
  · right
    obtain ⟨I, hIS, hlo, hhi⟩ :=
      exists_subset_product_in_matomakiTeravainen_typeII_range_finite
        hX.le hepsilon0.le hepsilon hQone hQcap (le_of_not_gt hsmall)
    have hthreshold : (1 : ℝ) < X ^ (epsilon / 2) :=
      Real.one_lt_rpow hX (div_pos hepsilon0 (by norm_num))
    have hI : I.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hlo
      simp at hlo
      linarith
    exact ⟨I, hIS, hI, hlo, hhi⟩

/-- Pair-term scale classification for the actual finite recursive-block index type. -/
theorem matomakiTeravainen_pairTerm_typeI_or_typeII_finite
    {ι : Type*} [DecidableEq ι] {Q : ι → ℝ} {S : Finset ι}
    {X epsilon E Q1 Q2 : ℝ}
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hE0 : 0 ≤ E) (hQ10 : 0 ≤ Q1) (hQ20 : 0 ≤ Q2)
    (hE : E ≤ X ^ (epsilon / 4))
    (hQ1 : Q1 ≤ X ^ (1 / 4 - 2 * epsilon))
    (hQ2 : Q2 ≤ X ^ (1 / 4 - 2 * epsilon))
    (hQone : ∀ i ∈ S, 1 ≤ Q i)
    (hQcap : ∀ i ∈ S, Q i ≤ X ^ (2 / 11 : ℝ)) :
    E * Q1 * Q2 * (∏ i ∈ S, Q i) ≤ X ^ (1 / 2 + epsilon) ∨
      ∃ I ⊆ S, I.Nonempty ∧
        X ^ (epsilon / 2) ≤ ∏ i ∈ I, Q i ∧
          ∏ i ∈ I, Q i ≤ X ^ (2 / 11 : ℝ) := by
  rcases matomakiTeravainen_primeBlockProduct_dichotomy_finite
      hX hepsilon0 hepsilon hQone hQcap with hsmall | htypeII
  · left
    exact matomakiTeravainen_small_product_typeI_scale hX.le hepsilon0.le
      hE0 hQ10 hQ20
      (Finset.prod_nonneg fun i hi => zero_le_one.trans (hQone i hi))
      hE hQ1 hQ2 hsmall.le
  · exact Or.inr htypeII

/-- Triple-term scale classification for the actual finite recursive-block index type. -/
theorem matomakiTeravainen_tripleTerm_typeI_II_or_typeII_finite
    {ι : Type*} [DecidableEq ι] {Q : ι → ℝ} {S : Finset ι}
    {X epsilon E Q1 Q2 Q3 : ℝ}
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hE0 : 0 ≤ E) (hQ10 : 0 ≤ Q1) (hQ20 : 0 ≤ Q2) (hQ30 : 0 ≤ Q3)
    (hE : E ≤ X ^ (epsilon / 4))
    (hQ1 : Q1 ≤ X ^ (1 / 4 - 2 * epsilon))
    (hQ3Q2 : Q3 ≤ Q2)
    (hgeometry : Q1 * Q2 ^ 4 ≤ X ^ (1 - 2 * epsilon))
    (hQone : ∀ i ∈ S, 1 ≤ Q i)
    (hQcap : ∀ i ∈ S, Q i ≤ X ^ (2 / 11 : ℝ)) :
    ((E * Q2 * Q3) ^ 2 * (Q1 * ∏ i ∈ S, Q i) ≤ X ^ (1 - epsilon) ∧
        Q1 * (∏ i ∈ S, Q i) ≤ X ^ (1 / 4 - epsilon)) ∨
      ∃ I ⊆ S, I.Nonempty ∧
        X ^ (epsilon / 2) ≤ ∏ i ∈ I, Q i ∧
          ∏ i ∈ I, Q i ≤ X ^ (2 / 11 : ℝ) := by
  rcases matomakiTeravainen_primeBlockProduct_dichotomy_finite
      hX hepsilon0 hepsilon hQone hQcap with hsmall | htypeII
  · left
    exact matomakiTeravainen_small_product_typeI_II_scales hX.le hepsilon0.le
      hE0 hQ10 hQ20 hQ30
      (Finset.prod_nonneg fun i hi => zero_le_one.trans (hQone i hi))
      hE hQ1 hQ3Q2 hgeometry hsmall.le
  · exact Or.inr htypeII

end

end RHTower.Sieve
