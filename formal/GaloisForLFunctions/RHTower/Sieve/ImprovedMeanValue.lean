import GaloisForLFunctions.RHTower.Sieve.PrimePairNeighbour

/-!
# The improved mean value theorem for Dirichlet polynomials

Matomäki–Teräväinen, *Almost primes in almost all short intervals II*, Lemma 3.3:

```text
∫_{-T}^{T}|A(it)|²dt  ≪  T ∑_{n ≤ N}|a_n|²  +  T ∑_{0<|k| ≤ N/T} ∑_{n ≤ N}|a_n||a_{n+k}| ,
```

which beats the classical mean value theorem exactly when the support of `a` is sparse — the
regime of every short-interval argument.  The corpus proves it in the equivalent Gallagher form:
the almost-diagonal mean value theorem of `Sieve/GallagherAlmostDiagonal` weighs each frequency by
its *multiplicative* neighbour count, and on a support inside `[1, N]` a multiplicative window of
ratio `e^δ` is an additive window of length `3Nδ`, so the neighbour count is a shifted-support
count.

The weighted bookkeeping lemma below is the weighted companion of
`Sieve.sum_card_neighbour_le`; the pair set splits into the diagonal and the two shifted copies,
and the weight rides along.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A nonnegative sum over a union of fibres, for an arbitrary value type. -/
theorem sum_biUnion_le_of_nonneg' {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s.biUnion t, f i ≤ ∑ p ∈ s, ∑ i ∈ t p, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hun : ∑ i ∈ t a ∪ s.biUnion t, f i
        ≤ ∑ i ∈ t a, f i + ∑ i ∈ s.biUnion t, f i := by
      have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hnn : (0 : ℝ) ≤ ∑ i ∈ t a ∩ s.biUnion t, f i :=
        Finset.sum_nonneg fun i _ => hf i
      linarith
    linarith [hun, ih]

/-- **The weighted near-diagonal pair count, split by the shift.** -/
theorem sum_weighted_neighbour_le (s : Finset ℕ) (K : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P]
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hP : ∀ n ∈ s, ∀ m ∈ s, P n m → n ≤ m + K ∧ m ≤ n + K) :
    ∑ n ∈ s, (#(s.filter (fun m => P n m)) : ℝ) * w n
      ≤ ∑ n ∈ s, w n
        + ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ s.filter (fun n => n + k ∈ s), (w n + w (n + k)) := by
  classical
  set F : ℕ × ℕ → ℝ := fun q => w q.1 with hF
  have hF0 : ∀ q : ℕ × ℕ, 0 ≤ F q := fun q => hw q.1
  -- the weighted pair count
  have hcount : ∑ n ∈ s, (#(s.filter (fun m => P n m)) : ℝ) * w n
      = ∑ q ∈ (s ×ˢ s).filter (fun q => P q.1 q.2), F q := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.card_filter]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hF]
    split_ifs <;> ring
  set Up : Finset (ℕ × ℕ) := (Finset.Icc 1 K).biUnion
    (fun k => (s.filter (fun n => n + k ∈ s)).image (fun n => (n, n + k))) with hUp
  set Down : Finset (ℕ × ℕ) := (Finset.Icc 1 K).biUnion
    (fun k => (s.filter (fun n => n + k ∈ s)).image (fun n => (n + k, n))) with hDown
  set Diag : Finset (ℕ × ℕ) := s.image (fun n => (n, n)) with hDiag
  have hsub : (s ×ˢ s).filter (fun q => P q.1 q.2) ⊆ Diag ∪ (Up ∪ Down) := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨h1, h2⟩, hPq⟩ := hq
    obtain ⟨hle1, hle2⟩ := hP q.1 h1 q.2 h2 hPq
    rcases lt_trichotomy q.1 q.2 with hlt | heq | hgt
    · refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
      refine Finset.mem_biUnion.2 ⟨q.2 - q.1, by rw [Finset.mem_Icc]; omega, ?_⟩
      refine Finset.mem_image.2 ⟨q.1, ?_, Prod.ext rfl (by omega)⟩
      rw [Finset.mem_filter]
      refine ⟨h1, ?_⟩
      have hq2 : q.1 + (q.2 - q.1) = q.2 := by omega
      rw [hq2]; exact h2
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨q.1, h1, Prod.ext rfl heq⟩)
    · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
      refine Finset.mem_biUnion.2 ⟨q.1 - q.2, by rw [Finset.mem_Icc]; omega, ?_⟩
      refine Finset.mem_image.2 ⟨q.2, ?_, Prod.ext (by omega) rfl⟩
      rw [Finset.mem_filter]
      refine ⟨h2, ?_⟩
      have hq1 : q.2 + (q.1 - q.2) = q.1 := by omega
      rw [hq1]; exact h1
  have hunion : ∑ q ∈ (s ×ˢ s).filter (fun q => P q.1 q.2), F q
      ≤ ∑ q ∈ Diag, F q + (∑ q ∈ Up, F q + ∑ q ∈ Down, F q) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hF0 i)) ?_
    have h1 := Finset.sum_union_inter (s₁ := Diag) (s₂ := Up ∪ Down) (f := F)
    have h2 := Finset.sum_union_inter (s₁ := Up) (s₂ := Down) (f := F)
    have hn1 : (0 : ℝ) ≤ ∑ q ∈ Diag ∩ (Up ∪ Down), F q := Finset.sum_nonneg fun i _ => hF0 i
    have hn2 : (0 : ℝ) ≤ ∑ q ∈ Up ∩ Down, F q := Finset.sum_nonneg fun i _ => hF0 i
    linarith
  have hDiagEq : ∑ q ∈ Diag, F q = ∑ n ∈ s, w n := by
    rw [hDiag, Finset.sum_image (by intro a _ b _ hab; exact (Prod.mk.injEq _ _ _ _ ▸ hab).1)]
  have hUpLe : ∑ q ∈ Up, F q
      ≤ ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ s.filter (fun n => n + k ∈ s), w n := by
    refine le_trans (sum_biUnion_le_of_nonneg' _ _ F hF0) (Finset.sum_le_sum fun k _ => ?_)
    rw [Finset.sum_image (by intro a _ b _ hab; exact (Prod.mk.injEq _ _ _ _ ▸ hab).1)]
  have hDownLe : ∑ q ∈ Down, F q
      ≤ ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ s.filter (fun n => n + k ∈ s), w (n + k) := by
    refine le_trans (sum_biUnion_le_of_nonneg' _ _ F hF0) (Finset.sum_le_sum fun k _ => ?_)
    rw [Finset.sum_image (by intro a _ b _ hab; exact (Prod.mk.injEq _ _ _ _ ▸ hab).2)]
  have hsplit : ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ s.filter (fun n => n + k ∈ s), (w n + w (n + k))
      = (∑ k ∈ Finset.Icc 1 K, ∑ n ∈ s.filter (fun n => n + k ∈ s), w n)
        + ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ s.filter (fun n => n + k ∈ s), w (n + k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_add_distrib]
  rw [hcount, hsplit]
  linarith [hunion, hDiagEq.le, hDiagEq.ge, hUpLe, hDownLe]

/-- **A multiplicative window on `[1, N]` is an additive window.** -/
theorem le_add_of_log_close_range {N K : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 3 * (N : ℝ) * δ ≤ (K : ℝ)) {n m : ℕ} (hn : 1 ≤ n ∧ n ≤ N) (hm : 1 ≤ m ∧ m ≤ N)
    (hlog : |Real.log (n : ℝ) - Real.log (m : ℝ)| < δ) :
    n ≤ m + K ∧ m ≤ n + K := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
  have hmN : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm.2
  have hexp := exp_sub_one_le_three_mul hδ0.le hδ1
  rw [abs_lt] at hlog
  constructor
  · have h1 : (n : ℝ) < (m : ℝ) * Real.exp δ := lt_mul_exp_of_log_sub_lt hn0 hm0 hlog.2
    have h2 : (n : ℝ) < (m : ℝ) + (K : ℝ) := by nlinarith [h1, hexp, hmN, hδ0.le, hK]
    have h3 : n < m + K := by exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((m + K : ℕ) : ℝ))
    omega
  · have h1 : (m : ℝ) < (n : ℝ) * Real.exp δ :=
      lt_mul_exp_of_log_sub_lt hm0 hn0 (by linarith [hlog.1])
    have h2 : (m : ℝ) < (n : ℝ) + (K : ℝ) := by nlinarith [h1, hexp, hnN, hδ0.le, hK]
    have h3 : m < n + K := by exact_mod_cast (by push_cast; linarith : (m : ℝ) < ((n + K : ℕ) : ℝ))
    omega

/-- **The improved mean value theorem.**  Matomäki–Teräväinen Lemma 3.3, in the corpus's Gallagher
form: the mean square of a Dirichlet polynomial supported in `[1, N]` is paid by the diagonal plus
the shifted supports at shifts up to `3Nδ`, where `δ` is the reciprocal of the height. -/
theorem integral_Icc_normSq_logPoly_le_shift (a : ℕ → ℂ) (s : Finset ℕ) {N K : ℕ}
    (hsN : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) {δ W : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hWδ : 2 * Real.pi * δ * W ≤ 1) (hK : 3 * (N : ℝ) * δ ≤ (K : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ (5 / (4 * δ)) * (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)
          + ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ s.filter (fun n => n + k ∈ s),
              (‖a n‖ ^ (2 : ℕ) + ‖a (n + k)‖ ^ (2 : ℕ))) := by
  classical
  refine le_trans (integral_Icc_normSq_logPoly_le_count a s hδ0 hWδ) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hstep := sum_weighted_neighbour_le s K
    (fun n m => |Real.log (n : ℝ) - Real.log (m : ℝ)| < δ)
    (fun n => ‖a n‖ ^ (2 : ℕ)) (fun n => by positivity)
    (fun n hn m hm hnm => le_add_of_log_close_range hδ0 hδ1 hK (hsN n hn) (hsN m hm) hnm)
  refine le_trans (le_of_eq ?_) hstep
  exact Finset.sum_congr rfl fun n _ => rfl

end

end RHTower.Sieve
