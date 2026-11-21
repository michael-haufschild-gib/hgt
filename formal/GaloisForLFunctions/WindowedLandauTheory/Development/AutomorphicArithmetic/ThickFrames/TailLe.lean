import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ThickFrames.MarkedLow
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ThickFrames.expectationSpec

/-! Upper bounds for the nonuniform Bernoulli cardinality tail. -/

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits WindowedLandauTheory.G0

noncomputable section

namespace UpperTheory.BernoulliSumsFrobeniusOrbits

private abbrev uniformEx (δ : ℝ) := exP (fun _ => δ)

private theorem uniformEx_powers (δ : ℝ) (S : Finset ℕ) (f : Finset ℕ → ℝ) :
    uniformEx δ S f =
      ∑ T ∈ S.powerset, δ ^ T.card * (1 - δ) ^ (S.card - T.card) * f T := by
  unfold uniformEx exP
  refine sum_congr rfl fun T hT => ?_
  rw [prod_const, prod_const, card_sdiff, inter_eq_left.mpr (mem_powerset.mp hT)]

variable {δ : ℝ}

private theorem uniform_mono (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {S : Finset ℕ}
    {f g : Finset ℕ → ℝ} (h : ∀ T ⊆ S, f T ≤ g T) : uniformEx δ S f ≤ uniformEx δ S g :=
  (expectation_spec (fun _ => δ)).2.2.2.1 S f g (fun _ _ => ⟨h0, h1⟩) h

private theorem uniform_restrict {A S : Finset ℕ} (hA : A ⊆ S) (f : Finset ℕ → ℝ) :
    uniformEx δ S (fun T => f (T ∩ A)) = uniformEx δ A f :=
  (expectation_spec (fun _ => δ)).2.2.2.2.2.1 A S f hA

private theorem ex_contains {Q B : Finset ℕ} (hQ : Q ⊆ B) :
    uniformEx δ B (fun T => ind (Q ⊆ T)) = δ ^ Q.card := by
  have e : (fun T : Finset ℕ => ind (Q ⊆ T)) = fun T => ind (Q ⊆ T ∩ Q) := by
    funext T
    simp only [subset_inter_iff, subset_rfl, and_true]
  conv_lhs => rw [e, uniform_restrict hQ (fun T => ind (Q ⊆ T)), uniformEx_powers]
  rw [sum_eq_single Q]
  · beta_reduce
    rw [ind_pos subset_rfl]
    simp
  · intro T hT hne
    beta_reduce
    rw [ind_neg, mul_zero]
    exact fun h => hne (subset_antisymm (mem_powerset.mp hT) h)
  · intro h
    exact absurd (mem_powerset_self Q) h

private theorem tail_le_choose (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {B : Finset ℕ} {L : ℕ} (hB : B.card ≤ L) (K : ℕ) :
    uniformEx δ B (fun T => ind (K ≤ T.card)) ≤ (L.choose K : ℝ) * δ ^ K := by
  have hpt : ∀ T ⊆ B, ind (K ≤ #T) ≤ ∑ Q ∈ B.powersetCard K, ind (Q ⊆ T) := by
    intro T hT
    refine ind_le (sum_nonneg fun _ _ => ind_nonneg _) fun hK => ?_
    obtain ⟨Q, hQT, hQ⟩ := Finset.exists_subset_card_eq hK
    have hQB : Q ∈ B.powersetCard K := mem_powersetCard.mpr ⟨hQT.trans hT, hQ⟩
    calc (1 : ℝ) = ind (Q ⊆ T) := (ind_pos hQT).symm
      _ ≤ _ := single_le_sum (f := fun Q => ind (Q ⊆ T)) (fun _ _ => ind_nonneg _) hQB
  calc uniformEx δ B (fun T => ind (K ≤ #T))
      ≤ uniformEx δ B (fun T => ∑ Q ∈ B.powersetCard K, ind (Q ⊆ T)) := uniform_mono h0 h1 hpt
    _ = ∑ Q ∈ B.powersetCard K, uniformEx δ B (fun T => ind (Q ⊆ T)) :=
      ex_sum (p := fun _ => δ) _ _ (fun Q T => ind (Q ⊆ T))
    _ = ∑ Q ∈ B.powersetCard K, δ ^ K := sum_congr rfl fun Q hQ => by
      rw [ex_contains (mem_powersetCard.mp hQ).1, (mem_powersetCard.mp hQ).2]
    _ = ((#B).choose K : ℝ) * δ ^ K := by rw [sum_const, card_powersetCard, nsmul_eq_mul]
    _ ≤ (L.choose K : ℝ) * δ ^ K :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose K hB) (pow_nonneg h0 _)

private theorem tail_eq (B : Finset ℕ) (K : ℕ) :
    uniformEx δ B (fun T => ind (K ≤ T.card)) = binUpper B.card δ K := by
  rw [uniformEx_powers]
  unfold binUpper
  have hs := sum_powerset_apply_card (fun m => δ ^ m * (1 - δ) ^ (#B - m) * ind (K ≤ m)) (x := B)
  rw [hs]
  have hI : Icc K #B = (range (#B + 1)).filter (fun m => K ≤ m) := by
    ext m
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  rw [hI, sum_filter]
  refine sum_congr rfl fun m _ => ?_
  unfold ind
  split_ifs
  · rw [nsmul_eq_mul]
    ring
  · simp

private theorem tail_le_binUpper (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {A : Finset ℕ} {G : ℕ} (hA : A.card ≤ G)
    (K : ℕ) : uniformEx δ A (fun T => ind (K ≤ T.card)) ≤ binUpper G δ K := by
  obtain ⟨A', hAA', hA'⟩ := Infinite.exists_superset_card_eq A G hA
  calc uniformEx δ A (fun T => ind (K ≤ #T)) = uniformEx δ A' (fun T => ind (K ≤ #(T ∩ A))) :=
      (uniform_restrict hAA' (fun T => ind (K ≤ #T))).symm
    _ ≤ uniformEx δ A' (fun T => ind (K ≤ #T)) := uniform_mono h0 h1 fun T _ =>
      ind_le (ind_nonneg _) fun h => (ind_pos (le_trans h (card_le_card inter_subset_left))).ge
    _ = binUpper G δ K := by rw [tail_eq, hA']

private theorem bernoulliExpectation_le_of_monotone (p : ℕ → ℝ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (A : Finset ℕ) :
    ∀ f : Finset ℕ → ℝ, Monotone f → (∀ a ∈ A, 0 ≤ p a ∧ p a ≤ δ) →
      exP p A f ≤ uniformEx δ A f := by
  induction A using Finset.induction_on with
  | empty =>
    intro f _ _
    simp [uniformEx, exP]
  | insert a S ha ih =>
    intro f hf hp
    have hpS : ∀ b ∈ S, 0 ≤ p b ∧ p b ≤ δ := fun b hb => hp b (Finset.mem_insert_of_mem hb)
    obtain ⟨hpa0, hpa1⟩ := hp a (Finset.mem_insert_self _ _)
    have e1 := ih f hf hpS
    have e2 := ih (fun T => f (insert a T))
      (fun T U hTU => hf (Finset.insert_subset_insert a hTU)) hpS
    have e3 : uniformEx δ S f ≤ uniformEx δ S (fun T => f (insert a T)) :=
      uniform_mono h0 h1 fun T _ => hf (Finset.subset_insert a T)
    unfold uniformEx at e1 e2 e3 ⊢
    rw [(expectation_spec p).2.2.2.2.1 a S f ha, (expectation_spec (fun _ => δ)).2.2.2.2.1 a S f ha]
    have k1 := mul_le_mul_of_nonneg_left e1 (show 0 ≤ 1 - p a by linarith)
    have k2 := mul_le_mul_of_nonneg_left e2 hpa0
    have k3 := mul_le_mul_of_nonneg_left e3 (show 0 ≤ δ - p a by linarith)
    linarith only [k1, k2, k3]

theorem tail_le :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (A : Finset ℕ) (G K : ℕ), (∀ a ∈ A, 0 ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → A.card ≤ G →
      exP p A (fun T => ind (K ≤ T.card)) ≤ (G.choose K : ℝ) * δ ^ K ∧ exP p A (fun T => ind (K ≤ T.card)) ≤ binUpper G δ K := by
  intro p δ A G K hp h0 h1 hG
  have hmono : Monotone (fun T : Finset ℕ => ind (K ≤ T.card)) := by
    intro T U hTU
    have hc := Finset.card_le_card hTU
    simp only [ind]
    split_ifs <;> first | (exfalso; omega) | norm_num
  have hle := bernoulliExpectation_le_of_monotone p δ h0 h1 A _ hmono hp
  exact ⟨le_trans hle (tail_le_choose h0 h1 hG K),
    le_trans hle (tail_le_binUpper h0 h1 hG K)⟩

end UpperTheory.BernoulliSumsFrobeniusOrbits
