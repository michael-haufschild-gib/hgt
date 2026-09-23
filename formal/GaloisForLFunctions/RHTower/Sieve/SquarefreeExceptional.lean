import GaloisForLFunctions.RHTower.Sieve.SquarefreeTruncationDefect
import GaloisForLFunctions.RHTower.Sieve.GoodStartMarkov
import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTail

/-!
# The exceptional set where the squarefree count is deficient

Markov's inequality for a nonnegative quantity: if the values sum to at most `V`, at most `V/θ` of
them reach `θ`.  Applied to the truncation defect and combined with `squarefree_count_ge`, a start
whose squarefree count falls below `½DL` must have defect at least

`θ = ½DL - (R + L/R)`,

so the deficient starts number at most `V/θ`.  This is the card's `(13)` with the averaged tail
supplying `V`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Markov's inequality for a nonnegative quantity.** -/
theorem card_large_le_of_sum_le {S : Finset ℕ} {f : ℕ → ℝ} {V θ : ℝ} (hθ : 0 < θ)
    (hf : ∀ t ∈ S, 0 ≤ f t) (h : ∑ t ∈ S, f t ≤ V) :
    (((S.filter (fun t => θ ≤ f t)).card : ℕ) : ℝ) ≤ V / θ := by
  classical
  have hsub : S.filter (fun t => θ ≤ f t) ⊆ S := Finset.filter_subset _ _
  have hlow : (((S.filter (fun t => θ ≤ f t)).card : ℕ) : ℝ) * θ
      ≤ ∑ t ∈ S.filter (fun t => θ ≤ f t), f t := by
    have hconst : ∑ _t ∈ S.filter (fun t => θ ≤ f t), θ
        = (((S.filter (fun t => θ ≤ f t)).card : ℕ) : ℝ) * θ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hconst]
    exact Finset.sum_le_sum fun t ht => (Finset.mem_filter.mp ht).2
  have hup : ∑ t ∈ S.filter (fun t => θ ≤ f t), f t ≤ ∑ t ∈ S, f t :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun t ht _ => hf t ht
  rw [le_div_iff₀ hθ]
  linarith

/-- **The deficient starts are few.**  Card equation `(13)`. -/
theorem card_squarefree_deficient_le {S : Finset ℕ} {L R M : ℕ} {V : ℝ} (hR : 1 ≤ R)
    (hM : ∀ t ∈ S, t + L ≤ M)
    (hθ : 0 < (1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ)))
    (hdef : ∑ t ∈ S, ∑ d ∈ Finset.Icc (R + 1) M,
        ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) ≤ V) :
    (((S.filter (fun t =>
        ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
          < (1 / 2) * ((L : ℝ) * squarefreeDensity))).card : ℕ) : ℝ)
      ≤ V / ((1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ))) := by
  classical
  set θ : ℝ := (1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ)) with hθdef
  set g : ℕ → ℝ := fun t => ∑ d ∈ Finset.Icc (R + 1) M,
      ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) with hg
  have hgnn : ∀ t ∈ S, 0 ≤ g t := by
    intro t _
    rw [hg]
    exact Finset.sum_nonneg fun d _ => Nat.cast_nonneg _
  have hsubset : S.filter (fun t =>
      ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
        < (1 / 2) * ((L : ℝ) * squarefreeDensity))
      ⊆ S.filter (fun t => θ ≤ g t) := by
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    obtain ⟨htS, hlt⟩ := ht
    refine ⟨htS, ?_⟩
    have hge := squarefree_count_ge t L R M hR (hM t htS)
    rw [hθdef, hg]
    linarith
  refine le_trans ?_ (card_large_le_of_sum_le (S := S) (f := g) hθ hgnn hdef)
  exact_mod_cast Finset.card_le_card hsubset

/-- **Step 1 with both exceptional sets explicit.**  Only the mean-square hypothesis `hms` is not
elementary; `hdef` is supplied by the averaged truncation tail. -/
theorem card_le_good_add_explicit {S : Finset ℕ} {L R M : ℕ} {V W : ℝ} (hR : 1 ≤ R)
    (hM : ∀ t ∈ S, t + L ≤ M)
    (hδ : 0 < (1 / 8) * squarefreeDensity * (L : ℝ))
    (hθ : 0 < (1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ)))
    (hms : ∑ t ∈ S, (∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ)) ^ (2 : ℕ) ≤ V)
    (hdef : ∑ t ∈ S, ∑ d ∈ Finset.Icc (R + 1) M,
        ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) ≤ W) :
    (S.card : ℝ)
      ≤ ((S.filter (fun t =>
          (3 / 16) * squarefreeDensity * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * squarefreeDensity * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
        + V / ((1 / 8) * squarefreeDensity * (L : ℝ)) ^ (2 : ℕ)
        + W / ((1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ))) := by
  classical
  set Bad₂ := S.filter (fun t =>
      ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
        < (1 / 2) * ((L : ℝ) * squarefreeDensity)) with hBad₂
  have h2 : ∀ t ∈ S, t ∉ Bad₂ →
      (1 / 2) * squarefreeDensity * (L : ℝ)
        ≤ ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ) := by
    intro t ht hnot
    have : ¬ (∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
        < (1 / 2) * ((L : ℝ) * squarefreeDensity)) := by
      intro hc
      exact hnot (by rw [hBad₂, Finset.mem_filter]; exact ⟨ht, hc⟩)
    have h := not_lt.mp this
    linarith
  have hstep := card_le_good_add_meanSquare (S := S) (Bad₂ := Bad₂) (L := L)
    (D := squarefreeDensity) (V := V) hδ hms h2
  have hbad : (Bad₂.card : ℝ)
      ≤ W / ((1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ))) := by
    rw [hBad₂]
    exact card_squarefree_deficient_le hR hM hθ hdef
  linarith

/-- **Card equation (13), fully explicit.**  The averaged truncation tail supplies the numerator, so
no free parameter remains. -/
theorem card_squarefree_deficient_Ico_le {A B L R M : ℕ} (hR : 1 ≤ R) (hAB : A ≤ B + L)
    (hM : ∀ t ∈ Finset.Ico A B, t + L ≤ M)
    (hθ : 0 < (1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ))) :
    ((((Finset.Ico A B).filter (fun t =>
        ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
          < (1 / 2) * ((L : ℝ) * squarefreeDensity))).card : ℕ) : ℝ)
      ≤ ((L : ℝ) * (((B : ℝ) + L - A) / (R : ℝ) + (M : ℝ)))
          / ((1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ))) :=
  card_squarefree_deficient_le hR hM hθ (sum_tail_divisor_count_le A B L R M hR hAB)

end RHTower.Sieve
