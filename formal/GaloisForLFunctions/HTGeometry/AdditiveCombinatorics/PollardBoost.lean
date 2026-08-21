import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardTranslation

/-!
# The boosted counting bound of Grynkiewicz's CASE 4

CASE 4 counts `∑_{i≤t} #(A ·_i B)` from below by three separate contributions: the
`t`-representable core `A' · B'`, the mixed representations of the deleted elements, and a set `S`
of products lying outside `A' · B'` which are already `t`-representable in `A × B`.  The last
contribution is worth `t − l` each, `l` being the defect, because the mixed count at such a
product is at most `l`.

The counting pair `(X, Y)` supplying the mixed representations may differ from `(A, B)`; in the
application it is the Dyson pair, whose representation counts are dominated by those of `(A, B)`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

theorem repSum_ge_boost {A B X Y A' B' S : Finset G} {t : ℕ}
    (hA' : A' ⊆ X) (hB' : B' ⊆ Y)
    (hrep : ∀ c : G, rep X Y c ≤ rep A B c)
    (hsub : A' * B' ⊆ repSet A B t)
    (hl : defect X A' Y B' ≤ t)
    (hS : S ⊆ Finset.univ \ (A' * B')) (hSt : ∀ c ∈ S, t ≤ rep A B c) :
    t * (A' * B').card
      + ∑ c ∈ Finset.univ \ (A' * B'), (rep (X \ A') B' c + rep A' (Y \ B') c)
      + S.card * (t - defect X A' Y B') ≤ repSum A B t := by
  classical
  rw [repSum_eq_sum_min]
  have hsplit : ∑ c ∈ Finset.univ \ (A' * B'), min (rep A B c) t
      + ∑ c ∈ A' * B', min (rep A B c) t = ∑ c : G, min (rep A B c) t :=
    Finset.sum_sdiff (Finset.subset_univ (A' * B'))
  have hin : ∑ c ∈ A' * B', min (rep A B c) t = t * (A' * B').card := by
    have hval : ∀ c ∈ A' * B', min (rep A B c) t = t := by
      intro c hc
      have hc' := hsub hc
      rw [mem_repSet] at hc'
      exact min_eq_right hc'
    rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul, mul_comm]
  have hmixed : ∀ c : G, rep (X \ A') B' c + rep A' (Y \ B') c ≤ defect X A' Y B' := by
    intro c
    have hL := rep_le_card_left (X \ A') B' c
    have hR := rep_le_card_right A' (Y \ B') c
    rw [defect]
    omega
  have hout : ∑ c ∈ Finset.univ \ (A' * B'),
        (rep (X \ A') B' c + rep A' (Y \ B') c
          + (if c ∈ S then t - defect X A' Y B' else 0))
      ≤ ∑ c ∈ Finset.univ \ (A' * B'), min (rep A B c) t := by
    refine Finset.sum_le_sum (fun c _ => ?_)
    have h1 : rep (X \ A') B' c + rep A' (Y \ B') c ≤ rep X Y c :=
      rep_sdiff_add_rep_sdiff_le hA' hB' c
    have h2 := hrep c
    have h3 := hmixed c
    by_cases hc : c ∈ S
    · rw [if_pos hc]
      have h4 := hSt c hc
      have : min (rep A B c) t = t := min_eq_right h4
      omega
    · rw [if_neg hc]
      have : rep (X \ A') B' c + rep A' (Y \ B') c ≤ min (rep A B c) t :=
        le_min (by omega) (by omega)
      omega
  have hite : ∑ c ∈ Finset.univ \ (A' * B'),
        (if c ∈ S then t - defect X A' Y B' else 0)
      = S.card * (t - defect X A' Y B') := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hS, Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_add_distrib, hite] at hout
  omega

/-- **The cumulative coset contribution.**  Each element outside the saturated witnesses
contributes at least `#H − ρ` mixed representations landing outside `A' · B'`, and these
contributions add. -/
theorem mixed_sum_ge {X Y A' B' : Finset G} (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hsmall : (A' * B').card + 2 ≤ A'.card + B'.card)
    (hsatA : ∀ z ∈ X, z ∈ A' * mulStab (A' * B') → z ∈ A')
    (hsatB : ∀ z ∈ Y, z ∈ B' * mulStab (A' * B') → z ∈ B') :
    defect X A' Y B' * ((mulStab (A' * B')).card - holes (mulStab (A' * B')) A' B')
      ≤ ∑ c ∈ Finset.univ \ (A' * B'), (rep (X \ A') B' c + rep A' (Y \ B') c) := by
  classical
  set H := mulStab (A' * B') with hHdef
  have hrho : holes H A' B' = ((A' * H) \ A').card + ((B' * H) \ B').card := rfl
  have hAsum : (X \ A').card * (H.card - holes H A' B')
      ≤ ∑ c ∈ Finset.univ \ (A' * B'), rep (X \ A') B' c := by
    rw [sum_rep_eq_sum_card_filter]
    calc (X \ A').card * (H.card - holes H A' B')
        = ∑ _a ∈ X \ A', (H.card - holes H A' B') := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ X \ A', (B'.filter (fun b => a * b ∈ Finset.univ \ (A' * B'))).card := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          rw [Finset.mem_sdiff] at ha
          have hcos := card_mulStab_le_filter_add_holes' hB'ne hsmall ha.1 ha.2 hsatA
          rw [← hHdef] at hcos
          have hfeq : (B'.filter (fun b => a * b ∈ Finset.univ \ (A' * B'))).card
              = (B'.filter (fun b => a * b ∉ A' * B')).card := by
            congr 1
            apply Finset.filter_congr
            intro b _
            simp
          rw [hfeq, hrho]
          omega
  have hBsum : (Y \ B').card * (H.card - holes H A' B')
      ≤ ∑ c ∈ Finset.univ \ (A' * B'), rep A' (Y \ B') c := by
    rw [sum_rep_eq_sum_card_filter']
    calc (Y \ B').card * (H.card - holes H A' B')
        = ∑ _b ∈ Y \ B', (H.card - holes H A' B') := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ b ∈ Y \ B', (A'.filter (fun a => a * b ∈ Finset.univ \ (A' * B'))).card := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          rw [Finset.mem_sdiff] at hb
          have hBA : B' * A' = A' * B' := mul_comm B' A'
          have hsatB' : ∀ z ∈ Y, z ∈ B' * mulStab (B' * A') → z ∈ B' := by
            intro z hz hmem
            rw [hBA] at hmem
            exact hsatB z hz hmem
          have hsmall' : (B' * A').card + 2 ≤ B'.card + A'.card := by
            rw [hBA]; omega
          have hcos := card_mulStab_le_filter_add_holes' hA'ne hsmall' hb.1 hb.2 hsatB'
          rw [hBA, ← hHdef] at hcos
          have hfeq : (A'.filter (fun a => a * b ∈ Finset.univ \ (A' * B'))).card
              = (A'.filter (fun a => b * a ∉ A' * B')).card := by
            congr 1
            apply Finset.filter_congr
            intro a _
            simp [mul_comm b a]
          rw [hfeq, hrho]
          omega
  rw [Finset.sum_add_distrib, defect, Nat.add_mul]
  omega

end GaloisForLFunctions.HTGeometry.AddComb
