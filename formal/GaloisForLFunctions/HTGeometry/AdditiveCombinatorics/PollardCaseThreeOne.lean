import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardSidon
import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardQubal

/-!
# The combinatorial core of Grynkiewicz's CASE 3.1

In CASE 3.1 of Grynkiewicz's STEP 3 the parameter is `t = 2`, so the maximal Dyson small part
has at most one element.  This file assembles the four combinatorial consequences that the case
needs, all of them for the set `T = dysonFull A B = {y : y · B ⊆ A}` of full translations:

* `card_uniqueExpr_le_of_right` — if no `b ∈ B` admits two unique-expression products then the
  unique-expression part of `A · B` has at most `#B` elements, so `#(A · B) ≤ #(A ·_2 B) + #B`;
* `dysonFull_mul_eq_of_uniqueExpr` — the same hypothesis on the left forces `T · B = A`;
* `sidon_of_dysonFull_mul_eq` — then `B ·_2 B⁻¹` stabilises `T`, hence `A`, so a trivial
  stabiliser makes `B` a Sidon set;
* `card_dysonFull_add_card_mul_self_le` — and `#T + #(B · B) ≤ #(A · B) + 1` unless every element
  of `A · B` is `2`-representable.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- The set of elements of `A · B` with exactly one representation. -/
def uniqueExpr (A B : Finset G) : Finset G := univ.filter (fun c => rep A B c = 1)

theorem mem_uniqueExpr {A B : Finset G} {c : G} : c ∈ uniqueExpr A B ↔ rep A B c = 1 := by
  simp [uniqueExpr]

/-- `A · B` is the disjoint union of its `2`-representable part and its unique-expression part. -/
theorem card_mul_le_card_repSet_two_add (A B : Finset G) :
    (A * B).card ≤ (repSet A B 2).card + (uniqueExpr A B).card := by
  classical
  have hsub : A * B ⊆ repSet A B 2 ∪ uniqueExpr A B := by
    intro c hc
    have h1 : 1 ≤ rep A B c := (rep_pos_iff_mem_mul A B c).2 hc
    rcases Nat.lt_or_ge (rep A B c) 2 with h | h
    · exact Finset.mem_union_right _ (mem_uniqueExpr.2 (by omega))
    · exact Finset.mem_union_left _ (by simp [repSet, h])
  calc (A * B).card ≤ (repSet A B 2 ∪ uniqueExpr A B).card := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _

/-- **Counting unique-expression elements by their right factor.**  If for every `b ∈ B` at most
one element of `A · b` has a unique representation, then `#(A ·_1 B) ≤ #(A ·_2 B) + #B`. -/
theorem card_uniqueExpr_le_of_right {A B : Finset G}
    (hue : ∀ b ∈ B, (A.filter (fun a => rep A B (a * b) = 1)).card ≤ 1) :
    (uniqueExpr A B).card ≤ B.card := by
  classical
  set P : Finset (G × G) := (A ×ˢ B).filter (fun p => rep A B (p.1 * p.2) = 1) with hPdef
  have hsurj : Set.SurjOn (fun p : G × G => p.1 * p.2) (P : Set (G × G))
      (uniqueExpr A B : Set G) := by
    intro c hc
    rw [Finset.mem_coe, mem_uniqueExpr] at hc
    have : c ∈ A * B := (rep_pos_iff_mem_mul A B c).1 (by omega)
    obtain ⟨a, ha, b, hb, hab⟩ := mem_mul.1 this
    refine ⟨(a, b), ?_, hab⟩
    simp only [hPdef, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product]
    exact ⟨⟨ha, hb⟩, by rw [hab]; exact hc⟩
  have h1 : (uniqueExpr A B).card ≤ P.card := Finset.card_le_card_of_surjOn _ hsurj
  have h2 : P.card = ∑ b ∈ B, (A.filter (fun a => rep A B (a * b) = 1)).card := by
    rw [hPdef, Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => (Finset.card_filter _ _).symm)
  calc (uniqueExpr A B).card ≤ P.card := h1
    _ = ∑ b ∈ B, (A.filter (fun a => rep A B (a * b) = 1)).card := h2
    _ ≤ ∑ _b ∈ B, 1 := Finset.sum_le_sum hue
    _ = B.card := by simp

/-- **Every product `T · B` exhausts `A`.**  If the maximal Dyson small part has at most one
element and no element of `A` admits two unique-expression products, then the full translations
`T = {y : y · B ⊆ A}` already cover `A`. -/
theorem dysonFull_mul_eq_of_uniqueExpr {A B : Finset G} {x₀ : G}
    (hk : (dysonSmall A B x₀).card + 1 ≤ 2)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B x₀).card)
    (hB2 : 2 ≤ B.card)
    (hueA : ∀ a ∈ A, (B.filter (fun b => rep A B (a * b) = 1)).card ≤ 1) :
    dysonFull A B * B = A := by
  classical
  refine Subset.antisymm (dysonFull_mul_subset A B) (fun a ha => ?_)
  by_contra hcon
  -- every product `a · b` is then a unique-expression element
  have hall : ∀ b ∈ B, rep A B (a * b) = 1 := by
    intro b hb
    have hge : 1 ≤ rep A B (a * b) :=
      (rep_pos_iff_mem_mul A B (a * b)).2 (Finset.mul_mem_mul ha hb)
    by_contra hne
    have h2 : 1 < rep A B (a * b) := by omega
    rw [rep] at h2
    have hmem : (a, b) ∈ (A ×ˢ B).filter (fun p => p.1 * p.2 = a * b) := by
      rw [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ha, hb⟩, rfl⟩
    obtain ⟨p, hp, hpne⟩ := Finset.exists_mem_ne h2 (a, b)
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hpeq⟩ := hp
    have hb' : p.2 ≠ b := by
      intro h
      have h1 : p.1 * b = a * b := by rw [← h, hpeq, h]
      exact hpne (Prod.ext (mul_right_cancel h1) h)
    have ha' : p.1 ≠ a := by
      intro h
      have h1 : a * p.2 = a * b := by rw [← h, hpeq, h]
      exact hb' (mul_left_cancel h1)
    -- the translate by `a · p.2⁻¹` meets `A` in the two points `a` and `p.1`
    have hz1 : a ∈ dysonSmall A B (a * p.2⁻¹) := by
      refine Finset.mem_inter.2 ⟨Finset.mem_smul_finset.2 ⟨p.2, hp2, ?_⟩, ha⟩
      simp [smul_eq_mul, inv_mul_cancel_right]
    have hz2 : p.1 ∈ dysonSmall A B (a * p.2⁻¹) := by
      refine Finset.mem_inter.2 ⟨Finset.mem_smul_finset.2 ⟨b, hb, ?_⟩, hp1⟩
      simp only [smul_eq_mul]
      rw [mul_assoc, mul_comm p.2⁻¹ b, ← mul_assoc, ← hpeq, mul_inv_cancel_right]
    have hcard : 2 ≤ (dysonSmall A B (a * p.2⁻¹)).card :=
      Finset.one_lt_card.2 ⟨a, hz1, p.1, hz2, fun h => ha' h.symm⟩
    have hT : a * p.2⁻¹ ∈ dysonFull A B := mem_dysonFull_of_card_ge hmax hk hcard
    exact hcon (mem_mul.2 ⟨a * p.2⁻¹, hT, p.2, hp2, by rw [inv_mul_cancel_right]⟩)
  have hfilter : B.filter (fun b => rep A B (a * b) = 1) = B :=
    Finset.filter_true_of_mem hall
  have := hueA a ha
  rw [hfilter] at this
  omega

/-- **The set of full translations is `B ·_2 B⁻¹`-periodic.**  Consequently, when `A` has trivial
stabiliser and is covered by `T · B`, the set `B` is a Sidon set. -/
theorem sidon_of_dysonFull_mul_eq {A B : Finset G} {x₀ : G}
    (hk : (dysonSmall A B x₀).card + 1 ≤ 2)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B x₀).card)
    (hTB : dysonFull A B * B = A)
    (hstab : (mulStab A).card ≤ 1) :
    ∀ y : G, 2 ≤ rep B B⁻¹ y → y = 1 := by
  classical
  intro y hy
  rw [rep] at hy
  set S : Finset (G × G) := (B ×ˢ B⁻¹).filter (fun p => p.1 * p.2 = y) with hSdef
  obtain ⟨q, hq⟩ := Finset.card_pos.1 (show 0 < S.card by omega)
  obtain ⟨p, hp, hpne⟩ := Finset.exists_mem_ne (show 1 < S.card by omega) q
  rw [hSdef, Finset.mem_filter, Finset.mem_product] at hp hq
  obtain ⟨⟨hp1, hp2⟩, hpeq⟩ := hp
  obtain ⟨⟨hq1, hq2⟩, hqeq⟩ := hq
  rw [Finset.mem_inv'] at hp2 hq2
  have hne : p.1 ≠ q.1 := by
    intro h
    exact hpne (Prod.ext h (by
      have : p.1 * p.2 = p.1 * q.2 := by rw [hpeq, h, hqeq]
      exact mul_left_cancel this))
  -- every full translation is carried into itself by `y`
  have hstep : ∀ z ∈ dysonFull A B, y * z ∈ dysonFull A B := by
    intro z hz
    rw [mem_dysonFull] at hz
    have hmem : ∀ u v : G, u ∈ B → v⁻¹ ∈ B → u * v = y →
        z * u ∈ dysonSmall A B (y * z) := by
      intro u v hu hv huv
      refine Finset.mem_inter.2 ⟨Finset.mem_smul_finset.2 ⟨v⁻¹, hv, ?_⟩, ?_⟩
      · simp only [smul_eq_mul]
        have hcancel : (y * z * v⁻¹) * v = (z * u) * v := by
          rw [inv_mul_cancel_right, mul_assoc, huv, mul_comm z y]
        exact mul_right_cancel hcancel
      · exact hz (Finset.mem_smul_finset.2 ⟨u, hu, rfl⟩)
    have hcard : 2 ≤ (dysonSmall A B (y * z)).card :=
      Finset.one_lt_card.2 ⟨z * p.1, hmem p.1 p.2 hp1 hp2 hpeq,
        z * q.1, hmem q.1 q.2 hq1 hq2 hqeq,
        fun h => hne (mul_left_cancel h)⟩
    exact mem_dysonFull_of_card_ge hmax hk hcard
  have hsub : y • dysonFull A B ⊆ dysonFull A B := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_smul_finset.1 hw
    exact hstep z hz
  have heq : y • dysonFull A B = dysonFull A B :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq (Finset.card_smul_finset y _).symm)
  have hyA : y ∈ mulStab A := by
    rw [mem_mulStab, ← hTB, ← smul_mul_assoc, heq]
  exact Finset.card_le_one.1 hstab y hyA 1 (by simp)

omit [Fintype G] in
/-- Two representations with distinct right factors witness `2 ≤ r_{A,B}(x)`. -/
theorem two_le_rep_of_pair {A B : Finset G} {x u v u' v' : G} (hu : u ∈ A) (hv : v ∈ B)
    (hu' : u' ∈ A) (hv' : v' ∈ B) (h1 : u * v = x) (h2 : u' * v' = x) (hvv : v ≠ v') :
    2 ≤ rep A B x := by
  classical
  rw [rep]
  refine Finset.one_lt_card.2 ⟨(u, v), ?_, (u', v'), ?_, fun h => hvv (congrArg Prod.snd h)⟩
  · rw [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hu, hv⟩, h1⟩
  · rw [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hu', hv'⟩, h2⟩

/-- **The upper bound on the number of full translations.**  If `T · B = A` and `A · B` is not
entirely `2`-representable, then `#T + #(B · B) ≤ #(A · B) + 1`. -/
theorem card_dysonFull_add_card_mul_self_le {A B : Finset G}
    (hTne : (dysonFull A B).Nonempty) (hBne : B.Nonempty)
    (hTB : dysonFull A B * B = A)
    (hAB2 : A * B ≠ repSet A B 2) :
    (dysonFull A B).card + (B * B).card ≤ (A * B).card + 1 := by
  classical
  by_contra hcon
  have hassoc : dysonFull A B * (B * B) = A * B := by rw [← mul_assoc, hTB]
  obtain ⟨b₀, hb₀⟩ := hBne
  have hBB : (B * B).Nonempty := ⟨b₀ * b₀, Finset.mul_mem_mul hb₀ hb₀⟩
  have hkey : ∀ x ∈ A * B, 2 ≤ rep A B x := by
    intro x hx
    have hx' : x ∈ dysonFull A B * (B * B) := by rw [hassoc]; exact hx
    have hprop := card_add_card_le_rep_add_card_mul hTne hBB hx'
    rw [hassoc] at hprop
    have h2 : 2 ≤ rep (dysonFull A B) (B * B) x := by omega
    rw [rep] at h2
    set S : Finset (G × G) :=
      ((dysonFull A B) ×ˢ (B * B)).filter (fun p => p.1 * p.2 = x) with hSdef
    obtain ⟨q, hq⟩ := Finset.card_pos.1 (show 0 < S.card by omega)
    obtain ⟨p, hp, hpne⟩ := Finset.exists_mem_ne (show 1 < S.card by omega) q
    rw [hSdef, Finset.mem_filter, Finset.mem_product] at hp hq
    obtain ⟨⟨hp1, hp2⟩, hpeq⟩ := hp
    obtain ⟨⟨hq1, hq2⟩, hqeq⟩ := hq
    have hzne : p.1 ≠ q.1 := by
      intro h
      refine hpne (Prod.ext h ?_)
      have : p.1 * p.2 = p.1 * q.2 := by rw [hpeq, h, hqeq]
      exact mul_left_cancel this
    obtain ⟨b₁, hb₁, b₂, hb₂, hbeq⟩ := mem_mul.1 hp2
    obtain ⟨c₁, hc₁, c₂, hc₂, hceq⟩ := mem_mul.1 hq2
    have hpA : ∀ b ∈ B, p.1 * b ∈ A := by
      intro b hb
      exact (mem_dysonFull.1 hp1) (Finset.mem_smul_finset.2 ⟨b, hb, rfl⟩)
    have hqA : ∀ b ∈ B, q.1 * b ∈ A := by
      intro b hb
      exact (mem_dysonFull.1 hq1) (Finset.mem_smul_finset.2 ⟨b, hb, rfl⟩)
    by_cases hb : b₁ = b₂
    · by_cases hc : c₁ = c₂
      · -- both products are squares; the two full translations force distinct square roots
        have hbc : b₁ ≠ c₁ := by
          intro h
          apply hzne
          have hb2c2 : b₂ = c₂ := by rw [← hb, h]; exact hc
          have hp2q2 : p.2 = q.2 := by rw [← hbeq, ← hceq, h, hb2c2]
          have : p.1 * p.2 = q.1 * p.2 := by rw [hpeq, hp2q2, hqeq]
          exact mul_right_cancel this
        have hbb : b₁ * b₁ = p.2 := by nth_rewrite 2 [hb]; exact hbeq
        have hcc : c₁ * c₁ = q.2 := by nth_rewrite 2 [hc]; exact hceq
        refine two_le_rep_of_pair (hpA b₁ hb₁) hb₁ (hqA c₁ hc₁) hc₁ ?_ ?_ hbc
        · rw [mul_assoc, hbb]; exact hpeq
        · rw [mul_assoc, hcc]; exact hqeq
      · refine two_le_rep_of_pair (hqA c₁ hc₁) hc₂ (hqA c₂ hc₂) hc₁ ?_ ?_ (fun h => hc h.symm)
        · rw [mul_assoc, hceq]; exact hqeq
        · rw [mul_assoc, mul_comm c₂ c₁, hceq]; exact hqeq
    · refine two_le_rep_of_pair (hpA b₁ hb₁) hb₂ (hpA b₂ hb₂) hb₁ ?_ ?_ (fun h => hb h.symm)
      · rw [mul_assoc, hbeq]; exact hpeq
      · rw [mul_assoc, mul_comm b₂ b₁, hbeq]; exact hpeq
  refine hAB2 (Subset.antisymm (fun x hx => ?_) (fun x hx => ?_))
  · simp only [repSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hkey x hx
  · simp only [repSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact (rep_pos_iff_mem_mul A B x).1 (by omega)

end GaloisForLFunctions.HTGeometry.AddComb
