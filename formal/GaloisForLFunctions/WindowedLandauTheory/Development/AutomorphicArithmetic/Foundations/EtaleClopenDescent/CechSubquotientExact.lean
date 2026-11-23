import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact
import Mathlib.Tactic.LinearCombination

/-! A weighted subquotient splits into augmented complexes indexed by
sets outside the selected coordinates. Reordering each fixed set across
the selected indices produces the sign in the restriction map. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {κ : Type} [LinearOrder κ] {d : ℕ}

/-- The index set of the regular subsequence. -/
def selectedIndices (e : Fin d ↪o κ) : Finset κ := Finset.univ.map e.toEmbedding

private def eps (e : Fin d ↪o κ) (b : Finset κ) (j : Fin d) : ℤ := (-1) ^ (b.filter (· < e j)).card

private def psi (e : Fin d ↪o κ) (b : Finset κ) (L : Finset (Fin d)) : ℤ := ∏ j ∈ L, eps e b j

private def emb (e : Fin d ↪o κ) (b : Finset κ) (L : Finset (Fin d)) : Finset κ := b ∪ L.map e.toEmbedding

private def pre (e : Fin d ↪o κ) (s : Finset κ) : Finset (Fin d) := Finset.univ.filter fun j => e j ∈ s

private theorem eps_sq (e : Fin d ↪o κ) (b : Finset κ) (j : Fin d) : eps e b j * eps e b j = 1 := by
  simp [eps, ← mul_pow]

private lemma psi_sq (e : Fin d ↪o κ) (b : Finset κ) (L : Finset (Fin d)) : psi e b L * psi e b L = 1 := by
  rw [psi, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun j _ => eps_sq e b j

private lemma psi_erase (e : Fin d ↪o κ) (b : Finset κ) {L : Finset (Fin d)} {j : Fin d} (h : j ∈ L) :
    psi e b L = eps e b j * psi e b (L.erase j) :=
  (Finset.mul_prod_erase L _ h).symm

private lemma mem_img (e : Fin d ↪o κ) (x : κ) : x ∈ selectedIndices e ↔ ∃ j, e j = x := by
  simp [selectedIndices]

private lemma disj (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) :
    Disjoint b (L.map e.toEmbedding) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hx'
  exact hb j hx

private lemma sign_emb (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) (j : Fin d) :
    GlobalTheory.cubeSign (emb e b L) (e j) = eps e b j * GlobalTheory.cubeSign L j := by
  have h1 : (emb e b L).filter (· < e j) = b.filter (· < e j) ∪ (L.filter (· < j)).map e.toEmbedding := by
    ext x
    simp only [emb, Finset.mem_filter, Finset.mem_union, Finset.mem_map]
    constructor
    · rintro ⟨h | ⟨i, hi, rfl⟩, hlt⟩
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr ⟨i, ⟨hi, e.lt_iff_lt.1 hlt⟩, rfl⟩
    · rintro (⟨h, hlt⟩ | ⟨i, ⟨hi, hlt⟩, rfl⟩)
      · exact ⟨Or.inl h, hlt⟩
      · exact ⟨Or.inr ⟨i, hi, rfl⟩, e.lt_iff_lt.2 hlt⟩
  have h2 : Disjoint (b.filter (· < e j)) ((L.filter (· < j)).map e.toEmbedding) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (disj e hb _)
  change (-1 : ℤ) ^ ((emb e b L).filter (· < e j)).card =
    eps e b j * (-1 : ℤ) ^ (L.filter (· < j)).card
  rw [h1, Finset.card_union_of_disjoint h2, Finset.card_map, pow_add, eps]

private lemma erase_emb (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) (j : Fin d) :
    (emb e b L).erase (e j) = emb e b (L.erase j) := by
  ext x
  simp only [emb, Finset.mem_erase, Finset.mem_union, Finset.mem_map]
  constructor
  · rintro ⟨hne, h | ⟨i, hi, rfl⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, ⟨fun h => hne (by simp [h]), hi⟩, rfl⟩
  · rintro (h | ⟨i, ⟨hne, hi⟩, rfl⟩)
    · exact ⟨fun h' => hb j (h' ▸ h), Or.inl h⟩
    · exact ⟨fun h => hne (e.injective h), Or.inr ⟨i, hi, rfl⟩⟩

private theorem restrict_weighted_differential {k E : Type} [Field k] [AddCommGroup E] [Module k E]
    (w : κ → Module.End k E) (e : Fin d ↪o κ)
    {b : Finset κ} (hb : ∀ j, e j ∉ b) (f : Finset κ → E) (L : Finset (Fin d)) :
    wd (fun j => w (e j)) (fun L' => psi e b L' • f (emb e b L')) L =
      psi e b L • wd (wOn (selectedIndices e) w) f (emb e b L) := by
  have hz : ∑ i ∈ b, (GlobalTheory.cubeSign (emb e b L) i : ℤ) • wOn (selectedIndices e) w i (f ((emb e b L).erase i)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : i ∉ selectedIndices e := by
      rw [mem_img]
      rintro ⟨j, rfl⟩
      exact hb j hi
    simp [wOn, this]
  rw [wd_apply, wd_apply]
  conv_rhs => rw [show ∑ i ∈ emb e b L, (GlobalTheory.cubeSign (emb e b L) i : ℤ) • wOn (selectedIndices e) w i (f ((emb e b L).erase i)) =
      ∑ i ∈ b, (GlobalTheory.cubeSign (emb e b L) i : ℤ) • wOn (selectedIndices e) w i (f ((emb e b L).erase i)) +
      ∑ i ∈ L.map e.toEmbedding, (GlobalTheory.cubeSign (emb e b L) i : ℤ) • wOn (selectedIndices e) w i (f ((emb e b L).erase i)) from
        Finset.sum_union (disj e hb L)]
  rw [hz, zero_add, Finset.sum_map, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hm : e j ∈ selectedIndices e := (mem_img e _).2 ⟨j, rfl⟩
  simp only [RelEmbedding.coe_toEmbedding, wOn, hm, if_true]
  rw [sign_emb e hb, erase_emb e hb, map_zsmul, smul_smul, smul_smul, psi_erase e b hj]
  congr 1
  have := eps_sq e b j
  linear_combination (-(psi e b (L.erase j) * GlobalTheory.cubeSign L j)) * this

private lemma emb_pre (e : Fin d ↪o κ) (s : Finset κ) : emb e (s \ selectedIndices e) (pre e s) = s := by
  ext x
  simp only [emb, pre, Finset.mem_union, Finset.mem_sdiff, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_img, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro (h | ⟨j, hj, rfl⟩)
    · exact h.1
    · exact hj
  · intro h
    by_cases hx : ∃ j, e j = x
    · obtain ⟨j, rfl⟩ := hx
      exact Or.inr ⟨j, h, rfl⟩
    · exact Or.inl ⟨h, hx⟩

private lemma sdiff_ok (e : Fin d ↪o κ) (s : Finset κ) (j : Fin d) : e j ∉ s \ selectedIndices e := by
  simp [mem_img]

private lemma sdiff_emb (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) :
    emb e b L \ selectedIndices e = b := by
  ext x
  simp only [emb, Finset.mem_sdiff, Finset.mem_union, Finset.mem_map, mem_img, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨h | ⟨j, _, rfl⟩, hn⟩
    · exact h
    · exact absurd ⟨j, rfl⟩ hn
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rintro ⟨j, rfl⟩
    exact hb j h

private lemma pre_emb (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) :
    pre e (emb e b L) = L := by
  ext j
  simp only [emb, pre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding]
  constructor
  · rintro (h | ⟨i, hi, h⟩)
    · exact absurd h (hb j)
    · exact e.injective h ▸ hi
  · exact fun h => Or.inr ⟨j, h, rfl⟩

private lemma card_emb (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) :
    (emb e b L).card = b.card + L.card := by
  rw [emb, Finset.card_union_of_disjoint (disj e hb L), Finset.card_map]

private lemma card_inter (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) :
    (emb e b L ∩ selectedIndices e).card = L.card := by
  have : emb e b L ∩ selectedIndices e = L.map e.toEmbedding := by
    ext x
    simp only [emb, Finset.mem_inter, Finset.mem_union, Finset.mem_map, mem_img, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨h | h, ⟨j, rfl⟩⟩
      · exact absurd h (hb j)
      · exact h
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Or.inr ⟨j, hj, rfl⟩, j, rfl⟩
  rw [this, Finset.card_map]

private theorem exists_level_primitive {k E : Type} [Field k] [AddCommGroup E] [Module k E]
    (M : Submodule k E) (w : κ → Module.End k E) (e : Fin d ↪o κ) {n m : ℤ}
    {c : Finset κ → E} (hc : c ∈ (acx (fun _ => M) w).C n)
    (hL : Lev (selectedIndices e) (· = m) c)
    (hz : wd (wOn (selectedIndices e) w) c = 0)
    (hK : ∀ b : Finset κ, (∀ j, e j ∉ b) →
      (fun L => psi e b L • c (emb e b L)) ∈ (acx (fun _ => M) fun j => w (e j)).Z m →
      (fun L => psi e b L • c (emb e b L)) ∈ (acx (fun _ => M) fun j => w (e j)).B m) :
    ∃ y ∈ (acx (fun _ => M) w).C (n - 1), Lev (selectedIndices e) (· = m - 1) y ∧
      wd (wOn (selectedIndices e) w) y = c := by
  have hcs : ∀ s, (s.card : ℤ) ≠ n → c s = 0 := fun s hs => by
    have := acx_mem_terms_iff.mp hc s
    simpa [hs] using this
  have hcM : ∀ s, c s ∈ M := fun s => by
    have := acx_mem_terms_iff.mp hc s
    split_ifs at this with h
    · exact this
    · rw [(Submodule.mem_bot k).mp this]; exact M.zero_mem

  have hex : ∀ b : Finset κ, ∃ Y ∈ (acx (fun _ => M) fun j => w (e j)).C (m - 1), (∀ j, e j ∉ b) →
      wd (fun j => w (e j)) Y = fun L => psi e b L • c (emb e b L) := by
    intro b
    by_cases hb : ∀ j, e j ∉ b
    · have hcol : (fun L => psi e b L • c (emb e b L)) ∈ (acx (fun _ => M) fun j => w (e j)).Z m := by
        refine ⟨acx_mem_terms_iff.mpr fun L => ?_, ?_⟩
        · by_cases hLm : (L.card : ℤ) = m
          · simp only [hLm, if_true]
            exact zsmul_mem (hcM _) _
          · have : c (emb e b L) = 0 := hL _ (by rwa [card_inter e hb])
            simp [this]
        · have : wd (fun j => w (e j)) (fun L => psi e b L • c (emb e b L)) = 0 := by
            funext L
            rw [restrict_weighted_differential w e hb c L, hz]
            simp
          exact this
      obtain ⟨Y, hY, hYd⟩ := hK b hb hcol
      exact ⟨Y, hY, fun _ => hYd⟩
    · exact ⟨0, Submodule.zero_mem _, fun h => absurd h hb⟩
  choose Y hYC hYd using hex
  have hYz : ∀ b L, (L.card : ℤ) ≠ m - 1 → Y b L = 0 := fun b L hLm => by
    have := acx_mem_terms_iff.mp (hYC b) L
    simpa [hLm] using this
  have hYM : ∀ b L, Y b L ∈ M := fun b L => by
    have := acx_mem_terms_iff.mp (hYC b) L
    split_ifs at this with h
    · exact this
    · rw [(Submodule.mem_bot k).mp this]; exact M.zero_mem
  let y : Finset κ → E := fun s =>
    if ((s \ selectedIndices e).card : ℤ) = n - m then psi e (s \ selectedIndices e) (pre e s) • Y (s \ selectedIndices e) (pre e s) else 0
  have hy : ∀ b (hb : ∀ j, e j ∉ b) L, y (emb e b L) = if (b.card : ℤ) = n - m then psi e b L • Y b L else 0 := by
    intro b hb L
    simp only [y, sdiff_emb e hb, pre_emb e hb]
  refine ⟨y, acx_mem_terms_iff.mpr fun s => ?_, fun s hs => ?_, ?_⟩
  · rw [← emb_pre e s]
    have hb := sdiff_ok e s
    rw [hy _ hb, card_emb e hb]
    split_ifs with h1 h2 h2
    · exact zsmul_mem (hYM _ _) _
    · exact M.zero_mem
    · have : ((pre e s).card : ℤ) ≠ m - 1 := by
        intro h; apply h1; push_cast; omega
      simp [hYz _ _ this]
    · exact Submodule.zero_mem _
  · rw [← emb_pre e s] at hs ⊢
    have hb := sdiff_ok e s
    rw [card_inter e hb] at hs
    rw [hy _ hb, hYz _ _ hs]
    simp
  · funext s
    obtain ⟨b, L, hb, rfl⟩ : ∃ b L, (∀ j, e j ∉ b) ∧ s = emb e b L :=
      ⟨_, _, sdiff_ok e s, (emb_pre e s).symm⟩
    have hk : wd (fun j => w (e j)) (fun L' => psi e b L' • y (emb e b L')) L =
        psi e b L • wd (wOn (selectedIndices e) w) y (emb e b L) := restrict_weighted_differential w e hb y L
    have hcancel : ∀ (L' : Finset (Fin d)) (v : E), psi e b L' • psi e b L' • v = v := fun L' v => by
      rw [smul_smul, psi_sq, one_smul]
    by_cases hn : (b.card : ℤ) = n - m
    · have h1 : (fun L' => psi e b L' • y (emb e b L')) = Y b := by
        funext L'
        rw [hy b hb, if_pos hn, hcancel]
      rw [h1, hYd b hb] at hk
      calc wd (wOn (selectedIndices e) w) y (emb e b L)
          = psi e b L • psi e b L • wd (wOn (selectedIndices e) w) y (emb e b L) := (hcancel _ _).symm
        _ = psi e b L • psi e b L • c (emb e b L) := by rw [← hk]
        _ = c (emb e b L) := hcancel _ _
    · have h1 : (fun L' => psi e b L' • y (emb e b L')) = 0 := by
        funext L'
        rw [hy b hb, if_neg hn]
        simp
      rw [h1, map_zero] at hk
      have h2 : wd (wOn (selectedIndices e) w) y (emb e b L) = 0 := by
        rw [← hcancel L (wd (wOn (selectedIndices e) w) y (emb e b L)), ← hk]
        simp
      rw [h2]
      by_cases hcard : ((emb e b L).card : ℤ) = n
      · have hLm : ¬ (((emb e b L) ∩ selectedIndices e).card : ℤ) = m := by
          rw [card_inter e hb]
          rw [card_emb e hb] at hcard
          intro h
          apply hn
          push_cast at hcard
          omega
        exact (hL _ hLm).symm
      · exact (hcs _ hcard).symm

/-- Exactness below the length of an ordered subsequence gives exactness
for every corresponding level of the filtration of the whole cube. -/
theorem qEx_of_subsequence_exact {k E : Type} [Field k] [AddCommGroup E] [Module k E]
    (M : Submodule k E) (w : κ → Module.End k E) (e : Fin d ↪o κ)
    (hK : ∀ m : ℤ, m < (d : ℤ) →
      (acx (fun _ => M) fun j => w (e j)).Z m ≤ (acx (fun _ => M) fun j => w (e j)).B m) :
    QEx (fun _ => M) w (selectedIndices e) d :=
  fun _ m hm _ hc hL hz => exists_level_primitive M w e hc hL hz fun _ _ hz' => hK m hm hz'

/-- The possible top coefficients of boundaries in the selected cube,
given by the signed sum of the images of its weights. -/
def selectedBoundaryValues {k E : Type} [Field k] [AddCommGroup E] [Module k E]
    (M : Submodule k E) (w : κ → Module.End k E) (e : Fin d ↪o κ) : Submodule k E :=
  ((acx (fun _ => M) fun j => w (e j)).B d).map (LinearMap.proj Finset.univ)

/-- A cochain at the top selected level has a primitive for the
selected differential if each top coefficient is a boundary value. -/
theorem exists_top_primitive_of_selectedBoundaryValues {k E : Type}
    [Field k] [AddCommGroup E] [Module k E]
    (M : Submodule k E) (w : κ → Module.End k E) (e : Fin d ↪o κ)
    (hw : ∀ i j, Commute (w i) (w j)) (hM : ∀ i, M ≤ M.comap (w i))
    {n : ℤ} {c : Finset κ → E} (hc : c ∈ (acx (fun _ => M) w).C n)
    (hL : Lev (selectedIndices e) (· = (d : ℤ)) c)
    (hz : wd (wOn (selectedIndices e) w) c = 0)
    (htop : ∀ s, c s ∈ selectedBoundaryValues M w e) :
    ∃ y ∈ (acx (fun _ => M) w).C (n - 1),
      Lev (selectedIndices e) (· = (d : ℤ) - 1) y ∧
      wd (wOn (selectedIndices e) w) y = c := by
  refine exists_level_primitive M w e hc hL hz fun b _ hcycle => ?_
  let v (L : Finset (Fin d)) := psi e b L • c (emb e b L)
  have hv : v Finset.univ ∈ selectedBoundaryValues M w e :=
    zsmul_mem (htop _) _
  obtain ⟨z, hzB, he⟩ := hv
  change z Finset.univ = v Finset.univ at he
  have hcx := acx_isCx (fun _ => M) (fun j => w (e j)) (fun i j => hw (e i) (e j))
    (fun _ i _ => hM (e i))
  have hzC := (Cx.boundaries_le_cycles hcx (d : ℤ) hzB).1
  suffices v = z by
    change v ∈ _
    rw [this]
    exact hzB
  funext L
  by_cases h : L = Finset.univ
  · exact h.symm ▸ he.symm
  · have hcard : (L.card : ℤ) ≠ (d : ℤ) := by
      have hlt : L.card < Fintype.card (Fin d) := (Finset.card_lt_iff_ne_univ L).mpr h
      rw [Fintype.card_fin] at hlt
      omega
    have hzero (f : Finset (Fin d) → E)
        (hf : f ∈ (acx (fun _ => M) fun j => w (e j)).C (d : ℤ)) : f L = 0 :=
      (Submodule.mem_bot k).mp (by simpa only [if_neg hcard] using acx_mem_terms_iff.mp hf L)
    exact (hzero v hcycle.1).trans (hzero z hzC).symm

end GlobalTheory.WH
