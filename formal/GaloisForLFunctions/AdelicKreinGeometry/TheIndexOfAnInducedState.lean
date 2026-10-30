import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank
import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula
import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerSuccessorForcesTheHeckeWeight

/-!
# The index of an induced state

A Hermitian function `ψ` on a subgroup `H ≤ G` has two canonical extensions to `G`.

* The **blind extension** `ψ ∘ r` along a retraction `r : G →* H`. It keeps the index:
  `κ(ψ ∘ r) = κ(ψ)` (`negIndex_comp_retraction`), and no extension has smaller index
  (`negIndex_le_of_extension`). Pullback along any surjective homomorphism keeps the index
  (`negIndex_comp_of_surjective`).
* The **regular extension** by zero off `H`. Its index is the **induction formula**
  (`negIndex_extendFromSubgroup`):

  `κ(ext₀ ψ) = [G : H] · κ(ψ)`,  with `[G : H] = ENat.card (G ⧸ H)`.

  Every left coset carries its own copy of the witnesses of `ψ`, and copies in distinct cosets
  are orthogonal (`card_mul_le_negIndex_of_orthogonal_translates`); conversely the squares that
  pay `ψ` pay `ext₀ ψ` once per coset (`negIndex_extendFromSubgroup_le`).

In the positive theory the two extensions are equally good: extension by zero is positive
(`ArithmeticPositiveDuality.isPosDefOnGroup_extendFromSubgroup`), and the coordinates off `H` are
free. In the indefinite theory they are not: off an infinite-index subgroup the regular
extension of a state with one negative square has infinitely many
(`negIndex_extendFromSubgroup_eq_top`). Freeing the successor costs the index once per coset.

The two languages of positivity agree (`isPosDefKernel_iff_isPosDefOnGroup`).
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality (IsPosDefOnGroup extendFromSubgroup
  leftCosetRep cosetPart isPosDefOnGroup_extendFromSubgroup)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {G : Type*} [Group G]

/-! ### Positive definiteness in the two languages -/

/-- The Gram form of a Hermitian kernel is real. -/
theorem conj_gramForm {k : G → ℂ} (hk : IsHermKernel k) {ι : Type*} [Fintype ι] (x : ι → G)
    (c : ι → ℂ) :
    conj (∑ a, ∑ b, conj (c a) * k ((x a)⁻¹ * x b) * c b) =
      ∑ a, ∑ b, conj (c a) * k ((x a)⁻¹ * x b) * c b := by
  simp only [map_sum, map_mul, conj_conj]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  rw [← hk, mul_inv_rev, inv_inv]
  ring

/-- A kernel is positive definite in the Krein–Toeplitz sense iff it is positive definite on the
group in the sense of `ArithmeticPositiveDuality`. -/
theorem isPosDefKernel_iff_isPosDefOnGroup {k : G → ℂ} :
    IsPosDefKernel k ↔ IsPosDefOnGroup k := by
  constructor
  · rintro ⟨hk, hq⟩ N x c
    refine ⟨hermQuad (gram k x) c, hq N x c, ?_⟩
    rw [hermQuad_gram]
    simp only [Complex.star_def]
    exact (Complex.conj_eq_iff_re.mp (conj_gramForm hk x c)).symm
  · intro h
    refine ⟨fun u => ArithmeticPositiveDuality.IsPosDefOnGroup.map_inv h u, fun N x c => ?_⟩
    obtain ⟨r, hr, hf⟩ := h N x c
    rw [hermQuad_gram]
    simp only [Complex.star_def] at hf
    rw [hf, Complex.ofReal_re]
    exact hr

/-! ### Pullbacks keep the index -/

/-- **Pullback along a surjective homomorphism keeps the index.** -/
theorem negIndex_comp_of_surjective {Q : Type*} [Group Q] (ψ : Q → ℂ) (σ : G →* Q)
    (hσ : Function.Surjective σ) : negIndex (ψ ∘ σ) = negIndex ψ := by
  refine le_antisymm (negIndex_comp_le ψ σ) (negIndex_le_iff.mpr fun n y => ?_)
  choose x hx using fun a => hσ (y a)
  have e : gram ψ y = gram (ψ ∘ σ) x := by
    ext a b
    simp [gram, map_mul, map_inv, hx]
  rw [e]
  exact hermNegIndex_gram_le_negIndex _ _

/-- No extension has smaller index than the function it extends. -/
theorem negIndex_le_of_extension {H : Subgroup G} {ψ : H → ℂ} {φ : G → ℂ}
    (hφ : ∀ h : H, φ h = ψ h) : negIndex ψ ≤ negIndex φ := by
  have e : φ ∘ H.subtype = ψ := funext hφ
  rw [← e]
  exact negIndex_comp_le φ H.subtype

/-- **The blind extension has the least index.** Along a retraction `r : G →* H` the extension
`ψ ∘ r` restricts to `ψ` and has index exactly `κ(ψ)`. -/
theorem negIndex_comp_retraction {H : Subgroup G} (ψ : H → ℂ) (r : G →* H)
    (hr : ∀ h : H, r h = h) : (∀ h : H, (ψ ∘ r) h = ψ h) ∧ negIndex (ψ ∘ r) = negIndex ψ :=
  ⟨fun h => by simp [hr], negIndex_comp_of_surjective ψ r fun h => ⟨h, hr h⟩⟩

/-! ### Orthogonal copies of a negative subspace -/

/-- **Orthogonal translates multiply a whole negative subspace.** If the translates `g_j x` of a
family are mutually `k`-orthogonal, each carries a copy of the negative squares of `x`. -/
theorem card_mul_le_negIndex_of_orthogonal_translates {k : G → ℂ} {ι J : Type*} [Fintype ι]
    [Fintype J] [DecidableEq J] (x : ι → G) (g : J → G)
    (horth : ∀ j j', j ≠ j' → ∀ a b, k ((g j * x a)⁻¹ * (g j' * x b)) = 0) :
    ((Fintype.card J * hermNegIndex (gram k x) : ℕ) : ℕ∞) ≤ negIndex k := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-gram k x)
  set r := Module.finrank ℂ W
  have hr : hermNegIndex (gram k x) = r := hrank.symm
  set bW := Module.finBasis ℂ W
  set y : J × ι → G := fun p => g p.1 * x p.2
  -- the form of the translated family is the sum of the block forms
  have key : ∀ w : J → ι → ℂ, hermQuad (gram k y) (fun p => w p.1 p.2) =
      ∑ j, hermQuad (gram k x) (w j) := by
    intro w
    simp only [hermQuad_gram]
    rw [← Complex.re_sum]
    congr 1
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun j _ => sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
    · refine sum_congr rfl fun b _ => ?_
      simp only [y, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    · intro j' _ hj'
      refine sum_eq_zero fun b _ => ?_
      simp only [y]
      rw [horth j j' (Ne.symm hj') a b, mul_zero, zero_mul]
    · exact fun h => absurd (mem_univ j) h
  -- the block vectors of a coefficient array
  set blk : (J × Fin r → ℂ) → J → W := fun β j => ∑ i, β (j, i) • bW i
  have hblk : ∀ β j a, ((blk β j : W) : ι → ℂ) a = ∑ i, β (j, i) * ((bW i : W) : ι → ℂ) a :=
    fun β j a => by simp [blk, Finset.sum_apply]
  let L : (J × Fin r → ℂ) →ₗ[ℂ] (J × ι → ℂ) :=
    { toFun := fun β p => ∑ i, β (p.1, i) * ((bW i : W) : ι → ℂ) p.2
      map_add' := fun β β' => funext fun p => by simp [add_mul, sum_add_distrib]
      map_smul' := fun t β => funext fun p => by simp [mul_assoc, mul_sum] }
  have hL : ∀ β, L β = fun p => ((blk β p.1 : W) : ι → ℂ) p.2 :=
    fun β => funext fun p => (hblk β p.1 p.2).symm
  have hnonpos : ∀ w : W, hermQuad (gram k x) w ≤ 0 := fun w => by
    by_cases hw : (w : ι → ℂ) = 0
    · rw [hw]; simp [hermQuad]
    · have := hW w w.2 hw
      rw [hermQuad_neg] at this
      linarith
  have hneg : ∀ β, β ≠ 0 → hermQuad (gram k y) (L β) < 0 := by
    intro β hβ
    obtain ⟨⟨j, i⟩, hji⟩ : ∃ p, β p ≠ 0 := by
      by_contra h
      push Not at h
      exact hβ (funext h)
    have hj : ((blk β j : W) : ι → ℂ) ≠ 0 := by
      intro h0
      have h0' : blk β j = 0 := Subtype.ext h0
      exact hji (Fintype.linearIndependent_iff.mp bW.linearIndependent (fun i => β (j, i)) h0' i)
    have hjneg : hermQuad (gram k x) (blk β j) < 0 := by
      have := hW _ (blk β j).2 hj
      rw [hermQuad_neg] at this
      linarith
    rw [hL, key fun j => (blk β j : ι → ℂ)]
    calc ∑ j', hermQuad (gram k x) (blk β j')
        < ∑ _j' : J, (0 : ℝ) :=
          Finset.sum_lt_sum (fun j' _ => hnonpos _) ⟨j, mem_univ _, hjneg⟩
      _ = 0 := by simp
  have h := card_le_hermNegIndex_of_forall_neg (gram k y) L hneg
  rw [Fintype.card_prod, Fintype.card_fin] at h
  rw [hr]
  exact (Nat.cast_le.mpr h).trans (hermNegIndex_gram_le_negIndex k y)

/-! ### The regular extension -/

omit [Group G] in
theorem extendFromSubgroup_subtype {G : Type*} [Group G] {H : Subgroup G} (ψ : H → ℂ) (h : H) :
    extendFromSubgroup H ψ h = ψ h := by
  simp [extendFromSubgroup]

theorem IsHermKernel.extendFromSubgroup {H : Subgroup G} {ψ : H → ℂ} (hψ : IsHermKernel ψ) :
    IsHermKernel (extendFromSubgroup H ψ) := fun g => by
  by_cases hg : g ∈ H
  · have hg' : g⁻¹ ∈ H := H.inv_mem hg
    simp only [ArithmeticPositiveDuality.extendFromSubgroup, dif_pos hg, dif_pos hg']
    rw [← hψ ⟨g, hg⟩]
    rfl
  · have hg' : g⁻¹ ∉ H := fun h => hg (by simpa using H.inv_mem h)
    simp [ArithmeticPositiveDuality.extendFromSubgroup, dif_neg hg, dif_neg hg']

/-- **Every coset carries a copy of the witnesses.** For any finite set `s` of left cosets of `H`
and any family `x` in `H`, the regular extension has at least `|s|` copies of the negative squares
of `ψ` on `x`. -/
theorem card_mul_le_negIndex_extendFromSubgroup {H : Subgroup G} (ψ : H → ℂ)
    (s : Finset (G ⧸ H)) {ι : Type*} [Fintype ι] (x : ι → H) :
    ((s.card * hermNegIndex (gram ψ x) : ℕ) : ℕ∞) ≤ negIndex (extendFromSubgroup H ψ) := by
  classical
  have hgram : gram (extendFromSubgroup H ψ) (fun a => (x a : G)) = gram ψ x := by
    ext a b
    have hmem : ((x a : G))⁻¹ * (x b : G) ∈ H := H.mul_mem (H.inv_mem (x a).2) (x b).2
    simp only [gram, ArithmeticPositiveDuality.extendFromSubgroup, dif_pos hmem]
    congr 1
  have h := card_mul_le_negIndex_of_orthogonal_translates (k := extendFromSubgroup H ψ)
    (J := s) (fun a => (x a : G)) (fun j => (j : G ⧸ H).out) fun j j' hjj' a b => by
      have hnot : ((j : G ⧸ H).out * (x a : G))⁻¹ * ((j' : G ⧸ H).out * (x b : G)) ∉ H := by
        intro hmem
        apply hjj'
        have e : (x a : G) * (((j : G ⧸ H).out * (x a : G))⁻¹ *
            ((j' : G ⧸ H).out * (x b : G))) * (x b : G)⁻¹ =
            ((j : G ⧸ H).out)⁻¹ * (j' : G ⧸ H).out := by group
        have hj : ((j : G ⧸ H).out)⁻¹ * (j' : G ⧸ H).out ∈ H := by
          rw [← e]
          exact H.mul_mem (H.mul_mem (x a).2 hmem) (H.inv_mem (x b).2)
        apply Subtype.ext
        rw [← QuotientGroup.out_eq' (j : G ⧸ H), ← QuotientGroup.out_eq' (j' : G ⧸ H)]
        exact QuotientGroup.eq.mpr hj
      simp only [ArithmeticPositiveDuality.extendFromSubgroup, dif_neg hnot]
  rwa [hgram, Fintype.card_coe] at h

/-- The Gram form of the regular extension splits into one Gram form of `ψ` per coset. -/
theorem hermQuad_gram_extendFromSubgroup {H : Subgroup G} [Fintype (G ⧸ H)]
    [DecidableEq (G ⧸ H)] (ψ : H → ℂ)
    {n : ℕ} (x : Fin n → G) (c : Fin n → ℂ) :
    hermQuad (gram (extendFromSubgroup H ψ) x) c =
      ∑ ρ : G ⧸ H, hermQuad (gram ψ fun a => cosetPart H (x a))
        (fun a => if (x a : G ⧸ H) = ρ then c a else 0) := by
  classical
  set c' : G ⧸ H → Fin n → ℂ := fun ρ a => if (x a : G ⧸ H) = ρ then c a else 0
  have hsplit : ∀ a b, conj (c a) * extendFromSubgroup H ψ ((x a)⁻¹ * x b) * c b =
      ∑ ρ : G ⧸ H, conj (c' ρ a) * ψ ((cosetPart H (x a))⁻¹ * cosetPart H (x b)) * c' ρ b := by
    intro a b
    by_cases hab : (x a : G ⧸ H) = (x b : G ⧸ H)
    · have hmem : (x a)⁻¹ * x b ∈ H := QuotientGroup.eq.mp hab
      have hrep : leftCosetRep H (x a) = leftCosetRep H (x b) := by
        unfold leftCosetRep; rw [hab]
      have hpart : ((cosetPart H (x a))⁻¹ * cosetPart H (x b) : H) = ⟨(x a)⁻¹ * x b, hmem⟩ := by
        ext
        simp only [cosetPart, Subgroup.coe_mul, Subgroup.coe_inv, hrep, mul_inv_rev, inv_inv]
        group
      rw [Finset.sum_eq_single (x a : G ⧸ H)]
      · simp only [c', if_pos rfl, if_pos hab.symm, hpart,
          ArithmeticPositiveDuality.extendFromSubgroup, dif_pos hmem]
      · intro ρ _ hρ
        simp only [c', if_neg (Ne.symm hρ), map_zero, zero_mul]
      · exact fun h => absurd (mem_univ _) h
    · have hnot : (x a)⁻¹ * x b ∉ H := fun h => hab (QuotientGroup.eq.mpr h)
      rw [ArithmeticPositiveDuality.extendFromSubgroup, dif_neg hnot, mul_zero, zero_mul]
      refine (Finset.sum_eq_zero fun ρ _ => ?_).symm
      simp only [c']
      by_cases h1 : (x a : G ⧸ H) = ρ
      · have h2 : ¬ (x b : G ⧸ H) = ρ := fun h2 => hab (h1.trans h2.symm)
        simp only [if_neg h2, mul_zero]
      · simp only [if_neg h1, map_zero, zero_mul]
  simp only [hermQuad_gram]
  rw [← Complex.re_sum]
  congr 1
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

/-- **The squares that pay `ψ` pay the regular extension once per coset.** -/
theorem negIndex_extendFromSubgroup_le {H : Subgroup G} [H.FiniteIndex] {ψ : H → ℂ}
    (hψ : IsHermKernel ψ) {m : ℕ} (hm : negIndex ψ ≤ m) :
    negIndex (extendFromSubgroup H ψ) ≤ (H.index * m : ℕ) := by
  classical
  obtain ⟨φ, hφ⟩ := (negIndex_le_iff_exists_rank hψ m).mp hm
  letI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  set e := Fintype.equivFin ((G ⧸ H) × Fin m)
  set Φ : (G ⧸ H) × Fin m → G → ℂ := fun p g =>
    if (g : G ⧸ H) = p.1 then φ p.2 (cosetPart H g) else 0
  have hcard : Fintype.card ((G ⧸ H) × Fin m) = H.index * m := by
    rw [Fintype.card_prod, Fintype.card_fin, Subgroup.index, Nat.card_eq_fintype_card]
  rw [← hcard]
  refine negIndex_le_of_rank (fun l => Φ (e.symm l)) fun n x c => ?_
  set c' : G ⧸ H → Fin n → ℂ := fun ρ a => if (x a : G ⧸ H) = ρ then c a else 0
  have hsq : ∑ l, normSq (∑ a, c a * Φ (e.symm l) (x a)) =
      ∑ ρ : G ⧸ H, ∑ i, normSq (∑ a, c' ρ a * φ i (cosetPart H (x a))) := by
    rw [e.symm.sum_comp (fun p => normSq (∑ a, c a * Φ p (x a))), Fintype.sum_prod_type]
    refine sum_congr rfl fun ρ _ => sum_congr rfl fun i _ => ?_
    congr 1
    refine sum_congr rfl fun a _ => ?_
    simp only [Φ, c']
    split_ifs <;> simp
  rw [hermQuad_gram_extendFromSubgroup, hsq, ← Finset.sum_add_distrib]
  exact Finset.sum_nonneg fun ρ _ => hφ n (fun a => cosetPart H (x a)) (c' ρ)

/-- **The induction formula.** The regular extension of a Hermitian function on a subgroup has
index `[G : H] · κ(ψ)`. -/
theorem negIndex_extendFromSubgroup {H : Subgroup G} {ψ : H → ℂ} (hψ : IsHermKernel ψ) :
    negIndex (extendFromSubgroup H ψ) = ENat.card (G ⧸ H) * negIndex ψ := by
  classical
  rcases eq_or_ne (negIndex ψ) 0 with h0 | h0
  · rw [h0, mul_zero]
    have hpd : IsPosDefKernel ψ := (isPosDefKernel_iff hψ).mpr h0
    exact (isPosDefKernel_iff_isPosDefOnGroup.mpr (isPosDefOnGroup_extendFromSubgroup
      (isPosDefKernel_iff_isPosDefOnGroup.mp hpd))).negIndex_eq_zero
  have hres : negIndex ψ ≤ negIndex (extendFromSubgroup H ψ) :=
    negIndex_le_of_extension (extendFromSubgroup_subtype ψ)
  -- a lower bound for every finite set of cosets
  have hlow : ∀ s : Finset (G ⧸ H),
      (s.card : ℕ∞) * negIndex ψ ≤ negIndex (extendFromSubgroup H ψ) := by
    intro s
    rcases eq_or_ne (negIndex ψ) ⊤ with htop | htop
    · have htop' : negIndex (extendFromSubgroup H ψ) = ⊤ := top_le_iff.mp (htop ▸ hres)
      rw [htop']
      exact le_top
    · obtain ⟨n, x, hx⟩ := exists_hermNegIndex_gram_eq_negIndex (lt_top_iff_ne_top.mpr htop)
      rw [← hx]
      exact_mod_cast card_mul_le_negIndex_extendFromSubgroup ψ s x
  by_cases hfin : Finite (G ⧸ H)
  · haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    letI : Fintype (G ⧸ H) := Fintype.ofFinite _
    have hcardE : ENat.card (G ⧸ H) = (H.index : ℕ∞) := by
      rw [ENat.card_eq_coe_natCard, Subgroup.index]
    rw [hcardE]
    refine le_antisymm ?_ ?_
    · rcases eq_or_ne (negIndex ψ) ⊤ with htop | htop
      · rw [htop, ENat.mul_top (by exact_mod_cast H.index_ne_zero_of_finite)]
        exact le_top
      · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
        rw [← hm]
        exact_mod_cast negIndex_extendFromSubgroup_le hψ hm.ge
    · have := hlow Finset.univ
      rwa [Finset.card_univ, Fintype.card_eq_nat_card, ← Subgroup.index] at this
  · haveI : Infinite (G ⧸ H) := not_finite_iff_infinite.mp hfin
    rw [ENat.card_eq_top_of_infinite, ENat.top_mul h0]
    refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq (G ⧸ H) n
    have h1 : (1 : ℕ∞) ≤ negIndex ψ := ENat.one_le_iff_ne_zero.mpr h0
    calc (n : ℕ∞) = (s.card : ℕ∞) * 1 := by rw [hs, mul_one]
      _ ≤ (s.card : ℕ∞) * negIndex ψ := mul_le_mul_left' h1 _
      _ ≤ _ := hlow s

/-- **Freeing the successor costs the index once per coset.** Off a subgroup of infinite index,
the regular extension of a non-positive Hermitian function has infinitely many negative squares. -/
theorem negIndex_extendFromSubgroup_eq_top {H : Subgroup G} (hH : Infinite (G ⧸ H))
    {ψ : H → ℂ} (hψ : IsHermKernel ψ) (h0 : negIndex ψ ≠ 0) :
    negIndex (extendFromSubgroup H ψ) = ⊤ := by
  rw [negIndex_extendFromSubgroup hψ, ENat.card_eq_top_of_infinite, ENat.top_mul h0]

end GaloisForLFunctions.AdelicKreinGeometry
