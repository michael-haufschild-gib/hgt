import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import GaloisForLFunctions.HTGeometry.ChainDegenerationCohenMacaulay
import GaloisForLFunctions.HTGeometry.StanleyReisnerCone
import GaloisForLFunctions.HTGeometry.CohenMacaulayLifting

/-!
# A regular local ring is a domain

```text
exists_finset_span_insert_of_ne_zero    a nonzero vector extends to a basis, as a finite set
exists_span_insert_of_notMem_sq         ** an element outside `𝔪²` is part of a minimal generating
                                           set of `𝔪` **
spanFinrank_map_maximalIdeal_succ_le    ** so the quotient by it needs one generator fewer **
```

The first is linear algebra in the cotangent space `𝔪/𝔪²`, transported to `𝔪` by Nakayama in the
form `CotangentSpace.span_image_eq_top_iff`.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Submodule IsLocalRing
open scoped Pointwise

universe u
variable {R : Type u} [CommRing R]

/-- A nonzero vector of a finite-dimensional space belongs to a spanning set of its dimension. -/
theorem exists_finset_span_insert_of_ne_zero {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {v : V} (hv : v ≠ 0) :
    ∃ b : Finset V, v ∈ b ∧ b.card = finrank k V ∧ Submodule.span k (b : Set V) = ⊤ := by
  classical
  have hli : LinearIndepOn k (id : V → V) ({v} : Set V) := by
    rw [linearIndepOn_singleton_iff]
    simpa using hv
  obtain ⟨B, -, hvB, hspan, hBli⟩ := exists_linearIndepOn_id_extension hli (Set.subset_univ _)
  have hsp : Submodule.span k B = ⊤ := by
    rw [eq_top_iff]
    intro y _hy
    exact hspan (Set.mem_univ y)
  have hfin : B.Finite := hBli.linearIndependent.setFinite
  haveI : Fintype B := hfin.fintype
  let bas : Basis B k V := Basis.mk hBli.linearIndependent (by
    simpa [Set.range_id'] using hsp.ge)
  refine ⟨hfin.toFinset, hfin.mem_toFinset.mpr (hvB rfl), ?_, ?_⟩
  · rw [finrank_eq_card_basis bas]
    simp
  · rw [Set.Finite.coe_toFinset]
    exact hsp

variable [IsLocalRing R] [IsNoetherianRing R]

/-- **An element outside `𝔪²` is part of a minimal generating set of `𝔪`.** -/
theorem exists_span_insert_of_notMem_sq {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ (maximalIdeal R) ^ (2 : ℕ)) :
    ∃ s : Finset R, s.card + 1 ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span (insert x (s : Set R)) = maximalIdeal R := by
  classical
  set V := CotangentSpace R
  set v : V := (maximalIdeal R).toCotangent ⟨x, hx⟩ with hv
  have hvne : v ≠ 0 := by
    rw [hv, Ne, Ideal.toCotangent_eq_zero]
    exact hx2
  obtain ⟨b, hvb, hcard, hspan⟩ := exists_finset_span_insert_of_ne_zero (k := ResidueField R) hvne
  -- lift the other basis vectors to `𝔪`
  have hsurj := (maximalIdeal R).toCotangent_surjective
  choose lift hlift using hsurj
  set s : Finset R := (b.erase v).image (fun w => ((lift w : ↥(maximalIdeal R)) : R)) with hs
  have himg : (maximalIdeal R).toCotangent ''
      (insert (⟨x, hx⟩ : ↥(maximalIdeal R))
        ((fun w => lift w) '' ((b.erase v : Finset V) : Set V))) = (b : Set V) := by
    rw [Set.image_insert_eq, Set.image_image]
    have : (fun w => (maximalIdeal R).toCotangent (lift w)) = id := by
      funext w
      exact hlift w
    rw [this, Set.image_id, ← hv]
    ext w
    constructor
    · rintro (rfl | hw)
      · exact hvb
      · exact Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hw))
    · intro hw
      by_cases hwv : w = v
      · exact Or.inl hwv
      · exact Or.inr (by simp [hwv, Finset.mem_coe.mp hw])
  have htop : Submodule.span R
      (insert (⟨x, hx⟩ : ↥(maximalIdeal R))
        ((fun w => lift w) '' ((b.erase v : Finset V) : Set V))) = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff, himg, hspan]
  refine ⟨s, ?_, ?_⟩
  · have h1 : s.card ≤ (b.erase v).card := Finset.card_image_le
    have h2 : (b.erase v).card = b.card - 1 := Finset.card_erase_of_mem hvb
    have h3 : 1 ≤ b.card := Finset.card_pos.mpr ⟨v, hvb⟩
    have h4 : b.card = (maximalIdeal R).spanFinrank := by
      rw [hcard, IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    omega
  · have hcoe : (insert x (s : Set R))
        = Subtype.val '' (insert (⟨x, hx⟩ : ↥(maximalIdeal R))
          ((fun w => lift w) '' ((b.erase v : Finset V) : Set V))) := by
      rw [Set.image_insert_eq, Set.image_image, hs, Finset.coe_image]
    have hmap : Submodule.map (Submodule.subtype (maximalIdeal R))
        (Submodule.span R (insert (⟨x, hx⟩ : ↥(maximalIdeal R))
          ((fun w => lift w) '' ((b.erase v : Finset V) : Set V)))) = maximalIdeal R := by
      rw [htop, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span] at hmap
    rw [hcoe]
    exact hmap

omit [IsLocalRing R] [IsNoetherianRing R] in
theorem annihilator_self_eq_bot [Nontrivial R] : Module.annihilator R R = ⊥ := by
  ext r
  simp only [Module.mem_annihilator, Ideal.mem_bot]
  exact ⟨fun h => by simpa using h 1, fun h m => by simp [h]⟩

/-- **Cutting by an element outside every minimal prime drops the dimension by exactly one.** -/
theorem ringKrullDim_quotient_span_singleton_succ_of_notMem_minimalPrimes {x : R}
    (hn : ∀ p ∈ minimalPrimes R, x ∉ p) (hx : x ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have h : Ideal.span {x} = x • (⊤ : Ideal R) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R h).toRingEquiv,
    ← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  refine Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal ?_ hx
  intro p hp
  exact hn p (by rwa [annihilator_self_eq_bot] at hp)

/-- **The quotient by an element outside `𝔪²` needs one generator fewer.** -/
theorem spanFinrank_map_maximalIdeal_succ_le {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ (maximalIdeal R) ^ (2 : ℕ)) :
    (Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (maximalIdeal R)).spanFinrank + 1
      ≤ (maximalIdeal R).spanFinrank := by
  classical
  obtain ⟨s, hcard, hspan⟩ := exists_span_insert_of_notMem_sq hx hx2
  have hmap : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (maximalIdeal R)
      = Ideal.span ((Ideal.Quotient.mk (Ideal.span {x})) '' (s : Set R)) := by
    have hx0 : (Ideal.Quotient.mk (Ideal.span {x})) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
    rw [← hspan, Ideal.map_span, Set.image_insert_eq, hx0]
    exact Submodule.span_insert_zero
  have hle : (Ideal.span ((Ideal.Quotient.mk (Ideal.span {x})) '' (s : Set R))).spanFinrank
      ≤ ((Ideal.Quotient.mk (Ideal.span {x})) '' (s : Set R)).ncard :=
    Submodule.spanFinrank_span_le_ncard_of_finite (s.finite_toSet.image _)
  have hcard2 : ((Ideal.Quotient.mk (Ideal.span {x})) '' (s : Set R)).ncard ≤ s.card := by
    refine le_trans (Set.ncard_image_le s.finite_toSet) ?_
    simp
  rw [hmap]
  omega

/-- **Cutting a regular local ring by a parameter outside `𝔪²` and outside every minimal prime
leaves a regular local ring.** -/
theorem isRegularLocalRing_quotient_span_singleton {S : Type u} [CommRing S]
    [IsRegularLocalRing S] {x : S}
    (hx : x ∈ maximalIdeal S) (hx2 : x ∉ (maximalIdeal S) ^ (2 : ℕ))
    (hn : ∀ p ∈ minimalPrimes S, x ∉ p) :
    IsRegularLocalRing (S ⧸ Ideal.span {x}) := by
  classical
  have hne : Ideal.span {x} ≠ ⊤ := by
    intro h
    exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ (Ideal.span_le.mpr
      (Set.singleton_subset_iff.mpr hx))))
  haveI : Nontrivial (S ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsLocalRing (S ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hdrop := ringKrullDim_quotient_span_singleton_succ_of_notMem_minimalPrimes hn hx
  have hdim : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) = ringKrullDim S :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hmax : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (maximalIdeal S)
      = maximalIdeal (S ⧸ Ideal.span {x}) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hgen := spanFinrank_map_maximalIdeal_succ_le hx hx2
  rw [hmax] at hgen
  have hpos : 1 ≤ (maximalIdeal S).spanFinrank := by
    by_contra hcon
    have hzero : (maximalIdeal S).spanFinrank = 0 := by omega
    have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp hzero
    apply hx2
    have hx0 : x = 0 := by rw [hbot] at hx; simpa using hx
    rw [hx0]
    exact Submodule.zero_mem _
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  have hle : ((maximalIdeal (S ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞)
      ≤ ringKrullDim (S ⧸ Ideal.span {x}) + ((1 : ℕ) : WithBot ℕ∞) := by
    rw [show ((1 : ℕ) : WithBot ℕ∞) = 1 from by norm_cast, hdrop, ← hdim]
    exact_mod_cast Nat.cast_le.mpr hgen
  exact ENat.WithBot.add_le_add_natCast_right_iff.mp hle

/-- The quotient by a parameter needs exactly one generator fewer. -/
theorem spanFinrank_maximalIdeal_quotient_succ {S : Type u} [CommRing S] [IsRegularLocalRing S]
    {x : S} (hx : x ∈ maximalIdeal S) (hx2 : x ∉ (maximalIdeal S) ^ (2 : ℕ))
    (hn : ∀ p ∈ minimalPrimes S, x ∉ p) :
    (Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (maximalIdeal S)).spanFinrank + 1
      = (maximalIdeal S).spanFinrank := by
  haveI := isRegularLocalRing_quotient_span_singleton hx hx2 hn
  have hmax : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (maximalIdeal S)
      = maximalIdeal (S ⧸ Ideal.span {x}) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hmax]
  have hdrop := ringKrullDim_quotient_span_singleton_succ_of_notMem_minimalPrimes hn hx
  have hreg1 : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) = ringKrullDim S :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hreg2 : ((maximalIdeal (S ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞)
      = ringKrullDim (S ⧸ Ideal.span {x}) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  rw [← hreg2, ← hreg1] at hdrop
  have hc : (((maximalIdeal (S ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞)
      = (((maximalIdeal S).spanFinrank : ℕ) : WithBot ℕ∞) := by
    push_cast
    exact hdrop
  exact Nat.cast_injective (R := WithBot ℕ∞) hc

/-- **A regular local ring is a domain.**  Induction on the number of generators of the maximal
ideal: an element outside `𝔪²` and outside every minimal prime cuts the ring down to a regular local
ring of one dimension less, which is a domain by induction, so the element generates a prime; a
minimal prime inside that principal ideal is then killed by Nakayama. -/
theorem isDomain_of_spanFinrank_maximalIdeal :
    ∀ (n : ℕ) (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → IsDomain S := by
  intro n
  induction n with
  | zero =>
    intro S _ _ hn
    have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp hn
    have hfield : IsField S := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot
    letI := hfield.toField
    infer_instance
  | succ n ih =>
    intro S _ _ hn
    classical
    -- the maximal ideal is not inside its square
    have hjac : maximalIdeal S ≤ Ideal.jacobson ⊥ :=
      le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm
    have hsq : ¬ (maximalIdeal S ≤ (maximalIdeal S) ^ (2 : ℕ)) := by
      intro hle
      have hnak : maximalIdeal S = ⊥ := by
        refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) (maximalIdeal S)
          (IsNoetherian.noetherian _) ?_ hjac
        rwa [smul_eq_mul, ← pow_two]
      rw [hnak] at hn
      simp [Submodule.spanFinrank_bot] at hn
    -- and not inside any minimal prime
    have hmin : ∀ p ∈ minimalPrimes S, ¬ (maximalIdeal S ≤ p) := by
      intro p hp hle
      haveI : p.IsPrime := hp.1.1
      have hpm : p = maximalIdeal S :=
        ((maximalIdeal.isMaximal S).eq_of_le hp.1.1.ne_top hle).symm
      have hzero : (maximalIdeal S).height = 0 := by
        rw [Ideal.height_eq_zero_iff]
        rwa [← hpm]
      have hdim : ringKrullDim S = 0 := by
        rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hzero]
        rfl
      have hreg : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) = ringKrullDim S :=
        IsRegularLocalRing.spanFinrank_maximalIdeal
      rw [hn, hdim] at hreg
      have hcast0 : ((n + 1 : ℕ) : WithBot ℕ∞) = ((0 : ℕ) : WithBot ℕ∞) := by
        push_cast
        exact hreg
      have := Nat.cast_injective (R := WithBot ℕ∞) hcast0
      omega
    -- prime avoidance
    obtain ⟨F, hF⟩ : ∃ F : Finset (Ideal S), (F : Set (Ideal S)) = minimalPrimes S :=
      ⟨(minimalPrimes.finite_of_isNoetherianRing S).toFinset, by simp⟩
    set G : Finset (Ideal S) := insert ((maximalIdeal S) ^ (2 : ℕ)) F with hGdef
    have hprime : ∀ i ∈ G, i ≠ (maximalIdeal S) ^ (2 : ℕ) → i ≠ (maximalIdeal S) ^ (2 : ℕ) → i.IsPrime := by
      intro i hi hne _
      have : i ∈ F := by
        rcases Finset.mem_insert.mp hi with h | h
        · exact absurd h hne
        · exact h
      have : i ∈ minimalPrimes S := by rw [← hF]; exact_mod_cast this
      exact this.1.1
    have hnotsub : ¬ ((maximalIdeal S : Set S) ⊆ ⋃ i ∈ (G : Set (Ideal S)), (i : Set S)) := by
      rw [Ideal.subset_union_prime (f := fun i : Ideal S => i)
        ((maximalIdeal S) ^ (2 : ℕ)) ((maximalIdeal S) ^ (2 : ℕ)) hprime]
      rintro ⟨i, hi, hle⟩
      rcases Finset.mem_insert.mp hi with h | h
      · exact hsq (h ▸ hle)
      · refine hmin i ?_ hle
        rw [← hF]
        exact_mod_cast h
    obtain ⟨x, hxmem, hxnot⟩ := Set.not_subset.mp hnotsub
    have hx2 : x ∉ (maximalIdeal S) ^ (2 : ℕ) := by
      intro h
      exact hxnot (Set.mem_biUnion (by exact_mod_cast Finset.mem_insert_self _ _) h)
    have hxmin : ∀ p ∈ minimalPrimes S, x ∉ p := by
      intro p hp h
      refine hxnot (Set.mem_biUnion ?_ h)
      have : p ∈ F := by rw [← hF] at hp; exact_mod_cast hp
      exact_mod_cast Finset.mem_insert_of_mem this
    -- the quotient is regular local of one dimension less
    haveI := isRegularLocalRing_quotient_span_singleton hxmem hx2 hxmin
    have hne : Ideal.span {x} ≠ ⊤ := by
      intro h
      exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ (Ideal.span_le.mpr
        (Set.singleton_subset_iff.mpr hxmem))))
    have hquotdim : (maximalIdeal (S ⧸ Ideal.span {x})).spanFinrank = n := by
      have hdrop := ringKrullDim_quotient_span_singleton_succ_of_notMem_minimalPrimes hxmin hxmem
      have hreg1 : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) = ringKrullDim S :=
        IsRegularLocalRing.spanFinrank_maximalIdeal
      have hreg2 : ((maximalIdeal (S ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞)
          = ringKrullDim (S ⧸ Ideal.span {x}) :=
        IsRegularLocalRing.spanFinrank_maximalIdeal
      rw [← hreg2] at hdrop
      rw [← hreg1, hn] at hdrop
      have : (((maximalIdeal (S ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞)
          = ((n + 1 : ℕ) : WithBot ℕ∞) := by push_cast; exact hdrop
      have := Nat.cast_injective (R := WithBot ℕ∞) this
      omega
    haveI : IsDomain (S ⧸ Ideal.span {x}) :=
      ih (S ⧸ Ideal.span {x}) hquotdim
    haveI hxprime : (Ideal.span {x}).IsPrime := Ideal.Quotient.isDomain_iff_prime _ |>.mp ‹_›
    -- a minimal prime inside `(x)` is killed by Nakayama
    obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Ideal.span {x}) bot_le
    haveI : p.IsPrime := hp.1.1
    have hxp : x ∉ p := hxmin p hp
    have hpsmul : p ≤ (maximalIdeal S) • p := by
      intro a ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hple ha)
      have hcp : c ∈ p := by
        rcases (‹p.IsPrime›).mem_or_mem (show c * x ∈ p from hc ▸ ha) with h | h
        · exact h
        · exact absurd h hxp
      have : a = x * c := by rw [← hc]; ring
      rw [this, smul_eq_mul]
      exact Ideal.mul_mem_mul hxmem hcp
    have hpbot : p = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) p
        (IsNoetherian.noetherian _) hpsmul hjac
    haveI : (⊥ : Ideal S).IsPrime := hpbot ▸ ‹p.IsPrime›
    exact IsDomain.of_bot_isPrime S

/-- **A regular local ring is a domain.** -/
instance (priority := 100) IsRegularLocalRing.isDomain (S : Type u) [CommRing S]
    [IsRegularLocalRing S] : IsDomain S :=
  isDomain_of_spanFinrank_maximalIdeal (maximalIdeal S).spanFinrank S rfl

/-- **The maximal ideal of a regular local ring is generated by a ring-regular sequence.**  Each
successive quotient is again regular local, hence a domain, so the next parameter is a
nonzerodivisor there. -/
theorem exists_isRingRegularSeq_of_isRegularLocalRing :
    ∀ (n : ℕ) (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n →
      ∃ rs : List S, rs.length = n ∧ Ideal.ofList rs = maximalIdeal S ∧ IsRingRegularSeq rs := by
  intro n
  induction n with
  | zero =>
    intro S _ _ hn
    have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp hn
    refine ⟨[], rfl, by rw [ofList_nil, hbot], ⟨fun i hi => absurd hi (by simp), ?_⟩⟩
    rw [ofList_nil]
    exact bot_ne_top
  | succ n ih =>
    intro S _ _ hn
    classical
    have hjac : maximalIdeal S ≤ Ideal.jacobson ⊥ :=
      le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm
    have hsq : ¬ (maximalIdeal S ≤ (maximalIdeal S) ^ (2 : ℕ)) := by
      intro hle
      have hnak : maximalIdeal S = ⊥ := by
        refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) (maximalIdeal S)
          (IsNoetherian.noetherian _) ?_ hjac
        rwa [smul_eq_mul, ← pow_two]
      rw [hnak] at hn
      simp [Submodule.spanFinrank_bot] at hn
    obtain ⟨x, hxmem, hx2⟩ := SetLike.not_le_iff_exists.mp hsq
    have hxne : x ≠ 0 := by
      intro h
      exact hx2 (h ▸ Submodule.zero_mem _)
    have hmin : ∀ p ∈ minimalPrimes S, x ∉ p := by
      intro p hp hxp
      have hpbot : p ≤ ⊥ := hp.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
      exact hxne (by simpa using hpbot hxp)
    haveI := isRegularLocalRing_quotient_span_singleton hxmem hx2 hmin
    have hmax : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (maximalIdeal S)
        = maximalIdeal (S ⧸ Ideal.span {x}) :=
      IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
    have hdrop := spanFinrank_maximalIdeal_quotient_succ hxmem hx2 hmin
    rw [hmax, hn] at hdrop
    obtain ⟨rs', hlen', hgen', hreg'⟩ := ih (S ⧸ Ideal.span {x}) (by omega)
    have hmem' : ∀ r ∈ rs', r ∈ maximalIdeal (S ⧸ Ideal.span {x}) := by
      intro r hr
      rw [← hgen']
      exact Ideal.subset_span hr
    obtain ⟨lifts, hlifts⟩ := exists_list_map_mk (Ideal.span {x}) rs'
    haveI : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hliftlen : lifts.length = rs'.length := by rw [← hlifts, List.length_map]
    have hliftmem : ∀ y ∈ lifts, y ∈ maximalIdeal S := by
      intro y hy
      have : Ideal.Quotient.mk (Ideal.span {x}) y ∈ rs' := by
        rw [← hlifts]
        exact List.mem_map_of_mem hy
      have hy' : y ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {x}))
          (maximalIdeal (S ⧸ Ideal.span {x})) := hmem' _ this
      rwa [IsLocalRing.maximalIdeal_comap] at hy'
    have hallmem : ∀ y ∈ (x :: lifts), y ∈ maximalIdeal S := by
      intro y hy
      rcases List.mem_cons.mp hy with h | h
      · exact h ▸ hxmem
      · exact hliftmem y h
    have hgen : Ideal.ofList (x :: lifts) = maximalIdeal S := by
      refine le_antisymm (by rw [Ideal.ofList, Ideal.span_le]; exact hallmem) ?_
      intro v hv
      have hvq : Ideal.Quotient.mk (Ideal.span {x}) v ∈ Ideal.ofList rs' := by
        rw [hgen', ← hmax]
        exact Ideal.mem_map_of_mem _ hv
      rw [← hlifts, ofList_map_mk] at hvq
      obtain ⟨w, hw, hwv⟩ := (Ideal.mem_map_iff_of_surjective _
        Ideal.Quotient.mk_surjective).mp hvq
      have hdiff : v - w ∈ Ideal.span {x} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hwv, sub_self]
      have hsplit : v = (v - w) + w := by ring
      rw [hsplit, ofList_cons]
      refine Submodule.add_mem _ (Submodule.mem_sup_left hdiff) (Submodule.mem_sup_right hw)
    refine ⟨x :: lifts, by simp [hliftlen, hlen'], hgen, ⟨?_, ?_⟩⟩
    · intro i hi
      match i with
      | 0 =>
        simp only [List.take_zero, ofList_nil, List.getElem_cons_zero]
        exact isRegularOn_bot_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hxne)
      | (j + 1) =>
        have hj : j < rs'.length := by
          simp only [List.length_cons] at hi
          omega
        have hjl : j < lifts.length := by rw [hliftlen]; exact hj
        rw [List.take_succ_cons, ofList_cons, ← isRegularOn_map_mk_iff]
        have hmapl : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.ofList (lifts.take j))
            = Ideal.ofList (rs'.take j) := by
          rw [← ofList_map_mk, List.map_take, hlifts]
        have hget : Ideal.Quotient.mk (Ideal.span {x}) (lifts[j]'hjl) = rs'[j] := by
          have hmapget : (List.map (Ideal.Quotient.mk (Ideal.span {x})) lifts)[j]'(by
              rw [List.length_map]; exact hjl) = rs'[j] := by
            simp [hlifts]
          rw [List.getElem_map] at hmapget
          exact hmapget
        rw [hmapl, List.getElem_cons_succ, hget]
        exact hreg'.regular j hj
    · intro htop
      have hle : Ideal.ofList (x :: lifts) ≤ maximalIdeal S := by
        rw [Ideal.ofList, Ideal.span_le]
        exact hallmem
      rw [htop] at hle
      exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp hle)

/-- **The maximal ideal of a regular local ring is generated by a ring-regular sequence.** -/
theorem exists_isRingRegularSeq_maximalIdeal (S : Type u) [CommRing S] [IsRegularLocalRing S] :
    ∃ rs : List S, rs.length = (maximalIdeal S).spanFinrank ∧
      Ideal.ofList rs = maximalIdeal S ∧ IsRingRegularSeq rs :=
  exists_isRingRegularSeq_of_isRegularLocalRing _ S rfl

/-- **A regular local ring is Cohen–Macaulay.** -/
theorem isCohenMacaulayRing_of_isRegularLocalRing (S : Type u) [CommRing S]
    [IsRegularLocalRing S] : IsCohenMacaulayRing S := by
  obtain ⟨rs, hlen, -, hreg⟩ := exists_isRingRegularSeq_maximalIdeal S
  refine ⟨rs, hreg, ?_⟩
  rw [hlen]
  exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S))

end GaloisForLFunctions.HTGeometry
