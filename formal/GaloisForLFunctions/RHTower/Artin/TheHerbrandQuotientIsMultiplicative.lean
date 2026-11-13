import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Order.ModularLattice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The Herbrand quotient is multiplicative

Let `f, g` be endomorphisms of an abelian group `A` with `f g = g f = 0`. The **Herbrand index**
is `h_f(A) = [ker f : im g]` (`herbrandIndex`, zero if the index is infinite) and the Herbrand
quotient is `h_f(A) / h_g(A)`. For `f = σ − 1`, `g = 1 + σ + … + σ^{n−1}` and `σ` of order `n`
these are the orders of the Tate cohomology groups `Ĥ⁰` and `Ĥ¹` of the cyclic group `⟨σ⟩`.

* **A stable subgroup** (`herbrandSubIndex_mul_herbrandQuotIndex`). For a subgroup `B` stable
  under `f` and `g`,
  `h_f(B) · h_f(A/B) = h_f(A) · [fA ∩ B : fB] · [gA ∩ B : gB]`.
  The last two factors do not change when `f` and `g` are exchanged.
* **Finite groups** (`herbrandIndex_comm_of_finite`): `h_f(A) = h_g(A) ≠ 0` for finite `A`.
* **A subgroup and a homomorphism** (`herbrandSubIndex_inf_ker_mul`). Let `φ : A → W` be
  compatible with pairs of endomorphisms of `A` and `W`, and `C` a stable subgroup of `A`. Then
  `h_f(C ∩ ker φ) · h_f(φ C) · h_g(C) = h_g(C ∩ ker φ) · h_g(φ C) · h_f(C)`: the Herbrand
  quotient of `C` is the product of those of `C ∩ ker φ` and `φ C`.
* **Subgroups of finite index** (`herbrandSubIndex_mul_of_index_ne_zero`): a stable subgroup of
  finite index has the Herbrand quotient of the group.

Proof of the first statement. With `π : A → A/B`: `ker f ∩ B ⊇ gA ∩ B ⊇ gB` and
`f⁻¹B ⊇ ker f + B ⊇ gA + B`, and
`[ker f : gA] = [ker f + B : gA + B] · [ker f ∩ B : gA ∩ B]`, while `f` maps
`f⁻¹B / (ker f + B)` isomorphically to `(fA ∩ B) / fB`.
-/

open Function

noncomputable section

namespace GaloisForLFunctions

section Index

variable {A : Type*} [AddCommGroup A]

/-- For subgroups `N ≤ M` and `H` of an abelian group,
`[M : N] = [M + H : N + H] · [M ∩ H : N ∩ H]`. -/
theorem relIndex_eq_sup_mul_inf {N M : AddSubgroup A} (h : N ≤ M) (H : AddSubgroup A) :
    N.relIndex M = (N ⊔ H).relIndex (M ⊔ H) * (N ⊓ H).relIndex (M ⊓ H) := by
  have h1 : (N ⊔ H).relIndex (M ⊔ H) = (N ⊔ M ⊓ H).relIndex M := by
    have hM : M ⊔ H = M ⊔ (N ⊔ H) := by rw [← sup_assoc, sup_eq_left.mpr h]
    have hmod : (N ⊔ H) ⊓ M = N ⊔ M ⊓ H := by rw [sup_inf_assoc_of_le H h, inf_comm]
    rw [hM, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (N ⊔ H) M, hmod]
  have h2 : (N ⊓ H).relIndex (M ⊓ H) = N.relIndex (N ⊔ M ⊓ H) := by
    have hN : N ⊓ (M ⊓ H) = N ⊓ H := by rw [← inf_assoc, inf_eq_left.mpr h]
    rw [AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right N (M ⊓ H), hN]
  rw [h1, h2, mul_comm]
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le h inf_le_left)).symm

/-- A homomorphism preserves the index of two subgroups that contain its kernel. -/
theorem relIndex_map_map_of_ker_le {B : Type*} [AddCommGroup B] (f : A →+ B)
    {Q P : AddSubgroup A} (hQ : f.ker ≤ Q) (hQP : Q ≤ P) :
    (Q.map f).relIndex (P.map f) = Q.relIndex P := by
  rw [AddSubgroup.relIndex_map_map, sup_eq_left.mpr hQ, sup_eq_left.mpr (hQ.trans hQP)]

end Index

section Herbrand

variable {A : Type*} [AddCommGroup A]

/-- The Herbrand index `[ker f : im g]` of a pair of endomorphisms; zero if it is infinite. -/
def herbrandIndex (f g : A →+ A) : ℕ := g.range.relIndex f.ker

/-- The Herbrand index `[ker f ∩ B : gB]` of the restrictions of `f, g` to a subgroup `B`. -/
def herbrandSubIndex (f g : A →+ A) (B : AddSubgroup A) : ℕ := (B.map g).relIndex (f.ker ⊓ B)

/-- The Herbrand index `[f⁻¹B : gA + B]` of the endomorphisms induced by `f, g` on `A/B`. -/
def herbrandQuotIndex (f g : A →+ A) (B : AddSubgroup A) : ℕ :=
  (g.range ⊔ B).relIndex (B.comap f)

/-- The index `[fA ∩ B : fB]`. -/
def herbrandDefect (f : A →+ A) (B : AddSubgroup A) : ℕ := (B.map f).relIndex (f.range ⊓ B)

variable {f g : A →+ A} {B : AddSubgroup A}

theorem herbrandSubIndex_top : herbrandSubIndex f g ⊤ = herbrandIndex f g := by
  rw [herbrandSubIndex, herbrandIndex, ← AddMonoidHom.range_eq_map, inf_top_eq]

theorem herbrandSubIndex_bot : herbrandSubIndex f g ⊥ = 1 := by
  rw [herbrandSubIndex, inf_bot_eq, AddSubgroup.relIndex_bot_right]

/-- `[ker f ∩ B : gB] = [gA ∩ B : gB] · [ker f ∩ B : gA ∩ B]`. -/
theorem herbrandSubIndex_eq (hfg : ∀ a, f (g a) = 0) (hg : ∀ a ∈ B, g a ∈ B) :
    herbrandSubIndex f g B = herbrandDefect g B * (g.range ⊓ B).relIndex (f.ker ⊓ B) := by
  refine (AddSubgroup.relIndex_mul_relIndex _ _ _ ?_ ?_).symm
  · rintro _ ⟨a, ha, rfl⟩
    exact AddSubgroup.mem_inf.mpr ⟨⟨a, rfl⟩, hg a ha⟩
  · intro x hx
    obtain ⟨⟨a, rfl⟩, hb⟩ := AddSubgroup.mem_inf.mp hx
    exact AddSubgroup.mem_inf.mpr ⟨AddMonoidHom.mem_ker.mpr (hfg a), hb⟩

/-- `[f⁻¹B : gA + B] = [ker f + B : gA + B] · [fA ∩ B : fB]`. -/
theorem herbrandQuotIndex_eq (hfg : ∀ a, f (g a) = 0) (hf : ∀ a ∈ B, f a ∈ B) :
    herbrandQuotIndex f g B = (g.range ⊔ B).relIndex (f.ker ⊔ B) * herbrandDefect f B := by
  have hle : f.ker ⊔ B ≤ B.comap f :=
    sup_le (fun x hx => by
      rw [AddSubgroup.mem_comap, AddMonoidHom.mem_ker.mp hx]; exact B.zero_mem) hf
  -- `f` maps `f⁻¹B / (ker f + B)` isomorphically to `(fA ∩ B) / fB`
  have h1 : (f.ker ⊔ B).relIndex (B.comap f) = herbrandDefect f B := by
    have hmap : (f.ker ⊔ B).map f = B.map f := by
      rw [AddSubgroup.map_sup, (AddSubgroup.map_eq_bot_iff _).mpr le_rfl, bot_sup_eq]
    rw [herbrandDefect, ← AddSubgroup.map_comap_eq, ← hmap]
    exact (relIndex_map_map_of_ker_le f le_sup_left hle).symm
  rw [← h1]
  refine (AddSubgroup.relIndex_mul_relIndex _ _ _ (sup_le_sup_right ?_ B) hle).symm
  rintro _ ⟨a, rfl⟩
  exact AddMonoidHom.mem_ker.mpr (hfg a)

/-- **The Herbrand index of a stable subgroup and of the quotient.**
`h_f(B) · h_f(A/B) = h_f(A) · [fA ∩ B : fB] · [gA ∩ B : gB]`. -/
theorem herbrandSubIndex_mul_herbrandQuotIndex (hfg : ∀ a, f (g a) = 0)
    (hf : ∀ a ∈ B, f a ∈ B) (hg : ∀ a ∈ B, g a ∈ B) :
    herbrandSubIndex f g B * herbrandQuotIndex f g B =
      herbrandIndex f g * (herbrandDefect f B * herbrandDefect g B) := by
  have hr : g.range ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    exact AddMonoidHom.mem_ker.mpr (hfg a)
  rw [herbrandSubIndex_eq hfg hg, herbrandQuotIndex_eq hfg hf, herbrandIndex,
    relIndex_eq_sup_mul_inf hr B]
  ring

/-- The Herbrand quotient is multiplicative, in a form valid without finiteness assumptions. -/
theorem herbrandSubIndex_mul_herbrandQuotIndex_mul (hfg : ∀ a, f (g a) = 0)
    (hgf : ∀ a, g (f a) = 0) (hf : ∀ a ∈ B, f a ∈ B) (hg : ∀ a ∈ B, g a ∈ B) :
    herbrandSubIndex f g B * herbrandQuotIndex f g B * herbrandIndex g f =
      herbrandSubIndex g f B * herbrandQuotIndex g f B * herbrandIndex f g := by
  rw [herbrandSubIndex_mul_herbrandQuotIndex hfg hf hg,
    herbrandSubIndex_mul_herbrandQuotIndex hgf hg hf]
  ring

/-- Finite indices for the subgroup and the quotient give a finite index for the group. -/
theorem herbrandIndex_ne_zero (hfg : ∀ a, f (g a) = 0) (hf : ∀ a ∈ B, f a ∈ B)
    (hg : ∀ a ∈ B, g a ∈ B) (hs : herbrandSubIndex f g B ≠ 0)
    (hq : herbrandQuotIndex f g B ≠ 0) : herbrandIndex f g ≠ 0 := fun h0 => by
  have h := herbrandSubIndex_mul_herbrandQuotIndex hfg hf hg
  rw [h0, zero_mul] at h
  exact mul_ne_zero hs hq h

/-- Finite indices for the group and the quotient give a finite index for the subgroup. -/
theorem herbrandSubIndex_ne_zero (hfg : ∀ a, f (g a) = 0) (hgf : ∀ a, g (f a) = 0)
    (hg : ∀ a ∈ B, g a ∈ B) (h : herbrandIndex f g ≠ 0)
    (hq' : herbrandQuotIndex g f B ≠ 0) : herbrandSubIndex f g B ≠ 0 := by
  have hr : g.range ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    exact AddMonoidHom.mem_ker.mpr (hfg a)
  have hdg : herbrandDefect g B ≠ 0 := fun h1 =>
    hq' (by rw [herbrandQuotIndex_eq hgf hg, h1, mul_zero])
  have hX : (g.range ⊓ B).relIndex (f.ker ⊓ B) ≠ 0 := fun h1 =>
    h (by rw [herbrandIndex, relIndex_eq_sup_mul_inf hr B, h1, mul_zero])
  rw [herbrandSubIndex_eq hfg hg]
  exact mul_ne_zero hdg hX

end Herbrand

section Transport

variable {A E : Type*} [AddCommGroup A] [AddCommGroup E]

/-- For a homomorphism `φ : A → E` compatible with the endomorphisms, the Herbrand index of
`A / ker φ` is that of the image of `φ`. -/
theorem herbrandQuotIndex_ker_eq_herbrandSubIndex_range (φ : A →+ E) {f g : A →+ A}
    {f' g' : E →+ E} (hf : ∀ a, φ (f a) = f' (φ a)) (hg : ∀ a, φ (g a) = g' (φ a)) :
    herbrandQuotIndex f g φ.ker = herbrandSubIndex f' g' φ.range := by
  have h1 : φ.range.map g' = g.range.map φ := by
    rw [AddMonoidHom.map_range, AddMonoidHom.map_range]
    congr 1
    ext a
    exact (hg a).symm
  have h2 : φ.ker.comap f = f'.ker.comap φ := by
    ext a
    simp only [AddSubgroup.mem_comap, AddMonoidHom.mem_ker, hf]
  rw [herbrandQuotIndex, herbrandSubIndex, h1, h2, ← AddSubgroup.comap_map_eq,
    AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq, inf_comm φ.range]

/-- An injective compatible homomorphism preserves the Herbrand index of a subgroup. -/
theorem herbrandSubIndex_map_of_injective (ι : A →+ E) (hι : Injective ι) {f g : A →+ A}
    {f' g' : E →+ E} (hf : ∀ a, ι (f a) = f' (ι a)) (hg : ∀ a, ι (g a) = g' (ι a))
    (B : AddSubgroup A) : herbrandSubIndex f' g' (B.map ι) = herbrandSubIndex f g B := by
  have h1 : (B.map ι).map g' = (B.map g).map ι := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext a
    exact (hg a).symm
  have h2 : f'.ker ⊓ B.map ι = (f.ker ⊓ B).map ι := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx0, a, ha, rfl⟩ := AddSubgroup.mem_inf.mp hx
      refine ⟨a, AddSubgroup.mem_inf.mpr ⟨AddMonoidHom.mem_ker.mpr (hι ?_), ha⟩, rfl⟩
      rw [hf, AddMonoidHom.mem_ker.mp hx0, map_zero]
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨ha0, haB⟩ := AddSubgroup.mem_inf.mp ha
      refine AddSubgroup.mem_inf.mpr ⟨AddMonoidHom.mem_ker.mpr ?_, a, haB, rfl⟩
      rw [← hf, AddMonoidHom.mem_ker.mp ha0, map_zero]
  rw [herbrandSubIndex, h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _ hι,
    herbrandSubIndex]

/-- The Herbrand index of a group embedded by `ι` is that of the subgroup `im ι`. -/
theorem herbrandIndex_eq_herbrandSubIndex_range (ι : A →+ E) (hι : Injective ι) {f g : A →+ A}
    {f' g' : E →+ E} (hf : ∀ a, ι (f a) = f' (ι a)) (hg : ∀ a, ι (g a) = g' (ι a)) :
    herbrandIndex f g = herbrandSubIndex f' g' ι.range := by
  rw [AddMonoidHom.range_eq_map, herbrandSubIndex_map_of_injective ι hι hf hg,
    herbrandSubIndex_top]

end Transport

section Finite

variable {A : Type*} [AddCommGroup A] {f g : A →+ A} {B : AddSubgroup A}

/-- **Finite groups have Herbrand quotient one**: `[ker f : im g] = [ker g : im f]`, since
`|ker f| · |im f| = |A| = |ker g| · |im g|`. -/
theorem herbrandIndex_comm_of_finite [Finite A] (hfg : ∀ a, f (g a) = 0)
    (hgf : ∀ a, g (f a) = 0) :
    herbrandIndex f g = herbrandIndex g f ∧ herbrandIndex f g ≠ 0 := by
  have key : ∀ f g : A →+ A, (∀ a, f (g a) = 0) →
      Nat.card g.range * herbrandIndex f g = Nat.card f.ker := by
    intro f g hfg
    have hr : g.range ≤ f.ker := by
      rintro _ ⟨a, rfl⟩
      exact AddMonoidHom.mem_ker.mpr (hfg a)
    have := AddSubgroup.relIndex_mul_relIndex ⊥ g.range f.ker bot_le hr
    rwa [AddSubgroup.relIndex_bot_left, AddSubgroup.relIndex_bot_left] at this
  have card : ∀ f : A →+ A, Nat.card f.ker * Nat.card f.range = Nat.card A := by
    intro f
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  have hf0 : Nat.card f.range ≠ 0 := Nat.card_pos.ne'
  have hg0 : Nat.card g.range ≠ 0 := Nat.card_pos.ne'
  have h1 := key f g hfg
  have h2 := key g f hgf
  refine ⟨?_, fun h0 => ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero hg0 hf0))
    calc Nat.card g.range * Nat.card f.range * herbrandIndex f g
        = Nat.card g.range * herbrandIndex f g * Nat.card f.range := by ring
      _ = Nat.card A := by rw [h1, card f]
      _ = Nat.card g.ker * Nat.card g.range := (card g).symm
      _ = Nat.card g.range * Nat.card f.range * herbrandIndex g f := by rw [← h2]; ring
  · rw [h0, mul_zero] at h1
    exact (Nat.card_pos (α := f.ker)).ne' h1.symm

/-- For a stable subgroup of finite index the two Herbrand indices of the quotient agree. -/
theorem herbrandQuotIndex_comm_of_index_ne_zero (hfg : ∀ a, f (g a) = 0)
    (hgf : ∀ a, g (f a) = 0) (hf : ∀ a ∈ B, f a ∈ B) (hg : ∀ a ∈ B, g a ∈ B)
    (hB : B.index ≠ 0) :
    herbrandQuotIndex f g B = herbrandQuotIndex g f B ∧ herbrandQuotIndex f g B ≠ 0 := by
  haveI : Finite (A ⧸ B) := Nat.finite_of_card_ne_zero hB
  set π := QuotientAddGroup.mk' B
  set f' : A ⧸ B →+ A ⧸ B := QuotientAddGroup.map B B f hf
  set g' : A ⧸ B →+ A ⧸ B := QuotientAddGroup.map B B g hg
  have hπf : ∀ a, π (f a) = f' (π a) := fun a => rfl
  have hπg : ∀ a, π (g a) = g' (π a) := fun a => rfl
  have hπ : π.range = ⊤ := AddMonoidHom.range_eq_top.mpr (QuotientAddGroup.mk'_surjective B)
  have hker : π.ker = B := QuotientAddGroup.ker_mk' B
  have e1 : herbrandQuotIndex f g B = herbrandIndex f' g' := by
    rw [← herbrandSubIndex_top, ← hπ, ← herbrandQuotIndex_ker_eq_herbrandSubIndex_range π hπf hπg,
      hker]
  have e2 : herbrandQuotIndex g f B = herbrandIndex g' f' := by
    rw [← herbrandSubIndex_top, ← hπ, ← herbrandQuotIndex_ker_eq_herbrandSubIndex_range π hπg hπf,
      hker]
  have hfg' : ∀ x, f' (g' x) = 0 := fun x => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective B x
    rw [← hπg, ← hπf, hfg, map_zero]
  have hgf' : ∀ x, g' (f' x) = 0 := fun x => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective B x
    rw [← hπf, ← hπg, hgf, map_zero]
  rw [e1, e2]
  exact herbrandIndex_comm_of_finite hfg' hgf'

end Finite

section FiniteIndex

variable {A : Type*} [AddCommGroup A] {f g : A →+ A} {B : AddSubgroup A}

/-- A stable subgroup of finite index has finite Herbrand index exactly when the group has. -/
theorem herbrandSubIndex_ne_zero_iff_of_index_ne_zero (hfg : ∀ a, f (g a) = 0)
    (hgf : ∀ a, g (f a) = 0) (hf : ∀ a ∈ B, f a ∈ B) (hg : ∀ a ∈ B, g a ∈ B)
    (hB : B.index ≠ 0) : herbrandSubIndex f g B ≠ 0 ↔ herbrandIndex f g ≠ 0 := by
  have ht := herbrandQuotIndex_comm_of_index_ne_zero hfg hgf hf hg hB
  refine ⟨fun hs => herbrandIndex_ne_zero hfg hf hg hs ht.2,
    fun he => herbrandSubIndex_ne_zero hfg hgf hg he ?_⟩
  rw [← ht.1]
  exact ht.2

/-- **A stable subgroup of finite index has the Herbrand quotient of the group.** -/
theorem herbrandSubIndex_mul_of_index_ne_zero (hfg : ∀ a, f (g a) = 0)
    (hgf : ∀ a, g (f a) = 0) (hf : ∀ a ∈ B, f a ∈ B) (hg : ∀ a ∈ B, g a ∈ B)
    (hB : B.index ≠ 0) :
    herbrandSubIndex f g B * herbrandIndex g f = herbrandSubIndex g f B * herbrandIndex f g := by
  have ht := herbrandQuotIndex_comm_of_index_ne_zero hfg hgf hf hg hB
  have hm := herbrandSubIndex_mul_herbrandQuotIndex_mul hfg hgf hf hg
  rw [← ht.1] at hm
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ht.2)
  linarith

end FiniteIndex

section Relative

variable {A W : Type*} [AddCommGroup A] [AddCommGroup W]

/-- The restriction of an endomorphism to a stable subgroup. -/
def restrictEnd (f : A →+ A) (C : AddSubgroup A) (hf : ∀ a ∈ C, f a ∈ C) : C →+ C :=
  (f.comp C.subtype).codRestrict C fun c => hf c c.2

variable (φ : A →+ W) {f g : A →+ A} {f' g' : W →+ W} {C : AddSubgroup A}

/-- For a stable subgroup `C` and a compatible homomorphism `φ`, the Herbrand indices of
`C ∩ ker φ`, of `φ C` and of `C` are those of the kernel of `φ|_C`, of the quotient by it, and
of the group `C`. -/
theorem herbrandIndex_restrictEnd (hφf : ∀ a, φ (f a) = f' (φ a))
    (hφg : ∀ a, φ (g a) = g' (φ a)) (hf : ∀ a ∈ C, f a ∈ C) (hg : ∀ a ∈ C, g a ∈ C) :
    herbrandSubIndex (restrictEnd f C hf) (restrictEnd g C hg) (φ.comp C.subtype).ker =
        herbrandSubIndex f g (C ⊓ φ.ker) ∧
      herbrandQuotIndex (restrictEnd f C hf) (restrictEnd g C hg) (φ.comp C.subtype).ker =
        herbrandSubIndex f' g' (C.map φ) ∧
      herbrandIndex (restrictEnd f C hf) (restrictEnd g C hg) = herbrandSubIndex f g C := by
  have hιf : ∀ c, C.subtype (restrictEnd f C hf c) = f (C.subtype c) := fun _ => rfl
  have hιg : ∀ c, C.subtype (restrictEnd g C hg c) = g (C.subtype c) := fun _ => rfl
  have hker : (φ.comp C.subtype).ker.map C.subtype = C ⊓ φ.ker := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact AddSubgroup.mem_inf.mpr ⟨c.2, hc⟩
    · intro hx
      obtain ⟨hxC, hx0⟩ := AddSubgroup.mem_inf.mp hx
      exact ⟨⟨x, hxC⟩, hx0, rfl⟩
  have hrange : (φ.comp C.subtype).range = C.map φ := by
    rw [← AddMonoidHom.map_range, AddSubgroup.range_subtype]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hker]
    exact (herbrandSubIndex_map_of_injective C.subtype C.subtype_injective hιf hιg _).symm
  · rw [← hrange]
    exact herbrandQuotIndex_ker_eq_herbrandSubIndex_range (φ.comp C.subtype)
      (fun c => hφf c) fun c => hφg c
  · have h := herbrandIndex_eq_herbrandSubIndex_range C.subtype C.subtype_injective hιf hιg
    rwa [AddSubgroup.range_subtype] at h

/-- **The Herbrand quotient of `C` is the product of those of `C ∩ ker φ` and `φ C`**:
`h_f(C ∩ ker φ) · h_f(φ C) · h_g(C) = h_g(C ∩ ker φ) · h_g(φ C) · h_f(C)`. -/
theorem herbrandSubIndex_inf_ker_mul (hφf : ∀ a, φ (f a) = f' (φ a))
    (hφg : ∀ a, φ (g a) = g' (φ a)) (hfg : ∀ a, f (g a) = 0) (hgf : ∀ a, g (f a) = 0)
    (hf : ∀ a ∈ C, f a ∈ C) (hg : ∀ a ∈ C, g a ∈ C) :
    herbrandSubIndex f g (C ⊓ φ.ker) * herbrandSubIndex f' g' (C.map φ) *
        herbrandSubIndex g f C =
      herbrandSubIndex g f (C ⊓ φ.ker) * herbrandSubIndex g' f' (C.map φ) *
        herbrandSubIndex f g C := by
  obtain ⟨e1, e2, e3⟩ := herbrandIndex_restrictEnd φ hφf hφg hf hg
  obtain ⟨e1', e2', e3'⟩ := herbrandIndex_restrictEnd φ hφg hφf hg hf
  have hst : ∀ {u : A →+ A} {u' : W →+ W} (_ : ∀ a, φ (u a) = u' (φ a))
      (hu : ∀ a ∈ C, u a ∈ C), ∀ c ∈ (φ.comp C.subtype).ker,
        restrictEnd u C hu c ∈ (φ.comp C.subtype).ker := fun {u u'} hφu hu c hc => by
    rw [AddMonoidHom.mem_ker] at hc ⊢
    show φ (u c) = 0
    rw [hφu]
    exact (congrArg u' hc).trans (map_zero u')
  have h := herbrandSubIndex_mul_herbrandQuotIndex_mul
    (f := restrictEnd f C hf) (g := restrictEnd g C hg) (B := (φ.comp C.subtype).ker)
    (fun c => Subtype.ext (hfg c)) (fun c => Subtype.ext (hgf c)) (hst hφf hf) (hst hφg hg)
  rwa [e1, e2, e3, e1', e2', e3'] at h

/-- Finite Herbrand indices of `C ∩ ker φ` and `φ C` give a finite Herbrand index of `C`. -/
theorem herbrandSubIndex_ne_zero_of_inf_ker (hφf : ∀ a, φ (f a) = f' (φ a))
    (hφg : ∀ a, φ (g a) = g' (φ a)) (hfg : ∀ a, f (g a) = 0)
    (hf : ∀ a ∈ C, f a ∈ C) (hg : ∀ a ∈ C, g a ∈ C)
    (hK : herbrandSubIndex f g (C ⊓ φ.ker) ≠ 0) (hI : herbrandSubIndex f' g' (C.map φ) ≠ 0) :
    herbrandSubIndex f g C ≠ 0 := by
  obtain ⟨e1, e2, e3⟩ := herbrandIndex_restrictEnd φ hφf hφg hf hg
  have hst : ∀ {u : A →+ A} {u' : W →+ W} (_ : ∀ a, φ (u a) = u' (φ a))
      (hu : ∀ a ∈ C, u a ∈ C), ∀ c ∈ (φ.comp C.subtype).ker,
        restrictEnd u C hu c ∈ (φ.comp C.subtype).ker := fun {u u'} hφu hu c hc => by
    rw [AddMonoidHom.mem_ker] at hc ⊢
    show φ (u c) = 0
    rw [hφu]
    exact (congrArg u' hc).trans (map_zero u')
  rw [← e3]
  refine herbrandIndex_ne_zero (B := (φ.comp C.subtype).ker) (fun c => Subtype.ext (hfg c))
    (hst hφf hf) (hst hφg hg) ?_ ?_
  · rwa [e1]
  · rwa [e2]

end Relative

end GaloisForLFunctions
