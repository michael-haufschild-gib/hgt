import GaloisForLFunctions.RHTower.Artin.CongruenceSubgroupsHaveFiniteIndexInTheUnitsAtS

/-!
# The norm index modulo a congruence subgroup

Let `L/K` be a cyclic extension of number fields with group `G = ⟨σ⟩`, `f = σ − 1` and `g = N`
on `L^×`, `S` a finite `G`-stable set of primes of `L` and `W = W_k` a congruence subgroup.

* **The Herbrand quotient of a quotient** (`herbrandQuotIndex_mul_herbrandSubIndex_range`): for a
  compatible homomorphism `φ : A → E` and a stable subgroup `W` of finite index in `ker φ`,
  `h_f(A/W) · h_g(φ A) = h_g(A/W) · h_f(φ A)`, because the finite group `ker φ / W` has Herbrand
  quotient one.
* **The Herbrand quotient of `L^×/W`** (`herbrandQuotIndex_congruenceSubgroup`):
  `[f⁻¹W : N L^× · W] = Π_ω |G_ω| · [N⁻¹W : (σ − 1) L^× · W]`, the product over the orbits of
  `G` on `S`. Here `φ` is the divisor map to `ℤ^S`, whose image has finite index, and `W` has
  finite index in its kernel.
* **The norm index** (`relIndex_range_actionNorm_sup_range_baseIncl`): since `H¹(G, W) = 0`,
  `f⁻¹W = K^× W` (`comap_actionDiff_congruenceSubgroup`), hence
  `[K^× : N L^× · (K^× ∩ W)] = Π_ω |G_ω| · [N⁻¹W : (σ − 1) L^× · W]`.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain HeightOneSpectrum

noncomputable section

namespace GaloisForLFunctions

section Quotient

variable {A E : Type*} [AddCommGroup A] [AddCommGroup E]

/-- A finite stable subgroup has Herbrand quotient one. -/
theorem herbrandSubIndex_comm_of_finite {f g : A →+ A} {C : AddSubgroup A} [Finite C]
    (hfg : ∀ a, f (g a) = 0) (hgf : ∀ a, g (f a) = 0) (hf : ∀ a ∈ C, f a ∈ C)
    (hg : ∀ a ∈ C, g a ∈ C) :
    herbrandSubIndex f g C = herbrandSubIndex g f C ∧ herbrandSubIndex f g C ≠ 0 := by
  obtain ⟨-, -, e⟩ := herbrandIndex_restrictEnd (AddMonoidHom.id A) (f := f) (g := g) (f' := f)
    (g' := g) (fun _ => rfl) (fun _ => rfl) hf hg
  obtain ⟨-, -, e'⟩ := herbrandIndex_restrictEnd (AddMonoidHom.id A) (f := g) (g := f) (f' := g)
    (g' := f) (fun _ => rfl) (fun _ => rfl) hg hf
  have h := herbrandIndex_comm_of_finite (f := restrictEnd f C hf) (g := restrictEnd g C hg)
    (fun c => Subtype.ext (hfg c)) (fun c => Subtype.ext (hgf c))
  rwa [e, e'] at h

/-- **The Herbrand quotient of a quotient**: for a stable subgroup `W` of finite index in the
kernel of a compatible homomorphism `φ`, `A/W` has the Herbrand quotient of the image of `φ`:
`h_f(A/W) · h_g(φ A) = h_g(A/W) · h_f(φ A)`. -/
theorem herbrandQuotIndex_mul_herbrandSubIndex_range (φ : A →+ E) {f g : A →+ A}
    {f' g' : E →+ E} (hφf : ∀ a, φ (f a) = f' (φ a)) (hφg : ∀ a, φ (g a) = g' (φ a))
    (hfg : ∀ a, f (g a) = 0) (hgf : ∀ a, g (f a) = 0) {W : AddSubgroup A}
    (hf : ∀ a ∈ W, f a ∈ W) (hg : ∀ a ∈ W, g a ∈ W) (hW : W ≤ φ.ker)
    (hfin : W.relIndex φ.ker ≠ 0) :
    herbrandQuotIndex f g W * herbrandSubIndex g' f' φ.range =
      herbrandQuotIndex g f W * herbrandSubIndex f' g' φ.range := by
  set π := QuotientAddGroup.mk' W
  set f₁ : A ⧸ W →+ A ⧸ W := QuotientAddGroup.map W W f hf
  set g₁ : A ⧸ W →+ A ⧸ W := QuotientAddGroup.map W W g hg
  set φ₁ : A ⧸ W →+ E := QuotientAddGroup.lift W φ hW
  have hπf : ∀ a, π (f a) = f₁ (π a) := fun a => rfl
  have hπg : ∀ a, π (g a) = g₁ (π a) := fun a => rfl
  have hπφ : ∀ a, φ₁ (π a) = φ a := fun a => rfl
  have hπ := QuotientAddGroup.mk'_surjective W
  have hrange : π.range = ⊤ := AddMonoidHom.range_eq_top.mpr hπ
  have hkerπ : π.ker = W := QuotientAddGroup.ker_mk' W
  have e1 : herbrandQuotIndex f g W = herbrandIndex f₁ g₁ := by
    rw [← herbrandSubIndex_top, ← hrange,
      ← herbrandQuotIndex_ker_eq_herbrandSubIndex_range π hπf hπg, hkerπ]
  have e2 : herbrandQuotIndex g f W = herbrandIndex g₁ f₁ := by
    rw [← herbrandSubIndex_top, ← hrange,
      ← herbrandQuotIndex_ker_eq_herbrandSubIndex_range π hπg hπf, hkerπ]
  have hfg₁ : ∀ q, f₁ (g₁ q) = 0 := fun q => by
    obtain ⟨a, rfl⟩ := hπ q
    rw [← hπg, ← hπf, hfg, map_zero]
  have hgf₁ : ∀ q, g₁ (f₁ q) = 0 := fun q => by
    obtain ⟨a, rfl⟩ := hπ q
    rw [← hπf, ← hπg, hgf, map_zero]
  have hφ₁f : ∀ q, φ₁ (f₁ q) = f' (φ₁ q) := fun q => by
    obtain ⟨a, rfl⟩ := hπ q
    rw [← hπf, hπφ, hπφ, hφf]
  have hφ₁g : ∀ q, φ₁ (g₁ q) = g' (φ₁ q) := fun q => by
    obtain ⟨a, rfl⟩ := hπ q
    rw [← hπg, hπφ, hπφ, hφg]
  -- the kernel of the induced map is the finite group `ker φ / W`
  have hker : φ₁.ker = φ.ker.map π := by
    ext q
    obtain ⟨a, rfl⟩ := hπ q
    constructor
    · intro hq
      exact ⟨a, AddMonoidHom.mem_ker.mpr ((hπφ a).symm.trans (AddMonoidHom.mem_ker.mp hq)), rfl⟩
    · rintro ⟨b, hb, hba⟩
      rw [AddMonoidHom.mem_ker, ← hba, hπφ]
      exact AddMonoidHom.mem_ker.mp hb
  have hrange₁ : φ₁.range = φ.range := by
    ext e
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨a, rfl⟩ := hπ q
      exact ⟨a, (hπφ a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨π a, hπφ a⟩
  haveI : Finite (φ.ker.map π) := Nat.finite_of_card_ne_zero (by
    rw [← AddSubgroup.relIndex_ker, hkerπ]
    exact hfin)
  have hst : ∀ {u : A →+ A} {u₁ : A ⧸ W →+ A ⧸ W} {u' : E →+ E}, (∀ a, π (u a) = u₁ (π a)) →
      (∀ a, φ (u a) = u' (φ a)) → ∀ q ∈ φ.ker.map π, u₁ q ∈ φ.ker.map π :=
    fun {u u₁ u'} hu hu' q hq => by
      obtain ⟨a, ha, rfl⟩ := hq
      refine ⟨u a, AddMonoidHom.mem_ker.mpr ?_, hu a⟩
      rw [hu', AddMonoidHom.mem_ker.mp ha, map_zero]
  obtain ⟨hc, hc0⟩ := herbrandSubIndex_comm_of_finite (C := φ.ker.map π) hfg₁ hgf₁
    (hst hπf hφf) (hst hπg hφg)
  have hmul := herbrandSubIndex_inf_ker_mul φ₁ (C := ⊤) hφ₁f hφ₁g hfg₁ hgf₁
    (fun _ _ => AddSubgroup.mem_top _) (fun _ _ => AddSubgroup.mem_top _)
  rw [top_inf_eq, ← AddMonoidHom.range_eq_map, herbrandSubIndex_top, herbrandSubIndex_top, hker,
    hrange₁, ← hc] at hmul
  rw [e1, e2]
  have h := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0)
    ((mul_assoc _ _ _).symm.trans (hmul.trans (mul_assoc _ _ _)))
  exact (mul_comm _ _).trans (h.symm.trans (mul_comm _ _))

end Quotient

section Divisors

variable {L : Type*} [Field L] [NumberField L] {G : Type*} [Group G] [MulSemiringAction G L]

attribute [local instance] primeMulAction

variable {S : SubMulAction G (HeightOneSpectrum (𝓞 L))} [Fintype S]

/-- The divisors of `L^×` at `S` have finite index in `ℤ^S`. -/
theorem index_range_divMap_ne_zero : (divMap L G S).range.index ≠ 0 := fun h => by
  have hle : (sUnits L G S).map (divMap L G S) ≤ (divMap L G S).range :=
    fun _ ⟨a, _, ha⟩ => ⟨a, ha⟩
  have hd := AddSubgroup.index_dvd_of_le hle
  rw [h] at hd
  exact index_map_divMap_ne_zero L G S (Nat.eq_zero_of_zero_dvd hd)

end Divisors

section Congruence

universe u

variable {K L G : Type u} [Field K] [Field L] [NumberField L] [Algebra K L] [CommGroup G]
  [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction

variable {S : SubMulAction G (HeightOneSpectrum (𝓞 L))} [Fintype S]

/-- **The Herbrand quotient of `L^×/W_k`**: `h_f = Π_ω |G_ω| · h_g`, the product over the orbits
of `G` on `S` of the orders of the stabilizers. -/
theorem herbrandQuotIndex_congruenceSubgroup {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ)
    (k : ℕ) :
    herbrandQuotIndex (actionDiff (fieldUnitsRep L G) σ) (actionNorm (fieldUnitsRep L G))
        (congruenceSubgroup K S k) =
      (∏ ω : MulAction.orbitRel.Quotient G S, Nat.card (MulAction.stabilizer G ω.out)) *
        herbrandQuotIndex (actionNorm (fieldUnitsRep L G)) (actionDiff (fieldUnitsRep L G) σ)
          (congruenceSubgroup K S k) := by
  set ρ := fieldUnitsRep L G
  set ρS := permRep G S
  set φ := divMap L G S
  set W := congruenceSubgroup K S k
  have hφ : ∀ τ a, φ (ρ τ a) = ρS τ (φ a) := divMap_fieldUnitsRep L G S
  have hφf := map_actionDiff φ hφ σ
  have hφg := map_actionNorm φ hφ
  have fg := actionDiff_actionNorm ρ σ
  have gf := actionNorm_actionDiff ρ σ
  have fgS := actionDiff_actionNorm ρS σ
  have gfS := actionNorm_actionDiff ρS σ
  have hW : ∀ τ, ∀ a ∈ W, ρ τ a ∈ W := fun τ a ha => fieldUnitsRep_mem_congruenceSubgroup τ ha
  have hWf : ∀ a ∈ W, actionDiff ρ σ a ∈ W := fun a ha => actionDiff_mem hW σ ha
  have hWg : ∀ a ∈ W, actionNorm ρ a ∈ W := fun a ha => actionNorm_mem hW ha
  have h1 := herbrandQuotIndex_mul_herbrandSubIndex_range φ hφf hφg fg gf hWf hWg
    (congruenceSubgroup_le_ker_divMap k) (relIndex_congruenceSubgroup_ker_divMap_ne_zero k)
  -- the divisors have finite index in the permutation module `ℤ^S`
  have hIf : ∀ y ∈ φ.range, actionDiff ρS σ y ∈ φ.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, hφf a⟩
  have hIg : ∀ y ∈ φ.range, actionNorm ρS y ∈ φ.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, hφg a⟩
  have hI : φ.range.index ≠ 0 := index_range_divMap_ne_zero
  have h2 := herbrandSubIndex_mul_of_index_ne_zero fgS gfS hIf hIg hI
  rw [herbrandIndex_actionNorm_permRep hσ, herbrandIndex_actionDiff_permRep hσ, mul_one] at h2
  have h3 : herbrandSubIndex (actionNorm ρS) (actionDiff ρS σ) φ.range ≠ 0 :=
    (herbrandSubIndex_ne_zero_iff_of_index_ne_zero gfS fgS hIg hIf hI).mpr (by
      rw [herbrandIndex_actionNorm_permRep hσ]
      exact one_ne_zero)
  rw [h2] at h1
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h3) ?_
  rw [h1]
  ring

omit [NumberField L] [Fintype G] in
/-- The elements of `L^×` fixed by `G` lie in `K^×`. -/
theorem mem_range_baseIncl_of_forall_eq {x : Additive Lˣ}
    (h : ∀ τ : G, fieldUnitsRep L G τ x = x) : x ∈ (baseIncl K L).range := by
  have hinv : ∀ τ : G, τ • ((Additive.toMul x : Lˣ) : L) = ((Additive.toMul x : Lˣ) : L) :=
    fun τ => congrArg (fun z : Additive Lˣ => ((Additive.toMul z : Lˣ) : L)) (h τ)
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := K) (G := G) _ hinv
  have ha0 : a ≠ 0 := fun h0 => (Additive.toMul x).ne_zero (by rw [← ha, h0, map_zero])
  refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
  show (Additive.ofMul (Units.map (algebraMap K L : K →* L) (Units.mk0 a ha0)) : Additive Lˣ) =
    Additive.ofMul (Additive.toMul x)
  exact congrArg _ (Units.ext ha)

omit [NumberField L] in
/-- Norms lie in `K^×`. -/
theorem range_actionNorm_le_range_baseIncl :
    (actionNorm (fieldUnitsRep L G)).range ≤ (baseIncl K L).range := by
  rintro _ ⟨x, rfl⟩
  exact mem_range_baseIncl_of_forall_eq fun τ => rep_apply_actionNorm _ τ x

/-- `(σ − 1)⁻¹ W_k = K^× W_k`: if `σx / x ∈ W_k`, then `σx / x = σz / z` with `z ∈ W_k`, and
`x / z` is fixed by `G`. -/
theorem comap_actionDiff_congruenceSubgroup {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ)
    (k : ℕ) :
    (congruenceSubgroup K S k).comap (actionDiff (fieldUnitsRep L G) σ) =
      (baseIncl K L).range ⊔ congruenceSubgroup K S k := by
  have hW : ∀ τ, ∀ a ∈ congruenceSubgroup K S k,
      fieldUnitsRep L G τ a ∈ congruenceSubgroup K S k :=
    fun τ a ha => fieldUnitsRep_mem_congruenceSubgroup τ ha
  refine le_antisymm (fun x hx => ?_) (sup_le ?_ fun x hx => actionDiff_mem hW σ hx)
  · obtain ⟨z, hz, hzx⟩ := exists_mem_congruenceSubgroup_actionDiff_eq hσ k
      (AddSubgroup.mem_comap.mp hx) (actionNorm_actionDiff _ σ x)
    have h0 : actionDiff (fieldUnitsRep L G) σ (x - z) = 0 := by rw [map_sub, hzx, sub_self]
    have h := AddSubgroup.add_mem_sup
      (mem_range_baseIncl_of_forall_eq (K := K) (rep_apply_eq_of_actionDiff_eq_zero hσ h0)) hz
    rwa [sub_add_cancel] at h
  · rintro _ ⟨c, rfl⟩
    rw [AddSubgroup.mem_comap, actionDiff_apply, fieldUnitsRep_baseIncl, sub_self]
    exact zero_mem _

/-- **The norm index modulo a congruence subgroup**:
`[K^× : N L^× · (K^× ∩ W_k)] = Π_ω |G_ω| · [N⁻¹ W_k : (σ − 1) L^× · W_k]`. -/
theorem relIndex_range_actionNorm_sup_range_baseIncl {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (k : ℕ) :
    ((actionNorm (fieldUnitsRep L G)).range ⊔
        (baseIncl K L).range ⊓ congruenceSubgroup K S k).relIndex (baseIncl K L).range =
      (∏ ω : MulAction.orbitRel.Quotient G S, Nat.card (MulAction.stabilizer G ω.out)) *
        herbrandQuotIndex (actionNorm (fieldUnitsRep L G)) (actionDiff (fieldUnitsRep L G) σ)
          (congruenceSubgroup K S k) := by
  rw [← herbrandQuotIndex_congruenceSubgroup hσ k, herbrandQuotIndex,
    comap_actionDiff_congruenceSubgroup hσ k]
  have hN : (actionNorm (fieldUnitsRep L G)).range ≤ (baseIncl K L).range :=
    range_actionNorm_le_range_baseIncl
  have h := relIndex_eq_sup_mul_inf (sup_le hN inf_le_left :
    (actionNorm (fieldUnitsRep L G)).range ⊔
      (baseIncl K L).range ⊓ congruenceSubgroup K S k ≤ (baseIncl K L).range)
    (congruenceSubgroup K S k)
  have e1 : (actionNorm (fieldUnitsRep L G)).range ⊔
      (baseIncl K L).range ⊓ congruenceSubgroup K S k ⊔ congruenceSubgroup K S k =
        (actionNorm (fieldUnitsRep L G)).range ⊔ congruenceSubgroup K S k := by
    rw [sup_assoc, (sup_eq_right.mpr inf_le_right :
      (baseIncl K L).range ⊓ congruenceSubgroup K S k ⊔ congruenceSubgroup K S k =
        congruenceSubgroup K S k)]
  have e2 : (((actionNorm (fieldUnitsRep L G)).range ⊔
      (baseIncl K L).range ⊓ congruenceSubgroup K S k) ⊓ congruenceSubgroup K S k).relIndex
        ((baseIncl K L).range ⊓ congruenceSubgroup K S k) = 1 :=
    AddSubgroup.relIndex_eq_one.mpr (le_inf le_sup_right inf_le_right)
  rw [e1, e2, mul_one] at h
  exact h

end Congruence

end GaloisForLFunctions
