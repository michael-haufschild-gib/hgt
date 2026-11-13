import GaloisForLFunctions.RHTower.Artin.SUnitsOfNormOneAreQuotientsOfConjugates

/-!
# The Herbrand indices of a permutation module

Let a finite group `G = ⟨σ⟩` act on a finite set `X`, and on `ℤ^X` by `(τ y)(x) = y(τ⁻¹ x)`.

* **The norm** (`actionNorm_permRep_apply`): `(N y)(r) = |G_r| · Σ_{x ∈ G r} y(x)`.
* **`H¹(G, ℤ^X) = 0`** (`herbrandIndex_actionNorm_permRep`): if `N y = 0`, the sums of `y` over
  the orbits vanish, so `y = Σ_x y(x) (δ_x − δ_{r(x)})`, `r(x)` the chosen point of the orbit of
  `x`; and `δ_{τ r} − δ_r = (τ − 1) δ_r` lies in the image of `σ − 1`.
* **`|Ĥ⁰(G, ℤ^X)| = Π_ω |G_ω|`** (`herbrandIndex_actionDiff_permRep`), the product over the
  orbits of the orders of the stabilizers: the invariant functions are the functions on the
  orbits, the norms those with value divisible by `|G_ω|` on `ω`.

For a number field `L` and a `G`-stable finite set `S` of primes whose invariant divisors
descend, this gives the norm index of the `S`-units exactly
(`card_mul_herbrandSubIndex_sUnits_eq`): `|G| · [L_S^G : N L_S] = Π_ω |G_ω|`, the product over
the orbits of `G` on the infinite places and on `S`.
-/

open Function
open scoped Classical NumberField
open NumberField IsDedekindDomain HeightOneSpectrum

noncomputable section

namespace GaloisForLFunctions

section Permutation

variable {G : Type*} [Group G] [Fintype G] {X : Type*} [Fintype X] [MulAction G X]

omit [Fintype X] in
/-- The elements carrying a point `b` of the orbit of `r` to `r` form a coset of the stabilizer
of `r`. -/
theorem card_filter_inv_smul_eq' (b r : X) (hb : b ∈ MulAction.orbit G r) :
    (Finset.univ.filter fun τ : G => τ⁻¹ • r = b).card = Nat.card (MulAction.stabilizer G r) := by
  obtain ⟨τ₀, rfl⟩ := hb
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_equiv (Equiv.mulRight τ₀) fun τ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight,
    MulAction.mem_stabilizer_iff]
  rw [inv_smul_eq_iff, mul_smul]
  exact eq_comm

/-- **The norm on a permutation module**: `(N y)(r) = |G_r| · Σ_{x ∈ G r} y(x)`. -/
theorem actionNorm_permRep_apply (y : X → ℤ) (r : X) :
    actionNorm (permRep G X) y r =
      Nat.card (MulAction.stabilizer G r) *
        ∑ x ∈ Finset.univ.filter (fun x => x ∈ MulAction.orbit G r), y x := by
  rw [actionNorm_apply, Finset.sum_apply]
  simp only [permRep_apply]
  rw [Finset.sum_comp y fun τ : G => τ⁻¹ • r, Finset.mul_sum]
  have himg : (Finset.univ.image fun τ : G => τ⁻¹ • r) =
      Finset.univ.filter (fun x => x ∈ MulAction.orbit G r) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨τ, rfl⟩
      exact ⟨τ⁻¹, rfl⟩
    · rintro ⟨τ, rfl⟩
      exact ⟨τ⁻¹, by rw [inv_inv]⟩
  rw [himg]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [card_filter_inv_smul_eq' b r (Finset.mem_filter.mp hb).2, nsmul_eq_mul]

omit [Fintype G] [Fintype X] in
/-- `τ δ_r = δ_{τ r}`. -/
theorem permRep_single (τ : G) (r : X) (c : ℤ) :
    permRep G X τ (Pi.single r c) = Pi.single (τ • r) c := by
  funext x
  rw [permRep_apply, Pi.single_apply, Pi.single_apply]
  exact if_congr inv_smul_eq_iff rfl rfl

omit [Fintype G] [Fintype X] in
/-- Every point lies in the orbit of the chosen point of its orbit. -/
theorem mem_orbit_out (x : X) :
    x ∈ MulAction.orbit G (Quotient.mk'' x : MulAction.orbitRel.Quotient G X).out := by
  letI := MulAction.orbitRel G X
  exact MulAction.orbitRel_apply.mp (Setoid.symm (Quotient.mk_out x))

/-- **`H¹` of a permutation module vanishes**: a function with norm zero lies in the image of
`σ − 1`. -/
theorem herbrandIndex_actionNorm_permRep {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    herbrandIndex (actionNorm (permRep G X)) (actionDiff (permRep G X) σ) = 1 := by
  refine AddSubgroup.relIndex_eq_one.mpr fun y hy => ?_
  rw [AddMonoidHom.mem_ker] at hy
  set r : X → X := fun x => (Quotient.mk'' x : MulAction.orbitRel.Quotient G X).out with hr
  have hrr : ∀ x : X, (Quotient.mk'' (r x) : MulAction.orbitRel.Quotient G X) = Quotient.mk'' x :=
    fun x => Quotient.out_eq' _
  have hex : ∀ x : X, ∃ τ : G, τ • r x = x := fun x => mem_orbit_out (G := G) x
  choose τ hτ using hex
  -- the sums of `y` over the orbits vanish
  have hsum : ∑ x, (Pi.single (r x) (y x) : X → ℤ) = 0 := by
    funext p
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.single_apply]
    by_cases hp : ∃ x₀, r x₀ = p
    · obtain ⟨x₀, hx₀⟩ := hp
      have hiff : ∀ x : X, p = r x ↔ x ∈ MulAction.orbit G p := fun x => by
        constructor
        · intro h
          rw [h]
          exact mem_orbit_out (G := G) x
        · intro h
          have h1 : (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) = Quotient.mk'' p :=
            Quotient.sound' (MulAction.orbitRel_apply.mpr h)
          have h2 : (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) = Quotient.mk'' x₀ := by
            rw [h1, ← hx₀, hrr]
          rw [← hx₀]
          exact (congrArg Quotient.out h2).symm
      have hN := actionNorm_permRep_apply (G := G) y p
      rw [hy, Pi.zero_apply] at hN
      have h0 := (mul_eq_zero.mp hN.symm).resolve_left
        (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      rw [Finset.sum_congr rfl fun x _ => if_congr (hiff x) rfl rfl, ← Finset.sum_filter]
      exact h0
    · refine Finset.sum_eq_zero fun x _ => if_neg fun h => hp ⟨x, h.symm⟩
  have hy' : y = ∑ x, ((Pi.single x (y x) : X → ℤ) - Pi.single (r x) (y x)) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.univ_sum_single]
  rw [hy']
  refine sum_mem fun x _ => ?_
  have h := sub_rep_mem_range_actionDiff (ρ := permRep G X) hσ (τ x) (Pi.single (r x) (y x))
  rw [permRep_single, hτ x] at h
  rw [← neg_sub]
  exact neg_mem h

/-- **`Ĥ⁰` of a permutation module**: `[(ℤ^X)^G : N ℤ^X] = Π_ω |G_ω|`, the product over the
orbits of the orders of the stabilizers. -/
theorem herbrandIndex_actionDiff_permRep {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    herbrandIndex (actionDiff (permRep G X) σ) (actionNorm (permRep G X)) =
      ∏ ω : MulAction.orbitRel.Quotient G X, Nat.card (MulAction.stabilizer G ω.out) := by
  refine le_antisymm (herbrandIndex_permRep_le hσ) ?_
  set f := actionDiff (permRep G X) σ
  set g := actionNorm (permRep G X)
  set m : MulAction.orbitRel.Quotient G X → ℕ := fun ω => Nat.card (MulAction.stabilizer G ω.out)
  haveI : ∀ ω, NeZero (m ω) := fun ω => ⟨Nat.card_pos.ne'⟩
  -- the values at the chosen points of the orbits, modulo the orders of the stabilizers
  let Θ : (X → ℤ) →+ (∀ ω : MulAction.orbitRel.Quotient G X, ZMod (m ω)) :=
    { toFun := fun y ω => ((y ω.out : ℤ) : ZMod (m ω))
      map_zero' := funext fun ω => by simp
      map_add' := fun y z => funext fun ω => by simp }
  -- norms are invariant and divisible by `|G_ω|` on the orbit `ω`
  have hle : g.range ≤ Θ.ker ⊓ f.ker := by
    rintro _ ⟨z, rfl⟩
    refine AddSubgroup.mem_inf.mpr ⟨AddMonoidHom.mem_ker.mpr (funext fun ω => ?_),
      AddMonoidHom.mem_ker.mpr (actionDiff_actionNorm _ σ z)⟩
    show ((actionNorm (permRep G X) z ω.out : ℤ) : ZMod (m ω)) = 0
    rw [actionNorm_permRep_apply, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  -- every system of residues comes from a function on the orbits
  have hsurj : f.ker.map Θ = ⊤ := by
    refine eq_top_iff.mpr fun t _ => ?_
    let Y : MulAction.orbitRel.Quotient G X → ℤ := fun ω => (t ω).cast
    refine ⟨fun x => Y (Quotient.mk'' x), AddMonoidHom.mem_ker.mpr (funext fun x => ?_),
      funext fun ω => ?_⟩
    · show Y (Quotient.mk'' (σ⁻¹ • x)) - Y (Quotient.mk'' x) = 0
      rw [show (Quotient.mk'' (σ⁻¹ • x) : MulAction.orbitRel.Quotient G X) = Quotient.mk'' x from
        Quotient.sound' (MulAction.orbitRel_apply.mpr ⟨σ⁻¹, rfl⟩), sub_self]
    · show ((Y (Quotient.mk'' ω.out) : ℤ) : ZMod (m ω)) = t ω
      rw [Quotient.out_eq']
      exact ZMod.intCast_zmod_cast (t ω)
  have hne : g.range.relIndex f.ker ≠ 0 := herbrandIndex_actionDiff_ne_zero hσ
  calc ∏ ω, m ω = Nat.card (∀ ω : MulAction.orbitRel.Quotient G X, ZMod (m ω)) := by
        rw [Nat.card_pi]
        exact (Finset.prod_congr rfl fun ω _ => Nat.card_zmod (m ω)).symm
    _ = Nat.card (f.ker.map Θ) := by
        rw [hsurj]
        exact (Nat.card_congr AddSubgroup.topEquiv.toEquiv).symm
    _ = Θ.ker.relIndex f.ker := (AddSubgroup.relIndex_ker _ _).symm
    _ = (Θ.ker ⊓ f.ker).relIndex f.ker := (AddSubgroup.inf_relIndex_right _ _).symm
    _ ≤ g.range.relIndex f.ker := AddSubgroup.relIndex_le_of_le_left hle hne

end Permutation

section SUnits

variable {L : Type*} [Field L] [NumberField L] {G : Type*} [Group G] [MulSemiringAction G L]

attribute [local instance] primeMulAction infinitePlaceMulAction

variable {S : SubMulAction G (HeightOneSpectrum (𝓞 L))} [Fintype G] [FaithfulSMul G L]
  [Fintype S]

/-- **The norm index of the `S`-units**: `|G| · [L_S^G : N L_S] = Π_ω |G_ω|`, the product over
the orbits of `G` on the infinite places and on `S` of the orders of the stabilizers. -/
theorem card_mul_herbrandSubIndex_sUnits_eq (hS : InvariantDivisorsDescend L G S) {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    Fintype.card G *
        herbrandSubIndex (actionDiff (fieldUnitsRep L G) σ) (actionNorm (fieldUnitsRep L G))
          (sUnits L G S) =
      (∏ ω : MulAction.orbitRel.Quotient G (InfinitePlace L),
          Nat.card (MulAction.stabilizer G ω.out)) *
        ∏ ω : MulAction.orbitRel.Quotient G S, Nat.card (MulAction.stabilizer G ω.out) := by
  have h := card_mul_herbrandSubIndex_sUnits L G S hσ
  rwa [herbrandSubIndex_actionNorm_sUnits_eq_one hS hσ, herbrandIndex_actionNorm_permRep hσ,
    herbrandIndex_actionNorm_permRep hσ, herbrandIndex_actionDiff_permRep hσ,
    herbrandIndex_actionDiff_permRep hσ, mul_one, mul_one, mul_one] at h

/-- The norms of the `S`-units have finite index in the invariant `S`-units. -/
theorem herbrandSubIndex_actionDiff_sUnits_ne_zero (hS : InvariantDivisorsDescend L G S) {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    herbrandSubIndex (actionDiff (fieldUnitsRep L G) σ) (actionNorm (fieldUnitsRep L G))
      (sUnits L G S) ≠ 0 := fun h0 => by
  have h := card_mul_herbrandSubIndex_sUnits_eq hS hσ
  rw [h0, mul_zero] at h
  exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ω _ => Nat.card_pos.ne')
    (Finset.prod_ne_zero_iff.mpr fun ω _ => Nat.card_pos.ne')) h.symm

end SUnits

end GaloisForLFunctions
