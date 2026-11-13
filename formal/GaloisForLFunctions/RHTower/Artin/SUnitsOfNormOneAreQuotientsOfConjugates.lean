import GaloisForLFunctions.RHTower.Artin.TheHerbrandQuotientOfTheSUnits
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# `S`-units of norm one are quotients of conjugates

Let a finite cyclic group `G = ⟨σ⟩` act faithfully on a field `L`.

* **Hilbert 90** (`exists_smul_div_eq_of_prod_smul_eq_one`): if `Π_τ τ x = 1`, then
  `x = σ y / y` for some `y ≠ 0`. With `p_i = x · σx ⋯ σ^{i−1}x` and
  `R(c) = Σ_{i < n} p_i σ^i(c)`, `x σ(R(c)) = R(c)`, and `R(c) ≠ 0` for some `c`, because the
  automorphisms `σ^i`, `i < n`, are linearly independent over `L`.

Let `L` be a number field and `S` a set of primes of `L` stable under `G` such that the
`G`-invariant divisors prime to `S` descend (`InvariantDivisorsDescend`): if `v_{τ w}(y) = v_w(y)`
for all `w ∉ S` and `τ`, then `y = c z` with `c` fixed by `G` and `z` an `S`-unit.

* **`H¹(G, L_S) = 0`** (`herbrandSubIndex_actionNorm_sUnits_eq_one`): an `S`-unit `x` of norm
  one is `σ z / z` for an `S`-unit `z`. Indeed `x = σ y / y`, and `v_w(σ y) = v_w(y)` for `w ∉ S`
  makes the divisor of `y` invariant outside `S`.
* **The norm index of the `S`-units** (`card_mul_herbrandSubIndex_sUnits_le_prod`):
  `|G| · [L_S^G : N L_S] ≤ Π_ω |G_ω|`, the product over the orbits of `G` on the infinite places
  and on `S`.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain HeightOneSpectrum

noncomputable section

namespace GaloisForLFunctions

section Hilbert90

variable {L : Type*} [Field L] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G L]
  [FaithfulSMul G L]

/-- **Hilbert 90** for a finite cyclic group `⟨σ⟩` acting faithfully on a field: an element
with `Π_τ τ x = 1` is of the form `σ y / y`. -/
theorem exists_smul_div_eq_of_prod_smul_eq_one {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ)
    {x : L} (hx : ∏ τ : G, τ • x = 1) : ∃ y : L, y ≠ 0 ∧ σ • y / y = x := by
  have hn0 : 0 < orderOf σ := orderOf_pos σ
  -- the partial products `p_i = x · σx ⋯ σ^{i−1}x`
  set p : ℕ → L := fun i => ∏ j ∈ Finset.range i, σ ^ j • x with hp
  have hp0 : p 0 = 1 := Finset.prod_range_zero _
  have hps : ∀ i, p (i + 1) = x * σ • p i := fun i => by
    show ∏ j ∈ Finset.range (i + 1), σ ^ j • x =
      x * MulSemiringAction.toRingHom G L σ (∏ j ∈ Finset.range i, σ ^ j • x)
    rw [Finset.prod_range_succ', pow_zero, one_smul, mul_comm, map_prod]
    refine congrArg _ (Finset.prod_congr rfl fun j _ => ?_)
    show σ ^ (j + 1) • x = σ • σ ^ j • x
    rw [← mul_smul, ← pow_succ']
  have hpn : p (orderOf σ) = 1 := by
    rw [← hx, ← IsCyclic.image_range_orderOf hσ, Finset.prod_image]
    intro i hi j hj h
    exact pow_injOn_Iio_orderOf (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  -- the resolvent
  set R : L → L := fun c => ∑ i ∈ Finset.range (orderOf σ), p i * σ ^ i • c with hR
  have hRσ : ∀ c, x * σ • R c = R c := fun c => by
    have h1 : x * σ • R c = ∑ i ∈ Finset.range (orderOf σ), p (i + 1) * σ ^ (i + 1) • c := by
      show x * MulSemiringAction.toRingHom G L σ
        (∑ i ∈ Finset.range (orderOf σ), p i * σ ^ i • c) = _
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← mul_assoc, hps]
      refine congrArg _ ?_
      show σ • σ ^ i • c = σ ^ (i + 1) • c
      rw [← mul_smul, ← pow_succ']
    have h2 := Finset.sum_range_succ' (fun i => p i * σ ^ i • c) (orderOf σ)
    rw [Finset.sum_range_succ, hpn, pow_orderOf_eq_one, hp0, pow_zero] at h2
    rw [h1]
    exact (add_right_cancel h2).symm
  -- the automorphisms `σ^i`, `i < n`, are linearly independent
  obtain ⟨c, hc⟩ : ∃ c, R c ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    let χ : Fin (orderOf σ) → (L →* L) := fun i =>
      (MulSemiringAction.toRingHom G L (σ ^ (i : ℕ)) : L →* L)
    have hχ : Function.Injective χ := fun i j hij => by
      refine Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 ?_)
      exact eq_of_smul_eq_smul fun a : L => (DFunLike.congr_fun hij a : _)
    have hli := (linearIndependent_monoidHom L L).comp χ hχ
    have hsum : ∑ i : Fin (orderOf σ), p i • ((fun f : L →* L => (f : L → L)) ∘ χ) i = 0 := by
      funext a
      rw [Finset.sum_apply]
      exact (Finset.sum_range fun i => p i * σ ^ i • a).symm.trans (hall a)
    have h0 := Fintype.linearIndependent_iff.mp hli (fun i => p i) hsum ⟨0, hn0⟩
    exact one_ne_zero (hp0.symm.trans h0)
  have hσc : σ • R c ≠ 0 := fun h => hc ((smul_eq_zero_iff_eq σ).mp h)
  refine ⟨(R c)⁻¹, inv_ne_zero hc, ?_⟩
  rw [smul_inv'', inv_div_inv, div_eq_iff hσc]
  exact (hRσ c).symm

/-- Hilbert 90 in the group `L^×`: the kernel of the norm is the image of `σ − 1`. -/
theorem mem_range_actionDiff_of_actionNorm_eq_zero {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) {x : Additive Lˣ}
    (hx : actionNorm (fieldUnitsRep L G) x = 0) :
    x ∈ (actionDiff (fieldUnitsRep L G) σ).range := by
  have hprod : ∏ τ : G, τ • ((Additive.toMul x : Lˣ) : L) = 1 := by
    rw [actionNorm_apply] at hx
    have h := congrArg (fun z : Additive Lˣ => ((Additive.toMul z : Lˣ) : L)) hx
    simp only [toMul_sum, Units.coe_prod, toMul_zero, Units.val_one] at h
    exact h
  obtain ⟨y, hy, hxy⟩ := exists_smul_div_eq_of_prod_smul_eq_one hσ hprod
  refine ⟨Additive.ofMul (Units.mk0 y hy), ?_⟩
  rw [actionDiff_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  rw [Units.val_div_eq_div_val]
  exact hxy

end Hilbert90

section SUnits

variable (L : Type*) [Field L] [NumberField L] (G : Type*) [Group G] [MulSemiringAction G L]

attribute [local instance] primeMulAction infinitePlaceMulAction

variable (S : SubMulAction G (HeightOneSpectrum (𝓞 L)))

/-- The `G`-invariant divisors prime to `S` descend: an element whose exponents outside `S` are
constant on the orbits of `G` is the product of an element fixed by `G` and an `S`-unit. -/
def InvariantDivisorsDescend : Prop :=
  ∀ y : Additive Lˣ, (∀ w, w ∉ S → ∀ τ : G, ordAt L (τ • w) y = ordAt L w y) →
    ∃ c : Additive Lˣ, (∀ τ : G, fieldUnitsRep L G τ c = c) ∧ y - c ∈ sUnits L G S

variable {L G S}

omit [NumberField L] in
theorem smul_notMem_of_notMem {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ S) (τ : G) : τ • w ∉ S :=
  fun h => hw (by simpa using S.smul_mem τ⁻¹ h)

variable [Fintype G] [FaithfulSMul G L]

/-- **`H¹(G, L_S) = 0`**: an `S`-unit of norm one is `σ z / z` for an `S`-unit `z`. -/
theorem herbrandSubIndex_actionNorm_sUnits_eq_one (hS : InvariantDivisorsDescend L G S) {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    herbrandSubIndex (actionNorm (fieldUnitsRep L G)) (actionDiff (fieldUnitsRep L G) σ)
      (sUnits L G S) = 1 := by
  refine AddSubgroup.relIndex_eq_one.mpr fun x hx => ?_
  obtain ⟨hxN, hxC⟩ := AddSubgroup.mem_inf.mp hx
  obtain ⟨y, rfl⟩ := mem_range_actionDiff_of_actionNorm_eq_zero hσ (AddMonoidHom.mem_ker.mp hxN)
  -- the divisor of `y` is invariant outside `S`
  let H : Subgroup G :=
    { carrier := {τ | ∀ w, w ∉ S → ordAt L (τ • w) y = ordAt L w y}
      one_mem' := fun w _ => by rw [one_smul]
      mul_mem' := fun {τ τ'} hτ hτ' w hw => by
        rw [mul_smul, hτ _ (smul_notMem_of_notMem hw τ'), hτ' w hw]
      inv_mem' := fun {τ} hτ w hw => by
        have h := hτ _ (smul_notMem_of_notMem hw τ⁻¹)
        rw [smul_inv_smul] at h
        exact h.symm }
  have hσH : σ⁻¹ ∈ H := fun w hw => by
    have h := hxC w hw
    rw [actionDiff_apply, map_sub, ordAt_fieldUnitsRep, sub_eq_zero] at h
    exact h
  have hH : ∀ τ : G, τ ∈ H := fun τ =>
    Subgroup.zpowers_le.mpr (by simpa using H.inv_mem hσH) (hσ τ)
  obtain ⟨c, hc, hyc⟩ := hS y fun w hw τ => hH τ w hw
  refine ⟨y - c, hyc, ?_⟩
  rw [map_sub, actionDiff_apply (fieldUnitsRep L G) σ c, hc σ, sub_self, sub_zero]

variable [Fintype S]

/-- **The norm index of the `S`-units**: `|G| · [L_S^G : N L_S] ≤ Π_ω |G_ω|`, the product over
the orbits of `G` on the infinite places and on `S` of the orders of the stabilizers. -/
theorem card_mul_herbrandSubIndex_sUnits_le_prod (hS : InvariantDivisorsDescend L G S) {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    Fintype.card G *
        herbrandSubIndex (actionDiff (fieldUnitsRep L G) σ) (actionNorm (fieldUnitsRep L G))
          (sUnits L G S) ≤
      (∏ ω : MulAction.orbitRel.Quotient G (InfinitePlace L),
          Nat.card (MulAction.stabilizer G ω.out)) *
        ∏ ω : MulAction.orbitRel.Quotient G S, Nat.card (MulAction.stabilizer G ω.out) := by
  have h := card_mul_herbrandSubIndex_sUnits_le L G S hσ
  rwa [herbrandSubIndex_actionNorm_sUnits_eq_one hS hσ, mul_one] at h

end SUnits

end GaloisForLFunctions
