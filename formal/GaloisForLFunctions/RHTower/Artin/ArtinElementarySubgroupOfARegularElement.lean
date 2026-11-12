import GaloisForLFunctions.RHTower.Artin.ArtinBrauerElementary
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.Sylow

/-!
# The elementary subgroup of a `p`-regular element

Let `x` be an element of a group `G` whose order is prime to `p`, and `P` a `p`-subgroup of the
centralizer of `x`.

* The product map `⟨x⟩ × P → G`, `(c, q) ↦ c q` (`elementaryHom`), is injective
  (`elementaryHom_injective`): an element of `⟨x⟩ ∩ P` has order prime to `p` and a power of `p`.
  Its range `⟨x⟩ · P` (`elementarySubgroup`) is therefore a direct product
  (`elementaryEquiv`), of order `|⟨x⟩| · |P|` (`card_elementarySubgroup`).
* It is Brauer `p`-elementary (`elementarySubgroup_mem_brauerElementaryFamily`); in particular
  every cyclic subgroup of a finite group is Brauer elementary
  (`zpowers_mem_brauerElementaryFamily`, with `P = 1` and a prime not dividing the order).
* A `p`-regular element `x q` with `q` in `P` equals `x` (`eq_one_of_regular_mul`): the
  `p`-regular elements of `⟨x⟩ · P` lie in `⟨x⟩`.
* `centralizerSylow p x` is a Sylow `p`-subgroup of the centralizer of `x`; its index in the
  centralizer is prime to `p` (`card_centralizer_eq`, `not_dvd_centralizerSylowIndex`).
-/

noncomputable section

universe u

namespace GaloisForLFunctions

variable {G : Type u} [Group G]

/-- An element killed by `m` and by a power of `p`, with `m` prime to `p`, is trivial. -/
theorem eq_one_of_pow_eq_one_of_coprime {g : G} {m p k : ℕ} (hm : g ^ m = 1)
    (hk : g ^ p ^ k = 1) (hcop : m.Coprime p) : g = 1 := by
  have h1 : orderOf g ∣ Nat.gcd m (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hk)
  rw [show Nat.gcd m (p ^ k) = 1 from Nat.Coprime.pow_right k hcop] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

/-- A power of `x` is killed by the order of `x`. -/
theorem pow_orderOf_eq_one_of_mem_zpowers {x c : G} (hc : c ∈ Subgroup.zpowers x) :
    c ^ orderOf x = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_of_mem_zpowers hc)

/-- The powers of `x` commute with the centralizer of `x`. -/
theorem commute_of_mem_zpowers_of_mem_centralizer {x c q : G} (hc : c ∈ Subgroup.zpowers x)
    (hq : q ∈ Subgroup.centralizer {x}) : Commute c q := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hq).symm n

/-- **A `p`-regular product `x q`, with `x` of order prime to `p` commuting with `q` of order a
power of `p`, has `q = 1`.** -/
theorem eq_one_of_regular_mul {x q : G} (hcomm : Commute x q) {p k : ℕ}
    (hx : (orderOf x).Coprime p) (hq : q ^ p ^ k = 1) (hz : (orderOf (x * q)).Coprime p) :
    q = 1 := by
  have hpow : x ^ orderOf (x * q) * q ^ orderOf (x * q) = 1 := by
    rw [← hcomm.mul_pow, pow_orderOf_eq_one]
  -- `w = q^m` lies in `⟨x⟩` and has order a power of `p`
  have hw : q ^ orderOf (x * q) = (x ^ orderOf (x * q))⁻¹ := eq_inv_of_mul_eq_one_right hpow
  have hw1 : q ^ orderOf (x * q) = 1 := by
    refine eq_one_of_pow_eq_one_of_coprime (m := orderOf x) (k := k) ?_ ?_ hx
    · rw [hw, inv_pow, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, inv_one]
    · rw [← pow_mul, mul_comm, pow_mul, hq, one_pow]
  exact eq_one_of_pow_eq_one_of_coprime hw1 hq hz

/-! ### The product of the cyclic group with a subgroup of the centralizer -/

section Product

variable (x : G) (P : Subgroup G) (hP : P ≤ Subgroup.centralizer {x})

/-- The product map `⟨x⟩ × P → G`, `(c, q) ↦ c q`, for a subgroup `P` of the centralizer. -/
def elementaryHom : Subgroup.zpowers x × P →* G :=
  (Subgroup.zpowers x).subtype.noncommCoprod P.subtype fun c q =>
    commute_of_mem_zpowers_of_mem_centralizer c.2 (hP q.2)

/-- The subgroup `⟨x⟩ · P`. -/
def elementarySubgroup : Subgroup G :=
  (elementaryHom x P hP).range

theorem elementaryHom_apply (a : Subgroup.zpowers x × P) :
    elementaryHom x P hP a = (a.1 : G) * (a.2 : G) :=
  rfl

theorem zpowers_le_elementarySubgroup : Subgroup.zpowers x ≤ elementarySubgroup x P hP :=
  fun c hc => ⟨(⟨c, hc⟩, 1), by rw [elementaryHom_apply, OneMemClass.coe_one, mul_one]⟩

theorem le_elementarySubgroup : P ≤ elementarySubgroup x P hP :=
  fun q hq => ⟨(1, ⟨q, hq⟩), by rw [elementaryHom_apply, OneMemClass.coe_one, one_mul]⟩

theorem mem_elementarySubgroup : x ∈ elementarySubgroup x P hP :=
  zpowers_le_elementarySubgroup x P hP (Subgroup.mem_zpowers x)

/-- With `P = 1` the subgroup is the cyclic group of `x`. -/
theorem elementarySubgroup_bot :
    elementarySubgroup x ⊥ bot_le = Subgroup.zpowers x := by
  rw [elementarySubgroup, elementaryHom, MonoidHom.noncommCoprod_range, Subgroup.range_subtype,
    Subgroup.range_subtype, sup_bot_eq]

variable {p : ℕ} (hx : (orderOf x).Coprime p) (hPp : IsPGroup p P)

include hx hPp in
/-- **The product map is injective** when the order of `x` is prime to `p` and `P` is a
`p`-group. -/
theorem elementaryHom_injective : Function.Injective (elementaryHom x P hP) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨c, q⟩ h
  have h' : (c : G) * (q : G) = 1 := h
  obtain ⟨k, hk⟩ := hPp q
  have hk' : (q : G) ^ p ^ k = 1 := by
    rw [← SubmonoidClass.coe_pow, hk, OneMemClass.coe_one]
  have hc1 : (c : G) = 1 := by
    refine eq_one_of_pow_eq_one_of_coprime (pow_orderOf_eq_one_of_mem_zpowers c.2) ?_ hx (k := k)
    rw [eq_inv_of_mul_eq_one_left h', inv_pow, hk', inv_one]
  have hq1 : (q : G) = 1 := by
    rw [hc1, one_mul] at h'
    exact h'
  exact Prod.ext (Subtype.ext hc1) (Subtype.ext hq1)

/-- `⟨x⟩ × P ≃ ⟨x⟩ · P`. -/
def elementaryEquiv : Subgroup.zpowers x × P ≃* elementarySubgroup x P hP :=
  MonoidHom.ofInjective (elementaryHom_injective x P hP hx hPp)

theorem coe_elementaryEquiv (a : Subgroup.zpowers x × P) :
    (elementaryEquiv x P hP hx hPp a : G) = (a.1 : G) * (a.2 : G) :=
  rfl

/-- Every element of `⟨x⟩ · P` is the product of its two coordinates. -/
theorem coe_eq_mul_elementaryEquiv_symm (h : elementarySubgroup x P hP) :
    (h : G) = (((elementaryEquiv x P hP hx hPp).symm h).1 : G) *
      (((elementaryEquiv x P hP hx hPp).symm h).2 : G) := by
  rw [← coe_elementaryEquiv x P hP hx hPp, MulEquiv.apply_symm_apply]

/-- The coordinates of `x` are `(x, 1)`. -/
theorem elementaryEquiv_symm_self :
    (elementaryEquiv x P hP hx hPp).symm ⟨x, mem_elementarySubgroup x P hP⟩ =
      (⟨x, Subgroup.mem_zpowers x⟩, 1) := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (by rw [coe_elementaryEquiv, OneMemClass.coe_one, mul_one])

/-- **A `p`-regular element of `⟨x⟩ · P` whose first coordinate is `x` equals `x`.** -/
theorem eq_of_regular_of_fst_eq {z : G} (hz : z ∈ elementarySubgroup x P hP)
    (hreg : (orderOf z).Coprime p)
    (hfst : ((elementaryEquiv x P hP hx hPp).symm ⟨z, hz⟩).1 = ⟨x, Subgroup.mem_zpowers x⟩) :
    z = x := by
  have hdec := coe_eq_mul_elementaryEquiv_symm x P hP hx hPp ⟨z, hz⟩
  rw [hfst] at hdec
  obtain ⟨k, hk⟩ := hPp ((elementaryEquiv x P hP hx hPp).symm ⟨z, hz⟩).2
  have hk' : ((((elementaryEquiv x P hP hx hPp).symm ⟨z, hz⟩).2 : P) : G) ^ p ^ k = 1 := by
    rw [← SubmonoidClass.coe_pow, hk, OneMemClass.coe_one]
  have hcomm : Commute x ((((elementaryEquiv x P hP hx hPp).symm ⟨z, hz⟩).2 : P) : G) :=
    commute_of_mem_zpowers_of_mem_centralizer (Subgroup.mem_zpowers x) (hP (Subtype.property _))
  have hz' : z = x * ((((elementaryEquiv x P hP hx hPp).symm ⟨z, hz⟩).2 : P) : G) := hdec
  have hq := eq_one_of_regular_mul hcomm hx hk' (hz' ▸ hreg)
  rw [hz', hq, mul_one]

include hx hPp in
/-- `|⟨x⟩ · P| = |⟨x⟩| · |P|`. -/
theorem card_elementarySubgroup :
    Nat.card (elementarySubgroup x P hP) = orderOf x * Nat.card P := by
  rw [← Nat.card_congr (elementaryEquiv x P hP hx hPp).toEquiv, Nat.card_prod, Nat.card_zpowers]

end Product

/-! ### Brauer-elementary subgroups -/

/-- The Brauer-elementary subgroups of a group: products of a cyclic group of order prime to a
prime `p` with a `p`-group. -/
def brauerElementaryFamily (G : Type u) [Group G] : Set (Subgroup G) :=
  Set.range fun E : BrauerElementarySubgroup G => E.subgroup

/-- **`⟨x⟩ · P` is Brauer `p`-elementary.** -/
theorem elementarySubgroup_mem_brauerElementaryFamily {p : ℕ} (hp : p.Prime) (x : G)
    (P : Subgroup G) (hP : P ≤ Subgroup.centralizer {x}) (hx : (orderOf x).Coprime p)
    (hPp : IsPGroup p P) : elementarySubgroup x P hP ∈ brauerElementaryFamily G := by
  have hC := zpowers_le_elementarySubgroup x P hP
  have hPle := le_elementarySubgroup x P hP
  refine ⟨{
    subgroup := elementarySubgroup x P hP
    p := p
    p_prime := hp
    cyclicPart := (Subgroup.zpowers x).subgroupOf (elementarySubgroup x P hP)
    pPart := P.subgroupOf (elementarySubgroup x P hP)
    cyclicPart_cyclic := (Subgroup.subgroupOfEquivOfLe hC).isCyclic.mpr inferInstance
    cyclicPart_coprime := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv, Nat.card_zpowers]
      exact hx
    pPart_isPGroup := hPp.comap_subtype
    multiplicationEquiv := ((Subgroup.subgroupOfEquivOfLe hC).prodCongr
      (Subgroup.subgroupOfEquivOfLe hPle)).trans (elementaryEquiv x P hP hx hPp)
    multiplicationEquiv_apply := fun c q => Subtype.ext rfl }, rfl⟩

/-- **Every cyclic subgroup of a finite group is Brauer elementary.** -/
theorem zpowers_mem_brauerElementaryFamily [Finite G] (g : G) :
    Subgroup.zpowers g ∈ brauerElementaryFamily G := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (orderOf g + 1)
  have hcop : (orderOf g).Coprime p := by
    refine (Nat.Coprime.symm ?_)
    rw [hp.coprime_iff_not_dvd]
    exact fun hdvd => absurd (Nat.le_of_dvd (orderOf_pos g) hdvd) (by omega)
  rw [← elementarySubgroup_bot g]
  exact elementarySubgroup_mem_brauerElementaryFamily hp g ⊥ bot_le hcop IsPGroup.of_bot

/-! ### A Sylow subgroup of the centralizer -/

section Sylow

variable (p : ℕ) (x : G)

/-- A Sylow `p`-subgroup of the centralizer of `x`, as a subgroup of `G`. -/
def centralizerSylow : Subgroup G :=
  ((default : Sylow p (Subgroup.centralizer {x})) : Subgroup (Subgroup.centralizer {x})).map
    (Subgroup.centralizer {x}).subtype

/-- The index of the chosen Sylow `p`-subgroup in the centralizer of `x`. -/
def centralizerSylowIndex : ℕ :=
  ((default : Sylow p (Subgroup.centralizer {x})) : Subgroup (Subgroup.centralizer {x})).index

theorem centralizerSylow_le : centralizerSylow p x ≤ Subgroup.centralizer {x} :=
  Subgroup.map_subtype_le _

theorem centralizerSylow_isPGroup : IsPGroup p (centralizerSylow p x) :=
  (default : Sylow p (Subgroup.centralizer {x})).isPGroup'.map _

/-- `|Z(x)| = |P| · [Z(x) : P]`. -/
theorem card_centralizer_eq :
    Nat.card (Subgroup.centralizer {x}) =
      Nat.card (centralizerSylow p x) * centralizerSylowIndex p x := by
  rw [centralizerSylow, centralizerSylowIndex,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Subgroup.card_mul_index]

/-- **The index of a Sylow `p`-subgroup of the centralizer is prime to `p`.** -/
theorem not_dvd_centralizerSylowIndex [Fact p.Prime] [Finite G] :
    ¬ p ∣ centralizerSylowIndex p x :=
  (default : Sylow p (Subgroup.centralizer {x})).not_dvd_index

end Sylow

end GaloisForLFunctions
