/-
# Böttcher tower — Tier 1: the one-coordinate monodromy obstruction (abstract algebraic core)

This is the bottom-most load-bearing block of the q62 formalization
(`unbounded-one-coordinate-monodromy-obstruction.md`). It contains NO analysis:
purely the algebra that turns "one coordinate is moved by arbitrarily high-order
scalar monodromy while the other is fixed" into "no nonzero polynomial relation".

Built bottom-up; each lemma compiles against Mathlib (lean4 v4.30.0).
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.OrderOfElement

open Polynomial

namespace Bottcher

/-- **T1a.** A polynomial over an integral domain that vanishes on a finite set of
strictly more than `natDegree` distinct points is the zero polynomial. -/
theorem eq_zero_of_card_roots_gt_natDegree
    {R : Type*} [CommRing R] [IsDomain R]
    (p : R[X]) (S : Finset R) (hS : ∀ x ∈ S, p.eval x = 0)
    (hcard : p.natDegree < S.card) : p = 0 := by
  classical
  by_contra hp
  have hsub : S ⊆ p.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hp, hS x hx⟩
  have h1 : S.card ≤ p.roots.toFinset.card := Finset.card_le_card hsub
  have h2 : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
  have h3 : Multiset.card p.roots ≤ p.natDegree := Polynomial.card_roots' p
  omega

/-- **T1b.** With `ζ` of order `m` and `f ≠ 0` in a field, the map `k ↦ ζ^k * f` is
injective on `{k | k < m}`: the `m` rotates of `f` under the monodromy multiplier are
pairwise distinct. -/
theorem rotate_injOn {M : Type*} [Field M] {ζ : M} {m : ℕ} (hζ : orderOf ζ = m)
    {f : M} (hf : f ≠ 0) :
    Set.InjOn (fun k : ℕ => ζ ^ k * f) (Set.Iio m) := by
  intro j hj k hk hjk
  have hpow : ζ ^ j = ζ ^ k := mul_right_cancel₀ hf hjk
  have hinj := pow_injOn_Iio_orderOf (x := ζ)
  rw [hζ] at hinj
  exact hinj hj hk hpow

/-- **T1c (scalar core of the one-coordinate monodromy obstruction).**
A polynomial of degree `< m` over a field that vanishes at every rotate `ζ^k · f`
(`k < m`) of a nonzero `f`, where the monodromy multiplier `ζ` has order `m`, is the
zero polynomial. This is the finite-degree contradiction in
`unbounded-one-coordinate-monodromy-obstruction.md`: arbitrarily high-order scalar
monodromy on one coordinate cannot be absorbed by any fixed-degree relation. -/
theorem eq_zero_of_high_monodromy {M : Type*} [Field M]
    {ζ : M} {m : ℕ} (hζ : orderOf ζ = m) {f : M} (hf : f ≠ 0)
    (P : M[X]) (hP : ∀ k : ℕ, k < m → P.eval (ζ ^ k * f) = 0)
    (hdeg : P.natDegree < m) : P = 0 := by
  classical
  set S : Finset M := (Finset.range m).image (fun k => ζ ^ k * f) with hSdef
  have hinj : Set.InjOn (fun k : ℕ => ζ ^ k * f) ↑(Finset.range m) := by
    rw [Finset.coe_range]; exact rotate_injOn hζ hf
  have hcard : S.card = m := by
    rw [hSdef, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hroots : ∀ x ∈ S, P.eval x = 0 := by
    intro x hx
    rw [hSdef, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact hP k (Finset.mem_range.mp hk)
  exact eq_zero_of_card_roots_gt_natDegree P S hroots (by omega)

end Bottcher

namespace Bottcher

/-- A monoid with elements of arbitrarily large finite order cannot be finite. This is the algebraic
finite-type obstruction behind the dyadic Böttcher monodromy card: any finite monodromy carrier has a
uniform order bound, namely its cardinality. -/
theorem not_finite_of_unbounded_order {G : Type*} [Monoid G]
    (h : ∀ d : ℕ, ∃ x : G, d < orderOf x) : ¬ Finite G := by
  intro hfin
  haveI : Finite G := hfin
  obtain ⟨x, hx⟩ := h (Nat.card G)
  exact (not_lt_of_ge (orderOf_le_card (x := x))) hx

end Bottcher

namespace Bottcher

/-- A power-divisible group has no nontrivial finite quotient by a normal subgroup. This is the
algebraic core of the finite-cover Böttcher-Prüfer obstruction: finite quotients have exponent bounded
by their cardinality, while divisibility lets every element be an `N`-th power. -/
theorem subgroup_eq_top_of_powerDivisible_finite_quotient {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, x ^ n = g)
    [Finite (G ⧸ H)] : H = ⊤ := by
  ext g
  constructor
  · intro _
    trivial
  · intro _
    let N := Nat.card (G ⧸ H)
    have hN : 0 < N := Nat.card_pos
    obtain ⟨x, hx⟩ := hdiv N hN g
    have hq : (QuotientGroup.mk x : G ⧸ H) ^ N = 1 := pow_card_eq_one'
    have hmk : (QuotientGroup.mk g : G ⧸ H) = 1 := by
      rw [← hx]
      simpa using hq
    exact (QuotientGroup.eq_one_iff g).mp hmk

/-- Finite-index version of `subgroup_eq_top_of_powerDivisible_finite_quotient`. -/
theorem subgroup_eq_top_of_powerDivisible_finiteIndex {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, x ^ n = g) : H = ⊤ := by
  exact subgroup_eq_top_of_powerDivisible_finite_quotient H hdiv

end Bottcher

namespace Bottcher

/-- Homomorphism form of the finite-cover obstruction: a power-divisible group maps trivially to every
finite group. -/
theorem monoidHom_eq_one_of_powerDivisible_finite_codomain {G Q : Type*} [Group G] [Group Q]
    [Finite Q] (φ : G →* Q)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, x ^ n = g) :
    ∀ g : G, φ g = 1 := by
  intro g
  let N := Nat.card Q
  have hN : 0 < N := Nat.card_pos
  obtain ⟨x, hx⟩ := hdiv N hN g
  rw [← hx, map_pow]
  exact pow_card_eq_one'

end Bottcher

namespace Bottcher

/-- Finite-image form of the finite-cover obstruction: a power-divisible group has no nontrivial finite
monodromy image. -/
theorem monoidHom_eq_one_of_powerDivisible_finite_range {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) [Finite φ.range]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, x ^ n = g) :
    ∀ g : G, φ g = 1 := by
  intro g
  have hφ := monoidHom_eq_one_of_powerDivisible_finite_codomain φ.rangeRestrict hdiv g
  exact Subtype.ext_iff.mp hφ

end Bottcher

namespace Bottcher

/-- Additive finite-quotient form: an `n`-divisible abelian group has no nontrivial finite quotient. -/
theorem addSubgroup_eq_top_of_nsmulDivisible_finite_quotient {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, n • x = g)
    [Finite (G ⧸ H)] : H = ⊤ := by
  ext g
  constructor
  · intro _
    trivial
  · intro _
    let N := Nat.card (G ⧸ H)
    have hN : 0 < N := Nat.card_pos
    obtain ⟨x, hx⟩ := hdiv N hN g
    have hq : N • (QuotientAddGroup.mk x : G ⧸ H) = 0 := card_nsmul_eq_zero'
    have hmk : (QuotientAddGroup.mk g : G ⧸ H) = 0 := by
      rw [← hx]
      simpa using hq
    exact (QuotientAddGroup.eq_zero_iff g).mp hmk

/-- Additive finite-index form: an `n`-divisible abelian group has no proper finite-index subgroup. -/
theorem addSubgroup_eq_top_of_nsmulDivisible_finiteIndex {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) [H.FiniteIndex]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, n • x = g) : H = ⊤ := by
  exact addSubgroup_eq_top_of_nsmulDivisible_finite_quotient H hdiv

/-- Additive homomorphism form: an `n`-divisible abelian group maps trivially to every finite abelian
group. -/
theorem addMonoidHom_eq_zero_of_nsmulDivisible_finite_codomain {G Q : Type*}
    [AddCommGroup G] [AddCommGroup Q] [Finite Q] (φ : G →+ Q)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, n • x = g) :
    ∀ g : G, φ g = 0 := by
  intro g
  let N := Nat.card Q
  have hN : 0 < N := Nat.card_pos
  obtain ⟨x, hx⟩ := hdiv N hN g
  rw [← hx, map_nsmul]
  exact card_nsmul_eq_zero'

/-- Additive finite-image form: an `n`-divisible abelian group has no nontrivial finite homomorphic
image. -/
theorem addMonoidHom_eq_zero_of_nsmulDivisible_finite_range {G Q : Type*}
    [AddCommGroup G] [AddCommGroup Q] (φ : G →+ Q) [Finite φ.range]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, n • x = g) :
    ∀ g : G, φ g = 0 := by
  intro g
  have hφ := addMonoidHom_eq_zero_of_nsmulDivisible_finite_codomain φ.rangeRestrict hdiv g
  exact Subtype.ext_iff.mp hφ

end Bottcher

namespace Bottcher

/-- If a subgroup `D` is `n`-divisible inside an ambient abelian group, then every finite quotient of the
ambient group kills `D`. Equivalently, `D` is contained in the finite-quotient kernel `B`. -/
theorem addSubgroup_le_of_nsmulDivisible_of_finite_quotient {A : Type*} [AddCommGroup A]
    (D B : AddSubgroup A)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ d : A, d ∈ D → ∃ e : A, e ∈ D ∧ n • e = d)
    [Finite (A ⧸ B)] : D ≤ B := by
  intro d hd
  let N := Nat.card (A ⧸ B)
  have hN : 0 < N := Nat.card_pos
  obtain ⟨e, _heD, heq⟩ := hdiv N hN d hd
  have hq : N • (QuotientAddGroup.mk e : A ⧸ B) = 0 := card_nsmul_eq_zero'
  have hmk : (QuotientAddGroup.mk d : A ⧸ B) = 0 := by
    rw [← heq]
    simpa using hq
  exact (QuotientAddGroup.eq_zero_iff d).mp hmk

/-- Finite-index version of `addSubgroup_le_of_nsmulDivisible_of_finite_quotient`. This is the exact
algebra behind `B ∩ D = D` in the Böttcher-Prüfer finite-cover card. -/
theorem addSubgroup_le_of_nsmulDivisible_of_finiteIndex {A : Type*} [AddCommGroup A]
    (D B : AddSubgroup A) [B.FiniteIndex]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ d : A, d ∈ D → ∃ e : A, e ∈ D ∧ n • e = d) :
    D ≤ B := by
  exact addSubgroup_le_of_nsmulDivisible_of_finite_quotient D B hdiv

/-- Intersection form of the finite-index containment: `B ∩ D = D` for a finite-index `B` and divisible
subgroup `D`. -/
theorem addSubgroup_inf_eq_right_of_nsmulDivisible_of_finiteIndex {A : Type*} [AddCommGroup A]
    (D B : AddSubgroup A) [B.FiniteIndex]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ d : A, d ∈ D → ∃ e : A, e ∈ D ∧ n • e = d) :
    B ⊓ D = D := by
  exact inf_eq_right.mpr (addSubgroup_le_of_nsmulDivisible_of_finiteIndex D B hdiv)

end Bottcher

namespace Bottcher

/-- Pushforward finite-index lemma: if `H` has finite index in the source, then its image has finite
index inside the homomorphic image. This is the formal version of `rho(H)` having finite index in
`rho(G)`. -/
theorem addSubgroup_map_rangeRestrict_finiteIndex {G A : Type*} [AddGroup G] [AddGroup A]
    (H : AddSubgroup G) [H.FiniteIndex] (ρ : G →+ A) :
    (H.map ρ.rangeRestrict).FiniteIndex := by
  refine AddSubgroup.FiniteIndex.mk ?_
  intro hzero
  have hdiv := H.index_map_dvd (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
  rw [hzero] at hdiv
  exact AddSubgroup.FiniteIndex.index_ne_zero (Nat.zero_dvd.mp hdiv)

/-- Finite-index cover subgroup image contains every divisible subgroup of the full monodromy image. -/
theorem addSubgroup_le_map_rangeRestrict_of_nsmulDivisible_finiteIndex
    {G A : Type*} [AddGroup G] [AddCommGroup A]
    (H : AddSubgroup G) [H.FiniteIndex] (ρ : G →+ A) (D : AddSubgroup ρ.range)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ d : ρ.range, d ∈ D → ∃ e : ρ.range, e ∈ D ∧ n • e = d) :
    D ≤ H.map ρ.rangeRestrict := by
  haveI : (H.map ρ.rangeRestrict).FiniteIndex :=
    addSubgroup_map_rangeRestrict_finiteIndex H ρ
  exact addSubgroup_le_of_nsmulDivisible_of_finiteIndex D (H.map ρ.rangeRestrict) hdiv

/-- Intersection form of `addSubgroup_le_map_rangeRestrict_of_nsmulDivisible_finiteIndex`. -/
theorem addSubgroup_inf_map_rangeRestrict_eq_right_of_nsmulDivisible_finiteIndex
    {G A : Type*} [AddGroup G] [AddCommGroup A]
    (H : AddSubgroup G) [H.FiniteIndex] (ρ : G →+ A) (D : AddSubgroup ρ.range)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ d : ρ.range, d ∈ D → ∃ e : ρ.range, e ∈ D ∧ n • e = d) :
    (H.map ρ.rangeRestrict) ⊓ D = D := by
  exact inf_eq_right.mpr (addSubgroup_le_map_rangeRestrict_of_nsmulDivisible_finiteIndex H ρ D hdiv)

end Bottcher

namespace Bottcher

/-- If a nonzero subgroup of the monodromy image is contained in the image of `H`, then the restriction
of the monodromy homomorphism to `H` is nontrivial. -/
theorem exists_mem_subgroup_apply_ne_zero_of_nontrivial_subgroup
    {G A : Type*} [AddGroup G] [AddGroup A]
    (H : AddSubgroup G) (ρ : G →+ A) (D : AddSubgroup ρ.range)
    (hD : D ≤ H.map ρ.rangeRestrict)
    (hne : ∃ d : ρ.range, d ∈ D ∧ d ≠ 0) :
    ∃ h : G, h ∈ H ∧ ρ h ≠ 0 := by
  obtain ⟨d, hdD, hdne⟩ := hne
  have hdmap : d ∈ H.map ρ.rangeRestrict := hD hdD
  obtain ⟨h, hhH, hh⟩ := AddSubgroup.mem_map.mp hdmap
  refine ⟨h, hhH, ?_⟩
  intro hrho
  apply hdne
  rw [← hh]
  ext
  exact hrho

/-- Finite-cover nontriviality step: a nonzero divisible subgroup of the full monodromy image remains
visible on every finite-index subgroup of the source. -/
theorem exists_mem_finiteIndex_subgroup_apply_ne_zero_of_nsmulDivisible_nontrivial
    {G A : Type*} [AddGroup G] [AddCommGroup A]
    (H : AddSubgroup G) [H.FiniteIndex] (ρ : G →+ A) (D : AddSubgroup ρ.range)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ d : ρ.range, d ∈ D → ∃ e : ρ.range, e ∈ D ∧ n • e = d)
    (hne : ∃ d : ρ.range, d ∈ D ∧ d ≠ 0) :
    ∃ h : G, h ∈ H ∧ ρ h ≠ 0 := by
  exact exists_mem_subgroup_apply_ne_zero_of_nontrivial_subgroup H ρ D
    (addSubgroup_le_map_rangeRestrict_of_nsmulDivisible_finiteIndex H ρ D hdiv) hne

/-- Contradiction form of the finite-cover nontriviality step: the monodromy homomorphism cannot vanish
on every element of a finite-index subgroup if its full image contains a nonzero divisible subgroup. -/
theorem not_forall_mem_finiteIndex_subgroup_apply_eq_zero_of_nsmulDivisible_nontrivial
    {G A : Type*} [AddGroup G] [AddCommGroup A]
    (H : AddSubgroup G) [H.FiniteIndex] (ρ : G →+ A) (D : AddSubgroup ρ.range)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ d : ρ.range, d ∈ D → ∃ e : ρ.range, e ∈ D ∧ n • e = d)
    (hne : ∃ d : ρ.range, d ∈ D ∧ d ≠ 0) :
    ¬ ∀ h : G, h ∈ H → ρ h = 0 := by
  obtain ⟨h, hhH, hρ⟩ :=
    exists_mem_finiteIndex_subgroup_apply_ne_zero_of_nsmulDivisible_nontrivial H ρ D hdiv hne
  intro htriv
  exact hρ (htriv h hhH)

end Bottcher
