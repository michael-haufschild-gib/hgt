import GaloisForLFunctions.RHTower.Artin.CongruenceSubgroupsOfANormalBasisLattice

/-!
# Congruence units of norm one are quotients of conjugates

Let `L/K` be an extension of number fields with cyclic group `G = ⟨σ⟩`, `S` a finite `G`-stable
set of primes of `L`, `Λ_j` the normal basis lattices and `W_k = {x : x − 1 ∈ Λ_{k₀+k}}` the
congruence subgroups of `L^×`.

**`H¹(G, W_k) = 0`** (`exists_mem_congruenceSubgroup_actionDiff_eq`): an element `u ∈ W_k` of
norm one is `σz / z` with `z ∈ W_k`. No completion is used; the proof has two steps.

* **One layer** (`exists_div_sub_one_mem_lattice`): write `u = 1 + a`, `a = Σ_τ a_τ τθ`. The norm
  is `1 + Tr a` up to products of two elements of `Λ`, and `Tr a = (Σ_τ a_τ) Tr θ`, so
  `s = Σ_τ a_τ` gains one level. Since `a − sθ = Σ_τ (τ − 1)(a_τ θ)` lies in `(σ − 1) Λ`, there
  is `z = 1 + b ∈ W` with `u z / σz ∈ 1 + Λ` one level deeper.
* **Deep elements** (`exists_actionDiff_eq_of_mem_congruenceSubgroup_add`): let `u = σy / y`
  (Hilbert 90) lie in `W_{k+c}`; then `τy / y ∈ W_{k+c}` for all `τ`. With `c₀` of trace one, the
  average `z' = Σ_τ (τy / y) τc₀` satisfies `z' − 1 = Σ_τ (τy / y − 1) τc₀ ∈ Λ`, a loss of a
  bounded number of levels, and `z' y = Tr(y c₀)` is fixed by `G`; hence `u = σ(z'⁻¹) / z'⁻¹`.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain HeightOneSpectrum

noncomputable section

namespace GaloisForLFunctions

section Generator

variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]

/-- For a subgroup `C` stable under `G = ⟨σ⟩` and `a ∈ C`, `τa − a ∈ (σ − 1) C`. -/
theorem exists_smul_sub_eq_smul_sub [DistribMulAction G A] {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) {C : AddSubgroup A}
    (hC : ∀ (τ : G) (a : A), a ∈ C → τ • a ∈ C) (τ : G) {a : A} (ha : a ∈ C) :
    ∃ c ∈ C, σ • c - c = τ • a - a := by
  let H : Subgroup G :=
    { carrier := {τ | ∀ a ∈ C, ∃ c ∈ C, σ • c - c = τ • a - a}
      one_mem' := fun a _ => ⟨0, zero_mem _, by rw [smul_zero, sub_zero, one_smul, sub_self]⟩
      mul_mem' := fun {τ τ'} hτ hτ' a ha => by
        obtain ⟨c, hc, e⟩ := hτ (τ' • a) (hC τ' a ha)
        obtain ⟨c', hc', e'⟩ := hτ' a ha
        refine ⟨c + c', add_mem hc hc', ?_⟩
        rw [smul_add, mul_smul, add_sub_add_comm, e, e', sub_add_sub_cancel]
      inv_mem' := fun {τ} hτ a ha => by
        obtain ⟨c, hc, e⟩ := hτ (τ⁻¹ • a) (hC τ⁻¹ a ha)
        refine ⟨-c, neg_mem hc, ?_⟩
        rw [smul_inv_smul] at e
        rw [smul_neg, neg_sub_neg, ← neg_sub (σ • c) c, e, neg_sub] }
  exact (Subgroup.zpowers_le (H := H)).mpr (fun a ha => ⟨a, ha, rfl⟩) (hσ τ) a ha

/-- If `σy − y` lies in a subgroup `C` stable under `G = ⟨σ⟩`, so does `τy − y` for all `τ`. -/
theorem rep_sub_mem_of_actionDiff_mem {ρ : G →* AddMonoid.End A} {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) {C : AddSubgroup A}
    (hC : ∀ (τ : G) (a : A), a ∈ C → ρ τ a ∈ C) {y : A} (hy : actionDiff ρ σ y ∈ C) (τ : G) :
    ρ τ y - y ∈ C := by
  let H : Subgroup G :=
    { carrier := {τ | ρ τ y - y ∈ C}
      one_mem' := by
        show ρ 1 y - y ∈ C
        rw [rep_one_apply, sub_self]
        exact zero_mem _
      mul_mem' := fun {τ τ'} hτ hτ' => by
        show ρ (τ * τ') y - y ∈ C
        have e : ρ (τ * τ') y - y = ρ τ (ρ τ' y - y) + (ρ τ y - y) := by
          rw [rep_mul_apply, map_sub]
          abel
        rw [e]
        exact add_mem (hC τ _ hτ') hτ
      inv_mem' := fun {τ} hτ => by
        show ρ τ⁻¹ y - y ∈ C
        have e : ρ τ⁻¹ y - y = -ρ τ⁻¹ (ρ τ y - y) := by
          rw [map_sub, ← rep_mul_apply, inv_mul_cancel, rep_one_apply]
          abel
        rw [e]
        exact neg_mem (hC τ⁻¹ _ hτ) }
  exact (Subgroup.zpowers_le (H := H)).mpr hy (hσ τ)

end Generator

section NormalBasis

variable (K L : Type*) [Field K] [Field L] [Algebra K L] (G : Type*) [Group G] [Fintype G]
  [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- The coordinates of a trace `Σ_ν νa` are all equal to the sum of the coordinates of `a`. -/
theorem repr_sum_smul_galoisNormalBasis (a : L) (μ : G) :
    (galoisNormalBasis K L G).repr (∑ ν : G, ν • a) μ =
      ∑ τ : G, (galoisNormalBasis K L G).repr a τ := by
  rw [map_sum, Finsupp.finsetSum_apply]
  simp_rw [repr_smul_galoisNormalBasis]
  exact Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight μ)) _ _ fun ν => rfl

/-- The coordinates of `1` in the normal basis are equal. -/
theorem repr_one_galoisNormalBasis (μ : G) :
    (galoisNormalBasis K L G).repr 1 μ = (galoisNormalBasis K L G).repr 1 1 := by
  have h := repr_smul_galoisNormalBasis K L G μ 1 μ
  rwa [smul_one, inv_mul_cancel] at h

/-- An element `c₀ = rθ` of trace one, `r` the common coordinate of `1`. -/
def traceOneElement : L := (galoisNormalBasis K L G).repr 1 1 • galoisNormalBasis K L G 1

theorem smul_traceOneElement (τ : G) :
    τ • traceOneElement K L G =
      (galoisNormalBasis K L G).repr 1 τ • galoisNormalBasis K L G τ := by
  haveI : SMulCommClass G K L := IsGaloisGroup.commutes
  rw [traceOneElement, smul_comm, smul_galoisNormalBasis, mul_one,
    repr_one_galoisNormalBasis K L G τ]

theorem sum_smul_traceOneElement : ∑ τ : G, τ • traceOneElement K L G = 1 := by
  rw [Finset.sum_congr rfl fun τ _ => smul_traceOneElement K L G τ]
  exact (galoisNormalBasis K L G).sum_repr 1

end NormalBasis

section Lattice

variable {K : Type*} {L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] {G : Type*}
  [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction

variable {S : SubMulAction G (HeightOneSpectrum (𝓞 L))}

/-- A multiple of a basis element by a scalar of level `j` lies in the lattice of level `j`. -/
theorem smul_galoisNormalBasis_mem_lattice {j : ℤ} {β : K}
    (hβ : algebraMap K L β ∈ level L G S j) (τ : G) :
    β • galoisNormalBasis K L G τ ∈ lattice K S j := by
  have h := smul_mem_lattice hβ (galoisNormalBasis_mem_lattice (K := K) (S := S) τ)
  rwa [add_zero] at h

/-- `a = (σ − 1) b + sθ` with `b ∈ Λ_k`, for `a ∈ Λ_k` with sum of coordinates `s`. -/
theorem exists_smul_sub_eq_sub_sum_repr_smul {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ)
    {k : ℤ} {a : L} (ha : a ∈ lattice K S k) :
    ∃ b ∈ lattice K S k, σ • b - b =
      a - (∑ τ : G, (galoisNormalBasis K L G).repr a τ) • galoisNormalBasis K L G 1 := by
  haveI : SMulCommClass G K L := IsGaloisGroup.commutes
  set B := galoisNormalBasis K L G
  have hsm : ∀ ν τ : G, ν • B τ = B (ν * τ) := smul_galoisNormalBasis K L G
  have hy : ∀ τ : G, B.repr a τ • B 1 ∈ lattice K S k := fun τ =>
    smul_galoisNormalBasis_mem_lattice (ha τ) 1
  -- `a_τ τθ − a_τ θ = (τ − 1)(a_τ θ)` lies in `(σ − 1) Λ_k`
  choose c hc hce using fun τ : G =>
    exists_smul_sub_eq_smul_sub hσ (fun ν y hy => galois_smul_mem_lattice ν hy) τ (hy τ)
  refine ⟨∑ τ, c τ, sum_mem fun τ _ => hc τ, ?_⟩
  have e1 : σ • ∑ τ, c τ - ∑ τ, c τ = ∑ τ, (σ • c τ - c τ) := by
    rw [Finset.smul_sum, Finset.sum_sub_distrib]
  have e2 : ∀ τ : G, σ • c τ - c τ = B.repr a τ • B τ - B.repr a τ • B 1 := fun τ => by
    rw [hce τ, smul_comm, hsm, mul_one]
  rw [e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_sub_distrib, B.sum_repr a,
    Finset.sum_smul]

variable [Fintype S]

/-- A trace one element and its conjugates lie in a common lattice. -/
theorem exists_smul_traceOneElement_mem_lattice :
    ∃ c : ℕ, ∀ τ : G, τ • traceOneElement K L G ∈ lattice K S (-(c : ℤ)) := by
  obtain ⟨c, hc⟩ := exists_forall_mem_lattice (K := K) (S := S) fun _ : Unit => (1 : L)
  refine ⟨c, fun τ => ?_⟩
  rw [smul_traceOneElement]
  exact smul_galoisNormalBasis_mem_lattice (hc () τ) τ

/-- A product of elements `1 + a_i`, `a_i ∈ Λ_k`, is `1 + Σ_i a_i` up to `Λ_{2k−c}`. -/
theorem prod_sub_one_sub_sum_mem_lattice {k : ℤ} (hk : (latticeMulConst K S : ℤ) ≤ k)
    {ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, f i - 1 ∈ lattice K S k) :
    (∏ i ∈ s, f i) - 1 - ∑ i ∈ s, (f i - 1) ∈ lattice K S (k + k - latticeMulConst K S) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, sub_self, sub_zero]
    exact zero_mem _
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have e : f i * ∏ j ∈ s, f j - 1 - (f i - 1 + ∑ j ∈ s, (f j - 1)) =
        ((∏ j ∈ s, f j) - 1 - ∑ j ∈ s, (f j - 1)) + (f i - 1) * ((∏ j ∈ s, f j) - 1) := by
      ring
    rw [e]
    exact add_mem (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (mul_mem_lattice (hf i (Finset.mem_insert_self i s))
        (prod_sub_one_mem_lattice hk s f fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- If `x ∈ 1 + Λ_k` has norm one, the sum of the coordinates of `x − 1` has level `k + 1`:
the norm is `1 + Tr(x − 1)` up to `Λ_{2k−c}`, and the coordinates of a trace are equal. -/
theorem sum_repr_mem_level_of_prod_smul_eq_one {k : ℤ}
    (hk : (latticeMulConst K S : ℤ) + 1 ≤ k) {x : L} (hx : x - 1 ∈ lattice K S k)
    (hN : ∏ τ : G, τ • x = 1) :
    algebraMap K L (∑ τ : G, (galoisNormalBasis K L G).repr (x - 1) τ) ∈
      level L G S (k + 1) := by
  have h := prod_sub_one_sub_sum_mem_lattice (by linarith) Finset.univ (fun τ : G => τ • x)
    fun τ _ => galois_smul_sub_one_mem_lattice τ hx
  rw [hN, sub_self, zero_sub] at h
  have h' : ∑ τ : G, τ • (x - 1) ∈ lattice K S (k + 1) := by
    have e : ∑ τ : G, τ • (x - 1) = ∑ τ : G, (τ • x - 1) :=
      Finset.sum_congr rfl fun τ _ => by rw [smul_sub, smul_one]
    rw [e]
    exact lattice_anti (by linarith) (neg_mem_iff.mp h)
  have h1 := h' 1
  rwa [repr_sum_smul_galoisNormalBasis] at h1

/-- **One layer**: for `x ∈ 1 + Λ_k` of norm one there is `z ∈ 1 + Λ_k` with
`x z − σz ∈ Λ_{k+1}`. -/
theorem exists_mul_sub_smul_mem_lattice {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) {k : ℤ}
    (hk : (latticeMulConst K S : ℤ) + 1 ≤ k) {x : L} (hx : x - 1 ∈ lattice K S k)
    (hN : ∏ τ : G, τ • x = 1) :
    ∃ z : L, z - 1 ∈ lattice K S k ∧ x * z - σ • z ∈ lattice K S (k + 1) := by
  obtain ⟨b, hb, hbe⟩ := exists_smul_sub_eq_sub_sum_repr_smul hσ hx
  refine ⟨1 + b, by rwa [add_sub_cancel_left], ?_⟩
  have e : x * (1 + b) - σ • (1 + b) =
      (∑ τ : G, (galoisNormalBasis K L G).repr (x - 1) τ) • galoisNormalBasis K L G 1 +
        (x - 1) * b := by
    rw [smul_add, smul_one]
    linear_combination -hbe
  rw [e]
  exact add_mem
    (smul_galoisNormalBasis_mem_lattice (sum_repr_mem_level_of_prod_smul_eq_one hk hx hN) 1)
    (lattice_anti (by linarith) (mul_mem_lattice hx hb))

variable [Nonempty S]

/-- The elements of `1 + Λ_k` are nonzero. -/
theorem ne_zero_of_sub_one_mem_lattice {k : ℤ} (hk : (latticeLevelConst K S : ℤ) + 1 ≤ k)
    {x : L} (hx : x - 1 ∈ lattice K S k) : x ≠ 0 := by
  obtain ⟨⟨w, hw⟩⟩ := ‹Nonempty S›
  intro h
  have h1 := valuation_eq_one_of_sub_one_mem_lattice hk hx hw
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- **One layer**, as a quotient: `x / (σz / z) ∈ 1 + Λ_{k+1}` for some `z ∈ 1 + Λ_k`. -/
theorem exists_div_sub_one_mem_lattice {σ : G} (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) {k : ℤ}
    (hk1 : (latticeMulConst K S : ℤ) + 1 ≤ k) (hk2 : (latticeLevelConst K S : ℤ) + 1 ≤ k)
    {x : L} (hx : x - 1 ∈ lattice K S k) (hN : ∏ τ : G, τ • x = 1) :
    ∃ z : L, z ≠ 0 ∧ z - 1 ∈ lattice K S k ∧
      x / (σ • z / z) - 1 ∈ lattice K S (k + 1) := by
  obtain ⟨z, hz, hxz⟩ := exists_mul_sub_smul_mem_lattice hσ hk1 hx hN
  have hz0 : z ≠ 0 := ne_zero_of_sub_one_mem_lattice hk2 hz
  have hσz : σ • z ≠ 0 := (smul_ne_zero_iff_ne σ).mpr hz0
  refine ⟨z, hz0, hz, ?_⟩
  have e : x / (σ • z / z) - 1 = (x * z - σ • z) * (σ • z)⁻¹ := by
    rw [div_div_eq_mul_div, div_eq_mul_inv, sub_mul, mul_inv_cancel₀ hσz]
  rw [e]
  exact mul_mem_lattice_of_sub_one_mem (by linarith) hxz
    (inv_sub_one_mem_lattice (by linarith) hk2 hσz (galois_smul_sub_one_mem_lattice σ hz))

end Lattice

section Congruence

variable {K : Type*} {L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] {G : Type*}
  [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction

variable {S : SubMulAction G (HeightOneSpectrum (𝓞 L))} [Fintype S]

omit [NumberField L] [IsGaloisGroup G K L] in
/-- The norm of `x ∈ L^×` in the field. -/
theorem prod_smul_eq_one_of_actionNorm_eq_zero {x : Additive Lˣ}
    (hx : actionNorm (fieldUnitsRep L G) x = 0) :
    ∏ τ : G, τ • ((Additive.toMul x : Lˣ) : L) = 1 := by
  rw [actionNorm_apply] at hx
  have h := congrArg (fun z : Additive Lˣ => ((Additive.toMul z : Lˣ) : L)) hx
  simp only [toMul_sum, Units.coe_prod, toMul_zero, Units.val_one] at h
  exact h

/-- **One layer** in `L^×`: an element of `W_k` of norm one is congruent to an element of
`W_{k+1}` modulo `(σ − 1) W_k`. -/
theorem exists_sub_actionDiff_mem_congruenceSubgroup_succ [Nonempty S] {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (k : ℕ) {u : Additive Lˣ}
    (hu : u ∈ congruenceSubgroup K S k) (hN : actionNorm (fieldUnitsRep L G) u = 0) :
    ∃ z ∈ congruenceSubgroup K S k,
      u - actionDiff (fieldUnitsRep L G) σ z ∈ congruenceSubgroup K S (k + 1) := by
  have hM : ((congruenceBase K S + (k + 1) : ℕ) : ℤ) = ((congruenceBase K S + k : ℕ) : ℤ) + 1 := by
    push_cast
    ring
  have hk1 : (latticeMulConst K S : ℤ) + 1 ≤ ((congruenceBase K S + k : ℕ) : ℤ) := by
    have h : latticeMulConst K S + 1 ≤ congruenceBase K S + k := by
      unfold congruenceBase
      omega
    exact_mod_cast h
  obtain ⟨z, hz0, hz, hxz⟩ := exists_div_sub_one_mem_lattice hσ hk1
    (latticeLevelConst_add_one_le k) (mem_congruenceSubgroup.mp hu)
    (prod_smul_eq_one_of_actionNorm_eq_zero hN)
  refine ⟨Additive.ofMul (Units.mk0 z hz0), hz, ?_⟩
  show (((Additive.toMul u : Lˣ) /
    (fieldUnitsMap L G σ (Units.mk0 z hz0) / Units.mk0 z hz0) : Lˣ) : L) - 1 ∈
      lattice K S ((congruenceBase K S + (k + 1) : ℕ) : ℤ)
  rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val, hM]
  exact hxz

/-- An element of `W_k` of norm one is congruent to an element of `W_{k+m}` modulo
`(σ − 1) W_k`. -/
theorem exists_sub_actionDiff_mem_congruenceSubgroup_add [Nonempty S] {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (k m : ℕ) {u : Additive Lˣ}
    (hu : u ∈ congruenceSubgroup K S k) (hN : actionNorm (fieldUnitsRep L G) u = 0) :
    ∃ z ∈ congruenceSubgroup K S k,
      u - actionDiff (fieldUnitsRep L G) σ z ∈ congruenceSubgroup K S (k + m) := by
  induction m with
  | zero => exact ⟨0, zero_mem _, by rwa [map_zero, sub_zero]⟩
  | succ m ih =>
    obtain ⟨z, hz, hzu⟩ := ih
    have hN' : actionNorm (fieldUnitsRep L G) (u - actionDiff (fieldUnitsRep L G) σ z) = 0 := by
      rw [map_sub, hN, actionNorm_actionDiff, sub_zero]
    obtain ⟨z', hz', hzu'⟩ :=
      exists_sub_actionDiff_mem_congruenceSubgroup_succ hσ (k + m) hzu hN'
    refine ⟨z + z', add_mem hz (congruenceSubgroup_anti (Nat.le_add_right k m) hz'), ?_⟩
    have e : u - actionDiff (fieldUnitsRep L G) σ (z + z') =
        u - actionDiff (fieldUnitsRep L G) σ z - actionDiff (fieldUnitsRep L G) σ z' := by
      rw [map_add]
      abel
    rw [e]
    exact hzu'

/-- **Deep elements**: an element of `W_{k+c}` of norm one is `σz / z` with `z ∈ W_k`. If
`u = σy / y`, the average `z' = Σ_τ (τy / y) τc₀` over a trace one element lies in `W_k` and
`z' y` is fixed by `G`. -/
theorem exists_actionDiff_eq_of_mem_congruenceSubgroup_add [Nonempty S] {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    ∃ c : ℕ, ∀ (k : ℕ) (u : Additive Lˣ), u ∈ congruenceSubgroup K S (k + c) →
      actionNorm (fieldUnitsRep L G) u = 0 →
        ∃ z ∈ congruenceSubgroup K S k, actionDiff (fieldUnitsRep L G) σ z = u := by
  haveI : FaithfulSMul G L := IsGaloisGroup.faithful K
  obtain ⟨c, hc⟩ := exists_smul_traceOneElement_mem_lattice (K := K) (S := S)
  refine ⟨c + latticeMulConst K S, fun k u hu hN => ?_⟩
  obtain ⟨y, rfl⟩ := mem_range_actionDiff_of_actionNorm_eq_zero hσ hN
  -- `τy / y ∈ W` for all `τ`
  have hq : ∀ τ : G, fieldUnitsRep L G τ y - y ∈
      congruenceSubgroup K S (k + (c + latticeMulConst K S)) :=
    rep_sub_mem_of_actionDiff_mem hσ (fun τ a ha => fieldUnitsRep_mem_congruenceSubgroup τ ha) hu
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : L, y₀ = ((Additive.toMul y : Lˣ) : L) := ⟨_, rfl⟩
  have hy0 : y₀ ≠ 0 := hy₀ ▸ (Additive.toMul y).ne_zero
  have hq' : ∀ τ : G, τ • y₀ / y₀ - 1 ∈
      lattice K S ((congruenceBase K S + (k + (c + latticeMulConst K S)) : ℕ) : ℤ) := fun τ => by
    have h := mem_congruenceSubgroup.mp (hq τ)
    have e : ((Additive.toMul (fieldUnitsRep L G τ y - y) : Lˣ) : L) = τ • y₀ / y₀ := by
      show ((fieldUnitsMap L G τ (Additive.toMul y) / Additive.toMul y : Lˣ) : L) = _
      rw [Units.val_div_eq_div_val, hy₀]
      rfl
    rwa [e] at h
  -- the average
  obtain ⟨z', hz'⟩ : ∃ z' : L, z' = ∑ τ : G, τ • y₀ / y₀ * τ • traceOneElement K L G :=
    ⟨_, rfl⟩
  have hz1 : z' - 1 ∈ lattice K S ((congruenceBase K S + k : ℕ) : ℤ) := by
    have e : z' - 1 = ∑ τ : G, (τ • y₀ / y₀ - 1) * τ • traceOneElement K L G := by
      calc z' - 1 = z' - ∑ τ : G, τ • traceOneElement K L G := by
            rw [sum_smul_traceOneElement]
        _ = ∑ τ : G, (τ • y₀ / y₀ * τ • traceOneElement K L G - τ • traceOneElement K L G) := by
            rw [hz', Finset.sum_sub_distrib]
        _ = ∑ τ : G, (τ • y₀ / y₀ - 1) * τ • traceOneElement K L G :=
            Finset.sum_congr rfl fun τ _ => by rw [sub_mul, one_mul]
    have hMk : ((congruenceBase K S + (k + (c + latticeMulConst K S)) : ℕ) : ℤ) + -(c : ℤ) -
        latticeMulConst K S = ((congruenceBase K S + k : ℕ) : ℤ) := by
      push_cast
      ring
    rw [e, ← hMk]
    exact sum_mem fun τ _ => mul_mem_lattice (hq' τ) (hc τ)
  have hz0 : z' ≠ 0 := ne_zero_of_sub_one_mem_lattice (latticeLevelConst_add_one_le k) hz1
  -- `z' y = Tr(y c₀)` is fixed by `σ`
  have hT : z' * y₀ = ∑ τ : G, τ • (y₀ * traceOneElement K L G) := by
    rw [hz', Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [smul_mul', mul_right_comm, div_mul_cancel₀ _ hy0]
  have hσT : σ • (z' * y₀) = z' * y₀ := by
    rw [hT, Finset.smul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun τ => (mul_smul σ τ _).symm
  have h0 : actionDiff (fieldUnitsRep L G) σ (y + Additive.ofMul (Units.mk0 z' hz0)) = 0 := by
    rw [actionDiff_apply, sub_eq_zero]
    show (Additive.ofMul (fieldUnitsMap L G σ (Additive.toMul y * Units.mk0 z' hz0)) :
      Additive Lˣ) = Additive.ofMul (Additive.toMul y * Units.mk0 z' hz0)
    refine congrArg _ (Units.ext ?_)
    show σ • (((Additive.toMul y : Lˣ) : L) * z') = ((Additive.toMul y : Lˣ) : L) * z'
    rw [← hy₀, mul_comm]
    exact hσT
  refine ⟨-Additive.ofMul (Units.mk0 z' hz0), neg_mem hz1, ?_⟩
  rw [map_add] at h0
  rw [map_neg]
  exact (eq_neg_of_add_eq_zero_left h0).symm

/-- **`H¹(G, W_k) = 0`**: an element of a congruence subgroup of norm one is `σz / z` with `z`
in the same congruence subgroup. -/
theorem exists_mem_congruenceSubgroup_actionDiff_eq {σ : G}
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (k : ℕ) {u : Additive Lˣ}
    (hu : u ∈ congruenceSubgroup K S k) (hN : actionNorm (fieldUnitsRep L G) u = 0) :
    ∃ z ∈ congruenceSubgroup K S k, actionDiff (fieldUnitsRep L G) σ z = u := by
  haveI : FaithfulSMul G L := IsGaloisGroup.faithful K
  rcases isEmpty_or_nonempty S with hS | hS
  · -- without primes the congruence subgroup is `L^×`
    obtain ⟨z, hz⟩ := mem_range_actionDiff_of_actionNorm_eq_zero hσ hN
    exact ⟨z, mem_congruenceSubgroup.mpr fun τ w hw => (hS.false ⟨w, hw⟩).elim, hz⟩
  · obtain ⟨c, hc⟩ := exists_actionDiff_eq_of_mem_congruenceSubgroup_add (K := K) (S := S) hσ
    obtain ⟨z, hz, hzu⟩ := exists_sub_actionDiff_mem_congruenceSubgroup_add hσ k c hu hN
    obtain ⟨z', hz', e⟩ := hc k _ hzu (by rw [map_sub, hN, actionNorm_actionDiff, sub_zero])
    exact ⟨z + z', add_mem hz hz', by rw [map_add, e]; abel⟩

end Congruence

end GaloisForLFunctions
