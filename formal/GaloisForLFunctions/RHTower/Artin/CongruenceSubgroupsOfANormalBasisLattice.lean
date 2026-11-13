import GaloisForLFunctions.RHTower.Artin.TheHerbrandIndicesOfAPermutationModule
import Mathlib.FieldTheory.Galois.NormalBasis

/-!
# Congruence subgroups of a normal basis lattice

Let `L` be a number field, `G` a finite group acting on `L` with fixed field `K`, and `S` a
finite `G`-stable set of primes of `L`.

* `level S j`: the elements of `L` with exponent at least `j` at every prime of `S`; a
  decreasing, exhaustive, multiplicative filtration of `L` by `G`-stable subgroups.
* `lattice K S j`: the elements `Σ_τ a_τ τθ` with `a_τ ∈ K` of level `j`, for a normal basis
  `(τθ)_τ` of `L/K` (`galoisNormalBasis`). The lattices are `G`-stable, since `G` permutes the
  coordinates, and `Λ_i Λ_j ⊂ Λ_{i+j−c}` with `c` from the finitely many products `τθ · τ'θ`
  (`mul_mem_lattice`); `Λ_j` lies in the level `j − c'` (`lattice_le_level`).
* `congruenceSubgroup K S k = {x ∈ L^× : x − 1 ∈ Λ_{k₀+k}}`. It is a group: products by
  `Λ_k Λ_k ⊂ Λ_k`; for the inverse, `x⁻¹ = Π_{τ ≠ 1} τx / N(x)`, where the norm
  `N(x) ∈ K ∩ (1 + Λ_k)` has exponent zero on `S`, so that `N(x)⁻¹ − 1 = −N(x)⁻¹ (N(x) − 1)` is
  a multiple of `N(x) − 1` by a scalar of level zero. It is `G`-stable, its elements have
  exponent zero on `S`, and it contains the elements of `K^×` congruent to `1` to a high order
  at `S` (`exists_level_le_congruenceSubgroup`).
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain HeightOneSpectrum

noncomputable section

namespace GaloisForLFunctions

section Levels

variable (L : Type*) [Field L] [NumberField L] (G : Type*) [Group G] [MulSemiringAction G L]

attribute [local instance] primeMulAction

variable (S : SubMulAction G (HeightOneSpectrum (𝓞 L)))

/-- The elements of `L` with exponent at least `j` at every prime of `S`. -/
def level (j : ℤ) : AddSubgroup L where
  carrier := {y | ∀ w, w ∈ S → w.valuation L y ≤ WithZero.exp (-j)}
  zero_mem' := fun w _ => by
    rw [map_zero]
    exact zero_le
  add_mem' := fun hx hy w hw => Valuation.map_add_le _ (hx w hw) (hy w hw)
  neg_mem' := fun hx w hw => by
    rw [Valuation.map_neg]
    exact hx w hw

variable {L G S}

theorem level_anti {i j : ℤ} (h : i ≤ j) : level L G S j ≤ level L G S i := fun _ hy w hw =>
  (hy w hw).trans (WithZero.exp_le_exp.mpr (neg_le_neg h))

theorem mul_mem_level {i j : ℤ} {y y' : L} (hy : y ∈ level L G S i) (hy' : y' ∈ level L G S j) :
    y * y' ∈ level L G S (i + j) := fun w hw => by
  rw [map_mul, neg_add, WithZero.exp_add]
  exact mul_le_mul' (hy w hw) (hy' w hw)

theorem one_mem_level : (1 : L) ∈ level L G S 0 := fun w _ => by
  rw [map_one, neg_zero, WithZero.exp_zero]

/-- The levels are stable under `G`. -/
theorem smul_mem_level (τ : G) {j : ℤ} {y : L} (hy : y ∈ level L G S j) :
    τ • y ∈ level L G S j := fun w hw => by
  have h := prime_smul_valuation L G τ⁻¹ w y
  rw [inv_inv] at h
  rw [← h]
  exact hy _ (S.smul_mem τ⁻¹ hw)

/-- An element congruent to `1` modulo the level `1` has exponent zero on `S`. -/
theorem valuation_eq_one_of_sub_one_mem_level {x : L} (hx : x - 1 ∈ level L G S 1)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ S) : w.valuation L x = 1 := by
  have h : w.valuation L (x - 1) < 1 :=
    lt_of_le_of_lt (hx w hw)
      (show WithZero.exp (-(1 : ℤ)) < WithZero.exp (0 : ℤ) from
        WithZero.exp_lt_exp.mpr (by norm_num))
  have h1 := (w.valuation L).map_one_add_of_lt h
  rwa [add_sub_cancel] at h1

variable [Fintype S]

/-- Every element of `L` lies in some level. -/
theorem exists_mem_level (y : L) : ∃ c : ℕ, y ∈ level L G S (-(c : ℤ)) := by
  by_cases hy : y = 0
  · exact ⟨0, by rw [hy]; exact zero_mem _⟩
  · obtain ⟨u, rfl⟩ : ∃ u : Lˣ, (u : L) = y := ⟨Units.mk0 y hy, rfl⟩
    have hsum : ∀ w : S, (ordAt L w.1 (Additive.ofMul u)).natAbs ≤
        ∑ v : S, (ordAt L v.1 (Additive.ofMul u)).natAbs := fun w =>
      Finset.single_le_sum (f := fun v : S => (ordAt L v.1 (Additive.ofMul u)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
    refine ⟨∑ v : S, (ordAt L v.1 (Additive.ofMul u)).natAbs, fun w hw => ?_⟩
    rw [valuation_eq_exp_neg_ordAt, WithZero.exp_le_exp, neg_neg]
    have h1 : (ordAt L w (Additive.ofMul u)).natAbs ≤
        ∑ v : S, (ordAt L v.1 (Additive.ofMul u)).natAbs := hsum ⟨w, hw⟩
    have h2 : ∀ z : ℤ, -z ≤ (z.natAbs : ℤ) := fun z => by omega
    exact (h2 _).trans (by exact_mod_cast h1)

/-- A finite family lies in a common level. -/
theorem exists_forall_mem_level {ι : Type*} [Finite ι] (f : ι → L) :
    ∃ c : ℕ, ∀ i, f i ∈ level L G S (-(c : ℤ)) := by
  haveI := Fintype.ofFinite ι
  choose c hc using fun i => exists_mem_level (S := S) (f i)
  refine ⟨∑ i, c i, fun i => level_anti ?_ (hc i)⟩
  rw [neg_le_neg_iff]
  exact_mod_cast Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

end Levels

section NormalBasis

variable (K L : Type*) [Field K] [Field L] [Algebra K L] (G : Type*) [Group G] [Fintype G]
  [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- A basis of `L/K` permuted simply transitively by `G`. -/
def galoisNormalBasis : Module.Basis G K L :=
  haveI := IsGaloisGroup.isGalois G K L
  haveI := IsGaloisGroup.finiteDimensional G K L
  (IsGalois.normalBasis K L).reindex (IsGaloisGroup.mulEquivAlgEquiv G K L).symm.toEquiv

/-- `ν (τ θ) = (ν τ) θ`. -/
theorem smul_galoisNormalBasis (ν τ : G) :
    ν • galoisNormalBasis K L G τ = galoisNormalBasis K L G (ν * τ) := by
  haveI := IsGaloisGroup.isGalois G K L
  haveI := IsGaloisGroup.finiteDimensional G K L
  have key : ∀ μ : G, galoisNormalBasis K L G μ = μ • IsGalois.normalBasis K L 1 := fun μ => by
    show (IsGalois.normalBasis K L).reindex _ μ = _
    rw [Module.Basis.reindex_apply, IsGalois.normalBasis_apply]
    rfl
  rw [key, key, mul_smul]

/-- `G` permutes the coordinates in the normal basis. -/
theorem repr_smul_galoisNormalBasis (ν : G) (a : L) (μ : G) :
    (galoisNormalBasis K L G).repr (ν • a) μ = (galoisNormalBasis K L G).repr a (ν⁻¹ * μ) := by
  haveI : SMulCommClass G K L := IsGaloisGroup.commutes
  set b := galoisNormalBasis K L G
  have h : ν • a = ∑ μ, b.repr a (ν⁻¹ * μ) • b μ := by
    conv_lhs => rw [← b.sum_repr a]
    rw [Finset.smul_sum]
    have e : ∀ τ : G, ν • (b.repr a τ • b τ) = b.repr a τ • b (ν * τ) := fun τ => by
      rw [smul_comm, smul_galoisNormalBasis]
    rw [Finset.sum_congr rfl fun τ _ => e τ]
    exact Fintype.sum_equiv (Equiv.mulLeft ν) _ _ fun τ => by
      rw [Equiv.coe_mulLeft, inv_mul_cancel_left]
  rw [h, b.repr_sum_self]

end NormalBasis

section Lattice

variable (K : Type*) {L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] {G : Type*}
  [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] primeMulAction

variable (S : SubMulAction G (HeightOneSpectrum (𝓞 L)))

/-- The normal basis lattice of level `j`: the elements whose coordinates in the normal basis
have exponent at least `j` at every prime of `S`. -/
def lattice (j : ℤ) : AddSubgroup L where
  carrier := {a | ∀ τ, algebraMap K L ((galoisNormalBasis K L G).repr a τ) ∈ level L G S j}
  zero_mem' := fun τ => by
    rw [map_zero, Finsupp.zero_apply, map_zero]
    exact zero_mem _
  add_mem' := fun ha ha' τ => by
    rw [map_add, Finsupp.add_apply, map_add]
    exact add_mem (ha τ) (ha' τ)
  neg_mem' := fun ha τ => by
    rw [map_neg, Finsupp.neg_apply, map_neg]
    exact neg_mem (ha τ)

variable {K S}

theorem lattice_anti {i j : ℤ} (h : i ≤ j) : lattice K S j ≤ lattice K S i := fun _ ha τ =>
  level_anti h (ha τ)

/-- Scalars of level `i` map the lattice of level `j` into the lattice of level `i + j`. -/
theorem smul_mem_lattice {i j : ℤ} {β : K} (hβ : algebraMap K L β ∈ level L G S i) {a : L}
    (ha : a ∈ lattice K S j) : β • a ∈ lattice K S (i + j) := fun τ => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_mem_level hβ (ha τ)

/-- The lattices are stable under `G`. -/
theorem galois_smul_mem_lattice (ν : G) {j : ℤ} {a : L} (ha : a ∈ lattice K S j) :
    ν • a ∈ lattice K S j := fun τ => by
  rw [repr_smul_galoisNormalBasis]
  exact ha _

/-- The elements of the normal basis lie in the lattice of level zero. -/
theorem galoisNormalBasis_mem_lattice (τ : G) : galoisNormalBasis K L G τ ∈ lattice K S 0 :=
  fun μ => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · rw [map_one]
      exact one_mem_level
    · rw [map_zero]
      exact zero_mem _

variable [Fintype S]

/-- A finite family lies in a common lattice. -/
theorem exists_forall_mem_lattice {ι : Type*} [Finite ι] (f : ι → L) :
    ∃ c : ℕ, ∀ i, f i ∈ lattice K S (-(c : ℤ)) := by
  obtain ⟨c, hc⟩ := exists_forall_mem_level (S := S)
    fun p : ι × G => algebraMap K L ((galoisNormalBasis K L G).repr (f p.1) p.2)
  exact ⟨c, fun i τ => hc (i, τ)⟩

/-- The lattice of level `j` lies in the level `j − c`. -/
theorem exists_lattice_le_level :
    ∃ c : ℕ, ∀ j : ℤ, lattice K S j ≤ level L G S (j - c) := by
  obtain ⟨c, hc⟩ := exists_forall_mem_level (S := S) fun τ : G => galoisNormalBasis K L G τ
  refine ⟨c, fun j a ha => ?_⟩
  have h : ∑ τ, (galoisNormalBasis K L G).repr a τ • galoisNormalBasis K L G τ ∈
      level L G S (j - c) := by
    rw [sub_eq_add_neg]
    refine sum_mem fun τ _ => ?_
    rw [Algebra.smul_def]
    exact mul_mem_level (ha τ) (hc τ)
  rwa [(galoisNormalBasis K L G).sum_repr a] at h

/-- Products: `Λ_i Λ_j ⊂ Λ_{i+j−c}`. -/
theorem exists_mul_mem_lattice : ∃ c : ℕ, ∀ (i j : ℤ) (a a' : L), a ∈ lattice K S i →
    a' ∈ lattice K S j → a * a' ∈ lattice K S (i + j - c) := by
  obtain ⟨c, hc⟩ := exists_forall_mem_lattice (K := K) (S := S)
    fun p : G × G => galoisNormalBasis K L G p.1 * galoisNormalBasis K L G p.2
  refine ⟨c, fun i j a a' ha ha' => ?_⟩
  set b := galoisNormalBasis K L G
  have h : (∑ τ, b.repr a τ • b τ) * ∑ τ', b.repr a' τ' • b τ' ∈ lattice K S (i + j - c) := by
    rw [Finset.sum_mul_sum, sub_eq_add_neg]
    refine sum_mem fun τ _ => sum_mem fun τ' _ => ?_
    rw [smul_mul_smul_comm]
    refine smul_mem_lattice ?_ (hc (τ, τ'))
    rw [map_mul]
    exact mul_mem_level (ha τ) (ha' τ')
  rwa [b.sum_repr a, b.sum_repr a'] at h

/-- The elements of `K` of level `j + c` lie in the lattice of level `j`. -/
theorem exists_algebraMap_mem_lattice : ∃ c : ℕ, ∀ (j : ℤ) (β : K),
    algebraMap K L β ∈ level L G S (j + c) → algebraMap K L β ∈ lattice K S j := by
  obtain ⟨c, hc⟩ := exists_forall_mem_lattice (K := K) (S := S) fun _ : Unit => (1 : L)
  refine ⟨c, fun j β hβ => ?_⟩
  have h := smul_mem_lattice hβ (hc ())
  rwa [Algebra.smul_def, mul_one, add_neg_cancel_right] at h

variable (K S)

/-- A constant `c` with `Λ_i Λ_j ⊂ Λ_{i+j−c}`. -/
def latticeMulConst : ℕ := (exists_mul_mem_lattice (K := K) (S := S)).choose

/-- A constant `c` with `Λ_j` contained in the level `j − c`. -/
def latticeLevelConst : ℕ := (exists_lattice_le_level (K := K) (S := S)).choose

/-- A level from which on `1 + Λ_k` is a group of elements with exponent zero on `S`. -/
def congruenceBase : ℕ := latticeMulConst K S + latticeLevelConst K S + 1

variable {K S}

theorem mul_mem_lattice {i j : ℤ} {a a' : L} (ha : a ∈ lattice K S i)
    (ha' : a' ∈ lattice K S j) : a * a' ∈ lattice K S (i + j - latticeMulConst K S) :=
  (exists_mul_mem_lattice (K := K) (S := S)).choose_spec i j a a' ha ha'

theorem lattice_le_level (j : ℤ) : lattice K S j ≤ level L G S (j - latticeLevelConst K S) :=
  (exists_lattice_le_level (K := K) (S := S)).choose_spec j

theorem latticeMulConst_le (k : ℕ) :
    (latticeMulConst K S : ℤ) ≤ ((congruenceBase K S + k : ℕ) : ℤ) := by
  have h : latticeMulConst K S ≤ congruenceBase K S + k := by
    unfold congruenceBase
    omega
  exact_mod_cast h

theorem latticeLevelConst_add_one_le (k : ℕ) :
    (latticeLevelConst K S : ℤ) + 1 ≤ ((congruenceBase K S + k : ℕ) : ℤ) := by
  have h : latticeLevelConst K S + 1 ≤ congruenceBase K S + k := by
    unfold congruenceBase
    omega
  exact_mod_cast h

/-- An element of the lattice of level `j ≥ k` times an element of `1 + Λ_k` stays in the
lattice of level `j`. -/
theorem mul_mem_lattice_of_sub_one_mem {j k : ℤ} (hk : (latticeMulConst K S : ℤ) ≤ k) {e y : L}
    (he : e ∈ lattice K S j) (hy : y - 1 ∈ lattice K S k) : e * y ∈ lattice K S j := by
  have h : e * y = e + e * (y - 1) := by ring
  rw [h]
  exact add_mem he (lattice_anti (by linarith) (mul_mem_lattice he hy))

/-- `(1 + Λ_k)(1 + Λ_k) ⊂ 1 + Λ_k` for `k ≥ c`. -/
theorem mul_sub_one_mem_lattice {k : ℤ} (hk : (latticeMulConst K S : ℤ) ≤ k) {x x' : L}
    (hx : x - 1 ∈ lattice K S k) (hx' : x' - 1 ∈ lattice K S k) :
    x * x' - 1 ∈ lattice K S k := by
  have h : x * x' - 1 = (x - 1) + (x' - 1) + (x - 1) * (x' - 1) := by ring
  rw [h]
  exact add_mem (add_mem hx hx') (lattice_anti (by linarith) (mul_mem_lattice hx hx'))

/-- Finite products of elements of `1 + Λ_k`. -/
theorem prod_sub_one_mem_lattice {k : ℤ} (hk : (latticeMulConst K S : ℤ) ≤ k) {ι : Type*}
    (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, f i - 1 ∈ lattice K S k) :
    (∏ i ∈ s, f i) - 1 ∈ lattice K S k := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, sub_self]
    exact zero_mem _
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact mul_sub_one_mem_lattice hk (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The elements of `1 + Λ_k` have exponent zero on `S` for `k ≥ c' + 1`. -/
theorem valuation_eq_one_of_sub_one_mem_lattice {k : ℤ}
    (hk : (latticeLevelConst K S : ℤ) + 1 ≤ k) {x : L} (hx : x - 1 ∈ lattice K S k)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ S) : w.valuation L x = 1 :=
  valuation_eq_one_of_sub_one_mem_level (level_anti (by linarith) (lattice_le_level k hx)) hw

omit [Fintype S] in
/-- The conjugates of an element of `1 + Λ_k` lie in `1 + Λ_k`. -/
theorem galois_smul_sub_one_mem_lattice (τ : G) {k : ℤ} {x : L} (hx : x - 1 ∈ lattice K S k) :
    τ • x - 1 ∈ lattice K S k := by
  have h := galois_smul_mem_lattice τ hx
  rwa [smul_sub, smul_one] at h

/-- **Inverses**: `1 + Λ_k` is stable under inversion for `k ≥ k₀`, because
`x⁻¹ = Π_{τ ≠ 1} τx / N(x)` and the norm is inverted in `K`. -/
theorem inv_sub_one_mem_lattice {k : ℤ} (hk1 : (latticeMulConst K S : ℤ) ≤ k)
    (hk2 : (latticeLevelConst K S : ℤ) + 1 ≤ k) {x : L} (hx0 : x ≠ 0)
    (hx : x - 1 ∈ lattice K S k) : x⁻¹ - 1 ∈ lattice K S k := by
  set P : L := ∏ τ ∈ (Finset.univ : Finset G).erase 1, τ • x with hP
  set N : L := ∏ τ : G, τ • x with hN
  have hPN : x * P = N := by
    have h := Finset.mul_prod_erase Finset.univ (fun τ : G => τ • x) (Finset.mem_univ 1)
    rwa [one_smul] at h
  have hP1 : P - 1 ∈ lattice K S k :=
    prod_sub_one_mem_lattice hk1 _ _ fun τ _ => galois_smul_sub_one_mem_lattice τ hx
  have hN1 : N - 1 ∈ lattice K S k :=
    prod_sub_one_mem_lattice hk1 _ _ fun τ _ => galois_smul_sub_one_mem_lattice τ hx
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun τ _ => (smul_ne_zero_iff_ne τ).mpr hx0
  have hP0 : P ≠ 0 := fun h => hN0 (by rw [← hPN, h, mul_zero])
  -- the norm lies in `K`
  have hinv : ∀ ν : G, ν • N = N := fun ν => by
    show MulSemiringAction.toRingHom G L ν (∏ τ : G, τ • x) = ∏ τ : G, τ • x
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft ν) _ _ fun τ => (mul_smul ν τ x).symm
  obtain ⟨n₀, hn₀⟩ := Algebra.IsInvariant.isInvariant (A := K) (G := G) N hinv
  -- `N⁻¹ − 1 = −N⁻¹ (N − 1)`, and `N⁻¹` has exponent zero on `S`
  have hNinv : N⁻¹ - 1 ∈ lattice K S k := by
    have hlev : algebraMap K L (-n₀⁻¹) ∈ level L G S 0 := fun w hw => by
      rw [map_neg, map_inv₀, hn₀, Valuation.map_neg, map_inv₀,
        valuation_eq_one_of_sub_one_mem_lattice hk2 hN1 hw, inv_one, neg_zero,
        WithZero.exp_zero]
    have h := smul_mem_lattice hlev hN1
    rw [zero_add, Algebra.smul_def, map_neg, map_inv₀, hn₀] at h
    have e : -N⁻¹ * (N - 1) = N⁻¹ - 1 := by
      field_simp
      ring
    rwa [e] at h
  have hx' : x⁻¹ = P * N⁻¹ := by
    rw [← hPN, mul_inv, mul_comm P, mul_assoc, inv_mul_cancel₀ hP0, mul_one]
  rw [hx']
  exact mul_sub_one_mem_lattice hk1 hP1 hNinv

variable (K S)

/-- The congruence subgroup `W_k = {x ∈ L^× : x − 1 ∈ Λ_{k₀+k}}`. -/
def congruenceSubgroup (k : ℕ) : AddSubgroup (Additive Lˣ) where
  carrier := {x | ((Additive.toMul x : Lˣ) : L) - 1 ∈
    lattice K S ((congruenceBase K S + k : ℕ) : ℤ)}
  zero_mem' := by
    show ((1 : Lˣ) : L) - 1 ∈ lattice K S ((congruenceBase K S + k : ℕ) : ℤ)
    rw [Units.val_one, sub_self]
    exact zero_mem _
  add_mem' := fun {x y} hx hy => by
    show ((Additive.toMul x * Additive.toMul y : Lˣ) : L) - 1 ∈
      lattice K S ((congruenceBase K S + k : ℕ) : ℤ)
    rw [Units.val_mul]
    exact mul_sub_one_mem_lattice (latticeMulConst_le k) hx hy
  neg_mem' := fun {x} hx => by
    show (((Additive.toMul x)⁻¹ : Lˣ) : L) - 1 ∈ lattice K S ((congruenceBase K S + k : ℕ) : ℤ)
    rw [Units.val_inv_eq_inv_val]
    exact inv_sub_one_mem_lattice (latticeMulConst_le k) (latticeLevelConst_add_one_le k)
      (Additive.toMul x).ne_zero hx

variable {K S}

theorem mem_congruenceSubgroup {k : ℕ} {x : Additive Lˣ} :
    x ∈ congruenceSubgroup K S k ↔
      ((Additive.toMul x : Lˣ) : L) - 1 ∈ lattice K S ((congruenceBase K S + k : ℕ) : ℤ) :=
  Iff.rfl

theorem congruenceSubgroup_anti {k k' : ℕ} (h : k ≤ k') :
    congruenceSubgroup K S k' ≤ congruenceSubgroup K S k := fun _ hx =>
  lattice_anti (by exact_mod_cast Nat.add_le_add_left h _) (mem_congruenceSubgroup.mp hx)

/-- The congruence subgroups are stable under `G`. -/
theorem fieldUnitsRep_mem_congruenceSubgroup (τ : G) {k : ℕ} {x : Additive Lˣ}
    (hx : x ∈ congruenceSubgroup K S k) :
    fieldUnitsRep L G τ x ∈ congruenceSubgroup K S k := by
  show τ • ((Additive.toMul x : Lˣ) : L) - 1 ∈ lattice K S ((congruenceBase K S + k : ℕ) : ℤ)
  exact galois_smul_sub_one_mem_lattice τ (mem_congruenceSubgroup.mp hx)

/-- The elements of a congruence subgroup have exponent zero on `S`. -/
theorem ordAt_eq_zero_of_mem_congruenceSubgroup {k : ℕ} {x : Additive Lˣ}
    (hx : x ∈ congruenceSubgroup K S k) {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ S) :
    ordAt L w x = 0 :=
  (ordAt_eq_zero_iff L w (Additive.toMul x)).mpr
    (valuation_eq_one_of_sub_one_mem_lattice (latticeLevelConst_add_one_le k)
      (mem_congruenceSubgroup.mp hx) hw)

/-- The congruence subgroups lie in the kernel of the divisor map at `S`. -/
theorem congruenceSubgroup_le_ker_divMap (k : ℕ) :
    congruenceSubgroup K S k ≤ (divMap L G S).ker := fun _ hx =>
  AddMonoidHom.mem_ker.mpr (funext fun w => ordAt_eq_zero_of_mem_congruenceSubgroup hx w.2)

/-- The elements of `K^×` congruent to `1` to a high order at `S` lie in `W_k`. -/
theorem exists_level_le_congruenceSubgroup (k : ℕ) : ∃ J : ℕ, ∀ α : Kˣ,
    algebraMap K L ((α : K) - 1) ∈ level L G S (J : ℤ) →
      Additive.ofMul (Units.map (algebraMap K L : K →* L) α) ∈ congruenceSubgroup K S k := by
  obtain ⟨c, hc⟩ := exists_algebraMap_mem_lattice (K := K) (S := S)
  refine ⟨congruenceBase K S + k + c, fun α hα => ?_⟩
  have h := hc ((congruenceBase K S + k : ℕ) : ℤ) ((α : K) - 1) (by
    rw [← Nat.cast_add]
    exact hα)
  rw [map_sub, map_one] at h
  exact h

end Lattice

end GaloisForLFunctions
