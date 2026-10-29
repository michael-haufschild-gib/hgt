import GaloisForLFunctions.HeckeKreinToeplitz.LocalityFailsButAlmostEveryPrimeDecides
import GaloisForLFunctions.HeckeKreinToeplitz.StepanovCompressionsAndTheAnnihilationLaw
import Mathlib.GroupTheory.CosetCover

/-!
# Cyclic subgroups decide the Krein–Langer class

A Hermitian kernel on a group restricts to every cyclic subgroup `⟨u⟩`. When do these restrictions
decide positivity? The answer depends on the class of the kernel.

**Cyclic Hasse principle** (`exists_one_le_negIndex_zpowers`, `negIndex_eq_zero_of_forall_zpowers`).
On *every* group, a positive-definite kernel plus finitely many hyperbolic pairs `h_{χ_j,ω_j}`
(non-unitary characters, the `2|J|` nodes `χ_j, χ_j†` distinct, weights nonzero) has a negative square
on some cyclic subgroup as soon as it has one pair. So a Krein–Langer kernel positive on every cyclic
subgroup is positive definite.

*Proof.* The elements at which two nodes coincide form the subgroups `ker(ν/ν')`; the nodes `ν, ν'`
are *torsion-aliased* when this subgroup has finite index. Fix the aliasing class `T` of one node and
the finite-index subgroup `H` on which all quotients `η_ν = ν/ν₀`, `ν ∈ T`, are trivial. Dedekind's
independence of the distinct characters `η_ν` gives `g` with `F(g) = Σ_{ν∈T} c_ν η_ν(g) ≠ 0`.
Neumann's lemma gives `u ∈ gH` outside every subgroup `ker(ν/ν')` of infinite index
(`exists_mul_not_mem`). At `u` every node is off the unit circle, nodes coincide only within aliasing
classes, and `F(u) = F(g)`. Orient every pair outward at `u`; the class `T` (or its reflection) is
outer and closed, so if all class weights on `⟨u⟩` vanished then `F(u) = 0`. The aliasing law
(`negIndex_zpowers_eq_card_classes`) turns a nonzero class weight into a negative square.

**Separation** (`exists_separating_of_not_aliased`, `negIndex_zpowers_eq_of_not_aliased`). Without
torsion aliasing a single element separates all nodes, and its cyclic subgroup carries the whole
index `κ`.

**Coordinate towers do not decide** (`coordinateKernel`, `coordinate_locality_fails`). On `ℤ²` the
Krein–Langer kernel `2i·sinh(a log 2)·(1 − (−1)^b) = h_{(2,1),i} + h_{(2,−1),−i}` has index `2` and
vanishes on both coordinate axes and on the index-two subgroup `b ∈ 2ℤ`: the two pairs are
torsion-aliased, with cancelling weights, along the first axis and unitary along the second.

**Outside the class even cyclic subgroups fail** (`starKernel`, `cyclic_locality_fails_off_class`).
The kernel `δ₀ − ½ Σ_{w ∈ {e₁, e₂, e₁+e₂}} (δ_w + δ_{−w})` is positive definite on every cyclic
subgroup of `ℤ²` and not on `ℤ²`: its defect is a signed spectral measure, not a hyperbolic pair.
-/

open Complex Finset
open scoped ComplexConjugate Pointwise
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

variable {G : Type*} [Group G]

/-! ### Neumann avoidance -/

/-- **Neumann avoidance.** Every coset of a finite-index subgroup contains an element outside any
finitely many subgroups of infinite index. -/
theorem exists_mul_not_mem (H : Subgroup G) [H.FiniteIndex] {ι : Type*} (s : Finset ι)
    (K : ι → Subgroup G) (hK : ∀ i ∈ s, ¬ (K i).FiniteIndex) (g : G) :
    ∃ h ∈ H, ∀ i ∈ s, g * h ∉ K i := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcov : ⋃ i ∈ (univ : Finset (G ⧸ H)) ×ˢ s,
      (fun c : (G ⧸ H) × ι => (Quotient.out c.1 : G) * g⁻¹) i •
        ((fun c : (G ⧸ H) × ι => K c.2) i : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : (Quotient.out (x : G ⧸ H) : G)⁻¹ * x ∈ H :=
      QuotientGroup.eq.mp (Quotient.out_eq _)
    obtain ⟨i, hi, hmem⟩ := hcon _ hx
    simp only [Set.mem_iUnion]
    refine ⟨((x : G ⧸ H), i), mem_product.mpr ⟨mem_univ _, hi⟩, ?_⟩
    rw [mem_leftCoset_iff, SetLike.mem_coe, show ((Quotient.out (x : G ⧸ H) : G) * g⁻¹)⁻¹ * x =
      g * ((Quotient.out (x : G ⧸ H) : G)⁻¹ * x) by group]
    exact hmem
  obtain ⟨k, hk, hfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcov
  exact hK k.2 (mem_product.mp hk).2 hfi

/-! ### Quotient characters and torsion aliasing -/

/-- The quotient character `χ/ψ`. -/
def quotChar (χ ψ : G →* ℂ) : G →* ℂ where
  toFun g := χ g * (ψ g)⁻¹
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, mul_inv]; ring

theorem quotChar_apply (χ ψ : G →* ℂ) (g : G) : quotChar χ ψ g = χ g * (ψ g)⁻¹ := rfl

theorem mem_ker_quotChar {χ ψ : G →* ℂ} {g : G} : g ∈ (quotChar χ ψ).ker ↔ χ g = ψ g := by
  rw [MonoidHom.mem_ker, quotChar_apply, mul_inv_eq_one₀ (map_ne_zero ψ g)]

/-- Two characters are **torsion-aliased** when they agree on a subgroup of finite index. -/
def IsTorsionAliased (χ ψ : G →* ℂ) : Prop := (quotChar χ ψ).ker.FiniteIndex

theorem isTorsionAliased_refl (χ : G →* ℂ) : IsTorsionAliased χ χ := by
  have : (quotChar χ χ).ker = ⊤ := by
    ext g; simp only [Subgroup.mem_top, iff_true]; exact mem_ker_quotChar.mpr rfl
  rw [IsTorsionAliased, this]; infer_instance

theorem IsTorsionAliased.symm {χ ψ : G →* ℂ} (h : IsTorsionAliased χ ψ) : IsTorsionAliased ψ χ := by
  have : (quotChar ψ χ).ker = (quotChar χ ψ).ker := by
    ext g; rw [mem_ker_quotChar, mem_ker_quotChar, eq_comm]
  rw [IsTorsionAliased, this]; exact h

theorem IsTorsionAliased.trans {χ ψ φ : G →* ℂ} (h₁ : IsTorsionAliased χ ψ)
    (h₂ : IsTorsionAliased ψ φ) : IsTorsionAliased χ φ := by
  haveI : (quotChar χ ψ).ker.FiniteIndex := h₁
  haveI : (quotChar ψ φ).ker.FiniteIndex := h₂
  have hle : (quotChar χ ψ).ker ⊓ (quotChar ψ φ).ker ≤ (quotChar χ φ).ker := fun g hg => by
    rw [Subgroup.mem_inf, mem_ker_quotChar, mem_ker_quotChar] at hg
    rw [mem_ker_quotChar, hg.1, hg.2]
  exact Subgroup.finiteIndex_of_le hle

/-- Reflection preserves torsion aliasing: both pairs agree on the same subgroup. -/
theorem isTorsionAliased_reflectChar_iff {χ ψ : G →* ℂ} :
    IsTorsionAliased (reflectChar χ) (reflectChar ψ) ↔ IsTorsionAliased χ ψ := by
  have : (quotChar (reflectChar χ) (reflectChar ψ)).ker = (quotChar χ ψ).ker := by
    ext g
    rw [mem_ker_quotChar, mem_ker_quotChar, reflectChar_apply, reflectChar_apply,
      (RingHom.injective _).eq_iff, map_inv_eq_inv, map_inv_eq_inv, inv_inj]
  rw [IsTorsionAliased, IsTorsionAliased, this]

/-- A torsion-aliased quotient is unimodular: `η(g)^{[G:K]} = 1`. -/
theorem norm_quotChar_eq_one {χ ψ : G →* ℂ} (h : IsTorsionAliased χ ψ) (g : G) :
    ‖quotChar χ ψ g‖ = 1 := by
  haveI : (quotChar χ ψ).ker.FiniteIndex := h
  have hmem := Subgroup.pow_index_mem (quotChar χ ψ).ker g
  rw [MonoidHom.mem_ker, map_pow] at hmem
  have hn := (Subgroup.FiniteIndex.index_ne_zero (H := (quotChar χ ψ).ker))
  have := congrArg norm hmem
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp this

theorem norm_eq_of_isTorsionAliased {χ ψ : G →* ℂ} (h : IsTorsionAliased χ ψ) (g : G) :
    ‖χ g‖ = ‖ψ g‖ := by
  have h1 := norm_quotChar_eq_one h g
  rw [quotChar_apply, norm_mul, norm_inv] at h1
  have hψ : ‖ψ g‖ ≠ 0 := norm_ne_zero_iff.mpr (map_ne_zero ψ g)
  field_simp at h1
  exact h1

/-- On the unit circle `1/z̄ = z`. -/
theorem inv_conj_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : (conj z)⁻¹ = z := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  simp

/-- A character agreeing with its reflection on a finite-index subgroup is unitary. -/
theorem isUnitaryChar_of_isTorsionAliased_reflectChar {χ : G →* ℂ}
    (h : IsTorsionAliased χ (reflectChar χ)) : IsUnitaryChar χ := fun g => by
  have h1 := norm_eq_of_isTorsionAliased h g
  rw [norm_reflectChar] at h1
  have hpos : 0 < ‖χ g‖ := norm_pos_iff.mpr (map_ne_zero χ g)
  have : ‖χ g‖ * ‖χ g‖ = 1 := by rw [congrArg (‖χ g‖ * ·) h1, mul_inv_cancel₀ hpos.ne']
  nlinarith

/-- On the unit circle a character agrees with its reflection. -/
theorem eq_reflectChar_of_norm_eq_one {χ : G →* ℂ} {u : G} (h : ‖χ u‖ = 1) :
    χ u = reflectChar χ u := by
  rw [reflectChar_apply, map_inv_eq_inv, map_inv₀, inv_conj_of_norm_eq_one h]

/-! ### Nodes, weights and orientation -/

variable {J : Type*}

/-- The `2|J|` nodes of a family of pairs: the characters and their reflections. -/
def node (χ : J → G →* ℂ) : J ⊕ J → G →* ℂ := Sum.elim χ fun j => reflectChar (χ j)

/-- The weight at a node: `ω_j` at `χ_j` and `ω̄_j` at `χ_j†`. -/
def nodeWeight (ω : J → ℂ) : J ⊕ J → ℂ := Sum.elim ω fun j => conj (ω j)

/-- The pair a node belongs to. -/
def pairIdx : J ⊕ J → J := Sum.elim id id

theorem node_swap (χ : J → G →* ℂ) (m : J ⊕ J) : node χ m.swap = reflectChar (node χ m) := by
  rcases m with j | j
  · rfl
  · exact (reflectChar_reflectChar (χ j)).symm

theorem nodeWeight_swap (ω : J → ℂ) (m : J ⊕ J) : nodeWeight ω m.swap = conj (nodeWeight ω m) := by
  rcases m with j | j
  · rfl
  · exact (conj_conj (ω j)).symm

theorem nodeWeight_ne_zero {ω : J → ℂ} (hω : ∀ j, ω j ≠ 0) (m : J ⊕ J) : nodeWeight ω m ≠ 0 := by
  rcases m with j | j
  · exact hω j
  · exact (_root_.map_ne_zero _).mpr (hω j)

/-- The outward node of pair `j` at `u`: the one of modulus `> 1` when `|χ_j(u)| ≠ 1`. -/
def outer (χ : J → G →* ℂ) (u : G) (j : J) : J ⊕ J :=
  if 1 < ‖χ j u‖ then Sum.inl j else Sum.inr j

theorem pairIdx_outer (χ : J → G →* ℂ) (u : G) (j : J) : pairIdx (outer χ u j) = j := by
  unfold outer; split_ifs <;> rfl

theorem pairKernel_outer (χ : J → G →* ℂ) (ω : J → ℂ) (u : G) (j : J) :
    pairKernel (node χ (outer χ u j)) (nodeWeight ω (outer χ u j)) = pairKernel (χ j) (ω j) := by
  unfold outer; split_ifs
  · rfl
  · exact pairKernel_reflectChar (χ j) (ω j)

theorem one_lt_norm_outer {χ : J → G →* ℂ} {u : G} (hne : ∀ j, ‖χ j u‖ ≠ 1) (j : J) :
    1 < ‖node χ (outer χ u j) u‖ := by
  unfold outer; split_ifs with h
  · exact h
  · show 1 < ‖reflectChar (χ j) u‖
    rw [norm_reflectChar]
    exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr (map_ne_zero _ _),
      lt_of_le_of_ne (not_lt.mp h) (hne j)⟩

/-- A node of modulus `> 1` is the outward node of its pair. -/
theorem outer_pairIdx_of_one_lt {χ : J → G →* ℂ} {u : G} {m : J ⊕ J}
    (hm : 1 < ‖node χ m u‖) : outer χ u (pairIdx m) = m := by
  rcases m with j | j
  · exact if_pos hm
  · have h : ¬ 1 < ‖χ j u‖ := fun h => by
      change 1 < ‖reflectChar (χ j) u‖ at hm
      rw [norm_reflectChar] at hm
      exact absurd (inv_lt_one_of_one_lt₀ h) (not_lt.mpr hm.le)
    exact if_neg h

/-- Reindexing a sum over outward nodes. -/
theorem sum_eq_sum_outer [Fintype J] [DecidableEq J] (χ : J → G →* ℂ) (u : G) (S : Finset (J ⊕ J))
    (hS : ∀ m ∈ S, outer χ u (pairIdx m) = m) (f : J ⊕ J → ℂ) :
    ∑ m ∈ S, f m = ∑ j, if outer χ u j ∈ S then f (outer χ u j) else 0 := by
  classical
  have h0 : ∑ m ∈ S, f m = ∑ m, if m ∈ S then f m else 0 := by rw [sum_ite_mem, univ_inter]
  rw [h0, Fintype.sum_sum_type, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  have hinl := hS (Sum.inl j)
  have hinr := hS (Sum.inr j)
  simp only [pairIdx, Sum.elim_inl, Sum.elim_inr, id] at hinl hinr
  unfold outer at hinl hinr ⊢
  by_cases h : 1 < ‖χ j u‖
  · simp only [h, if_true] at hinr ⊢
    have : Sum.inr j ∉ S := fun hm => Sum.inl_ne_inr (hinr hm)
    simp [this]
  · simp only [h, if_false] at hinl ⊢
    have : Sum.inl j ∉ S := fun hm => Sum.inr_ne_inl (hinl hm)
    simp [this]

/-- **Vanishing classes kill every weighted sum** of a function of the value. -/
theorem sum_mul_eq_zero_of_classWeight [Fintype J] (ψ : J → G →* ℂ) (w : J → ℂ) (u : G)
    (h : ∀ v, classWeight ψ w u v = 0) (φ : ℂ → ℂ) : ∑ j, w j * φ (ψ j u) = 0 := by
  classical
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image fun j => ψ j u)
    (g := fun j => ψ j u) (fun j _ => mem_image_of_mem _ (mem_univ j))]
  refine sum_eq_zero fun v _ => ?_
  rw [sum_congr rfl fun j hj => by rw [(mem_filter.mp hj).2], ← sum_mul]
  have hv := h v
  unfold classWeight at hv
  convert zero_mul (φ v) using 2


/-! ### The cyclic Hasse principle -/

/-- **Some cyclic subgroup carries a negative square.** A positive-definite kernel plus a nonempty
family of hyperbolic pairs, with non-unitary characters, distinct nodes and nonzero weights, has a
negative square on some cyclic subgroup. -/
theorem exists_one_le_negIndex_zpowers [Fintype J] {p : G → ℂ} (hp : IsPosDefKernel p)
    (χ : J → G →* ℂ) (ω : J → ℂ) (hω : ∀ j, ω j ≠ 0) (hU : ∀ j, ¬ IsUnitaryChar (χ j))
    (hD : Function.Injective (node χ)) (j₀ : J) :
    ∃ u : G, 1 ≤ negIndex ((fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) ∘ zpowersHom G u) := by
  classical
  set ν := node χ with hν
  set c := nodeWeight ω with hc
  set m₀ : J ⊕ J := Sum.inl j₀ with hm₀
  -- the aliasing class of `χ_{j₀}` and its quotient characters
  set T : Finset (J ⊕ J) := univ.filter fun m => IsTorsionAliased (ν m) (ν m₀) with hT
  set η : J ⊕ J → G →* ℂ := fun m => quotChar (ν m) (ν m₀) with hη
  have hm₀T : m₀ ∈ T := mem_filter.mpr ⟨mem_univ _, isTorsionAliased_refl _⟩
  -- Dedekind: `F = Σ_{m ∈ T} c_m η_m` is not identically zero
  have hF : ∃ g, ∑ m ∈ T, c m * η m g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective fun m : T => η m := fun m m' h => by
      refine Subtype.ext (hD (MonoidHom.ext fun g => ?_))
      have := DFunLike.congr_fun h g
      simp only [hη, quotChar_apply] at this
      exact mul_right_cancel₀ (inv_ne_zero (map_ne_zero (ν m₀) g)) this
    have hind := (linearIndependent_monoidHom G ℂ).comp _ hinj
    rw [Fintype.linearIndependent_iff] at hind
    have h0 := hind (fun m => c m) (funext fun g => by
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      rw [Finset.sum_coe_sort T (fun m => c m * η m g)]
      exact hcon g)
    exact nodeWeight_ne_zero hω m₀ (h0 ⟨m₀, hm₀T⟩)
  obtain ⟨g, hg⟩ := hF
  -- the finite-index subgroup on which the quotients of `T` are trivial
  set H : Subgroup G := ⨅ m ∈ T, (η m).ker with hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_iInf' _ fun m hm => (mem_filter.mp hm).2
  -- Neumann: `u ∈ gH` avoids every coincidence subgroup of infinite index
  obtain ⟨h, hhH, hgood⟩ := exists_mul_not_mem H
    (univ.filter fun mm : (J ⊕ J) × (J ⊕ J) => ¬ IsTorsionAliased (ν mm.1) (ν mm.2))
    (fun mm => (quotChar (ν mm.1) (ν mm.2)).ker) (fun mm hmm => (mem_filter.mp hmm).2) g
  set u := g * h with hu
  have hal : ∀ m m', ν m u = ν m' u → IsTorsionAliased (ν m) (ν m') := fun m m' he => by
    by_contra hna
    exact hgood (m, m') (mem_filter.mpr ⟨mem_univ _, hna⟩) (mem_ker_quotChar.mpr he)
  have hne : ∀ j, ‖χ j u‖ ≠ 1 := fun j h1 =>
    hU j (isUnitaryChar_of_isTorsionAliased_reflectChar
      (hal (Sum.inl j) (Sum.inr j) (eq_reflectChar_of_norm_eq_one h1)))
  have hFu : ∑ m ∈ T, c m * η m u ≠ 0 := by
    refine (sum_congr rfl fun m hm => ?_).trans_ne hg
    have hh : h ∈ (η m).ker := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hhH m) hm
    rw [hu, map_mul, MonoidHom.mem_ker.mp hh, mul_one]
  have hTnorm : ∀ m ∈ T, ‖ν m u‖ = ‖χ j₀ u‖ := fun m hm =>
    norm_eq_of_isTorsionAliased (mem_filter.mp hm).2 u
  -- orient every pair outward at `u`
  set o := outer χ u with ho
  set ψ : J → G →* ℂ := fun j => ν (o j) with hψ
  set w : J → ℂ := fun j => c (o j) with hw
  have hk : (fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) =
      fun g => p g + ∑ j, pairKernel (ψ j) (w j) g := by
    funext x; simp only [hψ, hw, ho, hν, hc, pairKernel_outer]
  have hV1 : ∀ j, ‖ψ j u‖ ≠ 1 := fun j => (one_lt_norm_outer hne j).ne'
  have hV2 : ∀ j k, ψ j u ≠ (conj (ψ k u))⁻¹ := fun j k he => by
    have := congrArg norm he
    rw [norm_inv, Complex.norm_conj] at this
    have h1 := one_lt_norm_outer hne j
    have h2 := one_lt_norm_outer hne k
    rw [show node χ (outer χ u j) u = ψ j u from rfl, this] at h1
    exact absurd (inv_lt_one_of_one_lt₀ h2) (not_lt.mpr h1.le)
  refine ⟨u, ?_⟩
  rw [hk, negIndex_zpowers_eq_card_classes hp ψ w u hV1 hV2, Nat.one_le_cast,
    Nat.one_le_iff_ne_zero, Ne, card_eq_zero, filter_eq_empty_iff]
  intro hzero
  have hcw : ∀ v, classWeight ψ w u v = 0 := fun v => by
    by_cases hv : v ∈ univ.image fun j => ψ j u
    · exact not_not.mp (hzero hv)
    · unfold classWeight
      refine sum_eq_zero fun j hj => absurd (mem_image_of_mem (fun j => ψ j u) (mem_univ j)) ?_
      rw [(mem_filter.mp hj).2]; exact hv
  -- an outward, closed set of nodes and a function supported on its values
  have key : ∀ S : Finset (J ⊕ J), (∀ m ∈ S, 1 < ‖ν m u‖) →
      (∀ j, ∀ m ∈ S, ν (o j) u = ν m u → o j ∈ S) → ∀ φ : ℂ → ℂ,
      ∑ m ∈ S, c m * φ (ν m u) =
        ∑ j, w j * (fun z => if ∃ m ∈ S, ν m u = z then φ z else 0) (ψ j u) := by
    intro S hSout hScl φ
    rw [sum_eq_sum_outer χ u S (fun m hm => outer_pairIdx_of_one_lt (hSout m hm))]
    refine sum_congr rfl fun j _ => ?_
    beta_reduce
    by_cases hj : o j ∈ S
    · rw [if_pos hj, if_pos ⟨o j, hj, rfl⟩]
    · rw [if_neg hj, if_neg, mul_zero]
      rintro ⟨m, hm, hmeq⟩
      exact hj (hScl j m hm hmeq.symm)
  rcases lt_or_gt_of_ne (hne j₀) with hlt | hgt
  · -- the class is inner at `u`: its reflection is outward
    have hout : ∀ m ∈ T.image Sum.swap, 1 < ‖ν m u‖ := fun m hm => by
      obtain ⟨m', hm', rfl⟩ := mem_image.mp hm
      rw [hν, node_swap, norm_reflectChar, ← hν, hTnorm m' hm']
      exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr (map_ne_zero _ _), hlt⟩
    have hcl : ∀ j, ∀ m ∈ T.image Sum.swap, ν (o j) u = ν m u → o j ∈ T.image Sum.swap := by
      intro j m hm he
      obtain ⟨m', hm', rfl⟩ := mem_image.mp hm
      have h1 := hal _ _ he
      rw [hν, node_swap χ m', ← isTorsionAliased_reflectChar_iff, reflectChar_reflectChar,
        ← node_swap] at h1
      refine mem_image.mpr ⟨(o j).swap, mem_filter.mpr ⟨mem_univ _, h1.trans ?_⟩, Sum.swap_swap _⟩
      exact (mem_filter.mp hm').2
    set φ : ℂ → ℂ := fun z => conj (z * conj (χ j₀ u)) with hφ
    have hval : ∀ m ∈ T, c m.swap * φ (ν m.swap u) = conj (c m * η m u) := fun m hm => by
      have hη1 : ‖η m u‖ = 1 := norm_quotChar_eq_one (mem_filter.mp hm).2 u
      have hνm : ν m u = η m u * χ j₀ u := by
        simp only [hη, quotChar_apply]
        rw [mul_assoc, inv_mul_cancel₀ (map_ne_zero (ν m₀) u), mul_one]
      have hsw : ν m.swap u = (conj (ν m u))⁻¹ := by
        rw [hν, node_swap, reflectChar_apply, map_inv_eq_inv, map_inv₀, ← hν]
      rw [hφ, hsw, hνm, map_mul, mul_inv, mul_assoc,
        inv_mul_cancel₀ ((_root_.map_ne_zero _).mpr (map_ne_zero (χ j₀) u)), mul_one,
        inv_conj_of_norm_eq_one hη1, hc, nodeWeight_swap, ← hc, map_mul]
    apply hFu
    have h1 := (key _ hout hcl φ).trans (sum_mul_eq_zero_of_classWeight ψ w u hcw _)
    rw [sum_image fun a _ b _ hab => Sum.swap_injective hab, sum_congr rfl hval, ← map_sum,
      map_eq_zero] at h1
    exact h1
  · -- the class is outward at `u`
    have hout : ∀ m ∈ T, 1 < ‖ν m u‖ := fun m hm => by rw [hTnorm m hm]; exact hgt
    have hcl : ∀ j, ∀ m ∈ T, ν (o j) u = ν m u → o j ∈ T := fun j m hm he =>
      mem_filter.mpr ⟨mem_univ _, (hal _ _ he).trans (mem_filter.mp hm).2⟩
    apply hFu
    calc ∑ m ∈ T, c m * η m u = ∑ m ∈ T, c m * (fun z => z * (χ j₀ u)⁻¹) (ν m u) := rfl
      _ = _ := key T hout hcl _
      _ = 0 := sum_mul_eq_zero_of_classWeight ψ w u hcw _

/-- **The cyclic Hasse principle.** A positive-definite kernel plus hyperbolic pairs (non-unitary
characters, distinct nodes, nonzero weights) that is positive definite on every cyclic subgroup has
no pair: it is the positive-definite part. -/
theorem negIndex_eq_zero_of_forall_zpowers [Fintype J] {p : G → ℂ} (hp : IsPosDefKernel p)
    (χ : J → G →* ℂ) (ω : J → ℂ) (hω : ∀ j, ω j ≠ 0) (hU : ∀ j, ¬ IsUnitaryChar (χ j))
    (hD : Function.Injective (node χ))
    (h : ∀ u : G, negIndex ((fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) ∘ zpowersHom G u) = 0) :
    IsEmpty J ∧ negIndex (fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) = 0 := by
  have hJ : IsEmpty J := ⟨fun j₀ => by
    obtain ⟨u, hu⟩ := exists_one_le_negIndex_zpowers hp χ ω hω hU hD j₀
    rw [h u] at hu
    exact absurd hu (by norm_num)⟩
  refine ⟨hJ, ?_⟩
  have : (fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) = p := by funext g; simp
  rw [this]
  exact hp.negIndex_eq_zero

/-! ### Separation without torsion aliasing -/

/-- **Separation.** If no two distinct nodes are torsion-aliased, some element is off the unit
circle at every character and separates all `2κ` nodes. -/
theorem exists_separating_of_not_aliased {κ : ℕ} (χ : Fin κ → G →* ℂ)
    (hA : ∀ m m', m ≠ m' → ¬ IsTorsionAliased (node χ m) (node χ m')) :
    ∃ u : G, (∀ j, ‖χ j u‖ ≠ 1) ∧ Function.Injective (nodes χ u) := by
  classical
  obtain ⟨u, -, hu⟩ := exists_mul_not_mem (⊤ : Subgroup G)
    (univ.filter fun mm : (Fin κ ⊕ Fin κ) × (Fin κ ⊕ Fin κ) => mm.1 ≠ mm.2)
    (fun mm => (quotChar (node χ mm.1) (node χ mm.2)).ker)
    (fun mm hmm => hA _ _ (mem_filter.mp hmm).2) 1
  have hal : ∀ m m', node χ m (1 * u) = node χ m' (1 * u) → m = m' := fun m m' he => by
    by_contra hne
    exact hu (m, m') (mem_filter.mpr ⟨mem_univ _, hne⟩) (mem_ker_quotChar.mpr he)
  refine ⟨u, fun j h1 => Sum.inl_ne_inr (hal (Sum.inl j) (Sum.inr j) ?_), fun m m' he => hal m m' ?_⟩
  · rw [one_mul]; exact eq_reflectChar_of_norm_eq_one h1
  · rw [one_mul]; rcases m with j | j <;> rcases m' with j' | j' <;> exact he

/-- **One cyclic subgroup carries the whole index** when no two nodes are torsion-aliased. -/
theorem negIndex_zpowers_eq_of_not_aliased {κ : ℕ} {p : G → ℂ} (hp : IsPosDefKernel p)
    (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0)
    (hA : ∀ m m', m ≠ m' → ¬ IsTorsionAliased (node χ m) (node χ m')) :
    ∃ u : G, negIndex ((fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) ∘ zpowersHom G u) = κ ∧
      negIndex (fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) = κ := by
  obtain ⟨u, hne, hsep⟩ := exists_separating_of_not_aliased χ hA
  refine ⟨u, ?_, negIndex_add_sum_pairKernel_eq hp χ ω hω u hne hsep⟩
  rw [comp_add_sum_pairKernel]
  simp only [comp_zpowersHom]
  refine negIndex_add_sum_pairKernel_eq (hp.comp _) _ ω hω (Multiplicative.ofAdd 1)
    (fun j => ?_) ?_
  · rw [valChar_ofAdd_one (map_ne_zero _ _)]; exact hne j
  · have : nodes (fun j => valChar (χ j u)) (Multiplicative.ofAdd 1) = nodes χ u := by
      funext m
      rcases m with j | j
      · exact valChar_ofAdd_one (map_ne_zero _ _)
      · show reflectChar (valChar (χ j u)) _ = reflectChar (χ j) u
        rw [reflectChar_valChar_ofAdd_one (map_ne_zero _ _), reflectChar_apply, map_inv_eq_inv,
          map_inv₀]
    rw [this]; exact hsep

end GaloisForLFunctions.ArithmeticKreinLangerTheory
