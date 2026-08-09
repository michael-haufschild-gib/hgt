import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.OrderIsoNat
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Kolchin--Spencer inverse-limit noncompactness

For a tower of finite-dimensional real normed spaces with surjective continuous linear
truncations, this file constructs the product normal form of its inverse limit.  It then proves the
exact local-compactness criterion and the finite-observer tail law.  Splittings are chosen using
finite dimensionality; no splitting or compactness conclusion is assumed.
-/

namespace HTGeometry.NomologicalHomotopyGeometry

open Function Filter Module Set
open scoped Topology

universe u

namespace KolchinSpencer

variable (V : ℕ → Type u)
variable [∀ n, NormedAddCommGroup (V n)] [∀ n, NormedSpace ℝ (V n)]
variable [∀ n, FiniteDimensional ℝ (V n)]
variable (π : ∀ n, V (n + 1) →L[ℝ] V n)

/-- The inverse limit, realized as the closed linear compatibility subspace of the product. -/
def inverseLimitSubmodule : Submodule ℝ (∀ n, V n) where
  carrier := {x | ∀ n, π n (x (n + 1)) = x n}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy n
    simp [hx n, hy n]
  smul_mem' := by
    intro c x hx n
    simp [hx n]

/-- Compatible infinite histories in the truncation tower. -/
abbrev InverseLimit := inverseLimitSubmodule V π

/-- New Spencer-symbol freedom at transition `n + 1 → n`. -/
abbrev Kernel (n : ℕ) := LinearMap.ker (π n).toLinearMap

variable (hπ : ∀ n, Surjective (π n))

include hπ

/-- A chosen continuous linear section of the `n`th truncation. -/
noncomputable def splitting (n : ℕ) : V n →L[ℝ] V (n + 1) :=
  (ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional (hπ n)).rightInverse

@[simp]
theorem splitting_rightInverse (n : ℕ) (x : V n) : π n (splitting V π hπ n x) = x :=
  (ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
    (hπ n)).rightInverse_rightInverse x

/-- Reconstruct a compatible history recursively from its base value and Spencer coordinates. -/
noncomputable def reconstruct :
    V 0 × (∀ n, Kernel V π n) → ∀ n, V n
  | z, 0 => z.1
  | z, n + 1 => splitting V π hπ n (reconstruct z n) + z.2 n

@[simp]
theorem reconstruct_zero (z : V 0 × (∀ n, Kernel V π n)) :
    reconstruct V π hπ z 0 = z.1 := rfl

@[simp]
theorem reconstruct_succ (z : V 0 × (∀ n, Kernel V π n)) (n : ℕ) :
    reconstruct V π hπ z (n + 1) =
      splitting V π hπ n (reconstruct V π hπ z n) + z.2 n := rfl

theorem reconstruct_compatible (z : V 0 × (∀ n, Kernel V π n)) (n : ℕ) :
    π n (reconstruct V π hπ z (n + 1)) = reconstruct V π hπ z n := by
  simp [reconstruct_succ]

/-- The inverse map of normal coordinates, as an element of the inverse limit. -/
noncomputable def ofNormalCoordinates (z : V 0 × (∀ n, Kernel V π n)) :
    InverseLimit V π :=
  ⟨reconstruct V π hπ z, reconstruct_compatible V π hπ z⟩

/-- Base value and successive vertical errors of a compatible history. -/
noncomputable def normalCoordinates (x : InverseLimit V π) :
    V 0 × (∀ n, Kernel V π n) :=
  (x.1 0, fun n => ⟨x.1 (n + 1) - splitting V π hπ n (x.1 n), by
    change π n (x.1 (n + 1) - splitting V π hπ n (x.1 n)) = 0
    simp [x.2 n]⟩)

@[simp]
theorem normalCoordinates_fst (x : InverseLimit V π) :
    (normalCoordinates V π hπ x).1 = x.1 0 := rfl

@[simp]
theorem normalCoordinates_snd (x : InverseLimit V π) (n : ℕ) :
    ((normalCoordinates V π hπ x).2 n : V (n + 1)) =
      x.1 (n + 1) - splitting V π hπ n (x.1 n) := rfl

theorem reconstruct_normalCoordinates (x : InverseLimit V π) (n : ℕ) :
    reconstruct V π hπ (normalCoordinates V π hπ x) n = x.1 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [reconstruct_succ, ih]

theorem normalCoordinates_ofNormalCoordinates (z : V 0 × (∀ n, Kernel V π n)) :
    normalCoordinates V π hπ (ofNormalCoordinates V π hπ z) = z := by
  ext n
  · rfl
  · simp [normalCoordinates, ofNormalCoordinates, reconstruct_succ]

theorem ofNormalCoordinates_normalCoordinates (x : InverseLimit V π) :
    ofNormalCoordinates V π hπ (normalCoordinates V π hπ x) = x := by
  apply Subtype.ext
  funext n
  exact reconstruct_normalCoordinates V π hπ x n

theorem reconstruct_add (z w : V 0 × (∀ n, Kernel V π n)) (n : ℕ) :
    reconstruct V π hπ (z + w) n =
      reconstruct V π hπ z n + reconstruct V π hπ w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [reconstruct_succ, ih, add_assoc, add_left_comm, add_comm]

theorem reconstruct_smul (c : ℝ) (z : V 0 × (∀ n, Kernel V π n)) (n : ℕ) :
    reconstruct V π hπ (c • z) n = c • reconstruct V π hπ z n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [reconstruct_succ, ih, smul_add]

theorem reconstruct_continuous_component (n : ℕ) :
    Continuous (fun z : V 0 × (∀ n, Kernel V π n) => reconstruct V π hπ z n) := by
  induction n with
  | zero => exact continuous_fst
  | succ n ih =>
      exact ((splitting V π hπ n).continuous.comp ih).add
        (continuous_subtype_val.comp ((continuous_apply n).comp continuous_snd))

/-- Theorem 2.1: noncanonical topological linear product normal form of the inverse limit. -/
noncomputable def inverseLimitNormalForm :
    InverseLimit V π ≃L[ℝ] V 0 × (∀ n, Kernel V π n) where
  toFun := normalCoordinates V π hπ
  invFun := ofNormalCoordinates V π hπ
  left_inv := ofNormalCoordinates_normalCoordinates V π hπ
  right_inv := normalCoordinates_ofNormalCoordinates V π hπ
  map_add' := by
    intro x y
    apply Prod.ext
    · rfl
    · funext n
      apply Subtype.ext
      simp [normalCoordinates, add_sub_add_comm]
  map_smul' := by
    intro c x
    apply Prod.ext
    · rfl
    · funext n
      apply Subtype.ext
      simp [normalCoordinates, smul_sub]
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (continuous_apply 0).comp continuous_subtype_val
    · exact continuous_pi fun n => Continuous.subtype_mk
        (((continuous_apply (n + 1)).comp continuous_subtype_val).sub
          ((splitting V π hπ n).continuous.comp
            ((continuous_apply n).comp continuous_subtype_val))) _
  continuous_invFun := by
    exact Continuous.subtype_mk
      (continuous_pi fun n => reconstruct_continuous_component V π hπ n) _

/-! ## Algebraic growth and local compactness -/

/-- Rank-nullity along a surjective truncation. -/
theorem finrank_succ (n : ℕ) :
    finrank ℝ (V (n + 1)) = finrank ℝ (V n) + finrank ℝ (Kernel V π n) := by
  have hrange : LinearMap.range (π n).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (hπ n)
  have h := (π n).toLinearMap.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at h
  change finrank ℝ (V n) + finrank ℝ (Kernel V π n) = finrank ℝ (V (n + 1)) at h
  exact h.symm

/-- Truncation dimensions are monotone. -/
theorem finrank_monotone : Monotone (fun n => finrank ℝ (V n)) := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
      apply ih.trans
      change finrank ℝ (V m) ≤ finrank ℝ (V (m + 1))
      rw [finrank_succ V π hπ m]
      exact Nat.le_add_right _ _

omit hπ

/-- A bounded monotone natural sequence is eventually constant, in the explicit form used below. -/
theorem monotone_nat_bounded_eventually_constant {a : ℕ → ℕ} (ha : Monotone a)
    (hbound : ∃ B, ∀ n, a n ≤ B) :
    ∃ N, ∀ n, N ≤ n → a n = a N := by
  rcases hbound with ⟨B, hB⟩
  let r : Set ℕ := Set.range a
  have hrfin : r.Finite := by
    exact (Set.finite_Iic B).subset (fun x hx => by
      rcases hx with ⟨n, rfl⟩
      exact hB n)
  have hrnonempty : r.Nonempty := ⟨a 0, ⟨0, rfl⟩⟩
  obtain ⟨M, hMmem, hM⟩ := Set.exists_max_image r id hrfin hrnonempty
  rcases hMmem with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  apply Nat.le_antisymm
  · simpa [hN] using hM (a n) ⟨n, rfl⟩
  · exact ha hn

include hπ

/-- Bounded truncation dimensions are equivalent to eventual vanishing of Spencer kernels. -/
theorem bounded_finrank_iff_eventually_kernel_eq_bot :
    (∃ B, ∀ n, finrank ℝ (V n) ≤ B) ↔
      ∃ N, ∀ n, N ≤ n → Kernel V π n = ⊥ := by
  constructor
  · intro hb
    obtain ⟨N, hN⟩ := monotone_nat_bounded_eventually_constant
      (finrank_monotone V π hπ) hb
    refine ⟨N, fun n hn => ?_⟩
    have hd : finrank ℝ (Kernel V π n) = 0 := by
      have hsame : finrank ℝ (V (n + 1)) = finrank ℝ (V n) := by
        rw [hN n hn, hN (n + 1) (hn.trans (Nat.le_succ n))]
      rw [finrank_succ V π hπ n] at hsame
      omega
    exact Submodule.finrank_eq_zero.mp hd
  · rintro ⟨N, hN⟩
    refine ⟨finrank ℝ (V N), fun n => ?_⟩
    rcases le_total n N with hn | hn
    · exact finrank_monotone V π hπ hn
    · have hconst : ∀ k, N ≤ k → finrank ℝ (V k) = finrank ℝ (V N) := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => rfl
        | succ k hk ih =>
            rw [finrank_succ V π hπ k, hN k hk, finrank_bot, add_zero, ih]
      exact (hconst n hn).le

omit hπ

set_option maxHeartbeats 1000000 in
/-- An infinite collection of nonzero product factors forces infinite algebraic dimension. -/
theorem not_finiteDimensional_pi_of_infinite_nonzero
    (hK : Set.Infinite {n | Kernel V π n ≠ ⊥}) :
    ¬ FiniteDimensional ℝ (∀ n, Kernel V π n) := by
  intro hfinite
  let I := {n : ℕ // Kernel V π n ≠ ⊥}
  have hI : Infinite I := Set.infinite_coe_iff.mpr hK
  letI : Infinite I := hI
  letI : DecidableEq ℕ := Classical.decEq ℕ
  have hnontrivial (i : I) : Nontrivial (Kernel V π i.1) :=
    Submodule.nontrivial_iff_ne_bot.mpr i.2
  choose v hv using fun i : I => @exists_ne (Kernel V π i.1) (hnontrivial i) 0
  let b : I → (∀ n, Kernel V π n) := fun i => Pi.single i.1 (v i)
  let restrict : (∀ n, Kernel V π n) →ₗ[ℝ] (∀ i : I, Kernel V π i.1) :=
    (Pi.compRightL ℝ (fun n => Kernel V π n) Subtype.val).toLinearMap
  have hrestrict : restrict ∘ b = fun i => Pi.single i (v i) := by
    funext i
    funext j
    by_cases hij : i = j
    · subst j
      simp [restrict, b]
    · have hval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [restrict, b, hij, hval]
  have hb : LinearIndependent ℝ b := by
    apply LinearIndependent.of_comp restrict
    rw [hrestrict]
    rw [← linearIndependent_equiv (Equiv.sigmaPUnit I)]
    exact Pi.linearIndependent_single (fun i (_ : Unit) => v i) (fun i => by
      rw [linearIndependent_unique_iff]
      exact hv i)
  letI : FiniteDimensional ℝ (∀ n, Kernel V π n) := hfinite
  letI : Finite I := hb.finite
  exact _root_.not_finite I

/-- If all factors after `N` vanish, the full product is linearly equivalent to a finite product. -/
noncomputable def piEventuallyZeroLinearEquiv (N : ℕ)
    (hK : ∀ n, N ≤ n → Kernel V π n = ⊥) :
    (∀ n, Kernel V π n) ≃ₗ[ℝ] (∀ n : Fin N, Kernel V π n) where
  toFun x n := x n
  invFun x n := if hn : n < N then x ⟨n, hn⟩ else 0
  left_inv := by
    intro x
    funext n
    dsimp
    by_cases hn : n < N
    · simp [hn]
    · simp [hn]
      have hz : Kernel V π n = ⊥ := hK n (Nat.le_of_not_gt hn)
      letI : Subsingleton (Kernel V π n) := hz ▸ inferInstance
      exact Subsingleton.elim _ _
  right_inv := by intro x; funext n; simp
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; funext n; rfl

/-- Eventual kernel vanishing makes the kernel product finite-dimensional. -/
theorem finiteDimensional_pi_of_eventually_kernel_eq_bot
    {N : ℕ} (hK : ∀ n, N ≤ n → Kernel V π n = ⊥) :
    FiniteDimensional ℝ (∀ n, Kernel V π n) := by
  exact FiniteDimensional.of_injective
    (piEventuallyZeroLinearEquiv V π N hK).toLinearMap
    (piEventuallyZeroLinearEquiv V π N hK).injective

/-- Algebraic finite dimensionality of the kernel product is exactly eventual kernel vanishing. -/
theorem finiteDimensional_pi_iff_eventually_kernel_eq_bot :
    FiniteDimensional ℝ (∀ n, Kernel V π n) ↔
      ∃ N, ∀ n, N ≤ n → Kernel V π n = ⊥ := by
  constructor
  · intro hfinite
    by_contra h
    push_neg at h
    have hinf : Set.Infinite {n | Kernel V π n ≠ ⊥} := by
      apply Set.infinite_of_not_bddAbove
      rintro ⟨B, hB⟩
      obtain ⟨n, hn, hne⟩ := h (B + 1)
      have := hB hne
      omega
    exact not_finiteDimensional_pi_of_infinite_nonzero V π hinf hfinite
  · rintro ⟨N, hN⟩
    exact finiteDimensional_pi_of_eventually_kernel_eq_bot V π hN

include hπ

/-- The inverse limit is finite-dimensional exactly when the Spencer symbols eventually vanish. -/
theorem finiteDimensional_inverseLimit_iff_eventually_kernel_eq_bot :
    FiniteDimensional ℝ (InverseLimit V π) ↔
      ∃ N, ∀ n, N ≤ n → Kernel V π n = ⊥ := by
  rw [← finiteDimensional_pi_iff_eventually_kernel_eq_bot V π]
  constructor
  · intro h
    letI : FiniteDimensional ℝ (InverseLimit V π) := h
    letI : FiniteDimensional ℝ (V 0 × (∀ n, Kernel V π n)) :=
      FiniteDimensional.of_surjective
        (inverseLimitNormalForm V π hπ).toLinearEquiv.toLinearMap
        (inverseLimitNormalForm V π hπ).surjective
    exact FiniteDimensional.of_injective
      (LinearMap.inr ℝ (V 0) (∀ n, Kernel V π n))
      (LinearMap.inr_injective (R := ℝ) (M := V 0) (M₂ := (∀ n, Kernel V π n)))
  · intro hpi
    letI : FiniteDimensional ℝ (∀ n, Kernel V π n) := hpi
    exact FiniteDimensional.of_injective
      (inverseLimitNormalForm V π hπ).toLinearEquiv.toLinearMap
      (inverseLimitNormalForm V π hπ).injective

omit hπ

/-- Riesz's theorem gives the exact equivalence between local compactness and algebraic finite
dimensionality for the inverse-limit topology. -/
theorem locallyCompact_inverseLimit_iff_finiteDimensional :
    LocallyCompactSpace (InverseLimit V π) ↔ FiniteDimensional ℝ (InverseLimit V π) := by
  constructor
  · intro h
    letI : LocallyCompactSpace (InverseLimit V π) := h
    exact FiniteDimensional.of_locallyCompactSpace ℝ
  · intro h
    letI : FiniteDimensional ℝ (InverseLimit V π) := h
    exact LocallyCompactSpace.of_finiteDimensional_of_complete ℝ (InverseLimit V π)

include hπ

/-- Theorem 3.1, local-compactness/eventual-symbol form. -/
theorem locallyCompact_inverseLimit_iff_eventually_kernel_eq_bot :
    LocallyCompactSpace (InverseLimit V π) ↔
      ∃ N, ∀ n, N ≤ n → Kernel V π n = ⊥ := by
  rw [locallyCompact_inverseLimit_iff_finiteDimensional V π,
    finiteDimensional_inverseLimit_iff_eventually_kernel_eq_bot V π hπ]

/-- Theorem 3.1, local-compactness/bounded-growth form. -/
theorem locallyCompact_inverseLimit_iff_bounded_finrank :
    LocallyCompactSpace (InverseLimit V π) ↔
      ∃ B, ∀ n, finrank ℝ (V n) ≤ B := by
  rw [locallyCompact_inverseLimit_iff_eventually_kernel_eq_bot V π hπ,
    ← bounded_finrank_iff_eventually_kernel_eq_bot V π hπ]

/-- Unbounded jet dimension forces nonlocal compactness. -/
theorem not_locallyCompact_of_unbounded_finrank
    (hunbounded : ∀ B, ∃ n, B < finrank ℝ (V n)) :
    ¬ LocallyCompactSpace (InverseLimit V π) := by
  intro hlocal
  obtain ⟨B, hB⟩ :=
    (locallyCompact_inverseLimit_iff_bounded_finrank V π hπ).mp hlocal
  obtain ⟨n, hn⟩ := hunbounded B
  exact (Nat.not_lt_of_ge (hB n)) hn

/-- Formula `(KS.6)`: dimension tending to infinity forces nonlocal compactness. -/
theorem not_locallyCompact_of_finrank_tendsto_atTop
    (hgrowth : Tendsto (fun n => finrank ℝ (V n)) atTop atTop) :
    ¬ LocallyCompactSpace (InverseLimit V π) := by
  apply not_locallyCompact_of_unbounded_finrank V π hπ
  intro B
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp hgrowth) (B + 1)
  exact ⟨N, by have := hN N le_rfl; omega⟩

/-! ## Finite observers and the full Spencer tail -/

omit hπ

/-- Transition indices invisible at prolongation order `N`.  Coordinate `n` represents the card's
symbol `K_(n+1)`, so `N ≤ n` is exactly `n + 1 > N`. -/
abbrev TailIndex (N : ℕ) := {n : ℕ // N ≤ n}

/-- Full product of all Spencer-symbol factors beyond observer order `N`. -/
abbrev TailProduct (N : ℕ) := ∀ i : TailIndex N, Kernel V π i.1

/-- Extend a tail by zero in every earlier Spencer coordinate. -/
noncomputable def tailKernelExtension (N : ℕ) :
    TailProduct V π N →L[ℝ] (∀ n, Kernel V π n) :=
  ContinuousLinearMap.pi fun n => if hn : N ≤ n then
    ContinuousLinearMap.proj (R := ℝ)
      (φ := fun i : TailIndex N => Kernel V π i.1) ⟨n, hn⟩
  else 0

@[simp]
theorem tailKernelExtension_apply_of_le (N n : ℕ) (hn : N ≤ n)
    (x : TailProduct V π N) :
    tailKernelExtension V π N x n = x ⟨n, hn⟩ := by
  simp [tailKernelExtension, hn]

@[simp]
theorem tailKernelExtension_apply_of_lt (N n : ℕ) (hn : n < N)
    (x : TailProduct V π N) :
    tailKernelExtension V π N x n = 0 := by
  simp [tailKernelExtension, Nat.not_le.mpr hn]

/-- Restriction from all Spencer coordinates to the full tail. -/
def tailKernelRestriction (N : ℕ) :
    (∀ n, Kernel V π n) →L[ℝ] TailProduct V π N :=
  Pi.compRightL ℝ (fun n => Kernel V π n) Subtype.val

@[simp]
theorem tailKernelRestriction_extension (N : ℕ) (x : TailProduct V π N) :
    tailKernelRestriction V π N (tailKernelExtension V π N x) = x := by
  funext i
  change tailKernelExtension V π N x i.1 = x i
  simpa using tailKernelExtension_apply_of_le V π N i.1 i.2 x

include hπ

/-- The tail embedded as compatible histories with zero value through order `N`. -/
noncomputable def tailEmbedding (N : ℕ) :
    TailProduct V π N →L[ℝ] InverseLimit V π :=
  (inverseLimitNormalForm V π hπ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inr ℝ (V 0) (∀ n, Kernel V π n)).comp
      (tailKernelExtension V π N))

/-- Recover tail coordinates from any compatible history. -/
noncomputable def tailProjection (N : ℕ) :
    InverseLimit V π →L[ℝ] TailProduct V π N :=
  (tailKernelRestriction V π N).comp
    ((ContinuousLinearMap.snd ℝ (V 0) (∀ n, Kernel V π n)).comp
      (inverseLimitNormalForm V π hπ).toContinuousLinearMap)

@[simp]
theorem tailProjection_embedding (N : ℕ) (x : TailProduct V π N) :
    tailProjection V π hπ N (tailEmbedding V π hπ N x) = x := by
  simp [tailProjection, tailEmbedding]

theorem tailEmbedding_injective (N : ℕ) :
    Injective (tailEmbedding V π hπ N) := by
  exact (show LeftInverse (tailProjection V π hπ N) (tailEmbedding V π hπ N) from
    tailProjection_embedding V π hπ N).injective

/-- The truncation map from the inverse limit to order `N`. -/
def truncation (N : ℕ) : InverseLimit V π →L[ℝ] V N :=
  (ContinuousLinearMap.proj N).comp (inverseLimitSubmodule V π).subtypeL

theorem reconstruct_tail_eq_zero (N n : ℕ) (hn : n ≤ N) (x : TailProduct V π N) :
    reconstruct V π hπ
      (0, tailKernelExtension V π N x) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnN : n < N := by omega
      simp [reconstruct_succ, ih (by omega), tailKernelExtension_apply_of_lt V π N n hnN]

/-- Every full-tail history has zero truncation at observer order `N`. -/
@[simp]
theorem truncation_tailEmbedding (N : ℕ) (x : TailProduct V π N) :
    truncation V π N (tailEmbedding V π hπ N x) = 0 := by
  change reconstruct V π hπ (0, tailKernelExtension V π N x) N = 0
  exact reconstruct_tail_eq_zero V π hπ N N le_rfl x

section Observer

variable {O : Type*} [NormedAddCommGroup O] [NormedSpace ℝ O]

/-- Corollary 4.1: if a continuous linear observer factors through order `N`, every full-tail
history lies in its kernel. -/
theorem tailEmbedding_mem_observerKernel (N : ℕ)
    (q : InverseLimit V π →L[ℝ] O) (qN : V N →L[ℝ] O)
    (hq : q = qN.comp (truncation V π N)) (x : TailProduct V π N) :
    tailEmbedding V π hπ N x ∈ LinearMap.ker q.toLinearMap := by
  change q (tailEmbedding V π hπ N x) = 0
  rw [hq]
  simp

/-- Set/subspace form of `(KS.9)`: the entire tail range is contained in the observer kernel. -/
theorem range_tailEmbedding_le_observerKernel (N : ℕ)
    (q : InverseLimit V π →L[ℝ] O) (qN : V N →L[ℝ] O)
    (hq : q = qN.comp (truncation V π N)) :
    LinearMap.range (tailEmbedding V π hπ N).toLinearMap ≤
      LinearMap.ker q.toLinearMap := by
  rintro y ⟨x, rfl⟩
  exact tailEmbedding_mem_observerKernel V π hπ N q qN hq x

end Observer

/-- The full invisible-tail subspace inside the inverse limit. -/
noncomputable def TailRange (N : ℕ) : Submodule ℝ (InverseLimit V π) :=
  LinearMap.range (tailEmbedding V π hπ N).toLinearMap

/-- The embedded tail carries exactly its product topology. -/
noncomputable def tailRangeNormalForm (N : ℕ) :
    TailProduct V π N ≃L[ℝ] TailRange V π hπ N where
  toFun x := ⟨tailEmbedding V π hπ N x, ⟨x, rfl⟩⟩
  invFun y := tailProjection V π hπ N y.1
  left_inv := tailProjection_embedding V π hπ N
  right_inv := by
    intro y
    apply Subtype.ext
    rcases y.2 with ⟨x, hx⟩
    change tailEmbedding V π hπ N (tailProjection V π hπ N y.1) = y.1
    rw [← hx]
    simp
  map_add' := by intro x y; apply Subtype.ext; simp
  map_smul' := by intro c x; apply Subtype.ext; simp
  continuous_toFun := Continuous.subtype_mk (tailEmbedding V π hπ N).continuous _
  continuous_invFun := (tailProjection V π hπ N).continuous.comp continuous_subtype_val

omit hπ

set_option maxHeartbeats 1000000 in
/-- Infinitely many nonzero tail symbols force the tail product to be infinite-dimensional. -/
theorem tailProduct_not_finiteDimensional (N : ℕ)
    (hK : Set.Infinite {i : TailIndex N | Kernel V π i.1 ≠ ⊥}) :
    ¬ FiniteDimensional ℝ (TailProduct V π N) := by
  intro hfinite
  let J := {i : TailIndex N // Kernel V π i.1 ≠ ⊥}
  have hJ : Infinite J := Set.infinite_coe_iff.mpr hK
  letI : Infinite J := hJ
  letI : DecidableEq (TailIndex N) := Classical.decEq (TailIndex N)
  have hnontrivial (j : J) : Nontrivial (Kernel V π j.1.1) :=
    Submodule.nontrivial_iff_ne_bot.mpr j.2
  choose v hv using fun j : J => @exists_ne (Kernel V π j.1.1) (hnontrivial j) 0
  let b : J → TailProduct V π N := fun j => Pi.single j.1 (v j)
  let restrict : TailProduct V π N →ₗ[ℝ] (∀ j : J, Kernel V π j.1.1) :=
    (Pi.compRightL ℝ (fun i : TailIndex N => Kernel V π i.1) Subtype.val).toLinearMap
  have hrestrict : restrict ∘ b = fun j => Pi.single j (v j) := by
    funext i
    funext j
    by_cases hij : i = j
    · subst j
      simp [restrict, b]
    · have hval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [restrict, b, hij, hval]
  have hb : LinearIndependent ℝ b := by
    apply LinearIndependent.of_comp restrict
    rw [hrestrict, ← linearIndependent_equiv (Equiv.sigmaPUnit J)]
    exact Pi.linearIndependent_single (fun j (_ : Unit) => v j) (fun j => by
      rw [linearIndependent_unique_iff]
      exact hv j)
  letI : FiniteDimensional ℝ (TailProduct V π N) := hfinite
  letI : Finite J := hb.finite
  exact _root_.not_finite J

/-- If infinitely many tail factors are nonzero, the invisible tail product is not locally compact. -/
theorem tailProduct_not_locallyCompact (N : ℕ)
    (hK : Set.Infinite {i : TailIndex N | Kernel V π i.1 ≠ ⊥}) :
    ¬ LocallyCompactSpace (TailProduct V π N) := by
  intro hlocal
  letI : LocallyCompactSpace (TailProduct V π N) := hlocal
  exact tailProduct_not_finiteDimensional V π N hK
    (FiniteDimensional.of_locallyCompactSpace ℝ)

include hπ

/-- Corollary 4.1, topological form: the full invisible fibre itself is not locally compact when
infinitely many tail factors survive. -/
theorem tailRange_not_locallyCompact (N : ℕ)
    (hK : Set.Infinite {i : TailIndex N | Kernel V π i.1 ≠ ⊥}) :
    ¬ LocallyCompactSpace (TailRange V π hπ N) := by
  intro hlocal
  letI : LocallyCompactSpace (TailRange V π hπ N) := hlocal
  letI : LocallyCompactSpace (TailProduct V π N) :=
    (tailRangeNormalForm V π hπ N).toHomeomorph.isOpenEmbedding.locallyCompactSpace
  exact tailProduct_not_locallyCompact V π N hK inferInstance

/-- Unbounded prolongation dimension leaves infinitely many nonzero Spencer factors beyond every
fixed observer order. -/
theorem infinite_nonzero_tail_of_unbounded_finrank
    (hunbounded : ∀ B, ∃ n, B < finrank ℝ (V n)) (N : ℕ) :
    Set.Infinite {i : TailIndex N | Kernel V π i.1 ≠ ⊥} := by
  have hnotEventually : ¬ ∃ M, ∀ n, M ≤ n → Kernel V π n = ⊥ := by
    intro heventual
    obtain ⟨B, hB⟩ :=
      (bounded_finrank_iff_eventually_kernel_eq_bot V π hπ).mpr heventual
    obtain ⟨n, hn⟩ := hunbounded B
    exact (Nat.not_lt_of_ge (hB n)) hn
  have hexists (M : ℕ) : ∃ n, M ≤ n ∧ Kernel V π n ≠ ⊥ := by
    by_contra h
    apply hnotEventually
    refine ⟨M, fun n hn => ?_⟩
    by_contra hne
    exact h ⟨n, hn, hne⟩
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  obtain ⟨n, hn, hne⟩ := hexists (b.1 + 1)
  have hNn : N ≤ n := b.2.trans (by omega)
  have hle := hb (show (⟨n, hNn⟩ : TailIndex N) ∈
    {i : TailIndex N | Kernel V π i.1 ≠ ⊥} from hne)
  exact (Nat.not_succ_le_self b.1) (hn.trans hle)

/-- Corollary 5.1: an unbounded Kolchin dimension function agreeing with the smooth jet tangent
dimensions forces nonlocal compactness and an infinite tail beyond every finite order. -/
theorem kolchin_unbounded_specialization (ω : ℕ → ℕ)
    (hω : ∀ n, ω n = finrank ℝ (V n))
    (hωunbounded : ∀ B, ∃ n, B < ω n) :
    ¬ LocallyCompactSpace (InverseLimit V π) ∧
      ∀ N, Set.Infinite {i : TailIndex N | Kernel V π i.1 ≠ ⊥} := by
  have hdim : ∀ B, ∃ n, B < finrank ℝ (V n) := by
    intro B
    obtain ⟨n, hn⟩ := hωunbounded B
    exact ⟨n, by simpa [hω n] using hn⟩
  exact ⟨not_locallyCompact_of_unbounded_finrank V π hπ hdim,
    infinite_nonzero_tail_of_unbounded_finrank V π hπ hdim⟩

omit hπ

/-- Completion-independent Riesz obstruction used in Section 6 of the card: no Hausdorff
topological real vector space can be both infinite-dimensional and locally compact. -/
theorem infiniteDimensional_not_locallyCompact
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hinfinite : ¬ FiniteDimensional ℝ E) : ¬ LocallyCompactSpace E := by
  intro hlocal
  letI : LocallyCompactSpace E := hlocal
  exact hinfinite (FiniteDimensional.of_locallyCompactSpace ℝ)

end KolchinSpencer

end HTGeometry.NomologicalHomotopyGeometry
