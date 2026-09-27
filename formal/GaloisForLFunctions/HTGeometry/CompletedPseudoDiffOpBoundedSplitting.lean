import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpContractingLattice

/-!
# Forward-bounded and backward-bounded vectors span the space

For a uniformizer-semilinear automorphism `T` of a finite-dimensional completed skew vector space,
every vector is the sum of a vector with bounded forward orbit and a vector with bounded backward
orbit (`DiffOp.forwardBoundedSubspace_sup_inv_eq_top`).

* `DiffOp.orbitConfined` — the vectors whose whole forward orbit stays in `M`; a `T`-stable
  integral submodule of `M`.  `DiffOp.exists_stable_lattice_forwardBoundedSubspace` uses it to give
  the forward-bounded subspace `B` a lattice `N` with `T N ⊆ N`.
* `DiffOp.mem_forwardBoundedSubspace_of_forall_mem_sup` — **boundedness modulo `B` is boundedness**:
  a projection onto `B` splits the orbit as `Tⁿx = u_n + β_n` with `u_n` in a fixed finitely
  generated submodule and `β_{n+1} = T β_n + (bounded)`, which stays in one dilation of `N`.
* `DiffOp.quotientSemilinearAut` — the automorphism induced on `E ⧸ W` by a stable subspace, again
  uniformizer-semilinear.  On `E ⧸ B` it has no nonzero forward-bounded vector, so the contracting
  lattice theorem applies there and lifts to a lattice `P` of `E` with `ϖ^{-1} P ⊆ T^m P + B`.
* `DiffOp.exists_sub_mem_forwardBoundedSubspace_inv_of_contracting_mod` — the **second splitting
  lemma**: each vector of `P` is corrected by an element of `B` (the series `Σ T^{m(j+1)} γ_j` of the
  scaled defects `γ_j ∈ ϖ^j N`) into a vector with bounded backward orbit.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]

variable {T : E ≃ₗ[ℤ] E} (hT : IsUniformizerSemilinear (K := K) T)

/-- The vectors whose whole forward orbit stays in `M`. -/
def orbitConfined (M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    Submodule (CompletedPseudoDiffOpInteger (K := K)) E where
  carrier := {y | ∀ n : ℕ, (T ^ n) y ∈ M}
  add_mem' hx hy n := by rw [_root_.map_add]; exact M.add_mem (hx n) (hy n)
  zero_mem' n := by rw [_root_.map_zero]; exact M.zero_mem
  smul_mem' a y hy n := by
    obtain ⟨b, hb, hby⟩ := IsUniformizerSemilinear.map_integer_smul (hT.pow n) a.2 y
    rw [integer_smul_eq, hby]
    exact M.smul_mem ⟨b, hb⟩ (hy n)

variable {M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}

theorem orbitConfined_le : orbitConfined hT M ≤ M := fun y hy => by
  have := hy 0
  rwa [pow_zero, LinearEquiv.coe_one, id] at this

theorem apply_mem_orbitConfined {y : E} (hy : y ∈ orbitConfined hT M) :
    T y ∈ orbitConfined hT M := fun n => by
  rw [← LinearEquiv.mul_apply, ← pow_succ]
  exact hy (n + 1)

theorem orbitConfined_le_forwardBoundedSubspace (hM : M.FG) :
    ((orbitConfined hT M : Submodule _ E) : Set E) ⊆ forwardBoundedSubspace T hT :=
  fun _ hy => mem_forwardBoundedSubspace.2 ⟨M, hM, hy⟩

variable [FiniteDimensional (CompletedPseudoDiffOp K) E]

/-- The forward-bounded subspace carries a lattice stable under `T`. -/
theorem exists_stable_lattice_forwardBoundedSubspace :
    ∃ N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, N.FG ∧
      Submodule.span (CompletedPseudoDiffOp K) (N : Set E) = forwardBoundedSubspace T hT ∧
      semilinearImage T hT N ≤ N := by
  classical
  obtain ⟨d, e, c, he, hsum, hδ⟩ := exists_coordinates (forwardBoundedSubspace T hT)
  choose Mi hMi hMie using fun i => mem_forwardBoundedSubspace.1 (he i)
  let MB := ⨆ i, Mi i
  have hMBfg : MB.FG := Submodule.fg_iSup _ hMi
  have hΛ : Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e) ≤
      orbitConfined hT MB := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ n
    exact Submodule.mem_iSup_of_mem i (hMie i n)
  refine ⟨orbitConfined hT MB, hMBfg.of_le (orbitConfined_le hT), le_antisymm ?_ ?_, ?_⟩
  · rw [Submodule.span_le]
    exact orbitConfined_le_forwardBoundedSubspace hT hMBfg
  · rw [← span_span_range_eq he hsum]
    exact Submodule.span_mono hΛ
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_semilinearImage_iff_exists.1 hy
    exact apply_mem_orbitConfined hT hx

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- Boundedness modulo a stable subspace with a stable lattice is boundedness, given a projection
onto that subspace. -/
theorem exists_fg_orbit_of_forall_mem_sup_of_projection {B : Submodule (CompletedPseudoDiffOp K) E}
    (hTB : ∀ y ∈ B, T y ∈ B) {N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (hNfg : N.FG) (hNB : Submodule.span (CompletedPseudoDiffOp K) (N : Set E) = B)
    (hTN : semilinearImage T hT N ≤ N) (hM : M.FG)
    {pO qO : E →ₗ[CompletedPseudoDiffOpInteger (K := K)] E}
    (hpB : ∀ y, pO y ∈ B) (hpfix : ∀ y ∈ B, pO y = y) (hq : ∀ y, qO y = y - pO y) {x : E}
    (hx : ∀ n : ℕ, (T ^ n) x ∈ M ⊔ B.restrictScalars (CompletedPseudoDiffOpInteger (K := K))) :
    ∃ M' : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, M'.FG ∧ ∀ n : ℕ, (T ^ n) x ∈ M' := by
  classical
  have hqB : ∀ y ∈ B, qO y = 0 := fun y hy => by rw [hq, hpfix y hy, sub_self]
  -- the complement component stays in a fixed finitely generated submodule
  have hMqfg : (M.map qO).FG := hM.map _
  have hu : ∀ n, qO ((T ^ n) x) ∈ M.map qO := by
    intro n
    obtain ⟨m, hm, b, hb, hmb⟩ := Submodule.mem_sup.1 (hx n)
    rw [← hmb, _root_.map_add, hqB b hb, add_zero]
    exact Submodule.mem_map_of_mem hm
  -- the bounded component satisfies an inhomogeneous recursion with bounded forcing
  have hDfg : ((semilinearImage T hT (M.map qO)).map pO ⊔
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) {pO x}).FG :=
    ((semilinearImage_fg hMqfg).map _).sup (Submodule.fg_span_singleton _)
  have hDB : ∀ y ∈ (semilinearImage T hT (M.map qO)).map pO ⊔
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) {pO x}, y ∈ B := by
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    refine B.add_mem ?_ ?_
    · obtain ⟨z, _, rfl⟩ := Submodule.mem_map.1 hy₁
      exact hpB z
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy₂
      rw [integer_smul_eq]
      exact B.smul_mem _ (hpB x)
  obtain ⟨c, hc⟩ := exists_nat_le_uniformizerDilate_of_fg (M := N) hDfg (by
    rw [hNB]
    exact hDB)
  have hβ : ∀ n, pO ((T ^ n) x) ∈ uniformizerDilate (-(c : ℤ)) N := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, LinearEquiv.coe_one, id]
        exact hc (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    | succ n ih =>
        have hsplit : (T ^ (n + 1)) x = T (qO ((T ^ n) x)) + T (pO ((T ^ n) x)) := by
          rw [← _root_.map_add, hq, sub_add_cancel, pow_succ', LinearEquiv.mul_apply]
        have hTpB : T (pO ((T ^ n) x)) ∈ B := hTB _ (hpB _)
        rw [hsplit, _root_.map_add, hpfix _ hTpB]
        refine Submodule.add_mem _ (hc (Submodule.mem_sup_left ?_)) ?_
        · exact Submodule.mem_map_of_mem (apply_mem_semilinearImage (hu n))
        · have := apply_mem_semilinearImage (hT := hT) ih
          rw [semilinearImage_uniformizerDilate] at this
          exact uniformizerDilate_mono hTN this
  refine ⟨M.map qO ⊔ uniformizerDilate (-(c : ℤ)) N, hMqfg.sup (uniformizerDilate_fg _ hNfg),
    fun n => ?_⟩
  have : (T ^ n) x = qO ((T ^ n) x) + pO ((T ^ n) x) := by rw [hq, sub_add_cancel]
  rw [this]
  exact Submodule.add_mem_sup (hu n) (hβ n)

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- Every subspace has a valuation-linear projection onto it. -/
theorem exists_integer_projection (B : Submodule (CompletedPseudoDiffOp K) E) :
    ∃ pO qO : E →ₗ[CompletedPseudoDiffOpInteger (K := K)] E, (∀ y, pO y ∈ B) ∧
      (∀ y ∈ B, pO y = y) ∧ ∀ y, qO y = y - pO y := by
  obtain ⟨U, hU⟩ := B.exists_isCompl
  refine ⟨(B.projection U hU).restrictScalars (CompletedPseudoDiffOpInteger (K := K)),
    (LinearMap.id - B.projection U hU).restrictScalars (CompletedPseudoDiffOpInteger (K := K)),
    fun y => Submodule.projection_apply_mem hU y,
    fun y hy => Submodule.projection_apply_of_mem_left hU hy, fun y => rfl⟩

/-- **Boundedness modulo the bounded part is boundedness.** -/
theorem mem_forwardBoundedSubspace_of_forall_mem_sup (hM : M.FG) {x : E}
    (hx : ∀ n : ℕ, (T ^ n) x ∈ M ⊔ (forwardBoundedSubspace T hT).restrictScalars
      (CompletedPseudoDiffOpInteger (K := K))) :
    x ∈ forwardBoundedSubspace T hT := by
  obtain ⟨N, hNfg, hNB, hTN⟩ := exists_stable_lattice_forwardBoundedSubspace hT
  obtain ⟨pO, qO, hpB, hpfix, hq⟩ := exists_integer_projection (forwardBoundedSubspace T hT)
  exact mem_forwardBoundedSubspace.2 (exists_fg_orbit_of_forall_mem_sup_of_projection hT
    (fun y hy => apply_mem_forwardBoundedSubspace hy) hNfg hNB hTN hM hpB hpfix hq hx)

theorem pow_apply_mem_of_forall {W : Set E} {S : E ≃ₗ[ℤ] E} (h : ∀ x ∈ W, S x ∈ W) (n : ℕ) :
    ∀ x ∈ W, (S ^ n) x ∈ W := by
  induction n with
  | zero => intro x hx; rwa [pow_zero]
  | succ n ih =>
      intro x hx
      rw [pow_succ', LinearEquiv.mul_apply]
      exact h _ (ih x hx)

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- The partial forward hull `Q + SQ + ⋯ + SⁿQ` contains every `S^r Q` with `r ≤ n`. -/
theorem pow_apply_mem_forwardHull {S : E ≃ₗ[ℤ] E} (hS : IsUniformizerSemilinear (K := K) S)
    {Q : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} :
    ∀ n r : ℕ, r ≤ n → ∀ x ∈ Q, (S ^ r) x ∈ forwardHull hS Q n := by
  intro n
  induction n with
  | zero =>
      intro r hr x hx
      rw [Nat.le_zero.1 hr, pow_zero, LinearEquiv.coe_one, id]
      exact hx
  | succ n ih =>
      intro r hr x hx
      rcases Nat.eq_zero_or_pos r with rfl | hpos
      · rw [pow_zero, LinearEquiv.coe_one, id]
        exact le_forwardHull hS (n + 1) hx
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        rw [pow_succ', LinearEquiv.mul_apply]
        exact semilinearImage_forwardHull_le hS n
          (apply_mem_semilinearImage (ih r' (by omega) x hx))

/-- Vectors whose backward orbit tends to zero. -/
def IsBackwardContracting (T : E ≃ₗ[ℤ] E) (x : E) : Prop :=
  ∃ M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, M.FG ∧
    ∀ k : ℕ, ∀ᶠ n in atTop, (T⁻¹ ^ n) x ∈ uniformizerDilate (k : ℤ) M

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
include hT in
theorem IsBackwardContracting.smul {x : E} (hx : IsBackwardContracting (K := K) T x)
    (a : CompletedPseudoDiffOp K) : IsBackwardContracting (K := K) T (a • x) := by
  obtain ⟨M, hM, hMx⟩ := hx
  obtain ⟨t, ht⟩ := exists_uniformizer_left_scale_mem_integer a
  refine ⟨uniformizerDilate (-t) M, uniformizerDilate_fg _ hM, fun k => ?_⟩
  filter_upwards [hMx k] with n hn
  obtain ⟨ρ, hρ, hTρ⟩ := hT.inv.pow n
  rw [hTρ, uniformizerDilate_uniformizerDilate]
  have hint : uniformizerZPow (K := K) t * ρ a ∈ CompletedPseudoDiffOpInteger (K := K) := by
    have := hρ.map_integer ht
    rwa [map_mul, hρ.map_uniformizerZPow] at this
  have h1 : (uniformizerZPow (K := K) t * ρ a) • (T⁻¹ ^ n) x ∈ uniformizerDilate (k : ℤ) M := by
    have := Submodule.smul_mem _ (⟨_, hint⟩ : CompletedPseudoDiffOpInteger (K := K)) hn
    rwa [integer_smul_eq] at this
  have h2 := smul_mem_uniformizerDilate (-t) h1
  rw [uniformizerDilate_uniformizerDilate, smul_smul, ← mul_assoc, uniformizerZPow_neg_mul,
    one_mul] at h2
  rwa [add_comm] at h2

/-- The backward-contracting vectors form a subspace. -/
def backwardContractingSubspace (T : E ≃ₗ[ℤ] E) (hT : IsUniformizerSemilinear (K := K) T) :
    Submodule (CompletedPseudoDiffOp K) E where
  carrier := {x | IsBackwardContracting (K := K) T x}
  add_mem' {x y} hx hy := by
    obtain ⟨M, hM, hMx⟩ := hx
    obtain ⟨M', hM', hMy⟩ := hy
    refine ⟨M ⊔ M', hM.sup hM', fun k => ?_⟩
    filter_upwards [hMx k, hMy k] with n hn hn'
    rw [_root_.map_add, uniformizerDilate_sup]
    exact Submodule.add_mem_sup hn hn'
  zero_mem' := ⟨⊥, Submodule.fg_bot, fun k => Filter.Eventually.of_forall fun n => by
    rw [_root_.map_zero]
    exact Submodule.zero_mem _⟩
  smul_mem' a x hx := hx.smul hT a

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
variable {hT} in
theorem mem_backwardContractingSubspace {x : E} :
    x ∈ backwardContractingSubspace T hT ↔ IsBackwardContracting (K := K) T x := Iff.rfl

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- A backward-contracting vector has bounded backward orbit. -/
theorem mem_forwardBoundedSubspace_inv_of_mem_backwardContractingSubspace {x : E}
    (hx : x ∈ backwardContractingSubspace T hT) : x ∈ forwardBoundedSubspace T⁻¹ hT.inv := by
  classical
  obtain ⟨M, hM, hMx⟩ := mem_backwardContractingSubspace.1 hx
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hMx 0)
  refine mem_forwardBoundedSubspace.2 ⟨M ⊔ Submodule.span (CompletedPseudoDiffOpInteger (K := K))
    ((Finset.range N₀).image fun n => (T⁻¹ ^ n) x : Set E),
    hM.sup ⟨_, rfl⟩, fun n => ?_⟩
  by_cases hn : N₀ ≤ n
  · have := hN₀ n hn
    rw [Nat.cast_zero, uniformizerDilate_zero] at this
    exact Submodule.mem_sup_left this
  · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨n, by omega, rfl⟩

/-- **Second splitting lemma.**  Let `B` be a subspace stable under `T⁻¹` carrying a lattice `N` with
`T N ⊆ N`, and let `P` be a finitely generated integral submodule on which `T^{-m}` contracts modulo
`B`.  Then every vector of `P` differs from a backward-contracting vector by an element of `B`. -/
theorem exists_sub_mem_backwardContractingSubspace_of_contracting_mod
    {B : Submodule (CompletedPseudoDiffOp K) E} (hB' : ∀ x ∈ B, T⁻¹ x ∈ B)
    {N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} (hN : N.FG)
    (hNB : Submodule.span (CompletedPseudoDiffOp K) (N : Set E) = B)
    (hTN : semilinearImage T hT N ≤ N)
    {P : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} (hP : P.FG) {m : ℕ} (hm : 1 ≤ m)
    (hcontr : semilinearImage (T⁻¹ ^ m) (hT.inv.pow m) P ≤
      uniformizerDilate 1 P ⊔ B.restrictScalars (CompletedPseudoDiffOpInteger (K := K)))
    {u : E} (hu : u ∈ P) :
    ∃ b ∈ B, u - b ∈ backwardContractingSubspace T hT := by
  classical
  subst hNB
  -- `T` does not enlarge dilations of `N`
  have hTpowN : ∀ (k : ℕ) (j : ℤ), semilinearImage (T ^ k) (hT.pow k) (uniformizerDilate j N) ≤
      uniformizerDilate j N := by
    intro k j
    rw [semilinearImage_uniformizerDilate]
    refine uniformizerDilate_mono ?_
    induction k with
    | zero => exact (semilinearImage_pow_zero (hT.pow 0)).le
    | succ k ih =>
        rw [semilinearImage_pow_succ hT k _ (hT.pow k)]
        exact (semilinearImage_mono ih).trans hTN
  -- continuity of `T^{-m}` on dilations of `N`
  obtain ⟨c, hc⟩ := exists_semilinearImage_le_shift (hT.inv.pow m) hN
    (pow_apply_mem_of_forall (W := (Submodule.span (CompletedPseudoDiffOp K) (N : Set E) :
      Set E)) hB' m)
  -- the defects live in a finitely generated submodule of `B`
  set R := (semilinearImage (T⁻¹ ^ m) (hT.inv.pow m) P ⊔ uniformizerDilate 1 P) ⊓
    (Submodule.span (CompletedPseudoDiffOp K) (N : Set E)).restrictScalars
      (CompletedPseudoDiffOpInteger (K := K)) with hRdef
  have hRfg : R.FG := ((semilinearImage_fg hP).sup (uniformizerDilate_fg 1 hP)).of_le inf_le_left
  obtain ⟨a, ha⟩ := exists_nat_le_uniformizerDilate_of_fg (M := N) hRfg (fun x hx => hx.2)
  have hstep : ∀ x ∈ P, ∃ x' ∈ P,
      (T⁻¹ ^ m) x - uniformizerZPow (K := K) 1 • x' ∈ R := by
    intro x hx
    have hSx := hcontr (apply_mem_semilinearImage (hT := hT.inv.pow m) hx)
    obtain ⟨z, hz, β, hβ, hzβ⟩ := Submodule.mem_sup.1 hSx
    obtain ⟨x', hx', rfl⟩ := mem_uniformizerDilate_iff_exists.1 hz
    refine ⟨x', hx', Submodule.sub_mem _ (Submodule.mem_sup_left (apply_mem_semilinearImage hx))
      (Submodule.mem_sup_right (smul_mem_uniformizerDilate 1 hx')), ?_⟩
    rw [← hzβ, add_sub_cancel_left]
    exact hβ
  choose! nxt hnxt hdef using hstep
  let xs : ℕ → E := fun j => nxt^[j] u
  have hxs : ∀ j, xs j ∈ P := by
    intro j
    induction j with
    | zero => exact hu
    | succ j ih =>
        change nxt^[j + 1] u ∈ P
        rw [Function.iterate_succ_apply']
        exact hnxt _ ih
  have hxs_succ : ∀ j, xs (j + 1) = nxt (xs j) := by
    intro j
    change nxt^[j + 1] u = nxt (nxt^[j] u)
    rw [Function.iterate_succ_apply']
  let βs : ℕ → E := fun j => (T⁻¹ ^ m) (xs j) - uniformizerZPow (K := K) 1 • xs (j + 1)
  have hβs : ∀ j, βs j ∈ R := by
    intro j
    change (T⁻¹ ^ m) (xs j) - uniformizerZPow (K := K) 1 • xs (j + 1) ∈ R
    rw [hxs_succ]
    exact hdef _ (hxs j)
  let γ : ℕ → E := fun j => uniformizerZPow (K := K) (j : ℤ) • βs j
  have hγ : ∀ j : ℕ, γ j ∈ uniformizerDilate ((j : ℤ) - a) N := by
    intro j
    have := smul_mem_uniformizerDilate (j : ℤ) (ha (hβs j))
    rwa [uniformizerDilate_uniformizerDilate, ← sub_eq_add_neg] at this
  -- the correction series and its shifted tails
  let z : ℕ → ℕ → E := fun n i => (T ^ (m * (i + 1))) (γ (n + i))
  have hz : ∀ n i : ℕ, z n i ∈ uniformizerDilate (((n + i : ℕ) : ℤ) - a) N := fun n i =>
    hTpowN _ _ (apply_mem_semilinearImage (hγ (n + i)))
  have hzn : ∀ n i : ℕ, z n i ∈ uniformizerDilate ((n : ℤ) - a) N := fun n i =>
    uniformizerDilate_antitone N (by push_cast; omega) (hz n i)
  let s : ℕ → ℕ → E := fun n K' => ∑ i ∈ Finset.range K', z n i
  have hsn : ∀ n K' : ℕ, s n K' ∈ uniformizerDilate ((n : ℤ) - a) N := fun n K' =>
    Submodule.sum_mem _ fun i _ => hzn n i
  have hlim : ∀ n, ∃ t, ∀ k : ℕ, ∀ᶠ K' in atTop, t - s n K' ∈ uniformizerDilate (k : ℤ) N := by
    intro n
    refine exists_limit_of_eventually_sub_mem_uniformizerDilate hN (s n) fun k => ?_
    refine eventually_atTop.2 ⟨k + a, fun K' hK' => ?_⟩
    have hdiff : s n (K' + 1) - s n K' = z n K' := by
      simp only [s, Finset.sum_range_succ, add_sub_cancel_left]
    rw [hdiff]
    exact uniformizerDilate_antitone N (by push_cast; omega) (hz n K')
  choose t ht using hlim
  have htmem : ∀ n : ℕ, t n ∈ uniformizerDilate ((n : ℤ) - a) N := by
    intro n
    obtain ⟨K', hK'⟩ := ((ht n (n + a)).and (eventually_ge_atTop 0)).exists
    have h1 : t n - s n K' ∈ uniformizerDilate ((n : ℤ) - a) N :=
      uniformizerDilate_antitone N (by push_cast; omega) hK'.1
    have := Submodule.add_mem _ h1 (hsn n K')
    rwa [sub_add_cancel] at this
  -- the tail recursion `T^{-m} t_n = γ_n + t_{n+1}`
  have hcancel : ∀ i : ℕ, ∀ y : E, (T⁻¹ ^ m) ((T ^ (m * (i + 1 + 1))) y) = (T ^ (m * (i + 1))) y := by
    intro i y
    rw [show m * (i + 1 + 1) = m + m * (i + 1) by ring, pow_add, inv_pow,
      ← LinearEquiv.mul_apply, inv_mul_cancel_left]
  have hcancel0 : ∀ y : E, (T⁻¹ ^ m) ((T ^ (m * (0 + 1))) y) = y := by
    intro y
    rw [show m * (0 + 1) = m by ring, inv_pow, ← LinearEquiv.mul_apply, inv_mul_cancel,
      LinearEquiv.coe_one, id]
  have hSs : ∀ n K', (T⁻¹ ^ m) (s n (K' + 1)) = γ n + s (n + 1) K' := by
    intro n K'
    simp only [s]
    rw [Finset.sum_range_succ', _root_.map_add, _root_.map_sum, add_comm]
    congr 1
    · simp only [z, add_zero]
      exact hcancel0 _
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [z]
      rw [hcancel, show n + (i + 1) = n + 1 + i by ring]
  have htail : ∀ n, (T⁻¹ ^ m) (t n) = γ n + t (n + 1) := by
    intro n
    refine eq_of_eventually_sub_mem_uniformizerDilate hN (s := fun K' => γ n + s (n + 1) K')
      (fun k => ?_) (fun k => ?_)
    · filter_upwards [(tendsto_add_atTop_nat 1).eventually (ht n (k + c))] with K' hK'
      rw [← hSs, ← _root_.map_sub]
      have := hc ((k + c : ℕ) : ℤ) (apply_mem_semilinearImage (hT := hT.inv.pow m) hK')
      convert this using 2
      push_cast
      ring
    · filter_upwards [ht (n + 1) k] with K' hK'
      rwa [add_sub_add_left_eq_sub]
  -- the corrected orbit under `T^{-m}`
  have horbit : ∀ q : ℕ, ((T⁻¹ ^ m) ^ q) (u - t 0) =
      uniformizerZPow (K := K) (q : ℤ) • xs q - t q := by
    intro q
    induction q with
    | zero =>
        rw [pow_zero, LinearEquiv.coe_one, id, Nat.cast_zero, uniformizerZPow_zero, one_smul]
        rfl
    | succ q ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, _root_.map_sub, htail,
          IsUniformizerSemilinear.map_uniformizerZPow_smul (hT.inv.pow m)]
        have hx : (T⁻¹ ^ m) (xs q) = uniformizerZPow (K := K) 1 • xs (q + 1) + βs q := by
          change _ = _ + ((T⁻¹ ^ m) (xs q) - uniformizerZPow (K := K) 1 • xs (q + 1))
          abel
        rw [hx, smul_add, smul_smul, ← uniformizerZPow_add]
        change _ - (uniformizerZPow (K := K) (q : ℤ) • βs q + t (q + 1)) = _
        rw [show ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 by push_cast; ring]
        abel
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : Submodule (CompletedPseudoDiffOpInteger (K := K)) E,
      Q₀ = P ⊔ N := ⟨_, rfl⟩
  have hPQ₀ : P ≤ Q₀ := hQ₀ ▸ le_sup_left
  have hNQ₀ : N ≤ Q₀ := hQ₀ ▸ le_sup_right
  have hQ₀fg : Q₀.FG := hQ₀ ▸ hP.sup hN
  have horbitQ : ∀ q : ℕ, ((T⁻¹ ^ m) ^ q) (u - t 0) ∈ uniformizerDilate ((q : ℤ) - a) Q₀ := by
    intro q
    rw [horbit]
    refine Submodule.sub_mem _ (uniformizerDilate_mono hPQ₀ ?_)
      (uniformizerDilate_mono hNQ₀ (htmem q))
    exact uniformizerDilate_antitone P (by omega) (smul_mem_uniformizerDilate (q : ℤ) (hxs q))
  have hcontract : ∀ k : ℕ, ∀ᶠ n in atTop, (T⁻¹ ^ n) (u - t 0) ∈
      uniformizerDilate (k : ℤ) (forwardHull hT.inv Q₀ (m - 1)) := by
    intro k
    refine eventually_atTop.2 ⟨m * (k + a), fun n hn => ?_⟩
    have hk : T⁻¹ ^ n = T⁻¹ ^ (n % m) * (T⁻¹ ^ m) ^ (n / m) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [hk, LinearEquiv.mul_apply]
    have hr : n % m ≤ m - 1 := by
      have := Nat.mod_lt n (show 0 < m by omega)
      omega
    have hq : k + a ≤ n / m := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      nlinarith
    obtain ⟨z, hz, hzeq⟩ := mem_uniformizerDilate_iff_exists.1 (horbitQ (n / m))
    rw [← hzeq, IsUniformizerSemilinear.map_uniformizerZPow_smul (hT.inv.pow (n % m))]
    refine uniformizerDilate_antitone _ ?_ (smul_mem_uniformizerDilate _
      (pow_apply_mem_forwardHull hT.inv (m - 1) (n % m) hr z hz))
    omega
  exact ⟨t 0, uniformizerDilate_subset_span _ (htmem 0), mem_backwardContractingSubspace.2
    ⟨_, forwardHull_fg hT.inv hQ₀fg (m - 1), hcontract⟩⟩

section Quotient

/-- The semilinear map carried by a uniformizer-semilinear automorphism. -/
def IsUniformizerSemilinear.semilinearMap {S : E ≃ₗ[ℤ] E}
    (hS : IsUniformizerSemilinear (K := K) S) :
    E →ₛₗ[((Classical.choose hS : CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K) :
      CompletedPseudoDiffOp K →+* CompletedPseudoDiffOp K)] E where
  toFun := S
  map_add' := _root_.map_add S
  map_smul' := (Classical.choose_spec hS).2

variable (W : Submodule (CompletedPseudoDiffOp K) E)

/-- The automorphism induced on `E ⧸ W` by an automorphism preserving `W` in both directions. -/
def quotientSemilinearAut (hW : ∀ x ∈ W, T x ∈ W) (hW' : ∀ x ∈ W, T⁻¹ x ∈ W) :
    (E ⧸ W) ≃ₗ[ℤ] (E ⧸ W) :=
  AddEquiv.toIntLinearEquiv
    { toFun := W.mapQ W hT.semilinearMap hW
      invFun := W.mapQ W hT.inv.semilinearMap hW'
      left_inv := fun y => by
        refine Submodule.Quotient.induction_on W y fun x => ?_
        rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
        congr 1
        exact T.symm_apply_apply x
      right_inv := fun y => by
        refine Submodule.Quotient.induction_on W y fun x => ?_
        rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
        congr 1
        exact T.apply_symm_apply x
      map_add' := _root_.map_add _ }

variable {W} (hW : ∀ x ∈ W, T x ∈ W) (hW' : ∀ x ∈ W, T⁻¹ x ∈ W)

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
theorem quotientSemilinearAut_mk (x : E) :
    quotientSemilinearAut hT W hW hW' (Submodule.Quotient.mk x) = Submodule.Quotient.mk (T x) :=
  Submodule.mapQ_apply W W hT.semilinearMap (h := hW) x

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
theorem quotientSemilinearAut_pow_mk (n : ℕ) (x : E) :
    (quotientSemilinearAut hT W hW hW' ^ n) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((T ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, quotientSemilinearAut_mk, pow_succ',
        LinearEquiv.mul_apply]

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
theorem isUniformizerSemilinear_quotientSemilinearAut :
    IsUniformizerSemilinear (K := K) (quotientSemilinearAut hT W hW hW') := by
  refine ⟨Classical.choose hT, (Classical.choose_spec hT).1, fun a y => ?_⟩
  refine Submodule.Quotient.induction_on W y fun x => ?_
  rw [← Submodule.Quotient.mk_smul, quotientSemilinearAut_mk, quotientSemilinearAut_mk,
    (Classical.choose_spec hT).2, Submodule.Quotient.mk_smul]

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- A finitely generated integral submodule of a quotient lifts to a finitely generated one. -/
theorem exists_fg_lift {M' : Submodule (CompletedPseudoDiffOpInteger (K := K)) (E ⧸ W)}
    (hM' : M'.FG) :
    ∃ M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, M.FG ∧ ∀ x : E,
      Submodule.Quotient.mk x ∈ M' ↔
        x ∈ M ⊔ W.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
  classical
  obtain ⟨S, rfl⟩ := hM'
  let f : E ⧸ W → E := fun y => (Submodule.Quotient.mk_surjective W y).choose
  have hf : ∀ y, Submodule.Quotient.mk (f y) = y := fun y =>
    (Submodule.Quotient.mk_surjective W y).choose_spec
  let q : E →ₗ[CompletedPseudoDiffOpInteger (K := K)] E ⧸ W :=
    W.mkQ.restrictScalars (CompletedPseudoDiffOpInteger (K := K))
  have hmap : (Submodule.span (CompletedPseudoDiffOpInteger (K := K))
      ((S.image f : Finset E) : Set E)).map q =
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (S : Set (E ⧸ W)) := by
    rw [Submodule.map_span, Finset.coe_image, ← Set.image_comp]
    congr 1
    ext y
    simp only [Set.mem_image, Function.comp_apply, Finset.mem_coe]
    constructor
    · rintro ⟨z, hz, rfl⟩
      change Submodule.Quotient.mk (f z) ∈ S
      rw [hf]
      exact hz
    · intro hy
      exact ⟨y, hy, hf y⟩
  refine ⟨_, ⟨S.image f, rfl⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [← hmap] at hx
    obtain ⟨m, hm, hmx⟩ := Submodule.mem_map.1 hx
    have hdiff : x - m ∈ W := by
      rw [← Submodule.Quotient.eq]
      exact hmx.symm
    have : x = m + (x - m) := by abel
    rw [this]
    exact Submodule.add_mem_sup hm hdiff
  · obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    rw [← hmap, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero W).2 hw, add_zero]
    exact Submodule.mem_map_of_mem hm

end Quotient

/-- The forward-bounded subspace is stable under `T⁻¹`. -/
theorem inv_apply_mem_forwardBoundedSubspace {x : E} (hx : x ∈ forwardBoundedSubspace T hT) :
    T⁻¹ x ∈ forwardBoundedSubspace T hT := by
  have hle : semilinearSubspaceImage T hT (forwardBoundedSubspace T hT) ≤
      forwardBoundedSubspace T hT := by
    intro y hy
    rw [mem_semilinearSubspaceImage] at hy
    have := apply_mem_forwardBoundedSubspace hy
    rwa [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at this
  have heq := semilinearSubspaceImage_eq_of_le hle
  rw [← heq] at hx
  exact hx

/-- **Forward-bounded and backward-contracting vectors span.**  Every vector is the sum of a vector
with bounded forward orbit and a vector whose backward orbit tends to zero. -/
theorem forwardBoundedSubspace_sup_backwardContractingSubspace_eq_top :
    forwardBoundedSubspace T hT ⊔ backwardContractingSubspace T hT = ⊤ := by
  classical
  have hB : ∀ x ∈ forwardBoundedSubspace T hT, T x ∈ forwardBoundedSubspace T hT :=
    fun x hx => apply_mem_forwardBoundedSubspace hx
  have hB' : ∀ x ∈ forwardBoundedSubspace T hT, T⁻¹ x ∈ forwardBoundedSubspace T hT :=
    fun x hx => inv_apply_mem_forwardBoundedSubspace hT hx
  have hTq := isUniformizerSemilinear_quotientSemilinearAut hT hB hB'
  -- no bounded vectors in the quotient
  have hbot : forwardBoundedSubspace (quotientSemilinearAut hT _ hB hB') hTq ⊓ ⊤ = ⊥ := by
    rw [inf_top_eq, eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨M', hM', hM'y⟩ := mem_forwardBoundedSubspace.1 hy
    obtain ⟨M, hM, hMiff⟩ := exists_fg_lift hM'
    have hx : x ∈ forwardBoundedSubspace T hT :=
      mem_forwardBoundedSubspace_of_forall_mem_sup hT hM fun n => (hMiff _).1 (by
        rw [← quotientSemilinearAut_pow_mk hT hB hB']
        exact hM'y n)
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hx
  obtain ⟨P', hP'fg, hP'span, m, hm, hcontr⟩ :=
    exists_contracting_lattice_of_inf_forwardBoundedSubspace_eq_bot hTq _ ⊤ rfl
      (fun _ _ => trivial) (fun _ _ => trivial) hbot
  have hstep := inv_pow_le_uniformizerDilate_one_of_contracting hTq hcontr
  obtain ⟨P, hPfg, hPiff⟩ := exists_fg_lift hP'fg
  -- the lifted lattice is contracted by `T^{-m}` modulo the bounded part
  have hcontrE : semilinearImage (T⁻¹ ^ m) (hT.inv.pow m) P ≤
      uniformizerDilate 1 P ⊔ (forwardBoundedSubspace T hT).restrictScalars
        (CompletedPseudoDiffOpInteger (K := K)) := by
    intro y hy
    rw [mem_semilinearImage, inv_pow, inv_inv] at hy
    have h1 : Submodule.Quotient.mk y ∈ semilinearImage
        ((quotientSemilinearAut hT _ hB hB')⁻¹ ^ m) (hTq.inv.pow m) P' := by
      rw [mem_semilinearImage, inv_pow, inv_inv, quotientSemilinearAut_pow_mk]
      exact (hPiff _).2 (Submodule.mem_sup_left hy)
    have h2 := hstep h1
    rw [mem_uniformizerDilate, ← Submodule.Quotient.mk_smul] at h2
    have h3 : y ∈ uniformizerDilate 1 (P ⊔ (forwardBoundedSubspace T hT).restrictScalars
        (CompletedPseudoDiffOpInteger (K := K))) := (hPiff _).1 h2
    rwa [uniformizerDilate_sup, uniformizerDilate_restrictScalars] at h3
  obtain ⟨N, hNfg, hNB, hTN⟩ := exists_stable_lattice_forwardBoundedSubspace hT
  have hPsub : ∀ u ∈ P, u ∈ forwardBoundedSubspace T hT ⊔ backwardContractingSubspace T hT := by
    intro u hu
    obtain ⟨b, hb, hub⟩ := exists_sub_mem_backwardContractingSubspace_of_contracting_mod hT hB'
      hNfg hNB hTN hPfg hm hcontrE hu
    have : u = b + (u - b) := by abel
    rw [this]
    exact Submodule.add_mem_sup hb hub
  rw [eq_top_iff]
  intro x _
  have hspan : Submodule.Quotient.mk x ∈ Submodule.span (CompletedPseudoDiffOp K)
      (P' : Set (E ⧸ forwardBoundedSubspace T hT)) := by
    rw [hP'span]
    trivial
  obtain ⟨t, ht⟩ := exists_nat_uniformizerZPow_smul_mem_of_mem_span hspan
  rw [← Submodule.Quotient.mk_smul] at ht
  obtain ⟨p, hp, b, hb, hpb⟩ := Submodule.mem_sup.1 ((hPiff _).1 ht)
  have hx' : uniformizerZPow (K := K) (t : ℤ) • x ∈
      forwardBoundedSubspace T hT ⊔ backwardContractingSubspace T hT := by
    rw [← hpb]
    exact Submodule.add_mem _ (hPsub p hp) (Submodule.mem_sup_left hb)
  have := Submodule.smul_mem _ (uniformizerZPow (K := K) (-(t : ℤ))) hx'
  rwa [smul_smul, uniformizerZPow_neg_mul, one_smul] at this

/-- **Forward-bounded and backward-bounded vectors span.** -/
theorem forwardBoundedSubspace_sup_inv_eq_top :
    forwardBoundedSubspace T hT ⊔ forwardBoundedSubspace T⁻¹ hT.inv = ⊤ := by
  rw [eq_top_iff, ← forwardBoundedSubspace_sup_backwardContractingSubspace_eq_top hT]
  exact sup_le_sup_left (fun x hx =>
    mem_forwardBoundedSubspace_inv_of_mem_backwardContractingSubspace hT hx) _

end

end DiffOp

end GaloisForLFunctions.HTGeometry
