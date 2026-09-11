import GaloisForLFunctions.HTGeometry.DifferentialVariationalBlockRecursion

/-!
# Splitting the orbit into a complement component and an accumulated block

The block estimate compares the orbit of a vector with the orbit of its component in a complement of
the invariant subspace `W`.  This leaf supplies the two structural ingredients.

* **Base independence.**  `variationalAttractingCore_base_independent` and its relative companion say
  that the growth filtration does not see the choice of base lattice.  Two lattices sit inside
  uniformizer dilations of each other, and a *constant* shift is invisible to a rate: reading the
  hypothesis at rate `1/(2c)` leaves exactly enough room, since `⌊n/2c⌋ + ⌊n/2c⌋ ≤ ⌊n/c⌋` and the
  constant is eventually below `⌊n/2c⌋`.  This is what lets the estimate be run in a lattice adapted
  to the splitting while the hypotheses are stated for the given lattice.

* **The decomposition itself.**  `exists_variationalBlockDecomposition` produces, for a vector `x` of
  the complement `U`, sequences `uₙ ∈ U` and `aₙ ∈ W` with `σ(uⱼ) = aⱼ + u_{j+1}` and
  `σⁿ(x) = uₙ + Σ_{j<n} σ^{n-1-j}(aⱼ)`.  Nothing but `W ⊔ U = ⊤` is needed: the splitting at each
  step is a choice, and the closed form follows from the recursion by the reindexing of
  `variationalBlockSum_succ`.

Two small utilities support both: every finite family of vectors is confined by a single uniformizer
dilation of any lattice, and a dilation transports along an inclusion of lattices with an additive
shift.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Additivity of the vector-level variational action. -/
theorem DifferentialFieldAut.vecBuildingAction_add (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (v w : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    σ.vecBuildingAction b (v + w) = σ.vecBuildingAction b v + σ.vecBuildingAction b w :=
  map_add (σ.vecBuildingActionMap b) v w

/-- Every vector lies in some uniformizer dilation of every lattice. -/
theorem DiffOp.exists_nat_mem_leftScale {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    ∃ k : ℕ, v ∈ (DiffOp.leftScaleCompletedPseudoDiffOpLattice
      (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(k : ℤ))) L).carrier := by
  obtain ⟨k, hk⟩ := DiffOp.exists_uniformizer_smul_mem_lattice L v
  refine ⟨k, ?_⟩
  have h := DiffOp.smul_mem_leftScale
    (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(k : ℤ))) L hk
  rwa [smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
    one_smul] at h

/-- A finite family of vectors is confined by a single uniformizer dilation. -/
theorem DiffOp.exists_nat_finset_mem_leftScale {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (F : Finset (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    ∃ k : ℕ, ∀ v ∈ F, v ∈ (DiffOp.leftScaleCompletedPseudoDiffOpLattice
      (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(k : ℤ))) L).carrier := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert v F _ ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨k', hk'⟩ := DiffOp.exists_nat_mem_leftScale L v
      refine ⟨max k k', fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with rfl | hwF
      · exact DiffOp.leftScale_uniformizer_zpow_carrier_antitone L
          (show (-((max k k' : ℕ) : ℤ)) ≤ (-(k' : ℤ)) by
            have hle : k' ≤ max k k' := le_max_right _ _
            omega) hk'
      · exact DiffOp.leftScale_uniformizer_zpow_carrier_antitone L
          (show (-((max k k' : ℕ) : ℤ)) ≤ (-(k : ℤ)) by
            have hle : k ≤ max k k' := le_max_left _ _
            omega) (hk w hwF)

/-- Transport of a uniformizer dilation along an inclusion of lattices. -/
theorem DiffOp.leftScale_uniformizer_le_of_carrier_le {r : ℕ}
    (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (k : ℕ)
    (hk : L.carrier ≤ (DiffOp.leftScaleCompletedPseudoDiffOpLattice
      (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(k : ℤ))) M).carrier) (a : ℕ) :
    (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(a : ℤ))) L).carrier ≤
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
          (-((a + k : ℕ) : ℤ))) M).carrier := by
  have hmono := DiffOp.leftScaleCompletedPseudoDiffOpLattice_carrier_mono
    (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(a : ℤ))) hk
  refine le_trans hmono ?_
  have hexp : (-(a : ℤ)) + (-(k : ℤ)) = -((a + k : ℕ) : ℤ) := by push_cast; ring
  rw [DiffOp.leftScaleCompletedPseudoDiffOpLattice_mul, ← zpow_add, hexp]

/-- Halving the rate index leaves room for a fixed additive shift. -/
theorem nat_div_two_mul_add_le {c k n : ℕ} (hn : 2 * (c + 1) * k ≤ n) :
    n / (2 * (c + 1)) + k ≤ n / (c + 1) := by
  have hpos : 0 < 2 * (c + 1) := by omega
  have hk : k ≤ n / (2 * (c + 1)) := by
    rw [Nat.le_div_iff_mul_le hpos]
    have hcomm : 2 * (c + 1) * k = k * (2 * (c + 1)) := by ring
    omega
  have hdouble : n / (2 * (c + 1)) + n / (2 * (c + 1)) ≤ (n + n) / (2 * (c + 1)) :=
    Nat.add_div_le_add_div n n _
  have heq : (n + n) / (2 * (c + 1)) = n / (c + 1) := by
    have h2 : n + n = 2 * n := by omega
    rw [h2, Nat.mul_div_mul_left n (c + 1) (by omega : 0 < 2)]
  omega

/-- **Base independence of the attracting core.** -/
theorem variationalAttractingCore_subset_of_lattice (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingCore σ b L ⊆ variationalAttractingCore σ b M := by
  intro x hx
  obtain ⟨k, hk⟩ := DiffOp.exists_nat_carrier_le_leftScale_uniformizer M L
  rw [variationalAttractingCore, Set.mem_iInter] at hx
  rw [variationalAttractingCore, Set.mem_iInter]
  intro c
  have hL := hx (2 * c + 1)
  have hd : 2 * c + 1 + 1 = 2 * (c + 1) := by omega
  rw [variationalSlowSet, Set.mem_setOf_eq, Filter.eventually_atTop] at hL
  obtain ⟨N, hN⟩ := hL
  refine Filter.eventually_atTop.2 ⟨max N (2 * (c + 1) * k), fun n hn => ?_⟩
  have hn1 : N ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 * (c + 1) * k ≤ n := le_trans (le_max_right _ _) hn
  have h1 := hN n hn1
  rw [hd] at h1
  have h2 := DiffOp.leftScale_uniformizer_le_of_carrier_le L M k hk (n / (2 * (c + 1))) h1
  refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone M ?_ h2
  have := nat_div_two_mul_add_le (c := c) (k := k) (n := n) hn2
  omega

theorem variationalAttractingCore_base_independent (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingCore σ b L = variationalAttractingCore σ b M :=
  Set.Subset.antisymm (variationalAttractingCore_subset_of_lattice σ b L M)
    (variationalAttractingCore_subset_of_lattice σ b M L)

/-- **Base independence of the relative attracting core.** -/
theorem variationalRelativeAttractingCore_subset_of_lattice (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    variationalRelativeAttractingCore σ b L W ⊆ variationalRelativeAttractingCore σ b M W := by
  intro x hx
  obtain ⟨k, hk⟩ := DiffOp.exists_nat_carrier_le_leftScale_uniformizer M L
  rw [variationalRelativeAttractingCore, Set.mem_iInter] at hx
  rw [variationalRelativeAttractingCore, Set.mem_iInter]
  intro c
  have hL := hx (2 * c + 1)
  have hd : 2 * c + 1 + 1 = 2 * (c + 1) := by omega
  rw [variationalRelativeSlowSet, Set.mem_setOf_eq, Filter.eventually_atTop] at hL
  obtain ⟨N, hN⟩ := hL
  refine Filter.eventually_atTop.2 ⟨max N (2 * (c + 1) * k), fun n hn => ?_⟩
  have hn1 : N ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 * (c + 1) * k ≤ n := le_trans (le_max_right _ _) hn
  have h1 := hN n hn1
  rw [hd] at h1
  have h2 : variationalRelativeTarget L W (n / (2 * (c + 1))) ≤
      variationalRelativeTarget M W (n / (2 * (c + 1)) + k) :=
    sup_le_sup_right (DiffOp.leftScale_uniformizer_le_of_carrier_le L M k hk _) _
  refine variationalRelativeTarget_mono M W ?_ (h2 h1)
  have := nat_div_two_mul_add_le (c := c) (k := k) (n := n) hn2
  omega

theorem variationalRelativeAttractingCore_base_independent (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    variationalRelativeAttractingCore σ b L W = variationalRelativeAttractingCore σ b M W :=
  Set.Subset.antisymm (variationalRelativeAttractingCore_subset_of_lattice σ b L M W)
    (variationalRelativeAttractingCore_subset_of_lattice σ b M L W)

/-- **The orbit splits into a `U`-component and an accumulated `W`-block.** -/
theorem exists_variationalBlockDecomposition (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (W U : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hWU : W ⊔ U = ⊤)
    {x : Fin r → DiffOp.CompletedPseudoDiffOp K} (hx : x ∈ U) :
    ∃ u a : ℕ → Fin r → DiffOp.CompletedPseudoDiffOp K,
      u 0 = x ∧ (∀ j, u j ∈ U) ∧ (∀ j, a j ∈ W) ∧
      (∀ j, σ.vecBuildingAction b (u j) = a j + u (j + 1)) ∧
      (∀ n, (σ ^ n).vecBuildingAction b x = u n + variationalBlockSum σ b a n) := by
  classical
  have hstep : ∀ y : Fin r → DiffOp.CompletedPseudoDiffOp K,
      ∃ p : (Fin r → DiffOp.CompletedPseudoDiffOp K) ×
        (Fin r → DiffOp.CompletedPseudoDiffOp K),
        p.1 ∈ W ∧ p.2 ∈ U ∧ σ.vecBuildingAction b y = p.1 + p.2 := by
    intro y
    have hmem : σ.vecBuildingAction b y ∈ (⊤ : Submodule (DiffOp.CompletedPseudoDiffOp K)
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) := Submodule.mem_top
    rw [← hWU] at hmem
    obtain ⟨w, hw, v, hv, hsum⟩ := Submodule.mem_sup.1 hmem
    exact ⟨(w, v), hw, hv, hsum.symm⟩
  choose f hfW hfU hfsum using hstep
  refine ⟨fun n => Nat.rec x (fun _ y => (f y).2) n,
    fun n => (f (Nat.rec x (fun _ y => (f y).2) n)).1, rfl, ?_, fun n => hfW _, fun n => hfsum _,
    ?_⟩
  · intro j
    induction j with
    | zero => exact hx
    | succ n _ => exact hfU _
  · intro n
    induction n with
    | zero =>
        show (σ ^ 0).vecBuildingAction b x = x + variationalBlockSum σ b _ 0
        rw [pow_zero, DifferentialFieldAut.vecBuildingAction_one, variationalBlockSum]
        simp
    | succ n ih =>
        rw [← σ.vecBuildingAction_succ_left n b x, ih, σ.vecBuildingAction_add,
          hfsum _, variationalBlockSum_succ]
        abel

end

end GaloisForLFunctions.HTGeometry
