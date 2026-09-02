import GaloisForLFunctions.HTGeometry.DifferentialVariationalLatticeCommensurability

/-!
# Interleaving distance for completed pseudodifferential valuation lattices

Uniformizer powers give a canonical integral gauge on the full lattice carrier.  Two lattices are
`n`-interleaved when multiplying either one on the left by `∂⁻¹` to the `n`th power puts it
inside the other.  Commensurability makes this relation nonempty for every pair.  Its least radius
is a genuine `ℕ`-valued metric on actual lattices.

This is exact relative-position infrastructure on the full lattice space.  It is deliberately not
identified with the Euclidean Cartan metric on the projective building: descending and comparing
the two metrics still requires the higher-rank noncommutative Cartan decomposition.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- A nonnegative uniformizer power sends every valuation lattice into itself. -/
theorem leftScale_uniformizer_zpow_carrier_le_self
    (L : CompletedPseudoDiffOpLattice K ι) {z : ℤ} (hz : 0 ≤ z) :
    (leftScaleCompletedPseudoDiffOpLattice
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L).carrier ≤ L.carrier := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ :=
    (mem_leftScaleCompletedPseudoDiffOpLattice_iff
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L y).1 hy
  let c : CompletedPseudoDiffOpInteger (K := K) :=
    ⟨((completedPseudoDiffOpUniformizerUnit (K := K) ^ z :
      (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K),
      (coe_unit_mem_completedPseudoDiffOpInteger_iff _).2 (by
        rw [completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
        exact hz)⟩
  exact L.carrier.smul_mem c hx

omit [Fintype ι] in
/-- Larger uniformizer exponents give smaller left-scaled lattices. -/
theorem leftScale_uniformizer_zpow_carrier_antitone
    (L : CompletedPseudoDiffOpLattice K ι) {a b : ℤ} (hab : a ≤ b) :
    (leftScaleCompletedPseudoDiffOpLattice
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ b) L).carrier ≤
    (leftScaleCompletedPseudoDiffOpLattice
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ a) L).carrier := by
  let d := b - a
  have hd : 0 ≤ d := sub_nonneg.mpr hab
  have hscale := leftScale_uniformizer_zpow_carrier_le_self
    (leftScaleCompletedPseudoDiffOpLattice
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ a) L) hd
  rw [leftScaleCompletedPseudoDiffOpLattice_mul] at hscale
  have hpow : completedPseudoDiffOpUniformizerUnit (K := K) ^ d *
      completedPseudoDiffOpUniformizerUnit (K := K) ^ a =
      completedPseudoDiffOpUniformizerUnit (K := K) ^ b := by
    simpa [d] using
      (zpow_add (completedPseudoDiffOpUniformizerUnit (K := K)) d a).symm
  rwa [hpow] at hscale

/-- Symmetric containment after the same nonnegative uniformizer shift. -/
def CompletedPseudoDiffOpLattice.InterleavedAt
    (n : ℕ) (L M : CompletedPseudoDiffOpLattice K ι) : Prop :=
  (leftScaleCompletedPseudoDiffOpLattice
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ)) L).carrier ≤ M.carrier ∧
  (leftScaleCompletedPseudoDiffOpLattice
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ)) M).carrier ≤ L.carrier

omit [Fintype ι] in
/-- Interleaving is symmetric. -/
theorem CompletedPseudoDiffOpLattice.InterleavedAt.symm
    {L M : CompletedPseudoDiffOpLattice K ι} {n : ℕ}
    (h : L.InterleavedAt n M) : M.InterleavedAt n L :=
  ⟨h.2, h.1⟩

omit [Fintype ι] in
/-- Interleaving persists after increasing the radius. -/
theorem CompletedPseudoDiffOpLattice.InterleavedAt.mono
    {L M : CompletedPseudoDiffOpLattice K ι} {m n : ℕ} (hmn : m ≤ n)
    (h : L.InterleavedAt m M) : L.InterleavedAt n M := by
  constructor
  · exact (leftScale_uniformizer_zpow_carrier_antitone L
      (Int.ofNat_le.mpr hmn)).trans h.1
  · exact (leftScale_uniformizer_zpow_carrier_antitone M
      (Int.ofNat_le.mpr hmn)).trans h.2

omit [Fintype ι] in
/-- Radius zero detects literal equality of lattices. -/
theorem completedPseudoDiffOpLattice_interleavedAt_zero_iff
    (L M : CompletedPseudoDiffOpLattice K ι) :
    L.InterleavedAt 0 M ↔ L = M := by
  simp only [CompletedPseudoDiffOpLattice.InterleavedAt, Int.ofNat_zero, zpow_zero,
    leftScaleCompletedPseudoDiffOpLattice_one]
  constructor
  · intro h
    apply CompletedPseudoDiffOpLattice.ext
    exact SetLike.coe_injective (le_antisymm h.1 h.2)
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

omit [Fintype ι] in
/-- Interleaving radii add under composition. -/
theorem CompletedPseudoDiffOpLattice.InterleavedAt.add
    {L M N : CompletedPseudoDiffOpLattice K ι} {m n : ℕ}
    (hLM : L.InterleavedAt m M) (hMN : M.InterleavedAt n N) :
    L.InterleavedAt (m + n) N := by
  have scale_add (P : CompletedPseudoDiffOpLattice K ι) :
      leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ ((m + n : ℕ) : ℤ)) P =
        leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ))
          (leftScaleCompletedPseudoDiffOpLattice
            (completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ)) P) := by
    rw [leftScaleCompletedPseudoDiffOpLattice_mul]
    congr 1
    simpa [add_comm] using
      (zpow_add (completedPseudoDiffOpUniformizerUnit (K := K)) (n : ℤ) (m : ℤ))
  have scale_add' (P : CompletedPseudoDiffOpLattice K ι) :
      leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ ((m + n : ℕ) : ℤ)) P =
        leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ))
          (leftScaleCompletedPseudoDiffOpLattice
            (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ)) P) := by
    rw [leftScaleCompletedPseudoDiffOpLattice_mul]
    congr 1
    simpa using
      (zpow_add (completedPseudoDiffOpUniformizerUnit (K := K)) (m : ℤ) (n : ℤ))
  constructor
  · rw [scale_add L]
    exact (leftScaleCompletedPseudoDiffOpLattice_carrier_mono _ hLM.1).trans hMN.1
  · rw [scale_add' N]
    exact (leftScaleCompletedPseudoDiffOpLattice_carrier_mono _ hMN.2).trans hLM.2

/-- Every pair of full finite valuation lattices has some integral interleaving radius. -/
theorem exists_completedPseudoDiffOpLattice_interleavedAt
    (L M : CompletedPseudoDiffOpLattice K ι) :
    ∃ n : ℕ, L.InterleavedAt n M := by
  obtain ⟨a, _, ha, _⟩ := completedPseudoDiffOpLattice_leftCommensurable L M
  obtain ⟨b, _, hb, _⟩ := completedPseudoDiffOpLattice_leftCommensurable M L
  let n := Int.toNat (max (max a b) 0)
  have han : a ≤ (n : ℤ) := by
    dsimp [n]
    omega
  have hbn : b ≤ (n : ℤ) := by
    dsimp [n]
    omega
  refine ⟨n, ?_, ?_⟩
  · exact (leftScale_uniformizer_zpow_carrier_antitone L han).trans ha
  · exact (leftScale_uniformizer_zpow_carrier_antitone M hbn).trans hb

/-- Every pair has a least interleaving radius. -/
theorem exists_least_completedPseudoDiffOpLattice_interleavedAt
    (L M : CompletedPseudoDiffOpLattice K ι) :
    ∃ n : ℕ, L.InterleavedAt n M ∧ ∀ m : ℕ, L.InterleavedAt m M → n ≤ m := by
  classical
  letI : DecidablePred (fun n : ℕ => L.InterleavedAt n M) := Classical.decPred _
  let hex : ∃ n : ℕ, L.InterleavedAt n M :=
    exists_completedPseudoDiffOpLattice_interleavedAt L M
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min' hex hm⟩

/-- Least symmetric uniformizer-interleaving radius between two actual lattices. -/
noncomputable def completedPseudoDiffOpLatticeInterleavingDistance
    (L M : CompletedPseudoDiffOpLattice K ι) : ℕ :=
  Classical.choose (exists_least_completedPseudoDiffOpLattice_interleavedAt L M)

/-- The least radius interleaves its two lattices. -/
theorem completedPseudoDiffOpLatticeInterleavingDistance_spec
    (L M : CompletedPseudoDiffOpLattice K ι) :
    L.InterleavedAt (completedPseudoDiffOpLatticeInterleavingDistance L M) M :=
  (Classical.choose_spec
    (exists_least_completedPseudoDiffOpLattice_interleavedAt L M)).1

/-- Characterization of all upper bounds for the least interleaving radius. -/
theorem completedPseudoDiffOpLatticeInterleavingDistance_le_iff
    (L M : CompletedPseudoDiffOpLattice K ι) (n : ℕ) :
    completedPseudoDiffOpLatticeInterleavingDistance L M ≤ n ↔ L.InterleavedAt n M := by
  constructor
  · intro h
    exact (completedPseudoDiffOpLatticeInterleavingDistance_spec L M).mono h
  · intro h
    exact (Classical.choose_spec
      (exists_least_completedPseudoDiffOpLattice_interleavedAt L M)).2 n h

/-- Interleaving distance vanishes on the diagonal. -/
@[simp] theorem completedPseudoDiffOpLatticeInterleavingDistance_self
    (L : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeInterleavingDistance L L = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [completedPseudoDiffOpLatticeInterleavingDistance_le_iff,
    completedPseudoDiffOpLattice_interleavedAt_zero_iff]

/-- Interleaving distance is symmetric. -/
theorem completedPseudoDiffOpLatticeInterleavingDistance_comm
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeInterleavingDistance L M =
      completedPseudoDiffOpLatticeInterleavingDistance M L := by
  apply le_antisymm
  · rw [completedPseudoDiffOpLatticeInterleavingDistance_le_iff]
    exact (completedPseudoDiffOpLatticeInterleavingDistance_spec M L).symm
  · rw [completedPseudoDiffOpLatticeInterleavingDistance_le_iff]
    exact (completedPseudoDiffOpLatticeInterleavingDistance_spec L M).symm

/-- Interleaving distance separates actual lattices. -/
@[simp] theorem completedPseudoDiffOpLatticeInterleavingDistance_eq_zero_iff
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeInterleavingDistance L M = 0 ↔ L = M := by
  constructor
  · intro h
    have hspec := completedPseudoDiffOpLatticeInterleavingDistance_spec L M
    rw [h, completedPseudoDiffOpLattice_interleavedAt_zero_iff] at hspec
    exact hspec
  · rintro rfl
    exact completedPseudoDiffOpLatticeInterleavingDistance_self L

/-- Triangle inequality for the exact integral interleaving metric. -/
theorem completedPseudoDiffOpLatticeInterleavingDistance_triangle
    (L M N : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeInterleavingDistance L N ≤
      completedPseudoDiffOpLatticeInterleavingDistance L M +
        completedPseudoDiffOpLatticeInterleavingDistance M N := by
  rw [completedPseudoDiffOpLatticeInterleavingDistance_le_iff]
  exact (completedPseudoDiffOpLatticeInterleavingDistance_spec L M).add
    (completedPseudoDiffOpLatticeInterleavingDistance_spec M N)

omit [Fintype ι] in
/-- An invertible completed-skew linear map reflects lattice inclusion. -/
theorem mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K ι) :
    (mapCompletedPseudoDiffOpLatticeLinear e L).carrier ≤
        (mapCompletedPseudoDiffOpLatticeLinear e M).carrier ↔
      L.carrier ≤ M.carrier := by
  constructor
  · intro h x hx
    have hex : e x ∈ (mapCompletedPseudoDiffOpLatticeLinear e L).carrier :=
      (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e L _).2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ :=
      (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e M _).1 (h hex)
    have hyx : y = x := e.injective heq
    rwa [hyx] at hy
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ :=
      (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e L y).1 hy
    exact (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e M _).2 ⟨x, h hx, rfl⟩

omit [Fintype ι] in
/-- Invertible completed-skew linear transport preserves every interleaving radius exactly. -/
theorem mapCompletedPseudoDiffOpLatticeLinear_interleavedAt_iff
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K ι) (n : ℕ) :
    (mapCompletedPseudoDiffOpLatticeLinear e L).InterleavedAt n
        (mapCompletedPseudoDiffOpLatticeLinear e M) ↔
      L.InterleavedAt n M := by
  unfold CompletedPseudoDiffOpLattice.InterleavedAt
  rw [← mapCompletedPseudoDiffOpLatticeLinear_leftScale,
    ← mapCompletedPseudoDiffOpLatticeLinear_leftScale,
    mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff,
    mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff]

/-- Invertible completed-skew linear transport is an isometry for interleaving distance. -/
theorem completedPseudoDiffOpLatticeInterleavingDistance_mapLinear
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeInterleavingDistance
        (mapCompletedPseudoDiffOpLatticeLinear e L)
        (mapCompletedPseudoDiffOpLatticeLinear e M) =
      completedPseudoDiffOpLatticeInterleavingDistance L M := by
  apply le_antisymm
  · rw [completedPseudoDiffOpLatticeInterleavingDistance_le_iff,
      mapCompletedPseudoDiffOpLatticeLinear_interleavedAt_iff]
    exact completedPseudoDiffOpLatticeInterleavingDistance_spec L M
  · rw [completedPseudoDiffOpLatticeInterleavingDistance_le_iff]
    exact (mapCompletedPseudoDiffOpLatticeLinear_interleavedAt_iff e L M _).1
      (completedPseudoDiffOpLatticeInterleavingDistance_spec
        (mapCompletedPseudoDiffOpLatticeLinear e L)
        (mapCompletedPseudoDiffOpLatticeLinear e M))

omit [Fintype ι] in
/-- Differential coefficient transport reflects lattice inclusion. -/
theorem mapCompletedPseudoDiffOpLattice_carrier_le_iff
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (L M : CompletedPseudoDiffOpLattice K ι) :
    (mapCompletedPseudoDiffOpLattice σ hσ L).carrier ≤
        (mapCompletedPseudoDiffOpLattice σ hσ M).carrier ↔
      L.carrier ≤ M.carrier := by
  have hinj : Function.Injective
      (mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ) := by
    intro x y hxy
    funext i
    apply (mapCompletedPseudoRingEquiv σ hσ).injective
    exact congrFun hxy i
  constructor
  · intro h x hx
    have hmap : mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ x ∈
        (mapCompletedPseudoDiffOpLattice σ hσ L).carrier :=
      (mem_mapCompletedPseudoDiffOpLattice_iff σ hσ L _).2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ :=
      (mem_mapCompletedPseudoDiffOpLattice_iff σ hσ M _).1 (h hmap)
    have hyx : y = x := hinj heq
    rwa [hyx] at hy
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ :=
      (mem_mapCompletedPseudoDiffOpLattice_iff σ hσ L y).1 hy
    exact (mem_mapCompletedPseudoDiffOpLattice_iff σ hσ M _).2 ⟨x, h hx, rfl⟩

omit [Fintype ι] in
/-- Differential coefficient transport preserves every interleaving radius exactly. -/
theorem mapCompletedPseudoDiffOpLattice_interleavedAt_iff
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (L M : CompletedPseudoDiffOpLattice K ι) (n : ℕ) :
    (mapCompletedPseudoDiffOpLattice σ hσ L).InterleavedAt n
        (mapCompletedPseudoDiffOpLattice σ hσ M) ↔
      L.InterleavedAt n M := by
  have hπ : mapCompletedPseudoDiffOpUnit σ hσ
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ)) =
      completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ) := by
    rw [map_zpow, mapCompletedPseudoDiffOpUnit_uniformizer]
  unfold CompletedPseudoDiffOpLattice.InterleavedAt
  rw [← hπ, ← mapCompletedPseudoDiffOpLattice_leftScale,
    ← mapCompletedPseudoDiffOpLattice_leftScale,
    mapCompletedPseudoDiffOpLattice_carrier_le_iff,
    mapCompletedPseudoDiffOpLattice_carrier_le_iff]
  simp only [hπ]

/-- Differential coefficient transport is an isometry for interleaving distance. -/
theorem completedPseudoDiffOpLatticeInterleavingDistance_mapCoefficients
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeInterleavingDistance
        (mapCompletedPseudoDiffOpLattice σ hσ L)
        (mapCompletedPseudoDiffOpLattice σ hσ M) =
      completedPseudoDiffOpLatticeInterleavingDistance L M := by
  apply le_antisymm
  · rw [completedPseudoDiffOpLatticeInterleavingDistance_le_iff,
      mapCompletedPseudoDiffOpLattice_interleavedAt_iff]
    exact completedPseudoDiffOpLatticeInterleavingDistance_spec L M
  · rw [completedPseudoDiffOpLatticeInterleavingDistance_le_iff]
    exact (mapCompletedPseudoDiffOpLattice_interleavedAt_iff σ hσ L M _).1
      (completedPseudoDiffOpLatticeInterleavingDistance_spec
        (mapCompletedPseudoDiffOpLattice σ hσ L)
        (mapCompletedPseudoDiffOpLattice σ hσ M))

/-- Literal lattice-level semilinear action `v ↦ σ(v) A`. -/
def differentialVariationalLatticeSemilinearAction
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    {r : ℕ} (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ)
    (L : CompletedPseudoDiffOpLattice K (Fin r)) :
    CompletedPseudoDiffOpLattice K (Fin r) :=
  mapCompletedPseudoDiffOpLatticeLinear
    (completedPseudoDiffOpMatrixLinearEquiv A)
    (mapCompletedPseudoDiffOpLattice σ hσ L)

/-- Every literal semilinear lattice action preserves interleaving distance. -/
theorem completedPseudoDiffOpLatticeInterleavingDistance_semilinearAction
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    {r : ℕ} (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ)
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpLatticeInterleavingDistance
        (differentialVariationalLatticeSemilinearAction σ hσ A L)
        (differentialVariationalLatticeSemilinearAction σ hσ A M) =
      completedPseudoDiffOpLatticeInterleavingDistance L M := by
  simp only [differentialVariationalLatticeSemilinearAction]
  rw [completedPseudoDiffOpLatticeInterleavingDistance_mapLinear,
    completedPseudoDiffOpLatticeInterleavingDistance_mapCoefficients]

end

end GaloisForLFunctions.HTGeometry.DiffOp
