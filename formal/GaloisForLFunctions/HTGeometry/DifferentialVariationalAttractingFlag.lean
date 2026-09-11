import GaloisForLFunctions.HTGeometry.DifferentialVariationalZeroSpeedBoundedOrbit

/-!
# The canonical attracting core of a variational automorphism

The boundary half of the differential variational phase law asks for a canonical object attached to
an automorphism of strictly positive stable speed.  This leaf builds that object algebraically, as
a growth filtration of the completed coordinate space, and identifies its properness with the
boundary phase.

For a vector `v` and a rate `1/c`, `variationalSlowSet` collects the vectors whose variational orbit
`σⁿ v` eventually stays inside the uniformizer dilation `π^{-⌊n/c⌋} L` of the base lattice — that is,
the vectors of variational growth rate at most `1/c`.  Each such set is a submodule over the
completed valuation ring, and the **attracting core** is their intersection over all rates, the
vectors of non-positive growth rate.

* `variationalAttractingCore_eq_univ_of_orbitBounded` — in the bounded phase the core is everything.
  Adjoining a single vector to the base lattice keeps it a lattice, boundedness is independent of
  the base vertex, and exact Cartan balance turns the Euclidean bound into a uniform uniformizer
  confinement.
* `translationLength_eq_zero_of_variationalAttractingCore_eq_univ` — conversely, a full core forces
  zero speed.  A finite generating family of the base lattice carries the whole lattice, so the
  rate-`1/c` confinement of the generators confines `σⁿ L` itself; the one-sided inclusion test
  `DiffOp.carrier_le_leftScale_uniformizer_iff_relativePosition` converts that into a lower bound on
  every Cartan coordinate, and exact balance turns the lower bound into the two-sided Euclidean
  bound `‖μ‖ ≤ (rank+1)³ ⌊n/c⌋`.  Dividing by `n` and letting `c → ∞` kills the speed.
* `variationalAttractingCore_ne_univ_iff_translationLength_pos` and its submodule and Cartan-vector
  forms — **the boundary phase is exactly properness of the canonical attracting core**: `σ` has
  positive stable variational speed if and only if some vector escapes the base lattice at a
  strictly positive exponential rate.

No visual boundary, geodesic, or CAT(0) structure is used; the canonical object is produced by the
growth filtration itself.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Coefficient transport of the valuation ring is a surjective ring map. -/
instance DiffOp.ringHomSurjective_mapCompletedPseudoIntegerEquiv
    {K : Type*} [Field K] [Differential K] (τ : K ≃+* K) (hτ : ∀ a : K, τ (a′) = (τ a)′) :
    RingHomSurjective (DiffOp.mapCompletedPseudoIntegerEquiv τ hτ).toRingHom :=
  ⟨(DiffOp.mapCompletedPseudoIntegerEquiv τ hτ).surjective⟩

/-- The vector-level semilinear map underlying the canonical variational lattice action. -/
def DifferentialFieldAut.vecBuildingActionMap (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    (Fin r → DiffOp.CompletedPseudoDiffOp K) →ₛₗ[(DiffOp.mapCompletedPseudoIntegerEquiv
        σ.toRingEquiv σ.deriv_comm).toRingHom] (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  (DiffOp.restrictCompletedPseudoVecLinearEquiv
      (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
        (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b))).toLinearMap.comp
    (DiffOp.mapCompletedPseudoIntegerVecLinearMap σ.toRingEquiv σ.deriv_comm)

/-- Value of the vector-level action. -/
def DifferentialFieldAut.vecBuildingAction (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) : Fin r → DiffOp.CompletedPseudoDiffOp K :=
  σ.vecBuildingActionMap b v

/-- The transported lattice carrier is the image of the carrier under the vector action. -/
theorem DifferentialFieldAut.latticeBuildingAction_carrier_eq_map (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    (σ.latticeBuildingAction b L).carrier =
      Submodule.map (σ.vecBuildingActionMap b) L.carrier := by
  rw [σ.latticeBuildingAction_eq b L]
  exact (Submodule.map_comp _ _ L.carrier).symm

/-- Membership in the transported lattice is exactly the image of the vector action. -/
theorem DifferentialFieldAut.mem_latticeBuildingAction_iff (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (w : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    w ∈ (σ.latticeBuildingAction b L).carrier ↔
      ∃ v ∈ L.carrier, σ.vecBuildingAction b v = w := by
  rw [σ.latticeBuildingAction_eq b L]
  rw [DiffOp.mem_mapCompletedPseudoDiffOpLatticeLinear_iff]
  constructor
  · rintro ⟨y, hy, hyw⟩
    obtain ⟨v, hv, hvy⟩ :=
      (DiffOp.mem_mapCompletedPseudoDiffOpLattice_iff σ.toRingEquiv σ.deriv_comm L y).1 hy
    refine ⟨v, hv, ?_⟩
    show σ.vecBuildingActionMap b v = w
    rw [DifferentialFieldAut.vecBuildingActionMap, LinearMap.comp_apply]
    rw [show DiffOp.mapCompletedPseudoIntegerVecLinearMap σ.toRingEquiv σ.deriv_comm v = y
      from hvy]
    exact hyw
  · rintro ⟨v, hv, hvw⟩
    refine ⟨DiffOp.mapCompletedPseudoIntegerVecLinearMap σ.toRingEquiv σ.deriv_comm v, ?_, hvw⟩
    exact (DiffOp.mem_mapCompletedPseudoDiffOpLattice_iff σ.toRingEquiv σ.deriv_comm L _).2
      ⟨v, hv, rfl⟩

/-- The vector action sends the base lattice into any lattice containing its image. -/
theorem DifferentialFieldAut.vecBuildingAction_mem (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K} (hv : v ∈ L.carrier) :
    σ.vecBuildingAction b v ∈ (σ.latticeBuildingAction b L).carrier :=
  (σ.mem_latticeBuildingAction_iff b L _).2 ⟨v, hv, rfl⟩


/-- **One-sided inclusion test.**  A lattice sits inside a uniformizer dilation of another exactly
when every canonical Cartan coordinate is bounded below. -/
theorem DiffOp.carrier_le_leftScale_uniformizer_iff_relativePosition {r : ℕ}
    (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (z : ℤ) :
    M.carrier ≤ (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L).carrier ↔
      ∀ i, z ≤ DiffOp.completedPseudoDiffOpDominantRelativePosition L M i := by
  classical
  let d := DiffOp.completedPseudoDiffOpDominantCartanData L M
  have hcw : d.coweight = DiffOp.completedPseudoDiffOpDominantRelativePosition L M :=
    DiffOp.completedPseudoDiffOpDominantRelativePosition_eq L M d.frame d.coweight
      d.map_left d.map_right d.dominant
  rw [← DiffOp.mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame,
    DiffOp.mapCompletedPseudoDiffOpLatticeLinear_leftScale, d.map_right, d.map_left,
    ← DiffOp.standardCompletedPseudoDiffOpLatticeAtCoweight_zero,
    DiffOp.leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const,
    DiffOp.standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff]
  simp only [Pi.add_apply, zero_add]
  rw [hcw]

/-- An antitone zero-sum vector bounded below is bounded above by the rank times the bound. -/
theorem antitone_sum_zero_top_le_of_lower_bound {s : ℕ}
    (v : Fin (s + 1) → ℝ) (hsum : ∑ i, v i = 0) (N : ℝ) (hv : ∀ i, -N ≤ v i) :
    v 0 ≤ (s : ℝ) * N := by
  classical
  have hsumErase : ∑ j ∈ Finset.univ.erase (0 : Fin (s + 1)), v j = -v 0 := by
    have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := v)
      (Finset.mem_univ (0 : Fin (s + 1)))
    rw [hsum] at hsplit
    linarith
  have hlow : ((Finset.univ.erase (0 : Fin (s + 1))).card : ℝ) * (-N) ≤
      ∑ j ∈ Finset.univ.erase (0 : Fin (s + 1)), v j := by
    calc ((Finset.univ.erase (0 : Fin (s + 1))).card : ℝ) * (-N)
        = ∑ _j ∈ Finset.univ.erase (0 : Fin (s + 1)), (-N) := by
          simp [nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.univ.erase (0 : Fin (s + 1)), v j :=
          Finset.sum_le_sum fun j _ => hv j
  have hcard : (Finset.univ.erase (0 : Fin (s + 1))).card = s := by simp
  rw [hsumErase, hcard] at hlow
  linarith

/-- **Distance bound from a one-sided inclusion.**  Together with exact Cartan balance, a single
uniformizer inclusion controls the whole Euclidean vertex displacement. -/
theorem DiffOp.euclideanVertexDistance_le_of_carrier_le_scale {r : ℕ}
    (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (N : ℕ)
    (hbal : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L M i = 0)
    (hle : M.carrier ≤ (DiffOp.leftScaleCompletedPseudoDiffOpLattice
      (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(N : ℤ))) L).carrier) :
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
        (Quotient.mk _ L) (Quotient.mk _ M) ≤ ((r : ℝ) + 1) ^ 3 * N := by
  classical
  cases r with
  | zero =>
      have : DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
          (Quotient.mk _ L) (Quotient.mk _ M) = 0 := by
        rw [DiffOp.differentialVariationalProjectiveEuclideanVertexDistance, norm_eq_zero]
        apply PiLp.ext
        intro i
        exact absurd i.2 (by omega)
      rw [this]
      positivity
  | succ s =>
      set mu := DiffOp.completedPseudoDiffOpDominantRelativePosition L M with hmu
      have hlower : ∀ i, (-(N : ℤ)) ≤ mu i :=
        (DiffOp.carrier_le_leftScale_uniformizer_iff_relativePosition L M (-(N : ℤ))).1 hle
      have hcenter : DiffOp.centeredCoweight mu = fun i => (mu i : ℝ) := by
        funext i
        simp only [DiffOp.centeredCoweight]
        rw [← Int.cast_sum, hbal]
        simp
      have hsumR : ∑ i, (mu i : ℝ) = 0 := by
        rw [← Int.cast_sum, hbal]; simp
      have hvR : ∀ i, -(N : ℝ) ≤ (mu i : ℝ) := by
        intro i
        exact_mod_cast hlower i
      have hanti : Antitone (fun i => (mu i : ℝ)) := by
        intro i j hij
        show (mu j : ℝ) ≤ (mu i : ℝ)
        exact_mod_cast DiffOp.completedPseudoDiffOpDominantRelativePosition_antitone L M hij
      have htop : (mu 0 : ℝ) ≤ (s : ℝ) * N :=
        antitone_sum_zero_top_le_of_lower_bound (fun i => (mu i : ℝ)) hsumR N hvR
      have hnorm := euclideanNorm_le_card_sq_mul_top_of_antitone_sum_zero
        (fun i => (mu i : ℝ)) hanti hsumR
      have hdist : DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
          (Quotient.mk _ L) (Quotient.mk _ M) =
          ‖(WithLp.toLp 2 (fun i => (mu i : ℝ)) : EuclideanSpace ℝ (Fin (s + 1)))‖ := by
        rw [DiffOp.differentialVariationalProjectiveEuclideanVertexDistance]
        change ‖WithLp.toLp 2 (DiffOp.completedPseudoDiffOpEuclideanRelativePosition L M)‖ = _
        rw [DiffOp.completedPseudoDiffOpEuclideanRelativePosition, hcenter]
      rw [hdist]
      have hcast : (((s + 1 : ℕ) : ℝ) + 1) = (s : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
      have hstep : ((s : ℝ) + 1) ^ (2 : ℕ) * (mu 0 : ℝ) ≤ ((s : ℝ) + 2) ^ 3 * N := by
        have hs : (0 : ℝ) ≤ ((s : ℝ) + 1) ^ (2 : ℕ) := by positivity
        calc ((s : ℝ) + 1) ^ (2 : ℕ) * (mu 0 : ℝ)
            ≤ ((s : ℝ) + 1) ^ (2 : ℕ) * ((s : ℝ) * N) :=
              mul_le_mul_of_nonneg_left htop hs
          _ ≤ ((s : ℝ) + 2) ^ 3 * N := by nlinarith [hNnn, hsnn, sq_nonneg ((s:ℝ))]
      exact le_trans hnorm hstep


/-- Adjoining one vector to a lattice again gives a full finite valuation lattice. -/
def DiffOp.adjoinVectorLattice {r : ℕ} (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    DiffOp.CompletedPseudoDiffOpLattice K (Fin r) where
  carrier := L.carrier ⊔ Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K)) {v}
  fg := L.fg.sup (Submodule.fg_span_singleton v)
  full := by
    refine le_antisymm le_top ?_
    rw [← L.full]
    exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)

theorem DiffOp.mem_adjoinVectorLattice {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    v ∈ (DiffOp.adjoinVectorLattice L v).carrier :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)

/-- Every lattice sits inside a uniformizer dilation of every other lattice. -/
theorem DiffOp.exists_nat_carrier_le_leftScale_uniformizer {r : ℕ}
    (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    ∃ k : ℕ, M.carrier ≤ (DiffOp.leftScaleCompletedPseudoDiffOpLattice
      (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(k : ℤ))) L).carrier := by
  obtain ⟨a, z, _, hup⟩ := DiffOp.completedPseudoDiffOpLattice_leftCommensurable L M
  refine ⟨(-z).toNat, le_trans hup ?_⟩
  exact DiffOp.leftScale_uniformizer_zpow_carrier_antitone L
    (show (-(((-z).toNat : ℕ) : ℤ)) ≤ z by omega)

/-- Vectors whose variational orbit leaves the base lattice at rate at most `1/c`. -/
def variationalSlowSet (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (c : ℕ) :
    Set (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  {v | ∀ᶠ n : ℕ in Filter.atTop,
    (σ ^ n).vecBuildingAction b v ∈
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-((n / c : ℕ) : ℤ)))
        L).carrier}

/-- The canonical attracting core: vectors of non-positive variational growth rate. -/
def variationalAttractingCore (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    Set (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  ⋂ c : ℕ, variationalSlowSet σ b L (c + 1)

/-- A finite spanning family controls the whole transported lattice. -/
theorem DifferentialFieldAut.latticeBuildingAction_carrier_le_of_span
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L P : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (s : Finset (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hs : Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (s : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) = L.carrier)
    (h : ∀ x ∈ s, σ.vecBuildingAction b x ∈ P.carrier) :
    (σ.latticeBuildingAction b L).carrier ≤ P.carrier := by
  rw [σ.latticeBuildingAction_carrier_eq_map b L, ← hs, Submodule.map_span, Submodule.span_le]
  rintro y ⟨x, hx, rfl⟩
  exact h x hx

/-- **Bounded orbit fills the attracting core.** -/
theorem variationalAttractingCore_eq_univ_of_orbitBounded (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (hb : DifferentialVariationalEuclideanOrbitBounded b (Quotient.mk _ L) σ) :
    variationalAttractingCore σ b L = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro v
  rw [variationalAttractingCore, Set.mem_iInter]
  intro c
  set L' := DiffOp.adjoinVectorLattice L v with hL'
  have hb' : DifferentialVariationalEuclideanOrbitBounded b (Quotient.mk _ L') σ :=
    (differentialVariationalEuclideanOrbitBounded_base_independent b
      (Quotient.mk _ L) (Quotient.mk _ L') σ).1 hb
  obtain ⟨B, hB⟩ := hb'
  obtain ⟨N, hN⟩ := exists_nat_ge B
  obtain ⟨k, hk⟩ := DiffOp.exists_nat_carrier_le_leftScale_uniformizer L L'
  have hstep : ∀ n : ℕ, ((σ ^ n).latticeBuildingAction b L').carrier ≤
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-((N + k : ℕ) : ℤ)))
        L).carrier := by
    intro n
    have hbal : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L'
        ((σ ^ n).latticeBuildingAction b L') i = 0 :=
      (σ ^ n).variationalOreCartanBalance_everyLattice b L'
    have hdist : DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
        (Quotient.mk _ L') (Quotient.mk _ ((σ ^ n).latticeBuildingAction b L')) ≤ (N : ℝ) := by
      refine le_trans ?_ hN
      simpa only [DifferentialFieldAut.projectiveBuildingAction_mk] using hB n
    have hinter := DiffOp.completedPseudoDiffOpLattice_interleavedAt_of_balanced_euclidean_le
      L' ((σ ^ n).latticeBuildingAction b L') N hbal hdist
    have hup := DiffOp.CompletedPseudoDiffOpLattice.carrier_le_inverseScale_of_interleavedAt
      hinter
    refine le_trans hup ?_
    have hmono := DiffOp.leftScaleCompletedPseudoDiffOpLattice_carrier_mono
      (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(N : ℤ))) hk
    refine le_trans hmono ?_
    have hexp : (-(N : ℤ)) + (-(k : ℤ)) = -((N + k : ℕ) : ℤ) := by push_cast; ring
    rw [DiffOp.leftScaleCompletedPseudoDiffOpLattice_mul, ← zpow_add, hexp]
  refine Filter.eventually_atTop.2 ⟨(c + 1) * (N + k) + (c + 1), fun n hn => ?_⟩
  have hmem : (σ ^ n).vecBuildingAction b v ∈ ((σ ^ n).latticeBuildingAction b L').carrier :=
    (σ ^ n).vecBuildingAction_mem b L' (DiffOp.mem_adjoinVectorLattice L v)
  have h1 := hstep n hmem
  have hdiv : N + k ≤ n / (c + 1) := by
    have hmul : (N + k) * (c + 1) = (c + 1) * (N + k) := Nat.mul_comm _ _
    rw [Nat.le_div_iff_mul_le (show 0 < c + 1 by omega)]
    omega
  exact DiffOp.leftScale_uniformizer_zpow_carrier_antitone L
    (show (-((n / (c + 1) : ℕ) : ℤ)) ≤ (-((N + k : ℕ) : ℤ)) by omega) h1


/-- **A full attracting core forces zero stable speed.** -/
theorem translationLength_eq_zero_of_variationalAttractingCore_eq_univ
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (hcore : variationalAttractingCore σ b L = Set.univ) :
    differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ = 0 := by
  classical
  obtain ⟨s, hs⟩ := L.fg
  have hnonneg : 0 ≤ differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ :=
    (differentialVariationalEuclideanOrbitGauge b (Quotient.mk _ L)).translationLength_nonneg σ
  have hbound : ∀ c : ℕ,
      differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ ≤
        ((r : ℝ) + 1) ^ 3 / ((c : ℝ) + 1) := by
    intro c
    have hev : ∀ᶠ n : ℕ in Filter.atTop, ∀ x ∈ s,
        (σ ^ n).vecBuildingAction b x ∈
          (DiffOp.leftScaleCompletedPseudoDiffOpLattice
            (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
              (-((n / (c + 1) : ℕ) : ℤ))) L).carrier := by
      rw [Filter.eventually_all_finset]
      intro x _
      have hx : x ∈ variationalAttractingCore σ b L := by rw [hcore]; trivial
      exact Set.mem_iInter.1 hx c
    have hdistev : ∀ᶠ n : ℕ in Filter.atTop,
        DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
            (Quotient.mk _ L) ((σ ^ n).projectiveBuildingAction b (Quotient.mk _ L)) / n
          ≤ ((r : ℝ) + 1) ^ 3 / ((c : ℝ) + 1) := by
      filter_upwards [hev, Filter.eventually_gt_atTop 0] with n hn hnpos
      have hle := (σ ^ n).latticeBuildingAction_carrier_le_of_span b L
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
            (-((n / (c + 1) : ℕ) : ℤ))) L) s hs hn
      have hbal : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L
          ((σ ^ n).latticeBuildingAction b L) i = 0 :=
        (σ ^ n).variationalOreCartanBalance_everyLattice b L
      have hdist := DiffOp.euclideanVertexDistance_le_of_carrier_le_scale L
        ((σ ^ n).latticeBuildingAction b L) (n / (c + 1)) hbal hle
      rw [DifferentialFieldAut.projectiveBuildingAction_mk]
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hdivle : ((n / (c + 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((c : ℝ) + 1) := by
        have := Nat.cast_div_le (α := ℝ) (m := n) (n := c + 1)
        push_cast at this
        exact this
      have hApos : (0 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := by positivity
      have hcpos : (0 : ℝ) < (c : ℝ) + 1 := by positivity
      rw [div_le_div_iff₀ hnR hcpos]
      calc DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
            (Quotient.mk _ L) (Quotient.mk _ ((σ ^ n).latticeBuildingAction b L)) *
              ((c : ℝ) + 1)
          ≤ (((r : ℝ) + 1) ^ 3 * ((n / (c + 1) : ℕ) : ℝ)) * ((c : ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_right hdist (le_of_lt hcpos)
        _ ≤ (((r : ℝ) + 1) ^ 3 * ((n : ℝ) / ((c : ℝ) + 1))) * ((c : ℝ) + 1) := by
            gcongr
        _ = ((r : ℝ) + 1) ^ 3 * (n : ℝ) := by
            field_simp
    exact le_of_tendsto
      (tendsto_differentialVariationalEuclidean_normalizedOrbitDistance b
        (Quotient.mk _ L) σ) hdistev
  refine le_antisymm ?_ hnonneg
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨c, hc⟩ := exists_nat_gt (((r : ℝ) + 1) ^ 3 / ε)
  have hcpos : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have hsmall : ((r : ℝ) + 1) ^ 3 / ((c : ℝ) + 1) ≤ ε := by
    rw [div_le_iff₀ hcpos]
    have h1 : ((r : ℝ) + 1) ^ 3 / ε < (c : ℝ) := hc
    rw [div_lt_iff₀ hε] at h1
    nlinarith [hε, (Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
  have := hbound c
  linarith

/-- **The canonical attracting core is the whole space exactly in the bounded phase.** -/
theorem variationalAttractingCore_eq_univ_iff (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingCore σ b L = Set.univ ↔
      differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ = 0 := by
  constructor
  · exact translationLength_eq_zero_of_variationalAttractingCore_eq_univ σ b L
  · intro hzero
    exact variationalAttractingCore_eq_univ_of_orbitBounded σ b L
      (differentialVariationalEuclideanTranslationLength_eq_zero_implies_orbitBounded b
        (Quotient.mk _ L) σ hzero)

/-- **Boundary phase.**  Strictly positive stable variational speed is exactly the existence of a
vector of strictly positive variational growth rate — a proper canonical attracting flag. -/
theorem variationalAttractingCore_ne_univ_iff_translationLength_pos
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingCore σ b L ≠ Set.univ ↔
      0 < differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ := by
  rw [Ne, variationalAttractingCore_eq_univ_iff σ b L]
  constructor
  · intro h
    exact lt_of_le_of_ne
      ((differentialVariationalEuclideanOrbitGauge b (Quotient.mk _ L)).translationLength_nonneg σ)
      (fun hzero => h hzero.symm)
  · intro h hzero
    rw [hzero] at h
    exact lt_irrefl 0 h

/-- The same dichotomy stated through the intrinsic Cartan translation vector. -/
theorem variationalAttractingCore_ne_univ_iff_cartanVector_ne_zero
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingCore σ b L ≠ Set.univ ↔
      differentialVariationalCartanTranslationVector b (Quotient.mk _ L) σ ≠ 0 := by
  rw [variationalAttractingCore_ne_univ_iff_translationLength_pos σ b L,
    differentialVariationalEuclideanTranslationLength_pos_iff_cartanVector_ne_zero]


set_option synthInstance.maxHeartbeats 400000 in
/-- Each slow set is a submodule over the completed valuation ring. -/
def variationalSlowSubmodule (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (c : ℕ) :
    Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K) where
  carrier := variationalSlowSet σ b L c
  add_mem' := by
    intro v w hv hw
    filter_upwards [hv, hw] with n hvn hwn
    have : (σ ^ n).vecBuildingAction b (v + w) =
        (σ ^ n).vecBuildingAction b v + (σ ^ n).vecBuildingAction b w :=
      map_add ((σ ^ n).vecBuildingActionMap b) v w
    rw [this]
    exact Submodule.add_mem _ hvn hwn
  zero_mem' := by
    filter_upwards with n
    have : (σ ^ n).vecBuildingAction b 0 = 0 := map_zero ((σ ^ n).vecBuildingActionMap b)
    rw [this]
    exact Submodule.zero_mem _
  smul_mem' := by
    intro a v hv
    filter_upwards [hv] with n hvn
    have : (σ ^ n).vecBuildingAction b (a • v) =
        (DiffOp.mapCompletedPseudoIntegerEquiv (σ ^ n).toRingEquiv (σ ^ n).deriv_comm a) •
          (σ ^ n).vecBuildingAction b v :=
      map_smulₛₗ ((σ ^ n).vecBuildingActionMap b) a v
    rw [this]
    exact Submodule.smul_mem _ _ hvn

@[simp] theorem mem_variationalSlowSubmodule (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (c : ℕ)
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    v ∈ variationalSlowSubmodule σ b L c ↔ v ∈ variationalSlowSet σ b L c := Iff.rfl

/-- The attracting core as a submodule over the completed valuation ring. -/
def variationalAttractingSubmodule (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  ⨅ c : ℕ, variationalSlowSubmodule σ b L (c + 1)

theorem variationalAttractingSubmodule_carrier (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    (variationalAttractingSubmodule σ b L :
        Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) =
      variationalAttractingCore σ b L := by
  ext v
  rw [SetLike.mem_coe, variationalAttractingSubmodule, Submodule.mem_iInf,
    variationalAttractingCore, Set.mem_iInter]
  rfl

/-- **Boundary phase, submodule form.**  Strictly positive stable speed is exactly properness of
the canonical attracting submodule. -/
theorem variationalAttractingSubmodule_ne_top_iff_translationLength_pos
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingSubmodule σ b L ≠ ⊤ ↔
      0 < differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ := by
  rw [← variationalAttractingCore_ne_univ_iff_translationLength_pos σ b L]
  constructor
  · intro h hcore
    apply h
    apply SetLike.coe_injective
    rw [variationalAttractingSubmodule_carrier, hcore]
    simp
  · intro h htop
    apply h
    have := variationalAttractingSubmodule_carrier σ b L
    rw [htop] at this
    simpa using this.symm

end

end GaloisForLFunctions.HTGeometry
