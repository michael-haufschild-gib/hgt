import GaloisForLFunctions.HTGeometry.DifferentialVariationalBoundedOrbitFixedVertex
import GaloisForLFunctions.HTGeometry.DifferentialVariationalPhaseNecessary
import GaloisForLFunctions.HTGeometry.DifferentialVariationalFixedVertexPhase

/-!
# Zero variational speed forces a bounded orbit

This leaf closes the last implication of the differential variational phase partition: a vanishing
stable Euclidean speed, equivalently a vanishing intrinsic Cartan translation vector, forces the
canonical variational orbit to be bounded, hence to fix a projective completed-lattice vertex.

The argument is purely algebraic; no CAT(0) realization, geodesic, or semisimplicity theorem for
affine buildings is used.  Write `M_n = L + σL + ⋯ + σⁿ L` for the forward orbit hull, built by the
recursion `M_{n+1} = L + σ M_n`, and `d_n` for the length of the layer `M_{n+1}/M_n`.

* **Layer monotonicity.**  Because `M_{n+1} = L + σ M_n`, the layer `M_{n+2}/M_{n+1}` is a quotient
  of `σ M_{n+1} / σ M_n`, and the semilinear action preserves length.  Hence `d_{n+1} ≤ d_n`, so the
  natural-number sequence of layer lengths is antitone.
* **Vanishing layer.**  If some `d_n = 0` then `M_{n+1} = M_n`, so the hull absorbs its own image,
  `σ M_n ⊆ M_n`.  Exact Cartan balance turns that one-sided inclusion into an equality, so `M_n` is a
  literally fixed lattice vertex and the orbit is bounded.
* **Persistent layer.**  Otherwise every layer has length at least one, so `M_n` has length at least
  `n` above `L`.  A sublinear Euclidean displacement confines every `σ^k L` with `k ≤ n`, hence the
  whole hull, to a uniformizer dilation of radius `O(B + εn)`, whose length above `L` is
  `rank · (B + εn + 1)`.  Choosing `ε` below `1/(2·rank)` contradicts linear growth.

The capstone `differentialVariationalPhase_iff` therefore records the complete unconditional
partition: bounded orbit, fixed projective vertex, zero scalar speed and zero Cartan vector are all
equivalent, and `differentialVariationalEuclideanTranslationLength_pos_iff_orbitUnbounded` states
that there is no parabolic third phase.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- For submodules `A`, `B' ≤ B` of a common module, the layer `(A ⊔ B)/(A ⊔ B')` is a quotient
of `B/B'`, so its length cannot be larger. -/
theorem length_sup_quotient_le {R : Type*} [Ring R] {N : Type*} [AddCommGroup N]
    [Module R N] (A B' B : Submodule R N) (_h : B' ≤ B) :
    Module.length R (↥(A ⊔ B) ⧸ (A ⊔ B').comap (A ⊔ B).subtype) ≤
      Module.length R (↥B ⧸ B'.comap B.subtype) := by
  classical
  have hBle : B ≤ A ⊔ B := le_sup_right
  have hAle : A ≤ A ⊔ B' := le_sup_left
  have hB'le : B' ≤ A ⊔ B' := le_sup_right
  set P : Submodule R (↥(A ⊔ B)) := (A ⊔ B').comap (A ⊔ B).subtype with hPdef
  let f : (↥B) →ₗ[R] (↥(A ⊔ B) ⧸ P) := P.mkQ.comp (Submodule.inclusion hBle)
  have hker : B'.comap (B : Submodule R N).subtype ≤ LinearMap.ker f := by
    intro x hx
    have hxB' : (x : N) ∈ B' := hx
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hB'le hxB'
  let g : ((↥B) ⧸ B'.comap (B : Submodule R N).subtype) →ₗ[R] (↥(A ⊔ B) ⧸ P) :=
    Submodule.liftQ _ f hker
  have hsurj : Function.Surjective g := by
    intro y
    induction y using Quotient.inductionOn with
    | _ z =>
      obtain ⟨a, ha, bb, hb, hab⟩ := Submodule.mem_sup.mp z.2
      refine ⟨Submodule.Quotient.mk ⟨bb, hb⟩, ?_⟩
      show Submodule.Quotient.mk (⟨bb, hBle hb⟩ : ↥(A ⊔ B)) = Quotient.mk _ z
      apply (Submodule.Quotient.eq P).2
      have hz : (z : N) = a + bb := hab.symm
      show ((⟨bb, hBle hb⟩ : ↥(A ⊔ B)) : N) - (z : N) ∈ A ⊔ B'
      have hval : (bb : N) - (z : N) = -a := by
        rw [hz]; abel
      show (bb : N) - (z : N) ∈ A ⊔ B'
      rw [hval]
      exact Submodule.neg_mem _ (hAle ha)
  exact Module.length_le_of_surjective g hsurj


variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- The literal lattice action is transport of coefficients followed by the matrix frame. -/
theorem DifferentialFieldAut.latticeBuildingAction_eq
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (X : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    σ.latticeBuildingAction b X =
      DiffOp.mapCompletedPseudoDiffOpLatticeLinear
        (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
          (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b))
        (DiffOp.mapCompletedPseudoDiffOpLattice σ.toRingEquiv σ.deriv_comm X) := rfl

/-- Coefficient transport is monotone on lattice carriers. -/
theorem DiffOp.mapCompletedPseudoDiffOpLattice_carrier_mono
    {ι : Type*} (τ : K ≃+* K) (hτ : ∀ a : K, τ (a′) = (τ a)′)
    {X Y : DiffOp.CompletedPseudoDiffOpLattice K ι} (h : X.carrier ≤ Y.carrier) :
    (DiffOp.mapCompletedPseudoDiffOpLattice τ hτ X).carrier ≤
      (DiffOp.mapCompletedPseudoDiffOpLattice τ hτ Y).carrier := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := (DiffOp.mem_mapCompletedPseudoDiffOpLattice_iff τ hτ X v).1 hv
  exact (DiffOp.mem_mapCompletedPseudoDiffOpLattice_iff τ hτ Y v).2 ⟨w, h hw, hwv⟩

/-- The canonical variational lattice action is monotone on carriers. -/
theorem DifferentialFieldAut.latticeBuildingAction_carrier_mono
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    {X Y : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)} (h : X.carrier ≤ Y.carrier) :
    (σ.latticeBuildingAction b X).carrier ≤ (σ.latticeBuildingAction b Y).carrier := by
  rw [σ.latticeBuildingAction_eq b X, σ.latticeBuildingAction_eq b Y]
  exact (DiffOp.mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff _ _ _).2
    (DiffOp.mapCompletedPseudoDiffOpLattice_carrier_mono σ.toRingEquiv σ.deriv_comm h)

/-- The canonical variational lattice action preserves the dominant Cartan vector exactly. -/
theorem DifferentialFieldAut.latticeBuildingAction_dominantRelativePosition
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (X Y : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    DiffOp.completedPseudoDiffOpDominantRelativePosition
        (σ.latticeBuildingAction b X) (σ.latticeBuildingAction b Y) =
      DiffOp.completedPseudoDiffOpDominantRelativePosition X Y := by
  rw [σ.latticeBuildingAction_eq b X, σ.latticeBuildingAction_eq b Y,
    DiffOp.completedPseudoDiffOpDominantRelativePosition_mapLinear,
    DiffOp.completedPseudoDiffOpDominantRelativePosition_mapCoefficients]

/-- The canonical variational lattice action preserves natural quotient length exactly. -/
theorem DifferentialFieldAut.latticeBuildingAction_natLength
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (X Y : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    DiffOp.completedPseudoDiffOpLatticeQuotientNatLength
        (σ.latticeBuildingAction b X) (σ.latticeBuildingAction b Y) =
      DiffOp.completedPseudoDiffOpLatticeQuotientNatLength X Y := by
  unfold DiffOp.completedPseudoDiffOpLatticeQuotientNatLength
  rw [σ.latticeBuildingAction_dominantRelativePosition b Y X]

/-- Successor form of the natural-power lattice action. -/
theorem DifferentialFieldAut.latticeBuildingAction_pow_succ
    (σ : DifferentialFieldAut C K) (n : ℕ) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    (σ ^ (n + 1)).latticeBuildingAction b L =
      σ.latticeBuildingAction b ((σ ^ n).latticeBuildingAction b L) := by
  rw [pow_succ, DifferentialFieldAut.latticeBuildingAction_mul]

/-- The inverse automorphism undoes the lattice action. -/
theorem DifferentialFieldAut.latticeBuildingAction_inv_cancel
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (P : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    σ.latticeBuildingAction b (σ⁻¹.latticeBuildingAction b P) = P := by
  rw [← DifferentialFieldAut.latticeBuildingAction_mul, inv_mul_cancel,
    DifferentialFieldAut.latticeBuildingAction_one]

/-- Forward orbit hull `L + σL + ⋯ + σⁿL`, built by the recursion `M_{n+1} = L + σ M_n`. -/
noncomputable def orbitHullLattice (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    ℕ → DiffOp.CompletedPseudoDiffOpLattice K (Fin r)
  | 0 => L
  | (n + 1) =>
      { carrier := L.carrier ⊔ (σ.latticeBuildingAction b (orbitHullLattice σ b L n)).carrier
        fg := L.fg.sup (σ.latticeBuildingAction b (orbitHullLattice σ b L n)).fg
        full := by
          refine le_antisymm le_top ?_
          rw [← L.full]
          exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left) }

@[simp] theorem orbitHullLattice_zero (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    orbitHullLattice σ b L 0 = L := rfl

theorem orbitHullLattice_succ_carrier (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (n : ℕ) :
    (orbitHullLattice σ b L (n + 1)).carrier =
      L.carrier ⊔ (σ.latticeBuildingAction b (orbitHullLattice σ b L n)).carrier := rfl


/-- The orbit hull increases with the index. -/
theorem orbitHullLattice_carrier_le_succ (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (n : ℕ) :
    (orbitHullLattice σ b L n).carrier ≤ (orbitHullLattice σ b L (n + 1)).carrier := by
  induction n with
  | zero =>
      rw [orbitHullLattice_succ_carrier]
      exact le_sup_left
  | succ n ih =>
      rw [orbitHullLattice_succ_carrier, orbitHullLattice_succ_carrier]
      exact sup_le_sup_left (σ.latticeBuildingAction_carrier_mono b ih) _

/-- Every iterate up to the index lies inside the orbit hull. -/
theorem pow_latticeBuildingAction_carrier_le_orbitHull
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    ∀ (n k : ℕ), k ≤ n →
      ((σ ^ k).latticeBuildingAction b L).carrier ≤ (orbitHullLattice σ b L n).carrier := by
  intro n
  induction n with
  | zero =>
      intro k hk
      interval_cases k
      rw [pow_zero, DifferentialFieldAut.latticeBuildingAction_one]
      exact le_rfl
  | succ n ih =>
      intro k hk
      cases k with
      | zero =>
          rw [pow_zero, DifferentialFieldAut.latticeBuildingAction_one,
            orbitHullLattice_succ_carrier]
          exact le_sup_left
      | succ j =>
          have hj : j ≤ n := Nat.succ_le_succ_iff.mp hk
          rw [σ.latticeBuildingAction_pow_succ j b L, orbitHullLattice_succ_carrier]
          exact le_sup_of_le_right
            (σ.latticeBuildingAction_carrier_mono b (ih j hj))

/-- The orbit hull is the smallest lattice containing every iterate up to the index. -/
theorem orbitHullLattice_carrier_le_of_forall
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    ∀ (n : ℕ) (P : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)),
      (∀ k ≤ n, ((σ ^ k).latticeBuildingAction b L).carrier ≤ P.carrier) →
        (orbitHullLattice σ b L n).carrier ≤ P.carrier := by
  intro n
  induction n with
  | zero =>
      intro P hP
      have h0 := hP 0 le_rfl
      rwa [pow_zero, DifferentialFieldAut.latticeBuildingAction_one] at h0
  | succ n ih =>
      intro P hP
      rw [orbitHullLattice_succ_carrier]
      refine sup_le ?_ ?_
      · have h0 := hP 0 (Nat.zero_le _)
        rwa [pow_zero, DifferentialFieldAut.latticeBuildingAction_one] at h0
      · have hinner : (orbitHullLattice σ b L n).carrier ≤
            (σ⁻¹.latticeBuildingAction b P).carrier := by
          refine ih _ ?_
          intro k hk
          have hk1 := hP (k + 1) (Nat.succ_le_succ hk)
          rw [σ.latticeBuildingAction_pow_succ k b L] at hk1
          have hmap := σ⁻¹.latticeBuildingAction_carrier_mono b hk1
          have hcancel :
              σ⁻¹.latticeBuildingAction b
                  (σ.latticeBuildingAction b ((σ ^ k).latticeBuildingAction b L)) =
                (σ ^ k).latticeBuildingAction b L := by
            rw [← DifferentialFieldAut.latticeBuildingAction_mul, mul_inv_cancel,
              DifferentialFieldAut.latticeBuildingAction_one]
          rwa [hcancel] at hmap
        have := σ.latticeBuildingAction_carrier_mono b hinner
        rwa [σ.latticeBuildingAction_inv_cancel b P] at this

/-- Successive orbit-hull layer length. -/
noncomputable def orbitHullDefect (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (n : ℕ) : ℕ :=
  DiffOp.completedPseudoDiffOpLatticeQuotientNatLength
    (orbitHullLattice σ b L n) (orbitHullLattice σ b L (n + 1))

/-- **Defect monotonicity.**  Each orbit-hull layer is a quotient of the previous one. -/
theorem orbitHullDefect_succ_le (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (n : ℕ) :
    orbitHullDefect σ b L (n + 1) ≤ orbitHullDefect σ b L n := by
  have hinner : (σ.latticeBuildingAction b (orbitHullLattice σ b L n)).carrier ≤
      (σ.latticeBuildingAction b (orbitHullLattice σ b L (n + 1))).carrier :=
    σ.latticeBuildingAction_carrier_mono b (orbitHullLattice_carrier_le_succ σ b L n)
  have houter : (orbitHullLattice σ b L (n + 1)).carrier ≤
      (orbitHullLattice σ b L (n + 2)).carrier :=
    orbitHullLattice_carrier_le_succ σ b L (n + 1)
  have hgen := length_sup_quotient_le L.carrier
    (σ.latticeBuildingAction b (orbitHullLattice σ b L n)).carrier
    (σ.latticeBuildingAction b (orbitHullLattice σ b L (n + 1))).carrier hinner
  have hleft := DiffOp.completedPseudoDiffOpLatticeQuotient_length_eq_natLength
    (orbitHullLattice σ b L (n + 1)) (orbitHullLattice σ b L (n + 2)) houter
  have hright := DiffOp.completedPseudoDiffOpLatticeQuotient_length_eq_natLength
    (σ.latticeBuildingAction b (orbitHullLattice σ b L n))
    (σ.latticeBuildingAction b (orbitHullLattice σ b L (n + 1))) hinner
  have hgen' :
      (DiffOp.completedPseudoDiffOpLatticeQuotientNatLength
          (orbitHullLattice σ b L (n + 1)) (orbitHullLattice σ b L (n + 2)) : ℕ∞) ≤
        (DiffOp.completedPseudoDiffOpLatticeQuotientNatLength
          (σ.latticeBuildingAction b (orbitHullLattice σ b L n))
          (σ.latticeBuildingAction b (orbitHullLattice σ b L (n + 1))) : ℕ∞) := by
    rw [← hleft, ← hright]
    exact hgen
  have hcast : orbitHullDefect σ b L (n + 1) ≤
      DiffOp.completedPseudoDiffOpLatticeQuotientNatLength
        (σ.latticeBuildingAction b (orbitHullLattice σ b L n))
        (σ.latticeBuildingAction b (orbitHullLattice σ b L (n + 1))) :=
    ENat.coe_le_coe.mp hgen'
  rwa [σ.latticeBuildingAction_natLength b (orbitHullLattice σ b L n)
    (orbitHullLattice σ b L (n + 1))] at hcast


/-- A one-sided inclusion of lattices with vanishing Cartan character is an equality. -/
theorem DiffOp.completedPseudoDiffOpLattice_eq_of_carrier_le_of_balanced
    {r : ℕ} (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (hle : L.carrier ≤ M.carrier)
    (hbal : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L M i = 0) :
    L = M := by
  classical
  set d := DiffOp.completedPseudoDiffOpDominantCartanData L M with hd
  have hmapped : (DiffOp.mapCompletedPseudoDiffOpLatticeLinear d.frame L).carrier ≤
      (DiffOp.mapCompletedPseudoDiffOpLatticeLinear d.frame M).carrier :=
    (DiffOp.mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame L M).2 hle
  rw [d.map_left, d.map_right,
    ← DiffOp.standardCompletedPseudoDiffOpLatticeAtCoweight_zero] at hmapped
  have hcw : ∀ i, d.coweight i ≤ 0 :=
    (DiffOp.standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff
      (fun _ : Fin r => (0 : ℤ)) d.coweight).1 hmapped
  have hbal' : ∑ i, d.coweight i = 0 := hbal
  have hzero : d.coweight = fun _ : Fin r => (0 : ℤ) := by
    funext i
    by_contra hne
    have hneg : d.coweight i < 0 := lt_of_le_of_ne (hcw i) hne
    have hlt : ∑ j, d.coweight j < ∑ _j : Fin r, (0 : ℤ) :=
      Finset.sum_lt_sum (fun j _ => hcw j) ⟨i, Finset.mem_univ i, hneg⟩
    rw [hbal'] at hlt
    simp at hlt
  have hMeq : DiffOp.mapCompletedPseudoDiffOpLatticeLinear d.frame M =
      DiffOp.mapCompletedPseudoDiffOpLatticeLinear d.frame L := by
    rw [d.map_left, d.map_right, hzero,
      DiffOp.standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
  have h1 : M.carrier ≤ L.carrier :=
    (DiffOp.mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame M L).1
      (le_of_eq (congrArg DiffOp.CompletedPseudoDiffOpLattice.carrier hMeq))
  exact DiffOp.CompletedPseudoDiffOpLattice.ext (le_antisymm hle h1)

/-- The Cartan character is antisymmetric in the pair of lattices. -/
theorem DiffOp.sum_dominantRelativePosition_comm
    {r : ℕ} (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition M L i =
      -∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L M i := by
  rw [DiffOp.completedPseudoDiffOpDominantRelativePosition_reverse L M]
  show ∑ i : Fin r, -(DiffOp.completedPseudoDiffOpDominantRelativePosition L M (Fin.rev i)) = _
  rw [Finset.sum_neg_distrib, neg_inj]
  simpa [DiffOp.completedPseudoDiffOpFinRevPerm] using
    (Equiv.sum_comp (DiffOp.completedPseudoDiffOpFinRevPerm r)
      (fun i : Fin r => DiffOp.completedPseudoDiffOpDominantRelativePosition L M i))

/-- A vanishing orbit-hull defect makes the hull literally invariant. -/
theorem orbitHullLattice_fixed_of_defect_eq_zero (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (n : ℕ)
    (hd : orbitHullDefect σ b L n = 0) :
    σ.latticeBuildingAction b (orbitHullLattice σ b L n) = orbitHullLattice σ b L n := by
  classical
  have hle : (orbitHullLattice σ b L n).carrier ≤
      (orbitHullLattice σ b L (n + 1)).carrier :=
    orbitHullLattice_carrier_le_succ σ b L n
  have hlen := DiffOp.completedPseudoDiffOpLatticeQuotient_length_eq_natLength
    (orbitHullLattice σ b L n) (orbitHullLattice σ b L (n + 1)) hle
  rw [show DiffOp.completedPseudoDiffOpLatticeQuotientNatLength
      (orbitHullLattice σ b L n) (orbitHullLattice σ b L (n + 1)) = 0 from hd] at hlen
  have hsub : Subsingleton
      (↥(orbitHullLattice σ b L (n + 1)).carrier ⧸
        DiffOp.completedPseudoDiffOpLatticeSubmoduleOf (orbitHullLattice σ b L n)
          (orbitHullLattice σ b L (n + 1)) hle) := by
    apply (Module.length_eq_zero_iff
      (R := ↥(DiffOp.CompletedPseudoDiffOpInteger (K := K)))).mp
    simpa using hlen
  have hrev : (orbitHullLattice σ b L (n + 1)).carrier ≤
      (orbitHullLattice σ b L n).carrier := by
    intro v hv
    have hq : (Submodule.Quotient.mk
        (⟨v, hv⟩ : ↥(orbitHullLattice σ b L (n + 1)).carrier) :
        ↥(orbitHullLattice σ b L (n + 1)).carrier ⧸
          DiffOp.completedPseudoDiffOpLatticeSubmoduleOf (orbitHullLattice σ b L n)
            (orbitHullLattice σ b L (n + 1)) hle) = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero
      (DiffOp.completedPseudoDiffOpLatticeSubmoduleOf (orbitHullLattice σ b L n)
        (orbitHullLattice σ b L (n + 1)) hle)).1 hq
  have hact : (σ.latticeBuildingAction b (orbitHullLattice σ b L n)).carrier ≤
      (orbitHullLattice σ b L n).carrier := by
    refine le_trans ?_ hrev
    rw [orbitHullLattice_succ_carrier]
    exact le_sup_right
  have hbal := σ.variationalOreCartanBalance_everyLattice b (orbitHullLattice σ b L n)
  have hbal' : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition
      (orbitHullLattice σ b L n)
      (σ.latticeBuildingAction b (orbitHullLattice σ b L n)) i = 0 := hbal
  have hbalrev : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition
      (σ.latticeBuildingAction b (orbitHullLattice σ b L n))
      (orbitHullLattice σ b L n) i = 0 := by
    rw [DiffOp.sum_dominantRelativePosition_comm, hbal', neg_zero]
  exact DiffOp.completedPseudoDiffOpLattice_eq_of_carrier_le_of_balanced
    (σ.latticeBuildingAction b (orbitHullLattice σ b L n))
    (orbitHullLattice σ b L n) hact hbalrev

/-- The base lattice sits inside every orbit hull. -/
theorem orbitHullLattice_base_carrier_le (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (n : ℕ) :
    L.carrier ≤ (orbitHullLattice σ b L n).carrier := by
  have h := pow_latticeBuildingAction_carrier_le_orbitHull σ b L n 0 (Nat.zero_le n)
  rwa [pow_zero, DifferentialFieldAut.latticeBuildingAction_one] at h

/-- The orbit-hull length is the accumulated defect. -/
theorem natLength_orbitHullLattice (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (n : ℕ) :
    DiffOp.completedPseudoDiffOpLatticeQuotientNatLength L (orbitHullLattice σ b L n) =
      ∑ k ∈ Finset.range n, orbitHullDefect σ b L k := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, orbitHullLattice_zero]
      unfold DiffOp.completedPseudoDiffOpLatticeQuotientNatLength
      rw [DiffOp.completedPseudoDiffOpDominantRelativePosition_self]
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact DiffOp.completedPseudoDiffOpLatticeQuotientNatLength_add L
        (orbitHullLattice σ b L n) (orbitHullLattice σ b L (n + 1))
        (orbitHullLattice_base_carrier_le σ b L n)
        (orbitHullLattice_carrier_le_succ σ b L n)

/-- Length of the uniformizer dilation of a lattice. -/
theorem natLength_leftScale_uniformizer {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (m : ℕ) :
    DiffOp.completedPseudoDiffOpLatticeQuotientNatLength L
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(m : ℤ))) L) =
      r * m := by
  unfold DiffOp.completedPseudoDiffOpLatticeQuotientNatLength
  rw [DiffOp.completedPseudoDiffOpDominantRelativePosition_first_leftScale,
    DiffOp.completedPseudoDiffOpDominantRelativePosition_self,
    DiffOp.completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
  simp

/-- A Euclidean displacement bound places an orbit lattice inside a uniformizer dilation. -/
theorem pow_latticeBuildingAction_carrier_le_scale (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (k N : ℕ)
    (hdist : DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
      (Quotient.mk _ L) (Quotient.mk _ ((σ ^ k).latticeBuildingAction b L)) ≤ (N : ℝ)) :
    ((σ ^ k).latticeBuildingAction b L).carrier ≤
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(N : ℤ))) L).carrier := by
  have hbal : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L
      ((σ ^ k).latticeBuildingAction b L) i = 0 :=
    (σ ^ k).variationalOreCartanBalance_everyLattice b L
  exact DiffOp.CompletedPseudoDiffOpLattice.carrier_le_inverseScale_of_interleavedAt
    (DiffOp.completedPseudoDiffOpLattice_interleavedAt_of_balanced_euclidean_le
      L ((σ ^ k).latticeBuildingAction b L) N hbal hdist)


/-- **Zero stable variational speed forces a bounded Euclidean orbit.**

If some orbit-hull layer is trivial the hull is a literally fixed lattice vertex.  Otherwise every
layer has length at least one, so the hull grows linearly, while a sublinear displacement confines
the hull to a uniformizer dilation of size `o(n)` -- a contradiction. -/
theorem differentialVariationalEuclideanTranslationLength_eq_zero_implies_orbitBounded
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K)
    (hzero : differentialVariationalEuclideanTranslationLength b x σ = 0) :
    DifferentialVariationalEuclideanOrbitBounded b x σ := by
  classical
  revert hzero
  induction x using Quotient.inductionOn with
  | _ L =>
    intro hzero
    by_contra hunb
    have hdefect : ∀ n : ℕ, 1 ≤ orbitHullDefect σ b L n := by
      intro n
      rcases Nat.eq_zero_or_pos (orbitHullDefect σ b L n) with h | h
      · exfalso
        have hfix := orbitHullLattice_fixed_of_defect_eq_zero σ b L n h
        have hfv : DifferentialVariationalHasFixedVertex b σ :=
          ⟨Quotient.mk _ (orbitHullLattice σ b L n), by
            rw [DifferentialFieldAut.projectiveBuildingAction_mk, hfix]⟩
        exact hunb
          (differentialVariationalHasFixedVertex_implies_orbitBounded b _ σ hfv)
      · exact h
    set D : ℕ → ℝ := fun k =>
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
        (Quotient.mk _ L) (Quotient.mk _ ((σ ^ k).latticeBuildingAction b L)) with hD
    have hDnonneg : ∀ k, 0 ≤ D k := fun k =>
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_nonneg _ _
    have hD0 : D 0 = 0 := by
      simp only [hD, pow_zero, DifferentialFieldAut.latticeBuildingAction_one]
      exact DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_self _
    have hDlim : Filter.Tendsto (fun n : ℕ => D n / n) Filter.atTop (nhds 0) := by
      have hbase := tendsto_differentialVariationalEuclidean_normalizedOrbitDistance b
        (Quotient.mk _ L) σ
      rw [hzero] at hbase
      simpa [hD, DifferentialFieldAut.projectiveBuildingAction_mk] using hbase
    set ε : ℝ := 1 / (2 * ((r : ℝ) + 1)) with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]; positivity
    obtain ⟨Kb, hKb⟩ := Metric.tendsto_atTop.mp hDlim ε hεpos
    have hsmall : ∀ k, Kb ≤ k → D k ≤ ε * k := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [hD0]; simp
      · have hdist := hKb k hk
        rw [Real.dist_eq, sub_zero] at hdist
        have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
        have hlt : D k / k < ε := lt_of_abs_lt hdist
        have hmul : (D k / k) * k ≤ ε * k := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hlt) (le_of_lt hkR)
        rwa [div_mul_cancel₀ _ (ne_of_gt hkR)] at hmul
    obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ k ≤ Kb, D k ≤ B := by
      refine ⟨(Finset.range (Kb + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos Kb)⟩ D,
        ?_, ?_⟩
      · refine le_trans (hDnonneg 0) ?_
        exact Finset.le_sup' D (Finset.mem_range.2 (Nat.succ_pos Kb))
      · intro k hk
        exact Finset.le_sup' D (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    have hDbound : ∀ k : ℕ, D k ≤ B + ε * k := by
      intro k
      rcases le_or_gt k Kb with h | h
      · have hnn : (0 : ℝ) ≤ ε * k := by positivity
        linarith [hB k h]
      · linarith [hsmall k (le_of_lt h)]
    have hkey : ∀ n : ℕ, (n : ℝ) ≤ (r : ℝ) * (B + ε * n + 1) := by
      intro n
      have hBn : (0 : ℝ) ≤ B + ε * n := by positivity
      set m : ℕ := ⌈B + ε * n⌉₊ with hm
      have hmR : B + ε * n ≤ (m : ℝ) := Nat.le_ceil _
      have hall : ∀ k ≤ n, ((σ ^ k).latticeBuildingAction b L).carrier ≤
          (DiffOp.leftScaleCompletedPseudoDiffOpLattice
            (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(m : ℤ))) L).carrier := by
        intro k hk
        refine pow_latticeBuildingAction_carrier_le_scale σ b L k m ?_
        have h2 : ε * (k : ℝ) ≤ ε * n := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hεpos)
          exact_mod_cast hk
        have h1 := hDbound k
        calc D k ≤ B + ε * k := h1
          _ ≤ B + ε * n := by linarith
          _ ≤ (m : ℝ) := hmR
      have hhull := orbitHullLattice_carrier_le_of_forall σ b L n _ hall
      have hadd := DiffOp.completedPseudoDiffOpLatticeQuotientNatLength_add L
        (orbitHullLattice σ b L n)
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(m : ℤ))) L)
        (orbitHullLattice_base_carrier_le σ b L n) hhull
      rw [natLength_leftScale_uniformizer L m, natLength_orbitHullLattice σ b L n] at hadd
      have hsum : n ≤ ∑ k ∈ Finset.range n, orbitHullDefect σ b L k := by
        calc n = ∑ _k ∈ Finset.range n, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun k _ => hdefect k)
      have hnm : n ≤ r * m := by omega
      have hnmR : (n : ℝ) ≤ (r : ℝ) * (m : ℝ) := by exact_mod_cast hnm
      have hceil : (m : ℝ) ≤ B + ε * n + 1 := by
        have := Nat.ceil_lt_add_one hBn
        rw [← hm] at this
        linarith
      calc (n : ℝ) ≤ (r : ℝ) * (m : ℝ) := hnmR
        _ ≤ (r : ℝ) * (B + ε * n + 1) :=
            mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg r)
    have hre : (r : ℝ) * ε ≤ 1 / 2 := by
      have hpos : (0 : ℝ) < 2 * ((r : ℝ) + 1) := by positivity
      rw [hεdef, mul_one_div, div_le_iff₀ hpos]
      nlinarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
    have hfinal : ∀ n : ℕ, (n : ℝ) ≤ 2 * ((r : ℝ) * B + (r : ℝ)) := by
      intro n
      have h := hkey n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [h, hre, hn0]
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * ((r : ℝ) * B + (r : ℝ)))
    exact absurd (hfinal n) (not_le.mpr hn)


/-- Zero intrinsic Cartan translation vector forces a bounded Euclidean orbit. -/
theorem differentialVariationalCartanTranslationVector_eq_zero_implies_orbitBounded
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K)
    (hzero : differentialVariationalCartanTranslationVector b x σ = 0) :
    DifferentialVariationalEuclideanOrbitBounded b x σ :=
  differentialVariationalEuclideanTranslationLength_eq_zero_implies_orbitBounded b x σ
    ((differentialVariationalEuclideanTranslationLength_eq_zero_iff_cartanVector_eq_zero
      b x σ).mpr hzero)

/-- **The complete variational phase partition.**  For every finite operator basis, every base
vertex and every differential field automorphism, the following are equivalent: a bounded
Euclidean orbit, a literally fixed projective lattice vertex, vanishing stable Euclidean speed and
a vanishing intrinsic Cartan translation vector. -/
theorem differentialVariationalPhase_iff
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    (DifferentialVariationalEuclideanOrbitBounded b x σ ↔
        DifferentialVariationalHasFixedVertex b σ) ∧
      (DifferentialVariationalEuclideanOrbitBounded b x σ ↔
        differentialVariationalEuclideanTranslationLength b x σ = 0) ∧
      (DifferentialVariationalEuclideanOrbitBounded b x σ ↔
        differentialVariationalCartanTranslationVector b x σ = 0) := by
  refine ⟨differentialVariationalEuclideanOrbitBounded_iff_hasFixedVertex b x σ, ?_, ?_⟩
  · exact ⟨differentialVariationalEuclideanOrbitBounded_implies_translationLength_eq_zero b x σ,
      differentialVariationalEuclideanTranslationLength_eq_zero_implies_orbitBounded b x σ⟩
  · exact ⟨differentialVariationalEuclideanOrbitBounded_implies_cartanVector_eq_zero b x σ,
      differentialVariationalCartanTranslationVector_eq_zero_implies_orbitBounded b x σ⟩

/-- **No parabolic phase.**  Strictly positive stable speed is the exact complement of the
bounded phase, so the variational displacement is either bounded or genuinely linear. -/
theorem differentialVariationalEuclideanTranslationLength_pos_iff_orbitUnbounded
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    0 < differentialVariationalEuclideanTranslationLength b x σ ↔
      ¬ DifferentialVariationalEuclideanOrbitBounded b x σ := by
  constructor
  · exact differentialVariationalEuclideanTranslationLength_pos_implies_orbitUnbounded b x σ
  · intro hunb
    have hnonneg : 0 ≤ differentialVariationalEuclideanTranslationLength b x σ :=
      (differentialVariationalEuclideanOrbitGauge b x).translationLength_nonneg σ
    refine lt_of_le_of_ne hnonneg (fun hzero => hunb ?_)
    exact differentialVariationalEuclideanTranslationLength_eq_zero_implies_orbitBounded b x σ
      hzero.symm

/-- **No parabolic phase, fixed-vertex form.** -/
theorem differentialVariationalEuclideanTranslationLength_pos_iff_noFixedVertex
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    0 < differentialVariationalEuclideanTranslationLength b x σ ↔
      ¬ DifferentialVariationalHasFixedVertex b σ := by
  rw [differentialVariationalEuclideanTranslationLength_pos_iff_orbitUnbounded b x σ,
    differentialVariationalEuclideanOrbitBounded_iff_hasFixedVertex b x σ]

end

end GaloisForLFunctions.HTGeometry
