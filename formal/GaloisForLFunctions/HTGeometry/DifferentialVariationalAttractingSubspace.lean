import GaloisForLFunctions.HTGeometry.DifferentialVariationalAttractingFlag

/-!
# The attracting core is a canonical invariant subspace

The attracting core of a variational automorphism was built as a growth filtration and shown to be
proper exactly in the boundary phase.  This leaf upgrades it from a valuation-ring submodule to an
honest subspace over the completed pseudodifferential skew field, invariant under the automorphism —
that is, to a genuine weighted differential flag datum.

* `DifferentialFieldAut.vecBuildingAction_mul` — the vector-level action obeys the same semilinear
  cocycle law as the lattice action.  The matrix cocycle `U_{στ} = τ(U_σ)·U_τ`, transport of a row
  product, and associativity of `vecMul` give it directly.
* `variationalAttractingCore_vecBuildingAction_mem` — the core is `σ`-invariant.  Reading the
  rate-`1/(2c+2)` condition one step along the orbit gives the rate-`1/(c+1)` condition for `σv`,
  because `⌊(n+1)/(2c+2)⌋ ≤ ⌊n/(c+1)⌋` for every `n`.
* `variationalAttractingCore_uniformizer_zpow_smul` — the uniformizer is fixed by every differential
  coefficient automorphism, so scaling by `π^z` only shifts the confinement exponent by the constant
  `z`, which a rate halving absorbs.
* `variationalAttractingCore_smul_mem` — an arbitrary nonzero completed skew scalar factors as
  `π^{-t}` times a valuation-ring element, so the previous two closures give closure under the whole
  skew field.
* `variationalAttractingSubspace` and
  `variationalAttractingSubspace_ne_top_iff_translationLength_pos` — the canonical `σ`-invariant
  subspace, proper exactly in the boundary phase.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

@[simp] theorem DifferentialFieldAut.vecBuildingAction_apply (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    σ.vecBuildingAction b v =
      Matrix.vecMul (DiffOp.mapCompletedPseudoVecLinearMap σ.toRingEquiv σ.deriv_comm v)
        ((variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b :
          Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K))) := rfl

/-- The vector action obeys the same semilinear cocycle law as the lattice action. -/
theorem DifferentialFieldAut.vecBuildingAction_mul (σ τ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    (σ * τ).vecBuildingAction b v = τ.vecBuildingAction b (σ.vecBuildingAction b v) := by
  have hunit := variationalOreCompletedMatrixUnit_trans (C := C)
    σ.toRingEquiv τ.toRingEquiv σ.fixes τ.fixes σ.deriv_comm τ.deriv_comm b
  have hcoeff : DiffOp.mapCompletedPseudoVecLinearMap (σ * τ).toRingEquiv (σ * τ).deriv_comm v =
      DiffOp.mapCompletedPseudoVecLinearMap τ.toRingEquiv τ.deriv_comm
        (DiffOp.mapCompletedPseudoVecLinearMap σ.toRingEquiv σ.deriv_comm v) := by
    funext i
    change DiffOp.mapCompletedPseudoRingEquiv (σ * τ).toRingEquiv (σ * τ).deriv_comm (v i) =
      DiffOp.mapCompletedPseudoRingEquiv τ.toRingEquiv τ.deriv_comm
        (DiffOp.mapCompletedPseudoRingEquiv σ.toRingEquiv σ.deriv_comm (v i))
    have hstep := DFunLike.congr_fun (DiffOp.mapCompletedPseudoRingEquiv_trans
      σ.toRingEquiv τ.toRingEquiv σ.deriv_comm τ.deriv_comm) (v i)
    exact hstep.symm
  rw [DifferentialFieldAut.vecBuildingAction_apply,
    DifferentialFieldAut.vecBuildingAction_apply,
    DifferentialFieldAut.vecBuildingAction_apply, hcoeff]
  have hmulval : ((variationalOreCompletedMatrixUnit (σ * τ).fixes (σ * τ).deriv_comm b :
        (Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K))ˣ) :
      Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K)) =
      ((variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b :
          Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K)).map
        (DiffOp.mapCompletedPseudoRingEquiv τ.toRingEquiv τ.deriv_comm)) *
        (variationalOreCompletedMatrixUnit τ.fixes τ.deriv_comm b :
          Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K)) := by
    rw [show (variationalOreCompletedMatrixUnit (σ * τ).fixes (σ * τ).deriv_comm b) =
        DiffOp.mapCompletedPseudoDiffOpMatrixUnit τ.toRingEquiv τ.deriv_comm
            (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b) *
          variationalOreCompletedMatrixUnit τ.fixes τ.deriv_comm b from hunit]
    rfl
  rw [hmulval, ← Matrix.vecMul_vecMul]
  congr 1
  exact (DiffOp.mapCompletedPseudoVecLinearMap_vecMul τ.toRingEquiv τ.deriv_comm
    (DiffOp.mapCompletedPseudoVecLinearMap σ.toRingEquiv σ.deriv_comm v)
    (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b)).symm


/-- Successor form of the natural-power vector action. -/
theorem DifferentialFieldAut.vecBuildingAction_pow_succ (σ : DifferentialFieldAut C K) (n : ℕ)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    (σ ^ (n + 1)).vecBuildingAction b v =
      (σ ^ n).vecBuildingAction b (σ.vecBuildingAction b v) := by
  rw [pow_succ', DifferentialFieldAut.vecBuildingAction_mul]

/-- **The attracting core is invariant under the automorphism.** -/
theorem variationalAttractingCore_vecBuildingAction_mem (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ variationalAttractingCore σ b L) :
    σ.vecBuildingAction b v ∈ variationalAttractingCore σ b L := by
  rw [variationalAttractingCore, Set.mem_iInter]
  intro c
  have hv2 : v ∈ variationalSlowSet σ b L (2 * c + 2) := by
    have h := Set.mem_iInter.1 hv (2 * c + 1)
    have hidx : 2 * c + 1 + 1 = 2 * c + 2 := by omega
    rwa [hidx] at h
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hv2
  refine Filter.eventually_atTop.2 ⟨M, fun n hn => ?_⟩
  have hshift := hM (n + 1) (by omega)
  rw [← DifferentialFieldAut.vecBuildingAction_pow_succ]
  refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L ?_ hshift
  have hq : ((n + 1) / (2 * c + 2)) ≤ n / (c + 1) := by
    have hdm : ((n + 1) / (2 * c + 2)) * (2 * c + 2) ≤ n + 1 := Nat.div_mul_le_self _ _
    have hexp : ((n + 1) / (2 * c + 2)) * (2 * c + 2) =
        2 * (((n + 1) / (2 * c + 2)) * (c + 1)) := by ring
    rw [Nat.le_div_iff_mul_le (show 0 < c + 1 by omega)]
    omega
  omega


/-- The vector action as a map semilinear over the completed skew field. -/
def DifferentialFieldAut.vecBuildingActionFieldMap (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    (Fin r → DiffOp.CompletedPseudoDiffOp K) →ₛₗ[(DiffOp.mapCompletedPseudoRingEquiv
        σ.toRingEquiv σ.deriv_comm).toRingHom] (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
      (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b)).toLinearMap.comp
    (DiffOp.mapCompletedPseudoVecLinearMap σ.toRingEquiv σ.deriv_comm)

theorem DifferentialFieldAut.vecBuildingAction_eq_fieldMap (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    σ.vecBuildingAction b v = σ.vecBuildingActionFieldMap b v := rfl

/-- The vector action is semilinear for the completed skew field. -/
theorem DifferentialFieldAut.vecBuildingAction_smul (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (a : DiffOp.CompletedPseudoDiffOp K) (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    σ.vecBuildingAction b (a • v) =
      (DiffOp.mapCompletedPseudoRingEquiv σ.toRingEquiv σ.deriv_comm a) •
        σ.vecBuildingAction b v := by
  rw [σ.vecBuildingAction_eq_fieldMap b, σ.vecBuildingAction_eq_fieldMap b]
  exact map_smulₛₗ (σ.vecBuildingActionFieldMap b) a v

omit [IsConstantBase C K] in
/-- Coefficient transport fixes every uniformizer power. -/
theorem DifferentialFieldAut.mapCompletedPseudoRingEquiv_uniformizer_zpow
    (σ : DifferentialFieldAut C K) (z : ℤ) :
    DiffOp.mapCompletedPseudoRingEquiv σ.toRingEquiv σ.deriv_comm
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) =
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) := by
  have hz : DiffOp.mapCompletedPseudoDiffOpUnit σ.toRingEquiv σ.deriv_comm
      (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z) =
      DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z := by
    rw [map_zpow, DiffOp.mapCompletedPseudoDiffOpUnit_uniformizer]
  exact congrArg (fun u : (DiffOp.CompletedPseudoDiffOp K)ˣ =>
    (u : DiffOp.CompletedPseudoDiffOp K)) hz

/-- Scaling a lattice member by a unit lands in the scaled lattice. -/
theorem DiffOp.smul_mem_leftScale {r : ℕ} (u : (DiffOp.CompletedPseudoDiffOp K)ˣ)
    (P : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    {w : Fin r → DiffOp.CompletedPseudoDiffOp K} (hw : w ∈ P.carrier) :
    (u : DiffOp.CompletedPseudoDiffOp K) • w ∈
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice u P).carrier := by
  rw [DiffOp.mem_leftScaleCompletedPseudoDiffOpLattice_iff]
  exact ⟨w, hw, rfl⟩

/-- **The attracting core is stable under uniformizer scaling.** -/
theorem variationalAttractingCore_uniformizer_zpow_smul (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (z : ℤ)
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ variationalAttractingCore σ b L) :
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈
      variationalAttractingCore σ b L := by
  rw [variationalAttractingCore, Set.mem_iInter]
  intro c
  have hv2 : v ∈ variationalSlowSet σ b L (2 * c + 2) := by
    have h := Set.mem_iInter.1 hv (2 * c + 1)
    have hidx : 2 * c + 1 + 1 = 2 * c + 2 := by omega
    rwa [hidx] at h
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hv2
  refine Filter.eventually_atTop.2 ⟨M + (2 * c + 2) * z.natAbs, fun n hn => ?_⟩
  have hbase := hM n (by omega)
  rw [(σ ^ n).vecBuildingAction_smul b,
    (σ ^ n).mapCompletedPseudoRingEquiv_uniformizer_zpow z]
  have hscaled := DiffOp.smul_mem_leftScale
    (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z) _ hbase
  rw [DiffOp.leftScaleCompletedPseudoDiffOpLattice_mul, ← zpow_add] at hscaled
  refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L ?_ hscaled
  set q := n / (2 * c + 2) with hqdef
  have h1 : q * (2 * c + 2) ≤ n := Nat.div_mul_le_self _ _
  have h2 : 2 * q * (c + 1) = q * (2 * c + 2) := by ring
  have htwice : 2 * q ≤ n / (c + 1) := by
    rw [Nat.le_div_iff_mul_le (show 0 < c + 1 by omega)]
    omega
  have h3 : z.natAbs * (2 * c + 2) = (2 * c + 2) * z.natAbs := by ring
  have hqbig : z.natAbs ≤ q := by
    rw [hqdef, Nat.le_div_iff_mul_le (show 0 < 2 * c + 2 by omega)]
    omega
  omega


theorem mem_variationalAttractingCore_iff_mem_submodule (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    v ∈ variationalAttractingCore σ b L ↔ v ∈ variationalAttractingSubmodule σ b L := by
  rw [← SetLike.mem_coe, variationalAttractingSubmodule_carrier]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The attracting core is closed under every completed skew scalar.** -/
theorem variationalAttractingCore_smul_mem (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (a : DiffOp.CompletedPseudoDiffOp K) {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ variationalAttractingCore σ b L) :
    a • v ∈ variationalAttractingCore σ b L := by
  classical
  obtain ⟨t, ht⟩ := DiffOp.exists_uniformizer_left_scale_mem_integer a
  set o : DiffOp.CompletedPseudoDiffOpInteger (K := K) :=
    ⟨((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ t :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) * a, ht⟩ with hodef
  have hov : o • v ∈ variationalAttractingCore σ b L := by
    rw [mem_variationalAttractingCore_iff_mem_submodule] at hv ⊢
    exact (variationalAttractingSubmodule σ b L).smul_mem o hv
  have hunit : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-t)) *
      (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ t) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) = 1 := by
    rw [← zpow_add]; simp
  have hdecomp : a • v =
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-t) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • (o • v) := by
    have hcoe : (o : DiffOp.CompletedPseudoDiffOp K) • v = o • v := rfl
    rw [← hcoe, smul_smul, hodef]
    congr 1
    show a = ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-t) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
      (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ t :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) * a)
    rw [← mul_assoc, ← Units.val_mul, hunit, Units.val_one, one_mul]
  rw [hdecomp]
  exact variationalAttractingCore_uniformizer_zpow_smul σ b L (-t) hov

set_option synthInstance.maxHeartbeats 400000 in
/-- **The canonical attracting subspace.**  A `σ`-invariant subspace of the completed coordinate
space over the completed skew field, namely the vectors of non-positive variational growth rate. -/
def variationalAttractingSubspace (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K) where
  carrier := variationalAttractingCore σ b L
  add_mem' := by
    intro v w hv hw
    exact (mem_variationalAttractingCore_iff_mem_submodule σ b L (v + w)).2
      ((variationalAttractingSubmodule σ b L).add_mem
        ((mem_variationalAttractingCore_iff_mem_submodule σ b L v).1 hv)
        ((mem_variationalAttractingCore_iff_mem_submodule σ b L w).1 hw))
  zero_mem' :=
    (mem_variationalAttractingCore_iff_mem_submodule σ b L 0).2
      (variationalAttractingSubmodule σ b L).zero_mem
  smul_mem' := by
    intro a v hv
    exact variationalAttractingCore_smul_mem σ b L a hv

@[simp] theorem mem_variationalAttractingSubspace (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    v ∈ variationalAttractingSubspace σ b L ↔ v ∈ variationalAttractingCore σ b L := Iff.rfl

/-- The attracting subspace is invariant under the canonical variational action. -/
theorem variationalAttractingSubspace_invariant (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ variationalAttractingSubspace σ b L) :
    σ.vecBuildingAction b v ∈ variationalAttractingSubspace σ b L :=
  variationalAttractingCore_vecBuildingAction_mem σ b L hv

/-- **The boundary phase is exactly a proper canonical attracting subspace.** -/
theorem variationalAttractingSubspace_ne_top_iff_translationLength_pos
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalAttractingSubspace σ b L ≠ ⊤ ↔
      0 < differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ := by
  rw [← variationalAttractingCore_ne_univ_iff_translationLength_pos σ b L]
  constructor
  · intro h hcore
    exact h (by
      apply SetLike.coe_injective
      show variationalAttractingCore σ b L = _
      rw [hcore]; simp)
  · intro h htop
    apply h
    apply Set.eq_univ_of_forall
    intro v
    have : v ∈ variationalAttractingSubspace σ b L := by rw [htop]; trivial
    exact this

end

end GaloisForLFunctions.HTGeometry
