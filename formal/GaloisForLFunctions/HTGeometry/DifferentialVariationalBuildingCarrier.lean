import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpLattice

/-!
# Homothety carrier of the differential variational building

For left valuation lattices over a noncommutative completed skew field, homothety is right
multiplication by a nonzero scalar.  This file proves that relation is an equivalence relation,
forms its quotient, and descends the functorial differential coefficient action to that quotient.
This is the exact vertex carrier of the differential variational building; metric, apartments, and
the semisimple isometry theorem remain separate structure.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*}

/-- Right multiplication by a nonzero completed pseudodifferential scalar is a left-linear
equivalence over the valuation ring. -/
def rightMulCompletedPseudoIntegerVecLinearEquiv (a : (CompletedPseudoDiffOp K)ˣ) :
    (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOpInteger (K := K)]
      (ι → CompletedPseudoDiffOp K) where
  toFun v i := v i * a
  invFun v i := v i * a⁻¹
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp
  map_add' v w := by
    funext i
    exact add_mul (v i) (w i) a
  map_smul' c v := by
    funext i
    exact mul_assoc (c : CompletedPseudoDiffOp K) (v i) a

/-- Right multiplication by a nonzero completed pseudodifferential scalar is also a left-linear
equivalence over the completed skew field. -/
def rightMulCompletedPseudoVecLinearEquiv (a : (CompletedPseudoDiffOp K)ˣ) :
    (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K) where
  toFun v i := v i * a
  invFun v i := v i * a⁻¹
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp
  map_add' v w := by
    funext i
    exact add_mul (v i) (w i) a
  map_smul' c v := by
    funext i
    exact mul_assoc c (v i) a

/-- Right homothety of a completed pseudodifferential valuation lattice. -/
def rightScaleCompletedPseudoDiffOpLattice (a : (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) : CompletedPseudoDiffOpLattice K ι where
  carrier := L.carrier.map
    (rightMulCompletedPseudoIntegerVecLinearEquiv (ι := ι) a).toLinearMap
  fg := L.fg.map (rightMulCompletedPseudoIntegerVecLinearEquiv (ι := ι) a).toLinearMap
  full := by
    rw [Submodule.eq_top_iff']
    intro y
    let x := (rightMulCompletedPseudoVecLinearEquiv (ι := ι) a).symm y
    have hx : x ∈ Submodule.span (CompletedPseudoDiffOp K)
        (L.carrier : Set (ι → CompletedPseudoDiffOp K)) := by
      rw [L.full]
      trivial
    have himage : rightMulCompletedPseudoVecLinearEquiv (ι := ι) a x ∈
        Submodule.map (rightMulCompletedPseudoVecLinearEquiv (ι := ι) a).toLinearMap
          (Submodule.span (CompletedPseudoDiffOp K)
            (L.carrier : Set (ι → CompletedPseudoDiffOp K))) := ⟨x, hx, rfl⟩
    rw [Submodule.map_span] at himage
    have hsubset : rightMulCompletedPseudoVecLinearEquiv (ι := ι) a ''
          (L.carrier : Set (ι → CompletedPseudoDiffOp K)) ⊆
        (L.carrier.map
            (rightMulCompletedPseudoIntegerVecLinearEquiv (ι := ι) a).toLinearMap :
          Set (ι → CompletedPseudoDiffOp K)) := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    have hy := Submodule.span_mono hsubset himage
    simpa [x] using hy

theorem mem_rightScaleCompletedPseudoDiffOpLattice_iff (a : (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) (y : ι → CompletedPseudoDiffOp K) :
    y ∈ (rightScaleCompletedPseudoDiffOpLattice a L).carrier ↔
      ∃ x ∈ L.carrier,
        rightMulCompletedPseudoIntegerVecLinearEquiv (ι := ι) a x = y := by
  constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, rfl⟩

/-- Scaling by one leaves a valuation lattice fixed. -/
theorem rightScaleCompletedPseudoDiffOpLattice_one (L : CompletedPseudoDiffOpLattice K ι) :
    rightScaleCompletedPseudoDiffOpLattice 1 L = L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_rightScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [rightMulCompletedPseudoIntegerVecLinearEquiv] using hx
  · intro hy
    exact ⟨y, hy, by simp [rightMulCompletedPseudoIntegerVecLinearEquiv]⟩

/-- Successive right homotheties multiply their scalars in application order. -/
theorem rightScaleCompletedPseudoDiffOpLattice_mul (a b : (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) :
    rightScaleCompletedPseudoDiffOpLattice b (rightScaleCompletedPseudoDiffOpLattice a L) =
      rightScaleCompletedPseudoDiffOpLattice (a * b) L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  simp only [mem_rightScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨z, ⟨x, hx, hzx⟩, hyz⟩
    refine ⟨x, hx, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact (mul_assoc (x i) a b).symm
  · rintro ⟨x, hx, hyx⟩
    let z := rightMulCompletedPseudoIntegerVecLinearEquiv (ι := ι) a x
    refine ⟨z, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyx]
    funext i
    exact mul_assoc (x i) a b

/-- Two valuation lattices are homothetic when one is obtained from the other by right
multiplication by a nonzero completed skew scalar. -/
def CompletedPseudoDiffOpLattice.Homothetic
    (L M : CompletedPseudoDiffOpLattice K ι) : Prop :=
  ∃ a : (CompletedPseudoDiffOp K)ˣ, rightScaleCompletedPseudoDiffOpLattice a L = M

theorem CompletedPseudoDiffOpLattice.Homothetic.refl
    (L : CompletedPseudoDiffOpLattice K ι) : L.Homothetic L :=
  ⟨1, rightScaleCompletedPseudoDiffOpLattice_one L⟩

theorem CompletedPseudoDiffOpLattice.Homothetic.symm
    {L M : CompletedPseudoDiffOpLattice K ι} (h : L.Homothetic M) : M.Homothetic L := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨a⁻¹, ?_⟩
  calc
    rightScaleCompletedPseudoDiffOpLattice a⁻¹
        (rightScaleCompletedPseudoDiffOpLattice a L) =
      rightScaleCompletedPseudoDiffOpLattice (a * a⁻¹) L :=
        rightScaleCompletedPseudoDiffOpLattice_mul a a⁻¹ L
    _ = rightScaleCompletedPseudoDiffOpLattice 1 L := by simp
    _ = L := rightScaleCompletedPseudoDiffOpLattice_one L

theorem CompletedPseudoDiffOpLattice.Homothetic.trans
    {L M N : CompletedPseudoDiffOpLattice K ι} (hLM : L.Homothetic M)
    (hMN : M.Homothetic N) : L.Homothetic N := by
  obtain ⟨a, rfl⟩ := hLM
  obtain ⟨b, rfl⟩ := hMN
  exact ⟨a * b, (rightScaleCompletedPseudoDiffOpLattice_mul a b L).symm⟩

/-- Homothety setoid on full valuation lattices. -/
def completedPseudoDiffOpLatticeHomothetySetoid :
    Setoid (CompletedPseudoDiffOpLattice K ι) where
  r := CompletedPseudoDiffOpLattice.Homothetic
  iseqv := ⟨CompletedPseudoDiffOpLattice.Homothetic.refl,
    CompletedPseudoDiffOpLattice.Homothetic.symm,
    CompletedPseudoDiffOpLattice.Homothetic.trans⟩

/-- Exact vertex carrier of the differential variational building: homothety classes of full
valuation lattices in the completed pseudodifferential vector space. -/
abbrev DifferentialVariationalBuildingCarrier
    (K : Type u) [Field K] [Differential K] (ι : Type*) :=
  Quotient (completedPseudoDiffOpLatticeHomothetySetoid (K := K) (ι := ι))

/-- Coefficient action on units of the completed pseudodifferential skew field. -/
def mapCompletedPseudoDiffOpUnit (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    (CompletedPseudoDiffOp K)ˣ →* (CompletedPseudoDiffOp K)ˣ :=
  Units.map (mapCompletedPseudoRingEquiv σ hσ).toMonoidHom

@[simp]
theorem mapCompletedPseudoDiffOpUnit_val (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (a : (CompletedPseudoDiffOp K)ˣ) :
    (mapCompletedPseudoDiffOpUnit σ hσ a : CompletedPseudoDiffOp K) =
      mapCompletedPseudoRingEquiv σ hσ a := rfl

/-- Coefficient transport intertwines right homothety with transport of the scalar. -/
theorem mapCompletedPseudoDiffOpLattice_rightScale (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (a : (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLattice σ hσ (rightScaleCompletedPseudoDiffOpLattice a L) =
      rightScaleCompletedPseudoDiffOpLattice (mapCompletedPseudoDiffOpUnit σ hσ a)
        (mapCompletedPseudoDiffOpLattice σ hσ L) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLattice_iff,
    mem_rightScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨z, hz, hyz⟩
    rw [mem_rightScaleCompletedPseudoDiffOpLattice_iff] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ x,
      ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact ((mapCompletedPseudoRingEquiv σ hσ).map_mul (x i) a).symm
  · rintro ⟨z, hz, hyz⟩
    rw [mem_mapCompletedPseudoDiffOpLattice_iff] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨rightMulCompletedPseudoIntegerVecLinearEquiv (ι := ι) a x,
      ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact (mapCompletedPseudoRingEquiv σ hσ).map_mul (x i) a

/-- Coefficient transport preserves lattice homothety. -/
theorem map_completedPseudoDiffOpLattice_homothetic (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′)
    {L M : CompletedPseudoDiffOpLattice K ι} (h : L.Homothetic M) :
    (mapCompletedPseudoDiffOpLattice σ hσ L).Homothetic
      (mapCompletedPseudoDiffOpLattice σ hσ M) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨mapCompletedPseudoDiffOpUnit σ hσ a,
    (mapCompletedPseudoDiffOpLattice_rightScale σ hσ a L).symm⟩

/-- Canonical coefficient action on the homothety-class carrier. -/
def mapDifferentialVariationalBuildingCarrier (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    DifferentialVariationalBuildingCarrier K ι → DifferentialVariationalBuildingCarrier K ι :=
  Quotient.map (mapCompletedPseudoDiffOpLattice σ hσ)
    (fun _ _ h => map_completedPseudoDiffOpLattice_homothetic σ hσ h)

/-- Identity coefficient automorphism acts trivially on the building carrier. -/
theorem mapDifferentialVariationalBuildingCarrier_refl :
    mapDifferentialVariationalBuildingCarrier (ι := ι) (RingEquiv.refl K)
      refl_deriv_comm = id := by
  funext q
  induction q using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      rw [mapCompletedPseudoDiffOpLattice_refl]

/-- Coefficient actions on the building carrier respect composition. -/
theorem mapDifferentialVariationalBuildingCarrier_trans (σ τ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (hτ : ∀ a : K, τ (a′) = (τ a)′) :
    mapDifferentialVariationalBuildingCarrier (ι := ι) (σ.trans τ)
        (trans_deriv_comm σ τ hσ hτ) =
      mapDifferentialVariationalBuildingCarrier τ hτ ∘
        mapDifferentialVariationalBuildingCarrier σ hσ := by
  funext q
  induction q using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      rw [mapCompletedPseudoDiffOpLattice_trans]

end

end DiffOp

end GaloisForLFunctions.HTGeometry
