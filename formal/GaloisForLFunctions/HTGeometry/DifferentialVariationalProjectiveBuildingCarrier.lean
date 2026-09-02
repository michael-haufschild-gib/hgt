import GaloisForLFunctions.HTGeometry.DifferentialVariationalStandardApartment

/-!
# Projective building carrier for completed pseudodifferential lattices

The completed pseudodifferential field is noncommutative.  For left valuation lattices, projective
homothety must therefore act by left scalar multiplication: arbitrary left-linear automorphisms
then commute with homothety and descend to lattice classes.  Left multiplication is semilinear over
inner conjugation, and invariance of the valuation under conjugation proves that it preserves the
valuation ring.

This leaf constructs that correctly oriented carrier and the functorial action of every completed-
skew linear equivalence.  It does not identify the quotient with an affine building or supply its
metric; those are separate geometric obligations.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*}

/-- Inner conjugation by a completed-skew unit. -/
def innerCompletedPseudoDiffOpRingEquiv (a : (CompletedPseudoDiffOp K)ˣ) :
    CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K where
  toFun x := a * x * a⁻¹
  invFun x := a⁻¹ * x * a
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  map_mul' x y := by simp [mul_assoc]

@[simp]
theorem innerCompletedPseudoDiffOpRingEquiv_apply
    (a : (CompletedPseudoDiffOp K)ˣ) (x : CompletedPseudoDiffOp K) :
    innerCompletedPseudoDiffOpRingEquiv a x = a * x * a⁻¹ := rfl

/-- Inner conjugation preserves the completed valuation ring. -/
theorem innerCompletedPseudoDiffOp_mem_integer
    (a : (CompletedPseudoDiffOp K)ˣ) (x : CompletedPseudoDiffOpInteger (K := K)) :
    a * (x : CompletedPseudoDiffOp K) * a⁻¹ ∈
      CompletedPseudoDiffOpInteger (K := K) := by
  have hx : 0 ≤ completedPseudoDiffOpAddValue (x : CompletedPseudoDiffOp K) :=
    (mem_completedPseudoDiffOpInteger_iff_addValue_nonneg _).mp x.property
  rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg]
  rw [completedPseudoDiffOpAddValue_mul, completedPseudoDiffOpAddValue_mul,
    completedPseudoDiffOpAddValue_unit_eq_coe,
    completedPseudoDiffOpAddValue_unit_eq_coe]
  rw [completedPseudoDiffOpUnitAddValue_inv]
  simpa [add_assoc, add_comm, add_left_comm] using hx

/-- Restriction of inner conjugation to the completed valuation ring. -/
def innerCompletedPseudoDiffOpIntegerEquiv (a : (CompletedPseudoDiffOp K)ˣ) :
    CompletedPseudoDiffOpInteger (K := K) ≃+*
      CompletedPseudoDiffOpInteger (K := K) where
  toFun x := ⟨a * (x : CompletedPseudoDiffOp K) * a⁻¹,
    innerCompletedPseudoDiffOp_mem_integer a x⟩
  invFun x := ⟨a⁻¹ * (x : CompletedPseudoDiffOp K) * a,
    innerCompletedPseudoDiffOp_mem_integer a⁻¹ x⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_add' x y := by ext; simp [mul_add, add_mul]
  map_mul' x y := by ext; simp [mul_assoc]

@[simp]
theorem innerCompletedPseudoDiffOpIntegerEquiv_apply_coe
    (a : (CompletedPseudoDiffOp K)ˣ) (x : CompletedPseudoDiffOpInteger (K := K)) :
    ((innerCompletedPseudoDiffOpIntegerEquiv a x :
        CompletedPseudoDiffOpInteger (K := K)) : CompletedPseudoDiffOp K) =
      a * (x : CompletedPseudoDiffOp K) * a⁻¹ := rfl

/-- Left scalar multiplication, semilinear over inner conjugation of the valuation ring. -/
def leftMulCompletedPseudoIntegerVecSemilinearMap
    (a : (CompletedPseudoDiffOp K)ˣ) :
    (ι → CompletedPseudoDiffOp K) →ₛₗ[(innerCompletedPseudoDiffOpIntegerEquiv a).toRingHom]
      (ι → CompletedPseudoDiffOp K) where
  toFun v i := a * v i
  map_add' v w := by funext i; exact mul_add _ _ _
  map_smul' c v := by
    funext i
    change a * ((c : CompletedPseudoDiffOp K) * v i) =
      (a * (c : CompletedPseudoDiffOp K) * a⁻¹) * (a * v i)
    simp [mul_assoc]

/-- Left scalar multiplication, semilinear over inner conjugation of the completed skew field. -/
def leftMulCompletedPseudoVecSemilinearMap
    (a : (CompletedPseudoDiffOp K)ˣ) :
    (ι → CompletedPseudoDiffOp K) →ₛₗ[(innerCompletedPseudoDiffOpRingEquiv a).toRingHom]
      (ι → CompletedPseudoDiffOp K) where
  toFun v i := a * v i
  map_add' v w := by funext i; exact mul_add _ _ _
  map_smul' c v := by
    funext i
    change a * (c * v i) = (a * c * a⁻¹) * (a * v i)
    simp [mul_assoc]

/-- Left homothety preserves finite generation and full completed-skew span. -/
def leftScaleCompletedPseudoDiffOpLattice (a : (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) : CompletedPseudoDiffOpLattice K ι := by
  letI : RingHomSurjective (innerCompletedPseudoDiffOpIntegerEquiv a).toRingHom :=
    ⟨(innerCompletedPseudoDiffOpIntegerEquiv a).surjective⟩
  letI : RingHomSurjective (innerCompletedPseudoDiffOpRingEquiv a).toRingHom :=
    ⟨(innerCompletedPseudoDiffOpRingEquiv a).surjective⟩
  refine {
    carrier := L.carrier.map (leftMulCompletedPseudoIntegerVecSemilinearMap a)
    fg := L.fg.map (leftMulCompletedPseudoIntegerVecSemilinearMap a)
    full := ?_ }
  ·
    rw [Submodule.eq_top_iff']
    intro y
    let x : ι → CompletedPseudoDiffOp K := fun i => a⁻¹ * y i
    have hx : x ∈ Submodule.span (CompletedPseudoDiffOp K)
        (L.carrier : Set (ι → CompletedPseudoDiffOp K)) := by
      rw [L.full]
      trivial
    have himage : leftMulCompletedPseudoVecSemilinearMap a x ∈
        Submodule.map (leftMulCompletedPseudoVecSemilinearMap a)
          (Submodule.span (CompletedPseudoDiffOp K)
            (L.carrier : Set (ι → CompletedPseudoDiffOp K))) := ⟨x, hx, rfl⟩
    rw [Submodule.map_span] at himage
    have hsubset : leftMulCompletedPseudoVecSemilinearMap a ''
          (L.carrier : Set (ι → CompletedPseudoDiffOp K)) ⊆
        (L.carrier.map (leftMulCompletedPseudoIntegerVecSemilinearMap a) :
          Set (ι → CompletedPseudoDiffOp K)) := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    have hy := Submodule.span_mono hsubset himage
    have heq : leftMulCompletedPseudoVecSemilinearMap a x = y := by
      funext i
      change (a : CompletedPseudoDiffOp K) *
        ((a⁻¹ : (CompletedPseudoDiffOp K)ˣ) * y i) = y i
      rw [← mul_assoc]
      simp
    rwa [heq] at hy

/-- Membership in a left-scaled lattice is membership of a left-scaled source vector. -/
theorem mem_leftScaleCompletedPseudoDiffOpLattice_iff
    (a : (CompletedPseudoDiffOp K)ˣ) (L : CompletedPseudoDiffOpLattice K ι)
    (y : ι → CompletedPseudoDiffOp K) :
    y ∈ (leftScaleCompletedPseudoDiffOpLattice a L).carrier ↔
      ∃ x ∈ L.carrier, leftMulCompletedPseudoIntegerVecSemilinearMap a x = y := by
  letI : RingHomSurjective (innerCompletedPseudoDiffOpIntegerEquiv a).toRingHom :=
    ⟨(innerCompletedPseudoDiffOpIntegerEquiv a).surjective⟩
  constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, rfl⟩

/-- Left scaling by one fixes every lattice. -/
theorem leftScaleCompletedPseudoDiffOpLattice_one
    (L : CompletedPseudoDiffOpLattice K ι) :
    leftScaleCompletedPseudoDiffOpLattice 1 L = L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_leftScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have heq : leftMulCompletedPseudoIntegerVecSemilinearMap
        (1 : (CompletedPseudoDiffOp K)ˣ) x = x := by
      funext i
      change (1 : CompletedPseudoDiffOp K) * x i = x i
      simp
    rwa [heq]
  · intro hy
    refine ⟨y, hy, ?_⟩
    funext i
    change (1 : CompletedPseudoDiffOp K) * y i = y i
    simp

/-- Successive left homotheties multiply in action order. -/
theorem leftScaleCompletedPseudoDiffOpLattice_mul
    (a b : (CompletedPseudoDiffOp K)ˣ) (L : CompletedPseudoDiffOpLattice K ι) :
    leftScaleCompletedPseudoDiffOpLattice b
        (leftScaleCompletedPseudoDiffOpLattice a L) =
      leftScaleCompletedPseudoDiffOpLattice (b * a) L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  simp only [mem_leftScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨z, ⟨x, hx, hzx⟩, hyz⟩
    refine ⟨x, hx, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact mul_assoc (b : CompletedPseudoDiffOp K) a (x i)
  · rintro ⟨x, hx, hyx⟩
    let z := leftMulCompletedPseudoIntegerVecSemilinearMap a x
    refine ⟨z, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyx]
    funext i
    exact (mul_assoc (b : CompletedPseudoDiffOp K) a (x i)).symm

/-- Correct projective homothety relation for left lattices over a skew field. -/
def CompletedPseudoDiffOpLattice.LeftHomothetic
    (L M : CompletedPseudoDiffOpLattice K ι) : Prop :=
  ∃ a : (CompletedPseudoDiffOp K)ˣ, leftScaleCompletedPseudoDiffOpLattice a L = M

/-- Left homothety is reflexive. -/
theorem CompletedPseudoDiffOpLattice.LeftHomothetic.refl
    (L : CompletedPseudoDiffOpLattice K ι) : L.LeftHomothetic L :=
  ⟨1, leftScaleCompletedPseudoDiffOpLattice_one L⟩

/-- Left homothety is symmetric. -/
theorem CompletedPseudoDiffOpLattice.LeftHomothetic.symm
    {L M : CompletedPseudoDiffOpLattice K ι} (h : L.LeftHomothetic M) :
    M.LeftHomothetic L := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨a⁻¹, ?_⟩
  calc
    leftScaleCompletedPseudoDiffOpLattice a⁻¹
        (leftScaleCompletedPseudoDiffOpLattice a L) =
      leftScaleCompletedPseudoDiffOpLattice (a⁻¹ * a) L :=
        leftScaleCompletedPseudoDiffOpLattice_mul a a⁻¹ L
    _ = L := by
      have hunit : a⁻¹ * a = 1 := by simp
      rw [hunit, leftScaleCompletedPseudoDiffOpLattice_one]

/-- Left homothety is transitive. -/
theorem CompletedPseudoDiffOpLattice.LeftHomothetic.trans
    {L M N : CompletedPseudoDiffOpLattice K ι} (hLM : L.LeftHomothetic M)
    (hMN : M.LeftHomothetic N) : L.LeftHomothetic N := by
  obtain ⟨a, rfl⟩ := hLM
  obtain ⟨b, rfl⟩ := hMN
  exact ⟨b * a, (leftScaleCompletedPseudoDiffOpLattice_mul a b L).symm⟩

/-- Setoid of completed valuation lattices under left homothety. -/
def completedPseudoDiffOpLatticeLeftHomothetySetoid :
    Setoid (CompletedPseudoDiffOpLattice K ι) where
  r := CompletedPseudoDiffOpLattice.LeftHomothetic
  iseqv := ⟨CompletedPseudoDiffOpLattice.LeftHomothetic.refl,
    CompletedPseudoDiffOpLattice.LeftHomothetic.symm,
    CompletedPseudoDiffOpLattice.LeftHomothetic.trans⟩

/-- Projective carrier of full completed valuation lattices with the noncommutatively correct
homothety orientation. -/
abbrev DifferentialVariationalProjectiveBuildingCarrier
    (K : Type u) [Field K] [Differential K] (ι : Type*) :=
  Quotient (completedPseudoDiffOpLatticeLeftHomothetySetoid (K := K) (ι := ι))

/-- Restriction of a completed-skew linear equivalence to valuation-ring scalars. -/
def restrictCompletedPseudoVecLinearEquiv
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K)) :
    (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOpInteger (K := K)]
      (ι → CompletedPseudoDiffOp K) :=
  e.restrictScalars (CompletedPseudoDiffOpInteger (K := K))

/-- Every completed-skew linear equivalence transports full finitely generated lattices. -/
def mapCompletedPseudoDiffOpLatticeLinear
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L : CompletedPseudoDiffOpLattice K ι) : CompletedPseudoDiffOpLattice K ι where
  carrier := L.carrier.map (restrictCompletedPseudoVecLinearEquiv e).toLinearMap
  fg := L.fg.map (restrictCompletedPseudoVecLinearEquiv e).toLinearMap
  full := by
    rw [Submodule.eq_top_iff']
    intro y
    let x := e.symm y
    have hx : x ∈ Submodule.span (CompletedPseudoDiffOp K)
        (L.carrier : Set (ι → CompletedPseudoDiffOp K)) := by
      rw [L.full]
      trivial
    have himage : e x ∈ Submodule.map e.toLinearMap
        (Submodule.span (CompletedPseudoDiffOp K)
          (L.carrier : Set (ι → CompletedPseudoDiffOp K))) := ⟨x, hx, rfl⟩
    rw [Submodule.map_span] at himage
    have hsubset : e '' (L.carrier : Set (ι → CompletedPseudoDiffOp K)) ⊆
        (L.carrier.map (restrictCompletedPseudoVecLinearEquiv e).toLinearMap :
          Set (ι → CompletedPseudoDiffOp K)) := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    have hy := Submodule.span_mono hsubset himage
    simpa [x] using hy

/-- Membership characterization for linear transport of a lattice. -/
theorem mem_mapCompletedPseudoDiffOpLatticeLinear_iff
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L : CompletedPseudoDiffOpLattice K ι) (y : ι → CompletedPseudoDiffOp K) :
    y ∈ (mapCompletedPseudoDiffOpLatticeLinear e L).carrier ↔
      ∃ x ∈ L.carrier, e x = y := by
  constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, rfl⟩

/-- Identity linear transport fixes every lattice. -/
theorem mapCompletedPseudoDiffOpLatticeLinear_refl
    (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLatticeLinear
      (LinearEquiv.refl (CompletedPseudoDiffOp K) _) L = L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff]
  simp

/-- Linear lattice transports compose functorially. -/
theorem mapCompletedPseudoDiffOpLatticeLinear_trans
    (e f : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLatticeLinear f
        (mapCompletedPseudoDiffOpLatticeLinear e L) =
      mapCompletedPseudoDiffOpLatticeLinear (e.trans f) L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  simp only [mem_mapCompletedPseudoDiffOpLatticeLinear_iff]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩

/-- Completed-skew linear transport commutes with left homothety. -/
theorem mapCompletedPseudoDiffOpLatticeLinear_leftScale
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (a : (CompletedPseudoDiffOp K)ˣ) (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLatticeLinear e
        (leftScaleCompletedPseudoDiffOpLattice a L) =
      leftScaleCompletedPseudoDiffOpLattice a
        (mapCompletedPseudoDiffOpLatticeLinear e L) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff,
    mem_leftScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_leftScaleCompletedPseudoDiffOpLattice_iff] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
    exact (e.map_smul (a : CompletedPseudoDiffOp K) x).symm
  · rintro ⟨z, hz, rfl⟩
    rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨leftMulCompletedPseudoIntegerVecSemilinearMap a x,
      ⟨x, hx, rfl⟩, ?_⟩
    exact e.map_smul (a : CompletedPseudoDiffOp K) x

/-- Completed-skew linear transport preserves left-homothety classes. -/
theorem mapCompletedPseudoDiffOpLatticeLinear_leftHomothetic
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    {L M : CompletedPseudoDiffOpLattice K ι} (h : L.LeftHomothetic M) :
    (mapCompletedPseudoDiffOpLatticeLinear e L).LeftHomothetic
      (mapCompletedPseudoDiffOpLatticeLinear e M) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a, (mapCompletedPseudoDiffOpLatticeLinear_leftScale e a L).symm⟩

/-- Functorial action of completed-skew linear equivalences on projective lattice classes. -/
def mapDifferentialVariationalProjectiveBuildingCarrier
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K)) :
    DifferentialVariationalProjectiveBuildingCarrier K ι →
      DifferentialVariationalProjectiveBuildingCarrier K ι :=
  Quotient.map (mapCompletedPseudoDiffOpLatticeLinear e) (by
    intro L M h
    exact mapCompletedPseudoDiffOpLatticeLinear_leftHomothetic e h)

/-- Identity linear equivalence acts trivially on projective lattice classes. -/
theorem mapDifferentialVariationalProjectiveBuildingCarrier_refl
    (x : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    mapDifferentialVariationalProjectiveBuildingCarrier
      (LinearEquiv.refl (CompletedPseudoDiffOp K) _) x = x := by
  induction x using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      change (mapCompletedPseudoDiffOpLatticeLinear
        (LinearEquiv.refl (CompletedPseudoDiffOp K) _) L).LeftHomothetic L
      rw [mapCompletedPseudoDiffOpLatticeLinear_refl]
      exact CompletedPseudoDiffOpLattice.LeftHomothetic.refl L

/-- Linear-equivalence actions compose on projective lattice classes. -/
theorem mapDifferentialVariationalProjectiveBuildingCarrier_trans
    (e f : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (x : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    mapDifferentialVariationalProjectiveBuildingCarrier f
        (mapDifferentialVariationalProjectiveBuildingCarrier e x) =
      mapDifferentialVariationalProjectiveBuildingCarrier (e.trans f) x := by
  induction x using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      change (mapCompletedPseudoDiffOpLatticeLinear f
          (mapCompletedPseudoDiffOpLatticeLinear e L)).LeftHomothetic
        (mapCompletedPseudoDiffOpLatticeLinear (e.trans f) L)
      rw [mapCompletedPseudoDiffOpLatticeLinear_trans]
      exact CompletedPseudoDiffOpLattice.LeftHomothetic.refl _

/-- Coefficient transport intertwines left homothety with transport of its scalar. -/
theorem mapCompletedPseudoDiffOpLattice_leftScale
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (a : (CompletedPseudoDiffOp K)ˣ) (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLattice σ hσ
        (leftScaleCompletedPseudoDiffOpLattice a L) =
      leftScaleCompletedPseudoDiffOpLattice (mapCompletedPseudoDiffOpUnit σ hσ a)
        (mapCompletedPseudoDiffOpLattice σ hσ L) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLattice_iff,
    mem_leftScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨z, hz, hyz⟩
    rw [mem_leftScaleCompletedPseudoDiffOpLattice_iff] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ x,
      ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact ((mapCompletedPseudoRingEquiv σ hσ).map_mul
      (a : CompletedPseudoDiffOp K) (x i)).symm
  · rintro ⟨z, hz, hyz⟩
    rw [mem_mapCompletedPseudoDiffOpLattice_iff] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨leftMulCompletedPseudoIntegerVecSemilinearMap a x,
      ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact (mapCompletedPseudoRingEquiv σ hσ).map_mul
      (a : CompletedPseudoDiffOp K) (x i)

/-- Differential coefficient automorphisms preserve left-homothety classes. -/
theorem mapCompletedPseudoDiffOpLattice_leftHomothetic
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    {L M : CompletedPseudoDiffOpLattice K ι} (h : L.LeftHomothetic M) :
    (mapCompletedPseudoDiffOpLattice σ hσ L).LeftHomothetic
      (mapCompletedPseudoDiffOpLattice σ hσ M) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨mapCompletedPseudoDiffOpUnit σ hσ a,
    (mapCompletedPseudoDiffOpLattice_leftScale σ hσ a L).symm⟩

/-- Coefficient action on correctly oriented projective lattice classes. -/
def mapDifferentialVariationalProjectiveBuildingCarrierCoefficients
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    DifferentialVariationalProjectiveBuildingCarrier K ι →
      DifferentialVariationalProjectiveBuildingCarrier K ι :=
  Quotient.map (mapCompletedPseudoDiffOpLattice σ hσ) (by
    intro L M h
    exact mapCompletedPseudoDiffOpLattice_leftHomothetic σ hσ h)

/-- Identity coefficient automorphism acts trivially on projective lattice classes. -/
theorem mapDifferentialVariationalProjectiveBuildingCarrierCoefficients_refl
    (x : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    mapDifferentialVariationalProjectiveBuildingCarrierCoefficients
      (RingEquiv.refl K) refl_deriv_comm x = x := by
  induction x using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      change (mapCompletedPseudoDiffOpLattice (RingEquiv.refl K)
        refl_deriv_comm L).LeftHomothetic L
      rw [mapCompletedPseudoDiffOpLattice_refl]
      exact CompletedPseudoDiffOpLattice.LeftHomothetic.refl L

/-- Coefficient actions compose functorially on projective lattice classes. -/
theorem mapDifferentialVariationalProjectiveBuildingCarrierCoefficients_trans
    (σ τ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (hτ : ∀ a : K, τ (a′) = (τ a)′)
    (x : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    mapDifferentialVariationalProjectiveBuildingCarrierCoefficients τ hτ
        (mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ x) =
      mapDifferentialVariationalProjectiveBuildingCarrierCoefficients
        (σ.trans τ) (trans_deriv_comm σ τ hσ hτ) x := by
  induction x using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      change (mapCompletedPseudoDiffOpLattice τ hτ
          (mapCompletedPseudoDiffOpLattice σ hσ L)).LeftHomothetic
        (mapCompletedPseudoDiffOpLattice (σ.trans τ)
          (trans_deriv_comm σ τ hσ hτ) L)
      rw [mapCompletedPseudoDiffOpLattice_trans]
      exact CompletedPseudoDiffOpLattice.LeftHomothetic.refl _

section MatrixAction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Right row action of an invertible completed-skew matrix as a left-linear equivalence. -/
def completedPseudoDiffOpMatrixLinearEquiv
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) :
    (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K) where
  toFun v := Matrix.vecMul v A
  invFun v := Matrix.vecMul v (↑(A⁻¹) : Matrix ι ι (CompletedPseudoDiffOp K))
  left_inv v := by
    change Matrix.vecMul (Matrix.vecMul v
      (A : Matrix ι ι (CompletedPseudoDiffOp K)))
        (↑(A⁻¹) : Matrix ι ι (CompletedPseudoDiffOp K)) = v
    rw [Matrix.vecMul_vecMul]
    have h : (A : Matrix ι ι (CompletedPseudoDiffOp K)) *
        (↑(A⁻¹) : Matrix ι ι (CompletedPseudoDiffOp K)) = 1 :=
      Units.mul_inv A
    rw [h, Matrix.vecMul_one]
  right_inv v := by
    change Matrix.vecMul (Matrix.vecMul v
      (↑(A⁻¹) : Matrix ι ι (CompletedPseudoDiffOp K)))
        (A : Matrix ι ι (CompletedPseudoDiffOp K)) = v
    rw [Matrix.vecMul_vecMul]
    have h : (↑(A⁻¹) : Matrix ι ι (CompletedPseudoDiffOp K)) *
        (A : Matrix ι ι (CompletedPseudoDiffOp K)) = 1 :=
      Units.inv_mul A
    rw [h, Matrix.vecMul_one]
  map_add' v w := by
    exact (Matrix.vecMulLinear (A : Matrix ι ι (CompletedPseudoDiffOp K))).map_add v w
  map_smul' c v := by
    exact (Matrix.vecMulLinear (A : Matrix ι ι (CompletedPseudoDiffOp K))).map_smul c v

@[simp]
theorem completedPseudoDiffOpMatrixLinearEquiv_apply
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ)
    (v : ι → CompletedPseudoDiffOp K) :
    completedPseudoDiffOpMatrixLinearEquiv A v = Matrix.vecMul v A := rfl

/-- Identity matrix induces the identity linear equivalence. -/
theorem completedPseudoDiffOpMatrixLinearEquiv_one :
    completedPseudoDiffOpMatrixLinearEquiv
        (1 : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) =
      LinearEquiv.refl (CompletedPseudoDiffOp K) _ := by
  ext v i
  exact congrFun (Matrix.vecMul_one v) i

/-- Matrix multiplication agrees with successive right row actions. -/
theorem completedPseudoDiffOpMatrixLinearEquiv_mul
    (A B : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) :
    (completedPseudoDiffOpMatrixLinearEquiv A).trans
        (completedPseudoDiffOpMatrixLinearEquiv B) =
      completedPseudoDiffOpMatrixLinearEquiv (A * B) := by
  ext v i
  exact congrFun (Matrix.vecMul_vecMul v
    (A : Matrix ι ι (CompletedPseudoDiffOp K))
    (B : Matrix ι ι (CompletedPseudoDiffOp K))) i

/-- Entrywise coefficient transport of invertible completed-skew matrices. -/
def mapCompletedPseudoDiffOpMatrixUnit
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    (Matrix ι ι (CompletedPseudoDiffOp K))ˣ →*
      (Matrix ι ι (CompletedPseudoDiffOp K))ˣ :=
  Units.map
    ((mapCompletedPseudoRingEquiv σ hσ).toRingHom.mapMatrix).toMonoidHom

@[simp]
theorem mapCompletedPseudoDiffOpMatrixUnit_val
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) :
    (mapCompletedPseudoDiffOpMatrixUnit σ hσ A :
        Matrix ι ι (CompletedPseudoDiffOp K)) =
      (A : Matrix ι ι (CompletedPseudoDiffOp K)).map
        (mapCompletedPseudoRingEquiv σ hσ) := rfl

omit [DecidableEq ι] in
/-- Coefficient transport commutes with right row multiplication after transporting every matrix
entry. -/
theorem mapCompletedPseudoVecLinearMap_vecMul
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (v : ι → CompletedPseudoDiffOp K)
    (A : Matrix ι ι (CompletedPseudoDiffOp K)) :
    mapCompletedPseudoVecLinearMap σ hσ (Matrix.vecMul v A) =
      Matrix.vecMul (mapCompletedPseudoVecLinearMap σ hσ v)
        (A.map (mapCompletedPseudoRingEquiv σ hσ)) := by
  funext j
  change mapCompletedPseudoRingEquiv σ hσ (∑ i, v i * A i j) =
    ∑ i, mapCompletedPseudoRingEquiv σ hσ (v i) *
      mapCompletedPseudoRingEquiv σ hσ (A i j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (mapCompletedPseudoRingEquiv σ hσ).map_mul (v i) (A i j)

/-- Coefficient transport and invertible-matrix transport commute after applying the coefficient
automorphism to the matrix. -/
theorem mapCompletedPseudoDiffOpLattice_matrix
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLattice σ hσ
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A) L) =
      mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpMatrixLinearEquiv
          (mapCompletedPseudoDiffOpMatrixUnit σ hσ A))
        (mapCompletedPseudoDiffOpLattice σ hσ L) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLattice_iff,
    mem_mapCompletedPseudoDiffOpLatticeLinear_iff]
  constructor
  · rintro ⟨z, hz, hyz⟩
    rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ x,
      ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyz, ← hzx]
    exact (mapCompletedPseudoVecLinearMap_vecMul σ hσ x A).symm
  · rintro ⟨z, hz, hyz⟩
    rw [mem_mapCompletedPseudoDiffOpLattice_iff] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨completedPseudoDiffOpMatrixLinearEquiv A x,
      ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyz, ← hzx]
    exact mapCompletedPseudoVecLinearMap_vecMul σ hσ x A



/-- Action of an invertible completed-skew matrix on projective lattice classes. -/
def mapDifferentialVariationalProjectiveBuildingCarrierMatrix
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) :
    DifferentialVariationalProjectiveBuildingCarrier K ι →
      DifferentialVariationalProjectiveBuildingCarrier K ι :=
  mapDifferentialVariationalProjectiveBuildingCarrier
    (completedPseudoDiffOpMatrixLinearEquiv A)

/-- Identity matrix acts trivially on projective lattice classes. -/
theorem mapDifferentialVariationalProjectiveBuildingCarrierMatrix_one
    (x : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    mapDifferentialVariationalProjectiveBuildingCarrierMatrix
        (1 : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) x = x := by
  rw [mapDifferentialVariationalProjectiveBuildingCarrierMatrix,
    completedPseudoDiffOpMatrixLinearEquiv_one]
  exact mapDifferentialVariationalProjectiveBuildingCarrier_refl x

/-- Successive matrix actions multiply in row-action order. -/
theorem mapDifferentialVariationalProjectiveBuildingCarrierMatrix_mul
    (A B : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ)
    (x : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    mapDifferentialVariationalProjectiveBuildingCarrierMatrix B
        (mapDifferentialVariationalProjectiveBuildingCarrierMatrix A x) =
      mapDifferentialVariationalProjectiveBuildingCarrierMatrix (A * B) x := by
  change mapDifferentialVariationalProjectiveBuildingCarrier
      (completedPseudoDiffOpMatrixLinearEquiv B)
      (mapDifferentialVariationalProjectiveBuildingCarrier
        (completedPseudoDiffOpMatrixLinearEquiv A) x) =
    mapDifferentialVariationalProjectiveBuildingCarrier
      (completedPseudoDiffOpMatrixLinearEquiv (A * B)) x
  rw [mapDifferentialVariationalProjectiveBuildingCarrier_trans,
    completedPseudoDiffOpMatrixLinearEquiv_mul]

/-- Matrix and coefficient actions commute after coefficientwise transport of the matrix. -/
theorem mapDifferentialVariationalProjectiveBuildingCarrierCoefficients_matrix
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ)
    (x : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ
        (mapDifferentialVariationalProjectiveBuildingCarrierMatrix A x) =
      mapDifferentialVariationalProjectiveBuildingCarrierMatrix
        (mapCompletedPseudoDiffOpMatrixUnit σ hσ A)
        (mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ x) := by
  induction x using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      change (mapCompletedPseudoDiffOpLattice σ hσ
          (mapCompletedPseudoDiffOpLatticeLinear
            (completedPseudoDiffOpMatrixLinearEquiv A) L)).LeftHomothetic
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv
            (mapCompletedPseudoDiffOpMatrixUnit σ hσ A))
          (mapCompletedPseudoDiffOpLattice σ hσ L))
      rw [mapCompletedPseudoDiffOpLattice_matrix]
      exact CompletedPseudoDiffOpLattice.LeftHomothetic.refl _

/-- Literal semilinear projective action `v ↦ σ(v) A`. -/
def differentialVariationalProjectiveSemilinearAction
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) :
    DifferentialVariationalProjectiveBuildingCarrier K ι →
      DifferentialVariationalProjectiveBuildingCarrier K ι :=
  fun x => mapDifferentialVariationalProjectiveBuildingCarrierMatrix A
    (mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ x)

/-- Identity coefficient map and identity matrix give the identity semilinear action. -/
theorem differentialVariationalProjectiveSemilinearAction_refl_one
    (x : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    differentialVariationalProjectiveSemilinearAction
      (RingEquiv.refl K) refl_deriv_comm
      (1 : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) x = x := by
  rw [differentialVariationalProjectiveSemilinearAction,
    mapDifferentialVariationalProjectiveBuildingCarrierCoefficients_refl,
    mapDifferentialVariationalProjectiveBuildingCarrierMatrix_one]

/-- Exact semidirect-product composition law for `v ↦ σ(v) A`. -/
theorem differentialVariationalProjectiveSemilinearAction_trans
    (σ τ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (hτ : ∀ a : K, τ (a′) = (τ a)′)
    (A B : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ)
    (x : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    differentialVariationalProjectiveSemilinearAction τ hτ B
        (differentialVariationalProjectiveSemilinearAction σ hσ A x) =
      differentialVariationalProjectiveSemilinearAction (σ.trans τ)
        (trans_deriv_comm σ τ hσ hτ)
        (mapCompletedPseudoDiffOpMatrixUnit τ hτ A * B) x := by
  unfold differentialVariationalProjectiveSemilinearAction
  rw [mapDifferentialVariationalProjectiveBuildingCarrierCoefficients_matrix,
    mapDifferentialVariationalProjectiveBuildingCarrierMatrix_mul,
    mapDifferentialVariationalProjectiveBuildingCarrierCoefficients_trans]

end MatrixAction

end
end GaloisForLFunctions.HTGeometry.DiffOp
