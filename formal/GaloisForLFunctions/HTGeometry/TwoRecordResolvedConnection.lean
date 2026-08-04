import GaloisForLFunctions.Core

/-!
# Resolved connection of two source records

Two real records `mass` and `clock` determine the alternating coefficient

`mass i * clock j - mass j * clock i`.

The unnormalized coefficient need not be a scalar cocycle.  If every clock is nonzero, however,
the normalized coefficient is a vertex coboundary and the determinant-one triangular source frames
have exactly flat transitions.  This file proves that generic algebra, the resulting covariant
square-zero law, and the exact graph-relation composition law.

Nothing here is arithmetic or spectral.  The theorem isolates the reusable source-frame mechanism
behind the BV--Wold Route-R construction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- Alternating connection determined by two labelled real source records. -/
def twoRecordConnection (mass clock : ι → ℝ) (i j : ι) : ℝ :=
  mass i * clock j - mass j * clock i

@[simp]
theorem twoRecordConnection_self (mass clock : ι → ℝ) (i : ι) :
    twoRecordConnection mass clock i i = 0 := by
  simp [twoRecordConnection]

theorem twoRecordConnection_swap (mass clock : ι → ℝ) (i j : ι) :
    twoRecordConnection mass clock j i = -twoRecordConnection mass clock i j := by
  simp only [twoRecordConnection]
  ring

/-- The clock-normalized source potential. -/
def twoRecordNormalizedPotential (mass clock : ι → ℝ) (i : ι) : ℝ :=
  mass i / clock i

/-- Normalization turns the alternating connection into a vertex coboundary. -/
theorem twoRecordConnection_div_clocks_eq_potential_sub
    (mass clock : ι → ℝ) (hclock : ∀ i, clock i ≠ 0) (i j : ι) :
    twoRecordConnection mass clock i j / (clock i * clock j) =
      twoRecordNormalizedPotential mass clock i -
        twoRecordNormalizedPotential mass clock j := by
  rw [twoRecordConnection, twoRecordNormalizedPotential,
    twoRecordNormalizedPotential]
  field_simp [hclock i, hclock j]

/-- Weighted cocycle identity retained before normalization. -/
theorem twoRecordConnection_weighted_cocycle
    (mass clock : ι → ℝ) (i j k : ι) :
    clock i * twoRecordConnection mass clock j k +
        clock k * twoRecordConnection mass clock i j =
      clock j * twoRecordConnection mass clock i k := by
  rw [twoRecordConnection, twoRecordConnection, twoRecordConnection]
  ring

/-- Additive defect of the scalar connection on an oriented triangle. -/
def twoRecordTriangleDefect
    (mass clock : ι → ℝ) (i j k : ι) : ℝ :=
  twoRecordConnection mass clock i j +
    twoRecordConnection mass clock j k -
      twoRecordConnection mass clock i k

/-- Exponentiated scalar reporter obtained after deleting the diagonal clock characters. -/
def twoRecordScalarTransport
    (mass clock : ι → ℝ) (a : ℝ) (i j : ι) : ℝ :=
  Real.exp (a * twoRecordConnection mass clock i j)

/-- On a triangle with nonzero additive defect, scalar multiplicative flatness is exactly the
neutral-rate condition. -/
theorem twoRecordScalarTransport_triangle_flat_iff
    (mass clock : ι → ℝ) (i j k : ι)
    (hdefect : twoRecordTriangleDefect mass clock i j k ≠ 0) (a : ℝ) :
    twoRecordScalarTransport mass clock a i j *
        twoRecordScalarTransport mass clock a j k =
      twoRecordScalarTransport mass clock a i k ↔
    a = 0 := by
  rw [twoRecordScalarTransport, twoRecordScalarTransport,
    twoRecordScalarTransport, ← Real.exp_add, Real.exp_injective.eq_iff]
  have hrearrange :
      a * twoRecordConnection mass clock i j +
          a * twoRecordConnection mass clock j k =
        a * twoRecordConnection mass clock i k ↔
      a * twoRecordTriangleDefect mass clock i j k = 0 := by
    rw [twoRecordTriangleDefect]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  rw [hrearrange, mul_eq_zero]
  simp [hdefect]

/-! ## Determinant-one triangular resolution -/

/-- Triangular frame carrying the clock on its diagonal and the second record off diagonal. -/
def twoRecordResolvedFrame (mass clock : ι → ℝ) (a : ℝ) (i : ι) :
    (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun z :=
    (((((1 / clock i : ℝ) : ℂ) * z.1 +
      ((a * mass i : ℝ) : ℂ) * z.2)),
      (clock i : ℂ) * z.2)
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' c x := by
    ext <;> simp <;> ring

/-- Explicit inverse of the triangular source frame. -/
def twoRecordResolvedFrameInv (mass clock : ι → ℝ) (a : ℝ) (i : ι) :
    (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun z :=
    ((((clock i : ℂ) * z.1 - ((a * mass i : ℝ) : ℂ) * z.2)),
      (((1 / clock i : ℝ) : ℂ) * z.2))
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' c x := by
    ext <;> simp <;> ring

theorem twoRecordResolvedFrameInv_frame
    (mass clock : ι → ℝ) (hclock : ∀ i, clock i ≠ 0)
    (a : ℝ) (i : ι) (z : ℂ × ℂ) :
    twoRecordResolvedFrameInv mass clock a i
        (twoRecordResolvedFrame mass clock a i z) = z := by
  ext <;> simp only [twoRecordResolvedFrame, twoRecordResolvedFrameInv,
    LinearMap.coe_mk, AddHom.coe_mk]
  · push_cast
    field_simp [hclock i]
    ring
  · push_cast
    field_simp [hclock i]

theorem twoRecordResolvedFrame_frameInv
    (mass clock : ι → ℝ) (hclock : ∀ i, clock i ≠ 0)
    (a : ℝ) (i : ι) (z : ℂ × ℂ) :
    twoRecordResolvedFrame mass clock a i
        (twoRecordResolvedFrameInv mass clock a i z) = z := by
  ext <;> simp only [twoRecordResolvedFrame, twoRecordResolvedFrameInv,
    LinearMap.coe_mk, AddHom.coe_mk]
  · push_cast
    field_simp [hclock i]
    ring
  · push_cast
    field_simp [hclock i]

/-- Resolved transition between two source frames. -/
def twoRecordResolvedTransport
    (mass clock : ι → ℝ) (a : ℝ) (i j : ι) :
    (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun z :=
    (((((clock i / clock j : ℝ) : ℂ) * z.1 -
      ((a * twoRecordConnection mass clock i j : ℝ) : ℂ) * z.2)),
      (((clock j / clock i : ℝ) : ℂ) * z.2))
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' c x := by
    ext <;> simp <;> ring

/-- The displayed transition is literally the change between source frames. -/
theorem twoRecordResolvedTransport_eq_frameTransition
    (mass clock : ι → ℝ) (hclock : ∀ i, clock i ≠ 0)
    (a : ℝ) (i j : ι) (z : ℂ × ℂ) :
    twoRecordResolvedTransport mass clock a i j z =
      twoRecordResolvedFrameInv mass clock a i
        (twoRecordResolvedFrame mass clock a j z) := by
  ext <;> simp only [twoRecordResolvedTransport, twoRecordResolvedFrame,
    twoRecordResolvedFrameInv, LinearMap.coe_mk, AddHom.coe_mk]
  · push_cast
    rw [twoRecordConnection]
    push_cast
    field_simp [hclock i, hclock j]
    ring
  · push_cast
    field_simp [hclock i, hclock j]

/-- **Resolved source flatness.**  Diagonal clock characters supply the exact mixed term needed
to compose the unnormalized alternating coefficient. -/
theorem twoRecordResolvedTransport_comp
    (mass clock : ι → ℝ) (hclock : ∀ i, clock i ≠ 0)
    (a : ℝ) (i j k : ι) (z : ℂ × ℂ) :
    twoRecordResolvedTransport mass clock a i j
        (twoRecordResolvedTransport mass clock a j k z) =
      twoRecordResolvedTransport mass clock a i k z := by
  have hw := twoRecordConnection_weighted_cocycle mass clock i j k
  have hdiag :
      clock i / clock j * (clock j / clock k) = clock i / clock k := by
    field_simp [hclock i, hclock j, hclock k]
  have hdiag' :
      clock j / clock i * (clock k / clock j) = clock k / clock i := by
    field_simp [hclock i, hclock j, hclock k]
  have hoff :
      clock i / clock j * twoRecordConnection mass clock j k +
          twoRecordConnection mass clock i j * (clock k / clock j) =
        twoRecordConnection mass clock i k := by
    field_simp [hclock j]
    linear_combination hw
  have hdiagc := congrArg (fun x : ℝ => (x : ℂ)) hdiag
  have hdiagc' := congrArg (fun x : ℝ => (x : ℂ)) hdiag'
  have hoffc := congrArg (fun x : ℝ => (x : ℂ)) hoff
  push_cast at hdiagc hdiagc' hoffc
  ext
  · simp only [twoRecordResolvedTransport, LinearMap.coe_mk, AddHom.coe_mk]
    push_cast
    rw [mul_sub, ← mul_assoc, hdiagc]
    linear_combination -(a : ℂ) * hoffc * z.2
  · simp only [twoRecordResolvedTransport, LinearMap.coe_mk, AddHom.coe_mk]
    push_cast
    rw [← mul_assoc, hdiagc']

@[simp]
theorem twoRecordResolvedTransport_self
    (mass clock : ι → ℝ) (hclock : ∀ i, clock i ≠ 0)
    (a : ℝ) (i : ι) (z : ℂ × ℂ) :
    twoRecordResolvedTransport mass clock a i i z = z := by
  ext <;> simp [twoRecordResolvedTransport, twoRecordConnection, hclock i]

/-! ## Resolved covariant differential -/

abbrev TwoRecordResolvedZeroCochain (ι : Type*) := ι → ℂ × ℂ
abbrev TwoRecordResolvedOneCochain (ι : Type*) := ι → ι → ℂ × ℂ
abbrev TwoRecordResolvedTwoCochain (ι : Type*) := ι → ι → ι → ℂ × ℂ

def twoRecordResolvedCovariantD0 (mass clock : ι → ℝ) (a : ℝ) :
    TwoRecordResolvedZeroCochain ι →ₗ[ℂ] TwoRecordResolvedOneCochain ι where
  toFun f i j := twoRecordResolvedTransport mass clock a i j (f j) - f i
  map_add' f g := by
    funext i j
    simp only [Pi.add_apply, map_add]
    module
  map_smul' c f := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]
    module

def twoRecordResolvedCovariantD1 (mass clock : ι → ℝ) (a : ℝ) :
    TwoRecordResolvedOneCochain ι →ₗ[ℂ] TwoRecordResolvedTwoCochain ι where
  toFun omega i j k :=
    twoRecordResolvedTransport mass clock a i j (omega j k) -
      omega i k + omega i j
  map_add' omega eta := by
    funext i j k
    simp only [Pi.add_apply, map_add]
    module
  map_smul' c omega := by
    funext i j k
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]
    module

/-- Flat source-frame composition makes the resolved covariant square vanish for every rate. -/
theorem twoRecordResolvedCovariantD1_comp_D0_apply
    (mass clock : ι → ℝ) (hclock : ∀ i, clock i ≠ 0)
    (a : ℝ) (f : TwoRecordResolvedZeroCochain ι) (i j k : ι) :
    twoRecordResolvedCovariantD1 mass clock a
        (twoRecordResolvedCovariantD0 mass clock a f) i j k = 0 := by
  change
    twoRecordResolvedTransport mass clock a i j
          (twoRecordResolvedTransport mass clock a j k (f k) - f j) -
        (twoRecordResolvedTransport mass clock a i k (f k) - f i) +
      (twoRecordResolvedTransport mass clock a i j (f j) - f i) = 0
  rw [map_sub, twoRecordResolvedTransport_comp mass clock hclock]
  module

/-! ## Relation-valued reciprocity -/

/-- Graph relation of one fully labelled resolved transition. -/
def twoRecordResolvedRelation
    (mass clock : ι → ℝ) (a : ℝ) (i j : ι) :
    Submodule ℂ ((ℂ × ℂ) × (ℂ × ℂ)) :=
  (twoRecordResolvedTransport mass clock a i j).graph

/-- Exact relational composition of the label-retaining graph relations. -/
theorem twoRecordResolvedRelation_comp_iff
    (mass clock : ι → ℝ) (hclock : ∀ i, clock i ≠ 0)
    (a : ℝ) (i j k : ι) (x z : ℂ × ℂ) :
    (∃ y : ℂ × ℂ,
        (x, y) ∈ twoRecordResolvedRelation mass clock a j k ∧
        (y, z) ∈ twoRecordResolvedRelation mass clock a i j) ↔
      (x, z) ∈ twoRecordResolvedRelation mass clock a i k := by
  constructor
  · rintro ⟨y, hy, hz⟩
    change y = twoRecordResolvedTransport mass clock a j k x at hy
    change z = twoRecordResolvedTransport mass clock a i j y at hz
    change z = twoRecordResolvedTransport mass clock a i k x
    rw [hy] at hz
    exact hz.trans (twoRecordResolvedTransport_comp mass clock hclock a i j k x)
  · intro hx
    refine ⟨twoRecordResolvedTransport mass clock a j k x, ?_, ?_⟩
    · change twoRecordResolvedTransport mass clock a j k x =
        twoRecordResolvedTransport mass clock a j k x
      rfl
    · change z = twoRecordResolvedTransport mass clock a i j
        (twoRecordResolvedTransport mass clock a j k x)
      change z = twoRecordResolvedTransport mass clock a i k x at hx
      rw [hx, twoRecordResolvedTransport_comp mass clock hclock a i j k x]

end

end GaloisForLFunctions.HTGeometry
