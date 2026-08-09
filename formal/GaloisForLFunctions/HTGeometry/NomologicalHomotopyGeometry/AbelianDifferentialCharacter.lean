import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Abelian differential-character higher holonomy and transgression

Smooth chains are represented by an abstract four-term additive chain complex.  A differential
character is an additive character on cycles satisfying the curvature boundary formula through a
coefficient quotient map.  Discreteness/locality is isolated as the standard small-chain
vanishing principle.  The formal consequences are closed curvature, lattice periods, exact
homology classification of same-curvature ambiguity, and signed transgression to a degree-two
character with the swept-cycle holonomy identity.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.AbelianDifferentialCharacter

/-- Four consecutive smooth-chain degrees around a degree-`n` differential character. -/
structure ChainComplex (Cnext Cn Cprev Cbelow : Type*)
    [AddCommGroup Cnext] [AddCommGroup Cn]
    [AddCommGroup Cprev] [AddCommGroup Cbelow] where
  boundaryNext : Cnext →+ Cn
  boundary : Cn →+ Cprev
  boundaryPrev : Cprev →+ Cbelow
  boundary_sq_next : boundary.comp boundaryNext = 0
  boundary_sq : boundaryPrev.comp boundary = 0

namespace ChainComplex

variable {Cnext Cn Cprev Cbelow : Type*}
variable [AddCommGroup Cnext] [AddCommGroup Cn]
variable [AddCommGroup Cprev] [AddCommGroup Cbelow]
variable (C : ChainComplex Cnext Cn Cprev Cbelow)

/-- Smooth `(n-1)`-cycles. -/
abbrev cycles := C.boundaryPrev.ker

/-- Smooth `n`-cycles. -/
abbrev upperCycles := C.boundary.ker

/-- Boundary of an `n`-chain, regarded as an `(n-1)`-cycle. -/
def boundaryCycle : Cn →+ C.cycles where
  toFun c := ⟨C.boundary c, by
    have h := congrArg (fun f : Cn →+ Cbelow => f c) C.boundary_sq
    simpa using h⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Boundaries inside the cycle group. -/
def boundariesInCycles : AddSubgroup C.cycles :=
  C.boundaryCycle.range

/-- Integral homology in degree `n-1`. -/
abbrev homology := C.cycles ⧸ C.boundariesInCycles

/-- Canonical projection from cycles to homology. -/
def homologyClass : C.cycles →+ C.homology :=
  QuotientAddGroup.mk' C.boundariesInCycles

/-- Boundary classes vanish in homology. -/
@[simp]
theorem homologyClass_boundaryCycle (c : Cn) :
    C.homologyClass (C.boundaryCycle c) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨c, rfl⟩

end ChainComplex

/-- Degree-`n` abelian differential character with coefficient quotient `V → Q`.

`small_chain_vanishing` is the exact use of lattice discreteness and arbitrarily small smooth
chains in the standard closed-curvature proof.
-/
structure DifferentialCharacter
    (Cnext Cn Cprev Cbelow V Q : Type*)
    [AddCommGroup Cnext] [AddCommGroup Cn]
    [AddCommGroup Cprev] [AddCommGroup Cbelow]
    [AddCommGroup V] [AddCommGroup Q]
    (chains : ChainComplex Cnext Cn Cprev Cbelow) where
  modLattice : V →+ Q
  curvatureIntegral : Cn →+ V
  character : chains.cycles →+ Q
  boundary_formula : ∀ c,
    character (chains.boundaryCycle c) = modLattice (curvatureIntegral c)
  small_chain_vanishing :
    (∀ b : Cnext, modLattice (curvatureIntegral (chains.boundaryNext b)) = 0) →
      curvatureIntegral.comp chains.boundaryNext = 0

namespace DifferentialCharacter

variable {Cnext Cn Cprev Cbelow V Q : Type*}
variable [AddCommGroup Cnext] [AddCommGroup Cn]
variable [AddCommGroup Cprev] [AddCommGroup Cbelow]
variable [AddCommGroup V] [AddCommGroup Q]
variable {chains : ChainComplex Cnext Cn Cprev Cbelow}
variable (h : DifferentialCharacter Cnext Cn Cprev Cbelow V Q chains)

/-- Curvature is closed: its integral on every boundary vanishes. -/
theorem curvature_closed :
    h.curvatureIntegral.comp chains.boundaryNext = 0 := by
  apply h.small_chain_vanishing
  intro b
  rw [← h.boundary_formula]
  have hsquare := congrArg (fun f : Cnext →+ Cprev => f b) chains.boundary_sq_next
  have hboundary : chains.boundaryCycle (chains.boundaryNext b) = 0 := by
    apply Subtype.ext
    exact hsquare
  rw [hboundary, map_zero]

/-- Every closed `n`-cycle has curvature integral in the lattice kernel. -/
theorem curvature_has_lattice_periods (z : chains.upperCycles) :
    h.curvatureIntegral z ∈ h.modLattice.ker := by
  rw [AddMonoidHom.mem_ker]
  rw [← h.boundary_formula]
  have hz : chains.boundaryCycle (z : Cn) = 0 := by
    ext
    exact z.property
  rw [hz, map_zero]

/-- Difference of two same-curvature characters. -/
def flatDifference
    (h' : DifferentialCharacter Cnext Cn Cprev Cbelow V Q chains) :
    chains.cycles →+ Q :=
  h.character - h'.character

/-- Same-curvature difference vanishes on all boundaries. -/
theorem boundaries_le_flatDifference_ker
    (h' : DifferentialCharacter Cnext Cn Cprev Cbelow V Q chains)
    (hmod : h.modLattice = h'.modLattice)
    (hsame : h.curvatureIntegral = h'.curvatureIntegral) :
    chains.boundariesInCycles ≤ (h.flatDifference h').ker := by
  rintro _ ⟨c, rfl⟩
  rw [AddMonoidHom.mem_ker, flatDifference, AddMonoidHom.sub_apply,
    h.boundary_formula, h'.boundary_formula, hmod, hsame, sub_self]

/-- Same-curvature ambiguity descends canonically to integral homology. -/
def flatHomologyCharacter
    (h' : DifferentialCharacter Cnext Cn Cprev Cbelow V Q chains)
    (hmod : h.modLattice = h'.modLattice)
    (hsame : h.curvatureIntegral = h'.curvatureIntegral) :
    chains.homology →+ Q :=
  QuotientAddGroup.lift chains.boundariesInCycles (h.flatDifference h')
    (h.boundaries_le_flatDifference_ker h' hmod hsame)

@[simp]
theorem flatHomologyCharacter_mk
    (h' : DifferentialCharacter Cnext Cn Cprev Cbelow V Q chains)
    (hmod : h.modLattice = h'.modLattice)
    (hsame : h.curvatureIntegral = h'.curvatureIntegral) (z : chains.cycles) :
    h.flatHomologyCharacter h' hmod hsame (chains.homologyClass z) =
      h.character z - h'.character z :=
  rfl

/-- Add a flat homology character without changing curvature. -/
def addFlatCharacter (f : chains.homology →+ Q) :
    DifferentialCharacter Cnext Cn Cprev Cbelow V Q chains where
  modLattice := h.modLattice
  curvatureIntegral := h.curvatureIntegral
  character := h.character + f.comp chains.homologyClass
  boundary_formula c := by
    rw [AddMonoidHom.add_apply, AddMonoidHom.comp_apply,
      chains.homologyClass_boundaryCycle, map_zero, add_zero, h.boundary_formula]
  small_chain_vanishing := h.small_chain_vanishing

@[simp]
theorem addFlatCharacter_curvature (f : chains.homology →+ Q) :
    (h.addFlatCharacter f).curvatureIntegral = h.curvatureIntegral :=
  rfl

/-- Nonzero flat homology characters give distinct higher holonomy with identical curvature. -/
theorem addFlatCharacter_ne_of_ne_zero (f : chains.homology →+ Q) (hf : f ≠ 0) :
    (h.addFlatCharacter f).character ≠ h.character := by
  intro heq
  apply hf
  ext z
  have hz := congrArg (fun g : chains.cycles →+ Q => g z) heq
  simp only [addFlatCharacter, AddMonoidHom.add_apply, AddMonoidHom.comp_apply] at hz
  apply add_left_cancel (a := h.character z)
  simpa [ChainComplex.homologyClass] using hz

end DifferentialCharacter

section Transgression

variable {SCnext SCn SCprev SCbelow TCnext TCn TCprev TCbelow V Q : Type*}
variable [AddCommGroup SCnext] [AddCommGroup SCn]
variable [AddCommGroup SCprev] [AddCommGroup SCbelow]
variable [AddCommGroup TCnext] [AddCommGroup TCn]
variable [AddCommGroup TCprev] [AddCommGroup TCbelow]
variable [AddCommGroup V] [AddCommGroup Q]

variable (S : ChainComplex SCnext SCn SCprev SCbelow)
variable (T : ChainComplex TCnext TCn TCprev TCbelow)

/-- Chain-level fibre-integration/transgression data.  `sign` is `(-1)^(n-2)`; its square-one law
is the orientation-sign cancellation in the boundary formula. -/
structure TransgressionData where
  sign : ℤ
  sign_sq : sign * sign = 1
  sweepCycles : T.cycles →+ S.cycles
  sweepChains : TCn →+ SCn
  boundary_compat : ∀ c,
    sweepCycles (T.boundaryCycle c) = sign • S.boundaryCycle (sweepChains c)

namespace TransgressionData

variable {S T}
variable (X : TransgressionData S T)

/-- Transgressed curvature integral, i.e. fibre integration over the probe. -/
def curvatureIntegral
    (h : DifferentialCharacter SCnext SCn SCprev SCbelow V Q S) : TCn →+ V :=
  h.curvatureIntegral.comp X.sweepChains

/-- Transgressed degree-two character on loop cycles. -/
def character
    (h : DifferentialCharacter SCnext SCn SCprev SCbelow V Q S) : T.cycles →+ Q :=
  X.sign • h.character.comp X.sweepCycles

/-- Higher curvature becomes ordinary boundary/loop holonomy after transgression. -/
theorem boundary_formula
    (h : DifferentialCharacter SCnext SCn SCprev SCbelow V Q S) (c : TCn) :
    X.character h (T.boundaryCycle c) =
      h.modLattice (X.curvatureIntegral h c) := by
  change X.sign • h.character (X.sweepCycles (T.boundaryCycle c)) =
    h.modLattice (h.curvatureIntegral (X.sweepChains c))
  rw [X.boundary_compat, map_zsmul, ← mul_zsmul, X.sign_sq, one_zsmul,
    h.boundary_formula]

/-- Loop holonomy is the original higher character evaluated on the signed swept cycle. -/
theorem loop_swept_cycle
    (h : DifferentialCharacter SCnext SCn SCprev SCbelow V Q S) (z : T.cycles) :
    X.character h z = X.sign • h.character (X.sweepCycles z) :=
  rfl

/-- Transgression sends flat ambiguity to flat loop-holonomy ambiguity. -/
theorem flat_difference_transgresses
    (h h' : DifferentialCharacter SCnext SCn SCprev SCbelow V Q S) (z : T.cycles) :
    X.character h z - X.character h' z =
      X.sign • (h.character (X.sweepCycles z) - h'.character (X.sweepCycles z)) := by
  change X.sign • h.character (X.sweepCycles z) -
      X.sign • h'.character (X.sweepCycles z) = _
  exact (zsmul_sub _ _ X.sign).symm

end TransgressionData

end Transgression

end HTGeometry.NomologicalHomotopyGeometry.AbelianDifferentialCharacter
