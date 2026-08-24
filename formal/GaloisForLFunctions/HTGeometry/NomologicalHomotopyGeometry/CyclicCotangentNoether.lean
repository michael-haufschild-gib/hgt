import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicActionNoether
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Cyclic cotangent Noether law of a square-zero linear source

Every square-zero linear differential has a canonical cotangent double.  The source and its
algebraic dual carry the evaluation pairing, while the differential acts on the dual by
precomposition.  This makes the doubled differential cyclic and supplies a linear
`CyclicMaurerCartanLaw` whose Noether identity is the original square-zero law.

The construction is deliberately generic.  In arithmetic applications, existence of a cyclic
action therefore has no selecting force by itself.  Mathematical content must enter through a
source-natural identification of a fixed physical reporter and fixed source boundaries with the
variational and gauge directions of this law.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.CyclicCotangentNoether

open CyclicActionNoether

universe u v

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]

/-- Cotangent doubling of a linear source. -/
abbrev CotangentFields (k : Type u) (V : Type v)
    [Field k] [AddCommGroup V] [Module k V] :=
  V × Module.Dual k V

/-- Canonical symmetric evaluation pairing on a source and its algebraic dual. -/
def cotangentPairing :
    CotangentFields k V →ₗ[k] CotangentFields k V →ₗ[k] k :=
  LinearMap.mk₂ k (fun x y => x.2 y.1 + y.2 x.1)
    (by intro x y z; simp [add_left_comm, add_comm])
    (by intro c x y; simp [mul_add])
    (by intro x y z; simp [add_left_comm, add_comm])
    (by intro c x y; simp [mul_add])

@[simp] theorem cotangentPairing_apply
    (x y : CotangentFields k V) :
    cotangentPairing x y = x.2 y.1 + y.2 x.1 :=
  rfl

theorem cotangentPairing_symm
    (x y : CotangentFields k V) :
    cotangentPairing x y = cotangentPairing y x := by
  simp [add_comm]

/-- The canonical cotangent pairing separates every doubled source vector. -/
theorem cotangentPairing_nondegenerate
    (z : CotangentFields k V)
    (h : ∀ η, cotangentPairing η z = 0) :
    z = 0 := by
  have hz1_all : ∀ φ : Module.Dual k V, φ z.1 = 0 := by
    intro φ
    simpa using h ((0 : V), φ)
  have hz1 : z.1 = 0 :=
    (Module.forall_dual_apply_eq_zero_iff k z.1).mp hz1_all
  have hz2_all : ∀ x : V, z.2 x = 0 := by
    intro x
    simpa using h (x, (0 : Module.Dual k V))
  have hz2 : z.2 = 0 := by
    ext x
    exact hz2_all x
  exact Prod.ext hz1 hz2

/-- Dual differential obtained by precomposition. -/
def dualDifferential (d : Module.End k V) :
    Module.End k (Module.Dual k V) where
  toFun φ := φ.comp d
  map_add' := by
    intro φ ψ
    ext x
    simp
  map_smul' := by
    intro c φ
    ext x
    simp

@[simp] theorem dualDifferential_apply
    (d : Module.End k V) (φ : Module.Dual k V) (x : V) :
    dualDifferential d φ x = φ (d x) :=
  rfl

/-- Differential on the cotangent double. -/
def cotangentDifferential (d : Module.End k V) :
    Module.End k (CotangentFields k V) :=
  d.prodMap (dualDifferential d)

@[simp] theorem cotangentDifferential_apply
    (d : Module.End k V) (x : CotangentFields k V) :
    cotangentDifferential d x = (d x.1, x.2.comp d) :=
  rfl

/-- Cotangent doubling makes every linear differential cyclic for the evaluation pairing. -/
theorem cotangentDifferential_cyclic
    (d : Module.End k V) (x y : CotangentFields k V) :
    cotangentPairing (cotangentDifferential d x) y =
      cotangentPairing x (cotangentDifferential d y) := by
  rfl

/-- Square-zero is preserved by cotangent doubling. -/
theorem cotangentDifferential_sq
    (d : Module.End k V) (hd : d.comp d = 0) :
    (cotangentDifferential d).comp (cotangentDifferential d) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact LinearMap.congr_fun hd x.1
  · apply LinearMap.ext
    intro y
    change x.2 (d (d y)) = 0
    have hy := LinearMap.congr_fun hd y
    simpa using congrArg x.2 hy

private def unaryMultilinear
    (D : Module.End k (CotangentFields k V))
    (n : PositiveNat) (hn : n.1 = 1) :
    MultilinearMap k (fun _ : Fin n.1 ↦ CotangentFields k V)
      (CotangentFields k V) :=
  MultilinearMap.mk'
    (fun x => D (x ⟨0, n.2⟩))
    (by
      intro x i y z
      have hi : i = ⟨0, n.2⟩ := by
        apply Fin.ext
        omega
      subst i
      simp)
    (by
      intro x i c y
      have hi : i = ⟨0, n.2⟩ := by
        apply Fin.ext
        omega
      subst i
      simp)

/-- Unary cyclic operation supplied by the doubled differential; all higher operations vanish. -/
def unaryEll
    (D : Module.End k (CotangentFields k V))
    (n : PositiveNat) :
    MultilinearMap k (fun _ : Fin n.1 ↦ CotangentFields k V)
      (CotangentFields k V) :=
  if hn : n.1 = 1 then unaryMultilinear D n hn else 0

@[simp] theorem unaryEll_apply_of_eq_one
    (D : Module.End k (CotangentFields k V))
    (n : PositiveNat) (hn : n.1 = 1)
    (x : Fin n.1 → CotangentFields k V) :
    unaryEll D n x = D (x ⟨0, n.2⟩) := by
  simp [unaryEll, hn, unaryMultilinear]

@[simp] theorem unaryEll_apply_of_ne_one
    (D : Module.End k (CotangentFields k V))
    (n : PositiveNat) (hn : n.1 ≠ 1)
    (x : Fin n.1 → CotangentFields k V) :
    unaryEll D n x = 0 := by
  simp [unaryEll, hn]

private theorem unaryEll_diagonal_cyclic
    (d : Module.End k V) (n : PositiveNat)
    (α η : CotangentFields k V) (i : Fin n.1) :
    cotangentPairing α
        (unaryEll (cotangentDifferential d) n
          (Function.update (fun _ : Fin n.1 ↦ α) i η)) =
      cotangentPairing η
        (unaryEll (cotangentDifferential d) n
          (fun _ : Fin n.1 ↦ α)) := by
  by_cases hn : n.1 = 1
  · rw [unaryEll_apply_of_eq_one _ n hn,
      unaryEll_apply_of_eq_one _ n hn]
    have hi : i = ⟨0, n.2⟩ := by
      apply Fin.ext
      omega
    subst i
    change cotangentPairing α (cotangentDifferential d η) =
      cotangentPairing η (cotangentDifferential d α)
    rw [cotangentPairing_symm]
    exact cotangentDifferential_cyclic d η α
  · simp [unaryEll_apply_of_ne_one _ n hn]

/-- Canonical linear cyclic operations of the cotangent-doubled source. -/
def cotangentCyclicOperations [CharZero k] (d : Module.End k V) :
    CyclicOperations (k := k) (L := CotangentFields k V) where
  pairing := cotangentPairing
  pairing_nondegenerate := cotangentPairing_nondegenerate
  ell := unaryEll (cotangentDifferential d)
  diagonal_cyclic := unaryEll_diagonal_cyclic d

/-- Canonical cyclic Maurer--Cartan law attached to a square-zero linear source. -/
def cotangentCyclicMaurerCartanLaw
    [CharZero k] (d : Module.End k V) (hd : d.comp d = 0) :
    CyclicMaurerCartanLaw (k := k) (L := CotangentFields k V) where
  toCyclicOperations := cotangentCyclicOperations d
  mc := cotangentDifferential d
  twisted := fun _ => cotangentDifferential d
  bianchi := by
    intro α
    exact LinearMap.congr_fun (cotangentDifferential_sq d hd) α
  twisted_square := by
    intro _ _
    exact cotangentDifferential_sq d hd
  twisted_cyclic := by
    intro _ x y
    exact cotangentDifferential_cyclic d x y

@[simp] theorem cotangentCyclicMaurerCartanLaw_mc
    [CharZero k] (d : Module.End k V) (hd : d.comp d = 0)
    (α : CotangentFields k V) :
    (cotangentCyclicMaurerCartanLaw d hd).mc α =
      cotangentDifferential d α :=
  rfl

@[simp] theorem cotangentCyclicMaurerCartanLaw_gaugeVariation
    [CharZero k] (d : Module.End k V) (hd : d.comp d = 0)
    (α ε : CotangentFields k V) :
    gaugeVariation (cotangentCyclicMaurerCartanLaw d hd) α ε =
      cotangentDifferential d ε :=
  rfl

/-- Noether identity of the cotangent theory is exactly annihilation of every source boundary. -/
theorem cotangent_variationalForm_boundary
    [CharZero k] (d : Module.End k V) (hd : d.comp d = 0)
    (α ε : CotangentFields k V) :
    variationalForm (cotangentCyclicMaurerCartanLaw d hd) α
        (cotangentDifferential d ε) = 0 := by
  exact infinitesimal_gauge_invariance
    (cotangentCyclicMaurerCartanLaw d hd) α ε

end HTGeometry.NomologicalHomotopyGeometry.CyclicCotangentNoether
