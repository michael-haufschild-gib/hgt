import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Determinant

/-!
# The D4 weld interface: `ω` as a complex-structure obstruction

This file isolates the formal algebraic surface of the T2 target.  A realized weld is modeled
as a real-linear operator `J` with `J² = -1`; a polarized weld additionally preserves a real
bilinear form `Q`.

The point is deliberately modest: a one-dimensional real carrier cannot support such a `J`,
while the standard real two-plane can.  This records, in Lean, the missing paired dimension
that the draft program describes as the archimedean/F₁ weld obstruction.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- A real-linear complex structure: the algebraic face of a realized weld. -/
structure OmegaComplexStructure (V : Type*) [AddCommGroup V] [Module ℝ V] where
  J : V →ₗ[ℝ] V
  sq : J.comp J = -LinearMap.id

/-- A bilinear form is preserved by `J` when `Q (J x) (J y) = Q x y`. -/
def PreservesBilin {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : LinearMap.BilinForm ℝ V) (J : V →ₗ[ℝ] V) : Prop :=
  ∀ x y, Q (J x) (J y) = Q x y

/-- A complex structure together with preservation of the chosen bilinear form. -/
structure PolarizedOmegaComplexStructure (V : Type*) [AddCommGroup V] [Module ℝ V]
    (Q : LinearMap.BilinForm ℝ V) where
  complex : OmegaComplexStructure V
  preserves : PreservesBilin Q complex.J

namespace OmegaComplexStructure

@[simp]
theorem apply_sq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) (x : V) :
    C.J (C.J x) = -x := by
  have h := congrArg (fun f : V →ₗ[ℝ] V => f x) C.sq
  simpa [LinearMap.comp_apply] using h

/-- Any realized weld operator is injective. -/
theorem injective {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) : Function.Injective C.J := by
  intro x y hxy
  have hJ : C.J (C.J x) = C.J (C.J y) := by rw [hxy]
  have hneg : -x = -y := by
    simpa [C.apply_sq x, C.apply_sq y] using hJ
  exact neg_injective hneg

/-- A realized weld complex structure has no nonzero real eigendirections. -/
theorem eq_zero_of_apply_eq_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) {a : ℝ} {x : V} (h : C.J x = a • x) : x = 0 := by
  have hJJ_smul : C.J (C.J x) = (a * a) • x := by
    calc
      C.J (C.J x) = C.J (a • x) := by rw [h]
      _ = a • C.J x := by rw [map_smul]
      _ = a • (a • x) := by rw [h]
      _ = (a * a) • x := by rw [smul_smul]
  have hquad : (a * a) • x = -x := by
    rw [← hJJ_smul, C.apply_sq x]
  have hzero : (a * a + 1) • x = 0 := by
    calc
      (a * a + 1) • x = (a * a) • x + x := by rw [add_smul, one_smul]
      _ = -x + x := by rw [hquad]
      _ = 0 := by simp
  have hcoef : a * a + 1 ≠ 0 := by
    nlinarith [sq_nonneg a]
  exact (smul_eq_zero.mp hzero).resolve_left hcoef

/-- Equivalently, no nonzero vector is carried by `J` onto a real scalar multiple of itself. -/
theorem apply_ne_smul_of_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) {a : ℝ} {x : V} (hx : x ≠ 0) : C.J x ≠ a • x := by
  intro h
  exact hx (C.eq_zero_of_apply_eq_smul h)

/-- A nonzero vector and its `J`-partner satisfy no nontrivial real linear relation. -/
theorem smul_add_smul_apply_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) {a b : ℝ} {x : V} (hx : x ≠ 0)
    (h : a • x + b • C.J x = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · have ha_smul : a • x = 0 := by simpa [hb] using h
    have ha : a = 0 := by
      exact (smul_eq_zero.mp ha_smul).resolve_right hx
    exact ⟨ha, hb⟩
  · exfalso
    have hb_smul : b • C.J x = (-a) • x := by
      calc
        b • C.J x = -(a • x) := by
          have hcomm : b • C.J x + a • x = 0 := by simpa [add_comm] using h
          exact eq_neg_of_add_eq_zero_left hcomm
        _ = (-a) • x := by rw [neg_smul]
    have hJ : C.J x = ((b⁻¹ * -a) : ℝ) • x := by
      calc
        C.J x = b⁻¹ • (b • C.J x) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = b⁻¹ • ((-a) • x) := by rw [hb_smul]
        _ = (b⁻¹ * -a) • x := by rw [smul_smul]
    exact hx (C.eq_zero_of_apply_eq_smul hJ)

/-- The real span relation between a nonzero vector and its `J`-partner is trivial. -/
theorem smul_add_smul_apply_eq_zero_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) {a b : ℝ} {x : V} (hx : x ≠ 0) :
    a • x + b • C.J x = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · exact C.smul_add_smul_apply_eq_zero hx
  · rintro ⟨rfl, rfl⟩
    simp

/-- Every nonzero vector gives a linearly independent real pair with its `J`-partner. -/
theorem linearIndependent_pair {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) {x : V} (hx : x ≠ 0) :
    LinearIndependent ℝ ![x, C.J x] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  exact C.smul_add_smul_apply_eq_zero hx h

/-- In finite dimension, `J² = -1` forces the determinant constraint
`det(J) * det(J) = (-1)^finrank`. -/
theorem det_mul_det_eq_neg_one_pow_finrank {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (C : OmegaComplexStructure V) :
    LinearMap.det C.J * LinearMap.det C.J = (-1 : ℝ) ^ Module.finrank ℝ V := by
  have hnegid : LinearMap.det (-LinearMap.id : V →ₗ[ℝ] V) =
      (-1 : ℝ) ^ Module.finrank ℝ V := by
    simpa [LinearMap.det_id] using
      (LinearMap.det_smul (M := V) (-1 : ℝ) (LinearMap.id : V →ₗ[ℝ] V))
  have h := congrArg (fun f : V →ₗ[ℝ] V => LinearMap.det f) C.sq
  simpa [LinearMap.det_comp, hnegid] using h

/-- A finite-dimensional real carrier admitting `J² = -1` has even dimension. -/
theorem finrank_even {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (C : OmegaComplexStructure V) : Even (Module.finrank ℝ V) := by
  by_contra hnot
  have hodd : Odd (Module.finrank ℝ V) := Nat.not_even_iff_odd.mp hnot
  have hpow : (-1 : ℝ) ^ Module.finrank ℝ V = -1 := hodd.neg_one_pow
  have hsq_nonneg : 0 ≤ LinearMap.det C.J * LinearMap.det C.J := mul_self_nonneg _
  rw [C.det_mul_det_eq_neg_one_pow_finrank, hpow] at hsq_nonneg
  norm_num at hsq_nonneg

end OmegaComplexStructure

/-- No finite-dimensional odd real carrier can support a weld complex structure. -/
theorem no_omegaComplexStructure_of_odd_finrank {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (hodd : Odd (Module.finrank ℝ V)) :
    IsEmpty (OmegaComplexStructure V) := by
  refine ⟨?_⟩
  intro C
  exact (Nat.not_even_iff_odd.mpr hodd) C.finrank_even

/--
The real line cannot carry a weld complex structure.

This is the formal one-dimensional obstruction: every real-linear endomorphism of `ℝ`
is multiplication by a real scalar `a`, so `J² = -1` would force `a * a = -1`.
-/
theorem no_real_line_omegaComplexStructure : IsEmpty (OmegaComplexStructure ℝ) := by
  refine ⟨?_⟩
  intro C
  let a : ℝ := C.J 1
  have hJx : ∀ x : ℝ, C.J x = x * a := by
    intro x
    calc
      C.J x = C.J (x • (1 : ℝ)) := by simp
      _ = x • C.J 1 := by rw [map_smul]
      _ = x * a := by simp [a]
  have hsq1 : C.J (C.J 1) = -(1 : ℝ) := C.apply_sq 1
  have ha : a * a = -1 := by
    calc
      a * a = C.J a := (hJx a).symm
      _ = C.J (C.J 1) := by rfl
      _ = -1 := hsq1
  have hnonneg : 0 ≤ a * a := mul_self_nonneg a
  linarith

/-- The standard rotation by `π/2` on the real two-plane. -/
def planeJ : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (-z.2, z.1)
  map_add' := by
    intro x y
    ext
    · simp
      ring
    · simp
  map_smul' := by
    intro a x
    ext
    · simp
    · simp

@[simp]
theorem planeJ_sq : planeJ.comp planeJ = -LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext <;> simp [planeJ]

/-- The standard two-plane realizes `J² = -1`. -/
def planeOmegaComplexStructure : OmegaComplexStructure (ℝ × ℝ) where
  J := planeJ
  sq := planeJ_sq

/-- The Euclidean bilinear form on the real two-plane. -/
def planeQ : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun x y : ℝ × ℝ => x.1 * y.1 + x.2 * y.2)
    (fun x y z => by simp; ring)
    (fun c x y => by simp; ring)
    (fun x y z => by simp; ring)
    (fun c x y => by simp; ring)

/-- The two-plane weld preserves the Euclidean bilinear form. -/
theorem planeJ_preserves_planeQ : PreservesBilin planeQ planeJ := by
  intro x y
  simp [planeQ, planeJ]
  ring

/-- The standard polarized two-plane model for the weld interface. -/
def planePolarizedOmegaComplexStructure :
    PolarizedOmegaComplexStructure (ℝ × ℝ) planeQ where
  complex := planeOmegaComplexStructure
  preserves := planeJ_preserves_planeQ

namespace PolarizedOmegaComplexStructure

/-- Preservation of `Q` by `J` turns a `J` in the right slot into `-J` in the left slot. -/
theorem neg_Q_right_J_eq_Q_J_left {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q) (x y : V) :
    -Q x (P.complex.J y) = Q (P.complex.J x) y := by
  have hpres := P.preserves (P.complex.J x) y
  simpa [P.complex.apply_sq] using hpres

/-- Preservation of `Q` by `J` makes the mixed `J`-slot form anti-invariant. -/
theorem Q_right_J_eq_neg_Q_J_left {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q) (x y : V) :
    Q x (P.complex.J y) = -Q (P.complex.J x) y := by
  have hneg := P.neg_Q_right_J_eq_Q_J_left x y
  linarith

/-- Preservation of `Q` by `J` turns `Q x (J x)` into its negative after rotating both slots. -/
theorem neg_Q_self_J_eq_Q_J_self {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q) (x : V) :
    -Q x (P.complex.J x) = Q (P.complex.J x) x := by
  exact P.neg_Q_right_J_eq_Q_J_left x x

/-- For a symmetric preserved form, every vector is `Q`-orthogonal to its `J`-partner. -/
theorem Q_self_J_eq_zero_of_isSymm {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    (hQ : Q.IsSymm) (x : V) :
    Q x (P.complex.J x) = 0 := by
  have hneg := P.neg_Q_self_J_eq_Q_J_self x
  have hsymm : Q (P.complex.J x) x = Q x (P.complex.J x) := hQ.eq (P.complex.J x) x
  rw [hsymm] at hneg
  linarith

end PolarizedOmegaComplexStructure

end RHTower
end GaloisForLFunctions
