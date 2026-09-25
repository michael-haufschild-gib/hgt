import GaloisForLFunctions.RHTower.GL3UpperHalfSpace
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic


/-!
# `h³` as the Iwasawa group `N·A⁺`, its topology, and continuity of the `GL₃(ℝ)` action

The Iwasawa matrices `mat z = [[y₁y₂, y₁x₂, x₃], [0, y₁, x₁], [0, 0, 1]]` form a group under
matrix multiplication; transporting it gives a group law on `h³` with `mat (z * w) = mat z * mat w`
(`mat_mul`), unit `(0,0,0,1,1)`, and the left action of this group on `h³` is the restriction of the
`GL₃(ℝ)` action (`toGL_smul`). So `h³` is a principal homogeneous space of its own Borel group.

The topology is induced by the coordinates `(x₁, x₂, x₃, y₁, y₂)`, an open embedding onto
`ℝ³ × (0,∞)²` (`isOpenEmbedding_coords`). This makes `h³` a locally compact, second countable,
Hausdorff topological group with its Borel structure. The Iwasawa reconstruction `ofPD` is continuous
along continuous families of positive definite matrices (`continuous_ofPD`), so the `GL₃(ℝ)` action
is jointly continuous.
-/

open Matrix Topology

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-! ### The Iwasawa group law -/

/-- The group law of `h³ ≅ N·A⁺` transported from upper-triangular matrices:
`mat (z * w) = mat z * mat w`. -/
instance : Mul H3 where
  mul z w := ⟨z.x1 + z.y1 * w.x1, z.x2 + z.y2 * w.x2, z.x3 + z.y1 * z.x2 * w.x1 + z.y1 * z.y2 * w.x3,
    z.y1 * w.y1, z.y2 * w.y2, mul_pos z.y1_pos w.y1_pos, mul_pos z.y2_pos w.y2_pos⟩

instance : One H3 := ⟨⟨0, 0, 0, 1, 1, one_pos, one_pos⟩⟩

noncomputable instance : Inv H3 where
  inv z := ⟨-z.x1 / z.y1, -z.x2 / z.y2, (z.x1 * z.x2 - z.x3) / (z.y1 * z.y2), z.y1⁻¹, z.y2⁻¹,
    inv_pos.2 z.y1_pos, inv_pos.2 z.y2_pos⟩

@[simp] theorem mul_x1 (z w : H3) : (z * w).x1 = z.x1 + z.y1 * w.x1 := rfl
@[simp] theorem mul_x2 (z w : H3) : (z * w).x2 = z.x2 + z.y2 * w.x2 := rfl
@[simp] theorem mul_x3 (z w : H3) :
    (z * w).x3 = z.x3 + z.y1 * z.x2 * w.x1 + z.y1 * z.y2 * w.x3 := rfl
@[simp] theorem mul_y1 (z w : H3) : (z * w).y1 = z.y1 * w.y1 := rfl
@[simp] theorem mul_y2 (z w : H3) : (z * w).y2 = z.y2 * w.y2 := rfl
@[simp] theorem one_x1 : (1 : H3).x1 = 0 := rfl
@[simp] theorem one_x2 : (1 : H3).x2 = 0 := rfl
@[simp] theorem one_x3 : (1 : H3).x3 = 0 := rfl
@[simp] theorem one_y1 : (1 : H3).y1 = 1 := rfl
@[simp] theorem one_y2 : (1 : H3).y2 = 1 := rfl
@[simp] theorem inv_x1 (z : H3) : z⁻¹.x1 = -z.x1 / z.y1 := rfl
@[simp] theorem inv_x2 (z : H3) : z⁻¹.x2 = -z.x2 / z.y2 := rfl
@[simp] theorem inv_x3 (z : H3) : z⁻¹.x3 = (z.x1 * z.x2 - z.x3) / (z.y1 * z.y2) := rfl
@[simp] theorem inv_y1 (z : H3) : z⁻¹.y1 = z.y1⁻¹ := rfl
@[simp] theorem inv_y2 (z : H3) : z⁻¹.y2 = z.y2⁻¹ := rfl

noncomputable instance : Group H3 where
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by
    have h1 := a.y1_pos.ne'
    have h2 := a.y2_pos.ne'
    ext <;> simp <;> field_simp <;> ring

theorem mat_mul (z w : H3) : (z * w).mat = z.mat * w.mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem mat_one : (1 : H3).mat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mat]

/-- The Iwasawa matrix as an element of `GL₃(ℝ)`. -/
noncomputable def toGL : H3 →* GL (Fin 3) ℝ where
  toFun z := ⟨z.mat, z⁻¹.mat, by rw [← mat_mul, mul_inv_cancel, mat_one],
    by rw [← mat_mul, inv_mul_cancel, mat_one]⟩
  map_one' := Units.ext mat_one
  map_mul' z w := Units.ext (mat_mul z w)

@[simp] theorem coe_toGL (z : H3) : (toGL z : Matrix (Fin 3) (Fin 3) ℝ) = z.mat := rfl

/-- **The group acts through the Iwasawa matrix.** `mat z • w = z * w`. -/
theorem toGL_smul (z w : H3) : toGL z • w = z * w :=
  smul_eq_of_mul (k := 1) (by simp) one_ne_zero (by rw [one_smul, Matrix.mul_one, coe_toGL, mat_mul])

/-- `z = mat z • 1`: the base point `1 = (0,0,0,1,1)` has orbit map `z ↦ z`. -/
theorem toGL_smul_one (z : H3) : toGL z • (1 : H3) = z := by rw [toGL_smul, mul_one]

/-! ### Topology -/

/-- The Iwasawa coordinate vector `(x₁, x₂, x₃, y₁, y₂)`. -/
def coords (z : H3) : Fin 5 → ℝ := ![z.x1, z.x2, z.x3, z.y1, z.y2]

theorem coords_injective : Function.Injective coords := by
  intro z w h
  have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
  have h3 := congrFun h 3; have h4 := congrFun h 4
  simp [coords] at h0 h1 h2 h3 h4
  ext <;> assumption

/-- The coordinate domain `ℝ³ × (0,∞)²`. -/
def dom : Set (Fin 5 → ℝ) := {p | 0 < p 3 ∧ 0 < p 4}

theorem isOpen_dom : IsOpen dom :=
  (isOpen_lt continuous_const (continuous_apply 3)).inter
    (isOpen_lt continuous_const (continuous_apply 4))

/-- The point with coordinates `p ∈ dom` (a base point outside `dom`). -/
noncomputable def ofCoords (p : Fin 5 → ℝ) : H3 := by
  classical
  exact if h : 0 < p 3 ∧ 0 < p 4 then ⟨p 0, p 1, p 2, p 3, p 4, h.1, h.2⟩ else 1

theorem ofCoords_eq {p : Fin 5 → ℝ} (hp : p ∈ dom) :
    ofCoords p = ⟨p 0, p 1, p 2, p 3, p 4, hp.1, hp.2⟩ := by
  unfold ofCoords; exact dif_pos hp

theorem coords_ofCoords {p : Fin 5 → ℝ} (hp : p ∈ dom) : coords (ofCoords p) = p := by
  rw [ofCoords_eq hp]
  ext i; fin_cases i <;> rfl

theorem ofCoords_coords (z : H3) : ofCoords (coords z) = z := by
  rw [ofCoords_eq (show coords z ∈ dom from ⟨z.y1_pos, z.y2_pos⟩)]
  rfl

theorem range_coords : Set.range coords = dom := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩; exact ⟨z.y1_pos, z.y2_pos⟩
  · intro hp; exact ⟨ofCoords p, coords_ofCoords hp⟩

instance : TopologicalSpace H3 := TopologicalSpace.induced coords inferInstance

theorem isOpenEmbedding_coords : IsOpenEmbedding coords :=
  ⟨⟨⟨rfl⟩, coords_injective⟩, by rw [range_coords]; exact isOpen_dom⟩

theorem continuous_coords : Continuous coords := isOpenEmbedding_coords.continuous

@[fun_prop] theorem continuous_x1 : Continuous H3.x1 := (continuous_apply 0).comp continuous_coords
@[fun_prop] theorem continuous_x2 : Continuous H3.x2 := (continuous_apply 1).comp continuous_coords
@[fun_prop] theorem continuous_x3 : Continuous H3.x3 := (continuous_apply 2).comp continuous_coords
@[fun_prop] theorem continuous_y1 : Continuous H3.y1 := (continuous_apply 3).comp continuous_coords
@[fun_prop] theorem continuous_y2 : Continuous H3.y2 := (continuous_apply 4).comp continuous_coords

/-- A map into `h³` is continuous when its five coordinates are. -/
theorem continuous_of_coords {X : Type*} [TopologicalSpace X] {f : X → H3}
    (h1 : Continuous fun x => (f x).x1) (h2 : Continuous fun x => (f x).x2)
    (h3 : Continuous fun x => (f x).x3) (h4 : Continuous fun x => (f x).y1)
    (h5 : Continuous fun x => (f x).y2) : Continuous f := by
  rw [isOpenEmbedding_coords.isInducing.continuous_iff]
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

instance : IsTopologicalGroup H3 where
  continuous_mul := by
    apply continuous_of_coords <;> simp only [mul_x1, mul_x2, mul_x3, mul_y1, mul_y2] <;> fun_prop
  continuous_inv := by
    apply continuous_of_coords <;> simp only [inv_x1, inv_x2, inv_x3, inv_y1, inv_y2]
    · exact (continuous_x1.neg).div continuous_y1 fun z => z.y1_pos.ne'
    · exact (continuous_x2.neg).div continuous_y2 fun z => z.y2_pos.ne'
    · exact (continuous_x1.mul continuous_x2 |>.sub continuous_x3).div
        (continuous_y1.mul continuous_y2) fun z => (mul_pos z.y1_pos z.y2_pos).ne'
    · exact continuous_y1.inv₀ fun z => z.y1_pos.ne'
    · exact continuous_y2.inv₀ fun z => z.y2_pos.ne'

instance : T2Space H3 := isOpenEmbedding_coords.isEmbedding.t2Space

instance : LocallyCompactSpace H3 := isOpenEmbedding_coords.locallyCompactSpace

instance : SecondCountableTopology H3 := isOpenEmbedding_coords.isEmbedding.secondCountableTopology

instance : MeasurableSpace H3 := borel H3

instance : BorelSpace H3 := ⟨rfl⟩

/-! ### Continuity of the `GL₃(ℝ)` action -/

/-- The Iwasawa reconstruction is continuous along any continuous family of positive definite
matrices: its coordinates are ratios and square roots of polynomials with positive denominators. -/
theorem continuous_ofPD {X : Type*} [TopologicalSpace X] {S : X → Matrix (Fin 3) (Fin 3) ℝ}
    (hS : Continuous S) (hpd : ∀ x, (S x).PosDef) : Continuous fun x => ofPD (S x) (hpd x) := by
  have he : ∀ i j, Continuous fun x => S x i j := fun i j => hS.matrix_elem i j
  have hnt : ∀ i j, Continuous fun x => nt (S x) i j := fun i j =>
    (he i j).div (he 2 2) fun x => (s22_pos (hpd x)).ne'
  have hqa : Continuous fun x => qa (S x) := (hnt 1 1).sub ((hnt 1 2).pow 2)
  have hqa0 : ∀ x, qa (S x) ≠ 0 := fun x => (qa_pos (hpd x)).ne'
  have hqb : Continuous fun x => qb (S x) := (hnt 0 1).sub ((hnt 1 2).mul (hnt 0 2))
  have hqe : Continuous fun x => qe (S x) :=
    ((hnt 0 0).sub ((hnt 0 2).pow 2)).sub ((hqb.pow 2).div hqa hqa0)
  apply continuous_of_coords
  · exact hnt 1 2
  · exact hqb.div hqa hqa0
  · exact hnt 0 2
  · exact hqa.sqrt
  · exact hqe.sqrt.div hqa.sqrt fun x => (Real.sqrt_pos.2 (qa_pos (hpd x))).ne'

theorem continuous_mat : Continuous mat := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [mat] <;> fun_prop

theorem continuous_gram : Continuous gram :=
  continuous_mat.matrix_mul continuous_mat.matrix_transpose

theorem smul_eq_ofPD (g : GL (Fin 3) ℝ) (z : H3) :
    g • z = ofPD ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ)
      (posDef_conj g z) :=
  ofMat_eq _

/-- **The action of `GL₃(ℝ)` on `h³` is jointly continuous.** -/
instance : ContinuousSMul (GL (Fin 3) ℝ) H3 where
  continuous_smul := by
    have hg : Continuous fun p : GL (Fin 3) ℝ × H3 => ((p.1 : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) :=
      Units.continuous_val.comp continuous_fst
    have hS : Continuous fun p : GL (Fin 3) ℝ × H3 =>
        ((p.1 : Matrix (Fin 3) (Fin 3) ℝ) * p.2.gram * (p.1 : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) :=
      (hg.matrix_mul (continuous_gram.comp continuous_snd)).matrix_mul hg.matrix_transpose
    have e : (fun p : GL (Fin 3) ℝ × H3 => p.1 • p.2) =
        fun p => ofPD _ (posDef_conj p.1 p.2) := funext fun p => smul_eq_ofPD p.1 p.2
    rw [e]
    exact continuous_ofPD hS _

end H3
end GaloisForLFunctions.RHTower.GL3
