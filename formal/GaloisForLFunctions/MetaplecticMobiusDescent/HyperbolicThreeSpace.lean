/-
The quotient and Iwasawa construction are adapted from OpenAI’s formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Hyperbolic three-space in upper coordinates

The quotient `SL₂(ℂ)/SU₂` carries the height given by the inverse bottom-row
energy. Its matrix action has the usual upper-half-space height formula.
An explicit unitary factor proves Iwasawa decomposition. The Gram matrix
recovers the horizontal coordinate, giving a homeomorphism with `ℂ × ℝ₊`.
-/

noncomputable section
open scoped BigOperators Classical MatrixGroups Matrix
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

/-- Squared Euclidean length of a two-entry complex row. -/
def rowEnergy (v : Fin 2 → ℂ) : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2

lemma rowEnergy_nonneg (v : Fin 2 → ℂ) : 0 ≤ rowEnergy v := by
  unfold rowEnergy; positivity

lemma norm_le_sqrt_rowEnergy (v : Fin 2 → ℂ) : ‖v‖ ≤ Real.sqrt (rowEnergy v) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply Real.le_sqrt_of_sq_le
  fin_cases i <;> dsimp [rowEnergy] <;> nlinarith [sq_nonneg ‖v 0‖, sq_nonneg ‖v 1‖]

lemma rowEnergy_pos (v : Fin 2 → ℂ) (hv : v ≠ 0) : 0 < rowEnergy v := by
  have h := norm_le_sqrt_rowEnergy v
  have hn := norm_pos_iff.mpr hv
  exact Real.sqrt_pos.mp (lt_of_lt_of_le hn h)

def rowOperator (g : SL(2,ℂ)) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLinearMapRight' (g : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap

@[simp] lemma rowOperator_apply (g : SL(2,ℂ)) (v : Fin 2 → ℂ) :
    rowOperator g v = Matrix.vecMul v (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl

lemma rowOperator_mul (g h : SL(2,ℂ)) (v : Fin 2 → ℂ) :
    rowOperator h (rowOperator g v) = rowOperator (g*h) v := by
  simp only [rowOperator_apply, Matrix.vecMul_vecMul, Matrix.SpecialLinearGroup.coe_mul]

@[simp] lemma rowOperator_one (v : Fin 2 → ℂ) : rowOperator 1 v = v := by
  simp only [rowOperator_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

lemma rowOperator_ne_zero (g : SL(2,ℂ)) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    rowOperator g v ≠ 0 := by
  intro hz
  have h := congrArg (rowOperator g⁻¹) hz
  rw [rowOperator_mul, mul_inv_cancel, rowOperator_one, map_zero] at h
  exact hv h

/-- The upper triangular determinant-one representative of a point `(z,v)`. -/
def upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) : SL(2,ℂ) :=
  ⟨!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹], by
    have hr : (Real.sqrt v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
    simp [Matrix.det_fin_two, hr]⟩

lemma rowOperator_upperSection_zero (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowOperator (upperSection z v hv) u 0 = u 0 * (Real.sqrt v : ℂ) := by
  change Matrix.vecMul u (!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) _ = _
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma rowOperator_upperSection_one (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowOperator (upperSection z v hv) u 1 = (u 0*z + u 1) / (Real.sqrt v : ℂ) := by
  change Matrix.vecMul u (!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) _ = _
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

def heightDenominator (z : ℂ) (v : ℝ) (u : Fin 2 → ℂ) : ℝ :=
  ‖u 0*z + u 1‖ ^ 2 + ‖u 0‖ ^ 2 * v ^ 2

lemma rowEnergy_upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowEnergy (rowOperator (upperSection z v hv) u) = heightDenominator z v u / v := by
  rw [rowEnergy, rowOperator_upperSection_zero, rowOperator_upperSection_one,
    norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg v),
    mul_pow, div_pow, Real.sq_sqrt hv.le]
  unfold heightDenominator
  field_simp
  ring

lemma heightDenominator_pos (z : ℂ) (v : ℝ) (hv : 0 < v)
    (u : Fin 2 → ℂ) (hu : u ≠ 0) : 0 < heightDenominator z v u := by
  have h := rowEnergy_pos _ (rowOperator_ne_zero (upperSection z v hv) u hu)
  rw [rowEnergy_upperSection] at h
  exact ((div_pos_iff.mp h).resolve_right (by rintro ⟨_,hneg⟩; linarith)).1

lemma ofReal_rowEnergy (u : Fin 2 → ℂ) :
    (rowEnergy u : ℂ) = dotProduct u (star u) := by
  simp only [rowEnergy, Complex.ofReal_add, ← Complex.normSq_eq_norm_sq, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, Complex.mul_conj]

lemma rowEnergy_unitary (k : SL(2,ℂ))
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (u : Fin 2 → ℂ) : rowEnergy (rowOperator k u) = rowEnergy u := by
  apply Complex.ofReal_injective
  rw [ofReal_rowEnergy, ofReal_rowEnergy, rowOperator_apply, Matrix.star_vecMul,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have hu := Matrix.mem_unitaryGroup_iff.mp hk
  change (k : Matrix (Fin 2) (Fin 2) ℂ) *
    Matrix.conjTranspose (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 at hu
  rw [hu, Matrix.vecMul_one]

/-- The special unitary subgroup, regarded inside the special linear group. -/
def compactSubgroup : Subgroup (SL(2,ℂ)) where
  carrier := {k | (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ}
  one_mem' := (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
  mul_mem' := by
    intro a b ha hb
    exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem ha hb
  inv_mem' := by
    intro k hk
    have hinv : (k⁻¹ : SL(2,ℂ)) * k = 1 := inv_mul_cancel k
    have hmat : ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
        (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := congrArg
          (fun a : SL(2,ℂ) => (a : Matrix (Fin 2) (Fin 2) ℂ)) hinv
    have he := Matrix.left_inv_eq_left_inv hmat (Matrix.mem_unitaryGroup_iff'.mp hk)
    change ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [he]
    exact Unitary.star_mem hk

abbrev HyperbolicSpace := SL(2,ℂ) ⧸ compactSubgroup

def upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) : HyperbolicSpace :=
  (upperSection z v hv : HyperbolicSpace)

def complexBottomRow (g : SL(2,ℂ)) : Fin 2 → ℂ := g 1

lemma complexBottomRow_mul (g h : SL(2,ℂ)) :
    complexBottomRow (g*h) = rowOperator h (complexBottomRow g) := by
  funext j
  simp only [complexBottomRow, rowOperator_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]

lemma complexBottomRow_ne_zero (g : SL(2,ℂ)) : complexBottomRow g ≠ 0 := by
  intro hz
  have hc : g 1 0 = 0 := congrFun hz 0
  have hd : g 1 1 = 0 := congrFun hz 1
  have h : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  simp only [hc, hd, mul_zero, sub_zero] at h
  exact zero_ne_one h

def liftedHeight (g : SL(2,ℂ)) : ℝ := (rowEnergy (complexBottomRow g))⁻¹

lemma liftedHeight_pos (g : SL(2,ℂ)) : 0 < liftedHeight g :=
  inv_pos.mpr (rowEnergy_pos _ (complexBottomRow_ne_zero g))

lemma liftedHeight_right_unitary (g k : SL(2,ℂ)) (hk : k ∈ compactSubgroup) :
    liftedHeight (g*k) = liftedHeight g := by
  simp only [liftedHeight, complexBottomRow_mul, rowEnergy_unitary k hk]

/-- Bottom-row energy descends because right unitary multiplication preserves it. -/
def hyperbolicHeight : HyperbolicSpace → ℝ :=
  Quotient.lift liftedHeight (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh]
    exact (liftedHeight_right_unitary g (g⁻¹*h) hk).symm)

@[simp] lemma hyperbolicHeight_mk (g : SL(2,ℂ)) :
    hyperbolicHeight (g : HyperbolicSpace) = liftedHeight g := rfl

lemma hyperbolicHeight_pos (w : HyperbolicSpace) : 0 < hyperbolicHeight w := by
  induction w using Quotient.inductionOn with | _ g => exact liftedHeight_pos g

/-- Height transforms by the positive denominator `|cz+d|²+|c|²v²`. -/
theorem hyperbolicHeight_action_upperPoint (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicHeight (g • upperPoint z v hv) =
      v / (‖g 1 0*z + g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * v ^ 2) := by
  change liftedHeight (g * upperSection z v hv) = _
  rw [liftedHeight, complexBottomRow_mul, rowEnergy_upperSection, inv_div]
  rfl

@[simp] lemma hyperbolicHeight_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (upperPoint z v hv)=v := by
  simpa [Matrix.one_apply] using hyperbolicHeight_action_upperPoint 1 z v hv

def bottomRowUnitary (c d : ℂ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star d/(r:ℂ),-star c/(r:ℂ);c/(r:ℂ),d/(r:ℂ)]

lemma bottomRowUnitary_mem (c d : ℂ) (r : ℝ) (hr : r≠0)
    (hrow : ‖c‖^2+‖d‖^2=r^2) : bottomRowUnitary c d r∈Matrix.unitaryGroup (Fin 2) ℂ := by
  have hC : c*star c+d*star d=(r:ℂ)^2 := by
    simpa only [Complex.ofReal_add,Complex.ofReal_pow,← Complex.mul_conj',Complex.star_def] using
      congrArg (fun x : ℝ => (x:ℂ)) hrow
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  simp only [Complex.star_def] at hC
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bottomRowUnitary,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply,
      Complex.conj_ofReal] <;>
    field_simp [hrC] <;> first | exact hC | (simpa only [mul_comm,add_comm] using hC) | ring

lemma iwasawa_z_row_identities (a b c d : ℂ) (q : ℝ)
    (hq : q≠0) (hrow : (q:ℂ)=c*star c+d*star d) (hdet : a*d-b*c=1) :
    star d/(q:ℂ)+(a*star c+b*star d)/(q:ℂ)*c=a ∧
    -star c/(q:ℂ)+(a*star c+b*star d)/(q:ℂ)*d=b := by
  have hqC : (q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hq
  constructor
  · field_simp [hqC]
    rw [hrow]
    linear_combination -(star d)*hdet
  · field_simp [hqC]
    rw [hrow]
    linear_combination (star c)*hdet

def matrixHorizontal (g : SL(2,ℂ)) : ℂ :=
  (g 0 0*star (g 1 0)+g 0 1*star (g 1 1))/(rowEnergy (complexBottomRow g):ℂ)

/-- Normalize the bottom row to construct the unitary factor explicitly. -/
lemma matrix_iwasawa_factor (g : SL(2,ℂ)) :
    ∃k : SL(2,ℂ), k∈compactSubgroup ∧
      g=upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k := by
  let q : ℝ := rowEnergy (complexBottomRow g)
  let r : ℝ := Real.sqrt q
  have hq : 0<q := rowEnergy_pos _ (complexBottomRow_ne_zero g)
  have hr : 0<r := Real.sqrt_pos.mpr hq
  have hr2 : r^2=q := Real.sq_sqrt hq.le
  have hrow : ‖g 1 0‖^2+‖g 1 1‖^2=r^2 := by
    rw [hr2]
    rfl
  have hqC : (q:ℂ)=g 1 0*star (g 1 0)+g 1 1*star (g 1 1) := by
    simp only [q,rowEnergy,complexBottomRow,Complex.ofReal_add,Complex.ofReal_pow,
      ← Complex.mul_conj',Complex.star_def]
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hz := iwasawa_z_row_identities (g 0 0) (g 0 1) (g 1 0) (g 1 1) q hq.ne' hqC hdet
  let B := upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)
  let U := bottomRowUnitary (g 1 0) (g 1 1) r
  have hroot : Real.sqrt (liftedHeight g)=r⁻¹ := by
    exact Real.sqrt_inv q
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hqrC : (r:ℂ)^2=(q:ℂ) := by exact_mod_cast hr2
  have hB : (B:Matrix (Fin 2) (Fin 2) ℂ)=
      !![(r:ℂ)⁻¹,matrixHorizontal g*(r:ℂ);0,(r:ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B,upperSection,hroot,Complex.ofReal_inv,div_eq_mul_inv]
  have hfactor : (B:Matrix (Fin 2) (Fin 2) ℂ)*U=(g:Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hB]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.mul_apply,Fin.sum_univ_two]
    · change (r:ℂ)⁻¹*(star (g 1 1)/(r:ℂ))+(matrixHorizontal g*(r:ℂ))*(g 1 0/(r:ℂ))=g 0 0
      calc
        _ = star (g 1 1)/(q:ℂ)+matrixHorizontal g*g 1 0 := by
          rw [← hqrC]
          field_simp [hrC]
        _ = _ := hz.1
    · change (r:ℂ)⁻¹*(-star (g 1 0)/(r:ℂ))+(matrixHorizontal g*(r:ℂ))*(g 1 1/(r:ℂ))=g 0 1
      calc
        _ = -star (g 1 0)/(q:ℂ)+matrixHorizontal g*g 1 1 := by
          rw [← hqrC]
          field_simp [hrC]
        _ = _ := hz.2
    · change 0*(star (g 1 1)/(r:ℂ))+(r:ℂ)*(g 1 0/(r:ℂ))=g 1 0
      field_simp [hrC] ; ring
    · change 0*(-star (g 1 0)/(r:ℂ))+(r:ℂ)*(g 1 1/(r:ℂ))=g 1 1
      field_simp [hrC] ; ring
  let k : SL(2,ℂ) := B⁻¹*g
  have hk : (k:Matrix (Fin 2) (Fin 2) ℂ)=U := by
    change ((B⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) * (g:Matrix (Fin 2) (Fin 2) ℂ)=U
    rw [← hfactor,← Matrix.mul_assoc]
    have hi : ((B⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*(B:Matrix (Fin 2) (Fin 2) ℂ)=1 := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_one] using
        congrArg (fun M : SL(2,ℂ) => (M:Matrix (Fin 2) (Fin 2) ℂ)) (inv_mul_cancel B)
    rw [hi,Matrix.one_mul]
  refine ⟨k,?_,?_⟩
  · change (k:Matrix (Fin 2) (Fin 2) ℂ)∈Matrix.unitaryGroup (Fin 2) ℂ
    rw [hk]
    exact bottomRowUnitary_mem _ _ r hr.ne' hrow
  · dsimp [k,B]
    group

/-- Every quotient point has upper-half-space coordinates. -/
theorem upperPoint_surjective (w : HyperbolicSpace) :
    ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v, upperPoint z v hv=w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    obtain ⟨k,hk,hg⟩ := matrix_iwasawa_factor g
    refine ⟨matrixHorizontal g,liftedHeight g,liftedHeight_pos g,?_⟩
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    change (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g∈compactSubgroup
    have hcancel : (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g=k := by
      calc
        _ = (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*
            (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k) :=
          congrArg (fun M => (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*M) hg
        _ = k := inv_mul_cancel_left _ _
    rw [hcancel]
    exact hk


abbrev UpperCoordinates := {p : ℂ × ℝ // 0 < p.2}

def coordinateSection (w : UpperCoordinates) : SL(2,ℂ) :=
  upperSection w.1.1 w.1.2 w.2

instance complexSLTopology : TopologicalSpace (SL(2,ℂ)) :=
  inferInstanceAs (TopologicalSpace {A : Matrix (Fin 2) (Fin 2) ℂ // A.det=1})

lemma continuous_complexSL_coe :
    Continuous (fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ)) :=
  continuous_subtype_val

lemma continuous_complexSL_mul (g : SL(2,ℂ)) :
    Continuous (fun h : SL(2,ℂ) => g*h) := by
  apply Continuous.subtype_mk
  change Continuous (fun h : SL(2,ℂ) =>
    (g : Matrix (Fin 2) (Fin 2) ℂ)*(h : Matrix (Fin 2) (Fin 2) ℂ))
  exact continuous_const.mul continuous_complexSL_coe

lemma continuous_coordinateSection : Continuous coordinateSection := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hroot : Continuous (fun w : UpperCoordinates => (Real.sqrt w.1.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_snd.comp continuous_subtype_val))
  have hne : ∀w : UpperCoordinates,(Real.sqrt w.1.2 : ℂ)≠0 := fun w =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr w.2).ne'
  fin_cases i <;> fin_cases j
  · exact hroot
  · exact (continuous_fst.comp continuous_subtype_val).div hroot hne
  · exact continuous_const
  · exact hroot.inv₀ hne

lemma continuous_hyperbolicProjection :
    Continuous (fun g : SL(2,ℂ) => (g : HyperbolicSpace)) :=
  continuous_quotient_mk'

lemma continuous_upperCoordinates :
    Continuous (fun w : UpperCoordinates => upperPoint w.1.1 w.1.2 w.2) :=
  continuous_hyperbolicProjection.comp continuous_coordinateSection

lemma continuous_translatedUpperCoordinates (g : SL(2,ℂ)) :
    Continuous (fun w : UpperCoordinates => g • upperPoint w.1.1 w.1.2 w.2) := by
  exact continuous_hyperbolicProjection.comp
    ((continuous_complexSL_mul g).comp continuous_coordinateSection)

def matrixGram (g : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (g : Matrix (Fin 2) (Fin 2) ℂ)*star (g : Matrix (Fin 2) (Fin 2) ℂ)

lemma matrixGram_right_unitary (g k : SL(2,ℂ)) (hk : k∈compactSubgroup) :
    matrixGram (g*k)=matrixGram g := by
  have hku : (k : Matrix (Fin 2) (Fin 2) ℂ)*star (k : Matrix (Fin 2) (Fin 2) ℂ)=1 :=
    Matrix.mem_unitaryGroup_iff.mp hk
  unfold matrixGram
  simp only [Matrix.SpecialLinearGroup.coe_mul,star_mul]
  calc
    _ = (g : Matrix (Fin 2) (Fin 2) ℂ)*
        ((k : Matrix (Fin 2) (Fin 2) ℂ)*star (k : Matrix (Fin 2) (Fin 2) ℂ))*
        star (g : Matrix (Fin 2) (Fin 2) ℂ) := by noncomm_ring
    _ = _ := by rw [hku]; simp

/-- The invariant Hermitian matrix `g g*` descends to the quotient. -/
def hyperbolicGram : HyperbolicSpace → Matrix (Fin 2) (Fin 2) ℂ :=
  Quotient.lift matrixGram (by
    intro g h hgh
    have hk : g⁻¹*h∈compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h=g*(g⁻¹*h) := by group
    rw [hh]
    exact (matrixGram_right_unitary g (g⁻¹*h) hk).symm)

lemma hyperbolicGram_continuous : Continuous hyperbolicGram := by
  apply Continuous.quotient_lift
  exact continuous_complexSL_coe.mul continuous_complexSL_coe.star

lemma hyperbolicHeight_continuous : Continuous hyperbolicHeight := by
  apply Continuous.quotient_lift
  have he (i j : Fin 2) : Continuous (fun g : SL(2,ℂ) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_complexSL_coe)
  apply Continuous.inv₀
  · exact ((he 1 0).norm.pow 2).add ((he 1 1).norm.pow 2)
  · intro g
    exact (rowEnergy_pos _ (complexBottomRow_ne_zero g)).ne'

lemma hyperbolicGram_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicGram (upperPoint z v hv) 0 1=z/(v:ℂ) := by
  have hr : (Real.sqrt v : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
  have hs : (Real.sqrt v : ℂ)^2=(v:ℂ) := by exact_mod_cast Real.sq_sqrt hv.le
  change matrixGram (upperSection z v hv) 0 1=_
  simp only [matrixGram,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply]
  change (Real.sqrt v : ℂ)*star (0:ℂ)+(z/(Real.sqrt v : ℂ))*star ((Real.sqrt v : ℂ)⁻¹)=_
  simp only [star_zero,star_inv₀,Complex.star_def,Complex.conj_ofReal,mul_zero,zero_add]
  rw [←hs]
  field_simp

def hyperbolicHorizontal (w : HyperbolicSpace) : ℂ :=
  hyperbolicGram w 0 1*(hyperbolicHeight w:ℂ)

lemma hyperbolicHorizontal_continuous : Continuous hyperbolicHorizontal := by
  unfold hyperbolicHorizontal
  exact ((continuous_apply 1).comp ((continuous_apply 0).comp hyperbolicGram_continuous)).mul
    (Complex.continuous_ofReal.comp hyperbolicHeight_continuous)

@[simp] lemma hyperbolicHorizontal_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHorizontal (upperPoint z v hv)=z := by
  simp only [hyperbolicHorizontal,hyperbolicGram_upperPoint,hyperbolicHeight_upperPoint]
  exact div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr hv.ne')

def hyperbolicCoordinates (w : HyperbolicSpace) : UpperCoordinates :=
  ⟨(hyperbolicHorizontal w,hyperbolicHeight w),hyperbolicHeight_pos w⟩

lemma hyperbolicCoordinates_continuous : Continuous hyperbolicCoordinates :=
  (hyperbolicHorizontal_continuous.prodMk hyperbolicHeight_continuous).subtype_mk _

lemma upperCoordinates_left_inverse : Function.LeftInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro p
  apply Subtype.ext
  exact Prod.ext (hyperbolicHorizontal_upperPoint _ _ _) (hyperbolicHeight_upperPoint _ _ _)

lemma upperCoordinates_right_inverse : Function.RightInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro w
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  exact congrArg (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2)
    (upperCoordinates_left_inverse ⟨(z,v),hv⟩)

/-- The quotient topology agrees with the upper-half-space topology. -/
def upperCoordinatesHomeomorph : UpperCoordinates ≃ₜ HyperbolicSpace where
  toFun p := upperPoint p.1.1 p.1.2 p.2
  invFun := hyperbolicCoordinates
  left_inv := upperCoordinates_left_inverse
  right_inv := upperCoordinates_right_inverse
  continuous_toFun := continuous_upperCoordinates
  continuous_invFun := hyperbolicCoordinates_continuous


instance hyperbolicT2Space : T2Space HyperbolicSpace :=
  T2Space.of_injective_continuous upperCoordinatesHomeomorph.symm.injective
    upperCoordinatesHomeomorph.symm.continuous

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.hyperbolicHeight_action_upperPoint
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.matrix_iwasawa_factor
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.upperPoint_surjective
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.upperCoordinatesHomeomorph
