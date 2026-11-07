/-
The cubic Eisenstein construction is adapted from OpenAI’s formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.BianchiReductionAndCompactCore
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The actual cubic Eisenstein source series

Bottom-row classes of level-three Eisenstein matrices carry the cubic
multiplier. Their inverse row energies define an absolutely convergent
series for `Re s>2`, dominated by a lattice sum on `ℤ⁴`. Uniform domination
on vertical strips proves holomorphy. Right multiplication reindexes the
classes, giving character automorphy; unitary invariance descends to
hyperbolic three-space.
-/

noncomputable section
open scoped BigOperators Classical MatrixGroups Matrix Topology
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def row (M : levelThree) : Fin 2 → O := (M : SL(2,O)) 1

lemma row_mul (M N : levelThree) :
    row (M*N) = Matrix.vecMul (row M) (N : SL(2,O)) := by
  funext j
  simp only [row, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]

lemma row_ne_zero (M : levelThree) : row M ≠ 0 := by
  intro hz
  have hc : (M : SL(2,O)) 1 0 = 0 := congrFun hz 0
  have hd : (M : SL(2,O)) 1 1 = 0 := congrFun hz 1
  have h : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  simp only [hc, hd, mul_zero, sub_zero] at h
  exact zero_ne_one h

/-- Equal bottom rows differ by an upper unipotent matrix, whose multiplier is one. -/
lemma character_eq_of_row_eq (M N : levelThree) (hr : row M = row N) :
    complexCharacter M = complexCharacter N := by
  have hrow : row (M*N⁻¹) = row 1 := by
    rw [row_mul, hr, ← row_mul]
    simp
  have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0 = 0 := by
    simpa [row, Matrix.one_apply] using congrFun hrow 0
  have hchar : complexCharacter (M*N⁻¹) = 1 := by
    change ringComplex (value (M*N⁻¹)) = 1
    rw [value_zero_lower_left _ hc, map_one]
  calc
    complexCharacter M = complexCharacter ((M*N⁻¹)*N) := by congr 1; group
    _ = complexCharacter (M*N⁻¹) * complexCharacter N := map_mul _ _ _
    _ = complexCharacter N := by rw [hchar, one_mul]

lemma row_eq_one_of_lower_left_zero (M : levelThree)
    (hc : (M : SL(2,O)) 1 0 = 0) : row M = row 1 := by
  have hdet : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 = 1 := by
    have hd : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
        (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
    simpa only [hc, mul_zero, sub_zero] using hd
  have ha := CubicJacobi.primary_isUnit_eq_one _ (IsUnit.of_mul_eq_one _ hdet)
    (levelThree_primary M)
  have hd : (M : SL(2,O)) 1 1 = 1 := by simpa only [ha, one_mul] using hdet
  funext j
  fin_cases j <;> simp [row, hc, hd]

def cuspStabilizer : Subgroup levelThree where
  carrier := {M | row M = row 1}
  one_mem' := rfl
  mul_mem' := by
    intro M N hM hN
    change row (M*N) = row 1
    rw [row_mul, hM, ← row_mul]
    simpa using hN
  inv_mem' := by
    intro M hM
    have h : row (M*M⁻¹) = row 1 := by simp
    rw [row_mul, hM, ← row_mul] at h
    simpa using h

lemma mem_cuspStabilizer_iff (M : levelThree) :
    M ∈ cuspStabilizer ↔ (M : SL(2,O)) 1 0 = 0 := by
  constructor
  · intro h
    simpa [row, Matrix.one_apply] using congrFun h 0
  · exact row_eq_one_of_lower_left_zero M

lemma row_eq_iff_left_cusp (M N : levelThree) : row M = row N ↔
    ∃ T : levelThree, T ∈ cuspStabilizer ∧ M = T*N := by
  constructor
  · intro h
    refine ⟨M*N⁻¹, ?_, by group⟩
    change row (M*N⁻¹) = row 1
    rw [row_mul, h, ← row_mul]
    simp
  · rintro ⟨T,hT,rfl⟩
    change row T = row 1 at hT
    rw [row_mul, hT, ← row_mul, one_mul]

/-- Equality of bottom rows is the left cusp-stabilizer relation. -/
def cuspRelation : Setoid levelThree := Setoid.ker row

abbrev CuspCosets := Quotient cuspRelation

def cosetOf (M : levelThree) : CuspCosets := Quotient.mk _ M

lemma cosetOf_eq_iff (M N : levelThree) : cosetOf M = cosetOf N ↔
    ∃ T : levelThree, T ∈ cuspStabilizer ∧ M = T*N := by
  rw [← row_eq_iff_left_cusp]
  exact Quotient.eq

def cosetRow : CuspCosets → (Fin 2 → O) :=
  Quotient.lift row (fun _ _ h => h)

@[simp] lemma cosetRow_cosetOf (M : levelThree) : cosetRow (cosetOf M) = row M := rfl

lemma cosetRow_injective : Function.Injective cosetRow := by
  intro x y
  induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
      intro h
      exact Quotient.sound h

lemma cosetRow_ne_zero (x : CuspCosets) : cosetRow x ≠ 0 := by
  induction x using Quotient.inductionOn with | _ M => exact row_ne_zero M

/-- The actual multiplier is well defined on bottom-row classes. -/
def cosetCharacter : CuspCosets → ℂ :=
  Quotient.lift complexCharacter (fun M N h => character_eq_of_row_eq M N h)

@[simp] lemma cosetCharacter_cosetOf (M : levelThree) :
    cosetCharacter (cosetOf M) = complexCharacter M := rfl

lemma norm_cosetCharacter (x : CuspCosets) : ‖cosetCharacter x‖ = 1 := by
  induction x using Quotient.inductionOn with | _ M => exact norm_complexCharacter M

def rightTranslate (M : levelThree) : CuspCosets → CuspCosets :=
  Quotient.map (fun N => N*M) (by
    intro A B h
    change row (A*M) = row (B*M)
    rw [row_mul, row_mul, show row A = row B from h])

@[simp] lemma rightTranslate_cosetOf (M N : levelThree) :
    rightTranslate M (cosetOf N) = cosetOf (N*M) := rfl

lemma rightTranslate_mul (M N : levelThree) (x : CuspCosets) :
    rightTranslate N (rightTranslate M x) = rightTranslate (M*N) x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf ((A*M)*N) = cosetOf (A*(M*N))
    rw [mul_assoc]

@[simp] lemma rightTranslate_one (x : CuspCosets) : rightTranslate 1 x = x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf (A*1) = cosetOf A
    rw [mul_one]

def rightEquiv (M : levelThree) : CuspCosets ≃ CuspCosets where
  toFun := rightTranslate M
  invFun := rightTranslate M⁻¹
  left_inv x := by rw [rightTranslate_mul]; simp
  right_inv x := by rw [rightTranslate_mul]; simp

lemma cosetRow_rightEquiv (M : levelThree) (x : CuspCosets) :
    cosetRow (rightEquiv M x) = Matrix.vecMul (cosetRow x) (M : SL(2,O)) := by
  induction x using Quotient.inductionOn with | _ N => exact row_mul N M

lemma cosetCharacter_rightEquiv (M : levelThree) (x : CuspCosets) :
    cosetCharacter (rightEquiv M x) = cosetCharacter x * complexCharacter M := by
  induction x using Quotient.inductionOn with | _ N => exact map_mul _ _ _

def complexMatrix : levelThree →* SL(2,ℂ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) ringComplex).comp levelThree.subtype

lemma complexMatrix_apply (M : levelThree) (i j : Fin 2) :
    complexMatrix M i j = ringComplex ((M : SL(2,O)) i j) := rfl

def embeddedRow (x : CuspCosets) : Fin 2 → ℂ := ringComplex ∘ cosetRow x

lemma embeddedRow_ne_zero (x : CuspCosets) : embeddedRow x ≠ 0 := by
  intro hz
  apply cosetRow_ne_zero x
  funext i
  apply ringComplex_injective
  simpa only [embeddedRow, Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hz i

lemma embeddedRow_rightEquiv (M : levelThree) (x : CuspCosets) :
    embeddedRow (rightEquiv M x) = Matrix.vecMul (embeddedRow x) (complexMatrix M : SL(2,ℂ)) := by
  funext j
  simp only [embeddedRow, Function.comp_apply, cosetRow_rightEquiv,
    Matrix.vecMul, dotProduct, map_sum, map_mul, complexMatrix_apply]

def integerLattice : Submodule ℤ ((Fin 2 × Fin 2) → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2 × Fin 2)))

instance : DiscreteTopology integerLattice := by
  unfold integerLattice
  infer_instance

instance : IsZLattice ℝ integerLattice := by
  unfold integerLattice
  infer_instance

def integerPoint (n : (Fin 2 × Fin 2) → ℤ) : integerLattice :=
  ⟨fun i => (n i : ℝ), by
    rw [integerLattice, (Pi.basisFun ℝ (Fin 2 × Fin 2)).mem_span_iff_repr_mem ℤ]
    intro i
    exact ⟨n i, by simp⟩⟩

lemma integerPoint_injective : Function.Injective integerPoint := by
  intro a b hab
  funext i
  have h := congrArg (fun x : integerLattice => (x : (Fin 2 × Fin 2) → ℝ) i) hab
  change (a i : ℝ) = (b i : ℝ) at h
  exact_mod_cast h

lemma integerPoint_norm (n : (Fin 2 × Fin 2) → ℤ) : ‖integerPoint n‖ = ‖n‖ := by
  change ‖fun i => (n i : ℝ)‖ = ‖n‖
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← Int.norm_eq_abs] using norm_le_pi_norm n i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← Int.norm_eq_abs] using norm_le_pi_norm (fun i => (n i : ℝ)) i

/-- A four-dimensional integer lattice has summable radial powers below exponent minus four. -/
lemma summable_integer_four_rpow (k : ℝ) (hk : 4 < k) :
    Summable (fun n : (Fin 2 × Fin 2) → ℤ => ‖n‖ ^ (-k)) := by
  have hf : Module.finrank ℤ integerLattice = 4 := by
    rw [ZLattice.rank ℝ integerLattice]
    simp
  have hs := ZLattice.summable_norm_rpow integerLattice (-k) (by rw [hf]; norm_num; linarith)
  apply (hs.comp_injective integerPoint_injective).congr
  intro n
  change ‖integerPoint n‖ ^ (-k) = ‖n‖ ^ (-k)
  rw [integerPoint_norm]

lemma norm_coordinates_ne_zero (x : CuspCosets) : 0 < ‖rowCoordinates (cosetRow x)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  apply cosetRow_ne_zero x
  apply rowCoordinates_injective
  have hz0 : rowCoordinates (0 : Fin 2 → O) = 0 := by
    apply norm_le_zero_iff.mp
    have he : (fun i : Fin 2 => ringComplex ((0 : Fin 2 → O) i)) =
        (0 : Fin 2 → ℂ) := by
      funext i
      exact map_zero _
    have hh := coordinates_norm_bound (0 : Fin 2 → O)
    rw [he, norm_zero, mul_zero] at hh
    exact hh
  rw [hz0]
  exact hz

/-- The cubic character weighted inverse row-energy power. -/
def summand (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) : ℂ :=
  (cosetCharacter x)⁻¹ *
    (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s)

lemma norm_summand (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    ‖summand g s x‖ = rowEnergy (rowOperator g (embeddedRow x)) ^ (-s.re) := by
  rw [summand, norm_mul, norm_inv, norm_cosetCharacter, inv_one, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x)))]
  rfl

/-- The inverse matrix compares transformed row energy with integral coordinates. -/
lemma norm_summand_bound (g : SL(2,ℂ)) (s : ℂ) (hs : 0 < s.re) (x : CuspCosets) :
    ‖summand g s x‖ ≤ (rowBound g) ^ (2*s.re) *
      ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re)) := by
  rw [norm_summand]
  have hn := norm_coordinates_ne_zero x
  have hb := rowBound_pos g
  have he := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  have hbd := coordinates_le_transformed_energy g (cosetRow x)
  change ‖rowCoordinates (cosetRow x)‖ ≤ rowBound g *
    Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) at hbd
  have hle : (‖rowCoordinates (cosetRow x)‖ / rowBound g) ^ 2 ≤
      rowEnergy (rowOperator g (embeddedRow x)) := by
    have hd : ‖rowCoordinates (cosetRow x)‖ / rowBound g ≤
        Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) :=
      (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hbd)
    have hsq := Real.sq_sqrt he.le
    nlinarith [div_pos hn hb, Real.sqrt_nonneg (rowEnergy (rowOperator g (embeddedRow x)))]
  have hp := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (div_pos hn hb)) hle (by linarith : -s.re ≤ 0)
  convert hp using 1
  rw [← Real.rpow_natCast_mul (div_nonneg hn.le hb.le) 2 (-s.re),
    Real.div_rpow hn.le hb.le]
  simp only [Nat.cast_ofNat, mul_neg, Real.rpow_neg hb.le, div_eq_mul_inv, inv_inv]
  exact mul_comm _ _

/-- Absolute convergence follows from the four-dimensional lattice majorant. -/
theorem summable_norm_summand (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun x : CuspCosets => ‖summand g s x‖) := by
  have hsum := summable_integer_four_rpow (2*s.re) (by linarith)
  have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
    rowCoordinates_injective.comp cosetRow_injective
  have hcomp : Summable (fun x : CuspCosets => ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re))) := by
    apply (hsum.comp_injective hinj).congr
    intro x
    rfl
  exact (hcomp.mul_left ((rowBound g) ^ (2*s.re))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun x => norm_summand_bound g s (by linarith) x)

theorem summable_summand (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    Summable (summand g s) := (summable_norm_summand g s hs).of_norm

/-- The cubic Eisenstein series, indexed by actual bottom-row classes. -/
def eisenstein (g : SL(2,ℂ)) (s : ℂ) : ℂ := ∑' x : CuspCosets, summand g s x

lemma transformedRow_rightEquiv (M : levelThree) (g : SL(2,ℂ)) (x : CuspCosets) :
    rowOperator g (embeddedRow (rightEquiv M x)) =
      rowOperator (complexMatrix M * g) (embeddedRow x) := by
  rw [embeddedRow_rightEquiv, ← rowOperator_apply, rowOperator_mul]

lemma summand_automorphy (M : levelThree) (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    summand (complexMatrix M * g) s x =
      complexCharacter M * summand g s (rightEquiv M x) := by
  have hM : complexCharacter M ≠ 0 := by
    intro h
    have hn := norm_complexCharacter M
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  simp only [summand, cosetCharacter_rightEquiv, transformedRow_rightEquiv,
    mul_inv_rev]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hM, one_mul]

/-- Right translation of bottom rows gives the cubic transformation law. -/
theorem eisenstein_automorphy (M : levelThree) (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    eisenstein (complexMatrix M * g) s = complexCharacter M * eisenstein g s := by
  have hleft := summable_summand (complexMatrix M * g) s hs
  have hright := summable_summand g s hs
  have hreindex : HasSum (fun x : CuspCosets => summand g s (rightEquiv M x))
      (eisenstein g s) := (rightEquiv M).hasSum_iff.mpr hright.hasSum
  have hscale := hreindex.mul_left (complexCharacter M)
  exact hleft.hasSum.unique (hscale.congr_fun (fun x => summand_automorphy M g s x))

lemma summand_differentiable (g : SL(2,ℂ)) (x : CuspCosets) :
    Differentiable ℂ (fun s : ℂ => summand g s x) := by
  have hq : (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))).ne'
  exact ((differentiable_id.neg).const_cpow (Or.inl hq)).const_mul _

lemma norm_summand_strip (g : SL(2,ℂ)) (a b : ℝ) (s : ℂ)
    (ha : a ≤ s.re) (hb : s.re ≤ b) (x : CuspCosets) :
    ‖summand g s x‖ ≤ ‖summand g (a : ℂ) x‖ + ‖summand g (b : ℂ) x‖ := by
  simp only [norm_summand, Complex.ofReal_re]
  have hq := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  by_cases hq1 : 1 ≤ rowEnergy (rowOperator g (embeddedRow x))
  · exact (Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg ha)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hq.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hq (le_of_not_ge hq1)
        (neg_le_neg hb)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hq.le _))

/-- Two real exponents dominate the series uniformly on a vertical strip. -/
theorem eisenstein_differentiableOn_strip (g : SL(2,ℂ)) (a b : ℝ)
    (ha : 2 < a) (hab : a < b) :
    DifferentiableOn ℂ (eisenstein g) {s : ℂ | a < s.re ∧ s.re < b} := by
  have hsa := summable_norm_summand g (a : ℂ) (by simpa using ha)
  have hsb := summable_norm_summand g (b : ℂ) (by simpa using lt_trans ha hab)
  apply Complex.differentiableOn_tsum_of_summable_norm (hsa.add hsb)
    (fun x => (summand_differentiable g x).differentiableOn)
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  · intro x s hs
    exact norm_summand_strip g a b s hs.1.le hs.2.le x

theorem eisenstein_differentiableAt (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    DifferentiableAt ℂ (eisenstein g) s := by
  let a := (2+s.re)/2
  let b := s.re+1
  have ha : 2 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hsU : s ∈ {z : ℂ | a < z.re ∧ z.re < b} := by
    constructor <;> dsimp [a,b] <;> linarith
  exact (eisenstein_differentiableOn_strip g a b ha hab s hsU).differentiableAt
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hsU)

theorem eisenstein_differentiableOn (g : SL(2,ℂ)) :
    DifferentiableOn ℂ (eisenstein g) {s : ℂ | 2 < s.re} := by
  intro s hs
  exact (eisenstein_differentiableAt g s hs).differentiableWithinAt

lemma inv_cpow_ofReal_nonneg {x : ℝ} (hx : 0≤x) (s : ℂ) :
    (x:ℂ)⁻¹^s=((x:ℂ)^s)⁻¹ := by
  apply Complex.inv_cpow
  rw [Complex.arg_ofReal_of_nonneg hx]
  exact Real.pi_pos.ne

def transformedHeight (z : ℂ) (v : ℝ) (u : Fin 2 → ℂ) : ℝ :=
  v / heightDenominator z v u

lemma summand_upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (x : CuspCosets) :
    summand (upperSection z v hv) s x = (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s := by
  rw [summand, rowEnergy_upperSection]
  congr 1
  have hq := heightDenominator_pos z v hv (embeddedRow x) (embeddedRow_ne_zero x)
  have hinv : (transformedHeight z v (embeddedRow x) : ℂ) =
      ((heightDenominator z v (embeddedRow x) / v : ℝ) : ℂ)⁻¹ := by
    simp only [transformedHeight, Complex.ofReal_div, inv_div]
  rw [hinv, inv_cpow_ofReal_nonneg (div_nonneg hq.le hv.le), Complex.cpow_neg]

def upperEisenstein (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) : ℂ :=
  eisenstein (upperSection z v hv) s

theorem upperEisenstein_eq_source_series (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    upperEisenstein z v hv s = ∑' x : CuspCosets, (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s :=
  tsum_congr (summand_upperSection z v hv s)

theorem source_series_summable (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun x : CuspCosets => (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s) :=
  (summable_summand (upperSection z v hv) s hs).congr (summand_upperSection z v hv s)

theorem eisenstein_right_unitary (g k : SL(2,ℂ)) (s : ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    eisenstein (g*k) s = eisenstein g s := by
  apply tsum_congr
  intro x
  simp only [summand, ← rowOperator_mul, rowEnergy_unitary k hk]

/-- Unitary invariance descends the source series to hyperbolic space. -/
def hyperbolicEisenstein (s : ℂ) : HyperbolicSpace → ℂ :=
  Quotient.lift (fun g => eisenstein g s) (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh]
    exact (eisenstein_right_unitary g (g⁻¹*h) s hk).symm)

@[simp] lemma hyperbolicEisenstein_mk (s : ℂ) (g : SL(2,ℂ)) :
    hyperbolicEisenstein s (g : HyperbolicSpace) = eisenstein g s := rfl

theorem hyperbolicEisenstein_automorphy (M : levelThree) (s : ℂ) (hs : 2 < s.re)
    (w : HyperbolicSpace) :
    hyperbolicEisenstein s (complexMatrix M • w) =
      complexCharacter M * hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with | _ g =>
    exact eisenstein_automorphy M g s hs

lemma hyperbolicEisenstein_upperPoint (s : ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicEisenstein s (upperPoint z v hv) = upperEisenstein z v hv s := rfl

/-- The positive height attached to each cusp coset. -/
def cosetHeight (x : CuspCosets) : HyperbolicSpace → ℝ :=
  Quotient.lift (fun g : SL(2,ℂ) => (rowEnergy (rowOperator g (embeddedRow x)))⁻¹) (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh, ← rowOperator_mul, rowEnergy_unitary (g⁻¹*h) hk])

lemma cosetHeight_cosetOf (M : levelThree) (w : HyperbolicSpace) :
    cosetHeight (cosetOf M) w = hyperbolicHeight (complexMatrix M • w) := by
  induction w using Quotient.inductionOn with | _ g =>
    change (rowEnergy (rowOperator g (embeddedRow (cosetOf M))))⁻¹ =
      liftedHeight (complexMatrix M * g)
    rw [liftedHeight, complexBottomRow_mul]
    rfl

/-- The descended series is the character weighted sum of cusp-height powers. -/
theorem hyperbolicEisenstein_eq_height_series (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s w = ∑' x : CuspCosets,
      (cosetCharacter x)⁻¹ * (cosetHeight x w : ℂ) ^ s := by
  induction w using Quotient.inductionOn with | _ g =>
    apply tsum_congr
    intro x
    change (cosetCharacter x)⁻¹ *
      (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s) =
      (cosetCharacter x)⁻¹ * ((rowEnergy (rowOperator g (embeddedRow x)))⁻¹ : ℝ) ^ s
    rw [Complex.ofReal_inv, inv_cpow_ofReal_nonneg (rowEnergy_nonneg _),
      Complex.cpow_neg]

theorem height_series_summable_norm (s : ℂ) (hs : 2 < s.re) (w : HyperbolicSpace) :
    Summable (fun x : CuspCosets =>
      ‖(cosetCharacter x)⁻¹ * (cosetHeight x w : ℂ) ^ s‖) := by
  induction w using Quotient.inductionOn with | _ g =>
    apply (summable_norm_summand g s hs).congr
    intro x
    congr 1
    change (cosetCharacter x)⁻¹ *
      (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s) =
      (cosetCharacter x)⁻¹ * ((rowEnergy (rowOperator g (embeddedRow x)))⁻¹ : ℝ) ^ s
    rw [Complex.ofReal_inv, inv_cpow_ofReal_nonneg (rowEnergy_nonneg _),
      Complex.cpow_neg]

theorem hyperbolicEisenstein_differentiableOn (w : HyperbolicSpace) :
    DifferentiableOn ℂ (fun s : ℂ => hyperbolicEisenstein s w) {s : ℂ | 2 < s.re} := by
  induction w using Quotient.inductionOn with | _ g =>
    exact eisenstein_differentiableOn g


end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.summable_norm_summand
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.eisenstein_differentiableOn
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.hyperbolicEisenstein_automorphy
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.hyperbolicEisenstein_eq_height_series
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.height_series_summable_norm
