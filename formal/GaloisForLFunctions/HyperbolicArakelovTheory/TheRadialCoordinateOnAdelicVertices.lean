import GaloisForLFunctions.HyperbolicArakelovTheory.ThePrimeAdjacencyOnTheAdelicCarrier
import GaloisForLFunctions.HTGeometry.SmithNormalFormDVR

/-!
# The intrinsic radial coordinate on projective p-adic vertices

The determinant divided by the squared maximum entry norm is invariant
under homothety and integral changes of basis. DVR Smith normal form
reduces its geometry to a single integral diagonal parameter.
-/

set_option autoImplicit false
noncomputable section
open Matrix Set
open scoped Classical

namespace GaloisForLFunctions.HyperbolicArakelovTheory.AdelicRadial
open FullAdelic AdelicAdjacency

local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩
variable (p : {p : ℕ // p.Prime})

/-- Maximum entry norm, independent of a choice of vector-space norm. -/
def entrySize (M : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) : ℝ :=
  max (max ‖M 0 0‖ ‖M 0 1‖) (max ‖M 1 0‖ ‖M 1 1‖)

theorem entry_le_size (M : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) (i j : Fin 2) :
    ‖M i j‖ ≤ entrySize p M := by
  fin_cases i <;> fin_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem entrySize_le {M : Matrix (Fin 2) (Fin 2) ℚ_[p.1]} {r : ℝ}
    (h : ∀ i j, ‖M i j‖ ≤ r) : entrySize p M ≤ r :=
  max_le (max_le (h 0 0) (h 0 1)) (max_le (h 1 0) (h 1 1))

theorem entrySize_nonneg (M : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) :
    0 ≤ entrySize p M := (norm_nonneg _).trans (entry_le_size p M 0 0)

theorem entrySize_mul_le (M N : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) :
    entrySize p (M * N) ≤ entrySize p M * entrySize p N := by
  apply entrySize_le
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  apply (Padic.nonarchimedean _ _).trans
  rw [norm_mul, norm_mul]
  exact max_le
    (mul_le_mul (entry_le_size p M i 0) (entry_le_size p N 0 j)
      (norm_nonneg _) (entrySize_nonneg p M))
    (mul_le_mul (entry_le_size p M i 1) (entry_le_size p N 1 j)
      (norm_nonneg _) (entrySize_nonneg p M))

theorem entrySize_integral_le_one (h : GL (Fin 2) ℤ_[p.1]) :
    entrySize p (integralMap p h).val ≤ 1 :=
  entrySize_le p (fun i j => (h i j).2)

theorem entrySize_integral_mul (h : GL (Fin 2) ℤ_[p.1]) (g : LocalGL p) :
    entrySize p (integralMap p h * g).val = entrySize p g.val := by
  have hbound (a : GL (Fin 2) ℤ_[p.1]) (b : LocalGL p) :
      entrySize p (integralMap p a * b).val ≤ entrySize p b.val := by
    apply (entrySize_mul_le p _ _).trans
    exact (mul_le_mul_of_nonneg_right (entrySize_integral_le_one p a)
      (entrySize_nonneg p b.val)).trans_eq (one_mul _)
  apply le_antisymm (hbound h g)
  have hi := hbound h⁻¹ (integralMap p h * g)
  simpa only [map_inv, inv_mul_cancel_left] using hi

theorem entrySize_mul_integral (g : LocalGL p) (h : GL (Fin 2) ℤ_[p.1]) :
    entrySize p (g * integralMap p h).val = entrySize p g.val := by
  have hbound (a : LocalGL p) (b : GL (Fin 2) ℤ_[p.1]) :
      entrySize p (a * integralMap p b).val ≤ entrySize p a.val := by
    apply (entrySize_mul_le p _ _).trans
    exact (mul_le_mul_of_nonneg_left (entrySize_integral_le_one p b)
      (entrySize_nonneg p a.val)).trans_eq (mul_one _)
  apply le_antisymm (hbound g h)
  have hi := hbound (g * integralMap p h) h⁻¹
  simpa only [map_inv, mul_inv_cancel_right] using hi

theorem entrySize_pos (g : LocalGL p) : 0 < entrySize p g.val := by
  by_contra h
  have hz : g.val = 0 := by
    ext i j
    exact norm_eq_zero.mp (le_antisymm
      ((entry_le_size p g.val i j).trans (le_of_not_gt h)) (norm_nonneg _))
  exact g.det_ne_zero (by rw [hz]; simp)

theorem exists_max_entry (g : LocalGL p) :
    ∃ i j : Fin 2, ‖g i j‖ = entrySize p g.val := by
  obtain ⟨q, _, hq⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin 2 × Fin 2)) (fun q => ‖g q.1 q.2‖)
    ⟨(0, 0), Finset.mem_univ _⟩
  exact ⟨q.1, q.2, le_antisymm (entry_le_size p g.val q.1 q.2)
    (entrySize_le p fun i j => hq (i, j) (Finset.mem_univ _))⟩

theorem entrySize_smul (a : ℚ_[p.1]) (M : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) :
    entrySize p (a • M) = ‖a‖ * entrySize p M := by
  simp only [entrySize, Matrix.smul_apply, smul_eq_mul, norm_mul]
  simp only [mul_max_of_nonneg _ _ (norm_nonneg a)]

private theorem mul_scalar_val (g : LocalGL p) (a : ℚ_[p.1]ˣ) :
    (g * GeneralLinearGroup.scalar (Fin 2) a).val = (a : ℚ_[p.1]) • g.val := by
  rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- The determinant ratio is the exponential radial coordinate of a lattice class. -/
def matrixRatio (g : LocalGL p) : ℝ := ‖g.val.det‖ / entrySize p g.val ^ 2

theorem matrixRatio_pos (g : LocalGL p) : 0 < matrixRatio p g :=
  div_pos (norm_pos_iff.mpr g.det_ne_zero) (sq_pos_of_pos (entrySize_pos p g))

theorem matrixRatio_mul_scalar (g : LocalGL p) (a : ℚ_[p.1]ˣ) :
    matrixRatio p (g * GeneralLinearGroup.scalar (Fin 2) a) = matrixRatio p g := by
  have ha : ‖(a : ℚ_[p.1])‖ ≠ 0 := (norm_pos_iff.mpr a.ne_zero).ne'
  simp only [matrixRatio, mul_scalar_val, Matrix.det_smul, Fintype.card_fin,
    norm_mul, norm_pow, entrySize_smul, mul_pow]
  field_simp

theorem matrixRatio_integral_mul (h : GL (Fin 2) ℤ_[p.1]) (g : LocalGL p) :
    matrixRatio p (integralMap p h * g) = matrixRatio p g := by
  unfold matrixRatio
  rw [entrySize_integral_mul]
  simp only [GeneralLinearGroup.coe_mul,
    Matrix.det_mul, norm_mul, integralMap_det_norm, one_mul]

theorem matrixRatio_mul_integral (g : LocalGL p) (h : GL (Fin 2) ℤ_[p.1]) :
    matrixRatio p (g * integralMap p h) = matrixRatio p g := by
  unfold matrixRatio
  rw [entrySize_mul_integral]
  simp only [GeneralLinearGroup.coe_mul,
    Matrix.det_mul, norm_mul, integralMap_det_norm, mul_one]

/-- Homotheties cancel from the radial coordinate. -/
def projectiveRatio : LocalPGL p → ℝ :=
  Quotient.lift (matrixRatio p) (by
    intro g h hgh
    have he : ProjGenLinGroup.mk g = ProjGenLinGroup.mk h := Quotient.sound hgh
    obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
    rw [← ha, matrixRatio_mul_scalar])

@[simp] theorem projectiveRatio_mk (g : LocalGL p) :
    projectiveRatio p (ProjGenLinGroup.mk g) = matrixRatio p g := rfl

theorem projectiveRatio_integral_mul (h : GL (Fin 2) ℤ_[p.1]) (g : LocalPGL p) :
    projectiveRatio p (ProjGenLinGroup.mk (integralMap p h) * g) = projectiveRatio p g := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g => rw [← map_mul, projectiveRatio_mk, projectiveRatio_mk, matrixRatio_integral_mul]

theorem projectiveRatio_mul_integral (g : LocalPGL p) (h : GL (Fin 2) ℤ_[p.1]) :
    projectiveRatio p (g * ProjGenLinGroup.mk (integralMap p h)) = projectiveRatio p g := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g => rw [← map_mul, projectiveRatio_mk, projectiveRatio_mk, matrixRatio_mul_integral]

/-- The radial coordinate on actual lattice-homothety vertices. -/
def vertexRatio : LocalVertex p → ℝ :=
  Quotient.lift (projectiveRatio p) (by
    intro g h hgh
    have he : (QuotientGroup.mk g : LocalVertex p) = QuotientGroup.mk h := Quotient.sound hgh
    obtain ⟨k, hk⟩ := QuotientGroup.eq.mp he
    change ProjGenLinGroup.mk (integralMap p k) = g⁻¹ * h at hk
    have hh : h = g * ProjGenLinGroup.mk (integralMap p k) := by
      rw [hk, mul_inv_cancel_left]
    rw [hh, projectiveRatio_mul_integral])

@[simp] theorem vertexRatio_mk (g : LocalPGL p) :
    vertexRatio p (QuotientGroup.mk g) = projectiveRatio p g := rfl

theorem vertexRatio_integral_smul (h : GL (Fin 2) ℤ_[p.1]) (v : LocalVertex p) :
    vertexRatio p (ProjGenLinGroup.mk (integralMap p h) • v) = vertexRatio p v := by
  induction v using Quotient.inductionOn with
  | h g => exact projectiveRatio_integral_mul p h g

/-- A diagonal lattice with a nonzero second basis vector. -/
def diagonalGL (d : ℚ_[p.1]) (hd : d ≠ 0) : LocalGL p :=
  ⟨!![1, 0; 0, d], !![1, 0; 0, d⁻¹],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hd],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hd]⟩

theorem matrixRatio_diagonal (d : ℚ_[p.1]) (hd : d ≠ 0) (hsmall : ‖d‖ ≤ 1) :
    matrixRatio p (diagonalGL p d hd) = ‖d‖ := by
  simp [matrixRatio, diagonalGL, entrySize, Matrix.det_fin_two,
    max_eq_left hsmall]

/-- Every projective matrix has an integral diagonal normal form, without a parity restriction. -/
theorem exists_integral_diagonal (g : LocalGL p) :
    ∃ (k l : GL (Fin 2) ℤ_[p.1]) (d : ℤ_[p.1]) (hd : (d : ℚ_[p.1]) ≠ 0),
      ProjGenLinGroup.mk g = ProjGenLinGroup.mk (integralMap p k) *
        ProjGenLinGroup.mk (diagonalGL p d hd) * ProjGenLinGroup.mk (integralMap p l) := by
  obtain ⟨i, j, hij⟩ := exists_max_entry p g
  let c : ℚ_[p.1] := g i j
  have hcsize : ‖c‖ = entrySize p g.val := hij
  have hcpos : 0 < ‖c‖ := by rw [hcsize]; exact entrySize_pos p g
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  let a : ℚ_[p.1]ˣ := Units.mk0 c hc0
  let N : LocalGL p := g * GeneralLinearGroup.scalar (Fin 2) a⁻¹
  have hN (i j : Fin 2) : ‖N i j‖ ≤ 1 := by
    dsimp only [N]
    rw [mul_scalar_val]
    change ‖c⁻¹ * g i j‖ ≤ 1
    rw [norm_mul, norm_inv, mul_comm, ← div_eq_mul_inv]
    apply (div_le_one hcpos).mpr
    rw [hcsize]
    exact entry_le_size p g.val i j
  let M : Matrix (Fin 2) (Fin 2) ℤ_[p.1] := fun i j => ⟨N i j, hN i j⟩
  obtain ⟨U, V, d, hU, hV, hdiag, hdiv⟩ :=
    GaloisForLFunctions.HTGeometry.exists_smithNormalForm M
  let U₀ : GL (Fin 2) ℤ_[p.1] := GeneralLinearGroup.mk'' U hU
  let V₀ : GL (Fin 2) ℤ_[p.1] := GeneralLinearGroup.mk'' V hV
  let H : LocalGL p := integralMap p U₀ * N * integralMap p V₀
  have hmat : H.val = (Matrix.diagonal d).map PadicInt.Coe.ringHom := by
    change U.map PadicInt.Coe.ringHom * M.map PadicInt.Coe.ringHom *
      V.map PadicInt.Coe.ringHom = _
    rw [← Matrix.map_mul, ← Matrix.map_mul, hdiag]
  have hprod : (d 0 : ℚ_[p.1]) * (d 1 : ℚ_[p.1]) ≠ 0 := by
    have h := H.det_ne_zero
    rw [hmat] at h
    simpa [Matrix.det_fin_two] using h
  have hd0 := (mul_ne_zero_iff.mp hprod).1
  have hd1 := (mul_ne_zero_iff.mp hprod).2
  obtain ⟨e, he⟩ := hdiv 0 1 (by norm_num)
  have hec : (d 1 : ℚ_[p.1]) = (d 0 : ℚ_[p.1]) * (e : ℚ_[p.1]) := by
    simpa only [PadicInt.coe_mul] using congrArg (fun x : ℤ_[p.1] => (x : ℚ_[p.1])) he
  have he0 : (e : ℚ_[p.1]) ≠ 0 := by
    intro h
    exact hd1 (by rw [hec, h, mul_zero])
  have hGL : H = diagonalGL p e he0 *
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (d 0 : ℚ_[p.1]) hd0) := by
    apply Units.ext
    rw [hmat, mul_scalar_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalGL, Matrix.smul_apply, smul_eq_mul, hec]
  have hproj : ProjGenLinGroup.mk (integralMap p U₀) * ProjGenLinGroup.mk g *
      ProjGenLinGroup.mk (integralMap p V₀) = ProjGenLinGroup.mk (diagonalGL p e he0) := by
    have h := congrArg (fun h : LocalGL p => ProjGenLinGroup.mk h) hGL
    simpa only [H, N, map_mul, ProjGenLinGroup.mk_scalar, mul_one] using h
  refine ⟨U₀⁻¹, V₀⁻¹, e, he0, ?_⟩
  simp only [map_inv]
  calc ProjGenLinGroup.mk g =
      (ProjGenLinGroup.mk (integralMap p U₀))⁻¹ *
        (ProjGenLinGroup.mk (integralMap p U₀) * ProjGenLinGroup.mk g *
          ProjGenLinGroup.mk (integralMap p V₀)) *
            (ProjGenLinGroup.mk (integralMap p V₀))⁻¹ := by group
    _ = _ := by rw [hproj]

private theorem entrySize_adjugate (M : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) :
    entrySize p M.adjugate = entrySize p M := by
  simp [entrySize, Matrix.adjugate_fin_two, max_assoc, max_left_comm, max_comm]

theorem matrixRatio_inv (g : LocalGL p) : matrixRatio p g⁻¹ = matrixRatio p g := by
  have hd : ‖g.val.det‖ ≠ 0 := (norm_pos_iff.mpr g.det_ne_zero).ne'
  have hn : entrySize p g.val ≠ 0 := (entrySize_pos p g).ne'
  have hi : (g⁻¹).val = g.val.det⁻¹ • g.val.adjugate := by
    rw [GeneralLinearGroup.coe_inv,
      Matrix.nonsing_inv_apply _ (isUnit_iff_ne_zero.mpr g.det_ne_zero)]
    simp only [Units.val_inv_eq_inv_val, IsUnit.unit_spec]
  have hs : entrySize p (g⁻¹).val = ‖g.val.det‖⁻¹ * entrySize p g.val := by
    rw [hi, entrySize_smul, norm_inv, entrySize_adjugate]
  unfold matrixRatio
  rw [hs, GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv, norm_inv]
  field_simp [hd, hn]

theorem projectiveRatio_inv (g : LocalPGL p) :
    projectiveRatio p g⁻¹ = projectiveRatio p g := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g => rw [← map_inv, projectiveRatio_mk, projectiveRatio_mk, matrixRatio_inv]

theorem vertexRatio_base : vertexRatio p (baseVertex p) = 1 := by
  change matrixRatio p (1 : LocalGL p) = 1
  simp [matrixRatio, entrySize]

theorem vertexRatio_pos (v : LocalVertex p) : 0 < vertexRatio p v := by
  induction v using Quotient.inductionOn with
  | h g =>
    induction g using ProjGenLinGroup.induction_on with
    | mk g => exact matrixRatio_pos p g

theorem vertexRatio_le_one (v : LocalVertex p) : vertexRatio p v ≤ 1 := by
  induction v using Quotient.inductionOn with
  | h g =>
    induction g using ProjGenLinGroup.induction_on with
    | mk g =>
      obtain ⟨k, l, d, hd, hg⟩ := exists_integral_diagonal p g
      rw [vertexRatio_mk, hg, projectiveRatio_mul_integral, projectiveRatio_integral_mul,
        projectiveRatio_mk, matrixRatio_diagonal p d hd d.2]
      exact d.2

/-- The radial coordinate detects the base lattice class exactly. -/
theorem vertexRatio_eq_one_iff (v : LocalVertex p) :
    vertexRatio p v = 1 ↔ v = baseVertex p := by
  constructor
  · induction v using Quotient.inductionOn with
    | h g =>
      induction g using ProjGenLinGroup.induction_on with
      | mk g =>
        intro hv
        obtain ⟨k, l, d, hd, hg⟩ := exists_integral_diagonal p g
        rw [vertexRatio_mk, hg, projectiveRatio_mul_integral, projectiveRatio_integral_mul,
          projectiveRatio_mk, matrixRatio_diagonal p d hd d.2] at hv
        have hdi : ProjGenLinGroup.mk (diagonalGL p d hd) ∈ integralPGL p := by
          apply integralPGL_of_entries_det_norm
          · intro i j
            fin_cases i <;> fin_cases j
            · norm_num [diagonalGL]
            · norm_num [diagonalGL]
            · norm_num [diagonalGL]
            · exact d.2
          · simpa [diagonalGL, Matrix.det_fin_two] using hv
        have hgmem : ProjGenLinGroup.mk g ∈ integralPGL p := by
          rw [hg]
          exact (integralPGL p).mul_mem ((integralPGL p).mul_mem ⟨k, rfl⟩ hdi) ⟨l, rfl⟩
        apply QuotientGroup.eq.mpr
        simpa only [mul_one] using (integralPGL p).inv_mem hgmem
  · intro h
    rw [h, vertexRatio_base]

/-- The two-point radial coordinate on actual projective lattice classes. -/
def localRatio (x y : LocalVertex p) : ℝ :=
  Quotient.liftOn x (fun g => vertexRatio p (g⁻¹ • y)) (by
    intro g h hgh
    have he : (QuotientGroup.mk g : LocalVertex p) = QuotientGroup.mk h := Quotient.sound hgh
    obtain ⟨k, hk⟩ := QuotientGroup.eq.mp he
    change ProjGenLinGroup.mk (integralMap p k) = g⁻¹ * h at hk
    have hh : h = g * ProjGenLinGroup.mk (integralMap p k) := by
      rw [hk, mul_inv_cancel_left]
    rw [hh, _root_.mul_inv_rev, mul_smul]
    have hi := vertexRatio_integral_smul p k⁻¹ (g⁻¹ • y)
    simpa only [map_inv] using hi.symm)

@[simp] theorem localRatio_mk (g h : LocalPGL p) :
    localRatio p (QuotientGroup.mk g) (QuotientGroup.mk h) =
      projectiveRatio p (g⁻¹ * h) := rfl

theorem localRatio_base (v : LocalVertex p) : localRatio p (baseVertex p) v = vertexRatio p v := by
  change vertexRatio p ((1 : LocalPGL p)⁻¹ • v) = _
  rw [inv_one, one_smul]

theorem localRatio_symm (x y : LocalVertex p) : localRatio p x y = localRatio p y x := by
  induction x using Quotient.inductionOn with
  | h g =>
    induction y using Quotient.inductionOn with
    | h h =>
      rw [localRatio_mk, localRatio_mk,
        show h⁻¹ * g = (g⁻¹ * h)⁻¹ by group, projectiveRatio_inv]

/-- The local radial kernel is invariant under simultaneous projective isometries. -/
theorem localRatio_smul (a : LocalPGL p) (x y : LocalVertex p) :
    localRatio p (a • x) (a • y) = localRatio p x y := by
  induction x using Quotient.inductionOn with
  | h g =>
    induction y using Quotient.inductionOn with
    | h h =>
      change projectiveRatio p ((a * g)⁻¹ * (a * h)) = projectiveRatio p (g⁻¹ * h)
      congr 1
      group

theorem localRatio_pos (x y : LocalVertex p) : 0 < localRatio p x y := by
  induction x using Quotient.inductionOn with
  | h g => exact vertexRatio_pos p (g⁻¹ • y)

theorem localRatio_le_one (x y : LocalVertex p) : localRatio p x y ≤ 1 := by
  induction x using Quotient.inductionOn with
  | h g => exact vertexRatio_le_one p (g⁻¹ • y)

/-- Unit radial coordinate is precisely equality of lattice classes. -/
theorem localRatio_eq_one_iff (x y : LocalVertex p) : localRatio p x y = 1 ↔ x = y := by
  induction x using Quotient.inductionOn with
  | h g =>
    induction y using Quotient.inductionOn with
    | h h =>
      change vertexRatio p (QuotientGroup.mk (g⁻¹ * h)) = 1 ↔
        (QuotientGroup.mk g : LocalVertex p) = QuotientGroup.mk h
      simp only [vertexRatio_eq_one_iff, baseVertex, QuotientGroup.eq,
        mul_one, Subgroup.inv_mem_iff]

#print axioms exists_integral_diagonal
#print axioms localRatio_smul
#print axioms localRatio_symm
#print axioms localRatio_eq_one_iff

end GaloisForLFunctions.HyperbolicArakelovTheory.AdelicRadial
