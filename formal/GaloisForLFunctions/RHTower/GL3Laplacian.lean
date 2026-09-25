import GaloisForLFunctions.RHTower.GL3FundamentalDomain
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2


/-!
# The invariant Laplacian of `h³`

For a function `F : h³ → ℂ` and a point `z`, the exponential chart at `z` is
`v ↦ F(mat z · exp(v + vᵀ) · 1)` on the Euclidean space of `3 × 3` arrays with the Frobenius inner
product (`chart`); `t ↦ mat z · exp(tY) · 1` is the geodesic through `z` in direction `Y`. The
Laplacian is the Euclidean Laplacian of the chart at the origin (`lap`), i.e. the trace of the
Hessian along geodesics.

**Invariance.** For `h ∈ GL₃(ℝ)`, the sections `h · mat z` and `mat (h·z)` of the orbit map differ
by an element of the stabilizer of `1`, which is a nonzero scalar times an orthogonal matrix `o`
(`exists_orthogonal_of_smul_one`). Scalars act trivially, and `o` rotates the chart by the Frobenius
isometry `Y ↦ oYoᵀ` (`chart_comp_smul`, `symExp_conjIso`). The Euclidean Laplacian commutes with
linear isometries (`laplacian_comp_linearIsometryEquiv`), so `Δ(F ∘ h) = (ΔF) ∘ h` for every `h` and
every `F` (`lap_comp_smul`), with no regularity assumption. In particular `Δ` commutes with `SL₃(ℤ)`.
-/

open Matrix Laplacian InnerProductSpace

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-! ### The stabilizer of the base point -/

theorem gram_one : (1 : H3).gram = 1 := by simp [gram, mat_one]

/-- An element fixing the base point `1` is a nonzero scalar times an orthogonal matrix. -/
theorem exists_orthogonal_of_smul_one {g : GL (Fin 3) ℝ} (hg : g • (1 : H3) = 1) :
    ∃ c : ℝ, c ≠ 0 ∧ ∃ o : Matrix (Fin 3) (Fin 3) ℝ, o * oᵀ = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) ℝ) = c • o := by
  have h := (smul_eq_self_iff g 1).1 hg
  rw [gram_one, Matrix.mul_one] at h
  set c1 := ((g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) 2 2
  have hc1 : 0 < c1 := by
    have := posDef_conj g 1
    rw [gram_one, Matrix.mul_one] at this
    exact this.diag_pos
  set c := Real.sqrt c1
  have hc : 0 < c := Real.sqrt_pos.2 hc1
  refine ⟨c, hc.ne', c⁻¹ • (g : Matrix (Fin 3) (Fin 3) ℝ), ?_, ?_⟩
  · rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul]
    have : c⁻¹ * c⁻¹ * c1 = 1 := by
      rw [← mul_inv, ← sq, Real.sq_sqrt hc1.le, inv_mul_cancel₀ hc1.ne']
    rw [this, one_smul]
  · rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- An orthogonal matrix moves a point `ofMat S` by congruence. -/
theorem smul_ofMat_orthogonal {o : Matrix (Fin 3) (Fin 3) ℝ} (ho : o * oᵀ = 1) {S : Matrix (Fin 3) (Fin 3) ℝ}
    (hS : S.PosDef) (g : GL (Fin 3) ℝ) (hg : (g : Matrix (Fin 3) (Fin 3) ℝ) = o) :
    g • ofMat S = ofMat (o * S * oᵀ) := by
  have hU : IsUnit o := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact IsUnit.of_mul_eq_one (oᵀ.det) (by rw [← Matrix.det_mul, ho, Matrix.det_one])
  have hP : (o * S * oᵀ).PosDef := by
    have := (IsUnit.posDef_star_right_conjugate_iff (x := S) hU).2 hS
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  rw [smul_def, gram_ofMat_of_posDef hS, Matrix.mul_smul, Matrix.smul_mul, hg,
    ofMat_smul hP (inv_pos.2 hS.diag_pos)]

/-! ### Isometry invariance of the Euclidean Laplacian -/

/-- The Laplacian of a real inner product space commutes with linear isometries. -/
theorem laplacian_comp_linearIsometryEquiv {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E ≃ₗᵢ[ℝ] E) (f : E → F) (x : E) : Δ (f ∘ L) x = Δ f (L x) := by
  set v := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ L) v,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (v.map L)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := L.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (Set.mem_univ (L x)) 2
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have h' := congrArg (fun T => T ![v i, v i]) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h'
  rw [OrthonormalBasis.map_apply]
  calc iteratedFDeriv ℝ 2 (f ∘ L) x ![v i, v i]
      = iteratedFDeriv ℝ 2 f (L x) (fun j => L (![v i, v i] j)) := h'
    _ = iteratedFDeriv ℝ 2 f (L x) ![L (v i), L (v i)] := by
        congr 1
        funext j
        fin_cases j <;> rfl

/-! ### The exponential chart -/

/-- Directions at a point: `3 × 3` real arrays with the Frobenius inner product. -/
abbrev Dir := EuclideanSpace ℝ (Fin 3 × Fin 3)

/-- The matrix of a direction. -/
def toMat (v : Dir) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => v (i, j)

/-- `exp(Y + Yᵀ)`, a positive definite matrix. -/
noncomputable def symExp (v : Dir) : Matrix (Fin 3) (Fin 3) ℝ :=
  NormedSpace.exp (toMat v + (toMat v)ᵀ)

theorem posDef_symExp (v : Dir) : (symExp v).PosDef := by
  set S := toMat v + (toMat v)ᵀ
  have hS : Sᵀ = S := by simp [S, add_comm]
  have hsplit : symExp v = NormedSpace.exp ((1 / 2 : ℝ) • S) * (NormedSpace.exp ((1 / 2 : ℝ) • S))ᵀ := by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul, hS, ← Matrix.exp_add_of_commute _ _
      (Commute.refl _), ← add_smul]
    norm_num [symExp, S]
  rw [hsplit]
  exact posDef_mul_transpose (Matrix.isUnit_exp _)

/-- The exponential chart at `z`: `v ↦ mat z · exp(v + vᵀ) · 1`, i.e. the geodesic spray of `h³` at
`z`. -/
noncomputable def chart (F : H3 → ℂ) (z : H3) (v : Dir) : ℂ := F (toGL z • ofMat (symExp v))

/-- **The invariant Laplacian on `h³`**: the Euclidean Laplacian of `F` in the exponential chart at
`z`, at the origin. -/
noncomputable def lap (F : H3 → ℂ) (z : H3) : ℂ := Δ (chart F z) 0

/-! ### Orthogonal conjugation of directions -/

/-- The direction with a given matrix. -/
def ofMatDir (A : Matrix (Fin 3) (Fin 3) ℝ) : Dir := WithLp.toLp 2 fun p => A p.1 p.2

@[simp] theorem toMat_ofMatDir (A : Matrix (Fin 3) (Fin 3) ℝ) : toMat (ofMatDir A) = A := rfl

@[simp] theorem ofMatDir_toMat (v : Dir) : ofMatDir (toMat v) = v := rfl

theorem toMat_add (v w : Dir) : toMat (v + w) = toMat v + toMat w := rfl

theorem toMat_smul (r : ℝ) (v : Dir) : toMat (r • v) = r • toMat v := rfl

theorem ofMatDir_add (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    ofMatDir (A + B) = ofMatDir A + ofMatDir B := rfl

theorem ofMatDir_smul (r : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ofMatDir (r • A) = r • ofMatDir A := rfl

/-- The Frobenius pairing is the trace pairing. -/
theorem sum_mul_eq_trace (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ i, ∑ j, A i j * B i j = (Aᵀ * B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem inner_eq_sum (v w : Dir) : inner ℝ v w = ∑ i, ∑ j, toMat v i j * toMat w i j := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [toMat, mul_comm]

/-- Conjugation `Y ↦ oYoᵀ` by an orthogonal matrix, as a linear isometry of the directions. -/
noncomputable def conjIso (o : Matrix (Fin 3) (Fin 3) ℝ) (ho : o * oᵀ = 1) : Dir ≃ₗᵢ[ℝ] Dir :=
  LinearEquiv.isometryOfInner
    { toFun := fun v => ofMatDir (o * toMat v * oᵀ)
      map_add' := fun v w => by
        simp only [toMat_add, Matrix.mul_add, Matrix.add_mul, ofMatDir_add]
      map_smul' := fun r v => by
        simp only [toMat_smul, Matrix.mul_smul, Matrix.smul_mul, ofMatDir_smul, RingHom.id_apply]
      invFun := fun v => ofMatDir (oᵀ * toMat v * o)
      left_inv := fun v => by
        have ho' : oᵀ * o = 1 := mul_eq_one_comm.1 ho
        show ofMatDir (oᵀ * (o * toMat v * oᵀ) * o) = v
        rw [show oᵀ * (o * toMat v * oᵀ) * o = (oᵀ * o) * toMat v * (oᵀ * o) by
          simp only [Matrix.mul_assoc], ho', Matrix.one_mul, Matrix.mul_one, ofMatDir_toMat]
      right_inv := fun v => by
        show ofMatDir (o * (oᵀ * toMat v * o) * oᵀ) = v
        rw [show o * (oᵀ * toMat v * o) * oᵀ = (o * oᵀ) * toMat v * (o * oᵀ) by
          simp only [Matrix.mul_assoc], ho, Matrix.one_mul, Matrix.mul_one, ofMatDir_toMat] }
    (fun v w => by
      have ho' : oᵀ * o = 1 := mul_eq_one_comm.1 ho
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      rw [inner_eq_sum, inner_eq_sum, toMat_ofMatDir, toMat_ofMatDir, sum_mul_eq_trace,
        sum_mul_eq_trace]
      have e : (o * toMat v * oᵀ)ᵀ * (o * toMat w * oᵀ) = o * ((toMat v)ᵀ * toMat w) * oᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc oᵀ o, ho', Matrix.one_mul]
      rw [e, Matrix.trace_mul_comm (o * _) oᵀ, ← Matrix.mul_assoc, ho', Matrix.one_mul])

theorem toMat_conjIso {o : Matrix (Fin 3) (Fin 3) ℝ} (ho : o * oᵀ = 1) (v : Dir) :
    toMat (conjIso o ho v) = o * toMat v * oᵀ := rfl

theorem symExp_conjIso {o : Matrix (Fin 3) (Fin 3) ℝ} (ho : o * oᵀ = 1) (v : Dir) :
    symExp (conjIso o ho v) = o * symExp v * oᵀ := by
  have hinv : o⁻¹ = oᵀ := Matrix.inv_eq_right_inv ho
  have hU : IsUnit o := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact IsUnit.of_mul_eq_one (oᵀ.det) (by rw [← Matrix.det_mul, ho, Matrix.det_one])
  rw [symExp, symExp, toMat_conjIso, ← hinv, ← Matrix.exp_conj _ _ hU]
  congr 1
  rw [hinv]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]

/-! ### Invariance of the Laplacian -/

/-- Changing the section by an element of the stabilizer of `1` rotates the exponential chart. -/
theorem chart_comp_smul (F : H3 → ℂ) (h : GL (Fin 3) ℝ) (z : H3) :
    ∃ (o : Matrix (Fin 3) (Fin 3) ℝ) (ho : o * oᵀ = 1),
      chart (fun w => F (h • w)) z = chart F (h • z) ∘ conjIso o ho := by
  set g := (toGL (h • z))⁻¹ * h * toGL z
  have hg1 : g • (1 : H3) = 1 := by
    simp only [g, mul_smul, toGL_smul_one]
    rw [inv_smul_eq_iff, toGL_smul_one]
  obtain ⟨c, hc, o, ho, hgo⟩ := exists_orthogonal_of_smul_one hg1
  let go : GL (Fin 3) ℝ := ⟨o, oᵀ, ho, mul_eq_one_comm.1 ho⟩
  refine ⟨o, ho, funext fun v => ?_⟩
  have hsplit : h * toGL z = toGL (h • z) * g := by
    simp only [g, ← mul_assoc, mul_inv_cancel, one_mul]
  have hX : g • ofMat (symExp v) = ofMat (symExp (conjIso o ho v)) := by
    rw [smul_eq_of_val_eq_smul (g := go) hc hgo, symExp_conjIso,
      smul_ofMat_orthogonal ho (posDef_symExp v) go rfl]
  show F (h • (toGL z • ofMat (symExp v))) = F (toGL (h • z) • ofMat (symExp (conjIso o ho v)))
  rw [← mul_smul, hsplit, mul_smul, hX]

/-- **The Laplacian is `GL₃(ℝ)`-invariant**: `Δ(F ∘ h) = (ΔF) ∘ h` for every `h ∈ GL₃(ℝ)` and every
function `F`, with no regularity assumption. -/
theorem lap_comp_smul (F : H3 → ℂ) (h : GL (Fin 3) ℝ) (z : H3) :
    lap (fun w => F (h • w)) z = lap F (h • z) := by
  obtain ⟨o, ho, hc⟩ := chart_comp_smul F h z
  rw [lap, hc, laplacian_comp_linearIsometryEquiv, map_zero, lap]

/-- **The Laplacian commutes with `SL₃(ℤ)`.** -/
theorem lap_comp_slSmul (F : H3 → ℂ) (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3) :
    lap (fun w => F (γ • w)) z = lap F (γ • z) :=
  lap_comp_smul F (slToGL γ) z

end H3
end GaloisForLFunctions.RHTower.GL3
