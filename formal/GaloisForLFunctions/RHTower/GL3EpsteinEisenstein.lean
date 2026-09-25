import GaloisForLFunctions.RHTower.GL3FundamentalDomain
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.Module.ZLattice.Basic


/-!
# The maximal parabolic Eisenstein series of `SL₃(ℤ)` (Epstein zeta)

The point `z ∈ h³` determines the positive definite ternary form `Q_z(v) = v · gram z · vᵀ =
‖v · mat z‖²` (`qf`, `qf_eq_sum_sq`). Writing `v = (v · mat z) · (mat z)⁻¹` bounds
`‖v‖² ≤ K² Q_z(v)` with `K` the operator bound of `(mat z)⁻¹` (`norm_sq_le_qf`), so the Epstein sum
`Z_z(s) = Σ_{v ∈ ℤ³ ∖ 0} Q_z(v)^{-s}` converges for `s > 3/2` by the lattice-sum bound
`Σ_{v ∈ ℤ³} ‖v‖^{-r} < ∞`, `r > 3` (`summable_epstein`, via `ZLattice.summable_norm_rpow`).

For `γ ∈ SL₃(ℤ)`, `gram(γz) = c⁻¹ γ gram z γᵀ` with `c = (γ gram z γᵀ)₂₂`, hence
`Q_{γz}(v) = c⁻¹ Q_z(vγ)` (`qf_slSmul`), and reindexing by the permutation `v ↦ vγ` of `ℤ³` gives
`Z_{γz}(s) = c^s Z_z(s)` (`epstein_slSmul`). Since `det gram(γz) = c⁻³ det gram z`, the normalised
series `E(z, s) = (det gram z)^{s/3} Z_z(s)` is `SL₃(ℤ)`-invariant (`epsteinE_slSmul`).
-/

open Matrix Module

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-! ### Summability of `‖v‖^{-r}` over `ℤ³` -/

/-- The standard lattice `ℤ³ ⊂ ℝ³`. -/
abbrev stdLattice : Submodule ℤ (Fin 3 → ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

theorem finrank_stdLattice : finrank ℤ stdLattice = 3 := by
  rw [ZLattice.rank ℝ stdLattice]; simp

/-- The inclusion `ℤ³ → ℝ³` lands in the standard lattice. -/
noncomputable def toStd (v : Fin 3 → ℤ) : stdLattice :=
  ⟨fun i => (v i : ℝ), by
    have : (fun i => (v i : ℝ)) = ∑ i, v i • Pi.basisFun ℝ (Fin 3) i := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩

theorem toStd_injective : Function.Injective toStd := by
  intro v w h
  ext i
  have := congrFun (congrArg Subtype.val h) i
  simp only [toStd] at this
  exact_mod_cast this

/-- **`Σ_{v ∈ ℤ³} ‖v‖^r` converges for `r < -3`.** -/
theorem summable_int_norm_rpow {r : ℝ} (hr : r < -3) :
    Summable fun v : Fin 3 → ℤ => ‖(fun i => (v i : ℝ))‖ ^ r := by
  have hL : r < -(finrank ℤ stdLattice : ℝ) := by
    rw [finrank_stdLattice]; push_cast; exact hr
  have h := (ZLattice.summable_norm_rpow stdLattice r hL).comp_injective toStd_injective
  refine h.congr fun v => ?_
  rfl

/-! ### The quadratic form of a point -/

/-- An integer vector as a real vector. -/
def vR (v : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (v i : ℝ)

/-- **The quadratic form** `Q_z(v) = v · gram z · vᵀ = ‖v · mat z‖²`. -/
noncomputable def qf (z : H3) (v : Fin 3 → ℤ) : ℝ := vR v ⬝ᵥ (z.gram *ᵥ vR v)

theorem qf_eq_sum_sq (z : H3) (v : Fin 3 → ℤ) : qf z v = ∑ j, (vR v ᵥ* z.mat) j ^ 2 := by
  simp only [qf, gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, sq]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  rfl

/-- The operator bound of `(mat z)⁻¹` in the sup norm. -/
noncomputable def invBound (z : H3) : ℝ := 1 + ∑ i, ∑ j, |z.mat⁻¹ i j|

theorem invBound_pos (z : H3) : 0 < invBound z := by
  unfold invBound; positivity

/-- **Lower bound**: `‖v‖² ≤ K² · Q_z(v)`. -/
theorem norm_sq_le_qf (z : H3) (v : Fin 3 → ℤ) : ‖vR v‖ ^ 2 ≤ invBound z ^ 2 * qf z v := by
  set w := vR v ᵥ* z.mat
  have hw : vR v = w ᵥ* z.mat⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 z.isUnit_mat),
      Matrix.vecMul_one]
  have hwj : ∀ j, |w j| ≤ Real.sqrt (qf z v) := by
    intro j
    rw [qf_eq_sum_sq]
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (f := fun j => w j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hnorm : ‖vR v‖ ≤ invBound z * Real.sqrt (qf z v) := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (invBound_pos z).le (Real.sqrt_nonneg _))).2
      fun i => ?_
    rw [Real.norm_eq_abs, hw]
    simp only [Matrix.vecMul, dotProduct]
    calc |∑ j, w j * z.mat⁻¹ j i| ≤ ∑ j, |w j| * |z.mat⁻¹ j i| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          simp [abs_mul]
      _ ≤ ∑ j, Real.sqrt (qf z v) * |z.mat⁻¹ j i| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hwj j) (abs_nonneg _)
      _ ≤ invBound z * Real.sqrt (qf z v) := by
          rw [← Finset.mul_sum, mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          unfold invBound
          have : ∑ j, |z.mat⁻¹ j i| ≤ ∑ j, ∑ k, |z.mat⁻¹ j k| :=
            Finset.sum_le_sum fun j _ => Finset.single_le_sum (f := fun k => |z.mat⁻¹ j k|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
          linarith
  have hq : 0 ≤ qf z v := by rw [qf_eq_sum_sq]; positivity
  calc ‖vR v‖ ^ 2 ≤ (invBound z * Real.sqrt (qf z v)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = invBound z ^ 2 * qf z v := by rw [mul_pow, Real.sq_sqrt hq]

theorem qf_nonneg (z : H3) (v : Fin 3 → ℤ) : 0 ≤ qf z v := by rw [qf_eq_sum_sq]; positivity

theorem vR_ne_zero {v : Fin 3 → ℤ} (hv : v ≠ 0) : vR v ≠ 0 := by
  intro h; apply hv; ext i; have := congrFun h i; simpa [vR] using this

theorem qf_pos (z : H3) {v : Fin 3 → ℤ} (hv : v ≠ 0) : 0 < qf z v := by
  have h1 : 0 < ‖vR v‖ ^ 2 := by have := norm_pos_iff.2 (vR_ne_zero hv); positivity
  have h2 := norm_sq_le_qf z v
  by_contra h
  have : qf z v = 0 := le_antisymm (not_lt.1 h) (qf_nonneg z v)
  rw [this, mul_zero] at h2
  linarith

/-! ### The Epstein series -/

/-- **The Epstein zeta function of the point `z`**: `Σ_{v ∈ ℤ³ ∖ 0} Q_z(v)^{-s}`. -/
noncomputable def epstein (z : H3) (s : ℝ) : ℝ :=
  ∑' v : Fin 3 → ℤ, if v = 0 then 0 else qf z v ^ (-s)

theorem summable_epstein (z : H3) {s : ℝ} (hs : 3 / 2 < s) :
    Summable fun v : Fin 3 → ℤ => if v = 0 then (0 : ℝ) else qf z v ^ (-s) := by
  have hK := invBound_pos z
  refine Summable.of_nonneg_of_le
    (fun v => by split_ifs; exacts [le_rfl, Real.rpow_nonneg (qf_nonneg z v) _]) (fun v => ?_)
    ((summable_int_norm_rpow (r := -(2 * s)) (by linarith)).mul_left ((invBound z ^ 2) ^ s))
  split_ifs with hv
  · positivity
  have hq := qf_pos z hv
  have hn : 0 < ‖vR v‖ := norm_pos_iff.2 (vR_ne_zero hv)
  have hle : ‖vR v‖ ^ 2 / invBound z ^ 2 ≤ qf z v := by
    rw [div_le_iff₀ (by positivity)]; linarith [norm_sq_le_qf z v]
  calc qf z v ^ (-s) ≤ (‖vR v‖ ^ 2 / invBound z ^ 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
    _ = (invBound z ^ 2) ^ s * ‖(fun i => (v i : ℝ))‖ ^ (-(2 * s)) := by
        rw [show (fun i => (v i : ℝ)) = vR v from rfl,
          Real.div_rpow (by positivity) (by positivity),
          Real.rpow_neg (by positivity : (0 : ℝ) ≤ invBound z ^ 2) s,
          div_inv_eq_mul, mul_comm, ← Real.rpow_natCast (‖vR v‖) 2, ← Real.rpow_mul hn.le]
        congr 2
        push_cast; ring

/-! ### Transformation under `SL₃(ℤ)` -/

/-- Right multiplication `v ↦ v γ` permutes `ℤ³`. -/
def vecMulEquiv (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) where
  toFun v := v ᵥ* (γ : Matrix (Fin 3) (Fin 3) ℤ)
  invFun v := v ᵥ* ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ)
  left_inv v := by
    simp only [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  right_inv v := by
    simp only [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

theorem vR_vecMul (v : Fin 3 → ℤ) (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
    vR (v ᵥ* (γ : Matrix (Fin 3) (Fin 3) ℤ)) =
      vR v ᵥ* ((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext j; simp [vR, Matrix.vecMul, dotProduct, slToGL]

/-- The normalising factor `(γ gram γᵀ)₂₂`. -/
noncomputable def normC (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3) : ℝ :=
  (((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) * z.gram *
    ((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) 2 2

theorem normC_pos (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3) : 0 < normC γ z :=
  (posDef_conj (slToGL γ) z).diag_pos

theorem gram_slSmul (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3) :
    (γ • z).gram = (normC γ z)⁻¹ •
      (((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) * z.gram *
        ((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) := by
  rw [sl_smul_def, smul_def, gram_ofMat_of_posDef (posDef_conj _ _)]
  rfl

/-- **Transformation of the quadratic form**: `Q_{γz}(v) = c⁻¹ Q_z(vγ)`. -/
theorem qf_slSmul (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3) (v : Fin 3 → ℤ) :
    qf (γ • z) v = (normC γ z)⁻¹ * qf z (vecMulEquiv γ v) := by
  have e : vR (vecMulEquiv γ v) =
      vR v ᵥ* ((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := vR_vecMul v γ
  simp only [qf, gram_slSmul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, e]
  congr 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.mulVec_transpose]

theorem vecMulEquiv_eq_zero_iff (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    vecMulEquiv γ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have := congrArg (vecMulEquiv γ).symm h
    rw [Equiv.symm_apply_apply] at this
    rw [this]
    simp [vecMulEquiv]
  · rintro rfl; simp [vecMulEquiv]

/-- **Transformation of the Epstein series**: `Z_{γz}(s) = c^s Z_z(s)`. -/
theorem epstein_slSmul (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3) (s : ℝ) :
    epstein (γ • z) s = normC γ z ^ s * epstein z s := by
  have hc := normC_pos γ z
  have hterm : ∀ v : Fin 3 → ℤ, (if v = 0 then (0 : ℝ) else qf (γ • z) v ^ (-s)) =
      normC γ z ^ s *
        (if vecMulEquiv γ v = 0 then 0 else qf z (vecMulEquiv γ v) ^ (-s)) := by
    intro v
    simp only [vecMulEquiv_eq_zero_iff]
    split_ifs
    · ring
    · rw [qf_slSmul, Real.mul_rpow (inv_nonneg.2 hc.le) (qf_nonneg _ _), Real.inv_rpow hc.le,
        Real.rpow_neg hc.le, inv_inv]
  rw [epstein, tsum_congr hterm, tsum_mul_left, epstein,
    (vecMulEquiv γ).tsum_eq (fun w => if w = 0 then (0 : ℝ) else qf z w ^ (-s))]

theorem det_gram_slSmul (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3) :
    (γ • z).gram.det = (normC γ z)⁻¹ ^ 3 * z.gram.det := by
  have hdet : ((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := by
    have := RingHom.map_det (Int.castRingHom ℝ) (γ : Matrix (Fin 3) (Fin 3) ℤ)
    rw [γ.2, map_one] at this
    exact this.symm
  rw [gram_slSmul, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hdet]
  ring

/-- **The maximal parabolic Eisenstein series of `SL₃(ℤ)`** (normalised Epstein zeta):
`E(z, s) = (det gram z)^{s/3} Σ_{v ∈ ℤ³ ∖ 0} Q_z(v)^{-s}`. -/
noncomputable def epsteinE (z : H3) (s : ℝ) : ℝ := z.gram.det ^ (s / 3) * epstein z s

/-- **`E(z, s)` is `SL₃(ℤ)`-invariant.** -/
theorem epsteinE_slSmul (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3) (s : ℝ) :
    epsteinE (γ • z) s = epsteinE z s := by
  have hc := normC_pos γ z
  have hD : 0 < z.gram.det := z.posDef_gram.det_pos
  rw [epsteinE, epsteinE, epstein_slSmul, det_gram_slSmul,
    Real.mul_rpow (by positivity) hD.le, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    Real.inv_rpow hc.le]
  have e : ((3 : ℕ) : ℝ) * (s / 3) = s := by push_cast; ring
  rw [e]
  field_simp

end H3
end GaloisForLFunctions.RHTower.GL3
