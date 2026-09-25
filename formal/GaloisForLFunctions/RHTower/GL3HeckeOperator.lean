import GaloisForLFunctions.RHTower.GL3PowerFunctionComplex
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs


/-!
# The Hecke operator `T_p` on `SL₃(ℤ)\h³`

The `p² + p + 1` upper triangular matrices `diag(p,1,1)`, `[[1,x,0],[0,p,0],[0,0,1]]`,
`[[1,0,y],[0,1,w],[0,0,p]]` (`heckeRep`) are indexed by the points of `P²(𝔽_p)`: the row lattice of
each is the kernel mod `p` of the functional `(1,0,0)`, `(−x,1,0)` or `(−y,−w,1)` (`heckeFun`), and it
contains every integer vector in that kernel (`exists_comb_of_heckeFun`).

For `γ ∈ SL₃(ℤ)` the rows of `δ_i γ` are killed by the transported functional `γ⁻¹ a_i` mod `p`, so
they lie in the row lattice of the representative `δ_{σ(i)}` of that projective point:
`δ_i γ = C δ_{σ(i)}` with `C` integral of determinant one (`exists_heckeRep_mul`). The map `σ` has a
left inverse given by `γ⁻¹`, hence is a permutation (`heckePerm_bijective`).

Therefore `(T_p F)(z) = Σ_i F(δ_i z)` is again `SL₃(ℤ)`-invariant when `F` is (`heckeOp_smul`), and,
since each `δ_i` acts through `GL₃(ℝ)`, `T_p` commutes with the invariant Laplacian on smooth
functions (`lap_heckeOp`).
-/

open Matrix Laplacian InnerProductSpace

namespace GaloisForLFunctions.RHTower.GL3

variable (p : ℕ) [Fact p.Prime]

/-! ### The `p² + p + 1` Hecke representatives -/

/-- The index set of the Hecke representatives of `SL₃(ℤ) diag(1,1,p) SL₃(ℤ)`. -/
abbrev HeckeIdx := Unit ⊕ ZMod p ⊕ (ZMod p × ZMod p)

/-- The upper triangular representatives `diag(p,1,1)`, `[[1,x,0],[0,p,0],[0,0,1]]`,
`[[1,0,y],[0,1,w],[0,0,p]]`. -/
def heckeRep : HeckeIdx p → Matrix (Fin 3) (Fin 3) ℤ
  | .inl _ => !![(p : ℤ), 0, 0; 0, 1, 0; 0, 0, 1]
  | .inr (.inl x) => !![1, (x.val : ℤ), 0; 0, (p : ℤ), 0; 0, 0, 1]
  | .inr (.inr (y, w)) => !![1, 0, (y.val : ℤ); 0, 1, (w.val : ℤ); 0, 0, (p : ℤ)]

theorem det_heckeRep (i : HeckeIdx p) : (heckeRep p i).det = p := by
  rcases i with _ | x | ⟨y, w⟩ <;> simp [heckeRep, Matrix.det_fin_three]

/-- The functional mod `p` cutting out the row lattice of a representative. -/
def heckeFun : HeckeIdx p → (Fin 3 → ZMod p)
  | .inl _ => ![1, 0, 0]
  | .inr (.inl x) => ![-x, 1, 0]
  | .inr (.inr (y, w)) => ![-y, -w, 1]

/-- The integer vector `v` reduced mod `p`. -/
def redVec (v : Fin 3 → ℤ) : Fin 3 → ZMod p := fun i => (v i : ZMod p)

/-- Every row of a representative is killed by its functional mod `p`. -/
theorem heckeFun_row (i : HeckeIdx p) (r : Fin 3) :
    heckeFun p i ⬝ᵥ redVec p (heckeRep p i r) = 0 := by
  rcases i with _ | x | ⟨y, w⟩ <;> fin_cases r <;>
    simp [heckeFun, heckeRep, redVec, dotProduct, Fin.sum_univ_three]

/-- **The row lattice of a representative contains the kernel of its functional**: every integer
vector killed mod `p` is an integer combination of the rows. -/
theorem exists_comb_of_heckeFun (i : HeckeIdx p) (v : Fin 3 → ℤ)
    (hv : heckeFun p i ⬝ᵥ redVec p v = 0) : ∃ c : Fin 3 → ℤ, v = c ᵥ* heckeRep p i := by
  rcases i with _ | x | ⟨y, w⟩
  · have h : ((v 0 : ℤ) : ZMod p) = 0 := by
      simpa [heckeFun, redVec, dotProduct, Fin.sum_univ_three] using hv
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h
    refine ⟨![k, v 1, v 2], ?_⟩
    ext j; fin_cases j <;> simp [heckeRep, vecMul, dotProduct, Fin.sum_univ_three, hk]; ring
  · have h : (((v 1 - (x.val : ℤ) * v 0 : ℤ)) : ZMod p) = 0 := by
      have := hv
      simp [heckeFun, redVec, dotProduct, Fin.sum_univ_three] at this
      push_cast
      simp only [ZMod.natCast_zmod_val]
      linear_combination this
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h
    refine ⟨![v 0, k, v 2], ?_⟩
    simp only [ZMod.natCast_val] at hk
    ext j; fin_cases j <;> simp [heckeRep, vecMul, dotProduct, Fin.sum_univ_three]
    linarith
  · have h : (((v 2 - (y.val : ℤ) * v 0 - (w.val : ℤ) * v 1 : ℤ)) : ZMod p) = 0 := by
      have := hv
      simp [heckeFun, redVec, dotProduct, Fin.sum_univ_three] at this
      push_cast
      simp only [ZMod.natCast_zmod_val]
      linear_combination this
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h
    refine ⟨![v 0, v 1, k], ?_⟩
    simp only [ZMod.natCast_val] at hk
    ext j; fin_cases j <;> simp [heckeRep, vecMul, dotProduct, Fin.sum_univ_three]
    linarith

/-! ### Normalising a functional to a representative -/

/-- The representative whose functional is proportional to a nonzero functional `a`. -/
noncomputable def heckeIdxOf (a : Fin 3 → ZMod p) : HeckeIdx p := by
  classical
  exact if a 2 = 0 then (if a 1 = 0 then .inl () else .inr (.inl (-(a 0 / a 1))))
    else .inr (.inr (-(a 0 / a 2), -(a 1 / a 2)))

/-- The normalising scalar. -/
noncomputable def heckeScale (a : Fin 3 → ZMod p) : ZMod p := by
  classical
  exact if a 2 = 0 then (if a 1 = 0 then (a 0)⁻¹ else (a 1)⁻¹) else (a 2)⁻¹

theorem ne_zero_of_ne {a : Fin 3 → ZMod p} (ha : a ≠ 0) (h1 : a 1 = 0) (h2 : a 2 = 0) :
    a 0 ≠ 0 := by
  intro h0; apply ha; ext j; fin_cases j <;> simp [h0, h1, h2]

theorem heckeFun_heckeIdxOf {a : Fin 3 → ZMod p} (ha : a ≠ 0) :
    heckeFun p (heckeIdxOf p a) = heckeScale p a • a := by
  classical
  by_cases h2 : a 2 = 0
  · by_cases h1 : a 1 = 0
    · have h0 := ne_zero_of_ne p ha h1 h2
      simp only [heckeIdxOf, heckeScale, h1, h2, if_true]
      ext j; fin_cases j <;> simp [heckeFun, h1, h2, h0]
    · simp only [heckeIdxOf, heckeScale, h1, h2, if_true, if_false]
      ext j; fin_cases j <;> simp [heckeFun, h2] <;> field_simp
  · simp only [heckeIdxOf, heckeScale, h2, if_false]
    ext j; fin_cases j <;> simp [heckeFun] <;> field_simp

theorem heckeScale_ne_zero {a : Fin 3 → ZMod p} (ha : a ≠ 0) : heckeScale p a ≠ 0 := by
  classical
  by_cases h2 : a 2 = 0
  · by_cases h1 : a 1 = 0
    · simp [heckeScale, h1, h2, ne_zero_of_ne p ha h1 h2]
    · simp [heckeScale, h1, h2]
  · simp [heckeScale, h2]

theorem heckeIdxOf_smul {a : Fin 3 → ZMod p} {u : ZMod p} (hu : u ≠ 0) :
    heckeIdxOf p (u • a) = heckeIdxOf p a := by
  classical
  simp only [heckeIdxOf, Pi.smul_apply, smul_eq_mul, mul_eq_zero, hu, false_or]
  by_cases h2 : a 2 = 0
  · by_cases h1 : a 1 = 0
    · simp [h1, h2]
    · simp only [h1, h2, if_true, if_false]
      congr 3
      field_simp
  · simp only [h2, if_false]
    congr 2
    field_simp

theorem heckeIdxOf_heckeFun (i : HeckeIdx p) : heckeIdxOf p (heckeFun p i) = i := by
  classical
  rcases i with _ | x | ⟨y, w⟩ <;> simp [heckeIdxOf, heckeFun]

theorem heckeFun_ne_zero (i : HeckeIdx p) : heckeFun p i ≠ 0 := by
  intro h
  rcases i with _ | x | ⟨y, w⟩
  · have := congrFun h 0; simp [heckeFun] at this
  · have := congrFun h 1; simp [heckeFun] at this
  · have := congrFun h 2; simp [heckeFun] at this

/-! ### The Hecke permutation -/

/-- Reduction of an integral matrix mod `p`. -/
abbrev redMat (M : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  M.map (Int.castRingHom (ZMod p))

theorem redMat_mul (M N : Matrix (Fin 3) (Fin 3) ℤ) :
    redMat p (M * N) = redMat p M * redMat p N := Matrix.map_mul

theorem redVec_vecMul (v : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℤ) :
    redVec p (v ᵥ* M) = redVec p v ᵥ* redMat p M := by
  ext j; simp [redVec, vecMul, dotProduct]

/-- The functional transported by `γ`. -/
noncomputable def transFun (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (i : HeckeIdx p) :
    Fin 3 → ZMod p :=
  redMat p ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ heckeFun p i

theorem redMat_mul_inv (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
    redMat p (γ : Matrix (Fin 3) (Fin 3) ℤ) *
      redMat p ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
  rw [← redMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one]
  exact map_one ((Int.castRingHom (ZMod p)).mapMatrix)

theorem transFun_ne_zero (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (i : HeckeIdx p) :
    transFun p γ i ≠ 0 := by
  intro h
  apply heckeFun_ne_zero p i
  have := congrArg (fun v => redMat p (γ : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ v) h
  simp only [transFun, Matrix.mulVec_mulVec, redMat_mul_inv, Matrix.one_mulVec,
    Matrix.mulVec_zero] at this
  exact this

/-- **The permutation of the representatives induced by `γ`.** -/
noncomputable def heckePerm (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (i : HeckeIdx p) :
    HeckeIdx p := heckeIdxOf p (transFun p γ i)

theorem heckePerm_inv (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (i : HeckeIdx p) :
    heckePerm p γ⁻¹ (heckePerm p γ i) = i := by
  have hne := transFun_ne_zero p γ i
  have key : transFun p γ⁻¹ (heckePerm p γ i) = heckeScale p (transFun p γ i) • heckeFun p i := by
    show redMat p (((γ⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ
      heckeFun p (heckeIdxOf p (transFun p γ i)) = _
    rw [heckeFun_heckeIdxOf p hne, Matrix.mulVec_smul, inv_inv]
    congr 1
    show redMat p (γ : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ
      (redMat p ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ
        heckeFun p i) = heckeFun p i
    rw [Matrix.mulVec_mulVec, redMat_mul_inv, Matrix.one_mulVec]
  rw [heckePerm, key, heckeIdxOf_smul p (heckeScale_ne_zero p hne), heckeIdxOf_heckeFun]

theorem heckePerm_bijective (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
    Function.Bijective (heckePerm p γ) :=
  (Function.LeftInverse.injective (heckePerm_inv p γ)).bijective_of_finite

/-- **Right multiplication by `γ` permutes the representatives up to `SL₃(ℤ)`**:
`δ_i γ = C δ_{σ(i)}` with `C ∈ SL₃(ℤ)`. -/
theorem exists_heckeRep_mul (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (i : HeckeIdx p) :
    ∃ C : Matrix.SpecialLinearGroup (Fin 3) ℤ,
      heckeRep p i * (γ : Matrix (Fin 3) (Fin 3) ℤ) =
        (C : Matrix (Fin 3) (Fin 3) ℤ) * heckeRep p (heckePerm p γ i) := by
  set j := heckePerm p γ i
  have hrow : ∀ k : Fin 3, ∃ c : Fin 3 → ℤ,
      (heckeRep p i * (γ : Matrix (Fin 3) (Fin 3) ℤ)) k = c ᵥ* heckeRep p j := by
    intro k
    apply exists_comb_of_heckeFun
    have hj : heckeFun p j = heckeScale p (transFun p γ i) • transFun p γ i :=
      heckeFun_heckeIdxOf p (transFun_ne_zero p γ i)
    rw [hj, smul_dotProduct, show (heckeRep p i * (γ : Matrix (Fin 3) (Fin 3) ℤ)) k =
      heckeRep p i k ᵥ* (γ : Matrix (Fin 3) (Fin 3) ℤ) from rfl, redVec_vecMul, dotProduct_comm,
      ← Matrix.dotProduct_mulVec, transFun, Matrix.mulVec_mulVec, redMat_mul_inv,
      Matrix.one_mulVec, dotProduct_comm, heckeFun_row, smul_zero]
  choose c hc using hrow
  set Cm : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of c
  have hCm : heckeRep p i * (γ : Matrix (Fin 3) (Fin 3) ℤ) = Cm * heckeRep p j := by
    ext k l
    rw [hc k]
    rfl
  have hdet : Cm.det = 1 := by
    have := congrArg Matrix.det hCm
    rw [Matrix.det_mul, Matrix.det_mul, det_heckeRep, det_heckeRep, γ.2, mul_one] at this
    have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact (mul_right_cancel₀ hp (this.symm.trans (one_mul _).symm))
  exact ⟨⟨Cm, hdet⟩, hCm⟩

/-! ### The Hecke operator `T_p` -/

theorem det_heckeRep_real (i : HeckeIdx p) :
    ((heckeRep p i).map (Int.castRingHom ℝ)).det ≠ 0 := by
  have h := RingHom.map_det (Int.castRingHom ℝ) (heckeRep p i)
  rw [det_heckeRep] at h
  change ((Int.castRingHom ℝ).mapMatrix (heckeRep p i)).det ≠ 0
  rw [← h, eq_intCast, Int.cast_natCast]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- A representative as an element of `GL₃(ℝ)`. -/
noncomputable def heckeGL (i : HeckeIdx p) : GL (Fin 3) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_heckeRep_real p i)

/-- **The Hecke operator** `(T_p F)(z) = Σ_{δ} F(δ z)` over the `p² + p + 1` representatives of
`SL₃(ℤ)\SL₃(ℤ) diag(1,1,p) SL₃(ℤ)`. -/
noncomputable def heckeOp (F : H3 → ℂ) (z : H3) : ℂ := ∑ i, F (heckeGL p i • z)

theorem heckeGL_mul_slToGL (γ C : Matrix.SpecialLinearGroup (Fin 3) ℤ) (i : HeckeIdx p)
    (h : heckeRep p i * (γ : Matrix (Fin 3) (Fin 3) ℤ) =
      (C : Matrix (Fin 3) (Fin 3) ℤ) * heckeRep p (heckePerm p γ i)) :
    heckeGL p i * H3.slToGL γ = H3.slToGL C * heckeGL p (heckePerm p γ i) := by
  apply Units.ext
  have := congrArg (fun M => M.map (Int.castRingHom ℝ)) h
  simp only [Matrix.map_mul] at this
  exact this

/-- **`T_p` preserves `SL₃(ℤ)`-invariant functions.** -/
theorem heckeOp_smul {F : H3 → ℂ}
    (hF : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3), F (γ • z) = F z)
    (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (z : H3) : heckeOp p F (γ • z) = heckeOp p F z := by
  have hterm : ∀ i, F (heckeGL p i • γ • z) = F (heckeGL p (heckePerm p γ i) • z) := by
    intro i
    obtain ⟨C, hC⟩ := exists_heckeRep_mul p γ i
    rw [H3.sl_smul_def, ← mul_smul, heckeGL_mul_slToGL p γ C i hC, mul_smul, ← H3.sl_smul_def, hF]
  simp only [heckeOp, hterm]
  exact Equiv.sum_comp (Equiv.ofBijective _ (heckePerm_bijective p γ)) (fun j => F (heckeGL p j • z))

/-! ### `T_p` commutes with the Laplacian -/

theorem contDiff_chart_comp_smul {F : H3 → ℂ} (hF : H3.IsSmooth F) (h : GL (Fin 3) ℝ) (z : H3) :
    ContDiff ℝ ⊤ (H3.chart (fun w => F (h • w)) z) := by
  obtain ⟨o, ho, hc⟩ := H3.chart_comp_smul F h z
  rw [hc]
  exact (H3.contDiff_chart hF (h • z)).comp (H3.conjIso o ho).contDiff

theorem laplacian_finset_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} (s : Finset ι) (f : ι → E → ℂ) (x : E)
    (hf : ∀ i ∈ s, ContDiff ℝ ⊤ (f i)) :
    Δ (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, Δ (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
      simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hs : ContDiff ℝ ⊤ (fun y => ∑ i ∈ s, f i y) :=
        ContDiff.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have h1 : ContDiffAt ℝ 2 (f a) x :=
        ((hf a (Finset.mem_insert_self a s)).of_le (by exact_mod_cast le_top)).contDiffAt
      have h2 : ContDiffAt ℝ 2 (fun y => ∑ i ∈ s, f i y) x :=
        (hs.of_le (by exact_mod_cast le_top)).contDiffAt
      rw [show (fun y => f a y + ∑ i ∈ s, f i y) = f a + fun y => ∑ i ∈ s, f i y from rfl,
        h1.laplacian_add h2, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **`T_p` commutes with the Laplacian** on smooth functions. -/
theorem lap_heckeOp {F : H3 → ℂ} (hF : H3.IsSmooth F) (z : H3) :
    H3.lap (heckeOp p F) z = heckeOp p (H3.lap F) z := by
  have e : H3.chart (heckeOp p F) z = fun v => ∑ i, H3.chart (fun w => F (heckeGL p i • w)) z v := by
    funext v; rfl
  rw [H3.lap, e, laplacian_finset_sum _ _ _ fun i _ => contDiff_chart_comp_smul hF _ z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← H3.lap, H3.lap_comp_smul]

end GaloisForLFunctions.RHTower.GL3
