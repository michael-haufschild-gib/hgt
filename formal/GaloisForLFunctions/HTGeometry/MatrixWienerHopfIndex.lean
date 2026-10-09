import GaloisForLFunctions.HTGeometry.MatrixWienerHopfFredholm
import GaloisForLFunctions.HTGeometry.CircleSymbolGroupCStar
import GaloisForLFunctions.HTGeometry.FiniteUnitaryFundamentalGroup
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryPathConnected

/-!
# The matrix Wiener–Hopf index theorem

For a unitary matrix symbol `U ∈ Mₙ(C(S¹))` the matrix Wiener–Hopf lift
`T_U = P̂ C_U P̂ + (1 - P̂)` on `L²(ℝ)ⁿ` is Fredholm of index `wind(det U)`
(`fredholmIndex_matWH`).

* `evalMat`: values of matrix symbols; unitarity, products and determinants are pointwise.
* `loopFamilySymbol`: a jointly continuous family of closed matrix loops `H(σ, t)` defines a
  continuous family of matrix symbols `z ↦ H(σ, t(z))`, `t(z) = fract(arg z / 2π)`
  (parametric descent along `θ ↦ e^{iθ}`, `continuous_of_continuous_comp_circleExp_snd`).
* `fredholmIndex_matWH_eq_of_det_eq`: based unitary symbols with the same determinant have loops
  homotopic in `U(m+1)` (`finiteUnitary_loops_homotopic_iff_det`), hence lifts of equal index.
* `fredholmIndex_matWH_eq_based`: moving the base point along a path in the connected `U(n)`.
* `fredholmIndex_matWH_diagonal`: `diag(det U, 1, …, 1)` has block-diagonal lift, of index
  `wind(det U)` by the scalar Wiener–Hopf index theorem.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-! ## Values of matrix symbols -/

/-- The value of a matrix symbol at a point of the circle. -/
def evalMat (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) (z : UnitCircle) :
    Matrix (Fin n) (Fin n) ℂ :=
  U.map (ContinuousMap.evalStarAlgHom ℂ ℂ z)

theorem evalMat_apply (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) (z : UnitCircle) (i j : Fin n) :
    evalMat U z i j = U i j z := rfl

theorem evalMat_mul (U V : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) (z : UnitCircle) :
    evalMat (U * V) z = evalMat U z * evalMat V z :=
  Matrix.map_mul (f := ((ContinuousMap.evalStarAlgHom ℂ ℂ z : C(UnitCircle, ℂ) →⋆ₐ[ℂ] ℂ) :
    C(UnitCircle, ℂ) →+* ℂ))

theorem evalMat_star (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) (z : UnitCircle) :
    evalMat (star U) z = star (evalMat U z) :=
  Matrix.ext fun _ _ => rfl

theorem evalMat_one (z : UnitCircle) : evalMat (1 : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) z = 1 :=
  Matrix.map_one _ rfl rfl

theorem det_evalMat (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) (z : UnitCircle) :
    (evalMat U z).det = U.det z :=
  ((ContinuousMap.evalStarAlgHom ℂ ℂ z : C(UnitCircle, ℂ) →⋆ₐ[ℂ] ℂ) :
    C(UnitCircle, ℂ) →+* ℂ).map_det U |>.symm

theorem matrix_ext_of_evalMat {U V : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)}
    (h : ∀ z, evalMat U z = evalMat V z) : U = V :=
  Matrix.ext fun i j => ContinuousMap.ext fun z => congrFun (congrFun (h z) i) j

theorem evalMat_mem_unitaryGroup {U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)} (hU : star U * U = 1)
    (z : UnitCircle) : evalMat U z ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [← evalMat_star, ← evalMat_mul, hU, evalMat_one]

theorem star_mul_self_of_evalMat {U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)}
    (h : ∀ z, evalMat U z ∈ Matrix.unitaryGroup (Fin n) ℂ) : star U * U = 1 :=
  matrix_ext_of_evalMat fun z => by
    rw [evalMat_mul, evalMat_star, evalMat_one]
    exact Matrix.mem_unitaryGroup_iff'.mp (h z)

theorem continuous_evalMat (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    Continuous (evalMat U) :=
  continuous_pi fun i => continuous_pi fun j => (U i j).continuous

/-! ## Loops and symbols -/

/-- A local section of `θ ↦ e^{iθ}` near `z₀`: `z ↦ arg z₀ + arg (z z̄₀)`. -/
def circleArgSection (z₀ : UnitCircle) (z : UnitCircle) : ℝ :=
  Complex.arg (z₀ : ℂ) + Complex.arg ((z : ℂ) * (starRingEnd ℂ) (z₀ : ℂ))

theorem circleExp_circleArgSection (z₀ z : UnitCircle) : circleExp (circleArgSection z₀ z) = z := by
  have hz₀ : (z₀ : ℂ) * (starRingEnd ℂ) (z₀ : ℂ) = 1 := by
    rw [Complex.mul_conj', norm_coe_unitCircle]
    norm_num
  apply Subtype.ext
  change Complex.exp (((Complex.arg (z₀ : ℂ) + Complex.arg ((z : ℂ) * (starRingEnd ℂ) (z₀ : ℂ)) :
    ℝ) : ℂ) * Complex.I) = z
  have hw : ‖(z : ℂ) * (starRingEnd ℂ) (z₀ : ℂ)‖ = 1 := by
    rw [norm_mul, Complex.norm_conj, norm_coe_unitCircle, norm_coe_unitCircle, one_mul]
  rw [Complex.ofReal_add, add_mul, Complex.exp_add,
    exp_arg_mul_I_of_norm_eq_one (norm_coe_unitCircle z₀), exp_arg_mul_I_of_norm_eq_one hw,
    mul_left_comm, hz₀, mul_one]

theorem continuousAt_circleArgSection (z₀ : UnitCircle) : ContinuousAt (circleArgSection z₀) z₀ := by
  have hz₀ : (z₀ : ℂ) * (starRingEnd ℂ) (z₀ : ℂ) = 1 := by
    rw [Complex.mul_conj', norm_coe_unitCircle]
    norm_num
  refine continuousAt_const.add ((Complex.continuousAt_arg ?_).comp ?_)
  · rw [hz₀]
    exact Complex.one_mem_slitPlane
  · exact (continuous_subtype_val.mul continuous_const).continuousAt

/-- **Parametric descent along `θ ↦ e^{iθ}`.** -/
theorem continuous_of_continuous_comp_circleExp_snd {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {G : X × UnitCircle → Y}
    (hG : Continuous fun p : X × ℝ => G (p.1, circleExp p.2)) : Continuous G := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, z₀⟩
  have hGφ : G = (fun p : X × ℝ => G (p.1, circleExp p.2)) ∘
      fun q : X × UnitCircle => (q.1, circleArgSection z₀ q.2) :=
    funext fun q => by simp only [Function.comp, circleExp_circleArgSection]
  rw [hGφ]
  exact hG.continuousAt.comp (continuousAt_fst.prodMk
    (ContinuousAt.comp (f := fun q : X × UnitCircle => q.2) (g := circleArgSection z₀)
      (continuousAt_circleArgSection z₀) continuousAt_snd))

/-- The turning coordinate `t = fract (arg z / 2π) ∈ [0, 1)`. -/
def circleTurn (z : UnitCircle) : ℝ := Int.fract (Complex.arg (z : ℂ) / (2 * Real.pi))

theorem circleExp_int_mul (θ : ℝ) (k : ℤ) : circleExp (θ + k * (2 * Real.pi)) = circleExp θ := by
  apply Subtype.ext
  change Complex.exp (((θ + k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
    Complex.exp ((θ : ℂ) * Complex.I)
  push_cast
  rw [add_mul, Complex.exp_add, show (k : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I =
    k * (2 * Real.pi * Complex.I) by ring, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem circleExp_two_pi_mul_circleTurn (z : UnitCircle) :
    circleExp (2 * Real.pi * circleTurn z) = z := by
  have h : 2 * Real.pi * circleTurn z =
      Complex.arg (z : ℂ) + (-⌊Complex.arg (z : ℂ) / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi) := by
    rw [circleTurn, Int.fract]
    push_cast
    field_simp
    ring
  rw [h, circleExp_int_mul, circleExp_arg]

theorem circleTurn_circleExp (θ : ℝ) : circleTurn (circleExp θ) = Int.fract (θ / (2 * Real.pi)) := by
  obtain ⟨k, hk⟩ := exists_int_of_circleExp_eq (circleExp_arg (circleExp θ))
  rw [circleTurn, hk, show (θ + k * (2 * Real.pi)) / (2 * Real.pi) = θ / (2 * Real.pi) + k by
    field_simp, Int.fract_add_intCast]

theorem circleTurn_mem_Icc (z : UnitCircle) : circleTurn z ∈ Icc (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

section LoopFamily

variable (Hm : ℝ → ℝ → Matrix (Fin n) (Fin n) ℂ) (hc : Continuous fun p : ℝ × ℝ => Hm p.1 p.2)
  (hcl : ∀ σ, Hm σ 0 = Hm σ 1)

include hc hcl in
theorem continuous_loopEval : Continuous fun p : ℝ × UnitCircle => Hm p.1 (circleTurn p.2) := by
  refine continuous_of_continuous_comp_circleExp_snd ?_
  simp only [circleTurn_circleExp]
  have h := ContinuousOn.comp_fract' (f := Hm) hc.continuousOn hcl
  exact h.comp (continuous_fst.prodMk (continuous_snd.div_const _))

/-- **The symbol of a loop family**: `z ↦ H(σ, t(z))`. -/
def loopFamilySymbol (σ : ℝ) : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ) := fun i j =>
  ⟨fun z => Hm σ (circleTurn z) i j,
    ((continuous_apply j).comp ((continuous_apply i).comp (continuous_loopEval Hm hc hcl))).comp
      (continuous_const.prodMk continuous_id)⟩

theorem evalMat_loopFamilySymbol (σ : ℝ) (z : UnitCircle) :
    evalMat (loopFamilySymbol Hm hc hcl σ) z = Hm σ (circleTurn z) := rfl

theorem continuous_loopFamilySymbol : Continuous (loopFamilySymbol Hm hc hcl) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  let F : C(ℝ × UnitCircle, ℂ) :=
    ⟨fun p => Hm p.1 (circleTurn p.2) i j,
      (continuous_apply j).comp ((continuous_apply i).comp (continuous_loopEval Hm hc hcl))⟩
  exact F.curry.continuous

theorem loopFamilySymbol_unitary (hu : ∀ σ t, Hm σ t ∈ Matrix.unitaryGroup (Fin n) ℂ) (σ : ℝ) :
    star (loopFamilySymbol Hm hc hcl σ) * loopFamilySymbol Hm hc hcl σ = 1 :=
  star_mul_self_of_evalMat fun _ => hu σ _

theorem loopFamilySymbol_eq {σ : ℝ} {U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, Hm σ t = evalMat U (circleExp (2 * Real.pi * t))) :
    loopFamilySymbol Hm hc hcl σ = U :=
  matrix_ext_of_evalMat fun z => by
    rw [evalMat_loopFamilySymbol, h _ (circleTurn_mem_Icc z), circleExp_two_pi_mul_circleTurn]

end LoopFamily

/-! ## The matrix index along homotopies -/

theorem circleExp_zero_eq_one : circleExp 0 = circleOne :=
  Subtype.ext (by simp [circleExp, circleOne])

theorem circleExp_two_pi_eq_one : circleExp (2 * Real.pi) = circleOne := by
  rw [← zero_add (2 * Real.pi), circleExp_add_two_pi, circleExp_zero_eq_one]

/-- The loop `t ↦ U(e^{2πit})` of a based unitary symbol. -/
def symbolLoop {U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)} (hU : star U * U = 1)
    (h1 : evalMat U circleOne = 1) : Path (1 : Matrix.unitaryGroup (Fin n) ℂ) 1 where
  toFun t := ⟨evalMat U (circleExp (2 * Real.pi * t)), evalMat_mem_unitaryGroup hU _⟩
  continuous_toFun := ((continuous_evalMat U).comp (continuous_circleExp.comp
    (continuous_const.mul continuous_subtype_val))).subtype_mk _
  source' := Subtype.ext (by
    change evalMat U (circleExp (2 * Real.pi * 0)) = 1
    rw [mul_zero, circleExp_zero_eq_one, h1])
  target' := Subtype.ext (by
    change evalMat U (circleExp (2 * Real.pi * 1)) = 1
    rw [mul_one, circleExp_two_pi_eq_one, h1])

/-- **Based unitary symbols with equal determinant have matrix Wiener–Hopf lifts of equal index**:
their loops are homotopic in `U(m+1)` (the determinant classifies `π₁`), and the homotopy is a
continuous family of unitary symbols. -/
theorem fredholmIndex_matWH_eq_of_det_eq {m : ℕ}
    {U V : Matrix (Fin (m + 1)) (Fin (m + 1)) C(UnitCircle, ℂ)} (hU : star U * U = 1)
    (hV : star V * V = 1) (hU1 : evalMat U circleOne = 1) (hV1 : evalMat V circleOne = 1)
    (hdet : U.det = V.det) : fredholmIndex (matWH U) = fredholmIndex (matWH V) := by
  set p := symbolLoop hU hU1
  set q := symbolLoop hV hV1
  have hdetPath : (p.map (finiteUnitaryDeterminant (Fin (m + 1))).continuous).cast
        (finiteUnitaryDeterminant (Fin (m + 1))).map_one.symm
        (finiteUnitaryDeterminant (Fin (m + 1))).map_one.symm =
      (q.map (finiteUnitaryDeterminant (Fin (m + 1))).continuous).cast
        (finiteUnitaryDeterminant (Fin (m + 1))).map_one.symm
        (finiteUnitaryDeterminant (Fin (m + 1))).map_one.symm := by
    ext s
    change (evalMat U _).det = (evalMat V _).det
    rw [det_evalMat, det_evalMat, hdet]
  obtain ⟨Φ⟩ := (finiteUnitary_loops_homotopic_iff_det m p q).mpr (by rw [hdetPath])
  set Hm : ℝ → ℝ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := fun σ t =>
    ((Φ (Set.projIcc 0 1 zero_le_one σ, Set.projIcc 0 1 zero_le_one t) :
      Matrix.unitaryGroup (Fin (m + 1)) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
  have hc : Continuous fun p : ℝ × ℝ => Hm p.1 p.2 :=
    continuous_subtype_val.comp (Φ.continuous.comp
      ((continuous_projIcc.comp continuous_fst).prodMk (continuous_projIcc.comp continuous_snd)))
  have hproj0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) :=
    Set.projIcc_left zero_le_one
  have hproj1 : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) :=
    Set.projIcc_right zero_le_one
  have hcl : ∀ σ, Hm σ 0 = Hm σ 1 := by
    intro σ
    simp only [Hm, hproj0, hproj1, Path.Homotopy.source, Path.Homotopy.target]
  have hu : ∀ σ t, Hm σ t ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ := fun σ t => (Φ _).2
  have h0 : loopFamilySymbol Hm hc hcl 0 = U := by
    refine loopFamilySymbol_eq Hm hc hcl fun t ht => ?_
    simp only [Hm, hproj0, ContinuousMap.HomotopyWith.apply_zero, Set.projIcc_of_mem _ ht]
    rfl
  have h1 : loopFamilySymbol Hm hc hcl 1 = V := by
    refine loopFamilySymbol_eq Hm hc hcl fun t ht => ?_
    simp only [Hm, hproj1, ContinuousMap.HomotopyWith.apply_one, Set.projIcc_of_mem _ ht]
    rfl
  have hpath := fredholmIndex_eq_of_continuous'
    (T := fun σ => matWH (loopFamilySymbol Hm hc hcl σ))
    (continuous_matWH.comp (continuous_loopFamilySymbol Hm hc hcl))
    (fun σ => isFredholmOp_matWH (loopFamilySymbol_unitary Hm hc hcl hu σ)) 0 1
  simpa only [h0, h1] using hpath

/-! ## Constant symbols and the base point -/

/-- The constant matrix symbol. -/
def constMat (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ) :=
  A.map (algebraMap ℂ C(UnitCircle, ℂ))

theorem evalMat_constMat (A : Matrix (Fin n) (Fin n) ℂ) (z : UnitCircle) :
    evalMat (constMat A) z = A := Matrix.ext fun _ _ => rfl

theorem continuous_constMat : Continuous (constMat (n := n)) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_algebraMap ℂ C(UnitCircle, ℂ)).comp ((continuous_apply j).comp (continuous_apply i))

theorem det_constMat (A : Matrix (Fin n) (Fin n) ℂ) :
    (constMat A).det = algebraMap ℂ C(UnitCircle, ℂ) A.det :=
  ((algebraMap ℂ C(UnitCircle, ℂ)).map_det A).symm

/-- **Moving the base point does not change the index**: `U` is joined to `U · U(1)*` by the
unitary symbols `U · Λ(σ)` along a path `Λ` from `1` to `U(1)*` in the connected group `U(n)`. -/
theorem fredholmIndex_matWH_eq_based {U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)}
    (hU : star U * U = 1) :
    fredholmIndex (matWH U) =
      fredholmIndex (matWH (U * constMat (star (evalMat U circleOne)))) := by
  have hW : star (evalMat U circleOne) ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem (evalMat_mem_unitaryGroup hU circleOne)
  let Λ : Path (1 : Matrix.unitaryGroup (Fin n) ℂ) ⟨star (evalMat U circleOne), hW⟩ :=
    PathConnectedSpace.somePath _ _
  set F : ℝ → Matrix (Fin n) (Fin n) C(UnitCircle, ℂ) := fun σ =>
    U * constMat ((Λ.extend σ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have hF : Continuous F :=
    continuous_const.mul (continuous_constMat.comp (continuous_subtype_val.comp Λ.extend.continuous))
  have hFu : ∀ σ, star (F σ) * F σ = 1 := fun σ =>
    star_mul_self_of_evalMat fun z => by
      rw [evalMat_mul, evalMat_constMat]
      exact mul_mem (evalMat_mem_unitaryGroup hU z) (Λ.extend σ).2
  have hpath := fredholmIndex_eq_of_continuous' (T := fun σ => matWH (F σ))
    (continuous_matWH.comp hF) (fun σ => isFredholmOp_matWH (hFu σ)) 0 1
  have h0 : F 0 = U := by
    simp only [F, Path.extend_zero]
    rw [show ((1 : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 from rfl]
    rw [show constMat (1 : Matrix (Fin n) (Fin n) ℂ) = 1 from
      Matrix.map_one _ (map_zero _) (map_one _), mul_one]
  have h1 : F 1 = U * constMat (star (evalMat U circleOne)) := by
    simp only [F, Path.extend_one]
  simpa only [h0, h1] using hpath

theorem evalMat_based (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) (hU : star U * U = 1) :
    evalMat (U * constMat (star (evalMat U circleOne))) circleOne = 1 := by
  rw [evalMat_mul, evalMat_constMat]
  exact Matrix.mem_unitaryGroup_iff.mp (evalMat_mem_unitaryGroup hU circleOne)

/-! ## Winding numbers of symbols -/

theorem isLoop_of_unimodular {f : C(UnitCircle, ℂ)} (hf : star f * f = 1) :
    RHTower.IsLoop (fun θ => f (circleExp θ)) 0 (2 * Real.pi) := by
  refine isLoop_circleSymbol fun z h => ?_
  have := (star_mul_self_eq_one_iff f).mp hf z
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem circleWinding_mul {f g : C(UnitCircle, ℂ)} (hf : star f * f = 1) (hg : star g * g = 1) :
    circleWinding (f * g) = circleWinding f + circleWinding g :=
  RHTower.windingNumber_mul (isLoop_of_unimodular hf) (isLoop_of_unimodular hg)

theorem circleWinding_algebraMap {c : ℂ} (hc : c ≠ 0) :
    circleWinding (algebraMap ℂ C(UnitCircle, ℂ) c) = 0 :=
  RHTower.windingNumber_const hc 0 (2 * Real.pi)

theorem circleWinding_one : circleWinding (1 : C(UnitCircle, ℂ)) = 0 := by
  have h := circleWinding_algebraMap (c := 1) one_ne_zero
  rwa [map_one] at h

theorem det_star_mul_self {U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)} (hU : star U * U = 1) :
    star U.det * U.det = 1 := by
  rw [← Matrix.det_conjTranspose, ← Matrix.star_eq_conjTranspose, ← Matrix.det_mul, hU,
    Matrix.det_one]

theorem circleWinding_mul_algebraMap {f : C(UnitCircle, ℂ)} (hf : star f * f = 1) {c : ℂ}
    (hc : c ≠ 0) : circleWinding (f * algebraMap ℂ C(UnitCircle, ℂ) c) = circleWinding f := by
  have h := RHTower.windingNumber_mul (isLoop_of_unimodular hf)
    (⟨continuous_const, fun _ => hc, rfl⟩ : RHTower.IsLoop (fun _ : ℝ => c) 0 (2 * Real.pi))
  rw [RHTower.windingNumber_const hc, add_zero] at h
  exact h

/-! ## Diagonal symbols -/

theorem matWH_diagonal (d : Fin n → C(UnitCircle, ℂ)) :
    matWH (Matrix.diagonal d) = l2BlockOp (Matrix.diagonal fun i => wienerHopfLift (d i)) := by
  have hC : matCircle (Matrix.diagonal d) =
      l2BlockOp (Matrix.diagonal fun i => circleMultiplier (d i)) := by
    rw [matCircle, Matrix.diagonal_map (f := circleMultiplier) (map_zero circleMultiplierHom)]
  rw [matWH, hC, one_sub_halfProjVec, halfProjVec, ← l2BlockOp_mul, ← l2BlockOp_mul,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← l2BlockOp_add, Matrix.diagonal_add]
  rfl

theorem fredholmIndex_matWH_diagonal {d : Fin n → C(UnitCircle, ℂ)}
    (hd : ∀ i, star (d i) * d i = 1) :
    IsFredholmOp (matWH (Matrix.diagonal d)) ∧
      fredholmIndex (matWH (Matrix.diagonal d)) = ∑ i, circleWinding (d i) := by
  rw [matWH_diagonal]
  obtain ⟨hF, hI⟩ := isFredholmOp_l2BlockOp_diagonal
    (d := fun i => wienerHopfLift (d i)) fun i => (fredholmIndex_wienerHopfLift_eq_circleWinding (hd i)).1
  refine ⟨hF, ?_⟩
  rw [hI]
  exact Finset.sum_congr rfl fun i _ => (fredholmIndex_wienerHopfLift_eq_circleWinding (hd i)).2

/-- `diag(f, 1, …, 1)`. -/
def diagFirst {m : ℕ} (f : C(UnitCircle, ℂ)) : Fin (m + 1) → C(UnitCircle, ℂ) :=
  fun i => if i = 0 then f else 1

/-! ## The matrix Wiener–Hopf index theorem -/

/-- **The matrix Wiener–Hopf index theorem**: for a unitary matrix symbol `U` on the circle the
matrix lift `P̂ C_U P̂ + (1 - P̂)` on `L²(ℝ)ⁿ` is Fredholm of index the winding number of `det U`.
(Move the base point, deform to `diag(det U, 1, …, 1)` through the determinant classification of
`π₁(U(n))`, and add the indices of the diagonal blocks.) -/
theorem fredholmIndex_matWH {U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)} (hU : star U * U = 1) :
    IsFredholmOp (matWH U) ∧ fredholmIndex (matWH U) = circleWinding U.det := by
  refine ⟨isFredholmOp_matWH hU, ?_⟩
  cases n with
  | zero =>
    haveI : Subsingleton (L2Vec 0) := ⟨fun x y => L2Vec.ext fun i => i.elim0⟩
    rw [Matrix.det_fin_zero, circleWinding_one, fredholmIndex,
      Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
    rfl
  | succ m =>
    obtain ⟨W, hWdef⟩ : ∃ W, W = evalMat U circleOne := ⟨_, rfl⟩
    obtain ⟨U', hU'def⟩ : ∃ U', U' = U * constMat (star W) := ⟨_, rfl⟩
    have hWu : star W ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ := by
      rw [hWdef]
      exact Unitary.star_mem (evalMat_mem_unitaryGroup hU circleOne)
    have hU' : star U' * U' = 1 := star_mul_self_of_evalMat fun z => by
      rw [hU'def, evalMat_mul, evalMat_constMat]
      exact mul_mem (evalMat_mem_unitaryGroup hU z) hWu
    have hU'1 : evalMat U' circleOne = 1 := by
      rw [hU'def, hWdef]
      exact evalMat_based U hU
    have hdetW : (star W).det ≠ 0 := by
      intro h
      have h' := (Unitary.mem_iff.mp (Matrix.det_of_mem_unitary hWu)).1
      rw [h, star_zero, zero_mul] at h'
      exact zero_ne_one h'
    have hdetU' : U'.det = U.det * algebraMap ℂ C(UnitCircle, ℂ) (star W).det := by
      rw [hU'def, Matrix.det_mul, det_constMat]
    obtain ⟨D, hDdef⟩ : ∃ D, D = Matrix.diagonal (diagFirst (m := m) U'.det) := ⟨_, rfl⟩
    have hdu : ∀ i, star (diagFirst (m := m) U'.det i) * diagFirst (m := m) U'.det i = 1 := by
      intro i
      by_cases hi : i = 0
      · simp only [diagFirst, if_pos hi]
        exact det_star_mul_self hU'
      · simp only [diagFirst, if_neg hi, star_one, mul_one]
    have hD : star D * D = 1 := by
      rw [hDdef, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact hdu i
    have hD1 : evalMat D circleOne = 1 := by
      refine Matrix.ext fun i j => ?_
      rw [evalMat_apply, hDdef]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        by_cases hi : i = 0
        · simp only [diagFirst, if_pos hi]
          rw [← det_evalMat, hU'1, Matrix.det_one]
        · simp only [diagFirst, if_neg hi]
          rfl
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
        rfl
    have hdet : U'.det = D.det := by
      rw [hDdef, Matrix.det_diagonal, Fin.prod_univ_succ]
      simp [diagFirst]
    have hbased : fredholmIndex (matWH U) = fredholmIndex (matWH U') := by
      rw [hU'def, hWdef]
      exact fredholmIndex_matWH_eq_based hU
    rw [hbased, fredholmIndex_matWH_eq_of_det_eq hU' hD hU'1 hD1 hdet, hDdef,
      (fredholmIndex_matWH_diagonal hdu).2, Fin.sum_univ_succ]
    simp only [diagFirst, Fin.succ_ne_zero, if_false, if_true, circleWinding_one,
      Finset.sum_const_zero, add_zero]
    rw [hdetU', circleWinding_mul_algebraMap (det_star_mul_self hU) hdetW]

end GaloisForLFunctions.HTGeometry
