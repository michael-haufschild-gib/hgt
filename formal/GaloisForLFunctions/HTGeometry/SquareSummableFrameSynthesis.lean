import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCofinalChildTraceClass
import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass

/-!
# Synthesis of a square-summable frame

A family `v : ι → H` with `∑ ‖vᵢ‖² < ∞` synthesizes the bounded operator
`W : ℓ²(ι) → H, W x = ∑ xᵢ vᵢ`, with `W eᵢ = vᵢ` and `(W* h)ᵢ = ⟨vᵢ, h⟩`.  It is Hilbert–Schmidt
with `‖W‖²_HS = ∑ ‖vᵢ‖²`; its right Gram `W*W` has matrix `⟨vᵢ, vⱼ⟩` and its left Gram `WW*` is the
frame operator.  Both Grams are positive, Schatten-one and have trace `∑ ‖vᵢ‖²`.  If the frame is
total then `WW*` is injective with dense range.
-/

open Filter Topology Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem summable_norm_smul_frame {v : ι → H} (hv : Summable fun i => ‖v i‖ ^ 2)
    (x : lp (fun _ : ι => ℂ) 2) : Summable fun i => ‖(x : ι → ℂ) i • v i‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_)
    (((HilbertSchmidt.summable_coe_sq x).add hv).div_const 2)
  rw [norm_smul]
  nlinarith [sq_nonneg (‖(x : ι → ℂ) i‖ - ‖v i‖)]

omit [CompleteSpace H] in
theorem tsum_norm_smul_frame_le {v : ι → H} (hv : Summable fun i => ‖v i‖ ^ 2)
    (x : lp (fun _ : ι => ℂ) 2) :
    ∑' i, ‖(x : ι → ℂ) i • v i‖ ≤ Real.sqrt (∑' i, ‖v i‖ ^ 2) * ‖x‖ := by
  have hx := HilbertSchmidt.summable_coe_sq x
  have hH := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun i => ‖(x : ι → ℂ) i‖) (g := fun i => ‖v i‖) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) (by simpa using hx) (by simpa using hv)
  have hxn : (∑' i, ‖(x : ι → ℂ) i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖x‖ := by
    rw [show (fun i => ‖(x : ι → ℂ) i‖ ^ (2 : ℝ)) = fun i => ‖(x : ι → ℂ) i‖ ^ 2 by
      funext i; exact Real.rpow_two _, ← HilbertSchmidt.lp_norm_sq_eq, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq (norm_nonneg _)]
  have hvn : (∑' i, ‖v i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = Real.sqrt (∑' i, ‖v i‖ ^ 2) := by
    rw [show (fun i => ‖v i‖ ^ (2 : ℝ)) = fun i => ‖v i‖ ^ 2 by funext i; exact Real.rpow_two _,
      ← Real.sqrt_eq_rpow]
  rw [hxn, hvn] at hH
  calc ∑' i, ‖(x : ι → ℂ) i • v i‖ = ∑' i, ‖(x : ι → ℂ) i‖ * ‖v i‖ :=
        tsum_congr fun i => norm_smul _ _
    _ ≤ ‖x‖ * Real.sqrt (∑' i, ‖v i‖ ^ 2) := hH
    _ = _ := mul_comm _ _

/-- The synthesis map `x ↦ ∑ xᵢ vᵢ` as a linear map. -/
def squareSummableSynthesisLinear (v : ι → H) (hv : Summable fun i => ‖v i‖ ^ 2) :
    lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] H where
  toFun x := ∑' i, (x : ι → ℂ) i • v i
  map_add' x y := by
    simp only [lp.coeFn_add, Pi.add_apply, add_smul]
    exact ((summable_norm_smul_frame hv x).of_norm).tsum_add
      (summable_norm_smul_frame hv y).of_norm
  map_smul' c x := by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    exact ((summable_norm_smul_frame hv x).of_norm).tsum_const_smul c

/-- **The synthesis operator** `W : ℓ²(ι) → H`, `W x = ∑ xᵢ vᵢ`. -/
def squareSummableSynthesis (v : ι → H) (hv : Summable fun i => ‖v i‖ ^ 2) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] H :=
  LinearMap.mkContinuous (squareSummableSynthesisLinear v hv) (Real.sqrt (∑' i, ‖v i‖ ^ 2)) fun x =>
    (norm_tsum_le_tsum_norm (summable_norm_smul_frame hv x)).trans
      (tsum_norm_smul_frame_le hv x)

theorem squareSummableSynthesis_apply {v : ι → H} (hv : Summable fun i => ‖v i‖ ^ 2)
    (x : lp (fun _ : ι => ℂ) 2) :
    squareSummableSynthesis v hv x = ∑' i, (x : ι → ℂ) i • v i := rfl

theorem squareSummableSynthesis_single [DecidableEq ι] {v : ι → H}
    (hv : Summable fun i => ‖v i‖ ^ 2)
    (i : ι) (c : ℂ) : squareSummableSynthesis v hv (lp.single 2 i c) = c • v i := by
  rw [squareSummableSynthesis_apply, tsum_eq_single i fun j hj => by
    rw [lp.single_apply_ne _ _ _ hj, zero_smul], lp.single_apply_self]

/-- `(W* h)ᵢ = ⟨vᵢ, h⟩`. -/
theorem adjoint_squareSummableSynthesis_apply [DecidableEq ι] {v : ι → H}
    (hv : Summable fun i => ‖v i‖ ^ 2) (h : H) (i : ι) :
    (ContinuousLinearMap.adjoint (squareSummableSynthesis v hv) h : ι → ℂ) i = ⟪v i, h⟫_ℂ := by
  have h1 := lp.inner_single_left (𝕜 := ℂ) (G := fun _ : ι => ℂ) i (1 : ℂ)
    (ContinuousLinearMap.adjoint (squareSummableSynthesis v hv) h)
  rw [ContinuousLinearMap.adjoint_inner_right, squareSummableSynthesis_single, one_smul] at h1
  rw [h1, RCLike.inner_apply]
  simp

/-- The right Gram has matrix `⟨vᵢ, vⱼ⟩`. -/
theorem inner_single_rightGram_single [DecidableEq ι] {v : ι → H}
    (hv : Summable fun i => ‖v i‖ ^ 2) (i j : ι) :
    ⟪(lp.single 2 i (1 : ℂ) : lp (fun _ : ι => ℂ) 2),
        (ContinuousLinearMap.adjoint (squareSummableSynthesis v hv) ∘L squareSummableSynthesis v hv)
          (lp.single 2 j 1)⟫_ℂ = ⟪v i, v j⟫_ℂ := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    squareSummableSynthesis_single, squareSummableSynthesis_single, one_smul, one_smul]

theorem squareSummableSynthesis_isHilbertSchmidt [DecidableEq ι] {v : ι → H}
    (hv : Summable fun i => ‖v i‖ ^ 2) : (squareSummableSynthesis v hv).IsHilbertSchmidt := by
  refine ContinuousLinearMap.isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis ι) ?_
  refine hv.congr fun i => ?_
  rw [HilbertSchmidt.lpBasis_apply, squareSummableSynthesis_single, one_smul]

theorem hsNormSq_squareSummableSynthesis [DecidableEq ι] {v : ι → H}
    (hv : Summable fun i => ‖v i‖ ^ 2) :
    ContinuousLinearMap.hsNormSq (squareSummableSynthesis v hv) = ∑' i, ‖v i‖ ^ 2 := by
  rw [ContinuousLinearMap.hsNormSq_eq (squareSummableSynthesis_isHilbertSchmidt hv)
    (HilbertSchmidt.lpBasis ι)]
  refine tsum_congr fun i => ?_
  rw [HilbertSchmidt.lpBasis_apply, squareSummableSynthesis_single, one_smul]

/-- The right Gram `W*W` is positive and Schatten-one with trace `∑ ‖vᵢ‖²`. -/
theorem rightGram_traceClass [DecidableEq ι] {v : ι → H} (hv : Summable fun i => ‖v i‖ ^ 2) :
    (ContinuousLinearMap.adjoint (squareSummableSynthesis v hv) ∘L
        squareSummableSynthesis v hv).IsPositive ∧
      MemSchattenClass 1
        (ContinuousLinearMap.adjoint (squareSummableSynthesis v hv) ∘L
          squareSummableSynthesis v hv) ∧
      (ContinuousLinearMap.adjoint (squareSummableSynthesis v hv) ∘L
          squareSummableSynthesis v hv).opTrace =
        ((∑' i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  set W := squareSummableSynthesis v hv
  have hpos : (ContinuousLinearMap.adjoint W ∘L W).IsPositive :=
    ContinuousLinearMap.isPositive_adjoint_comp_self W
  have hdiag : ∀ i, ⟪HilbertSchmidt.lpBasis ι i,
      (ContinuousLinearMap.adjoint W ∘L W) (HilbertSchmidt.lpBasis ι i)⟫_ℂ =
        ((‖v i‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [HilbertSchmidt.lpBasis_apply, inner_single_rightGram_single, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hsum : Summable fun i => ⟪HilbertSchmidt.lpBasis ι i,
      (ContinuousLinearMap.adjoint W ∘L W) (HilbertSchmidt.lpBasis ι i)⟫_ℂ := by
    simp_rw [hdiag]
    exact Complex.summable_ofReal.2 hv
  have hS := memSchattenClass_one_of_isPositive_of_summable_diagonal
    (HilbertSchmidt.lpBasis ι) hpos hsum
  refine ⟨hpos, hS, ?_⟩
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hS (HilbertSchmidt.lpBasis ι)]
  simp_rw [hdiag]
  rw [Complex.ofReal_tsum]

/-- The left Gram `WW*` is positive and Schatten-one with the same trace. -/
theorem leftGram_traceClass [DecidableEq ι] {v : ι → H} (hv : Summable fun i => ‖v i‖ ^ 2) :
    (squareSummableSynthesis v hv ∘L
        ContinuousLinearMap.adjoint (squareSummableSynthesis v hv)).IsPositive ∧
      MemSchattenClass 1
        (squareSummableSynthesis v hv ∘L
          ContinuousLinearMap.adjoint (squareSummableSynthesis v hv)) ∧
      (squareSummableSynthesis v hv ∘L
          ContinuousLinearMap.adjoint (squareSummableSynthesis v hv)).opTrace =
        ((∑' i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  set W := squareSummableSynthesis v hv
  have hW := squareSummableSynthesis_isHilbertSchmidt hv
  refine ⟨ContinuousLinearMap.isPositive_self_comp_adjoint W,
    memSchattenClass_one_comp hW hW.adjoint, ?_⟩
  rw [ContinuousLinearMap.opTrace_comp_comm hW hW.adjoint]
  exact (rightGram_traceClass hv).2.2

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Two bounded operators on `ℓ²(ι)` with the same matrix entries coincide. -/
theorem ext_of_inner_single [DecidableEq ι]
    {A B : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2}
    (h : ∀ i j, ⟪(lp.single 2 i (1 : ℂ) : lp (fun _ : ι => ℂ) 2), A (lp.single 2 j 1)⟫_ℂ =
      ⟪(lp.single 2 i (1 : ℂ) : lp (fun _ : ι => ℂ) 2), B (lp.single 2 j 1)⟫_ℂ) : A = B := by
  have hcol : ∀ j, A (lp.single 2 j 1) = B (lp.single 2 j 1) := fun j => by
    refine lp.ext (funext fun i => ?_)
    have hij := h i j
    rw [lp.inner_single_left, lp.inner_single_left, RCLike.inner_apply, RCLike.inner_apply] at hij
    simpa using hij
  have hdense : Dense (Submodule.span ℂ (Set.range fun j => (lp.single 2 j (1 : ℂ) :
      lp (fun _ : ι => ℂ) 2)) : Set (lp (fun _ : ι => ℂ) 2)) := by
    have := (HilbertSchmidt.lpBasis ι).dense_span
    rw [show (⇑(HilbertSchmidt.lpBasis ι)) = fun j => (lp.single 2 j (1 : ℂ) :
      lp (fun _ : ι => ℂ) 2) from funext HilbertSchmidt.lpBasis_apply] at this
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr this
  exact ContinuousLinearMap.ext_on hdense (by rintro _ ⟨j, rfl⟩; exact hcol j)

/-- A total frame has injective left Gram with dense range. -/
theorem leftGram_injective_denseRange [DecidableEq ι] {v : ι → H}
    (hv : Summable fun i => ‖v i‖ ^ 2)
    (htotal : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    Function.Injective (squareSummableSynthesis v hv ∘L
        ContinuousLinearMap.adjoint (squareSummableSynthesis v hv)) ∧
      DenseRange (squareSummableSynthesis v hv ∘L
        ContinuousLinearMap.adjoint (squareSummableSynthesis v hv)) := by
  have hker : ∀ h : H,
      ContinuousLinearMap.adjoint (squareSummableSynthesis v hv) h = 0 → h = 0 := by
    intro h hh
    have horth : h ∈ (Submodule.span ℂ (Set.range v))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (p := fun u _ => ⟪h, u⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
      · rintro _ ⟨i, rfl⟩
        have hi := adjoint_squareSummableSynthesis_apply hv h i
        rw [hh, lp.coeFn_zero, Pi.zero_apply] at hi
        rw [← inner_conj_symm, ← hi, map_zero]
      · simp
      · intro a b _ _ ha hb
        rw [inner_add_right, ha, hb, add_zero]
      · intro c a _ ha
        rw [inner_smul_right, ha, mul_zero]
    rw [Submodule.topologicalClosure_eq_top_iff.1 htotal] at horth
    exact (Submodule.mem_bot ℂ).1 horth
  have hinj : Function.Injective
      (squareSummableSynthesis v hv ∘L
        ContinuousLinearMap.adjoint (squareSummableSynthesis v hv)) := by
    refine (injective_iff_map_eq_zero _).2 fun h hh => hker h ?_
    have h0 : ⟪h, (squareSummableSynthesis v hv ∘L
        ContinuousLinearMap.adjoint (squareSummableSynthesis v hv)) h⟫_ℂ = 0 := by
      rw [hh, inner_zero_right]
    rwa [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_zero] at h0
  refine ⟨hinj, ?_⟩
  have hsa : IsSelfAdjoint
      (squareSummableSynthesis v hv ∘L
        ContinuousLinearMap.adjoint (squareSummableSynthesis v hv)) :=
    (ContinuousLinearMap.isPositive_self_comp_adjoint _).isSelfAdjoint
  have hrange : Set.range ⇑(squareSummableSynthesis v hv ∘L
        ContinuousLinearMap.adjoint (squareSummableSynthesis v hv))
      = (LinearMap.range ((squareSummableSynthesis v hv ∘L
          ContinuousLinearMap.adjoint (squareSummableSynthesis v hv) : H →L[ℂ] H) :
            H →ₗ[ℂ] H) : Set H) :=
    (LinearMap.coe_range _).symm
  rw [DenseRange, hrange, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range,
    hsa.adjoint_eq]
  exact LinearMap.ker_eq_bot.2 hinj

end GaloisForLFunctions.HTGeometry
