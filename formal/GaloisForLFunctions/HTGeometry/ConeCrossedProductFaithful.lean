import GaloisForLFunctions.HTGeometry.RealGroupCStarFaithful

/-!
# Full = reduced for `C₀((-∞, +∞]) ⋊ ℝ`

The Schrödinger representation of the full cone crossed product on `L²(ℝ)` is isometric
(`norm_coneSchrodinger`).  For a bounded representation `ρ` of the cone core and a cone kernel
`K = χG + k`:

* **The symbol bound** `‖C_G‖ ≤ ‖T_K‖` (`norm_op_conv_coneSymbol_le`): translated far to the right a
  test function only sees the convolution part, `T_K f(· - t) = (G ⋆ f)(· - t)`.
* **The essential subspace** `H_I = closure span ρ(C₀(ℝ) ⋊ ℝ) H` of the compact ideal is invariant,
  and there `‖ρ(K) ξ‖ ≤ ‖T_K‖ ‖ξ‖` (`norm_π_apply_le_of_mem_essSpace`): along an increasing approximate
  unit `e` of the C⋆-algebra `C₀(ℝ) ⋊ ℝ` one has `ρ(e) ξ → ξ`, and `ρ(K) ρ(e) = ρ(K e)` with
  `‖K e‖ = ‖T_K S(e)‖ ≤ ‖T_K‖` computed in `𝒦(L²(ℝ)) ≅ C₀(ℝ) ⋊ ℝ` (`coneMulLeft`).
* **On `H_I^⊥`** the ideal acts by zero, so `G ↦ ρ(χG)|_{H_I^⊥}` is an `L¹`-bounded representation of
  `(C_c(ℝ), ⋆)` (`tailRep`); full = reduced for `ℝ` and the symbol bound give
  `‖ρ(K) ζ‖ ≤ ‖C_G‖ ‖ζ‖ ≤ ‖T_K‖ ‖ζ‖`.
* Pythagoras over `H = H_I ⊕ H_I^⊥` gives `‖ρ(K)‖ ≤ ‖T_K‖` (`BoundedRep.norm_π_le_norm_op`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped CompactlySupported ENNReal NNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open BandKernel

/-! ## The symbol is dominated by the Schrödinger norm -/

/-- The translate `x ↦ f(x - t)`. -/
def ccShift (f : C_c(ℝ, ℂ)) (t : ℝ) : C_c(ℝ, ℂ) where
  toFun x := f (x - t)
  continuous_toFun := f.continuous.comp (continuous_id.sub continuous_const)
  hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (Homeomorph.subRight t)

theorem ccShift_apply (f : C_c(ℝ, ℂ)) (t x : ℝ) : ccShift f t x = f (x - t) := rfl

theorem norm_cc2_ccShift (f : C_c(ℝ, ℂ)) (t : ℝ) : ‖cc2 (ccShift f t)‖ = ‖cc2 f‖ := by
  have h : ‖cc2 (ccShift f t)‖ ^ 2 = ‖cc2 f‖ ^ 2 := by
    rw [KernelAlg.norm_cc2_sq, KernelAlg.norm_cc2_sq]
    exact integral_sub_right_eq_self (fun x => ‖f x‖ ^ 2) t
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- Far to the right a cone kernel acts as the convolution by its symbol. -/
theorem op_ccShift_eventually (K : coneKernels) (f : C_c(ℝ, ℂ)) :
    ∃ t₀, ∀ t, t₀ ≤ t → (K : BandKernel).op (cc2 (ccShift f t)) =
      cc2 (ccShift (convProfile (coneSymbol K) f) t) := by
  obtain ⟨Rf, hRf0, hRf⟩ := exists_supportedIn f
  obtain ⟨R, hR⟩ := exists_colsVanish_ofKernelAlg (coneRemainder K)
  set G := coneSymbol K
  set w := (conv G).width
  refine ⟨|R| + Rf + w + 1, fun t ht => ?_⟩
  have hw := (conv G).width_nonneg
  apply Lp.ext
  filter_upwards [(K : BandKernel).op_ae (cc2 (ccShift f t)),
    cc2_ae (ccShift (convProfile G f) t)] with x h1 h2
  rw [h1, h2, ccShift_apply, convProfile_apply]
  have h3 : ∫ y, (K : BandKernel).toFun (x, y) * (cc2 (ccShift f t) : ℝ → ℂ) y =
      ∫ y, (K : BandKernel).toFun (x, y) * f (y - t) := by
    refine integral_congr_ae ?_
    filter_upwards [cc2_ae (ccShift f t)] with y hy
    rw [hy, ccShift_apply]
  rw [h3, ← integral_add_right_eq_self _ t]
  congr 1
  funext y
  rw [add_sub_cancel_right, coneKernel_decomp K, BandKernel.add_apply, cutConv_toFun]
  by_cases hy : Rf < |y|
  · rw [hRf y hy]
    ring
  · push Not at hy
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    have hcol : (ofKernelAlg (coneRemainder K)).toFun (x, y + t) = 0 := by
      refine hR x (y + t) ?_
      rw [abs_of_pos (by linarith [abs_nonneg R])]
      linarith [le_abs_self R]
    rw [hcol, add_zero, show x - t - y = x - (y + t) by ring]
    by_cases hxy : w < |x - (y + t)|
    · rw [← conv_toFun G, (conv G).toFun_eq_zero hxy]
      ring
    · push Not at hxy
      rw [coneCut_of_one_le (by linarith [(abs_le.mp hxy).1, abs_nonneg R]), Complex.ofReal_one,
        one_mul]

/-- **The symbol is dominated by the Schrödinger norm**: `‖C_G‖ ≤ ‖T_K‖` for the symbol `G` of a
cone kernel `K` (translate a test function far to the right, where `T_K` is convolution by `G`). -/
theorem norm_op_conv_coneSymbol_le (K : coneKernels) :
    ‖(conv (coneSymbol K)).op‖ ≤ ‖(K : BandKernel).op‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ξ => ?_
  have hcore : ∀ f : C_c(ℝ, ℂ), ‖(conv (coneSymbol K)).op (cc2 f)‖ ≤
      ‖(K : BandKernel).op‖ * ‖cc2 f‖ := by
    intro f
    obtain ⟨t₀, ht⟩ := op_ccShift_eventually K f
    rw [op_conv_cc2, ← norm_cc2_ccShift _ t₀, ← ht t₀ le_rfl, ← norm_cc2_ccShift f t₀]
    exact (K : BandKernel).op.le_opNorm _
  have hclosed : IsClosed {ξ : L2Real | ‖(conv (coneSymbol K)).op ξ‖ ≤
      ‖(K : BandKernel).op‖ * ‖ξ‖} :=
    isClosed_le (continuous_norm.comp (conv (coneSymbol K)).op.continuous)
      (continuous_const.mul continuous_norm)
  exact denseRange_cc2.induction_on ξ hclosed hcore

/-! ## Left multiplication by cone kernels on `C₀(ℝ) ⋊ ℝ` -/

/-- Left multiplication by a cone kernel on `C₀(ℝ) ⋊ ℝ ≅ 𝒦(L²(ℝ))`. -/
theorem isCompactOperator_op_mul_schrodinger (K : coneKernels) (y : RealCrossedProduct) :
    IsCompactOperator ⇑((K : BandKernel).op * schrodinger y) :=
  (isCompactOperator_schrodinger y).clm_comp (K : BandKernel).op

def coneMulLeft (K : coneKernels) (y : RealCrossedProduct) : RealCrossedProduct :=
  Classical.choose (compact_mem_range_schrodinger (isCompactOperator_op_mul_schrodinger K y))

theorem schrodinger_coneMulLeft (K : coneKernels) (y : RealCrossedProduct) :
    schrodinger (coneMulLeft K y) = (K : BandKernel).op * schrodinger y :=
  Classical.choose_spec (compact_mem_range_schrodinger (isCompactOperator_op_mul_schrodinger K y))

theorem norm_coneMulLeft_le (K : coneKernels) (y : RealCrossedProduct) :
    ‖coneMulLeft K y‖ ≤ ‖(K : BandKernel).op‖ * ‖y‖ := by
  rw [← norm_schrodinger, schrodinger_coneMulLeft, ← norm_schrodinger y]
  exact norm_mul_le _ _

theorem continuous_coneMulLeft (K : coneKernels) : Continuous (coneMulLeft K) := by
  refine (LipschitzWith.of_dist_le_mul (K := ‖(K : BandKernel).op‖₊) fun y z => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← norm_schrodinger, map_sub, schrodinger_coneMulLeft,
    schrodinger_coneMulLeft, ← mul_sub, ← map_sub, coe_nnnorm, ← norm_schrodinger (y - z)]
  exact norm_mul_le _ _

theorem exists_coneIdealHom_eq_mul (K : coneKernels) (k : KernelAlg) :
    ∃ k' : KernelAlg, coneIdealHom k' = K * coneIdealHom k := by
  obtain ⟨k', hk'⟩ := mul_ofKernelAlg_mem (K : BandKernel) k
  exact ⟨k', Subtype.ext hk'⟩

theorem coneMulLeft_toRCP (K : coneKernels) {k k' : KernelAlg}
    (hk : coneIdealHom k' = K * coneIdealHom k) : coneMulLeft K (toRCP k) = toRCP k' := by
  apply schrodinger_injective
  rw [schrodinger_coneMulLeft, schrodinger_toEnvelope, schrodinger_toEnvelope,
    ← op_ofKernelAlg, ← op_ofKernelAlg, ← coneIdealHom_apply, ← coneIdealHom_apply, hk]
  exact (op_mul _ _).symm

/-! ## Full = reduced for the cone crossed product -/

section FullReduced

variable (ρ : BoundedRep coneKernels coneL1Norm)

/-- The restriction of a representation to the compact ideal, extended to `C₀(ℝ) ⋊ ℝ`. -/
def BoundedRep.idealExt : RealCrossedProduct →⋆ₙₐ[ℂ] (ρ.H →L[ℂ] ρ.H) :=
  (ρ.pullback coneIdealHom fun k => (coneL1Norm_coneIdealHom k).le).extend

theorem BoundedRep.idealExt_toRCP (k : KernelAlg) : ρ.idealExt (toRCP k) = ρ.π (coneIdealHom k) :=
  rfl

theorem BoundedRep.continuous_idealExt : Continuous ρ.idealExt :=
  (NonUnitalStarAlgHom.instContinuousLinearMapClassComplex (F := RealCrossedProduct →⋆ₙₐ[ℂ]
    (ρ.H →L[ℂ] ρ.H))).map_continuous ρ.idealExt

theorem BoundedRep.idealExt_coneMulLeft (K : coneKernels) (y : RealCrossedProduct) :
    ρ.idealExt (coneMulLeft K y) = ρ.π K * ρ.idealExt y := by
  have h := (toEnvelope_dense KernelAlg KernelAlg.l1Norm).equalizer
    (ρ.continuous_idealExt.comp (continuous_coneMulLeft K))
    (continuous_const.mul ρ.continuous_idealExt) (funext fun k => by
      obtain ⟨k', hk'⟩ := exists_coneIdealHom_eq_mul K k
      change ρ.idealExt (coneMulLeft K (toRCP k)) = ρ.π K * ρ.idealExt (toRCP k)
      rw [coneMulLeft_toRCP K hk', ρ.idealExt_toRCP, ρ.idealExt_toRCP, hk', map_mul])
  exact congrFun h y

/-- **The essential subspace of the compact ideal**: the closed span of `ρ(C₀(ℝ) ⋊ ℝ) H`. -/
def BoundedRep.essSpace : Submodule ℂ ρ.H :=
  (⨆ y : RealCrossedProduct,
    LinearMap.range ((ρ.idealExt y : ρ.H →L[ℂ] ρ.H) : ρ.H →ₗ[ℂ] ρ.H)).topologicalClosure

theorem BoundedRep.idealExt_mem_essSpace (y : RealCrossedProduct) (η : ρ.H) :
    ρ.idealExt y η ∈ ρ.essSpace :=
  Submodule.le_topologicalClosure _
    (Submodule.mem_iSup_of_mem y (LinearMap.mem_range_self _ η))

/-- The ideal acts by zero on the orthogonal complement of its essential subspace. -/
theorem BoundedRep.idealExt_apply_eq_zero {ζ : ρ.H} (hζ : ζ ∈ ρ.essSpaceᗮ)
    (y : RealCrossedProduct) : ρ.idealExt y ζ = 0 := by
  have h : ∀ η : ρ.H, ⟪η, ρ.idealExt y ζ⟫_ℂ = 0 := fun η => by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star]
    exact Submodule.inner_right_of_mem_orthogonal (ρ.idealExt_mem_essSpace _ η) hζ
  exact inner_self_eq_zero.mp (h _)

/-- The cone kernels preserve the essential subspace. -/
theorem BoundedRep.π_mem_essSpace (K : coneKernels) {ξ : ρ.H} (hξ : ξ ∈ ρ.essSpace) :
    ρ.π K ξ ∈ ρ.essSpace := by
  set V := ⨆ y : RealCrossedProduct,
    LinearMap.range ((ρ.idealExt y : ρ.H →L[ℂ] ρ.H) : ρ.H →ₗ[ℂ] ρ.H)
  have hV : V ≤ ρ.essSpace.comap ((ρ.π K : ρ.H →L[ℂ] ρ.H) : ρ.H →ₗ[ℂ] ρ.H) := by
    refine iSup_le fun y => ?_
    rintro _ ⟨η, rfl⟩
    change ρ.π K (ρ.idealExt y η) ∈ ρ.essSpace
    have h := congrArg (fun T : ρ.H →L[ℂ] ρ.H => T η) (ρ.idealExt_coneMulLeft K y)
    rw [show (ρ.π K * ρ.idealExt y) η = ρ.π K (ρ.idealExt y η) from rfl] at h
    rw [← h]
    exact ρ.idealExt_mem_essSpace _ η
  have hclosed : IsClosed (ρ.essSpace.comap ((ρ.π K : ρ.H →L[ℂ] ρ.H) : ρ.H →ₗ[ℂ] ρ.H) :
      Set ρ.H) :=
    (Submodule.isClosed_topologicalClosure _).preimage (ρ.π K).continuous
  exact Submodule.topologicalClosure_minimal V hV hclosed hξ

/-- The cone kernels preserve the orthogonal complement of the essential subspace. -/
theorem BoundedRep.π_mem_orthogonal (K : coneKernels) {ζ : ρ.H} (hζ : ζ ∈ ρ.essSpaceᗮ) :
    ρ.π K ζ ∈ ρ.essSpaceᗮ := by
  rw [Submodule.mem_orthogonal]
  intro ξ hξ
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  exact Submodule.inner_right_of_mem_orthogonal (ρ.π_mem_essSpace (star K) hξ) hζ

/-- **On the essential subspace a cone kernel is dominated by its Schrödinger norm.**  With an
approximate unit `e` of `C₀(ℝ) ⋊ ℝ`, `ρ(e) ξ → ξ` on the essential subspace and
`ρ(K) ρ(e) = ρ(K e)` with `‖K e‖ ≤ ‖T_K‖ ‖e‖` computed in `𝒦(L²(ℝ))`. -/
theorem BoundedRep.norm_π_apply_le_of_mem_essSpace (K : coneKernels) {ξ : ρ.H}
    (hξ : ξ ∈ ρ.essSpace) : ‖ρ.π K ξ‖ ≤ ‖(K : BandKernel).op‖ * ‖ξ‖ := by
  letI := CStarAlgebra.spectralOrder RealCrossedProduct
  haveI := CStarAlgebra.spectralOrderedRing RealCrossedProduct
  set l := CStarAlgebra.approximateUnit RealCrossedProduct
  have hl := CStarAlgebra.increasingApproximateUnit RealCrossedProduct
  haveI : l.NeBot := hl.neBot
  -- the approximate unit acts as the identity on the essential subspace
  set S : Set ρ.H := {ξ | Tendsto (fun e => ρ.idealExt e ξ) l (𝓝 ξ)}
  have hgen : ∀ (y : RealCrossedProduct) (η : ρ.H), ρ.idealExt y η ∈ S := by
    intro y η
    have h1 : Tendsto (fun e => e * y) l (𝓝 y) := hl.tendsto_mul_right y
    have h2 : Continuous fun z : RealCrossedProduct => ρ.idealExt z η :=
      (ContinuousLinearMap.apply ℂ ρ.H η).continuous.comp ρ.continuous_idealExt
    have h3 := (h2.tendsto y).comp h1
    refine h3.congr fun e => ?_
    simp only [Function.comp, map_mul]
    rfl
  have hsub : ∀ ξ₁ ξ₂, ξ₁ ∈ S → ξ₂ ∈ S → ξ₁ + ξ₂ ∈ S := fun ξ₁ ξ₂ h₁ h₂ => by
    simp only [S, mem_setOf_eq, map_add] at h₁ h₂ ⊢
    exact h₁.add h₂
  have hsmul : ∀ (c : ℂ) ξ, ξ ∈ S → c • ξ ∈ S := fun c ξ h => by
    simp only [S, mem_setOf_eq, map_smul] at h ⊢
    exact h.const_smul c
  have hzero : (0 : ρ.H) ∈ S := by
    simp only [S, mem_setOf_eq, map_zero]
    exact tendsto_const_nhds
  let SS : Submodule ℂ ρ.H :=
    { carrier := S
      add_mem' := fun h₁ h₂ => hsub _ _ h₁ h₂
      zero_mem' := hzero
      smul_mem' := fun c _ h => hsmul c _ h }
  have hV : (⨆ y : RealCrossedProduct,
      LinearMap.range ((ρ.idealExt y : ρ.H →L[ℂ] ρ.H) : ρ.H →ₗ[ℂ] ρ.H)) ≤ SS := by
    refine iSup_le fun y => ?_
    rintro _ ⟨η, rfl⟩
    exact hgen y η
  have hclS : ∀ ξ ∈ ρ.essSpace, ξ ∈ S := by
    intro ξ hξ₀
    have hξ : ξ ∈ closure ((⨆ y : RealCrossedProduct,
        LinearMap.range ((ρ.idealExt y : ρ.H →L[ℂ] ρ.H) : ρ.H →ₗ[ℂ] ρ.H) : Submodule ℂ ρ.H) :
          Set ρ.H) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hξ₀
    change Tendsto (fun e => ρ.idealExt e ξ) l (𝓝 ξ)
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨b, hb, hξb⟩ := Metric.mem_closure_iff.mp hξ (ε / 3) (by positivity)
    have hbS : Tendsto (fun e => ρ.idealExt e b) l (𝓝 b) := hV hb
    filter_upwards [Metric.tendsto_nhds.mp hbS (ε / 3) (by positivity), hl.eventually_norm]
      with e he hne
    have hop : ‖ρ.idealExt e‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le ρ.idealExt e).trans hne
    calc dist (ρ.idealExt e ξ) ξ
        ≤ dist (ρ.idealExt e ξ) (ρ.idealExt e b) + dist (ρ.idealExt e b) b + dist b ξ :=
          dist_triangle4 _ _ _ _
      _ ≤ dist ξ b + ε / 3 + ε / 3 := by
          have h1 : dist (ρ.idealExt e ξ) (ρ.idealExt e b) ≤ dist ξ b := by
            rw [dist_eq_norm, dist_eq_norm, ← map_sub]
            exact ((ρ.idealExt e).le_opNorm _).trans
              (mul_le_of_le_one_left (norm_nonneg _) hop)
          have h3 : dist b ξ ≤ ε / 3 := by
            rw [dist_comm]
            exact hξb.le
          linarith [he.le]
      _ < ε := by linarith
  -- the estimate along the approximate unit
  have hconv : Tendsto (fun e => ρ.π K (ρ.idealExt e ξ)) l (𝓝 (ρ.π K ξ)) :=
    ((ρ.π K).continuous.tendsto ξ).comp (hclS ξ hξ)
  refine le_of_tendsto hconv.norm ?_
  filter_upwards [hl.eventually_norm] with e he
  have heq : ρ.π K (ρ.idealExt e ξ) = ρ.idealExt (coneMulLeft K e) ξ := by
    rw [ρ.idealExt_coneMulLeft]
    rfl
  rw [heq]
  calc ‖ρ.idealExt (coneMulLeft K e) ξ‖ ≤ ‖ρ.idealExt (coneMulLeft K e)‖ * ‖ξ‖ :=
        (ρ.idealExt _).le_opNorm ξ
    _ ≤ ‖coneMulLeft K e‖ * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le ρ.idealExt _) (norm_nonneg _)
    _ ≤ ‖(K : BandKernel).op‖ * ‖e‖ * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right (norm_coneMulLeft_le K e) (norm_nonneg _)
    _ ≤ ‖(K : BandKernel).op‖ * ‖ξ‖ := by
        gcongr
        exact mul_le_of_le_one_right (norm_nonneg _) he

/-- A cone kernel restricted to the orthogonal complement of the essential subspace. -/
def BoundedRep.restrictOrth (K : coneKernels) : ρ.essSpaceᗮ →L[ℂ] ρ.essSpaceᗮ :=
  ((ρ.π K).comp (ρ.essSpaceᗮ).subtypeL).codRestrict (ρ.essSpaceᗮ) fun ζ =>
    ρ.π_mem_orthogonal K ζ.2

theorem BoundedRep.restrictOrth_apply (K : coneKernels) (ζ : ρ.essSpaceᗮ) :
    (ρ.restrictOrth K ζ : ρ.H) = ρ.π K ζ := rfl

theorem BoundedRep.restrictOrth_coneIdealHom (k : KernelAlg) :
    ρ.restrictOrth (coneIdealHom k) = 0 := by
  ext ζ
  rw [ρ.restrictOrth_apply, ← ρ.idealExt_toRCP, ρ.idealExt_apply_eq_zero ζ.2]
  rfl

theorem BoundedRep.restrictOrth_add (K L : coneKernels) :
    ρ.restrictOrth (K + L) = ρ.restrictOrth K + ρ.restrictOrth L := by
  ext ζ
  change ρ.π (K + L) ζ = ρ.π K ζ + ρ.π L ζ
  rw [map_add]
  rfl

theorem BoundedRep.restrictOrth_sub (K L : coneKernels) :
    ρ.restrictOrth (K - L) = ρ.restrictOrth K - ρ.restrictOrth L := by
  ext ζ
  change ρ.π (K - L) ζ = ρ.π K ζ - ρ.π L ζ
  rw [map_sub]
  rfl

theorem BoundedRep.restrictOrth_smul (c : ℂ) (K : coneKernels) :
    ρ.restrictOrth (c • K) = c • ρ.restrictOrth K := by
  ext ζ
  change ρ.π (c • K) ζ = c • ρ.π K ζ
  rw [map_smul]
  rfl

theorem BoundedRep.restrictOrth_mul (K L : coneKernels) :
    ρ.restrictOrth (K * L) = ρ.restrictOrth K * ρ.restrictOrth L := by
  ext ζ
  change ρ.π (K * L) ζ = ρ.π K (ρ.π L ζ)
  rw [map_mul]
  rfl

theorem BoundedRep.restrictOrth_star (K : coneKernels) :
    ρ.restrictOrth (star K) = ContinuousLinearMap.adjoint (ρ.restrictOrth K) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [Submodule.coe_inner, Submodule.coe_inner, ρ.restrictOrth_apply, ρ.restrictOrth_apply,
    map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

theorem BoundedRep.norm_restrictOrth_le (K : coneKernels) : ‖ρ.restrictOrth K‖ ≤ ‖ρ.π K‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ζ => by
    rw [Submodule.coe_norm, ρ.restrictOrth_apply, Submodule.coe_norm]
    exact (ρ.π K).le_opNorm _

/-- The profile of a convolution kernel. -/
def convProfileOf (K : convKernels) : C_c(ℝ, ℂ) := Classical.choose K.2

theorem conv_convProfileOf (K : convKernels) : conv (convProfileOf K) = K :=
  Classical.choose_spec K.2

theorem convProfileOf_convElem (G : C_c(ℝ, ℂ)) : convProfileOf (convElem G) = G :=
  conv_injective (conv_convProfileOf (convElem G))

theorem cutElem_add (G₁ G₂ : C_c(ℝ, ℂ)) : cutElem (G₁ + G₂) = cutElem G₁ + cutElem G₂ :=
  Subtype.ext (cutConv_add G₁ G₂)

theorem cutElem_smul (c : ℂ) (G : C_c(ℝ, ℂ)) : cutElem (c • G) = c • cutElem G :=
  Subtype.ext (cutConv_smul c G)

theorem exists_cutElem_mul (G₁ G₂ : C_c(ℝ, ℂ)) :
    ∃ k : KernelAlg, cutElem G₁ * cutElem G₂ - cutElem (convProfile G₁ G₂) = coneIdealHom k := by
  obtain ⟨k, hk⟩ := cutConv_mul_cutConv_sub_mem G₁ G₂
  exact ⟨k, Subtype.ext hk.symm⟩

theorem exists_star_cutElem (G : C_c(ℝ, ℂ)) :
    ∃ k : KernelAlg, star (cutElem G) - cutElem (starProfile G) = coneIdealHom k := by
  obtain ⟨k, hk⟩ := star_cutConv_sub_mem G
  exact ⟨k, Subtype.ext hk.symm⟩

/-- **The representation of `C*(ℝ)` on the complement of the essential subspace**: there the
compact ideal acts by zero, so `G ↦ ρ(χG)` is multiplicative. -/
def BoundedRep.tailRep : convKernels →⋆ₙₐ[ℂ] (ρ.essSpaceᗮ →L[ℂ] ρ.essSpaceᗮ) where
  toFun K := ρ.restrictOrth (cutElem (convProfileOf K))
  map_smul' c K := by
    have h : convProfileOf (c • K) = c • convProfileOf K :=
      conv_injective (by rw [conv_convProfileOf, conv_smul, conv_convProfileOf]; rfl)
    simp only [MonoidHom.id_apply]
    rw [h, cutElem_smul, ρ.restrictOrth_smul]
  map_zero' := by
    have h : convProfileOf 0 = 0 :=
      conv_injective (by rw [conv_convProfileOf, conv_zero]; rfl)
    change ρ.restrictOrth (cutElem (convProfileOf 0)) = 0
    rw [h, show cutElem 0 = 0 from Subtype.ext cutConv_zero, show (0 : coneKernels) =
      coneIdealHom 0 from (map_zero coneIdealHom).symm, ρ.restrictOrth_coneIdealHom]
  map_add' K L := by
    have h : convProfileOf (K + L) = convProfileOf K + convProfileOf L :=
      conv_injective (by rw [conv_convProfileOf, conv_add, conv_convProfileOf, conv_convProfileOf]; rfl)
    change ρ.restrictOrth (cutElem (convProfileOf (K + L))) = _ + _
    rw [h, cutElem_add, ρ.restrictOrth_add]
  map_mul' K L := by
    have h : convProfileOf (K * L) = convProfile (convProfileOf K) (convProfileOf L) :=
      conv_injective (by
        rw [conv_convProfileOf, ← conv_mul_conv, conv_convProfileOf, conv_convProfileOf]; rfl)
    obtain ⟨k, hk⟩ := exists_cutElem_mul (convProfileOf K) (convProfileOf L)
    have hc : cutElem (convProfile (convProfileOf K) (convProfileOf L)) =
        cutElem (convProfileOf K) * cutElem (convProfileOf L) - coneIdealHom k := by
      rw [← hk, sub_sub_cancel]
    change ρ.restrictOrth (cutElem (convProfileOf (K * L))) =
      ρ.restrictOrth (cutElem (convProfileOf K)) * ρ.restrictOrth (cutElem (convProfileOf L))
    rw [h, hc, ρ.restrictOrth_sub, ρ.restrictOrth_coneIdealHom, sub_zero, ρ.restrictOrth_mul]
  map_star' K := by
    have h : convProfileOf (star K) = starProfile (convProfileOf K) :=
      conv_injective (by rw [conv_convProfileOf, ← star_conv, conv_convProfileOf]; rfl)
    obtain ⟨k, hk⟩ := exists_star_cutElem (convProfileOf K)
    have hc : cutElem (starProfile (convProfileOf K)) =
        star (cutElem (convProfileOf K)) - coneIdealHom k := by
      rw [← hk, sub_sub_cancel]
    change ρ.restrictOrth (cutElem (convProfileOf (star K))) =
      star (ρ.restrictOrth (cutElem (convProfileOf K)))
    rw [h, hc, ρ.restrictOrth_sub, ρ.restrictOrth_coneIdealHom, sub_zero, ρ.restrictOrth_star,
      ContinuousLinearMap.star_eq_adjoint]

theorem BoundedRep.tailRep_apply (K : convKernels) :
    ρ.tailRep K = ρ.restrictOrth (cutElem (convProfileOf K)) := rfl

theorem BoundedRep.norm_tailRep_le (K : convKernels) : ‖ρ.tailRep K‖ ≤ convL1Norm K := by
  rw [ρ.tailRep_apply]
  refine (ρ.norm_restrictOrth_le _).trans ((ρ.bound _).trans (le_of_eq ?_))
  rw [coneL1Norm_cutElem]
  have h : K = convElem (convProfileOf K) := Subtype.ext (conv_convProfileOf K).symm
  conv_rhs => rw [h]
  rw [convL1Norm_convElem]

/-- **On the complement of the essential subspace a cone kernel is dominated by the convolution
norm of its symbol**, by full = reduced for `ℝ`. -/
theorem BoundedRep.norm_π_apply_le_of_mem_orthogonal (K : coneKernels) {ζ : ρ.H}
    (hζ : ζ ∈ ρ.essSpaceᗮ) : ‖ρ.π K ζ‖ ≤ ‖(K : BandKernel).op‖ * ‖ζ‖ := by
  have hK : ρ.π K ζ = (ρ.tailRep (convElem (coneSymbol K)) ⟨ζ, hζ⟩ : ρ.H) := by
    rw [ρ.tailRep_apply, convProfileOf_convElem, ρ.restrictOrth_apply]
    conv_lhs => rw [coneKernel_eq_cutElem_add K]
    rw [map_add, _root_.add_apply, ← ρ.idealExt_toRCP,
      ρ.idealExt_apply_eq_zero hζ, add_zero]
  rw [hK, ← Submodule.coe_norm]
  calc ‖ρ.tailRep (convElem (coneSymbol K)) ⟨ζ, hζ⟩‖
      ≤ ‖ρ.tailRep (convElem (coneSymbol K))‖ * ‖(⟨ζ, hζ⟩ : ρ.essSpaceᗮ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(conv (coneSymbol K)).op‖ * ‖ζ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_le_norm_op_of_convL1Bounded ρ.tailRep ρ.norm_tailRep_le _) (norm_nonneg _)
    _ ≤ ‖(K : BandKernel).op‖ * ‖ζ‖ :=
        mul_le_mul_of_nonneg_right (norm_op_conv_coneSymbol_le K) (norm_nonneg _)

/-- **Every bounded representation of the cone core is dominated by the Schrödinger
representation.**  Split `ξ` along the essential subspace of the compact ideal and its orthogonal
complement; both are invariant, and the two estimates add by Pythagoras. -/
theorem BoundedRep.norm_π_le_norm_op (K : coneKernels) : ‖ρ.π K‖ ≤ ‖(K : BandKernel).op‖ := by
  haveI : CompleteSpace ρ.essSpace := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ξ => ?_
  set a := ρ.essSpace.starProjection ξ
  set b := ξ - a
  have ha : a ∈ ρ.essSpace := ρ.essSpace.starProjection_apply_mem ξ
  have hb : b ∈ ρ.essSpaceᗮ := ρ.essSpace.sub_starProjection_mem_orthogonal ξ
  have hξ : ξ = a + b := by rw [add_sub_cancel]
  have hab : ⟪a, b⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal ha hb
  have hKab : ⟪ρ.π K a, ρ.π K b⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (ρ.π_mem_essSpace K ha) (ρ.π_mem_orthogonal K hb)
  set c := ‖(K : BandKernel).op‖
  have h1 := ρ.norm_π_apply_le_of_mem_essSpace K ha
  have h2 := ρ.norm_π_apply_le_of_mem_orthogonal K hb
  have hP1 : ‖ρ.π K a + ρ.π K b‖ ^ 2 = ‖ρ.π K a‖ ^ 2 + ‖ρ.π K b‖ ^ 2 := by
    rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hKab]
  have hP2 : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hab]
  have hsq : ‖ρ.π K ξ‖ ^ 2 ≤ (c * ‖ξ‖) ^ 2 := by
    rw [hξ, map_add, hP1, mul_pow, hP2]
    have e1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [mul_pow] at e1 e2
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    two_ne_zero).mp hsq

end FullReduced

/-! ## The Schrödinger representation of `C₀((-∞, +∞]) ⋊ ℝ` is faithful -/

theorem norm_toEnvelope_cone_le (K : coneKernels) :
    ‖toEnvelope coneKernels coneL1Norm K‖ ≤ ‖(K : BandKernel).op‖ :=
  EnvFamily.norm_le_of_forall_le (norm_nonneg _) fun ρ => ρ.norm_π_le_norm_op K

/-- **Full = reduced for `C₀((-∞, +∞]) ⋊ ℝ`**: the Schrödinger representation of the full crossed
product on `L²(ℝ)` is isometric. -/
theorem norm_coneSchrodinger (y : ConeCrossedProduct) : ‖coneSchrodinger y‖ = ‖y‖ := by
  have hcore : ∀ K : coneKernels, ‖coneSchrodinger (toEnvelope coneKernels coneL1Norm K)‖ =
      ‖toEnvelope coneKernels coneL1Norm K‖ := fun K =>
    le_antisymm (coneSchrodingerRep.norm_le_envelope K)
      ((norm_toEnvelope_cone_le K).trans (le_of_eq (congrArg norm
        (coneSchrodinger_toEnvelope K).symm)))
  have h := (toEnvelope_dense coneKernels coneL1Norm).equalizer
    (continuous_norm.comp continuous_coneSchrodinger) continuous_norm (funext hcore)
  exact congrFun h y

theorem coneSchrodinger_injective : Function.Injective coneSchrodinger := by
  intro y z h
  have := norm_coneSchrodinger (y - z)
  rw [map_sub, h, sub_self, norm_zero] at this
  exact sub_eq_zero.mp (norm_eq_zero.mp this.symm)


end GaloisForLFunctions.HTGeometry
