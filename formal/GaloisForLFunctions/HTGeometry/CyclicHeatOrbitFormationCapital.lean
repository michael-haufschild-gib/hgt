import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitSelection
import GaloisForLFunctions.HTGeometry.SplitRecoveryFormationCapital
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCofinalChildTraceClass

/-!
# Formation capital of a cyclic heat source

For a Hilbert–Schmidt defect `X : U → ℓ²`:

* `E_G(X X^*) = Σ_k ‖X^* f_k‖²/γ_k = ‖G^{-1/2} X‖²_HS` (**(OG.35a)**), finite exactly when
  `X = G^{1/2} Y` for a Hilbert–Schmidt `Y`, equivalently when `X = W B` for a Hilbert–Schmidt
  control `B`;
* `E_G(X X^*)` is the least formation capital `min {‖B‖²_HS : W B = X}` (**(OG.22a)**), attained
  by the unique factor `B_min = V^* Y` (**(OG.22b)**), and every factor splits orthogonally as
  `B = B_min + C`, `V C = 0`, `‖B‖²_HS = ‖B_min‖²_HS + ‖C‖²_HS` (**(OG.22c)**);
* for a control `B`, the reachable defect `T = (WB)(WB)^*` is positive trace class with
  `E_G(T) = ‖V B‖²_HS ≤ ‖B‖²_HS` (**(OG.22d)–(OG.22e)**), so bounded formation capital together
  with approximate source invariance forces `‖T_n‖₁ → 0`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι : Type*}

local notation "ℓ²ι" => lp (fun _ : ι => ℂ) 2

namespace CyclicHeatSource

variable (c : CyclicHeatSource ι) [DecidableEq ι]
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]

omit [DecidableEq ι] in
theorem inner_comp_adjoint_self (X : U →L[ℂ] ℓ²ι) (x : ℓ²ι) :
    ⟪x, (X ∘L ContinuousLinearMap.adjoint X) x⟫_ℂ = ((‖ContinuousLinearMap.adjoint X x‖ ^ 2 : ℝ) : ℂ) := by
  rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- **(OG.35a)** `E_G(XX^*) = Σ_k ‖X^* f_k‖²/γ_k`. -/
theorem orbitDefectCost_formation (X : U →L[ℂ] ℓ²ι) :
    c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) =
      ∑' k, ENNReal.ofReal (‖ContinuousLinearMap.adjoint X (c.orbitEigenbasis k)‖ ^ 2 /
        c.orbitEigenvalue k) := by
  rw [orbitDefectCost]
  refine tsum_congr fun k => ?_
  rw [inner_comp_adjoint_self, Complex.ofReal_re]

omit [DecidableEq ι] in
/-- A Hilbert–Schmidt defect `XX^*` is positive and trace class. -/
theorem formation_traceClass {X : U →L[ℂ] ℓ²ι} (hX : X.IsHilbertSchmidt) :
    (X ∘L ContinuousLinearMap.adjoint X).IsPositive ∧ MemSchattenClass 1 (X ∘L ContinuousLinearMap.adjoint X) := by
  have hpos : (X ∘L ContinuousLinearMap.adjoint X).IsPositive := by
    have h := ContinuousLinearMap.isPositive_adjoint_comp_self (ContinuousLinearMap.adjoint X)
    rwa [ContinuousLinearMap.adjoint_adjoint] at h
  classical
  refine ⟨hpos, memSchattenClass_one_of_isPositive_of_summable_diagonal (HilbertSchmidt.lpBasis ι)
    hpos ?_⟩
  simp_rw [inner_comp_adjoint_self]
  exact Complex.summable_ofReal.2 (hX.adjoint.summable (HilbertSchmidt.lpBasis ι))

/-- **(OG.35a)** `E_G((G^{1/2}Y)(G^{1/2}Y)^*) = ‖Y‖²_HS`. -/
theorem orbitDefectCost_root {Y : U →L[ℂ] ℓ²ι} (hY : Y.IsHilbertSchmidt) :
    c.orbitDefectCost ((c.orbitRoot ∘L Y) ∘L ContinuousLinearMap.adjoint (c.orbitRoot ∘L Y)) =
      ENNReal.ofReal (ContinuousLinearMap.hsNormSq Y) := by
  have hadj : ContinuousLinearMap.adjoint (c.orbitRoot ∘L Y) =
      ContinuousLinearMap.adjoint Y ∘L c.orbitRoot := by
    rw [ContinuousLinearMap.adjoint_comp, c.isSelfAdjoint_orbitRoot.adjoint_eq]
  have hterm : ∀ k, ‖ContinuousLinearMap.adjoint (c.orbitRoot ∘L Y) (c.orbitEigenbasis k)‖ ^ 2 /
      c.orbitEigenvalue k = ‖ContinuousLinearMap.adjoint Y (c.orbitEigenbasis k)‖ ^ 2 := fun k => by
    rw [hadj, ContinuousLinearMap.comp_apply, orbitRoot_orbitEigenbasis, map_smul, norm_smul,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (c.orbitEigenvalue_pos k).le]
    field_simp [(c.orbitEigenvalue_pos k).ne']
  rw [orbitDefectCost_formation]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hY.adjoint.summable c.orbitEigenbasis),
    ← ContinuousLinearMap.hsNormSq_eq hY.adjoint c.orbitEigenbasis, hY.hsNormSq_adjoint]

theorem summable_formation_of_lt_top {X : U →L[ℂ] ℓ²ι}
    (hX : c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) < ⊤) :
    Summable fun k => ‖ContinuousLinearMap.adjoint X (c.orbitEigenbasis k)‖ ^ 2 / c.orbitEigenvalue k := by
  rw [orbitDefectCost_formation] at hX
  have h := ENNReal.summable_toReal hX.ne
  refine h.congr fun k => ?_
  rw [ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (c.orbitEigenvalue_pos k).le)]

/-- The columns `X^* f_k / √γ_k` of the square-root factor. -/
def rootColumn (X : U →L[ℂ] ℓ²ι) (k : EigenIndex c.orbitGramian) : U :=
  ((Real.sqrt (c.orbitEigenvalue k))⁻¹ : ℂ) • ContinuousLinearMap.adjoint X (c.orbitEigenbasis k)

theorem norm_sq_rootColumn (X : U →L[ℂ] ℓ²ι) (k : EigenIndex c.orbitGramian) :
    ‖c.rootColumn X k‖ ^ 2 = ‖ContinuousLinearMap.adjoint X (c.orbitEigenbasis k)‖ ^ 2 /
      c.orbitEigenvalue k := by
  rw [rootColumn, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, inv_pow, Real.sq_sqrt (c.orbitEigenvalue_pos k).le]
  ring

/-- **(OG.35a)** For a finite-cost defect, the adjoint `Y^*` of the factor `Y = G^{-1/2} X`. -/
def rootFactorAdjoint {X : U →L[ℂ] ℓ²ι} (hX : c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) < ⊤) :
    ℓ²ι →L[ℂ] U :=
  squareSummableSynthesis (c.rootColumn X) (by
      simp_rw [norm_sq_rootColumn]
      exact c.summable_formation_of_lt_top hX) ∘L
    c.orbitEigenbasis.repr.toContinuousLinearEquiv.toContinuousLinearMap

theorem rootFactorAdjoint_orbitEigenbasis {X : U →L[ℂ] ℓ²ι}
    (hX : c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) < ⊤) (k : EigenIndex c.orbitGramian) :
    c.rootFactorAdjoint hX (c.orbitEigenbasis k) = c.rootColumn X k := by
  classical
  rw [rootFactorAdjoint, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    HilbertBasis.repr_self]
  rw [squareSummableSynthesis_single, one_smul]

/-- **(OG.35a)** The square-root factor `Y = G^{-1/2} X`. -/
def rootFactor {X : U →L[ℂ] ℓ²ι} (hX : c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) < ⊤) :
    U →L[ℂ] ℓ²ι := ContinuousLinearMap.adjoint (c.rootFactorAdjoint hX)

theorem isHilbertSchmidt_rootFactor {X : U →L[ℂ] ℓ²ι}
    (hX : c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) < ⊤) :
    (c.rootFactor hX).IsHilbertSchmidt := by
  exact ContinuousLinearMap.IsHilbertSchmidt.adjoint
    ((squareSummableSynthesis_isHilbertSchmidt _).comp_right _)

theorem orbitRoot_comp_rootFactor {X : U →L[ℂ] ℓ²ι}
    (hX : c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) < ⊤) :
    c.orbitRoot ∘L c.rootFactor hX = X := by
  apply ContinuousLinearMap.adjoint.injective
  rw [ContinuousLinearMap.adjoint_comp, rootFactor, ContinuousLinearMap.adjoint_adjoint,
    c.isSelfAdjoint_orbitRoot.adjoint_eq]
  refine ext_hilbertBasis c.orbitEigenbasis fun k => ?_
  rw [ContinuousLinearMap.comp_apply, orbitRoot_orbitEigenbasis, map_smul,
    rootFactorAdjoint_orbitEigenbasis, rootColumn, smul_smul, mul_inv_cancel₀, one_smul]
  exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (c.orbitEigenvalue_pos k)).ne'

omit [CompleteSpace U] in
/-- `W B = X` forces `X = G^{1/2} (V B)`. -/
theorem orbitRoot_comp_coisometry {B : U →L[ℂ] HalfLineL2} :
    c.heatReachability ∘L B = c.orbitRoot ∘L (c.orbitCoisometry ∘L B) := by
  rw [heatReachability_eq, ContinuousLinearMap.comp_assoc]

/-- **(OG.22a) Equivalences.**  `E_G(XX^*) < ∞` iff `X = G^{1/2} Y` with `Y` Hilbert–Schmidt, iff
`X = W B` with `B` Hilbert–Schmidt. -/
theorem formation_iff (X : U →L[ℂ] ℓ²ι) :
    (c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) < ⊤ ↔
        ∃ Y : U →L[ℂ] ℓ²ι, Y.IsHilbertSchmidt ∧ c.orbitRoot ∘L Y = X) ∧
      (c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) < ⊤ ↔
        ∃ B : U →L[ℂ] HalfLineL2, B.IsHilbertSchmidt ∧ c.heatReachability ∘L B = X) := by
  have h1 : c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) < ⊤ ↔
      ∃ Y : U →L[ℂ] ℓ²ι, Y.IsHilbertSchmidt ∧ c.orbitRoot ∘L Y = X := by
    constructor
    · intro hX
      exact ⟨c.rootFactor hX, c.isHilbertSchmidt_rootFactor hX, c.orbitRoot_comp_rootFactor hX⟩
    · rintro ⟨Y, hY, rfl⟩
      rw [c.orbitDefectCost_root hY]
      exact ENNReal.ofReal_lt_top
  refine ⟨h1, h1.trans ⟨fun ⟨Y, hY, hYX⟩ => ⟨c.orbitCoisometryAdjoint ∘L Y, hY.comp_left _, ?_⟩,
    fun ⟨B, hB, hBX⟩ => ⟨c.orbitCoisometry ∘L B, hB.comp_left _, ?_⟩⟩⟩
  · rw [heatReachability_eq, ← hYX, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc c.orbitCoisometry, orbitCoisometry_comp_adjoint]
    exact ContinuousLinearMap.ext fun _ => rfl
  · rw [← hBX, orbitRoot_comp_coisometry]

theorem norm_orbitCoisometryAdjoint_comp (Y : U →L[ℂ] ℓ²ι) :
    ContinuousLinearMap.hsNormSq (c.orbitCoisometryAdjoint ∘L Y) = ContinuousLinearMap.hsNormSq Y := by
  unfold ContinuousLinearMap.hsNormSq
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.comp_apply, norm_orbitCoisometryAdjoint]

theorem hsNormSq_orbitCoisometry_comp_le {B : U →L[ℂ] HalfLineL2} (hB : B.IsHilbertSchmidt) :
    ContinuousLinearMap.hsNormSq (c.orbitCoisometry ∘L B) ≤ ContinuousLinearMap.hsNormSq B := by
  unfold ContinuousLinearMap.hsNormSq
  refine Summable.tsum_le_tsum (fun i => ?_)
    ((hB.comp_left _).summable (ContinuousLinearMap.hsBasis ℂ U))
    (hB.summable (ContinuousLinearMap.hsBasis ℂ U))
  rw [ContinuousLinearMap.comp_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (c.norm_orbitCoisometry_le _) 2

omit [CompleteSpace U] in
theorem heatReachability_comp_coisometryAdjoint (Y : U →L[ℂ] ℓ²ι) :
    c.heatReachability ∘L (c.orbitCoisometryAdjoint ∘L Y) = c.orbitRoot ∘L Y := by
  rw [heatReachability_eq, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc c.orbitCoisometry, orbitCoisometry_comp_adjoint]
  exact ContinuousLinearMap.ext fun _ => rfl

theorem orbitCoisometry_eq_zero_of_mem_ker {z : HalfLineL2} (hz : c.heatReachability z = 0) :
    c.orbitCoisometry z = 0 := by
  apply c.orbitRoot_injective
  rw [map_zero, ← ContinuousLinearMap.comp_apply, ← heatReachability_eq]
  exact hz

theorem orbitCoisometryAdjoint_mem_coimage (y : ℓ²ι) :
    c.orbitCoisometryAdjoint y ∈ (LinearMap.ker (c.heatReachability : HalfLineL2 →ₗ[ℂ] ℓ²ι))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro z hz
  have hVz := c.orbitCoisometry_eq_zero_of_mem_ker (LinearMap.mem_ker.1 hz)
  rw [← ContinuousLinearMap.adjoint_inner_right, ← orbitCoisometry, hVz, inner_zero_right]

omit [CompleteSpace U] in
theorem minimalFactor_orbitCoisometryAdjoint (Y : U →L[ℂ] ℓ²ι) :
    minimalFactor c.heatReachability (c.orbitCoisometryAdjoint ∘L Y) = c.orbitCoisometryAdjoint ∘L Y := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [minimalFactor, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, coimageProjection]
  exact Submodule.starProjection_eq_self_iff.2 (c.orbitCoisometryAdjoint_mem_coimage _)

/-- **(OG.22a) Least formation capital.**  `E_G(XX^*) = min {‖B‖²_HS : W B = X}`, infinite when no
Hilbert–Schmidt factorization exists. -/
theorem orbitDefectCost_eq_formationCapital (X : U →L[ℂ] ℓ²ι) :
    c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) = formationCapital c.heatReachability X := by
  by_cases hX : c.orbitDefectCost (X ∘L ContinuousLinearMap.adjoint X) < ⊤
  · have hY := c.isHilbertSchmidt_rootFactor hX
    have hYX := c.orbitRoot_comp_rootFactor hX
    have hmem : c.orbitCoisometryAdjoint ∘L c.rootFactor hX ∈
        formationFactorizations c.heatReachability X :=
      ⟨hY.comp_left _, by rw [heatReachability_comp_coisometryAdjoint, hYX]⟩
    rw [formationCapital_eq_of_mem hmem, minimalFactor_orbitCoisometryAdjoint,
      norm_orbitCoisometryAdjoint_comp]
    conv_lhs => rw [← hYX]
    exact c.orbitDefectCost_root hY
  · rw [not_lt, top_le_iff] at hX
    rw [hX, eq_comm, formationCapital_eq_top_iff]
    refine Set.eq_empty_of_forall_notMem fun B hB => ?_
    have h := (c.formation_iff X).2.2 ⟨B, hB.1, hB.2⟩
    rw [hX] at h
    exact lt_irrefl _ h

theorem hsInner_orbitCoisometryAdjoint_eq_zero (Y : U →L[ℂ] ℓ²ι) {C : U →L[ℂ] HalfLineL2}
    (hC : c.orbitCoisometry ∘L C = 0) :
    ContinuousLinearMap.hsInner (c.orbitCoisometryAdjoint ∘L Y) C = 0 := by
  rw [ContinuousLinearMap.hsInner]
  have hz : ∀ i, ⟪(c.orbitCoisometryAdjoint ∘L Y) (ContinuousLinearMap.hsBasis ℂ U i),
      C (ContinuousLinearMap.hsBasis ℂ U i)⟫_ℂ = 0 := fun i => by
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_right, ← orbitCoisometry,
      ← ContinuousLinearMap.comp_apply c.orbitCoisometry, hC, zero_apply,
      inner_zero_right]
  simp only [hz, tsum_zero]

/-- **(OG.22b)** The least-capital factor of a factorization `W B = X` is `B_min = V^* (V B)`,
with `G^{1/2} (V B) = X`. -/
theorem minimalFactor_eq {B : U →L[ℂ] HalfLineL2} (hB : B.IsHilbertSchmidt) :
    minimalFactor c.heatReachability B = c.orbitCoisometryAdjoint ∘L (c.orbitCoisometry ∘L B) := by
  have h1 : minimalFactor c.heatReachability B ∈
      formationFactorizations c.heatReachability (c.heatReachability ∘L B) :=
    minimalFactor_mem ⟨hB, rfl⟩
  have h2 : c.orbitCoisometryAdjoint ∘L (c.orbitCoisometry ∘L B) ∈
      formationFactorizations c.heatReachability (c.heatReachability ∘L B) :=
    ⟨(hB.comp_left _).comp_left _, by
      rw [heatReachability_comp_coisometryAdjoint, orbitRoot_comp_coisometry]⟩
  refine minimalFactor_unique h1 h2 (fun C hC => hsInner_minimalFactor_eq_zero hC) fun C hC => ?_
  refine c.hsInner_orbitCoisometryAdjoint_eq_zero _ ?_
  refine ContinuousLinearMap.ext fun u => ?_
  have := DFunLike.congr_fun hC u
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at this ⊢
  exact c.orbitCoisometry_eq_zero_of_mem_ker this

/-- **(OG.22c) Orthogonal splitting.**  Every Hilbert–Schmidt control splits as `B = B_min + C`
with `V C = 0` and `‖B‖²_HS = ‖B_min‖²_HS + ‖C‖²_HS`; equality of capitals forces `B = B_min`. -/
theorem capital_split {B : U →L[ℂ] HalfLineL2} (hB : B.IsHilbertSchmidt) :
    c.orbitCoisometry ∘L (B - c.orbitCoisometryAdjoint ∘L (c.orbitCoisometry ∘L B)) = 0 ∧
      ContinuousLinearMap.hsNormSq B =
        ContinuousLinearMap.hsNormSq (c.orbitCoisometryAdjoint ∘L (c.orbitCoisometry ∘L B)) +
          ContinuousLinearMap.hsNormSq (B - c.orbitCoisometryAdjoint ∘L (c.orbitCoisometry ∘L B)) ∧
      (ContinuousLinearMap.hsNormSq B =
          ContinuousLinearMap.hsNormSq (c.orbitCoisometryAdjoint ∘L (c.orbitCoisometry ∘L B)) ↔
        B = c.orbitCoisometryAdjoint ∘L (c.orbitCoisometry ∘L B)) := by
  set Bm := c.orbitCoisometryAdjoint ∘L (c.orbitCoisometry ∘L B)
  have hBm : Bm.IsHilbertSchmidt := (hB.comp_left _).comp_left _
  have hC : (B - Bm).IsHilbertSchmidt := hB.sub hBm
  have hVC : c.orbitCoisometry ∘L (B - Bm) = 0 := by
    rw [ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.comp_assoc,
      orbitCoisometry_comp_adjoint, sub_eq_zero]
    exact ContinuousLinearMap.ext fun _ => rfl
  have hsplit := ContinuousLinearMap.hsNormSq_add_eq_of_hsInner_eq_zero hBm hC
    (c.hsInner_orbitCoisometryAdjoint_eq_zero _ hVC)
  rw [add_sub_cancel] at hsplit
  refine ⟨hVC, hsplit, ⟨fun h => ?_, fun h => by rw [← h]⟩⟩
  have h0 : ContinuousLinearMap.hsNormSq (B - Bm) = 0 := by linarith
  exact sub_eq_zero.1 ((ContinuousLinearMap.hsNormSq_eq_zero_iff hC).1 h0)

/-- **(OG.22d)–(OG.22e)** A control `B` forms the positive trace-class defect `T = (WB)(WB)^*`
with `E_G(T) = ‖V B‖²_HS ≤ ‖B‖²_HS`. -/
theorem reachableDefect {B : U →L[ℂ] HalfLineL2} (hB : B.IsHilbertSchmidt) :
    ((c.heatReachability ∘L B) ∘L ContinuousLinearMap.adjoint (c.heatReachability ∘L B)).IsPositive ∧
      MemSchattenClass 1
        ((c.heatReachability ∘L B) ∘L ContinuousLinearMap.adjoint (c.heatReachability ∘L B)) ∧
      c.orbitDefectCost
          ((c.heatReachability ∘L B) ∘L ContinuousLinearMap.adjoint (c.heatReachability ∘L B)) =
        ENNReal.ofReal (ContinuousLinearMap.hsNormSq (c.orbitCoisometry ∘L B)) ∧
      ContinuousLinearMap.hsNormSq (c.orbitCoisometry ∘L B) ≤ ContinuousLinearMap.hsNormSq B := by
  obtain ⟨hpos, hS⟩ := formation_traceClass (hB.comp_left c.heatReachability)
  refine ⟨hpos, hS, ?_, c.hsNormSq_orbitCoisometry_comp_le hB⟩
  rw [orbitRoot_comp_coisometry]
  exact c.orbitDefectCost_root (hB.comp_left _)

/-- **(OG.22e) Selection by bounded formation capital.**  Reachable defects `T_n = (WB_n)(WB_n)^*`
with `sup_n ‖B_n‖²_HS < ∞` and `‖[T_n, D]‖₁ + ‖[T_n, P]‖₁ → 0` have `‖T_n‖₁ → 0`. -/
theorem tendsto_traceNorm_of_bounded_capital [Infinite ι] [Countable ι]
    (B : ℕ → U →L[ℂ] HalfLineL2) (hB : ∀ n, (B n).IsHilbertSchmidt) {K : ℝ}
    (hK : ∀ n, ContinuousLinearMap.hsNormSq (B n) ≤ K)
    (hcomm : Tendsto (fun n =>
      traceNorm ℓ²ι (((c.heatReachability ∘L B n) ∘L ContinuousLinearMap.adjoint (c.heatReachability ∘L B n))
          ∘L c.heatReporter - c.heatReporter ∘L
            ((c.heatReachability ∘L B n) ∘L ContinuousLinearMap.adjoint (c.heatReachability ∘L B n))) +
        traceNorm ℓ²ι (((c.heatReachability ∘L B n) ∘L ContinuousLinearMap.adjoint (c.heatReachability ∘L B n))
          ∘L c.heatProjection - c.heatProjection ∘L
            ((c.heatReachability ∘L B n) ∘L ContinuousLinearMap.adjoint (c.heatReachability ∘L B n))))
      atTop (𝓝 0)) :
    Tendsto (fun n => traceNorm ℓ²ι
      ((c.heatReachability ∘L B n) ∘L ContinuousLinearMap.adjoint (c.heatReachability ∘L B n))) atTop (𝓝 0) :=
  c.tendsto_traceNorm_of_selection _ (fun n => (c.reachableDefect (hB n)).1)
    (fun n => (c.reachableDefect (hB n)).2.1) hcomm (M := K) fun n => by
      rw [(c.reachableDefect (hB n)).2.2.1]
      exact ENNReal.ofReal_le_ofReal (((c.reachableDefect (hB n)).2.2.2).trans (hK n))

/-! ## (IX) Positive aggregation -/

/-- **(OG.22h)–(OG.22i)** For positive defects `A_r`, nonnegative weights `w_r` and
`T = Σ_r w_r A_r` (norm convergent), `E_G(T) = Σ_r w_r E_G(A_r)` in `[0, ∞]`. -/
theorem orbitDefectCost_tsum {κ : Type*} (A : κ → ℓ²ι →L[ℂ] ℓ²ι) (hA : ∀ r, (A r).IsPositive)
    (w : κ → ℝ) (hw : ∀ r, 0 ≤ w r) {T : ℓ²ι →L[ℂ] ℓ²ι}
    (hT : HasSum (fun r => ((w r : ℝ) : ℂ) • A r) T) :
    c.orbitDefectCost T = ∑' r, ENNReal.ofReal (w r) * c.orbitDefectCost (A r) := by
  have hdiag : ∀ k, HasSum (fun r => w r * (⟪c.orbitEigenbasis k, A r (c.orbitEigenbasis k)⟫_ℂ).re)
      (⟪c.orbitEigenbasis k, T (c.orbitEigenbasis k)⟫_ℂ).re := fun k => by
    have h := hT.mapL ((innerSL ℂ (c.orbitEigenbasis k)).comp
      (ContinuousLinearMap.apply ℂ ℓ²ι (c.orbitEigenbasis k)))
    have h' := Complex.hasSum_re h
    refine h'.congr_fun fun r => ?_
    simp
  have hnn : ∀ r k, 0 ≤ w r * (⟪c.orbitEigenbasis k, A r (c.orbitEigenbasis k)⟫_ℂ).re /
      c.orbitEigenvalue k := fun r k =>
    div_nonneg (mul_nonneg (hw r) ((hA r).re_inner_nonneg_right _)) (c.orbitEigenvalue_pos k).le
  rw [orbitDefectCost]
  have hterm : ∀ k, ENNReal.ofReal ((⟪c.orbitEigenbasis k, T (c.orbitEigenbasis k)⟫_ℂ).re /
      c.orbitEigenvalue k) = ∑' r, ENNReal.ofReal (w r *
        (⟪c.orbitEigenbasis k, A r (c.orbitEigenbasis k)⟫_ℂ).re / c.orbitEigenvalue k) := fun k => by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => hnn r k) ((hdiag k).summable.div_const _),
      tsum_div_const, (hdiag k).tsum_eq]
  simp_rw [hterm]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun r => ?_
  rw [orbitDefectCost, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [← ENNReal.ofReal_mul (hw r), mul_div_assoc]

/-- **(OG.22i)** One positive-weight infinite-capital component forces infinite capital. -/
theorem orbitDefectCost_tsum_eq_top {κ : Type*} (A : κ → ℓ²ι →L[ℂ] ℓ²ι) (hA : ∀ r, (A r).IsPositive)
    (w : κ → ℝ) (hw : ∀ r, 0 ≤ w r) {T : ℓ²ι →L[ℂ] ℓ²ι}
    (hT : HasSum (fun r => ((w r : ℝ) : ℂ) • A r) T) {r₀ : κ} (hr₀ : 0 < w r₀)
    (htop : c.orbitDefectCost (A r₀) = ⊤) : c.orbitDefectCost T = ⊤ := by
  rw [c.orbitDefectCost_tsum A hA w hw hT, eq_top_iff]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum r₀)
  rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hr₀).ne']

end CyclicHeatSource

end GaloisForLFunctions.HTGeometry
