import GaloisForLFunctions.RHTower.RepPointPairCuspBound
import GaloisForLFunctions.RHTower.FiniteTimeBandFourierCompact
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompactModularPeriodization

/-!
# The core part of a point-pair operator is compact

Let `χ_H = 1 − ψ_H` be the core cutoff: `1` below height `H`, `0` above `2H`.  On the truncated cell
`{z ∈ 𝒟 : Im z ≤ 2H}`, which is compact, only a fixed finite set `S` of translates `B` brings the cell
within `u ≤ R` (`exists_finset_near`).  So the core operator `χ_H L_φ χ_H` has the jointly continuous
bounded kernel `χ_H(z) χ_H(z') ½ Σ_{B ∈ S} φ(u(z, Bz')) ρ(B)`.  Each coordinate of it is the operator
of an `L²` field of continuous functionals `z ↦ ⟪G_j(z), ·⟫`, whose Riesz vectors `G_j(z)` depend
continuously on `z` in `L²` by dominated convergence (`continuous_toLp_of_bound`).  The
Hilbert–Schmidt kernel theorem makes every coordinate compact, hence the core operator is compact
(`isCompactOperator_coreOp`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

/-! ## The core cutoff -/

/-- The core cutoff `χ_H = 1 − ψ_H`: `1` below height `H`, `0` above `2H`. -/
def coreCutoff (H : ℝ) (z : ℍ) : ℝ := 1 - cuspCutoff H z

theorem coreCutoff_nonneg (H : ℝ) (z : ℍ) : 0 ≤ coreCutoff H z :=
  sub_nonneg.2 (cuspCutoff_le_one H z)

theorem coreCutoff_le_one (H : ℝ) (z : ℍ) : coreCutoff H z ≤ 1 := by
  have := cuspCutoff_nonneg H z
  unfold coreCutoff
  linarith

theorem abs_coreCutoff_le (H : ℝ) (z : ℍ) : |coreCutoff H z| ≤ 1 := by
  rw [abs_of_nonneg (coreCutoff_nonneg H z)]
  exact coreCutoff_le_one H z

theorem continuous_coreCutoff (H : ℝ) : Continuous (coreCutoff H) :=
  continuous_const.sub (continuous_cuspCutoff H)

theorem im_lt_of_coreCutoff_ne_zero {H : ℝ} (hH : 0 < H) {z : ℍ} (h : coreCutoff H z ≠ 0) :
    z.im < 2 * H := by
  by_contra hle
  push Not at hle
  exact h (by rw [coreCutoff, cuspCutoff_eq_one hH hle, sub_self])

theorem coreCutoff_eq_one {H : ℝ} (hH : 0 < H) {z : ℍ} (h : z.im ≤ H) : coreCutoff H z = 1 := by
  rw [coreCutoff, cuspCutoff_eq_zero hH h, sub_zero]

variable (ι) in
/-- Multiplication by the core cutoff `χ_H`. -/
def coreMul (H : ℝ) : RepL2 ι →L[ℂ] RepL2 ι :=
  repMul ι (continuous_coreCutoff H).measurable (abs_coreCutoff_le H)

/-! ## A finite set of translates serves the whole core -/

/-- **Uniform local finiteness on the core.**  One finite set of matrices contains every `B` that
brings the modular cell within `u ≤ R` of a point of the truncated cell `{z ∈ 𝒟 : Im z ≤ T}`. -/
theorem exists_finset_near (T R : ℝ) : ∃ S : Finset SL(2, ℤ), ∀ z : ℍ, z ∈ fd → z.im ≤ T →
    ∀ z' : ℍ, z' ∈ fd → ∀ B : SL(2, ℤ), pairU z (B • z') ≤ R → B ∈ S := by
  obtain ⟨D, hD⟩ := (RHTower.D4BMModularCore.truncated_cell_compact T).isBounded.subset_closedBall
    UpperHalfPlane.I
  set R' : ℝ := (Real.cosh (D + (1 + 2 * R)) - 1) / 2 with hR'
  refine ⟨(finite_near_fd UpperHalfPlane.I R').toFinset, fun z hz hzT z' hz' B h => ?_⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨z', hz', ?_⟩
  have hR : 0 ≤ R := (pairU_nonneg _ _).trans h
  have h1 : dist z (B • z') ≤ 1 + 2 * R := DeckPointPair.dist_le_of_pairU_le h
  have h2 : dist z UpperHalfPlane.I ≤ D := Metric.mem_closedBall.1 (hD ⟨hz, hzT⟩)
  have h3 : dist UpperHalfPlane.I (B • z') ≤ D + (1 + 2 * R) := by
    calc dist UpperHalfPlane.I (B • z') ≤ dist UpperHalfPlane.I z + dist z (B • z') :=
          dist_triangle _ _ _
      _ ≤ D + (1 + 2 * R) := by rw [dist_comm]; linarith
  rw [pairU_eq_cosh]
  have h4 : Real.cosh (dist UpperHalfPlane.I (B • z')) ≤ Real.cosh (D + (1 + 2 * R)) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg (dist_nonneg.trans h3)]
    exact h3
  rw [hR']
  linarith

/-! ## Continuity in `L²` by dominated convergence -/

theorem memLp_of_bound_cont {g : ℍ → EuclideanSpace ℂ ι} (hg : Continuous g) {C : ℝ}
    (hb : ∀ z', ‖g z'‖ ≤ C) : MemLp g 2 cellMeasure :=
  MemLp.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hb)

/-- **Continuity in `L²`.**  A jointly continuous, uniformly bounded family `g(z, ·)` depends
continuously on `z` in `L²(𝒟; ℂ^ι)`, by dominated convergence on the finite measure of the cell. -/
theorem continuous_toLp_of_bound {g : ℍ → ℍ → EuclideanSpace ℂ ι}
    (hg : Continuous (Function.uncurry g)) {C : ℝ} (hb : ∀ z z', ‖g z z'‖ ≤ C) :
    Continuous (fun z => (memLp_of_bound_cont (hg.uncurry_left z) (hb z)).toLp (g z)) := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  simp_rw [Lp.edist_toLp_toLp]
  have hfin : ∫⁻ _ : ℍ, ENNReal.ofReal ((2 * C) ^ 2) ∂cellMeasure ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hmeas : ∀ w, Measurable (fun z' => ENNReal.ofReal (‖g w z' - g z z'‖ ^ 2)) := fun w =>
    ENNReal.measurable_ofReal.comp
      ((((hg.uncurry_left w).sub (hg.uncurry_left z)).norm.pow 2).measurable)
  have hbd : ∀ w z', ENNReal.ofReal (‖g w z' - g z z'‖ ^ 2) ≤ ENNReal.ofReal ((2 * C) ^ 2) := by
    intro w z'
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    calc ‖g w z' - g z z'‖ ≤ ‖g w z'‖ + ‖g z z'‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith [hb w z', hb z z']
  have hlim : ∀ z', Tendsto (fun w => ENNReal.ofReal (‖g w z' - g z z'‖ ^ 2)) (𝓝 z) (𝓝 0) := by
    intro z'
    have hc : Tendsto (fun w => g w z') (𝓝 z) (𝓝 (g z z')) := (hg.uncurry_right z').tendsto z
    have := ENNReal.tendsto_ofReal (((hc.sub_const (g z z')).norm).pow 2)
    simpa using this
  have hlin : Tendsto (fun w => ∫⁻ z', ENNReal.ofReal (‖g w z' - g z z'‖ ^ 2) ∂cellMeasure)
      (𝓝 z) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence (μ := cellMeasure) (l := 𝓝 z)
      (F := fun w z' => ENNReal.ofReal (‖g w z' - g z z'‖ ^ 2)) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal ((2 * C) ^ 2)) (Eventually.of_forall hmeas)
      (Eventually.of_forall fun w => Eventually.of_forall (hbd w)) hfin
      (Eventually.of_forall hlim)
    simpa using h
  have hpow : ∀ w, eLpNorm (g w - g z) 2 cellMeasure =
      (∫⁻ z', ENNReal.ofReal (‖g w z' - g z z'‖ ^ 2) ∂cellMeasure) ^ (1 / 2 : ℝ) := by
    intro w
    rw [show (fun z' => ENNReal.ofReal (‖g w z' - g z z'‖ ^ 2)) =
      fun z' => ENNReal.ofReal (‖(g w - g z) z'‖ ^ 2) from rfl, ← eLpNorm_two_sq_ofReal,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp_rw [hpow]
  have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  exact this.comp hlin

/-! ## The kernel theorem in pointwise form -/

/-- The operator of an `L²` field of functionals acts pointwise: `(T_K f)(x) = K(x) f` a.e. -/
theorem kernelOperator_coeFn_ae {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (μ : Measure α) [IsFiniteMeasure μ] (K : Lp (E →L[ℂ] ℂ) 2 μ) (f : E) :
    (_root_.RHTower.kernelOperator (E := E) μ K f : α → ℂ) =ᵐ[μ]
      fun x => (K : α → E →L[ℂ] ℂ) x f := by
  filter_upwards [(_root_.RHTower.evalBilinear (𝕜 := ℂ) (E := E)).coeFn_holder (r := (2 : ENNReal))
    K (Lp.const ∞ μ f), Lp.coeFn_const (p := ∞) μ f] with x hholder hconst
  rw [_root_.RHTower.kernelOperator, _root_.RHTower.kernelOperatorMap_apply, hholder, hconst]
  rfl

/-! ## The core operator and its kernel -/

/-- The finite set of translates serving the core `{z ∈ 𝒟 : Im z ≤ 2H}`. -/
def coreSet (H R : ℝ) : Finset SL(2, ℤ) := (exists_finset_near (2 * H) R).choose

theorem coreSet_spec (H R : ℝ) : ∀ z : ℍ, z ∈ fd → z.im ≤ 2 * H → ∀ z' : ℍ, z' ∈ fd →
    ∀ B : SL(2, ℤ), pairU z (B • z') ≤ R → B ∈ coreSet H R :=
  (exists_finset_near (2 * H) R).choose_spec

variable [DecidableEq ι]

variable (ρ) in
/-- The Riesz kernel of the `j`-th coordinate of the core operator:
`G_j(z, z') = χ_H(z') Σ_{B ∈ S} (φ(u(z, Bz'))/2) ρ(B)⁻¹ e_j`. -/
def coreKernel (φ : ℝ → ℝ) (H R : ℝ) (j : ι) (z z' : ℍ) : EuclideanSpace ℂ ι :=
  ((coreCutoff H z' : ℝ) : ℂ) • ∑ B ∈ coreSet H R,
    ((φ (pairU z (B • z')) / 2 : ℝ) : ℂ) • (ρ B).symm (EuclideanSpace.single j 1)

theorem continuous_coreKernel {φ : ℝ → ℝ} (hφc : Continuous φ) (H R : ℝ) (j : ι) :
    Continuous (Function.uncurry (coreKernel ρ φ H R j)) := by
  unfold coreKernel
  refine (Complex.continuous_ofReal.comp ((continuous_coreCutoff H).comp continuous_snd)).smul
    (continuous_finsetSum _ fun B _ => ?_)
  exact (Complex.continuous_ofReal.comp ((hφc.comp (continuous_pairU.comp
    (continuous_fst.prodMk ((continuous_smul_int B).comp continuous_snd)))).div_const 2)).smul
      continuous_const

theorem norm_coreKernel_le {φ : ℝ → ℝ} {M : ℝ} (hφM : ∀ u, |φ u| ≤ M) (H R : ℝ) (j : ι)
    (z z' : ℍ) : ‖coreKernel ρ φ H R j z z'‖ ≤ (coreSet H R).card * (M / 2) := by
  unfold coreKernel
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  refine (mul_le_of_le_one_left (norm_nonneg _) (abs_coreCutoff_le H z')).trans ?_
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun B _ => ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, LinearIsometryEquiv.norm_map,
    PiLp.norm_single, norm_one, mul_one, abs_div, abs_two]
  exact div_le_div_of_nonneg_right (hφM _) zero_le_two


section Core

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)

variable (ρ) in
/-- The Riesz vector `G_j(z) ∈ L²(𝒟; ℂ^ι)` of the `j`-th coordinate of the core operator. -/
def coreVec (H : ℝ) (j : ι) (z : ℍ) : RepL2 ι :=
  (memLp_of_bound_cont ((continuous_coreKernel (ρ := ρ) hφc H R j).uncurry_left z)
    (norm_coreKernel_le (ρ := ρ) hφM H R j z)).toLp (coreKernel ρ φ H R j z)

theorem continuous_coreVec (H : ℝ) (j : ι) : Continuous (coreVec ρ hφc hφM (R := R) H j) :=
  continuous_toLp_of_bound (continuous_coreKernel hφc H R j) (norm_coreKernel_le hφM H R j)

theorem coreVec_coeFn (H : ℝ) (j : ι) (z : ℍ) :
    (coreVec ρ hφc hφM (R := R) H j z : ℍ → EuclideanSpace ℂ ι) =ᵐ[cellMeasure]
      coreKernel ρ φ H R j z :=
  MemLp.coeFn_toLp _

theorem norm_coreVec_le (H : ℝ) (j : ι) (z : ℍ) :
    ‖coreVec ρ hφc hφM (R := R) H j z‖ ≤
      (measureUnivNNReal cellMeasure : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ *
        ((coreSet H R).card * (M / 2)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hφM 0)
  refine Lp.norm_le_of_ae_bound (by positivity) ?_
  filter_upwards [coreVec_coeFn hφc hφM H j z] with z' hz'
  rw [hz']
  exact norm_coreKernel_le hφM H R j z z'

variable (ρ) in
/-- The `j`-th coordinate field of the core operator: `z ↦ χ_H(z) ⟪G_j(z), ·⟫`. -/
def coreField (H : ℝ) (j : ι) (z : ℍ) : RepL2 ι →L[ℂ] ℂ :=
  ((coreCutoff H z : ℝ) : ℂ) • innerSL ℂ (coreVec ρ hφc hφM (R := R) H j z)

theorem continuous_coreField (H : ℝ) (j : ι) : Continuous (coreField ρ hφc hφM (R := R) H j) :=
  (Complex.continuous_ofReal.comp (continuous_coreCutoff H)).smul
    ((innerSL ℂ).continuous.comp (continuous_coreVec hφc hφM H j))

theorem norm_coreField_le (H : ℝ) (j : ι) (z : ℍ) :
    ‖coreField ρ hφc hφM (R := R) H j z‖ ≤
      (measureUnivNNReal cellMeasure : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ *
        ((coreSet H R).card * (M / 2)) := by
  rw [coreField, norm_smul, Complex.norm_real, Real.norm_eq_abs, innerSL_apply_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) (abs_coreCutoff_le H z)).trans
    (norm_coreVec_le hφc hφM H j z)

variable (ρ) in
/-- The coordinate field as an `L²` field of functionals. -/
def coreFieldLp (H : ℝ) (j : ι) : Lp (RepL2 ι →L[ℂ] ℂ) 2 cellMeasure :=
  (MemLp.of_bound (continuous_coreField (ρ := ρ) hφc hφM (R := R) H j).aestronglyMeasurable _
    (Eventually.of_forall (norm_coreField_le hφc hφM H j))).toLp _

theorem coreFieldLp_coeFn (H : ℝ) (j : ι) :
    (coreFieldLp ρ hφc hφM (R := R) H j : ℍ → RepL2 ι →L[ℂ] ℂ) =ᵐ[cellMeasure]
      coreField ρ hφc hφM (R := R) H j :=
  MemLp.coeFn_toLp _

end Core

/-! ## The core operator -/

section CoreOp

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M) (hR : 0 ≤ R)
  (hφR : KernelSupport φ R)

variable (ρ) in
/-- **The core operator** `χ_H L_φ χ_H`. -/
def coreOp (H : ℝ) : RepL2 ι →L[ℂ] RepL2 ι :=
  coreMul ι H ∘L ppL2 ρ hφc hφM hR hφR ∘L coreMul ι H

omit [DecidableEq ι] in
theorem coreOp_coeFn (H : ℝ) (F : RepL2 ι) :
    (coreOp ρ hφc hφM hR hφR H F : ℍ → EuclideanSpace ℂ ι) =ᵐ[cellMeasure] fun z =>
      ((coreCutoff H z : ℝ) : ℂ) •
        ppApply ρ φ (fun z' => ((coreCutoff H z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z') z := by
  have h1 := repMul_coeFn (ι := ι) (continuous_coreCutoff H).measurable (abs_coreCutoff_le H)
    (ppL2 ρ hφc hφM hR hφR (coreMul ι H F))
  have h2 := ppL2_coeFn hφc hφM hR hφR (ρ := ρ) (coreMul ι H F)
  have h3 : ppApply ρ φ (coreMul ι H F : ℍ → EuclideanSpace ℂ ι) =
      ppApply ρ φ (fun z' => ((coreCutoff H z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z') :=
    ppApply_congr_ae φ (repMul_coeFn (continuous_coreCutoff H).measurable (abs_coreCutoff_le H) F)
  filter_upwards [h1, h2] with z hz1 hz2
  change (repMul ι (continuous_coreCutoff H).measurable (abs_coreCutoff_le H)
    (ppL2 ρ hφc hφM hR hφR (coreMul ι H F)) : ℍ → EuclideanSpace ℂ ι) z = _
  rw [hz1, hz2, h3]

omit [DecidableEq ι] in
include hφR in
/-- On the core only the translates in `coreSet` act:
`(L_φ G)(z) = Σ_{B ∈ S} ∫_𝒟 (φ(u(z, Bz'))/2) ρ(B) G(z') dμ(z')`. -/
theorem ppApply_eq_coreSet_sum (H : ℝ) {z : ℍ} (hz : z ∈ fd) (hzH : z.im ≤ 2 * H)
    (G : ℍ → EuclideanSpace ℂ ι) :
    ppApply ρ φ G z = ∑ B ∈ coreSet H R,
      ∫ z' in fd, ((φ (pairU z (B • z')) / 2 : ℝ) : ℂ) • ρ B (G z') := by
  have hvan : ∀ B ∉ coreSet H R, ppTerm ρ φ G z B = 0 := by
    intro B hB
    unfold ppTerm
    refine setIntegral_eq_zero_of_forall_eq_zero fun z' hz' => ?_
    have : φ (pairU z (B • z')) = 0 := by
      by_contra hne
      exact hB (coreSet_spec H R z hz hzH z' hz' B (not_lt.1 fun hlt => hne (hφR _ hlt)))
    rw [this, Complex.ofReal_zero, zero_smul]
  unfold ppApply
  rw [tsum_eq_sum hvan, Finset.smul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  unfold ppTerm
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  simp only
  rw [smul_smul]
  congr 1
  push_cast
  ring

omit [DecidableEq ι] in
include hφc hφM in
/-- The integrand of the `B`-th core term is integrable. -/
theorem integrable_coreTerm (z : ℍ) (H : ℝ) (B : SL(2, ℤ)) (F : RepL2 ι) :
    Integrable (fun z' => ((φ (pairU z (B • z')) / 2 : ℝ) : ℂ) •
      ρ B (((coreCutoff H z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z')) cellMeasure := by
  have hcont : Continuous (fun p : ℍ × EuclideanSpace ℂ ι => ((φ (pairU z (B • p.1)) / 2 : ℝ) : ℂ) •
      ρ B (((coreCutoff H p.1 : ℝ) : ℂ) • p.2)) :=
    (Complex.continuous_ofReal.comp ((hφc.comp ((continuous_pairU_right z).comp
      ((continuous_smul_int B).comp continuous_fst))).div_const 2)).smul
      ((ρ B).continuous.comp ((Complex.continuous_ofReal.comp
        ((continuous_coreCutoff H).comp continuous_fst)).smul continuous_snd))
  have hmeas := hcont.comp_aestronglyMeasurable
    (aestronglyMeasurable_id.prodMk (Lp.aestronglyMeasurable F))
  have hint : Integrable (fun z' => M / 2 * ‖(F : ℍ → EuclideanSpace ℂ ι) z'‖) cellMeasure :=
    ((Lp.memLp F).integrable one_le_two).norm.const_mul _
  refine hint.mono' hmeas (Eventually.of_forall fun z' => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, LinearIsometryEquiv.norm_map, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
  have h1 := mul_le_of_le_one_left (norm_nonneg ((F : ℍ → EuclideanSpace ℂ ι) z'))
    (abs_coreCutoff_le H z')
  have h2 : |φ (pairU z (B • z'))| / 2 ≤ M / 2 := div_le_div_of_nonneg_right (hφM _) zero_le_two
  have hM : 0 ≤ M / 2 := le_trans (by positivity) h2
  calc |φ (pairU z (B • z'))| / 2 * (|coreCutoff H z'| * ‖(F : ℍ → EuclideanSpace ℂ ι) z'‖)
      ≤ M / 2 * ‖(F : ℍ → EuclideanSpace ℂ ι) z'‖ :=
        mul_le_mul h2 h1 (by positivity) hM


include hφR in
/-- **The coordinate field computes the core operator**: for `z ∈ 𝒟`,
`χ_H(z) ⟪G_j(z), F⟫ = ⟪e_j, χ_H(z) (L_φ(χ_H F))(z)⟫`. -/
theorem coreField_apply {H : ℝ} (hH : 0 < H) (j : ι) {z : ℍ} (hz : z ∈ fd) (F : RepL2 ι) :
    coreField ρ hφc hφM (R := R) H j z F = ⟪EuclideanSpace.single j 1, ((coreCutoff H z : ℝ) : ℂ) •
      ppApply ρ φ (fun z' => ((coreCutoff H z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z') z⟫_ℂ := by
  rw [coreField, smul_apply, innerSL_apply_apply, inner_smul_right, smul_eq_mul]
  by_cases h0 : coreCutoff H z = 0
  · rw [h0, Complex.ofReal_zero, zero_mul, zero_mul]
  congr 1
  have hzH : z.im ≤ 2 * H := (im_lt_of_coreCutoff_ne_zero hH h0).le
  rw [ppApply_eq_coreSet_sum hφR H hz hzH, inner_sum, L2.inner_def]
  calc ∫ z', ⟪(coreVec ρ hφc hφM (R := R) H j z : ℍ → EuclideanSpace ℂ ι) z',
        (F : ℍ → EuclideanSpace ℂ ι) z'⟫_ℂ ∂cellMeasure
      = ∫ z', ⟪coreKernel ρ φ H R j z z', (F : ℍ → EuclideanSpace ℂ ι) z'⟫_ℂ ∂cellMeasure := by
        refine integral_congr_ae ?_
        filter_upwards [coreVec_coeFn hφc hφM H j z] with z' hz'
        rw [hz']
    _ = ∫ z', ∑ B ∈ coreSet H R, ⟪EuclideanSpace.single j 1,
          ((φ (pairU z (B • z')) / 2 : ℝ) : ℂ) •
            ρ B (((coreCutoff H z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z')⟫_ℂ ∂cellMeasure := by
        refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
        simp only
        unfold coreKernel
        rw [inner_smul_left, sum_inner, Finset.mul_sum]
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [inner_smul_left, LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm,
          map_smul, inner_smul_right, inner_smul_right, Complex.conj_ofReal, Complex.conj_ofReal]
        ring
    _ = ∑ B ∈ coreSet H R, ∫ z', ⟪EuclideanSpace.single j 1,
          ((φ (pairU z (B • z')) / 2 : ℝ) : ℂ) •
            ρ B (((coreCutoff H z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z')⟫_ℂ ∂cellMeasure :=
        integral_finsetSum _ fun B _ =>
          (integrable_coreTerm hφc hφM z H B F).const_inner _
    _ = _ := Finset.sum_congr rfl fun B _ =>
          integral_inner (integrable_coreTerm hφc hφM z H B F) _

include hφR in
/-- **The core operator is the sum of its coordinate kernel operators.** -/
theorem coreOp_eq_sum {H : ℝ} (hH : 0 < H) :
    coreOp ρ hφc hφM hR hφR H = ∑ j : ι,
      (ContinuousLinearMap.compLpL 2 cellMeasure
        (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single j (1 : ℂ)))) ∘L
        _root_.RHTower.kernelOperator (E := RepL2 ι) cellMeasure
          (coreFieldLp ρ hφc hφM (R := R) H j) := by
  ext1 F
  rw [sum_apply]
  apply Lp.ext
  have hj : ∀ᵐ z ∂cellMeasure, ∀ j : ι,
      (((ContinuousLinearMap.compLpL 2 cellMeasure
        (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single j (1 : ℂ)))) ∘L
        _root_.RHTower.kernelOperator (E := RepL2 ι) cellMeasure
          (coreFieldLp ρ hφc hφM (R := R) H j)) F : ℍ → EuclideanSpace ℂ ι) z =
        coreField ρ hφc hφM (R := R) H j z F • EuclideanSpace.single j (1 : ℂ) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := cellMeasure)
        (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single j (1 : ℂ)))
        (_root_.RHTower.kernelOperator (E := RepL2 ι) cellMeasure
          (coreFieldLp ρ hφc hφM (R := R) H j) F),
      kernelOperator_coeFn_ae cellMeasure (coreFieldLp ρ hφc hφM (R := R) H j) F,
      coreFieldLp_coeFn hφc hφM H j] with z h1 h2 h3
    rw [ContinuousLinearMap.comp_apply, h1, ContinuousLinearMap.toSpanSingleton_apply, h2, h3]
  filter_upwards [coreOp_coeFn hφc hφM hR hφR H F, Lp.coeFn_fun_finsetSum Finset.univ
      (fun j : ι => ((ContinuousLinearMap.compLpL 2 cellMeasure
        (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single j (1 : ℂ)))) ∘L
        _root_.RHTower.kernelOperator (E := RepL2 ι) cellMeasure
          (coreFieldLp ρ hφc hφM (R := R) H j)) F), hj,
      ae_restrict_mem (μ := volume) isClosed_fd.measurableSet] with z h1 h2 h3 hz
  rw [h1, h2]
  simp_rw [h3, coreField_apply hφc hφM hφR hH _ hz F]
  have := (EuclideanSpace.basisFun ι ℂ).sum_repr' (((coreCutoff H z : ℝ) : ℂ) •
    ppApply ρ φ (fun z' => ((coreCutoff H z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z') z)
  simp only [EuclideanSpace.basisFun_apply] at this
  exact this.symm

include hφR in
/-- **The core operator `χ_H L_φ χ_H` is compact.** -/
theorem isCompactOperator_coreOp {H : ℝ} (hH : 0 < H) :
    IsCompactOperator (coreOp ρ hφc hφM hR hφR H) := by
  rw [coreOp_eq_sum hφc hφM hR hφR hH]
  refine Finset.sum_induction _ (fun T : RepL2 ι →L[ℂ] RepL2 ι => IsCompactOperator T)
    (fun A B hA hB => ?_) ?_ fun j _ => ?_
  · rw [FunLike.coe_add]
    exact hA.add hB
  · rw [FunLike.coe_zero]
    exact isCompactOperator_zero
  · rw [ContinuousLinearMap.coe_comp]
    exact (_root_.RHTower.isCompactOperator_kernelOperator cellMeasure _).clm_comp _

end CoreOp

end

end GaloisForLFunctions.RHTower.RepPointPair
