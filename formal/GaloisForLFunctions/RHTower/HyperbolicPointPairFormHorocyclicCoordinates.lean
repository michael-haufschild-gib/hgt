import GaloisForLFunctions.RHTower.HyperbolicAbelTransformHorocyclicSlice

/-!
# The quadratic form of a point-pair kernel in horocyclic coordinates

For a continuous profile `k` vanishing on `(R, ∞)` and a continuous compactly supported test
`g : ℍ → ℂ` the quadratic form of the point-pair kernel is

`Q_k(g) = ∫_ℍ ∫_ℍ k(u(z, w)) g(z) ḡ(w) dμ(z) dμ(w)`   (`pointPairForm`).

In the chart `z = x + iy`, `w = x' + iy'` (`pointPairForm_eq_iterated`):

`Q_k(g) = ∫_y ∫_{y'} ∫_x ∫_{x'} y⁻² y'⁻² k(((x − x')² + (y − y')²)/(4yy')) G(x, y) Ḡ(x', y')`,

with `G` the extension of `g` by zero to `ℂ` (`zeroExtendC`), which is continuous with compact
support in the open upper half-plane.  The integrand is bounded and supported in a compact box, so
the four integrations commute.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate MatrixGroups

noncomputable section

namespace GaloisForLFunctions.RHTower.MehlerFock

open DeckPointPair

/-- The quadratic form `Q_k(g) = ∫∫ k(u(z, w)) g(z) ḡ(w) dμ(z) dμ(w)`. -/
def pointPairForm (k : ℝ → ℝ) (g : ℍ → ℂ) : ℂ :=
  ∫ z, ∫ w, ((k (pairU z w) : ℝ) : ℂ) * g z * conj (g w)

/-! ### Extension by zero -/

theorem continuousOn_ofComplex_of_im_pos : ContinuousOn ofComplex {z : ℂ | 0 < z.im} := by
  have hs : ofComplex.source = {z : ℂ | 0 < z.im} := by
    change (isOpenEmbedding_coe.toOpenPartialHomeomorph UpperHalfPlane.coe).target = _
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, range_coe]
  exact hs ▸ ofComplex.continuousOn

/-- `g` extended by zero from `ℍ` to `ℂ`. -/
def zeroExtendC (g : ℍ → ℂ) (w : ℂ) : ℂ := if 0 < w.im then g (ofComplex w) else 0

theorem zeroExtendC_apply (g : ℍ → ℂ) (z : ℍ) : zeroExtendC g z = g z := by
  simp only [zeroExtendC, coe_im, z.im_pos, if_true, ofComplex_apply]

theorem zeroExtendC_of_im_pos (g : ℍ → ℂ) {w : ℂ} (hw : 0 < w.im) :
    zeroExtendC g w = g (ofComplex w) := if_pos hw

theorem zeroExtendC_of_im_nonpos (g : ℍ → ℂ) {w : ℂ} (hw : w.im ≤ 0) : zeroExtendC g w = 0 :=
  if_neg (not_lt.mpr hw)

theorem tsupport_zeroExtendC_subset {g : ℍ → ℂ} (hgc : HasCompactSupport g) :
    tsupport (zeroExtendC g) ⊆ UpperHalfPlane.coe '' tsupport g := by
  apply closure_minimal _ (hgc.image continuous_coe).isClosed
  intro z hz
  by_cases hy : 0 < z.im
  · refine ⟨ofComplex z, subset_tsupport g ?_, ?_⟩
    · simpa only [Function.mem_support, zeroExtendC, if_pos hy] using hz
    · rw [ofComplex_apply_of_im_pos hy]
  · exact (hz (by simp only [zeroExtendC, if_neg hy])).elim

theorem hasCompactSupport_zeroExtendC {g : ℍ → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (zeroExtendC g) :=
  (hgc.image continuous_coe).of_isClosed_subset isClosed_closure (tsupport_zeroExtendC_subset hgc)

theorem continuous_zeroExtendC {g : ℍ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (zeroExtendC g) := by
  have h : ContinuousOn (zeroExtendC g) {z : ℂ | 0 < z.im} :=
    (hg.comp_continuousOn continuousOn_ofComplex_of_im_pos).congr fun z hz => zeroExtendC_of_im_pos g hz
  refine h.continuous_of_tsupport_subset isOpen_upperHalfPlaneSet fun z hz => ?_
  obtain ⟨w, _, rfl⟩ := tsupport_zeroExtendC_subset hgc hz
  exact w.im_pos

/-- The support of a compactly supported test lies in a box `[-X, X] × [a, b]`, `a > 0`. -/
theorem exists_support_box_zeroExtendC {g : ℍ → ℂ} (hgc : HasCompactSupport g) :
    ∃ a b X : ℝ, 0 < a ∧ 0 ≤ X ∧
      ∀ w : ℂ, zeroExtendC g w ≠ 0 → a ≤ w.im ∧ w.im ≤ b ∧ |w.re| ≤ X := by
  set K := UpperHalfPlane.coe '' tsupport g
  have hK : IsCompact K := hgc.image continuous_coe
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, 0, 0, one_pos, le_rfl, fun w hw => ?_⟩
    have hwK : w ∈ K := tsupport_zeroExtendC_subset hgc (subset_tsupport _ hw)
    rw [hKe] at hwK; exact hwK.elim
  obtain ⟨p, hpK, hp⟩ := hK.exists_isMinOn hKne Complex.continuous_im.continuousOn
  obtain ⟨q, hqK, hq⟩ := hK.exists_isMaxOn hKne Complex.continuous_im.continuousOn
  obtain ⟨r, hrK, hr⟩ := hK.exists_isMaxOn hKne (continuous_abs.comp Complex.continuous_re).continuousOn
  have hp0 : 0 < p.im := by obtain ⟨w, _, rfl⟩ := hpK; exact w.im_pos
  refine ⟨p.im, q.im, |r.re|, hp0, abs_nonneg _, fun w hw => ?_⟩
  have hwK := tsupport_zeroExtendC_subset hgc (subset_tsupport _ hw)
  exact ⟨isMinOn_iff.mp hp _ hwK, isMaxOn_iff.mp hq _ hwK, isMaxOn_iff.mp hr _ hwK⟩

theorem exists_norm_le_of_compactSupport {g : ℍ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖g z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  exact ⟨max C 0, le_max_right _ _, fun z => (hC z).trans (le_max_left _ _)⟩

/-! ### The form in coordinates -/

/-- `u(x + iy, x' + iy')` in coordinates. -/
def pairUCoord (x y x' y' : ℝ) : ℝ := ((x - x') ^ 2 + (y - y') ^ 2) / (4 * y * y')

/-- The coordinate integrand `y⁻² y'⁻² k(u) G(x, y) Ḡ(x', y')`. -/
def formIntegrand (k : ℝ → ℝ) (g : ℍ → ℂ) (y y' x x' : ℝ) : ℂ :=
  (((y ^ 2)⁻¹ * (y' ^ 2)⁻¹ * k (pairUCoord x y x' y') : ℝ) : ℂ) * zeroExtendC g ⟨x, y⟩ *
    conj (zeroExtendC g ⟨x', y'⟩)

theorem integral_pairU_centre {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (z : ℍ) : ∫ w, f (pairU z w) = ∫ w, f (pairU UpperHalfPlane.I w) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) UpperHalfPlane.I z
  subst hg
  have hmp := measurePreserving_smul ((g : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have e : ∀ w : ℍ, ((g : GL (Fin 2) ℝ)) • w = g • w := fun w => rfl
  rw [← hmp.integral_comp (measurableEmbedding_const_smul _)]
  simp only [e, pairU_smul]

section Form

variable {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : KernelSupport k R)
  {g : ℍ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
include hkc hkR hg hgc

omit hgc in
/-- The integrand of the inner integral `H(z) = ∫ k(u(z, w)) ḡ(w) dμ(w)`. -/
theorem integrable_pairKernel_conj (z : ℍ) :
    Integrable fun w => ((k (pairU z w) : ℝ) : ℂ) * conj (g w) :=
  (integrable_pairKernel_smul' hkc hkR (continuous_conj.comp hg) z).congr
    (Eventually.of_forall fun w => by simp [Complex.real_smul])

theorem integrable_mul_innerIntegral :
    Integrable fun z => g z * ∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (g w) := by
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_le_of_compactSupport hg hgc
  set Ck := ∫ w, |k (pairU UpperHalfPlane.I w)|
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  refine hgi.mul_bdd (c := Cg * Ck) ?_ (Eventually.of_forall fun z => ?_)
  · have hF : StronglyMeasurable fun p : ℍ × ℍ =>
        ((k (pairU p.1 p.2) : ℝ) : ℂ) * conj (g p.2) :=
      ((continuous_ofReal.comp (hkc.comp continuous_pairU)).mul
        (continuous_conj.comp (hg.comp continuous_snd))).stronglyMeasurable
    exact hF.integral_prod_right'.aestronglyMeasurable
  · calc ‖∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (g w)‖
        ≤ ∫ w, ‖((k (pairU z w) : ℝ) : ℂ) * conj (g w)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ w, Cg * |k (pairU z w)| := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            ((integrable_pairKernel_smul' hkc hkR continuous_const z (G := fun _ => (1 : ℝ))).norm
              |>.const_mul Cg |>.congr (Eventually.of_forall fun w => by simp))
            (Eventually.of_forall fun w => ?_)
          dsimp only
          rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right (hCg w) (abs_nonneg _)
      _ = Cg * Ck := by rw [integral_const_mul, integral_pairU_centre (fun u => |k u|) z]

/-- **The form as an iterated integral in the chart.** -/
theorem pointPairForm_eq_iterated_yx :
    pointPairForm k g = ∫ y, ∫ x, ∫ y', ∫ x', formIntegrand k g y y' x x' := by
  have hA : ∀ z, ∫ w, ((k (pairU z w) : ℝ) : ℂ) * g z * conj (g w) =
      g z * ∫ w, ((k (pairU z w) : ℝ) : ℂ) * conj (g w) := fun z => by
    rw [← integral_const_mul]; congr 1 with w; ring
  rw [pointPairForm, integral_congr_ae (Eventually.of_forall hA),
    integral_upperHalfPlane_eq_iterated _ (integrable_mul_innerIntegral hkc hkR hg hgc)]
  -- the outer integral vanishes off `y > 0`
  have hzero : ∀ y : ℝ, y ∉ Ioi (0 : ℝ) → ∫ x, ∫ y', ∫ x', formIntegrand k g y y' x x' = 0 := by
    intro y hy
    have hy' : (⟨0, y⟩ : ℂ).im ≤ 0 := not_lt.mp hy
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y' => ?_)
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x' => ?_)
    simp only [formIntegrand, zeroExtendC_of_im_nonpos g (show (⟨x, y⟩ : ℂ).im ≤ 0 from hy'),
      mul_zero, zero_mul, Pi.zero_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  rw [← integral_smul]
  congr 1 with x
  have hzero' : ∀ y' : ℝ, y' ∉ Ioi (0 : ℝ) → ∫ x', formIntegrand k g y y' x x' = 0 := by
    intro y' hy'
    have hy'0 : (⟨0, y'⟩ : ℂ).im ≤ 0 := not_lt.mp hy'
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x' => ?_)
    simp only [formIntegrand, zeroExtendC_of_im_nonpos g (show (⟨x', y'⟩ : ℂ).im ≤ 0 from hy'0),
      map_zero, mul_zero, Pi.zero_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero',
    integral_upperHalfPlane_eq_iterated _ (integrable_pairKernel_conj hkc hkR hg (ofComplex ⟨x, y⟩))]
  have hG : zeroExtendC g ⟨x, y⟩ = g (ofComplex ⟨x, y⟩) := zeroExtendC_of_im_pos g hy0
  have hinner : ∀ y' ∈ Ioi (0 : ℝ), ∫ x', formIntegrand k g y y' x x' =
      ((((y ^ 2)⁻¹ : ℝ) : ℂ) * g (ofComplex ⟨x, y⟩)) * ((y' ^ 2)⁻¹ • ∫ x',
        ((k (pairU (ofComplex ⟨x, y⟩) (ofComplex ⟨x', y'⟩)) : ℝ) : ℂ) *
          conj (g (ofComplex ⟨x', y'⟩))) := by
    intro y' hy'
    have hy'0 : (0 : ℝ) < y' := hy'
    rw [Complex.real_smul, ← mul_assoc, ← integral_const_mul]
    congr 1 with x'
    rw [formIntegrand, hG, zeroExtendC_of_im_pos g (show (0 : ℝ) < (⟨x', y'⟩ : ℂ).im from hy'0),
      pairU_ofComplex_eq hy0 hy'0, pairUCoord]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul, Complex.real_smul]
  ring

/-! ### Bounds and the order of integration -/

omit hkc hkR hg hgc in
theorem continuous_complex_mk : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) :=
  Complex.equivRealProdCLM.symm.continuous

omit hkc hkR hg hgc in
theorem norm_zeroExtendC_le {C : ℝ} (hC : 0 ≤ C) (hgC : ∀ z, ‖g z‖ ≤ C) (w : ℂ) :
    ‖zeroExtendC g w‖ ≤ C := by
  by_cases hw : 0 < w.im
  · rw [zeroExtendC_of_im_pos g hw]; exact hgC _
  · rw [zeroExtendC_of_im_nonpos g (not_lt.mp hw), norm_zero]; exact hC

omit hkc hkR hg hgc in
/-- The box indicator `1_{[a,b]}(y) 1_{[-X,X]}(x)`. -/
def boxIndicator (a b X y x : ℝ) : ℝ :=
  (Icc a b).indicator (fun _ => (1 : ℝ)) y * (Icc (-X) X).indicator (fun _ => (1 : ℝ)) x

omit hkc hkR hg hgc in
theorem boxIndicator_nonneg (a b X y x : ℝ) : 0 ≤ boxIndicator a b X y x :=
  mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) y)
    (indicator_nonneg (fun _ _ => zero_le_one) x)

omit hkc hkR hg hgc in
theorem boxIndicator_eq_one {a b X y x : ℝ} (hy : a ≤ y ∧ y ≤ b) (hx : |x| ≤ X) :
    boxIndicator a b X y x = 1 := by
  rw [boxIndicator, indicator_of_mem (show y ∈ Icc a b from hy),
    indicator_of_mem (show x ∈ Icc (-X) X from abs_le.mp hx), mul_one]

omit hkc hkR hg hgc in
/-- **Bound.**  With the box `[a, b] × [-X, X]` of the support, `|k| ≤ M` on `[0, ∞)` and
`|g| ≤ C`: `|F(y, y', x, x')| ≤ a⁻⁴ M C² 1_box(y, x) 1_box(y', x')`. -/
theorem norm_formIntegrand_le {a b X M C : ℝ} (ha : 0 < a) (hM : ∀ u, 0 ≤ u → |k u| ≤ M)
    (hC : 0 ≤ C) (hgC : ∀ z, ‖g z‖ ≤ C)
    (hbox : ∀ w : ℂ, zeroExtendC g w ≠ 0 → a ≤ w.im ∧ w.im ≤ b ∧ |w.re| ≤ X) (y y' x x' : ℝ) :
    ‖formIntegrand k g y y' x x'‖ ≤
      (a ^ 2)⁻¹ * (a ^ 2)⁻¹ * M * C * C * (boxIndicator a b X y x * boxIndicator a b X y' x') := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 le_rfl)
  by_cases h1 : zeroExtendC g ⟨x, y⟩ = 0
  · rw [formIntegrand, h1, mul_zero, zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (boxIndicator_nonneg _ _ _ _ _)
      (boxIndicator_nonneg _ _ _ _ _))
  by_cases h2 : zeroExtendC g ⟨x', y'⟩ = 0
  · rw [formIntegrand, h2, map_zero, mul_zero, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (boxIndicator_nonneg _ _ _ _ _)
      (boxIndicator_nonneg _ _ _ _ _))
  obtain ⟨hy1, hy2, hx⟩ := hbox _ h1
  obtain ⟨hy1', hy2', hx'⟩ := hbox _ h2
  simp only at hy1 hy2 hx hy1' hy2' hx'
  rw [boxIndicator_eq_one ⟨hy1, hy2⟩ hx, boxIndicator_eq_one ⟨hy1', hy2'⟩ hx', mul_one, mul_one]
  have hy0 : 0 < y := lt_of_lt_of_le ha hy1
  have hy0' : 0 < y' := lt_of_lt_of_le ha hy1'
  have hinv : (y ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hy1 2)
  have hinv' : (y' ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hy1' 2)
  have hk : |k (pairUCoord x y x' y')| ≤ M := hM _ (by unfold pairUCoord; positivity)
  rw [formIntegrand, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2)⁻¹),
    abs_of_pos (by positivity : (0 : ℝ) < (y' ^ 2)⁻¹)]
  have hG := norm_zeroExtendC_le hC hgC (⟨x, y⟩ : ℂ)
  have hG' := norm_zeroExtendC_le hC hgC (⟨x', y'⟩ : ℂ)
  calc (y ^ 2)⁻¹ * (y' ^ 2)⁻¹ * |k (pairUCoord x y x' y')| * ‖zeroExtendC g ⟨x, y⟩‖ *
        ‖zeroExtendC g ⟨x', y'⟩‖ ≤ (a ^ 2)⁻¹ * (a ^ 2)⁻¹ * M * C * C := by
        gcongr
    _ = _ := rfl

omit hkR in
theorem measurable_formIntegrand_swap (y : ℝ) :
    Measurable fun q : (ℝ × ℝ) × ℝ => formIntegrand k g y q.1.2 q.1.1 q.2 := by
  have hk : Measurable k := hkc.measurable
  have hz : Measurable (zeroExtendC g) := (continuous_zeroExtendC hg hgc).measurable
  have hm : Measurable fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) := continuous_complex_mk.measurable
  have h1 : Measurable fun q : (ℝ × ℝ) × ℝ => zeroExtendC g ⟨q.1.1, y⟩ :=
    hz.comp (hm.comp (measurable_fst.fst.prodMk measurable_const))
  have h2 : Measurable fun q : (ℝ × ℝ) × ℝ => conj (zeroExtendC g ⟨q.2, q.1.2⟩) :=
    (Complex.continuous_conj.measurable).comp (hz.comp (hm.comp (measurable_snd.prodMk
      measurable_fst.snd)))
  have h3 : Measurable fun q : (ℝ × ℝ) × ℝ =>
      ((y ^ 2)⁻¹ * (q.1.2 ^ 2)⁻¹ * k (pairUCoord q.1.1 y q.2 q.1.2) : ℝ) := by
    unfold pairUCoord
    exact (measurable_const.mul (measurable_fst.snd.pow_const 2).inv).mul
      (hk.comp (by fun_prop))
  exact ((Complex.measurable_ofReal.comp h3).mul h1).mul h2

/-- **Reordering.**  `Q_k(g) = ∫_y ∫_{y'} ∫_x ∫_{x'} F`. -/
theorem pointPairForm_eq_iterated :
    pointPairForm k g = ∫ y, ∫ y', ∫ x, ∫ x', formIntegrand k g y y' x x' := by
  rw [pointPairForm_eq_iterated_yx hkc hkR hg hgc]
  congr 1 with y
  obtain ⟨a, b, X, ha, hX, hbox⟩ := exists_support_box_zeroExtendC hgc
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_kernelSupport hkc hkR
  obtain ⟨C, hC, hgC⟩ := exists_norm_le_of_compactSupport hg hgc
  set B := (a ^ 2)⁻¹ * (a ^ 2)⁻¹ * M * C * C with hB
  have hB0 : 0 ≤ B := by positivity
  have hint1 : Integrable ((Icc (-X) X).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp) (by simp))
  have hint2 : Integrable ((Icc a b).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp) (by simp))
  have hvol : ∫ x', (Icc (-X) X).indicator (fun _ => (1 : ℝ)) x' = 2 * X := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
      Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  refine integral_integral_swap ?_
  refine ((hint1.mul_prod hint2).const_mul (B * (2 * X))).mono'
    ((measurable_formIntegrand_swap hkc hg hgc y).stronglyMeasurable.integral_prod_right'
      |>.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
  show ‖∫ x', formIntegrand k g y p.2 p.1 x'‖ ≤ _
  have hbx : boxIndicator a b X y p.1 ≤ (Icc (-X) X).indicator (fun _ => (1 : ℝ)) p.1 := by
    rw [boxIndicator]
    refine mul_le_of_le_one_left (indicator_nonneg (fun _ _ => zero_le_one) _) ?_
    by_cases hy : y ∈ Icc a b <;> simp [hy]
  calc ‖∫ x', formIntegrand k g y p.2 p.1 x'‖
      ≤ ∫ x', ‖formIntegrand k g y p.2 p.1 x'‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x', B * (boxIndicator a b X y p.1 * boxIndicator a b X p.2 x') := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ?_
          (Eventually.of_forall fun x' => norm_formIntegrand_le ha hM hC hgC hbox y p.2 p.1 x')
        exact (hint1.const_mul (B * boxIndicator a b X y p.1 *
          (Icc a b).indicator (fun _ => (1 : ℝ)) p.2)).congr
          (Eventually.of_forall fun x' => by simp only [boxIndicator]; ring)
    _ = B * boxIndicator a b X y p.1 * (Icc a b).indicator (fun _ => (1 : ℝ)) p.2 * (2 * X) := by
        rw [← hvol, ← integral_const_mul]
        congr 1 with x'
        simp only [boxIndicator]; ring
    _ ≤ B * (2 * X) * ((Icc (-X) X).indicator (fun _ => (1 : ℝ)) p.1 *
          (Icc a b).indicator (fun _ => (1 : ℝ)) p.2) := by
        have h2 : 0 ≤ (Icc a b).indicator (fun _ => (1 : ℝ)) p.2 :=
          indicator_nonneg (fun _ _ => zero_le_one) _
        calc B * boxIndicator a b X y p.1 * (Icc a b).indicator (fun _ => (1 : ℝ)) p.2 * (2 * X)
            = B * (2 * X) * (boxIndicator a b X y p.1 *
                (Icc a b).indicator (fun _ => (1 : ℝ)) p.2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbx h2) (by positivity)

end Form

end GaloisForLFunctions.RHTower.MehlerFock
