import GaloisForLFunctions.HTGeometry.CompactKernelL2Representation
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Density of rank-one kernels in the `L¹(ℝ, C₀(ℝ))` norm

Every continuous compactly supported kernel is an `L¹(ℝ, C₀(ℝ))`-limit of finite sums of rank-one
kernels `φ(x) conj ψ(y)`, `φ, ψ ∈ C_c(ℝ)`:

* on a box `[-M, M]²` containing the support, Stone–Weierstrass (the span of the product functions
  `a(x) b(y)` is a point-separating star subalgebra) approximates the restriction uniformly;
* the tent cutoff `χ_M(x) χ_M(y) f(clamp(x, y))` turns a continuous function on the box into a
  kernel supported in the box, linearly, with the same sup bound, and turns product functions into
  rank-one kernels;
* a kernel bounded by `δ` and supported in `[-M, M]²` has `‖k‖₁ ≤ 4 M δ`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped CompactlySupported Pointwise

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The tent cutoff -/

/-- The tent `x ↦ clamp(M - |x|, 0, 1)`: equal to `1` on `[-(M-1), M-1]` and `0` off `(-M, M)`. -/
def tentReal (M x : ℝ) : ℝ := max 0 (min 1 (M - |x|))

theorem continuous_tentReal (M : ℝ) : Continuous (tentReal M) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

theorem tentReal_nonneg (M x : ℝ) : 0 ≤ tentReal M x := le_max_left _ _

theorem tentReal_le_one (M x : ℝ) : tentReal M x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem tentReal_eq_zero {M x : ℝ} (hx : M ≤ |x|) : tentReal M x = 0 := by
  unfold tentReal
  rw [max_eq_left]
  exact (min_le_right _ _).trans (by linarith)

theorem tentReal_eq_one {M x : ℝ} (hx : |x| ≤ M - 1) : tentReal M x = 1 := by
  unfold tentReal
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem abs_lt_of_tentReal_ne_zero {M x : ℝ} (h : tentReal M x ≠ 0) : |x| < M := by
  by_contra hx
  exact h (tentReal_eq_zero (not_lt.mp hx))

/-- The tent cutoff as a compactly supported continuous function `ℝ → ℂ`. -/
def tentCc (M : ℝ) : C_c(ℝ, ℂ) where
  toFun x := (tentReal M x : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp (continuous_tentReal M)
  hasCompactSupport' := HasCompactSupport.intro (isCompact_Icc (a := -M) (b := M)) fun x hx => by
    have : M ≤ |x| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · exact (by linarith : M ≤ -x).trans (neg_le_abs x)
      · exact h.le.trans (le_abs_self x)
    simp [tentReal_eq_zero this]

/-- `χ_M · a` for a continuous `a`. -/
def tentMul (M : ℝ) (a : C(ℝ, ℂ)) : C_c(ℝ, ℂ) where
  toFun x := (tentReal M x : ℂ) * a x
  continuous_toFun := (Complex.continuous_ofReal.comp (continuous_tentReal M)).mul a.continuous
  hasCompactSupport' := (tentCc M).hasCompactSupport.mul_right

theorem tentMul_apply (M : ℝ) (a : C(ℝ, ℂ)) (x : ℝ) :
    tentMul M a x = (tentReal M x : ℂ) * a x := rfl

/-! ## The box and the cutoff extension -/

/-- The square box `[-M, M]²`. -/
def squareBox (M : ℝ) : Set (ℝ × ℝ) := Icc (-M) M ×ˢ Icc (-M) M

instance (M : ℝ) : CompactSpace (squareBox M) :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)

/-- The coordinatewise clamp `ℝ² → [-M, M]²` (for `0 ≤ M`). -/
def squareBoxClamp {M : ℝ} (hM : 0 ≤ M) (p : ℝ × ℝ) : squareBox M :=
  ⟨((projIcc (-M) M (by linarith) p.1 : ℝ), (projIcc (-M) M (by linarith) p.2 : ℝ)),
    ⟨(projIcc (-M) M (by linarith) p.1).2, (projIcc (-M) M (by linarith) p.2).2⟩⟩

theorem continuous_squareBoxClamp {M : ℝ} (hM : 0 ≤ M) : Continuous (squareBoxClamp hM) :=
  Continuous.subtype_mk ((continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))) _

theorem squareBoxClamp_of_abs_le {M : ℝ} (hM : 0 ≤ M) {x y : ℝ} (hx : |x| ≤ M) (hy : |y| ≤ M) :
    ((squareBoxClamp hM (x, y) : squareBox M) : ℝ × ℝ) = (x, y) := by
  have hx' : x ∈ Icc (-M) M := abs_le.mp hx
  have hy' : y ∈ Icc (-M) M := abs_le.mp hy
  simp [squareBoxClamp, projIcc_of_mem _ hx', projIcc_of_mem _ hy']

/-- The cutoff extension `f ↦ χ_M(x) χ_M(y) f(clamp(x, y))` of a continuous function on the box to
a compactly supported kernel. -/
def boxExtend {M : ℝ} (hM : 0 ≤ M) (f : C(squareBox M, ℂ)) : KernelAlg :=
  (show C_c(ℝ × ℝ, ℂ) from
  { toFun := fun p => (tentReal M p.1 : ℂ) * (tentReal M p.2 : ℂ) * f (squareBoxClamp hM p)
    continuous_toFun :=
      (((Complex.continuous_ofReal.comp ((continuous_tentReal M).comp continuous_fst)).mul
        (Complex.continuous_ofReal.comp ((continuous_tentReal M).comp continuous_snd))).mul
        (f.continuous.comp (continuous_squareBoxClamp hM)))
    hasCompactSupport' := HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (-M) M ×ˢ Icc (-M) M)) fun p hp => by
        simp only [mem_prod, not_and_or] at hp
        have key : ∀ x : ℝ, x ∉ Icc (-M) M → tentReal M x = 0 := fun x hx => by
          refine tentReal_eq_zero ?_
          rw [mem_Icc, not_and_or, not_le, not_le] at hx
          rcases hx with h | h
          · exact (by linarith : M ≤ -x).trans (neg_le_abs x)
          · exact h.le.trans (le_abs_self x)
        rcases hp with h | h
        · simp [key _ h]
        · simp [key _ h] })

theorem boxExtend_apply {M : ℝ} (hM : 0 ≤ M) (f : C(squareBox M, ℂ)) (x y : ℝ) :
    (boxExtend hM f).toFun (x, y) =
      (tentReal M x : ℂ) * (tentReal M y : ℂ) * f (squareBoxClamp hM (x, y)) := rfl

/-- The cutoff extension is linear. -/
def boxExtendₗ {M : ℝ} (hM : 0 ≤ M) : C(squareBox M, ℂ) →ₗ[ℂ] KernelAlg where
  toFun := boxExtend hM
  map_add' f g := KernelAlg.ext fun ⟨x, y⟩ => by
    simp only [boxExtend_apply, KernelAlg.add_apply, ContinuousMap.add_apply]
    ring
  map_smul' c f := KernelAlg.ext fun ⟨x, y⟩ => by
    simp only [boxExtend_apply, KernelAlg.smul_apply, ContinuousMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem norm_boxExtend_le {M : ℝ} (hM : 0 ≤ M) (f : C(squareBox M, ℂ)) (p : ℝ × ℝ) :
    ‖(boxExtend hM f).toFun p‖ ≤ ‖f‖ := by
  obtain ⟨x, y⟩ := p
  rw [boxExtend_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (tentReal_nonneg M x), Real.norm_of_nonneg (tentReal_nonneg M y)]
  have h1 := tentReal_le_one M x
  have h2 := tentReal_le_one M y
  have h3 := f.norm_coe_le_norm (squareBoxClamp hM (x, y))
  have h4 := tentReal_nonneg M x
  have h5 := tentReal_nonneg M y
  calc tentReal M x * tentReal M y * ‖f (squareBoxClamp hM (x, y))‖ ≤ 1 * 1 * ‖f‖ := by gcongr
    _ = ‖f‖ := by ring

theorem boxExtend_eq_zero {M : ℝ} (hM : 0 ≤ M) (f : C(squareBox M, ℂ)) {x y : ℝ}
    (h : M < |x| ∨ M < |y|) : (boxExtend hM f).toFun (x, y) = 0 := by
  rw [boxExtend_apply]
  rcases h with h | h
  · simp [tentReal_eq_zero h.le]
  · simp [tentReal_eq_zero h.le]

/-! ## The `L¹(ℝ, C₀(ℝ))` norm of a box-supported kernel -/

/-- A kernel bounded by `δ` and supported in `[-M, M]²` has `‖k‖₁ ≤ 4 M δ`. -/
theorem KernelAlg.l1Norm_le_of_box (k : KernelAlg) {M δ : ℝ} (hM : 0 ≤ M) (hδ0 : 0 ≤ δ)
    (hδ : ∀ p, ‖k.toFun p‖ ≤ δ) (hsupp : ∀ x y, (M < |x| ∨ M < |y|) → k.toFun (x, y) = 0) :
    k.l1Norm ≤ 4 * M * δ := by
  have hfib : ∀ s, k.fibreNorm s ≤ (Icc (-(2 * M)) (2 * M)).indicator (fun _ => δ) s := by
    intro s
    by_cases hs : s ∈ Icc (-(2 * M)) (2 * M)
    · rw [indicator_of_mem hs]
      exact (BoundedContinuousFunction.norm_le hδ0).mpr fun x => hδ _
    · rw [indicator_of_notMem hs]
      have hzero : k.fibre s = 0 := by
        ext x
        rw [KernelAlg.fibre_apply]
        refine hsupp x (x - s) ?_
        by_contra h
        push Not at h
        apply hs
        have h1 := abs_le.mp h.1
        have h2 := abs_le.mp h.2
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      rw [KernelAlg.fibreNorm, hzero]
      have h0 : (0 : C_c(ℝ, ℂ)).toBoundedContinuousFunction = 0 :=
        BoundedContinuousFunction.ext fun _ => rfl
      rw [h0, norm_zero]
  have hint : Integrable ((Icc (-(2 * M)) (2 * M)).indicator (fun _ : ℝ => δ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  calc k.l1Norm ≤ ∫ s, (Icc (-(2 * M)) (2 * M)).indicator (fun _ => δ) s :=
        integral_mono k.integrable_fibreNorm hint hfib
    _ = 4 * M * δ := by
        rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
          smul_eq_mul, ENNReal.toReal_ofReal (by linarith)]
        ring

/-! ## Product functions on the box and Stone–Weierstrass -/

/-- The product function `(x, y) ↦ a(x) b(y)` on the box. -/
def prodFn (M : ℝ) (a b : C(ℝ, ℂ)) : C(squareBox M, ℂ) :=
  ⟨fun q => a (q : ℝ × ℝ).1 * b (q : ℝ × ℝ).2,
    (a.continuous.comp (continuous_fst.comp continuous_subtype_val)).mul
      (b.continuous.comp (continuous_snd.comp continuous_subtype_val))⟩

theorem prodFn_apply (M : ℝ) (a b : C(ℝ, ℂ)) (q : squareBox M) :
    prodFn M a b q = a (q : ℝ × ℝ).1 * b (q : ℝ × ℝ).2 := rfl

/-- The product functions. -/
def prodFns (M : ℝ) : Set C(squareBox M, ℂ) := Set.range fun ab : C(ℝ, ℂ) × C(ℝ, ℂ) => prodFn M ab.1 ab.2

theorem prodFns_mul_subset (M : ℝ) : prodFns M * prodFns M ⊆ prodFns M := by
  rintro _ ⟨_, ⟨⟨a, b⟩, rfl⟩, _, ⟨⟨a', b'⟩, rfl⟩, rfl⟩
  refine ⟨⟨a * a', b * b'⟩, ?_⟩
  ext q
  simp only [prodFn_apply, ContinuousMap.mul_apply]
  ring

/-- The span of the product functions, a star subalgebra. -/
def prodSpan (M : ℝ) : StarSubalgebra ℂ C(squareBox M, ℂ) where
  carrier := Submodule.span ℂ (prodFns M)
  mul_mem' {f g} hf hg := by
    have h := Submodule.mul_mem_mul hf hg
    rw [Submodule.span_mul_span] at h
    exact Submodule.span_mono (prodFns_mul_subset M) h
  one_mem' := Submodule.subset_span ⟨⟨1, 1⟩, by ext q; simp [prodFn_apply]⟩
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' c := by
    have h1 : (1 : C(squareBox M, ℂ)) ∈ Submodule.span ℂ (prodFns M) :=
      Submodule.subset_span ⟨⟨1, 1⟩, by ext q; simp [prodFn_apply]⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c h1
  star_mem' {f} hf := by
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hg
      refine Submodule.subset_span ⟨⟨star a, star b⟩, ?_⟩
      ext q
      simp [prodFn_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

theorem prodFn_mem_prodSpan (M : ℝ) (a b : C(ℝ, ℂ)) : prodFn M a b ∈ prodSpan M :=
  Submodule.subset_span ⟨⟨a, b⟩, rfl⟩

theorem prodSpan_separatesPoints (M : ℝ) : (prodSpan M).toSubalgebra.SeparatesPoints := by
  intro q q' hqq'
  have hne : (q : ℝ × ℝ) ≠ q' := fun h => hqq' (Subtype.ext h)
  by_cases h1 : (q : ℝ × ℝ).1 = (q' : ℝ × ℝ).1
  · have h2 : (q : ℝ × ℝ).2 ≠ (q' : ℝ × ℝ).2 := fun h2 => hne (Prod.ext h1 h2)
    refine ⟨_, ⟨prodFn M 1 ⟨Complex.ofReal, Complex.continuous_ofReal⟩,
      prodFn_mem_prodSpan M _ _, rfl⟩, ?_⟩
    simp only [prodFn_apply, ContinuousMap.one_apply, ContinuousMap.coe_mk, one_mul]
    exact_mod_cast h2
  · refine ⟨_, ⟨prodFn M ⟨Complex.ofReal, Complex.continuous_ofReal⟩ 1,
      prodFn_mem_prodSpan M _ _, rfl⟩, ?_⟩
    simp only [prodFn_apply, ContinuousMap.one_apply, ContinuousMap.coe_mk, mul_one]
    exact_mod_cast h1

/-- **Stone–Weierstrass**: sums of products `a(x) b(y)` are uniformly dense on the box. -/
theorem exists_prodSpan_dist_lt (M : ℝ) (f : C(squareBox M, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ prodSpan M, dist f p < ε := by
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (prodSpan M) (prodSpan_separatesPoints M)
  have hf : f ∈ (prodSpan M).topologicalClosure := by rw [htop]; trivial
  exact Metric.mem_closure_iff.mp hf ε hε

/-! ## Extension of product functions is rank one -/

theorem boxExtend_prodFn {M : ℝ} (hM : 0 ≤ M) (a b : C(ℝ, ℂ)) :
    boxExtend hM (prodFn M a b) = KernelAlg.rankOneKernel (tentMul M a) (tentMul M (star b)) := by
  refine KernelAlg.ext fun ⟨x, y⟩ => ?_
  rw [boxExtend_apply, KernelAlg.rankOneKernel_apply, tentMul_apply, tentMul_apply,
    prodFn_apply]
  by_cases hx : tentReal M x = 0
  · simp [hx]
  by_cases hy : tentReal M y = 0
  · simp [hy]
  rw [squareBoxClamp_of_abs_le hM (abs_lt_of_tentReal_ne_zero hx).le (abs_lt_of_tentReal_ne_zero hy).le]
  simp only [ContinuousMap.star_apply, StarMul.star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- The span of the rank-one kernels. -/
def rankOneSpan : Submodule ℂ KernelAlg :=
  Submodule.span ℂ (Set.range fun φψ : C_c(ℝ, ℂ) × C_c(ℝ, ℂ) => KernelAlg.rankOneKernel φψ.1 φψ.2)

theorem boxExtend_mem_rankOneSpan {M : ℝ} (hM : 0 ≤ M) {f : C(squareBox M, ℂ)}
    (hf : f ∈ prodSpan M) : boxExtend hM f ∈ rankOneSpan := by
  change boxExtendₗ hM f ∈ rankOneSpan
  have hf' : f ∈ Submodule.span ℂ (prodFns M) := hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hg
    change boxExtend hM (prodFn M a b) ∈ rankOneSpan
    rw [boxExtend_prodFn]
    exact Submodule.subset_span ⟨⟨_, _⟩, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-! ## Density of the rank-one kernels in the `L¹(ℝ, C₀(ℝ))` norm -/

/-- **The rank-one kernels are dense in the twisted convolution core** for the `L¹(ℝ, C₀(ℝ))`
norm. -/
theorem KernelAlg.exists_rankOneSpan_l1Norm_sub_lt (k : KernelAlg) {ε : ℝ} (hε : 0 < ε) :
    ∃ k' ∈ rankOneSpan, (k - k').l1Norm < ε := by
  -- a box containing the support with a margin
  obtain ⟨R, hR⟩ := k.hasCompactSupport_toFun.isCompact.isBounded.subset_closedBall 0
  set M : ℝ := |R| + 1
  have hM : 0 ≤ M := by positivity
  have hsupp : ∀ x y, (M - 1 < |x| ∨ M - 1 < |y|) → k.toFun (x, y) = 0 := by
    intro x y hxy
    by_contra h
    have hmem : (x, y) ∈ Metric.closedBall (0 : ℝ × ℝ) R := hR (subset_tsupport _ h)
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      Real.norm_eq_abs] at hmem
    have hR' : R ≤ |R| := le_abs_self R
    rcases hxy with h1 | h1 <;> [linarith [le_max_left |x| |y|]; linarith [le_max_right |x| |y|]]
  -- the restriction of `k` to the box
  let f : C(squareBox M, ℂ) := ⟨fun q => k.toFun q, k.continuous_toFun.comp continuous_subtype_val⟩
  have hf_apply : ∀ q, f q = k.toFun (q : ℝ × ℝ) := fun q => rfl
  have hkf : boxExtend hM f = k := by
    refine KernelAlg.ext fun ⟨x, y⟩ => ?_
    rw [boxExtend_apply]
    by_cases hxy : M - 1 < |x| ∨ M - 1 < |y|
    · rw [hsupp x y hxy]
      by_cases hx : tentReal M x = 0
      · simp [hx]
      by_cases hy : tentReal M y = 0
      · simp [hy]
      rw [hf_apply, squareBoxClamp_of_abs_le hM (abs_lt_of_tentReal_ne_zero hx).le
        (abs_lt_of_tentReal_ne_zero hy).le, hsupp x y hxy, mul_zero]
    · push Not at hxy
      rw [tentReal_eq_one hxy.1, tentReal_eq_one hxy.2, hf_apply,
        squareBoxClamp_of_abs_le hM (by linarith) (by linarith)]
      simp
  -- uniform approximation on the box
  obtain ⟨p, hp, hfp⟩ := exists_prodSpan_dist_lt M f
    (by positivity : (0 : ℝ) < ε / (4 * M + 1))
  refine ⟨boxExtend hM p, boxExtend_mem_rankOneSpan hM hp, ?_⟩
  have hdiff : k - boxExtend hM p = boxExtend hM (f - p) := by
    rw [← hkf]
    exact ((boxExtendₗ hM).map_sub f p).symm
  rw [hdiff]
  have hb := (boxExtend hM (f - p)).l1Norm_le_of_box hM (norm_nonneg (f - p))
    (norm_boxExtend_le hM (f - p)) fun x y h => boxExtend_eq_zero hM (f - p) h
  rw [dist_eq_norm] at hfp
  calc (boxExtend hM (f - p)).l1Norm ≤ 4 * M * ‖f - p‖ := hb
    _ ≤ 4 * M * (ε / (4 * M + 1)) := by gcongr
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end GaloisForLFunctions.HTGeometry
