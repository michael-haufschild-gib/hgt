import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitGramian
import GaloisForLFunctions.HTGeometry.WeakSequentialCompactness
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability

/-!
# Inverse Gramians: diagonal calculus, inverse operator, conjugate form and naturality

* **Basis-diagonal operators.**  For a Hilbert basis `(b_k)` and bounded multipliers `c_k`, the
  operator `b_k ↦ c_k b_k`; it is compact when `c_k → 0`.
* **Compact images.**  A compact operator on a separable Hilbert space maps every closed ball onto
  a compact set (weak sequential compactness of the ball).
* **The inverse operator.**  For an injective bounded `G`, the partially defined operator
  `G^{-1}` with domain `Ran G`.  When `G` is self-adjoint its range is dense and `G^{-1}` is
  self-adjoint; when `G` is positive, so is `G^{-1}`.
* **The conjugate form** `q_G(x) = sup_y (2 Re⟨y, x⟩ - ⟨y, G y⟩) ∈ [0, ∞]`, natural under unitary
  conjugation and homogeneous of degree `-1` in `G`.
* **Naturality of orbit Gramians**: `∫ |U S_t U^{-1} U v⟩⟨⋯| dt = U (∫ |S_t v⟩⟨S_t v| dt) U^{-1}`
  and `∫ |S_{at} v⟩⟨S_{at} v| dt = a^{-1} ∫ |S_t v⟩⟨S_t v| dt`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## Basis-diagonal operators -/

section BasisDiagonal

variable {κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The operator acting by `b_k ↦ c_k b_k` on a Hilbert basis, for bounded multipliers. -/
def basisDiag (b : HilbertBasis κ ℂ E) (c : κ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hc : ∀ k, ‖c k‖ ≤ M) :
    E →L[ℂ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L LpDiagonal.lpDiag c M hM hc ∘L
    b.repr.toContinuousLinearEquiv.toContinuousLinearMap

variable (b : HilbertBasis κ ℂ E) (c : κ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hc : ∀ k, ‖c k‖ ≤ M)

theorem repr_basisDiag (x : E) (k : κ) : b.repr (basisDiag b c hM hc x) k = c k * b.repr x k := by
  simp [basisDiag]

theorem inner_basis_basisDiag (x : E) (k : κ) :
    ⟪b k, basisDiag b c hM hc x⟫_ℂ = c k * ⟪b k, x⟫_ℂ := by
  rw [← b.repr_apply_apply, repr_basisDiag, b.repr_apply_apply]

theorem basisDiag_basis [DecidableEq κ] (k : κ) : basisDiag b c hM hc (b k) = c k • b k := by
  refine b.repr.injective (lp.ext (funext fun l => ?_))
  rw [repr_basisDiag, map_smul, lp.coeFn_smul, Pi.smul_apply, HilbertBasis.repr_self,
    lp.single_apply]
  by_cases hl : l = k
  · subst hl; simp
  · simp [Pi.single_eq_of_ne hl]

/-- Two bounded operators agreeing on a Hilbert basis are equal. -/
theorem ext_hilbertBasis {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {A B : E →L[ℂ] F} (h : ∀ k, A (b k) = B (b k)) : A = B := by
  have hd : Dense (Submodule.span ℂ (Set.range b) : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span
  exact ContinuousLinearMap.ext_on hd (by rintro _ ⟨k, rfl⟩; exact h k)

theorem isCompactOperator_basisDiag [DecidableEq κ]
    (hlim : Tendsto (fun k => ‖c k‖) cofinite (𝓝 0)) : IsCompactOperator (basisDiag b c hM hc) := by
  have hD := LpDiagonal.isCompactOperator_lpDiag c M hM hc hlim
  exact (hD.comp_clm b.repr.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem basisDiag_comp {d : κ → ℂ} {N : ℝ} (hN : 0 ≤ N) (hd : ∀ k, ‖d k‖ ≤ N)
    {P : ℝ} (hP : 0 ≤ P) (hcd : ∀ k, ‖c k * d k‖ ≤ P) :
    basisDiag b c hM hc ∘L basisDiag b d hN hd = basisDiag b (fun k => c k * d k) hP hcd := by
  refine ContinuousLinearMap.ext fun x => b.repr.injective (lp.ext (funext fun k => ?_))
  rw [ContinuousLinearMap.comp_apply, repr_basisDiag, repr_basisDiag, repr_basisDiag, mul_assoc]

end BasisDiagonal

/-! ## Compact images of balls -/

section CompactImage

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- A compact operator on a separable Hilbert space maps closed balls onto compact sets. -/
theorem isCompact_image_closedBall_of_isCompactOperator (A : E →L[ℂ] F) (hA : IsCompactOperator A)
    (r : ℝ) : IsCompact (A '' Metric.closedBall 0 r) := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [Metric.closedBall_eq_empty.2 hr, image_empty]
    exact isCompact_empty
  rw [isCompact_iff_isSeqCompact]
  intro x hx
  choose y hy hyx using hx
  have hbound : ∀ n, ‖y n‖ ≤ r := fun n => by simpa using hy n
  obtain ⟨w, φ, hφ, hw, hweak⟩ := exists_weaklyConvergent_subseq_of_bounded y r hbound
  refine ⟨A w, ⟨w, by simpa using hw, rfl⟩, φ, hφ, ?_⟩
  set c : ℝ := 2 * r + 1
  have hc : 0 < c := by positivity
  set u : ℕ → E := fun n => (c⁻¹ : ℂ) • (y (φ n) - w)
  have hu1 : ∀ n, ‖u n‖ ≤ 1 := fun n => by
    simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le]
    rw [inv_mul_le_iff₀ hc, mul_one]
    calc ‖y (φ n) - w‖ ≤ ‖y (φ n)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ r + r := add_le_add (hbound _) hw
      _ ≤ c := by simp only [c]; linarith
  have huweak : ∀ z, Tendsto (fun n => ⟪z, u n⟫_ℂ) atTop (𝓝 0) := fun z => by
    have h1 : Tendsto (fun n => ⟪y (φ n) - w, z⟫_ℂ) atTop (𝓝 0) := by
      have := (hweak z).sub (tendsto_const_nhds (x := ⟪w, z⟫_ℂ))
      rw [sub_self] at this
      exact this.congr fun n => by rw [inner_sub_left]
    have h2 := ((Complex.continuous_conj.tendsto 0).comp h1).const_mul (c⁻¹ : ℂ)
    rw [map_zero, mul_zero] at h2
    refine h2.congr fun n => ?_
    simp only [u, Function.comp_apply, inner_smul_right]
    rw [inner_conj_symm]
  have hK := tendsto_norm_compact_of_weaklyNull A hA u hu1 huweak
  have hK' := hK.const_smul (c : ℂ)
  rw [smul_zero] at hK'
  have hlim : Tendsto (fun n => A (y (φ n)) - A w) atTop (𝓝 0) :=
    hK'.congr fun n => by
      simp only [u, map_smul, smul_smul, map_sub]
      rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hc.ne'), one_smul]
  have := hlim.add_const (A w)
  rw [zero_add] at this
  refine this.congr fun n => ?_
  simp only [Function.comp_apply, sub_add_cancel, hyx]

end CompactImage

/-! ## The inverse operator -/

section GramInverse

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The inverse `G^{-1}` of an injective bounded operator, defined on `Ran G`. -/
def gramInverse (G : H →L[ℂ] H) (hG : Function.Injective G) : H →ₗ.[ℂ] H where
  domain := LinearMap.range (G : H →ₗ[ℂ] H)
  toFun := (LinearEquiv.ofInjective (G : H →ₗ[ℂ] H) hG).symm.toLinearMap

theorem gramInverse_domain {G : H →L[ℂ] H} (hG : Function.Injective G) :
    (gramInverse G hG).domain = LinearMap.range (G : H →ₗ[ℂ] H) := rfl

theorem apply_gramInverse {G : H →L[ℂ] H} (hG : Function.Injective G)
    (x : (gramInverse G hG).domain) : G (gramInverse G hG x) = x := by
  have h := congrArg Subtype.val
    ((LinearEquiv.ofInjective (G : H →ₗ[ℂ] H) hG).apply_symm_apply x)
  rw [LinearEquiv.ofInjective_apply] at h
  exact h

theorem gramInverse_eq_of_apply {G : H →L[ℂ] H} (hG : Function.Injective G) {x : H}
    (hx : x ∈ (gramInverse G hG).domain) {z : H} (hz : G z = x) : gramInverse G hG ⟨x, hx⟩ = z := by
  apply hG
  rw [apply_gramInverse, hz]

theorem mem_gramInverse_domain {G : H →L[ℂ] H} (hG : Function.Injective G) (y : H) :
    G y ∈ (gramInverse G hG).domain := ⟨y, rfl⟩

/-- **Scaling.**  `(a^{-1} G)^{-1} = a G^{-1}`. -/
theorem gramInverse_smul {G : H →L[ℂ] H} (hG : Function.Injective G) {a : ℝ} (ha : 0 < a)
    (hG' : Function.Injective ((a⁻¹ : ℂ) • G)) :
    gramInverse ((a⁻¹ : ℂ) • G) hG' = (a : ℂ) • gramInverse G hG := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hsm : ∀ y, ((a⁻¹ : ℂ) • G) y = G ((a⁻¹ : ℂ) • y) := fun y => by
    rw [smul_apply, map_smul]
  have hdom : (gramInverse ((a⁻¹ : ℂ) • G) hG').domain = ((a : ℂ) • gramInverse G hG).domain := by
    rw [LinearPMap.smul_domain]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(a⁻¹ : ℂ) • y, (hsm y).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(a : ℂ) • y, ?_⟩
      change ((a⁻¹ : ℂ) • G) ((a : ℂ) • y) = G y
      rw [hsm, smul_smul, inv_mul_cancel₀ ha', one_smul]
  refine LinearPMap.ext hdom fun x hx hx' => ?_
  obtain ⟨y, hy⟩ := hx
  rw [LinearPMap.smul_apply]
  have hx'' : x ∈ (gramInverse G hG).domain := by rwa [LinearPMap.smul_domain] at hx'
  have e1 : gramInverse ((a⁻¹ : ℂ) • G) hG' ⟨x, ⟨y, hy⟩⟩ = y :=
    gramInverse_eq_of_apply hG' _ hy
  have e2 : gramInverse G hG ⟨x, hx''⟩ = (a⁻¹ : ℂ) • y :=
    gramInverse_eq_of_apply hG _ (by rw [← hsm]; exact hy)
  change gramInverse ((a⁻¹ : ℂ) • G) hG' ⟨x, ⟨y, hy⟩⟩ = (a : ℂ) • gramInverse G hG ⟨x, hx''⟩
  rw [e1, e2, smul_smul, mul_inv_cancel₀ ha', one_smul]

/-- **Unitary covariance.**  `(U G U^{-1})^{-1} (U G y) = U y`. -/
theorem gramInverse_conj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {G : H →L[ℂ] H} (U : H ≃ₗᵢ[ℂ] H')
    (hG' : Function.Injective (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L G ∘L
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap)) (y : H) :
    ∃ hy, gramInverse _ hG' ⟨U (G y), hy⟩ = U y := by
  have hy : (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L G ∘L
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap) (U y) = U (G y) := by simp
  exact ⟨⟨U y, hy⟩, gramInverse_eq_of_apply hG' _ hy⟩

/-- **`G^{-1}` is positive** when `G` is. -/
theorem re_inner_gramInverse_nonneg {G : H →L[ℂ] H} (hG : Function.Injective G)
    (hpos : G.IsPositive) (x : (gramInverse G hG).domain) :
    0 ≤ (⟪gramInverse G hG x, (x : H)⟫_ℂ).re := by
  obtain ⟨u, hu⟩ := x.2
  rw [show gramInverse G hG x = u from gramInverse_eq_of_apply hG x.2 hu, ← hu]
  exact hpos.re_inner_nonneg_right u

variable [CompleteSpace H]

theorem dense_range_of_isSelfAdjoint {G : H →L[ℂ] H} (hG : Function.Injective G)
    (hsa : IsSelfAdjoint G) : Dense (LinearMap.range (G : H →ₗ[ℂ] H) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    ContinuousLinearMap.orthogonal_range, hsa.adjoint_eq]
  exact LinearMap.ker_eq_bot.2 hG

/-- **`G^{-1}` is self-adjoint** when `G` is. -/
theorem isSelfAdjoint_gramInverse {G : H →L[ℂ] H} (hG : Function.Injective G)
    (hsa : IsSelfAdjoint G) : IsSelfAdjoint (gramInverse G hG) := by
  have hdense := dense_range_of_isSelfAdjoint hG hsa
  have hsym : ∀ x y : H, ⟪G x, y⟫_ℂ = ⟪x, G y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_right, hsa.adjoint_eq]
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := gramInverse G hG) hdense
  have hdom : (gramInverse G hG).adjoint.domain = (gramInverse G hG).domain := by
    ext y
    constructor
    · intro hy
      refine ⟨(gramInverse G hG).adjoint ⟨y, hy⟩, ext_inner_right ℂ fun u => ?_⟩
      have h := hfa ⟨y, hy⟩ ⟨G u, mem_gramInverse_domain hG u⟩
      rw [gramInverse_eq_of_apply hG _ rfl] at h
      change ⟪G ((gramInverse G hG).adjoint ⟨y, hy⟩), u⟫_ℂ = ⟪y, u⟫_ℂ
      rw [hsym]
      exact h
    · rintro ⟨z, rfl⟩
      refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨z, fun x => ?_⟩
      obtain ⟨u, hu⟩ := x.2
      rw [show gramInverse G hG x = u from gramInverse_eq_of_apply hG x.2 hu, ← hu]
      change ⟪z, G u⟫_ℂ = ⟪G z, u⟫_ℂ
      rw [hsym]
  rw [LinearPMap.isSelfAdjoint_def]
  refine LinearPMap.ext hdom fun y hy hy' => ?_
  obtain ⟨z, hz⟩ := id hy'
  rw [gramInverse_eq_of_apply hG hy' hz]
  refine LinearPMap.adjoint_apply_eq hdense _ fun x => ?_
  obtain ⟨u, hu⟩ := x.2
  rw [show gramInverse G hG x = u from gramInverse_eq_of_apply hG x.2 hu]
  show ⟪z, (x : H)⟫_ℂ = ⟪y, u⟫_ℂ
  rw [← hu, ← hz]
  change ⟪z, G u⟫_ℂ = ⟪G z, u⟫_ℂ
  rw [hsym]

end GramInverse

/-! ## The conjugate form -/

section LegendreForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The conjugate quadratic form `q_G(x) = sup_y (2 Re⟨y, x⟩ - Re⟨y, G y⟩) ∈ [0, ∞]`. -/
def legendreForm (G : H →L[ℂ] H) (x : H) : ℝ≥0∞ :=
  ⨆ y : H, ENNReal.ofReal (2 * (⟪y, x⟫_ℂ).re - (⟪y, G y⟫_ℂ).re)

/-- **Unitary covariance.**  `q_{UGU^{-1}}(Ux) = q_G(x)`. -/
theorem legendreForm_conj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (U : H ≃ₗᵢ[ℂ] H') (G : H →L[ℂ] H) (x : H) :
    legendreForm (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L G ∘L
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap) (U x) = legendreForm G x := by
  unfold legendreForm
  refine le_antisymm (iSup_le fun y => ?_) (iSup_le fun y => ?_)
  · refine le_trans (le_of_eq ?_) (le_iSup _ (U.symm y))
    congr 2
    · rw [← U.inner_map_map, U.apply_symm_apply]
    · simp only [ContinuousLinearMap.comp_apply]
      rw [← U.inner_map_map, U.apply_symm_apply]
      simp
  · refine le_trans (le_of_eq ?_) (le_iSup _ (U y))
    congr 2
    · rw [U.inner_map_map]
    · simp only [ContinuousLinearMap.comp_apply]
      rw [← U.inner_map_map]
      simp

/-- **Homogeneity.**  `q_{aG} = a^{-1} q_G` for `a > 0`. -/
theorem legendreForm_smul {a : ℝ} (ha : 0 < a) (G : H →L[ℂ] H) (x : H) :
    legendreForm ((a : ℂ) • G) x = ENNReal.ofReal a⁻¹ * legendreForm G x := by
  unfold legendreForm
  rw [ENNReal.mul_iSup]
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  refine le_antisymm (iSup_le fun y => ?_) (iSup_le fun y => ?_)
  · refine le_trans (le_of_eq ?_) (le_iSup _ ((a : ℂ) • y))
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [smul_apply, inner_smul_left, inner_smul_right, map_smul,
      Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    field_simp
  · refine le_trans (le_of_eq ?_) (le_iSup _ ((a⁻¹ : ℂ) • y))
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [smul_apply, inner_smul_left, inner_smul_right, map_smul,
      map_inv₀, Complex.conj_ofReal]
    rw [← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    field_simp

end LegendreForm

/-! ## Naturality of orbit Gramians -/

section OrbitNaturality

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrableOn_positiveRankOne {f : ℝ → H} (hc : Continuous f)
    (hi : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioi 0)) :
    IntegrableOn (fun t => positiveRankOneSchattenOne (f t)) (Ioi 0) :=
  Integrable.mono' hi (continuous_positiveRankOneSchattenOne.comp hc).aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [norm_positiveRankOneSchattenOne])

theorem schattenOnePairing_orbitGramianOf (S : ℝ → H →L[ℂ] H) (v : H)
    (hint : IntegrableOn (fun t => positiveRankOneSchattenOne (S t v)) (Ioi 0)) (x y : H) :
    schattenOnePairing x y (orbitGramianOf S v) =
      ∫ t in Ioi (0 : ℝ), ⟪x, S t v⟫_ℂ * ⟪S t v, y⟫_ℂ := by
  rw [orbitGramianOf, ← (schattenOnePairing x y).integral_comp_comm hint]
  simp_rw [schattenOnePairing_positiveRankOne]

/-- **(OG.22) Time scaling.**  `∫ |S_{at} v⟩⟨S_{at} v| dt = a^{-1} ∫ |S_t v⟩⟨S_t v| dt`. -/
theorem orbitGramianOf_comp_mul (S : ℝ → H →L[ℂ] H) (v : H) {a : ℝ} (ha : 0 < a) :
    orbitGramianOf (fun t => S (a * t)) v = (a⁻¹ : ℂ) • orbitGramianOf S v := by
  unfold orbitGramianOf
  rw [integral_comp_mul_left_Ioi (fun t => positiveRankOneSchattenOne (S t v)) 0 ha, mul_zero]
  rw [← Complex.coe_smul]
  norm_cast

/-- **(OG.22) Unitary covariance.**  The orbit Gramian of `(U S U^{-1}, U v)` is `U G U^{-1}`. -/
theorem orbitGramianOf_conj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') (S : ℝ → H →L[ℂ] H) (v : H)
    (hc : Continuous fun t => S t v) (hi : IntegrableOn (fun t => ‖S t v‖ ^ 2) (Ioi 0)) :
    (orbitGramianOf (fun t => U.toContinuousLinearEquiv.toContinuousLinearMap ∘L S t ∘L
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap) (U v) : H' →L[ℂ] H') =
      U.toContinuousLinearEquiv.toContinuousLinearMap ∘L (orbitGramianOf S v : H →L[ℂ] H) ∘L
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  have hsimp : ∀ t, (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L S t ∘L
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap) (U v) = U (S t v) := fun t => by simp
  have hc' : Continuous fun t => U (S t v) := U.continuous.comp hc
  have hi' : IntegrableOn (fun t => ‖U (S t v)‖ ^ 2) (Ioi 0) := by
    simpa only [LinearIsometryEquiv.norm_map] using hi
  have hint := integrableOn_positiveRankOne hc hi
  have hint' : IntegrableOn (fun t => positiveRankOneSchattenOne
      ((U.toContinuousLinearEquiv.toContinuousLinearMap ∘L S t ∘L
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap) (U v))) (Ioi 0) := by
    simp_rw [hsimp]
    exact integrableOn_positiveRankOne hc' hi'
  have h1 : ∀ (x' : H') (a : H), ⟪x', U a⟫_ℂ = ⟪U.symm x', a⟫_ℂ := fun x' a => by
    rw [← U.inner_map_map, U.apply_symm_apply]
  have h2 : ∀ (y' : H') (a : H), ⟪U a, y'⟫_ℂ = ⟪a, U.symm y'⟫_ℂ := fun y' a => by
    rw [← U.inner_map_map, U.apply_symm_apply]
  refine ContinuousLinearMap.ext fun y' => ext_inner_left ℂ fun x' => ?_
  rw [← schattenOnePairing_apply, schattenOnePairing_orbitGramianOf _ _ hint',
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change _ = ⟪x', U ((orbitGramianOf S v : H →L[ℂ] H) (U.symm y'))⟫_ℂ
  rw [h1, ← schattenOnePairing_apply, schattenOnePairing_orbitGramianOf _ _ hint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [hsimp, h1, h2]

end OrbitNaturality

end GaloisForLFunctions.HTGeometry
