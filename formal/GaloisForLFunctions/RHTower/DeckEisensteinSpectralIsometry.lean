import GaloisForLFunctions.RHTower.DeckIncompleteEisensteinDensity

/-!
# The continuous spectrum: the Eisenstein transform and Parseval

With `κ = (2L²)⁻¹ ρ₁` (`resConst`), Parseval for pairs of generators reads
`⟨E_i, E_j⟩ = π⁻¹ ⟨T_i, T_j⟩_{L²(ℝ)} + κ ⟨E_i, 𝟙⟩⟨𝟙, E_j⟩` (`inner_genVec`); it extends
sesquilinearly to finite combinations (`inner_combVec`).  Hence the transform of a combination depends
only on the combination itself, is bounded on the span of the generators, and extends to a bounded
operator `T̄` on the Eisenstein space `ℰ` (`eisTransformE`) satisfying the same identity
(`inner_eisSpace`).  Composed with the projection onto `ℰ` it gives `eisTransformL2` on `L²`.

Since `𝟙 ∈ ℰ` (constants are orthogonal to the cuspidal carrier) and the cuspidal carrier is the
orthogonal complement of `ℰ` in the central space, every central `f, g` with `⟨𝟙, g⟩ = 0` satisfy
**Parseval** `⟨f, g⟩ = Σ_j ⟨f, u_j⟩⟨u_j, g⟩ + π⁻¹ ⟨T̄ f, T̄ g⟩` over the cuspidal eigenbasis
(`inner_eq_cusp_add_eisTransform`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Metric EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry
open _root_.RHTower (linePt linePt_re linePt_im)

noncomputable section

variable {N : ℕ}

/-! ## The residual term -/

/-- The residual constant `κ = (2L²)⁻¹ ρ₁`. -/
def resConst (N : ℕ) : ℂ := (2 * (N + 1 : ℂ) ^ 2)⁻¹ * scatResidue N

theorem inner_onesVec_left (w : DeckSpace N) : ⟪onesVec N, w⟫_ℂ = ∑ x : Deck N, w x := by
  simp [PiLp.inner_apply, onesVec_apply]

theorem horoAverage_onesField (v : DeckSpace N) (y : ℝ) :
    horoAverage v (onesField N) y = ⟪v, onesVec N⟫_ℂ := by
  simp only [horoAverage, onesField]
  rw [setIntegral_const, Real.volume_real_Ico_of_le zero_le_one, sub_zero, one_smul]

theorem inner_incEisL2_onesL2 (ψ : HeightProfile) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) :
    ⟪incEisL2 ψ v, onesL2 N⟫_ℂ = 2 * (conj (hMellin ψ.toFun 1) * ⟪v, onesVec N⟫_ℂ) := by
  rw [inner_incEisL2 ψ hv onesL2_coeFn continuous_const deckEquivariant_onesField]
  congr 1
  simp_rw [horoAverage_onesField]
  have h := ψ.conjProfile.integral_inv_sq_smul_mul_cpow 0
  simp only [Complex.cpow_zero, mul_one, sub_zero] at h
  have hc : conj (hMellin ψ.toFun 1) = hMellin ψ.conjProfile.toFun 1 := by
    rw [HeightProfile.hMellin_conjProfile, map_one]
  rw [hc, ← h, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [smul_mul_assoc]
  rfl

/-- **Parseval for a pair of generators**, residual term written with `𝟙`. -/
theorem inner_incEisL2_eq_eisTransform_res (hN : 2 ≤ N) (ψ φ : HeightProfile)
    (hψ : ContDiff ℝ 2 ψ.toFun) (hφ : ContDiff ℝ 2 φ.toFun) {v w : DeckSpace N}
    (hv : IsCuspVec v) (hw : IsCuspVec w) :
    ⟪incEisL2 ψ v, incEisL2 φ w⟫_ℂ =
      (Real.pi : ℂ)⁻¹ * (∫ t : ℝ, ⟪eisTransform ψ v t, eisTransform φ w t⟫_ℂ) +
        resConst N * ⟪incEisL2 ψ v, onesL2 N⟫_ℂ * ⟪onesL2 N, incEisL2 φ w⟫_ℂ := by
  rw [inner_incEisL2_eq_eisTransform hN ψ φ hψ hφ hv hw, ← inner_conj_symm (onesL2 N),
    inner_incEisL2_onesL2 ψ hv.1, inner_incEisL2_onesL2 φ hw.1, resVec, inner_smul_right]
  simp only [map_mul, Complex.conj_conj, map_ofNat, inner_conj_symm, inner_onesVec_left, resConst]
  ring

/-! ## The transform of a generator -/

theorem continuous_eisTransform (hN : 2 ≤ N) (ψ : HeightProfile) {v : DeckSpace N}
    (hv : IsCuspVec v) : Continuous (eisTransform ψ v) := by
  have hL : ∀ t : ℝ, ContinuousAt (scatExt v) (linePt (-t)) := fun t =>
    continuousAt_scatExt hN hv (by rw [linePt_re]) fun h => by
      have := congrArg Complex.re h; rw [linePt_re] at this; norm_num at this
  have hc1 : Continuous fun t : ℝ => hMellin ψ.toFun (linePt t) := ψ.continuous_hMellin_line (1 / 2)
  have hc2 : Continuous fun t : ℝ => hMellin ψ.toFun (linePt (-t)) := hc1.comp continuous_neg
  have hc3 : Continuous fun t : ℝ => scatExt v (linePt (-t)) :=
    continuous_iff_continuousAt.2 fun t =>
      (hL t).comp (f := fun t : ℝ => linePt (-t)) (by unfold linePt; fun_prop)
  exact (hc1.smul continuous_const).add (hc2.smul hc3)

theorem norm_eisTransform_le (hN : 2 ≤ N) (ψ : HeightProfile) {v : DeckSpace N} (hv : IsCuspVec v)
    (t : ℝ) : ‖eisTransform ψ v t‖ ≤
      (‖hMellin ψ.toFun (linePt t)‖ + ‖hMellin ψ.toFun (linePt (-t))‖) * ‖v‖ := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, show ‖scatExt v (linePt (-t))‖ = ‖v‖ from norm_scatExt_line hN hv (-t)]
  ring

theorem memLp_eisTransform (hN : 2 ≤ N) (ψ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun)
    {v : DeckSpace N} (hv : IsCuspVec v) : MemLp (eisTransform ψ v) 2 volume := by
  obtain ⟨C, hC0, hC⟩ := ψ.exists_bound_hMellin hψ (1 / 2) (1 / 2)
  have hb : ∀ s : ℝ, ‖hMellin ψ.toFun (linePt s)‖ ≤ C * (1 + s ^ 2)⁻¹ := fun s => by
    have := hC (linePt s) (by rw [linePt_re]) (by rw [linePt_re])
    rwa [linePt_im] at this
  have hc := continuous_eisTransform hN ψ hv
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_
  refine (integrable_inv_one_add_sq.const_mul (4 * C ^ 2 * ‖v‖ ^ 2)).mono'
    (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h1 := norm_eisTransform_le hN ψ hv t
  have h2 := hb t
  have h3 := hb (-t)
  rw [neg_sq] at h3
  have hi := inv_one_add_sq_le_one t
  have hpos : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc ‖eisTransform ψ v t‖ ^ 2
      ≤ ((‖hMellin ψ.toFun (linePt t)‖ + ‖hMellin ψ.toFun (linePt (-t))‖) * ‖v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ ((2 * C * (1 + t ^ 2)⁻¹) * ‖v‖) ^ 2 := by
        gcongr
        linarith
    _ = 4 * C ^ 2 * ‖v‖ ^ 2 * ((1 + t ^ 2)⁻¹ * (1 + t ^ 2)⁻¹) := by ring
    _ ≤ 4 * C ^ 2 * ‖v‖ ^ 2 * (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hpos hi) (by positivity)

/-! ## Generators and their combinations -/

/-- A generator of the Eisenstein space: a `C²` height profile and a vector of `V_∞`. -/
structure EisGenIndex (N : ℕ) where
  prof : HeightProfile
  contDiff : ContDiff ℝ 2 prof.toFun
  vec : DeckSpace N
  cusp : IsCuspVec vec

/-- The incomplete Eisenstein series of a generator. -/
def genVec (i : EisGenIndex N) : DeckL2 N := incEisL2 i.prof i.vec

/-- The Eisenstein transform of a generator, as an element of `L²(ℝ)`. -/
def genTrans (hN : 2 ≤ N) (i : EisGenIndex N) : Lp (DeckSpace N) 2 (volume : Measure ℝ) :=
  (memLp_eisTransform hN i.prof i.contDiff i.cusp).toLp _

theorem genTrans_coeFn (hN : 2 ≤ N) (i : EisGenIndex N) :
    (genTrans hN i : ℝ → DeckSpace N) =ᵐ[volume] eisTransform i.prof i.vec :=
  MemLp.coeFn_toLp _

theorem inner_genTrans (hN : 2 ≤ N) (i j : EisGenIndex N) :
    ⟪genTrans hN i, genTrans hN j⟫_ℂ =
      ∫ t : ℝ, ⟪eisTransform i.prof i.vec t, eisTransform j.prof j.vec t⟫_ℂ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [genTrans_coeFn hN i, genTrans_coeFn hN j] with t h1 h2
  rw [h1, h2]

theorem inner_genVec (hN : 2 ≤ N) (i j : EisGenIndex N) :
    ⟪genVec i, genVec j⟫_ℂ = (Real.pi : ℂ)⁻¹ * ⟪genTrans hN i, genTrans hN j⟫_ℂ +
      resConst N * ⟪genVec i, onesL2 N⟫_ℂ * ⟪onesL2 N, genVec j⟫_ℂ := by
  rw [inner_genTrans]
  exact inner_incEisL2_eq_eisTransform_res hN _ _ i.contDiff j.contDiff i.cusp j.cusp

/-- Finite combinations of generators. -/
def combVec : (EisGenIndex N →₀ ℂ) →ₗ[ℂ] DeckL2 N := Finsupp.linearCombination ℂ genVec

/-- Their transforms. -/
def combTrans (hN : 2 ≤ N) : (EisGenIndex N →₀ ℂ) →ₗ[ℂ] Lp (DeckSpace N) 2 (volume : Measure ℝ) :=
  Finsupp.linearCombination ℂ (genTrans hN)

theorem inner_combVec (hN : 2 ≤ N) (x y : EisGenIndex N →₀ ℂ) :
    ⟪combVec x, combVec y⟫_ℂ = (Real.pi : ℂ)⁻¹ * ⟪combTrans hN x, combTrans hN y⟫_ℂ +
      resConst N * ⟪combVec x, onesL2 N⟫_ℂ * ⟪onesL2 N, combVec y⟫_ℂ := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']; ring
  | single i a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']; ring
    | single j b =>
      simp only [combVec, combTrans, Finsupp.linearCombination_single, inner_smul_left,
        inner_smul_right, inner_genVec hN i j]
      ring

theorem combTrans_eq_zero (hN : 2 ≤ N) {x : EisGenIndex N →₀ ℂ} (hx : combVec x = 0) :
    combTrans hN x = 0 := by
  have h := inner_combVec hN x x
  simp only [hx, inner_zero_left, inner_zero_right, mul_zero, add_zero] at h
  have hπ : (Real.pi : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  exact inner_self_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_left hπ)

/-! ## The transform on the span of the generators -/

/-- The span of the generators. -/
abbrev genSpan (N : ℕ) : Submodule ℂ (DeckL2 N) := LinearMap.range (combVec (N := N))

/-- The transform on the span of the generators. -/
def transOnSpan (hN : 2 ≤ N) : genSpan N →ₗ[ℂ] Lp (DeckSpace N) 2 (volume : Measure ℝ) :=
  ((LinearMap.ker (combVec (N := N))).liftQ (combTrans hN) fun _ hx =>
    LinearMap.mem_ker.2 (combTrans_eq_zero hN (LinearMap.mem_ker.1 hx))).comp
    (combVec (N := N)).quotKerEquivRange.symm.toLinearMap

theorem transOnSpan_apply (hN : 2 ≤ N) (x : EisGenIndex N →₀ ℂ) :
    transOnSpan hN ⟨combVec x, LinearMap.mem_range_self _ x⟩ = combTrans hN x := by
  simp only [transOnSpan, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

theorem norm_transOnSpan_le (hN : 2 ≤ N) (f : genSpan N) :
    ‖transOnSpan hN f‖ ≤ Real.sqrt (Real.pi * (1 + ‖resConst N‖ * ‖onesL2 N‖ ^ 2)) * ‖f‖ := by
  obtain ⟨x, hx⟩ := f.2
  have hf : f = ⟨combVec x, LinearMap.mem_range_self _ x⟩ := Subtype.ext hx.symm
  subst hf
  rw [transOnSpan_apply]
  set T := combTrans hN x
  set F := combVec x
  have h := inner_combVec hN x x
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e : ⟪T, T⟫_ℂ = (Real.pi : ℂ) * (⟪F, F⟫_ℂ - resConst N * ⟪F, onesL2 N⟫_ℂ * ⟪onesL2 N, F⟫_ℂ) := by
    rw [h]; field_simp; ring
  have hT : ‖T‖ ^ 2 ≤ Real.pi * (1 + ‖resConst N‖ * ‖onesL2 N‖ ^ 2) * ‖F‖ ^ 2 := by
    have n1 : ‖⟪T, T⟫_ℂ‖ = ‖T‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    have n2 : ‖⟪F, F⟫_ℂ - resConst N * ⟪F, onesL2 N⟫_ℂ * ⟪onesL2 N, F⟫_ℂ‖ ≤
        ‖F‖ ^ 2 + ‖resConst N‖ * ‖onesL2 N‖ ^ 2 * ‖F‖ ^ 2 := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · exact (norm_inner_le_norm _ _).trans (le_of_eq (by ring))
      · rw [norm_mul, norm_mul]
        have h1 := norm_inner_le_norm (𝕜 := ℂ) F (onesL2 N)
        have h2 := norm_inner_le_norm (𝕜 := ℂ) (onesL2 N) F
        calc ‖resConst N‖ * ‖⟪F, onesL2 N⟫_ℂ‖ * ‖⟪onesL2 N, F⟫_ℂ‖
            ≤ ‖resConst N‖ * (‖F‖ * ‖onesL2 N‖) * (‖onesL2 N‖ * ‖F‖) := by gcongr
          _ = ‖resConst N‖ * ‖onesL2 N‖ ^ 2 * ‖F‖ ^ 2 := by ring
    rw [← n1, e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    calc Real.pi * ‖⟪F, F⟫_ℂ - resConst N * ⟪F, onesL2 N⟫_ℂ * ⟪onesL2 N, F⟫_ℂ‖
        ≤ Real.pi * (‖F‖ ^ 2 + ‖resConst N‖ * ‖onesL2 N‖ ^ 2 * ‖F‖ ^ 2) :=
          mul_le_mul_of_nonneg_left n2 Real.pi_pos.le
      _ = Real.pi * (1 + ‖resConst N‖ * ‖onesL2 N‖ ^ 2) * ‖F‖ ^ 2 := by ring
  have hc : 0 ≤ Real.pi * (1 + ‖resConst N‖ * ‖onesL2 N‖ ^ 2) := by positivity
  change ‖T‖ ≤ _ * ‖F‖
  rw [← Real.sqrt_sq (norm_nonneg T), ← Real.sqrt_sq (norm_nonneg F), ← Real.sqrt_mul hc]
  exact Real.sqrt_le_sqrt hT

/-- The bounded transform on the span of the generators. -/
def transOnSpanCLM (hN : 2 ≤ N) : genSpan N →L[ℂ] Lp (DeckSpace N) 2 (volume : Measure ℝ) :=
  (transOnSpan hN).mkContinuous _ (norm_transOnSpan_le hN)

/-! ## Extension to the Eisenstein space -/

instance eisSpace_completeSpace : CompleteSpace (eisSpace N) := isClosed_eisSpace.completeSpace_coe

theorem range_genVec : Set.range (genVec (N := N)) = eisGen N := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.prof, i.contDiff, i.vec, i.cusp, rfl⟩
  · rintro ⟨ψ, hψ, v, hv, rfl⟩
    exact ⟨⟨ψ, hψ, v, hv⟩, rfl⟩

theorem genSpan_eq : genSpan N = Submodule.span ℂ (eisGen N) := by
  rw [genSpan, combVec, Finsupp.range_linearCombination, range_genVec]

theorem genSpan_le_eisSpace : genSpan N ≤ eisSpace N := by
  rw [genSpan_eq]
  exact Submodule.le_topologicalClosure _

/-- The inclusion of the span into the Eisenstein space. -/
def spanIncl : genSpan N →L[ℂ] eisSpace N :=
  (Submodule.inclusion genSpan_le_eisSpace).mkContinuous 1 fun _ => by
    rw [one_mul]
    exact le_of_eq rfl

theorem spanIncl_apply (x : genSpan N) : ((spanIncl x : eisSpace N) : DeckL2 N) = x := rfl

theorem isUniformInducing_spanIncl : IsUniformInducing (spanIncl (N := N)) :=
  (AddMonoidHomClass.isometry_of_norm spanIncl fun _ => rfl).isUniformInducing

theorem denseRange_spanIncl : DenseRange (spanIncl (N := N)) := by
  intro y
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, mem_preimage]
  have hsub : (genSpan N : Set (DeckL2 N)) ⊆ Subtype.val '' Set.range (spanIncl (N := N)) :=
    fun f hf => ⟨spanIncl ⟨f, hf⟩, ⟨⟨f, hf⟩, rfl⟩, rfl⟩
  refine closure_mono hsub ?_
  have h : (eisSpace N : Set (DeckL2 N)) = closure (genSpan N : Set (DeckL2 N)) := by
    rw [genSpan_eq]
    exact Submodule.topologicalClosure_coe _
  rw [← h]
  exact y.2

/-- **The Eisenstein transform on the Eisenstein space.** -/
def eisTransformE (hN : 2 ≤ N) : eisSpace N →L[ℂ] Lp (DeckSpace N) 2 (volume : Measure ℝ) :=
  (transOnSpanCLM hN).extend spanIncl

theorem eisTransformE_spanIncl (hN : 2 ≤ N) (x : genSpan N) :
    eisTransformE hN (spanIncl x) = transOnSpan hN x :=
  (transOnSpanCLM hN).extend_eq denseRange_spanIncl isUniformInducing_spanIncl x

/-- **Parseval on the Eisenstein space.** -/
theorem inner_eisSpace (hN : 2 ≤ N) (f g : eisSpace N) :
    ⟪(f : DeckL2 N), g⟫_ℂ = (Real.pi : ℂ)⁻¹ * ⟪eisTransformE hN f, eisTransformE hN g⟫_ℂ +
      resConst N * ⟪(f : DeckL2 N), onesL2 N⟫_ℂ * ⟪onesL2 N, (g : DeckL2 N)⟫_ℂ := by
  refine denseRange_spanIncl.induction_on₂ (p := fun f g : eisSpace N => ⟪(f : DeckL2 N), g⟫_ℂ =
      (Real.pi : ℂ)⁻¹ * ⟪eisTransformE hN f, eisTransformE hN g⟫_ℂ +
        resConst N * ⟪(f : DeckL2 N), onesL2 N⟫_ℂ * ⟪onesL2 N, (g : DeckL2 N)⟫_ℂ) ?_ ?_ f g
  · refine isClosed_eq ?_ ?_
    · exact (continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd)
    · refine (continuous_const.mul (((eisTransformE hN).continuous.comp continuous_fst).inner
        ((eisTransformE hN).continuous.comp continuous_snd))).add ?_
      exact (continuous_const.mul ((continuous_subtype_val.comp continuous_fst).inner
        continuous_const)).mul (continuous_const.inner (continuous_subtype_val.comp continuous_snd))
  · intro a b
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    have ha : a = ⟨combVec x, LinearMap.mem_range_self _ x⟩ := Subtype.ext hx.symm
    have hb : b = ⟨combVec y, LinearMap.mem_range_self _ y⟩ := Subtype.ext hy.symm
    subst ha hb
    rw [eisTransformE_spanIncl, eisTransformE_spanIncl, transOnSpan_apply, transOnSpan_apply,
      spanIncl_apply, spanIncl_apply]
    exact inner_combVec hN x y

theorem genVec_mem_genSpan (i : EisGenIndex N) : genVec i ∈ genSpan N :=
  ⟨Finsupp.single i 1, by rw [combVec, Finsupp.linearCombination_single, one_smul]⟩

/-- The extended transform of a generator is its explicit transform. -/
theorem eisTransformE_genVec (hN : 2 ≤ N) (i : EisGenIndex N) :
    eisTransformE hN ⟨genVec i, genSpan_le_eisSpace (genVec_mem_genSpan i)⟩ = genTrans hN i := by
  have h := eisTransformE_spanIncl hN ⟨combVec (Finsupp.single i 1), LinearMap.mem_range_self _ _⟩
  rw [transOnSpan_apply] at h
  have e : (spanIncl ⟨combVec (Finsupp.single i 1), LinearMap.mem_range_self _ _⟩ : eisSpace N) =
      ⟨genVec i, genSpan_le_eisSpace (genVec_mem_genSpan i)⟩ := by
    apply Subtype.ext
    rw [spanIncl_apply]
    simp [combVec]
  rw [e] at h
  rw [h]
  simp [combTrans]

/-! ## Spectral decomposition of the central space -/

/-- The constant vector lies in the Eisenstein space. -/
theorem onesL2_mem_eisSpace : onesL2 N ∈ eisSpace N := by
  set P := (eisSpace N).starProjection
  have hc : onesL2 N - P (onesL2 N) ∈ cuspidalL2Closure N := by
    rw [mem_cuspidalL2Closure_iff_eisSpace]
    refine ⟨Submodule.sub_mem _ ?_ (eisSpace_le_deckCentralFixedL2 ((eisSpace N).starProjection_apply_mem _)), ?_⟩
    · exact toDeckL2_mem_deckCentralFixedL2 deckEquivariant_onesField memLp_onesField
    · intro g hg
      exact ((eisSpace N).mem_orthogonal _).1 ((eisSpace N).sub_starProjection_mem_orthogonal _) g hg
  have h0 := inner_onesL2_eq_zero_of_mem hc
  have h1 : ⟪P (onesL2 N), onesL2 N - P (onesL2 N)⟫_ℂ = 0 :=
    ((eisSpace N).mem_orthogonal _).1 ((eisSpace N).sub_starProjection_mem_orthogonal _) _
      ((eisSpace N).starProjection_apply_mem _)
  have h2 : ⟪onesL2 N - P (onesL2 N), onesL2 N - P (onesL2 N)⟫_ℂ = 0 := by
    rw [inner_sub_left, h0, h1, sub_zero]
  have h3 := sub_eq_zero.1 (inner_self_eq_zero.1 h2)
  rw [h3]
  exact (eisSpace N).starProjection_apply_mem _

/-- **The Eisenstein transform on `L²`**: `T̄` applied to the projection onto `ℰ`. -/
def eisTransformL2 (hN : 2 ≤ N) : DeckL2 N →L[ℂ] Lp (DeckSpace N) 2 (volume : Measure ℝ) :=
  (eisTransformE hN).comp (eisSpace N).orthogonalProjectionOnto

theorem eisTransformL2_incEisL2 (hN : 2 ≤ N) (ψ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun)
    {v : DeckSpace N} (hv : IsCuspVec v) :
    eisTransformL2 hN (incEisL2 ψ v) = (memLp_eisTransform hN ψ hψ hv).toLp _ := by
  have hmem : incEisL2 ψ v ∈ eisSpace N := incEisL2_mem_eisSpace ψ hv.1
  rw [eisTransformL2, ContinuousLinearMap.comp_apply,
    show (eisSpace N).orthogonalProjectionOnto (incEisL2 ψ v) = ⟨incEisL2 ψ v, hmem⟩ from
      (eisSpace N).orthogonalProjectionOnto_mem_subspace_eq_self ⟨incEisL2 ψ v, hmem⟩]
  exact eisTransformE_genVec hN ⟨ψ, hψ, v, hv⟩

/-- **Parseval over the full spectrum.** For central `f, g` with `⟨𝟙, g⟩ = 0`,
`⟨f, g⟩ = Σ_j ⟨f, u_j⟩⟨u_j, g⟩ + π⁻¹ ⟨T̄ f, T̄ g⟩`, `u_j` the cuspidal Laplace eigenbasis. -/
theorem inner_eq_cusp_add_eisTransform (hN : 2 ≤ N) {f g : DeckL2 N}
    (hf : f ∈ deckCentralFixedL2 N) (hg : g ∈ deckCentralFixedL2 N) (hg1 : ⟪onesL2 N, g⟫_ℂ = 0) :
    ⟪f, g⟫_ℂ = (∑' j, ⟪f, (cuspEigenBasis N j : DeckL2 N)⟫_ℂ * ⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ) +
      (Real.pi : ℂ)⁻¹ * ⟪eisTransformL2 hN f, eisTransformL2 hN g⟫_ℂ := by
  set E := eisSpace N
  set P := E.starProjection
  have hcusp : ∀ h ∈ deckCentralFixedL2 N, h - P h ∈ cuspidalL2Closure N := fun h hh => by
    rw [mem_cuspidalL2Closure_iff_eisSpace]
    refine ⟨Submodule.sub_mem _ hh (eisSpace_le_deckCentralFixedL2 (E.starProjection_apply_mem _)),
      fun u hu => ?_⟩
    exact (E.mem_orthogonal _).1 (E.sub_starProjection_mem_orthogonal _) u hu
  have horthE : ∀ c ∈ cuspidalL2Closure N, ∀ e ∈ E, ⟪c, e⟫_ℂ = 0 := fun c hc e he => by
    rw [← inner_conj_symm, ((mem_cuspidalL2Closure_iff_eisSpace c).1 hc).2 e he, map_zero]
  set fc : CuspidalL2 N := ⟨f - P f, hcusp f hf⟩
  set gc : CuspidalL2 N := ⟨g - P g, hcusp g hg⟩
  have hPf := E.starProjection_apply_mem f
  have hPg := E.starProjection_apply_mem g
  -- splitting the inner product
  have hsplit : ⟪f, g⟫_ℂ = ⟪(fc : DeckL2 N), gc⟫_ℂ + ⟪P f, P g⟫_ℂ := by
    have e1 : f = (f - P f) + P f := by abel
    have e2 : g = (g - P g) + P g := by abel
    conv_lhs => rw [e1, e2]
    rw [inner_add_left, inner_add_right, inner_add_right, horthE _ fc.2 _ hPg,
      ← inner_conj_symm (P f), horthE _ gc.2 _ hPf, map_zero]
    simp [fc, gc]
  -- the cuspidal part
  have hcuspsum : ⟪(fc : DeckL2 N), gc⟫_ℂ = ∑' j, ⟪f, (cuspEigenBasis N j : DeckL2 N)⟫_ℂ *
      ⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ := by
    have h := (cuspEigenBasis N).tsum_inner_mul_inner fc gc
    rw [← Submodule.coe_inner, ← h]
    refine tsum_congr fun j => ?_
    have hj := (cuspEigenBasis N j).2
    have e1 : ⟪fc, cuspEigenBasis N j⟫_ℂ = ⟪f, (cuspEigenBasis N j : DeckL2 N)⟫_ℂ := by
      rw [Submodule.coe_inner]
      simp only [fc]
      rw [inner_sub_left, ← inner_conj_symm (P f), horthE _ hj _ hPf, map_zero, sub_zero]
    have e2 : ⟪cuspEigenBasis N j, gc⟫_ℂ = ⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ := by
      rw [Submodule.coe_inner]
      simp only [gc]
      rw [inner_sub_right, horthE _ hj _ hPg, sub_zero]
    rw [e1, e2]
  -- the Eisenstein part
  have heis : ⟪P f, P g⟫_ℂ = (Real.pi : ℂ)⁻¹ * ⟪eisTransformL2 hN f, eisTransformL2 hN g⟫_ℂ := by
    have h := inner_eisSpace hN (E.orthogonalProjectionOnto f) (E.orthogonalProjectionOnto g)
    simp only [Submodule.coe_orthogonalProjectionOnto_apply] at h
    have hone : ⟪onesL2 N, P g⟫_ℂ = 0 := by
      have h0 : ⟪onesL2 N, g - P g⟫_ℂ = 0 :=
        (E.mem_orthogonal _).1 (E.sub_starProjection_mem_orthogonal _) _ onesL2_mem_eisSpace
      rw [inner_sub_right, hg1, zero_sub, neg_eq_zero] at h0
      exact h0
    rw [h, hone, mul_zero, add_zero]
    rfl
  rw [hsplit, hcuspsum, heis]

end

end GaloisForLFunctions.RHTower.DeckPointPair
