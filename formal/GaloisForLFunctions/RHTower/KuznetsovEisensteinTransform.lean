import GaloisForLFunctions.RHTower.KuznetsovContourShift
import GaloisForLFunctions.RHTower.DeckEisensteinTransformSymmetry

/-!
# The Eisenstein transform of a Poincaré series

For `U = U(·| s₁, μ, v)` (`Re s₁ > 1`, `μ > 0`, `μ(N+1) = n`) and every `w ∈ V_∞`,

`2⟨T̄U(t), w⟩ = Φ_w(½+it)` for almost every `t` (`eisTransformL2_poinc_inner`),

with the explicit Poincaré–Eisenstein pairing `Φ_w`; likewise for the conjugate series
`P(·|h̄_{s₂,ν}, w₂)` with the pairing at `(s̄₂, ν)` and frequency `−ν(N+1)`
(`eisTransformL2_conj_inner`).  Proof: for a generator `E(·|ψ, w)`,
`⟨T̄U, T̄E⟩ = π⟨U, E⟩` (Parseval on the Eisenstein space, `U ⊥ 𝟙`); the symmetry
`T̄U(−t) = Φ̃(½+it)T̄U(t)` and `Φ̃(½−it)* = Φ̃(½+it)` give `⟨T̄U, T̄E⟩ = 2∫ψ̂(½+it)⟨T̄U(t), w⟩dt`; the
contour shift gives `π⟨U, E⟩ = ∫ψ̂(½+it)Φ_w(½+it)dt` for smooth `ψ`; density of the test-function
transforms `ψ̂_g(½+i·)` in `L²(ℝ)` concludes.  On the critical line
`|Φ_w(½+it)| ≤ C(1+|t|)^K e^{−π|t|/2}`, so `Φ_w(½+i·) ∈ L²`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ComplexConjugate InnerProductSpace ContDiff

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry
open _root_.RHTower (linePt linePt_re linePt_im)

noncomputable section

variable {N : ℕ}

/-! ## The pairing on the critical line -/

theorem exists_poly_exp_le_inv_one_add_sq (m : ℕ) :
    ∃ D, 0 ≤ D ∧ ∀ t : ℝ, (1 + |t|) ^ m * Real.exp (-(Real.pi * |t| / 2)) ≤ D * (1 + t ^ 2)⁻¹ := by
  set a : ℝ := Real.pi / 2
  have ha : 0 < a := by positivity
  set D : ℝ := Real.exp a * (((m + 2 : ℕ) : ℝ) / a) ^ (((m + 2 : ℕ) : ℝ))
  refine ⟨D, by positivity, fun t => ?_⟩
  set x := 1 + |t|
  have hx : 1 ≤ x := by simp only [x]; linarith [abs_nonneg t]
  have hsq : 1 + t ^ 2 ≤ x ^ 2 := by simp only [x]; nlinarith [abs_nonneg t, sq_abs t]
  have h1 := SelbergPoincareBounded.rpow_mul_exp_le (σ := ((m + 2 : ℕ) : ℝ)) (c := a) (t := x)
    (by positivity) ha (by linarith)
  rw [Real.rpow_natCast] at h1
  have hexp : Real.exp (-(Real.pi * |t| / 2)) = Real.exp a * Real.exp (-a * x) := by
    rw [← Real.exp_add]; congr 1; simp only [a, x]; ring
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [hexp, le_mul_inv_iff₀ hpos]
  calc x ^ m * (Real.exp a * Real.exp (-a * x)) * (1 + t ^ 2)
      ≤ x ^ m * (Real.exp a * Real.exp (-a * x)) * x ^ 2 := by gcongr
    _ = Real.exp a * (x ^ (m + 2) * Real.exp (-a * x)) := by rw [pow_add]; ring
    _ ≤ Real.exp a * (((m + 2 : ℕ) : ℝ) / a) ^ (((m + 2 : ℕ) : ℝ)) := by
        gcongr
    _ = D := rfl

/-- **The pairing on the critical line** decays like `(1+|t|)^K e^{−π|t|/2}`. -/
theorem exists_bound_poincEisPairing_half {s₁ : ℂ} (hs₁ : 1 < s₁.re) (μ : ℝ)
    (v w : DeckSpace N) {n : ℤ} (hn : n ≠ 0) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ t : ℝ, t ≠ 0 →
      ‖poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ K * Real.exp (-(Real.pi * |t| / 2)) := by
  obtain ⟨C, K, hC0, hC⟩ := exists_bound_poincEisPairing hs₁ μ v w hn (σ₀ := 1) hs₁
  refine ⟨C, K, hC0, fun t ht => ?_⟩
  have hcont : ContinuousAt (poincEisPairing s₁ μ v w n) (1 / 2 + t * Complex.I) := by
    refine (differentiableAt_poincEisPairing μ v w n (by simp) (fun h => ht ?_)
      (by simp; linarith)).continuousAt
    have := congrArg Complex.im h; simpa using this
  set p : ℕ → ℂ := fun k => ((1 / 2 + 1 / ((k : ℝ) + 2) : ℝ) : ℂ) + t * Complex.I
  have hp : Tendsto p atTop (𝓝 (1 / 2 + t * Complex.I)) := by
    have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      refine (this.comp (tendsto_add_atTop_nat 1)).congr fun k => ?_
      simp; ring
    have h1 := ((Complex.continuous_ofReal.tendsto 0).comp h0).const_add
      ((1 / 2 : ℂ) + t * Complex.I)
    refine h1.congr' (Eventually.of_forall fun k => ?_) |>.trans (by simp)
    simp only [Function.comp_apply, p]; push_cast; ring
  have hle : ∀ k, ‖poincEisPairing s₁ μ v w n (p k)‖ ≤
      C * (1 + |t|) ^ K * Real.exp (-(Real.pi * |t| / 2)) := fun k => by
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
    have hk1 : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [k.cast_nonneg (α := ℝ)]
    have hre : (p k).re = 1 / 2 + 1 / ((k : ℝ) + 2) := by
      simp only [p, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    have him : (p k).im = t := by
      simp only [p, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    have := hC (p k) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rwa [him] at this
  exact le_of_tendsto ((continuous_norm.tendsto _).comp (hcont.tendsto.comp hp))
    (Eventually.of_forall hle)

theorem memLp_poincEisPairing_half {s₁ : ℂ} (hs₁ : 1 < s₁.re) (μ : ℝ) (v w : DeckSpace N)
    {n : ℤ} (hn : n ≠ 0) :
    MemLp (fun t : ℝ => poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I)) 2 volume := by
  obtain ⟨C, K, hC0, hC⟩ := exists_bound_poincEisPairing_half hs₁ μ v w hn
  obtain ⟨D, hD0, hD⟩ := exists_poly_exp_le_inv_one_add_sq K
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I)) volume := by
    have hco : ContinuousOn (fun t : ℝ => poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I))
        {t : ℝ | t ≠ 0} := fun t ht => by
      refine ((differentiableAt_poincEisPairing μ v w n (by simp) (fun h => ht ?_)
        (by simp; linarith)).continuousAt.comp (f := fun t : ℝ => (1 / 2 : ℂ) + t * Complex.I)
          (by fun_prop)).continuousWithinAt
      have := congrArg Complex.im h; simpa using this
    have h := hco.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ)).compl
    have hne' : ∀ᵐ t : ℝ ∂volume, t ∈ {t : ℝ | t ≠ 0} := hne
    rwa [Measure.restrict_eq_self_of_ae_mem hne'] at h
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  refine (integrable_inv_one_add_sq.const_mul ((C * D) ^ 2)).mono'
    (hmeas.norm.pow 2) ?_
  filter_upwards [hne] with t ht
  have h1 := hC t ht
  have h2 := hD t
  have hb : ‖poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I)‖ ≤ C * D * (1 + t ^ 2)⁻¹ := by
    calc _ ≤ C * (1 + |t|) ^ K * Real.exp (-(Real.pi * |t| / 2)) := h1
      _ = C * ((1 + |t|) ^ K * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ ≤ C * (D * (1 + t ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h2 hC0
      _ = C * D * (1 + t ^ 2)⁻¹ := by ring
  have hi := inv_one_add_sq_le_one t
  have hpos : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc ‖poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I)‖ ^ 2
      ≤ (C * D * (1 + t ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = (C * D) ^ 2 * ((1 + t ^ 2)⁻¹ * (1 + t ^ 2)⁻¹) := by ring
    _ ≤ (C * D) ^ 2 * (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hpos hi) (by positivity)

/-! ## The Poincaré series is orthogonal to the constants -/

theorem inner_poincL2_onesL2 {s₁ : ℂ} (hs₁ : 1 < s₁.re) {μ : ℝ} (hμ : 0 < μ) {v : DeckSpace N}
    (hv : IsCuspEigen μ v) :
    ⟪toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v), onesL2 N⟫_ℂ = 0 := by
  rw [onesL2, inner_toDeckL2_toDeckL2, integral_inner_poincSeries_eq_deckCuspCoeff (G := onesField N)
    hs₁ hμ hv (continuous_const : Continuous (onesField N)) deckEquivariant_onesField
    memLp_onesField]
  simp [deckCuspCoeff_onesField hμ.ne' hv]

theorem inner_conjL2_onesL2 {s₂ : ℂ} (hs₂ : 1 < s₂.re) {ν : ℝ} (hν : 0 < ν) {w₂ : DeckSpace N}
    (hw₂ : IsCuspEigen (-ν) w₂) :
    ⟪toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w₂), onesL2 N⟫_ℂ = 0 := by
  rw [onesL2, inner_toDeckL2_toDeckL2, integral_inner_poincSeries_conjProfile_onesField hs₂ hν hw₂]

/-! ## Parseval against a generator -/

/-- **`⟨T̄f, T̄E⟩ = π⟨f, E⟩`** for every `f ⊥ 𝟙` and every generator `E` of the Eisenstein space. -/
theorem inner_eisTransformL2_incEisL2 (hN : 2 ≤ N) {f : DeckL2 N} (hf : ⟪f, onesL2 N⟫_ℂ = 0)
    (ψ : HeightProfile) {w : DeckSpace N} (hw : IsCuspVec w) :
    ⟪eisTransformL2 hN f, eisTransformL2 hN (incEisL2 ψ w)⟫_ℂ =
      (Real.pi : ℂ) * ⟪f, incEisL2 ψ w⟫_ℂ := by
  set E := eisSpace N
  have hg : incEisL2 ψ w ∈ E := incEisL2_mem_eisSpace ψ hw.1
  have hPg : E.orthogonalProjectionOnto (incEisL2 ψ w) = ⟨incEisL2 ψ w, hg⟩ :=
    E.orthogonalProjectionOnto_mem_subspace_eq_self ⟨incEisL2 ψ w, hg⟩
  have h := inner_eisSpace hN (E.orthogonalProjectionOnto f) ⟨incEisL2 ψ w, hg⟩
  have hl : ⟪((E.orthogonalProjectionOnto f : E) : DeckL2 N), incEisL2 ψ w⟫_ℂ =
      ⟪f, incEisL2 ψ w⟫_ℂ := by
    rw [← Submodule.starProjection_apply, Submodule.inner_starProjection_left_eq_right,
      (Submodule.starProjection_eq_self_iff).2 hg]
  have h1 : ⟪((E.orthogonalProjectionOnto f : E) : DeckL2 N), onesL2 N⟫_ℂ = 0 := by
    rw [← Submodule.starProjection_apply, Submodule.inner_starProjection_left_eq_right,
      (Submodule.starProjection_eq_self_iff).2 onesL2_mem_eisSpace, hf]
  rw [hl, h1, mul_zero, zero_mul, add_zero] at h
  have hT : eisTransformL2 hN (incEisL2 ψ w) = eisTransformE hN ⟨incEisL2 ψ w, hg⟩ := by
    rw [eisTransformL2, ContinuousLinearMap.comp_apply, hPg]
  rw [hT, show eisTransformL2 hN f = eisTransformE hN (E.orthogonalProjectionOnto f) from rfl, h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-! ## The pairing of a symmetric class with a generator transform -/

theorem memLp_hMellin_linePt (ψ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun) :
    MemLp (fun t : ℝ => hMellin ψ.toFun (linePt t)) 2 volume := by
  obtain ⟨C, hC0, hC⟩ := ψ.exists_bound_hMellin hψ (1 / 2) (1 / 2)
  have hb : ∀ s : ℝ, ‖hMellin ψ.toFun (linePt s)‖ ≤ C * (1 + s ^ 2)⁻¹ := fun s => by
    have := hC (linePt s) (by rw [linePt_re]) (by rw [linePt_re])
    rwa [linePt_im] at this
  have hc : Continuous fun t : ℝ => hMellin ψ.toFun (linePt t) :=
    ψ.differentiable_hMellin.continuous.comp (by unfold linePt; fun_prop)
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_
  refine (integrable_inv_one_add_sq.const_mul (C ^ 2)).mono' (hc.norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hi := inv_one_add_sq_le_one t
  have hpos : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc ‖hMellin ψ.toFun (linePt t)‖ ^ 2 ≤ (C * (1 + t ^ 2)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hb t) 2
    _ = C ^ 2 * ((1 + t ^ 2)⁻¹ * (1 + t ^ 2)⁻¹) := by ring
    _ ≤ C ^ 2 * (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hpos hi) (by positivity)

theorem memLp_inner_right (X : Lp (DeckSpace N) 2 (volume : Measure ℝ)) (w : DeckSpace N) :
    MemLp (fun t : ℝ => ⟪(X : ℝ → DeckSpace N) t, w⟫_ℂ) 2 volume := by
  have h := (innerSL ℂ w).comp_memLp' (Lp.memLp X)
  have hm : AEStronglyMeasurable (fun t : ℝ => ⟪(X : ℝ → DeckSpace N) t, w⟫_ℂ) volume :=
    (Lp.memLp X).1.inner aestronglyMeasurable_const
  refine h.congr_norm hm (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, innerSL_apply_apply]
  rw [← inner_conj_symm, Complex.norm_conj]

/-- **A symmetric class against a generator transform**:
`⟨X, T_ψ w⟩ = 2 ∫ ψ̂(½+it)⟨X(t), w⟩ dt` for `X` in the symmetric subspace and `w ∈ V_∞`. -/
theorem inner_symSpace_eisTransform (hN : 2 ≤ N) {X : Lp (DeckSpace N) 2 (volume : Measure ℝ)}
    (hX : X ∈ symSpace N) (ψ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun) {w : DeckSpace N}
    (hw : IsCuspVec w) :
    ⟪X, (memLp_eisTransform hN ψ hψ hw).toLp (eisTransform ψ w)⟫_ℂ =
      2 * ∫ t : ℝ, hMellin ψ.toFun (linePt t) * ⟪(X : ℝ → DeckSpace N) t, w⟫_ℂ := by
  set f : ℝ → ℂ := fun t => hMellin ψ.toFun (linePt t) * ⟪(X : ℝ → DeckSpace N) t, w⟫_ℂ with hf
  have hfi : Integrable f :=
    (memLp_hMellin_linePt ψ hψ).integrable_mul (memLp_inner_right X w) (p := 2) (q := 2)
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  rw [L2.inner_def]
  have hpt : (fun t : ℝ => ⟪(X : ℝ → DeckSpace N) t,
      ((memLp_eisTransform hN ψ hψ hw).toLp (eisTransform ψ w) : ℝ → DeckSpace N) t⟫_ℂ) =ᵐ[volume]
      fun t => f t + f (-t) := by
    filter_upwards [MemLp.coeFn_toLp (memLp_eisTransform hN ψ hψ hw), hX, hne] with t h1 h2 ht
    rw [h1, eisTransform, scatExt_of_ne (linePt_ne_half (neg_ne_zero.mpr ht)), inner_add_right,
      inner_smul_right, inner_smul_right]
    have hadj : ⟪(X : ℝ → DeckSpace N) t, scatVec (linePt (-t)) w⟫_ℂ =
        ⟪scatVec (linePt t) ((X : ℝ → DeckSpace N) t), w⟫_ℂ := by
      have := inner_scatVec_linePt_adjoint (neg_ne_zero.mpr ht) ((X : ℝ → DeckSpace N) t) w
      rw [neg_neg] at this
      exact this.symm
    rw [hadj, ← h2.2]
  rw [integral_congr_ae hpt, integral_add hfi (hfi.comp_neg), integral_neg_eq_self]
  ring

/-! ## The identification -/

/-- **Identification from the line pairings**: if `F ⊥ 𝟙` and, for every smooth profile `ψ`,
`⟨F, E(·|ψ,w)⟩ = π⁻¹ ∫ ψ̂(σ+it)Φ(σ+it) dt` on one line `½ < σ < Re s₁`, with
`Φ = poincEisPairing s₁ μ v w n` (`n ≠ 0`), then `2⟨T̄F(t), w⟩ = Φ(½+it)` for almost every `t`. -/
theorem eisTransformL2_inner_of_line (hN : 2 ≤ N) {F : DeckL2 N} (hF : ⟪F, onesL2 N⟫_ℂ = 0)
    {s₁ : ℂ} (hs₁ : 1 < s₁.re) (μ : ℝ) (v : DeckSpace N) {n : ℤ} (hn : n ≠ 0) {w : DeckSpace N}
    (hw : IsCuspVec w) {σ : ℝ} (hσ : 1 / 2 < σ) (hσs : σ < s₁.re)
    (hline : ∀ ψ : SmoothHeightProfile, ⟪F, incEisL2 ψ.toHeightProfile w⟫_ℂ =
      (Real.pi : ℂ)⁻¹ * ∫ t : ℝ, hMellin ψ.toFun ((σ : ℂ) + t * Complex.I) *
        poincEisPairing s₁ μ v w n ((σ : ℂ) + t * Complex.I)) :
    ∀ᵐ t : ℝ ∂volume, 2 * ⟪(eisTransformL2 hN F : ℝ → DeckSpace N) t, w⟫_ℂ =
      poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I) := by
  set X := eisTransformL2 hN F
  have hX : X ∈ symSpace N := eisTransformL2_mem_symSpace hN F
  set Φ : ℝ → ℂ := fun t => poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I)
  have hΦ : MemLp Φ 2 volume := memLp_poincEisPairing_half hs₁ μ v w hn
  set B : ℝ → ℂ := fun t => 2 * ⟪(X : ℝ → DeckSpace N) t, w⟫_ℂ - Φ t
  have hB : MemLp B 2 volume := ((memLp_inner_right X w).const_mul 2).sub hΦ
  have hB0 : B =ᵐ[volume] 0 := by
    refine SmoothHeightProfile.ae_eq_zero_of_integral_hMellin_ofTest hB fun g hgc hgs => ?_
    set ψ := SmoothHeightProfile.ofTest g hgc hgs
    have hψ2 : ContDiff ℝ 2 ψ.toFun := ψ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
    -- the two sides of `⟨T̄F, T̄E⟩ = π⟨F, E⟩`
    have ha := inner_eisTransformL2_incEisL2 hN hF ψ.toHeightProfile hw
    rw [eisTransformL2_incEisL2 hN ψ.toHeightProfile hψ2 hw,
      inner_symSpace_eisTransform hN hX ψ.toHeightProfile hψ2 hw, hline ψ,
      integral_line_eq_integral_half hs₁ μ v w hn ψ hσ hσs] at ha
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [← mul_assoc, mul_inv_cancel₀ hπ, one_mul] at ha
    -- integrability of the two pieces
    have hlp : ∀ t : ℝ, linePt t = 1 / 2 + t * Complex.I := fun t => by
      simp [_root_.RHTower.linePt]
    have hi1 : Integrable fun t : ℝ => hMellin ψ.toFun (linePt t) *
        ⟪(X : ℝ → DeckSpace N) t, w⟫_ℂ :=
      (memLp_hMellin_linePt ψ.toHeightProfile hψ2).integrable_mul (memLp_inner_right X w)
        (p := 2) (q := 2)
    have hi2 : Integrable fun t : ℝ => hMellin ψ.toFun (linePt t) *
        poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I) :=
      (memLp_hMellin_linePt ψ.toHeightProfile hψ2).integrable_mul hΦ (p := 2) (q := 2)
    simp only [hlp] at ha hi1 hi2
    have key : ∫ t : ℝ, hMellin ψ.toFun (1 / 2 + t * Complex.I) * B t =
        2 * (∫ t : ℝ, hMellin ψ.toFun (1 / 2 + t * Complex.I) * ⟪(X : ℝ → DeckSpace N) t, w⟫_ℂ) -
          ∫ t : ℝ, hMellin ψ.toFun (1 / 2 + t * Complex.I) *
            poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I) := by
      rw [← integral_const_mul, ← integral_sub (hi1.const_mul 2) hi2]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      show hMellin ψ.toFun (1 / 2 + t * Complex.I) * (2 * ⟪(X : ℝ → DeckSpace N) t, w⟫_ℂ -
        poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I)) = _
      ring
    rw [key, ha, sub_self]
  filter_upwards [hB0] with t ht
  simp only [B, Pi.zero_apply, sub_eq_zero] at ht
  exact ht

theorem int_ne_zero_of_mul_eq {μ : ℝ} (hμ : μ ≠ 0) {n : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n) :
    n ≠ 0 := by
  rintro rfl
  have h0 : μ * ((N + 1 : ℕ) : ℝ) = 0 := by exact_mod_cast hn
  rcases mul_eq_zero.1 h0 with h | h
  · exact hμ h
  · exact (Nat.cast_add_one_pos (α := ℝ) N).ne' (by exact_mod_cast h)

/-- **The Eisenstein transform of a Poincaré series**: `2⟨T̄U(t), w⟩ = Φ_w(½+it)` for almost every `t`,
for every `w ∈ V_∞`. -/
theorem eisTransformL2_poinc_inner (hN : 2 ≤ N) {s₁ : ℂ} (hs₁ : 1 < s₁.re) {μ : ℝ} (hμ : 0 < μ)
    {v : DeckSpace N} (hv : IsCuspEigen μ v) {n : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n)
    {w : DeckSpace N} (hw : IsCuspVec w) :
    ∀ᵐ t : ℝ ∂volume, 2 * ⟪(eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v)) :
        ℝ → DeckSpace N) t, w⟫_ℂ = poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I) :=
  eisTransformL2_inner_of_line hN (inner_poincL2_onesL2 hs₁ hμ hv) hs₁ μ v
    (int_ne_zero_of_mul_eq hμ.ne' hn) hw (σ := (1 + s₁.re) / 2) (by linarith) (by linarith)
    fun ψ => inner_poincL2_incEisL2_eq_integral_pairing hN hs₁ hμ hv hn ψ.toHeightProfile
      (ψ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hw (by linarith) (by linarith)

/-- **The Eisenstein transform of the conjugate series**: for `P = P(·|h̄_{s₂,ν}, w₂)`,
`2⟨T̄P(t), w⟩ = Φ_w(½+it)` for almost every `t`, with the explicit pairing at `(s̄₂, ν)` and the
frequency `−ν(N+1) = m`. -/
theorem eisTransformL2_conj_inner (hN : 2 ≤ N) {s₂ : ℂ} (hs₂ : 1 < s₂.re) {ν : ℝ} (hν : 0 < ν)
    {w₂ : DeckSpace N} (hw₂ : IsCuspEigen (-ν) w₂) {m : ℤ} (hm : -ν * ((N + 1 : ℕ) : ℝ) = m)
    {w : DeckSpace N} (hw : IsCuspVec w) :
    ∀ᵐ t : ℝ ∂volume,
      2 * ⟪(eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w₂)) :
        ℝ → DeckSpace N) t, w⟫_ℂ = poincEisPairing (conj s₂) ν w₂ w m (1 / 2 + t * Complex.I) := by
  have hre : (conj s₂).re = s₂.re := Complex.conj_re s₂
  exact eisTransformL2_inner_of_line hN (inner_conjL2_onesL2 hs₂ hν hw₂) (by rw [hre]; exact hs₂) ν
    w₂ (int_ne_zero_of_mul_eq (neg_ne_zero.mpr hν.ne') hm) hw (σ := (1 + s₂.re) / 2)
    (by linarith) (by rw [hre]; linarith)
    fun ψ => inner_conjL2_incEisL2_eq_integral_pairing hN hs₂ hν hw₂ hm ψ.toHeightProfile
      (ψ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hw (by linarith) (by linarith)

end

end GaloisForLFunctions.RHTower.DeckPointPair
