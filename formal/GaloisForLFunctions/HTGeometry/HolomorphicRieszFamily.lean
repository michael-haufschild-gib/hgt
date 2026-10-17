import GaloisForLFunctions.HTGeometry.QuasiCompactSpectralCircle
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Holomorphic families of Riesz projections and their finite-rank spectral data

Let `s ↦ T(s)` be a holomorphic family of bounded operators on a complex Banach space and let the
circle `|z| = ρ` lie in the resolvent set of every `T(s)`, `s ∈ U`.

* `hasDerivAt_resolvent_family`: `∂_s R_{T(s)}(z) = R T'(s) R`.
* `differentiableOn_rieszProjection_family`: `s ↦ P(s) = (2πi)⁻¹ ∮ R_{T(s)}(z) dz` is holomorphic;
  the integrand is differentiated under the integral sign, with the resolvent bound `2Λ`
  propagated from one point by perturbation.
* `differentiableOn_finiteRankTrace_outer`, `differentiableOn_finiteRankDet_outer`: when the outer
  ranges `ran(1 − P(s))` are finite dimensional, `s ↦ tr(T(s)ⁿ(1 − P(s)))` and
  `s ↦ det(1 − T(s)(1 − P(s)))` are holomorphic.  Near `s₀`, Kato's transformation
  `A(s) = P(s)P(s₀) + (1 − P(s))(1 − P(s₀))` is invertible and conjugates the outer part at `s`
  to an operator on the fixed space `ran(1 − P(s₀))`, where trace and determinant are polynomial in
  the matrix entries.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Filter Topology FiniteRank Module

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **The resolvent is holomorphic in the operator**: `∂_s R_{T(s)}(z) = R T'(s) R`. -/
theorem hasDerivAt_resolvent_family {T : ℂ → E →L[ℂ] E} {T' : E →L[ℂ] E} {s : ℂ}
    (hT : HasDerivAt T T' s) {z : ℂ} (hz : z ∈ resolventSet ℂ (T s)) :
    HasDerivAt (fun s => resolvent (T s) z) (resolvent (T s) z * T' * resolvent (T s) z) s := by
  obtain ⟨u, hu⟩ := (hz : IsUnit (algebraMap ℂ (E →L[ℂ] E) z - T s))
  have hg : HasDerivAt (fun s => algebraMap ℂ (E →L[ℂ] E) z - T s) (0 - T') s :=
    (hasDerivAt_const s _).sub hT
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℂ) u
  rw [hu] at hinv
  have hcomp := hinv.comp_hasDerivAt s hg
  have hval : (-((ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E)) ↑u⁻¹) ↑u⁻¹) (0 - T')
      = resolvent (T s) z * T' * resolvent (T s) z := by
    have hR : resolvent (T s) z = ↑u⁻¹ := by
      rw [resolvent, ← hu, Ring.inverse_unit]
    rw [hR, neg_apply, ContinuousLinearMap.mulLeftRight_apply, zero_sub,
      mul_neg, neg_mul, neg_neg]
  exact hcomp.congr_deriv hval

/-- **A holomorphic family of operators has a holomorphic family of Riesz projections.** -/
theorem differentiableOn_rieszProjection_family {T : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U)
    (hT : DifferentiableOn ℂ T U) {ρ : ℝ} (hρ : 0 < ρ)
    (hres : ∀ s ∈ U, ∀ z ∈ sphere (0 : ℂ) ρ, z ∈ resolventSet ℂ (T s)) :
    DifferentiableOn ℂ (fun s => rieszProjection (T s) 0 ρ) U := by
  intro s₀ hs₀
  refine DifferentiableAt.differentiableWithinAt ?_
  have hTa : AnalyticOnNhd ℂ T U := hT.analyticOnNhd hU
  have hT'c : ContinuousAt (deriv T) s₀ := (hTa.deriv s₀ hs₀).continuousAt
  have hTc : ContinuousAt T s₀ := (hTa s₀ hs₀).continuousAt
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_norm_resolvent_le_on_sphere (T s₀) (hres s₀ hs₀)
  have hev1 : ∀ᶠ s in 𝓝 s₀, ‖T s - T s₀‖ < (2 * Λ)⁻¹ := by
    have := (hTc.sub continuousAt_const).norm (f := fun s => T s - T s₀)
    exact this.eventually (gt_mem_nhds (show ‖T s₀ - T s₀‖ < (2 * Λ)⁻¹ by
      rw [sub_self, norm_zero]; positivity))
  have hev2 : ∀ᶠ s in 𝓝 s₀, ‖deriv T s‖ < ‖deriv T s₀‖ + 1 :=
    hT'c.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hev1.and (hev2.and (hU.mem_nhds hs₀)))
  set C' : ℝ := ‖deriv T s₀‖ + 1
  have hRb : ∀ s ∈ ball s₀ δ, ∀ z ∈ sphere (0 : ℂ) ρ, ‖resolvent (T s) z‖ ≤ 2 * Λ := by
    intro s hs z hz
    refine (resolvent_bound_of_perturb (T s₀) (T s) (hres s₀ hs₀) hΛ ?_).2 z hz
    have h1 := (hball s hs).1
    have : ‖T s - T s₀‖ * (2 * Λ) < 1 := by
      calc ‖T s - T s₀‖ * (2 * Λ) < (2 * Λ)⁻¹ * (2 * Λ) :=
            mul_lt_mul_of_pos_right h1 (by positivity)
        _ = 1 := inv_mul_cancel₀ (by positivity)
    nlinarith
  have hmem : ∀ θ, circleMap 0 ρ θ ∈ sphere (0 : ℂ) ρ := fun θ => circleMap_mem_sphere 0 hρ.le θ
  have hresCont : ∀ s ∈ U, Continuous fun θ => resolvent (T s) (circleMap 0 ρ θ) := by
    intro s hs
    have hco : ContinuousOn (resolvent (T s)) (sphere (0 : ℂ) ρ) := fun z hz =>
      ((spectrum.hasDerivAt_resolvent_const_left (hres s hs z hz)).continuousAt).continuousWithinAt
    exact hco.comp_continuous (continuous_circleMap 0 ρ) hmem
  set F : ℂ → ℝ → E →L[ℂ] E := fun s θ =>
    deriv (circleMap 0 ρ) θ • resolvent (T s) (circleMap 0 ρ θ)
  set F' : ℂ → ℝ → E →L[ℂ] E := fun s θ => deriv (circleMap 0 ρ) θ •
    (resolvent (T s) (circleMap 0 ρ θ) * deriv T s * resolvent (T s) (circleMap 0 ρ θ))
  have hdc : Continuous fun θ => deriv (circleMap 0 ρ) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 ρ).mul continuous_const
  have hFc : ∀ s ∈ U, Continuous (F s) := fun s hs => hdc.smul (hresCont s hs)
  have hF'c : Continuous (F' s₀) := hdc.smul (((hresCont s₀ hs₀).mul continuous_const).mul
    (hresCont s₀ hs₀))
  have hderiv_norm : ∀ θ, ‖deriv (circleMap 0 ρ) θ‖ = ρ := by
    intro θ
    rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hρ]
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * Real.pi)
    (bound := fun _ => ρ * (2 * Λ * C' * (2 * Λ))) (F := F) (F' := F') (x₀ := s₀)
    (ball_mem_nhds s₀ hδ)
    (Filter.eventually_of_mem (hU.mem_nhds hs₀) fun s hs => (hFc s hs).aestronglyMeasurable)
    ((hFc s₀ hs₀).intervalIntegrable _ _)
    hF'c.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun θ _ s hs => ?_) intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ s hs => ?_)
  · have hP : (fun s => rieszProjection (T s) 0 ρ) =
        fun s => (2 * Real.pi * Complex.I)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, F s θ := by
      funext s
      rfl
    rw [hP]
    exact (key.2.const_smul ((2 * Real.pi * Complex.I)⁻¹ : ℂ)).differentiableAt
  · have hsU := hs
    rw [norm_smul, hderiv_norm]
    refine mul_le_mul_of_nonneg_left ?_ hρ.le
    have hR := hRb s hs _ (hmem θ)
    calc ‖resolvent (T s) (circleMap 0 ρ θ) * deriv T s * resolvent (T s) (circleMap 0 ρ θ)‖
        ≤ ‖resolvent (T s) (circleMap 0 ρ θ)‖ * ‖deriv T s‖ *
          ‖resolvent (T s) (circleMap 0 ρ θ)‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 2 * Λ * C' * (2 * Λ) := by
          have hd := (hball s hs).2.1
          gcongr
  · have hsU : s ∈ U := (hball s hs).2.2
    have hTd : HasDerivAt T (deriv T s) s :=
      ((hT s hsU).differentiableAt (hU.mem_nhds hsU)).hasDerivAt
    exact (hasDerivAt_resolvent_family hTd (hres s hsU _ (hmem θ))).const_smul
      (deriv (circleMap 0 ρ) θ)

/-! ## Compression to a fixed finite-dimensional subspace -/

section Compress

variable (W : Submodule ℂ E) (Q : E →L[ℂ] E) (hQ : ∀ v, Q v ∈ W)

/-- The compression `Y ↦ Q Y|_W`, a continuous linear map into the operators on `W`. -/
def compressCLM : (E →L[ℂ] E) →L[ℂ] (W →L[ℂ] W) :=
  (ContinuousLinearMap.compL ℂ W E W (Q.codRestrict W hQ)).comp
    ((ContinuousLinearMap.compL ℂ W E E).flip W.subtypeL)

omit [CompleteSpace E] in
theorem compressCLM_apply_coe (Y : E →L[ℂ] E) (w : W) :
    ((compressCLM W Q hQ Y w : W) : E) = Q (Y w) := rfl

omit [CompleteSpace E] in
/-- On operators with range in `W`, the compression by a projection fixing `W` is the
restriction. -/
theorem compressCLM_eq_restrictEnd (hfix : ∀ w ∈ W, Q w = w) (Y : E →L[ℂ] E)
    (hY : ∀ v, Y v ∈ W) :
    ((compressCLM W Q hQ Y : W →L[ℂ] W) : W →ₗ[ℂ] W) = restrictEnd Y W (fun v _ => hY v) := by
  ext w
  rw [ContinuousLinearMap.coe_coe, compressCLM_apply_coe, coe_restrictEnd_apply, hfix _ (hY w)]

variable [FiniteDimensional ℂ W]

omit [CompleteSpace E] in
/-- The trace of the compression is holomorphic in a holomorphic family. -/
theorem differentiableAt_trace_compress {Y : ℂ → E →L[ℂ] E} {s : ℂ}
    (hY : DifferentiableAt ℂ Y s) :
    DifferentiableAt ℂ
      (fun s => LinearMap.trace ℂ W ((compressCLM W Q hQ (Y s) : W →L[ℂ] W) : W →ₗ[ℂ] W)) s := by
  set L : (W →L[ℂ] W) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℂ W).comp (ContinuousLinearMap.coeLM ℂ))
  have h : (fun s => LinearMap.trace ℂ W ((compressCLM W Q hQ (Y s) : W →L[ℂ] W) : W →ₗ[ℂ] W))
      = fun s => L (compressCLM W Q hQ (Y s)) := rfl
  rw [h]
  exact (L.comp (compressCLM W Q hQ)).differentiableAt.comp s hY

omit [CompleteSpace E] in
/-- The determinant `det(1 − ·)` of the compression is holomorphic in a holomorphic family. -/
theorem differentiableAt_det_one_sub_compress {Y : ℂ → E →L[ℂ] E} {s : ℂ}
    (hY : DifferentiableAt ℂ Y s) :
    DifferentiableAt ℂ (fun s => LinearMap.det
      (1 - ((compressCLM W Q hQ (Y s) : W →L[ℂ] W) : W →ₗ[ℂ] W))) s := by
  set b := Module.finBasis ℂ W
  set M : ℂ → Matrix (Fin (finrank ℂ W)) (Fin (finrank ℂ W)) ℂ := fun s =>
    LinearMap.toMatrix b b ((compressCLM W Q hQ (Y s) : W →L[ℂ] W) : W →ₗ[ℂ] W)
  have hent : ∀ i j, DifferentiableAt ℂ (fun s => M s i j) s := by
    intro i j
    set Lij : (W →L[ℂ] W) →L[ℂ] ℂ :=
      (LinearMap.toContinuousLinearMap (b.coord i)).comp (ContinuousLinearMap.apply ℂ W (b j))
    have hfun : (fun s => M s i j) = fun s => Lij (compressCLM W Q hQ (Y s)) := by
      funext s
      simp [M, Lij, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
    rw [hfun]
    exact (Lij.comp (compressCLM W Q hQ)).differentiableAt.comp s hY
  have hrw : (fun s => LinearMap.det (1 - ((compressCLM W Q hQ (Y s) : W →L[ℂ] W) : W →ₗ[ℂ] W)))
      = fun s => ∑ σ : Equiv.Perm (Fin (finrank ℂ W)), (Equiv.Perm.sign σ : ℂ) *
        ∏ i, ((if σ i = i then (1 : ℂ) else 0) - M s (σ i) i) := by
    funext s
    rw [← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
    simp [Matrix.one_apply, M]
  rw [hrw]
  refine DifferentiableAt.fun_sum fun σ _ => (differentiableAt_const _).mul ?_
  exact DifferentiableAt.fun_finsetProd fun i _ => (differentiableAt_const _).sub (hent _ _)

end Compress

/-! ## Kato's transformation function -/

/-- **Kato's intertwining identity**: for idempotents `P`, `P₀`, the element
`A = P P₀ + (1 − P)(1 − P₀)` satisfies `(1 − P) A = A (1 − P₀)`. -/
theorem kato_intertwine {R : Type*} [Ring R] {P P₀ : R} (hP : P * P = P) (hP₀ : P₀ * P₀ = P₀) :
    (1 - P) * (P * P₀ + (1 - P) * (1 - P₀)) = (P * P₀ + (1 - P) * (1 - P₀)) * (1 - P₀) := by
  have h1 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have h2 : P₀ * (1 - P₀) = 0 := by rw [mul_sub, mul_one, hP₀, sub_self]
  have h3 : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hP, sub_self, sub_zero]
  have h4 : (1 - P₀) * (1 - P₀) = 1 - P₀ := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hP₀, sub_self, sub_zero]
  calc (1 - P) * (P * P₀ + (1 - P) * (1 - P₀))
      = ((1 - P) * P) * P₀ + ((1 - P) * (1 - P)) * (1 - P₀) := by noncomm_ring
    _ = (1 - P) * (1 - P₀) := by rw [h1, h3, zero_mul, zero_add]
    _ = P * (P₀ * (1 - P₀)) + (1 - P) * ((1 - P₀) * (1 - P₀)) := by
        rw [h2, h4, mul_zero, zero_add]
    _ = (P * P₀ + (1 - P) * (1 - P₀)) * (1 - P₀) := by noncomm_ring

/-- **Holomorphy of the outer finite-rank trace and determinant.**  If `s ↦ P(s)` is a holomorphic
family of idempotents, `ran(1 − P(s₀))` is finite dimensional and `Y(s)` is a holomorphic family
commuting with `P(s)`, then `s ↦ tr(Y(s)(1 − P(s)))` and `s ↦ det(1 − Y(s)(1 − P(s)))` are
holomorphic at `s₀`. -/
theorem differentiableAt_finiteRank_outer {P Y : ℂ → E →L[ℂ] E} {s₀ : ℂ}
    (hPd : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ P s) (hPP : ∀ᶠ s in 𝓝 s₀, P s * P s = P s)
    (hYd : DifferentiableAt ℂ Y s₀) (hYP : ∀ᶠ s in 𝓝 s₀, Y s * P s = P s * Y s)
    [FiniteDimensional ℂ (opRange (1 - P s₀))] :
    DifferentiableAt ℂ (fun s => finiteRankTrace (Y s * (1 - P s))) s₀ ∧
      DifferentiableAt ℂ (fun s => finiteRankDet (Y s * (1 - P s))) s₀ := by
  set Q₀ : E →L[ℂ] E := 1 - P s₀
  set W₀ : Submodule ℂ E := opRange Q₀
  have hP₀ : P s₀ * P s₀ = P s₀ := hPP.self_of_nhds
  have hQ₀ : Q₀ * Q₀ = Q₀ := by
    simp only [Q₀, sub_mul, mul_sub, one_mul, mul_one, hP₀, sub_self, sub_zero]
  have hQW : ∀ v, Q₀ v ∈ W₀ := mem_opRange Q₀
  have hfix : ∀ w ∈ W₀, Q₀ w = w := by
    rintro _ ⟨v, rfl⟩
    show (Q₀ * Q₀) v = Q₀ v
    rw [hQ₀]
  set A : ℂ → E →L[ℂ] E := fun s => P s * P s₀ + (1 - P s) * Q₀
  have hA0 : A s₀ = 1 := by
    show P s₀ * P s₀ + (1 - P s₀) * (1 - P s₀) = 1
    rw [hP₀, sub_mul, one_mul, mul_sub, mul_one, hP₀, sub_self, sub_zero, add_sub_cancel]
  have hAd : DifferentiableAt ℂ A s₀ :=
    (hPd.self_of_nhds.mul_const _).add
      ((differentiableAt_const _).sub hPd.self_of_nhds |>.mul_const _)
  have hAc : ContinuousAt A s₀ := hAd.continuousAt
  have hAunit : ∀ᶠ s in 𝓝 s₀, IsUnit (A s) := by
    have hev : ∀ᶠ s in 𝓝 s₀, ‖A s - 1‖ < 1 := by
      have := (hAc.sub continuousAt_const).norm (f := fun s => A s - 1)
      have h0 : ‖A s₀ - 1‖ < 1 := by rw [hA0, sub_self, norm_zero]; exact one_pos
      exact this.eventually (gt_mem_nhds h0)
    filter_upwards [hev] with s hs
    have := isUnit_one_sub_of_norm_lt_one (x := 1 - A s) (by rwa [norm_sub_rev])
    simpa using this
  set Ainv : ℂ → E →L[ℂ] E := fun s => Ring.inverse (A s)
  have hAinvd : DifferentiableAt ℂ Ainv s₀ := by
    have hu : IsUnit (A s₀) := by rw [hA0]; exact isUnit_one
    exact (differentiableAt_inverse hu).comp s₀ hAd
  set Z : ℂ → E →L[ℂ] E := fun s => Ainv s * Y s * A s * Q₀
  have hZd : DifferentiableAt ℂ Z s₀ :=
    ((hAinvd.mul hYd).mul hAd).mul_const _
  -- the local identities
  have hloc : ∀ᶠ s in 𝓝 s₀, (∀ v, Z s v ∈ W₀) ∧
      ∃ u : (E →L[ℂ] E)ˣ, Y s * (1 - P s) = (u : E →L[ℂ] E) * Z s * (↑(u⁻¹) : E →L[ℂ] E) := by
    filter_upwards [hAunit, hPP, hYP] with s hu hPs hYs
    obtain ⟨u, hu'⟩ := hu
    have hinv : Ainv s = ↑(u⁻¹) := by simp only [Ainv, ← hu', Ring.inverse_unit]
    have hK : (1 - P s) * A s = A s * Q₀ := kato_intertwine hPs hP₀
    have hAi : Ainv s * A s = 1 := by rw [hinv, ← hu', Units.inv_mul]
    have hAi' : A s * Ainv s = 1 := by rw [hinv, ← hu', Units.mul_inv]
    have hK' : Ainv s * (1 - P s) = Q₀ * Ainv s := by
      calc Ainv s * (1 - P s) = Ainv s * (1 - P s) * (A s * Ainv s) := by rw [hAi', mul_one]
        _ = Ainv s * ((1 - P s) * A s) * Ainv s := by noncomm_ring
        _ = Ainv s * (A s * Q₀) * Ainv s := by rw [hK]
        _ = (Ainv s * A s) * Q₀ * Ainv s := by noncomm_ring
        _ = Q₀ * Ainv s := by rw [hAi, one_mul]
    have hYQ : Y s * (1 - P s) = (1 - P s) * Y s := by
      rw [mul_sub, sub_mul, mul_one, one_mul, hYs]
    refine ⟨fun v => ?_, u, ?_⟩
    · have hZ : Z s = Q₀ * (Ainv s * Y s * A s) := by
        calc Z s = Ainv s * Y s * (A s * Q₀) := by simp only [Z, mul_assoc]
          _ = Ainv s * Y s * ((1 - P s) * A s) := by rw [hK]
          _ = Ainv s * (Y s * (1 - P s)) * A s := by noncomm_ring
          _ = Ainv s * ((1 - P s) * Y s) * A s := by rw [hYQ]
          _ = (Ainv s * (1 - P s)) * Y s * A s := by noncomm_ring
          _ = Q₀ * (Ainv s * Y s * A s) := by rw [hK']; noncomm_ring
      rw [hZ]
      exact hQW _
    · rw [hu', ← hinv]
      calc Y s * (1 - P s) = Y s * ((1 - P s) * (A s * Ainv s)) := by rw [hAi', mul_one]
        _ = Y s * ((1 - P s) * A s) * Ainv s := by noncomm_ring
        _ = Y s * (A s * Q₀) * Ainv s := by rw [hK]
        _ = (A s * Ainv s) * (Y s * (A s * Q₀)) * Ainv s := by rw [hAi', one_mul]
        _ = A s * Z s * Ainv s := by simp only [Z]; noncomm_ring
  have htrace : (fun s => finiteRankTrace (Y s * (1 - P s))) =ᶠ[𝓝 s₀]
      fun s => LinearMap.trace ℂ W₀
        ((compressCLM W₀ Q₀ hQW (Z s) : W₀ →L[ℂ] W₀) : W₀ →ₗ[ℂ] W₀) := by
    filter_upwards [hloc] with s hs
    obtain ⟨hZW, u, hu⟩ := hs
    haveI : FiniteDimensional ℂ (opRange (Z s)) :=
      Submodule.finiteDimensional_of_le (opRange_le (Z s) hZW)
    rw [hu, finiteRankTrace_conj, finiteRankTrace_eq_trace_restrict (Z s) W₀ hZW,
      compressCLM_eq_restrictEnd W₀ Q₀ hQW hfix (Z s) hZW]
  have hdet : (fun s => finiteRankDet (Y s * (1 - P s))) =ᶠ[𝓝 s₀]
      fun s => LinearMap.det (1 - ((compressCLM W₀ Q₀ hQW (Z s) : W₀ →L[ℂ] W₀) : W₀ →ₗ[ℂ] W₀)) := by
    filter_upwards [hloc] with s hs
    obtain ⟨hZW, u, hu⟩ := hs
    haveI : FiniteDimensional ℂ (opRange (Z s)) :=
      Submodule.finiteDimensional_of_le (opRange_le (Z s) hZW)
    rw [hu, finiteRankDet_conj, finiteRankDet_eq_det_restrict (Z s) W₀ hZW,
      compressCLM_eq_restrictEnd W₀ Q₀ hQW hfix (Z s) hZW]
  exact ⟨(differentiableAt_trace_compress W₀ Q₀ hQW hZd).congr_of_eventuallyEq htrace,
    (differentiableAt_det_one_sub_compress W₀ Q₀ hQW hZd).congr_of_eventuallyEq hdet⟩

end

end GaloisForLFunctions.HTGeometry
