import GaloisForLFunctions.RHTower.CCMArchimedeanSoninGenericTraceless

/-!
# The Sonin generic trace is a Toeplitz form

Let `ϑ_u = ϑ(e^u)` be the scaling unitary of `L²(ℝ)^ev` and `G_Λ = 1 - P_Λ - P̂_Λ - S_Λ` the
generic part of the cutoff pair.  Since `G_Λ` is trace class, its scaling trace

`τ_Λ(u) = Tr(G_Λ ϑ_u)`

is a bounded continuous function, and for every trace-class `T` and logarithmic kernel `g`,
`Tr(T ϑ(g)) = ∫ g(u) Tr(T ϑ_u) du`.  With `ϑ(g)†ϑ(g) = ϑ(g★ ⋆ g)` this turns the generic trace of
a Gram test into a Toeplitz form:

`Tr(ϑ(g) G_Λ ϑ(g)†) = ∫∫ conj (g s) g t τ_Λ(t - s) ds dt`.

The kernel is real and even (`F G_Λ F = G_Λ`, `F ϑ_u F = ϑ_{-u}`, `G_Λ = G_Λ†`), bounded by
`‖G_Λ‖₁`, and vanishes at the origin because `Tr G_Λ = 0`.  Hence the Connes--Consani Sonin-trace
domination at cutoff one is the positivity of the Toeplitz form with kernel `τ_1` on the test
class.
-/

noncomputable section

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

open MeasureTheory ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate SchwartzMap

namespace RHTower

/-- `ϑ(g)` for a Schwartz logarithmic kernel. -/
local notation "ϑ[" g "]" => ccmIntegratedScaling (ccmSchwartzLogKernel g)

/-! ## The scaling unitaries -/

/-- The scaling unitary `ϑ(e^u)`, `f ↦ e^{-u/2} f(e^{-u} ·)`. -/
def ccmLogDilation (u : ℝ) : evenSubspace →L[ℂ] evenSubspace :=
  (evenDilationUnitary (Real.exp (-u)) (Real.exp_pos (-u)) : evenSubspace →L[ℂ] evenSubspace)

@[simp] theorem ccmLogDilation_apply (u : ℝ) (f : evenSubspace) :
    ccmLogDilation u f = ccmLogDilationOrbit f u := rfl

theorem ccmLogDilationOrbit_zero (f : evenSubspace) : ccmLogDilationOrbit f 0 = f := by
  have h := ccmLogDilationOrbit_add f 0 0
  rw [add_zero] at h
  exact (evenDilationUnitary (Real.exp (-0)) (Real.exp_pos (-0))).injective h

theorem ccmLogDilation_zero : ccmLogDilation 0 = ContinuousLinearMap.id ℂ evenSubspace :=
  ContinuousLinearMap.ext fun f => ccmLogDilationOrbit_zero f

theorem ccmLogDilation_comp (u v : ℝ) :
    ccmLogDilation u ∘L ccmLogDilation v = ccmLogDilation (u + v) :=
  ContinuousLinearMap.ext fun f => ccmLogDilationOrbit_add f u v

theorem norm_ccmLogDilation_le (u : ℝ) : ‖ccmLogDilation u‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul, ccmLogDilation_apply, norm_ccmLogDilationOrbit]

/-- `ϑ_u† = ϑ_{-u}`. -/
theorem adjoint_ccmLogDilation (u : ℝ) :
    ContinuousLinearMap.adjoint (ccmLogDilation u) = ccmLogDilation (-u) := by
  set e := evenDilationUnitary (Real.exp (-u)) (Real.exp_pos (-u))
  have h := LinearIsometryEquiv.adjoint_eq_symm e
  change ContinuousLinearMap.adjoint (ccmLogDilation u) = _ at h
  rw [h]
  refine ContinuousLinearMap.ext fun f => e.injective ?_
  change e (e.symm f) = ccmLogDilationOrbit (ccmLogDilationOrbit f (-u)) u
  rw [LinearIsometryEquiv.apply_symm_apply, ccmLogDilationOrbit_add, add_neg_cancel,
    ccmLogDilationOrbit_zero]

/-- `F ϑ_u F = ϑ_{-u}`. -/
theorem evenFourierTransform_conj_ccmLogDilation (u : ℝ) :
    evenFourierTransform * ccmLogDilation u * evenFourierTransform = ccmLogDilation (-u) := by
  refine ContinuousLinearMap.ext fun f => ?_
  change evenFourierTransform (ccmLogDilationOrbit (evenFourierTransform f) u) =
    ccmLogDilationOrbit f (-u)
  rw [evenFourierTransform_ccmLogDilationOrbit, evenFourierTransform_involutive]

/-! ## Traces against integrated scaling -/

/-- For `T = S U` with `S`, `U` Hilbert--Schmidt, `Tr(T X) = ∑ᵢ ⟨U† bᵢ, X S bᵢ⟩`. -/
theorem opTrace_comp_comp_eq_tsum {S U : evenSubspace →L[ℂ] evenSubspace}
    (hS : IsHilbertSchmidt S) (hU : IsHilbertSchmidt U) (X : evenSubspace →L[ℂ] evenSubspace) :
    opTrace ((S ∘L U) ∘L X) = ∑' i, ⟪ContinuousLinearMap.adjoint U (hsBasis ℂ evenSubspace i),
      X (S (hsBasis ℂ evenSubspace i))⟫_ℂ := by
  rw [ContinuousLinearMap.comp_assoc, opTrace_comp_comm hS (hU.comp_right X),
    opTrace_comp_eq_tsum_basis (hU.comp_right X) hS (hsBasis ℂ evenSubspace)]
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- The diagonal weights `‖U† bᵢ‖ ‖S bᵢ‖` of a Hilbert--Schmidt pair are summable. -/
theorem summable_norm_adjoint_mul_norm {S U : evenSubspace →L[ℂ] evenSubspace}
    (hS : IsHilbertSchmidt S) (hU : IsHilbertSchmidt U) :
    Summable fun i => ‖ContinuousLinearMap.adjoint U (hsBasis ℂ evenSubspace i)‖ *
      ‖S (hsBasis ℂ evenSubspace i)‖ := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (((hU.adjoint.summable (hsBasis ℂ evenSubspace)).add
      (hS.summable (hsBasis ℂ evenSubspace))).div_const 2)
  have := two_mul_le_add_sq ‖ContinuousLinearMap.adjoint U (hsBasis ℂ evenSubspace i)‖
    ‖S (hsBasis ℂ evenSubspace i)‖
  linarith

/-- **Trace against `ϑ(g)`.**  For trace-class `T`, `Tr(T ϑ(g)) = ∫ g(u) Tr(T ϑ_u) du`.  With
`T = S U` a Hilbert--Schmidt factorization, both sides are `∑ᵢ ⟨U† bᵢ, · S bᵢ⟩`, and the bound
`|⟨U† bᵢ, ϑ_u S bᵢ⟩| ≤ ‖U† bᵢ‖ ‖S bᵢ‖` is summable uniformly in `u`. -/
theorem opTrace_comp_ccmIntegratedScaling {T : evenSubspace →L[ℂ] evenSubspace}
    (hT : MemSchattenClass 1 T) (g : CCMLogKernel) :
    opTrace (T ∘L ccmIntegratedScaling g) = ∫ u, g u * opTrace (T ∘L ccmLogDilation u) := by
  obtain ⟨S, U, hS, hU, rfl⟩ := hT.one_isTraceClass
  letI : Countable (exists_hilbertBasis ℂ evenSubspace).choose :=
    (hsBasis ℂ evenSubspace).orthonormal.countable_index
  set b := hsBasis ℂ evenSubspace
  set F : _ → ℝ → ℂ := fun i u =>
    ⟪ContinuousLinearMap.adjoint U (b i), g u • ccmLogDilationOrbit (S (b i)) u⟫_ℂ with hF
  have hF_int : ∀ i, Integrable (F i) volume :=
    fun i => (integrable_ccmLogKernel_smul_orbit g (S (b i))).const_inner _
  have hF_le : ∀ i u, ‖F i u‖ ≤ ‖g u‖ * (‖ContinuousLinearMap.adjoint U (b i)‖ * ‖S (b i)‖) := by
    intro i u
    calc ‖F i u‖ ≤ ‖ContinuousLinearMap.adjoint U (b i)‖ *
          ‖g u • ccmLogDilationOrbit (S (b i)) u‖ := by
          exact norm_inner_le_norm (𝕜 := ℂ) (ContinuousLinearMap.adjoint U (b i))
            (g u • ccmLogDilationOrbit (S (b i)) u)
      _ = _ := by rw [norm_smul, norm_ccmLogDilationOrbit]; ring
  have hF_sum : Summable fun i => ∫ u, ‖F i u‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun u => norm_nonneg _)
      (fun i => ?_) ((summable_norm_adjoint_mul_norm hS hU).mul_left (∫ u, ‖g u‖))
    rw [← integral_mul_const]
    exact integral_mono (hF_int i).norm ((L1.integrable_coeFn g).norm.mul_const _) (hF_le i)
  have h1 : opTrace ((S ∘L U) ∘L ccmIntegratedScaling g) = ∑' i, ∫ u, F i u := by
    rw [opTrace_comp_comp_eq_tsum hS hU]
    refine tsum_congr fun i => ?_
    rw [ccmIntegratedScaling_apply, ← integral_inner (integrable_ccmLogKernel_smul_orbit g _)]
  have h2 : ∀ u, ∑' i, F i u = g u * opTrace ((S ∘L U) ∘L ccmLogDilation u) := by
    intro u
    rw [opTrace_comp_comp_eq_tsum hS hU, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [hF]
    exact inner_smul_right (𝕜 := ℂ) (ContinuousLinearMap.adjoint U (b i))
      (ccmLogDilationOrbit (S (b i)) u) (g u)
  rw [h1, integral_tsum_of_summable_integral_norm hF_int hF_sum]
  exact integral_congr_ae (Filter.Eventually.of_forall h2)

/-! ## The Toeplitz kernel -/

/-- The scaling trace `τ_Λ(u) = Tr(G_Λ ϑ_u)` of the generic part. -/
def ccmSoninToeplitzKernel (Λ u : ℝ) : ℂ :=
  opTrace (ccmSoninGenericPartAt Λ ∘L ccmLogDilation u)

/-- `τ_Λ(0) = Tr G_Λ = 0`. -/
theorem ccmSoninToeplitzKernel_zero {Λ : ℝ} (hΛ : 0 < Λ) : ccmSoninToeplitzKernel Λ 0 = 0 := by
  rw [ccmSoninToeplitzKernel, ccmLogDilation_zero, ContinuousLinearMap.comp_id]
  exact opTrace_ccmSoninGenericPartAt Λ hΛ

/-- `|τ_Λ(u)| ≤ ‖G_Λ‖₁`. -/
theorem norm_ccmSoninToeplitzKernel_le {Λ : ℝ} (hΛ : 0 < Λ) (u : ℝ) :
    ‖ccmSoninToeplitzKernel Λ u‖ ≤ traceNorm evenSubspace (ccmSoninGenericPartAt Λ) :=
  (norm_opTrace_comp_le_norm_mul_traceNorm (memSchattenClass_one_ccmSoninGenericPartAt hΛ) _).trans
    (mul_le_of_le_one_right (traceNorm_nonneg _) (norm_ccmLogDilation_le u))

/-- `τ_Λ` is continuous: a uniformly summable series of continuous matrix coefficients. -/
theorem continuous_ccmSoninToeplitzKernel {Λ : ℝ} (hΛ : 0 < Λ) :
    Continuous (ccmSoninToeplitzKernel Λ) := by
  obtain ⟨S, U, hS, hU, hSU⟩ := (memSchattenClass_one_ccmSoninGenericPartAt hΛ).one_isTraceClass
  set b := hsBasis ℂ evenSubspace
  have key : ∀ u, ccmSoninToeplitzKernel Λ u =
      ∑' i, ⟪ContinuousLinearMap.adjoint U (b i), ccmLogDilationOrbit (S (b i)) u⟫_ℂ := by
    intro u
    rw [ccmSoninToeplitzKernel, hSU, ContinuousLinearMap.comp_assoc,
      opTrace_comp_comm hS (hU.comp_right _), opTrace_comp_eq_tsum_basis (hU.comp_right _) hS b]
    refine tsum_congr fun i => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hc : Summable fun i => ‖ContinuousLinearMap.adjoint U (b i)‖ * ‖S (b i)‖ := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      (((hU.adjoint.summable b).add (hS.summable b)).div_const 2)
    have := two_mul_le_add_sq ‖ContinuousLinearMap.adjoint U (b i)‖ ‖S (b i)‖
    linarith
  rw [funext key]
  refine continuous_tsum
    (fun i => Continuous.inner (𝕜 := ℂ) continuous_const (continuous_ccmLogDilationOrbit _)) hc
    fun i u => ?_
  refine (norm_inner_le_norm (𝕜 := ℂ) (ContinuousLinearMap.adjoint U (b i))
    (ccmLogDilationOrbit (S (b i)) u)).trans_eq ?_
  rw [norm_ccmLogDilationOrbit]

/-- `F G_Λ F = G_Λ`. -/
theorem evenFourierTransform_conj_ccmSoninGenericPartAt (Λ : ℝ) :
    evenFourierTransform * ccmSoninGenericPartAt Λ * evenFourierTransform =
      ccmSoninGenericPartAt Λ := by
  have hP : evenFourierTransform * evenIndicatorCutoff Λ * evenFourierTransform =
      evenFourierCutoff Λ := by
    rw [evenFourierCutoff_eq_reflectedCutoff, reflectedCutoff]
  have hR : evenFourierTransform * evenFourierCutoff Λ * evenFourierTransform =
      evenIndicatorCutoff Λ := by
    rw [← hP]
    calc evenFourierTransform *
          (evenFourierTransform * evenIndicatorCutoff Λ * evenFourierTransform) *
          evenFourierTransform
        = (evenFourierTransform * evenFourierTransform) * evenIndicatorCutoff Λ *
            (evenFourierTransform * evenFourierTransform) := by noncomm_ring
      _ = evenIndicatorCutoff Λ := by rw [evenFourierTransform_mul_self, one_mul, mul_one]
  have hS : evenFourierTransform * evenCentralSoninProjection Λ * evenFourierTransform =
      evenCentralSoninProjection Λ := by
    rw [evenFourierTransform_mul_evenCentralSoninProjection, mul_assoc,
      evenFourierTransform_mul_self, mul_one]
  have hexp : evenFourierTransform * ccmSoninGenericPartAt Λ * evenFourierTransform =
      evenFourierTransform * evenFourierTransform -
        evenFourierTransform * evenIndicatorCutoff Λ * evenFourierTransform -
          evenFourierTransform * evenFourierCutoff Λ * evenFourierTransform -
            evenFourierTransform * evenCentralSoninProjection Λ * evenFourierTransform := by
    simp only [ccmSoninGenericPartAt, mul_sub, sub_mul, mul_one]
  rw [hexp, hP, hR, hS, evenFourierTransform_mul_self, ccmSoninGenericPartAt]
  abel

/-- `τ_Λ` is even: `Tr(G ϑ_{-u}) = Tr(G F ϑ_u F) = Tr(F G F ϑ_u)`. -/
theorem ccmSoninToeplitzKernel_neg {Λ : ℝ} (hΛ : 0 < Λ) (u : ℝ) :
    ccmSoninToeplitzKernel Λ (-u) = ccmSoninToeplitzKernel Λ u := by
  have hmem : MemSchattenClass 1
      (ccmSoninGenericPartAt Λ * evenFourierTransform * ccmLogDilation u) :=
    memSchattenClass_one_comp_right
      (memSchattenClass_one_comp_right (memSchattenClass_one_ccmSoninGenericPartAt hΛ) _) _
  calc ccmSoninToeplitzKernel Λ (-u)
      = opTrace (ccmSoninGenericPartAt Λ *
          (evenFourierTransform * ccmLogDilation u * evenFourierTransform)) := by
        rw [ccmSoninToeplitzKernel, evenFourierTransform_conj_ccmLogDilation]
        rfl
    _ = opTrace (ccmSoninGenericPartAt Λ * evenFourierTransform * ccmLogDilation u *
          evenFourierTransform) := by simp only [mul_assoc]
    _ = opTrace (evenFourierTransform *
          (ccmSoninGenericPartAt Λ * evenFourierTransform * ccmLogDilation u)) :=
        (hmem.one_opTrace_comp_comm evenFourierTransform).symm
    _ = opTrace (evenFourierTransform * ccmSoninGenericPartAt Λ * evenFourierTransform *
          ccmLogDilation u) := by simp only [mul_assoc]
    _ = ccmSoninToeplitzKernel Λ u := by
        rw [evenFourierTransform_conj_ccmSoninGenericPartAt]
        rfl

/-- `conj τ_Λ(u) = τ_Λ(-u)`, from `G_Λ† = G_Λ` and `ϑ_u† = ϑ_{-u}`. -/
theorem conj_ccmSoninToeplitzKernel {Λ : ℝ} (hΛ : 0 < Λ) (u : ℝ) :
    conj (ccmSoninToeplitzKernel Λ u) = ccmSoninToeplitzKernel Λ (-u) := by
  unfold ccmSoninToeplitzKernel
  rw [← opTrace_adjoint, ContinuousLinearMap.adjoint_comp, adjoint_ccmLogDilation,
    adjoint_ccmSoninGenericPartAt]
  exact (memSchattenClass_one_ccmSoninGenericPartAt hΛ).one_opTrace_comp_comm _

/-- `τ_Λ` is real. -/
theorem im_ccmSoninToeplitzKernel {Λ : ℝ} (hΛ : 0 < Λ) (u : ℝ) :
    (ccmSoninToeplitzKernel Λ u).im = 0 := by
  have h := conj_ccmSoninToeplitzKernel hΛ u
  rw [ccmSoninToeplitzKernel_neg hΛ] at h
  exact Complex.conj_eq_iff_im.mp h

/-! ## The Toeplitz form of the generic trace -/

/-- `(g★ ⋆ g)(x) = ∫ conj (g (-t)) g (x - t) dt`. -/
theorem ccmSoninGramTest_apply (g : CCMCompactSchwartzLogTest) (x : ℝ) :
    ccmSoninGramTest g x = ∫ t, conj (g (-t)) * g (x - t) := by
  change SchwartzMap.autocorrelationSchwartz
    (SchwartzMap.conjugateReflectionSchwartz g.toSchwartzMap) x = _
  rw [SchwartzMap.autocorrelationSchwartz_apply, SchwartzMap.autocorrelation, convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [SchwartzMap.conjugateReflection]

/-- **Generic trace of a Gram test.**  `Tr(ϑ(g) G_Λ ϑ(g)†) = ∫ (g★ ⋆ g)(u) τ_Λ(u) du`. -/
theorem opTrace_ccmSoninGenericPartAt_gram (g : CCMCompactSchwartzLogTest) {Λ : ℝ}
    (hΛ : 0 < Λ) :
    opTrace (ϑ[g.toSchwartzMap] ∘L ccmSoninGenericPartAt Λ ∘L
        ContinuousLinearMap.adjoint ϑ[g.toSchwartzMap]) =
      ∫ u, ccmSoninGramTest g u * ccmSoninToeplitzKernel Λ u := by
  have hG := memSchattenClass_one_ccmSoninGenericPartAt hΛ
  rw [(memSchattenClass_one_comp_right hG _).one_opTrace_comp_comm,
    ContinuousLinearMap.comp_assoc, ← ccmIntegratedScaling_ccmSoninGramTest,
    opTrace_comp_ccmIntegratedScaling hG]
  refine integral_congr_ae ?_
  filter_upwards [ccmSchwartzLogKernel_ae (ccmSoninGramTest g).toSchwartzMap] with u hu
  rw [hu]
  rfl

/-- Pairing a Gram test with a bounded continuous kernel is the Toeplitz form
`∫∫ conj (g s) g t τ(t - s)`. -/
theorem integral_ccmSoninGramTest_mul (g : CCMCompactSchwartzLogTest) {τ : ℝ → ℂ}
    (hτ : Continuous τ) {C : ℝ} (hC : ∀ u, ‖τ u‖ ≤ C) :
    ∫ x, ccmSoninGramTest g x * τ x = ∫ s, ∫ t, conj (g s) * g t * τ (t - s) := by
  have hv : Integrable (fun t => conj (g (-t))) volume := by
    have h := (SchwartzMap.conjugateReflectionSchwartz g.toSchwartzMap).integrable (μ := volume)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp
  have hint : Integrable (fun p : ℝ × ℝ => conj (g (-p.2)) * g (p.1 - p.2) * τ p.1)
      (volume.prod volume) := by
    have h0 := hv.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
      g.toSchwartzMap.integrable (μ := volume) (ν := volume)
    exact h0.mul_bdd ((hτ.comp continuous_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => hC p.1)
  calc ∫ x, ccmSoninGramTest g x * τ x
      = ∫ x, ∫ t, conj (g (-t)) * g (x - t) * τ x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [ccmSoninGramTest_apply, ← integral_mul_const]
    _ = ∫ t, ∫ x, conj (g (-t)) * g (x - t) * τ x := integral_integral_swap hint
    _ = ∫ t, ∫ x, conj (g (-t)) * g x * τ (x + t) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        dsimp only
        rw [← integral_add_right_eq_self (fun x => conj (g (-t)) * g (x - t) * τ x) t]
        simp only [add_sub_cancel_right]
    _ = ∫ s, ∫ t, conj (g s) * g t * τ (t - s) := by
        have h := integral_neg_eq_self (fun s : ℝ => ∫ t, conj (g s) * g t * τ (t - s)) volume
        simpa [sub_neg_eq_add] using h

/-- **The generic trace is a Toeplitz form.**
`Tr(ϑ(g) G_Λ ϑ(g)†) = ∫∫ conj (g s) g t τ_Λ(t - s) ds dt`. -/
theorem opTrace_ccmSoninGenericPartAt_eq_toeplitz (g : CCMCompactSchwartzLogTest) {Λ : ℝ}
    (hΛ : 0 < Λ) :
    opTrace (ϑ[g.toSchwartzMap] ∘L ccmSoninGenericPartAt Λ ∘L
        ContinuousLinearMap.adjoint ϑ[g.toSchwartzMap]) =
      ∫ s, ∫ t, conj (g s) * g t * ccmSoninToeplitzKernel Λ (t - s) := by
  rw [opTrace_ccmSoninGenericPartAt_gram g hΛ]
  exact integral_ccmSoninGramTest_mul g (continuous_ccmSoninToeplitzKernel hΛ)
    (norm_ccmSoninToeplitzKernel_le hΛ)

/-- **Connes--Consani Sonin-trace domination as Toeplitz positivity.**  At cutoff one,
`Re Tr(ϑ(g★ ⋆ g) S) ≤ -Re W(g★ ⋆ g)` holds exactly when the Toeplitz form of the real, even,
bounded, continuous kernel `τ_1` with `τ_1(0) = 0` is nonnegative at `g`. -/
theorem ccmSoninTraceDomination_iff_toeplitz (g : CCMCompactSchwartzLogTest) :
    (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel (ccmSoninGramTest g).toSchwartzMap) *
        evenCentralSoninProjection 1)).re ≤ (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re ↔
      0 ≤ (∫ s, ∫ t, conj (g s) * g t * ccmSoninToeplitzKernel 1 (t - s)).re := by
  rw [ccmSoninTraceDomination_iff, ← opTrace_ccmSoninGenericPartAt_eq_toeplitz g one_pos,
    ccmIntegratedScaling_ccmSoninGramTest]
  have hG := memSchattenClass_one_ccmSoninGenericPartAt (Λ := 1) one_pos
  have h : opTrace (ContinuousLinearMap.adjoint ϑ[g.toSchwartzMap] ∘L ϑ[g.toSchwartzMap] *
      ccmSoninGenericPart) = opTrace (ϑ[g.toSchwartzMap] ∘L ccmSoninGenericPartAt 1 ∘L
        ContinuousLinearMap.adjoint ϑ[g.toSchwartzMap]) := by
    change opTrace (ContinuousLinearMap.adjoint ϑ[g.toSchwartzMap] ∘L
      (ϑ[g.toSchwartzMap] ∘L ccmSoninGenericPartAt 1)) = _
    rw [(memSchattenClass_one_comp_left hG _).one_opTrace_comp_comm,
      ContinuousLinearMap.comp_assoc]
  rw [h]

end RHTower
