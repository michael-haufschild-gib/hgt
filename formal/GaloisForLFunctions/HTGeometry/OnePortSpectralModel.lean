import GaloisForLFunctions.HTGeometry.OnePortStieltjesTransform
import GaloisForLFunctions.HTGeometry.MaximalMultiplicationSelfAdjoint

/-!
# A self-adjoint spectral model of one port

For a one-port source `k` with density `σ`, the measure `dμ = σ(t) dt/(1 + t)` on `(0, ∞)` is
finite, although `∫ σ = ∞` in general.  Multiplication by `t` on its maximal domain in `L²(μ)` is
a self-adjoint operator `A`, and the constant vector `1` has finite norm.  For `ζ ∉ [0, ∞)` the
operator `A - ζ` has the bounded two-sided inverse `(t - ζ)⁻¹`, and the Stieltjes function of the
port satisfies

`m(ζ) = m(-1) + (ζ + 1) ⟨1, (A - ζ)⁻¹ 1⟩_{L²(μ)}`,

by the partial-fraction identity `1/(t - ζ) - 1/(t + 1) = (ζ + 1)/((t - ζ)(t + 1))`.  Since `μ`
has no atoms, `A` has no eigenvalues.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Complex Set Filter
open scoped InnerProductSpace

variable {k : ℝ → ℝ}

/-- The spectral measure `dμ = σ(t) dt / (1 + t)` on `(0, ∞)`. -/
def onePortSpectralMeasure (k : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (onePortDensity k t / (1 + t))

/-- Multiplication by the spectral variable `t` on `L²(μ)`. -/
def onePortOperator (k : ℝ → ℝ) : Lp ℂ 2 (onePortSpectralMeasure k) →ₗ.[ℂ]
    Lp ℂ 2 (onePortSpectralMeasure k) :=
  maximalMul (onePortSpectralMeasure k) id

/-- The operator `A` is self-adjoint. -/
theorem isSelfAdjoint_onePortOperator (k : ℝ → ℝ) : IsSelfAdjoint (onePortOperator k) :=
  maximalMul_isSelfAdjoint measurable_id

/-- The spectral measure has no atoms: every real point is a null set. -/
theorem ae_onePortSpectralMeasure_ne (k : ℝ → ℝ) (a : ℝ) :
    ∀ᵐ t ∂(onePortSpectralMeasure k), t ≠ a :=
  ((withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)).ae_le (Measure.ae_ne volume a)

/-- **No eigenvalues.** Multiplication by `t` on `L²(μ)` has no eigenvectors: if `A f = λ f`
then `f = 0`.  A real zero of the principal-value trace is therefore not an eigenvalue of `A`. -/
theorem onePortOperator_eigenvector_eq_zero (k : ℝ → ℝ) (lam : ℂ)
    (f : (onePortOperator k).domain)
    (hf : onePortOperator k f = lam • (f : Lp ℂ 2 (onePortSpectralMeasure k))) :
    (f : Lp ℂ 2 (onePortSpectralMeasure k)) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [maximalMul_coeFn (μ := onePortSpectralMeasure k) id f,
    Lp.coeFn_smul lam (f : Lp ℂ 2 (onePortSpectralMeasure k)),
    ae_onePortSpectralMeasure_ne k lam.re] with t h1 h2 h3
  have heq : ((t : ℝ) : ℂ) * ((f : Lp ℂ 2 (onePortSpectralMeasure k)) : ℝ → ℂ) t =
      lam * ((f : Lp ℂ 2 (onePortSpectralMeasure k)) : ℝ → ℂ) t := by
    have := h1.symm.trans (congrArg (fun g : Lp ℂ 2 (onePortSpectralMeasure k) =>
      (g : ℝ → ℂ) t) hf ▸ h2)
    simpa using this
  have hne : ((t : ℝ) : ℂ) - lam ≠ 0 := by
    intro h0
    apply h3
    have := congrArg Complex.re h0
    simpa [sub_eq_zero] using this
  have : (((t : ℝ) : ℂ) - lam) * ((f : Lp ℂ 2 (onePortSpectralMeasure k)) : ℝ → ℂ) t = 0 := by
    rw [sub_mul, heq, sub_self]
  simpa [hne] using this

namespace OnePortSource

theorem isFiniteMeasure_onePortSpectralMeasure (hk : OnePortSource k) :
    IsFiniteMeasure (onePortSpectralMeasure k) :=
  isFiniteMeasure_withDensity_ofReal hk.integrableOn_onePortDensity_div.hasFiniteIntegral

theorem ae_onePortSpectralMeasure_pos (k : ℝ → ℝ) : ∀ᵐ t ∂(onePortSpectralMeasure k), 0 < t :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

theorem memLp_one (hk : OnePortSource k) :
    MemLp (fun _ : ℝ => (1 : ℂ)) 2 (onePortSpectralMeasure k) := by
  haveI := hk.isFiniteMeasure_onePortSpectralMeasure
  exact memLp_const 1

/-- The constant vector `1 ∈ L²(μ)`, of finite norm. -/
def onePortUnit (hk : OnePortSource k) : Lp ℂ 2 (onePortSpectralMeasure k) :=
  hk.memLp_one.toLp _

theorem integral_onePortSpectralMeasure (hk : OnePortSource k) (g : ℝ → ℂ) :
    ∫ t, g t ∂(onePortSpectralMeasure k) =
      ∫ t in Ioi (0 : ℝ), ((onePortDensity k t / (1 + t) : ℝ) : ℂ) * g t := by
  have hmeas : Measurable fun t => ENNReal.ofReal (onePortDensity k t / (1 + t)) :=
    (hk.continuous_onePortDensity.measurable.div (by fun_prop)).ennreal_ofReal
  rw [onePortSpectralMeasure, integral_withDensity_eq_integral_toReal_smul hmeas
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : 0 < t := ht
  rw [ENNReal.toReal_ofReal (div_nonneg (hk.onePortDensity_nonneg t) (by linarith)),
    Complex.real_smul]

/-- **(2a).** The resolvent formula in the self-adjoint model. For `ζ ∉ [0, ∞)` the resolvent
`R = (A - ζ)⁻¹` exists as a bounded two-sided inverse, and
`m(ζ) = m(-1) + (ζ + 1) ⟨1, (A - ζ)⁻¹ 1⟩_{L²(μ)}`. -/
theorem onePortStieltjes_eq_resolvent (hk : OnePortSource k) {ζ : ℂ} (hζ : -ζ ∈ slitPlane) :
    ∃ R : Lp ℂ 2 (onePortSpectralMeasure k) →L[ℂ] Lp ℂ 2 (onePortSpectralMeasure k),
      (∀ f, ∃ hf : R f ∈ (onePortOperator k).domain,
        onePortOperator k ⟨R f, hf⟩ - ζ • R f = f) ∧
      (∀ g : (onePortOperator k).domain,
        R (onePortOperator k g - ζ • (g : Lp ℂ 2 (onePortSpectralMeasure k))) = g) ∧
      onePortStieltjes k ζ = onePortStieltjes k (-1) +
        (ζ + 1) * ⟪hk.onePortUnit, R hk.onePortUnit⟫_ℂ := by
  haveI := hk.isFiniteMeasure_onePortSpectralMeasure
  obtain ⟨c, hc, hcle⟩ := exists_mul_one_add_le_norm_sub hζ
  have hae : ∀ᵐ t ∂(onePortSpectralMeasure k), c ≤ ‖((id t : ℝ) : ℂ) - ζ‖ := by
    filter_upwards [ae_onePortSpectralMeasure_pos k] with t ht
    have := hcle t ht.le
    simp only [id]
    nlinarith
  refine ⟨mulResolvent measurable_id ζ hc, fun f => ⟨mulResolvent_mem_domain _ ζ hc f,
    maximalMul_mulResolvent measurable_id hc hae f⟩,
    fun g => mulResolvent_maximalMul measurable_id hc hae g, ?_⟩
  have hunit : hk.onePortUnit = Lp.const 2 (onePortSpectralMeasure k) (1 : ℂ) := by
    apply Lp.ext
    filter_upwards [hk.memLp_one.coeFn_toLp, Lp.coeFn_const 2 (onePortSpectralMeasure k) (1 : ℂ)]
      with t h1 h2
    rw [onePortUnit, h1, h2, Function.const_apply]
  have hone : -(-1 : ℂ) ∈ slitPlane := by simp [mem_slitPlane_iff]
  rw [hunit, inner_const_mulResolvent_const measurable_id hc hae,
    hk.integral_onePortSpectralMeasure, hk.onePortStieltjes_eq hζ, hk.onePortStieltjes_eq hone,
    ← integral_const_mul, ← integral_add (hk.integrableOn_onePortDensity_div_sub hone)]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : 0 < t := ht
    have h1 : (t : ℂ) - ζ ≠ 0 := by
      intro h0
      have := hcle t ht.le
      rw [h0, norm_zero] at this
      nlinarith
    have h2 : (t : ℂ) - -1 ≠ 0 := by
      rw [sub_neg_eq_add]; exact_mod_cast (by linarith : (t + 1 : ℝ) ≠ 0)
    have h3 : (1 : ℂ) + t ≠ 0 := by exact_mod_cast (by linarith : (1 + t : ℝ) ≠ 0)
    simp only [id]
    push_cast
    field_simp
    ring
  · refine (((hk.integrableOn_onePortDensity_div_sub hζ).sub
      (hk.integrableOn_onePortDensity_div_sub hone))).congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht : 0 < t := ht
    have h1 : (t : ℂ) - ζ ≠ 0 := by
      intro h0
      have := hcle t ht.le
      rw [h0, norm_zero] at this
      nlinarith
    have h2 : (t : ℂ) - -1 ≠ 0 := by
      rw [sub_neg_eq_add]; exact_mod_cast (by linarith : (t + 1 : ℝ) ≠ 0)
    have h3 : (1 : ℂ) + t ≠ 0 := by exact_mod_cast (by linarith : (1 + t : ℝ) ≠ 0)
    simp only [id, Pi.sub_apply]
    push_cast
    field_simp
    ring

end OnePortSource

end

end GaloisForLFunctions.HTGeometry
