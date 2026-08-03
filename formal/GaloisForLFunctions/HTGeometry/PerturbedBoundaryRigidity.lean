import GaloisForLFunctions.HTGeometry.PerturbedOuterOrbitBoundary

/-!
# The boundary is a faithful torus and misses the orbit

Two boundary states which agree on the upper half plane agree everywhere, because the carriers are
entire; so the boundary family inherits the injectivity of the phase hull and is a homeomorphic copy
of the phase torus.

An orbit point cannot be a boundary state.  On the line `Im z = 1` the difference of two boundary
states is an almost periodic exponential series, while the background contribution tends to zero as
the real part grows.  An almost periodic series tending to zero has all coefficients zero, so the
phases coincide and the background is constant -- which it is not.
-/

open Filter MeasureTheory Set Topology

namespace GaloisForLFunctions

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-! ## The carrier on the line of height one -/

theorem cexpChar_I (omega : ℝ) : cexpChar omega Complex.I = Complex.exp (-(omega : ℂ)) := by
  rw [cexpChar]
  congr 1
  rw [mul_comm Complex.I (omega : ℂ), mul_assoc, Complex.I_mul_I]
  ring

/-- Amplitudes of the carrier read on the line of height one. -/
def heightOneAmp (a : ι → ℂ) (omega : ι → ℝ) (i : ι) : ℂ :=
  a i * Complex.exp (-(omega i : ℂ))

theorem heightOneAmp_ne_zero {a : ι → ℂ} {omega : ι → ℝ} (hane : ∀ i, a i ≠ 0) (i : ι) :
    heightOneAmp a omega i ≠ 0 :=
  mul_ne_zero (hane i) (Complex.exp_ne_zero _)

theorem norm_heightOneAmp (a : ι → ℂ) (omega : ι → ℝ) (i : ι) :
    ‖heightOneAmp a omega i‖ = ‖a i‖ * Real.exp (-(omega i)) := by
  rw [heightOneAmp, norm_mul, Complex.norm_exp]
  simp

theorem summable_norm_heightOneAmp {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) :
    Summable fun i => ‖heightOneAmp a omega i‖ := by
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) (h 1)
  rw [norm_heightOneAmp]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine Real.exp_le_exp.mpr ?_
  rw [one_mul]
  exact neg_le_abs _

/-- **The carrier on the line of height one is an almost periodic series.** -/
theorem cexpSeriesCarrier_ofReal_add_I (a : ι → ℂ) (omega : ι → ℝ) (x : ℝ) :
    cexpSeriesCarrier a omega ((x : ℂ) + Complex.I)
      = expSeriesCarrier (heightOneAmp a omega) omega x := by
  rw [cexpSeriesCarrier, expSeriesCarrier]
  congr 1
  funext i
  rw [cexpChar_add, cexpChar_ofReal, cexpChar_I, heightOneAmp]
  ring

/-! ## Faithfulness of the boundary family -/

/-- **The boundary family is injective.**  Two boundary states agreeing on the upper half plane have
equal entire carriers, hence equal phases. -/
theorem injective_perturbedBoundary {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (c : ℂ) {eps : ℂ} (heps : eps ≠ 0)
    (hane : ∀ i, a i ≠ 0) (hinj : Function.Injective omega) :
    Function.Injective (perturbedBoundary h c eps) := by
  intro lam mu hlm
  refine injective_bohrHullMap h hane hinj ?_
  have hdiff : Differentiable ℂ
      fun z => bohrHullMap a omega h lam z - bohrHullMap a omega h mu z := by
    refine Differentiable.sub ?_ ?_
    · exact differentiable_cexpSeriesCarrier
        (expSeriesNormallySummable_phase h fun i => le_of_eq (Circle.norm_coe (lam i)))
    · exact differentiable_cexpSeriesCarrier
        (expSeriesNormallySummable_phase h fun i => le_of_eq (Circle.norm_coe (mu i)))
  have hupper : ∀ z : ℂ, 0 < z.im →
      bohrHullMap a omega h lam z - bohrHullMap a omega h mu z = 0 := by
    intro z hz
    have hval := congrArg (fun g : C(UpperPlane, ℂ) => g ⟨z, hz⟩) hlm
    simp only [perturbedBoundary_apply] at hval
    have hz0 : eps * (bohrHullMap a omega h lam z - bohrHullMap a omega h mu z) = 0 := by
      linear_combination hval
    rcases mul_eq_zero.mp hz0 with hcase | hcase
    · exact absurd hcase heps
    · exact hcase
  have hA : AnalyticOnNhd ℂ
      (fun z => bohrHullMap a omega h lam z - bohrHullMap a omega h mu z) Set.univ :=
    hdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : (fun z => bohrHullMap a omega h lam z - bohrHullMap a omega h mu z)
      =ᶠ[nhds Complex.I] 0 := by
    filter_upwards [hopen.mem_nhds (by simp)] with z hz
    exact hupper z hz
  have hzero := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ Complex.I) hev
  ext z
  have hzz := hzero (Set.mem_univ z)
  simpa [sub_eq_zero] using hzz

/-- **The boundary is a homeomorphic copy of the phase torus.**  This is claim (3) of the card. -/
theorem isClosedEmbedding_perturbedBoundary {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (c : ℂ) {eps : ℂ} (heps : eps ≠ 0)
    (hane : ∀ i, a i ≠ 0) (hinj : Function.Injective omega) :
    Topology.IsClosedEmbedding (perturbedBoundary h c eps) :=
  (continuous_perturbedBoundary h c eps).isClosedEmbedding
    (injective_perturbedBoundary h c heps hane hinj)

/-! ## The orbit misses the boundary -/

/-- **The orbit and the boundary are disjoint.**  This is the disjointness half of equation (12). -/
theorem perturbedOrbit_ne_perturbedBoundary {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) {S : ℂ → ℂ}
    (hS : ContinuousOn S {z : ℂ | 0 < z.im}) {c eps : ℂ} (heps : eps ≠ 0)
    (hane : ∀ i, a i ≠ 0) (hinj : Function.Injective omega)
    (hcollapse : ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 0 < z.im) →
      TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => S (z + (t : ℂ))) (fun _ => c) (cocompact ℝ) K)
    (hnc : ¬ ∀ z : ℂ, 0 < z.im → S z = c) (t : ℝ) (lam : ι → Circle) :
    perturbedOrbit h S hS eps t ≠ perturbedBoundary h c eps lam := by
  intro heq
  -- the identity of (15) on the upper half plane
  have hid : ∀ z : ℂ, 0 < z.im →
      S (z + (t : ℂ)) - c
        = eps * (bohrHullMap a omega h lam z
            - bohrHullMap a omega h (circlePhaseFlow omega t) z) := by
    intro z hz
    have hval := congrArg (fun g : C(UpperPlane, ℂ) => g ⟨z, hz⟩) heq
    simp only [perturbedOrbit_apply, perturbedBoundary_apply] at hval
    rw [← bohrHullMap_circlePhaseFlow h t z] at hval
    linear_combination hval
  -- the background collapses along the line of height one
  have hbg : Tendsto (fun x : ℝ => S (((x : ℂ) + Complex.I) + (t : ℂ)) - c) atTop (nhds 0) := by
    have hK : IsCompact ({Complex.I} : Set ℂ) := isCompact_singleton
    have hKH : ∀ z ∈ ({Complex.I} : Set ℂ), 0 < z.im := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simp
    have hcol := hcollapse _ hK hKH
    rw [Metric.tendstoUniformlyOn_iff] at hcol
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hatTop : (atTop : Filter ℝ) ≤ cocompact ℝ := by
      rw [cocompact_eq_atBot_atTop]
      exact le_sup_right
    have hshift : Tendsto (fun x : ℝ => x + t) atTop (cocompact ℝ) :=
      (tendsto_atTop_add_const_right atTop t tendsto_id).mono_right hatTop
    have hev := hshift.eventually (hcol ε hε)
    filter_upwards [hev] with x hx
    have hxI := hx Complex.I rfl
    rw [Complex.dist_eq] at hxI
    have hrw : ((x : ℂ) + Complex.I) + (t : ℂ) = Complex.I + ((x + t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hrw, norm_sub_rev]
    exact hxI
  -- hence the two boundary carriers agree
  have hnorm := summable_norm_heightOneAmp h
  have hsum : ∀ nu : ι → Circle,
      Summable fun i => ‖heightOneAmp a omega i * (nu i : ℂ)‖ := by
    intro nu
    refine hnorm.congr fun i => ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
  have hcarr : Tendsto (fun x : ℝ =>
      expSeriesCarrier (fun i => heightOneAmp a omega i * (lam i : ℂ)) omega x
        - expSeriesCarrier
            (fun i => heightOneAmp a omega i * (circlePhaseFlow omega t i : ℂ)) omega x)
      atTop (nhds 0) := by
    have hzero : Tendsto (fun x : ℝ => eps * (expSeriesCarrier
        (fun i => heightOneAmp a omega i * (lam i : ℂ)) omega x
          - expSeriesCarrier
              (fun i => heightOneAmp a omega i * (circlePhaseFlow omega t i : ℂ)) omega x))
        atTop (nhds 0) := by
      refine hbg.congr fun x => ?_
      have hz : 0 < ((x : ℂ) + Complex.I).im := by simp
      rw [hid _ hz]
      congr 1
      have hamp : ∀ nu : ι → Circle,
          heightOneAmp (fun i => a i * (nu i : ℂ)) omega
            = fun i => heightOneAmp a omega i * (nu i : ℂ) := by
        intro nu
        funext i
        rw [heightOneAmp, heightOneAmp]
        ring
      rw [bohrHullMap_apply, bohrHullMap_apply, cexpSeriesCarrier_ofReal_add_I,
        cexpSeriesCarrier_ofReal_add_I, hamp lam, hamp (circlePhaseFlow omega t)]
    have := hzero.const_mul eps⁻¹
    rw [mul_zero] at this
    refine this.congr fun x => ?_
    rw [← mul_assoc, inv_mul_cancel₀ heps, one_mul]
  have hphase := expSeriesCarrier_phase_eq_of_tendsto_zero (hsum lam)
    (hsum (circlePhaseFlow omega t)) (heightOneAmp_ne_zero hane) hinj hcarr
  -- so the carrier terms cancel and the background is constant
  have hconst : ∀ z : ℂ, 0 < z.im → S (z + (t : ℂ)) = c := by
    intro z hz
    have hcarrier : bohrHullMap a omega h lam z
        = bohrHullMap a omega h (circlePhaseFlow omega t) z := by
      simp only [bohrHullMap_apply, cexpSeriesCarrier]
      exact tsum_congr fun i => by rw [congrFun hphase i]
    have hval := hid z hz
    rw [hcarrier, sub_self, mul_zero, sub_eq_zero] at hval
    exact hval
  refine hnc fun w hw => ?_
  have hwt : 0 < (w - (t : ℂ)).im := by simpa using hw
  have := hconst (w - (t : ℂ)) hwt
  rwa [sub_add_cancel] at this

end

end GaloisForLFunctions
