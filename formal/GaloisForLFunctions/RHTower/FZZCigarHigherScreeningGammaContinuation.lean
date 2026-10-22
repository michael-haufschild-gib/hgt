import GaloisForLFunctions.RHTower.FZZCigarHigherScreeningRestoration
import GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningGammaContinuation

/-!
# Higher original screening source and its Gamma continuation

The full fifth local subtraction and all six restored radial terms define the
original source with three collision factors explicitly cancelled at each
puncture. Both local remainders and the original exterior are retained.
The source is separately analytic on `alpha,beta > -8`, `alpha+beta < -2`.
Its exact nonzero collision-line values are preserved before evaluation.

The ordinary admitted whole-plane integral supplies the initial identity.
Three Gamma recurrences at each puncture give the higher cleared Gamma family.
Two connected real analytic slices and reflection extend the equality to the
entire higher chamber. An onto positive chart discharges all domain conditions.
Local equality then identifies every mixed finite jet of the cleared source,
including every order at the original cubic collision `(-6,-6)`.

These are derivatives of the explicitly cleared original position source.
Identifying the uncleared marked and unmarked finite-part cutoff values still
requires the derivatives of the clearing factors and restored counterterms.
Screening-count continuation, full physical normalization, the independently
fixed phase frame and the complete mixed Ward producer remain separate.
-/

open MeasureTheory Set Metric Filter ProbabilityTheory
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

/-- All three local collision factors, cleared before evaluation. -/
def fzzScreeningHigherPoleFactor (α : ℝ) : ℝ := (α+2)*(α+4)*(α+6)

/-- Explicitly cancelled radial primitives; the finite tail remains intact. -/
def fzzScreeningHigherClearedRadial (α : ℝ) : ℕ → ℝ
  | 0 => (α+4)*(α+6)*(1/2 : ℝ)^(α+2)
  | 1 => (α+2)*(α+6)*(1/2 : ℝ)^(α+4)
  | 2 => (α+2)*(α+4)*(1/2 : ℝ)^(α+6)
  | n+3 => fzzScreeningHigherPoleFactor α *
      (1/2 : ℝ)^(α+2*((n+3 : ℕ):ℝ)+2)/(α+2*((n+3 : ℕ):ℝ)+2)

/-- The complete restored polynomial after explicit local pole cancellation. -/
def fzzScreeningHigherClearedCounterterm (α β : ℝ) : ℝ :=
  2*Real.pi * ∑ k ∈ Finset.range 6,
    fzzScreeningFifthAngularCoefficient β k * fzzScreeningHigherClearedRadial α k

/-- The original two-puncture source, including its exterior and all restored terms. -/
def fzzScreeningHigherClearedSource (α β : ℝ) : ℝ :=
  fzzScreeningHigherPoleFactor α * fzzScreeningHigherPoleFactor β *
    ((∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted α β z) +
     (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted β α z) +
     (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α β z)) +
    fzzScreeningHigherPoleFactor β * fzzScreeningHigherClearedCounterterm α β +
    fzzScreeningHigherPoleFactor α * fzzScreeningHigherClearedCounterterm β α

private def higherPositiveWeightMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun z => ENNReal.ofReal (max (f z) 0))



private theorem exterior_admission (α β : ℝ) (hs : α+β < -2) :
    IntegrableOn (fzzScreeningPlaneKernel α β) fzzScreeningPlaneExterior :=
  exterior_integrable α β hs

private theorem exterior_reflection (α β : ℝ) :
    (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α β z) =
      ∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel β α z := by
  have hp : (fun z : ℂ => 1-z) ⁻¹' fzzScreeningPlaneExterior = fzzScreeningPlaneExterior := by
    ext z
    simp only [fzzScreeningPlaneExterior, mem_preimage, mem_compl_iff, mem_union,
      mem_ball, dist_eq_norm, sub_zero, sub_sub_cancel_left, norm_neg, norm_sub_rev (1 : ℂ) z,
      or_comm]
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).setIntegral_preimage_emb
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding (fzzScreeningPlaneKernel α β)
      fzzScreeningPlaneExterior
  rw [hp] at h
  simpa only [fzzScreeningPlaneKernel_reflection] using h.symm

private theorem fifth_singular_analytic (α β : ℝ) (ha : -8 < α) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted s β z) α := by
  have h := fzzScreeningFifthSubtracted_singular_analytic (Real.log (α+8)) β
  rw [Real.exp_log (by linarith : 0 < α+8)] at h
  have he : -8+(α+8)=α := by ring
  rw [he] at h
  have ht := h.comp_sub α
  have he' (s : ℝ) : α+(s-α)=s := by ring
  simpa only [zero_add, he'] using ht

private theorem fifth_regular_analytic (α β : ℝ) (ha : -8 < α) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted α s z) β := by
  have h := fzzScreeningFifthSubtracted_regular_analytic (Real.log (α+8)) β
  rw [Real.exp_log (by linarith : 0 < α+8)] at h
  simpa only [show -8+(α+8)=α by ring] using h

private theorem higher_factor_analytic (α : ℝ) :
    AnalyticAt ℝ fzzScreeningHigherPoleFactor α := by
  unfold fzzScreeningHigherPoleFactor
  fun_prop

private theorem half_power_analytic (α c : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => (1/2 : ℝ)^(s+c)) α := by
  have h : AnalyticAt ℝ (fun s : ℝ => Real.exp (Real.log (1/2)*(s+c))) α := by fun_prop
  simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1/2)] using h

theorem higher_radial_analytic (α : ℝ) (ha : -8 < α) (k : ℕ) :
    AnalyticAt ℝ (fun s => fzzScreeningHigherClearedRadial s k) α := by
  rcases k with _ | (_ | (_ | n))
  · exact (show AnalyticAt ℝ (fun s : ℝ => (s+4)*(s+6)) α by fun_prop).mul
      (half_power_analytic α 2)
  · exact (show AnalyticAt ℝ (fun s : ℝ => (s+2)*(s+6)) α by fun_prop).mul
      (half_power_analytic α 4)
  · exact (show AnalyticAt ℝ (fun s : ℝ => (s+2)*(s+4)) α by fun_prop).mul
      (half_power_analytic α 6)
  · have hp : AnalyticAt ℝ (fun s : ℝ => (1/2 : ℝ)^(s+2*((n+3:ℕ):ℝ)+2)) α := by
      convert half_power_analytic α (2*((n+3:ℕ):ℝ)+2) using 1; simp only [add_assoc]
    have hd : α+2*((n+3:ℕ):ℝ)+2 ≠ 0 := by
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      linarith
    exact ((higher_factor_analytic α).mul hp).div (by fun_prop) hd

theorem higher_counterterm_analytic_left (α β : ℝ) (ha : -8 < α) :
    AnalyticAt ℝ (fun s => fzzScreeningHigherClearedCounterterm s β) α := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact analyticAt_const.mul (higher_radial_analytic α ha k)

private theorem higher_counterterm_analytic_right (α β : ℝ) :
    AnalyticAt ℝ (fun s => fzzScreeningHigherClearedCounterterm α s) β := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact (fzzScreeningFifthAngularCoefficient_analytic β k).mul analyticAt_const

private theorem higher_source_analytic (α β : ℝ) (ha : -8 < α) (hb : -8 < β)
    (hs : α+β < -2) : AnalyticAt ℝ (fun s => fzzScreeningHigherClearedSource s β) α := by
  have hi := ((fifth_singular_analytic α β ha).add
    (fifth_regular_analytic β α hb)).add (exterior_analytic α β hs)
  exact ((((higher_factor_analytic α).mul analyticAt_const).mul hi).add
    (analyticAt_const.mul (higher_counterterm_analytic_left α β ha))).add
      ((higher_factor_analytic α).mul (higher_counterterm_analytic_right β α))

/-- Reflection retains both punctures, the finite polynomial terms, and the exterior. -/
theorem fzzScreeningHigherClearedSource_symm (α β : ℝ) :
    fzzScreeningHigherClearedSource α β = fzzScreeningHigherClearedSource β α := by
  unfold fzzScreeningHigherClearedSource
  rw [exterior_reflection α β]
  ring

/-- The higher original cleared source is analytic on each full admitted left slice. -/
theorem fzzScreeningHigherClearedSource_analytic_left (v : ℝ) :
    AnalyticOnNhd ℝ (fun α => fzzScreeningHigherClearedSource α (-8+Real.exp v))
      (Ioo (-8) (-2-(-8+Real.exp v))) := by
  intro α hα
  exact higher_source_analytic α _ hα.1 (by linarith [Real.exp_pos v]) (by linarith [hα.2])

/-- Reflection gives the full right analytic slice of the same original source. -/
theorem fzzScreeningHigherClearedSource_analytic_right (u : ℝ) :
    AnalyticOnNhd ℝ (fun β => fzzScreeningHigherClearedSource (-8+Real.exp u) β)
      (Ioo (-8) (-2-(-8+Real.exp u))) := by
  intro β hβ
  have h := fzzScreeningHigherClearedSource_analytic_left u β hβ
  apply h.congr
  filter_upwards with s
  exact fzzScreeningHigherClearedSource_symm s (-8+Real.exp u)


private theorem higher_counterterm_clearing (α β : ℝ) (ha : -2 < α) :
    fzzScreeningHigherClearedCounterterm α β =
      fzzScreeningHigherPoleFactor α * fzzScreeningFifthCounterterm α β := by
  have h2 : α+2 ≠ 0 := by linarith
  have h4 : α+4 ≠ 0 := by linarith
  have h6 : α+6 ≠ 0 := by linarith
  unfold fzzScreeningHigherClearedCounterterm fzzScreeningFifthCounterterm
  rw [mul_left_comm (fzzScreeningHigherPoleFactor α) (2*Real.pi)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rcases k with _ | (_ | (_ | n))
  · simp only [fzzScreeningHigherClearedRadial, fzzScreeningHigherPoleFactor,
      Nat.cast_zero, mul_zero, add_zero]
    field_simp [h2,h4,h6]
  · simp only [fzzScreeningHigherClearedRadial, fzzScreeningHigherPoleFactor, Nat.reduceAdd, Nat.cast_one, mul_one]
    rw [show α+2+2=α+4 by ring]
    field_simp [h2,h4,h6]
  · simp only [fzzScreeningHigherClearedRadial, fzzScreeningHigherPoleFactor, Nat.reduceAdd, Nat.cast_ofNat]
    rw [show α+2*2+2=α+6 by ring]
    field_simp [h2,h4,h6]
  · dsimp [fzzScreeningHigherClearedRadial]
    ring

private theorem original_local_restoration (α β : ℝ) (ha : -2 < α) :
    (∫ z : ℂ in ball 0 (1/2), fzzScreeningPlaneKernel α β z) =
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted α β z) +
        fzzScreeningFifthCounterterm α β := by
  have h := fzzScreeningFifthSubtracted_original_integral (Real.log (α+2)) β
  rw [Real.exp_log (by linarith : 0 < α+2)] at h
  simpa only [show -2+(α+2)=α by ring] using h

private theorem original_local_reflection (α β : ℝ) :
    (∫ z : ℂ in ball 0 (1/2), fzzScreeningPlaneKernel β α z) =
      ∫ z : ℂ in ball 1 (1/2), fzzScreeningPlaneKernel α β z := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).setIntegral_preimage_emb
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding (fzzScreeningPlaneKernel α β) (ball 1 (1/2))
  have hp : (fun z : ℂ => 1-z) ⁻¹' ball 1 (1/2) = ball 0 (1/2) := by
    ext z
    simp [mem_ball, dist_eq_norm]
  rw [hp] at h
  simpa only [fzzScreeningPlaneKernel_reflection] using h


private theorem higher_original_integral (α β : ℝ) (ha : -2 < α) (hb : -2 < β)
    (hs : α+β < -2) : fzzScreeningHigherClearedSource α β =
      fzzScreeningHigherPoleFactor α * fzzScreeningHigherPoleFactor β *
        (∫ z : ℂ, fzzScreeningPlaneKernel α β z) := by
  have hi := (original_plane_gamma α β ha hb hs).1
  have hu : (ball (0 : ℂ) (1/2) ∪ ball 1 (1/2)) ∪ fzzScreeningPlaneExterior = univ :=
    union_compl_self _
  have hm : MeasurableSet fzzScreeningPlaneExterior :=
    (isOpen_ball.union isOpen_ball).measurableSet.compl
  have hd : Disjoint (ball (0 : ℂ) (1/2) ∪ ball 1 (1/2)) fzzScreeningPlaneExterior :=
    disjoint_compl_right
  have hd01 : Disjoint (ball (0 : ℂ) (1/2)) (ball 1 (1/2)) :=
    ball_disjoint_ball (by norm_num [dist_eq_norm])
  have hh : (∫ z : ℂ, fzzScreeningPlaneKernel α β z) =
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningPlaneKernel α β z) +
      (∫ z : ℂ in ball 1 (1/2), fzzScreeningPlaneKernel α β z) +
      (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α β z) := by
    calc
      _ = ∫ z : ℂ in (ball 0 (1/2) ∪ ball 1 (1/2)) ∪ fzzScreeningPlaneExterior,
          fzzScreeningPlaneKernel α β z := by rw [hu, setIntegral_univ]
      _ = _ := by
        rw [setIntegral_union hd hm hi.integrableOn hi.integrableOn,
          setIntegral_union hd01 measurableSet_ball hi.integrableOn hi.integrableOn]
  rw [hh, ← original_local_reflection α β, original_local_restoration α β ha,
    original_local_restoration β α hb]
  unfold fzzScreeningHigherClearedSource
  rw [higher_counterterm_clearing α β ha, higher_counterterm_clearing β α hb]
  ring

/-- The cleared source is the original admitted whole-plane integral in the ordinary chamber. -/
theorem fzzScreeningHigherClearedSource_original (x y : ℝ) :
    fzzScreeningHigherClearedSource (-2*fzzScreeningBetaA x y) (-2*fzzScreeningBetaB x y) =
      fzzScreeningHigherPoleFactor (-2*fzzScreeningBetaA x y) *
        fzzScreeningHigherPoleFactor (-2*fzzScreeningBetaB x y) * fzzScreeningBetaIntegral x y := by
  obtain ⟨ha0,ha,hb0,hb,hs⟩ := fzzScreeningBeta_chamber x y
  exact higher_original_integral _ _ (by linarith) (by linarith) (by linarith)

/-- Explicit local cancellation preserves the three collision-line residues. -/
theorem fzzScreeningHigherClearedSource_pole_values (β : ℝ) :
    fzzScreeningHigherClearedSource (-2) β = 16*Real.pi*fzzScreeningHigherPoleFactor β ∧
    fzzScreeningHigherClearedSource (-4) β =
      -8*Real.pi*fzzScreeningFifthAngularCoefficient β 1*fzzScreeningHigherPoleFactor β ∧
    fzzScreeningHigherClearedSource (-6) β =
      16*Real.pi*fzzScreeningFifthAngularCoefficient β 2*fzzScreeningHigherPoleFactor β := by
  have hc0 : fzzScreeningFifthAngularCoefficient β 0 = 1 := rfl
  constructor
  · norm_num [fzzScreeningHigherClearedSource, fzzScreeningHigherClearedCounterterm,
      fzzScreeningHigherPoleFactor, Finset.sum_range_succ, fzzScreeningHigherClearedRadial, hc0]
    ring
  constructor
  · norm_num [fzzScreeningHigherClearedSource, fzzScreeningHigherClearedCounterterm,
      fzzScreeningHigherPoleFactor, Finset.sum_range_succ, fzzScreeningHigherClearedRadial, hc0]
    ring
  · norm_num [fzzScreeningHigherClearedSource, fzzScreeningHigherClearedCounterterm,
      fzzScreeningHigherPoleFactor, Finset.sum_range_succ, fzzScreeningHigherClearedRadial, hc0]
    ring

/-- Gamma family with all six collision factors cancelled before evaluation. -/
def fzzScreeningHigherClearedGamma (α β : ℝ) : ℝ :=
  64*Real.pi*Real.Gamma (-α/2-β/2-1)*Real.Gamma (4+α/2)*Real.Gamma (4+β/2)*
    (Real.Gamma (-α/2))⁻¹*(Real.Gamma (-β/2))⁻¹*(Real.Gamma (2+α/2+β/2))⁻¹

private theorem higher_gamma_shift (α : ℝ) (ha : -2 < α) :
    Real.Gamma (4+α/2) = fzzScreeningHigherPoleFactor α / 8 * Real.Gamma (1+α/2) := by
  have h1 : Real.Gamma (2+α/2) = (1+α/2)*Real.Gamma (1+α/2) := by
    convert Real.Gamma_add_one (show 1+α/2 ≠ 0 by linarith) using 1; congr 1; ring
  have h2 : Real.Gamma (3+α/2) = (2+α/2)*Real.Gamma (2+α/2) := by
    convert Real.Gamma_add_one (show 2+α/2 ≠ 0 by linarith) using 1; congr 1; ring
  have h3 : Real.Gamma (4+α/2) = (3+α/2)*Real.Gamma (3+α/2) := by
    convert Real.Gamma_add_one (show 3+α/2 ≠ 0 by linarith) using 1; congr 1; ring
  rw [h3,h2,h1]
  unfold fzzScreeningHigherPoleFactor
  ring

private theorem higher_gamma_clearing (α β : ℝ) (ha : -2 < α) (hb : -2 < β) :
    fzzScreeningHigherClearedGamma α β =
      fzzScreeningHigherPoleFactor α * fzzScreeningHigherPoleFactor β *
        fzzScreeningPlaneContinuedGamma α β := by
  unfold fzzScreeningHigherClearedGamma fzzScreeningPlaneContinuedGamma
  rw [higher_gamma_shift α ha, higher_gamma_shift β hb]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private theorem higher_original_gamma (α β : ℝ) (ha : -2 < α) (hb : -2 < β)
    (hs : α+β < -2) : fzzScreeningHigherClearedSource α β =
      fzzScreeningHigherClearedGamma α β := by
  rw [higher_original_integral α β ha hb hs, (original_plane_gamma α β ha hb hs).2,
    higher_gamma_clearing α β ha hb]

private theorem reciprocal_gamma_analytic (r : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => (Real.Gamma s)⁻¹) r := by
  have hc := Complex.differentiable_one_div_Gamma.analyticAt (r : ℂ)
  convert! hc.re_ofReal using 1
  simp only [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re]

private theorem positive_gamma_analytic (r : ℝ) (hr : 0 < r) :
    AnalyticAt ℝ Real.Gamma r := by
  have h := (reciprocal_gamma_analytic r).inv (inv_ne_zero (Real.Gamma_pos_of_pos hr).ne')
  convert! h using 1
  ext s
  simp

private theorem fzzScreeningHigherClearedGamma_analytic (α β : ℝ) (ha : -8 < α)
    (hs : α+β < -2) : AnalyticAt ℝ (fun s => fzzScreeningHigherClearedGamma s β) α := by
  have h1 : AnalyticAt ℝ (fun s : ℝ => -s/2-β/2-1) α := by fun_prop
  have h2 : AnalyticAt ℝ (fun s : ℝ => 4+s/2) α := by fun_prop
  have h3 : AnalyticAt ℝ (fun s : ℝ => -s/2) α := by fun_prop
  have h4 : AnalyticAt ℝ (fun s : ℝ => 2+s/2+β/2) α := by fun_prop
  have hg1 := (positive_gamma_analytic (-α/2-β/2-1) (by linarith)).comp_of_eq h1 rfl
  have hg2 := (positive_gamma_analytic (4+α/2) (by linarith)).comp_of_eq h2 rfl
  have hg3 := (reciprocal_gamma_analytic (-α/2)).comp_of_eq h3 rfl
  have hg4 := (reciprocal_gamma_analytic (2+α/2+β/2)).comp_of_eq h4 rfl
  exact (((((analyticAt_const.mul hg1).mul hg2).mul analyticAt_const).mul hg3).mul
    analyticAt_const).mul hg4

private theorem source_analytic_left (β : ℝ) (hb : -8 < β) :
    AnalyticOnNhd ℝ (fun α => fzzScreeningHigherClearedSource α β) (Ioo (-8) (-2-β)) := by
  have h := fzzScreeningHigherClearedSource_analytic_left (Real.log (β+8))
  rw [Real.exp_log (by linarith : 0 < β+8)] at h
  simpa only [show -8+(β+8) = β by ring] using h

private theorem source_analytic_right (α : ℝ) (ha : -8 < α) :
    AnalyticOnNhd ℝ (fun β => fzzScreeningHigherClearedSource α β) (Ioo (-8) (-2-α)) := by
  have h := fzzScreeningHigherClearedSource_analytic_right (Real.log (α+8))
  rw [Real.exp_log (by linarith : 0 < α+8)] at h
  simpa only [show -8+(α+8) = α by ring] using h

private theorem gamma_symm (α β : ℝ) : fzzScreeningHigherClearedGamma α β = fzzScreeningHigherClearedGamma β α := by
  unfold fzzScreeningHigherClearedGamma
  rw [show -α/2-β/2-1 = -β/2-α/2-1 by ring,
    show 2+α/2+β/2 = 2+β/2+α/2 by ring]
  ring

private theorem gamma_analytic_left (β : ℝ) :
    AnalyticOnNhd ℝ (fun α => fzzScreeningHigherClearedGamma α β) (Ioo (-8) (-2-β)) := by
  intro α hα
  exact fzzScreeningHigherClearedGamma_analytic α β hα.1 (by linarith [hα.2])

private theorem gamma_analytic_right (α : ℝ) :
    AnalyticOnNhd ℝ (fun β => fzzScreeningHigherClearedGamma α β) (Ioo (-8) (-2-α)) := by
  intro β hβ
  have h := gamma_analytic_left α β hβ
  apply h.congr
  filter_upwards with s
  exact gamma_symm s α

private theorem first_slice_identity (α β : ℝ) (ha : -8 < α) (hb : -2 < β)
    (hb0 : β < 0) (hs : α+β < -2) :
    fzzScreeningHigherClearedSource α β = fzzScreeningHigherClearedGamma α β := by
  let a0 := -2-β/2
  have h0 : a0 ∈ Ioo (-8 : ℝ) (-2-β) := by
    dsimp [a0]
    constructor <;> linarith
  have he : (fun a => fzzScreeningHigherClearedSource a β) =ᶠ[𝓝 a0]
      (fun a => fzzScreeningHigherClearedGamma a β) := by
    have hn : ∀ᶠ a : ℝ in 𝓝 a0, -2 < a ∧ a+β < -2 := by
      have hm : a0 ∈ Ioo (-2 : ℝ) (-2-β) := by
        dsimp [a0]
        constructor <;> linarith
      filter_upwards [isOpen_Ioo.mem_nhds hm] with a ha
      exact ⟨ha.1, by linarith [ha.2]⟩
    filter_upwards [hn] with a ha
    exact higher_original_gamma a β ha.1 hb ha.2
  have heq := (source_analytic_left β (by linarith)).eqOn_of_preconnected_of_eventuallyEq
    (gamma_analytic_left β) isPreconnected_Ioo h0 he
  exact heq ⟨ha, by linarith⟩

private theorem second_slice_identity (α β : ℝ) (ha : -8 < α) (ha1 : α < -1)
    (hb : -8 < β) (hs : α+β < -2) :
    fzzScreeningHigherClearedSource α β = fzzScreeningHigherClearedGamma α β := by
  have h0 : (-1 : ℝ) ∈ Ioo (-8) (-2-α) := by
    constructor <;> linarith
  have he : (fun b => fzzScreeningHigherClearedSource α b) =ᶠ[𝓝 (-1 : ℝ)]
      (fun b => fzzScreeningHigherClearedGamma α b) := by
    have hn : ∀ᶠ b : ℝ in 𝓝 (-1 : ℝ), b ∈ Ioo (-2) (min 0 (-2-α)) :=
      isOpen_Ioo.mem_nhds ⟨by norm_num, lt_min (by norm_num) (by linarith)⟩
    filter_upwards [hn] with b hb
    have hh := lt_min_iff.mp hb.2
    exact first_slice_identity α b ha hb.1 hh.1 (by linarith [hh.2])
  have heq := (source_analytic_right α ha).eqOn_of_preconnected_of_eventuallyEq
    (gamma_analytic_right α) isPreconnected_Ioo h0 he
  exact heq ⟨hb, by linarith⟩

private theorem higher_cleared_identity (α β : ℝ) (ha : -8 < α) (hb : -8 < β)
    (hs : α+β < -2) : fzzScreeningHigherClearedSource α β =
      fzzScreeningHigherClearedGamma α β := by
  by_cases hα : α < -1
  · exact second_slice_identity α β ha hα hb hs
  · rw [fzzScreeningHigherClearedSource_symm α β, gamma_symm α β]
    exact second_slice_identity β α hb (by linarith) ha (by linarith)

/-- Independent positive coordinates for the full higher collision and tail chamber. -/
def fzzScreeningHigherPowerA (u v : ℝ) : ℝ :=
  -8+14*Real.exp u/(1+Real.exp u+Real.exp v)

/-- The second original exponent in the same full continuation chamber. -/
def fzzScreeningHigherPowerB (u v : ℝ) : ℝ :=
  -8+14*Real.exp v/(1+Real.exp u+Real.exp v)

/-- Both punctures and the original exterior remain admitted throughout this chart. -/
theorem fzzScreeningHigherPower_chamber (u v : ℝ) :
    -8 < fzzScreeningHigherPowerA u v ∧ -8 < fzzScreeningHigherPowerB u v ∧
      fzzScreeningHigherPowerA u v+fzzScreeningHigherPowerB u v < -2 := by
  have hd : 0 < 1+Real.exp u+Real.exp v := by positivity
  have hu : 0 < 14*Real.exp u/(1+Real.exp u+Real.exp v) := by positivity
  have hv : 0 < 14*Real.exp v/(1+Real.exp u+Real.exp v) := by positivity
  unfold fzzScreeningHigherPowerA fzzScreeningHigherPowerB
  refine ⟨by linarith, by linarith, ?_⟩
  have h : (14*Real.exp u+14*Real.exp v)/(1+Real.exp u+Real.exp v) < 14 := by
    rw [div_lt_iff₀ hd]
    linarith
  rw [add_div] at h
  linarith

/-- Equality follows from the original integral and two real analytic identity arguments,
including the collision lines, throughout the full higher chamber. -/
theorem fzzScreeningHigherClearedSource_eq_gamma (u v : ℝ) :
    fzzScreeningHigherClearedSource (fzzScreeningHigherPowerA u v) (fzzScreeningHigherPowerB u v) =
      fzzScreeningHigherClearedGamma (fzzScreeningHigherPowerA u v) (fzzScreeningHigherPowerB u v) := by
  obtain ⟨ha,hb,hs⟩ := fzzScreeningHigherPower_chamber u v
  exact higher_cleared_identity _ _ ha hb hs



/-- The source chart covers the entire admitted higher chamber. -/
theorem fzzScreeningHigherPower_chart_iff (α β : ℝ) :
    (∃ u v : ℝ, fzzScreeningHigherPowerA u v = α ∧ fzzScreeningHigherPowerB u v = β) ↔
      -8 < α ∧ -8 < β ∧ α+β < -2 := by
  constructor
  · rintro ⟨u,v,rfl,rfl⟩
    exact fzzScreeningHigherPower_chamber u v
  · rintro ⟨ha,hb,hs⟩
    have hd : 0 < -2-α-β := by linarith
    have hu : 0 < (α+8)/(-2-α-β) := div_pos (by linarith) hd
    have hv : 0 < (β+8)/(-2-α-β) := div_pos (by linarith) hd
    have he : 1+(α+8)/(-2-α-β)+(β+8)/(-2-α-β) = 14/(-2-α-β) := by
      field_simp
      ring
    refine ⟨Real.log ((α+8)/(-2-α-β)), Real.log ((β+8)/(-2-α-β)), ?_, ?_⟩
    · unfold fzzScreeningHigherPowerA
      rw [Real.exp_log hu, Real.exp_log hv, he]
      field_simp
      ring
    · unfold fzzScreeningHigherPowerB
      rw [Real.exp_log hu, Real.exp_log hv, he]
      field_simp
      ring

private theorem higher_source_mixed_jet (α β : ℝ) (ha : -8 < α) (hb : -8 < β)
    (hs : α+β < -2) (m n : ℕ) :
    iteratedDeriv m (fun a => iteratedDeriv n (fun b => fzzScreeningHigherClearedSource a b) β) α =
      iteratedDeriv m (fun a => iteratedDeriv n (fun b => fzzScreeningHigherClearedGamma a b) β) α := by
  have houter : ∀ᶠ a : ℝ in 𝓝 α, a ∈ Ioo (-8) (-2-β) :=
    isOpen_Ioo.mem_nhds ⟨ha, by linarith⟩
  apply Filter.EventuallyEq.iteratedDeriv_eq m
  filter_upwards [houter] with a ha'
  have hinner : ∀ᶠ b : ℝ in 𝓝 β, b ∈ Ioo (-8) (-2-a) :=
    isOpen_Ioo.mem_nhds ⟨hb, by linarith [ha'.2]⟩
  apply Filter.EventuallyEq.iteratedDeriv_eq n
  filter_upwards [hinner] with b hb'
  exact higher_cleared_identity a b ha'.1 hb'.1 (by linarith [hb'.2])

/-- Every mixed finite jet of the actual cleared integral source agrees with its Gamma family.
This does not yet identify the finite part of the uncleared original cutoff at a pole. -/
theorem fzzScreeningHigherClearedSource_mixed_jet (u v : ℝ) (m n : ℕ) :
    iteratedDeriv m (fun a => iteratedDeriv n (fun b => fzzScreeningHigherClearedSource a b)
      (fzzScreeningHigherPowerB u v)) (fzzScreeningHigherPowerA u v) =
    iteratedDeriv m (fun a => iteratedDeriv n (fun b => fzzScreeningHigherClearedGamma a b)
      (fzzScreeningHigherPowerB u v)) (fzzScreeningHigherPowerA u v) := by
  obtain ⟨ha,hb,hs⟩ := fzzScreeningHigherPower_chamber u v
  exact higher_source_mixed_jet _ _ ha hb hs m n

/-- The original cubic collision lies inside the proved source identity domain. -/
theorem fzzScreeningHigherClearedSource_cubic_mixed_jet (m n : ℕ) :
    iteratedDeriv m (fun a => iteratedDeriv n (fun b => fzzScreeningHigherClearedSource a b) (-6)) (-6) =
    iteratedDeriv m (fun a => iteratedDeriv n (fun b => fzzScreeningHigherClearedGamma a b) (-6)) (-6) :=
  higher_source_mixed_jet _ _ (by norm_num) (by norm_num) (by norm_num) m n


end GaloisForLFunctions.RHTower
