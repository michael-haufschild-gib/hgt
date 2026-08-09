import GaloisForLFunctions.RHTower.BurnolFirstWallExteriorMass

/-!
# The aperture-crossing correlation of the zero-divided source

On the logarithmic ray the unitary lift of a positive-ray function is `G(u) = e^{u/2} g(e^u)` and
the fixed aperture sits at `β = log(1/2)`.  The aperture-crossing correlation

`W_G(s) = ∫_ℝ conj(G(v+s)) (1_{v+s ≤ β} - 1_{v ≤ β}) G(v) dv`

has, for `s > 0`, indicator weight `-1` exactly on the window `(β-s, β]`.  On that window the
lifted source is the constant head times `e^{v/2}`, so the exponential substitution `t = e^{v+s}`
collapses the correlation to

`W_G(s) = -a e^{-s/2} ∫_{1/2}^{e^s/2} conj(g)`.

Letting `s → ∞` produces the singular first-wall Cartier residue `-a conj(B)`, which is exactly the
abstract residue of the polarization layer.
-/

open Complex Real MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-! ## The logarithmic lift and the crossing weight -/

/-- The logarithmic unitary lift of a positive-ray function. -/
def burnolLogLift (g : ℝ → ℂ) (u : ℝ) : ℂ := ((Real.exp (u / 2) : ℝ) : ℂ) * g (Real.exp u)

/-- The fixed aperture in logarithmic coordinates. -/
def burnolApertureLog : ℝ := -Real.log 2

theorem exp_burnolApertureLog : Real.exp burnolApertureLog = 1 / 2 := by
  rw [burnolApertureLog, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

/-- The indicator weight of the aperture-crossing correlation. -/
def burnolCrossingWeight (s v : ℝ) : ℝ :=
  (if v + s ≤ burnolApertureLog then (1 : ℝ) else 0) -
    (if v ≤ burnolApertureLog then (1 : ℝ) else 0)

/-- The aperture-crossing correlation. -/
def burnolCrossingCorrelationW (g : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ v : ℝ, (starRingEnd ℂ) (burnolLogLift g (v + s)) *
    ((burnolCrossingWeight s v : ℝ) : ℂ) * burnolLogLift g v

theorem burnolCrossingWeight_eq_neg_indicator {s : ℝ} (hs : 0 < s) (v : ℝ) :
    burnolCrossingWeight s v =
      -(Set.indicator (Ioc (burnolApertureLog - s) burnolApertureLog) (fun _ => (1 : ℝ)) v) := by
  rw [burnolCrossingWeight]
  by_cases h1 : v ≤ burnolApertureLog
  · by_cases h3 : v + s ≤ burnolApertureLog
    · have hmem : v ∉ Ioc (burnolApertureLog - s) burnolApertureLog := by
        intro hc
        linarith [hc.1]
      rw [if_pos h3, if_pos h1, Set.indicator_of_notMem hmem]
      norm_num
    · have hmem : v ∈ Ioc (burnolApertureLog - s) burnolApertureLog := ⟨by linarith, h1⟩
      rw [if_neg h3, if_pos h1, Set.indicator_of_mem hmem]
      norm_num
  · have h3 : ¬ (v + s ≤ burnolApertureLog) := by
      intro hc
      exact h1 (by linarith)
    have hmem : v ∉ Ioc (burnolApertureLog - s) burnolApertureLog := fun hc => h1 hc.2
    rw [if_neg h3, if_neg h1, Set.indicator_of_notMem hmem]
    norm_num

theorem burnolCrossingCorrelationW_eq_window {g : ℝ → ℂ} {s : ℝ} (hs : 0 < s) :
    burnolCrossingCorrelationW g s =
      -∫ v in Ioc (burnolApertureLog - s) burnolApertureLog,
        (starRingEnd ℂ) (burnolLogLift g (v + s)) * burnolLogLift g v := by
  rw [burnolCrossingCorrelationW]
  have hpt : ∀ v : ℝ,
      (starRingEnd ℂ) (burnolLogLift g (v + s)) * ((burnolCrossingWeight s v : ℝ) : ℂ) *
          burnolLogLift g v =
        Set.indicator (Ioc (burnolApertureLog - s) burnolApertureLog)
          (fun w : ℝ => -((starRingEnd ℂ) (burnolLogLift g (w + s)) * burnolLogLift g w)) v := by
    intro v
    rw [burnolCrossingWeight_eq_neg_indicator hs v]
    by_cases hv : v ∈ Ioc (burnolApertureLog - s) burnolApertureLog
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
      push_cast
      ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_indicator measurableSet_Ioc, MeasureTheory.integral_neg]

/-! ## The exponential window substitution -/

theorem burnolExpShift_image {a b s : ℝ} :
    (fun v : ℝ => Real.exp (v + s)) '' Ioc a b = Ioc (Real.exp (a + s)) (Real.exp (b + s)) := by
  ext t
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Real.exp_lt_exp.mpr (by linarith [hv.1]), Real.exp_le_exp.mpr (by linarith [hv.2])⟩
  · rintro ⟨h1, h2⟩
    have ht : 0 < t := lt_trans (Real.exp_pos _) h1
    refine ⟨Real.log t - s, ⟨?_, ?_⟩, ?_⟩
    · have := Real.log_lt_log (Real.exp_pos (a + s)) h1
      rw [Real.log_exp] at this
      linarith
    · have h3 := Real.log_le_log ht h2
      rw [Real.log_exp] at h3
      linarith
    · show Real.exp (Real.log t - s + s) = t
      rw [show Real.log t - s + s = Real.log t by ring, Real.exp_log ht]

theorem integral_burnolExpShiftSubstitution (F : ℝ → ℂ) (a b s : ℝ) :
    (∫ t in Ioc (Real.exp (a + s)) (Real.exp (b + s)), F t) =
      ∫ v in Ioc a b, Real.exp (v + s) • F (Real.exp (v + s)) := by
  have hderiv : ∀ v ∈ Ioc a b,
      HasDerivWithinAt (fun w : ℝ => Real.exp (w + s)) (Real.exp (v + s)) (Ioc a b) v := by
    intro v _
    have h : HasDerivAt (fun w : ℝ => Real.exp (w + s)) (Real.exp (v + s) * 1) v :=
      ((hasDerivAt_id v).add_const s).exp
    exact (h.congr_deriv (by ring)).hasDerivWithinAt
  have hinj : Set.InjOn (fun v : ℝ => Real.exp (v + s)) (Ioc a b) := by
    intro u _ v _ huv
    have := Real.exp_eq_exp.mp huv
    linarith
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun v : ℝ => Real.exp (v + s)) (f' := fun v : ℝ => Real.exp (v + s))
    (s := Ioc a b) measurableSet_Ioc hderiv hinj F
  rw [burnolExpShift_image] at hcov
  rw [hcov]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
  rw [abs_of_pos (Real.exp_pos _)]

/-! ## The collapsed correlation of the zero-divided source -/

/-- A positive-ray function is *aperture constant* with value `c` when it equals `c` on the
fixed aperture `(0, 1/2]`. -/
def BurnolApertureHead (g : ℝ → ℂ) (c : ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → g t = c

theorem burnolLogLift_of_apertureHead {g : ℝ → ℂ} {c : ℂ} (hhead : BurnolApertureHead g c)
    {v : ℝ} (hv : v ≤ burnolApertureLog) :
    burnolLogLift g v = ((Real.exp (v / 2) : ℝ) : ℂ) * c := by
  rw [burnolLogLift]
  congr 1
  refine hhead _ (Real.exp_pos v) ?_
  have h := Real.exp_le_exp.mpr hv
  rwa [exp_burnolApertureLog] at h

theorem xiDivisor_burnolZeroDividedSource_apertureHead {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) :
    BurnolApertureHead (burnolZeroDividedSource ρ) (burnolFirstWallHead ρ) :=
  fun _ ht hthalf => xiDivisor_burnolZeroDividedSource_head_eq hρ0 hρ1 hxi ht hthalf

/-- **The collapsed crossing correlation.**  For positive lag the correlation is the head times a
half-line window of the conjugated source. -/
theorem burnolCrossingCorrelationW_eq_of_head {g : ℝ → ℂ} {c : ℂ}
    (hhead : BurnolApertureHead g c) {s : ℝ} (hs : 0 < s) :
    burnolCrossingCorrelationW g s =
      -c * ((Real.exp (-s / 2) : ℝ) : ℂ) *
        ∫ t in Ioc (1 / 2 : ℝ) (Real.exp s / 2), (starRingEnd ℂ) (g t) := by
  rw [burnolCrossingCorrelationW_eq_window hs]
  set F : ℝ → ℂ := fun t => (starRingEnd ℂ) (g t) with hF
  have hint : ∀ v ∈ Ioc (burnolApertureLog - s) burnolApertureLog,
      (starRingEnd ℂ) (burnolLogLift g (v + s)) * burnolLogLift g v =
        (c * ((Real.exp (-s / 2) : ℝ) : ℂ)) *
          (Real.exp (v + s) • F (Real.exp (v + s))) := by
    intro v hv
    rw [burnolLogLift_of_apertureHead hhead hv.2, burnolLogLift, map_mul,
      Complex.conj_ofReal, Complex.real_smul, hF]
    have hexp : ((Real.exp ((v + s) / 2) : ℝ) : ℂ) * ((Real.exp (v / 2) : ℝ) : ℂ) =
        ((Real.exp (-s / 2) : ℝ) : ℂ) * ((Real.exp (v + s) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    calc ((Real.exp ((v + s) / 2) : ℝ) : ℂ) * (starRingEnd ℂ) (g (Real.exp (v + s))) *
            (((Real.exp (v / 2) : ℝ) : ℂ) * c)
        = (((Real.exp ((v + s) / 2) : ℝ) : ℂ) * ((Real.exp (v / 2) : ℝ) : ℂ)) *
            (c * (starRingEnd ℂ) (g (Real.exp (v + s)))) := by ring
      _ = _ := by rw [hexp]; ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hint,
    MeasureTheory.integral_const_mul, ← integral_burnolExpShiftSubstitution F
      (burnolApertureLog - s) burnolApertureLog s]
  have h1 : Real.exp (burnolApertureLog - s + s) = 1 / 2 := by
    rw [show burnolApertureLog - s + s = burnolApertureLog by ring, exp_burnolApertureLog]
  have h2 : Real.exp (burnolApertureLog + s) = Real.exp s / 2 := by
    rw [Real.exp_add, exp_burnolApertureLog]
    ring
  rw [h1, h2, hF]
  ring


/-! ## The singular first-wall residue -/

theorem tendsto_burnolCrossingWindow {g : ℝ → ℂ}
    (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) :
    Tendsto (fun s : ℝ => ∫ t in Ioc (1 / 2 : ℝ) (Real.exp s / 2),
        (starRingEnd ℂ) (g t)) atTop
      (𝓝 ((starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t))) := by
  have hexp : Tendsto (fun s : ℝ => Real.exp s / 2) atTop atTop :=
    Real.tendsto_exp_atTop.atTop_div_const (by norm_num)
  have hbase : Tendsto (fun X : ℝ => ∫ t in (1 / 2 : ℝ)..X, g t) atTop
      (𝓝 (∫ t in Ioi (1 / 2 : ℝ), g t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi _ hIoi tendsto_id
  have hcomp := hbase.comp hexp
  have hIoc : Tendsto (fun s : ℝ => ∫ t in Ioc (1 / 2 : ℝ) (Real.exp s / 2), g t) atTop
      (𝓝 (∫ t in Ioi (1 / 2 : ℝ), g t)) := by
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have hle : (1 / 2 : ℝ) ≤ Real.exp s / 2 := by
      have := Real.one_le_exp hs
      linarith
    rw [Function.comp_apply, intervalIntegral.integral_of_le hle]
  have hconj := (Complex.continuous_conj.tendsto _).comp hIoc
  refine hconj.congr fun s => ?_
  rw [Function.comp_apply, ← integral_conj]

/-- **The singular first-wall Cartier residue of the actual source.** -/
theorem tendsto_burnolCrossingResidue {g : ℝ → ℂ} {c : ℂ} (hhead : BurnolApertureHead g c)
    (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) :
    Tendsto (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) * burnolCrossingCorrelationW g s) atTop
      (𝓝 (-c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t))) := by
  have hmain := (tendsto_burnolCrossingWindow hIoi).const_mul (-c)
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [burnolCrossingCorrelationW_eq_of_head hhead hs]
  have hcancel : ((Real.exp (s / 2) : ℝ) : ℂ) * ((Real.exp (-s / 2) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show s / 2 + -s / 2 = 0 by ring, Real.exp_zero]
    norm_num
  calc -c * ∫ t in Ioc (1 / 2 : ℝ) (Real.exp s / 2), (starRingEnd ℂ) (g t)
      = (((Real.exp (s / 2) : ℝ) : ℂ) * ((Real.exp (-s / 2) : ℝ) : ℂ)) *
          (-c * ∫ t in Ioc (1 / 2 : ℝ) (Real.exp s / 2), (starRingEnd ℂ) (g t)) := by
        rw [hcancel]; ring
    _ = _ := by ring

/-- The collapsed correlation of the actual zero-divided source. -/
theorem xiDivisor_burnolCrossingCorrelationW_eq {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {s : ℝ} (hs : 0 < s) :
    burnolCrossingCorrelationW (burnolZeroDividedSource ρ) s =
      -(burnolFirstWallHead ρ) * ((Real.exp (-s / 2) : ℝ) : ℂ) *
        ∫ t in Ioc (1 / 2 : ℝ) (Real.exp s / 2),
          (starRingEnd ℂ) (burnolZeroDividedSource ρ t) :=
  burnolCrossingCorrelationW_eq_of_head
    (xiDivisor_burnolZeroDividedSource_apertureHead hρ0 hρ1 hxi) hs

/-- **The singular first-wall Cartier residue of the actual source.** -/
theorem xiDivisor_tendsto_burnolFirstWallResidue {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) :
    Tendsto (fun s : ℝ => ((Real.exp (s / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW (burnolZeroDividedSource ρ) s) atTop
      (𝓝 (burnolFirstWallResidue ρ)) := by
  have hIoi : IntegrableOn (burnolZeroDividedSource ρ) (Ioi (1 / 2 : ℝ)) :=
    (integrableOn_burnolZeroDividedSource hρ0 hρ1 hxi).mono_set
      (fun x hx => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hx)))
  have h := tendsto_burnolCrossingResidue
    (xiDivisor_burnolZeroDividedSource_apertureHead hρ0 hρ1 hxi) hIoi
  rwa [xiDivisor_integral_burnolZeroDividedSource_exterior hρ0 hρ1 hxi] at h

/-- **The deep depth profile.**  Along the dyadic ladder the normalized correlation converges to
the residue times the `A`-null mode. -/
theorem xiDivisor_tendsto_burnolCrossingDepthProfile {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) (r : ℝ) :
    Tendsto (fun n : ℕ => ((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW (burnolZeroDividedSource ρ)
          ((n : ℝ) * Real.log 2 + r)) atTop
      (𝓝 (burnolFirstWallResidue ρ * ((Real.exp (-r / 2) : ℝ) : ℂ))) := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) * Real.log 2 + r) atTop atTop := by
    refine Filter.Tendsto.atTop_add ?_ tendsto_const_nhds
    exact Filter.Tendsto.atTop_mul_const (Real.log_pos (by norm_num))
      tendsto_natCast_atTop_atTop
  have hcomp := ((xiDivisor_tendsto_burnolFirstWallResidue hρ0 hρ1 hxi).comp hshift).mul_const
    ((Real.exp (-r / 2) : ℝ) : ℂ)
  refine hcomp.congr fun n => ?_
  rw [Function.comp_apply]
  have hsplit : ((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) =
      ((Real.exp (((n : ℝ) * Real.log 2 + r) / 2) : ℝ) : ℂ) * ((Real.exp (-r / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [hsplit]
  ring

end RHTower
