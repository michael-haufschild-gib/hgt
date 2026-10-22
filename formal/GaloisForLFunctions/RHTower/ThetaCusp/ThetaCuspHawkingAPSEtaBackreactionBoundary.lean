import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo

/-!
# Hawking edge eta and topological-black-hole mass jet

For a thermal-circle shift `0 < a < 1`, the positive and negative spectra have magnitudes
`n + a` and `n + 1 - a`. Their heat-regularized eta invariant tends to `1 - 2*a`.

For the four-dimensional topological black hole, write `x = r₊/l`. Birmingham--Mokhtari's
mass and surface gravity become `m(x) = x*(x²-1)` and `kappa(x) = (3*x²-1)/(2*x)`.
At the massless hole `x=1`, both derivatives equal two. The fixed-frequency ingoing exponent
therefore has mass jet `decay/2`. Applied to reflected real-pair QNM frequencies, its defect is
half the thermal-circle eta invariant and vanishes exactly on the critical line.

Reflection-pair eta cancels unconditionally. APS index balance alone therefore cannot select RH;
sector-local cancellation is the stronger RH-equivalent condition. No claim here identifies the
effective thermal edge operator with the full nonlinear Teukolsky Calderón boundary operator.
-/

open Filter Topology

namespace RHTower

noncomputable section

def thermalCirclePositiveHeatTrace (a t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-t * ((n : ℝ) + a))

def thermalCircleNegativeHeatTrace (a t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-t * ((n : ℝ) + (1 - a)))

def thermalCircleHeatEta (a t : ℝ) : ℝ :=
  thermalCirclePositiveHeatTrace a t - thermalCircleNegativeHeatTrace a t

def thermalCircleAPSEta (a : ℝ) : ℝ := 1 - 2 * a

theorem thermalCirclePositiveHeatTrace_eq
    (a : ℝ) {t : ℝ} (ht : 0 < t) :
    thermalCirclePositiveHeatTrace a t =
      Real.exp (-t * a) / (1 - Real.exp (-t)) := by
  have hr0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hterm : ∀ n : ℕ,
      Real.exp (-t * ((n : ℝ) + a)) =
        Real.exp (-t * a) * Real.exp (-t) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [thermalCirclePositiveHeatTrace, tsum_congr hterm,
    tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [div_eq_mul_inv]

theorem thermalCircleNegativeHeatTrace_eq
    (a : ℝ) {t : ℝ} (ht : 0 < t) :
    thermalCircleNegativeHeatTrace a t =
      Real.exp (-t * (1 - a)) / (1 - Real.exp (-t)) := by
  have h := thermalCirclePositiveHeatTrace_eq (1 - a) ht
  simpa [thermalCircleNegativeHeatTrace,
    thermalCirclePositiveHeatTrace] using h

theorem thermalCircleHeatEta_eq
    (a : ℝ) {t : ℝ} (ht : 0 < t) :
    thermalCircleHeatEta a t =
      (Real.exp (-t * a) - Real.exp (-t * (1 - a))) /
        (1 - Real.exp (-t)) := by
  rw [thermalCircleHeatEta, thermalCirclePositiveHeatTrace_eq a ht,
    thermalCircleNegativeHeatTrace_eq a ht]
  ring

private theorem tendsto_ratio_of_hasDerivAt_zero
    {f g : ℝ → ℝ} {A B : ℝ}
    (hf : HasDerivAt f A 0) (hf0 : f 0 = 0)
    (hg : HasDerivAt g B 0) (hg0 : g 0 = 0) (hB : B ≠ 0)
    (hgne : ∀ t, t ≠ 0 → g t ≠ 0) :
    Tendsto (fun t => f t / g t) (𝓝[≠] 0) (𝓝 (A / B)) := by
  have hquot := hf.tendsto_slope.div hg.tendsto_slope hB
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  change slope f 0 t / slope g 0 t = f t / g t
  rw [slope_def_field, slope_def_field, hf0, hg0]
  field_simp [ht0, hgne t ht0]
  ring

theorem thermalCircleHeatEta_tendsto (a : ℝ) :
    Tendsto
      (fun t =>
        (Real.exp (-t * a) - Real.exp (-t * (1 - a))) /
          (1 - Real.exp (-t)))
      (𝓝[≠] 0) (𝓝 (thermalCircleAPSEta a)) := by
  let f : ℝ → ℝ := fun t =>
    Real.exp (-t * a) - Real.exp (-t * (1 - a))
  let g : ℝ → ℝ := fun t => 1 - Real.exp (-t)
  have hf : HasDerivAt f (1 - 2 * a) 0 := by
    dsimp [f]
    have h1 : HasDerivAt (fun t : ℝ => -t * a) (-a) 0 :=
      by simpa using! (hasDerivAt_id (𝕜 := ℝ) 0).neg.mul_const a
    have h2 : HasDerivAt (fun t : ℝ => -t * (1 - a)) (-(1 - a)) 0 :=
      by simpa using! (hasDerivAt_id (𝕜 := ℝ) 0).neg.mul_const (1 - a)
    have hraw := h1.exp.sub h2.exp
    rw [show (fun t : ℝ => Real.exp (-t * a) - Real.exp (-t * (1 - a))) =
      (fun t : ℝ => Real.exp (-t * a)) -
        (fun t : ℝ => Real.exp (-t * (1 - a))) by rfl]
    exact hraw.congr_deriv (by norm_num; ring)
  have hg : HasDerivAt g 1 0 := by
    dsimp [g]
    have hneg : HasDerivAt (fun t : ℝ => -t) (-1) 0 :=
      (hasDerivAt_id (𝕜 := ℝ) 0).neg
    simpa using! (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hneg.exp
  have hlim := tendsto_ratio_of_hasDerivAt_zero hf (by simp [f])
    hg (by simp [g]) (by norm_num) (by
      intro t ht hzero
      have hexp : Real.exp (-t) = 1 := by linarith
      have : -t = 0 := by
        apply Real.exp_injective
        simpa using hexp
      exact ht (by linarith))
  simpa [f, g, thermalCircleAPSEta] using hlim

theorem thermalCircleHeatEta_tendsto_zero_right (a : ℝ) :
    Tendsto (thermalCircleHeatEta a) (𝓝[>] 0)
      (𝓝 (thermalCircleAPSEta a)) := by
  have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := by
    apply nhdsWithin_mono
    intro t ht
    simpa using ne_of_gt ht
  have hclosed := (thermalCircleHeatEta_tendsto a).mono_left hmono
  apply hclosed.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (thermalCircleHeatEta_eq a ht).symm

lemma thermalCircleAPSEta_reflect (a : ℝ) :
    thermalCircleAPSEta (1 - a) = -thermalCircleAPSEta a := by
  unfold thermalCircleAPSEta
  ring

theorem thermalCircleAPSEta_reflection_pair_cancel (a : ℝ) :
    thermalCircleAPSEta a + thermalCircleAPSEta (1 - a) = 0 := by
  rw [thermalCircleAPSEta_reflect]
  ring

def d4TopologicalBlackHoleDimensionlessMass (x : ℝ) : ℝ :=
  x * (x ^ (2 : ℕ) - 1)

def d4TopologicalBlackHoleDimensionlessSurfaceGravity (x : ℝ) : ℝ :=
  (3 * x ^ (2 : ℕ) - 1) / (2 * x)

def d4TopologicalBlackHoleIngoingExponent (x decay : ℝ) : ℝ :=
  -decay / (2 * d4TopologicalBlackHoleDimensionlessSurfaceGravity x)

def d4TopologicalBlackHoleIngoingExponentMassJet (decay : ℝ) : ℝ :=
  deriv (fun x => d4TopologicalBlackHoleIngoingExponent x decay) 1 /
    deriv d4TopologicalBlackHoleDimensionlessMass 1

lemma hasDerivAt_d4TopologicalBlackHoleDimensionlessMass_one :
    HasDerivAt d4TopologicalBlackHoleDimensionlessMass 2 1 := by
  unfold d4TopologicalBlackHoleDimensionlessMass
  have hx : HasDerivAt (fun x : ℝ => x) 1 1 := hasDerivAt_id 1
  have hs := (hx.pow 2).sub_const 1
  simpa using! hx.mul hs

lemma hasDerivAt_d4TopologicalBlackHoleDimensionlessSurfaceGravity_one :
    HasDerivAt d4TopologicalBlackHoleDimensionlessSurfaceGravity 2 1 := by
  unfold d4TopologicalBlackHoleDimensionlessSurfaceGravity
  have hx : HasDerivAt (fun x : ℝ => x) 1 1 := hasDerivAt_id 1
  have hnum := ((hx.pow 2).const_mul 3).sub_const 1
  have hden := hx.const_mul 2
  have hraw := hnum.div hden (by norm_num)
  rw [show (fun x : ℝ => (3 * x ^ (2 : ℕ) - 1) / (2 * x)) =
    (fun x : ℝ => 3 * x ^ (2 : ℕ) - 1) / (fun x : ℝ => 2 * x) by rfl]
  exact hraw.congr_deriv (by norm_num)

lemma hasDerivAt_d4TopologicalBlackHoleIngoingExponent_one (decay : ℝ) :
    HasDerivAt (fun x => d4TopologicalBlackHoleIngoingExponent x decay) decay 1 := by
  unfold d4TopologicalBlackHoleIngoingExponent
  have hk := hasDerivAt_d4TopologicalBlackHoleDimensionlessSurfaceGravity_one
  have hden := hk.const_mul 2
  have hnum := hasDerivAt_const (x := (1 : ℝ)) (c := -decay)
  have hraw := hnum.div hden
    (by norm_num [d4TopologicalBlackHoleDimensionlessSurfaceGravity])
  rw [show (fun x : ℝ => -decay /
      (2 * d4TopologicalBlackHoleDimensionlessSurfaceGravity x)) =
    (fun _ : ℝ => -decay) /
      (fun x : ℝ => 2 * d4TopologicalBlackHoleDimensionlessSurfaceGravity x) by rfl]
  exact hraw.congr_deriv (by
    norm_num [d4TopologicalBlackHoleDimensionlessSurfaceGravity])

theorem d4TopologicalBlackHoleIngoingExponentMassJet_eq (decay : ℝ) :
    d4TopologicalBlackHoleIngoingExponentMassJet decay = decay / 2 := by
  rw [d4TopologicalBlackHoleIngoingExponentMassJet,
    (hasDerivAt_d4TopologicalBlackHoleIngoingExponent_one decay).deriv,
    hasDerivAt_d4TopologicalBlackHoleDimensionlessMass_one.deriv]

def d4BMXiReflectedRealPairDecay (n : ℕ) (q : XiZeroCopy) : ℝ :=
  4 * n + 3 - (q.1 : ℂ).re

def d4BMXiReflectedHorizonMassJetDefect (n : ℕ) (q : XiZeroCopy) : ℝ :=
  d4TopologicalBlackHoleIngoingExponentMassJet
      (d4BMXiReflectedRealPairDecay n q) -
    d4TopologicalBlackHoleIngoingExponentMassJet
      (d4BMXiReflectedRealPairDecay n (xiZeroCopyReflectEquiv q))

lemma d4BMXiReflectedRealPairFrequency_eq_decay (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedRealPairFrequency n q =
      -Complex.I * (d4BMXiReflectedRealPairDecay n q : ℂ) := by
  rw [d4BMXiReflectedRealPairFrequency_eq]
  simp [d4BMXiReflectedRealPairDecay]

theorem d4BMXiReflectedHorizonMassJetDefect_eq (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedHorizonMassJetDefect n q =
      (1 - 2 * (q.1 : ℂ).re) / 2 := by
  rw [d4BMXiReflectedHorizonMassJetDefect,
    d4TopologicalBlackHoleIngoingExponentMassJet_eq,
    d4TopologicalBlackHoleIngoingExponentMassJet_eq]
  simp [d4BMXiReflectedRealPairDecay]
  ring

theorem d4BMXiReflectedHorizonMassJetDefect_eq_half_eta
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedHorizonMassJetDefect n q =
      thermalCircleAPSEta (q.1 : ℂ).re / 2 := by
  rw [d4BMXiReflectedHorizonMassJetDefect_eq]
  rfl

theorem d4BMXiReflectedHorizonMassJetDefect_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedHorizonMassJetDefect n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiReflectedHorizonMassJetDefect_eq]
  constructor <;> intro h
  · linarith
  · rw [h]
    norm_num

theorem d4BMXiReflectedHorizonMassJetDefect_reflection_pair_cancel
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedHorizonMassJetDefect n q +
      d4BMXiReflectedHorizonMassJetDefect n (xiZeroCopyReflectEquiv q) = 0 := by
  unfold d4BMXiReflectedHorizonMassJetDefect
  rw [xiZeroCopyReflectEquiv_apply_apply]
  ring

def D4BMXiReflectedHorizonMassJetsAreSectorLocal : Prop :=
  ∀ (n : ℕ) (q : XiZeroCopy),
    d4BMXiReflectedHorizonMassJetDefect n q = 0

theorem riemannHypothesis_iff_d4BMXiReflectedHorizonMassJetsAreSectorLocal :
    RiemannHypothesis ↔ D4BMXiReflectedHorizonMassJetsAreSectorLocal := by
  constructor
  · intro hRH n q
    rw [d4BMXiReflectedHorizonMassJetDefect_eq_zero_iff]
    have hreal := xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q
    simp [xiSpectralPoint] at hreal
    linarith
  · intro hlocal
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hhalf :=
      (d4BMXiReflectedHorizonMassJetDefect_eq_zero_iff 0 q).1 (hlocal 0 q)
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [xiSpectralPoint]
      linarith

end

end RHTower

