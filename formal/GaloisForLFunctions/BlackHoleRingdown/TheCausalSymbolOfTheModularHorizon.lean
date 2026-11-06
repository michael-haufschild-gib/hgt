import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTopologicalBlackHoleQNMIncidence
import GaloisForLFunctions.RHTower.SpectralBlaschkeMatching
import GaloisForLFunctions.BlackHoleRingdown.TheEchoTrainOfTheCusp

/-!
# The causal symbol of the modular horizon

On the massless topological black hole with modular horizon, a radial overtone of decay `D` multiplies
the horizon response by `e^{-Dt}`, so its retarded transform in the cusp channel evaluates the
scattering coefficient `φ` at `s = D + 1/2 - iω`. This module studies that composite symbol in the
frequency plane.

At a Xi divisor `z` the two continued QNM branches `ω_± = ±ξ - iD`, `ξ = z/2 + i/4`, behave oppositely.
The branch `ω_-` lands on `z` and is a pole. The branch `ω_+` lands on the functional-equation shadow
and is a regular zero. So the symbol selects `ω_-`, and its damping rate at `ρ = β + iγ` is
`D + (1-β)/2`, with oscillation `γ/2`.

Damping is universal, equal to `D + 1/4` at every zero, exactly when RH holds; this is a restatement of
RH, not a route to it. Each pole has a nonzero leading coefficient, the excitation factor of the mode.
The symbol is a genuine causal object: up to `s/(s-1)` it is the retarded transform of the damped echo
train `e^{-Dt} K(t)`.
-/

open Complex Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower

/-- The resonance coordinate `z` of the point `s = D + 1/2 - iω`. -/
def causalCoordinate (D : ℝ) (ω : ℂ) : ℂ := -2 * ω - 2 * I * D - I / 2

theorem resonanceParameter_causalCoordinate (D : ℝ) (ω : ℂ) :
    thetaCuspHawkingOpticalCuspResonanceParameter (causalCoordinate D ω) = D + 1 / 2 - I * ω := by
  unfold thetaCuspHawkingOpticalCuspResonanceParameter causalCoordinate
  linear_combination (-(D : ℂ) - 1 / 4) * I_sq

/-- The minus branch lands on the divisor coordinate. -/
theorem causalCoordinate_qnmMinus (n : ℕ) (z : ℂ) :
    causalCoordinate (thetaCuspHawkingTopologicalBlackHoleConformalDecay n)
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z) = z := by
  unfold causalCoordinate thetaCuspHawkingTopologicalBlackHoleQNMMinus
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
  ring

/-- The plus branch lands on the functional-equation shadow. -/
theorem causalCoordinate_qnmPlus (n : ℕ) (z : ℂ) :
    causalCoordinate (thetaCuspHawkingTopologicalBlackHoleConformalDecay n)
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) =
      thetaCuspHawkingOpticalCuspShadow z := by
  unfold causalCoordinate thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum thetaCuspHawkingOpticalCuspShadow
  ring

/-- The scattering coefficient as a function of frequency, at radial decay `D`. -/
def causalSymbol (D : ℝ) (ω : ℂ) : ℂ :=
  thetaCuspHawkingOpticalCuspScattering (causalCoordinate D ω)

theorem differentiable_causalCoordinate (D : ℝ) : Differentiable ℂ (causalCoordinate D) := by
  unfold causalCoordinate
  fun_prop

/-- **The excited branch.**  Every Xi divisor makes the minus branch a pole of the causal symbol. -/
theorem causalSymbol_qnmMinus_isPole (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt (causalSymbol (thetaCuspHawkingTopologicalBlackHoleConformalDecay n))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) < 0 := by
  set D := thetaCuspHawkingTopologicalBlackHoleConformalDecay n with hD
  set w := thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q) with hw
  have hcoord : causalCoordinate D w = xiSpectralPoint q := causalCoordinate_qnmMinus n _
  have hcd := differentiable_causalCoordinate D
  have hnumD : Differentiable ℂ
      (fun ω => thetaCuspHawkingOpticalCuspNumerator (causalCoordinate D ω)) := by
    unfold thetaCuspHawkingOpticalCuspNumerator
    exact XiC_differentiable.comp (hcd.add_const _)
  have hdenD : Differentiable ℂ
      (fun ω => thetaCuspHawkingOpticalCuspDenominator (causalCoordinate D ω)) := by
    unfold thetaCuspHawkingOpticalCuspDenominator
    exact XiC_differentiable.comp hcd
  have hfun : causalSymbol D =
      (fun ω => thetaCuspHawkingOpticalCuspNumerator (causalCoordinate D ω)) /
        (fun ω => thetaCuspHawkingOpticalCuspDenominator (causalCoordinate D ω)) := by
    funext ω
    rfl
  rw [hfun]
  refine meromorphicOrderAt_div_neg_of_analyticAt_num_ne_den_zero (hnumD.analyticAt w)
    (hdenD.analyticAt w) ?_ ?_ ?_
  · show thetaCuspHawkingOpticalCuspNumerator (causalCoordinate D w) ≠ 0
    rw [hcoord]
    exact thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero q
  · show thetaCuspHawkingOpticalCuspDenominator (causalCoordinate D w) = 0
    rw [hcoord]
    exact thetaCuspHawkingOpticalCuspDenominator_xiSpectralPoint_eq_zero q
  · intro htop
    have hevent : (fun ω => thetaCuspHawkingOpticalCuspDenominator (causalCoordinate D ω))
        =ᶠ[𝓝 w] 0 := analyticOrderAt_eq_top.mp htop
    have hglobal : AnalyticOnNhd ℂ
        (fun ω => thetaCuspHawkingOpticalCuspDenominator (causalCoordinate D ω)) Set.univ :=
      fun z _ => hdenD.analyticAt z
    have hzero := hglobal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ w) hevent
    have hshift : causalCoordinate D (w - I / 2) = xiSpectralPoint q + I := by
      rw [← hcoord]
      unfold causalCoordinate
      ring
    have h0 := hzero (Set.mem_univ (w - I / 2))
    simp only [Pi.zero_apply] at h0
    rw [hshift] at h0
    exact thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero q h0

/-- **The silent branch.**  At every Xi divisor the plus branch is a regular zero of the causal
symbol. -/
theorem causalSymbol_qnmPlus_isZero (n : ℕ) (q : XiZeroCopy) :
    AnalyticAt ℂ (causalSymbol (thetaCuspHawkingTopologicalBlackHoleConformalDecay n))
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) ∧
      causalSymbol (thetaCuspHawkingTopologicalBlackHoleConformalDecay n)
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) = 0 := by
  obtain ⟨han, hzero⟩ := thetaCuspHawkingOpticalCuspShadow_xiSpectralPoint_isZero q
  have hcoord := causalCoordinate_qnmPlus n (xiSpectralPoint q)
  constructor
  · rw [← hcoord] at han
    exact han.comp ((differentiable_causalCoordinate _).analyticAt _)
  · rw [causalSymbol, hcoord]
    exact hzero

/-! ### The ringdown rate -/

/-- The damping rate of the minus branch at radial decay `D` and divisor coordinate `z`. -/
def ringdownRate (D : ℝ) (z : ℂ) : ℝ := D + 1 / 4 + z.im / 2

theorem qnmMinus_im_eq_neg_ringdownRate (n : ℕ) (z : ℂ) :
    (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z).im =
      -ringdownRate (thetaCuspHawkingTopologicalBlackHoleConformalDecay n) z := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMMinus_im, ringdownRate]
  ring

/-- **The rate at a zero.**  A zero `ρ = β + iγ` rings with damping `D + (1-β)/2`. -/
theorem ringdownRate_xiSpectralPoint (D : ℝ) (q : XiZeroCopy) :
    ringdownRate D (xiSpectralPoint q) = D + (1 - (q.1 : ℂ).re) / 2 := by
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint] <;> ring
  rw [ringdownRate, him]
  ring

/-- **The frequency at a zero.**  A zero `ρ = β + iγ` rings at frequency `-γ/2`; its conjugate zero
gives `+γ/2` at the same damping. -/
theorem qnmMinus_re_xiSpectralPoint (n : ℕ) (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)).re =
      -(q.1 : ℂ).im / 2 := by
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    simp [xiSpectralPoint]
  simp [thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum, Complex.div_ofNat_re, hre] <;> ring

/-- **Universal damping is RH.**  This restates RH; it is not an input towards it. -/
theorem riemannHypothesis_iff_universal_damping (D : ℝ) :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy, ringdownRate D (xiSpectralPoint q) = D + 1 / 4 := by
  rw [riemannHypothesis_iff_forall_xiSpectralPointSupport_im_eq_zero]
  constructor
  · intro h q
    have him : (xiSpectralPoint q).im = 0 := by
      rw [xiSpectralPoint_eq_support]
      exact h q.1
    rw [ringdownRate, him]
    ring
  · intro h ρ
    have hpos := xi_divisor_pos_on_support ρ
    have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by omega
    have hq := h ⟨ρ, ⟨0, hn⟩⟩
    rw [ringdownRate, xiSpectralPoint_eq_support] at hq
    change D + 1 / 4 + (xiSpectralPointSupport ρ).im / 2 = D + 1 / 4 at hq
    linarith

/-! ### The excitation factor -/

/-- **The excitation factor.**  At every Xi divisor the scattering coefficient has a pole of some
finite order `m ≥ 1` with a nonzero leading coefficient. -/
theorem exists_excitationFactor (q : XiZeroCopy) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ A : ℂ, A ≠ 0 ∧
      Tendsto (fun z => (z - xiSpectralPoint q) ^ m * thetaCuspHawkingOpticalCuspScattering z)
        (𝓝[≠] (xiSpectralPoint q)) (𝓝 A) := by
  set z₀ := xiSpectralPoint q with hz₀
  have hnum : XiC (z₀ + I) ≠ 0 := thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero q
  have hzero : XiC z₀ = 0 := XiC_xiSpectralPoint_eq_zero q
  have han : AnalyticAt ℂ XiC z₀ := XiC_differentiable.analyticAt z₀
  have htop : analyticOrderAt XiC z₀ ≠ ⊤ := by
    intro h
    have hevent : XiC =ᶠ[𝓝 z₀] 0 := analyticOrderAt_eq_top.mp h
    have hglobal : AnalyticOnNhd ℂ XiC Set.univ := fun z _ => XiC_differentiable.analyticAt z
    have hall := hglobal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z₀) hevent
    exact hnum (hall (Set.mem_univ (z₀ + I)))
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨g, hgan, hg0, hfac⟩ := (han.analyticOrderAt_eq_natCast (n := m)).mp hm.symm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have hval := hfac.self_of_nhds
      rw [pow_zero, one_smul] at hval
      exact absurd (hval.symm.trans hzero) hg0
    · exact hpos
  refine ⟨m, hm1, XiC (z₀ + I) / g z₀, div_ne_zero hnum hg0, ?_⟩
  have hnumT : Tendsto (fun z => XiC (z + I)) (𝓝[≠] z₀) (𝓝 (XiC (z₀ + I))) := by
    have hc : Continuous (fun z => XiC (z + I)) :=
      XiC_differentiable.continuous.comp (continuous_id.add continuous_const)
    exact (hc.tendsto z₀).mono_left nhdsWithin_le_nhds
  have hgT : Tendsto g (𝓝[≠] z₀) (𝓝 (g z₀)) := hgan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine (hnumT.div hgT hg0).congr' ?_
  filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hne
  have hne' : z ≠ z₀ := hne
  have hp : (z - z₀) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hne')
  show XiC (z + I) / g z = _
  rw [thetaCuspHawkingOpticalCuspScattering, thetaCuspHawkingOpticalCuspNumerator,
    thetaCuspHawkingOpticalCuspDenominator, hz, smul_eq_mul, ← mul_div_assoc,
    mul_div_mul_left _ _ hp]

/-! ### The causal transform -/

/-- **The causal symbol is a retarded transform.**  For `Im ω > 1/2 - D`, the retarded transform of the
damped echo train `e^{-Dt} K(t)` is `Λ(2s-1)/Λ(2s)` at `s = D + 1/2 - iω`, which is the causal symbol
up to the kinematic factor `s/(s-1)`. -/
theorem retardedTransform_dampedEchoKernel {D : ℝ} {ω : ℂ} (hω : 1 / 2 < D + ω.im) :
    (∫ t : ℝ, Complex.exp (I * ω * (t : ℂ)) * ((Real.exp (-D * t) * echoKernel t : ℝ) : ℂ))
      = ((D + 1 / 2 - I * ω) / (D + 1 / 2 - I * ω - 1)) * causalSymbol D ω := by
  set s : ℂ := D + 1 / 2 - I * ω with hs
  have hsre : s.re = D + 1 / 2 + ω.im := by
    simp [hs] <;> ring
  have hs1 : 1 < s.re := by linarith
  set w : ℂ := D - I * ω with hw
  have hwre : 1 / 2 < w.re := by
    have : w.re = D + ω.im := by
      simp [hw]
    linarith
  have hint : (∫ t : ℝ, Complex.exp (I * ω * (t : ℂ)) * ((Real.exp (-D * t) * echoKernel t : ℝ) : ℂ))
      = ∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * ((echoKernel t : ℝ) : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    push_cast
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hw]
    ring
  have hws : w = s - 1 / 2 := by
    rw [hw, hs]
    ring
  have htwo1 : 2 * w = 2 * s - 1 := by
    rw [hws]
    ring
  have htwo2 : 2 * w + 1 = 2 * s := by
    rw [hws]
    ring
  rw [hint, integral_cexp_mul_echoKernel_eq_completed hwre, htwo2, htwo1]
  have hz : thetaCuspHawkingOpticalCuspResonanceParameter (causalCoordinate D ω) = s :=
    resonanceParameter_causalCoordinate D ω
  have hnum : thetaCuspHawkingOpticalCuspNumerator (causalCoordinate D ω) = xi (2 * s - 1) := by
    rw [thetaCuspHawkingOpticalCuspNumerator_eq_xi, hz]
  have hden : thetaCuspHawkingOpticalCuspDenominator (causalCoordinate D ω) = xi (2 * s) := by
    rw [thetaCuspHawkingOpticalCuspDenominator_eq_xi, hz]
  have hre2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hre21 : 1 < (2 * s - 1).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re,
      zero_mul, sub_zero]
    linarith
  have hne (u : ℂ) (hu : 1 < u.re) : u ≠ 0 ∧ u ≠ 1 :=
    ⟨fun h => by rw [h] at hu; norm_num at hu, fun h => by rw [h] at hu; norm_num at hu⟩
  have hx1 := xi_eq_half_mul (hne _ hre21).1 (hne _ hre21).2
  have hx2 := xi_eq_half_mul (hne _ hre2).1 (hne _ hre2).2
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs1; norm_num at hs1
  have hsm1 : s - 1 ≠ 0 := fun h => by
    have hone : s = 1 := sub_eq_zero.mp h
    rw [hone] at hs1
    norm_num at hs1
  have h2m1 : 2 * s - 1 ≠ 0 := (hne _ hre21).1
  have hΛ : completedRiemannZeta (2 * s) ≠ 0 := by
    intro h
    have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre2.le
    exact hz2 (by rw [riemannZeta_def_of_ne_zero (hne _ hre2).1, h, zero_div])
  rw [causalSymbol, thetaCuspHawkingOpticalCuspScattering, hnum, hden, hx1, hx2]
  field_simp <;> ring

end GaloisForLFunctions.BlackHoleRingdown

end
