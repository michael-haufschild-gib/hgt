import GaloisForLFunctions.RHTower.XiShiftedHardEdgeComplexPaleyWienerDivisorLimit

/-!
# Dyadic even/odd coherence of hard-edge lattice samples at Xi spectral points

At hard-edge scale `r` the lattice sample of a Xi zero copy `q` is the Riemann sum
`h ∑_j exp(i φ h j) f_n(h j)` with mesh `h = 2/(1 + |r|)`, Cayley phase
`φ = (1 + |r|) arctan(γ_q / (1 + |r|))` of the spectral point `γ_q`, and `f_n` the compactly
supported cutoff of a Schwartz function `f`. Along the fine scales `2k + 1` the mesh is exactly half
the mesh at scale `k`, so the fine lattice splits into an even sublattice, which is the coarse
lattice, and an odd sublattice. As `k → ∞` the full fine sample converges to the positive Fourier
extension `F_n(γ_q)`, the even part converges to `F_n(γ_q)/2`, and hence the odd part also
converges to `F_n(γ_q)/2`: both sublattices carry exactly half of the limit.

## Main results

- `routeUDyadicFineEvenLatticeSample_eq_evenSample`: the even-sublattice part of the fine sample
  equals the even sample built on the coarse mesh.
- `routeUXiComplexHardEdgeSample_fine_eq_even_add_odd`: fine sample `=` even `+` odd sample.
- `tendsto_routeUXiComplexHardEdgeSample_fine`: the fine samples converge to `F_n(γ_q)`.
- `tendsto_routeUDyadicEvenSample_half`: the even samples converge to `F_n(γ_q)/2`.
- `tendsto_routeUDyadicOddSample_half`: the odd samples converge to `F_n(γ_q)/2`.

## Hypotheses

All results are unconditional and hold for every cutoff level `n`, Schwartz function `f` and Xi
zero copy `q`, with no assumption on the location of the zero. The periodization identity
`routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail` assumes the phase window
`|Re z| ≤ π (1 + |r|) / 2`.
-/

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory

noncomputable section

namespace RHTower

/-- Fine dyadic scale `2k + 1`, at which the hard-edge mass doubles relative to scale `k`. -/
def routeUDyadicFineIndex (k : ℕ) : ℕ := 2 * k + 1

theorem tendsto_routeUDyadicFineIndex_atTop :
    Tendsto routeUDyadicFineIndex atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with a ha
  simp only [routeUDyadicFineIndex]
  omega

/-- Cayley phase of `alpha` at the fine scale `2k + 1`. -/
def routeUDyadicFinePhase (k : ℕ) (alpha : ℂ) : ℂ :=
  routeUComplexHardEdgePhase (routeUDyadicFineIndex k : ℝ) alpha

/-- The fine-scale Cayley phase of `alpha` converges to `alpha`. -/
theorem tendsto_routeUDyadicFinePhase (alpha : ℂ) :
    Tendsto (fun k : ℕ => routeUDyadicFinePhase k alpha) atTop (nhds alpha) := by
  exact (tendsto_routeUComplexHardEdgePhase_natCast alpha).comp
    tendsto_routeUDyadicFineIndex_atTop

/-- The hard-edge mass at scale `2k + 1` is twice the mass at scale `k`. -/
theorem routeUHardEdgeMass_fineIndex (k : ℕ) :
    routeUHardEdgeMass (routeUDyadicFineIndex k : ℝ) =
      2 * routeUHardEdgeMass (k : ℝ) := by
  rw [routeUHardEdgeMass, routeUHardEdgeMass,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (routeUDyadicFineIndex k)),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
  simp only [routeUDyadicFineIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The mesh at scale `2k + 1` is half the mesh at scale `k`. -/
theorem routeUHardEdgeMesh_fineIndex (k : ℕ) :
    2 * routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) =
      routeUHardEdgeMesh (k : ℝ) := by
  rw [routeUHardEdgeMesh, routeUHardEdgeMesh,
    routeUHardEdgeMass_fineIndex]
  have hmass : routeUHardEdgeMass (k : ℝ) ≠ 0 :=
    ne_of_gt (routeUHardEdgeMass_pos (k : ℝ))
  field_simp [hmass]

/-- Lattice Riemann sum `h ∑_j exp(i z h j) f_n(h j)` at mesh `h = 2/(1 + |r|)` and an arbitrary
complex frequency `z`. -/
def routeUComplexHardEdgePeriodizationAt
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  ((routeUHardEdgeMesh r : ℝ) : ℂ) *
    ∑' j : ℤ,
      Complex.exp
          (Complex.I * z *
            (((routeUHardEdgeMesh r) * (j : ℝ) : ℝ) : ℂ)) *
        SchwartzMap.compactSupportApproximation n f
          (routeUHardEdgeMesh r * (j : ℝ))

/-- Periodization splitting: within the phase window `|Re z| ≤ π (1 + |r|) / 2`, the lattice sum is
the positive Fourier extension at `z` plus the noncentral alias tail. -/
theorem routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ)
    (hz : |z.re| ≤ routeUHardEdgeAliasPeriod r / 2) :
    routeUComplexHardEdgePeriodizationAt n f r z =
      routeUComplexPositiveFourierExtension n f z +
        routeUComplexHardEdgeAliasTail n f r z := by
  rw [routeUComplexHardEdgePeriodizationAt,
    routeU_complex_hardEdge_periodization]
  exact tsum_routeUComplexAlias_eq_extension_add_tail n f r z hz

/-- Even sample: half the coarse-mesh (scale `k`) lattice sum at the fine-scale phase of the
spectral point of `q`. -/
def routeUDyadicEvenSample
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) : ℂ :=
  (1 / 2 : ℂ) * routeUComplexHardEdgePeriodizationAt n f (k : ℝ)
    (routeUDyadicFinePhase k (xiSpectralPoint q))

/-- The part of the fine-scale lattice sample supported on even lattice indices `2j`. -/
def routeUDyadicFineEvenLatticeSample
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) : ℂ :=
  ((routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) : ℝ) : ℂ) *
    ∑' j : ℤ,
      Complex.exp
          (Complex.I * routeUDyadicFinePhase k (xiSpectralPoint q) *
            (((routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ)) *
              ((2 * j : ℤ) : ℝ) : ℝ) : ℂ)) *
        SchwartzMap.compactSupportApproximation n f
          (routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) *
            ((2 * j : ℤ) : ℝ))

/-- The even-sublattice part of the fine sample equals the even sample, because the fine
points `2j · h(2k + 1)` are the coarse points `j · h(k)`. -/
theorem routeUDyadicFineEvenLatticeSample_eq_evenSample
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) :
    routeUDyadicFineEvenLatticeSample n f k q =
      routeUDyadicEvenSample n f k q := by
  have hmesh := routeUHardEdgeMesh_fineIndex k
  have hmeshHalfReal : routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) =
      (1 / 2 : ℝ) * routeUHardEdgeMesh (k : ℝ) := by
    linarith
  have hmeshHalf :
      ((routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) : ℝ) : ℂ) =
        (1 / 2 : ℂ) * (routeUHardEdgeMesh (k : ℝ) : ℂ) := by
    have hcast := congrArg (fun x : ℝ => (x : ℂ)) hmeshHalfReal
    push_cast at hcast
    simpa using hcast
  have hsum :
      (∑' j : ℤ,
        Complex.exp
            (Complex.I * routeUDyadicFinePhase k (xiSpectralPoint q) *
              (((routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ)) *
                ((2 * j : ℤ) : ℝ) : ℝ) : ℂ)) *
          SchwartzMap.compactSupportApproximation n f
            (routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) *
              ((2 * j : ℤ) : ℝ))) =
        ∑' j : ℤ,
          Complex.exp
              (Complex.I * routeUDyadicFinePhase k (xiSpectralPoint q) *
                (((routeUHardEdgeMesh (k : ℝ)) * (j : ℝ) : ℝ) : ℂ)) *
            SchwartzMap.compactSupportApproximation n f
              (routeUHardEdgeMesh (k : ℝ) * (j : ℝ)) := by
    apply tsum_congr
    intro j
    have hpoint :
        routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) * ((2 * j : ℤ) : ℝ) =
          routeUHardEdgeMesh (k : ℝ) * (j : ℝ) := by
      calc
        routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ) * ((2 * j : ℤ) : ℝ) =
            (2 * routeUHardEdgeMesh (routeUDyadicFineIndex k : ℝ)) * (j : ℝ) := by
              push_cast
              ring
        _ = routeUHardEdgeMesh (k : ℝ) * (j : ℝ) := by rw [hmesh]
    rw [hpoint]
  rw [routeUDyadicFineEvenLatticeSample, routeUDyadicEvenSample,
    routeUComplexHardEdgePeriodizationAt, hsum, hmeshHalf]
  ring

/-- Odd sample: the fine-scale lattice sample minus the even sample. -/
def routeUDyadicOddSample
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) : ℂ :=
  routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q -
    routeUDyadicEvenSample n f k q

theorem routeUXiComplexHardEdgeSample_fine_eq_even_add_odd
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) :
    routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q =
      routeUDyadicEvenSample n f k q + routeUDyadicOddSample n f k q := by
  rw [routeUDyadicOddSample]
  ring

/-- As `k → ∞`, the even samples converge to half the positive Fourier extension at the spectral
point of `q`; the alias tail decays like the inverse square of the alias period. -/
theorem tendsto_routeUDyadicEvenSample_half
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (q : XiZeroCopy) :
    Tendsto (fun k : ℕ => routeUDyadicEvenSample n f k q) atTop
      (nhds ((1 / 2 : ℂ) *
        routeUComplexPositiveFourierExtension n f (xiSpectralPoint q))) := by
  let z : ℕ → ℂ := fun k => routeUDyadicFinePhase k (xiSpectralPoint q)
  let C : ℝ := routeUComplexHardEdgeUniformAliasTailConstant n f 0
  have hz : Tendsto z atTop (nhds (xiSpectralPoint q)) :=
    tendsto_routeUDyadicFinePhase (xiSpectralPoint q)
  have hcentral : Tendsto
      (fun k : ℕ => routeUComplexPositiveFourierExtension n f (z k)) atTop
      (nhds (routeUComplexPositiveFourierExtension n f (xiSpectralPoint q))) := by
    apply tendsto_routeUComplexPositiveFourierExtension_of_tendsto
      n f z (xiSpectralPoint q) hz
    intro k
    exact (abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one
      (routeUDyadicFineIndex k : ℝ) q).le
  have hmass : Tendsto (fun k : ℕ => 1 + (k : ℝ)) atTop atTop := by
    simpa only [add_comm] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hperiod : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod (k : ℝ)) atTop atTop := by
    have hmul := Tendsto.const_mul_atTop Real.pi_pos hmass
    simpa only [routeUHardEdgeAliasPeriod, routeUHardEdgeMass,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hmul
  have hperiodHalf : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod (k : ℝ) / 2) atTop atTop := by
    have hmul := Tendsto.const_mul_atTop (by positivity : 0 < (1 / 2 : ℝ)) hperiod
    simpa only [one_div, inv_mul_eq_div] using hmul
  have hzRe : Tendsto (fun k : ℕ => |(z k).re|) atTop
      (nhds |(xiSpectralPoint q).re|) := by
    exact (continuous_abs.tendsto _).comp
      ((Complex.reCLM.continuous.tendsto _).comp hz)
  have hzReBound : ∀ᶠ k : ℕ in atTop,
      |(z k).re| < |(xiSpectralPoint q).re| + 1 :=
    hzRe.eventually (Iio_mem_nhds (lt_add_one _))
  have hperiodBound : ∀ᶠ k : ℕ in atTop,
      |(xiSpectralPoint q).re| + 1 ≤
        routeUHardEdgeAliasPeriod (k : ℝ) / 2 :=
    (tendsto_atTop.1 hperiodHalf) (|(xiSpectralPoint q).re| + 1)
  have hphaseWindow : ∀ᶠ k : ℕ in atTop,
      |(z k).re| ≤ routeUHardEdgeAliasPeriod (k : ℝ) / 2 := by
    filter_upwards [hzReBound, hperiodBound] with k hk hK
    exact hk.le.trans hK
  have hperiodSq : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod (k : ℝ) ^ (2 : ℕ)) atTop atTop := by
    simpa only [pow_two] using hperiod.atTop_mul_atTop₀ hperiod
  have hbound : Tendsto
      (fun k : ℕ => C / routeUHardEdgeAliasPeriod (k : ℝ) ^ (2 : ℕ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hperiodSq
  have htail : Tendsto
      (fun k : ℕ => routeUComplexHardEdgeAliasTail n f (k : ℝ) (z k))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero'
      (Eventually.of_forall fun k => norm_nonneg _)
      ?_ hbound
    filter_upwards [hphaseWindow] with k hk
    simpa only [C,
      GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent,
      Nat.zero_add, Nat.mul_one] using
      (norm_routeUComplexHardEdgeAliasTail_uniform_le n f (k : ℝ) (z k)
        (by
          simpa only [z, routeUDyadicFinePhase] using
            (abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one
              (routeUDyadicFineIndex k : ℝ) q).le)
        hk 0)
  have hperiodization : Tendsto
      (fun k : ℕ => routeUComplexHardEdgePeriodizationAt n f (k : ℝ) (z k))
      atTop
      (nhds (routeUComplexPositiveFourierExtension n f (xiSpectralPoint q))) := by
    have hsum := hcentral.add htail
    simpa only [add_zero] using hsum.congr'
      (by
        filter_upwards [hphaseWindow] with k hk
        exact (routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail
          n f (k : ℝ) (z k) hk).symm)
  simpa only [routeUDyadicEvenSample, z] using
    (tendsto_const_nhds.mul hperiodization)

/-- Along the fine scales `2k + 1`, the hard-edge lattice samples converge to the positive Fourier
extension at the spectral point of `q`. -/
theorem tendsto_routeUXiComplexHardEdgeSample_fine
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (q : XiZeroCopy) :
    Tendsto (fun k : ℕ =>
      routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q)
      atTop
      (nhds (routeUComplexPositiveFourierExtension n f (xiSpectralPoint q))) := by
  let C : ℝ := routeUComplexHardEdgeUniformAliasTailConstant n f 0
  have hcentral :=
    (tendsto_routeUXiComplexHardEdgeCentral_natCast n f q).comp
      tendsto_routeUDyadicFineIndex_atTop
  have hmass : Tendsto (fun k : ℕ => 1 + (k : ℝ)) atTop atTop := by
    simpa only [add_comm] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hperiod : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod (k : ℝ)) atTop atTop := by
    have hmul := Tendsto.const_mul_atTop Real.pi_pos hmass
    simpa only [routeUHardEdgeAliasPeriod, routeUHardEdgeMass,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hmul
  have hperiodFine : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod
        (routeUDyadicFineIndex k : ℝ)) atTop atTop :=
    hperiod.comp tendsto_routeUDyadicFineIndex_atTop
  have hperiodFineSq : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod
        (routeUDyadicFineIndex k : ℝ) ^ (2 : ℕ)) atTop atTop := by
    simpa only [pow_two] using hperiodFine.atTop_mul_atTop₀ hperiodFine
  have hbound : Tendsto
      (fun k : ℕ => C / routeUHardEdgeAliasPeriod
        (routeUDyadicFineIndex k : ℝ) ^ (2 : ℕ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hperiodFineSq
  have htail : Tendsto
      (fun k : ℕ => routeUComplexHardEdgeAliasTail n f
        (routeUDyadicFineIndex k : ℝ)
        (routeUDyadicFinePhase k (xiSpectralPoint q)))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero'
      (Eventually.of_forall fun k => norm_nonneg _)
      (Eventually.of_forall fun k => ?_) hbound
    simpa only [C, routeUDyadicFinePhase,
      GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent,
      Nat.zero_add, Nat.mul_one] using
      (norm_routeUComplexHardEdgeAliasTail_xiSpectralPoint_le n f
        (routeUDyadicFineIndex k : ℝ) q 0)
  have hsum := hcentral.add htail
  simpa only [add_zero] using hsum.congr'
    (Eventually.of_forall fun k =>
      (routeUXiComplexHardEdgeSample_eq_central_add_aliasTail n f
        (routeUDyadicFineIndex k : ℝ) q).symm)

/-- Dyadic coherence: the odd samples also converge to half the positive Fourier extension at the
spectral point of `q`, so even and odd sublattices contribute equally in the limit. -/
theorem tendsto_routeUDyadicOddSample_half
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (q : XiZeroCopy) :
    Tendsto (fun k : ℕ => routeUDyadicOddSample n f k q) atTop
      (nhds ((1 / 2 : ℂ) *
        routeUComplexPositiveFourierExtension n f (xiSpectralPoint q))) := by
  have hfull := tendsto_routeUXiComplexHardEdgeSample_fine n f q
  have heven := tendsto_routeUDyadicEvenSample_half n f q
  have hsub := hfull.sub heven
  convert hsub using 1
  · funext k
    rfl
  · ring

end RHTower
