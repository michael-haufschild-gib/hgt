import GaloisForLFunctions.RHTower.XiWardCubicPrimeGammaSecantFundamentalSymmetryGap
import GaloisForLFunctions.RHTower.XiWardCubicPrimitivePrimeGammaSecantCoalescence

/-!
# Prime--Gamma secant quantum mismatch no-go (W-H207)

W-H206 proves that a fixed strict-Euler Cauchy secant detects every off-line zero through its
fundamental-symmetry gap.  Detection alone is not enough for the cubic Ward capacity argument:
the detector must pay a uniform zero quantum.

This module computes the detector exactly.  Phase-match a primitive lower-sector secant to an
ordinate and let `a` be horizontal depth from the critical line.  For primitive rate `lambda` and
positive secant aperture `c`, its reflection difference is

`-2 a (2 lambda + c) /
  ((lambda-a)(lambda+c-a)(lambda+a)(lambda+c+a))`.

Thus its Hermitian energy vanishes quadratically as `a -> 0+`.  The cubic Hellinger self-charge,
by contrast, is at least `115/108` throughout `0 < a <= 1/2` and grows like `a^-3`.  Lean proves
that no scalar, of either sign, can uniformly dominate the cubic charge by the fixed secant
reflection energy.

The positive survivor is sharp: a viable source contraction must introduce source poles adaptive
to the unknown horizontal scale, or collectively renormalize the completed pole--Gamma current
before codiagonalization.  Keeping a fixed absolute-Euler secant gap and bounding it afterward
cannot supply the one-quantum capacity law.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Primitive lower-sector secant with its real coordinate phase-matched to `gamma`. -/
def xiWardCubicPhaseMatchedPrimitiveLowerSecant
    (pe : Nat.Primes × ℕ) (gamma c : ℝ) (hc : 0 ≤ c) : ℂ → ℂ :=
  xiWardCubicPrimeGammaLowerSecantTest
    (xiWardCubicPrimitiveDeningerLowerShift pe (-gamma) 0 (le_refl 0))
    (xiWardCubicPrimitiveDeningerLowerShift pe (-gamma) c hc)

/-- Scalar reflection defect of the phase-matched lower secant. -/
def xiWardCubicPrimitiveLowerSecantReflectionDefect
    (lambda c a : ℝ) : ℝ :=
  -2 * a * (2 * lambda + c) /
    ((lambda - a) * (lambda + c - a) *
      (lambda + a) * (lambda + c + a))

/-- **W-H207 exact defect law.**  The phase-matched primitive lower secant has this exact
reflection difference at horizontal depth `a`. -/
theorem xiWardCubicPhaseMatchedPrimitiveLowerSecant_sub_star
    (pe : Nat.Primes × ℕ) (gamma : ℝ) {c : ℝ} (hc : 0 < c)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    xiWardCubicPhaseMatchedPrimitiveLowerSecant pe gamma c hc.le
          ((gamma : ℂ) - I * (a : ℂ)) -
        xiWardCubicPhaseMatchedPrimitiveLowerSecant pe gamma c hc.le
          (star ((gamma : ℂ) - I * (a : ℂ))) =
      (xiWardCubicPrimitiveLowerSecantReflectionDefect
        (xiGammaEulerPrimitiveLogFrequency pe) c a : ℂ) := by
  let z0 := xiWardCubicPrimitiveDeningerLowerShift pe (-gamma) 0 (le_refl 0)
  let z1 := xiWardCubicPrimitiveDeningerLowerShift pe (-gamma) c hc.le
  let alpha : ℂ := (gamma : ℂ) - I * (a : ℂ)
  have hlambda := half_lt_xiGammaEulerPrimitiveLogFrequency pe
  have hz : z0 ≠ z1 := by
    intro h
    have him := congrArg (fun z : DeningerPrimeGammaLowerPoint => (z : ℂ).im) h
    dsimp [z0, z1, xiWardCubicPrimitiveDeningerLowerShift,
      routePPrimitiveBurnolCenteredMode] at him
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at him
    norm_num at him
    linarith
  have ha_z0 : alpha ≠ (z0 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    dsimp [alpha, z0, xiWardCubicPrimitiveDeningerLowerShift,
      routePPrimitiveBurnolCenteredMode] at him
    norm_num [Complex.mul_im] at him
    linarith
  have ha_z1 : alpha ≠ (z1 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    dsimp [alpha, z1, xiWardCubicPrimitiveDeningerLowerShift,
      routePPrimitiveBurnolCenteredMode] at him
    norm_num [Complex.mul_im] at him
    linarith
  have hca_z0 : star alpha ≠ (z0 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    dsimp [alpha, z0, xiWardCubicPrimitiveDeningerLowerShift,
      routePPrimitiveBurnolCenteredMode] at him
    norm_num [Complex.mul_im] at him
    linarith
  have hca_z1 : star alpha ≠ (z1 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    dsimp [alpha, z1, xiWardCubicPrimitiveDeningerLowerShift,
      routePPrimitiveBurnolCenteredMode] at him
    norm_num [Complex.mul_im] at him
    linarith
  have halpha0 : alpha - (z0 : ℂ) =
      I * ((xiGammaEulerPrimitiveLogFrequency pe - a : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [alpha, z0, xiWardCubicPrimitiveDeningerLowerShift,
        routePPrimitiveBurnolCenteredMode, Complex.mul_re, Complex.mul_im] <;>
      ring
  have halpha1 : alpha - (z1 : ℂ) =
      I * ((xiGammaEulerPrimitiveLogFrequency pe + c - a : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [alpha, z1, xiWardCubicPrimitiveDeningerLowerShift,
        routePPrimitiveBurnolCenteredMode, Complex.mul_re, Complex.mul_im] <;>
      ring
  have hstar0 : star alpha - (z0 : ℂ) =
      I * ((xiGammaEulerPrimitiveLogFrequency pe + a : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [alpha, z0, xiWardCubicPrimitiveDeningerLowerShift,
        routePPrimitiveBurnolCenteredMode, Complex.mul_re, Complex.mul_im] <;>
      ring
  have hstar1 : star alpha - (z1 : ℂ) =
      I * ((xiGammaEulerPrimitiveLogFrequency pe + c + a : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [alpha, z1, xiWardCubicPrimitiveDeningerLowerShift,
        routePPrimitiveBurnolCenteredMode, Complex.mul_re, Complex.mul_im] <;>
      ring
  have hmulInv (x y : ℝ) :
      (I * (x : ℂ))⁻¹ * (I * (y : ℂ))⁻¹ =
        -((((x * y)⁻¹ : ℝ) : ℂ)) := by
    rw [mul_inv, mul_inv, Complex.inv_I]
    push_cast
    ring_nf
    rw [show (I : ℂ) ^ (2 : ℕ) = -1 by norm_num]
    ring
  have hma : 0 < xiGammaEulerPrimitiveLogFrequency pe - a := by linarith
  have hcma : 0 < xiGammaEulerPrimitiveLogFrequency pe + c - a := by linarith
  have hpa : 0 < xiGammaEulerPrimitiveLogFrequency pe + a := by linarith
  have hcpa : 0 < xiGammaEulerPrimitiveLogFrequency pe + c + a := by linarith
  change xiWardCubicPrimeGammaLowerSecantTest z0 z1 alpha -
      xiWardCubicPrimeGammaLowerSecantTest z0 z1 (star alpha) = _
  rw [xiWardCubicPrimeGammaLowerSecantTest_factorization hz ha_z0 ha_z1,
    xiWardCubicPrimeGammaLowerSecantTest_factorization hz hca_z0 hca_z1,
    halpha1, halpha0, hstar1, hstar0, hmulInv, hmulInv]
  have hreal :
      -(((xiGammaEulerPrimitiveLogFrequency pe + c - a) *
          (xiGammaEulerPrimitiveLogFrequency pe - a))⁻¹) -
        -(((xiGammaEulerPrimitiveLogFrequency pe + c + a) *
          (xiGammaEulerPrimitiveLogFrequency pe + a))⁻¹) =
      xiWardCubicPrimitiveLowerSecantReflectionDefect
        (xiGammaEulerPrimitiveLogFrequency pe) c a := by
    unfold xiWardCubicPrimitiveLowerSecantReflectionDefect
    field_simp [hma.ne', hcma.ne', hpa.ne', hcpa.ne']
    ring
  exact_mod_cast hreal

/-- Hermitian energy of the phase-matched reflection difference is the square of the scalar
defect. -/
theorem normSq_xiWardCubicPhaseMatchedPrimitiveLowerSecant_sub_star
    (pe : Nat.Primes × ℕ) (gamma : ℝ) {c : ℝ} (hc : 0 < c)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Complex.normSq
      (xiWardCubicPhaseMatchedPrimitiveLowerSecant pe gamma c hc.le
          ((gamma : ℂ) - I * (a : ℂ)) -
        xiWardCubicPhaseMatchedPrimitiveLowerSecant pe gamma c hc.le
          (star ((gamma : ℂ) - I * (a : ℂ)))) =
      xiWardCubicPrimitiveLowerSecantReflectionDefect
        (xiGammaEulerPrimitiveLogFrequency pe) c a ^ (2 : ℕ) := by
  rw [xiWardCubicPhaseMatchedPrimitiveLowerSecant_sub_star pe gamma hc ha0 ha]
  rw [Complex.normSq_ofReal]
  simp only [pow_two]

/-- Actual strict-right copy specialization of the phase-matched defect energy. -/
theorem normSq_pairDif_xiWardCubicPhaseMatchedPrimitiveLowerSecant
    (pe : Nat.Primes × ℕ) {c : ℝ} (hc : 0 < c)
    (q : XiRightZeroCopy) :
    Complex.normSq
      (xiWeilPairDif
        (xiWardCubicPhaseMatchedPrimitiveLowerSecant pe
          (xiRightCenteredZero q).im c hc.le) q.1) =
      xiWardCubicPrimitiveLowerSecantReflectionDefect
          (xiGammaEulerPrimitiveLogFrequency pe) c
          (xiRightCenteredZero q).re ^ (2 : ℕ) := by
  have ha0 := (xiRightCenteredZero_re_pos q).le
  have ha : (xiRightCenteredZero q).re < 1 / 2 :=
    (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  have hspectral : xiSpectralPoint q.1 =
      (((xiRightCenteredZero q).im : ℝ) : ℂ) -
        I * ((((xiRightCenteredZero q).re : ℝ) : ℂ)) := by
    rw [xiRightCenteredZero]
    simp only [xiSpectralPoint]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [xiWeilPairDif, xiSpectralPoint_lineConj, hspectral]
  exact normSq_xiWardCubicPhaseMatchedPrimitiveLowerSecant_sub_star
    pe (xiRightCenteredZero q).im hc ha0 ha

/-- A fixed primitive secant reflection defect tends to zero at the critical line. -/
theorem tendsto_xiWardCubicPrimitiveLowerSecantReflectionDefect
    {lambda c : ℝ} (hlambda : 0 < lambda) (hc : 0 < c) :
    Tendsto (xiWardCubicPrimitiveLowerSecantReflectionDefect lambda c)
      (nhds 0) (nhds 0) := by
  have hcont : ContinuousAt
      (xiWardCubicPrimitiveLowerSecantReflectionDefect lambda c) 0 := by
    unfold xiWardCubicPrimitiveLowerSecantReflectionDefect
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
      exact ⟨⟨⟨hlambda.ne', (add_pos hlambda hc).ne'⟩,
        hlambda.ne'⟩, (add_pos hlambda hc).ne'⟩
  simpa [xiWardCubicPrimitiveLowerSecantReflectionDefect] using hcont.tendsto

/-- **W-H207 quantum mismatch no-go.**  No scalar multiple of a fixed absolute-Euler secant
reflection energy uniformly dominates the cubic Hellinger self-charge on the strict-right
horizontal strip. -/
theorem not_exists_uniform_cubicHellinger_domination_by_primitiveLowerSecantDefect
    {lambda c : ℝ} (hlambda : 1 / 2 < lambda) (hc : 0 < c) :
    ¬ ∃ C : ℝ, ∀ a : ℝ, 0 < a → a < 1 / 2 →
      cubicLogMomentHellingerHorizontalKernel a a ≤
        C * xiWardCubicPrimitiveLowerSecantReflectionDefect lambda c a ^ (2 : ℕ) := by
  rintro ⟨C, hC⟩
  have hdef := tendsto_xiWardCubicPrimitiveLowerSecantReflectionDefect
    (lt_trans (by norm_num) hlambda) hc
  have ht : Tendsto (fun a : ℝ =>
      C * xiWardCubicPrimitiveLowerSecantReflectionDefect lambda c a ^ (2 : ℕ))
      (nhds 0) (nhds 0) := by
    convert tendsto_const_nhds.mul (hdef.pow 2) using 1 <;> norm_num
  have htWithin : Tendsto
      (fun a : ℝ =>
        C * xiWardCubicPrimitiveLowerSecantReflectionDefect lambda c a ^ (2 : ℕ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    ht.mono_left inf_le_left
  have hsmall : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      C * xiWardCubicPrimitiveLowerSecantReflectionDefect lambda c a ^ (2 : ℕ) <
        115 / 108 :=
    (tendsto_order.1 htWithin).2 _ (by norm_num)
  have hpos : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < a :=
    self_mem_nhdsWithin
  have hhalfNhds : ∀ᶠ a : ℝ in nhds 0, a < 1 / 2 :=
    Iio_mem_nhds (by norm_num)
  have hhalf : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), a < 1 / 2 :=
    hhalfNhds.filter_mono inf_le_left
  obtain ⟨a, ha, haHalf, haSmall⟩ :=
    (hpos.and (hhalf.and hsmall)).exists
  have hquantum := cubicLogMomentHellingerHorizontalKernel_self_ge
    ha haHalf.le
  have hbound := hC a ha haHalf
  linarith

end

end RHTower
