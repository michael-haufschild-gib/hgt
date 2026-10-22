import GaloisForLFunctions.RHTower.EulerHedenmalmGammaStokesTransgression
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFourierLaplace

/-!
# The ordinary Euler and Möbius dilation inverse of the anti-causal Gamma mode

The literal first theta atom `h` and the completed theta source `k` are related by the ordinary
normalized integer dilations `T_n f (x) = n^(-1/2) f(x + log n)`:

```text
thetaCuspSourceTerm x n = T_n h x,      k = ∑_{n ≥ 1} T_n h.
```

Both statements transport to the anti-causal Green responses

```text
R⁺_α f (x) = -exp(-i α x) ∫_x^∞ exp(i α y) f y dy :
  E R⁺_α h = R⁺_α k,        M R⁺_α k = R⁺_α h,
```

where `E = ∑_n T_n` and `M = ∑_n μ(n) T_n`.  Both series converge absolutely: the atom bound
`exp x |h_n(x)| ≤ C exp(-(π/2) n²)` on the positive half-line makes the phase-weighted integrals
summable in `n`, and the finite Möbius divisor inversion collapses the resulting double series.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Normalized integer dilations -/

/-- The normalized integer dilation `T_n f (x) = n^(-1/2) f (x + log n)`. -/
def normalizedLogDilation (n : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (x + Real.log n)

/-- The literal first theta atom in logarithmic coordinates, complexified. -/
def thetaAtomSeed (x : ℝ) : ℂ := (thetaCuspLogSeed x : ℂ)

/-- The completed theta source in logarithmic coordinates, complexified. -/
def thetaSourceComplex (x : ℝ) : ℂ := (thetaCuspFullSource x : ℂ)

/-- **The literal atom scaling law.**  Every theta-cusp source term is the normalized integer
dilation of the single first atom. -/
theorem normalizedLogDilation_thetaAtomSeed {n : ℕ} (hn : 0 < n) (x : ℝ) :
    normalizedLogDilation n thetaAtomSeed x = (thetaCuspSourceTerm x n : ℂ) := by
  have h := invSqrt_mul_logTranslate_thetaCuspLogSeed hn x
  rw [normalizedLogDilation, thetaAtomSeed, thetaCuspSourceTerm]
  rw [show ((thetaCuspLogSeed (x + Real.log n) : ℝ) : ℂ) =
      ((logTranslate (Real.log n) thetaCuspLogSeed x : ℝ) : ℂ) from rfl]
  rw [← Complex.ofReal_mul, h]

/-- Ordinary Euler dilation synthesis over the positive integers. -/
def eulerDilationSynthesis (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, normalizedLogDilation (n + 1) f x

/-- Ordinary Möbius dilation synthesis over the positive integers. -/
def mobiusDilationSynthesis (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℂ) *
    normalizedLogDilation (n + 1) f x

/-- **The Euler synthesis of the first atom is the completed source.** -/
theorem eulerDilationSynthesis_thetaAtomSeed (x : ℝ) :
    eulerDilationSynthesis thetaAtomSeed x = thetaSourceComplex x := by
  have hzero : thetaCuspSourceTerm x 0 = 0 := by
    simp [thetaCuspSourceTerm, thetaCuspSeed]
  have hbase : HasSum (fun n : ℕ => thetaCuspSourceTerm x n) (thetaCuspFullSource x) :=
    (summable_thetaCuspSourceTerm x).hasSum
  have hshift : HasSum (fun n : ℕ => thetaCuspSourceTerm x (n + 1))
      (thetaCuspFullSource x) := by
    refine (hasSum_nat_add_iff (f := fun n : ℕ => thetaCuspSourceTerm x n) 1).mpr ?_
    simpa [Finset.sum_range_one, hzero] using hbase
  have hcast := Complex.ofRealCLM.hasSum hshift
  rw [eulerDilationSynthesis, thetaSourceComplex,
    tsum_congr (fun n => normalizedLogDilation_thetaAtomSeed (Nat.succ_pos n) x)]
  exact hcast.tsum_eq

/-! ## The anti-causal Green response -/

/-- The homogeneous Stokes phase `exp(i α y)`. -/
def stokesPhase (α : ℂ) (y : ℝ) : ℂ := Complex.exp (Complex.I * α * (y : ℂ))

theorem norm_stokesPhase (α : ℂ) (y : ℝ) : ‖stokesPhase α y‖ = Real.exp (-α.im * y) := by
  rw [stokesPhase, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem continuous_stokesPhase (α : ℂ) : Continuous (stokesPhase α) := by
  unfold stokesPhase
  fun_prop

theorem stokesPhase_add (α : ℂ) (y z : ℝ) :
    stokesPhase α (y + z) = stokesPhase α y * stokesPhase α z := by
  rw [stokesPhase, stokesPhase, stokesPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The anti-causal first-order Green response. -/
def antiCausalGreen (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -Complex.exp (-(Complex.I * α * (x : ℂ))) * ∫ y in Ioi x, stokesPhase α y * f y

/-! ## Translation of half-line integrals -/

theorem setIntegral_Ioi_comp_add_right (f : ℝ → ℂ) (x a : ℝ) :
    (∫ y in Ioi x, f (y + a)) = ∫ y in Ioi (x + a), f y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun y => (Ioi (x + a)).indicator f y) a]
  congr 1
  funext y
  by_cases h : y ∈ Ioi x
  · have h' : y + a ∈ Ioi (x + a) := by
      simp only [mem_Ioi] at h ⊢
      linarith
    rw [indicator_of_mem h, indicator_of_mem h']
  · have h' : y + a ∉ Ioi (x + a) := by
      simp only [mem_Ioi] at h ⊢
      intro hc
      exact h (by linarith)
    rw [indicator_of_notMem h, indicator_of_notMem h']

/-! ## Integrability of the phase-weighted atoms -/

private theorem integrableOn_Ioi_of_Ioi_zero {F : ℝ → ℂ} (hc : Continuous F)
    (h0 : IntegrableOn F (Ioi 0)) (x : ℝ) : IntegrableOn F (Ioi x) := by
  rcases le_or_gt 0 x with hx | hx
  · exact h0.mono_set (Ioi_subset_Ioi hx)
  · rw [← Ioc_union_Ioi_eq_Ioi hx.le]
    exact (hc.integrableOn_Ioc).union h0

theorem integrableOn_stokesPhase_mul_sourceTerm {α : ℂ} (hα : -1 < α.im) {n : ℕ} (hn : 0 < n)
    (x : ℝ) :
    IntegrableOn (fun y : ℝ => stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)) (Ioi x) := by
  have hcont : Continuous (fun y : ℝ => stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)) := by
    have hsource : Continuous (fun y : ℝ => thetaCuspSourceTerm y n) := by
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop
    exact (continuous_stokesPhase α).mul (Complex.continuous_ofReal.comp hsource)
  refine integrableOn_Ioi_of_Ioi_zero hcont ?_ x
  have hmajor := integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one hn
    (z := -α.im) (by linarith)
  refine Integrable.mono hmajor hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hnn : 0 ≤ thetaCuspSourceTerm y n := thetaCuspSourceTerm_nonneg_of_pos hy n
  rw [norm_mul, norm_stokesPhase, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnn, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hnn)]

theorem integrableOn_stokesPhase_mul_source {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    IntegrableOn (fun y : ℝ => stokesPhase α y * thetaSourceComplex y) (Ioi x) := by
  have hfull := integrable_thetaCuspFourierLaplaceIntegrand (w := -α)
    (by simpa using hα)
  have hcong : Integrable (fun y : ℝ => stokesPhase α y * thetaSourceComplex y) := by
    refine hfull.congr ?_
    filter_upwards with y
    rw [thetaCuspFourierLaplaceIntegrand, stokesPhase, thetaSourceComplex]
    congr 2
    ring
  exact hcong.integrableOn

end

end RHTower

namespace RHTower

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

/-! ## Summability of the phase-weighted atom masses -/

private theorem norm_phaseAtom (α : ℂ) (n : ℕ) (y : ℝ) :
    ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖ =
      Real.exp (-α.im * y) * |thetaCuspSourceTerm y n| := by
  rw [norm_mul, norm_stokesPhase, Complex.norm_real, Real.norm_eq_abs]

private theorem integral_norm_phaseAtom_Ioi_zero_le {α : ℂ} (hα : -1 < α.im) {n : ℕ}
    (hn : 0 < n) :
    (∫ y in Ioi (0 : ℝ), ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖) ≤
      thetaCuspGaussianConstant thetaCuspSeedPolynomial *
        Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2) * (1 / (1 + α.im)) := by
  set K : ℝ := thetaCuspGaussianConstant thetaCuspSeedPolynomial with hK
  have hK0 : 0 ≤ K := thetaCuspGaussianConstant_nonneg _
  have hexp : (-α.im - 1) < 0 := by linarith
  have hbase : IntegrableOn (fun y : ℝ => Real.exp ((-α.im - 1) * y)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi hexp 0
  have hdom : IntegrableOn (fun y : ℝ =>
      K * Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2) * Real.exp ((-α.im - 1) * y)) (Ioi 0) :=
    hbase.const_mul _
  have hint := integrableOn_stokesPhase_mul_sourceTerm hα hn (0 : ℝ)
  have hle : ∀ y ∈ Ioi (0 : ℝ),
      ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖ ≤
        K * Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2) * Real.exp ((-α.im - 1) * y) := by
    intro y hy
    have hy0 : (0 : ℝ) ≤ y := le_of_lt hy
    have hatom := exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos
      thetaCuspSeedPolynomial hy0 hn
    have hrw : thetaCuspPolynomialAtom thetaCuspSeedPolynomial n y =
        thetaCuspSourceTerm y n :=
      (congrFun (thetaCuspSourceTerm_eq_polynomialAtom n) y).symm
    rw [hrw] at hatom
    rw [norm_phaseAtom α n y]
    have hsplit : Real.exp (-α.im * y) =
        Real.exp ((-α.im - 1) * y) * Real.exp y := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit, mul_assoc]
    have hpos : (0 : ℝ) ≤ Real.exp ((-α.im - 1) * y) := (Real.exp_pos _).le
    calc Real.exp ((-α.im - 1) * y) * (Real.exp y * |thetaCuspSourceTerm y n|)
        ≤ Real.exp ((-α.im - 1) * y) * (K * Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hatom hpos
      _ = K * Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2) * Real.exp ((-α.im - 1) * y) := by ring
  calc (∫ y in Ioi (0 : ℝ), ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖)
      ≤ ∫ y in Ioi (0 : ℝ),
          K * Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2) * Real.exp ((-α.im - 1) * y) :=
        setIntegral_mono_on hint.norm hdom measurableSet_Ioi hle
    _ = K * Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2) *
          ∫ y in Ioi (0 : ℝ), Real.exp ((-α.im - 1) * y) := by
        rw [MeasureTheory.integral_const_mul]
    _ = K * Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2) * (1 / (1 + α.im)) := by
        rw [integral_exp_mul_Ioi hexp]
        congr 1
        rw [mul_zero, Real.exp_zero]
        have hne : (1 : ℝ) + α.im ≠ 0 := by linarith
        rw [show (-α.im - 1) = -(1 + α.im) by ring]
        field_simp

private theorem integral_norm_phaseAtom_Ioc_le {α : ℂ} (hα : -1 < α.im) {R : ℝ} (hR : 0 < R)
    {n : ℕ} (hn : 0 < n) :
    (∫ y in Ioc (-R) (0 : ℝ), ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖) ≤
      Real.exp (|α.im| * R) * thetaCuspSourceMajorant R n * R := by
  have hintIoi : IntegrableOn
      (fun y : ℝ => ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖) (Ioi (-R)) :=
    (integrableOn_stokesPhase_mul_sourceTerm hα hn (-R)).norm
  have hint : IntegrableOn
      (fun y : ℝ => ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖) (Ioc (-R) (0 : ℝ)) :=
    hintIoi.mono_set Ioc_subset_Ioi_self
  have hle : ∀ y ∈ Ioc (-R) (0 : ℝ),
      ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖ ≤
        Real.exp (|α.im| * R) * thetaCuspSourceMajorant R n := by
    intro y hy
    have hmem : y ∈ Icc (-R) R := ⟨hy.1.le, le_trans hy.2 hR.le⟩
    have hmaj := abs_thetaCuspSourceTerm_le_majorant hmem n
    have hphase : ‖stokesPhase α y‖ ≤ Real.exp (|α.im| * R) := by
      rw [norm_stokesPhase]
      apply Real.exp_le_exp.mpr
      calc -α.im * y ≤ |(-α.im) * y| := le_abs_self _
        _ = |α.im| * |y| := by rw [abs_mul, abs_neg]
        _ ≤ |α.im| * R := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [abs_of_nonpos hy.2]
            linarith [hy.1]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hphase hmaj (abs_nonneg _) (Real.exp_pos _).le
  have hconst : IntegrableOn (fun _ : ℝ =>
      Real.exp (|α.im| * R) * thetaCuspSourceMajorant R n) (Ioc (-R) (0 : ℝ)) :=
    continuous_const.integrableOn_Ioc
  calc (∫ y in Ioc (-R) (0 : ℝ), ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖)
      ≤ ∫ _y in Ioc (-R) (0 : ℝ), Real.exp (|α.im| * R) * thetaCuspSourceMajorant R n :=
        setIntegral_mono_on hint hconst measurableSet_Ioc hle
    _ = Real.exp (|α.im| * R) * thetaCuspSourceMajorant R n * R := by
        rw [setIntegral_const, smul_eq_mul]
        have hvol : MeasureTheory.volume.real (Ioc (-R) (0 : ℝ)) = R := by
          simp [MeasureTheory.measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal, hR.le]
        rw [hvol]
        ring

end

end RHTower

namespace RHTower

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

/-! ## The Euler transgression of the anti-causal mode -/

theorem integral_norm_phaseAtom_le {α : ℂ} (hα : -1 < α.im) {R : ℝ} (hR : 0 < R) {x : ℝ}
    (hxR : -R ≤ x) {n : ℕ} (hn : 0 < n) :
    (∫ y in Ioi x, ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖) ≤
      Real.exp (|α.im| * R) * thetaCuspSourceMajorant R n * R +
        thetaCuspGaussianConstant thetaCuspSeedPolynomial *
          Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2) * (1 / (1 + α.im)) := by
  have hintR : IntegrableOn
      (fun y : ℝ => ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖)
      (Ioi (-R)) := (integrableOn_stokesPhase_mul_sourceTerm hα hn (-R)).norm
  have hmono : (∫ y in Ioi x, ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖) ≤
      ∫ y in Ioi (-R), ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖ := by
    refine setIntegral_mono_set hintR ?_ ?_
    · filter_upwards with y using norm_nonneg _
    · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hxR)
  have hunion : Ioc (-R) (0 : ℝ) ∪ Ioi (0 : ℝ) = Ioi (-R) :=
    Ioc_union_Ioi_eq_Ioi (by linarith)
  have hdisj : Disjoint (Ioc (-R) (0 : ℝ)) (Ioi (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact absurd hy.2 (not_le.mpr hy')
  have hsplit : (∫ y in Ioi (-R), ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖) =
      (∫ y in Ioc (-R) (0 : ℝ), ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖) +
        ∫ y in Ioi (0 : ℝ), ‖stokesPhase α y * (thetaCuspSourceTerm y n : ℂ)‖ := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
      (hintR.mono_set (by rw [← hunion]; exact subset_union_left))
      (hintR.mono_set (by rw [← hunion]; exact subset_union_right))]
  refine hmono.trans ?_
  rw [hsplit]
  exact add_le_add (integral_norm_phaseAtom_Ioc_le hα hR hn)
    (integral_norm_phaseAtom_Ioi_zero_le hα hn)

theorem summable_integral_norm_phaseAtom {α : ℂ} (hα : -1 < α.im) (x : ℝ) :
    Summable (fun n : ℕ =>
      ∫ y in Ioi x, ‖stokesPhase α y * (thetaCuspSourceTerm y (n + 1) : ℂ)‖) := by
  obtain ⟨R, hR, hxR⟩ : ∃ R : ℝ, 0 < R ∧ -R ≤ x :=
    ⟨|x| + 1, by positivity, by linarith [neg_abs_le x]⟩
  have hbound : ∀ n : ℕ,
      (∫ y in Ioi x, ‖stokesPhase α y * (thetaCuspSourceTerm y (n + 1) : ℂ)‖) ≤
        Real.exp (|α.im| * R) * thetaCuspSourceMajorant R (n + 1) * R +
          thetaCuspGaussianConstant thetaCuspSeedPolynomial *
            Real.exp (-(Real.pi / 2) * ((n : ℝ) + 1) ^ 2) * (1 / (1 + α.im)) := by
    intro n
    have h := integral_norm_phaseAtom_le hα hR hxR (Nat.succ_pos n)
    rwa [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring] at h
  have hsum1 : Summable (fun n : ℕ =>
      Real.exp (|α.im| * R) * thetaCuspSourceMajorant R (n + 1) * R) := by
    have h := (summable_nat_add_iff 1).mpr (summable_thetaCuspSourceMajorant R)
    exact ((h.mul_left (Real.exp (|α.im| * R))).mul_right R)
  have hsum2 : Summable (fun n : ℕ =>
      thetaCuspGaussianConstant thetaCuspSeedPolynomial *
        Real.exp (-(Real.pi / 2) * ((n : ℝ) + 1) ^ 2) * (1 / (1 + α.im))) := by
    have hpi : 0 < Real.pi / 2 := by positivity
    have h := summable_pow_mul_exp_neg_nat_sq 0 hpi
    have h' : Summable (fun n : ℕ => Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2)) := by
      simpa using h
    have h'' := (summable_nat_add_iff 1).mpr h'
    have h3 : Summable (fun n : ℕ => Real.exp (-(Real.pi / 2) * ((n : ℝ) + 1) ^ 2)) := by
      refine h''.congr fun n => ?_
      push_cast
      ring_nf
    exact (h3.mul_left (thetaCuspGaussianConstant thetaCuspSeedPolynomial)).mul_right
      (1 / (1 + α.im))
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _)
    hbound (hsum1.add hsum2)

theorem normalizedLogDilation_antiCausalGreen {α : ℂ} {n : ℕ} (hn : 0 < n) (x : ℝ) :
    normalizedLogDilation n (antiCausalGreen α thetaAtomSeed) x =
      -Complex.exp (-(Complex.I * α * (x : ℂ))) *
        ∫ y in Ioi x, stokesPhase α y * (thetaCuspSourceTerm y n : ℂ) := by
  rw [normalizedLogDilation, antiCausalGreen]
  set L : ℝ := Real.log (n : ℝ) with hLdef
  set c : ℂ := (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcdef
  set P : ℂ := stokesPhase α L with hPdef
  set J : ℂ := ∫ y in Ioi x, stokesPhase α y * thetaAtomSeed (y + L) with hJdef
  have step1 : (∫ y in Ioi (x + L), stokesPhase α y * thetaAtomSeed y) = P * J := by
    rw [hJdef, hPdef,
      ← setIntegral_Ioi_comp_add_right (fun y => stokesPhase α y * thetaAtomSeed y) x L,
      ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    rw [stokesPhase_add]
    ring
  have step2 : c * J = ∫ y in Ioi x, stokesPhase α y * (thetaCuspSourceTerm y n : ℂ) := by
    rw [hJdef, hcdef, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    have h3 := normalizedLogDilation_thetaAtomSeed hn y
    rw [normalizedLogDilation] at h3
    rw [← h3, hLdef]
    ring
  have step3 : Complex.exp (-(Complex.I * α * ((x + L : ℝ) : ℂ))) * P =
      Complex.exp (-(Complex.I * α * (x : ℂ))) := by
    rw [hPdef, stokesPhase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [step1,
    show c * (-Complex.exp (-(Complex.I * α * ((x + L : ℝ) : ℂ))) * (P * J)) =
      -(Complex.exp (-(Complex.I * α * ((x + L : ℝ) : ℂ))) * P) * (c * J) by ring,
    step3, step2]

/-- The shifted source atoms sum to the completed source. -/
theorem hasSum_sourceTerm_succ_complex (y : ℝ) :
    HasSum (fun n : ℕ => ((thetaCuspSourceTerm y (n + 1) : ℝ) : ℂ)) (thetaSourceComplex y) := by
  have hzero : thetaCuspSourceTerm y 0 = 0 := by
    simp [thetaCuspSourceTerm, thetaCuspSeed]
  have hbase : HasSum (fun n : ℕ => thetaCuspSourceTerm y n) (thetaCuspFullSource y) :=
    (summable_thetaCuspSourceTerm y).hasSum
  have hshift : HasSum (fun n : ℕ => thetaCuspSourceTerm y (n + 1))
      (thetaCuspFullSource y) := by
    refine (hasSum_nat_add_iff (f := fun n : ℕ => thetaCuspSourceTerm y n) 1).mpr ?_
    simpa [Finset.sum_range_one, hzero] using hbase
  exact Complex.ofRealCLM.hasSum hshift

/-- **The ordinary anti-causal Euler transgression.**  Euler synthesis of the anti-causal first
atom response is the anti-causal response of the completed source. -/
theorem eulerDilationSynthesis_antiCausalGreen {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    eulerDilationSynthesis (antiCausalGreen α thetaAtomSeed) x =
      antiCausalGreen α thetaSourceComplex x := by
  have hα' : -1 < α.im := by
    have h := abs_lt.mp hα
    linarith [h.1]
  have hint : ∀ n : ℕ, Integrable
      (fun y : ℝ => stokesPhase α y * (thetaCuspSourceTerm y (n + 1) : ℂ))
      (volume.restrict (Ioi x)) := fun n =>
    integrableOn_stokesPhase_mul_sourceTerm hα' (Nat.succ_pos n) x
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm hint
    (summable_integral_norm_phaseAtom hα' x)
  have hptw : ∀ y : ℝ,
      (∑' n : ℕ, stokesPhase α y * (thetaCuspSourceTerm y (n + 1) : ℂ)) =
        stokesPhase α y * thetaSourceComplex y := by
    intro y
    rw [tsum_mul_left, (hasSum_sourceTerm_succ_complex y).tsum_eq]
  rw [eulerDilationSynthesis,
    tsum_congr (fun n => normalizedLogDilation_antiCausalGreen (α := α) (Nat.succ_pos n) x),
    tsum_mul_left, hsum.tsum_eq, antiCausalGreen]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun y _ => hptw y)

end

end RHTower

namespace RHTower

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

/-! ## Geometric domination of the dilated anti-causal modes -/

theorem normalizedLogDilation_zero (f : ℝ → ℂ) (x : ℝ) :
    normalizedLogDilation 0 f x = 0 := by
  rw [normalizedLogDilation]
  norm_num [Real.zero_rpow]

theorem normalizedLogDilation_one (f : ℝ → ℂ) (x : ℝ) :
    normalizedLogDilation 1 f x = f x := by
  rw [normalizedLogDilation]
  norm_num

private theorem thetaCuspSourceMajorant_le (R : ℝ) (n : ℕ) :
    thetaCuspSourceMajorant R n ≤
      Real.exp (R / 2) * 2 * Real.pi *
          (2 * Real.pi * Real.exp R ^ 4 + 3 * Real.exp R ^ 2) *
        (((n : ℝ) + 1) ^ 4 * Real.exp (-(Real.pi * Real.exp (-2 * R)) * n)) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h4 : (n : ℝ) ^ 4 ≤ ((n : ℝ) + 1) ^ 4 := by
    gcongr
    linarith
  have h2 : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 4 := by
    have hsq : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
      gcongr
      linarith
    have hgrow : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 4 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      calc ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ 2 * 1 := by ring
        _ ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 := by nlinarith
        _ = ((n : ℝ) + 1) ^ 4 := by ring
    linarith
  rw [thetaCuspSourceMajorant]
  have hpoly : 2 * Real.pi * ((n : ℝ) * Real.exp R) ^ 4 + 3 * ((n : ℝ) * Real.exp R) ^ 2 ≤
      (2 * Real.pi * Real.exp R ^ 4 + 3 * Real.exp R ^ 2) * ((n : ℝ) + 1) ^ 4 := by
    rw [mul_pow, mul_pow]
    have hA : 2 * Real.pi * Real.exp R ^ 4 * (n : ℝ) ^ 4 ≤
        2 * Real.pi * Real.exp R ^ 4 * ((n : ℝ) + 1) ^ 4 :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have hB : 3 * Real.exp R ^ 2 * (n : ℝ) ^ 2 ≤
        3 * Real.exp R ^ 2 * ((n : ℝ) + 1) ^ 4 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hpos : (0 : ℝ) ≤ Real.exp (R / 2) * 2 * Real.pi := by positivity
  have hexp : (0 : ℝ) ≤ Real.exp (-(Real.pi * Real.exp (-2 * R)) * n) := (Real.exp_pos _).le
  calc Real.exp (R / 2) * 2 * Real.pi *
        (2 * Real.pi * ((n : ℝ) * Real.exp R) ^ 4 + 3 * ((n : ℝ) * Real.exp R) ^ 2) *
        Real.exp (-(Real.pi * Real.exp (-2 * R)) * n)
      ≤ Real.exp (R / 2) * 2 * Real.pi *
          ((2 * Real.pi * Real.exp R ^ 4 + 3 * Real.exp R ^ 2) * ((n : ℝ) + 1) ^ 4) *
          Real.exp (-(Real.pi * Real.exp (-2 * R)) * n) := by
        gcongr
    _ = Real.exp (R / 2) * 2 * Real.pi *
          (2 * Real.pi * Real.exp R ^ 4 + 3 * Real.exp R ^ 2) *
          (((n : ℝ) + 1) ^ 4 * Real.exp (-(Real.pi * Real.exp (-2 * R)) * n)) := by ring

theorem exists_geometric_bound_dilated_antiCausalGreen {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    ∃ C σ : ℝ, 0 < σ ∧ ∀ r : ℕ,
      ‖normalizedLogDilation r (antiCausalGreen α thetaAtomSeed) x‖ ≤
        C * ((r : ℝ) + 1) ^ 4 * Real.exp (-σ * r) := by
  have hα' : -1 < α.im := by
    have h := abs_lt.mp hα
    linarith [h.1]
  obtain ⟨R, hR, hxR⟩ : ∃ R : ℝ, 0 < R ∧ -R ≤ x :=
    ⟨|x| + 1, by positivity, by linarith [neg_abs_le x]⟩
  set C₁ : ℝ := Real.exp (R / 2) * 2 * Real.pi *
    (2 * Real.pi * Real.exp R ^ 4 + 3 * Real.exp R ^ 2) with hC₁
  set K : ℝ := thetaCuspGaussianConstant thetaCuspSeedPolynomial with hKdef
  have hK0 : 0 ≤ K := thetaCuspGaussianConstant_nonneg _
  have hσ₁ : 0 < Real.pi * Real.exp (-2 * R) := mul_pos Real.pi_pos (Real.exp_pos _)
  refine ⟨Real.exp (α.im * x) *
      (Real.exp (|α.im| * R) * R * C₁ + K * (1 / (1 + α.im))),
    min (Real.pi * Real.exp (-2 * R)) (Real.pi / 2), lt_min hσ₁ (by positivity), fun r => ?_⟩
  set σ : ℝ := min (Real.pi * Real.exp (-2 * R)) (Real.pi / 2) with hσdef
  have hCnn : (0 : ℝ) ≤ Real.exp (α.im * x) *
      (Real.exp (|α.im| * R) * R * C₁ + K * (1 / (1 + α.im))) := by
    have h1 : (0 : ℝ) ≤ C₁ := by
      rw [hC₁]
      positivity
    have h2 : (0 : ℝ) < 1 + α.im := by linarith
    positivity
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [normalizedLogDilation_zero, norm_zero]
    norm_num
    rw [one_div] at hCnn
    exact hCnn
  · have hW := normalizedLogDilation_antiCausalGreen (α := α) hr x
    have hnormphase : ‖Complex.exp (-(Complex.I * α * (x : ℂ)))‖ = Real.exp (α.im * x) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    have hbnd : ‖normalizedLogDilation r (antiCausalGreen α thetaAtomSeed) x‖ ≤
        Real.exp (α.im * x) *
          (∫ y in Ioi x, ‖stokesPhase α y * (thetaCuspSourceTerm y r : ℂ)‖) := by
      rw [hW, norm_mul, norm_neg, hnormphase]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
        (Real.exp_pos _).le
    refine hbnd.trans ?_
    have hint := integral_norm_phaseAtom_le hα' hR hxR hr
    have hmaj := thetaCuspSourceMajorant_le R r
    have hrsq : (r : ℝ) ≤ (r : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith
    have hgauss : Real.exp (-(Real.pi / 2) * (r : ℝ) ^ 2) ≤
        ((r : ℝ) + 1) ^ 4 * Real.exp (-σ * r) := by
      have hstep : Real.exp (-(Real.pi / 2) * (r : ℝ) ^ 2) ≤ Real.exp (-σ * r) := by
        apply Real.exp_le_exp.mpr
        have hσle : σ ≤ Real.pi / 2 := min_le_right _ _
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        nlinarith [Real.pi_pos]
      have hone : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 4 := by
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        have h1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
        exact one_le_pow₀ h1
      nlinarith [Real.exp_pos (-σ * (r : ℝ)), Real.exp_pos (-(Real.pi / 2) * (r : ℝ) ^ 2)]
    have hmajσ : thetaCuspSourceMajorant R r ≤ C₁ * (((r : ℝ) + 1) ^ 4 * Real.exp (-σ * r)) := by
      refine hmaj.trans ?_
      have hσle : σ ≤ Real.pi * Real.exp (-2 * R) := min_le_left _ _
      have hstep : Real.exp (-(Real.pi * Real.exp (-2 * R)) * r) ≤ Real.exp (-σ * r) := by
        apply Real.exp_le_exp.mpr
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        nlinarith
      have hC₁0 : (0 : ℝ) ≤ C₁ := by rw [hC₁]; positivity
      have hpow : (0 : ℝ) ≤ ((r : ℝ) + 1) ^ 4 := by positivity
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hpow) hC₁0
    have hinv : (0 : ℝ) < 1 / (1 + α.im) := by
      have : (0 : ℝ) < 1 + α.im := by linarith
      positivity
    have hfinal : Real.exp (|α.im| * R) * thetaCuspSourceMajorant R r * R +
        K * Real.exp (-(Real.pi / 2) * (r : ℝ) ^ 2) * (1 / (1 + α.im)) ≤
        (Real.exp (|α.im| * R) * R * C₁ + K * (1 / (1 + α.im))) *
          (((r : ℝ) + 1) ^ 4 * Real.exp (-σ * r)) := by
      have hA : Real.exp (|α.im| * R) * thetaCuspSourceMajorant R r * R ≤
          Real.exp (|α.im| * R) * R * C₁ * (((r : ℝ) + 1) ^ 4 * Real.exp (-σ * r)) := by
        have h0 : (0 : ℝ) ≤ Real.exp (|α.im| * R) * R := by positivity
        nlinarith [hmajσ, Real.exp_pos (|α.im| * R), hR]
      have hB : K * Real.exp (-(Real.pi / 2) * (r : ℝ) ^ 2) * (1 / (1 + α.im)) ≤
          K * (1 / (1 + α.im)) * (((r : ℝ) + 1) ^ 4 * Real.exp (-σ * r)) := by
        have hcoef : (0 : ℝ) ≤ K * (1 / (1 + α.im)) := mul_nonneg hK0 hinv.le
        have hstep := mul_le_mul_of_nonneg_left hgauss hcoef
        have heq : K * Real.exp (-(Real.pi / 2) * (r : ℝ) ^ 2) * (1 / (1 + α.im)) =
            K * (1 / (1 + α.im)) * Real.exp (-(Real.pi / 2) * (r : ℝ) ^ 2) := by ring
        rw [heq]
        exact hstep
      exact le_trans (add_le_add hA hB) (le_of_eq (by ring))
    refine le_trans (mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hfinal (Real.exp_pos _).le) (le_of_eq ?_)
    ring

end

end RHTower

namespace RHTower

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

/-! ## The ordinary Möbius inverse on the anti-causal mode -/

theorem normalizedLogDilation_mul (m n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    normalizedLogDilation (m * n) f x =
      (((m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        normalizedLogDilation n f (x + Real.log m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [normalizedLogDilation, Real.zero_rpow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [normalizedLogDilation, Real.zero_rpow]
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : (((m * n : ℕ) : ℝ)) = (m : ℝ) * (n : ℝ) := by push_cast; ring
  have hpow : (((m * n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hcast, Real.mul_rpow hm0.le hn0.le]
  have hlog : Real.log ((m * n : ℕ) : ℝ) = Real.log (m : ℝ) + Real.log (n : ℝ) := by
    rw [hcast, Real.log_mul hm0.ne' hn0.ne']
  rw [normalizedLogDilation, normalizedLogDilation, hpow, hlog,
    show x + (Real.log (m : ℝ) + Real.log (n : ℝ)) = x + Real.log (m : ℝ) + Real.log (n : ℝ) by
      ring]
  push_cast
  ring

private theorem summable_pow_four_exp_neg {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) ^ 4 * Real.exp (-σ * r)) := by
  have h : ∀ A : ℕ, Summable (fun r : ℕ => (r : ℝ) ^ A * Real.exp (-σ * r)) := by
    intro A
    refine (summable_pow_mul_exp_neg A hσ).congr fun r => ?_
    congr 2
    ring
  have hall := (((h 4).add ((h 3).mul_left 4)).add ((h 2).mul_left 6)).add
    (((h 1).mul_left 4).add ((h 0).mul_left 1))
  refine hall.congr fun r => ?_
  ring

theorem summable_prod_norm_dilated {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      ‖normalizedLogDilation (p.1 * p.2) (antiCausalGreen α thetaAtomSeed) x‖) := by
  obtain ⟨C, σ, hσ, hbd⟩ := exists_geometric_bound_dilated_antiCausalGreen hα x
  have hC0 : 0 ≤ C := by
    have h := hbd 0
    rw [normalizedLogDilation_zero, norm_zero] at h
    simpa using h
  have hPsummable : Summable (fun r : ℕ =>
      (C + 1) * (((r : ℝ) + 1) ^ 4 * Real.exp (-(σ / 2) * r))) :=
    (summable_pow_four_exp_neg (by positivity)).mul_left (C + 1)
  have hPnonneg : ∀ r : ℕ,
      0 ≤ (C + 1) * (((r : ℝ) + 1) ^ 4 * Real.exp (-(σ / 2) * r)) := by
    intro r
    have : (0 : ℝ) ≤ C + 1 := by linarith
    positivity
  have hprod : Summable (fun p : ℕ × ℕ =>
      (C + 1) * (((p.1 : ℝ) + 1) ^ 4 * Real.exp (-(σ / 2) * p.1)) *
      ((C + 1) * (((p.2 : ℝ) + 1) ^ 4 * Real.exp (-(σ / 2) * p.2)))) :=
    hPsummable.mul_of_nonneg hPsummable hPnonneg hPnonneg
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hprod
  rcases Nat.eq_zero_or_pos p.1 with h1 | h1
  · rw [h1, zero_mul, normalizedLogDilation_zero, norm_zero]
    exact mul_nonneg (hPnonneg _) (hPnonneg _)
  rcases Nat.eq_zero_or_pos p.2 with h2 | h2
  · rw [h2, mul_zero, normalizedLogDilation_zero, norm_zero]
    exact mul_nonneg (hPnonneg _) (hPnonneg _)
  have hm : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast h1
  have hn : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast h2
  have hcast : ((p.1 * p.2 : ℕ) : ℝ) = (p.1 : ℝ) * (p.2 : ℝ) := by push_cast; ring
  have hb := hbd (p.1 * p.2)
  rw [hcast] at hb
  refine hb.trans ?_
  have hexp : Real.exp (-σ * ((p.1 : ℝ) * (p.2 : ℝ))) ≤
      Real.exp (-(σ / 2) * p.1) * Real.exp (-(σ / 2) * p.2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hkey : (0 : ℝ) ≤ (p.1 : ℝ) * (p.2 : ℝ) - ((p.1 : ℝ) + (p.2 : ℝ)) / 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (p.1 : ℝ) - 1)
        (by linarith : (0 : ℝ) ≤ (p.2 : ℝ) - 1)]
    nlinarith [mul_nonneg hσ.le hkey]
  have hbase : (0 : ℝ) ≤ (p.1 : ℝ) * (p.2 : ℝ) + 1 := by nlinarith
  have hlin : (p.1 : ℝ) * (p.2 : ℝ) + 1 ≤ ((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) := by nlinarith
  have hpoly : ((p.1 : ℝ) * (p.2 : ℝ) + 1) ^ 4 ≤ ((p.1 : ℝ) + 1) ^ 4 * ((p.2 : ℝ) + 1) ^ 4 := by
    have h4 := pow_le_pow_left₀ hbase hlin 4
    rwa [mul_pow] at h4
  have hCsq : C ≤ (C + 1) * (C + 1) := by nlinarith
  have hnn1 : (0 : ℝ) ≤ ((p.1 : ℝ) + 1) ^ 4 * ((p.2 : ℝ) + 1) ^ 4 := by positivity
  have hnn2 : (0 : ℝ) ≤ Real.exp (-(σ / 2) * p.1) * Real.exp (-(σ / 2) * p.2) := by positivity
  have hApos : (0 : ℝ) ≤ C * (((p.1 : ℝ) * (p.2 : ℝ) + 1) ^ 4) := by positivity
  have hA : C * (((p.1 : ℝ) * (p.2 : ℝ) + 1) ^ 4) ≤
      (C + 1) * (C + 1) * (((p.1 : ℝ) + 1) ^ 4 * ((p.2 : ℝ) + 1) ^ 4) := by
    have hstep1 : C * (((p.1 : ℝ) * (p.2 : ℝ) + 1) ^ 4) ≤
        C * (((p.1 : ℝ) + 1) ^ 4 * ((p.2 : ℝ) + 1) ^ 4) :=
      mul_le_mul_of_nonneg_left hpoly hC0
    have hstep2 : C * (((p.1 : ℝ) + 1) ^ 4 * ((p.2 : ℝ) + 1) ^ 4) ≤
        (C + 1) * (C + 1) * (((p.1 : ℝ) + 1) ^ 4 * ((p.2 : ℝ) + 1) ^ 4) :=
      mul_le_mul_of_nonneg_right hCsq hnn1
    exact hstep1.trans hstep2
  have hstep : C * (((p.1 : ℝ) * (p.2 : ℝ) + 1) ^ 4) *
      Real.exp (-σ * ((p.1 : ℝ) * (p.2 : ℝ))) ≤
      (C + 1) * (C + 1) * (((p.1 : ℝ) + 1) ^ 4 * ((p.2 : ℝ) + 1) ^ 4) *
        (Real.exp (-(σ / 2) * p.1) * Real.exp (-(σ / 2) * p.2)) :=
    le_trans (mul_le_mul_of_nonneg_left hexp hApos)
      (mul_le_mul_of_nonneg_right hA hnn2)
  refine hstep.trans (le_of_eq ?_)
  ring

end

end RHTower

namespace RHTower

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

theorem summable_normalizedLogDilation_antiCausalGreen {α : ℂ} (hα : |α.im| < 1) (z : ℝ) :
    Summable (fun n : ℕ => normalizedLogDilation n (antiCausalGreen α thetaAtomSeed) z) := by
  obtain ⟨C, σ, hσ, hbd⟩ := exists_geometric_bound_dilated_antiCausalGreen hα z
  refine Summable.of_norm_bounded ((summable_pow_four_exp_neg hσ).mul_left C) fun n => ?_
  have h := hbd n
  rw [mul_assoc] at h
  exact h

theorem tsum_normalizedLogDilation_eq_euler {α : ℂ} (hα : |α.im| < 1) (z : ℝ) :
    (∑' n : ℕ, normalizedLogDilation n (antiCausalGreen α thetaAtomSeed) z) =
      eulerDilationSynthesis (antiCausalGreen α thetaAtomSeed) z := by
  rw [eulerDilationSynthesis,
    (summable_normalizedLogDilation_antiCausalGreen hα z).tsum_eq_zero_add,
    normalizedLogDilation_zero, zero_add]

private theorem sum_divisorsAntidiagonal_moebius_complex (r : ℕ) :
    (∑ p ∈ r.divisorsAntidiagonal, ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ)) =
      if r = 1 then 1 else 0 := by
  have hz : (ArithmeticFunction.moebius *
      (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) r = (1 : ArithmeticFunction ℤ) r := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at hz
  have hzsimp : (∑ p ∈ r.divisorsAntidiagonal,
      ArithmeticFunction.moebius p.1 *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) p.2)) =
      ∑ p ∈ r.divisorsAntidiagonal, ArithmeticFunction.moebius p.1 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 := (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).2
    simp [hp2]
  rw [hzsimp] at hz
  rw [← Int.cast_sum, hz]
  split_ifs <;> norm_num

/-- **The ordinary Möbius inverse on the root tail.**  Möbius dilation synthesis applied to the
anti-causal response of the completed source returns the anti-causal response of the single first
theta atom. -/
theorem mobiusDilationSynthesis_antiCausalGreen {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    mobiusDilationSynthesis (antiCausalGreen α thetaSourceComplex) x =
      antiCausalGreen α thetaAtomSeed x := by
  set v : ℝ → ℂ := antiCausalGreen α thetaAtomSeed with hv
  set F : ℕ × ℕ → ℂ := fun p =>
    ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) *
      normalizedLogDilation (p.1 * p.2) v x with hFdef
  have hFsum : Summable F := by
    refine Summable.of_norm_bounded (summable_prod_norm_dilated hα x) fun p => ?_
    rw [hFdef]
    simp only [norm_mul]
    have hmu : ‖((ArithmeticFunction.moebius p.1 : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hnn := norm_nonneg (normalizedLogDilation (p.1 * p.2) v x)
    nlinarith
  have hinner : ∀ m : ℕ, (∑' n : ℕ, F (m, n)) =
      ((ArithmeticFunction.moebius m : ℤ) : ℂ) *
        normalizedLogDilation m (antiCausalGreen α thetaSourceComplex) x := by
    intro m
    have h1 : (∑' n : ℕ, F (m, n)) =
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) *
          ∑' n : ℕ, normalizedLogDilation (m * n) v x := by
      have hbeta : ∀ n : ℕ, F (m, n) =
          ((ArithmeticFunction.moebius m : ℤ) : ℂ) * normalizedLogDilation (m * n) v x :=
        fun n => rfl
      rw [tsum_congr hbeta, tsum_mul_left]
    have h2 : (∑' n : ℕ, normalizedLogDilation (m * n) v x) =
        normalizedLogDilation m (antiCausalGreen α thetaSourceComplex) x := by
      have hcong : (∑' n : ℕ, normalizedLogDilation (m * n) v x) =
          (((m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑' n : ℕ, normalizedLogDilation n v (x + Real.log m) := by
        rw [tsum_congr (fun n => normalizedLogDilation_mul m n v x), tsum_mul_left]
      rw [hcong, hv, tsum_normalizedLogDilation_eq_euler hα,
        eulerDilationSynthesis_antiCausalGreen hα, normalizedLogDilation]
    rw [h1, h2]
  have hfiber : ∀ r : ℕ,
      (∑' b : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {r}), F b) =
        if r = 1 then normalizedLogDilation 1 v x else 0 := by
    intro r
    rcases eq_or_ne r 0 with rfl | hr
    · have hzero : ∀ b : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {(0 : ℕ)}), F b = 0 := by
        rintro ⟨p, hp⟩
        have hp0 : p.1 * p.2 = 0 := hp
        rw [hFdef]
        simp only
        rw [hp0, normalizedLogDilation_zero, mul_zero]
      simp [hzero]
    · have hset : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {r} = ↑(r.divisorsAntidiagonal) := by
        ext p
        simp [Nat.mem_divisorsAntidiagonal, hr]
      rw [hset, Finset.tsum_subtype' r.divisorsAntidiagonal F]
      have hterm : ∀ p ∈ r.divisorsAntidiagonal,
          F p = ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) *
            normalizedLogDilation r v x := by
        intro p hp
        rw [hFdef]
        simp only
        rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
        sum_divisorsAntidiagonal_moebius_complex r]
      split_ifs with h
      · rw [h, one_mul]
      · rw [zero_mul]
  have hfib := hFsum.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  rw [funext hfiber] at hfib
  have hone : HasSum (fun r : ℕ => if r = 1 then normalizedLogDilation 1 v x else 0)
      (normalizedLogDilation 1 v x) := hasSum_ite_eq (1 : ℕ) _
  have hval : (∑' p : ℕ × ℕ, F p) = normalizedLogDilation 1 v x := hfib.unique hone
  have hG : HasSum (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ) *
      normalizedLogDilation m (antiCausalGreen α thetaSourceComplex) x)
      (normalizedLogDilation 1 v x) := by
    have h := hFsum.hasSum.prod_fiberwise
      (g := fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ) *
        normalizedLogDilation m (antiCausalGreen α thetaSourceComplex) x)
      (fun m => by
        rw [← hinner m]
        exact (hFsum.prod_factor m).hasSum)
    rwa [hval] at h
  have hG0 : ((ArithmeticFunction.moebius 0 : ℤ) : ℂ) *
      normalizedLogDilation 0 (antiCausalGreen α thetaSourceComplex) x = 0 := by
    rw [normalizedLogDilation_zero, mul_zero]
  have hshift : HasSum (fun m : ℕ => ((ArithmeticFunction.moebius (m + 1) : ℤ) : ℂ) *
      normalizedLogDilation (m + 1) (antiCausalGreen α thetaSourceComplex) x)
      (normalizedLogDilation 1 v x) := by
    refine (hasSum_nat_add_iff (f := fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ) *
      normalizedLogDilation m (antiCausalGreen α thetaSourceComplex) x) 1).mpr ?_
    simpa [Finset.sum_range_one, hG0] using hG
  rw [mobiusDilationSynthesis, hshift.tsum_eq, normalizedLogDilation_one, hv]

end

end RHTower

namespace RHTower

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

/-! ## The killed Gamma Stokes jet and its multiplicity -/

/-- The analytic Stokes jump family in the logarithmic coordinate. -/
def stokesJumpFamily (L : ℝ) (s : ℂ) : ℂ := Complex.exp (-s * (L : ℂ)) * archFactor s

theorem analyticAt_completedEulerStokes (L : ℝ) (ρ : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => Complex.exp (-s * (L : ℂ)) * xi s) ρ := by
  have hchar : AnalyticAt ℂ (fun s : ℂ => Complex.exp (-s * (L : ℂ))) ρ := by fun_prop
  exact hchar.mul (xi_analyticOnNhd_univ ρ (Set.mem_univ ρ))

theorem analyticOrderAt_completedEulerStokes (L : ℝ) (ρ : ℂ) :
    analyticOrderAt (fun s : ℂ => Complex.exp (-s * (L : ℂ)) * xi s) ρ =
      analyticOrderAt xi ρ := by
  have hfun : (fun s : ℂ => Complex.exp (-s * (L : ℂ)) * xi s) =
      thetaGammaCompletedEulerOutput (Real.exp L) := by
    funext s
    rw [thetaGammaCompletedEulerOutput, Real.log_exp]
  rw [hfun]
  exact analyticOrderAt_thetaGammaCompletedEulerOutput (Real.exp_pos L) ρ

/-- **The killed Stokes jet has exactly the Xi multiplicity.**  Every spectral jet of the
completed Euler image below the analytic order of `Xi` vanishes. -/
theorem iteratedDeriv_completedEulerStokes_eq_zero (L : ℝ) {ρ : ℂ} {m : ℕ}
    (hm : analyticOrderAt xi ρ = m) {r : ℕ} (hr : r < m) :
    iteratedDeriv r (fun s : ℂ => Complex.exp (-s * (L : ℂ)) * xi s) ρ = 0 :=
  (((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (analyticAt_completedEulerStokes L ρ)).1
      (by rw [analyticOrderAt_completedEulerStokes, hm])).1) r hr

/-- The order-`m` jet of the completed Euler image is nonzero. -/
theorem iteratedDeriv_completedEulerStokes_ne_zero (L : ℝ) {ρ : ℂ} {m : ℕ}
    (hm : analyticOrderAt xi ρ = m) :
    iteratedDeriv m (fun s : ℂ => Complex.exp (-s * (L : ℂ)) * xi s) ρ ≠ 0 :=
  ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (analyticAt_completedEulerStokes L ρ)).1
      (by rw [analyticOrderAt_completedEulerStokes, hm])).2

end

end RHTower

namespace RHTower

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

/-! ## Triangularity and independence of the Stokes jets -/

private theorem iteratedDeriv_expLinear (L : ℝ) (j : ℕ) (ρ : ℂ) :
    iteratedDeriv j (fun s : ℂ => Complex.exp (-s * (L : ℂ))) ρ =
      (-(L : ℂ)) ^ j * Complex.exp (-ρ * (L : ℂ)) := by
  induction j generalizing ρ with
  | zero => simp
  | succ j ih =>
      have hderiv : deriv (fun s : ℂ => Complex.exp (-s * (L : ℂ))) =
          fun s : ℂ => -(L : ℂ) * Complex.exp (-s * (L : ℂ)) := by
        funext s
        have hlin : HasDerivAt (fun z : ℂ => -z * (L : ℂ)) (-(L : ℂ)) s := by
          simpa using ((hasDerivAt_id s).neg).mul_const (L : ℂ)
        have h := hlin.cexp
        rw [h.deriv]
        ring
      rw [iteratedDeriv_succ', hderiv,
        iteratedDeriv_const_mul _ (by fun_prop : ContDiffAt ℂ j
          (fun s : ℂ => Complex.exp (-s * (L : ℂ))) ρ), ih]
      ring

/-- The Stokes jet polynomial: the spectral jet of the jump family divided by its nonvanishing
character. -/
def stokesJetPolynomial (ρ : ℂ) (r : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (r + 1),
    Polynomial.C ((r.choose j : ℂ) * (-1) ^ j * iteratedDeriv (r - j) archFactor ρ) *
      Polynomial.X ^ j

theorem stokesJetPolynomial_natDegree_le (ρ : ℂ) (r : ℕ) :
    (stokesJetPolynomial ρ r).natDegree ≤ r := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_X_pow]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

theorem stokesJetPolynomial_coeff_self (ρ : ℂ) (r : ℕ) :
    (stokesJetPolynomial ρ r).coeff r = (-1) ^ r * archFactor ρ := by
  rw [stokesJetPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single r]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl]
    simp
  · intro j hj hjr
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hjr), mul_zero]
  · intro h
    exact absurd (Finset.self_mem_range_succ r) h

theorem iteratedDeriv_stokesJumpFamily {ρ : ℂ} (hρ : 0 < ρ.re) (L : ℝ) (r : ℕ) :
    iteratedDeriv r (stokesJumpFamily L) ρ =
      Complex.exp (-ρ * (L : ℂ)) * (stokesJetPolynomial ρ r).eval (L : ℂ) := by
  have hA : AnalyticAt ℂ archFactor ρ := archFactor_analyticOnNhd_re_pos ρ hρ
  have hg : ContDiffAt ℂ (r : ℕ) archFactor ρ := hA.contDiffAt
  have hf : ContDiffAt ℂ (r : ℕ) (fun s : ℂ => Complex.exp (-s * (L : ℂ))) ρ := by fun_prop
  have hmul := iteratedDeriv_fun_mul (n := r)
    (f := fun s : ℂ => Complex.exp (-s * (L : ℂ))) (g := archFactor) hf hg
  rw [show stokesJumpFamily L = fun s : ℂ => Complex.exp (-s * (L : ℂ)) * archFactor s from rfl,
    hmul, stokesJetPolynomial, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedDeriv_expLinear, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  ring

private theorem eq_zero_of_triangular_sum {m : ℕ} (Q : ℕ → Polynomial ℂ) (c : ℕ → ℂ)
    (hdeg : ∀ r, (Q r).natDegree ≤ r) (hlead : ∀ r, (Q r).coeff r ≠ 0)
    (hsum : ∑ r ∈ Finset.range m, Polynomial.C (c r) * Q r = 0) :
    ∀ r < m, c r = 0 := by
  induction m with
  | zero => intro r hr; omega
  | succ m ih =>
      have hcoeff : (∑ r ∈ Finset.range (m + 1), Polynomial.C (c r) * Q r).coeff m =
          c m * (Q m).coeff m := by
        rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
        · rw [Polynomial.coeff_C_mul]
        · intro r hr hrm
          have hlt : r < m := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) hrm
          rw [Polynomial.coeff_C_mul,
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg r) hlt), mul_zero]
        · intro h
          exact absurd (Finset.self_mem_range_succ m) h
      rw [hsum, Polynomial.coeff_zero] at hcoeff
      have hcm : c m = 0 := by
        rcases mul_eq_zero.mp hcoeff.symm with h | h
        · exact h
        · exact absurd h (hlead m)
      have hrest : ∑ r ∈ Finset.range m, Polynomial.C (c r) * Q r = 0 := by
        rw [Finset.sum_range_succ, hcm, map_zero, zero_mul, add_zero] at hsum
        exact hsum
      intro r hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | h
      · exact ih hrest r h
      · rw [h]; exact hcm

/-- **Independence of the killed Gamma Stokes jets.**  The spectral jets of the Stokes jump family
are triangular in the polynomial degree with nonvanishing diagonal `(-1)^r archFactor(rho)`, hence
linearly independent as functions of the logarithmic coordinate. -/
theorem stokesJumpJets_linearIndependent {ρ : ℂ} (hstrip : 0 < ρ.re ∧ ρ.re < 1) (m : ℕ)
    (c : ℕ → ℂ)
    (hzero : ∀ L : ℝ,
      ∑ r ∈ Finset.range m, c r * iteratedDeriv r (stokesJumpFamily L) ρ = 0) :
    ∀ r < m, c r = 0 := by
  have hA : archFactor ρ ≠ 0 := archFactor_ne_zero_strip hstrip
  have hlead : ∀ r : ℕ, (stokesJetPolynomial ρ r).coeff r ≠ 0 := by
    intro r
    rw [stokesJetPolynomial_coeff_self]
    exact mul_ne_zero (pow_ne_zero r (by norm_num)) hA
  set S : Polynomial ℂ :=
    ∑ r ∈ Finset.range m, Polynomial.C (c r) * stokesJetPolynomial ρ r with hS
  have hroot : ∀ L : ℝ, S.eval (L : ℂ) = 0 := by
    intro L
    have hz := hzero L
    have hexp : Complex.exp (-ρ * (L : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hz' : Complex.exp (-ρ * (L : ℂ)) * S.eval (L : ℂ) = 0 := by
      rw [hS, Polynomial.eval_finsetSum, Finset.mul_sum, ← hz]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C,
        iteratedDeriv_stokesJumpFamily hstrip.1 L r]
      ring
    exact (mul_eq_zero.mp hz').resolve_left hexp
  have hSzero : S = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot S ?_
    have hsub : Set.range (fun L : ℝ => (L : ℂ)) ⊆ {x | S.IsRoot x} := by
      rintro x ⟨L, rfl⟩
      exact hroot L
    refine Set.Infinite.mono hsub ?_
    exact Set.infinite_range_of_injective Complex.ofReal_injective
  exact eq_zero_of_triangular_sum (stokesJetPolynomial ρ) c
    (stokesJetPolynomial_natDegree_le ρ) hlead hSzero

end

end RHTower
