import GaloisForLFunctions.RHTower.EulerHedenmalmGammaStokesTransgression
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.ThetaCuspFourierLaplace

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
    have hn : 0 < n + 1 := Nat.succ_pos n
    have hintR : IntegrableOn
        (fun y : ℝ => ‖stokesPhase α y * (thetaCuspSourceTerm y (n + 1) : ℂ)‖)
        (Ioi (-R)) := (integrableOn_stokesPhase_mul_sourceTerm hα hn (-R)).norm
    have hmono : (∫ y in Ioi x, ‖stokesPhase α y * (thetaCuspSourceTerm y (n + 1) : ℂ)‖) ≤
        ∫ y in Ioi (-R), ‖stokesPhase α y * (thetaCuspSourceTerm y (n + 1) : ℂ)‖ := by
      refine setIntegral_mono_set hintR ?_ ?_
      · filter_upwards with y using norm_nonneg _
      · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hxR)
    have hunion : Ioc (-R) (0 : ℝ) ∪ Ioi (0 : ℝ) = Ioi (-R) :=
      Ioc_union_Ioi_eq_Ioi (by linarith)
    have hdisj : Disjoint (Ioc (-R) (0 : ℝ)) (Ioi (0 : ℝ)) := by
      rw [Set.disjoint_left]
      intro y hy hy'
      exact absurd hy.2 (not_le.mpr hy')
    have hsplit : (∫ y in Ioi (-R), ‖stokesPhase α y * (thetaCuspSourceTerm y (n + 1) : ℂ)‖) =
        (∫ y in Ioc (-R) (0 : ℝ), ‖stokesPhase α y * (thetaCuspSourceTerm y (n + 1) : ℂ)‖) +
          ∫ y in Ioi (0 : ℝ), ‖stokesPhase α y * (thetaCuspSourceTerm y (n + 1) : ℂ)‖ := by
      rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
        (hintR.mono_set (by rw [← hunion]; exact subset_union_left))
        (hintR.mono_set (by rw [← hunion]; exact subset_union_right))]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hlow := integral_norm_phaseAtom_Ioc_le hα hR hn
    have hhigh := integral_norm_phaseAtom_Ioi_zero_le hα hn
    rw [hcast] at hhigh
    refine hmono.trans ?_
    rw [hsplit]
    exact add_le_add hlow hhigh
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
