import GaloisForLFunctions.ArithmeticLorentzianGeometry.ThePoleDefectPaysThePole
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheUniversalThresholdIsFinite
import GaloisForLFunctions.ArithmeticElectrostatics.TheGaugeIsInvisibleAtAtomicResolution

/-!
# The pole hyperplane is the harmonic hyperplane

Weil's form carries the pole through the two exponential moments `A(f) = ∫ f e^{−u/2}` and
`B(f) = ∫ f e^{u/2}`: `W(f) = M(f) + 2A(f)B(f)` with `M` the Markov form.
RenormalizedArithmeticPotentialTheory proves its prime gap on the discrete *harmonic hyperplane*
`Σ_{n ≤ N} x_n/√n = 0`, and SpacingScaleHarmonicAnalysis states RH on the continuous *pole
hyperplane* `A(f) = 0`. On atomic tests `f_x = Σ_{n ≤ N} x_n g(· − log n)` the two are the same
hyperplane.

* **Pole moments of an atomic test** (`integral_atomicTest_mul_exp_neg_half`,
  `integral_atomicTest_mul_exp_half`): `A(f_x) = A(g) Σ x_n/√n` and `B(f_x) = B(g) Σ x_n √n`.
* **Weil's form is the Markov form on the hyperplane**
  (`weilQuad_atomicTest_eq_markov_of_harmonic`): the pole term of an atomic test vanishes when
  `Σ x_n/√n = 0`.
* **Twins differ only in the prime form** (`weilQuadTw_atomicTest_sub_weilQuad`): for a sign twin
  `ωΛ`, the full twisted Weil form of an atomic test below the spacing is `ζ`'s full form plus
  `(∫ g²)(P_N(x) − P_N^ω(x))`. The archimedean diagonal and both pole moments cancel exactly; the
  whole difference between `ζ` and its twin is prime.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticLorentzianGeometry

theorem exp_half_log_eq_sqrt {n : ℕ} (hn : 1 ≤ n) : Real.exp (Real.log n / 2) = Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]
  ring_nf

theorem exp_neg_half_log_eq {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(Real.log n / 2)) = 1 / Real.sqrt n := by
  rw [Real.exp_neg, exp_half_log_eq_sqrt hn, one_div]

/-- Translating a profile multiplies its exponential moment:
`∫ g(u − c) e^{au} = e^{ac} ∫ g e^{au}`. -/
theorem integral_shift_mul_exp (g : ℝ → ℝ) (c a : ℝ) :
    ∫ u, g (u - c) * Real.exp (a * u) = Real.exp (a * c) * ∫ u, g u * Real.exp (a * u) := by
  have h := integral_sub_right_eq_self (μ := volume) (fun v => g v * Real.exp (a * (v + c))) c
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul]
  congr 1
  funext v
  rw [mul_add, Real.exp_add]
  ring

variable {g : ℝ → ℝ} {w : ℝ}

/-- **The lower pole moment of an atomic test is the harmonic sum**: `A(f_x) = A(g) Σ x_n/√n`. -/
theorem integral_atomicTest_mul_exp_neg_half (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (x : ℕ → ℝ) :
    ∫ u, atomicTest N x g u * Real.exp (-(u / 2)) =
      (∫ u, g u * Real.exp (-(u / 2))) * ∑ n ∈ Icc 1 N, x n / Real.sqrt n := by
  rw [integral_atomicTest_mul (by fun_prop) hg hgsupp, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have h := integral_shift_mul_exp g (Real.log n) (-(1 / 2))
  simp only [show ∀ u : ℝ, -(1 / 2) * u = -(u / 2) from fun u => by ring] at h
  rw [h, exp_neg_half_log_eq (mem_Icc.mp hn).1]
  ring

/-- **The upper pole moment of an atomic test**: `B(f_x) = B(g) Σ x_n √n`. -/
theorem integral_atomicTest_mul_exp_half (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (x : ℕ → ℝ) :
    ∫ u, atomicTest N x g u * Real.exp (u / 2) =
      (∫ u, g u * Real.exp (u / 2)) * ∑ n ∈ Icc 1 N, x n * Real.sqrt n := by
  rw [integral_atomicTest_mul (by fun_prop) hg hgsupp, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have h := integral_shift_mul_exp g (Real.log n) (1 / 2)
  simp only [show ∀ u : ℝ, 1 / 2 * u = u / 2 from fun u => by ring] at h
  rw [h, exp_half_log_eq_sqrt (mem_Icc.mp hn).1]
  ring

/-- A compactly supported real function vanishes outside some symmetric window. -/
theorem exists_supportedIn {f : ℝ → ℝ} (hfc : HasCompactSupport f) : ∃ R, SupportedIn R f := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun u hu => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have h' := hR h
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h'
  linarith

/-- **Weil's form is the Markov form plus the pole term**: `W(f) = M(f) + 2A(f)B(f)`. -/
theorem weilQuad_eq_markov_add_pole {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    weilQuad f = markovEnergy (fun u => (f u : ℂ)) +
      2 * (∫ u, f u * Real.exp (-(u / 2))) * ∫ u, f u * Real.exp (u / 2) := by
  rw [weilQuad_eq hf hfc, add_sub_assoc, two_mul_cosh_sq_sub_sinh_sq_eq hf.continuous hfc,
    markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc]
  ring

/-- **A twin's Weil form is its Markov form plus the same pole term.** -/
theorem weilQuadTw_eq_twinMarkov_add_pole (ω : ArithmeticFunction ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    weilQuadTw (fun n => ω n * ArithmeticFunction.vonMangoldt n) f =
      archForm f - twistedPrimeSum ω f +
        2 * (∫ u, f u * Real.exp (-(u / 2))) * ∫ u, f u * Real.exp (u / 2) := by
  obtain ⟨R, hR⟩ := exists_supportedIn hfc
  rw [weilQuadTw_eq_markov ω hf hfc hR, two_mul_cosh_sq_sub_sinh_sq_eq hf.continuous hfc]

/-- **On the harmonic hyperplane Weil's form is the Markov form**: if `Σ x_n/√n = 0`, the pole
term of the atomic test vanishes. -/
theorem weilQuad_atomicTest_eq_markov_of_harmonic (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) {x : ℕ → ℝ}
    (hx : ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0) :
    weilQuad (atomicTest N x g) = markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  rw [weilQuad_eq_markov_add_pole (contDiff_atomicTest hg N x)
    (hasCompactSupport_atomicTest hgsupp N x),
    integral_atomicTest_mul_exp_neg_half hg.continuous hgsupp, hx]
  ring

/-- **Twins differ from `ζ` only in the prime form**: below the spacing, for every sign twin `ωΛ`,
`W_ω(f_x) − W(f_x) = (∫ g²)(P_N(x) − P_N^ω(x))`. -/
theorem weilQuadTw_atomicTest_sub_weilQuad {ω : ArithmeticFunction ℝ}
    (hω : ∀ a b, ω (a * b) = ω a * ω b) (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ) :
    weilQuadTw (fun n => ω n * ArithmeticFunction.vonMangoldt n) (atomicTest N x g) -
        weilQuad (atomicTest N x g) =
      (∫ u, g u ^ 2) * (atomicWeilForm N x - twistedAtomicWeilForm ω N x) := by
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [weilQuadTw_eq_twinMarkov_add_pole ω hf hfc, weilQuad_eq_markov_add_pole hf hfc,
    ← twinMarkov_sub_markov_atomicTest hω hsign hg hgc hgsupp hw x]
  ring

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
