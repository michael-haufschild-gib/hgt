import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheCriticalExponent
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheStabilityLawAtTheSpacingScale
import GaloisForLFunctions.RHTower.CHMDEvenSectorPointSpectrum
import GaloisForLFunctions.RHTower.WeilMarkovOnePoleHyperplane
import GaloisForLFunctions.RHTower.WeilPolarConeKernelTransformForm

/-!
# The pole is the only negative square beyond the threshold

The Markov form `M = archForm − primeSum` is Weil's form without its pole:
`M(g) = Q(g) − 2 m₋(g) m₊(g)` with the pole moments `m_∓(g) = ∫ g e^{∓u/2}` (`markovQuad_eq`). At
width `≤ c₀ δ_N` it is nonnegative on every atomic test, for every `N` (SH4). Beyond the threshold
it is not, and the failure is not arithmetic.

* **Real and imaginary parts** (`markovEnergy_eq_re_add_im`): `M(u + iv) = M(u) + M(v)`, so the
  negative direction of `M` can be taken real (`exists_markovQuad_neg`).
* **The Markov law fails under overlap growth** (`markov_atomicFamilies_negative`): for every width
  `1/κ_N` of overlap growth, for infinitely many `N` some atomic test has `M < 0` — unconditionally,
  for `ζ` itself. The threshold of the Markov law lies between `c₀` and overlap growth
  (`markovThreshold_bracket`).
* **One negative square iff RH** (`riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg`): RH
  holds iff for all large `N` the Markov form is nonnegative on the atomic tests of width `1/κ_N` in
  the pole hyperplane `m₋ = 0`. The synthesis of a pole-free negative test is moved back into the
  hyperplane by a vanishing multiple of a synthesized bump.

The correction rank of the stability law is zero at the spacing; once the overlap ratio beats
`√(log N)` it is at least one, and it is exactly one — the pole — iff RH.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower Zeta23
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### The Markov form on real tests -/

/-- The pole moment `m₋(g) = ∫ g e^{−u/2}`: the transform at `s = 0`. -/
def poleMomentNeg (g : ℝ → ℝ) : ℝ := ∫ u, g u * Real.exp (-(u / 2))

/-- The pole moment `m₊(g) = ∫ g e^{u/2}`: the transform at `s = 1`. -/
def poleMomentPos (g : ℝ → ℝ) : ℝ := ∫ u, g u * Real.exp (u / 2)

/-- The Markov form `M(g) = archForm g − primeSum g` of a real test. -/
def markovQuad (g : ℝ → ℝ) : ℝ := markovEnergy (fun u => (g u : ℂ))

variable {g : ℝ → ℝ}

theorem re_weilPoleTerm_ofReal (hg : Continuous g) (hgc : HasCompactSupport g) :
    (weilPoleTerm (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re =
      2 * (poleMomentNeg g * poleMomentPos g) := by
  rw [weilPoleTerm_weilTest_eq (f := fun u => (g u : ℂ)) (Complex.continuous_ofReal.comp hg)
      (hgc.comp_left Complex.ofReal_zero), neg_div, paperFT_ofReal_I_half,
    paperFT_ofReal_neg_I_half, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  unfold poleMomentNeg poleMomentPos
  ring

/-- **Weil's form minus its pole**: `M(g) = Q(g) − 2 m₋(g) m₊(g)`. -/
theorem markovQuad_eq (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    markovQuad g = weilQuad g - 2 * (poleMomentNeg g * poleMomentPos g) := by
  have hf : ContDiff ℝ 2 (fun u => (g u : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hfc : HasCompactSupport (fun u => (g u : ℂ)) := hgc.comp_left Complex.ofReal_zero
  unfold markovQuad
  rw [markovEnergy_eq_W_sub hf hfc, zeta_W_eq_weilFullFunctional hf hfc,
    re_weilPoleTerm_ofReal hg.continuous hgc]
  rfl

/-- **Real and imaginary parts**: `M(u + iv) = M(u) + M(v)`. -/
theorem markovEnergy_eq_re_add_im {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    markovEnergy f = markovQuad (fun x => (f x).re) + markovQuad (fun x => (f x).im) := by
  have hu : ContDiff ℝ 2 (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have hv : ContDiff ℝ 2 (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have huc : HasCompactSupport (fun x => (f x).re) := hfc.comp_left Complex.zero_re
  have hvc : HasCompactSupport (fun x => (f x).im) := hfc.comp_left Complex.zero_im
  rw [markovQuad_eq hu huc, markovQuad_eq hv hvc, markovEnergy_eq_W_sub hf hfc,
    zeta_W_eq_weilFullFunctional hf hfc]
  have hsplit : (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest f f)).re = weilQuad (fun x => (f x).re) + weilQuad (fun x => (f x).im) :=
    CHMDPolar.re_weilFullFunctional_split _ ⟨f, hf, hfc⟩
  have hint : ∀ h : ℝ → ℝ, Continuous h → HasCompactSupport h → ∀ z : ℂ,
      Integrable fun u : ℝ => (h u : ℂ) * Complex.exp (Complex.I * z * u) := fun h hh hhc z =>
    integrable_mul_cexp_of_compact (Complex.continuous_ofReal.comp hh)
      (hhc.comp_left Complex.ofReal_zero) z
  have hP : ∀ z : ℂ, paperFT f z = paperFT (fun x => ((f x).re : ℂ)) z +
      Complex.I * paperFT (fun x => ((f x).im : ℂ)) z := by
    intro z
    have e : f = fun x => (1 : ℂ) * ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ) := by
      funext x
      rw [one_mul, mul_comm]
      exact (Complex.re_add_im (f x)).symm
    conv_lhs => rw [e]
    rw [paperFT_smul_add_smul 1 Complex.I z (hint _ hu.continuous huc z)
      (hint _ hv.continuous hvc z), one_mul]
  have hpole : (weilPoleTerm (EF.weilTest f f)).re =
      2 * (poleMomentNeg (fun x => (f x).re) * poleMomentPos (fun x => (f x).re)) +
        2 * (poleMomentNeg (fun x => (f x).im) * poleMomentPos (fun x => (f x).im)) := by
    rw [weilPoleTerm_weilTest_eq hf.continuous hfc, neg_div, hP, hP, paperFT_ofReal_I_half,
      paperFT_ofReal_I_half, paperFT_ofReal_neg_I_half, paperFT_ofReal_neg_I_half]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, Complex.add_im, Complex.mul_im]
    unfold poleMomentNeg poleMomentPos
    ring
  rw [hsplit, hpole]
  ring

/-- **The Markov form has a real negative direction.** -/
theorem exists_markovQuad_neg :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ markovQuad g < 0 := by
  obtain ⟨f, hf, hfc, hneg⟩ := exists_markovEnergy_neg
  rw [markovEnergy_eq_re_add_im hf hfc] at hneg
  by_cases h : markovQuad (fun x => (f x).re) < 0
  · exact ⟨fun x => (f x).re, Complex.reCLM.contDiff.comp hf, hfc.comp_left Complex.zero_re, h⟩
  · exact ⟨fun x => (f x).im, Complex.imCLM.contDiff.comp hf, hfc.comp_left Complex.zero_im,
      by linarith [not_lt.mp h]⟩

/-! ### Translation and continuity -/

theorem poleMomentNeg_comp_sub (g : ℝ → ℝ) (c : ℝ) :
    poleMomentNeg (fun u => g (u - c)) = Real.exp (-(c / 2)) * poleMomentNeg g := by
  unfold poleMomentNeg
  have h := integral_sub_right_eq_self (μ := volume) (fun v => g v * Real.exp (-((v + c) / 2))) c
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul]
  congr 1
  funext v
  rw [show -((v + c) / 2) = -(c / 2) + -(v / 2) by ring, Real.exp_add]
  ring

theorem poleMomentPos_comp_sub (g : ℝ → ℝ) (c : ℝ) :
    poleMomentPos (fun u => g (u - c)) = Real.exp (c / 2) * poleMomentPos g := by
  unfold poleMomentPos
  have h := integral_sub_right_eq_self (μ := volume) (fun v => g v * Real.exp ((v + c) / 2)) c
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul]
  congr 1
  funext v
  rw [show (v + c) / 2 = c / 2 + v / 2 by ring, Real.exp_add]
  ring

/-- **Translation invariance** of the Markov form. -/
theorem markovQuad_comp_sub (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (c : ℝ) :
    markovQuad (fun u => g (u - c)) = markovQuad g := by
  have h1 : ContDiff ℝ 2 (fun u => g (u - c)) := hg.comp (contDiff_id.sub contDiff_const)
  have h2 : HasCompactSupport (fun u => g (u - c)) := hgc.comp_homeomorph (Homeomorph.subRight c)
  have hexp : Real.exp (-(c / 2)) * Real.exp (c / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [markovQuad_eq h1 h2, markovQuad_eq hg hgc, weilQuad_comp_sub, poleMomentNeg_comp_sub,
    poleMomentPos_comp_sub]
  calc weilQuad g - 2 * (Real.exp (-(c / 2)) * poleMomentNeg g * (Real.exp (c / 2) *
        poleMomentPos g))
      = weilQuad g - 2 * ((Real.exp (-(c / 2)) * Real.exp (c / 2)) *
          (poleMomentNeg g * poleMomentPos g)) := by ring
    _ = _ := by rw [hexp, one_mul]

/-- A moment of a test supported in `[−R, R]` against a weight bounded by `K` there. -/
theorem abs_integral_mul_le_of_supportedIn {R K : ℝ} {d φ : ℝ → ℝ} (hd : Continuous d)
    (hdc : HasCompactSupport d) (hdR : SupportedIn R d) (hφ : Continuous φ)
    (hφR : ∀ u, |u| ≤ R → |φ u| ≤ K) : |∫ u, d u * φ u| ≤ K * ∫ u, |d u| := by
  have hint : Integrable fun u => |d u| := (hd.integrable_of_hasCompactSupport hdc).abs
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono ((hd.mul hφ).integrable_of_hasCompactSupport hdc.mul_right).abs
    (hint.const_mul _) fun u => ?_
  by_cases hu : R < |u|
  · simp [hdR u hu]
  · push Not at hu
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hφR u hu) (abs_nonneg _)

theorem abs_poleMomentNeg_le {R : ℝ} {d : ℝ → ℝ} (hd : Continuous d) (hdc : HasCompactSupport d)
    (hdR : SupportedIn R d) : |poleMomentNeg d| ≤ Real.exp (R / 2) * ∫ u, |d u| :=
  abs_integral_mul_le_of_supportedIn hd hdc hdR (by fun_prop) fun u hu => by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    linarith [neg_abs_le u]

theorem abs_poleMomentPos_le {R : ℝ} {d : ℝ → ℝ} (hd : Continuous d) (hdc : HasCompactSupport d)
    (hdR : SupportedIn R d) : |poleMomentPos d| ≤ Real.exp (R / 2) * ∫ u, |d u| :=
  abs_integral_mul_le_of_supportedIn hd hdc hdR (by fun_prop) fun u hu => by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    linarith [le_abs_self u]

theorem poleMomentNeg_add {p q : ℝ → ℝ} (hp : Continuous p) (hpc : HasCompactSupport p)
    (hq : Continuous q) (hqc : HasCompactSupport q) :
    poleMomentNeg (fun u => p u + q u) = poleMomentNeg p + poleMomentNeg q := by
  unfold poleMomentNeg
  have h1 : Integrable fun u => p u * Real.exp (-(u / 2)) :=
    (hp.mul (by fun_prop)).integrable_of_hasCompactSupport hpc.mul_right
  have h2 : Integrable fun u => q u * Real.exp (-(u / 2)) :=
    (hq.mul (by fun_prop)).integrable_of_hasCompactSupport hqc.mul_right
  rw [← integral_add h1 h2]
  congr 1
  funext u
  dsimp only
  ring

theorem poleMomentPos_add {p q : ℝ → ℝ} (hp : Continuous p) (hpc : HasCompactSupport p)
    (hq : Continuous q) (hqc : HasCompactSupport q) :
    poleMomentPos (fun u => p u + q u) = poleMomentPos p + poleMomentPos q := by
  unfold poleMomentPos
  have h1 : Integrable fun u => p u * Real.exp (u / 2) :=
    (hp.mul (by fun_prop)).integrable_of_hasCompactSupport hpc.mul_right
  have h2 : Integrable fun u => q u * Real.exp (u / 2) :=
    (hq.mul (by fun_prop)).integrable_of_hasCompactSupport hqc.mul_right
  rw [← integral_add h1 h2]
  congr 1
  funext u
  dsimp only
  ring

theorem poleMomentNeg_const_mul (t : ℝ) (p : ℝ → ℝ) :
    poleMomentNeg (fun u => t * p u) = t * poleMomentNeg p := by
  unfold poleMomentNeg
  rw [← integral_const_mul]
  congr 1
  funext u
  ring

/-- **Continuity of the Markov form**: Weil's motion plus the motion of the pole product. -/
theorem markovQuad_add_le {d : ℝ → ℝ} {R : ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hd : ContDiff ℝ 2 d) (hdc : HasCompactSupport d) (hgR : SupportedIn R g)
    (hdR : SupportedIn R d) :
    markovQuad (fun u => g u + d u) ≤ markovQuad g +
      ((2 * |gammaHardyPhaseRate 0| * (2 * (Real.sqrt (∫ u, g u ^ 2) * Real.sqrt (∫ u, d u ^ 2)) +
          ∫ u, d u ^ 2) +
        (2 * (Real.sqrt (levyEnergy g) * Real.sqrt (levyEnergy d)) + levyEnergy d) +
        2 * primeMass R * (2 * (Real.sqrt (∫ u, g u ^ 2) * Real.sqrt (∫ u, d u ^ 2)) +
          ∫ u, d u ^ 2) +
        4 * Real.cosh (R / 2) * (|coshHalfMoment g| + |sinhHalfMoment g|) * (∫ u, |d u|) +
        4 * Real.cosh (R / 2) ^ 2 * (∫ u, |d u|) ^ 2) +
      2 * (Real.exp (R / 2) * (|poleMomentNeg g| + |poleMomentPos g|) * (∫ u, |d u|) +
        Real.exp R * (∫ u, |d u|) ^ 2)) := by
  have hQ := weilQuad_add_le hg hgc hd hdc hgR hdR
  rw [markovQuad_eq (hg.add hd) (hgc.add hdc), markovQuad_eq hg hgc,
    poleMomentNeg_add hg.continuous hgc hd.continuous hdc,
    poleMomentPos_add hg.continuous hgc hd.continuous hdc]
  have hm1 := abs_poleMomentNeg_le hd.continuous hdc hdR
  have hm2 := abs_poleMomentPos_le hd.continuous hdc hdR
  set a := ∫ u, |d u|
  set E := Real.exp (R / 2)
  have hE2 : Real.exp R = E * E := by rw [← Real.exp_add]; ring_nf
  have ha : 0 ≤ a := integral_nonneg fun u => abs_nonneg _
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hcross : -(poleMomentNeg g * poleMomentPos d + poleMomentNeg d * poleMomentPos g +
      poleMomentNeg d * poleMomentPos d) ≤
      E * (|poleMomentNeg g| + |poleMomentPos g|) * a + Real.exp R * a ^ 2 := by
    have t1 : -(poleMomentNeg g * poleMomentPos d) ≤ |poleMomentNeg g| * (E * a) := by
      have := neg_abs_le (poleMomentNeg g * poleMomentPos d)
      rw [abs_mul] at this
      nlinarith [abs_nonneg (poleMomentNeg g), abs_nonneg (poleMomentPos d)]
    have t2 : -(poleMomentNeg d * poleMomentPos g) ≤ (E * a) * |poleMomentPos g| := by
      have := neg_abs_le (poleMomentNeg d * poleMomentPos g)
      rw [abs_mul] at this
      nlinarith [abs_nonneg (poleMomentNeg d), abs_nonneg (poleMomentPos g)]
    have t3 : -(poleMomentNeg d * poleMomentPos d) ≤ (E * a) * (E * a) := by
      have := neg_abs_le (poleMomentNeg d * poleMomentPos d)
      rw [abs_mul] at this
      have := mul_le_mul hm1 hm2 (abs_nonneg _) (by positivity)
      linarith
    rw [hE2]
    nlinarith
  nlinarith

/-! ### The Markov law fails under overlap growth -/

theorem one_le_blockSize (R : ℝ) : 1 ≤ blockSize R := by
  have h := Nat.le_ceil (1 + Real.exp (2 * R))
  have : (1 : ℝ) ≤ blockSize R := by
    have := Real.exp_pos (2 * R)
    simp only [blockSize] at h ⊢
    linarith
  exact_mod_cast this

/-- A radius, a supremum and a Lipschitz constant of a test. -/
theorem exists_test_constants (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∃ R M L : ℝ, 0 ≤ R ∧ SupportedIn R g ∧ (∀ t, |g t| ≤ M) ∧
      ∀ u v, |g u - g v| ≤ L * |u - v| := by
  obtain ⟨R0, hR0⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  refine ⟨max R0 0, M, C, le_max_right _ _, fun u hu => ?_, fun t => by
    simpa [Real.norm_eq_abs] using hM t, fun u v => by simpa [Real.dist_eq] using hC.dist_le_mul u v⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hR0 hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left R0 0]

variable {φ : ℝ → ℝ} {κ : ℕ → ℝ}

/-- **The Markov law fails under overlap growth**: for every width `1/κ_N` of overlap growth, for
infinitely many `N` some atomic test has negative Markov form — unconditionally. -/
theorem markov_atomicFamilies_negative (hκ : OverlapGrowth κ) (hφ : ContDiff ℝ 2 φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, markovQuad (atomicTest N x (dilate (κ N) φ)) < 0 := by
  obtain ⟨g, hg, hgc, hneg⟩ := exists_markovQuad_neg
  obtain ⟨R, M, L, hR, hgR, hM, hL⟩ := exists_test_constants hg hgc
  set B := blockSize R
  have hB : 1 ≤ B := one_le_blockSize R
  obtain ⟨he, hV⟩ := tendsto_synth hκ hB (∫ s, |φ s|) (∫ s, |deriv φ s|)
    (∫ s, |deriv (deriv φ) s|) M L (R + 3)
  set E := Real.exp ((R + 3) / 2)
  set m := |poleMomentNeg g| + |poleMomentPos g|
  have hmom : Tendsto (fun n : ℕ => 2 * (E * m * (2 * (R + 3) *
      synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L (κ (n * B)) n) + Real.exp (R + 3) *
      (2 * (R + 3) * synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L (κ (n * B)) n) ^ 2))
      atTop (𝓝 0) := by
    have := (((he.const_mul (2 * (R + 3))).const_mul (E * m)).add
      (((he.const_mul (2 * (R + 3))).pow 2).const_mul (Real.exp (R + 3)))).const_mul 2
    simpa using this
  have hErr := (tendsto_weilErr g (R + 3) he hV).add hmom
  rw [add_zero] at hErr
  have h1 := hErr.eventually (gt_mem_nhds (show (0 : ℝ) < -markovQuad g by linarith))
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  have h3 := hNB.eventually (hκ.1.eventually_ge_atTop 1)
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨n, hn1, hk, hn3, hna⟩ :=
    (h1.and (h3.and ((eventually_ge_atTop 1).and (eventually_ge_atTop a)))).exists
  refine ⟨n * B, hna.trans (Nat.le_mul_of_pos_right n hB), ?_⟩
  obtain ⟨x, D, hx, hD2, hDc, hDsupp, hsqD, hN2, hLev, hN1⟩ :=
    exists_synthesis hφ hφ1 hφint hg hR hgR hM hL hn3 hk
  refine ⟨x, ?_⟩
  have hgR3 : SupportedIn (R + 3) g := fun u hu => hgR u (by linarith)
  rw [hx, markovQuad_comp_sub (hg.add hD2) (hgc.add hDc)]
  have hb := markovQuad_add_le hg hgc hD2 hDc hgR3 hDsupp
  have hmono := weilErr_mono (F := g) hsqD hN2 hLev (integral_nonneg fun u => abs_nonneg _) hN1
  have hD1 : 0 ≤ ∫ u, |D u| := integral_nonneg fun u => abs_nonneg _
  have hm0 : 0 ≤ m := by positivity
  have hpm : 2 * (E * m * (∫ u, |D u|) + Real.exp (R + 3) * (∫ u, |D u|) ^ 2) ≤
      2 * (E * m * (2 * (R + 3) * synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L (κ (n * B)) n) +
        Real.exp (R + 3) * (2 * (R + 3) *
          synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) M L (κ (n * B)) n) ^ 2) := by
    have hE : 0 ≤ E := (Real.exp_pos _).le
    gcongr
  linarith

/-- **The threshold of the Markov law is bracketed**: `M ≥ 0` on every atomic test of width
`≤ c₀ δ_N`, for every `N` (and for every twist, SH4′); and for every width `1/κ_N` of overlap
growth, `M < 0` on some atomic test for infinitely many `N`. The second statement concerns `ζ`
itself: the threshold is not arithmetic. -/
theorem markovThreshold_bracket (hκ : OverlapGrowth κ) (hφ : ContDiff ℝ 2 φ)
    (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) :
    (∀ {b : ℝ → ℝ} {w : ℝ} {N : ℕ}, ContDiff ℝ 2 b → HasCompactSupport b →
      (∀ u, u ∉ Set.Icc 0 w → b u = 0) → 1 ≤ N → 0 < w → w ≤ spacingWidthRatio * atomSpacing N →
        ∀ x : ℕ → ℝ, 0 ≤ markovQuad (atomicTest N x b)) ∧
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, markovQuad (atomicTest N x (dilate (κ N) φ)) < 0 :=
  ⟨fun hb hbc hbs hN hw0 hw x => markovEnergy_atomicTest_nonneg_spacing hb hbc hbs hN hw0 hw x,
    markov_atomicFamilies_negative hκ hφ hφ1 hφint⟩

/-! ### Perturbations of Weil's form -/

/-- The motion bound of Weil's form at `F` for a perturbation with `‖d‖₂ = s`, `‖d‖₂² = q`,
`levyEnergy d = l`, `‖d‖₁ = a`, on the window `[−R, R]`. -/
def perturbErr (F : ℝ → ℝ) (R s q l a : ℝ) : ℝ :=
  2 * |gammaHardyPhaseRate 0| * (2 * (Real.sqrt (∫ u, F u ^ 2) * s) + q) +
    (2 * (Real.sqrt (levyEnergy F) * Real.sqrt l) + l) +
    2 * primeMass R * (2 * (Real.sqrt (∫ u, F u ^ 2) * s) + q) +
    4 * Real.cosh (R / 2) * (|coshHalfMoment F| + |sinhHalfMoment F|) * a +
    4 * Real.cosh (R / 2) ^ 2 * a ^ 2

theorem perturbErr_mono (F : ℝ → ℝ) {R s q l a s' q' l' a' : ℝ} (hs : s ≤ s') (hq : q ≤ q')
    (hl : l ≤ l') (ha0 : 0 ≤ a) (ha : a ≤ a') :
    perturbErr F R s q l a ≤ perturbErr F R s' q' l' a' := by
  unfold perturbErr
  have hF2 : 0 ≤ Real.sqrt (∫ u, F u ^ 2) := Real.sqrt_nonneg _
  have hLF : 0 ≤ Real.sqrt (levyEnergy F) := Real.sqrt_nonneg _
  have hP : 0 ≤ primeMass R := primeMass_nonneg _
  have hch : 0 ≤ Real.cosh (R / 2) := (Real.cosh_pos _).le
  have hmom : 0 ≤ |coshHalfMoment F| + |sinhHalfMoment F| := by positivity
  have hsl : Real.sqrt l ≤ Real.sqrt l' := Real.sqrt_le_sqrt hl
  have ha2 : a ^ 2 ≤ a' ^ 2 := pow_le_pow_left₀ ha0 ha 2
  gcongr

theorem tendsto_perturbErr (F : ℝ → ℝ) (R : ℝ) {s q l a : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0))
    (hq : Tendsto q atTop (𝓝 0)) (hl : Tendsto l atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => perturbErr F R (s n) (q n) (l n) (a n)) atTop (𝓝 0) := by
  unfold perturbErr
  have hsl : Tendsto (fun n => Real.sqrt (l n)) atTop (𝓝 0) := by simpa using hl.sqrt
  have := (((((((hs.const_mul (Real.sqrt (∫ u, F u ^ 2))).const_mul 2).add hq).const_mul
    (2 * |gammaHardyPhaseRate 0|)).add
    (((hsl.const_mul (Real.sqrt (levyEnergy F))).const_mul 2).add hl)).add
    ((((hs.const_mul (Real.sqrt (∫ u, F u ^ 2))).const_mul 2).add hq).const_mul
      (2 * primeMass R))).add
    (ha.const_mul (4 * Real.cosh (R / 2) * (|coshHalfMoment F| + |sinhHalfMoment F|)))).add
    ((ha.pow 2).const_mul (4 * Real.cosh (R / 2) ^ 2))
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at this
  exact this

theorem levyEnergy_const_mul (t : ℝ) (h : ℝ → ℝ) :
    levyEnergy (fun u => t * h u) = t ^ 2 * levyEnergy h := by
  unfold levyEnergy
  have hin : ∀ y : ℝ, (∫ u, (t * h u - t * h (u + y)) ^ 2) =
      t ^ 2 * ∫ u, (h u - h (u + y)) ^ 2 := fun y => by
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  simp_rw [hin]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem levyEnergy_add_le_two {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b) :
    levyEnergy (fun u => a u + b u) ≤ 2 * levyEnergy a + 2 * levyEnergy b := by
  have h := levyEnergy_add_le ha hac hb hbc
  have h1 := Real.sq_sqrt (levyEnergy_nonneg' a)
  have h2 := Real.sq_sqrt (levyEnergy_nonneg' b)
  nlinarith [sq_nonneg (Real.sqrt (levyEnergy a) - Real.sqrt (levyEnergy b))]

/-- `∫ (a − t(b + c))² ≤ 3(∫a² + T²∫b² + T²∫c²)` for `|t| ≤ T`. -/
theorem integral_sq_comb_le {a b c : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (hc : Continuous c) (hcc : HasCompactSupport c)
    {t T : ℝ} (ht : |t| ≤ T) :
    ∫ u, (a u + -t * (b u + c u)) ^ 2 ≤
      3 * ((∫ u, a u ^ 2) + T ^ 2 * (∫ u, b u ^ 2) + T ^ 2 * ∫ u, c u ^ 2) := by
  have hi : ∀ p : ℝ → ℝ, Continuous p → HasCompactSupport p → Integrable fun u => p u ^ 2 :=
    fun p hp hpc => integrable_sq_of_continuous hp hpc
  have ht2 : t ^ 2 ≤ T ^ 2 := by
    have := sq_abs t
    nlinarith [abs_nonneg t]
  have hcomb : Integrable fun u => (a u + -t * (b u + c u)) ^ 2 :=
    hi _ (ha.add (continuous_const.mul (hb.add hc))) (hac.add ((hbc.add hcc).mul_left))
  calc ∫ u, (a u + -t * (b u + c u)) ^ 2
      ≤ ∫ u, ((3 * T ^ 2) * b u ^ 2 + (3 * T ^ 2) * c u ^ 2 + 3 * a u ^ 2) := by
        refine integral_mono hcomb (((hi b hb hbc).const_mul _).add ((hi c hc hcc).const_mul _) |>.add
          ((hi a ha hac).const_mul _)) fun u => ?_
        have key : (a u + -t * (b u + c u)) ^ 2 ≤ 3 * (a u ^ 2 + t ^ 2 * b u ^ 2 + t ^ 2 * c u ^ 2) := by
          nlinarith [sq_nonneg (a u + t * b u), sq_nonneg (a u + t * c u),
            sq_nonneg (t * b u - t * c u)]
        have h1 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg (b u))
        have h2 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg (c u))
        linarith
    _ = 3 * ((∫ u, a u ^ 2) + T ^ 2 * (∫ u, b u ^ 2) + T ^ 2 * ∫ u, c u ^ 2) := by
        rw [integral_lin3 (hi b hb hbc) (hi c hc hcc) ((hi a ha hac).const_mul 3),
          integral_const_mul]
        ring

/-- `∫ |a − t(b + c)| ≤ ∫|a| + T(∫|b| + ∫|c|)` for `|t| ≤ T`. -/
theorem integral_abs_comb_le {a b c : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (hc : Continuous c) (hcc : HasCompactSupport c)
    {t T : ℝ} (ht : |t| ≤ T) :
    ∫ u, |a u + -t * (b u + c u)| ≤ (∫ u, |a u|) + T * ((∫ u, |b u|) + ∫ u, |c u|) := by
  have hi : ∀ p : ℝ → ℝ, Continuous p → HasCompactSupport p → Integrable fun u => |p u| :=
    fun p hp hpc => (hp.integrable_of_hasCompactSupport hpc).abs
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  calc ∫ u, |a u + -t * (b u + c u)|
      ≤ ∫ u, (T * |b u| + T * |c u| + |a u|) := by
        refine integral_mono (hi _ (ha.add (continuous_const.mul (hb.add hc)))
          (hac.add ((hbc.add hcc).mul_left))) (((hi b hb hbc).const_mul _).add
          ((hi c hc hcc).const_mul _) |>.add (hi a ha hac)) fun u => ?_
        calc |a u + -t * (b u + c u)| ≤ |a u| + |t| * (|b u| + |c u|) := by
              refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
              rw [abs_mul, abs_neg]
              exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
          _ ≤ |a u| + T * (|b u| + |c u|) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right ht (by positivity))
          _ = T * |b u| + T * |c u| + |a u| := by ring
    _ = (∫ u, |a u|) + T * ((∫ u, |b u|) + ∫ u, |c u|) := by
        rw [integral_lin3 (hi b hb hbc) (hi c hc hcc) (hi a ha hac)]
        ring

theorem atomicTest_sub_const_mul (N : ℕ) (a b : ℕ → ℝ) (t : ℝ) (ψ : ℝ → ℝ) :
    atomicTest N (fun n => a n - t * b n) ψ =
      fun u => atomicTest N a ψ u - t * atomicTest N b ψ u := by
  funext u
  simp only [atomicTest, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-! ### One negative square iff RH -/

/-- A smooth bump `h ≥ 0` supported in `[−2, 2]` with `m₋(h) > 0`. -/
theorem exists_bump_poleMomentNeg_pos :
    ∃ h : ℝ → ℝ, ContDiff ℝ 2 h ∧ HasCompactSupport h ∧ 0 < poleMomentNeg h := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨bump, bump.contDiff, bump.hasCompactSupport, ?_⟩
  unfold poleMomentNeg
  have hint : Integrable fun u => bump u * Real.exp (-(u / 2)) :=
    (bump.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      bump.hasCompactSupport.mul_right
  rw [integral_pos_iff_support_of_nonneg (fun u => mul_nonneg bump.nonneg (Real.exp_pos _).le) hint]
  have hs : (Function.support fun u => bump u * Real.exp (-(u / 2))) = Metric.ball 0 2 := by
    ext u
    simp only [Function.mem_support, ne_eq, mul_eq_zero, Real.exp_ne_zero, or_false]
    rw [← bump.support_eq, Function.mem_support]
  rw [hs]
  exact Metric.measure_ball_pos volume 0 two_pos

/-- `levy(a − t(b + c)) ≤ 2 levy a + 2T²(2 levy b + 2 levy c)` for `|t| ≤ T`. -/
theorem levyEnergy_comb_le {a b c : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b) (hc : ContDiff ℝ 2 c)
    (hcc : HasCompactSupport c) {t T : ℝ} (ht : |t| ≤ T) :
    levyEnergy (fun u => a u + -t * (b u + c u)) ≤
      2 * levyEnergy a + 2 * (T ^ 2 * (2 * levyEnergy b + 2 * levyEnergy c)) := by
  have hadd := levyEnergy_add_le_two (b := fun u => -t * (b u + c u)) ha hac
    (contDiff_const.mul (hb.add hc)) ((hbc.add hcc).mul_left)
  have hct : levyEnergy (fun u => -t * (b u + c u)) = (-t) ^ 2 * levyEnergy (fun u => b u + c u) :=
    levyEnergy_const_mul (-t) (fun u => b u + c u)
  have hbc2 := levyEnergy_add_le_two hb hbc hc hcc
  have ht2 : (-t) ^ 2 ≤ T ^ 2 := by
    rw [neg_sq, ← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hL0 : 0 ≤ levyEnergy (fun u => b u + c u) := levyEnergy_nonneg' _
  have := mul_le_mul ht2 hbc2 hL0 (sq_nonneg T)
  linarith

/-- The coefficient bound `T = 2 E (2(R+3) e_u)/m₋(h)` of the correction. -/
def corrT (E R eu mh : ℝ) : ℝ := 2 * (E * (2 * (R + 3) * eu)) / mh

/-- The `L²` bound of the corrected perturbation. -/
def corrQ (R eu eh T h2 : ℝ) : ℝ :=
  3 * (2 * (R + 3) * eu ^ 2 + T ^ 2 * h2 + T ^ 2 * (2 * (R + 3) * eh ^ 2))

/-- The Lévy bound of the corrected perturbation. -/
def corrL (Vu Vh T lh : ℝ) : ℝ := 2 * Vu + 2 * (T ^ 2 * (2 * lh + 2 * Vh))

/-- The `L¹` bound of the corrected perturbation. -/
def corrA (R eu eh T h1 : ℝ) : ℝ := 2 * (R + 3) * eu + T * (h1 + 2 * (R + 3) * eh)

section Corrected

variable {u h : ℝ → ℝ} {R Mu Lu Mh Lh k : ℝ} {n₀ : ℕ}

/-- **The corrected synthesis**: atoms of level `n₀ B` synthesize a translate of `u + D'` lying in
the pole hyperplane, where `u` is pole free and `D' = D_u − t (h + D_h)` corrects the synthesis
error of `u` by a multiple of the synthesis of a bump `h` with `m₋(h) > 0`. Its Markov form is at
most `Q(u)` plus the motion bound of `D'`. -/
theorem exists_corrected_synthesis (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (hu0 : poleMomentNeg u = 0)
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) (hh0 : 0 < poleMomentNeg h) (hR : 0 ≤ R)
    (huR : SupportedIn R u) (hhR : SupportedIn R h) (hMu : ∀ t, |u t| ≤ Mu)
    (hLu : ∀ v w, |u v - u w| ≤ Lu * |v - w|) (hMh : ∀ t, |h t| ≤ Mh)
    (hLh : ∀ v w, |h v - h w| ≤ Lh * |v - w|) (hn₀ : 1 ≤ n₀) (hk : 1 ≤ k)
    (hsmall : Real.exp ((R + 3) / 2) * (2 * (R + 3) *
      synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mh Lh k n₀) < poleMomentNeg h / 2) :
    ∃ x : ℕ → ℝ, poleMomentNeg (atomicTest (n₀ * blockSize R) x (dilate k φ)) = 0 ∧
      markovQuad (atomicTest (n₀ * blockSize R) x (dilate k φ)) ≤ weilQuad u +
        perturbErr u (R + 3)
          (Real.sqrt (corrQ R (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu k n₀)
            (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mh Lh k n₀)
            (corrT (Real.exp ((R + 3) / 2)) R (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu k n₀)
              (poleMomentNeg h)) (∫ v, h v ^ 2)))
          (corrQ R (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu k n₀)
            (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mh Lh k n₀)
            (corrT (Real.exp ((R + 3) / 2)) R (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu k n₀)
              (poleMomentNeg h)) (∫ v, h v ^ 2))
          (corrL (synthLevy (R + 3) (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu k n₀)
              (synthLip (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) Mu Lu k n₀) k)
            (synthLevy (R + 3) (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mh Lh k n₀)
              (synthLip (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) Mh Lh k n₀) k)
            (corrT (Real.exp ((R + 3) / 2)) R (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu k n₀)
              (poleMomentNeg h)) (levyEnergy h))
          (corrA R (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu k n₀)
            (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mh Lh k n₀)
            (corrT (Real.exp ((R + 3) / 2)) R (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu k n₀)
              (poleMomentNeg h)) (∫ v, |h v|)) := by
  obtain ⟨xu, Du, hxu, hDu2, hDuc, hDuR, -, hN2u, hLevu, hN1u⟩ :=
    exists_synthesis hφ hφ1 hφint hu hR huR hMu hLu hn₀ hk
  obtain ⟨xh, Dh, hxh, hDh2, hDhc, hDhR, -, hN2h, hLevh, hN1h⟩ :=
    exists_synthesis hφ hφ1 hφint hh hR hhR hMh hLh hn₀ hk
  set eu := synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu k n₀
  set eh := synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mh Lh k n₀
  set E := Real.exp ((R + 3) / 2)
  set mh := poleMomentNeg h
  set T := corrT E R eu mh
  have hE0 : 0 < E := Real.exp_pos _
  have hhR3 : SupportedIn (R + 3) h := fun v hv => hhR v (by linarith)
  have huR3 : SupportedIn (R + 3) u := fun v hv => huR v (by linarith)
  -- the denominator `m₋(h) + m₋(D_h)` is at least `m₋(h)/2`
  have hmDh := abs_poleMomentNeg_le hDh2.continuous hDhc hDhR
  have hmDu := abs_poleMomentNeg_le hDu2.continuous hDuc hDuR
  have hden : mh / 2 ≤ mh + poleMomentNeg Dh := by
    have : E * (∫ v, |Dh v|) ≤ E * (2 * (R + 3) * eh) := mul_le_mul_of_nonneg_left hN1h hE0.le
    have := neg_abs_le (poleMomentNeg Dh)
    linarith
  have hden0 : 0 < mh + poleMomentNeg Dh := by linarith
  set t := poleMomentNeg Du / (mh + poleMomentNeg Dh)
  have heu0 : 0 ≤ eu := by
    have h0 := (integral_nonneg fun v => abs_nonneg (Du v)).trans hN1u
    nlinarith
  have hT0 : 0 ≤ T := by
    simp only [T, corrT]
    positivity
  have htT : |t| ≤ T := by
    rw [abs_div, abs_of_pos hden0, div_le_iff₀ hden0]
    have hTn : T * (mh / 2) = E * (2 * (R + 3) * eu) := by
      simp only [T, corrT]
      field_simp
    calc |poleMomentNeg Du| ≤ E * (∫ v, |Du v|) := hmDu
      _ ≤ E * (2 * (R + 3) * eu) := mul_le_mul_of_nonneg_left hN1u hE0.le
      _ = T * (mh / 2) := hTn.symm
      _ ≤ T * (mh + poleMomentNeg Dh) := mul_le_mul_of_nonneg_left hden hT0
  -- the corrected perturbation
  set D' : ℝ → ℝ := fun v => Du v + -t * (h v + Dh v)
  have hD'2 : ContDiff ℝ 2 D' := hDu2.add (contDiff_const.mul (hh.add hDh2))
  have hD'c : HasCompactSupport D' := hDuc.add ((hhc.add hDhc).mul_left)
  have hD'R : SupportedIn (R + 3) D' := fun v hv => by
    simp only [D', hDuR v hv, hhR3 v hv, hDhR v hv, add_zero, mul_zero]
  have hx : atomicTest (n₀ * blockSize R) (fun j => xu j - t * xh j) (dilate k φ) =
      fun v => u (v - (Real.log n₀ + R)) + D' (v - (Real.log n₀ + R)) := by
    rw [atomicTest_sub_const_mul, hxu, hxh]
    funext v
    simp only [D']
    ring
  have hc1 : Continuous fun v => -t * (h v + Dh v) :=
    continuous_const.mul (hh.continuous.add hDh2.continuous)
  have hc1c : HasCompactSupport fun v => -t * (h v + Dh v) := (hhc.add hDhc).mul_left
  have hmD' : poleMomentNeg (fun v => u v + D' v) = 0 := by
    rw [poleMomentNeg_add hu.continuous huc hD'2.continuous hD'c, hu0, zero_add]
    simp only [D']
    rw [poleMomentNeg_add (q := fun v => -t * (h v + Dh v)) hDu2.continuous hDuc hc1 hc1c,
      poleMomentNeg_const_mul, poleMomentNeg_add hh.continuous hhc hDh2.continuous hDhc]
    simp only [t]
    field_simp
    ring
  refine ⟨fun j => xu j - t * xh j, ?_, ?_⟩
  · rw [hx, poleMomentNeg_comp_sub (fun v => u v + D' v), hmD', mul_zero]
  rw [hx, markovQuad_comp_sub (hu.add hD'2) (huc.add hD'c), markovQuad_eq (hu.add hD'2)
    (huc.add hD'c), hmD', zero_mul, mul_zero, sub_zero]
  have hb : weilQuad (fun v => u v + D' v) ≤
      weilQuad u + perturbErr u (R + 3) (Real.sqrt (∫ v, D' v ^ 2)) (∫ v, D' v ^ 2)
        (levyEnergy D') (∫ v, |D' v|) := weilQuad_add_le hu huc hD'2 hD'c huR3 hD'R
  have hq : ∫ v, D' v ^ 2 ≤ corrQ R eu eh T (∫ v, h v ^ 2) := by
    refine (integral_sq_comb_le hDu2.continuous hDuc hh.continuous hhc hDh2.continuous hDhc
      htT).trans ?_
    simp only [corrQ]
    have hT2 : 0 ≤ T ^ 2 := sq_nonneg _
    gcongr
  have hl : levyEnergy D' ≤ corrL (synthLevy (R + 3) eu
      (synthLip (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) Mu Lu k n₀) k)
      (synthLevy (R + 3) eh (synthLip (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) Mh Lh k n₀) k)
      T (levyEnergy h) := by
    refine (levyEnergy_comb_le hDu2 hDuc hh hhc hDh2 hDhc htT).trans ?_
    simp only [corrL]
    have hT2 : 0 ≤ T ^ 2 := sq_nonneg _
    gcongr
  have ha : ∫ v, |D' v| ≤ corrA R eu eh T (∫ v, |h v|) := by
    refine (integral_abs_comb_le hDu2.continuous hDuc hh.continuous hhc hDh2.continuous hDhc
      htT).trans ?_
    simp only [corrA]
    gcongr
  exact hb.trans (add_le_add le_rfl (perturbErr_mono u (Real.sqrt_le_sqrt hq) hq hl
    (integral_nonneg fun v => abs_nonneg _) ha))

end Corrected

/-- **One negative square iff RH**: for every width `1/κ_N` of overlap growth, RH holds iff for all
large `N` the Markov form is nonnegative on every atomic test of width `1/κ_N` in the pole
hyperplane `m₋ = 0`. -/
theorem riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg (hκ : OverlapGrowth κ)
    (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      poleMomentNeg (atomicTest N x (dilate (κ N) φ)) = 0 →
        0 ≤ markovQuad (atomicTest N x (dilate (κ N) φ)) := by
  constructor
  · intro hRH
    filter_upwards [hκ.1.eventually_gt_atTop 0] with N hk x h0
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ hφ1 hk N x
    exact riemannHypothesis_iff_forall_exp_neg_half_moment_zero_markovEnergy_nonneg.mp hRH _ h2 hc
      h0
  intro H
  by_contra hRH
  -- a pole-free test with `Q(u) < 0`
  obtain ⟨u, hu, huc, -, hpole, hneg⟩ := exists_even_poleFree_negative_of_not_riemannHypothesis hRH
  have hu0 : poleMomentNeg u = 0 := by
    rw [paperFT_ofReal_I_half] at hpole
    exact_mod_cast hpole
  have hQu : weilQuad u < 0 := by
    rw [zeta_W_eq_weilFullFunctional (f := fun x => (u x : ℂ)) (Complex.ofRealCLM.contDiff.comp hu)
      (huc.comp_left Complex.ofReal_zero)] at hneg
    exact hneg
  -- an auxiliary bump, and common constants
  obtain ⟨h, hh, hhc, hh0⟩ := exists_bump_poleMomentNeg_pos
  obtain ⟨Ru, Mu, Lu, hRu, huR, hMu, hLu⟩ := exists_test_constants hu huc
  obtain ⟨Rh, Mh, Lh, hRh, hhR, hMh, hLh⟩ := exists_test_constants hh hhc
  have hR : 0 ≤ max Ru Rh := hRu.trans (le_max_left _ _)
  have huR' : SupportedIn (max Ru Rh) u := fun v hv => huR v (lt_of_le_of_lt (le_max_left _ _) hv)
  have hhR' : SupportedIn (max Ru Rh) h := fun v hv => hhR v (lt_of_le_of_lt (le_max_right _ _) hv)
  set R := max Ru Rh
  set B := blockSize R
  have hB : 1 ≤ B := one_le_blockSize R
  obtain ⟨heu, hVu⟩ := tendsto_synth hκ hB (∫ s, |φ s|) (∫ s, |deriv φ s|)
    (∫ s, |deriv (deriv φ) s|) Mu Lu (R + 3)
  obtain ⟨heh, hVh⟩ := tendsto_synth hκ hB (∫ s, |φ s|) (∫ s, |deriv φ s|)
    (∫ s, |deriv (deriv φ) s|) Mh Lh (R + 3)
  set E := Real.exp ((R + 3) / 2)
  set mh := poleMomentNeg h
  have hT : Tendsto (fun n : ℕ => corrT E R
      (synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu (κ (n * B)) n) mh) atTop (𝓝 0) := by
    have := ((heu.const_mul (2 * (R + 3))).const_mul E).const_mul 2 |>.div_const mh
    simpa [corrT] using this
  set eu : ℕ → ℝ := fun n => synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mu Lu (κ (n * B)) n
  set eh : ℕ → ℝ := fun n => synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mh Lh (κ (n * B)) n
  set T : ℕ → ℝ := fun n => corrT E R (eu n) mh
  have hQ : Tendsto (fun n => corrQ R (eu n) (eh n) (T n) (∫ v, h v ^ 2)) atTop (𝓝 0) := by
    have := ((((heu.pow 2).const_mul (2 * (R + 3))).add ((hT.pow 2).mul_const
      (∫ v, h v ^ 2))).add ((hT.pow 2).mul ((heh.pow 2).const_mul (2 * (R + 3))))).const_mul 3
    simpa [corrQ] using this
  have hLv : Tendsto (fun n => corrL
      (synthLevy (R + 3) (eu n) (synthLip (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) Mu Lu
        (κ (n * B)) n) (κ (n * B)))
      (synthLevy (R + 3) (eh n) (synthLip (∫ s, |deriv φ s|) (∫ s, |deriv (deriv φ) s|) Mh Lh
        (κ (n * B)) n) (κ (n * B))) (T n) (levyEnergy h)) atTop (𝓝 0) := by
    have := (hVu.const_mul 2).add (((hT.pow 2).mul ((hVh.const_mul 2).const_add
      (2 * levyEnergy h))).const_mul 2)
    simpa [corrL] using this
  have hA : Tendsto (fun n => corrA R (eu n) (eh n) (T n) (∫ v, |h v|)) atTop (𝓝 0) := by
    have := (heu.const_mul (2 * (R + 3))).add (hT.mul ((heh.const_mul (2 * (R + 3))).const_add
      (∫ v, |h v|)))
    simpa [corrA] using this
  have hErr := tendsto_perturbErr u (R + 3) (by simpa using hQ.sqrt) hQ hLv hA
  -- choose a level
  have h1 := hErr.eventually (gt_mem_nhds (show (0 : ℝ) < -weilQuad u by linarith))
  have hc0 : 0 < mh / 2 / (E * (2 * (R + 3))) := by
    have : 0 < E := Real.exp_pos _
    positivity
  have h2 := heh.eventually (gt_mem_nhds hc0)
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  obtain ⟨n, hn1, hn2, hk, hH, hn⟩ := (h1.and (h2.and ((hNB.eventually
    (hκ.1.eventually_ge_atTop 1)).and ((hNB.eventually H).and (eventually_ge_atTop 1))))).exists
  have hsmall : E * (2 * (R + 3) *
      synthErr (∫ s, |φ s|) (∫ s, |deriv φ s|) Mh Lh (κ (n * B)) n) < mh / 2 := by
    have hpos : 0 < E * (2 * (R + 3)) := by
      have : 0 < E := Real.exp_pos _
      positivity
    have := (lt_div_iff₀ hpos).mp hn2
    linarith
  obtain ⟨x, hx0, hxM⟩ := exists_corrected_synthesis hφ hφ1 hφint hu huc hu0 hh hhc hh0 hR huR' hhR'
    hMu hLu hMh hLh hn hk hsmall
  have := hH x hx0
  linarith

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
