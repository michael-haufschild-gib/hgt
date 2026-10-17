import GaloisForLFunctions.BiScaleUncertainty.CausalCorrelationPacketRepresentation
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel

/-!
# The spectral form of the Laplace energy on the critical line

The Fourier transform of the causal response `R_N = K ⋆ ν_N` factors through the pole:
with `s(ξ) = ½ + 2πiξ`,

`𝓕 R_N (ξ) = ν̂_N(ξ) / s(ξ)`,  `ν̂_N(ξ) = ∫ e^{−2πiξt} dν_N(t)`.

Plancherel therefore turns the Laplace Gram energy into a weighted critical-line mean square,

`laplaceEnergy N = ∫ ‖ν̂_N(ξ)‖² / (¼ + 4π²ξ²) dξ`,

and `ν̂_N` is the pole-subtracted truncated logarithmic derivative of zeta on the critical line,

`ν̂_N(ξ) = Σ_{n ≤ N+2} Λ(n) n^{−s(ξ)} − (e^{(1−s(ξ))L} − 1)/(1 − s(ξ)) − (1 − e^{−s(ξ)L})/s(ξ)`.

Thus the square-root barrier for the Chebyshev function is, inside the field, the statement that the
truncated Dirichlet series `Σ Λ(n) n^{−s}` with its two pole terms removed has weighted mean square
`O(log N)` on the critical line against the weight `1/|s|²`: the frequency side of the same
bi-scale energy whose position side is `∫_0^L Ẽ²`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real FourierTransform

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## The complex pairing -/

/-- The complex pairing `∫ h dν_N` of the signed prime–polar measure. -/
def pairingC (N : ℕ) (h : ℝ → ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 (N + 2), (primeWeight n : ℂ) * h (Real.log n)) -
    ∫ x in Icc 0 (cutoff N), (polarDensity x : ℂ) * h x

theorem pairingC_ofReal (N : ℕ) (h : ℝ → ℝ) :
    pairingC N (fun s => (h s : ℂ)) = (pairing N h : ℂ) := by
  unfold pairingC pairing
  rw [Complex.ofReal_sub, Complex.ofReal_sum, ← integral_complex_ofReal]
  congr 1
  · exact Finset.sum_congr rfl fun n _ => by push_cast; ring
  · exact integral_congr_ae (Eventually.of_forall fun x => by push_cast; ring)

theorem pairingC_const_mul (N : ℕ) (c : ℂ) (h : ℝ → ℂ) :
    pairingC N (fun s => c * h s) = c * pairingC N h := by
  unfold pairingC
  rw [mul_sub, Finset.mul_sum, ← integral_const_mul c (fun x => (polarDensity x : ℂ) * h x)]
  congr 1
  · exact Finset.sum_congr rfl fun n _ => by ring
  · exact integral_congr_ae (Eventually.of_forall fun s => by ring)

theorem pairingC_mul_const (N : ℕ) (c : ℂ) (h : ℝ → ℂ) :
    pairingC N (fun s => h s * c) = pairingC N h * c := by
  have h1 : (fun s => h s * c) = fun s => c * h s := funext fun s => mul_comm _ _
  calc pairingC N (fun s => h s * c) = pairingC N (fun s => c * h s) := congrArg (pairingC N) h1
    _ = c * pairingC N h := pairingC_const_mul N c h
    _ = pairingC N h * c := mul_comm _ _

/-- The complex pairing only reads its argument on the window `[0, L]`. -/
theorem pairingC_congr_window (N : ℕ) {h h' : ℝ → ℂ}
    (hh : ∀ s ∈ Icc (0 : ℝ) (cutoff N), h s = h' s) : pairingC N h = pairingC N h' := by
  unfold pairingC
  congr 1
  · exact Finset.sum_congr rfl fun n hn => by
      rw [hh _ ⟨(node_bounds N n hn).1, (node_bounds N n hn).2⟩]
  · exact setIntegral_congr_fun measurableSet_Icc fun s hs => by rw [hh s hs]

/-- Uniform bound: `‖pairingC N h‖ ≤ mass N · sup ‖h‖`. -/
theorem norm_pairingC_le_mass_mul (N : ℕ) (h : ℝ → ℂ) {B : ℝ} (hb : ∀ s, ‖h s‖ ≤ B) :
    ‖pairingC N h‖ ≤ mass N * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hb 0)
  unfold pairingC mass
  rw [add_mul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (primeWeight_nonneg n)]
    exact mul_le_mul_of_nonneg_left (hb _) (primeWeight_nonneg n)
  · refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_mul_const]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
      ((continuous_polarDensity.integrableOn_Icc).mul_const B) (Eventually.of_forall fun x => ?_)
    show ‖(polarDensity x : ℂ) * h x‖ ≤ polarDensity x * B
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (polarDensity_nonneg x)]
    exact mul_le_mul_of_nonneg_left (hb x) (polarDensity_nonneg x)

/-- **Exchange of the complex pairing with a dominated line integral.** -/
theorem integral_pairingC_of_dominated (N : ℕ) (F : ℝ → ℝ → ℂ)
    (hF : Measurable (Function.uncurry F)) {w : ℝ → ℝ} (hw : Integrable w) {C : ℝ}
    (hb : ∀ t s, ‖F t s‖ ≤ |w t| * C) :
    (∫ t, pairingC N fun s => F t s) = pairingC N fun s => ∫ t, F t s := by
  set Cp : ℝ := 2 * Real.cosh (cutoff N / 2) with hCp
  have hCp0 : 0 ≤ Cp := by positivity
  have hatom : ∀ n : ℕ, Integrable fun t => (primeWeight n : ℂ) * F t (Real.log n) := by
    intro n
    refine ((hw.norm.mul_const C).const_mul (primeWeight n)).mono'
      ((hF.comp (measurable_id.prodMk measurable_const)).const_mul _).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (primeWeight_nonneg n),
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb t _) (primeWeight_nonneg n)
  set pw : ℝ → ℝ := (Icc 0 (cutoff N)).indicator polarDensity with hpw
  have hpwb : ∀ s, |pw s| ≤ Cp := by
    intro s
    by_cases hs : s ∈ Icc 0 (cutoff N)
    · rw [hpw, Set.indicator_of_mem hs, abs_of_nonneg (polarDensity_nonneg s)]
      exact polarDensity_le_window hs
    · rw [hpw, Set.indicator_of_notMem hs, abs_zero]; exact hCp0
  have hpwm : Measurable pw := continuous_polarDensity.measurable.indicator measurableSet_Icc
  have hprod : Integrable (Function.uncurry fun t s => (pw s : ℂ) * F t s)
      (volume.prod (volume.restrict (Icc 0 (cutoff N)))) := by
    refine Integrable.mono' ((hw.norm.mul_const (C * Cp)).mul_prod
      (integrable_const (1 : ℝ) (μ := volume.restrict (Icc 0 (cutoff N))))) ?_
      (Eventually.of_forall fun p => ?_)
    · exact ((Complex.measurable_ofReal.comp (hpwm.comp measurable_snd)).mul hF).aestronglyMeasurable
    · show ‖(pw p.2 : ℂ) * F p.1 p.2‖ ≤ ‖w p.1‖ * (C * Cp) * 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, mul_one]
      calc |pw p.2| * ‖F p.1 p.2‖ ≤ Cp * (|w p.1| * C) :=
            mul_le_mul (hpwb _) (hb _ _) (norm_nonneg _) hCp0
        _ = |w p.1| * (C * Cp) := by ring
  have hpolar_eq : ∀ t, (∫ s in Icc 0 (cutoff N), (polarDensity s : ℂ) * F t s) =
      ∫ s in Icc 0 (cutoff N), (pw s : ℂ) * F t s :=
    fun t => setIntegral_congr_fun measurableSet_Icc fun s hs => by
      rw [hpw, Set.indicator_of_mem hs]
  have hpolar_int : Integrable fun t => ∫ s in Icc 0 (cutoff N), (pw s : ℂ) * F t s :=
    hprod.integral_prod_left
  have hswap : (∫ t, ∫ s in Icc 0 (cutoff N), (pw s : ℂ) * F t s) =
      ∫ s in Icc 0 (cutoff N), ∫ t, (pw s : ℂ) * F t s :=
    integral_integral_swap hprod
  have hsum_int : Integrable fun t =>
      ∑ n ∈ Finset.Icc 1 (N + 2), (primeWeight n : ℂ) * F t (Real.log n) :=
    integrable_finsetSum _ fun n _ => hatom n
  calc (∫ t, pairingC N fun s => F t s)
      = ∫ t, ((∑ n ∈ Finset.Icc 1 (N + 2), (primeWeight n : ℂ) * F t (Real.log n)) -
          ∫ s in Icc 0 (cutoff N), (pw s : ℂ) * F t s) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show pairingC N (fun s => F t s) = _
        unfold pairingC
        simp only
        rw [hpolar_eq t]
    _ = (∑ n ∈ Finset.Icc 1 (N + 2), (primeWeight n : ℂ) * ∫ t, F t (Real.log n)) -
          ∫ s in Icc 0 (cutoff N), (polarDensity s : ℂ) * ∫ t, F t s := by
        rw [integral_sub hsum_int hpolar_int, integral_finsetSum _ fun n _ => hatom n, hswap]
        congr 1
        · exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _
        · refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
          rw [integral_const_mul, hpw, Set.indicator_of_mem hs]
    _ = _ := rfl

/-! ## The critical-line point and the frequency character -/

/-- The critical-line point `s(ξ) = ½ + 2πiξ` attached to the frequency `ξ`. -/
def criticalPoint (ξ : ℝ) : ℂ := ⟨1 / 2, 2 * π * ξ⟩

theorem criticalPoint_re (ξ : ℝ) : (criticalPoint ξ).re = 1 / 2 := rfl

theorem criticalPoint_im (ξ : ℝ) : (criticalPoint ξ).im = 2 * π * ξ := rfl

theorem criticalPoint_ne_zero (ξ : ℝ) : criticalPoint ξ ≠ 0 := fun h => by
  have := congrArg Complex.re h
  rw [criticalPoint_re, Complex.zero_re] at this
  norm_num at this

theorem one_sub_criticalPoint_ne_zero (ξ : ℝ) : 1 - criticalPoint ξ ≠ 0 := fun h => by
  have := congrArg Complex.re h
  rw [Complex.sub_re, Complex.one_re, criticalPoint_re, Complex.zero_re] at this
  norm_num at this

theorem normSq_criticalPoint (ξ : ℝ) :
    Complex.normSq (criticalPoint ξ) = 1 / 4 + (2 * π * ξ) ^ 2 := by
  rw [Complex.normSq_apply, criticalPoint_re, criticalPoint_im]; ring

theorem normSq_criticalPoint_pos (ξ : ℝ) : 0 < Complex.normSq (criticalPoint ξ) := by
  rw [normSq_criticalPoint]; positivity

/-- The Fourier transform as an explicit exponential integral. -/
theorem fourierTransform_eq_integral_exp (h : ℝ → ℂ) (ξ : ℝ) :
    𝓕 h ξ = ∫ t, Complex.exp (-(2 * π * t * ξ : ℝ) * Complex.I) * h t := by
  rw [Real.fourier_real_eq]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 2
  push_cast; ring

/-- The frequency character `χ_ξ(t) = e^{−2πiξt}`. -/
def frequencyCharacter (ξ t : ℝ) : ℂ := Complex.exp (-(2 * π * t * ξ : ℝ) * Complex.I)

theorem norm_frequencyCharacter (ξ t : ℝ) : ‖frequencyCharacter ξ t‖ = 1 := by
  unfold frequencyCharacter
  rw [Complex.norm_exp]
  simp

theorem frequencyCharacter_add (ξ t s : ℝ) :
    frequencyCharacter ξ (t + s) = frequencyCharacter ξ t * frequencyCharacter ξ s := by
  unfold frequencyCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

theorem measurable_frequencyCharacter (ξ : ℝ) : Measurable (frequencyCharacter ξ) := by
  unfold frequencyCharacter
  fun_prop

/-! ## The Fourier transform of the causal kernel -/

theorem frequencyCharacter_mul_causalKernel {ξ t : ℝ} (ht : 0 ≤ t) :
    frequencyCharacter ξ t * (causalKernel t : ℂ) = Complex.exp (-criticalPoint ξ * t) := by
  unfold frequencyCharacter
  rw [causalKernel_of_nonneg ht, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [criticalPoint] <;> ring

theorem re_neg_criticalPoint_mul (ξ t : ℝ) : (-criticalPoint ξ * t).re = -(t / 2) := by
  simp [criticalPoint]; ring

/-- `∫_0^∞ e^{−s(ξ) t} dt = 1/s(ξ)`. -/
theorem integral_exp_neg_criticalPoint_mul (ξ : ℝ) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-criticalPoint ξ * t)) = 1 / criticalPoint ξ := by
  have hc0 : criticalPoint ξ ≠ 0 := criticalPoint_ne_zero ξ
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => -Complex.exp (-criticalPoint ξ * t) / criticalPoint ξ)
      (Complex.exp (-criticalPoint ξ * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -criticalPoint ξ * (t : ℂ)) (-criticalPoint ξ) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (-criticalPoint ξ)
    have h2 := ((Complex.hasDerivAt_exp (-criticalPoint ξ * t)).comp t h1).neg.div_const
      (criticalPoint ξ)
    refine h2.congr_deriv ?_
    rw [mul_neg, neg_neg, mul_div_assoc, div_self hc0, mul_one]
  have hcont : Continuous fun t : ℝ => -Complex.exp (-criticalPoint ξ * t) / criticalPoint ξ :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).neg).div_const _
  have hlim : Tendsto (fun t : ℝ => -Complex.exp (-criticalPoint ξ * t) / criticalPoint ξ) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun t : ℝ => Real.exp (-(t / 2)) / ‖criticalPoint ξ‖) atTop
        (𝓝 (0 / ‖criticalPoint ξ‖)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).div_const _
    rw [zero_div] at h1
    refine h1.congr fun t => ?_
    rw [norm_div, norm_neg, Complex.norm_exp, re_neg_criticalPoint_mul]
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-criticalPoint ξ * t)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 (show (0 : ℝ) < 1 / 2 by norm_num)).mono'
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    show ‖Complex.exp (-criticalPoint ξ * t)‖ ≤ Real.exp (-(1 / 2) * t)
    rw [Complex.norm_exp, re_neg_criticalPoint_mul]
    exact le_of_eq (by congr 1; ring)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt (fun t _ => hd t) hint hlim]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_sub, neg_div, neg_neg]

/-- **`𝓕 K (ξ) = 1/(½ + 2πiξ)`.** -/
theorem fourier_causalKernel (ξ : ℝ) :
    𝓕 (fun t => (causalKernel t : ℂ)) ξ = 1 / criticalPoint ξ := by
  rw [fourierTransform_eq_integral_exp, ← integral_exp_neg_criticalPoint_mul ξ]
  have h1 : (∫ t, frequencyCharacter ξ t * (causalKernel t : ℂ)) =
      ∫ t in Ici (0 : ℝ), frequencyCharacter ξ t * (causalKernel t : ℂ) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    rw [causalKernel_of_neg (not_le.1 ht), Complex.ofReal_zero, mul_zero]
  show (∫ t, frequencyCharacter ξ t * (causalKernel t : ℂ)) = _
  rw [h1, integral_Ici_eq_integral_Ioi]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht =>
    frequencyCharacter_mul_causalKernel (le_of_lt ht)

/-- The transform of the shifted causal kernel: `∫ χ_ξ(t) K(t − s) dt = χ_ξ(s)/s(ξ)`. -/
theorem integral_frequencyCharacter_mul_causalKernel_shift (ξ s : ℝ) :
    (∫ t, frequencyCharacter ξ t * (causalKernel (t - s) : ℂ)) =
      frequencyCharacter ξ s * (1 / criticalPoint ξ) := by
  have h := fourier_causalKernel ξ
  rw [fourierTransform_eq_integral_exp] at h
  rw [← integral_add_right_eq_self (μ := volume)
    (fun t => frequencyCharacter ξ t * (causalKernel (t - s) : ℂ)) s, ← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show frequencyCharacter ξ (t + s) * (causalKernel (t + s - s) : ℂ) =
    frequencyCharacter ξ s * (Complex.exp (-(2 * π * t * ξ : ℝ) * Complex.I) * (causalKernel t : ℂ))
  rw [add_sub_cancel_right, frequencyCharacter_add]
  show frequencyCharacter ξ t * frequencyCharacter ξ s * (causalKernel t : ℂ) =
    frequencyCharacter ξ s * (frequencyCharacter ξ t * (causalKernel t : ℂ))
  ring

/-! ## The Fourier transform of the causal response -/

/-- The causal kernel windowed to the field's cutoff in the source variable. -/
def windowedCausalKernel (L t s : ℝ) : ℝ :=
  causalKernel (t - s) * (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ)) s

theorem windowedCausalKernel_of_mem {L s : ℝ} (hs : s ∈ Icc (0 : ℝ) L) (t : ℝ) :
    windowedCausalKernel L t s = causalKernel (t - s) := by
  simp [windowedCausalKernel, Set.indicator_of_mem hs]

theorem measurable_windowedCausalKernel (L : ℝ) :
    Measurable (Function.uncurry (windowedCausalKernel L)) :=
  (measurable_causalKernel.comp (measurable_fst.sub measurable_snd)).mul
    ((measurable_const.indicator measurableSet_Icc).comp measurable_snd)

theorem abs_windowedCausalKernel_le (L t s : ℝ) :
    |windowedCausalKernel L t s| ≤ |causalKernel t| * Real.exp (L / 2) := by
  by_cases hs : s ∈ Icc (0 : ℝ) L
  · rw [windowedCausalKernel_of_mem hs, abs_of_nonneg (causalKernel_nonneg _),
      abs_of_nonneg (causalKernel_nonneg _)]
    by_cases hts : s ≤ t
    · rw [causalKernel_of_nonneg (by linarith), causalKernel_of_nonneg (by linarith [hs.1])]
      have : Real.exp (-(t - s) / 2) = Real.exp (-t / 2) * Real.exp (s / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hs.2])) (Real.exp_pos _).le
    · rw [causalKernel_of_neg (by linarith)]
      exact mul_nonneg (causalKernel_nonneg t) (Real.exp_pos _).le
  · have h0 : windowedCausalKernel L t s = 0 := by
      unfold windowedCausalKernel; rw [Set.indicator_of_notMem hs, mul_zero]
    rw [h0, abs_zero]
    positivity

/-- The Fourier transform of the signed prime–polar measure, `ν̂_N(ξ) = ∫ e^{−2πiξs} dν_N(s)`. -/
def fourierPairing (N : ℕ) (ξ : ℝ) : ℂ := pairingC N fun s => frequencyCharacter ξ s

theorem norm_fourierPairing_le (N : ℕ) (ξ : ℝ) : ‖fourierPairing N ξ‖ ≤ mass N := by
  have := norm_pairingC_le_mass_mul N (fun s => frequencyCharacter ξ s)
    (B := 1) fun s => (norm_frequencyCharacter ξ s).le
  rwa [mul_one] at this

/-- **The response transform factors through the pole: `𝓕 R_N (ξ) = ν̂_N(ξ) / s(ξ)`.** -/
theorem fourier_causalResponse (N : ℕ) (ξ : ℝ) :
    𝓕 (fun t => (causalResponse N t : ℂ)) ξ = fourierPairing N ξ / criticalPoint ξ := by
  have hmeas : Measurable (Function.uncurry fun t s =>
      frequencyCharacter ξ t * (windowedCausalKernel (cutoff N) t s : ℂ)) :=
    ((measurable_frequencyCharacter ξ).comp measurable_fst).mul
      (Complex.measurable_ofReal.comp (measurable_windowedCausalKernel (cutoff N)))
  have hb : ∀ t s, ‖frequencyCharacter ξ t * (windowedCausalKernel (cutoff N) t s : ℂ)‖ ≤
      |causalKernel t| * Real.exp (cutoff N / 2) := by
    intro t s
    rw [norm_mul, norm_frequencyCharacter, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_windowedCausalKernel_le _ t s
  have hF := integral_pairingC_of_dominated N
    (fun t s => frequencyCharacter ξ t * (windowedCausalKernel (cutoff N) t s : ℂ)) hmeas
    integrable_causalKernel hb
  calc 𝓕 (fun t => (causalResponse N t : ℂ)) ξ
      = ∫ t, frequencyCharacter ξ t * (causalResponse N t : ℂ) :=
        fourierTransform_eq_integral_exp _ ξ
    _ = ∫ t, pairingC N fun s =>
          frequencyCharacter ξ t * (windowedCausalKernel (cutoff N) t s : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show frequencyCharacter ξ t * (causalResponse N t : ℂ) =
          pairingC N fun s => frequencyCharacter ξ t * (windowedCausalKernel (cutoff N) t s : ℂ)
        rw [pairingC_const_mul, pairingC_ofReal]
        congr 2
        unfold causalResponse
        exact pairing_congr_window N fun s hs => (windowedCausalKernel_of_mem hs t).symm
    _ = pairingC N fun s => ∫ t, frequencyCharacter ξ t * (windowedCausalKernel (cutoff N) t s : ℂ) :=
        hF
    _ = pairingC N fun s => frequencyCharacter ξ s * (1 / criticalPoint ξ) := by
        refine pairingC_congr_window N fun s hs => ?_
        rw [← integral_frequencyCharacter_mul_causalKernel_shift ξ s]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show frequencyCharacter ξ t * (windowedCausalKernel (cutoff N) t s : ℂ) =
          frequencyCharacter ξ t * (causalKernel (t - s) : ℂ)
        rw [windowedCausalKernel_of_mem hs]
    _ = fourierPairing N ξ / criticalPoint ξ := by
        rw [pairingC_mul_const]
        unfold fourierPairing
        ring

/-! ## Plancherel: the Laplace energy as a weighted critical-line mean square -/

/-- **Spectral form of the Laplace energy:**
`laplaceEnergy N = ∫ ‖ν̂_N(ξ)‖² / (¼ + 4π²ξ²) dξ`. -/
theorem laplaceEnergy_eq_integral_fourierPairing_sq (N : ℕ) :
    laplaceEnergy N = ∫ ξ, ‖fourierPairing N ξ‖ ^ 2 / (1 / 4 + (2 * π * ξ) ^ 2) := by
  have hRi : Integrable fun t => (causalResponse N t : ℂ) := (integrable_causalResponse N).ofReal
  have hR2 : MemLp (fun t => (causalResponse N t : ℂ)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hRi.aestronglyMeasurable]
    refine (integrable_sq_causalResponse N).congr (Eventually.of_forall fun t => ?_)
    show causalResponse N t ^ 2 = ‖(causalResponse N t : ℂ)‖ ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hP := GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier hRi hR2
  have h2 : (∫ x, ‖(causalResponse N x : ℂ)‖ ^ 2) = ∫ t, causalResponse N t ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun t => by
      show ‖(causalResponse N t : ℂ)‖ ^ 2 = causalResponse N t ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])
  rw [← integral_sq_causalResponse_eq_laplaceEnergy, ← h2, ← hP]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  show ‖𝓕 (fun t => (causalResponse N t : ℂ)) ξ‖ ^ 2 =
    ‖fourierPairing N ξ‖ ^ 2 / (1 / 4 + (2 * π * ξ) ^ 2)
  rw [fourier_causalResponse, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm,
    normSq_criticalPoint]

/-- The mean-square Chebyshev error is controlled by the critical-line spectral energy. -/
theorem chebyshev_mean_square_le_spectral (N : ℕ) :
    (∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2) ≤
      2 * (∫ ξ, ‖fourierPairing N ξ‖ ^ 2 / (1 / 4 + (2 * π * ξ) ^ 2)) + 2 := by
  rw [← laplaceEnergy_eq_integral_fourierPairing_sq]
  exact chebyshev_mean_square_le_laplaceEnergy N

/-! ## The Dirichlet-polynomial form of `ν̂_N` -/

theorem natCast_cpow_eq_exp_mul_log {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    (n : ℂ) ^ s = Complex.exp (s * (Real.log (n : ℝ) : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.natCast_log, mul_comm]

/-- Each atom of `ν̂_N` is a term of the Dirichlet series `Σ Λ(n) n^{−s}` at `s = s(ξ)`. -/
theorem primeWeight_mul_frequencyCharacter_log {n : ℕ} (hn : 1 ≤ n) (ξ : ℝ) :
    (primeWeight n : ℂ) * frequencyCharacter ξ (Real.log n) =
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-criticalPoint ξ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.log_sqrt hn0.le, Real.exp_log (Real.sqrt_pos.2 hn0)]
  have h1 : primeWeight n = ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2)) := by
    unfold primeWeight
    rw [← hsq, Real.exp_neg, div_eq_mul_inv]
  rw [h1, natCast_cpow_eq_exp_mul_log hn, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc]
  unfold frequencyCharacter
  rw [← Complex.exp_add]
  congr 2
  generalize Real.log (n : ℝ) = l
  apply Complex.ext <;> simp [criticalPoint] <;> ring

/-- The polar part of `ν̂_N`: the two pole terms of the truncated explicit formula. -/
theorem integral_polarDensity_mul_frequencyCharacter (N : ℕ) (ξ : ℝ) :
    (∫ x in Icc 0 (cutoff N), (polarDensity x : ℂ) * frequencyCharacter ξ x) =
      (Complex.exp ((1 - criticalPoint ξ) * cutoff N) - 1) / (1 - criticalPoint ξ) +
        (1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ := by
  have hcongr : ∀ x : ℝ, (polarDensity x : ℂ) * frequencyCharacter ξ x =
      Complex.exp ((1 - criticalPoint ξ) * x) + Complex.exp (-criticalPoint ξ * x) := by
    intro x
    have e1 : Complex.exp ((1 - criticalPoint ξ) * x) =
        (Real.exp (x / 2) : ℂ) * frequencyCharacter ξ x := by
      unfold frequencyCharacter
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      apply Complex.ext <;> simp [criticalPoint] <;> ring
    have e2 : Complex.exp (-criticalPoint ξ * x) =
        (Real.exp (-(x / 2)) : ℂ) * frequencyCharacter ξ x := by
      unfold frequencyCharacter
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      apply Complex.ext <;> simp [criticalPoint] <;> ring
    rw [e1, e2]
    unfold polarDensity
    rw [Real.cosh_eq]
    push_cast
    ring
  have hc1 : Continuous fun x : ℝ => Complex.exp ((1 - criticalPoint ξ) * x) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hc2 : Continuous fun x : ℝ => Complex.exp (-criticalPoint ξ * x) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  rw [setIntegral_congr_fun measurableSet_Icc fun x _ => hcongr x, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (cutoff_nonneg N),
    intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    integral_exp_mul_complex (one_sub_criticalPoint_ne_zero ξ),
    integral_exp_mul_complex (neg_ne_zero.2 (criticalPoint_ne_zero ξ))]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  ring

/-- **The spectral density is the pole-subtracted truncated `−ζ'/ζ` on the critical line.** -/
theorem fourierPairing_eq_dirichlet (N : ℕ) (ξ : ℝ) :
    fourierPairing N ξ =
      (∑ n ∈ Finset.Icc 1 (N + 2),
          (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-criticalPoint ξ)) -
        ((Complex.exp ((1 - criticalPoint ξ) * cutoff N) - 1) / (1 - criticalPoint ξ) +
          (1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ) := by
  unfold fourierPairing pairingC
  rw [integral_polarDensity_mul_frequencyCharacter]
  congr 1
  exact Finset.sum_congr rfl fun n hn =>
    primeWeight_mul_frequencyCharacter_log (Finset.mem_Icc.mp hn).1 ξ

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
