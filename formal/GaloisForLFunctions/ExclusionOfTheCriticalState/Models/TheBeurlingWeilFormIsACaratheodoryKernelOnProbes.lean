import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.RealProbeNodesDecideTheRiemannHypothesis
import GaloisForLFunctions.StripBochnerWeilForcing.PositiveDefiniteSectionsAreCompletelyMonotone
import GaloisForLFunctions.HTGeometry.LogDerivNoZero
import GaloisForLFunctions.RHTower.GammaRealHalfPlane
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeDensityFormula

/-!
# The Weil form of a Beurling system

A Beurling system is recorded by its von Mangoldt measure `ν` in the logarithmic coordinate: a
positive measure on `[0, ∞)` with `∫ e^{-σt} dν < ∞` for every `σ > 1` (`IsBeurlingMeasure`), so
that `-(log ζ_ν)'(s) = ∫ e^{-st} dν(t)`. For `ℕ` it is `Σ_n Λ(n) δ_{log n}` (`vonMangoldtMeasure`);
for a continuous system with logarithmic prime density `w` it is `t w(t) dt`.

* **The form** (`beurlingWeilForm`). On half-line profiles: `ζ`'s Gamma and pole parts and the prime
  part `∫ e^{-t/2} (∫ F(u) G(u-t) du + ∫ F(u) G(u+t) du) dν(t)`, symmetrized; `beurlingConfinedForm`
  adds the confinement `a(R) ∫_{u<0} F G e^{-8u}`. For the von Mangoldt measure of `ℕ` it is the bare
  Weil form of `ζ` (`beurlingWeilForm_vonMangoldtMeasure`).
* **The probe kernel** (`beurlingWeilForm_probe`). On probes `e_p = 1_{u<0} e^{pu}`, `p, q > ½`, the
  form is `(D_ν(p) + D_ν(q))/(p + q)` with
  `D_ν(p) = 1/(p+½) + 1/(p-½) + (Re ψ(¼+p/2) - log π)/2 - ∫ e^{-(½+p)t} dν`. This is the real
  trace of `D_ν(w) = 1/(w+½) + 1/(w-½) + (Γℝ'/Γℝ)(½+w) - ∫ e^{-(½+w)t} dν`, holomorphic on
  `Re w > ½` (`beurlingLogDeriv`, `differentiableAt_beurlingLogDeriv`), the centred logarithmic
  derivative of the completed zeta `s(s-1)Γℝ(s)ζ_ν(s)`. For `ℕ` the symbol is `ζ`'s
  (`beurlingProbeSymbol_vonMangoldtMeasure`).
* **Weil positivity is a Carathéodory extension** (`beurling_probe_forms_nonneg_iff`). For nodes
  `S ⊆ (½, ∞)` accumulating at a point of `(½, ∞)`: the form is nonnegative on the real span of the
  probes `e_p`, `p ∈ S`, iff `D_ν` extends from `Re w > ½` to a holomorphic function of nonnegative
  real part on `Re w > 0`. Mechanism: Nevanlinna–Pick interpolation of the positive kernel on `S`
  and the identity theorem. Positivity on `S` then holds on all nodes `> ½`
  (`beurling_probe_forms_nonneg_of_accumulating`).
* **Zeros right of the line block positivity** (`beurling_ne_zero_of_probe_forms_nonneg`,
  `exists_beurling_probe_form_neg_of_zero`). If `Y` is holomorphic on `Re w > 0`, zero-free on
  `Re w > ½`, with `Y'/Y = D_ν` there (a continuation of the completed zeta), and `Y` vanishes at a
  point of `Re w > 0`, then on every such `S` some real Pick matrix of the form is not positive
  semidefinite.

No functional equation enters: the zero set of a Beurling system need not be reflection-invariant,
and the probe kernel carries no Krein structure, but it remains a Carathéodory kernel.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate ComplexOrder Matrix ENNReal NNReal

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry _root_.RHTower CriticalArithmeticCorrelationTheory

/-! ### Beurling measures -/

/-- A Beurling von Mangoldt measure in the logarithmic coordinate: carried by `[0, ∞)`, with a
convergent Laplace transform right of `1`. -/
structure IsBeurlingMeasure (ν : Measure ℝ) : Prop where
  support : ν (Ici 0)ᶜ = 0
  integrable : ∀ σ : ℝ, 1 < σ → Integrable (fun t => Real.exp (-(σ * t))) ν

theorem IsBeurlingMeasure.ae_nonneg {ν : Measure ℝ} (hν : IsBeurlingMeasure ν) :
    ∀ᵐ t ∂ν, 0 ≤ t := by
  rw [ae_iff]
  simpa [compl_def, mem_Ici, not_le] using hν.support

/-- The Laplace transform `∫ e^{-st} dν` at a real point. -/
def beurlingLaplace (ν : Measure ℝ) (s : ℝ) : ℝ := ∫ t, Real.exp (-(s * t)) ∂ν

/-! ### The von Mangoldt measure of `ℕ` -/

/-- `Σ_n Λ(n) δ_{log n}`. -/
def vonMangoldtMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (ArithmeticFunction.vonMangoldt n) • Measure.dirac (Real.log n)

theorem integrable_vonMangoldtMeasure {f : ℝ → ℝ}
    (hf : Summable fun n : ℕ => ArithmeticFunction.vonMangoldt n * |f (Real.log n)|) :
    Integrable f vonMangoldtMeasure := by
  refine ⟨aestronglyMeasurable_sum_measure_iff.mpr fun n => ?_, ?_⟩
  · exact (aestronglyMeasurable_const.congr (ae_eq_dirac f).symm).smul_measure _
  · unfold HasFiniteIntegral
    rw [vonMangoldtMeasure, lintegral_sum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    have e : ∀ n : ℕ, ENNReal.ofReal (ArithmeticFunction.vonMangoldt n) * ‖f (Real.log n)‖ₑ =
        ENNReal.ofReal (ArithmeticFunction.vonMangoldt n * |f (Real.log n)|) := fun n => by
      rw [ENNReal.ofReal_mul ArithmeticFunction.vonMangoldt_nonneg, ← ofReal_norm_eq_enorm,
        Real.norm_eq_abs]
    simp_rw [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (abs_nonneg _)) hf]
    exact ENNReal.ofReal_lt_top

theorem integral_vonMangoldtMeasure {f : ℝ → ℝ}
    (hf : Summable fun n : ℕ => ArithmeticFunction.vonMangoldt n * |f (Real.log n)|) :
    ∫ t, f t ∂vonMangoldtMeasure =
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f (Real.log n) := by
  have hi := integrable_vonMangoldtMeasure hf
  rw [vonMangoldtMeasure] at hi ⊢
  rw [integral_sum_measure hi]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal ArithmeticFunction.vonMangoldt_nonneg, smul_eq_mul]

theorem vonMangoldt_mul_exp_neg (σ : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n * Real.exp (-(σ * Real.log n)) =
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Real.rpow_def_of_pos (by exact_mod_cast hn), Real.exp_neg, div_eq_mul_inv,
      mul_comm (Real.log n)]

theorem isBeurlingMeasure_vonMangoldtMeasure : IsBeurlingMeasure vonMangoldtMeasure where
  support := by
    have hs : MeasurableSet (Ici (0 : ℝ))ᶜ := measurableSet_Ici.compl
    rw [vonMangoldtMeasure, Measure.sum_apply _ hs]
    refine ENNReal.tsum_eq_zero.mpr fun n => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hs,
      Set.indicator_of_notMem (by simpa using Real.log_natCast_nonneg n), smul_zero]
  integrable σ hσ := integrable_vonMangoldtMeasure <|
    (summable_vonMangoldt_div_rpow hσ).congr fun n => by
      rw [abs_of_pos (Real.exp_pos _), vonMangoldt_mul_exp_neg]

theorem beurlingLaplace_vonMangoldtMeasure {σ : ℝ} (hσ : 1 < σ) :
    beurlingLaplace vonMangoldtMeasure σ =
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
  unfold beurlingLaplace
  rw [integral_vonMangoldtMeasure]
  · exact tsum_congr fun n => vonMangoldt_mul_exp_neg σ n
  · exact (summable_vonMangoldt_div_rpow hσ).congr fun n => by
      rw [abs_of_pos (Real.exp_pos _), vonMangoldt_mul_exp_neg]

/-! ### The form -/

/-- The prime atom at lag `t`: the two lag correlations of `F` and `G`, weighted by `e^{-t/2}`. -/
def primeLagPair (F G : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(t / 2)) * ((∫ u, F u * G (u - t)) + ∫ u, F u * G (u + t))

/-- The prime part of the Weil form of the system. -/
def beurlingPrimeForm (ν : Measure ℝ) (F G : ℝ → ℝ) : ℝ := ∫ t, primeLagPair F G t ∂ν

/-- **The Weil form of a Beurling system**: Gamma part minus the prime part of `ν` plus the pole
part. -/
def beurlingWeilForm (ν : Measure ℝ) (F G : ℝ → ℝ) : ℝ :=
  gammaMixedForm F G - (beurlingPrimeForm ν F G + beurlingPrimeForm ν G F) / 2 +
    (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G)

/-- The confined Weil form `B_ν + a(R) W₈` of the system. -/
def beurlingConfinedForm (ν : Measure ℝ) (R : ℝ) (F G : ℝ → ℝ) : ℝ :=
  beurlingWeilForm ν F G +
    criticalAliasCoefficient R * ∫ u in Iio 0, F u * G u * Real.exp (-(8 * u))

theorem vonMangoldt_mul_primeLagPair (F G : ℝ → ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n * primeLagPair F G (Real.log n) = primePairTerm F G n := by
  unfold primeLagPair primePairTerm vonMangoldtAtom
  split_ifs with h
  · have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have he : Real.exp (-(Real.log n / 2)) = (Real.sqrt n)⁻¹ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn, ← Real.exp_neg]
      congr 1
      ring
    rw [he, div_eq_mul_inv]
    ring
  · have h0 : ArithmeticFunction.vonMangoldt n = 0 := by
      interval_cases n <;> simp
    rw [h0]
    ring

/-- For `ℕ` the prime part is `ζ`'s prime form. -/
theorem beurlingPrimeForm_vonMangoldtMeasure {F G : ℝ → ℝ} (hF : WeightedTwo F)
    (hG : WeightedTwo G) : beurlingPrimeForm vonMangoldtMeasure F G = primeMixedForm F G := by
  have hs : Summable fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * |primeLagPair F G (Real.log n)| := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (abs_nonneg _)) (fun n => ?_)
      (((summable_vonMangoldt_div_rpow (σ := 3 / 2) (by norm_num)).mul_left 2).mul_right
        (Real.sqrt (exponentialSourceMass F) * Real.sqrt (exponentialSourceMass G)))
    have e : ArithmeticFunction.vonMangoldt n * |primeLagPair F G (Real.log n)| =
        |primePairTerm F G n| := by
      rw [← vonMangoldt_mul_primeLagPair, abs_mul,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [e]
    exact abs_primePairTerm_le hF hG n
  unfold beurlingPrimeForm primeMixedForm
  rw [integral_vonMangoldtMeasure hs]
  exact tsum_congr fun n => vonMangoldt_mul_primeLagPair F G n

/-- **For `ℕ` the Beurling Weil form is `ζ`'s bare Weil form** on the weighted domain. -/
theorem beurlingWeilForm_vonMangoldtMeasure {F G : ℝ → ℝ} (hF : WeightedTwo F)
    (hG : WeightedTwo G) : beurlingWeilForm vonMangoldtMeasure F G = bareMixedEnergy F G := by
  unfold beurlingWeilForm bareMixedEnergy
  rw [beurlingPrimeForm_vonMangoldtMeasure hF hG, beurlingPrimeForm_vonMangoldtMeasure hG hF]

/-! ### The probe kernel -/

theorem primeLagPair_probe {p q : ℝ} (hpq : 0 < p + q) {t : ℝ} (ht : 0 ≤ t) :
    primeLagPair (probe p) (probe q) t =
      (Real.exp (-((1 / 2 + q) * t)) + Real.exp (-((1 / 2 + p) * t))) / (p + q) := by
  unfold primeLagPair
  rw [integral_probe_mul_probe_sub hpq ht, integral_probe_mul_probe_add hpq ht]
  have e : ∀ c : ℝ, Real.exp (-((1 / 2 + c) * t)) = Real.exp (-(t / 2)) * Real.exp (-(c * t)) :=
    fun c => by rw [← Real.exp_add]; congr 1; ring
  rw [e, e]
  ring

theorem beurlingPrimeForm_probe {ν : Measure ℝ} (hν : IsBeurlingMeasure ν) {p q : ℝ}
    (hp : 1 / 2 < p) (hq : 1 / 2 < q) :
    beurlingPrimeForm ν (probe p) (probe q) =
      (beurlingLaplace ν (1 / 2 + q) + beurlingLaplace ν (1 / 2 + p)) / (p + q) := by
  have hpq : 0 < p + q := by linarith
  unfold beurlingPrimeForm beurlingLaplace
  rw [integral_congr_ae (hν.ae_nonneg.mono fun t ht => primeLagPair_probe hpq ht), integral_div,
    integral_add (hν.integrable _ (by linarith)) (hν.integrable _ (by linarith))]

/-- The real probe symbol `D_ν(p)` of the system. -/
def beurlingProbeSymbol (ν : Measure ℝ) (p : ℝ) : ℝ :=
  1 / (p + 1 / 2) + 1 / (p - 1 / 2) +
    ((Complex.digamma ((1 / 4 + p / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 -
    beurlingLaplace ν (1 / 2 + p)

/-- **The probe kernel.** The Weil form of a Beurling system on two probes is
`(D_ν(p) + D_ν(q))/(p + q)`. -/
theorem beurlingWeilForm_probe {ν : Measure ℝ} (hν : IsBeurlingMeasure ν) {p q : ℝ}
    (hp : 1 / 2 < p) (hq : 1 / 2 < q) :
    beurlingWeilForm ν (probe p) (probe q) =
      (beurlingProbeSymbol ν p + beurlingProbeSymbol ν q) / (p + q) := by
  unfold beurlingWeilForm
  rw [gammaMixedForm_probe (by linarith) (by linarith), beurlingPrimeForm_probe hν hp hq,
    beurlingPrimeForm_probe hν hq hp, polePart_probe hp hq]
  unfold beurlingProbeSymbol
  have h5 : p + q ≠ 0 := by linarith
  rw [add_comm q p]
  field_simp
  ring

/-- The confined probe kernel `(D_ν(p) + D_ν(q))/(p + q) + a(R)/(p + q - 8)`. -/
theorem beurlingConfinedForm_probe {ν : Measure ℝ} (hν : IsBeurlingMeasure ν) (R : ℝ) {p q : ℝ}
    (hp : 4 < p) (hq : 4 < q) :
    beurlingConfinedForm ν R (probe p) (probe q) =
      (beurlingProbeSymbol ν p + beurlingProbeSymbol ν q) / (p + q) +
        criticalAliasCoefficient R / (p + q - 8) := by
  unfold beurlingConfinedForm
  rw [beurlingWeilForm_probe hν (by linarith) (by linarith), confinement_probe_probe (by linarith)]
  ring

/-- For `ℕ` the probe symbol is `ζ`'s, `(log ξ)'(½ + p)`. -/
theorem beurlingProbeSymbol_vonMangoldtMeasure {p : ℝ} (hp : 1 / 2 < p) :
    beurlingProbeSymbol vonMangoldtMeasure p = probeSymbol p := by
  unfold beurlingProbeSymbol probeSymbol
  rw [beurlingLaplace_vonMangoldtMeasure (by linarith)]

theorem beurlingWeilForm_probe_symm {ν : Measure ℝ} (hν : IsBeurlingMeasure ν) {p q : ℝ}
    (hp : 1 / 2 < p) (hq : 1 / 2 < q) :
    beurlingWeilForm ν (probe p) (probe q) = beurlingWeilForm ν (probe q) (probe p) := by
  rw [beurlingWeilForm_probe hν hp hq, beurlingWeilForm_probe hν hq hp,
    add_comm (beurlingProbeSymbol ν p), add_comm p]

/-! ### The holomorphic symbol -/

/-- The complex symbol `D_ν(w) = 1/(w+½) + 1/(w-½) + (Γℝ'/Γℝ)(½+w) - ∫ e^{-(½+w)t} dν`. -/
def beurlingLogDeriv (ν : Measure ℝ) (w : ℂ) : ℂ :=
  1 / (w + 1 / 2) + 1 / (w - 1 / 2) + logDeriv Gammaℝ (1 / 2 + w) -
    ∫ t, cexp (-((1 / 2 + w) * t)) ∂ν

/-- The complex Laplace transform of a Beurling measure is holomorphic on `Re s > 1`: it is the
Laplace transform of the finite measure `e^{-σt} dν` shifted by `σ`. -/
theorem differentiableAt_beurlingLaplaceC {ν : Measure ℝ} (hν : IsBeurlingMeasure ν) {s₀ : ℂ}
    (hs₀ : 1 < s₀.re) : DifferentiableAt ℂ (fun s : ℂ => ∫ t, cexp (-(s * t)) ∂ν) s₀ := by
  set σ : ℝ := (1 + s₀.re) / 2 with hσdef
  have hσ : 1 < σ := by rw [hσdef]; linarith
  set τ : Measure ℝ := ν.withDensity fun t => ((Real.toNNReal (Real.exp (-(σ * t))) : ℝ≥0) : ℝ≥0∞)
    with hτdef
  haveI : IsFiniteMeasure τ :=
    isFiniteMeasure_withDensity_ofReal (hν.integrable σ hσ).hasFiniteIntegral
  have hτ : τ (Ici (0 : ℝ))ᶜ = 0 := withDensity_absolutelyContinuous _ _ hν.support
  have hshift : ∀ s : ℂ, (∫ t, cexp (-(s * t)) ∂ν) = ∫ t, cexp (-(s - σ) * t) ∂τ := by
    intro s
    rw [hτdef, integral_withDensity_eq_integral_smul (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, Complex.real_smul,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfun : (fun s : ℂ => ∫ t, cexp (-(s * t)) ∂ν) =
      (fun z : ℂ => ∫ t, cexp (-z * t) ∂τ) ∘ fun s : ℂ => s - σ := funext hshift
  have hmem : s₀ - σ ∈ {z : ℂ | 0 < z.re} := by
    show 0 < (s₀ - σ).re
    rw [Complex.sub_re, Complex.ofReal_re, hσdef]
    linarith
  rw [hfun]
  exact ((differentiableOn_laplaceC hτ).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).comp s₀
    (differentiableAt_id.sub_const _)

theorem differentiableAt_logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (logDeriv Gammaℝ) s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gammaℝ {z : ℂ | 0 < z.re} := fun z hz =>
    (differentiableAt_Gammaℝ_of_re_pos hz).differentiableWithinAt
  have hd' := ((hd.deriv hU).differentiableAt (hU.mem_nhds hs)).div
    (differentiableAt_Gammaℝ_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos hs)
  exact hd'

/-- **The symbol is holomorphic on `Re w > ½`.** -/
theorem differentiableAt_beurlingLogDeriv {ν : Measure ℝ} (hν : IsBeurlingMeasure ν) {w : ℂ}
    (hw : 1 / 2 < w.re) : DifferentiableAt ℂ (beurlingLogDeriv ν) w := by
  have h1 : w + 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : w - 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs : 0 < ((1 : ℂ) / 2 + w).re := by simp; linarith
  have hs1 : 1 < ((1 : ℂ) / 2 + w).re := by simp; linarith
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 + w) w :=
    (differentiableAt_const _).add differentiableAt_id
  unfold beurlingLogDeriv
  refine ((((differentiableAt_const _).div (differentiableAt_id.add_const _) h1).add
    ((differentiableAt_const _).div (differentiableAt_id.sub_const _) h2)).add ?_).sub ?_
  · exact (differentiableAt_logDeriv_Gammaℝ hs).comp w hlin
  · exact (differentiableAt_beurlingLaplaceC hν hs1).comp w hlin

/-- On real points the complex symbol is the real probe symbol. -/
theorem beurlingLogDeriv_ofReal (ν : Measure ℝ) {p : ℝ} (hp : 1 / 2 < p) :
    beurlingLogDeriv ν p = beurlingProbeSymbol ν p := by
  have hs : (1 : ℂ) / 2 + p = ((1 / 2 + p : ℝ) : ℂ) := by push_cast; ring
  have hG : logDeriv Gammaℝ ((1 : ℂ) / 2 + p) =
      ((((Complex.digamma ((1 / 4 + p / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 : ℝ) : ℂ) := by
    rw [hs, logDeriv_Gammaℝ_ofReal_eq (by linarith), logDeriv_Gammaℝ_eq (by simp; linarith)]
    congr 1
    have hdg : (((1 / 2 + p : ℝ) : ℂ)) / 2 = ((1 / 4 + p / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hdg]
    simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re]
    ring
  have hL : (∫ t, cexp (-((1 / 2 + (p : ℂ)) * t)) ∂ν) =
      ((beurlingLaplace ν (1 / 2 + p) : ℝ) : ℂ) := by
    unfold beurlingLaplace
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    push_cast
    ring_nf
  unfold beurlingLogDeriv beurlingProbeSymbol
  rw [hG, hL]
  push_cast
  ring

/-- The real probe kernel is the Carathéodory kernel of the complex symbol. -/
theorem beurlingWeilForm_probe_eq_caratheodory {ν : Measure ℝ} (hν : IsBeurlingMeasure ν)
    {p q : ℝ} (hp : 1 / 2 < p) (hq : 1 / 2 < q) :
    ((beurlingWeilForm ν (probe p) (probe q) : ℝ) : ℂ) =
      (beurlingLogDeriv ν p + conj (beurlingLogDeriv ν q)) / ((p : ℂ) + conj (q : ℂ)) := by
  rw [beurlingWeilForm_probe hν hp hq, beurlingLogDeriv_ofReal ν hp, beurlingLogDeriv_ofReal ν hq,
    Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast
  rfl

/-! ### Weil positivity is a Carathéodory extension -/

/-- **Positivity on accumulating nodes gives a Carathéodory extension of the symbol.** -/
theorem exists_caratheodory_extension_of_probe_forms_nonneg {ν : Measure ℝ}
    (hν : IsBeurlingMeasure ν) {S : Set ℝ} (hS : ∀ p ∈ S, 1 / 2 < p) {p₀ : ℝ} (hp₀ : 1 / 2 < p₀)
    (hacc : ∃ᶠ x in 𝓝[≠] p₀, x ∈ S)
    (h : ∀ (n : ℕ) (p c : Fin n → ℝ), (∀ i, p i ∈ S) →
      0 ≤ ∑ i, ∑ j, c i * c j * beurlingWeilForm ν (probe (p i)) (probe (p j))) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {z : ℂ | 0 < z.re} ∧
      (∀ z : ℂ, 0 < z.re → 0 ≤ (G z).re) ∧
      ∀ w : ℂ, 1 / 2 < w.re → G w = beurlingLogDeriv ν w := by
  have hK : IsPSDKernel (fun x y : S =>
      ((beurlingWeilForm ν (probe (x : ℝ)) (probe (y : ℝ)) : ℝ) : ℂ)) :=
    isPSDKernel_ofReal_of_forall_real
      (fun x y => beurlingWeilForm_probe_symm hν (hS x x.2) (hS y y.2))
      fun n w c => h n (fun i => (w i : ℝ)) c fun i => (w i).2
  haveI : Nonempty S := by
    obtain ⟨x, hx⟩ := hacc.exists
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨G, hGd, hGre, hGeq⟩ := exists_caratheodory_interpolant (X := S)
    (fun x => (((x : ℝ)) : ℂ)) (fun x => beurlingLogDeriv ν ((x : ℝ) : ℂ))
    (fun x => by simpa using (by linarith [hS x x.2] : (0 : ℝ) < x))
    (hK.congr fun x y => by rw [beurlingWeilForm_probe_eq_caratheodory hν (hS x x.2) (hS y y.2)])
  refine ⟨G, hGd, hGre, ?_⟩
  have hopen0 : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU : IsOpen {w : ℂ | 1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGa : AnalyticOnNhd ℂ G {w : ℂ | 1 / 2 < w.re} :=
    (hGd.analyticOnNhd hopen0).mono fun w (hw : 1 / 2 < w.re) =>
      (show 0 < w.re by linarith)
  have hDa : AnalyticOnNhd ℂ (beurlingLogDeriv ν) {w : ℂ | 1 / 2 < w.re} :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (differentiableAt_beurlingLogDeriv hν hw).differentiableWithinAt) hU
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] p₀) (𝓝[≠] (p₀ : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_ofReal.tendsto p₀).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun x hx =>
        Complex.ofReal_injective.ne hx⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] (p₀ : ℂ), G z = beurlingLogDeriv ν z :=
    ht.frequently (hacc.mono fun x hx => hGeq ⟨x, hx⟩)
  have h₀ : (p₀ : ℂ) ∈ {w : ℂ | 1 / 2 < w.re} := by
    show 1 / 2 < ((p₀ : ℂ)).re
    simpa using hp₀
  exact fun w hw => hGa.eqOn_of_preconnected_of_frequently_eq hDa
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected h₀ hfreq hw

/-- **A Carathéodory extension gives positivity on every node set in `(½, ∞)`.** -/
theorem probe_forms_nonneg_of_caratheodory {ν : Measure ℝ} (hν : IsBeurlingMeasure ν)
    {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {z : ℂ | 0 < z.re})
    (hGre : ∀ z : ℂ, 0 < z.re → 0 ≤ (G z).re)
    (hGD : ∀ w : ℂ, 1 / 2 < w.re → G w = beurlingLogDeriv ν w) {n : ℕ} (p c : Fin n → ℝ)
    (hp : ∀ i, 1 / 2 < p i) :
    0 ≤ ∑ i, ∑ j, c i * c j * beurlingWeilForm ν (probe (p i)) (probe (p j)) := by
  have hopen0 : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hK := isPSDKernel_halfPlaneCaratheodory
    (fun u hu => hGd.differentiableAt (hopen0.mem_nhds hu)) hGre
  have hM : 0 ≤ dotProduct (star fun i => ((c i : ℝ) : ℂ)) (Matrix.mulVec (Matrix.of fun j k =>
      (G ((p j : ℝ) : ℂ) + conj (G ((p k : ℝ) : ℂ))) / (((p j : ℝ) : ℂ) + conj ((p k : ℝ) : ℂ)))
        fun i => ((c i : ℝ) : ℂ)) :=
    (hK.posSemidef fun i => (⟨((p i : ℝ) : ℂ), by simp; linarith [hp i]⟩ :
      {u : ℂ // 0 < u.re})).dotProduct_mulVec_nonneg _
  have hval : dotProduct (star fun i => ((c i : ℝ) : ℂ)) (Matrix.mulVec (Matrix.of fun j k =>
      (G ((p j : ℝ) : ℂ) + conj (G ((p k : ℝ) : ℂ))) / (((p j : ℝ) : ℂ) + conj ((p k : ℝ) : ℂ)))
        fun i => ((c i : ℝ) : ℂ)) =
      ((∑ i, ∑ j, c i * c j * beurlingWeilForm ν (probe (p i)) (probe (p j)) : ℝ) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Complex.star_def,
      Complex.conj_ofReal, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hGD _ (by simpa using hp i), hGD _ (by simpa using hp j),
      ← Complex.conj_ofReal (p j), ← beurlingWeilForm_probe_eq_caratheodory hν (hp i) (hp j)]
    ring
  rw [hval] at hM
  exact Complex.zero_le_real.mp hM

/-- **Weil positivity of a Beurling system is a Carathéodory extension of its symbol.** On nodes
`S ⊆ (½, ∞)` accumulating at a point of `(½, ∞)`, the form is nonnegative on the real span of the
probes `e_p`, `p ∈ S`, iff `D_ν` extends from `Re w > ½` to a holomorphic function of nonnegative real
part on `Re w > 0`. -/
theorem beurling_probe_forms_nonneg_iff {ν : Measure ℝ} (hν : IsBeurlingMeasure ν) {S : Set ℝ}
    (hS : ∀ p ∈ S, 1 / 2 < p) {p₀ : ℝ} (hp₀ : 1 / 2 < p₀) (hacc : ∃ᶠ x in 𝓝[≠] p₀, x ∈ S) :
    (∀ (n : ℕ) (p c : Fin n → ℝ), (∀ i, p i ∈ S) →
        0 ≤ ∑ i, ∑ j, c i * c j * beurlingWeilForm ν (probe (p i)) (probe (p j))) ↔
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {z : ℂ | 0 < z.re} ∧
        (∀ z : ℂ, 0 < z.re → 0 ≤ (G z).re) ∧
        ∀ w : ℂ, 1 / 2 < w.re → G w = beurlingLogDeriv ν w :=
  ⟨exists_caratheodory_extension_of_probe_forms_nonneg hν hS hp₀ hacc,
    fun ⟨_, hGd, hGre, hGD⟩ n p c hp =>
      probe_forms_nonneg_of_caratheodory hν hGd hGre hGD p c fun i => hS _ (hp i)⟩

/-- **Positivity propagates.** Positivity on an accumulating node set gives positivity on all
nodes `> ½`. -/
theorem beurling_probe_forms_nonneg_of_accumulating {ν : Measure ℝ} (hν : IsBeurlingMeasure ν)
    {S : Set ℝ} (hS : ∀ p ∈ S, 1 / 2 < p) {p₀ : ℝ} (hp₀ : 1 / 2 < p₀)
    (hacc : ∃ᶠ x in 𝓝[≠] p₀, x ∈ S)
    (h : ∀ (n : ℕ) (p c : Fin n → ℝ), (∀ i, p i ∈ S) →
      0 ≤ ∑ i, ∑ j, c i * c j * beurlingWeilForm ν (probe (p i)) (probe (p j)))
    {n : ℕ} (p c : Fin n → ℝ) (hp : ∀ i, 1 / 2 < p i) :
    0 ≤ ∑ i, ∑ j, c i * c j * beurlingWeilForm ν (probe (p i)) (probe (p j)) := by
  obtain ⟨G, hGd, hGre, hGD⟩ := exists_caratheodory_extension_of_probe_forms_nonneg hν hS hp₀ hacc h
  exact probe_forms_nonneg_of_caratheodory hν hGd hGre hGD p c hp

/-! ### Zeros right of the line block positivity -/

/-- **Weil positivity forbids zeros right of the line.** A holomorphic continuation `Y` of the
completed zeta (`Y'/Y = D_ν` on `Re w > ½`, zero-free there) has no zero on `Re w > 0` once the form
is nonnegative on an accumulating node set. -/
theorem beurling_ne_zero_of_probe_forms_nonneg {ν : Measure ℝ} (hν : IsBeurlingMeasure ν)
    {S : Set ℝ} (hS : ∀ p ∈ S, 1 / 2 < p) {p₀ : ℝ} (hp₀ : 1 / 2 < p₀)
    (hacc : ∃ᶠ x in 𝓝[≠] p₀, x ∈ S)
    (h : ∀ (n : ℕ) (p c : Fin n → ℝ), (∀ i, p i ∈ S) →
      0 ≤ ∑ i, ∑ j, c i * c j * beurlingWeilForm ν (probe (p i)) (probe (p j)))
    {Y : ℂ → ℂ} (hY : AnalyticOnNhd ℂ Y {w : ℂ | 0 < w.re})
    (hYne : ∀ w : ℂ, 1 / 2 < w.re → Y w ≠ 0)
    (hYD : ∀ w : ℂ, 1 / 2 < w.re → logDeriv Y w = beurlingLogDeriv ν w) :
    ∀ w : ℂ, 0 < w.re → Y w ≠ 0 := by
  obtain ⟨G, hGd, -, hGD⟩ := exists_caratheodory_extension_of_probe_forms_nonneg hν hS hp₀ hacc h
  have hΩ : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΩc : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hGa : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} := hGd.analyticOnNhd hΩ
  have hh : AnalyticOnNhd ℂ (fun z => deriv Y z - G z * Y z) {z : ℂ | 0 < z.re} :=
    fun z hz => ((hY z hz).deriv).sub ((hGa z hz).mul (hY z hz))
  have hzero : ∀ W : ℂ, 1 / 2 < W.re → deriv Y W - G W * Y W = 0 := by
    intro W hW
    have h1 := hYD W hW
    have hYW := hYne W hW
    rw [← hGD W hW, logDeriv_apply, div_eq_iff hYW] at h1
    rw [h1]
    ring
  have hmem : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by show (0 : ℝ) < (1 : ℂ).re; simp
  have hev : (fun z => deriv Y z - G z * Y z) =ᶠ[𝓝 (1 : ℂ)] 0 := by
    have hopen : IsOpen {W : ℂ | 1 / 2 < W.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℂ) ∈ {W : ℂ | 1 / 2 < W.re} by
      show (1 / 2 : ℝ) < (1 : ℂ).re; norm_num)] with u hu
    exact hzero u hu
  have hEq := hh.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc hmem hev
  have hrel : ∀ z ∈ {z : ℂ | 0 < z.re}, deriv Y z = G z * Y z := fun z hz => by
    have := hEq hz
    simp only [Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  exact fun w hw => ne_zero_of_deriv_eq_mul hΩ hΩc hY hGa hrel hmem
    (hYne 1 (by show (1 / 2 : ℝ) < (1 : ℂ).re; norm_num)) w hw

/-- **A zero right of the line gives a negative Pick matrix** on every accumulating node set. -/
theorem exists_beurling_probe_form_neg_of_zero {ν : Measure ℝ} (hν : IsBeurlingMeasure ν)
    {S : Set ℝ} (hS : ∀ p ∈ S, 1 / 2 < p) {p₀ : ℝ} (hp₀ : 1 / 2 < p₀)
    (hacc : ∃ᶠ x in 𝓝[≠] p₀, x ∈ S)
    {Y : ℂ → ℂ} (hY : AnalyticOnNhd ℂ Y {w : ℂ | 0 < w.re})
    (hYne : ∀ w : ℂ, 1 / 2 < w.re → Y w ≠ 0)
    (hYD : ∀ w : ℂ, 1 / 2 < w.re → logDeriv Y w = beurlingLogDeriv ν w)
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) (hY0 : Y z₀ = 0) :
    ∃ (n : ℕ) (p c : Fin n → ℝ), (∀ i, p i ∈ S) ∧
      ∑ i, ∑ j, c i * c j * beurlingWeilForm ν (probe (p i)) (probe (p j)) < 0 := by
  by_contra hcon
  push_neg at hcon
  exact beurling_ne_zero_of_probe_forms_nonneg hν hS hp₀ hacc hcon hY hYne hYD z₀ hz₀ hY0

end GaloisForLFunctions.ExclusionOfTheCriticalState
