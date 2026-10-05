import GaloisForLFunctions.RHTower.LebesgueAtomArchimedeanWeilDensity
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure
import GaloisForLFunctions.HTGeometry.ResolventSubordination

/-!
# Weil positivity of the Lebesgue-minus-atom system

A weight system for the archimedean datum of `ζ` need not live on the integers.  For a signed weight
`ν₊ − ν₋` given by two measures on `(1, ∞)` the Weil functional with pole weight one is

`W(k) = ĥ(i/2) + ĥ(−i/2) − ∫ x^{−1/2} (k(log x) + k(−log x)) d(ν₊ − ν₋)(x) + (1/2π) ∫ ĥ(r) γ(r) dr`,

with `ĥ = paperFT k` and `γ(r) = Re ψ(1/4 + ir/2) − log π` (`weilMeasureFunctional`).  For the
counting weights `Σ lam(n) δ_n` it is the corpus functional `weilFullFunctional lam`
(`weilMeasureFunctional_natWeights`).

For `λ₀ = 1_{(1,∞)} dx − e^{1/20000} δ_{e^{1/10000}}`:

* the Lebesgue part cancels the growing half `e^{|u|/2}` of the pole term exactly, leaving the pairing
  with `e^{−|u|/2}` (`pole_sub_lebesgue_eq`), and the atom enters with weight one
  (`integral_atomPart`);
* by Fourier inversion and Fubini these are `(1/2π) ∫ ĥ(r)/(1/4 + r²) dr` and
  `(1/π) ∫ ĥ(r) cos(r/10⁴) dr` (`integral_expNegHalfAbs_mul_eq`);
* hence the Weil distribution of `λ₀` is the absolutely continuous measure `ρ(r) dr/2π` with density
  `ρ(r) = γ(r) + 1/(1/4 + r²) + 2 cos(r/10⁴) = 2[θ'(r) + Re(1/(1/2+ir)) + cos(r/10⁴)]`
  (`lebesgueAtomWeilFunctional_weilTest_eq`, `lebesgueAtomDensity_eq`);
* `ρ ≥ 1/100` everywhere (`one_hundredth_le_lebesgueAtomDensity`), so the form is coercive:
  `Re W(f ⋆ f̃) ≥ (1/100) ∫ |f|²` (`lebesgueAtomWeilFunctional_coercive`), and `λ₀` is Weil-positive
  (`weilMeasurePositive_lebesgueAtom`).
-/

open Complex MeasureTheory Filter Set
open scoped Real ComplexConjugate FourierTransform
open Zeta23

noncomputable section

namespace RHTower.LebesgueAtomWeil

/-! ## The Weil functional of a measure weight system -/

/-- The prime-side integrand `x^{−1/2} (k(log x) + k(−log x))`. -/
def primeIntegrand (k : ℝ → ℂ) (x : ℝ) : ℂ :=
  (((Real.sqrt x)⁻¹ : ℝ) : ℂ) * (k (Real.log x) + k (-Real.log x))

/-- The Weil functional of the archimedean datum of `ζ` (pole weight one) for the signed weight system
`ν₊ − ν₋`. -/
def weilMeasureFunctional (νp νm : Measure ℝ) (k : ℝ → ℂ) : ℂ :=
  paperFT k (I / 2) + paperFT k (-I / 2)
  - ((∫ x, primeIntegrand k x ∂νp) - ∫ x, primeIntegrand k x ∂νm)
  + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)

/-- Weil positivity of the signed weight system `ν₊ − ν₋`: nonnegative real part on every
autocorrelation of a `C²` compactly supported test. -/
def WeilMeasurePositive (νp νm : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
    0 ≤ (weilMeasureFunctional νp νm (EF.weilTest f f)).re

/-! ## Integer weights -/

/-- The positive part `Σ_{n ≥ 2} lam(n)⁺ δ_n` of an integer weight system. -/
def natWeightsPos (lam : ℕ → ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ => ENNReal.ofReal (if 2 ≤ n then lam n else 0) • Measure.dirac (n : ℝ)

/-- The negative part `Σ_{n ≥ 2} lam(n)⁻ δ_n` of an integer weight system. -/
def natWeightsNeg (lam : ℕ → ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ => ENNReal.ofReal (if 2 ≤ n then -lam n else 0) • Measure.dirac (n : ℝ)

theorem primeIntegrand_natCast_eq_zero {k : ℝ → ℂ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0) {n : ℕ} (hn : N ≤ n) :
    primeIntegrand k n = 0 := by
  rw [primeIntegrand, (hN n hn).1, (hN n hn).2, add_zero, mul_zero]

/-- Integration of the prime integrand against a weighted counting measure. -/
theorem integral_primeIntegrand_sum {k : ℝ → ℂ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0) (c : ℕ → ℝ) :
    ∫ x, primeIntegrand k x ∂(Measure.sum fun n : ℕ => ENNReal.ofReal (c n) • Measure.dirac (n : ℝ))
      = ∑ n ∈ Finset.range N, ((max (c n) 0 : ℝ) : ℂ) * primeIntegrand k n := by
  set μ : ℕ → Measure ℝ := fun n => ENNReal.ofReal (c n) • Measure.dirac (n : ℝ) with hμ
  have hint : ∀ n, ∫ x, primeIntegrand k x ∂(μ n) = ((max (c n) 0 : ℝ) : ℂ) * primeIntegrand k n := by
    intro n
    rw [hμ, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal', Complex.real_smul]
  have hzero : ∀ n, n ∉ Finset.range N → ∫ x, primeIntegrand k x ∂(μ n) = 0 := by
    intro n hn
    rw [hint, primeIntegrand_natCast_eq_zero hN (by simpa using hn), mul_zero]
  have hInt : Integrable (primeIntegrand k) (Measure.sum μ) := by
    refine ⟨?_, ?_⟩
    · refine (aestronglyMeasurable_sum_measure_iff).mpr fun n => ?_
      exact aestronglyMeasurable_dirac.smul_measure _
    · rw [HasFiniteIntegral, lintegral_sum_measure]
      have hfin : ∀ n, n ∉ Finset.range N → ∫⁻ x, ‖primeIntegrand k x‖ₑ ∂(μ n) = 0 := by
        intro n hn
        rw [hμ, lintegral_smul_measure, lintegral_dirac,
          primeIntegrand_natCast_eq_zero hN (by simpa using hn), enorm_zero, smul_zero]
      rw [tsum_eq_sum (s := Finset.range N) hfin]
      refine ENNReal.sum_lt_top.mpr fun n _ => ?_
      rw [hμ, lintegral_smul_measure, lintegral_dirac]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top
  rw [integral_sum_measure hInt, tsum_eq_sum (s := Finset.range N) hzero]
  exact Finset.sum_congr rfl fun n _ => hint n

/-- **The measure functional extends the integer one.**  For the counting weights
`Σ_{n ≥ 2} lam(n) δ_n` the measure Weil functional is `weilFullFunctional lam` on every compactly
supported test. -/
theorem weilMeasureFunctional_natWeights (lam : ℕ → ℝ) {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    weilMeasureFunctional (natWeightsPos lam) (natWeightsNeg lam) k = weilFullFunctional lam k := by
  obtain ⟨N, hN⟩ := exists_forall_log_eq_zero hk
  have hsum : ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ)
      * (k (Real.log n) + k (-Real.log n))
      = ∑ n ∈ Finset.range N, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ)
      * (k (Real.log n) + k (-Real.log n)) := by
    refine tsum_eq_sum fun n hn => ?_
    have h := hN n (by simpa using hn)
    rw [h.1, h.2, add_zero, mul_zero]
  have hterm : ∀ n : ℕ, ((max (if 2 ≤ n then lam n else 0) 0 : ℝ) : ℂ) * primeIntegrand k n
      - ((max (if 2 ≤ n then -lam n else 0) 0 : ℝ) : ℂ) * primeIntegrand k n
      = ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
    intro n
    rw [primeIntegrand, ← sub_mul, ← mul_assoc, ← Complex.ofReal_sub, ← Complex.ofReal_mul]
    congr 2
    split_ifs with h2
    · rw [div_eq_mul_inv]
      rcases le_total 0 (lam n) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · simp
  unfold weilMeasureFunctional weilFullFunctional
  rw [natWeightsPos, natWeightsNeg, integral_primeIntegrand_sum hN, integral_primeIntegrand_sum hN,
    hsum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun n _ => hterm n]

/-! ## The Lebesgue-minus-atom system -/

/-- The atom position `e^{1/10000}`. -/
def atomPoint : ℝ := Real.exp (1 / 10000)

/-- The atom mass `e^{1/20000}`. -/
def atomMass : ℝ := Real.exp (1 / 20000)

/-- The Lebesgue part `1_{(1,∞)} dx`. -/
def lebesguePart : Measure ℝ := volume.restrict (Ioi 1)

/-- The atomic part `e^{1/20000} δ_{e^{1/10000}}`. -/
def atomPart : Measure ℝ := ENNReal.ofReal atomMass • Measure.dirac atomPoint

/-- The Weil functional of `λ₀ = 1_{(1,∞)} dx − e^{1/20000} δ_{e^{1/10000}}`. -/
def lebesgueAtomWeilFunctional (k : ℝ → ℂ) : ℂ :=
  weilMeasureFunctional lebesguePart atomPart k

/-- The Weil density `ρ(r) = γ(r) + 1/(1/4 + r²) + 2 cos(r/10⁴)` of `λ₀`. -/
def lebesgueAtomDensity (r : ℝ) : ℝ :=
  EF.gammaBracket r + 1 / (1 / 4 + r ^ 2) + 2 * Real.cos (r / 10000)

/-! ### The atom -/

theorem sqrt_atomPoint : Real.sqrt atomPoint = atomMass := by
  rw [atomPoint, atomMass, ← Real.exp_half]; norm_num

/-- The atom contributes `k(u₀) + k(−u₀)` with weight one. -/
theorem integral_atomPart (k : ℝ → ℂ) :
    ∫ x, primeIntegrand k x ∂atomPart = k (1 / 10000) + k (-(1 / 10000)) := by
  rw [atomPart, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (show 0 ≤ atomMass from (Real.exp_pos _).le), primeIntegrand,
    sqrt_atomPoint, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (show atomMass ≠ 0 from (Real.exp_pos _).ne'), Complex.ofReal_one, one_mul,
    atomPoint, Real.log_exp]

/-! ### The Lebesgue part -/

/-- `ĥ(i/2) = ∫ k(u) e^{−u/2} du`. -/
theorem paperFT_I_div_two (k : ℝ → ℂ) :
    paperFT k (I / 2) = ∫ u : ℝ, k u * (Real.exp (-u / 2) : ℂ) := by
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination ((u : ℂ) / 2) * Complex.I_mul_I

/-- `ĥ(−i/2) = ∫ k(u) e^{u/2} du`. -/
theorem paperFT_neg_I_div_two (k : ℝ → ℂ) :
    paperFT k (-I / 2) = ∫ u : ℝ, k u * (Real.exp (u / 2) : ℂ) := by
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (-(u : ℂ) / 2) * Complex.I_mul_I

/-- Change of variables `x = e^u` on `(1, ∞)`. -/
theorem integral_lebesguePart (k : ℝ → ℂ) :
    ∫ x, primeIntegrand k x ∂lebesguePart
      = ∫ u in Ioi (0 : ℝ), (Real.exp (u / 2) : ℂ) * (k u + k (-u)) := by
  have himg : Real.exp '' Ioi 0 = Ioi 1 := by rw [Real.image_exp_Ioi, Real.exp_zero]
  rw [lebesguePart, ← himg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [primeIntegrand, Real.log_exp]
  rw [abs_of_pos (Real.exp_pos u), ← Real.exp_half, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 3
  ring

/-- **The Lebesgue part cancels the growing half of the pole term.**
`ĥ(i/2) + ĥ(−i/2) − ∫_{(1,∞)} x^{−1/2}(k(log x) + k(−log x)) dx = ∫ e^{−|u|/2} k(u) du`. -/
theorem pole_sub_lebesgue_eq {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    paperFT k (I / 2) + paperFT k (-I / 2) - ∫ x, primeIntegrand k x ∂lebesguePart
      = ∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * k u := by
  have hint : ∀ g : ℝ → ℂ, Continuous g → Integrable fun u => g u * k u := fun g hg =>
    (hg.mul hk).integrable_of_hasCompactSupport (hkc.mul_left)
  set F : ℝ → ℂ := fun u => (Real.exp (|u| / 2) : ℂ) * k u with hF
  have hFi : Integrable F := hint _ (by fun_prop)
  have hA : Integrable fun u : ℝ => k u * (Real.exp (-u / 2) : ℂ) :=
    (hint (fun u : ℝ => (Real.exp (-u / 2) : ℂ)) (by fun_prop)).congr
      (Eventually.of_forall fun u => mul_comm _ _)
  have hB : Integrable fun u : ℝ => k u * (Real.exp (u / 2) : ℂ) :=
    (hint (fun u : ℝ => (Real.exp (u / 2) : ℂ)) (by fun_prop)).congr
      (Eventually.of_forall fun u => mul_comm _ _)
  have hAB : Integrable fun u : ℝ => k u * (Real.exp (-u / 2) : ℂ) + k u * (Real.exp (u / 2) : ℂ) :=
    hA.add hB
  -- the Lebesgue part is the pairing with `e^{|u|/2}`
  have hleb : ∫ x, primeIntegrand k x ∂lebesguePart = ∫ u, F u := by
    rw [integral_lebesguePart]
    have hsplit : ∫ u in Ioi (0 : ℝ), (Real.exp (u / 2) : ℂ) * (k u + k (-u))
        = (∫ u in Ioi (0 : ℝ), F u) + ∫ u in Ioi (0 : ℝ), F (-u) := by
      rw [← integral_add hFi.integrableOn (hFi.comp_neg.integrableOn)]
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      have hu' : 0 < u := hu
      simp only [hF, abs_neg, abs_of_pos hu']
      ring
    rw [hsplit, integral_comp_neg_Ioi, neg_zero, add_comm,
      ← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hFi.integrableOn
        hFi.integrableOn, Iic_union_Ioi, setIntegral_univ]
  calc paperFT k (I / 2) + paperFT k (-I / 2) - ∫ x, primeIntegrand k x ∂lebesguePart
      = ((∫ u, k u * (Real.exp (-u / 2) : ℂ)) + ∫ u, k u * (Real.exp (u / 2) : ℂ)) - ∫ u, F u := by
        rw [hleb, paperFT_I_div_two, paperFT_neg_I_div_two]
    _ = ∫ u, (k u * (Real.exp (-u / 2) : ℂ) + k u * (Real.exp (u / 2) : ℂ) - F u) := by
        rw [integral_sub hAB hFi, integral_add hA hB]
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [hF]
        rcases le_total 0 u with hu | hu
        · rw [abs_of_nonneg hu]
          push_cast; ring
        · rw [abs_of_nonpos hu]
          push_cast
          ring

/-! ### Spectral form -/

/-- `∫ e^{−|u|/2} e^{−iru} du = 1/(1/4 + r²)`. -/
theorem integral_expNegHalfAbs_mul_cexp (r : ℝ) :
    ∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * cexp (-I * r * u) = ((1 / (1 / 4 + r ^ 2) : ℝ) : ℂ) := by
  have h := GaloisForLFunctions.HTGeometry.fourierIntegral_exp_neg_mul_abs
    (μ := 1 / 2) (by norm_num) (r / (2 * π))
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden : (1 / 4 + (r : ℂ) ^ 2) ≠ 0 := by
    have : (1 / 4 + (r : ℂ) ^ 2) = ((1 / 4 + r ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_ne_zero]; positivity
  calc ∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * cexp (-I * r * u)
      = ∫ v : ℝ, cexp (↑(-2 * π * v * (r / (2 * π))) * I) • (Real.exp (-(1 / 2 * |v|)) : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [smul_eq_mul]
        rw [mul_comm]
        congr 2
        · push_cast; field_simp
        · ring
    _ = _ := by
        rw [h]
        push_cast
        field_simp
        ring

/-- **Spectral form of the `e^{−|u|/2}` pairing.**
`∫ e^{−|u|/2} k(u) du = (1/2π) ∫ ĥ(r)/(1/4 + r²) dr`. -/
theorem integral_expNegHalfAbs_mul_eq {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) :
    ∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * k u
      = (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * ((1 / (1 / 4 + r ^ 2) : ℝ) : ℂ) := by
  have hP : Integrable fun r : ℝ => paperFT k r := EF.integrable_paperFT_ofReal hFk
  have hE : Integrable fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) := by
    have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (show (0 : ℝ) < 1 / 2 by norm_num)
    refine (Integrable.ofReal (h.congr (Eventually.of_forall fun u => ?_)))
    simp only [pow_zero, one_mul]
    congr 1; ring
  have hPc : Continuous fun r : ℝ => paperFT k r := WeilHerglotz.continuous_paperFT_real hki
  have hprod : Integrable (Function.uncurry fun (u r : ℝ) =>
      (Real.exp (-|u| / 2) : ℂ) * (paperFT k r * cexp (-I * r * u))) (volume.prod volume) := by
    refine (hE.mul_prod hP).norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (Continuous.aestronglyMeasurable (by
        change Continuous fun p : ℝ × ℝ =>
          (Real.exp (-|p.1| / 2) : ℂ) * (paperFT k p.2 * cexp (-I * p.2 * p.1))
        have h2 : Continuous fun p : ℝ × ℝ => paperFT k (p.2 : ℂ) := hPc.comp continuous_snd
        fun_prop))
    · rcases p with ⟨u, r⟩
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [show ‖cexp (-I * (r : ℂ) * u)‖ = 1 by
        rw [Complex.norm_exp]; simp]
      rw [mul_one]
  calc ∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * k u
      = ∫ u : ℝ, (1 / (2 * π) : ℂ) *
          ∫ r : ℝ, (Real.exp (-|u| / 2) : ℂ) * (paperFT k r * cexp (-I * r * u)) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        rw [EF.paper_inversion hk hki hFk u, EF.cintegral_const_mul]
        ring
    _ = (1 / (2 * π) : ℂ) * ∫ r : ℝ, ∫ u : ℝ,
          (Real.exp (-|u| / 2) : ℂ) * (paperFT k r * cexp (-I * r * u)) := by
        rw [EF.cintegral_const_mul, integral_integral_swap hprod]
    _ = _ := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        simp only
        rw [← integral_expNegHalfAbs_mul_cexp r, ← EF.cintegral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        ring

/-- **The Weil functional of `λ₀` in spectral form.**  For a continuous compactly supported test with
integrable Fourier transform and integrable archimedean term,
`W_{λ₀}(k) = (1/2π) ∫ ĥ(r) ρ(r) dr`. -/
theorem lebesgueAtomWeilFunctional_eq {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k)
    (hFk : Integrable (𝓕 k)) (harch : Integrable fun r : ℝ => paperFT k r * (EF.gammaBracket r : ℂ)) :
    lebesgueAtomWeilFunctional k
      = (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (lebesgueAtomDensity r : ℂ) := by
  have hki : Integrable k := hk.integrable_of_hasCompactSupport hkc
  have hP : Integrable fun r : ℝ => paperFT k r := EF.integrable_paperFT_ofReal hFk
  have h1 : Integrable fun r : ℝ => paperFT k r * ((1 / (1 / 4 + r ^ 2) : ℝ) : ℂ) := by
    refine hP.mul_bdd (c := 4) ((Complex.continuous_ofReal.comp (continuous_const.div
      (by fun_prop) fun r => by positivity)).aestronglyMeasurable) (Eventually.of_forall fun r => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg r]
  have h2 := EF.integrable_paperFT_mul_cos hFk (1 / 10000)
  have hcos : ∀ r : ℝ, Real.cos (r / 10000) = Real.cos (r * (1 / 10000)) := fun r => by
    congr 1; ring
  have hsplit : ∫ r : ℝ, paperFT k r * (lebesgueAtomDensity r : ℂ)
      = (∫ r : ℝ, paperFT k r * ((1 / (1 / 4 + r ^ 2) : ℝ) : ℂ))
        + 2 * (∫ r : ℝ, paperFT k r * (Real.cos (r * (1 / 10000)) : ℂ))
        + ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ) := by
    have h12 : Integrable fun r : ℝ => paperFT k r * ((1 / (1 / 4 + r ^ 2) : ℝ) : ℂ)
        + 2 * (paperFT k r * (Real.cos (r * (1 / 10000)) : ℂ)) := h1.add (h2.const_mul 2)
    rw [← EF.cintegral_const_mul, ← integral_add h1 (h2.const_mul 2), ← integral_add h12 harch]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [lebesgueAtomDensity, hcos]
    push_cast
    ring
  have e1 := pole_sub_lebesgue_eq hk hkc
  rw [integral_expNegHalfAbs_mul_eq hk hki hFk] at e1
  have e2 := integral_atomPart k
  rw [EF.k_add_k_neg hk hki hFk] at e2
  unfold lebesgueAtomWeilFunctional weilMeasureFunctional
  rw [hsplit]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have e3 : (1 / π : ℂ) = (1 / (2 * π) : ℂ) * 2 := by field_simp
  rw [e3] at e2
  linear_combination e1 + e2

/-! ### The density -/

/-- `Re(1/(1/2 + ir)) = (1/2)/(1/4 + r²)`. -/
theorem re_one_div_half_add_mul_I (r : ℝ) :
    (1 / (((1 / 2 : ℝ) : ℂ) + (r : ℂ) * I)).re = (1 / 2) / (1 / 4 + r ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp
  ring

/-- **The density in Riemann–Siegel form**: `ρ(r) = 2[θ'(r) + Re(1/(1/2+ir)) + cos(r/10⁴)]`. -/
theorem lebesgueAtomDensity_eq (r : ℝ) :
    lebesgueAtomDensity r = 2 * ((1 / 2 : ℝ) *
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re
      - (1 / 2 : ℝ) * Real.log Real.pi + (1 / (((1 / 2 : ℝ) : ℂ) + (r : ℂ) * I)).re
      + Real.cos (r / 10000)) := by
  rw [lebesgueAtomDensity, WeilHerglotz.gammaBracket_eq, re_one_div_half_add_mul_I]
  have : (0 : ℝ) < 1 / 4 + r ^ 2 := by positivity
  field_simp

/-- **The Weil density of `λ₀` is at least `1/100`.** -/
theorem one_hundredth_le_lebesgueAtomDensity (r : ℝ) : 1 / 100 ≤ lebesgueAtomDensity r := by
  rw [lebesgueAtomDensity_eq]
  linarith [thetaDeriv_add_pole_add_atom_ge r]

/-! ### Autocorrelations -/

theorem integrable_paperFT_weilTest_mul_gammaBracket {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Integrable fun r : ℝ => paperFT (EF.weilTest f g) r * (EF.gammaBracket r : ℂ) := by
  obtain ⟨a, ha⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport hfc
  obtain ⟨b, hb⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport hgc
  set D := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hD
  set E := 4 * ((∫ u, ‖g u‖) + ∫ u, ‖deriv (deriv g) u‖) with hE
  set K := digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi + 1 with hK
  have hK0 : 0 ≤ K := by
    have := digammaVerticalGrowthConst_nonneg (c := 1 / 4) (by norm_num)
    have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hD0 : 0 ≤ D := by
    have h1 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv f) u‖ := integral_nonneg fun _ => norm_nonneg _
    rw [hD]; positivity
  have hE0 : 0 ≤ E := by
    have h1 : 0 ≤ ∫ u, ‖g u‖ := integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv g) u‖ := integral_nonneg fun _ => norm_nonneg _
    rw [hE]; positivity
  have hdf : ∀ r : ℝ, ‖paperFT f r‖ ≤ D / (1 + |r|) ^ 2 := fun r => by
    simpa [hD] using norm_paperFT_le_decay hf ha (r : ℂ)
  have hdg : ∀ r : ℝ, ‖paperFT g r‖ ≤ E / (1 + |r|) ^ 2 := fun r => by
    simpa [hE] using norm_paperFT_le_decay hg hb (r : ℂ)
  have hmaj : Integrable fun r : ℝ => D * E * (K + 1) * (1 + ‖r‖) ^ (-(3 : ℝ)) :=
    (integrable_one_add_norm (μ := volume) (E := ℝ) (r := 3) (by norm_num)).const_mul _
  refine hmaj.mono' ?_ (Eventually.of_forall fun r => ?_)
  · have hc := WeilHerglotz.continuous_paperFT_real
      ((EF.weilTest_contDiff hf hg.continuous hfc).continuous.integrable_of_hasCompactSupport
        (EF.weilTest_hasCompactSupport hfc hgc))
    exact (hc.mul (Complex.continuous_ofReal.comp
      WeilHerglotz.continuous_gammaBracket)).aestronglyMeasurable
  · rw [EF.paperFT_weilTest hf.continuous hg.continuous hfc hgc, Complex.conj_ofReal, norm_mul,
      norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hγ := WeilSpectral.abs_gammaBracket_le r
    rw [← hK] at hγ
    have hpos : 0 < 1 + |r| := by positivity
    have hrpow : (1 + |r|) ^ (-(3 : ℝ)) = 1 / (1 + |r|) ^ 3 := by
      rw [Real.rpow_neg hpos.le, one_div]
      norm_cast
    rw [hrpow]
    have hsq : ‖paperFT f r‖ * ‖paperFT g r‖ ≤ D * E / (1 + |r|) ^ 4 := by
      calc ‖paperFT f r‖ * ‖paperFT g r‖ ≤ (D / (1 + |r|) ^ 2) * (E / (1 + |r|) ^ 2) :=
            mul_le_mul (hdf r) (hdg r) (norm_nonneg _) (by positivity)
        _ = D * E / (1 + |r|) ^ 4 := by field_simp
    have hγ' : |EF.gammaBracket r| ≤ (K + 1) * (1 + |r|) := by nlinarith [abs_nonneg r]
    calc ‖paperFT f r‖ * ‖paperFT g r‖ * |EF.gammaBracket r|
        ≤ D * E / (1 + |r|) ^ 4 * ((K + 1) * (1 + |r|)) :=
          mul_le_mul hsq hγ' (abs_nonneg _) (by positivity)
      _ = D * E * (K + 1) * (1 / (1 + |r|) ^ 3) := by field_simp

/-- **The Weil distribution of `λ₀` is absolutely continuous with density `ρ`.**  For all `C²`
compactly supported tests, `W_{λ₀}(f ⋆ g̃) = (1/2π) ∫ f̂(r) conj(ĝ(r)) ρ(r) dr`. -/
theorem lebesgueAtomWeilFunctional_weilTest_eq {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    lebesgueAtomWeilFunctional (EF.weilTest f g)
      = (1 / (2 * π) : ℂ) *
        ∫ r : ℝ, paperFT f r * conj (paperFT g r) * (lebesgueAtomDensity r : ℂ) := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f g) := EF.weilTest_contDiff hf hg.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f g) := EF.weilTest_hasCompactSupport hfc hgc
  rw [lebesgueAtomWeilFunctional_eq hkd.continuous hkc
    (EF.integrable_fourier_of_contDiff_two hkd hkc)
    (integrable_paperFT_weilTest_mul_gammaBracket hf hfc hg hgc)]
  congr 2
  funext r
  rw [EF.paperFT_weilTest hf.continuous hg.continuous hfc hgc, Complex.conj_ofReal]

/-- Plancherel through inversion: `(1/2π) ∫ |f̂|² = ∫ |f|²`. -/
theorem integral_norm_sq_paperFT_eq {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 = ∫ u : ℝ, ‖f u‖ ^ 2 := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hinv := EF.paper_inversion hkd.continuous (hkd.continuous.integrable_of_hasCompactSupport hkc)
    (EF.integrable_fourier_of_contDiff_two hkd hkc) 0
  rw [WeilSpectral.weilTest_apply] at hinv
  have hl : ∫ u : ℝ, f u * conj (f (u - 0)) = ((∫ u : ℝ, ‖f u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hr : ∫ r : ℝ, paperFT (EF.weilTest f f) r * cexp (-I * r * ((0 : ℝ) : ℂ))
      = ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hl, hr] at hinv
  have h := congrArg Complex.re hinv
  simp only [Complex.ofReal_re] at h
  rw [h]
  rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- **Coercivity.**  `Re W_{λ₀}(f ⋆ f̃) ≥ (1/100) ∫ |f|²` for every `C²` compactly supported `f`. -/
theorem lebesgueAtomWeilFunctional_coercive {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (1 / 100) * ∫ u : ℝ, ‖f u‖ ^ 2 ≤ (lebesgueAtomWeilFunctional (EF.weilTest f f)).re := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hFk := EF.integrable_fourier_of_contDiff_two hkd hkc
  have hP : Integrable fun r : ℝ => paperFT (EF.weilTest f f) r := EF.integrable_paperFT_ofReal hFk
  have hPn : ∀ r : ℝ, paperFT (EF.weilTest f f) r = ((‖paperFT f r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq : Integrable fun r : ℝ => ‖paperFT f r‖ ^ 2 := by
    have := hP.norm
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only
    rw [hPn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have harch := integrable_paperFT_weilTest_mul_gammaBracket hf hfc hf hfc
  have hρ : Integrable fun r : ℝ => ‖paperFT f r‖ ^ 2 * lebesgueAtomDensity r := by
    have h1 : Integrable fun r : ℝ => paperFT (EF.weilTest f f) r * (lebesgueAtomDensity r : ℂ) := by
      have hb : Integrable fun r : ℝ => paperFT (EF.weilTest f f) r *
          (((1 / (1 / 4 + r ^ 2) : ℝ) : ℂ) + 2 * (Real.cos (r / 10000) : ℂ)) := by
        refine hP.mul_bdd (c := 6) (by fun_prop) (Eventually.of_forall fun r => ?_)
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_mul,
          Complex.norm_real, Real.norm_eq_abs]
        have h1 : (1 / 4 + r ^ 2)⁻¹ ≤ 4 := by
          rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith [sq_nonneg r]
        have h2 := Real.abs_cos_le_one (r / 10000)
        norm_num
        linarith
      refine (hb.add harch).congr (Eventually.of_forall fun r => ?_)
      simp only [Pi.add_apply, lebesgueAtomDensity]
      push_cast
      ring
    have := h1.re
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only
    rw [hPn, ← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  have hW := lebesgueAtomWeilFunctional_eq hkd.continuous hkc hFk harch
  have hre : (lebesgueAtomWeilFunctional (EF.weilTest f f)).re
      = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * lebesgueAtomDensity r := by
    rw [hW]
    have : ∫ r : ℝ, paperFT (EF.weilTest f f) r * (lebesgueAtomDensity r : ℂ)
        = ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 * lebesgueAtomDensity r : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only
      rw [hPn]; push_cast; ring
    rw [this, show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hmono : ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (1 / 100)
      ≤ ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * lebesgueAtomDensity r :=
    integral_mono (hsq.mul_const _) hρ fun r =>
      mul_le_mul_of_nonneg_left (one_hundredth_le_lebesgueAtomDensity r) (by positivity)
  rw [integral_mul_const] at hmono
  rw [hre, ← integral_norm_sq_paperFT_eq hf hfc]
  have hπ : 0 < 1 / (2 * π) := by positivity
  nlinarith

/-- **`λ₀ = 1_{(1,∞)} dx − e^{1/20000} δ_{e^{1/10000}}` is Weil-positive** for the archimedean datum
of `ζ` with pole weight one. -/
theorem weilMeasurePositive_lebesgueAtom : WeilMeasurePositive lebesguePart atomPart := by
  intro f hf hfc
  have h := lebesgueAtomWeilFunctional_coercive hf hfc
  have h0 : 0 ≤ ∫ u : ℝ, ‖f u‖ ^ 2 := integral_nonneg fun _ => by positivity
  exact le_trans (by positivity) h

end RHTower.LebesgueAtomWeil
