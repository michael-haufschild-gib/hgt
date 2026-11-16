import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExponentialProbesLieInTheEnergyDomain
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateSatisfiesTheWeakEquation
import GaloisForLFunctions.RHTower.PoissonDigammaReproduction
import GaloisForLFunctions.RHTower.XiWeilTwoChannelResolvent
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit

/-!
# Weil's form on exponential probes is the Carathéodory kernel of `ξ'/ξ`

For `p, q > 4` each part of Weil's form on the probes `e_p, e_q` is explicit:

* pole part: `(1/(p+½) + 1/(p-½) + 1/(q+½) + 1/(q-½))/(p+q)`;
* prime part: `(Σ Λ(n) n^{-½-p} + Σ Λ(n) n^{-½-q})/(p+q)`;
* Gamma part: the Poisson integral of `Re ψ(¼ + ir/2) - log π` at heights `p` and `q`,
  i.e. `(Re ψ(¼+p/2) + Re ψ(¼+q/2) - 2 log π)/(2(p+q))`.

Their sum is `(D(p) + D(q))/(p+q)` with `D = (log ξ)'(½ + ·)`, the Carathéodory kernel whose
positivity on `Re p > 0` is RH. By the two-channel resolvent identity the same number is the
zero sum `Σ_ρ 1/((p + ρ - ½)(q - ρ + ½))`: Weil's explicit formula holds on the probe span.
The confinement adds `a/(p + q - 8)`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

/-! ### The prime part -/

theorem integral_probe_mul_probe_sub {p q L : ℝ} (hpq : 0 < p + q) (hL : 0 ≤ L) :
    (∫ t, probe p t * probe q (t - L)) = Real.exp (-(q * L)) / (p + q) := by
  have hpt : (fun t => probe p t * probe q (t - L)) =
      fun t => Real.exp (-(q * L)) * probe (p + q) t := by
    funext t
    rcases lt_or_ge t 0 with ht | ht
    · rw [probe_of_neg ht, probe_of_neg (by linarith : t - L < 0), probe_of_neg ht,
        ← Real.exp_add, ← Real.exp_add]
      ring_nf
    · rw [probe_of_nonneg ht, probe_of_nonneg ht, zero_mul, mul_zero]
  rw [hpt, integral_const_mul, integral_probe hpq]
  ring

theorem integral_probe_mul_probe_add {p q L : ℝ} (hpq : 0 < p + q) (hL : 0 ≤ L) :
    (∫ t, probe p t * probe q (t + L)) = Real.exp (-(p * L)) / (p + q) := by
  have h := integral_add_right_eq_self (μ := volume) (fun s => probe p (s - L) * probe q s) L
  simp only [add_sub_cancel_right] at h
  rw [h]
  simp_rw [mul_comm (probe p _) (probe q _)]
  rw [integral_probe_mul_probe_sub (by linarith) hL, add_comm q p]

/-- One prime term of two probes. -/
theorem primePairTerm_probe {p q : ℝ} (hpq : 0 < p + q) (n : ℕ) :
    primePairTerm (probe p) (probe q) n = vonMangoldtAtom n *
      (Real.exp (-(q * Real.log n)) + Real.exp (-(p * Real.log n))) / (p + q) := by
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  unfold primePairTerm
  rw [integral_probe_mul_probe_sub hpq hL, integral_probe_mul_probe_add hpq hL]
  ring

/-- The prime coefficient at a probe is the von Mangoldt Dirichlet coefficient at `½ + p`. -/
theorem vonMangoldtAtom_mul_exp_eq (p : ℝ) (n : ℕ) :
    vonMangoldtAtom n * Real.exp (-(p * Real.log n)) =
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p) := by
  unfold vonMangoldtAtom
  split_ifs with h
  · have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [Real.rpow_add hn, Real.sqrt_eq_rpow, show -(p * Real.log n) = Real.log n * (-p) by ring,
      ← Real.rpow_def_of_pos hn, Real.rpow_neg hn.le]
    field_simp
  · interval_cases n <;> simp

theorem summable_vonMangoldt_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
  rw [← Complex.summable_ofReal]
  refine h.congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  · rw [LSeries.term_of_ne_zero h0, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rfl

/-- The prime part on two probes is the sum of the two von Mangoldt series at `½ + p`, `½ + q`. -/
theorem primeMixedForm_probe {p q : ℝ} (hp : 1 / 2 < p) (hq : 1 / 2 < q) :
    primeMixedForm (probe p) (probe q) =
      ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p)) +
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + q)) / (p + q) := by
  have hpq : 0 < p + q := by linarith
  have sp := summable_vonMangoldt_div_rpow (σ := 1 / 2 + p) (by linarith)
  have sq := summable_vonMangoldt_div_rpow (σ := 1 / 2 + q) (by linarith)
  unfold primeMixedForm
  simp_rw [primePairTerm_probe hpq, mul_add, vonMangoldtAtom_mul_exp_eq]
  rw [tsum_div_const, tsum_add sq sp, add_comm]

/-! ### The Gamma part -/

theorem re_one_div_probe (p r : ℝ) :
    (1 / ((p : ℂ) + I * r)).re = p / (p ^ 2 + r ^ 2) := by
  simp [Complex.div_re, Complex.normSq_apply]
  ring

theorem im_one_div_probe (p r : ℝ) :
    (1 / ((p : ℂ) + I * r)).im = -r / (p ^ 2 + r ^ 2) := by
  simp [Complex.div_im, Complex.normSq_apply]
  ring

/-- The Fourier pairing of two probes splits into two Poisson kernels. -/
theorem gammaFourierPair_probe {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (r : ℝ) :
    gammaFourierPair (probe p) (probe q) r =
      (p / (p ^ 2 + r ^ 2) + q / (q ^ 2 + r ^ 2)) / (p + q) := by
  unfold gammaFourierPair
  rw [paperFT_probe (z := (r : ℂ)) (by simpa using hp),
    paperFT_probe (z := (r : ℂ)) (by simpa using hq), re_one_div_probe, re_one_div_probe,
    im_one_div_probe, im_one_div_probe]
  have h1 : 0 < p ^ 2 + r ^ 2 := by positivity
  have h2 : 0 < q ^ 2 + r ^ 2 := by positivity
  field_simp
  ring

theorem gammaBracket_eq_re_digamma_half (r : ℝ) :
    EF.gammaBracket r = (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re -
      Real.log Real.pi := by
  unfold EF.gammaBracket
  congr 3
  push_cast
  ring

theorem integrable_poissonWeight_mul_gammaBracket {p : ℝ} (hp : 0 < p) :
    Integrable fun r => poissonWeight p r * EF.gammaBracket r := by
  have h1 := integrable_poissonWeight_mul_re_digamma_half hp (c := 1 / 4) (by norm_num)
  have h2 := (integrable_poissonWeight hp).mul_const (Real.log Real.pi)
  refine (h1.sub h2).congr (Eventually.of_forall fun r => ?_)
  simp only [Pi.sub_apply, gammaBracket_eq_re_digamma_half]
  ring

/-- The Gamma Poisson integral: `(1/2π) ∫ p/(p²+r²) γ(r) dr = (Re ψ(¼+p/2) - log π)/2`. -/
theorem gamma_poisson_probe {p : ℝ} (hp : 0 < p) :
    1 / (2 * Real.pi) * (∫ r, p / (p ^ 2 + r ^ 2) * EF.gammaBracket r) =
      ((Complex.digamma ((1 / 4 + p / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hpt : (fun r => p / (p ^ 2 + r ^ 2) * EF.gammaBracket r) = fun r =>
      Real.pi * (poissonWeight p r * ((Complex.digamma (((1 / 4 : ℝ) : ℂ) +
        ((r / 2 : ℝ) : ℂ) * I)).re + Real.eulerMascheroniConstant) -
        (Real.eulerMascheroniConstant + Real.log Real.pi) * poissonWeight p r) := by
    funext r
    rw [gammaBracket_eq_re_digamma_half, poissonWeight]
    have : 0 < p ^ 2 + r ^ 2 := by positivity
    field_simp
    ring
  have hi1 := (integrable_poissonWeight_mul_re_digamma_half hp (c := 1 / 4) (by norm_num)).add
    ((integrable_poissonWeight hp).mul_const Real.eulerMascheroniConstant)
  have hi1' : Integrable fun r => poissonWeight p r * ((Complex.digamma (((1 / 4 : ℝ) : ℂ) +
      ((r / 2 : ℝ) : ℂ) * I)).re + Real.eulerMascheroniConstant) :=
    hi1.congr (Eventually.of_forall fun r => by simp only [Pi.add_apply]; ring)
  have hi2 := (integrable_poissonWeight hp).const_mul
    (Real.eulerMascheroniConstant + Real.log Real.pi)
  rw [hpt, integral_const_mul, integral_sub hi1' hi2, integral_const_mul,
    integral_poissonWeight_mul_re_digamma_add_euler hp (by norm_num), integral_poissonWeight hp]
  field_simp
  ring

/-- The Gamma part on two probes. -/
theorem gammaMixedForm_probe {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    gammaMixedForm (probe p) (probe q) =
      (((Complex.digamma ((1 / 4 + p / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 +
        ((Complex.digamma ((1 / 4 + q / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2) / (p + q) := by
  have hpq : 0 < p + q := by linarith
  have ip : Integrable fun r => p / (p ^ 2 + r ^ 2) * EF.gammaBracket r :=
    ((integrable_poissonWeight_mul_gammaBracket hp).const_mul Real.pi).congr
      (Eventually.of_forall fun r => by
        rw [poissonWeight]; have : 0 < p ^ 2 + r ^ 2 := by positivity
        field_simp)
  have iq : Integrable fun r => q / (q ^ 2 + r ^ 2) * EF.gammaBracket r :=
    ((integrable_poissonWeight_mul_gammaBracket hq).const_mul Real.pi).congr
      (Eventually.of_forall fun r => by
        rw [poissonWeight]; have : 0 < q ^ 2 + r ^ 2 := by positivity
        field_simp)
  unfold gammaMixedForm
  simp_rw [gammaFourierPair_probe hp hq, div_mul_eq_mul_div, add_mul]
  rw [integral_div, integral_add ip iq, ← gamma_poisson_probe hp, ← gamma_poisson_probe hq]
  ring

/-! ### The pole part -/

theorem polePart_probe {p q : ℝ} (hp : 1 / 2 < p) (hq : 1 / 2 < q) :
    2 * coshHalfMoment (probe p) * coshHalfMoment (probe q) -
        2 * sinhHalfMoment (probe p) * sinhHalfMoment (probe q) =
      (1 / (p + 1 / 2) + 1 / (p - 1 / 2) + (1 / (q + 1 / 2) + 1 / (q - 1 / 2))) / (p + q) := by
  rw [coshHalfMoment_probe hp, coshHalfMoment_probe hq, sinhHalfMoment_probe hp,
    sinhHalfMoment_probe hq]
  have h1 : p + 1 / 2 ≠ 0 := by linarith
  have h2 : p - 1 / 2 ≠ 0 := by linarith
  have h3 : q + 1 / 2 ≠ 0 := by linarith
  have h4 : q - 1 / 2 ≠ 0 := by linarith
  have h5 : p + q ≠ 0 := by linarith
  field_simp
  ring

/-! ### The probe symbol and the kernel -/

/-- The probe symbol `D(p) = 1/(p+½) + 1/(p-½) + (Re ψ(¼+p/2) - log π)/2 - Σ Λ(n) n^{-½-p}`. -/
def probeSymbol (p : ℝ) : ℝ :=
  1 / (p + 1 / 2) + 1 / (p - 1 / 2) +
    ((Complex.digamma ((1 / 4 + p / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 -
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p)

/-- On real points the centred logarithmic derivative of `ξ` is real. -/
theorem logDeriv_xiCent_ofReal_eq_re {p : ℝ} (hp : 1 / 2 < p) :
    logDeriv xiCent (p : ℂ) = ((logDeriv xiCent (p : ℂ)).re : ℂ) := by
  have h := logDeriv_xiCent_conj (v := (p : ℂ)) (by simpa using hp)
  rw [Complex.conj_ofReal] at h
  exact (Complex.conj_eq_iff_re.mp h.symm)

/-- The probe symbol is `(log ξ)'(½ + p)`. -/
theorem probeSymbol_eq_logDeriv_xiCent {p : ℝ} (hp : 1 / 2 < p) :
    (probeSymbol p : ℂ) = logDeriv xiCent (p : ℂ) := by
  rw [logDeriv_xiCent_ofReal_eq_re hp, logDeriv_xiCent_eq_eulerPresentation (by simpa using hp)]
  congr 1
  have hG := logDeriv_Gammaℝ_eq (s := (1 : ℂ) / 2 + p) (by simp; linarith)
  have hL := LSeries_vonMangoldt_ofReal (1 / 2 + p)
  have hdg : ((1 : ℂ) / 2 + p) / 2 = ((1 / 4 + p / 2 : ℝ) : ℂ) := by push_cast; ring
  have hs : (1 : ℂ) / 2 + p = ((1 / 2 + p : ℝ) : ℂ) := by push_cast; ring
  rw [hG, hdg, hs, hL]
  unfold probeSymbol
  have hre1 : (((1 / 2 + p : ℝ) : ℂ))⁻¹.re = 1 / (p + 1 / 2) := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re]; ring_nf
  have hre2 : (((1 / 2 + p : ℝ) : ℂ) - 1)⁻¹.re = 1 / (p - 1 / 2) := by
    rw [show ((1 / 2 + p : ℝ) : ℂ) - 1 = ((p - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  simp only [Complex.add_re, Complex.sub_re, hre1, hre2, Complex.neg_re, Complex.div_re,
    Complex.ofReal_re, Complex.ofReal_im]
  simp [Complex.normSq_apply]
  ring

/-- Bare mixed Weil form on the half-line: Gamma part minus prime part plus pole part. -/
def bareMixedEnergy (F G : ℝ → ℝ) : ℝ :=
  gammaMixedForm F G - (primeMixedForm F G + primeMixedForm G F) / 2 +
    (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G)

theorem criticalHalfLineMixedEnergy_eq_bare_add (R : ℝ) (F G : ℝ → ℝ) :
    criticalHalfLineMixedEnergy R F G = bareMixedEnergy F G +
      criticalAliasCoefficient R * (∫ u in Iio 0, F u * G u * Real.exp (-(8 * u))) := rfl

/-- **The probe kernel.** Weil's bare form on two probes is `(D(p) + D(q))/(p + q)`. -/
theorem bareMixedEnergy_probe {p q : ℝ} (hp : 1 / 2 < p) (hq : 1 / 2 < q) :
    bareMixedEnergy (probe p) (probe q) = (probeSymbol p + probeSymbol q) / (p + q) := by
  unfold bareMixedEnergy
  rw [gammaMixedForm_probe (by linarith) (by linarith), primeMixedForm_probe hp hq,
    primeMixedForm_probe hq hp, polePart_probe hp hq]
  unfold probeSymbol
  have h5 : p + q ≠ 0 := by linarith
  rw [add_comm q p]
  field_simp
  ring

/-- **The confined probe kernel** `K_a(p,q) = (D(p)+D(q))/(p+q) + a/(p+q-8)`. -/
theorem criticalHalfLineMixedEnergy_probe (R : ℝ) {p q : ℝ} (hp : 4 < p) (hq : 4 < q) :
    criticalHalfLineMixedEnergy R (probe p) (probe q) =
      (probeSymbol p + probeSymbol q) / (p + q) + criticalAliasCoefficient R / (p + q - 8) := by
  rw [criticalHalfLineMixedEnergy_eq_bare_add, bareMixedEnergy_probe (by linarith) (by linarith),
    confinement_probe_probe (by linarith)]
  ring

/-- The probe kernel is the Carathéodory kernel of the centred logarithmic derivative of `ξ`. -/
theorem bareMixedEnergy_probe_eq_criticalLogDerivKernel {p q : ℝ} (hp : 1 / 2 < p)
    (hq : 1 / 2 < q) :
    (bareMixedEnergy (probe p) (probe q) : ℂ) = criticalLogDerivKernel (p : ℂ) (q : ℂ) := by
  rw [bareMixedEnergy_probe hp hq, criticalLogDerivKernel, Complex.conj_ofReal,
    ← probeSymbol_eq_logDeriv_xiCent hp, ← probeSymbol_eq_logDeriv_xiCent hq,
    Complex.conj_ofReal]
  push_cast
  rfl

/-- **The explicit formula on probes.** Weil's bare form on two probes equals the zero side
`Σ_ρ ½ (L e_p(z) L e_q(-z) + L e_p(-z) L e_q(z))` over the multiplicity-exact divisor, with
`z = ρ - ½` written in centred spectral coordinates. -/
theorem bareMixedEnergy_probe_eq_zeroSide {p q : ℝ} (hp : 1 / 2 < p) (hq : 1 / 2 < q) :
    (bareMixedEnergy (probe p) (probe q) : ℂ) =
      (xiWeilPolarization (weilResolventPlus p) (weilResolventPlus q) +
        xiWeilPolarization (weilResolventMinus p) (weilResolventMinus q)) / 2 := by
  rw [bareMixedEnergy_probe_eq_criticalLogDerivKernel hp hq,
    criticalLogDerivKernel_eq_resolventChannels (by simpa using hp) (by simpa using hq)]

end GaloisForLFunctions.ExclusionOfTheCriticalState
