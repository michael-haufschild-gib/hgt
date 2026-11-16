import GaloisForLFunctions.ExclusionOfTheCriticalState.TheGammaPairingIsTheFunctionalEquationOnTheStrip
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.ZetaSquareStirlingCarrier

/-!
# The transform of the state is meromorphic in the plane

The state equation continues `L F` by `L F(w) = -R(w + 8)/a`. The remainder `R` has three
expressions, each holomorphic on its own region, which agree on the overlaps:

* right of `Re p = -½`: the Lévy form `Γ F + L F · ζ'/ζ(½+p) - T F + poles`;
* on the strip `-4 < Re p < ½`: `-L F · ζ'/ζ(½-p) + J F - T F + poles`, by the functional equation in
  Lévy form (the Gamma pairing is the reflected Euler term plus the head term `J F`);
* left of `Re p = -½`: `J F(p) + Ŝ F(p) + L F(½)/(p-½) + L F(-½)/(p+½)`, where
  `Ŝ F(p) = Σ Λ(n) n^{p-½} ∫_{-log n}^0 F(u) e^{pu} du`. Here `ζ'/ζ(½-p)` is the Dirichlet series
  of `Λ`, and the Euler parts of the reflected term and of the prime tail cancel exactly.

The glued function is holomorphic in the whole plane except at the points `ρ - 17/2`, `ρ` a zero
of `ζ` in the critical strip, where the residue is `-m_ρ L F(ρ - ½)/a`, and it is bounded on every
half-plane `Re w ≤ -17/2 - δ`. Left of the strip the transform of the state is the prime side seen
from beyond the wall: the head term and the prime heads only.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The Euler sum as a Dirichlet series -/

theorem vonMangoldtAtom_mul_cexp_eq_term (p : ℂ) (n : ℕ) :
    (vonMangoldtAtom n : ℂ) * cexp (p * Real.log n) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 - p) n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp [vonMangoldtAtom, LSeries.term]
  · have hn0 : n ≠ 0 := by omega
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [LSeries.term_of_ne_zero hn0]
    unfold vonMangoldtAtom
    rw [if_pos hn, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0), ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hpos.le, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
    push_cast
    rw [div_mul_eq_mul_div, div_eq_div_iff (Complex.exp_ne_zero _) (Complex.exp_ne_zero _),
      mul_assoc, ← Complex.exp_add]
    congr 2
    ring

theorem summable_vonMangoldtAtom_mul_cexp {p : ℂ} (hp : p.re < -(1 / 2)) :
    Summable fun n : ℕ => (vonMangoldtAtom n : ℂ) * cexp (p * Real.log n) :=
  (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 1 / 2 - p) (by simp; linarith)).congr
    fun n => (vonMangoldtAtom_mul_cexp_eq_term p n).symm

/-- Left of the strip the Euler sum is `-ζ'/ζ(½ - p)`. -/
theorem tsum_vonMangoldtAtom_mul_cexp {p : ℂ} (hp : p.re < -(1 / 2)) :
    ∑' n : ℕ, (vonMangoldtAtom n : ℂ) * cexp (p * Real.log n) =
      -(deriv riemannZeta (1 / 2 - p) / riemannZeta (1 / 2 - p)) := by
  have hs : 1 < (1 / 2 - p).re := by simp; linarith
  have h : (∑' n : ℕ, (vonMangoldtAtom n : ℂ) * cexp (p * Real.log n)) =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 - p) := by
    unfold LSeries; exact tsum_congr (vonMangoldtAtom_mul_cexp_eq_term p)
  rw [h, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div]

/-! ### The prime heads -/

/-- The prime heads `Ŝ F(p) = Σ_n Λ(n) n^{p-½} H_{log n}(p)`: the prime power `n` sees the profile on
`(-log n, 0)` only. -/
def primeHead (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  ∑' n : ℕ, (vonMangoldtAtom n : ℂ) * (cexp (p * Real.log n) * levyHead F p (Real.log n))

theorem norm_primeHead_term_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {σ : ℝ}
    (hσ : -4 < σ) {p : ℂ} (hp : p.re ≤ σ) (n : ℕ) :
    ‖(vonMangoldtAtom n : ℂ) * (cexp (p * Real.log n) * levyHead F p (Real.log n))‖ ≤
      vonMangoldtAtom n * Real.exp (σ * Real.log n) * ∫ u, |F u| * Real.exp (σ * u) := by
  set L := Real.log n with _hLdef
  have hatom : 0 ≤ vonMangoldtAtom n := by
    unfold vonMangoldtAtom; split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  have hint : Integrable fun u => |F u| * Real.exp (σ * u) := integrable_abs_mul_exp_of_domain hF hσ
  have hpt : ∀ u : ℝ, Real.exp (σ * L) * (|F u| * Real.exp (σ * u)) =
      |F u| * Real.exp (σ * (u + L)) := fun u => by rw [mul_add, Real.exp_add]; ring
  have hint' : Integrable fun u => |F u| * Real.exp (σ * (u + L)) :=
    (hint.const_mul (Real.exp (σ * L))).congr (Eventually.of_forall hpt)
  have h1 : ‖cexp (p * L) * levyHead F p L‖ ≤ ∫ u in Ici (-L), |F u| * Real.exp (σ * (u + L)) := by
    unfold levyHead
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le hint'.integrableOn
      ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
    have hu' : -L ≤ u := hu
    rw [norm_mul, norm_mul, norm_cexp_mul_ofReal, norm_cexp_mul_ofReal, Complex.norm_real,
      Real.norm_eq_abs, ← mul_assoc, ← Real.exp_add, mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hp) (by linarith : (0 : ℝ) ≤ u + L)])) (abs_nonneg _)
  have h2 : (∫ u in Ici (-L), |F u| * Real.exp (σ * (u + L))) ≤
      Real.exp (σ * L) * ∫ u, |F u| * Real.exp (σ * u) := by
    refine (setIntegral_le_integral hint' (Eventually.of_forall fun u => by positivity)).trans_eq ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => (hpt u).symm)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hatom, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) hatom

theorem summable_primeHead_bound {F : ℝ → ℝ} {σ : ℝ} (hσ : σ < -(1 / 2)) :
    Summable fun n : ℕ =>
      vonMangoldtAtom n * Real.exp (σ * Real.log n) * ∫ u, |F u| * Real.exp (σ * u) := by
  have h := (summable_vonMangoldt_div_rpow (σ := 1 / 2 + -σ) (by linarith)).mul_right
    (∫ u, |F u| * Real.exp (σ * u))
  refine h.congr fun n => ?_
  rw [← vonMangoldtAtom_mul_exp_eq, show -(-σ * Real.log n) = σ * Real.log n by ring]

/-- The prime heads are holomorphic left of the strip. -/
theorem differentiableOn_primeHead {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    DifferentiableOn ℂ (primeHead F) {p : ℂ | p.re < -(1 / 2)} := by
  intro p₀ hp₀
  have hp₀' : p₀.re < -(1 / 2) := hp₀
  set σ := (max p₀.re (-2) + -(1 / 2)) / 2 with hσdef
  have hσ4 : -4 < σ := by rw [hσdef]; have := le_max_right p₀.re (-2); linarith
  have hσh : σ < -(1 / 2) := by
    rw [hσdef]; have := max_lt hp₀' (by norm_num : (-2 : ℝ) < -(1 / 2)); linarith
  have hσp : p₀.re < σ := by rw [hσdef]; have := le_max_left p₀.re (-2); linarith
  have hU : IsOpen {p : ℂ | p.re < σ} := isOpen_lt Complex.continuous_re continuous_const
  have hd : DifferentiableOn ℂ (primeHead F) {p : ℂ | p.re < σ} :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_primeHead_bound hσh)
      (fun n => (((by fun_prop : Differentiable ℂ fun p : ℂ => cexp (p * Real.log n)).mul
        (differentiable_levyHead hF (Real.log n))).const_mul _).differentiableOn) hU
      (fun n p hp => norm_primeHead_term_le hF hσ4 (le_of_lt hp) n)
  exact (hd.differentiableAt (hU.mem_nhds hσp)).differentiableWithinAt

/-- **The prime tail left of the strip.** For `-4 < Re p < -½`,
`T F(p) = -L F(p) ζ'/ζ(½ - p) - Ŝ F(p)`. -/
theorem stateTail_eq_left {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp4 : -4 < p.re) (hp : p.re < -(1 / 2)) :
    stateTail F p = -(negativeHalfLineLaplace (cx F) p *
      (deriv riemannZeta (1 / 2 - p) / riemannZeta (1 / 2 - p))) - primeHead F p := by
  have hterm : ∀ n : ℕ, (vonMangoldtAtom n : ℂ) * (cexp (p * Real.log n) *
      ∫ u in Iio (-Real.log n), (F u : ℂ) * cexp (p * u)) =
      (vonMangoldtAtom n : ℂ) * cexp (p * Real.log n) * negativeHalfLineLaplace (cx F) p -
        (vonMangoldtAtom n : ℂ) * (cexp (p * Real.log n) * levyHead F p (Real.log n)) := by
    intro n
    have hs := laplace_eq_levyTail_add hF hp4 (Real.log n)
    have ht : (∫ u in Iio (-Real.log n), (F u : ℂ) * cexp (p * u)) =
        negativeHalfLineLaplace (cx F) p - levyHead F p (Real.log n) := by
      rw [hs]
      unfold levyTail levyHead
      rw [add_sub_cancel_right]
      exact integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)
    rw [ht]; ring
  have hs1 : Summable fun n : ℕ =>
      (vonMangoldtAtom n : ℂ) * cexp (p * Real.log n) * negativeHalfLineLaplace (cx F) p :=
    (summable_vonMangoldtAtom_mul_cexp hp).mul_right _
  have hs2 : Summable fun n : ℕ =>
      (vonMangoldtAtom n : ℂ) * (cexp (p * Real.log n) * levyHead F p (Real.log n)) :=
    Summable.of_norm_bounded (summable_primeHead_bound (F := F) hp)
      (fun n => norm_primeHead_term_le hF hp4 le_rfl n)
  unfold stateTail primeHead
  simp_rw [hterm]
  rw [hs1.tsum_sub hs2, tsum_mul_right, tsum_vonMangoldtAtom_mul_cexp hp]
  ring

/-! ### Three forms of the remainder -/

/-- The remainder on the strip `-4 < Re p < ½`, written with the reflected Euler factor. -/
def stripRemainder (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  -(negativeHalfLineLaplace (cx F) p * logDeriv zetaEntire (1 / 2 - p)) -
    dslope (negativeHalfLineLaplace (cx F)) (-(1 / 2)) p + levyHeadTerm F p - stateTail F p +
      negativeHalfLineLaplace (cx F) (1 / 2) / (p - 1 / 2)

/-- The remainder left of the strip: head term, prime heads and the two charges. -/
def leftRemainder (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  levyHeadTerm F p + primeHead F p + negativeHalfLineLaplace (cx F) (1 / 2) / (p - 1 / 2) +
    negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)

theorem logDeriv_zetaEntire_add {p : ℂ} (hs : (1 : ℂ) / 2 + p ≠ 1)
    (hζ : riemannZeta (1 / 2 + p) ≠ 0) :
    logDeriv zetaEntire (1 / 2 + p) =
      deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p) + 1 / (p - 1 / 2) := by
  have h := Sieve.logDeriv_riemannZeta_eq hs hζ
  rw [logDeriv_apply riemannZeta] at h
  rw [h, show (1 : ℂ) / 2 + p - 1 = p - 1 / 2 by ring]
  ring

theorem logDeriv_zetaEntire_sub {p : ℂ} (hs : (1 : ℂ) / 2 - p ≠ 1)
    (hζ : riemannZeta (1 / 2 - p) ≠ 0) :
    logDeriv zetaEntire (1 / 2 - p) =
      deriv riemannZeta (1 / 2 - p) / riemannZeta (1 / 2 - p) - 1 / (p + 1 / 2) := by
  have h := Sieve.logDeriv_riemannZeta_eq hs hζ
  rw [logDeriv_apply riemannZeta, show (1 : ℂ) / 2 - p - 1 = -(p + 1 / 2) by ring,
    one_div_neg_eq_neg_one_div] at h
  rw [h]
  ring

/-- On the strip the Lévy form of the remainder is the strip form. -/
theorem levyRemainder_eq_stripRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : |p.re| < 1 / 2) (hζ₁ : riemannZeta (1 / 2 + p) ≠ 0) (hζ₂ : riemannZeta (1 / 2 - p) ≠ 0) :
    levyRemainder F p = stripRemainder F p := by
  have h := abs_lt.mp hp
  have hp1 : p ≠ 1 / 2 := by intro e; have := congrArg Complex.re e; simp at this; linarith
  have hpm : p ≠ -(1 / 2) := by intro e; have := congrArg Complex.re e; simp at this; linarith
  have hs1 : (1 : ℂ) / 2 + p ≠ 1 := by intro e; apply hp1; linear_combination e
  have hs2 : (1 : ℂ) / 2 - p ≠ 1 := by intro e; apply hpm; linear_combination -e
  unfold levyRemainder stripRemainder
  rw [levyGamma_eq_reflected_euler hF hp hζ₁ hζ₂, logDeriv_zetaEntire_add hs1 hζ₁,
    logDeriv_zetaEntire_sub hs2 hζ₂, dslope_of_ne _ hp1, slope_def_field, dslope_of_ne _ hpm,
    slope_def_field]
  ring

/-- Left of the strip the strip form of the remainder is the left form: the Euler parts cancel. -/
theorem stripRemainder_eq_leftRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp4 : -4 < p.re) (hp : p.re < -(1 / 2)) : stripRemainder F p = leftRemainder F p := by
  have hpm : p ≠ -(1 / 2) := by intro e; have := congrArg Complex.re e; simp at this; linarith
  have hs2 : (1 : ℂ) / 2 - p ≠ 1 := by
    intro e; have := congrArg Complex.re e; simp at this; linarith
  have hζ₂ : riemannZeta (1 / 2 - p) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  unfold stripRemainder leftRemainder
  rw [stateTail_eq_left hF hp4 hp, logDeriv_zetaEntire_sub hs2 hζ₂, dslope_of_ne _ hpm,
    slope_def_field]
  ring

theorem differentiableAt_stripRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp4 : -4 < p.re) (hp : p.re < 1 / 2) (hz : zetaEntire (1 / 2 - p) ≠ 0) :
    DifferentiableAt ℂ (stripRemainder F) p := by
  have hopen4 : IsOpen {p : ℂ | -(8 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
  have hL : DifferentiableAt ℂ (negativeHalfLineLaplace (cx F)) p :=
    hLap.differentiableAt (hopen4.mem_nhds (by show -(8 / 2) < p.re; linarith))
  have hZ : DifferentiableAt ℂ (fun p : ℂ => logDeriv zetaEntire (1 / 2 - p)) p := by
    have hd1 : DifferentiableAt ℂ (fun p : ℂ => deriv zetaEntire (1 / 2 - p)) p :=
      (differentiable_deriv_zetaEntire _).comp p ((differentiableAt_const _).sub differentiableAt_id)
    have hd2 : DifferentiableAt ℂ (fun p : ℂ => zetaEntire (1 / 2 - p)) p :=
      (differentiable_zetaEntire _).comp p ((differentiableAt_const _).sub differentiableAt_id)
    simp only [logDeriv_apply]
    exact hd1.div hd2 hz
  have hD : DifferentiableAt ℂ (dslope (negativeHalfLineLaplace (cx F)) (-(1 / 2))) p := by
    have hhalf : {p : ℂ | -(8 / 2) < p.re} ∈ 𝓝 (-(1 / 2) : ℂ) :=
      hopen4.mem_nhds (by show -(8 / 2) < (-(1 / 2) : ℂ).re; norm_num)
    exact ((differentiableOn_dslope hhalf).mpr hLap).differentiableAt
      (hopen4.mem_nhds (by show -(8 / 2) < p.re; linarith))
  have hJ : DifferentiableAt ℂ (levyHeadTerm F) p :=
    (differentiableOn_levyHeadTerm hF).differentiableAt
      ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hp)
  have hT : DifferentiableAt ℂ (stateTail F) p :=
    (differentiableOn_stateTail_strip hF).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp4)
  have hP : DifferentiableAt ℂ (fun p : ℂ => negativeHalfLineLaplace (cx F) (1 / 2) / (p - 1 / 2)) p :=
    (differentiableAt_const _).div (differentiableAt_id.sub_const _)
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
  exact (((((hL.mul hZ).neg).sub hD).add hJ).sub hT).add hP

theorem differentiableAt_leftRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : p.re < -(1 / 2)) : DifferentiableAt ℂ (leftRemainder F) p := by
  have hJ : DifferentiableAt ℂ (levyHeadTerm F) p :=
    (differentiableOn_levyHeadTerm hF).differentiableAt
      ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds (show p.re < 1 / 2 by linarith))
  have hS : DifferentiableAt ℂ (primeHead F) p :=
    (differentiableOn_primeHead hF).differentiableAt
      ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hp)
  have hP1 : DifferentiableAt ℂ
      (fun p : ℂ => negativeHalfLineLaplace (cx F) (1 / 2) / (p - 1 / 2)) p :=
    (differentiableAt_const _).div (differentiableAt_id.sub_const _)
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
  have hP2 : DifferentiableAt ℂ
      (fun p : ℂ => negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)) p :=
    (differentiableAt_const _).div (differentiableAt_id.add_const _)
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
  exact ((hJ.add hS).add hP1).add hP2

/-! ### Zeta on the line `Re s = 0` -/

/-- `ζ` has no zero on `Re s = 0` (functional equation and `ζ ≠ 0` on `Re s = 1`). -/
theorem riemannZeta_ne_zero_of_re_eq_zero {s : ℂ} (hs : s.re = 0) : riemannZeta s ≠ 0 := by
  by_cases h0 : s = 0
  · rw [h0, riemannZeta_zero]; norm_num
  · have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have him : s.im ≠ 0 := by intro h; exact h0 (Complex.ext hs h)
    have hG : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [hs])
    rw [zeta_eq_zetaChi_mul h0 h1 hG]
    exact mul_ne_zero (ZetaNotch.zetaChi_ne_zero_of_im_ne_zero him)
      (riemannZeta_ne_zero_of_one_le_re (by simp [hs]))

theorem eventually_riemannZeta_ne_zero {s₀ : ℂ} (h : riemannZeta s₀ ≠ 0) :
    ∀ᶠ s in 𝓝 s₀, riemannZeta s ≠ 0 := by
  have hz := zetaEntire_ne_zero_of_riemannZeta_ne_zero h
  filter_upwards [(differentiable_zetaEntire.continuous.continuousAt (x := s₀)).eventually_ne hz]
    with s hs
  by_cases h1 : s = 1
  · rw [h1]; exact riemannZeta_ne_zero_of_one_le_re (by norm_num)
  · rw [zetaEntire_eq h1] at hs; exact right_ne_zero_of_mul hs

/-! ### The glued remainder and the continuation -/

/-- The remainder in the whole plane: Lévy form right of `Re p = -½`, strip form on the line, left
form left of it. -/
def globalRemainder (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  if -(1 / 2) < p.re then levyRemainder F p
  else if p.re < -(1 / 2) then leftRemainder F p else stripRemainder F p

/-- The continuation of the state's transform to the whole plane. -/
def stateMeromorphic (W₀ : ℝ) (F : ℝ → ℝ) (w : ℂ) : ℂ :=
  -globalRemainder F (w + 8) / criticalAliasCoefficient W₀

theorem differentiableAt_globalRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -(1 / 2) < p.re → zetaEntire (1 / 2 + p) ≠ 0) :
    DifferentiableAt ℂ (globalRemainder F) p := by
  rcases lt_trichotomy p.re (-(1 / 2)) with h | h | h
  · have heq : globalRemainder F =ᶠ[𝓝 p] leftRemainder F := by
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds h] with q hq
      have hq' : q.re < -(1 / 2) := hq
      unfold globalRemainder
      rw [if_neg (not_lt.mpr hq'.le), if_pos hq']
    exact (differentiableAt_leftRemainder hF h).congr_of_eventuallyEq heq
  · -- on the line `Re p = -½`: the three forms agree near `p`
    have hζ₁ : riemannZeta (1 / 2 + p) ≠ 0 := riemannZeta_ne_zero_of_re_eq_zero (by simp [h])
    have hζ₂ : riemannZeta (1 / 2 - p) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num [h])
    have e₁ : ∀ᶠ q in 𝓝 p, riemannZeta (1 / 2 + q) ≠ 0 :=
      ((continuous_const.add continuous_id).tendsto p).eventually (eventually_riemannZeta_ne_zero hζ₁)
    have e₂ : ∀ᶠ q in 𝓝 p, riemannZeta (1 / 2 - q) ≠ 0 :=
      ((continuous_const.sub continuous_id).tendsto p).eventually (eventually_riemannZeta_ne_zero hζ₂)
    have e₃ : ∀ᶠ q in 𝓝 p, -4 < q.re ∧ q.re < 1 / 2 :=
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
          (show p ∈ {q : ℂ | -4 < q.re} ∩ {q : ℂ | q.re < 1 / 2} by
            constructor <;> show _ <;> simp only [Set.mem_setOf_eq] <;> linarith))
    have heq : globalRemainder F =ᶠ[𝓝 p] stripRemainder F := by
      filter_upwards [e₁, e₂, e₃] with q hq₁ hq₂ ⟨hq4, hq5⟩
      unfold globalRemainder
      by_cases hr : -(1 / 2) < q.re
      · rw [if_pos hr]
        exact levyRemainder_eq_stripRemainder hF (abs_lt.mpr ⟨hr, hq5⟩) hq₁ hq₂
      · rw [if_neg hr]
        by_cases hl : q.re < -(1 / 2)
        · rw [if_pos hl]; exact (stripRemainder_eq_leftRemainder hF hq4 hl).symm
        · rw [if_neg hl]
    exact (differentiableAt_stripRemainder hF (by linarith) (by linarith)
      (zetaEntire_ne_zero_of_riemannZeta_ne_zero hζ₂)).congr_of_eventuallyEq heq
  · have heq : globalRemainder F =ᶠ[𝓝 p] levyRemainder F := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h] with q hq
      have hq' : -(1 / 2) < q.re := hq
      unfold globalRemainder
      rw [if_pos hq']
    exact (differentiableAt_levyRemainder hF h (hp h)).congr_of_eventuallyEq heq

theorem stateMeromorphic_eq_levyContinuation {W₀ : ℝ} {F : ℝ → ℝ} {w : ℂ}
    (hw : -(17 / 2) < w.re) : stateMeromorphic W₀ F w = levyContinuation W₀ F w := by
  unfold stateMeromorphic levyContinuation globalRemainder
  rw [if_pos (by simp; linarith)]

/-- **Left of the strip the state is its prime heads.** For `Re w < -17/2`,
`a · L F(w) = -(J F(w+8) + Ŝ F(w+8) + L F(½)/(w + 15/2) + L F(-½)/(w + 17/2))`. -/
theorem stateMeromorphic_eq_left {W₀ : ℝ} {F : ℝ → ℝ} {w : ℂ} (hw : w.re < -(17 / 2)) :
    stateMeromorphic W₀ F w = -leftRemainder F (w + 8) / criticalAliasCoefficient W₀ := by
  unfold stateMeromorphic globalRemainder
  rw [if_neg (by simp; linarith), if_pos (by simp; linarith)]

/-- **Holomorphy in the plane.** The continuation is holomorphic at every point that is not
`ρ - 17/2` for a zero `ρ` of `ζ` with `Re ρ > 0`. -/
theorem differentiableAt_stateMeromorphic {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {w : ℂ}
    (hw : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → w ≠ ρ - 17 / 2) :
    DifferentiableAt ℂ (stateMeromorphic W₀ F) w := by
  have h := differentiableAt_globalRemainder hF (p := w + 8) (fun hre => ?_)
  · exact (h.comp w (differentiableAt_id.add_const (8 : ℂ))).neg.div_const _
  · apply zetaEntire_ne_zero_of_riemannZeta_ne_zero
    intro hz
    exact hw (1 / 2 + (w + 8)) hz (by simp at hre ⊢; linarith) (by ring)

/-- **Residue law in the plane.** -/
theorem tendsto_stateMeromorphic_residue {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ : 0 < ρ.re) :
    Tendsto (fun w => (w - (ρ - 17 / 2)) * stateMeromorphic W₀ F w) (𝓝[≠] (ρ - 17 / 2))
      (𝓝 (-(((analyticOrderAt riemannZeta ρ).toNat : ℂ) *
        negativeHalfLineLaplace (cx F) (ρ - 1 / 2)) / criticalAliasCoefficient W₀)) := by
  refine (tendsto_levyContinuation_residue (W₀ := W₀) hF hζ hρ).congr' ?_
  have hU : {w : ℂ | -(17 / 2) < w.re} ∈ 𝓝 (ρ - 17 / 2) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp; linarith)
  filter_upwards [nhdsWithin_le_nhds hU] with w hw
  rw [stateMeromorphic_eq_levyContinuation hw]

/-- **Boundedness on the left.** The continuation is bounded on every half-plane
`Re w ≤ -17/2 - δ`. -/
theorem exists_bound_stateMeromorphic_left {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ w : ℂ, w.re ≤ -(17 / 2) - δ → ‖stateMeromorphic W₀ F w‖ ≤ C := by
  obtain ⟨g, hg, hgb⟩ := exists_levyHeadTerm_dominator hF (σ := 0) le_rfl (by norm_num)
  set σ := -(1 / 2) - min δ 1 with hσdef
  have hmin : 0 < min δ 1 := lt_min hδ one_pos
  have hmin1 : min δ 1 ≤ 1 := min_le_right _ _
  have hminδ : min δ 1 ≤ δ := min_le_left _ _
  have hσ4 : -4 < σ := by rw [hσdef]; linarith
  have hσh : σ < -(1 / 2) := by rw [hσdef]; linarith
  have hsum := summable_primeHead_bound (F := F) hσh
  set a := criticalAliasCoefficient W₀ with ha
  have hapos : 0 < a := criticalAliasCoefficient_positive hW
  refine ⟨((∫ x in Ioi (0 : ℝ), g x) + (∑' n : ℕ, vonMangoldtAtom n * Real.exp (σ * Real.log n) *
      ∫ u, |F u| * Real.exp (σ * u)) + ‖negativeHalfLineLaplace (cx F) (1 / 2)‖ +
      ‖negativeHalfLineLaplace (cx F) (-(1 / 2))‖ / δ) / a, fun w hw => ?_⟩
  set p := w + 8 with hpdef
  have hpre : p.re ≤ -(1 / 2) - δ := by rw [hpdef]; simp; linarith
  rw [stateMeromorphic_eq_left (by linarith), norm_div, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg hapos.le]
  refine div_le_div_of_nonneg_right ?_ hapos.le
  unfold leftRemainder
  have hJ : ‖levyHeadTerm F p‖ ≤ ∫ x in Ioi (0 : ℝ), g x :=
    norm_integral_le_of_norm_le hg ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun x hx => hgb x hx p (by linarith)))
  have hS : ‖primeHead F p‖ ≤ ∑' n : ℕ, vonMangoldtAtom n * Real.exp (σ * Real.log n) *
      ∫ u, |F u| * Real.exp (σ * u) :=
    tsum_of_norm_bounded hsum.hasSum fun n => norm_primeHead_term_le hF hσ4 (by linarith) n
  have hP1 : ‖negativeHalfLineLaplace (cx F) (1 / 2) / (p - 1 / 2)‖ ≤
      ‖negativeHalfLineLaplace (cx F) (1 / 2)‖ := by
    rw [norm_div]
    have h1 : 1 ≤ ‖p - 1 / 2‖ := by
      have := Complex.abs_re_le_norm (p - 1 / 2)
      simp only [Complex.sub_re] at this
      rw [abs_of_neg (by norm_num; linarith)] at this
      norm_num at this ⊢; linarith
    exact div_le_self (norm_nonneg _) h1
  have hP2 : ‖negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)‖ ≤
      ‖negativeHalfLineLaplace (cx F) (-(1 / 2))‖ / δ := by
    rw [norm_div]
    have h1 : δ ≤ ‖p + 1 / 2‖ := by
      have := Complex.abs_re_le_norm (p + 1 / 2)
      simp only [Complex.add_re] at this
      rw [abs_of_neg (by norm_num; linarith)] at this
      norm_num at this ⊢; linarith
    exact div_le_div_of_nonneg_left (norm_nonneg _) hδ h1
  calc ‖levyHeadTerm F p + primeHead F p + negativeHalfLineLaplace (cx F) (1 / 2) / (p - 1 / 2) +
        negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)‖
      ≤ ‖levyHeadTerm F p‖ + ‖primeHead F p‖ +
          ‖negativeHalfLineLaplace (cx F) (1 / 2) / (p - 1 / 2)‖ +
          ‖negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)‖ :=
        norm_add₄_le
    _ ≤ _ := by gcongr

/-! ### The dichotomy -/

/-- **The state is meromorphic in the plane.** Either RH holds, or the critical state exists and
its transform continues from `Re w > -4` to a function on `ℂ` that is holomorphic off the points
`ρ - 17/2` (`ζ(ρ) = 0`, `Re ρ > 0`), has residue `-m_ρ L F(ρ - ½)/a` there, is singular at every
such point with `Re ρ ≥ ½`, and is bounded on every half-plane `Re w ≤ -17/2 - δ`. -/
theorem riemannHypothesis_or_criticalState_meromorphic :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧
        (∀ w : ℂ, -4 < w.re → stateMeromorphic W₀ F w = negativeHalfLineLaplace (cx F) w) ∧
        (∀ w : ℂ, (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → w ≠ ρ - 17 / 2) →
          DifferentiableAt ℂ (stateMeromorphic W₀ F) w) ∧
        (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re →
          Tendsto (fun w => (w - (ρ - 17 / 2)) * stateMeromorphic W₀ F w) (𝓝[≠] (ρ - 17 / 2))
            (𝓝 (-(((analyticOrderAt riemannZeta ρ).toNat : ℂ) *
              negativeHalfLineLaplace (cx F) (ρ - 1 / 2)) / criticalAliasCoefficient W₀))) ∧
        (∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re →
          ¬ DifferentiableAt ℂ (stateMeromorphic W₀ F) (ρ - 17 / 2)) ∧
        ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ w : ℂ, w.re ≤ -(17 / 2) - δ →
          ‖stateMeromorphic W₀ F w‖ ≤ C := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · have hd := criticalHalfLineEnergyDomain_of_groundState hF
    refine Or.inr ⟨W₀, F, hW, ht, hF, fun w hw => ?_, fun w hw => differentiableAt_stateMeromorphic hd hw,
      fun ρ hζ hρ => tendsto_stateMeromorphic_residue hd hζ hρ, fun ρ hζ hρ => ?_,
      fun δ hδ => exists_bound_stateMeromorphic_left hW hd hδ⟩
    · rw [stateMeromorphic_eq_levyContinuation (by linarith)]
      exact levyContinuation_eq_laplace hW ht hF hw
    · have hL : negativeHalfLineLaplace (cx F) (ρ - 1 / 2) ≠ 0 :=
        criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF (by simp; linarith)
      exact not_differentiableAt_of_residue (tendsto_stateMeromorphic_residue hd hζ (by linarith))
        ((levyResidue_ne_zero_iff hW hζ).mpr hL)

end GaloisForLFunctions.ExclusionOfTheCriticalState
