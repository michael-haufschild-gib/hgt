import GaloisForLFunctions.RHTower.WeilParityPoleOneSidedRH
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling

/-!
# The literal parity poles carry the prime number theorem

On the aperture `[−a, a]` let `X = e^{2a}` and let `Q_λ(r)` be the restricted Weil energy of the
literal parity pole `e^{x/2} + r e^{−x/2}` (`r = ±1`) for prime-side weights `λ`, summed over
`2 ≤ n ≤ X`. The energy is affine in `λ`, and the atom `n` enters with the exact coefficient
`2(2(e^a/n − e^{−a}) + r(2a − log n)(1 + 1/n))` (`weilSourceQuadraticWith_parityPole_eq`).
So the odd pole sees deleted mass at the rate `−2(2a − log n)` and the even pole sees added mass at
the same rate, up to the reciprocal channel `4e^a Σ Λ(n)/n`.

* **Integrated weight.** `Σ_{2 ≤ n ≤ e^T} Λ(n)(T − log n) = ∫_0^T ψ(e^t) dt`
  (`sum_vonMangoldt_mul_logGap_eq_integral`). Hence the pole deficit is
  `D(a) = e^{2a} − 1 − Σ_{n ≤ X} Λ(n)(2a − log n)`.
* **Deletion law** (`sum_deleted_logGap_le_of_oddParityPole_subsystem`). If `0 ≤ λ ≤ Λ` and
  `Q_λ(−1) ≥ 0` at every aperture, then for every aperture
  `Σ_{n ≤ X} (Λ(n) − λ(n)) log(X/n) ≤ (2U + 2(log X + log 4 + 5)) √X`.
* **Addition law** (`sum_added_logGap_le_of_evenParityPole_supersystem`). If `λ ≥ Λ` and
  `Q_λ(1) ≥ 0` at every aperture, then `Σ_{n ≤ X} (λ(n) − Λ(n)) log(X/n) ≤ 2U √X`.
* **Scaling** (`eventually_oddParityPole_scaled_neg`). For `0 ≤ β < 1` the odd-pole energy of
  `βΛ` is at most `−(1 − β) X + O(√X log X)`. By the prime number theorem it is negative at every
  large aperture.

Here `U` is the absolute constant `ccmWeilPoleUniformDeficitBound`.

The odd pole has polar energy `−2((e^a − e^{−a}) − 2a)² ≈ −2X`, and only the prime main term
`2 Σ Λ(n) log(X/n) ≈ 2X` cancels it. Consequently no inequality that holds for all weights `βΛ`
with `β` in an interval `[β₀, 1]` can imply nonnegativity of the odd-pole energy at every aperture.
Both laws use RH only through the corpus criteria: one-sided positivity of a subsystem or
supersystem already implies RH, and RH bounds the deficit of `Λ`.
-/

open Complex Set MeasureTheory Filter
open scoped InnerProduct BigOperators Topology
open GaloisForLFunctions.RHTower

noncomputable section
namespace RHTower

/-! ## The prime atoms on the literal parity poles -/

/-- The energy of the prime atom `n` on the literal parity pole `e^{x/2} + r e^{−x/2}`. -/
def parityPoleAtom (a : SuzukiPositiveAperture) (r : ℝ) (n : ℕ) : ℝ :=
  (1 / Real.sqrt n) *
    (inner ℂ (logTranslationCLM (Real.log n)
        (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)).1)
        (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)).1 +
      inner ℂ (logTranslationCLM (-Real.log n)
        (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)).1)
        (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r)).1).re

private theorem log_le_of_le_floor_exp (a : SuzukiPositiveAperture) {n : ℕ} (hn : 2 ≤ n)
    (hN : n ≤ ⌊Real.exp (2 * a.1)⌋₊) : Real.log n ≤ 2 * a.1 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hle : (n : ℝ) ≤ Real.exp (2 * a.1) :=
    le_trans (by exact_mod_cast hN) (Nat.floor_le (Real.exp_pos _).le)
  rw [← Real.exp_le_exp, Real.exp_log hnR]
  exact hle

/-- The exact atom energy `2(2(e^a/n − e^{−a}) + r(2a − log n)(1 + 1/n))` for every visible atom. -/
theorem parityPoleAtom_eq (a : SuzukiPositiveAperture) {r : ℝ} (hr : r = 1 ∨ r = -1) {n : ℕ}
    (hn : 2 ≤ n) (hN : n ≤ ⌊Real.exp (2 * a.1)⌋₊) :
    parityPoleAtom a r n =
      2 * (2 * (Real.exp a.1 / n - Real.exp (-a.1)) +
        r * (2 * a.1 - Real.log n) * (1 + 1 / (n : ℝ))) := by
  have hv := log_le_of_le_floor_exp a hn hN
  unfold parityPoleAtom
  set f := ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a r) with hf
  have hT := inner_ccmPrimeTransportOperator a n f f
  have hpar := ccmPrimeTransport_polar_parity a hn hv hr
  rw [ccmArchimedeanFormToAperture_polarParity] at hf
  rw [hf] at hT
  rw [hT] at hpar
  have hre := congrArg Complex.re hpar
  rw [Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  rw [hf, hre]

/-- On the odd pole a visible atom costs at most `4e^a/n − 2(2a − log n)`. -/
theorem parityPoleAtom_odd_le (a : SuzukiPositiveAperture) {n : ℕ} (hn : 2 ≤ n)
    (hN : n ≤ ⌊Real.exp (2 * a.1)⌋₊) :
    parityPoleAtom a (-1) n ≤ 4 * (Real.exp a.1 / n) - 2 * (2 * a.1 - Real.log n) := by
  rw [parityPoleAtom_eq a (Or.inr rfl) hn hN]
  have hv := log_le_of_le_floor_exp a hn hN
  have hl : 0 ≤ 2 * a.1 - Real.log n := by linarith
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 ≤ (2 * a.1 - Real.log n) * (1 / (n : ℝ)) := mul_nonneg hl (by positivity)
  have hm := Real.exp_pos (-a.1)
  nlinarith

/-- On the even pole a visible atom gains at least `2(2a − log n)`. -/
theorem parityPoleAtom_even_ge (a : SuzukiPositiveAperture) {n : ℕ} (hn : 2 ≤ n)
    (hN : n ≤ ⌊Real.exp (2 * a.1)⌋₊) :
    2 * (2 * a.1 - Real.log n) ≤ parityPoleAtom a 1 n := by
  rw [parityPoleAtom_eq a (Or.inl rfl) hn hN]
  have hv := log_le_of_le_floor_exp a hn hN
  have hl : 0 ≤ 2 * a.1 - Real.log n := by linarith
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 ≤ (2 * a.1 - Real.log n) * (1 / (n : ℝ)) := mul_nonneg hl (by positivity)
  have hexp : Real.exp (-a.1) ≤ Real.exp a.1 / n := by
    rw [le_div_iff₀ hnR, ← Real.exp_log hnR, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  nlinarith

/-- **The parity-pole energy is affine in the weights.** -/
theorem weilSourceQuadraticWith_parityPole_eq (a : SuzukiPositiveAperture) (lam : ℕ → ℝ) (r : ℝ) :
    ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
        (ccmPolarParityFormVector a r) =
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * parityPoleAtom a r n := by
  rw [← ccmRestrictedWeilSourceQuadraticWith_eq a (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    le_rfl (fun n _ _ => rfl)]
  unfold ccmRestrictedWeilSourceQuadraticWith parityPoleAtom
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc]
  ring

/-! ## The integrated von Mangoldt weight -/

/-- `Σ_{2 ≤ n ≤ e^T} Λ(n)(T − log n) = ∫_0^T ψ(e^t) dt`, by Abel summation against `T − log y`. -/
theorem sum_vonMangoldt_mul_logGap_eq_integral {T : ℝ} (hT : 0 ≤ T) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp T⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * (T - Real.log n) =
      ∫ t in (0 : ℝ)..T, Chebyshev.psi (Real.exp t) := by
  have h1 : (1 : ℝ) ≤ Real.exp T := Real.one_le_exp hT
  have hderiv : deriv (fun y : ℝ => T - Real.log y) = fun y => -y⁻¹ := by
    funext y
    rw [deriv_const_sub, Real.deriv_log]
  have hint : IntegrableOn (deriv (fun y : ℝ => T - Real.log y)) (Icc 1 (Real.exp T)) volume := by
    rw [hderiv]
    refine ContinuousOn.integrableOn_Icc (ContinuousOn.neg (continuousOn_inv₀.mono ?_))
    intro y hy
    exact ne_of_gt (lt_of_lt_of_le one_pos hy.1)
  have habel := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))
    (f := fun y : ℝ => T - Real.log y) (a := 1) (b := Real.exp T) (by norm_num) h1
    (fun y hy => (differentiableAt_const T).sub
      (Real.differentiableAt_log (ne_of_gt (lt_of_lt_of_le one_pos hy.1)))) hint
  simp_rw [← Chebyshev.psi_eq_sum_Icc, hderiv] at habel
  rw [Real.log_exp, sub_self, zero_mul, Real.log_one, sub_zero, Nat.floor_one,
    Chebyshev.psi_eq_zero_of_lt_two (by norm_num), mul_zero, sub_zero, zero_sub] at habel
  have hIoc : Finset.Ioc 1 ⌊Real.exp T⌋₊ = Finset.Icc 2 ⌊Real.exp T⌋₊ :=
    (Finset.Icc_succ_left_eq_Ioc 1 _).symm
  rw [hIoc] at habel
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp T⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℝ) * (T - Real.log n) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp T⌋₊,
        (T - Real.log n) * (ArithmeticFunction.vonMangoldt n : ℝ) :=
    Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [hsum, habel, ← integral_neg, ← integral_Icc_eq_integral_Ioc]
  have himg : Icc (1 : ℝ) (Real.exp T) = Real.exp '' Icc 0 T := by
    rw [Real.image_exp_Icc, Real.exp_zero]
  rw [himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun s _ => (Real.hasDerivAt_exp s).hasDerivWithinAt) Real.exp_injective.injOn,
    intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  have he := (Real.exp_pos s).ne'
  rw [abs_of_pos (Real.exp_pos s), smul_eq_mul]
  field_simp

/-- The pole deficit is `e^{2a} − 1` minus the integrated von Mangoldt weight. -/
theorem ccmPoleIntegratedChebyshevDeficit_eq_sub (a : SuzukiPositiveAperture) :
    ccmPoleIntegratedChebyshevDeficit a = Real.exp (2 * a.1) - 1 -
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) * (2 * a.1 - Real.log n) := by
  have hpsi : IntervalIntegrable (fun t => Chebyshev.psi (Real.exp t)) volume 0 (2 * a.1) :=
    (Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable
  rw [ccmPoleIntegratedChebyshevDeficit_eq_logPrimitive, ccmLogChebyshevDeficitPrimitive,
    sum_vonMangoldt_mul_logGap_eq_integral (by linarith [a.property]),
    intervalIntegral.integral_sub (Real.continuous_exp.intervalIntegrable _ _) hpsi, integral_exp,
    Real.exp_zero]

/-! ## The von Mangoldt parity energies against the deficit -/

/-- `Q_Λ(r) ≤ 2r D(a) + 2U e^a` for both parities. -/
theorem weilSourceQuadratic_parityPole_le (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r = 1 ∨ r = -1) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) ≤
      2 * r * ccmPoleIntegratedChebyshevDeficit a +
        2 * ccmWeilPoleUniformDeficitBound * Real.exp a.1 := by
  rw [ccmWeilPoleCompression_parity_energy a hr]
  have hd := abs_le.mp (abs_integratedChebyshevDeficit_sub_weilPoleCross_le a)
  have hA := abs_le.mp (abs_ccmWeilPoleDiagonal_le a)
  have hB := ccmGammaPoleCrossBoundaryMass_le a
  have ha := a.property
  have he : 1 ≤ Real.exp a.1 := Real.one_le_exp ha.le
  have hae : a.1 ≤ Real.exp a.1 := by linarith [Real.add_one_le_exp a.1]
  have hC : 0 ≤ 2 * Real.log 2 + Real.pi + 1 := by positivity
  have hK : 0 ≤ |-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| + Real.log 4 + 5 := by
    positivity
  have hBC := mul_le_mul_of_nonneg_left he hC
  have hKC := mul_le_mul_of_nonneg_left hae hK
  unfold ccmWeilPoleUniformDeficitBound
  rcases hr with rfl | rfl <;> nlinarith

/-- The reciprocal channel `Σ_{n ≤ e^{2a}} Λ(n)/n ≤ 2a + log 4 + 5`. -/
private theorem reciprocal_cumulative_le (a : SuzukiPositiveAperture) :
    ccmReciprocalMangoldtCumulative (Real.exp (2 * a.1)) ≤ 2 * a.1 + (Real.log 4 + 5) := by
  have hE := abs_le.mp (abs_ccmReciprocalMangoldtError_le
    (show 0 ≤ 2 * a.1 by linarith [a.property]))
  unfold ccmReciprocalMangoldtError at hE
  linarith [hE.2]

/-! ## Deletion and addition inequalities -/

/-- **Deletion inequality.** For `0 ≤ λ ≤ Λ` the odd-pole energy drops by twice the deleted
log-weighted mass, up to the reciprocal channel. -/
theorem weilSourceQuadraticWith_oddParity_le_deletion {lam : ℕ → ℝ}
    (h0 : ∀ n, 2 ≤ n → 0 ≤ lam n)
    (hle : ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ))
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
        (ccmPolarParityFormVector a (-1)) ≤
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) +
        4 * Real.exp a.1 * ccmReciprocalMangoldtCumulative (Real.exp (2 * a.1)) -
        2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * (2 * a.1 - Real.log n) := by
  rw [weilSourceQuadraticWith_parityPole_eq, ccmReciprocalMangoldtCumulative, Finset.mul_sum,
    Finset.mul_sum]
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * parityPoleAtom a (-1) n ≤
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        (4 * Real.exp a.1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) -
          2 * (((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * (2 * a.1 - Real.log n))) := by
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
    have hatom := parityPoleAtom_odd_le a hn2 hnN
    have hu0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) - lam n := by linarith [hle n hn2]
    have hul : (ArithmeticFunction.vonMangoldt n : ℝ) - lam n ≤ ArithmeticFunction.vonMangoldt n := by
      linarith [h0 n hn2]
    have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hq : 0 ≤ 4 * (Real.exp a.1 / n) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hatom hu0
    have h2 := mul_le_mul_of_nonneg_right hul hq
    have h3 : (ArithmeticFunction.vonMangoldt n : ℝ) * (4 * (Real.exp a.1 / n)) =
        4 * Real.exp a.1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) := by ring
    nlinarith
  rw [Finset.sum_sub_distrib] at hsum
  linarith

/-- **Addition inequality.** For `λ ≥ Λ` the even-pole energy drops by at least twice the added
log-weighted mass. -/
theorem weilSourceQuadraticWith_evenParity_le_addition {lam : ℕ → ℝ}
    (hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n)
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
        (ccmPolarParityFormVector a 1) ≤
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) -
        2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (lam n - ArithmeticFunction.vonMangoldt n) * (2 * a.1 - Real.log n) := by
  rw [weilSourceQuadraticWith_parityPole_eq, Finset.mul_sum]
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * parityPoleAtom a 1 n ≤
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        -(2 * ((lam n - ArithmeticFunction.vonMangoldt n) * (2 * a.1 - Real.log n))) := by
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
    have hatom := parityPoleAtom_even_ge a hn2 hnN
    have hu0 : 0 ≤ lam n - (ArithmeticFunction.vonMangoldt n : ℝ) := by linarith [hge n hn2]
    have h1 := mul_le_mul_of_nonneg_left hatom hu0
    nlinarith
  rw [Finset.sum_neg_distrib] at hsum
  linarith

/-! ## Deletion and addition laws -/

/-- **Deletion law.** A nonnegative subsystem `λ ≤ Λ` with nonnegative odd-pole energy at every
aperture deletes at most `O(√X log X)` log-weighted mass:
`Σ_{n ≤ X} (Λ(n) − λ(n)) log(X/n) ≤ (2U + 2(log X + log 4 + 5)) √X`, `X = e^{2a}`. -/
theorem sum_deleted_logGap_le_of_oddParityPole_subsystem {lam : ℕ → ℝ}
    (h0 : ∀ n, 2 ≤ n → 0 ≤ lam n)
    (hle : ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ))
    (hpos : ∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
        (ccmPolarParityFormVector a (-1)))
    (a : SuzukiPositiveAperture) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * (2 * a.1 - Real.log n) ≤
      (2 * ccmWeilPoleUniformDeficitBound + 2 * (2 * a.1 + (Real.log 4 + 5))) * Real.exp a.1 := by
  have hRH := riemannHypothesis_of_oddParityPole_subsystem h0 hle hpos
  have hD := ccmPoleIntegratedChebyshevDeficit_ge_of_evenParity a
    (ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH a _)
  have hQ := weilSourceQuadratic_parityPole_le a (r := -1) (Or.inr rfl)
  have hdel := weilSourceQuadraticWith_oddParity_le_deletion h0 hle a
  have hM := reciprocal_cumulative_le a
  have hM' := mul_le_mul_of_nonneg_left hM (show 0 ≤ 4 * Real.exp a.1 by positivity)
  have := hpos a
  nlinarith

/-- **Addition law.** A supersystem `λ ≥ Λ` with nonnegative even-pole energy at every aperture
adds at most `O(√X)` log-weighted mass:
`Σ_{n ≤ X} (λ(n) − Λ(n)) log(X/n) ≤ 2U √X`, `X = e^{2a}`. -/
theorem sum_added_logGap_le_of_evenParityPole_supersystem {lam : ℕ → ℝ}
    (hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n)
    (hpos : ∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
        (ccmPolarParityFormVector a 1))
    (a : SuzukiPositiveAperture) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        (lam n - ArithmeticFunction.vonMangoldt n) * (2 * a.1 - Real.log n) ≤
      2 * ccmWeilPoleUniformDeficitBound * Real.exp a.1 := by
  have hRH := riemannHypothesis_of_evenParityPole_supersystem hge hpos
  have hD := ccmPoleIntegratedChebyshevDeficit_le_of_oddParity a
    (ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH a _)
  have hQ := weilSourceQuadratic_parityPole_le a (r := 1) (Or.inl rfl)
  have hadd := weilSourceQuadraticWith_evenParity_le_addition hge a
  have := hpos a
  nlinarith

/-! ## Scaled von Mangoldt weights -/

/-- For `0 ≤ β ≤ 1` the odd-pole energy of `βΛ` is at most
`2β ∫_0^{2a} ψ(e^t) dt − 2e^{2a} + (2U + 4(2a + log 4 + 5)) e^a + 2`. -/
theorem weilSourceQuadraticWith_oddParity_scaled_le (a : SuzukiPositiveAperture) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ccmRestrictedWeilSourceQuadraticWith a (fun n => β * ArithmeticFunction.vonMangoldt n)
        ⌊Real.exp (2 * a.1)⌋₊ (ccmPolarParityFormVector a (-1)) ≤
      2 * β * (∫ t in (0 : ℝ)..2 * a.1, Chebyshev.psi (Real.exp t)) - 2 * Real.exp (2 * a.1) +
        (2 * ccmWeilPoleUniformDeficitBound + 4 * (2 * a.1 + (Real.log 4 + 5))) * Real.exp a.1 +
        2 := by
  have hdel := weilSourceQuadraticWith_oddParity_le_deletion
    (lam := fun n => β * ArithmeticFunction.vonMangoldt n)
    (fun n _ => mul_nonneg hβ0 ArithmeticFunction.vonMangoldt_nonneg)
    (fun n _ => by
      have := (ArithmeticFunction.vonMangoldt_nonneg : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n)
      nlinarith) a
  have hscale : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) - β * ArithmeticFunction.vonMangoldt n) *
          (2 * a.1 - Real.log n) =
      (1 - β) * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) * (2 * a.1 - Real.log n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hscale] at hdel
  have hQ := weilSourceQuadratic_parityPole_le a (r := -1) (Or.inr rfl)
  have hD := ccmPoleIntegratedChebyshevDeficit_eq_sub a
  have hS := sum_vonMangoldt_mul_logGap_eq_integral (T := 2 * a.1) (by linarith [a.property])
  have hM := reciprocal_cumulative_le a
  have hM' := mul_le_mul_of_nonneg_left hM (show 0 ≤ 4 * Real.exp a.1 by positivity)
  rw [← hS]
  nlinarith

/-- The prime number theorem in the form used here: for every `ε > 0` there is `K ≥ 0` with
`ψ(e^t) ≤ (1 + ε) e^t + K` for all `t`. -/
theorem exists_psi_exp_le (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, Chebyshev.psi (Real.exp t) ≤ (1 + ε) * Real.exp t + K := by
  have hident (x : ℝ) : chebyshevPsiReal x = Chebyshev.psi x := by
    rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_Icc]
    congr 1
    ext n
    simp
  have hev : ∀ᶠ x : ℝ in atTop, chebyshevPsiReal x / x < 1 + ε :=
    tendsto_chebyshevPsiReal_div.eventually (gt_mem_nhds (by linarith))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hev
  set x₁ := max x₀ 1 with hx₁
  refine ⟨Chebyshev.psi x₁, Chebyshev.psi_nonneg _, fun t => ?_⟩
  have he := Real.exp_pos t
  rcases le_or_gt x₁ (Real.exp t) with h | h
  · have hlt := hx₀ (Real.exp t) (le_trans (le_max_left _ _) h)
    rw [hident, div_lt_iff₀ he] at hlt
    linarith [Chebyshev.psi_nonneg x₁]
  · have hmono := Chebyshev.psi_mono h.le
    have : 0 ≤ (1 + ε) * Real.exp t := by positivity
    linarith

/-- **Scaled weights are eventually odd-pole negative.** For `0 ≤ β < 1` the odd-pole energy of
`βΛ` is negative at every large aperture. -/
theorem eventually_oddParityPole_scaled_neg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ a₀ : ℝ, ∀ a : SuzukiPositiveAperture, a₀ ≤ a.1 →
      ccmRestrictedWeilSourceQuadraticWith a (fun n => β * ArithmeticFunction.vonMangoldt n)
        ⌊Real.exp (2 * a.1)⌋₊ (ccmPolarParityFormVector a (-1)) < 0 := by
  have hβ' : 0 < 1 - β := by linarith
  obtain ⟨K, hK0, hK⟩ := exists_psi_exp_le ((1 - β) / 2) (by linarith)
  have hU0 := ccmWeilPoleUniformDeficitBound_pos
  have hL0 : 0 ≤ Real.log 4 + 5 := by positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 2 * ccmWeilPoleUniformDeficitBound + 4 * (Real.log 4 + 5) + 2 :=
    ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 8 + 4 * K := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  refine ⟨2 * (P + R + 1) / (1 - β) + 1, fun a ha => ?_⟩
  have hpos := a.property
  have hmain := weilSourceQuadraticWith_oddParity_scaled_le a hβ0 hβ1.le
  have hint : (∫ t in (0 : ℝ)..2 * a.1, Chebyshev.psi (Real.exp t)) ≤
      ∫ t in (0 : ℝ)..2 * a.1, ((1 + (1 - β) / 2) * Real.exp t + K) :=
    intervalIntegral.integral_mono_on (by linarith)
      ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable)
      (by apply Continuous.intervalIntegrable; fun_prop) (fun t _ => hK t)
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_exp,
      intervalIntegral.integral_const, Real.exp_zero, smul_eq_mul, sub_zero] at hint
  set E := Real.exp a.1 with hE
  have hE2 : Real.exp (2 * a.1) = E * E := by rw [hE, ← Real.exp_add, two_mul]
  have hEq := Real.quadratic_le_exp_of_nonneg hpos.le
  rw [← hE] at hEq
  have hE1 : 1 ≤ E := by nlinarith
  have ha0 : 2 * (P + R + 1) / (1 - β) ≤ a.1 := by linarith
  rw [div_le_iff₀ hβ'] at ha0
  have ha1 : 1 ≤ a.1 := by
    have : 0 < 2 * (P + R + 1) / (1 - β) := by positivity
    linarith
  -- `(1 − β) e^a > P + R a`
  have hgrow : P + R * a.1 < (1 - β) * E := by
    have h1 := mul_le_mul_of_nonneg_left ha0 hpos.le
    have h2 := mul_le_mul_of_nonneg_left hEq hβ'.le
    have h3 : P ≤ P * a.1 := le_mul_of_one_le_right hP0 ha1
    have h4 : 0 ≤ (1 - β) * a.1 := mul_nonneg hβ'.le hpos.le
    nlinarith
  have hint' := mul_le_mul_of_nonneg_left hint (show 0 ≤ 2 * β by linarith)
  rw [hE2] at hint' hmain ⊢
  have hβε : β * (1 + (1 - β) / 2) ≤ (1 + β) / 2 := by nlinarith [sq_nonneg (β - 1)]
  have hfin : 2 * β * ((1 + (1 - β) / 2) * (E * E - 1) + 2 * a.1 * K) ≤
      (1 + β) * (E * E) + 4 * K * a.1 := by
    have hA := mul_le_mul_of_nonneg_right hβε (mul_nonneg (by linarith : (0:ℝ) ≤ E) (by linarith))
    have hB : 0 ≤ β * (1 + (1 - β) / 2) := mul_nonneg hβ0 (by linarith)
    have hC : β * (K * a.1) ≤ K * a.1 := mul_le_of_le_one_left (mul_nonneg hK0 hpos.le) hβ1.le
    nlinarith
  have hKa : 4 * K * a.1 ≤ 4 * K * a.1 * E :=
    le_mul_of_one_le_right (by positivity) hE1
  have hfinal := mul_lt_mul_of_pos_right hgrow (show 0 < E by positivity)
  rw [hP, hR] at hfinal
  nlinarith

/-- Scaled weights `βΛ` with `0 ≤ β < 1` are never odd-pole positive at every aperture. -/
theorem not_forall_oddParityPole_scaled_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ¬ ∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadraticWith a (fun n => β * ArithmeticFunction.vonMangoldt n)
        ⌊Real.exp (2 * a.1)⌋₊ (ccmPolarParityFormVector a (-1)) := by
  intro h
  obtain ⟨a₀, ha₀⟩ := eventually_oddParityPole_scaled_neg hβ0 hβ1
  have hpos : 0 < max a₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have := ha₀ ⟨max a₀ 1, hpos⟩ (le_max_left _ _)
  linarith [h ⟨max a₀ 1, hpos⟩]

end RHTower
