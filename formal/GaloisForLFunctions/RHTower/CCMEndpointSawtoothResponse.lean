import GaloisForLFunctions.RHTower.CCMSawtoothExteriorTail
import GaloisForLFunctions.RHTower.CCMEndpointResponseConstants

/-!
# The exterior sawtooth incidence constant of the endpoint layer

The endpoint layer of the CCM source carries the exterior tail `T_L(s) = e^{-s/2} S(L e^s)`, and its
complete von Mangoldt incidence

```text
sum_(n>=2) Lambda(n) n^{-1/2} integral_0^infinity T_L(s) T_L(s + log n) ds
```

converges, as the aperture grows, to `(pi²/12)(-zeta'(2)/zeta(2))`.

Two identifications do all the work.  First, the pairing of the tail with its own multiplicative
translate *is* the corpus's exterior response of the unit sawtooth: the two half-weights combine into
`e^{-s} n^{-1/2}`, the dilation `L e^{s+log n} = n L e^s` moves inside the second sawtooth, and the
normalization `S = pi · sawUnit(·/(2 pi))` contributes `pi²`.  Second, the universal Euler scalar
`sum Lambda(n) n^{-2}` of that response is the negative logarithmic derivative of zeta at `2`, which
is mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` transported across the real-to-complex
cast.

Everything analytic — the exact period mean `1/(12 n)`, the uniform `O(1/L)` averaging error, the
`O(1/n)` domination and the dominated passage to the limit — is already proved in
`CCMSawtoothDilationIncidence` and `CCMSawtoothExteriorTail`; this module only performs the two
identifications and states the constant in the endpoint layer's own variables.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set ArithmeticFunction Filter Topology

/-! ## The Euler scalar is the logarithmic derivative of zeta -/

/-- **Equation (17).**  The real Euler weight `sum Lambda(n) n^{-2}` is `-zeta'(2)/zeta(2)`. -/
theorem ofReal_tsum_vonMangoldt_div_sq :
    ((∑' n : ℕ, Λ n / (n : ℝ) ^ 2 : ℝ) : ℂ) = -deriv riemannZeta 2 / riemannZeta 2 := by
  rw [← lseries_vonMangoldt_two, LSeries]
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [LSeries.term_zero]
    simp
  · rw [LSeries.term_of_ne_zero (by exact_mod_cast hn.ne')]
    push_cast
    rw [show ((2 : ℂ)) = ((2 : ℕ) : ℂ) from by norm_num, Complex.cpow_natCast]

/-! ## The endpoint tail and its multiplicative translates -/

/-- The exterior tail of the endpoint layer: `T_L(s) = e^{-s/2} S(L e^s)`. -/
def sawTail (L : ℝ) (s : ℝ) : ℝ := Real.exp (-s / 2) * sawWave (L * Real.exp s)

/-- The pairing of the tail with its `log n`-translate, pointwise: the two half-weights combine, the
dilation moves inside the sawtooth, and the normalization contributes `pi²`. -/
theorem sawTail_mul_shift {L : ℝ} {n : ℕ} (hn : 0 < n) (s : ℝ) :
    sawTail L s * sawTail L (s + Real.log n)
      = (Real.pi ^ 2 / Real.sqrt n) * (Real.exp (-s) *
        (sawUnit (L / (2 * Real.pi) * Real.exp s) *
          sawUnit ((n : ℝ) * (L / (2 * Real.pi) * Real.exp s)))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hdil : L * Real.exp (s + Real.log n) = (n : ℝ) * (L * Real.exp s) := by
    rw [Real.exp_add, Real.exp_log hn0]
    ring
  have hhalf : Real.exp (-(s + Real.log n) / 2) = Real.exp (-s / 2) / Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_log hn0, ← Real.exp_mul]
    rw [← Real.exp_sub]
    congr 1
    have hlog : Real.log (Real.exp (Real.log n)) = Real.log n := Real.log_exp _
    rw [Real.exp_log hn0]
    ring
  have hs1 : sawWave (L * Real.exp s)
      = Real.pi * sawUnit (L / (2 * Real.pi) * Real.exp s) := by
    rw [sawWave]
    congr 1
    field_simp
  have hs2 : sawWave ((n : ℝ) * (L * Real.exp s))
      = Real.pi * sawUnit ((n : ℝ) * (L / (2 * Real.pi) * Real.exp s)) := by
    rw [sawWave]
    congr 1
    field_simp
  have hexp : Real.exp (-s / 2) * Real.exp (-s / 2) = Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [sawTail, sawTail, hdil, hhalf, hs1, hs2, ← hexp]
  ring

/-- The pairing integral of the tail with its `log n`-translate is `pi² n^{-1/2}` times the corpus's
exterior response of the unit sawtooth. -/
theorem integral_sawTail_mul_shift {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    (∫ s in Ioi (0 : ℝ), sawTail L s * sawTail L (s + Real.log n))
      = (Real.pi ^ 2 / Real.sqrt n) *
        ∫ x in Ioi (L / (2 * Real.pi)), invSqWeight (L / (2 * Real.pi)) x *
          (sawUnit x * sawUnit ((n : ℝ) * x)) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hL' : (0 : ℝ) < L / (2 * Real.pi) := by positivity
  have hcongr : (∫ s in Ioi (0 : ℝ), sawTail L s * sawTail L (s + Real.log n))
      = ∫ s in Ioi (0 : ℝ), (Real.pi ^ 2 / Real.sqrt n) * (Real.exp (-s) *
        (sawUnit (L / (2 * Real.pi) * Real.exp s) *
          sawUnit ((n : ℝ) * (L / (2 * Real.pi) * Real.exp s)))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    exact sawTail_mul_shift hn s
  rw [hcongr, integral_const_mul,
    integral_expWeight_Ioi_eq_invSqWeight hL'
      (fun x => sawUnit x * sawUnit ((n : ℝ) * x))]

/-! ## The full incidence -/

/-- **Equation (17) in the endpoint layer's variables.**  The complete von Mangoldt incidence of the
endpoint tail converges to `(pi²/12) sum Lambda(n) n^{-2}` as the aperture grows. -/
theorem tendsto_sawTailPrimeResponse :
    Tendsto (fun L : ℝ => ∑' n : ℕ, Λ n / Real.sqrt n *
        ∫ s in Ioi (0 : ℝ), sawTail L s * sawTail L (s + Real.log n)) atTop
      (nhds ((Real.pi ^ 2 / 12) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2)) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- the corpus limit, along the rescaled aperture
  have hscale : Tendsto (fun L : ℝ => L / (2 * Real.pi)) atTop atTop :=
    Filter.Tendsto.atTop_div_const hpi tendsto_id
  have hbase := tendsto_fullPrimeResponse.comp hscale
  have hconst := hbase.const_mul (Real.pi ^ 2)
  have hval : Real.pi ^ 2 * ((1 / 12) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2)
      = (Real.pi ^ 2 / 12) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2 := by ring
  rw [hval] at hconst
  refine hconst.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hterm : ∀ n : ℕ, Λ n / Real.sqrt n *
      (∫ s in Ioi (0 : ℝ), sawTail L s * sawTail L (s + Real.log n))
      = Real.pi ^ 2 * (Λ n / (n : ℝ) *
        ∫ x in Ioi (L / (2 * Real.pi)), invSqWeight (L / (2 * Real.pi)) x *
          (sawUnit x * sawUnit ((n : ℝ) * x))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn0.le
      have hsqpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hcoef : ∀ t : ℝ, 0 < t → t * t = (n : ℝ) →
          Λ n / t * (Real.pi ^ 2 / t) = Real.pi ^ 2 * (Λ n / (n : ℝ)) := by
        intro t ht htt
        rw [← htt]
        field_simp
      rw [integral_sawTail_mul_shift hL hn, ← mul_assoc, hcoef _ hsqpos hsq, mul_assoc]
  calc Real.pi ^ 2 * ∑' n : ℕ, Λ n / (n : ℝ) *
        ∫ x in Ioi (L / (2 * Real.pi)), invSqWeight (L / (2 * Real.pi)) x *
          (sawUnit x * sawUnit ((n : ℝ) * x))
      = ∑' n : ℕ, Real.pi ^ 2 * (Λ n / (n : ℝ) *
          ∫ x in Ioi (L / (2 * Real.pi)), invSqWeight (L / (2 * Real.pi)) x *
            (sawUnit x * sawUnit ((n : ℝ) * x))) := by
        rw [tsum_mul_left]
    _ = ∑' n : ℕ, Λ n / Real.sqrt n *
          ∫ s in Ioi (0 : ℝ), sawTail L s * sawTail L (s + Real.log n) :=
        tsum_congr fun n => (hterm n).symm

/-- **Equation (17), with the zeta constant.**  The limit constant of the endpoint incidence is
`(pi²/12)(-zeta'(2)/zeta(2))`. -/
theorem tendsto_sawTailPrimeResponse_ofReal :
    Tendsto (fun L : ℝ => ((∑' n : ℕ, Λ n / Real.sqrt n *
        ∫ s in Ioi (0 : ℝ), sawTail L s * sawTail L (s + Real.log n) : ℝ) : ℂ)) atTop
      (nhds ((Real.pi ^ 2 / 12) * (-deriv riemannZeta 2 / riemannZeta 2))) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp tendsto_sawTailPrimeResponse
  have hval : ((((Real.pi ^ 2 / 12) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2 : ℝ)) : ℂ)
      = (Real.pi ^ 2 / 12) * (-deriv riemannZeta 2 / riemannZeta 2) := by
    rw [Complex.ofReal_mul, ofReal_tsum_vonMangoldt_div_sq]
    push_cast
    ring
  rw [hval] at h
  exact h.congr fun L => rfl

/-- **Equation (18) with the sawtooth constant supplied.**  Given the amplitude limit `(15)`, the
complete prime response of the endpoint layer divided by the reference leakage converges to
`(4 pi/33) sum Lambda(n) n^{-2}`. -/
theorem tendsto_primeResponse_div_leakage_sawTail {d1 A R : ℝ → ℝ}
    (hR : ∀ᶠ L in atTop, R L = A L * (∑' n : ℕ, Λ n / Real.sqrt n *
      ∫ s in Ioi (0 : ℝ), sawTail L s * sawTail L (s + Real.log n)))
    (hA : Tendsto (fun L : ℝ => A L / d1 L) atTop (nhds (16 / (11 * Real.pi)))) :
    Tendsto (fun L : ℝ => R L / d1 L) atTop
      (nhds (4 * Real.pi / 33 * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2)) :=
  tendsto_primeResponse_div_leakage hR hA tendsto_sawTailPrimeResponse

end GaloisForLFunctions.RHTower

end
