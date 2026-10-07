import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorStripBounds
import GaloisForLFunctions.RHTower.XiFinitePacketGauge

/-!
# Rapid vertical tails of the actual completed quotient

The pole-cleared representative retains removable values at common zeros of
`E` and `xi`. Every polynomial decay order follows from the cubic datum;
one height threshold suffices for all orders.
-/

noncomputable section

open Complex Set Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

/-- The meromorphic degree-two completion using the entire pole-cleared numerator. -/
def poleClearedDegreeTwoCompletion (P : Polynomial ℂ) (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  H s / (2 * P.eval s * s ^ 2 * (s - 1) ^ 2)

/-- The representative is meromorphic everywhere, including poles of arbitrary order. -/
theorem poleClearedDegreeTwoCompletion_meromorphicAt (P : Polynomial ℂ) {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (s : ℂ) : MeromorphicAt (poleClearedDegreeTwoCompletion P H) s := by
  have hPA : AnalyticAt ℂ (fun z => P.eval z) s :=
    P.differentiable.differentiableOn.analyticAt Filter.univ_mem
  have hden : AnalyticAt ℂ (fun z => 2 * P.eval z * z ^ 2 * (z - 1) ^ 2) s := by fun_prop
  exact (hH.differentiableOn.analyticAt Filter.univ_mem).meromorphicAt.div hden.meromorphicAt

/-- Outside the clearing polynomial's roots and the endpoints, the representative is analytic. -/
theorem poleClearedDegreeTwoCompletion_analyticAt (P : Polynomial ℂ) {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) {s : ℂ} (hP : P.eval s ≠ 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (poleClearedDegreeTwoCompletion P H) s := by
  have hPA : AnalyticAt ℂ (fun z => P.eval z) s :=
    P.differentiable.differentiableOn.analyticAt Filter.univ_mem
  have hden : AnalyticAt ℂ (fun z => 2 * P.eval z * z ^ 2 * (z - 1) ^ 2) s := by fun_prop
  exact (hH.differentiableOn.analyticAt Filter.univ_mem).div hden
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hP) (pow_ne_zero _ hs0))
      (pow_ne_zero _ (sub_ne_zero.mpr hs1)))

/-- The right contour half-plane is zero-free for xi. -/
theorem xi_ne_zero_right {s : ℂ} (hs : 2 ≤ s.re) : xi s ≠ 0 := by
  have hspos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hζ : riemannZeta s ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by norm_num) (norm_riemannZeta_ge_of_two_le_re hs))
  have hn := mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
    (Complex.Gammaℝ_ne_zero_of_re_pos hspos)) hζ
  intro hzero
  have hxi := MaassZetaSquaredConverse.two_xi_eq hspos hs1
  rw [hzero, mul_zero] at hxi
  exact hn hxi.symm

/-- Exact deficit orders exclude spurious right-half-plane roots of the clearing polynomial. -/
theorem deficitPolynomial_ne_zero_right {E : ℂ → ℂ} (P : Polynomial ℂ)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {s : ℂ} (hs : 2 ≤ s.re) : P.eval s ≠ 0 := by
  have hxiord : analyticOrderAt xi s = 0 :=
    (xi_analyticOnNhd_univ s (mem_univ _)).analyticOrderAt_eq_zero.mpr (xi_ne_zero_right hs)
  have hd : xiDeficit E s = 0 := by simp [xiDeficit, analyticOrderNatAt, hxiord]
  apply (P.differentiable.differentiableOn.analyticAt
    (s := univ) Filter.univ_mem).analyticOrderAt_eq_zero.mp
  rw [hord s, hd, Nat.cast_zero]

/-- This representative agrees with the completed Dirichlet-series quotient on the right. -/
theorem poleClearedDegreeTwoCompletion_eq_right {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {s : ℂ} (hs : 2 ≤ s.re) :
    poleClearedDegreeTwoCompletion P H s = Complex.Gammaℝ s ^ 2 *
      LSeries g s / riemannZeta s := by
  have hP := deficitPolynomial_ne_zero_right P hord hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by intro h; norm_num [h] at hs)
  rw [poleClearedDegreeTwoCompletion, cubicQuotient_eq_right hD P hfac hs]
  field_simp

/-- All vertical decay orders hold beyond one height, derived from the actual cubic datum. -/
theorem poleClearedDegreeTwoCompletion_rapid_tail {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (P : Polynomial ℂ) (hP : P ≠ 0)
    (hH : Differentiable ℂ H) (hHfinite : FiniteOrderEnvelope H)
    (hfac : ∀ z, P.eval z * E z = H z * xi z) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      -1 ≤ s.re → s.re ≤ 2 → T ≤ |s.im| →
      ‖poleClearedDegreeTwoCompletion P H s‖ ≤ C / (1 + |s.im|) ^ N := by
  obtain ⟨c, hc, R, hR⟩ := exists_radius_norm_polynomial_ge hP
  refine ⟨max 1 R, le_max_left _ _, fun N => ?_⟩
  obtain ⟨B, hB, hb⟩ := cubicQuotient_polynomial_strip_bounded hD P (X ^ N) hH hHfinite hfac
  refine ⟨2 ^ N * B / (2 * c), by positivity, fun s hs₁ hs₂ ht => ?_⟩
  have ht1 : 1 ≤ |s.im| := (le_max_left 1 R).trans ht
  have htnorm : R ≤ ‖s‖ := ((le_max_right 1 R).trans ht).trans (Complex.abs_im_le_norm s)
  have hnorm : 1 ≤ ‖s‖ := ht1.trans (Complex.abs_im_le_norm s)
  have hsub : 1 ≤ ‖s - 1‖ := by
    have hi := Complex.abs_im_le_norm (s - 1)
    simpa using ht1.trans (by simpa using hi)
  have hden : 2 * c ≤ ‖2 * P.eval s * s ^ 2 * (s - 1) ^ 2‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    norm_num only [norm_ofNat]
    calc
      2 * c = 2 * c * (1 : ℝ) ^ 2 * 1 ^ 2 := by ring
      _ ≤ 2 * ‖P.eval s‖ * ‖s‖ ^ 2 * ‖s - 1‖ ^ 2 := by
        gcongr
        exact hR s htnorm
  have hw : (1 + |s.im|) ^ N * ‖H s‖ ≤ 2 ^ N * B := by
    have hbase : 1 + |s.im| ≤ 2 * ‖s‖ := by linarith [Complex.abs_im_le_norm s]
    have hpoly : ‖s‖ ^ N * ‖H s‖ ≤ B := by
      simpa only [Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow] using hb s hs₁ hs₂
    calc
      (1 + |s.im|) ^ N * ‖H s‖ ≤ (2 * ‖s‖) ^ N * ‖H s‖ := by gcongr
      _ = 2 ^ N * (‖s‖ ^ N * ‖H s‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ N * B := mul_le_mul_of_nonneg_left hpoly (by positivity)
  have hnormC : ‖poleClearedDegreeTwoCompletion P H s‖ ≤ ‖H s‖ / (2 * c) := by
    rw [poleClearedDegreeTwoCompletion, norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden
  rw [le_div_iff₀ (by positivity : 0 < (1 + |s.im|) ^ N)]
  calc
    ‖poleClearedDegreeTwoCompletion P H s‖ * (1 + |s.im|) ^ N ≤
        (‖H s‖ / (2 * c)) * (1 + |s.im|) ^ N :=
      mul_le_mul_of_nonneg_right hnormC (by positivity)
    _ = ((1 + |s.im|) ^ N * ‖H s‖) / (2 * c) := by ring
    _ ≤ (2 ^ N * B) / (2 * c) := div_le_div_of_nonneg_right hw (by positivity)

/-- No decay premise is added: the original datum supplies the representative and every tail bound. -/
theorem degreeThree_infiniteDeficits_or_rapidCompletion {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0) :
    (xiDeficitSupport E).Infinite ∨
      ∃ (P : Polynomial ℂ) (H : ℂ → ℂ), P.Monic ∧ P.eval 1 ≠ 0 ∧
        (∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞)) ∧
        Differentiable ℂ H ∧ FiniteOrderEnvelope H ∧ H 1 ≠ 0 ∧
        (∀ z, P.eval z * E z = H z * xi z) ∧
        (∀ s : ℂ, 2 ≤ s.re → poleClearedDegreeTwoCompletion P H s =
          Complex.Gammaℝ s ^ 2 * LSeries g s / riemannZeta s) ∧
        ∃ T : ℝ, 1 ≤ T ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
          -1 ≤ s.re → s.re ≤ 2 → T ≤ |s.im| →
          ‖poleClearedDegreeTwoCompletion P H s‖ ≤ C / (1 + |s.im|) ^ N := by
  rcases degreeThree_infiniteDeficits_or_poleCleared hD hE1 with h | ⟨P, H, hm, hp, ho, hd, hg, h₁, hf⟩
  · exact Or.inl h
  · exact Or.inr ⟨P, H, hm, hp, ho, hd, hg, h₁, hf,
      fun _ hs => poleClearedDegreeTwoCompletion_eq_right hD P hf ho hs,
      poleClearedDegreeTwoCompletion_rapid_tail hD P hm.ne_zero hd hg hf⟩

end RHTower.WeilHigherDenominator
