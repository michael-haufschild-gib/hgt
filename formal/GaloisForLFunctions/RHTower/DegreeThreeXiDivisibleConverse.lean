import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorQuotientMellin

/-!
# A degree-three datum divisible by `ξ` is a multiple of `ζ³`

Let `g` be an absolutely convergent Dirichlet series on `Re s > 1` whose completion
`E(s) = (s(s−1)Γ_ℝ(s))³ L(g, s)` is entire of finite order, with `E(1 − s) = ±E(s)` and
`E(1) ≠ 0` (`WeilZetaPower.ZetaPowerDatum 3 g E`).  If every zero of `ξ` is a zero of `E` of at
least the same order, then the sign is `+1` and `L(g, s) = g(1) ζ(s)³` on `Re s > 1`
(`degreeThree_eq_zetaCube_of_xi_le`).  No Euler product, positivity, real-rootedness or
critical-line hypothesis enters.

**Proof.**  The quotient `H = E/ξ` is entire of finite order with `H(1) ≠ 0`, bounded on
`−1 ≤ Re s ≤ 2` (`degreeThree_infiniteDeficits_or_stripBounded`, with an empty deficit
divisor), and `H/2 = s²(s−1)²Γ_ℝ(s)² L(g ⋆ μ, s)` on `Re s > 1`.  `H` inherits the sign of `E`.
For the sign `+1`, the `ζ²` converse theorem applied to `g ⋆ μ + (1 − g(1)) d` (completion
`H/2 + (1 − g(1))(2ξ)²`) gives `g ⋆ μ = g(1) d`, so `L(g) = g(1)ζ³`.  For the sign `−1`, the odd
converse gives `g ⋆ μ = 0`, so `H` vanishes on `Re s > 1` and hence everywhere, contradicting
`H(1) ≠ 0`.
-/

noncomputable section

open Complex Set Filter Topology Polynomial

namespace RHTower.WeilHigherDenominator

open MaassZetaSquaredConverse

/-- A monic polynomial without complex roots is `1`. -/
private theorem monic_eq_one_of_eval_ne_zero {P : Polynomial ℂ} (hm : P.Monic)
    (h : ∀ z, P.eval z ≠ 0) : P = 1 := by
  refine Polynomial.eq_one_of_monic_natDegree_zero hm ?_
  by_contra hdeg
  obtain ⟨z, hz⟩ := Complex.exists_root (f := P) (by
    rw [Polynomial.degree_eq_natDegree hm.ne_zero]
    exact_mod_cast Nat.pos_of_ne_zero hdeg)
  exact h z (by simpa [IsRoot] using hz)

/-- An entire function vanishing on a neighbourhood of `3` vanishes identically. -/
private theorem eq_zero_of_eventually_zero_three {K : ℂ → ℂ} (hK : Differentiable ℂ K)
    (h : ∀ s : ℂ, 2 < s.re → K s = 0) (s : ℂ) : K s = 0 := by
  have hA : AnalyticOnNhd ℂ K univ := fun z _ => hK.analyticAt z
  have hev : K =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with z hz
    exact h z hz
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _) hev
    (mem_univ s)

/-- With full `ξ` divisibility, the cubic datum is `H · ξ` for an entire, strip-bounded `H`. -/
theorem degreeThree_xi_quotient_of_xi_le {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0)
    (hdiv : ∀ s, analyticOrderNatAt xi s ≤ analyticOrderNatAt E s) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ H 1 ≠ 0 ∧ (∀ z, E z = H z * xi z) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → ‖H s‖ ≤ B := by
  have hempty : xiDeficitSupport E = ∅ := by
    ext z
    simp only [xiDeficitSupport, mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
    exact hdiv z
  rcases degreeThree_infiniteDeficits_or_stripBounded hD hE1 with hinf |
      ⟨P, H, hm, _, ho, hH, _, hH1, hfac, hbd⟩
  · exact absurd (hempty ▸ finite_empty) hinf
  · have hP : P = 1 := by
      refine monic_eq_one_of_eval_ne_zero hm fun z => ?_
      have hz : analyticOrderAt (fun w => P.eval w) z = 0 := by
        rw [ho z]
        have : xiDeficit E z = 0 := by
          simp only [xiDeficit]
          exact Nat.sub_eq_zero_of_le (hdiv z)
        simp [this]
      exact (P.differentiable.differentiableOn.analyticAt
        (s := univ) Filter.univ_mem).analyticOrderAt_eq_zero.mp hz
    subst hP
    obtain ⟨B, hB, hb⟩ := hbd 1
    refine ⟨H, hH, hH1, fun z => by simpa using hfac z, B, hB, fun s h₁ h₂ => ?_⟩
    simpa using hb s h₁ h₂

/-- The quotient is the completed degree-two series of `g ⋆ μ` on `Re s > 1`. -/
theorem xiQuotient_eq_degreeTwo {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hfac : ∀ z, E z = H z * xi z)
    {s : ℂ} (hs : 1 < s.re) :
    H s / 2 = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 *
      LSeries (degreeTwoQuotientCoeff g) s := by
  have hspos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hΓ := Complex.Gammaℝ_ne_zero_of_re_pos hspos
  have hζ := riemannZeta_ne_zero_of_one_lt_re hs
  have hA : s * (s - 1) * Complex.Gammaℝ s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hΓ
  have hxi := two_xi_eq hspos hs1
  rw [LSeries_degreeTwoQuotientCoeff (hD.summable s hs) hs]
  apply mul_right_cancel₀ (mul_ne_zero hA hζ)
  calc
    H s / 2 * (s * (s - 1) * Complex.Gammaℝ s * riemannZeta s) = H s * xi s := by
      rw [← hxi]
      ring
    _ = E s := (hfac s).symm
    _ = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * (LSeries g s / riemannZeta s) *
        (s * (s - 1) * Complex.Gammaℝ s * riemannZeta s) := by
      rw [hD.completion s hs]
      field_simp

/-- The quotient inherits the sign of the cubic datum. -/
theorem xiQuotient_one_sub {E H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hfac : ∀ z, E z = H z * xi z) {ε : ℂ} (hsym : ∀ s, E (1 - s) = ε * E s) (s : ℂ) :
    H (1 - s) = ε * H s := by
  have hK : Differentiable ℂ fun z => H (1 - z) - ε * H z :=
    (hH.comp (differentiable_const 1 |>.sub differentiable_id)).sub (hH.const_mul ε)
  have h := eq_zero_of_eventually_zero_three hK (fun z hz => by
    have hxi : xi z ≠ 0 := xi_ne_zero_right hz.le
    have he : H (1 - z) * xi z = ε * H z * xi z := by
      calc H (1 - z) * xi z = H (1 - z) * xi (1 - z) := by rw [xi_one_sub]
        _ = E (1 - z) := (hfac (1 - z)).symm
        _ = ε * E z := hsym z
        _ = ε * H z * xi z := by rw [hfac z]; ring
    have := mul_right_cancel₀ hxi he
    simp [this]) s
  exact sub_eq_zero.mp h

/-- **Degree-three converse under `ξ` divisibility.**  A cubic datum whose completion vanishes at
every zero of `ξ` to at least the same order has sign `+1` and is `g(1) ζ³` on `Re s > 1`. -/
theorem degreeThree_eq_zetaCube_of_xi_le {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0)
    (hdiv : ∀ s, analyticOrderNatAt xi s ≤ analyticOrderNatAt E s) :
    (∀ s, E (1 - s) = E s) ∧
      ∀ s : ℂ, 1 < s.re → LSeries g s = g 1 * riemannZeta s ^ 3 := by
  obtain ⟨H, hH, hH1, hfac, B, hB, hb⟩ := degreeThree_xi_quotient_of_xi_le hD hE1 hdiv
  set f := degreeTwoQuotientCoeff g with hfdef
  have hfsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖f n‖ * (n : ℝ) ^ (-σ) :=
    fun σ hσ => degreeTwoQuotientCoeff_weighted_summable hD hσ
  have heqf : ∀ s : ℂ, 1 < s.re →
      H s / 2 = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries f s :=
    fun s hs => xiQuotient_eq_degreeTwo hD hfac hs
  have hbdH : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖H s / 2‖ ≤ B :=
    ⟨B, fun s h₁ h₂ => by
      rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
      have := hb s (by linarith) (by linarith)
      linarith [norm_nonneg (H s)]⟩
  have hHdiff : Differentiable ℂ fun s => H s / 2 := hH.div_const 2
  -- the odd sign is impossible
  have heven : ∀ s, E (1 - s) = E s := by
    rcases hD.functional_equation with h | hodd
    · exact h
    · exfalso
      have hHodd : ∀ s, H s / 2 * 0 + H (1 - s) / 2 = -(H s / 2) := fun s => by
        rw [xiQuotient_one_sub hH hfac (ε := -1) (fun z => by rw [hodd]; ring) s]
        ring
      have hf0 : ∀ m : ℕ, 1 ≤ m → f m = 0 := fun m hm =>
        coeff_eq_zero_of_odd_functional_equation hfsum hHdiff
          (fun s => by simpa using hHodd s) heqf hbdH hm
      have hL : ∀ s : ℂ, 1 < s.re → LSeries f s = 0 := fun s _ => by
        rw [LSeries_congr (g := fun _ => (0 : ℂ)) (fun {n} hn => hf0 n (Nat.one_le_iff_ne_zero.mpr hn))]
        exact congrFun LSeries_zero s
      have hH0 := eq_zero_of_eventually_zero_three hH (fun s hs => by
        have h := heqf s (by linarith)
        rw [hL s (by linarith), mul_zero] at h
        linear_combination 2 * h) 1
      exact hH1 hH0
  refine ⟨heven, fun s hs => ?_⟩
  have hHeven : ∀ s, H (1 - s) = H s := fun s => by
    simpa using xiQuotient_one_sub hH hfac (ε := 1) (fun z => by rw [heven]; ring) s
  -- the `ζ²` converse for `f + (1 − f 1) d`
  set c : ℂ := 1 - f 1 with hc
  set f' : ℕ → ℂ := fun n => f n + c * divisorCount n with hf'
  have hf'sum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖f' n‖ * (n : ℝ) ^ (-σ) := by
    intro σ hσ
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((hfsum σ hσ).add ((summable_divisorCount hσ).mul_left ‖c‖))
    have hn : 0 ≤ (n : ℝ) ^ (-σ) := by positivity
    calc ‖f' n‖ * (n : ℝ) ^ (-σ)
        ≤ (‖f n‖ + ‖c‖ * ‖divisorCount n‖) * (n : ℝ) ^ (-σ) := by
          apply mul_le_mul_of_nonneg_right _ hn
          simpa [f', norm_mul] using norm_add_le (f n) (c * divisorCount n)
      _ = ‖f n‖ * (n : ℝ) ^ (-σ) + ‖c‖ * (‖divisorCount n‖ * (n : ℝ) ^ (-σ)) := by ring
  have hf'1 : f' 1 = 1 := by simp [f', hc, divisorCount_one]
  have hΛ' : Differentiable ℂ fun s => H s / 2 + c * zetaSqCompleted s :=
    hHdiff.add (differentiable_zetaSqCompleted.const_mul c)
  have hsym' : ∀ s, H (1 - s) / 2 + c * zetaSqCompleted (1 - s) =
      H s / 2 + c * zetaSqCompleted s := fun s => by
    rw [hHeven, zetaSqCompleted_one_sub]
  have heq' : ∀ s : ℂ, 1 < s.re → H s / 2 + c * zetaSqCompleted s =
      s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries f' s := by
    intro s hs
    have hsumf : LSeriesSummable f s := degreeTwoQuotientCoeff_summable (hD.summable s hs) hs
    have hsumd : LSeriesSummable (c • divisorCount) s :=
      (LSeriesSummable_divisorCount hs).smul c
    have hLf' : LSeries f' s = LSeries f s + c * LSeries divisorCount s := by
      rw [show f' = f + c • divisorCount from rfl, LSeries_add hsumf hsumd,
        LSeries_smul]
    rw [heqf s hs, zetaSqCompleted_eq hs, hLf']
    ring
  have hbd' : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      ‖H s / 2 + c * zetaSqCompleted s‖ ≤ B := by
    obtain ⟨B₁, hb₁⟩ := hbdH
    obtain ⟨B₂, hb₂⟩ := exists_bound_zetaSqCompleted
    refine ⟨B₁ + ‖c‖ * B₂, fun s h₁ h₂ => ?_⟩
    calc ‖H s / 2 + c * zetaSqCompleted s‖ ≤ ‖H s / 2‖ + ‖c‖ * ‖zetaSqCompleted s‖ := by
          simpa [norm_mul] using norm_add_le (H s / 2) (c * zetaSqCompleted s)
      _ ≤ B₁ + ‖c‖ * B₂ := add_le_add (hb₁ s h₁ h₂)
          (mul_le_mul_of_nonneg_left (hb₂ s h₁ h₂) (norm_nonneg c))
  have hcoef : ∀ n : ℕ, n ≠ 0 → f n = f 1 * divisorCount n := fun n hn => by
    have h := coeff_eq_divisorCount_of_functional_equation hf'sum hf'1 hΛ' hsym' heq' hbd'
      (Nat.one_le_iff_ne_zero.mpr hn)
    simp only [f', hc] at h
    linear_combination h
  have hLf : LSeries f s = f 1 * riemannZeta s ^ 2 := by
    rw [LSeries_congr (g := f 1 • divisorCount) (fun {n} hn => hcoef n hn),
      LSeries_smul, LSeries_divisorCount hs]
  have hq := LSeries_degreeTwoQuotientCoeff (hD.summable s hs) hs
  have hζ := riemannZeta_ne_zero_of_one_lt_re hs
  have hf1 : f 1 = g 1 := degreeTwoQuotientCoeff_one g
  rw [← hfdef, hLf, hf1, eq_div_iff hζ] at hq
  rw [← hq]
  ring

/-- An odd cubic datum never contains a full copy of the `ξ` divisor. -/
theorem exists_xiDeficit_of_odd {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0)
    (hodd : ∀ s, E (1 - s) = -E s) :
    ∃ ρ : ℂ, analyticOrderNatAt E ρ < analyticOrderNatAt xi ρ := by
  by_contra h
  push Not at h
  have heven := (degreeThree_eq_zetaCube_of_xi_le hD hE1 h).1
  have a := heven 1
  have b := hodd 1
  rw [sub_self] at a b
  exact hE1 (by linear_combination (b - a) / 2)

end RHTower.WeilHigherDenominator
