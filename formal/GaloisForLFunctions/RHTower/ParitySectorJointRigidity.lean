import GaloisForLFunctions.RHTower.EvenSectorAbelRigidity

/-!
# Joint parity rigidity: odd positivity and even pole-free positivity

**Theorem** (`riemannHypothesis_of_weilPositiveOddAt_of_weilPositiveEvenPolar`).  Let real weights
`lam` be Weil-positive on odd tests at some pole weight `β ≥ 0`, and Weil-positive on even tests
whose transform vanishes at `i/2`.  Then RH holds and `lam = Λ` on `n ≥ 2`.

At `β = 0` neither hypothesis involves the pole: both say that the form
`A(f) − Σ_{n ≥ 2} lam(n) n^{−1/2} (k_f(log n) + k_f(−log n))` (archimedean energy minus prime
pairing, `k_f = f ⋆ f̃`) is nonnegative, on odd tests and on even pole-free tests.  These span the
primitive hyperplane `f̂(i/2) + f̂(−i/2) = 0` of real tests.  So the primitive-hyperplane positivity
criterion has exactly one certificate, `Λ`, and it exists iff RH
(`riemannHypothesis_iff_exists_weilPositiveOddAt_zero_weilPositiveEvenPolar`).

Proof.  The odd sector supplies what the even Abel pinning needs: absolute convergence on
`Re s > 1` (`summable_abs_div_rpow_of_weilPositiveOddAt`), the log-density ceiling
(`odd_log_density_le`), and the lower far-bump bound, whose Laplace transform gives
`K(s) F(s) ≥ −C` and hence no negative double pole (`eventually_neg_le_of_weilPositiveOddAt`).
Even pole-free positivity then gives `W(g) ≥ 0` for every real even test
(`realWeil_nonneg_of_polar`),
so `lam` is even-positive at pole weight one, which is RH with `lam = Λ`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open OddSector WeilOneSided WeilPoleWeight

/-- **No negative double pole from odd positivity.**  At a pole weight `β ≥ 0`, the odd far bumps
give `K(s) F(s) ≥ −2|2βJ² + A₀|`, so `s² F(s) ≥ −O(s²)`. -/
theorem eventually_neg_le_of_weilPositiveOddAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) (hβ : 0 ≤ β) :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s) := by
  have hsl := fun σ (hσ : 1 < σ) => summable_abs_div_rpow_of_weilPositiveOddAt h hβ hσ
  intro ε hε
  set C₂ := 2 * |2 * β * farJ ^ 2 + farArchConst| with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hJ2 : 0 < farJ ^ 2 := pow_pos farJ_pos 2
  have hδpos : 0 < min 1 (ε * farJ ^ 2 / (2 * C₂ + 1)) := lt_min one_pos (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδpos)] with s hs hsδ
  have hs' : 0 < s := hs
  have hs1 : s ≤ 1 := (hsδ.trans_le (min_le_left _ _)).le
  have hsε : s < ε * farJ ^ 2 / (2 * C₂ + 1) := hsδ.trans_le (min_le_right _ _)
  have hlow := farLaplace_lower h hβ hsl hs'
  have hKF : -C₂ ≤ farLaplace s * oddDirichlet lam s := by
    have h1 : 0 ≤ β * farJ ^ 2 / (2 * s) := by positivity
    have h2 : (2 * β * farJ ^ 2 + farArchConst) / (1 + 2 * s) ≤
        |2 * β * farJ ^ 2 + farArchConst| := by
      rw [div_le_iff₀ (by linarith)]
      have := le_abs_self (2 * β * farJ ^ 2 + farArchConst)
      have := abs_nonneg (2 * β * farJ ^ 2 + farArchConst)
      nlinarith
    rw [hC₂]
    linarith
  have hK : farJ ^ 2 / 2 ≤ farLaplace s := by
    have h1 := farLaplace_ge hs'.le
    rw [farLaplace_zero] at h1
    have h2 : (1 : ℝ) / 2 ≤ Real.exp (-(s / 6)) := by
      have := Real.add_one_le_exp (-(s / 6))
      linarith
    nlinarith
  have hKpos : 0 < farLaplace s := lt_of_lt_of_le (by positivity) hK
  have hF : -(2 * C₂ / farJ ^ 2) ≤ oddDirichlet lam s := by
    have h1 : -C₂ / farLaplace s ≤ oddDirichlet lam s := by
      rw [div_le_iff₀ hKpos]; linarith
    have h2 : C₂ / farLaplace s ≤ 2 * C₂ / farJ ^ 2 := by
      rw [div_le_div_iff₀ hKpos hJ2]; nlinarith
    have h3 : -C₂ / farLaplace s = -(C₂ / farLaplace s) := by ring
    linarith
  have hs2 : s * s ≤ s := by nlinarith
  have hfin : s * s * (2 * C₂ / farJ ^ 2) ≤ ε := by
    have h1 : s * (2 * C₂ + 1) < ε * farJ ^ 2 := by rwa [lt_div_iff₀ (by positivity)] at hsε
    have h2 : s * s * (2 * C₂ / farJ ^ 2) ≤ s * (2 * C₂ / farJ ^ 2) :=
      mul_le_mul_of_nonneg_right hs2 (by positivity)
    have h3 : s * (2 * C₂ / farJ ^ 2) ≤ ε := by
      rw [show s * (2 * C₂ / farJ ^ 2) = s * (2 * C₂) / farJ ^ 2 by ring, div_le_iff₀ hJ2]
      nlinarith
    linarith
  have hmul := mul_le_mul_of_nonneg_left hF (mul_nonneg hs'.le hs'.le)
  nlinarith

/-- **Joint parity rigidity.**  Odd positivity at a nonnegative pole weight and even pole-free
positivity force RH and `lam = Λ`. -/
theorem riemannHypothesis_of_weilPositiveOddAt_of_weilPositiveEvenPolar {β : ℝ} {lam : ℕ → ℝ}
    (ho : WeilPositiveOddAt β lam) (hβ : 0 ≤ β) (hpf : WeilPositiveEvenPolar lam) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hsl := fun σ (hσ : 1 < σ) => summable_abs_div_rpow_of_weilPositiveOddAt ho hβ hσ
  have hup := eventually_le_one_add_of_log_density_le hsl fun _ hε => odd_log_density_le ho hε
  have hdp := eventually_neg_le_of_weilPositiveOddAt ho hβ
  exact weilPositiveEvenAt_one_iff.mp (weilPositiveEvenAt_one_of_real fun _ hg hgc hge =>
    realWeil_nonneg_of_polar hpf hsl hup hdp hg hgc hge)

/-- Odd positivity at a nonnegative pole weight and even positivity at any pole weight force RH and
`lam = Λ`. -/
theorem riemannHypothesis_of_weilPositiveOddAt_of_weilPositiveEvenAt {β₀ β₁ : ℝ} {lam : ℕ → ℝ}
    (ho : WeilPositiveOddAt β₀ lam) (hβ₀ : 0 ≤ β₀) (he : WeilPositiveEvenAt β₁ lam) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  riemannHypothesis_of_weilPositiveOddAt_of_weilPositiveEvenPolar ho hβ₀
    (weilPositiveEvenPolar_of_weilPositiveEvenAt he)

/-- **RH is pole-free positivity on the primitive hyperplane, with a unique certificate.**  RH holds
iff some weights make the archimedean-minus-prime form nonnegative on odd tests (pole weight `0`)
and on even pole-free tests. -/
theorem riemannHypothesis_iff_exists_weilPositiveOddAt_zero_weilPositiveEvenPolar :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveOddAt 0 lam ∧ WeilPositiveEvenPolar lam := by
  constructor
  · intro hRH
    exact ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      (riemannHypothesis_iff_weilPositiveOddAt_vonMangoldt (by norm_num)).mp hRH,
      weilPositiveEvenPolar_of_weilPositiveEvenAt
        (weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩)⟩
  · rintro ⟨lam, ho, hpf⟩
    exact (riemannHypothesis_of_weilPositiveOddAt_of_weilPositiveEvenPolar ho le_rfl hpf).1

/-- The certificate of primitive-hyperplane positivity is unique. -/
theorem eq_vonMangoldt_of_weilPositiveOddAt_zero_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (ho : WeilPositiveOddAt 0 lam) (hpf : WeilPositiveEvenPolar lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  (riemannHypothesis_of_weilPositiveOddAt_of_weilPositiveEvenPolar ho le_rfl hpf).2

end RHTower.EvenSector

end
