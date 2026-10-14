import GaloisForLFunctions.RHTower.HerglotzWeilPositiveBridge
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional

/-!
# Every Herglotz producer is the von Mangoldt producer

Let `lam : ℕ → ℝ` satisfy `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1`, and let `Φ` be holomorphic on
`Re s > ½` with `Re Φ ≥ 0` there and

`Φ(s) = ½ψ(s/2) − ½ log π + 1/s + 1/(s − 1) − Σ_{n≥2} lam(n) n^{−s}`  on `Re s > 1`.

**Theorem** (`herglotzProducer_eq_vonMangoldt`).  `lam(n) = Λ(n)` for every `n ≥ 2`, and the
Riemann hypothesis holds.  No hypothesis on the boundary measure of `Φ` (atoms, locks, growth of a
quotient) is needed.

Proof.  Herglotz positivity makes `lam` full-cone Weil-positive (`weilPositiveFull_of_herglotz`),
and the Weil cone is `{Λ}` under RH and empty otherwise
(`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`).

Conversely (`riemannHypothesis_iff_exists_herglotzProducer`), RH holds exactly when some real
weight sequence has a Herglotz Weil function; the weights are then forced to be `Λ`.
-/

open Complex

noncomputable section

namespace RHTower.AtomDomination

/-- **Herglotz producers are unique.**  A Herglotz continuation of the Weil function of `lam` forces
`lam = Λ` on `n ≥ 2` and the Riemann hypothesis. -/
theorem herglotzProducer_eq_vonMangoldt {lam : ℕ → ℝ} {Φ : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = WeilHerglotz.weilFunction lam s) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp
    (weilPositiveFull_of_herglotz hsl hΦd hΦre hΦ)

/-- **RH is the existence of a Herglotz producer.**  The Riemann hypothesis holds exactly when some
real weight sequence of at most polynomial growth on average has a Weil function with a Herglotz
continuation to `Re s > ½`. -/
theorem riemannHypothesis_iff_exists_herglotzProducer :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ,
      (∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) ∧
      ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
        (∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) ∧
        ∀ s : ℂ, 1 < s.re → Φ s = WeilHerglotz.weilFunction lam s := by
  constructor
  · intro hRH
    set lam : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n with hlam
    have hW : WeilPositiveFull lam :=
      riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH
    have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
      intro σ hσ
      have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
        (by simpa using hσ)).norm
      refine h.congr fun n => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [LSeries.term, hlam]
      · rw [LSeries.term_of_ne_zero hn.ne', norm_div, Complex.norm_natCast_cpow_of_pos hn,
          Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]
    exact ⟨lam, hsl, (weilPositiveFull_iff_exists_herglotz hsl).mp hW⟩
  · rintro ⟨lam, hsl, Φ, hΦd, hΦre, hΦ⟩
    exact (herglotzProducer_eq_vonMangoldt hsl hΦd hΦre hΦ).1

end RHTower.AtomDomination
