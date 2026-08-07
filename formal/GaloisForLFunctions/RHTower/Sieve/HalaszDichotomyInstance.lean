import GaloisForLFunctions.RHTower.Sieve.DichotomySplitAssembly
/-!
# The Halász dichotomy substituted into the split

Taking the threshold to be the damped size of the series, `halaszDampedBound σ z δ`, the exceptional window of the
split becomes the corpus's large-value set, whose measure `volume_halaszLargeValues_le` bounds by
`halaszWindowMeasureBound T z δ`.  Hence

`‖∫_{|y| ≤ T} L(a)L(b)L(f)W‖
    ≤ (1+1/(σ−1))e^{7/2}·Wsup·(window measure)·(ℓ¹a)(ℓ¹b)
      + (damped bound)·Wsup·√(sieve a)·√(sieve b)`.

The first term carries the trivial size of the series, but only against the measure of a short window, and the
two square roots of `|S|(ℓ¹)²` combine into `|S|·(ℓ¹a)(ℓ¹b)` exactly.  The second carries the `e^{−δ²}` damping
over the whole range.  Both savings are present at once, which no earlier form of this estimate achieved: the
accountings that collapsed had the trivial size multiplying the entire height range.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Finset

/-- The damped size of a bounded multiplicative series off the exceptional window. -/
def halaszDampedBound (σ : ℝ) (z : ℕ) (δ : ℝ) : ℝ :=
  (1 + 1 / (σ - 1)) * Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2)

/-- The corpus's bound for the measure of the exceptional window inside `[−T, T]`. -/
def halaszWindowMeasureBound (T : ℝ) (z : ℕ) (δ : ℝ) : ℝ :=
  (2 * T * Real.log (z : ℝ) / Real.pi + 1) * (2 * Real.sqrt (2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z))

theorem halaszDampedBound_nonneg {σ : ℝ} (hσ : 1 < σ) (z : ℕ) (δ : ℝ) :
    0 ≤ halaszDampedBound σ z δ := by
  have h1 : 0 < σ - 1 := by linarith
  rw [halaszDampedBound]
  positivity

/-- **The Halász dichotomy substituted into the split.**  At the threshold `c = halaszDampedBound σ z δ` the
exceptional window is the corpus's large-value set, so its measure is bounded and

`‖∫_{|y| ≤ T} L(a)L(b)L(f)W‖
    ≤ (1+1/(σ−1))e^{7/2}·Wsup·(window measure)·(ℓ¹a)(ℓ¹b)
      + (damped bound)·Wsup·√(sieve a)·√(sieve b)`.

The first term carries the trivial size but only against the measure of a short window; the second carries the
`e^{−δ²}` damping over the whole range.  Both savings are present at once — which no earlier form of this
estimate achieved. -/
theorem norm_integral_Icc_mul_three_le_halasz {a b f : ℕ → ℂ} {sa sb : Finset ℕ}
    (hs0a : (0 : ℕ) ∉ sa) (hsuppa : ∀ n : ℕ, a n ≠ 0 → n ∈ sa)
    (hprimea : ∀ n ∈ sa, a n ≠ 0 → n.Prime)
    (hs0b : (0 : ℕ) ∉ sb) (hsuppb : ∀ n : ℕ, b n ≠ 0 → n ∈ sb)
    (hprimeb : ∀ n ∈ sb, b n ≠ 0 → n.Prime)
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {T : ℝ} (hT : 0 < T) {z : ℕ} (hz2 : 2 ≤ z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hWz : 0 < logSqWeight z)
    {W : ℝ → ℂ} {Wsup : ℝ} (hWsup0 : 0 ≤ Wsup) (hW : ∀ y : ℝ, ‖W y‖ ≤ Wsup)
    (hint : Integrable (fun y : ℝ => (LSeries a ((σ : ℂ) + (y : ℝ) * I)
        * LSeries b ((σ : ℂ) + (y : ℝ) * I) * LSeries f ((σ : ℂ) + (y : ℝ) * I)) * W y)
      (volume.restrict (Set.Icc (-T) T)))
    (z' Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z') (hz' : 2 ≤ z') (hlog : 0 < Real.log Y) :
    ‖∫ y in Set.Icc (-T) T, (LSeries a ((σ : ℂ) + (y : ℝ) * I)
          * LSeries b ((σ : ℂ) + (y : ℝ) * I) * LSeries f ((σ : ℂ) + (y : ℝ) * I)) * W y‖
      ≤ ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * Wsup
            * (halaszWindowMeasureBound T z δ
                * ((∑ n ∈ sa, ‖a n‖ * (n : ℝ) ^ (-σ)) * (∑ n ∈ sb, ‖b n‖ * (n : ℝ) ^ (-σ))))
        + halaszDampedBound σ z δ * Wsup
            * (Real.sqrt (truncSieveSum a sa σ T z' Y) * Real.sqrt (truncSieveSum b sb σ T z' Y)) := by
  classical
  set c : ℝ := halaszDampedBound σ z δ with hc
  have hc0 : 0 ≤ c := halaszDampedBound_nonneg hσ z δ
  set S : Set ℝ := {t : ℝ | c < ‖∑' n : ℕ,
    twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖} with hS
  have hMtriv0 : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by
    have h1 : 0 < σ - 1 := by linarith
    positivity
  have hvolbd : (volume (S ∩ Set.Icc (-T) T)).toReal ≤ halaszWindowMeasureBound T z δ := by
    refine ENNReal.toReal_le_of_le_ofReal ?_ ?_
    · rw [halaszWindowMeasureBound]
      have hlogz : 0 ≤ Real.log (z : ℝ) := by
        have h1 : (1 : ℝ) ≤ (z : ℝ) := by
          have := hz2
          exact_mod_cast this.trans' (by norm_num)
        exact Real.log_nonneg h1
      positivity
    · rw [hS, hc, halaszDampedBound, halaszWindowMeasureBound]
      exact volume_halaszLargeValues_le hf1 hmul hbdd hσ hz2 hδ hWz hT.le
  have hla : (0 : ℝ) ≤ ∑ n ∈ sa, ‖a n‖ * (n : ℝ) ^ (-σ) := sum_norm_mul_rpow_nonneg a sa σ
  have hlb : (0 : ℝ) ≤ ∑ n ∈ sb, ‖b n‖ * (n : ℝ) ^ (-σ) := sum_norm_mul_rpow_nonneg b sb σ
  refine le_trans (norm_integral_Icc_mul_three_le_dichotomy hs0a hsuppa hprimea hs0b hsuppb hprimeb
    hf1 hmul hbdd hσ hT hc0 hWsup0 hW hint z' Y hY hYz hz' hlog) ?_
  refine add_le_add ?_ (le_refl _)
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hMtriv0 hWsup0)
  -- the two square roots of `|S|·(ℓ¹)²` multiply to `|S|·(ℓ¹a)(ℓ¹b)`
  have hsq : ∀ (g : ℕ → ℂ) (sg : Finset ℕ), (0 : ℝ) ≤ ∑ n ∈ sg, ‖g n‖ * (n : ℝ) ^ (-σ) →
      Real.sqrt ((volume (S ∩ Set.Icc (-T) T)).toReal
          * (∑ n ∈ sg, ‖g n‖ * (n : ℝ) ^ (-σ)) ^ 2)
        = Real.sqrt ((volume (S ∩ Set.Icc (-T) T)).toReal)
            * (∑ n ∈ sg, ‖g n‖ * (n : ℝ) ^ (-σ)) := by
    intro g sg hg
    rw [Real.sqrt_mul ENNReal.toReal_nonneg, Real.sqrt_sq hg]
  rw [hsq a sa hla, hsq b sb hlb]
  have hvol0 : (0 : ℝ) ≤ (volume (S ∩ Set.Icc (-T) T)).toReal := ENNReal.toReal_nonneg
  have hsqrtsq : Real.sqrt ((volume (S ∩ Set.Icc (-T) T)).toReal)
      * Real.sqrt ((volume (S ∩ Set.Icc (-T) T)).toReal)
      = (volume (S ∩ Set.Icc (-T) T)).toReal := Real.mul_self_sqrt hvol0
  have hprod : Real.sqrt ((volume (S ∩ Set.Icc (-T) T)).toReal)
        * (∑ n ∈ sa, ‖a n‖ * (n : ℝ) ^ (-σ))
        * (Real.sqrt ((volume (S ∩ Set.Icc (-T) T)).toReal)
            * (∑ n ∈ sb, ‖b n‖ * (n : ℝ) ^ (-σ)))
      = (volume (S ∩ Set.Icc (-T) T)).toReal
          * ((∑ n ∈ sa, ‖a n‖ * (n : ℝ) ^ (-σ)) * (∑ n ∈ sb, ‖b n‖ * (n : ℝ) ^ (-σ))) := by
    have hrw : Real.sqrt ((volume (S ∩ Set.Icc (-T) T)).toReal)
          * (∑ n ∈ sa, ‖a n‖ * (n : ℝ) ^ (-σ))
          * (Real.sqrt ((volume (S ∩ Set.Icc (-T) T)).toReal)
              * (∑ n ∈ sb, ‖b n‖ * (n : ℝ) ^ (-σ)))
        = (Real.sqrt ((volume (S ∩ Set.Icc (-T) T)).toReal)
            * Real.sqrt ((volume (S ∩ Set.Icc (-T) T)).toReal))
            * ((∑ n ∈ sa, ‖a n‖ * (n : ℝ) ^ (-σ)) * (∑ n ∈ sb, ‖b n‖ * (n : ℝ) ^ (-σ))) := by
      ring
    rw [hrw, hsqrtsq]
  rw [hprod]
  exact mul_le_mul_of_nonneg_right hvolbd (mul_nonneg hla hlb)

end RHTower.Sieve
end
