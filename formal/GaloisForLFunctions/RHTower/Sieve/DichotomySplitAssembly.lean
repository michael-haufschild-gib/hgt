import GaloisForLFunctions.RHTower.Sieve.HalaszWindowMeasurable
import GaloisForLFunctions.RHTower.Sieve.TruncatedPrimeSieveMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LSeriesTrivialSize
import GaloisForLFunctions.RHTower.Sieve.GhsStepFourTruncated
/-!
# The truncated three-factor integral, split by the dichotomy

For a threshold `c`, let `S` be the set of heights where the bounded factor exceeds `c`.  The split of the
three-factor inequality gives

`‖∫_{|y| ≤ T} L(a)L(b)L(f)·W‖
    ≤ (trivial size of L(f))·Wsup·√(|S|·(ℓ¹a)²)·√(|S|·(ℓ¹b)²) + c·Wsup·√(sieve a)·√(sieve b)`,

with `|S|` the measure of `S` inside the height range.  On `S` the third factor keeps only its trivial size, but
the mean squares are charged to `|S|`; off `S` the factor is at most `c` by the definition of `S`, and the mean
squares are the Selberg-sieve ones.

Nothing is assumed about `c` beyond `c ≥ 0`: the statement holds for every threshold.  The arithmetic chooses `c`
to be the damped bound of the Halász dichotomy, `(1 + 1/(σ−1))exp(7/2 + 2(σ−1)(log z + log 4) − δ²)`, where the
corpus's `volume_halaszLargeValues_le` makes `|S|` small — and that is the shape in which the mean square finally
buys something, the trivial size appearing only against a short set.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Finset

/-- **The truncated three-factor integral, split by the dichotomy.**  For any threshold `c`, let `S` be the set
of heights where the bounded factor exceeds `c`.  On `S` the factor keeps only its trivial size but the mean
squares are charged to the measure of `S`; off `S` the factor is at most `c` and the mean squares are the
Selberg-sieve ones.  Nothing is assumed about `c`: the arithmetic later chooses it to be the damped bound of the
dichotomy, where the measure of `S` is small. -/
theorem norm_integral_Icc_mul_three_le_dichotomy {a b f : ℕ → ℂ} {sa sb : Finset ℕ}
    (hs0a : (0 : ℕ) ∉ sa) (hsuppa : ∀ n : ℕ, a n ≠ 0 → n ∈ sa)
    (hprimea : ∀ n ∈ sa, a n ≠ 0 → n.Prime)
    (hs0b : (0 : ℕ) ∉ sb) (hsuppb : ∀ n : ℕ, b n ≠ 0 → n ∈ sb)
    (hprimeb : ∀ n ∈ sb, b n ≠ 0 → n.Prime)
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {T : ℝ} (hT : 0 < T) {c : ℝ} (hc0 : 0 ≤ c)
    {W : ℝ → ℂ} {Wsup : ℝ} (hWsup0 : 0 ≤ Wsup) (hW : ∀ y : ℝ, ‖W y‖ ≤ Wsup)
    (hint : Integrable (fun y : ℝ => (LSeries a ((σ : ℂ) + (y : ℝ) * I)
        * LSeries b ((σ : ℂ) + (y : ℝ) * I) * LSeries f ((σ : ℂ) + (y : ℝ) * I)) * W y)
      (volume.restrict (Set.Icc (-T) T)))
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    ‖∫ y in Set.Icc (-T) T, (LSeries a ((σ : ℂ) + (y : ℝ) * I)
          * LSeries b ((σ : ℂ) + (y : ℝ) * I) * LSeries f ((σ : ℂ) + (y : ℝ) * I)) * W y‖
      ≤ ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * Wsup
            * (Real.sqrt ((volume ({t : ℝ | c < ‖∑' n : ℕ,
                    twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖}
                  ∩ Set.Icc (-T) T)).toReal * (∑ n ∈ sa, ‖a n‖ * (n : ℝ) ^ (-σ)) ^ 2)
                * Real.sqrt ((volume ({t : ℝ | c < ‖∑' n : ℕ,
                    twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖}
                  ∩ Set.Icc (-T) T)).toReal * (∑ n ∈ sb, ‖b n‖ * (n : ℝ) ^ (-σ)) ^ 2))
        + c * Wsup * (Real.sqrt (truncSieveSum a sa σ T z Y)
            * Real.sqrt (truncSieveSum b sb σ T z Y)) := by
  classical
  set S : Set ℝ := {t : ℝ | c < ‖∑' n : ℕ,
    twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) n‖} with hS
  have hSmeas : MeasurableSet S := measurableSet_halaszLargeValues hbdd hσ c
  have hMtriv0 : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by
    have h1 : 0 < σ - 1 := by linarith
    positivity
  -- the two bounds on the third factor
  have hM₁ : ∀ y ∈ S, ‖LSeries f ((σ : ℂ) + (y : ℝ) * I)‖
      ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) :=
    fun y _ => norm_LSeries_line_le_trivial hf1 hmul hbdd hσ y
  have hM₂ : ∀ y ∈ Sᶜ, ‖LSeries f ((σ : ℂ) + (y : ℝ) * I)‖ ≤ c := by
    intro y hy
    have hne : ((σ : ℂ) + (y : ℝ) * I) ≠ 0 := by
      intro h
      have hre : ((σ : ℂ) + (y : ℝ) * I).re = σ := by simp
      rw [h] at hre
      simp at hre
      linarith
    rw [LSeries_eq_tsum_twistedSummand hne]
    exact norm_tsum_twistedSummand_le_of_not_mem hy
  -- continuity and integrability of the two prime polynomials
  have hcont1 : Continuous fun y : ℝ => LSeries a ((σ : ℂ) + (y : ℝ) * I) :=
    continuous_LSeries_line_of_support hs0a hsuppa σ
  have hcont2 : Continuous fun y : ℝ => LSeries b ((σ : ℂ) + (y : ℝ) * I) :=
    continuous_LSeries_line_of_support hs0b hsuppb σ
  have h1 : Integrable (fun y : ℝ => ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      (volume.restrict (Set.Icc (-T) T)) := (hcont1.norm.pow 2).integrableOn_Icc
  have h2 : Integrable (fun y : ℝ => ‖LSeries b ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      (volume.restrict (Set.Icc (-T) T)) := (hcont2.norm.pow 2).integrableOn_Icc
  -- the split
  have hsplit := GaloisForLFunctions.HTGeometry.norm_integral_mul_three_le_split
    (μ := volume.restrict (Set.Icc (-T) T)) hSmeas hMtriv0 hc0 hWsup0
    hcont1.aestronglyMeasurable.restrict hcont2.aestronglyMeasurable.restrict hM₁ hM₂ hW hint h1 h2
  refine hsplit.trans ?_
  -- the restricted set integrals are integrals over the intersections
  have hres : ∀ g : ℝ → ℝ, (∫ y in S, g y ∂(volume.restrict (Set.Icc (-T) T)))
      = ∫ y in S ∩ Set.Icc (-T) T, g y := by
    intro g
    rw [Measure.restrict_restrict hSmeas]
  have hrescompl : ∀ g : ℝ → ℝ, (∫ y in Sᶜ, g y ∂(volume.restrict (Set.Icc (-T) T)))
      = ∫ y in Sᶜ ∩ Set.Icc (-T) T, g y := by
    intro g
    rw [Measure.restrict_restrict hSmeas.compl]
  rw [hres, hres, hrescompl, hrescompl]
  refine add_le_add ?_ ?_
  · -- on the window: the short-set estimate
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hMtriv0 hWsup0)
    refine mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    · exact integral_normSq_LSeries_le_measure hs0a hsuppa σ (volume_inter_Icc_ne_top S T)
    · exact integral_normSq_LSeries_le_measure hs0b hsuppb σ (volume_inter_Icc_ne_top S T)
  · -- off the window: the truncated sieve estimate, after enlarging the set
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc0 hWsup0)
    have hmono : ∀ (g : ℕ → ℂ) (sg : Finset ℕ), (0 : ℕ) ∉ sg → (∀ n : ℕ, g n ≠ 0 → n ∈ sg) →
        (∫ y in Sᶜ ∩ Set.Icc (-T) T, ‖LSeries g ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
          ≤ ∫ y in Set.Icc (-T) T, ‖LSeries g ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 := by
      intro g sg hs0g hsuppg
      refine setIntegral_mono_set ?_ (Filter.Eventually.of_forall fun y => by positivity)
        (LE.le.eventuallyLE Set.inter_subset_right)
      exact ((continuous_LSeries_line_of_support hs0g hsuppg σ).norm.pow 2).integrableOn_Icc
    refine mul_le_mul (Real.sqrt_le_sqrt (le_trans (hmono a sa hs0a hsuppa) ?_))
      (Real.sqrt_le_sqrt (le_trans (hmono b sb hs0b hsuppb) ?_)) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    · rw [truncSieveSum]
      exact integral_Icc_normSq_LSeries_le_prime_sieve hs0a hsuppa hprimea σ hT z Y hY hYz hz hlog
    · rw [truncSieveSum]
      exact integral_Icc_normSq_LSeries_le_prime_sieve hs0b hsuppb hprimeb σ hT z Y hY hYz hz hlog

end RHTower.Sieve
end
