import GaloisForLFunctions.HTGeometry.DigammaGaussSeries

/-!
# Digamma differences as reciprocal-difference series

`HTGeometry.DigammaGaussSeries.digamma_eq_neg_euler_add_tsum_gauss` gives Gauss's series
`ψ(s) = −γ + ∑ₙ (1/(n+1) − 1/(s+n))` on `Re s > 0`.  Subtracting two instances cancels both `γ` and the
harmonic terms and leaves the difference series

**`digamma_sub_eq_tsum` — `ψ(b) − ψ(a) = ∑ₙ (1/(a+n) − 1/(b+n))` for `Re a, Re b > 0`.**

This is the form every evaluation of a digamma difference consumes: sums of reciprocals over an arithmetic
progression are exactly such differences, and the Euler constant never appears.  It is a connector, not new
analysis — the content is in the Gauss series it rests on.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- **The digamma difference series.** -/
theorem digamma_sub_eq_tsum {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.digamma b - Complex.digamma a
      = ∑' n : ℕ, (1 / (a + (n : ℂ)) - 1 / (b + (n : ℂ))) := by
  have hsa := summable_gaussDigammaSeriesTerm ha
  have hsb := summable_gaussDigammaSeriesTerm hb
  have hva := digamma_eq_neg_euler_add_tsum_gauss ha
  have hvb := digamma_eq_neg_euler_add_tsum_gauss hb
  have hterm : ∀ n : ℕ,
      gaussDigammaSeriesTerm b n
        - gaussDigammaSeriesTerm a n
        = 1 / (a + (n : ℂ)) - 1 / (b + (n : ℂ)) := by
    intro n
    rw [gaussDigammaSeriesTerm,
      gaussDigammaSeriesTerm]
    ring
  have hsub : ∑' n : ℕ, (gaussDigammaSeriesTerm b n
      - gaussDigammaSeriesTerm a n)
      = (∑' n : ℕ, gaussDigammaSeriesTerm b n)
        - ∑' n : ℕ, gaussDigammaSeriesTerm a n :=
    hsb.tsum_sub hsa
  rw [← funext hterm, hsub, hva, hvb]
  ring

/-- The same, with the sum written as a single reciprocal difference of shifted arguments. -/
theorem hasSum_digamma_sub {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    HasSum (fun n : ℕ => 1 / (a + (n : ℂ)) - 1 / (b + (n : ℂ)))
      (Complex.digamma b - Complex.digamma a) := by
  have hsa := summable_gaussDigammaSeriesTerm ha
  have hsb := summable_gaussDigammaSeriesTerm hb
  have hterm : ∀ n : ℕ,
      gaussDigammaSeriesTerm b n
        - gaussDigammaSeriesTerm a n
        = 1 / (a + (n : ℂ)) - 1 / (b + (n : ℂ)) := by
    intro n
    rw [gaussDigammaSeriesTerm,
      gaussDigammaSeriesTerm]
    ring
  have hsummable : Summable (fun n : ℕ => 1 / (a + (n : ℂ)) - 1 / (b + (n : ℂ))) := by
    rw [← funext hterm]
    exact hsb.sub hsa
  rw [digamma_sub_eq_tsum ha hb]
  exact hsummable.hasSum

end RHTower

end
