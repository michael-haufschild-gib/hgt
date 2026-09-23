import GaloisForLFunctions.RHTower.Sieve.CoprimeSignDensity

/-!
# The coprime square-root Möbius product-sign law

The whole chain, assembled.  Given the bilinear all-interval theorem at the three weights the
argument uses — `μ`, `μ²`, and `μ²·1_{p∤·}` at each rescaled parameter pair — both coprime sign
classes of the balanced pair space keep a density at least

    D²(1/2 - A) > 0,   D = 6/π²,  A = ∑_p (p+1)^{-2} ≤ 13/36.

Every step other than the bilinear theorem itself is proved unconditionally in this corpus.
-/

namespace RHTower.Sieve

open Filter Topology
open scoped ArithmeticFunction.Moebius

/-- **The card's Theorem `(3)`.**  Both coprime sign classes have density at least the margin. -/
theorem route_e_sign_density {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hMR1 : MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (hMR2 : MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ)) hh)
    (hMRp : ∀ p : ℕ, p.Prime → MRBilinearAt (coprimeSquarefreeWeight p)
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  have hboth := tendsto_signClass_of_MR hMR1 hMR2
  rcases hs with rfl | rfl
  · exact eventually_coprimeSignClass_ge (Or.inl rfl) hgrow hboth.1 hMRp hε
  · exact eventually_coprimeSignClass_ge (Or.inr rfl) hgrow hboth.2 hMRp hε

/-- **The margin is strictly positive**, so both sign classes are eventually nonempty. -/
theorem route_e_margin_pos :
    0 < squarefreeDensity ^ (2 : ℕ) / 2
      - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity :=
  coprime_margin_pos

/-- **Both sign classes are eventually nonempty.**  The card's stated consequence: every large
balanced window carries a coprime squarefree pair of each product sign. -/
theorem route_e_signClass_nonempty {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hMR1 : MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (hMR2 : MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ)) hh)
    (hMRp : ∀ p : ℕ, p.Prime → MRBilinearAt (coprimeSquarefreeWeight p)
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ))) :
    ∀ᶠ x in atTop, (coprimeSignClass x (hh x) s).Nonempty := by
  have hmargin := route_e_margin_pos
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  have hbound := route_e_sign_density hs hgrow hMR1 hMR2 hMRp
    (ε := (squarefreeDensity ^ (2 : ℕ) / 2
      - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity) / 2) (by linarith)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hhtop.eventually_gt_atTop (0 : ℝ), hbound]
    with x hx0 hhx hb
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hden : (0 : ℝ) < hh x * Real.sqrt x * Real.log 2 := by positivity
  have hpos : 0 < coprimeSignClassCount x (hh x) s
      / (hh x * Real.sqrt x * Real.log 2) := by linarith
  have hcard : 0 < coprimeSignClassCount x (hh x) s := by
    rcases lt_or_ge 0 (coprimeSignClassCount x (hh x) s) with hc | hc
    · exact hc
    · exact absurd hpos (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hc hden.le))
  rw [coprimeSignClassCount] at hcard
  refine Finset.card_pos.1 ?_
  exact_mod_cast hcard

end RHTower.Sieve
