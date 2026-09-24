import GaloisForLFunctions.RHTower.XiHadamardPairOrdinateIntegral

/-!
# The falsification criterion

The pair law is effective in the negative direction as well.  If `Re (ξ'/ξ)(s) < 0` at any point
right of the critical line, then the disk bound must fail at some divisor copy, which therefore
lies off the critical line: one negative value **locates** a counterexample.

Combined with the equivalence of `XiLogDerivReCriterion` this gives

```text
¬ RiemannHypothesis  ↔  ∃ s, 1/2 < Re s ∧ Re (ξ'/ξ)(s) < 0 .
```

So refuting the Riemann hypothesis is exactly exhibiting one negative value of this real quantity
right of the critical line.
-/

open Complex

namespace RHTower

noncomputable section

/-- **A single negative value locates an off-line zero.**  If the completed logarithmic derivative
has negative real part at `s` right of the critical line, then some divisor copy lies in the closed
disk of radius `|Re ρ - 1/2|` about `1/2 + i Im ρ` containing `s`; in particular that copy is off
the critical line. -/
theorem exists_zero_disk_of_re_logDeriv_xi_neg {s : ℂ} (hs : 1 / 2 < s.re) (hxi : xi s ≠ 0)
    (hneg : (logDeriv xi s).re < 0) :
    ∃ q : XiZeroCopy,
      (s.re - 1 / 2) ^ 2 + (s.im - ((q.1 : ℂ)).im) ^ 2 ≤ (((q.1 : ℂ)).re - 1 / 2) ^ 2 := by
  by_contra hcon
  push Not at hcon
  exact absurd (re_logDeriv_xi_nonneg_of_disk_bound hs hxi fun q => hcon q) (not_le.mpr hneg)

/-- The located copy is genuinely off the critical line. -/
theorem exists_offLine_zero_of_re_logDeriv_xi_neg {s : ℂ} (hs : 1 / 2 < s.re) (hxi : xi s ≠ 0)
    (hneg : (logDeriv xi s).re < 0) :
    ∃ q : XiZeroCopy, ((q.1 : ℂ)).re ≠ 1 / 2 := by
  obtain ⟨q, hq⟩ := exists_zero_disk_of_re_logDeriv_xi_neg hs hxi hneg
  refine ⟨q, fun hline => ?_⟩
  rw [hline] at hq
  nlinarith [sq_nonneg (s.im - ((q.1 : ℂ)).im)]

/-- **Falsification criterion.**  A single point right of the critical line at which the completed
logarithmic derivative has negative real part refutes the Riemann hypothesis. -/
theorem not_riemannHypothesis_of_re_logDeriv_xi_neg {s : ℂ} (hs : 1 / 2 < s.re)
    (hneg : (logDeriv xi s).re < 0) : ¬ RiemannHypothesis := by
  intro hRH
  exact absurd (riemannHypothesis_iff_re_logDeriv_xi_nonneg.mp hRH s hs) (not_le.mpr hneg)

/-- Contrapositive form: refuting the Riemann hypothesis is exactly exhibiting one negative value
of `Re (ξ'/ξ)` right of the critical line. -/
theorem not_riemannHypothesis_iff_exists_re_logDeriv_xi_neg :
    ¬ RiemannHypothesis ↔ ∃ s : ℂ, 1 / 2 < s.re ∧ (logDeriv xi s).re < 0 := by
  constructor
  · intro hnot
    by_contra hcon
    push Not at hcon
    exact hnot (riemannHypothesis_iff_re_logDeriv_xi_nonneg.mpr fun s hs => hcon s hs)
  · rintro ⟨s, hs, hneg⟩
    exact not_riemannHypothesis_of_re_logDeriv_xi_neg hs hneg

end

end RHTower
