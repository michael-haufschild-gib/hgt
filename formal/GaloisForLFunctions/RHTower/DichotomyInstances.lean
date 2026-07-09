/-
Instances of the periodicity dichotomy.

The degree-zero integral multiplicative functional-equation class satisfies the periodicity
dichotomy outright: each member is identically zero or a Dirichlet polynomial in finitely many
prime columns, so every strip zero of a member lies on a full vertical arithmetic progression —
the right disjunct of the dichotomy holds at every zero, without reference to the critical line.
The class therefore has no member whose divisor carries an aperiodic strip zero: within this cell
the dichotomy's on-line clause is never exercised, and all divisor data is clockwork.
-/
import GaloisForLFunctions.RHTower.IntegralFEPolynomial
import GaloisForLFunctions.RHTower.PeriodicityDichotomy
import GaloisForLFunctions.RHTower.GammaCellMobility
import GaloisForLFunctions.RHTower.ZetaRealStrip

namespace RHTower

/-- **Every member of the integral multiplicative functional-equation class satisfies the
periodicity dichotomy.**  A strip zero of a member is vertically periodic: for an identically
vanishing member any period works, and otherwise the member is a finite column product whose
zeros propagate along the responsible column's vertical progression. -/
theorem integralMultiplicativeFEClass_periodicityDichotomy {f : ℂ → ℂ}
    (hf : IntegralMultiplicativeFEClass f) : PeriodicityDichotomy f := by
  intro ρ _ _ h0
  rcases integralMultiplicativeFEClass_zero_periodic hf h0 with hz | ⟨T, hT, hper⟩
  · exact Or.inr ⟨1, one_pos, fun k => hz _⟩
  · exact Or.inr ⟨T, hT, hper⟩

end RHTower

namespace RHTower

/-- **The gamma-widened cell carries unit odd charge at the interior off-line strip point `ρdzo`
through the zeta-bearing member `zetaDzo`.**  The zeta factor is negative, hence nonvanishing, at
the real strip point `ρdzo = 1/3`, so the product's analytic order there is exactly the simple
order of the polynomial factor: `1`, odd, with rung-one charge `−1 ≠ 1`.  The witness is a member
whose divisor is not that of any finite column product — the charge sits on a factor with genuine
Euler-product analytic continuation, not on a Dirichlet polynomial alone. -/
theorem gammaFECell_carriesChargeAt_ρdzo : CarriesChargeAt GammaFECell ρdzo :=
  ⟨zetaDzo, zetaDzo_mem_gammaFECell, by
    show carrierCharge (fun s => riemannZeta s * dzo s) 1 ρdzo ≠ 1
    rw [zetaMulDzo_charge_neg_one]
    norm_num⟩

end RHTower

namespace RHTower

/-- **The off-line charge exhibited by the zeta-bearing witness is itself vertically periodic.**
The polynomial factor of `zetaDzo` is a single base-`8` column, so it vanishes along the whole
vertical progression of period `2π/log 8` through `ρdzo`, and the product vanishes with it: the
constructed off-line charge of the gamma-widened cell is clockwork, consistent with the
periodicity dichotomy. -/
theorem zetaDzo_witness_zero_periodic :
    ∃ T : ℝ, 0 < T ∧ ∀ k : ℤ, zetaDzo (ρdzo + (k * T) * Complex.I) = 0 := by
  obtain ⟨i, hi, hall⟩ := columnForm_zero_periodic columnForm_example
    (by intro i hi; simp only [Finset.mem_singleton] at hi; omega) dzo_ρdzo_eq_zero
  have hi8 : i = 8 := Finset.mem_singleton.mp hi
  subst hi8
  refine ⟨2 * Real.pi / Real.log (8 : ℕ), by positivity, fun k => ?_⟩
  have h := hall k
  have hcast : ((2 * Real.pi / Real.log ((8 : ℕ) : ℝ) : ℝ) : ℂ)
      = 2 * (Real.pi : ℂ) / ((Real.log ((8 : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  show riemannZeta _ * dzo _ = 0
  rw [hcast, show dzo (ρdzo + (k : ℂ) * (2 * (Real.pi : ℂ) /
      ((Real.log ((8 : ℕ) : ℝ) : ℝ) : ℂ)) * Complex.I) = 0 from h, mul_zero]

/-- **The periodicity dichotomy on the gamma-widened cell implies the Riemann Hypothesis**, given
that zeta admits no off-line vertical progression of strip zeros.  Zeta is a member of the cell,
so a cell-wide dichotomy applies to it; an off-line strip zero would then ride a full vertical
progression of zeros, excluded by hypothesis — every strip zero is forced onto the critical
line. -/
theorem gammaFECell_dichotomy_implies_rh
    (hCPD : ∀ f, GammaFECell f → PeriodicityDichotomy f)
    (hAP : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1/2 →
      ¬ ∃ T : ℝ, 0 < T ∧ ∀ k : ℤ, riemannZeta (ρ + (k * T) * Complex.I) = 0) :
    RiemannHypothesis :=
  (periodicityDichotomy_zeta_iff_riemannHypothesis hAP).mp
    (hCPD riemannZeta zeta_mem_gammaFECell)

end RHTower
