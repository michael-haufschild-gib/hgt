import GaloisForLFunctions.HTGeometry.FinitePhaseLawFromRatios
import GaloisForLFunctions.HTGeometry.FullJetPolyDatum
import GaloisForLFunctions.HTGeometry.JetPolyCoeffDatum
import GaloisForLFunctions.HTGeometry.GammaJetDatumUniqueness

/-!
# The finite phase law on coefficients given by their datum

The law consumes coefficients as residues against a Gamma-jet shape.  The residue machinery produces
them in the datum form `s^{b}·F(s)/(log t + iπ/2)^{a} → c`, and that *is* a residue against the shape
`L^a/s^b`, i.e. against `gammaJetShape σ 0 a 0 b`.

So a relation whose coefficients are given by their data — which is what the unquantified residue
theorems produce for jet polynomials — feeds the law directly.
-/

open Filter Topology Complex

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **The law on coefficients given by their datum.** -/
theorem finite_phase_law_of_coefficient_datum {n N : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ) (hN : 0 < N)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (a b : Fin N → ℕ) (c : Fin N → ℂ) (hc : ∀ α, c α ≠ 0)
    (hdat : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      ((σ : ℂ) + (t : ℂ) * Complex.I) ^ b α * F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        / vertLog t ^ a α) atTop (nhds (c α)))
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ (β : Fin N) (d : Fin N → ℂ), d β = 1
      ∧ (∀ z ∈ verticalStrip σ R,
        jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0)
      ∧ (∑ α : Fin N, MvPolynomial.C (d α)
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℂ) ^ (e α i)) ≠ 0
      ∧ ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  refine finite_phase_law_of_gammaJet_data hσ hN hr hρ hrρ hR hΦ hap e F
    (fun _ => 0) a (fun _ => 0) b c hc ?_ hrel he hf hfu hftb
  intro α
  have hshape := tendsto_div_polyJetShape_of_datum hσ (hdat α)
  refine hshape.congr fun t => ?_
  rw [gammaJetShape_gamma_zero]

/-- The datum hypothesis is satisfied by a constant coefficient, with trivial datum `(0, 0)`: the
hypothesis class of the law's datum form is inhabited at every level of the family. -/
theorem datum_of_const (σ : ℝ) (c : ℂ) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (0 : ℕ) * c / vertLog t ^ (0 : ℕ))
      atTop (nhds c) := by
  refine tendsto_const_nhds.congr fun t => ?_
  simp

/-- A coefficient with a datum in the `s`-power scale alone also satisfies the hypothesis, with log
degree zero. -/
theorem datum_of_pow_datum {σ : ℝ} {F : ℂ → ℂ} {b : ℕ} {c : ℂ}
    (h : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ b
      * F ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds c)) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ b
        * F ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t ^ (0 : ℕ)) atTop (nhds c) := by
  refine h.congr fun t => ?_
  simp

/-- The line-level form of the same reduction: any datum in the `s`-power scale is a datum with log
degree zero. -/
theorem datum_of_pow_datum_line {σ : ℝ} {g : ℝ → ℂ} {b : ℕ} {c : ℂ}
    (h : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ b * g t) atTop (nhds c)) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ b * g t / vertLog t ^ (0 : ℕ))
      atTop (nhds c) := by
  refine h.congr fun t => ?_
  simp

/-- **A non-flat jet polynomial supplies the law's datum hypothesis.**  Composing the unquantified
residue theorem with the reduction above: the coefficient needs no presentation, only non-flatness. -/
theorem exists_datum_hypothesis_of_jetPolyCoeff {σ : ℝ} (hσ : 0 < σ) (N M W d : ℕ)
    (e : Fin M → Fin N → ℕ) (a : Fin M → Polynomial ℂ)
    (hdeg : ∀ α : Fin M, (a α).natDegree ≤ d)
    (hW : ∀ α : Fin M, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i) {n : ℕ}
    (hnotflat : ¬ IsLineBigO σ n (fun t : ℝ => ∑ α : Fin M,
      ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)) :
    ∃ (b : ℕ) (c : ℂ), c ≠ 0 ∧ Tendsto (fun t : ℝ =>
      ((σ : ℂ) + (t : ℂ) * Complex.I) ^ b * (∑ α : Fin M,
        ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i) / vertLog t ^ (0 : ℕ)) atTop (nhds c) := by
  obtain ⟨p, c, hc, hlim⟩ := exists_jetPolyCoeff_datum hσ N M W d e a hdeg hW hnotflat
  exact ⟨p, c, hc, datum_of_pow_datum_line hlim⟩

end GaloisForLFunctions
