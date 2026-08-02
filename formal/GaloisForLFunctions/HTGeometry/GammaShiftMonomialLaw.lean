import GaloisForLFunctions.HTGeometry.GammaShiftDatumSum
import GaloisForLFunctions.HTGeometry.GammaShiftZeta

/-!
# The shifted law with explicit monomial coefficients

Feeding the monomial data into the finite phase law removes the abstract datum hypothesis: a
relation whose coefficients are finite sums of shifted Gamma monomials with pairwise distinct
signatures is covered outright.

For zeta this gives an unconditional exclusion — no analytic hypothesis is left beyond the strip
data, since the coefficients' data are computed from their degrees and leading coefficients.
-/

open Filter Set Topology Function
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The finite phase law for monomial-sum coefficients.**  A strip almost periodic holomorphic
solution of a relation whose coefficients are finite sums of shifted Gamma monomials with pairwise
distinct signatures has finite rational Bohr frequency rank. -/
theorem rank_finite_of_gammaShiftMonomial {n N M : ℕ} {σ lam R rr ρ : ℝ} (hσ : 0 < σ + lam)
    (hN : 0 < N) (hM : 0 < M) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e) (F : Fin N → ℂ → ℂ)
    (cc : Fin N → Fin M → ℂ) (hcc : ∀ α i, cc α i ≠ 0) (nn : Fin N → Fin M → ℤ)
    (q p : Fin N → Fin M → Polynomial ℂ) (hq : ∀ α i, q α i ≠ 0) (hp : ∀ α i, p α i ≠ 0)
    (bb : Fin N → Fin M → ℤ)
    (hdist : ∀ (α : Fin N) (i j : Fin M), i ≠ j → ¬(nn α i = nn α j
      ∧ ((((q α i).natDegree : ℕ) : ℝ) - (((p α i).natDegree : ℕ) : ℝ)
        = (((q α j).natDegree : ℕ) : ℝ) - (((p α j).natDegree : ℕ) : ℝ))
      ∧ bb α i = bb α j))
    (hF : ∀ (α : Fin N) (t : ℝ), F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      = ∑ i : Fin M, cc α i * gammaLine (σ + lam) t ^ nn α i
        * ((q α i).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / (p α i).eval ((σ : ℂ) + (t : ℂ) * Complex.I))
        * vertLog t ^ bb α i)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x)) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  choose β hβ using fun α : Fin N => exists_hasShiftDatum_monomialSum (lam := lam) (σ := σ)
    hσ hM (cc α) (hcc α) (nn α) (q α) (p α) (hq α) (hp α) (bb α) (hdist α)
  have hdat : ∀ α : Fin N, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape lam σ (nn α (β α))
        ((((q α (β α)).natDegree : ℕ) : ℝ) - (((p α (β α)).natDegree : ℕ) : ℝ))
        (bb α (β α)) t)
      atTop (nhds (cc α (β α) * ((q α (β α)).leadingCoeff / (p α (β α)).leadingCoeff))) := by
    intro α
    refine (hβ α).2.congr fun t => ?_
    rw [hF α t]
  exact rank_finite_of_gammaShift_data hσ hN hr hρ hrρ hR hΦ hap e he F
    (fun α => nn α (β α))
    (fun α => (((q α (β α)).natDegree : ℕ) : ℝ) - (((p α (β α)).natDegree : ℕ) : ℝ))
    (fun α => bb α (β α))
    (fun α => cc α (β α) * ((q α (β α)).leadingCoeff / (p α (β α)).leadingCoeff))
    (fun α => (hβ α).1) hdat hrel hf hfu hftb

/-- **Zeta satisfies no relation with monomial-sum coefficients.**  Equation (21) of the shifted law
with the coefficients written out: finite sums of shifted Gamma monomials with pairwise distinct
signatures, whose data are read off their degrees and leading coefficients. -/
theorem zeta_no_gammaShiftMonomial_relation {n N M : ℕ} {σ lam R rr ρ : ℝ} (hσ : 1 < σ)
    (hlam : 0 < σ + lam) (hN : 0 < N) (hM : 0 < M) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R)
    (hR : 0 < R) (hRσ : R ≤ σ - 1)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e) (F : Fin N → ℂ → ℂ)
    (cc : Fin N → Fin M → ℂ) (hcc : ∀ α i, cc α i ≠ 0) (nn : Fin N → Fin M → ℤ)
    (q p : Fin N → Fin M → Polynomial ℂ) (hq : ∀ α i, q α i ≠ 0) (hp : ∀ α i, p α i ≠ 0)
    (bb : Fin N → Fin M → ℤ)
    (hdist : ∀ (α : Fin N) (i j : Fin M), i ≠ j → ¬(nn α i = nn α j
      ∧ ((((q α i).natDegree : ℕ) : ℝ) - (((p α i).natDegree : ℕ) : ℝ)
        = (((q α j).natDegree : ℕ) : ℝ) - (((p α j).natDegree : ℕ) : ℝ))
      ∧ bb α i = bb α j))
    (hF : ∀ (α : Fin N) (t : ℝ), F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      = ∑ i : Fin M, cc α i * gammaLine (σ + lam) t ^ nn α i
        * ((q α i).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / (p α i).eval ((σ : ℂ) + (t : ℂ) * Complex.I))
        * vertLog t ^ bb α i)
    (hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) riemannZeta s) ^ (e α i) = 0) :
    False := by
  classical
  choose β hβ using fun α : Fin N => exists_hasShiftDatum_monomialSum (lam := lam) (σ := σ)
    hlam hM (cc α) (hcc α) (nn α) (q α) (p α) (hq α) (hp α) (bb α) (hdist α)
  have hdat : ∀ α : Fin N, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape lam σ (nn α (β α))
        ((((q α (β α)).natDegree : ℕ) : ℝ) - (((p α (β α)).natDegree : ℕ) : ℝ))
        (bb α (β α)) t)
      atTop (nhds (cc α (β α) * ((q α (β α)).leadingCoeff / (p α (β α)).leadingCoeff))) := by
    intro α
    refine (hβ α).2.congr fun t => ?_
    rw [hF α t]
  exact zeta_no_gammaShift_relation hσ hlam hN hr hρ hrρ hR hRσ e he F
    (fun α => nn α (β α))
    (fun α => (((q α (β α)).natDegree : ℕ) : ℝ) - (((p α (β α)).natDegree : ℕ) : ℝ))
    (fun α => bb α (β α))
    (fun α => cc α (β α) * ((q α (β α)).leadingCoeff / (p α (β α)).leadingCoeff))
    (fun α => (hβ α).1) hdat hrel

end

end GaloisForLFunctions.HTGeometry
