import GaloisForLFunctions.HTGeometry.GammaShiftMultiDatum
import GaloisForLFunctions.HTGeometry.GammaShiftDatumSum
import GaloisForLFunctions.HTGeometry.GammaShiftZeta

/-!
# The shifted law with several translates

The signature `(16)` is now computed for a monomial in several translates, so a sum of such
monomials with pairwise distinct signatures has a datum, and the law applies to coefficients of that
shape.

This is the card's setting: finitely many real translates, a relation whose coefficients are built
from all of them, and the conclusion that a recurrent solution has finite phase rank — with the zeta
exclusion as the contrapositive.
-/

open Filter Set Topology Function
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The line function of a sum of multi-translate monomials. -/
def multiMonomialSum {r M : ℕ} (σ : ℝ) (lamf : Fin r → ℝ) (cc : Fin M → ℂ)
    (ee : Fin M → Fin r → ℕ) (q p : Fin M → Polynomial ℂ) (bb : Fin M → ℤ) (t : ℝ) : ℂ :=
  ∑ i : Fin M, cc i * (∏ k : Fin r, gammaLine (σ + lamf k) t ^ ee i k)
    * ((q i).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      / (p i).eval ((σ : ℂ) + (t : ℂ) * Complex.I))
    * vertLog t ^ bb i

/-- The `Γ`-degree of a multi-translate monomial. -/
def multiDegree {r : ℕ} (ee : Fin r → ℕ) : ℤ := ∑ k : Fin r, (ee k : ℤ)

/-- The real argument exponent of a multi-translate monomial. -/
def multiExponent {r : ℕ} (lamf : Fin r → ℝ) (ee : Fin r → ℕ) (q p : Polynomial ℂ) : ℝ :=
  (∑ k : Fin r, (ee k : ℝ) * lamf k)
    + ((((q.natDegree : ℕ) : ℝ)) - (((p.natDegree : ℕ) : ℝ)))

/-- **A sum of multi-translate monomials with distinct signatures has a datum.** -/
theorem exists_hasShiftDatum_multiMonomialSum {σ : ℝ} (hσ : 0 < σ) {r M : ℕ} (hM : 0 < M)
    (lamf : Fin r → ℝ) (hlam : ∀ k, 0 < σ + lamf k) (cc : Fin M → ℂ) (hcc : ∀ i, cc i ≠ 0)
    (ee : Fin M → Fin r → ℕ) (q p : Fin M → Polynomial ℂ) (hq : ∀ i, q i ≠ 0)
    (hp : ∀ i, p i ≠ 0) (bb : Fin M → ℤ)
    (hdist : ∀ i j : Fin M, i ≠ j → ¬(multiDegree (ee i) = multiDegree (ee j)
      ∧ multiExponent lamf (ee i) (q i) (p i) = multiExponent lamf (ee j) (q j) (p j)
      ∧ bb i = bb j)) :
    ∃ β : Fin M, HasShiftDatum 0 σ (multiMonomialSum σ lamf cc ee q p bb)
      (multiDegree (ee β)) (multiExponent lamf (ee β) (q β) (p β)) (bb β)
      (cc β * ((q β).leadingCoeff / (p β).leadingCoeff)) := by
  classical
  have hσ' : 0 < σ + (0 : ℝ) := by simpa using hσ
  exact hasShiftDatum_sum_of_distinct hσ' hM
    (fun i t => cc i * (∏ k : Fin r, gammaLine (σ + lamf k) t ^ ee i k)
      * ((q i).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / (p i).eval ((σ : ℂ) + (t : ℂ) * Complex.I))
      * vertLog t ^ bb i)
    (fun i => multiDegree (ee i)) (fun i => multiExponent lamf (ee i) (q i) (p i)) bb
    (fun i => cc i * ((q i).leadingCoeff / (p i).leadingCoeff))
    (fun i => hasShiftDatum_multiMonomial hσ lamf hlam (ee i) (hcc i) (hq i) (hp i) (bb i))
    hdist

/-- **The finite phase law with several translates.**  A strip almost periodic holomorphic solution
of a relation whose coefficients are sums of multi-translate Gamma monomials with pairwise distinct
signatures has finite rational Bohr frequency rank. -/
theorem rank_finite_of_gammaShiftMulti {n N M r : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hN : 0 < N) (hM : 0 < M) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e) (F : Fin N → ℂ → ℂ)
    (lamf : Fin r → ℝ) (hlam : ∀ k, 0 < σ + lamf k)
    (cc : Fin N → Fin M → ℂ) (hcc : ∀ α i, cc α i ≠ 0) (ee : Fin N → Fin M → Fin r → ℕ)
    (q p : Fin N → Fin M → Polynomial ℂ) (hq : ∀ α i, q α i ≠ 0) (hp : ∀ α i, p α i ≠ 0)
    (bb : Fin N → Fin M → ℤ)
    (hdist : ∀ (α : Fin N) (i j : Fin M), i ≠ j →
      ¬(multiDegree (ee α i) = multiDegree (ee α j)
        ∧ multiExponent lamf (ee α i) (q α i) (p α i)
          = multiExponent lamf (ee α j) (q α j) (p α j)
        ∧ bb α i = bb α j))
    (hF : ∀ (α : Fin N) (t : ℝ), F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      = multiMonomialSum σ lamf (cc α) (ee α) (q α) (p α) (bb α) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x)) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  have hσ' : 0 < σ + (0 : ℝ) := by simpa using hσ
  choose β hβ using fun α : Fin N => exists_hasShiftDatum_multiMonomialSum hσ hM lamf hlam
    (cc α) (hcc α) (ee α) (q α) (p α) (hq α) (hp α) (bb α) (hdist α)
  have hdat : ∀ α : Fin N, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape 0 σ (multiDegree (ee α (β α)))
        (multiExponent lamf (ee α (β α)) (q α (β α)) (p α (β α))) (bb α (β α)) t)
      atTop (nhds (cc α (β α) * ((q α (β α)).leadingCoeff / (p α (β α)).leadingCoeff))) := by
    intro α
    refine (hβ α).2.congr fun t => ?_
    rw [hF α t]
  exact rank_finite_of_gammaShift_data hσ' hN hr hρ hrρ hR hΦ hap e he F
    (fun α => multiDegree (ee α (β α)))
    (fun α => multiExponent lamf (ee α (β α)) (q α (β α)) (p α (β α)))
    (fun α => bb α (β α))
    (fun α => cc α (β α) * ((q α (β α)).leadingCoeff / (p α (β α)).leadingCoeff))
    (fun α => (hβ α).1) hdat hrel hf hfu hftb

/-- **Zeta satisfies no relation with multi-translate coefficients.**  Equation (21) in the card's
stated generality: the coefficients may involve any finite family of nonnegative real translates, as
long as the monomial signatures inside each coefficient are pairwise distinct. -/
theorem zeta_no_gammaShiftMulti_relation {n N M r : ℕ} {σ R rr ρ : ℝ} (hσ : 1 < σ)
    (hN : 0 < N) (hM : 0 < M) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    (hRσ : R ≤ σ - 1)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e) (F : Fin N → ℂ → ℂ)
    (lamf : Fin r → ℝ) (hlam : ∀ k, 0 < σ + lamf k)
    (cc : Fin N → Fin M → ℂ) (hcc : ∀ α i, cc α i ≠ 0) (ee : Fin N → Fin M → Fin r → ℕ)
    (q p : Fin N → Fin M → Polynomial ℂ) (hq : ∀ α i, q α i ≠ 0) (hp : ∀ α i, p α i ≠ 0)
    (bb : Fin N → Fin M → ℤ)
    (hdist : ∀ (α : Fin N) (i j : Fin M), i ≠ j →
      ¬(multiDegree (ee α i) = multiDegree (ee α j)
        ∧ multiExponent lamf (ee α i) (q α i) (p α i)
          = multiExponent lamf (ee α j) (q α j) (p α j)
        ∧ bb α i = bb α j))
    (hF : ∀ (α : Fin N) (t : ℝ), F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      = multiMonomialSum σ lamf (cc α) (ee α) (q α) (p α) (bb α) t)
    (hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) riemannZeta s) ^ (e α i) = 0) :
    False := by
  classical
  have hσpos : (0 : ℝ) < σ := by linarith
  have hσ' : 0 < σ + (0 : ℝ) := by simpa using hσpos
  choose β hβ using fun α : Fin N => exists_hasShiftDatum_multiMonomialSum hσpos hM lamf hlam
    (cc α) (hcc α) (ee α) (q α) (p α) (hq α) (hp α) (bb α) (hdist α)
  have hdat : ∀ α : Fin N, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape 0 σ (multiDegree (ee α (β α)))
        (multiExponent lamf (ee α (β α)) (q α (β α)) (p α (β α))) (bb α (β α)) t)
      atTop (nhds (cc α (β α) * ((q α (β α)).leadingCoeff / (p α (β α)).leadingCoeff))) := by
    intro α
    refine (hβ α).2.congr fun t => ?_
    rw [hF α t]
  exact zeta_no_gammaShift_relation hσ hσ' hN hr hρ hrρ hR hRσ e he F
    (fun α => multiDegree (ee α (β α)))
    (fun α => multiExponent lamf (ee α (β α)) (q α (β α)) (p α (β α)))
    (fun α => bb α (β α))
    (fun α => cc α (β α) * ((q α (β α)).leadingCoeff / (p α (β α)).leadingCoeff))
    (fun α => (hβ α).1) hdat hrel

end

end GaloisForLFunctions.HTGeometry
