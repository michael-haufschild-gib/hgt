import GaloisForLFunctions.HTGeometry.GammaShiftDatumClass
import GaloisForLFunctions.HTGeometry.GammaShiftMultiLaw

/-!
# The shifted law for coefficients in normal form

Collecting monomials with equal exponents is what eq. (15) means by normal form, so the signatures
inside a coefficient may repeat.  The hypothesis that survives is the one the card states: the
residues of the dominant signature class do not cancel.

Under that hypothesis the whole chain applies — the datum, the finite phase law, and the zeta
exclusion — for coefficients built from any finite family of real translates.
-/

open Filter Set Topology Function
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The signature class of a monomial inside a coefficient. -/
def multiClass {r M : ℕ} (lamf : Fin r → ℝ) (ee : Fin M → Fin r → ℕ)
    (q p : Fin M → Polynomial ℂ) (bb : Fin M → ℤ) (β : Fin M) : Finset (Fin M) :=
  Finset.univ.filter (fun i : Fin M => multiDegree (ee i) = multiDegree (ee β)
    ∧ multiExponent lamf (ee i) (q i) (p i) = multiExponent lamf (ee β) (q β) (p β)
    ∧ bb i = bb β)

/-- **A normal-form sum of multi-translate monomials has a datum.**  Signatures may repeat; only the
dominant class has to survive. -/
theorem exists_hasShiftDatum_multiMonomialSum_class {σ : ℝ} (hσ : 0 < σ) {r M : ℕ} (hM : 0 < M)
    (lamf : Fin r → ℝ) (hlam : ∀ k, 0 < σ + lamf k) (cc : Fin M → ℂ) (hcc : ∀ i, cc i ≠ 0)
    (ee : Fin M → Fin r → ℕ) (q p : Fin M → Polynomial ℂ) (hq : ∀ i, q i ≠ 0)
    (hp : ∀ i, p i ≠ 0) (bb : Fin M → ℤ)
    (hclass : ∀ β : Fin M, (∀ i : Fin M,
        (multiDegree (ee i) = multiDegree (ee β)
          ∧ multiExponent lamf (ee i) (q i) (p i) = multiExponent lamf (ee β) (q β) (p β)
          ∧ bb i = bb β)
        ∨ ShiftShapeDominates (multiDegree (ee β)) (multiExponent lamf (ee β) (q β) (p β)) (bb β)
            (multiDegree (ee i)) (multiExponent lamf (ee i) (q i) (p i)) (bb i)) →
      (∑ i ∈ multiClass lamf ee q p bb β,
        cc i * ((q i).leadingCoeff / (p i).leadingCoeff)) ≠ 0) :
    ∃ β : Fin M, HasShiftDatum 0 σ (multiMonomialSum σ lamf cc ee q p bb)
      (multiDegree (ee β)) (multiExponent lamf (ee β) (q β) (p β)) (bb β)
      (∑ i ∈ multiClass lamf ee q p bb β,
        cc i * ((q i).leadingCoeff / (p i).leadingCoeff)) := by
  classical
  have hσ' : 0 < σ + (0 : ℝ) := by simpa using hσ
  exact exists_hasShiftDatum_sum_class hσ' hM
    (fun i t => cc i * (∏ k : Fin r, gammaLine (σ + lamf k) t ^ ee i k)
      * ((q i).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / (p i).eval ((σ : ℂ) + (t : ℂ) * Complex.I))
      * vertLog t ^ bb i)
    (fun i => multiDegree (ee i)) (fun i => multiExponent lamf (ee i) (q i) (p i)) bb
    (fun i => cc i * ((q i).leadingCoeff / (p i).leadingCoeff))
    (fun i => hasShiftDatum_multiMonomial hσ lamf hlam (ee i) (hcc i) (hq i) (hp i) (bb i))
    hclass

/-- **The finite phase law for normal-form coefficients.** -/
theorem rank_finite_of_gammaShiftClass {n N M r : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hN : 0 < N) (hM : 0 < M) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e) (F : Fin N → ℂ → ℂ)
    (lamf : Fin r → ℝ) (hlam : ∀ k, 0 < σ + lamf k)
    (cc : Fin N → Fin M → ℂ) (hcc : ∀ α i, cc α i ≠ 0) (ee : Fin N → Fin M → Fin r → ℕ)
    (q p : Fin N → Fin M → Polynomial ℂ) (hq : ∀ α i, q α i ≠ 0) (hp : ∀ α i, p α i ≠ 0)
    (bb : Fin N → Fin M → ℤ)
    (hclass : ∀ (α : Fin N) (β : Fin M), (∀ i : Fin M,
        (multiDegree (ee α i) = multiDegree (ee α β)
          ∧ multiExponent lamf (ee α i) (q α i) (p α i)
            = multiExponent lamf (ee α β) (q α β) (p α β)
          ∧ bb α i = bb α β)
        ∨ ShiftShapeDominates (multiDegree (ee α β))
            (multiExponent lamf (ee α β) (q α β) (p α β)) (bb α β)
            (multiDegree (ee α i)) (multiExponent lamf (ee α i) (q α i) (p α i)) (bb α i)) →
      (∑ i ∈ multiClass lamf (ee α) (q α) (p α) (bb α) β,
        cc α i * ((q α i).leadingCoeff / (p α i).leadingCoeff)) ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ), F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      = multiMonomialSum σ lamf (cc α) (ee α) (q α) (p α) (bb α) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x)) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  have hσ' : 0 < σ + (0 : ℝ) := by simpa using hσ
  choose β hβ using fun α : Fin N => exists_hasShiftDatum_multiMonomialSum_class hσ hM lamf hlam
    (cc α) (hcc α) (ee α) (q α) (p α) (hq α) (hp α) (bb α) (hclass α)
  have hdat : ∀ α : Fin N, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape 0 σ (multiDegree (ee α (β α)))
        (multiExponent lamf (ee α (β α)) (q α (β α)) (p α (β α))) (bb α (β α)) t)
      atTop (nhds (∑ i ∈ multiClass lamf (ee α) (q α) (p α) (bb α) (β α),
        cc α i * ((q α i).leadingCoeff / (p α i).leadingCoeff))) := by
    intro α
    refine (hβ α).2.congr fun t => ?_
    rw [hF α t]
  exact rank_finite_of_gammaShift_data hσ' hN hr hρ hrρ hR hΦ hap e he F
    (fun α => multiDegree (ee α (β α)))
    (fun α => multiExponent lamf (ee α (β α)) (q α (β α)) (p α (β α)))
    (fun α => bb α (β α))
    (fun α => ∑ i ∈ multiClass lamf (ee α) (q α) (p α) (bb α) (β α),
      cc α i * ((q α i).leadingCoeff / (p α i).leadingCoeff))
    (fun α => (hβ α).1) hdat hrel hf hfu hftb

/-- **Zeta satisfies no relation with normal-form coefficients.**  Equation (21) with the card's own
hypothesis: the monomials of each coefficient are collected, and the residues of the dominant
signature class do not cancel. -/
theorem zeta_no_gammaShiftClass_relation {n N M r : ℕ} {σ R rr ρ : ℝ} (hσ : 1 < σ)
    (hN : 0 < N) (hM : 0 < M) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    (hRσ : R ≤ σ - 1)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e) (F : Fin N → ℂ → ℂ)
    (lamf : Fin r → ℝ) (hlam : ∀ k, 0 < σ + lamf k)
    (cc : Fin N → Fin M → ℂ) (hcc : ∀ α i, cc α i ≠ 0) (ee : Fin N → Fin M → Fin r → ℕ)
    (q p : Fin N → Fin M → Polynomial ℂ) (hq : ∀ α i, q α i ≠ 0) (hp : ∀ α i, p α i ≠ 0)
    (bb : Fin N → Fin M → ℤ)
    (hclass : ∀ (α : Fin N) (β : Fin M), (∀ i : Fin M,
        (multiDegree (ee α i) = multiDegree (ee α β)
          ∧ multiExponent lamf (ee α i) (q α i) (p α i)
            = multiExponent lamf (ee α β) (q α β) (p α β)
          ∧ bb α i = bb α β)
        ∨ ShiftShapeDominates (multiDegree (ee α β))
            (multiExponent lamf (ee α β) (q α β) (p α β)) (bb α β)
            (multiDegree (ee α i)) (multiExponent lamf (ee α i) (q α i) (p α i)) (bb α i)) →
      (∑ i ∈ multiClass lamf (ee α) (q α) (p α) (bb α) β,
        cc α i * ((q α i).leadingCoeff / (p α i).leadingCoeff)) ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ), F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      = multiMonomialSum σ lamf (cc α) (ee α) (q α) (p α) (bb α) t)
    (hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) riemannZeta s) ^ (e α i) = 0) :
    False := by
  classical
  have hσpos : (0 : ℝ) < σ := by linarith
  have hσ' : 0 < σ + (0 : ℝ) := by simpa using hσpos
  choose β hβ using fun α : Fin N =>
    exists_hasShiftDatum_multiMonomialSum_class hσpos hM lamf hlam
      (cc α) (hcc α) (ee α) (q α) (p α) (hq α) (hp α) (bb α) (hclass α)
  have hdat : ∀ α : Fin N, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape 0 σ (multiDegree (ee α (β α)))
        (multiExponent lamf (ee α (β α)) (q α (β α)) (p α (β α))) (bb α (β α)) t)
      atTop (nhds (∑ i ∈ multiClass lamf (ee α) (q α) (p α) (bb α) (β α),
        cc α i * ((q α i).leadingCoeff / (p α i).leadingCoeff))) := by
    intro α
    refine (hβ α).2.congr fun t => ?_
    rw [hF α t]
  exact zeta_no_gammaShift_relation hσ hσ' hN hr hρ hrρ hR hRσ e he F
    (fun α => multiDegree (ee α (β α)))
    (fun α => multiExponent lamf (ee α (β α)) (q α (β α)) (p α (β α)))
    (fun α => bb α (β α))
    (fun α => ∑ i ∈ multiClass lamf (ee α) (q α) (p α) (bb α) (β α),
      cc α i * ((q α i).leadingCoeff / (p α i).leadingCoeff))
    (fun α => (hβ α).1) hdat hrel

end

end GaloisForLFunctions.HTGeometry
