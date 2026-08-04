import GaloisForLFunctions.HTGeometry.JetRelationPropagation

/-!
# A differential relation among several entire functions holds everywhere

The single-function propagation says that a relation among the jets of an entire function, valid on a
nonempty open set, is valid on the whole plane.  A palette needs the same statement for a relation
among the jets of finitely many entire functions, and the proof is the same: the jet evaluation is
analytic, and a function analytic on the connected plane which vanishes on a nonempty open set
vanishes identically.

The relation is indexed by pairs (function, order), so no variable slot is reserved for the point --
a relation among the jets alone, which is what a palette's algebraic independence forbids.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The jet evaluation of a family relation is analytic where the functions are.** -/
theorem analyticAt_familyJetEval {n : ℕ} {A : Fin n → ℂ → ℂ}
    (hA : ∀ (k : Fin n) (w : ℂ), AnalyticAt ℂ (A k) w) (Q : MvPolynomial (Fin n × ℕ) ℂ) (z : ℂ) :
    AnalyticAt ℂ
      (fun w => MvPolynomial.eval (fun q : Fin n × ℕ => iteratedDeriv q.2 (A q.1) w) Q) z := by
  induction Q using MvPolynomial.induction_on with
  | C c => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) z)
  | add P R hP hR =>
      have heq : (fun w => MvPolynomial.eval
          (fun q : Fin n × ℕ => iteratedDeriv q.2 (A q.1) w) (P + R))
          = fun w => MvPolynomial.eval
              (fun q : Fin n × ℕ => iteratedDeriv q.2 (A q.1) w) P
            + MvPolynomial.eval
              (fun q : Fin n × ℕ => iteratedDeriv q.2 (A q.1) w) R := by
        funext w
        simp
      rw [heq]
      exact hP.add hR
  | mul_X P q hP =>
      have heq : (fun w => MvPolynomial.eval
          (fun r : Fin n × ℕ => iteratedDeriv r.2 (A r.1) w) (P * MvPolynomial.X q))
          = fun w => MvPolynomial.eval
              (fun r : Fin n × ℕ => iteratedDeriv r.2 (A r.1) w) P
            * iteratedDeriv q.2 (A q.1) w := by
        funext w
        simp
      rw [heq]
      exact hP.mul (analyticAt_iteratedDeriv_of_analyticAt (hA q.1 z) q.2)

/-- **A differential relation among entire functions propagates to the whole plane.** -/
theorem familyJetRelation_eq_zero_of_isOpen {n : ℕ} {A : Fin n → ℂ → ℂ}
    (hA : ∀ (k : Fin n) (w : ℂ), AnalyticAt ℂ (A k) w) {Q : MvPolynomial (Fin n × ℕ) ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hrel : ∀ z ∈ U, MvPolynomial.eval
      (fun q : Fin n × ℕ => iteratedDeriv q.2 (A q.1) z) Q = 0) :
    ∀ z : ℂ, MvPolynomial.eval (fun q : Fin n × ℕ => iteratedDeriv q.2 (A q.1) z) Q = 0 := by
  set E : ℂ → ℂ := fun z => MvPolynomial.eval
    (fun q : Fin n × ℕ => iteratedDeriv q.2 (A q.1) z) Q with hE
  obtain ⟨z₀, hz₀⟩ := hUne
  have han : AnalyticOnNhd ℂ E Set.univ := fun z _ => analyticAt_familyJetEval hA Q z
  letI : NeBot (𝓝[≠] z₀) := NormedField.nhdsNE_neBot z₀
  have hlocal : ∀ᶠ z in 𝓝 z₀, E z = 0 := by
    filter_upwards [hU.mem_nhds hz₀] with z hz
    exact hrel z hz
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  intro z
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z₀) hfreq (Set.mem_univ z)

end

end GaloisForLFunctions.HTGeometry
