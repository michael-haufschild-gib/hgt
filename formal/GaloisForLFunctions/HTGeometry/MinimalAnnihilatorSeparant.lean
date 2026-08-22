import GaloisForLFunctions.HTGeometry.BoundedJetNaturalBoundary
import GaloisForLFunctions.HTGeometry.DifferentialCharacteristicPseudoReduction

/-!
# A leader-minimal annihilator has a nonvanishing separant
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

noncomputable section

variable {n : ℕ}

/-- `P` is a leader-minimal annihilator of the augmented jet of `f` on the unit disk: it is a
nonzero differential polynomial of positive degree in the leader `f⁽ⁿ⁾`, it vanishes along the
jet, and no nonzero polynomial of strictly smaller leader degree does. -/
structure IsLeaderMinimalAnnihilator (f : ℂ → ℂ) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : Prop where
  ne_zero : P ≠ 0
  leader_pos : MvPolynomial.degreeOf (Fin.last (n + 1)) P ≠ 0
  annihilates : ∀ z ∈ ball (0 : ℂ) 1, MvPolynomial.eval (odeJet f n z) P = 0
  minimal : ∀ Q : MvPolynomial (Fin (n + 2)) ℂ, Q ≠ 0 →
    MvPolynomial.degreeOf (Fin.last (n + 1)) Q
      < MvPolynomial.degreeOf (Fin.last (n + 1)) P →
    ∃ z ∈ ball (0 : ℂ) 1, MvPolynomial.eval (odeJet f n z) Q ≠ 0

/-- **The separant of a leader-minimal annihilator does not vanish identically along the jet.**
This is the differential-algebra half of the bounded-jet bridge lemma: it replaces the
resultant/irreducibility argument by minimality in the leader degree, which is exactly what the
Ritt reduction supplies. -/
theorem separant_ne_zero_of_leaderMinimal {f : ℂ → ℂ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (h : IsLeaderMinimalAnnihilator f n P) :
    ∃ z₀ ∈ ball (0 : ℂ) 1,
      MvPolynomial.eval (odeJet f n z₀) (jetSeparant n P) ≠ 0 := by
  have hmem : (Fin.last (n + 1)) ∈ P.vars :=
    MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr h.leader_pos
  have hne : jetSeparant n P ≠ 0 := by
    rw [jetSeparant]
    exact mvPolynomial_pderiv_ne_zero_of_mem_vars_charZero hmem
  have hdeg : MvPolynomial.degreeOf (Fin.last (n + 1)) (jetSeparant n P)
      < MvPolynomial.degreeOf (Fin.last (n + 1)) P := by
    rw [jetSeparant]
    exact mvPolynomial_degreeOf_pderiv_lt h.leader_pos
  exact h.minimal _ hne hdeg

/-- **The bounded-jet natural-boundary bridge lemma.**  A holomorphic function on the unit disk
whose augmented order-`n` jet is bounded and which is annihilated by a leader-minimal algebraic
differential polynomial extends holomorphically across the unit circle; equivalently, the unit
circle is not a natural boundary of `f`. -/
theorem exists_analytic_continuation_of_leaderMinimal
    {f : ℂ → ℂ} {P : MvPolynomial (Fin (n + 2)) ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hjet : ∀ z ∈ ball (0 : ℂ) 1, ‖odeJet f n z‖ ≤ M)
    (h : IsLeaderMinimalAnnihilator f n P) :
    ∃ (z₁ : ℂ) (δ : ℝ), z₁ ∈ ball (0 : ℂ) 1 ∧ 0 < δ ∧ 1 - ‖z₁‖ < δ ∧
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₁ δ) ∧
        ∀ z ∈ ball z₁ δ ∩ ball (0 : ℂ) 1, g z = f z :=
  exists_analytic_continuation_of_annihilator hf hjet h.annihilates
    (separant_ne_zero_of_leaderMinimal h)

/-- **A leader-minimal annihilator exists** as soon as some annihilator of positive leader degree
does and no nonzero polynomial free of the leader annihilates the jet (order minimality). -/
theorem exists_leaderMinimalAnnihilator {f : ℂ → ℂ}
    {P₀ : MvPolynomial (Fin (n + 2)) ℂ} (hP₀ : P₀ ≠ 0)
    (hdeg : MvPolynomial.degreeOf (Fin.last (n + 1)) P₀ ≠ 0)
    (hann : ∀ z ∈ ball (0 : ℂ) 1, MvPolynomial.eval (odeJet f n z) P₀ = 0)
    (horder : ∀ Q : MvPolynomial (Fin (n + 2)) ℂ, Q ≠ 0 →
      MvPolynomial.degreeOf (Fin.last (n + 1)) Q = 0 →
      ∃ z ∈ ball (0 : ℂ) 1, MvPolynomial.eval (odeJet f n z) Q ≠ 0) :
    ∃ P, IsLeaderMinimalAnnihilator f n P := by
  classical
  have hex : ∃ d : ℕ, ∃ Q : MvPolynomial (Fin (n + 2)) ℂ, Q ≠ 0 ∧
      MvPolynomial.degreeOf (Fin.last (n + 1)) Q = d ∧ d ≠ 0 ∧
      (∀ z ∈ ball (0 : ℂ) 1, MvPolynomial.eval (odeJet f n z) Q = 0) :=
    ⟨_, P₀, hP₀, rfl, hdeg, hann⟩
  obtain ⟨Q, hQ0, hQd, hQdne, hQann⟩ := Nat.find_spec hex
  refine ⟨Q, ⟨hQ0, by rw [hQd]; exact hQdne, hQann, ?_⟩⟩
  intro R hR0 hRlt
  by_contra hcon
  push Not at hcon
  by_cases hR : MvPolynomial.degreeOf (Fin.last (n + 1)) R = 0
  · obtain ⟨z, hz, hne⟩ := horder R hR0 hR
    exact hne (hcon z hz)
  · have hle : Nat.find hex ≤ MvPolynomial.degreeOf (Fin.last (n + 1)) R :=
      Nat.find_le ⟨R, hR0, rfl, hR, hcon⟩
    rw [hQd] at hRlt
    omega

/-- **The bounded-jet natural-boundary bridge lemma, order-minimal form.**  If `f` is holomorphic
on the unit disk with bounded augmented order-`n` jet, is annihilated by some algebraic
differential polynomial of positive degree in `f⁽ⁿ⁾`, and no nonzero polynomial free of `f⁽ⁿ⁾`
annihilates the jet, then the unit circle is not a natural boundary of `f`. -/
theorem exists_analytic_continuation_of_minimal_order
    {f : ℂ → ℂ} {P₀ : MvPolynomial (Fin (n + 2)) ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hjet : ∀ z ∈ ball (0 : ℂ) 1, ‖odeJet f n z‖ ≤ M)
    (hP₀ : P₀ ≠ 0)
    (hdeg : MvPolynomial.degreeOf (Fin.last (n + 1)) P₀ ≠ 0)
    (hann : ∀ z ∈ ball (0 : ℂ) 1, MvPolynomial.eval (odeJet f n z) P₀ = 0)
    (horder : ∀ Q : MvPolynomial (Fin (n + 2)) ℂ, Q ≠ 0 →
      MvPolynomial.degreeOf (Fin.last (n + 1)) Q = 0 →
      ∃ z ∈ ball (0 : ℂ) 1, MvPolynomial.eval (odeJet f n z) Q ≠ 0) :
    ∃ (z₁ : ℂ) (δ : ℝ), z₁ ∈ ball (0 : ℂ) 1 ∧ 0 < δ ∧ 1 - ‖z₁‖ < δ ∧
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₁ δ) ∧
        ∀ z ∈ ball z₁ δ ∩ ball (0 : ℂ) 1, g z = f z := by
  obtain ⟨P, hP⟩ := exists_leaderMinimalAnnihilator hP₀ hdeg hann horder
  exact exists_analytic_continuation_of_leaderMinimal hf hjet hP

end

end GaloisForLFunctions.HTGeometry
