import GaloisForLFunctions.HTGeometry.GomesDilatonPolynomialPotential
import GaloisForLFunctions.HTGeometry.GomesDilatonDualShiftRigidity

/-!
# Complete polynomial Hamiltonian fibers and their missing origin data

The geometry/connection reconstruction question of arXiv:2607.24901v1 section 4
has a sharp scalar analogue: a polynomial Hamiltonian forgets constant log-amplitude,
and additionally identifies opposite affine slopes. An origin slope removes the latter
ambiguity; an origin value then recovers the entire generating profile.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A specified constant derivative determines an affine profile with one free intercept. -/
theorem gomesDilatonDerivative_constant_iff (H : ℝ[X]) (a : ℝ) :
    H.derivative = C a ↔ ∃ b : ℝ, H = C a * X + C b := by
  constructor
  · intro h
    apply (gomesDilatonDerivative_eq_iff H (C a * X)).mp
    simpa using h
  · rintro ⟨b, rfl⟩
    simp

/-- Complete fibers of the polynomial scalar potential, including the opposite affine exception. -/
theorem gomesDilatonPotential_profile_fibers (H K : ℝ[X]) :
    dilatonPotential H = dilatonPotential K ↔
      (∃ c : ℝ, H = K + C c) ∨
        ∃ a b c : ℝ, H = C a * X + C b ∧ K = C (-a) * X + C c := by
  rw [gomesDilatonPotential_derivative_fibers]
  constructor
  · rintro (hsame | ⟨hopp, hd⟩)
    · exact Or.inl ((gomesDilatonDerivative_eq_iff H K).mp hsame)
    · let a := H.derivative.coeff 0
      have ha : H.derivative = C a := eq_C_of_derivative_eq_zero hd
      obtain ⟨b, hb⟩ := (gomesDilatonDerivative_constant_iff H a).mp ha
      have hk : K.derivative = C (-a) := by
        have hh : -H.derivative = K.derivative := (neg_eq_iff_eq_neg).mpr hopp
        rw [← hh, ha, map_neg]
      obtain ⟨c, hc⟩ := (gomesDilatonDerivative_constant_iff K (-a)).mp hk
      exact Or.inr ⟨a, b, c, hb, hc⟩
  · rintro (hsame | ⟨a, b, c, rfl, rfl⟩)
    · exact Or.inl ((gomesDilatonDerivative_eq_iff H K).mpr hsame)
    · right
      simp

/-- All coincidences of the actual Schwartz Hamiltonians are classified at the profile level. -/
theorem gomesDilatonHamiltonian_profile_fibers (H K : ℝ[X]) :
    dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ↔
      (∃ c : ℝ, H = K + C c) ∨
        ∃ a b c : ℝ, H = C a * X + C b ∧ K = C (-a) * X + C c := by
  rw [gomesDilatonHamiltonian_potential_eq_iff, gomesDilatonPotential_profile_fibers]

/-- Exact equality with the dual Hamiltonian occurs precisely for affine profiles. -/
theorem gomesDilatonHamiltonian_dual_eq_iff (H : ℝ[X]) :
    dilatonHamiltonianCLM H = dilatonHamiltonianCLM (-H) ↔
      ∃ a b : ℝ, H = C a * X + C b := by
  have hz : dilatonHamiltonianCLM H = dilatonHamiltonianCLM (-H) ↔
      H.derivative.derivative = 0 := by
    rw [gomesDilatonHamiltonian_parts_iff]
    constructor
    · rintro ⟨hd, _⟩
      simp only [derivative_neg] at hd
      apply Polynomial.funext
      intro x
      have hx := congrArg (Polynomial.eval x) hd
      simp only [eval_neg, eval_zero] at hx ⊢
      linarith
    · intro h
      constructor
      · simp only [derivative_neg, h, neg_zero]
      · simp only [derivative_neg]
        ring
  rw [hz]
  simpa using (gomesDilaton_secondDerivative_constant_iff H 0)

/-- One origin slope restores first-order connection information from the Hamiltonian. -/
theorem gomesDilatonHamiltonian_origin_slope_iff (H K : ℝ[X]) :
    (dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ∧
      H.derivative.eval 0 = K.derivative.eval 0) ↔
        dilatonSuperchargeCLM H = dilatonSuperchargeCLM K := by
  constructor
  · rintro ⟨hh, hs⟩
    apply (gomesDilatonConnection_eq_iff H K).mpr
    have hd := ((gomesDilatonHamiltonian_parts_iff H K).mp hh).1
    obtain ⟨c, hc⟩ := (gomesDilatonDerivative_eq_iff H.derivative K.derivative).mp hd
    have hx := congrArg (Polynomial.eval 0) hc
    simp only [eval_add, eval_C] at hx
    have hz : c = 0 := by linarith
    rw [hz, map_zero, add_zero] at hc
    exact hc
  · intro h
    obtain ⟨c, hc⟩ := (gomesDilatonConnection_constant_iff H K).mp h
    constructor
    · rw [hc, gomesDilatonHamiltonian_constant]
    · rw [(gomesDilatonConnection_eq_iff H K).mp h]

/-- Hamiltonian plus the two origin jets recovers every real polynomial profile uniquely. -/
theorem gomesDilatonHamiltonian_origin_jets_iff (H K : ℝ[X]) :
    (dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ∧
      H.eval 0 = K.eval 0 ∧ H.derivative.eval 0 = K.derivative.eval 0) ↔ H = K := by
  constructor
  · rintro ⟨hh, hv, hs⟩
    exact (gomesDilatonConnection_origin_iff H K).mp
      ⟨(gomesDilatonHamiltonian_origin_slope_iff H K).mp ⟨hh, hs⟩, hv⟩
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩

/-- The constant-amplitude ambiguity is the entire fiber whenever curvature is nonzero. -/
theorem gomesDilatonHamiltonian_curved_fibers
    (H : {H : ℝ[X] // H.derivative.derivative ≠ 0}) (K : ℝ[X]) :
    dilatonHamiltonianCLM H.val = dilatonHamiltonianCLM K ↔
      ∃ c : ℝ, H.val = K + C c := by
  rw [gomesDilatonHamiltonian_derivative_fibers]
  constructor
  · rintro (hd | ⟨_, hz⟩)
    · exact (gomesDilatonDerivative_eq_iff H.val K).mp hd
    · exact False.elim (H.property hz)
  · intro h
    exact Or.inl ((gomesDilatonDerivative_eq_iff H.val K).mpr h)

end GaloisForLFunctions.HTGeometry
