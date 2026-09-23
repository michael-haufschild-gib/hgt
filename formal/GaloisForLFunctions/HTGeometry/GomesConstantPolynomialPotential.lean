import GaloisForLFunctions.HTGeometry.GomesPolynomialHamiltonianFibers

/-!
# Constant potentials and the affine reconstruction exception

The scalar reconstruction experiment completely classifies the profiles of constant
Hamiltonian potentials. Every such potential is nonnegative; all profiles are affine,
with the two opposite slopes determined by a square root and arbitrary intercepts.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The affine potential retains the squared slope and discards its sign and intercept. -/
theorem gomesDilatonPotential_affine (a b x : ℝ) :
    dilatonPotential (C a * X + C b) x = a ^ (2 : ℕ) / 4 := by
  simp [dilatonPotential]

/-- Every profile of a constant potential is affine, with its exact half-slope square. -/
theorem gomesDilatonPotential_constant_iff (H : ℝ[X]) (k : ℝ) :
    (∀ x : ℝ, dilatonPotential H x = k) ↔
      ∃ r b : ℝ, H = C (2 * r) * X + C b ∧ r ^ (2 : ℕ) = k := by
  constructor
  · intro h
    have hp : gomesDilatonPotentialPolynomial H = C k := by
      apply Polynomial.funext
      intro x
      rw [gomesDilatonPotentialPolynomial_eval, eval_C, h]
    obtain ⟨r, hr, hk⟩ :=
      (gomesPolynomialRiccati_constant_iff (gomesDilatonConnectionPolynomial H) k).mp hp
    have hd : H.derivative = C (2 * r) := by
      apply Polynomial.funext
      intro x
      have hx := congrArg (Polynomial.eval x) hr
      simp only [gomesDilatonConnectionPolynomial, eval_mul, eval_C] at hx ⊢
      linarith
    obtain ⟨b, hb⟩ := (gomesDilatonDerivative_constant_iff H (2 * r)).mp hd
    exact ⟨r, b, hb, hk⟩
  · rintro ⟨r, b, rfl, rfl⟩ x
    rw [gomesDilatonPotential_affine]
    ring

/-- The possible constant potentials are exactly the nonnegative real numbers. -/
theorem gomesDilatonPotential_constant_image_iff (k : ℝ) :
    (∃ H : ℝ[X], ∀ x : ℝ, dilatonPotential H x = k) ↔ 0 ≤ k := by
  constructor
  · rintro ⟨H, h⟩
    obtain ⟨r, _, _, hr⟩ := (gomesDilatonPotential_constant_iff H k).mp h
    rw [← hr]
    exact sq_nonneg r
  · intro h
    refine ⟨C (2 * Real.sqrt k) * X, (gomesDilatonPotential_constant_iff _ _).mpr ?_⟩
    exact ⟨Real.sqrt k, 0, by rw [map_zero, add_zero], Real.sq_sqrt h⟩

/-- A prescribed square yields precisely the two opposite affine slope families. -/
theorem gomesDilatonPotential_square_fiber (H : ℝ[X]) (r : ℝ) :
    (∀ x : ℝ, dilatonPotential H x = r ^ (2 : ℕ)) ↔
      (∃ b : ℝ, H = C (2 * r) * X + C b) ∨
        ∃ b : ℝ, H = C (-2 * r) * X + C b := by
  rw [gomesDilatonPotential_constant_iff]
  constructor
  · rintro ⟨s, b, hb, hs⟩
    have hp : (s - r) * (s + r) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with he | he
    · exact Or.inl ⟨b, by rwa [sub_eq_zero.mp he] at hb⟩
    · right
      refine ⟨b, ?_⟩
      rw [eq_neg_of_add_eq_zero_left he] at hb
      simpa only [mul_neg, neg_mul] using hb
  · rintro (⟨b, hb⟩ | ⟨b, hb⟩)
    · exact ⟨r, b, hb, rfl⟩
    · exact ⟨-r, b, by simpa only [mul_neg, neg_mul] using hb, by ring⟩

/-- Zero scalar potential has only constant log-profile preimages. -/
theorem gomesDilatonPotential_zero_iff (H : ℝ[X]) :
    (∀ x : ℝ, dilatonPotential H x = 0) ↔ ∃ b : ℝ, H = C b := by
  have h := gomesDilatonPotential_square_fiber H 0
  simpa using h

/-- The free Schwartz Hamiltonian is realized by exactly the constant profile family. -/
theorem gomesDilatonHamiltonian_free_iff (H : ℝ[X]) :
    dilatonHamiltonianCLM H = dilatonHamiltonianCLM 0 ↔ ∃ b : ℝ, H = C b := by
  rw [gomesDilatonHamiltonian_potential_eq_iff, ← gomesDilatonPotential_zero_iff]
  constructor
  · intro h x
    have hx := congrFun h x
    simpa [dilatonPotential] using hx
  · intro h
    funext x
    simpa [dilatonPotential] using h x

/-- Two affine Hamiltonians coincide exactly when their slopes have the same square. -/
theorem gomesDilatonHamiltonian_affine_eq_iff (a b c d : ℝ) :
    dilatonHamiltonianCLM (C a * X + C b) =
      dilatonHamiltonianCLM (C c * X + C d) ↔ a ^ (2 : ℕ) = c ^ (2 : ℕ) := by
  rw [gomesDilatonHamiltonian_potential_eq_iff]
  constructor
  · intro h
    have hx := congrFun h 0
    rw [gomesDilatonPotential_affine, gomesDilatonPotential_affine] at hx
    linarith
  · intro h
    funext x
    rw [gomesDilatonPotential_affine, gomesDilatonPotential_affine, h]

/-- First-order connections retain the affine slope itself. -/
theorem gomesDilatonConnection_affine_eq_iff (a b c d : ℝ) :
    dilatonSuperchargeCLM (C a * X + C b) =
      dilatonSuperchargeCLM (C c * X + C d) ↔ a = c := by
  rw [gomesDilatonConnection_eq_iff]
  simp

end GaloisForLFunctions.HTGeometry
