import GaloisForLFunctions.HTGeometry.GomesDilatonPotentialEnergyShifts

/-!
# Energy-reference reconstruction for actual Schwartz Hamiltonians

The polynomial Riccati classification lifts to the corpus's actual continuous linear
Schwartz operators. One everywhere nonzero Gaussian probe detects the entire energy
shift. Removing the potential's origin value gives the exact energy-reference invariant.
-/

noncomputable section
open Polynomial
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- An exact real scalar energy shift on every actual Schwartz state. -/
def gomesDilatonEnergyShift (H K : ℝ[X]) (k : ℝ) : Prop :=
  ∀ ψ : 𝓢(ℝ, ℂ), dilatonHamiltonianCLM H ψ = dilatonHamiltonianCLM K ψ + (k : ℂ) • ψ

/-- One nonvanishing Gaussian state detects every scalar potential shift. -/
theorem gomesDilatonEnergyShift_gaussian_potential_iff (H K : ℝ[X]) (k : ℝ) :
    (dilatonHamiltonianCLM H gaussianSchwartz =
      dilatonHamiltonianCLM K gaussianSchwartz + (k : ℂ) • gaussianSchwartz) ↔
        ∀ x : ℝ, dilatonPotential H x = dilatonPotential K x + k := by
  constructor
  · intro h x
    have hx := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ x) h
    change dilatonHamiltonianCLM H gaussianSchwartz x =
      dilatonHamiltonianCLM K gaussianSchwartz x + (k : ℂ) * gaussianSchwartz x at hx
    rw [dilatonHamiltonianCLM_apply, dilatonHamiltonianCLM_apply] at hx
    have he : (dilatonPotential H x : ℂ) * gaussianSchwartz x =
        ((dilatonPotential K x : ℂ) + k) * gaussianSchwartz x := by
      linear_combination hx
    have hg : gaussianSchwartz x ≠ 0 := by
      rw [gaussianSchwartz_apply]
      exact Complex.ofReal_ne_zero.mpr (gaussReal_pos x).ne'
    exact_mod_cast (mul_right_cancel₀ hg he)
  · intro h
    ext x
    change dilatonHamiltonianCLM H gaussianSchwartz x =
      dilatonHamiltonianCLM K gaussianSchwartz x + (k : ℂ) * gaussianSchwartz x
    rw [dilatonHamiltonianCLM_apply, dilatonHamiltonianCLM_apply, h x]
    push_cast
    ring

/-- Exact scalar-potential differences are equivalent to energy shifts of the full Schwartz operators. -/
theorem gomesDilatonEnergyShift_potential_iff (H K : ℝ[X]) (k : ℝ) :
    gomesDilatonEnergyShift H K k ↔
      ∀ x : ℝ, dilatonPotential H x = dilatonPotential K x + k := by
  constructor
  · intro h
    exact (gomesDilatonEnergyShift_gaussian_potential_iff H K k).mp (h gaussianSchwartz)
  · intro h ψ
    ext x
    change dilatonHamiltonianCLM H ψ x = dilatonHamiltonianCLM K ψ x + (k : ℂ) * ψ x
    rw [dilatonHamiltonianCLM_apply, dilatonHamiltonianCLM_apply, h x]
    push_cast
    ring

/-- Agreement on the single Gaussian probe is already agreement on the full Schwartz domain. -/
theorem gomesDilatonEnergyShift_gaussian_iff (H K : ℝ[X]) (k : ℝ) :
    gomesDilatonEnergyShift H K k ↔
      dilatonHamiltonianCLM H gaussianSchwartz =
        dilatonHamiltonianCLM K gaussianSchwartz + (k : ℂ) • gaussianSchwartz := by
  rw [gomesDilatonEnergyShift_potential_iff, gomesDilatonEnergyShift_gaussian_potential_iff]

/-- The zero-energy-reference case is literal equality of continuous linear operators. -/
theorem gomesDilatonEnergyShift_zero_iff (H K : ℝ[X]) :
    gomesDilatonEnergyShift H K 0 ↔ dilatonHamiltonianCLM H = dilatonHamiltonianCLM K := by
  rw [gomesDilatonEnergyShift_potential_iff, gomesDilatonHamiltonian_potential_eq_iff]
  simp only [add_zero, funext_iff]

/-- The complete polynomial profile trichotomy holds for the actual Hamiltonians. -/
theorem gomesDilatonEnergyShift_profiles_iff (H K : ℝ[X]) (k : ℝ) :
    gomesDilatonEnergyShift H K k ↔
      ((∃ c : ℝ, H = K + C c) ∧ k = 0) ∨
        (∃ a b c d : ℝ, H = C (2 * a) * X + C b ∧
          K = C (2 * c) * X + C d ∧ a ^ (2 : ℕ) = c ^ (2 : ℕ) + k) ∨
            ∃ a b c : ℝ, H = C (k / 2) * X ^ (2 : ℕ) + C a * X + C b ∧ K = -H + C c := by
  rw [gomesDilatonEnergyShift_potential_iff, gomesDilatonPotential_shifted_profiles_iff]

/-- Reversing the comparison reverses precisely the scalar energy offset. -/
theorem gomesDilatonEnergyShift_symm_iff (H K : ℝ[X]) (k : ℝ) :
    gomesDilatonEnergyShift H K k ↔ gomesDilatonEnergyShift K H (-k) := by
  rw [gomesDilatonEnergyShift_potential_iff, gomesDilatonEnergyShift_potential_iff]
  constructor <;> intro h x <;> have hx := h x <;> linarith

/-- The scalar energy offset of a fixed pair of Hamiltonians is unique. -/
theorem gomesDilatonEnergyShift_unique_iff (H K : ℝ[X]) (a b : ℝ) :
    (gomesDilatonEnergyShift H K a ∧ gomesDilatonEnergyShift H K b) ↔
      gomesDilatonEnergyShift H K a ∧ a = b := by
  constructor
  · rintro ⟨ha, hb⟩
    have hx := (gomesDilatonEnergyShift_potential_iff H K a).mp ha 0
    have hy := (gomesDilatonEnergyShift_potential_iff H K b).mp hb 0
    exact ⟨ha, by linarith⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, h⟩

/-- The potential after removing its origin energy reference. -/
def gomesDilatonCenteredPotential (H : ℝ[X]) (x : ℝ) : ℝ :=
  dilatonPotential H x - dilatonPotential H 0

/-- Centering retains exactly the potential shape and exposes the missing energy reference. -/
theorem gomesDilatonEnergyShift_centered_iff (H K : ℝ[X]) (k : ℝ) :
    gomesDilatonEnergyShift H K k ↔
      gomesDilatonCenteredPotential H = gomesDilatonCenteredPotential K ∧
        k = dilatonPotential H 0 - dilatonPotential K 0 := by
  rw [gomesDilatonEnergyShift_potential_iff]
  constructor
  · intro h
    constructor
    · funext x
      unfold gomesDilatonCenteredPotential
      rw [h x, h 0]
      ring
    · have hx := h 0
      linarith
  · rintro ⟨h, hk⟩ x
    have hx := congrFun h x
    unfold gomesDilatonCenteredPotential at hx
    linarith

/-- Equality after discarding the energy reference is precisely existence of a scalar operator shift. -/
theorem gomesDilatonCenteredPotential_eq_iff (H K : ℝ[X]) :
    gomesDilatonCenteredPotential H = gomesDilatonCenteredPotential K ↔
      ∃ k : ℝ, gomesDilatonEnergyShift H K k := by
  constructor
  · intro h
    exact ⟨dilatonPotential H 0 - dilatonPotential K 0,
      (gomesDilatonEnergyShift_centered_iff H K _).mpr ⟨h, rfl⟩⟩
  · rintro ⟨k, h⟩
    exact ((gomesDilatonEnergyShift_centered_iff H K k).mp h).1

/-- Every real scalar offset is realized on the actual Schwartz domain by opposite quadratics. -/
theorem gomesDilatonEnergyShift_surjective (k : ℝ) :
    ∃ H K : ℝ[X], gomesDilatonEnergyShift H K k := by
  obtain ⟨H, K, h⟩ := gomesDilatonPotential_energy_shift_surjective k
  exact ⟨H, K, (gomesDilatonEnergyShift_potential_iff H K k).mpr h⟩

end GaloisForLFunctions.HTGeometry
