import GaloisForLFunctions.HTGeometry.GomesGaussianChargeCompleteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Exact charged Gaussian point spectrum on Schwartz space

The common connection and integral-charge experiment has a complete spectral classification.
Every positive effective charge has exactly the nonnegative integer oscillator levels, each
with a one-dimensional eigenspace. Reversing charge shifts the entire list by one level.
These are classifications on the actual Schwartz domain, not claims about an unspecified
self-adjoint extension on a larger Hilbert domain.
-/

noncomputable section
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- A nonzero Schwartz eigenstate exists exactly at a charge-scaled nonnegative integer level. -/
theorem gomesGaussianChargeSpectrum_iff (a : Set.Ioi (0 : ℝ)) (ζ : ℂ) :
    (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM (gomesGaussianLogWeight a.val) ψ = ζ • ψ) ↔
      ∃ n : ℕ, ζ = 4 * (Real.pi : ℂ) * a.val * n := by
  constructor
  · rintro ⟨ψ, hψ, hζ⟩
    by_contra hn
    apply hψ
    apply (gomesGaussianChargeLadder_complete_iff a ψ).mp
    intro n
    have h := gomesDilatonHamiltonian_pair_symmetric (gomesGaussianLogWeight a.val)
      ψ (gomesGaussianChargeLadder a n)
    rw [hζ, gomesGaussianChargeLadder_eigen, schwartzPair_smul_left, schwartzPair_smul_right] at h
    have he : ζ ≠ 4 * (Real.pi : ℂ) * a.val * n := fun he => hn ⟨n, he⟩
    have hz : (ζ - 4 * (Real.pi : ℂ) * a.val * n) *
        schwartzPair ψ (gomesGaussianChargeLadder a n) = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr he)
  · rintro ⟨n, rfl⟩
    exact gomesGaussianChargeLadder_exists_eigen a n

/-- Every eigenspace at an allowed level is the scalar line through its charged rung. -/
theorem gomesGaussianChargeSpectrum_eigenline (a : Set.Ioi (0 : ℝ)) (n : ℕ) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesGaussianLogWeight a.val) ψ =
        (4 * (Real.pi : ℂ) * a.val * n) • ψ ↔
      ∃ c : ℂ, ψ = c • gomesGaussianChargeLadder a n := by
  constructor
  · intro hζ
    have hs : schwartzPair (gomesGaussianChargeLadder a n) (gomesGaussianChargeLadder a n) ≠ 0 :=
      fun hz => (gomesGaussianChargeLadder_pair_zero_iff a n n).mp hz rfl
    let c := schwartzPair ψ (gomesGaussianChargeLadder a n) /
      schwartzPair (gomesGaussianChargeLadder a n) (gomesGaussianChargeLadder a n)
    refine ⟨c, sub_eq_zero.mp ((gomesGaussianChargeLadder_complete_iff a _).mp ?_)⟩
    intro m
    rw [gomesSchwartzPair_sub_left, schwartzPair_smul_left]
    by_cases hmn : m = n
    · subst m
      dsimp only [c]
      rw [div_mul_cancel₀ _ hs, sub_self]
    · have h := gomesDilatonHamiltonian_pair_symmetric (gomesGaussianLogWeight a.val)
        ψ (gomesGaussianChargeLadder a m)
      rw [hζ, gomesGaussianChargeLadder_eigen, schwartzPair_smul_left, schwartzPair_smul_right] at h
      have he : 4 * (Real.pi : ℂ) * a.val * n ≠ 4 * (Real.pi : ℂ) * a.val * m :=
        fun he => hmn (gomesGaussianChargeLadder_eigenvalue_injective a he).symm
      have hz : (4 * (Real.pi : ℂ) * a.val * n - 4 * (Real.pi : ℂ) * a.val * m) *
          schwartzPair ψ (gomesGaussianChargeLadder a m) = 0 := by rw [sub_mul, h, sub_self]
      have hp := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr he)
      rw [hp, (gomesGaussianChargeLadder_pair_zero_iff a n m).mpr (Ne.symm hmn), mul_zero, sub_self]
  · rintro ⟨c, rfl⟩
    rw [map_smul, gomesGaussianChargeLadder_eigen, smul_smul, smul_smul, mul_comm]

/-- Complete eigenstate classification, including the zero vector at arbitrary spectral parameter. -/
theorem gomesGaussianChargeSpectrum_state_iff (a : Set.Ioi (0 : ℝ)) (ζ : ℂ) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesGaussianLogWeight a.val) ψ = ζ • ψ ↔
      ψ = 0 ∨ ∃ (n : ℕ) (c : ℂ), ζ = 4 * (Real.pi : ℂ) * a.val * n ∧
        ψ = c • gomesGaussianChargeLadder a n := by
  constructor
  · intro h
    by_cases hz : ψ = 0
    · exact Or.inl hz
    · obtain ⟨n, hn⟩ := (gomesGaussianChargeSpectrum_iff a ζ).mp ⟨ψ, hz, h⟩
      have he := h
      rw [hn] at he
      obtain ⟨c, hc⟩ := (gomesGaussianChargeSpectrum_eigenline a n ψ).mp he
      exact Or.inr ⟨n, c, hn, hc⟩
  · rintro (rfl | ⟨n, c, rfl, rfl⟩)
    · rw [map_zero, smul_zero]
    · exact (gomesGaussianChargeSpectrum_eigenline a n _).mpr ⟨c, rfl⟩

/-- Dual spectral parameters differ from the positive ones by precisely one charge quantum. -/
theorem gomesGaussianChargeSpectrum_dual_equation_iff (a : Set.Ioi (0 : ℝ)) (ζ : ℂ)
    (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesGaussianLogWeight (-a.val)) ψ = ζ • ψ ↔
      dilatonHamiltonianCLM (gomesGaussianLogWeight a.val) ψ =
        (ζ - 4 * (Real.pi : ℂ) * a.val) • ψ := by
  rw [gomesGaussianHamiltonian_dual, sub_smul]
  exact eq_sub_iff_add_eq.symm

/-- The entire reversed-charge Schwartz point spectrum is the strictly positive shifted ladder. -/
theorem gomesGaussianChargeSpectrum_dual_iff (a : Set.Ioi (0 : ℝ)) (ζ : ℂ) :
    (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM (gomesGaussianLogWeight (-a.val)) ψ = ζ • ψ) ↔
      ∃ n : ℕ, ζ = 4 * (Real.pi : ℂ) * a.val * ((n : ℂ) + 1) := by
  simp only [gomesGaussianChargeSpectrum_dual_equation_iff]
  rw [gomesGaussianChargeSpectrum_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    linear_combination hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    linear_combination hn

/-- Each shifted dual eigenspace is the same scalar line as its positive-charge partner. -/
theorem gomesGaussianChargeSpectrum_dual_eigenline (a : Set.Ioi (0 : ℝ)) (n : ℕ) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesGaussianLogWeight (-a.val)) ψ =
        (4 * (Real.pi : ℂ) * a.val * ((n : ℂ) + 1)) • ψ ↔
      ∃ c : ℂ, ψ = c • gomesGaussianChargeLadder a n := by
  rw [gomesGaussianChargeSpectrum_dual_equation_iff]
  have h : 4 * (Real.pi : ℂ) * a.val * ((n : ℂ) + 1) - 4 * (Real.pi : ℂ) * a.val =
      4 * (Real.pi : ℂ) * a.val * n := by ring
  rw [h, gomesGaussianChargeSpectrum_eigenline]

/-- The bundled eigenspace is literally the span of one nonzero charged rung. -/
theorem gomesGaussianChargeSpectrum_eigenspace (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    Module.End.eigenspace (dilatonHamiltonianCLM (gomesGaussianLogWeight a.val)).toLinearMap
      (4 * (Real.pi : ℂ) * a.val * n) =
      Submodule.span ℂ {gomesGaussianChargeLadder a n} := by
  ext ψ
  rw [Module.End.mem_eigenspace_iff, Submodule.mem_span_singleton]
  exact (gomesGaussianChargeSpectrum_eigenline a n ψ).trans
    (by simp only [eq_comm])

/-- Every allowed positive-charge eigenvalue has exactly one complex degree of freedom. -/
theorem gomesGaussianChargeSpectrum_eigenspace_finrank (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    Module.finrank ℂ (Module.End.eigenspace
      (dilatonHamiltonianCLM (gomesGaussianLogWeight a.val)).toLinearMap
      (4 * (Real.pi : ℂ) * a.val * n)) = 1 := by
  rw [gomesGaussianChargeSpectrum_eigenspace]
  exact finrank_span_singleton (gomesGaussianChargeLadder_ne_zero a n)

/-- Literal integer tensor charges multiply the complete level spacing by their effective charge. -/
theorem gomesGaussianTensorChargeSpectrum_iff (b : ℝ) (n : GomesGaussianFiniteCharge b) (ζ : ℂ) :
    (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧
      dilatonHamiltonianCLM (gomesGaussianTensorLogWeight b n.val) ψ = ζ • ψ) ↔
      ∃ k : ℕ, ζ = 4 * (Real.pi : ℂ) * (((n.val : ℝ) * b : ℝ) : ℂ) * k :=
  gomesGaussianChargeSpectrum_iff ⟨(n.val : ℝ) * b, n.property⟩ ζ

/-- The literal dual integer charge has precisely the shifted complete list of eigenvalues. -/
theorem gomesGaussianTensorDualChargeSpectrum_iff (b : ℝ) (n : GomesGaussianFiniteCharge b) (ζ : ℂ) :
    (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧
      dilatonHamiltonianCLM (gomesGaussianTensorLogWeight b (-n.val)) ψ = ζ • ψ) ↔
      ∃ k : ℕ, ζ = 4 * (Real.pi : ℂ) * (((n.val : ℝ) * b : ℝ) : ℂ) * ((k : ℂ) + 1) := by
  simp only [gomesGaussianTensorLogWeight, Int.cast_neg, neg_mul]
  exact gomesGaussianChargeSpectrum_dual_iff ⟨(n.val : ℝ) * b, n.property⟩ ζ

end GaloisForLFunctions.HTGeometry
