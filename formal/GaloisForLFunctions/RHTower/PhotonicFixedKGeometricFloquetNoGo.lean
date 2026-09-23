import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Fixed-wavenumber geometric Floquet obstruction

For the literal two-sided rotating material coefficient operator, a geometric
sideband `lam ^ n` is an eigenfamily of the material convolution. A temporal
Maxwell equation with one conserved spatial wavenumber would then require its
single material eigenvalue times `(ω + n Δ)^2` to equal one nonzero spatial
constant at every grade. Three consecutive grades make this impossible for
nonzero drive and nonzero spatial wavenumber.

This closes the fixed-wavenumber geometric coefficient ansatz, not the full
rotating-cylinder Maxwell boundary problem. Grade-dependent spatial dispersion
or vector-valued boundary states are outside this theorem.
-/

namespace RHTower

set_option autoImplicit false

/-- The second difference of three squared Floquet frequencies cannot equal
the same nonzero spatial constant after multiplication by one fixed scalar. -/
theorem ptr_no_three_fixedK_geometric_frequencies
    (ω Δ C K : ℂ) (hΔ : Δ ≠ 0) (hK : K ≠ 0)
    (h0 : ω ^ 2 * C = K)
    (h1 : (ω + Δ) ^ 2 * C = K)
    (h2 : (ω + 2 * Δ) ^ 2 * C = K) : False := by
  have hsec : 2 * Δ ^ 2 * C = 0 := by
    calc
      2 * Δ ^ 2 * C = ω ^ 2 * C - 2 * ((ω + Δ) ^ 2 * C) +
          (ω + 2 * Δ) ^ 2 * C := by ring
      _ = 0 := by rw [h0, h1, h2]; ring
  have hcoef : (2 : ℂ) * Δ ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hΔ)
  have hC : C = 0 := (mul_eq_zero.mp hsec).resolve_left hcoef
  apply hK
  simpa [hC] using h0.symm

/-- Stronger positive rigidity: three all-grade equations force both the
material response and the spatial response to vanish. -/
theorem ptr_three_fixedK_geometric_frequencies_common_null
    (ω Δ C K : ℂ) (hΔ : Δ ≠ 0)
    (h0 : ω ^ 2 * C = K)
    (h1 : (ω + Δ) ^ 2 * C = K)
    (h2 : (ω + 2 * Δ) ^ 2 * C = K) : C = 0 ∧ K = 0 := by
  have hsec : 2 * Δ ^ 2 * C = 0 := by
    calc
      2 * Δ ^ 2 * C = ω ^ 2 * C - 2 * ((ω + Δ) ^ 2 * C) +
          (ω + 2 * Δ) ^ 2 * C := by ring
      _ = 0 := by rw [h0, h1, h2]; ring
  have hcoef : (2 : ℂ) * Δ ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hΔ)
  have hC : C = 0 := (mul_eq_zero.mp hsec).resolve_left hcoef
  exact ⟨hC, by simpa [hC] using h0.symm⟩

/-- Full balanced helical material convolution on bilateral coefficients. -/
def ptrMaterialCoefficient (d a : ℂ) (c : ℤ → ℂ) (n : ℤ) : ℂ :=
  d * c n + a * (c (n - 1) + c (n + 1))

/-- A nonzero geometric sequence is a material-convolution eigenfamily, with
eigenvalue independent of the Floquet grade. -/
theorem ptrMaterialCoefficient_geometric (d a lam : ℂ) (hlam : lam ≠ 0)
    (n : ℤ) :
    ptrMaterialCoefficient d a (fun j => lam ^ j) n =
      (d + a * (lam + lam⁻¹)) * lam ^ n := by
  rw [ptrMaterialCoefficient, zpow_sub₀ hlam, zpow_add₀ hlam]
  simp only [zpow_one, div_eq_mul_inv]
  ring

/-- No nonzero geometric sideband solves the all-grade fixed-spatial-
wavenumber Maxwell coefficient equation when drive and wavenumber are nonzero. -/
theorem ptr_no_fixedK_geometric_coefficient_solution
    (ω Δ k μ d a lam : ℂ)
    (hΔ : Δ ≠ 0) (hk : k ≠ 0) (hμ : μ ≠ 0) (hlam : lam ≠ 0)
    (hmaxwell : ∀ n : ℤ,
      (ω + (n : ℂ) * Δ) ^ 2 *
        ptrMaterialCoefficient d a (fun j => lam ^ j) n =
      (k ^ 2 / μ) * lam ^ n) : False := by
  have hfreq (n : ℤ) :
      (ω + (n : ℂ) * Δ) ^ 2 * (d + a * (lam + lam⁻¹)) = k ^ 2 / μ := by
    have h := hmaxwell n
    rw [ptrMaterialCoefficient_geometric d a lam hlam n] at h
    apply mul_right_cancel₀ (zpow_ne_zero n hlam)
    simpa only [mul_assoc] using h
  have hK : k ^ 2 / μ ≠ 0 := div_ne_zero (pow_ne_zero 2 hk) hμ
  apply ptr_no_three_fixedK_geometric_frequencies ω Δ
    (d + a * (lam + lam⁻¹)) (k ^ 2 / μ) hΔ hK
  · simpa using hfreq 0
  · simpa using hfreq 1
  · simpa using hfreq 2

/-- Sharp necessary exception: any geometric all-grade solution has either
zero drive frequency or zero spatial wavenumber. -/
theorem ptr_fixedK_geometric_solution_static_or_zeroK
    (ω Δ k μ d a lam : ℂ)
    (hμ : μ ≠ 0) (hlam : lam ≠ 0)
    (hmaxwell : ∀ n : ℤ,
      (ω + (n : ℂ) * Δ) ^ 2 *
        ptrMaterialCoefficient d a (fun j => lam ^ j) n =
      (k ^ 2 / μ) * lam ^ n) :
    Δ = 0 ∨ k = 0 := by
  by_cases hΔ : Δ = 0
  · exact Or.inl hΔ
  · right
    by_contra hk
    exact ptr_no_fixedK_geometric_coefficient_solution
      ω Δ k μ d a lam hΔ hk hμ hlam hmaxwell

/-- Closed no-premise formulation: no nondegenerate fixed-`k` temporal-Maxwell
coefficient system admits an all-grade geometric Floquet solution. -/
theorem ptr_no_nonzero_fixedK_geometric_solution :
    ¬ ∃ ω Δ k μ d a lam : ℂ,
      Δ ≠ 0 ∧ k ≠ 0 ∧ μ ≠ 0 ∧ lam ≠ 0 ∧
      ∀ n : ℤ,
        (ω + (n : ℂ) * Δ) ^ 2 *
          ptrMaterialCoefficient d a (fun j => lam ^ j) n =
        (k ^ 2 / μ) * lam ^ n := by
  rintro ⟨ω, Δ, k, μ, d, a, lam, hΔ, hk, hμ, hlam, hmaxwell⟩
  exact ptr_no_fixedK_geometric_coefficient_solution
    ω Δ k μ d a lam hΔ hk hμ hlam hmaxwell

/-- Exact survivor for a grade-dependent spatial dispersion: a nonzero
geometric sideband solves the coefficient equation precisely when the spatial
coefficient is the displayed squared-Floquet-frequency profile. -/
theorem ptr_geometric_coefficient_dispersion_iff
    (ω Δ d a lam : ℂ) (hlam : lam ≠ 0) (K : ℤ → ℂ) :
    (∀ n : ℤ,
      (ω + (n : ℂ) * Δ) ^ 2 *
        ptrMaterialCoefficient d a (fun j => lam ^ j) n =
      K n * lam ^ n) ↔
    (∀ n : ℤ,
      K n = (ω + (n : ℂ) * Δ) ^ 2 *
        (d + a * (lam + lam⁻¹))) := by
  constructor
  · intro h n
    have hn := h n
    rw [ptrMaterialCoefficient_geometric d a lam hlam n] at hn
    have hc : ((ω + (n : ℂ) * Δ) ^ 2 *
        (d + a * (lam + lam⁻¹))) * lam ^ n = K n * lam ^ n := by
      simpa only [mul_assoc] using hn
    exact (mul_right_cancel₀ (zpow_ne_zero n hlam) hc).symm
  · intro h n
    rw [ptrMaterialCoefficient_geometric d a lam hlam n, h n]
    ring

end RHTower
