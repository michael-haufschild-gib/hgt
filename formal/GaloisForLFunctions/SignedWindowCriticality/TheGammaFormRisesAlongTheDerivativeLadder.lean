import GaloisForLFunctions.SignedWindowCriticality.TheSectorsAreTheMomentConditionsOfTheJets
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws

/-!
# The Gamma form rises along the derivative ladder

The archimedean form `A(g) = (1/2π)∫|ĝ(r)|²Ω(r)dr` of Weil's form has the symbol
`Ω(r) = Re ψ(¼ + ir/2) − log π`, which increases with `|r|` (`gammaBracket_mono`). Differentiation
multiplies `|ĝ|²` by `r²`, another increasing function of `|r|`. Chebyshev's association inequality
for the two co-monotone weights gives:

* **The ladder inequality** (`archForm_mul_le`): `A(g)·‖g'‖² ≤ A(g')·‖g‖²` for every smooth bump:
  the Rayleigh quotient of the Gamma form does not decrease under `d/dx`
  (`archForm_div_le_of_deriv`, `archForm_iteratedDeriv_div_mono`).
* **The Gamma form prefers the even sector** (`archForm_odd_floor_of_even_floor`): on every
  symmetric window, a floor `A ≥ μ‖·‖²` on the even smooth tests holds on the odd ones, because
  every odd test is the derivative of an even one (`exists_even_antideriv`); and a floor on the odd
  tests holds on the even tests of mean zero (`archForm_meanZero_floor_of_odd_floor`).

So the sector order of the archimedean place is a covariance inequality along the derivative ladder,
not a symmetry: its even ground energy never exceeds its odd one. In Weil's form the pole adds its
positive square to the even sector and its negative square to the odd sector, against this order.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis DimensionZeroGeometryOfSpecZ
open Zeta23
open _root_.RHTower (archForm)

variable {g : ℝ → ℝ}

theorem eq_zero_of_integral_sq_eq_zero {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h0 : ∫ u, g u ^ 2 = 0) : g = 0 := by
  have hi := integrable_sq_of_continuous hg hgc
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg (g u)) hi).mp h0
  have hc : Continuous fun u => g u ^ 2 := hg.pow 2
  have := (hc.ae_eq_iff_eq volume continuous_zero).mp hae
  funext u
  have hu : g u ^ 2 = 0 := congrFun this u
  exact pow_eq_zero_iff two_ne_zero |>.mp hu

/-- **The ladder inequality of the Gamma form**: `A(g)‖g'‖² ≤ A(g')‖g‖²`. With `w = |ĝ|²` and the
mean `ρ² = ∫r²w/∫w`, the pointwise inequality `(Ω(r) − Ω(ρ))(r² − ρ²) ≥ 0` integrates to
`∫Ωr²w ≥ ρ²∫Ωw`. -/
theorem archForm_mul_le (hg : ContDiff ℝ 3 g) (hgc : HasCompactSupport g) :
    archForm g * ∫ u, deriv g u ^ 2 ≤ archForm (deriv g) * ∫ u, g u ^ 2 := by
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  have hd2 : ContDiff ℝ 2 (deriv g) := hg.deriv'
  have hdc : HasCompactSupport (deriv g) := hgc.deriv
  set F : ℝ → ℝ := fun r => ‖paperFT (fun u => ((deriv g u : ℝ) : ℂ)) r‖ ^ 2
  set G : ℝ → ℝ := fun r => ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2
  set a : ℝ → ℝ := fun r => EF.gammaBracket r
  have hFi : Integrable F := _root_.RHTower.integrable_normSq_paperFT_ofReal hd2 hdc
  have hGi : Integrable G := _root_.RHTower.integrable_normSq_paperFT_ofReal hg2 hgc
  have hFai : Integrable fun r => F r * a r :=
    _root_.RHTower.integrable_normSq_paperFT_mul_gammaBracket hd2 hdc
  have hGai : Integrable fun r => G r * a r :=
    _root_.RHTower.integrable_normSq_paperFT_mul_gammaBracket hg2 hgc
  have hFG : ∀ r, F r = r ^ 2 * G r := fun r =>
    norm_sq_paperFT_deriv (hg.of_le (by norm_num)) hgc r
  have hPF : ∫ r, F r = 2 * π * ∫ u, deriv g u ^ 2 :=
    integral_norm_sq_paperFT_real hd2.continuous hdc
  have hPG : ∫ r, G r = 2 * π * ∫ u, g u ^ 2 :=
    integral_norm_sq_paperFT_real hg.continuous hgc
  have hAF : archForm (deriv g) = 1 / (2 * π) * ∫ r, F r * a r := rfl
  have hAG : archForm g = 1 / (2 * π) * ∫ r, G r * a r := rfl
  have hπ : 0 < 2 * π := by positivity
  -- the case `g = 0`
  by_cases hz : ∫ u, g u ^ 2 = 0
  · have hg0 := eq_zero_of_integral_sq_eq_zero hg.continuous hgc hz
    have hG0 : ∀ r, G r = 0 := fun r => by
      simp only [G, hg0, Pi.zero_apply, Complex.ofReal_zero]
      simp [paperFT]
    have : archForm g = 0 := by
      rw [hAG]; simp only [hG0, zero_mul, integral_zero, mul_zero]
    rw [this, hz, zero_mul, mul_zero]
  have hG0 : 0 < ∫ r, G r := by
    rw [hPG]
    exact mul_pos hπ (lt_of_le_of_ne (integral_nonneg fun u => sq_nonneg _) (Ne.symm hz))
  set ρ2 := (∫ r, F r) / ∫ r, G r
  have hρ2 : 0 ≤ ρ2 := div_nonneg (integral_nonneg fun r => sq_nonneg _) hG0.le
  set ρ := Real.sqrt ρ2
  have hρ : ρ ^ 2 = ρ2 := Real.sq_sqrt hρ2
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  -- Chebyshev's covariance inequality
  have hpt : ∀ r, 0 ≤ (a r - a ρ) * (r ^ 2 - ρ ^ 2) * G r := by
    intro r
    refine mul_nonneg ?_ (sq_nonneg _)
    rcases le_total ρ |r| with h | h
    · have h1 : a ρ ≤ a r := _root_.RHTower.ArchimedeanAnomaly.gammaBracket_mono
        (by rwa [abs_of_nonneg hρ0])
      have h2 : ρ ^ 2 ≤ r ^ 2 := by
        rw [← sq_abs r]; exact pow_le_pow_left₀ hρ0 h 2
      exact mul_nonneg (by linarith) (by linarith)
    · have h1 : a r ≤ a ρ := _root_.RHTower.ArchimedeanAnomaly.gammaBracket_mono
        (by rwa [abs_of_nonneg hρ0])
      have h2 : r ^ 2 ≤ ρ ^ 2 := by
        rw [← sq_abs r]; exact pow_le_pow_left₀ (abs_nonneg r) h 2
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hexp : (fun r => (a r - a ρ) * (r ^ 2 - ρ ^ 2) * G r) =
      fun r => F r * a r - a ρ * F r - (ρ ^ 2 * (G r * a r) - a ρ * ρ ^ 2 * G r) := by
    funext r; rw [hFG]; ring
  have i1 : Integrable fun r => F r * a r - a ρ * F r := hFai.sub (hFi.const_mul _)
  have i2 : Integrable fun r => ρ ^ 2 * (G r * a r) - a ρ * ρ ^ 2 * G r :=
    (hGai.const_mul _).sub (hGi.const_mul _)
  have hint : 0 ≤ ∫ r, (a r - a ρ) * (r ^ 2 - ρ ^ 2) * G r := integral_nonneg hpt
  rw [hexp, integral_sub i1 i2, integral_sub hFai (hFi.const_mul _),
    integral_sub (hGai.const_mul _) (hGi.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul] at hint
  have hρG : ρ ^ 2 * ∫ r, G r = ∫ r, F r := by
    rw [hρ]
    show (∫ r, F r) / (∫ r, G r) * ∫ r, G r = ∫ r, F r
    exact div_mul_cancel₀ _ hG0.ne'
  have hcheb : (∫ r, G r * a r) * (∫ r, F r) ≤ (∫ r, F r * a r) * ∫ r, G r := by
    have h3 : a ρ * ρ ^ 2 * ∫ r, G r = a ρ * ∫ r, F r := by rw [mul_assoc, hρG]
    have h1 : ρ ^ 2 * (∫ r, G r * a r) ≤ ∫ r, F r * a r := by linarith
    calc (∫ r, G r * a r) * (∫ r, F r) = (ρ ^ 2 * ∫ r, G r * a r) * ∫ r, G r := by
          rw [← hρG]; ring
      _ ≤ (∫ r, F r * a r) * ∫ r, G r := mul_le_mul_of_nonneg_right h1 hG0.le
  rw [hAF, hAG]
  have e1 : ∫ u, deriv g u ^ 2 = (∫ r, F r) / (2 * π) := by rw [hPF]; field_simp
  have e2 : ∫ u, g u ^ 2 = (∫ r, G r) / (2 * π) := by rw [hPG]; field_simp
  rw [e1, e2]
  have : 0 < (2 * π) ^ 2 := by positivity
  calc 1 / (2 * π) * (∫ r, G r * a r) * ((∫ r, F r) / (2 * π))
      = ((∫ r, G r * a r) * (∫ r, F r)) / (2 * π) ^ 2 := by ring
    _ ≤ ((∫ r, F r * a r) * ∫ r, G r) / (2 * π) ^ 2 := by gcongr
    _ = 1 / (2 * π) * (∫ r, F r * a r) * ((∫ r, G r) / (2 * π)) := by ring

/-- The Rayleigh quotient of the Gamma form does not decrease under differentiation. -/
theorem archForm_div_le_of_deriv (hg : ContDiff ℝ 3 g) (hgc : HasCompactSupport g)
    (h0 : 0 < ∫ u, g u ^ 2) (h1 : 0 < ∫ u, deriv g u ^ 2) :
    archForm g / ∫ u, g u ^ 2 ≤ archForm (deriv g) / ∫ u, deriv g u ^ 2 := by
  rw [div_le_div_iff₀ h0 h1]
  exact archForm_mul_le hg hgc

/-- Along the jets of a nonzero smooth bump the Rayleigh quotients of the Gamma form increase. -/
theorem archForm_iteratedDeriv_div_mono {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφ0 : φ ≠ 0) (k : ℕ) :
    archForm (iteratedDeriv k φ) / ∫ u, iteratedDeriv k φ u ^ 2 ≤
      archForm (iteratedDeriv (k + 1) φ) / ∫ u, iteratedDeriv (k + 1) φ u ^ 2 := by
  have hpos : ∀ j, 0 < ∫ u, iteratedDeriv j φ u ^ 2 := fun j => by
    rcases (integral_nonneg (f := fun u => iteratedDeriv j φ u ^ 2) fun u => sq_nonneg _).eq_or_lt
      with h | h
    · exfalso
      have hz := eq_zero_of_integral_sq_eq_zero (contDiff_iteratedDeriv_of_smooth hφ j).continuous
        (iteratedDeriv_mem_realTests hφ hφc j).2 h.symm
      have := eq_zero_of_sum_smul_iteratedDeriv hφ hφc hφ0 (j + 1) (fun i => if (i : ℕ) = j then 1 else 0)
        (by
          rw [Finset.sum_eq_single (Fin.last j)]
          · simp [hz]
          · intro b _ hb
            have : (b : ℕ) ≠ j := fun h => hb (Fin.ext (by simpa using h))
            simp [this]
          · simp)
      have h1 := congrFun this (Fin.last j)
      simp at h1
    · exact h
  rw [iteratedDeriv_succ]
  exact archForm_div_le_of_deriv
    (by exact_mod_cast contDiff_infty.mp (contDiff_iteratedDeriv_of_smooth hφ k) 3)
    (iteratedDeriv_mem_realTests hφ hφc k).2 (hpos k)
    (by rw [← iteratedDeriv_succ]; exact hpos (k + 1))

/-! ### The Gamma form prefers the even sector -/

variable {a μ : ℝ}

/-- **An even floor of the Gamma form is an odd floor**: if `A(φ) ≥ μ‖φ‖²` for every even smooth
test of `[−a, a]`, then `A(G) ≥ μ‖G‖²` for every odd one. -/
theorem archForm_odd_floor_of_even_floor
    (he : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → SupportedIn a φ → (∀ x, φ (-x) = φ x) →
      μ * ∫ u, φ u ^ 2 ≤ archForm φ)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (hGa : SupportedIn a G) (hGo : ∀ x, G (-x) = -G x) :
    μ * ∫ u, G u ^ 2 ≤ archForm G := by
  obtain ⟨ψ, hψ, hψa, hψe, hψG⟩ := exists_even_antideriv hG hGa hGo
  have hψc := hasCompactSupport_of_supportedIn' hψa
  have hlad := archForm_mul_le (by exact_mod_cast contDiff_infty.mp hψ 3) hψc
  rw [hψG] at hlad
  have hfl := he ψ hψ hψa hψe
  rcases (integral_nonneg (f := fun u => ψ u ^ 2) fun u => sq_nonneg _).eq_or_lt with h0 | h0
  · have hψ0 := eq_zero_of_integral_sq_eq_zero hψ.continuous hψc h0.symm
    have hG0 : G = 0 := by rw [← hψG, hψ0]; funext x; exact deriv_const x 0
    subst hG0
    have hA : archForm (0 : ℝ → ℝ) = 0 := by
      show 1 / (2 * π) * ∫ r : ℝ, ‖paperFT (fun u => (((0 : ℝ → ℝ) u : ℝ) : ℂ)) r‖ ^ 2 *
        EF.gammaBracket r = 0
      simp [paperFT]
    simp [hA]
  · have hG2 : 0 ≤ ∫ u, G u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have : μ * (∫ u, ψ u ^ 2) * ∫ u, G u ^ 2 ≤ archForm G * ∫ u, ψ u ^ 2 :=
      (mul_le_mul_of_nonneg_right hfl hG2).trans hlad
    nlinarith

/-- **An odd floor of the Gamma form is a floor on the even tests of mean zero**: these are the
derivatives of the odd tests. -/
theorem archForm_meanZero_floor_of_odd_floor
    (ho : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → SupportedIn a φ → (∀ x, φ (-x) = -φ x) →
      μ * ∫ u, φ u ^ 2 ≤ archForm φ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψa : SupportedIn a ψ) (hψo : ∀ x, ψ (-x) = -ψ x) :
    μ * ∫ u, deriv ψ u ^ 2 ≤ archForm (deriv ψ) := by
  have hψc := hasCompactSupport_of_supportedIn' hψa
  have hlad := archForm_mul_le (by exact_mod_cast contDiff_infty.mp hψ 3) hψc
  have hfl := ho ψ hψ hψa hψo
  rcases (integral_nonneg (f := fun u => ψ u ^ 2) fun u => sq_nonneg _).eq_or_lt with h0 | h0
  · have hψ0 := eq_zero_of_integral_sq_eq_zero hψ.continuous hψc h0.symm
    have hd : deriv ψ = 0 := by rw [hψ0]; funext x; exact deriv_const x 0
    rw [hd]
    have hA : archForm (0 : ℝ → ℝ) = 0 := by
      show 1 / (2 * π) * ∫ r : ℝ, ‖paperFT (fun u => (((0 : ℝ → ℝ) u : ℝ) : ℂ)) r‖ ^ 2 *
        EF.gammaBracket r = 0
      simp [paperFT]
    simp [hA]
  · have hG2 : 0 ≤ ∫ u, deriv ψ u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have : μ * (∫ u, ψ u ^ 2) * ∫ u, deriv ψ u ^ 2 ≤ archForm (deriv ψ) * ∫ u, ψ u ^ 2 :=
      (mul_le_mul_of_nonneg_right hfl hG2).trans hlad
    nlinarith

end GaloisForLFunctions.SignedWindowCriticality

end
