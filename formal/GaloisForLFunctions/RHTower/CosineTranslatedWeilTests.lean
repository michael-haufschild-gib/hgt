import GaloisForLFunctions.RHTower.PolynomialWeilTests

/-!
# Cosine-translated Weil tests

For a test `g` and `c ≥ 0`, the cosine translate
`(e^{-iγ₀c} g(u - c) + e^{iγ₀c} g(u + c))/2` has transform `cos(c(z - γ₀))·ĝ(z)`
(`paperFT_cosTranslate`).  The factor `cos(c x)` is at most `1` on the real line and at least
`sinh(c|Im x|)` off it, so it rewards the deep zeros by `e^{c·depth}` against the real ones.

Applied to the polynomial tests of `PolynomialWeilTests`, the cosine translate is a `C²` test
supported in `[-(N + c), N + c]` whose Weil summand at a zero `ρ` is
`m_ρ (cos(c x_ρ) F(x_ρ))²`, `x_ρ = γ_ρ - γ₀` (`Wsummand_cosPolyTest`), and a root of `Q` at
`±i/2 - γ₀` makes it polar-constrained (`cosPolyTest_polar_zero`).
-/

open Complex MeasureTheory Real Set Filter Topology Polynomial
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-- Translating the argument multiplies the transform by `e^{izc}`. -/
theorem paperFT_comp_sub (g : ℝ → ℂ) (c : ℝ) (z : ℂ) :
    paperFT (fun u => g (u - c)) z = cexp (I * z * c) * paperFT g z := by
  unfold paperFT
  have h : (fun y : ℝ => g (y - c) * cexp (I * z * y)) =
      fun y : ℝ => (fun t : ℝ => cexp (I * z * c) * (g t * cexp (I * z * t))) (y - c) := by
    funext y
    have e : cexp (I * z * y) = cexp (I * z * c) * cexp (I * z * ((y - c : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp only
    rw [e]
    ring
  rw [h, integral_sub_right_eq_self (fun t : ℝ => cexp (I * z * c) * (g t * cexp (I * z * t))) c,
    integral_const_mul]

/-- The cosine translate `(e^{-iγ₀c} g(u - c) + e^{iγ₀c} g(u + c))/2`. -/
def cosTranslate (γ₀ c : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun u => (cexp (-(I * γ₀ * c)) * g (u - c) + cexp (I * γ₀ * c) * g (u + c)) / 2

theorem integrable_mul_cexp_of_supp {g : ℝ → ℂ} {B : ℝ} (hgc : Continuous g)
    (hgs : ∀ u, g u ≠ 0 → |u| ≤ B) (z : ℂ) :
    Integrable (fun u : ℝ => g u * cexp (I * z * u)) := by
  have hcs : HasCompactSupport g := hasCompactSupport_of_support_subset_abs hgs
  exact (hgc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right

theorem paperFT_cosTranslate (γ₀ c : ℝ) {g : ℝ → ℂ} {B : ℝ} (hgc : Continuous g)
    (hgs : ∀ u, g u ≠ 0 → |u| ≤ B) (z : ℂ) :
    paperFT (cosTranslate γ₀ c g) z = Complex.cos (c * (z - γ₀)) * paperFT g z := by
  have h1 := paperFT_comp_sub g c z
  have h2 := paperFT_comp_sub g (-c) z
  simp only [sub_neg_eq_add, ofReal_neg] at h2
  have hs1 : ∀ u, (fun u => g (u - c)) u ≠ 0 → |u| ≤ B + |c| := fun u hu => by
    have := hgs _ hu
    have := abs_sub u c
    have h3 := abs_sub_abs_le_abs_sub u c
    linarith
  have hs2 : ∀ u, (fun u => g (u + c)) u ≠ 0 → |u| ≤ B + |c| := fun u hu => by
    have := hgs _ hu
    have h3 := abs_sub_abs_le_abs_sub u (-c)
    rw [sub_neg_eq_add, abs_neg] at h3
    linarith
  have i1 : Integrable (fun u : ℝ => g (u - c) * cexp (I * z * u)) :=
    integrable_mul_cexp_of_supp (g := fun u => g (u - c)) (by fun_prop) hs1 z
  have i2 : Integrable (fun u : ℝ => g (u + c) * cexp (I * z * u)) :=
    integrable_mul_cexp_of_supp (g := fun u => g (u + c)) (by fun_prop) hs2 z
  have hsplit : (fun u : ℝ => cosTranslate γ₀ c g u * cexp (I * z * u)) =
      fun u => (cexp (-(I * γ₀ * c)) / 2) * (g (u - c) * cexp (I * z * u)) +
        (cexp (I * γ₀ * c) / 2) * (g (u + c) * cexp (I * z * u)) := by
    funext u; simp only [cosTranslate]; ring
  rw [paperFT, hsplit, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul]
  have h1' : (∫ u : ℝ, g (u - c) * cexp (I * z * u)) = cexp (I * z * c) * paperFT g z := h1
  have h2' : (∫ u : ℝ, g (u + c) * cexp (I * z * u)) = cexp (I * z * -(c : ℂ)) * paperFT g z :=
    h2
  rw [h1', h2', Complex.cos]
  have e1 : cexp (-(I * γ₀ * c)) * cexp (I * z * c) = cexp (c * (z - γ₀) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : cexp (I * γ₀ * c) * cexp (-(I * z * c)) = cexp (-(c * (z - γ₀)) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [show cexp (I * z * -(c : ℂ)) = cexp (-(I * z * c)) by ring_nf]
  linear_combination (paperFT g z / 2) * e1 + (paperFT g z / 2) * e2

theorem cosTranslate_contDiff (γ₀ c : ℝ) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (cosTranslate γ₀ c g) := by
  unfold cosTranslate
  have h1 : ContDiff ℝ 2 (fun u : ℝ => g (u - c)) := hg.comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ 2 (fun u : ℝ => g (u + c)) := hg.comp (contDiff_id.add contDiff_const)
  exact ((contDiff_const.mul h1).add (contDiff_const.mul h2)).div_const _

theorem cosTranslate_supp (γ₀ : ℝ) {c : ℝ} (hc : 0 ≤ c) {g : ℝ → ℂ} {B : ℝ}
    (hgs : ∀ u, g u ≠ 0 → |u| ≤ B) :
    ∀ u, cosTranslate γ₀ c g u ≠ 0 → |u| ≤ B + c := by
  intro u hu
  by_contra hlt
  push Not at hlt
  have h1 : g (u - c) = 0 := by
    by_contra h
    have := hgs _ h
    have h3 := abs_sub_abs_le_abs_sub u c
    rw [abs_of_nonneg hc] at h3
    linarith
  have h2 : g (u + c) = 0 := by
    by_contra h
    have := hgs _ h
    have h3 := abs_sub_abs_le_abs_sub u (-c)
    rw [sub_neg_eq_add, abs_neg, abs_of_nonneg hc] at h3
    linarith
  apply hu
  simp [cosTranslate, h1, h2]

/-! ### The cosine-translated polynomial test -/

/-- The cosine translate of the polynomial test. -/
def cosPolyTest (γ₀ c : ℝ) (w : ℝ → ℝ) (N : ℕ) (Q : ℂ[X]) : ℝ → ℂ :=
  cosTranslate γ₀ c (polyTest γ₀ w N Q)

theorem cosPolyTest_props {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (heven : ∀ u, w (-u) = w u)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) (γ₀ : ℝ) {c : ℝ} (hc : 0 ≤ c) {N : ℕ} {Q : ℂ[X]}
    (hN : Q.natDegree + 1 ≤ N) :
    ContDiff ℝ 2 (cosPolyTest γ₀ c w N Q) ∧
      (∀ u, cosPolyTest γ₀ c w N Q u ≠ 0 → |u| ≤ N + c) ∧
      ∀ z, paperFT (cosPolyTest γ₀ c w N Q) z =
        Complex.cos (c * (z - γ₀)) * polyProfile w N Q (z - γ₀) := by
  obtain ⟨hgc, hgs, hgf⟩ := polyTest_props hw heven hsupp γ₀ hN
  refine ⟨cosTranslate_contDiff γ₀ c hgc, cosTranslate_supp γ₀ hc hgs, fun z => ?_⟩
  rw [cosPolyTest, paperFT_cosTranslate γ₀ c hgc.continuous hgs, hgf]

/-- Real structure of the polynomial profile. -/
theorem conj_polyProfile_conj {w : ℝ → ℝ} (heven : ∀ u, w (-u) = w u) {N : ℕ} {Q : ℂ[X]}
    (hQ0 : Q ≠ 0) (hQ : ∀ n, conj (Q.coeff n) = Q.coeff n) (y : ℂ) :
    conj (polyProfile w N Q (conj y)) = polyProfile w N Q y := by
  have hlc : conj Q.leadingCoeff = Q.leadingCoeff := hQ _
  rw [polyProfile_eq w N hQ0, polyProfile_eq w N hQ0, map_mul, map_pow,
    conj_paperFT_conj_of_even heven, map_div₀, conj_eval_conj_of_real hQ, hlc]

/-- Real structure: the Weil summand of the cosine-translated test is `m (cos(c x) F(x))²`. -/
theorem Wsummand_cosPolyTest {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (heven : ∀ u, w (-u) = w u)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) (Z : ZeroConfig) (γ₀ : ℝ) {c : ℝ} (hc : 0 ≤ c) {N : ℕ}
    {Q : ℂ[X]} (hQ0 : Q ≠ 0) (hQ : ∀ n, conj (Q.coeff n) = Q.coeff n)
    (hN : Q.natDegree + 1 ≤ N) (ρ : ℂ) :
    Z.Wsummand (cosPolyTest γ₀ c w N Q) (cosPolyTest γ₀ c w N Q) ρ =
      (Z.mult ρ : ℂ) * (Complex.cos (c * (gammaOf ρ - γ₀)) *
        polyProfile w N Q (gammaOf ρ - γ₀)) ^ 2 := by
  obtain ⟨-, -, hf⟩ := cosPolyTest_props hw heven hsupp γ₀ hc hN
  rw [ZeroConfig.Wsummand, hf, hf]
  have hcj : conj (gammaOf ρ) - (γ₀ : ℂ) = conj (gammaOf ρ - γ₀) := by
    rw [map_sub, Complex.conj_ofReal]
  rw [hcj, map_mul, conj_polyProfile_conj heven hQ0 hQ]
  have hcos : conj (Complex.cos ((c : ℂ) * conj (gammaOf ρ - γ₀))) =
      Complex.cos (c * (gammaOf ρ - γ₀)) := by
    rw [← Complex.cos_conj, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  rw [hcos]
  ring

/-- A root of `Q` at `±i/2 - γ₀` makes the cosine-translated test vanish at the poles. -/
theorem cosPolyTest_polar_zero {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (heven : ∀ u, w (-u) = w u)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) (γ₀ : ℝ) {c : ℝ} (hc : 0 ≤ c) {N : ℕ} {Q : ℂ[X]}
    (hQ0 : Q ≠ 0) (hN : Q.natDegree + 1 ≤ N) {z : ℂ} (hz : Q.eval (z - γ₀) = 0) :
    paperFT (cosPolyTest γ₀ c w N Q) z = 0 := by
  obtain ⟨-, -, hf⟩ := cosPolyTest_props hw heven hsupp γ₀ hc hN
  rw [hf, polyProfile_eq w N hQ0, hz, zero_div, mul_zero, mul_zero]

end RHTower
