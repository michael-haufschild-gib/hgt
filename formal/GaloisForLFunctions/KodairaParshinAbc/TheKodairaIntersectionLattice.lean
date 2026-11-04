import GaloisForLFunctions.ArithmeticLorentzianGeometry.LorentzianFormsAtDegreeTwo
import GaloisForLFunctions.HTGeometry.GrothendieckKTheoryIntersectionApplications

/-!
# The intersection lattice of a Kodaira fibration

Let `X → Y` be the Kodaira fibration built from an étale double cover `Y₁ → Y₀` of a genus-two
curve: a double cover of `Y₁ × Y` branched along the diagonal `Δ₁` and the graph `Δ₂` of the
covering involution, pulled back along a degree-`k` map `Y → Y₁`.  On the span of the two branch
sections `B₁, B₂` and the pullback `W` of a Weierstrass point of `Y₁` the intersection numbers are

  `B₁ · B₂ = 0,  B₁² = B₂² = -2k,  W · B₁ = W · B₂ = k,  W² = 0`,

and Riemann–Hurwitz gives `ω = B₁ + B₂ + 4W`.  This module records the resulting lattice and
the numbers it forces:

* `ω² = 12k`, `B = 2B₁ + 2B₂` has `B² = -16k`, `ω·B = 8k`, and `L = ω - B` has `L² = -20k`,
  so `L² = -(5/3) ω²`;
* the Grothendieck–Riemann–Roch degree `B²/2 - ω·B/2 + ω²/12 = -11k`, and with the torsion
  contribution `8k` the bound `deg φ_*L ≥ -3k = -ω²/4`;
* the Gram matrix is hyperbolic (Hodge index theorem on the span), as it must be on a surface.

The two estimates of `L²` — `-L² = (5/3) ω²` from the lattice and `-L² ≤ (3/2) ω² + 6δ` from
Minkowski — differ by the slope gap `5/3 - 3/2 = 1/6`, whence `ω² ≤ 36 δ`.

As a check of the Grothendieck–Riemann–Roch normalisation, on the corpus Chow ring of `P¹ × P¹`
(the trivial family of genus-zero curves over `P¹`) the same expression evaluates to
`b (a + 1) = rank · degree` of the pushforward of `O(a, b)`.
-/

noncomputable section

open Matrix

namespace GaloisForLFunctions.KodairaParshinAbc

open GaloisForLFunctions.ArithmeticLorentzianGeometry

/-! ## Genus numerology -/

/-- An étale double cover of a genus-`g₀` curve has genus `2g₀ - 1`; a double cover of that
branched at two points has genus `4g₀ - 2`.  For `g₀ = 2`: genera `3` and `6`. -/
theorem kodaira_genera (g₀ : ℕ) (hg : 1 ≤ g₀) :
    2 * (2 * g₀ - 1) - 2 = 2 * (2 * g₀ - 2) ∧
      2 * (4 * g₀ - 2) - 2 = 2 * (2 * (2 * g₀ - 1) - 2) + 2 := by
  constructor <;> omega

/-- On a genus-six fibre, Serre duality and Riemann–Roch give `h⁰(ω - B) = h⁰(B) + 1` for a
divisor `B` of degree `4`. -/
theorem kodaira_fibre_riemannRoch (h0B : ℤ) : h0B - 4 + 6 - 1 = h0B + 1 := by ring

/-! ## The Gram matrix -/

/-- The Gram matrix of `(B₁, B₂, W)` on a Kodaira fibration of degree `k` over `Y₁`. -/
def kodairaGram (k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-2 * k, 0, k; 0, -2 * k, k; k, k, 0]

theorem kodairaGram_isSymm (k : ℝ) : (kodairaGram k).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The relative dualizing sheaf `ω = B₁ + B₂ + 4W`. -/
def kodairaOmega : Fin 3 → ℝ := ![1, 1, 4]

/-- The branch class `B = 2B₁ + 2B₂`. -/
def kodairaBranch : Fin 3 → ℝ := ![2, 2, 0]

/-- The test bundle `L = ω - B`. -/
def kodairaTest : Fin 3 → ℝ := kodairaOmega - kodairaBranch

theorem bil_kodairaGram (k : ℝ) (x y : Fin 3 → ℝ) :
    bil (kodairaGram k) x y =
      -2 * k * x 0 * y 0 - 2 * k * x 1 * y 1 + k * (x 0 * y 2 + x 2 * y 0) +
        k * (x 1 * y 2 + x 2 * y 1) := by
  simp only [bil, kodairaGram, dotProduct, mulVec, Fin.sum_univ_three]
  simp
  ring

theorem kodaira_omega_sq (k : ℝ) : qf (kodairaGram k) kodairaOmega = 12 * k := by
  simp only [qf, bil_kodairaGram, kodairaOmega]
  simp
  ring

theorem kodaira_branch_sq (k : ℝ) : qf (kodairaGram k) kodairaBranch = -16 * k := by
  simp only [qf, bil_kodairaGram, kodairaBranch]
  simp
  ring

theorem kodaira_omega_branch (k : ℝ) :
    bil (kodairaGram k) kodairaOmega kodairaBranch = 8 * k := by
  simp only [bil_kodairaGram, kodairaOmega, kodairaBranch]
  simp
  ring

theorem kodaira_test_sq (k : ℝ) : qf (kodairaGram k) kodairaTest = -20 * k := by
  simp only [qf, bil_kodairaGram, kodairaTest, kodairaOmega, kodairaBranch]
  simp
  ring

theorem kodaira_omega_test (k : ℝ) :
    bil (kodairaGram k) kodairaOmega kodairaTest = 4 * k := by
  simp only [bil_kodairaGram, kodairaTest, kodairaOmega, kodairaBranch]
  simp
  ring

/-- **`L² = -(5/3) ω²`.** -/
theorem kodaira_test_sq_eq (k : ℝ) :
    qf (kodairaGram k) kodairaTest = -(5 / 3) * qf (kodairaGram k) kodairaOmega := by
  rw [kodaira_test_sq, kodaira_omega_sq]
  ring

/-- **Grothendieck–Riemann–Roch for `B`**: `B²/2 - ω·B/2 + ω²/12 = -11k`. -/
theorem kodaira_grr_branch (k : ℝ) :
    qf (kodairaGram k) kodairaBranch / 2 - bil (kodairaGram k) kodairaOmega kodairaBranch / 2 +
      qf (kodairaGram k) kodairaOmega / 12 = -11 * k := by
  rw [kodaira_branch_sq, kodaira_omega_branch, kodaira_omega_sq]
  ring

/-- **The pushforward bound** `-11k + 2 · #Ψ = -3k = -ω²/4`, with `#Ψ = 4k` exceptional fibres
each contributing torsion of length `2`. -/
theorem kodaira_pushforward_bound (k : ℝ) :
    (qf (kodairaGram k) kodairaBranch / 2 -
        bil (kodairaGram k) kodairaOmega kodairaBranch / 2 +
          qf (kodairaGram k) kodairaOmega / 12) + 2 * (4 * k) =
      -(qf (kodairaGram k) kodairaOmega / 4) := by
  rw [kodaira_grr_branch, kodaira_omega_sq]
  ring

/-! ## Hodge index on the Kodaira lattice -/

/-- **The Kodaira Gram matrix is hyperbolic** for `k ≥ 0`: it is negative semidefinite on
`{W-coordinate = 0}`, the span of `B₁, B₂`. -/
theorem kodairaGram_isHyperbolic {k : ℝ} (hk : 0 ≤ k) : IsHyperbolic (kodairaGram k) := by
  refine isHyperbolic_of_nonpos_on_ker (kodairaGram_isSymm k) (LinearMap.proj 2) ?_
  intro z hz
  simp only [LinearMap.coe_proj, Function.eval] at hz
  simp only [qf, bil_kodairaGram, hz]
  nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), mul_nonneg hk (sq_nonneg (z 0)),
    mul_nonneg hk (sq_nonneg (z 1))]

/-- The Hodge index inequality `ω² · D² ≤ (ω · D)²` for every class `D` of the span. -/
theorem kodaira_hodgeIndex {k : ℝ} (hk : 0 < k) (D : Fin 3 → ℝ) :
    qf (kodairaGram k) kodairaOmega * qf (kodairaGram k) D ≤
      bil (kodairaGram k) kodairaOmega D ^ 2 :=
  kodairaGram_isHyperbolic hk.le _ _ (by rw [kodaira_omega_sq]; positivity)

/-! ## The slope gap -/

/-- **The absorption step.**  If `-L² = (5/3) X` and `-L² ≤ (3/2) X + 6δ + C`, then
`X ≤ 36 δ + 6C`: the two slopes differ by `1/6`. -/
theorem kodaira_slope_gap {X Lsq δ C : ℝ} (hL : Lsq = -(5 / 3) * X)
    (hup : -Lsq ≤ 3 / 2 * X + 6 * δ + C) : X ≤ 36 * δ + 6 * C := by
  rw [hL] at hup
  linarith

/-- **The absorption step with losses.**  For every `η > 0` there is `ε > 0` such that
`(5/3 - ε) X ≤ (3/2 + ε) X + 6δ + C` with `δ, C ≥ 0` implies `X ≤ (36 + η) δ + 7C`. -/
theorem kodaira_slope_gap_eps {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ X δ C : ℝ, 0 ≤ δ → 0 ≤ C →
      (5 / 3 - ε) * X ≤ (3 / 2 + ε) * X + 6 * δ + C → X ≤ (36 + η) * δ + 7 * C := by
  refine ⟨min (1 / 168) (η / (12 * (36 + η))), by positivity, ?_⟩
  intro X δ C hδ hC h
  set ε := min (1 / 168) (η / (12 * (36 + η))) with hε
  have hε1 : ε ≤ 1 / 168 := min_le_left _ _
  have hε2 : ε ≤ η / (12 * (36 + η)) := min_le_right _ _
  have hε0 : 0 < ε := by positivity
  -- `(1/6 - 2ε) X ≤ 6δ + C` with `1/6 - 2ε > 0`.
  have hgap : (1 / 6 - 2 * ε) * X ≤ 6 * δ + C := by linarith
  have hpos : 0 < 1 / 6 - 2 * ε := by linarith
  by_cases hX : X ≤ 0
  · nlinarith
  push_neg at hX
  have hX' : X ≤ (6 * δ + C) / (1 / 6 - 2 * ε) := by
    rw [le_div_iff₀ hpos]; linarith
  have h6 : 6 / (1 / 6 - 2 * ε) ≤ 36 + η := by
    rw [div_le_iff₀ hpos]
    have : 12 * (36 + η) * ε ≤ η := by
      have h := mul_le_mul_of_nonneg_left hε2 (by positivity : (0 : ℝ) ≤ 12 * (36 + η))
      rwa [mul_div_cancel₀ _ (by positivity)] at h
    nlinarith
  have h7 : 1 / (1 / 6 - 2 * ε) ≤ 7 := by
    rw [div_le_iff₀ hpos]; linarith
  calc X ≤ (6 * δ + C) / (1 / 6 - 2 * ε) := hX'
    _ = 6 / (1 / 6 - 2 * ε) * δ + 1 / (1 / 6 - 2 * ε) * C := by field_simp
    _ ≤ (36 + η) * δ + 7 * C := by
        gcongr

/-! ## The Grothendieck–Riemann–Roch normalisation on `P¹ × P¹` -/

open GaloisForLFunctions.HTGeometry

/-- The relative canonical class `(-2, 0)` of the projection `P¹ × P¹ → P¹` onto the second
factor. -/
def p1xp1RelativeCanonical : ChowProd 1 1 := p1xp1DivisorClass (-2) 0

/-- `ω² = 0` for the trivial family of genus-zero curves (Noether's formula with no singular
fibres). -/
theorem p1xp1_relativeCanonical_sq :
    p1xp1RelativeCanonical * p1xp1RelativeCanonical = 0 := by
  rw [p1xp1RelativeCanonical, p1xp1_divisor_intersection]
  simp

/-- **The GRR expression `B² - ω·B = 2 b (a+1)` on `P¹ × P¹`.**  Together with `ω² = 0` this
is `2 (B²/2 - ω·B/2 + ω²/12) = 2 · rank · degree` of `R p₂₊ O(a, b) = H⁰(P¹, O(a)) ⊗ O(b)`. -/
theorem p1xp1_grr (a b : ℤ) :
    p1xp1DivisorClass a b * p1xp1DivisorClass a b -
        p1xp1RelativeCanonical * p1xp1DivisorClass a b =
      ((2 * (b * (a + 1)) : ℤ) : ChowProd 1 1) * chowTop 1 1 := by
  rw [p1xp1RelativeCanonical, p1xp1_divisor_intersection, p1xp1_divisor_intersection, ← sub_mul]
  congr 1
  push_cast
  ring

end GaloisForLFunctions.KodairaParshinAbc
