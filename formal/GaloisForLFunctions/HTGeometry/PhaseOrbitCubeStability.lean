import GaloisForLFunctions.HTGeometry.PhaseOrbitGradient
import GaloisForLFunctions.HTGeometry.TorusFejerDisplacement

/-!
# A phase cube moves the orbit, and its scores, by a controlled amount

Rotating each component of an orthogonal family by its own phase changes the orbit by at most the
sup-distance between the phase vectors: the differences of the phases enter only through
`|e^{iα} - e^{iβ}| = 2|sin((α-β)/2)| ≤ |α - β|`, and orthogonality turns the sum of the component
errors into a Pythagorean sum.

The overlap score with a unit target is `2`-Lipschitz in the state, because a difference of squared
moduli factors as a difference times a sum bounded by two.  Consequently a phase cube of half-width
`ρ` around a point where every target overlap is below `a₀` keeps every target overlap below
`a₀ + 2ρ`: a strict inequality at one point survives on a whole cube.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section CubeStability

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Two unimodular phases differ by at most the difference of their arguments. -/
theorem norm_expPhase_sub_le (a b : ℝ) :
    ‖Complex.exp (-(2 * π * Complex.I) * (a : ℂ)) - Complex.exp (-(2 * π * Complex.I) * (b : ℂ))‖
      ≤ 2 * π * |a - b| := by
  have hfac : Complex.exp (-(2 * π * Complex.I) * (a : ℂ))
      - Complex.exp (-(2 * π * Complex.I) * (b : ℂ))
      = Complex.exp (-(2 * π * Complex.I) * (b : ℂ))
        * (Complex.exp (((-(2 * π * (a - b)) : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hunit : ‖Complex.exp (-(2 * π * Complex.I) * (b : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hfac, norm_mul, hunit, one_mul, norm_exp_mul_I_sub_one]
  have hsin : |Real.sin ((-(2 * π * (a - b))) / 2)| ≤ |(-(2 * π * (a - b))) / 2| :=
    Real.abs_sin_le_abs
  have habs : |(-(2 * π * (a - b))) / 2| = π * |a - b| := by
    have h2 : (-(2 * π * (a - b))) / 2 = -(π * (a - b)) := by ring
    rw [h2, abs_neg, abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]
  rw [habs] at hsin
  linarith

/-- **`(27)`.**  The phase orbit of an orthogonal family of total weight at most one moves by at
most `2π` times the sup-distance between the phase vectors. -/
theorem norm_phaseOrbit_sub_le (u : d → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    (hweight : ∑ j : d, ‖u j‖ ^ (2 : ℕ) ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (x y : d → ℝ)
    (hxy : ∀ j, |x j - y j| ≤ ρ) :
    ‖phaseOrbit u x - phaseOrbit u y‖ ≤ 2 * π * ρ := by
  classical
  have hdiff : phaseOrbit u x - phaseOrbit u y
      = ∑ j : d, (Complex.exp (-(2 * π * Complex.I) * (x j))
          - Complex.exp (-(2 * π * Complex.I) * (y j))) • u j := by
    rw [phaseOrbit, phaseOrbit, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [sub_smul]
  have horth' : ∀ i j : d, i ≠ j →
      (inner ℂ ((Complex.exp (-(2 * π * Complex.I) * (x i))
          - Complex.exp (-(2 * π * Complex.I) * (y i))) • u i)
        ((Complex.exp (-(2 * π * Complex.I) * (x j))
          - Complex.exp (-(2 * π * Complex.I) * (y j))) • u j) : ℂ) = 0 := by
    intro i j hij
    rw [inner_smul_left, inner_smul_right, horth i j hij]
    ring
  have hpy : ‖phaseOrbit u x - phaseOrbit u y‖ ^ (2 : ℕ)
      = ∑ j : d, ‖(Complex.exp (-(2 * π * Complex.I) * (x j))
          - Complex.exp (-(2 * π * Complex.I) * (y j))) • u j‖ ^ (2 : ℕ) := by
    rw [hdiff]
    exact norm_sq_sum_of_orthogonal horth'
  have hterm : ∀ j : d, ‖(Complex.exp (-(2 * π * Complex.I) * (x j))
      - Complex.exp (-(2 * π * Complex.I) * (y j))) • u j‖ ^ (2 : ℕ)
      ≤ (2 * π * ρ) ^ (2 : ℕ) * ‖u j‖ ^ (2 : ℕ) := by
    intro j
    rw [norm_smul, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hb := norm_expPhase_sub_le (x j) (y j)
    have hle : ‖Complex.exp (-(2 * π * Complex.I) * (x j))
        - Complex.exp (-(2 * π * Complex.I) * (y j))‖ ≤ 2 * π * ρ := by
      refine hb.trans ?_
      have := hxy j
      nlinarith [Real.pi_pos]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hsq : ‖phaseOrbit u x - phaseOrbit u y‖ ^ (2 : ℕ) ≤ (2 * π * ρ) ^ (2 : ℕ) := by
    calc ‖phaseOrbit u x - phaseOrbit u y‖ ^ (2 : ℕ)
        = ∑ j : d, ‖(Complex.exp (-(2 * π * Complex.I) * (x j))
            - Complex.exp (-(2 * π * Complex.I) * (y j))) • u j‖ ^ (2 : ℕ) := hpy
      _ ≤ ∑ j : d, (2 * π * ρ) ^ (2 : ℕ) * ‖u j‖ ^ (2 : ℕ) := Finset.sum_le_sum fun j _ => hterm j
      _ = (2 * π * ρ) ^ (2 : ℕ) * ∑ j : d, ‖u j‖ ^ (2 : ℕ) := by rw [Finset.mul_sum]
      _ ≤ (2 * π * ρ) ^ (2 : ℕ) * 1 := by
          refine mul_le_mul_of_nonneg_left hweight (by positivity)
      _ = (2 * π * ρ) ^ (2 : ℕ) := by ring
  have hnn : (0 : ℝ) ≤ 2 * π * ρ := by positivity
  nlinarith [norm_nonneg (phaseOrbit u x - phaseOrbit u y), hsq, hnn]

/-- **`(27)` in the radian parametrization.**  Measuring the phases in radians removes the `2π`. -/
theorem norm_phaseOrbit_sub_le_radian (u : d → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    (hweight : ∑ j : d, ‖u j‖ ^ (2 : ℕ) ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (θ θ' : d → ℝ)
    (hθ : ∀ j, |θ j - θ' j| ≤ ρ) :
    ‖phaseOrbit u (fun j => -θ j / (2 * π)) - phaseOrbit u (fun j => -θ' j / (2 * π))‖ ≤ ρ := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hxy : ∀ j, |(-θ j / (2 * π)) - (-θ' j / (2 * π))| ≤ ρ / (2 * π) := by
    intro j
    have hrw : (-θ j / (2 * π)) - (-θ' j / (2 * π)) = -((θ j - θ' j) / (2 * π)) := by
      field_simp
      ring
    rw [hrw, abs_neg, abs_div, abs_of_pos hpi]
    gcongr
    exact hθ j
  have h := norm_phaseOrbit_sub_le u horth hweight (by positivity : (0 : ℝ) ≤ ρ / (2 * π))
    (fun j => -θ j / (2 * π)) (fun j => -θ' j / (2 * π)) hxy
  calc ‖phaseOrbit u (fun j => -θ j / (2 * π)) - phaseOrbit u (fun j => -θ' j / (2 * π))‖
      ≤ 2 * π * (ρ / (2 * π)) := h
    _ = ρ := by field_simp

/-- **`(28)`.**  The overlap score with a unit target is `2`-Lipschitz in the state. -/
theorem abs_score_sub_le (z v w : V) (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |‖(inner ℂ z v : ℂ)‖ ^ (2 : ℕ) - ‖(inner ℂ z w : ℂ)‖ ^ (2 : ℕ)| ≤ 2 * ‖v - w‖ := by
  have hsub : ‖(inner ℂ z v : ℂ)‖ - ‖(inner ℂ z w : ℂ)‖ ≤ ‖v - w‖ ∧
      ‖(inner ℂ z w : ℂ)‖ - ‖(inner ℂ z v : ℂ)‖ ≤ ‖v - w‖ := by
    have hdiff : (inner ℂ z v : ℂ) - (inner ℂ z w : ℂ) = (inner ℂ z (v - w) : ℂ) := by
      rw [inner_sub_right]
    have hcs : ‖(inner ℂ z v : ℂ) - (inner ℂ z w : ℂ)‖ ≤ ‖v - w‖ := by
      rw [hdiff]
      refine (norm_inner_le_norm (𝕜 := ℂ) z (v - w)).trans ?_
      nlinarith [hz, norm_nonneg (v - w), norm_nonneg z]
    have h := abs_norm_sub_norm_le (inner ℂ z v : ℂ) (inner ℂ z w : ℂ)
    rw [abs_le] at h
    exact ⟨le_trans h.2 hcs, by linarith [h.1, hcs]⟩
  have hbv : ‖(inner ℂ z v : ℂ)‖ ≤ 1 := by
    refine (norm_inner_le_norm (𝕜 := ℂ) z v).trans ?_
    nlinarith [hz, hv, norm_nonneg z, norm_nonneg v]
  have hbw : ‖(inner ℂ z w : ℂ)‖ ≤ 1 := by
    refine (norm_inner_le_norm (𝕜 := ℂ) z w).trans ?_
    nlinarith [hz, hw, norm_nonneg z, norm_nonneg w]
  have hnv : (0 : ℝ) ≤ ‖(inner ℂ z v : ℂ)‖ := norm_nonneg _
  have hnw : (0 : ℝ) ≤ ‖(inner ℂ z w : ℂ)‖ := norm_nonneg _
  have hnvw : (0 : ℝ) ≤ ‖v - w‖ := norm_nonneg _
  rw [abs_le]
  constructor <;> nlinarith [hsub.1, hsub.2]

/-- **`(29)`.**  A strict overlap bound at the cube centre survives on the whole cube, with the loss
`2ρ`. -/
theorem score_le_of_norm_sub_le {z v w : V} (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    {a ρ : ℝ} (hcentre : ‖(inner ℂ z w : ℂ)‖ ^ (2 : ℕ) ≤ a) (hnear : ‖v - w‖ ≤ ρ) :
    ‖(inner ℂ z v : ℂ)‖ ^ (2 : ℕ) ≤ a + 2 * ρ := by
  have h := abs_score_sub_le z v w hz hv hw
  have h2 := (abs_le.mp h).2
  have hmono : 2 * ‖v - w‖ ≤ 2 * ρ := by linarith
  linarith

end CubeStability

end

end GaloisForLFunctions.HTGeometry
