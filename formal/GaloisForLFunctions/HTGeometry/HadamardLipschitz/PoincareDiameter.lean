/-
# Appendix B: the Poincaré-disc computation behind the sharpness of `τ ≤ 2`

Along the diameter through a boundary point `P`, write `x = ρ P` with `ρ ∈ (-1,1)`.  Then

* the Busemann function is `b_P(ρP) = -2 artanh ρ` (`poincareBusemann_diameter`);
* the hyperbolic distance is `d(λ₁P, λ₂P) = 2|artanh λ₁ - artanh λ₂|`, which is the closed
  form `2 artanh((λ₁-λ₂)/(1-λ₁λ₂))` (`poincareDiameterDist_eq_closedForm`, via `artanh_sub`);
* the squared-ReLU layer `T_τ(x) = Φ_{τ ReLU(b_P(x))}(x)` sends `P_i = -r_i P` to
  `tanh((τ-1) artanh r_i) · P` (`poincare_flow_position`);
* consequently the distance ratio is exactly `|1-τ|` (`poincare_tightness`), so the layer is
  nonexpansive if and only if `0 ≤ τ ≤ 2`.

The abstract mechanism behind this — that the layer acts on a Busemann flow line as the affine
map `b ↦ (1-τ)b` — is `flowline_layer_dist_eq` in `BusemannSharpness`.
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.PoincareBusemann
import Mathlib.Analysis.SpecialFunctions.Artanh

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Real

/-- `artanh` as a difference of logarithms. -/
theorem artanh_eq_log_sub {x : ℝ} (h1 : -1 < x) (h2 : x < 1) :
    artanh x = (Real.log (1 + x) - Real.log (1 - x)) / 2 := by
  rw [Real.artanh_eq_half_log (Set.mem_Icc.mpr ⟨h1.le, h2.le⟩),
    Real.log_div (by linarith) (by linarith)]
  ring

theorem artanh_neg_eq {x : ℝ} (h1 : -1 < x) (h2 : x < 1) : artanh (-x) = -artanh x := by
  rw [artanh_eq_log_sub (by linarith) (by linarith), artanh_eq_log_sub h1 h2]
  have e1 : 1 + -x = 1 - x := by ring
  have e2 : 1 - -x = 1 + x := by ring
  rw [e1, e2]
  ring

/-- The subtraction formula for `artanh`, i.e. the hyperbolic-distance cocycle on a
diameter. -/
theorem artanh_sub {a b : ℝ} (ha1 : -1 < a) (ha2 : a < 1) (hb1 : -1 < b) (hb2 : b < 1) :
    artanh a - artanh b = artanh ((a - b) / (1 - a * b)) := by
  have hab : 0 < 1 - a * b := by nlinarith
  have ha' : (0:ℝ) < 1 - a ^ 2 := by nlinarith
  have hb' : (0:ℝ) < 1 - b ^ 2 := by nlinarith
  have hpos : 0 < (1 - a ^ 2) * (1 - b ^ 2) := mul_pos ha' hb'
  have habs : |a - b| < 1 - a * b := by
    have hsq : (a - b) ^ 2 < (1 - a * b) ^ 2 := by nlinarith
    nlinarith [abs_nonneg (a - b), sq_abs (a - b)]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have ht1 : -1 < (a - b) / (1 - a * b) := by
    rw [lt_div_iff₀ hab]; linarith
  have ht2 : (a - b) / (1 - a * b) < 1 := by
    rw [div_lt_one hab]; linarith
  rw [artanh_eq_log_sub ha1 ha2, artanh_eq_log_sub hb1 hb2, artanh_eq_log_sub ht1 ht2]
  have e1 : 1 + (a - b) / (1 - a * b) = (1 + a) * (1 - b) / (1 - a * b) := by
    field_simp; ring
  have e2 : 1 - (a - b) / (1 - a * b) = (1 - a) * (1 + b) / (1 - a * b) := by
    field_simp; ring
  rw [e1, e2,
    Real.log_div (ne_of_gt (by nlinarith : (0:ℝ) < (1 + a) * (1 - b))) (ne_of_gt hab),
    Real.log_div (ne_of_gt (by nlinarith : (0:ℝ) < (1 - a) * (1 + b))) (ne_of_gt hab),
    Real.log_mul (by linarith) (by linarith), Real.log_mul (by linarith) (by linarith)]
  ring

/-- The hyperbolic distance between two points of a diameter of the Poincaré ball. -/
noncomputable def poincareDiameterDist (l₁ l₂ : ℝ) : ℝ := 2 * |artanh l₁ - artanh l₂|

/-- The closed form of the diametral distance. -/
theorem poincareDiameterDist_eq_closedForm {l₁ l₂ : ℝ} (h₁ : -1 < l₁) (h₁' : l₁ < 1)
    (h₂ : -1 < l₂) (h₂' : l₂ < 1) :
    poincareDiameterDist l₁ l₂ = 2 * |artanh ((l₁ - l₂) / (1 - l₁ * l₂))| := by
  rw [poincareDiameterDist, artanh_sub h₁ h₁' h₂ h₂']

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Appendix B.**  On the diameter through the boundary point `P`, the Busemann function is
`-2 artanh ρ`. -/
theorem poincareBusemann_diameter (P : E) (hP : ‖P‖ = 1) {ρ : ℝ} (h1 : -1 < ρ) (h2 : ρ < 1) :
    poincareBusemann P (ρ • P) = -2 * artanh ρ := by
  have hnum : ‖P - ρ • P‖ ^ 2 = (1 - ρ) ^ 2 := by
    rw [show P - ρ • P = (1 - ρ) • P by module, norm_smul, Real.norm_eq_abs, hP, mul_one, sq_abs]
  have hden : ‖ρ • P‖ ^ 2 = ρ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, hP, mul_one, sq_abs]
  rw [poincareBusemann, hnum, hden]
  have hq : (1 - ρ) ^ 2 / (1 - ρ ^ 2) = (1 - ρ) / (1 + ρ) := by
    have h3 : 1 + ρ ≠ 0 := by linarith
    have h4 : 1 - ρ ≠ 0 := by linarith
    have h5 : 1 - ρ ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  rw [hq, Real.log_div (by linarith) (by linarith), artanh_eq_log_sub h1 h2]
  ring

/-- The Busemann value of the active point `P_i = -r_i P`. -/
theorem poincareBusemann_active (P : E) (hP : ‖P‖ = 1) {r : ℝ} (h1 : 0 < r) (h2 : r < 1) :
    poincareBusemann P ((-r) • P) = 2 * artanh r := by
  rw [poincareBusemann_diameter P hP (by linarith) (by linarith), artanh_neg_eq (by linarith) h2]
  ring

/-- **Appendix B.**  The position after a squared-ReLU Busemann step: the Busemann value is
scaled by `1 - τ`, hence the diametral coordinate becomes `tanh((τ-1) artanh r)`. -/
theorem poincare_flow_position {r τ ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1)
    (h : -2 * artanh ρ = 2 * (1 - τ) * artanh r) : ρ = tanh ((τ - 1) * artanh r) := by
  have hA : artanh ρ = (τ - 1) * artanh r := by linarith
  rw [← hA, Real.tanh_artanh (Set.mem_Ioo.mpr ⟨hρ1, hρ2⟩)]

/-- **Appendix B, the sharpness ratio.**  The squared-ReLU Busemann layer with step `τ`
multiplies diametral distances by exactly `|1 - τ|`; it is therefore nonexpansive exactly for
`0 ≤ τ ≤ 2`. -/
theorem poincare_tightness {r₁ r₂ τ : ℝ} (h₁ : 0 < r₁) (h₁' : r₁ < 1) (h₂ : 0 < r₂)
    (h₂' : r₂ < 1) :
    poincareDiameterDist (tanh ((τ - 1) * artanh r₁)) (tanh ((τ - 1) * artanh r₂))
      = |1 - τ| * poincareDiameterDist (-r₁) (-r₂) := by
  rw [poincareDiameterDist, poincareDiameterDist, Real.artanh_tanh, Real.artanh_tanh,
    artanh_neg_eq (by linarith) h₁', artanh_neg_eq (by linarith) h₂',
    show (τ - 1) * artanh r₁ - (τ - 1) * artanh r₂ = (τ - 1) * (artanh r₁ - artanh r₂) by ring,
    show -artanh r₁ - -artanh r₂ = -(artanh r₁ - artanh r₂) by ring, abs_mul, abs_neg,
    abs_sub_comm τ 1]
  ring

/-- The layer is expansive on the diameter exactly when `τ > 2` (or `τ < 0`). -/
theorem poincare_ratio_gt_one_iff {τ : ℝ} : 1 < |1 - τ| ↔ τ < 0 ∨ 2 < τ := by
  rw [lt_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
