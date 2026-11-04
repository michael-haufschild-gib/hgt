import GaloisForLFunctions.KodairaParshinAbc.TheLegendreInvariantOfTheModularLambdaFunction
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.NumberTheory.Height.NumberField

/-!
# The height of the Legendre invariant

The map `f(x₀, x₁, x₂) = (256 (x₀² + x₁x₂)³ : (x₀x₁x₂)²)` is given by two forms of degree six, and
`f(λ, 1 - λ, 1) = (256 (λ² - λ + 1)³ : (λ(1-λ))²)` is the Legendre invariant `J(λ)`.  Over any field
with an admissible family of absolute values (in particular every number field) the height bound
for homogeneous polynomial maps gives

  `h(f(x)) ≤ C + 6 h(x)`  and hence  `h(J(λ)) ≤ C + 6 h(λ)`,

the logarithmic form of `H(j, 1) ≪ H(λ, 1 - λ, 1)⁶`.

Over `ℚ` the bound is two-sided on the `abc` line: for coprime `a, b` with `ab(a+b) ≠ 0` and
`H = max(|a|, |b|, |a+b|)`,

  `6 log H - log 8 ≤ h(J(a/(a+b))) ≤ 6 log H + log 864`,

since `J(a/(a+b)) = 256 (a² + ab + b²)³ / (ab(a+b))²` has numerator and denominator sharing at
most the factor `256`.
-/

noncomputable section

open MvPolynomial Height Real

namespace GaloisForLFunctions.KodairaParshinAbc

/-! ## The degree-six map -/

section General

variable {K : Type*} [Field K]

/-- The two sextic forms `256 (x₀² + x₁x₂)³` and `(x₀x₁x₂)²`. -/
def legendreSextics : Fin 2 → MvPolynomial (Fin 3) K :=
  ![C 256 * (X 0 ^ 2 + X 1 * X 2) ^ 3, (X 0 * X 1 * X 2) ^ 2]

theorem legendreSextics_isHomogeneous (i : Fin 2) :
    (legendreSextics (K := K) i).IsHomogeneous 6 := by
  have h0 : (X 0 ^ 2 : MvPolynomial (Fin 3) K).IsHomogeneous 2 := by
    simpa using (isHomogeneous_X K (0 : Fin 3)).pow 2
  have h12 : (X 1 * X 2 : MvPolynomial (Fin 3) K).IsHomogeneous 2 :=
    (isHomogeneous_X K (1 : Fin 3)).mul (isHomogeneous_X K (2 : Fin 3))
  have h012 : (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) K).IsHomogeneous 3 :=
    ((isHomogeneous_X K (0 : Fin 3)).mul (isHomogeneous_X K (1 : Fin 3))).mul
      (isHomogeneous_X K (2 : Fin 3))
  fin_cases i
  · simpa [legendreSextics] using ((h0.add h12).pow 3).C_mul 256
  · simpa [legendreSextics] using h012.pow 2

/-- The linear forms `(x₀, x₁) ↦ (x₀, x₁ - x₀, x₁)` embedding `P¹` as the line `y₀ + y₁ = y₂`. -/
def abcLine : Fin 3 → MvPolynomial (Fin 2) K := ![X 0, X 1 - X 0, X 1]

theorem abcLine_isHomogeneous (i : Fin 3) : (abcLine (K := K) i).IsHomogeneous 1 := by
  fin_cases i
  · exact isHomogeneous_X K 0
  · exact (isHomogeneous_X K 1).sub (isHomogeneous_X K 0)
  · exact isHomogeneous_X K 1

theorem eval_legendreSextics (x : Fin 3 → K) :
    (fun j => (legendreSextics j).eval x) =
      ![256 * (x 0 ^ 2 + x 1 * x 2) ^ 3, (x 0 * x 1 * x 2) ^ 2] := by
  funext j
  fin_cases j <;> simp [legendreSextics]

theorem eval_abcLine (u v : K) : (fun j => (abcLine j).eval ![u, v]) = ![u, v - u, v] := by
  funext j
  fin_cases j <;> simp [abcLine]

/-- The Legendre invariant is the quotient of the two sextics at `(λ, 1 - λ, 1)`. -/
theorem legendreInvariant_eq_div (w : K) :
    legendreInvariant w = (256 * (w ^ 2 + (1 - w) * 1) ^ 3) / ((w * (1 - w) * 1) ^ 2) := by
  unfold legendreInvariant
  congr 1 <;> ring

variable [AdmissibleAbsValues K]

/-- **The degree-six height bound** `h(f(x)) ≤ C + 6 h(x)`. -/
theorem exists_logHeight_legendreSextics_le :
    ∃ C, ∀ x : Fin 3 → K,
      logHeight ![256 * (x 0 ^ 2 + x 1 * x 2) ^ 3, (x 0 * x 1 * x 2) ^ 2] ≤ C + 6 * logHeight x := by
  obtain ⟨C, hC⟩ := logHeight_eval_le' (p := legendreSextics (K := K)) legendreSextics_isHomogeneous
  refine ⟨C, fun x => ?_⟩
  have := hC x
  rw [eval_legendreSextics] at this
  exact_mod_cast this

/-- **`h(J(λ)) ≤ C + 6 h(λ)`**: the Legendre invariant has at most six times the height of its
parameter, up to a constant. -/
theorem exists_logHeight₁_legendreInvariant_le :
    ∃ C, ∀ w : K, logHeight₁ (legendreInvariant w) ≤ C + 6 * logHeight₁ w := by
  obtain ⟨C₁, hC₁⟩ := exists_logHeight_legendreSextics_le (K := K)
  obtain ⟨C₂, hC₂⟩ := logHeight_eval_le' (p := abcLine (K := K)) abcLine_isHomogeneous
  refine ⟨C₁ + 6 * C₂, fun w => ?_⟩
  have h1 : logHeight ![256 * (w ^ 2 + (1 - w) * 1) ^ 3, (w * (1 - w) * 1) ^ 2] ≤
      C₁ + 6 * logHeight ![w, 1 - w, 1] := hC₁ ![w, 1 - w, 1]
  have h2 := hC₂ ![w, 1]
  rw [eval_abcLine] at h2
  simp only [Nat.cast_one, one_mul] at h2
  rw [legendreInvariant_eq_div, logHeight₁_div_eq_logHeight, logHeight₁_eq_logHeight]
  linarith

end General

/-! ## The two-sided bound over `ℚ` -/

/-- Over `ℚ`, the Legendre invariant of the triple `(a, b, a + b)` is the reduced fraction of the
integers `256 (a² + ab + b²)³` and `(ab(a+b))²`. -/
theorem legendreInvariant_abc_rat {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : a + b ≠ 0) :
    legendreInvariant ((a : ℚ) / (a + b)) =
      (((256 * (a ^ 2 + a * b + b ^ 2) ^ 3 : ℤ) : ℚ) / (((a * b * (a + b)) ^ 2 : ℤ) : ℚ)) := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hc' : (a : ℚ) + b ≠ 0 := by exact_mod_cast hc
  have hl1 : (a : ℚ) / (a + b) - 1 = -b / (a + b) := by field_simp; ring
  unfold legendreInvariant
  rw [hl1]
  push_cast
  field_simp
  ring

/-- **The height of the Frey–Legendre invariant is `6 log H + O(1)` over `ℚ`.** -/
theorem logHeight₁_legendreInvariant_abc {a b : ℤ} (h : IsCoprime a b) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : a + b ≠ 0) :
    6 * Real.log (tripleHeight a b) - Real.log 8 ≤
        logHeight₁ (legendreInvariant ((a : ℚ) / (a + b))) ∧
      logHeight₁ (legendreInvariant ((a : ℚ) / (a + b))) ≤
        6 * Real.log (tripleHeight a b) + Real.log 864 := by
  obtain ⟨hlo, hhi⟩ := ratHeight_abcInvariant_bounds h ha hb hc
  rw [legendreInvariant_abc_rat ha hb hc, Rat.logHeight₁_eq_log_max]
  set q : ℚ := (((256 * (a ^ 2 + a * b + b ^ 2) ^ 3 : ℤ) : ℚ) / (((a * b * (a + b)) ^ 2 : ℤ) : ℚ))
  have hR : (ratHeight q : ℝ) = ((max q.num.natAbs q.den : ℕ) : ℝ) := rfl
  have hH : (0 : ℝ) < tripleHeight a b := by
    have := (abs_le_tripleHeight a b).1
    exact_mod_cast lt_of_lt_of_le (abs_pos.mpr ha) this
  have hlo' : (tripleHeight a b : ℝ) ^ 6 ≤ 8 * (ratHeight q : ℝ) := by exact_mod_cast hlo
  have hhi' : (ratHeight q : ℝ) ≤ 864 * (tripleHeight a b : ℝ) ^ 6 := by exact_mod_cast hhi
  have hpos : (0 : ℝ) < ratHeight q := by
    have : (0 : ℝ) < (tripleHeight a b : ℝ) ^ 6 := by positivity
    linarith
  rw [← hR]
  constructor
  · have := Real.log_le_log (by positivity) hlo'
    rw [Real.log_pow, Real.log_mul (by norm_num) hpos.ne'] at this
    push_cast at this
    linarith
  · have := Real.log_le_log hpos hhi'
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith

end GaloisForLFunctions.KodairaParshinAbc
