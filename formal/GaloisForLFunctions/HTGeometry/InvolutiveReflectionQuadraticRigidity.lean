import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard
import GaloisForLFunctions.HTGeometry.DirectionalMeromorphicField
import GaloisForLFunctions.HTGeometry.FirstOrderMvPoly

/-!
# Involutive-reflection quadratic rigidity

An affine involution `σ(z) = b - z` and a reflection law `W ∘ σ = C - W` on a finite-order entire
`W` force every quadratic entire inner factor `W = a + g²` to be first-order differentially
algebraic.

The mechanism is a difference of squares.  The reflection law says
`g(σ z)² + g(z)² = C - 2a =: D`, and over `ℂ` this factors as `A·B = D` with

`A z = g(σ z) - i g z`,  `B z = g(σ z) + i g z`.

If `D = 0` the identity theorem forces one factor to vanish identically, and applying the involution
twice then forces `g ≡ 0`.  If `D ≠ 0` both factors are zero-free entire functions of finite order,
so Hadamard's zero-free factorization (`exists_polynomial_exp_of_ne_zero`) writes them as
`c exp S` and `d exp (-S)` for a single polynomial `S`.  Eliminating `exp (±S)` between `g` and `g'`
leaves the order-one equation

`S'(z)² g(z)² - g'(z)² = D · S'(z)²`.

## Main results

* `reflectionFactor_mul` — the difference-of-squares factorization;
* `involutive_reflection_hyperexponential` — the `c exp S` / `d exp (-S)` normal form;
* `involutive_reflection_firstOrder_relation` — the explicit order-one equation;
* `involutive_reflection_differentiallyAlgebraicOfOrder_one` — the card's conclusion;
* `sinPrimitive_quadratic_inner_firstOrder` — the nonautonomous `z sin z` witness.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex GaloisForLFunctions

/-! ### The difference-of-squares factorization -/

/-- The `-i` reflection factor `g ∘ σ - i g`. -/
def reflectionFactorMinus (b : ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ := g (b - z) - Complex.I * g z

/-- The `+i` reflection factor `g ∘ σ + i g`. -/
def reflectionFactorPlus (b : ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ := g (b - z) + Complex.I * g z

/-- **Difference of squares.**  The two reflection factors multiply to the reflected square sum. -/
theorem reflectionFactor_mul (b : ℂ) (g : ℂ → ℂ) (z : ℂ) :
    reflectionFactorMinus b g z * reflectionFactorPlus b g z = g (b - z) ^ (2 : ℕ) + g z ^ (2 : ℕ) := by
  simp only [reflectionFactorMinus, reflectionFactorPlus]
  linear_combination (-(g z) ^ (2 : ℕ)) * Complex.I_sq

theorem differentiable_reflectionFactorMinus {g : ℂ → ℂ} (hg : Differentiable ℂ g) (b : ℂ) :
    Differentiable ℂ (reflectionFactorMinus b g) :=
  (hg.comp (differentiable_id.const_sub b)).sub (hg.const_mul Complex.I)

theorem differentiable_reflectionFactorPlus {g : ℂ → ℂ} (hg : Differentiable ℂ g) (b : ℂ) :
    Differentiable ℂ (reflectionFactorPlus b g) :=
  (hg.comp (differentiable_id.const_sub b)).add (hg.const_mul Complex.I)

/-! ### The reflection law -/

/-- The reflection law transported to the inner factor. -/
theorem reflection_square_sum {W g : ℂ → ℂ} {b C a : ℂ}
    (hrefl : ∀ z, W (b - z) = C - W z) (hquad : ∀ z, W z = a + g z ^ (2 : ℕ)) (z : ℂ) :
    g (b - z) ^ (2 : ℕ) + g z ^ (2 : ℕ) = C - 2 * a := by
  have h1 := hrefl z
  rw [hquad (b - z), hquad z] at h1
  linear_combination h1

/-- The finite-order envelope descends from the outer function to the inner factor. -/
theorem finiteOrderEnvelope_inner {W g : ℂ → ℂ} {a : ℂ}
    (henv : FiniteOrderEnvelope W) (hquad : ∀ z, W z = a + g z ^ (2 : ℕ)) :
    FiniteOrderEnvelope g := by
  refine FiniteOrderEnvelope.of_sq ?_
  obtain ⟨Cc, dd, hCc, hb⟩ := henv.sub (FiniteOrderEnvelope.const a)
  refine ⟨Cc, dd, hCc, fun z => ?_⟩
  have hz : g z ^ (2 : ℕ) = W z - a := by rw [hquad z]; ring
  simpa [hz] using hb z

/-- The reflected copy of a finite-order function is finite order. -/
theorem finiteOrderEnvelope_reflect {g : ℂ → ℂ} (henv : FiniteOrderEnvelope g) (b : ℂ) :
    FiniteOrderEnvelope (fun z => g (b - z)) := by
  obtain ⟨Cc, dd, hCc, hb⟩ := henv.compAffine (-1) b
  refine ⟨Cc, dd, hCc, fun z => ?_⟩
  have hz : ‖g ((-1 : ℂ) * z + b)‖ ≤ Real.exp (Cc * (1 + ‖z‖) ^ dd) := hb z
  rwa [show (-1 : ℂ) * z + b = b - z by ring] at hz

/-! ### The degenerate reflection constant -/

/-- **A vanishing reflection constant kills the inner factor.**  If `C = 2a` then one of the two
reflection factors vanishes identically, and applying the involution twice forces `g ≡ 0`. -/
theorem inner_eq_zero_of_reflection_const_eq {W g : ℂ → ℂ} {b C a : ℂ}
    (hg : Differentiable ℂ g)
    (hrefl : ∀ z, W (b - z) = C - W z) (hquad : ∀ z, W z = a + g z ^ (2 : ℕ))
    (hD : C - 2 * a = 0) : ∀ z, g z = 0 := by
  have hprod : ∀ z, reflectionFactorMinus b g z * reflectionFactorPlus b g z = 0 := by
    intro z
    rw [reflectionFactor_mul, reflection_square_sum hrefl hquad z, hD]
  have hAan : AnalyticOnNhd ℂ (reflectionFactorMinus b g) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_reflectionFactorMinus hg b)
  have hBan : AnalyticOnNhd ℂ (reflectionFactorPlus b g) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_reflectionFactorPlus hg b)
  have hcase := analyticOnNhd_domain' hAan hBan isPreconnected_univ isOpen_univ
    (fun z _ => hprod z)
  -- in either case the involution applied twice forces `g = -g`
  have hinv : ∀ (e : ℂ), e * e = -1 → (∀ z, g (b - z) = e * g z) → ∀ z, g z = 0 := by
    intro e he h z
    have h1 := h z
    have h2 := h (b - z)
    rw [show b - (b - z) = z by ring] at h2
    have : (2 : ℂ) * g z = 0 := by
      rw [h1] at h2
      linear_combination h2 + g z * he
    have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
    exact (mul_eq_zero.mp this).resolve_left h2ne
  rcases hcase with h | h
  · refine hinv Complex.I (by linear_combination Complex.I_sq) (fun z => ?_)
    have := h (Set.mem_univ z)
    simp only [reflectionFactorMinus, Pi.zero_apply] at this
    linear_combination this
  · refine hinv (-Complex.I) (by linear_combination Complex.I_sq) (fun z => ?_)
    have := h (Set.mem_univ z)
    simp only [reflectionFactorPlus, Pi.zero_apply] at this
    linear_combination this

/-! ### The hyperexponential normal form -/

/-- **Involutive-reflection quadratic rigidity, normal form.**  Under the reflection law every
quadratic inner factor of a finite-order entire function splits into a single hyperexponential
generator and its inverse. -/
theorem involutive_reflection_hyperexponential {W g : ℂ → ℂ} {b C a : ℂ}
    (hg : Differentiable ℂ g) (henv : FiniteOrderEnvelope W)
    (hrefl : ∀ z, W (b - z) = C - W z) (hquad : ∀ z, W z = a + g z ^ (2 : ℕ)) :
    ∃ (S : Polynomial ℂ) (c d : ℂ), c * d = C - 2 * a ∧
      (∀ z, g (b - z) - Complex.I * g z = c * Complex.exp (S.eval z)) ∧
      (∀ z, g (b - z) + Complex.I * g z = d * Complex.exp (-(S.eval z))) := by
  by_cases hD : C - 2 * a = 0
  · -- degenerate constant: the inner factor vanishes and both sides are zero
    have hzero := inner_eq_zero_of_reflection_const_eq hg hrefl hquad hD
    refine ⟨0, 0, 0, by rw [hD]; ring, fun z => ?_, fun z => ?_⟩ <;>
      rw [hzero, hzero] <;> ring
  · -- nondegenerate constant: both factors are zero-free of finite order
    have hprod : ∀ z, reflectionFactorMinus b g z * reflectionFactorPlus b g z = C - 2 * a := by
      intro z
      rw [reflectionFactor_mul, reflection_square_sum hrefl hquad z]
    have hAne : ∀ z, reflectionFactorMinus b g z ≠ 0 := by
      intro z hz
      exact hD (by rw [← hprod z, hz, zero_mul])
    have hgenv : FiniteOrderEnvelope g := finiteOrderEnvelope_inner henv hquad
    have hAenv : FiniteOrderEnvelope (reflectionFactorMinus b g) := by
      obtain ⟨Cc, dd, hCc, hb⟩ :=
        (finiteOrderEnvelope_reflect hgenv b).sub
          ((FiniteOrderEnvelope.const Complex.I).mul hgenv)
      exact ⟨Cc, dd, hCc, fun z => hb z⟩
    obtain ⟨S, hS⟩ := exists_polynomial_exp_of_ne_zero
      (differentiable_reflectionFactorMinus hg b) hAne hAenv
    refine ⟨S, 1, C - 2 * a, by ring, fun z => ?_, fun z => ?_⟩
    · have := hS z
      simp only [reflectionFactorMinus] at this
      rw [this]; ring
    · have hAz := hS z
      have hpz := hprod z
      simp only [reflectionFactorMinus, reflectionFactorPlus] at hAz hpz
      have hne : Complex.exp (S.eval z) ≠ 0 := Complex.exp_ne_zero _
      rw [hAz] at hpz
      rw [Complex.exp_neg]
      field_simp
      linear_combination hpz

/-! ### The order-one differential equation -/

/-- **The explicit order-one equation.**  With `S` the hyperexponential exponent the inner factor
satisfies `S'² g² - g'² = (C - 2a) S'²` everywhere. -/
theorem involutive_reflection_firstOrder_relation {W g : ℂ → ℂ} {b C a : ℂ}
    (hg : Differentiable ℂ g) (henv : FiniteOrderEnvelope W)
    (hrefl : ∀ z, W (b - z) = C - W z) (hquad : ∀ z, W z = a + g z ^ (2 : ℕ)) :
    ∃ S : Polynomial ℂ, ∀ z : ℂ,
      ((Polynomial.derivative S).eval z) ^ (2 : ℕ) * g z ^ (2 : ℕ) - (deriv g z) ^ (2 : ℕ)
        = (C - 2 * a) * ((Polynomial.derivative S).eval z) ^ (2 : ℕ) := by
  obtain ⟨S, c, d, hcd, hA, hB⟩ :=
    involutive_reflection_hyperexponential hg henv hrefl hquad
  refine ⟨S, fun z => ?_⟩
  -- the doubled inner factor and its derivative in terms of the generator
  have hgfun : ∀ w : ℂ, 2 * Complex.I * g w
      = d * Complex.exp (-(S.eval w)) - c * Complex.exp (S.eval w) := by
    intro w
    have h1 := hA w
    have h2 := hB w
    linear_combination h2 - h1
  set P : ℂ := (Polynomial.derivative S).eval z with hP
  have hSd : HasDerivAt (fun x => S.eval x) P z := by rw [hP]; exact S.hasDerivAt z
  have hExpNeg : HasDerivAt (fun x => Complex.exp (-(S.eval x)))
      (Complex.exp (-(S.eval z)) * (-P)) z := (hSd.neg).cexp
  have hExpPos : HasDerivAt (fun x => Complex.exp (S.eval x))
      (Complex.exp (S.eval z) * P) z := hSd.cexp
  have hRHS : HasDerivAt (fun x => d * Complex.exp (-(S.eval x)) - c * Complex.exp (S.eval x))
      (d * (Complex.exp (-(S.eval z)) * (-P)) - c * (Complex.exp (S.eval z) * P)) z :=
    (hExpNeg.const_mul d).sub (hExpPos.const_mul c)
  have hLHS : HasDerivAt (fun x => 2 * Complex.I * g x) (2 * Complex.I * deriv g z) z :=
    ((hg z).hasDerivAt).const_mul _
  rw [funext hgfun] at hLHS
  have hderiv : 2 * Complex.I * deriv g z
      = d * (Complex.exp (-(S.eval z)) * (-P)) - c * (Complex.exp (S.eval z) * P) :=
    hLHS.unique hRHS
  -- eliminate the generator
  have hEinv : Complex.exp (-(S.eval z)) * Complex.exp (S.eval z) = 1 := by
    rw [← Complex.exp_add]; simp
  have hkey : P ^ (2 : ℕ) * (2 * Complex.I * g z) ^ (2 : ℕ) - (2 * Complex.I * deriv g z) ^ (2 : ℕ)
      = -4 * (C - 2 * a) * P ^ (2 : ℕ) := by
    rw [hgfun z, hderiv, ← hcd]
    linear_combination (-4 * c * d * P ^ (2 : ℕ)) * hEinv
  linear_combination (-1 / 4 : ℂ) * hkey
    + (P ^ (2 : ℕ) * g z ^ (2 : ℕ) - (deriv g z) ^ (2 : ℕ)) * Complex.I_sq

/-! ### The card statement -/

/-- The three-term differential polynomial of the reflection equation. -/
def reflectionRelationCoeff (S : Polynomial ℂ) (D : ℂ) : ℕ × ℕ → Polynomial ℂ := fun p =>
  if p = (2, 0) then (Polynomial.derivative S) ^ (2 : ℕ)
  else if p = (0, 2) then -1
  else -(Polynomial.C D) * (Polynomial.derivative S) ^ (2 : ℕ)

/-- The support of the reflection equation. -/
def reflectionRelationSupport : Finset (ℕ × ℕ) := {(2, 0), (0, 2), (0, 0)}

theorem reflectionRelation_sum (S : Polynomial ℂ) (D : ℂ) (z u v : ℂ) :
    ∑ p ∈ reflectionRelationSupport, (reflectionRelationCoeff S D p).eval z * u ^ p.1 * v ^ p.2
      = ((Polynomial.derivative S).eval z) ^ (2 : ℕ) * u ^ (2 : ℕ) - v ^ (2 : ℕ)
        - D * ((Polynomial.derivative S).eval z) ^ (2 : ℕ) := by
  rw [reflectionRelationSupport]
  norm_num [reflectionRelationCoeff]
  ring

/-- **Involutive-reflection quadratic rigidity.**  An affine reflection constraint on a
finite-order entire function forces every quadratic entire inner factor to be differentially
algebraic of order at most one. -/
theorem involutive_reflection_differentiallyAlgebraicOfOrder_one {W g : ℂ → ℂ} {b C a : ℂ}
    (hg : Differentiable ℂ g) (henv : FiniteOrderEnvelope W)
    (hrefl : ∀ z, W (b - z) = C - W z) (hquad : ∀ z, W z = a + g z ^ (2 : ℕ)) :
    DifferentiallyAlgebraicOfOrder g 1 := by
  obtain ⟨S, hrel⟩ := involutive_reflection_firstOrder_relation hg henv hrefl hquad
  -- the differential polynomial is nonzero: specialize `u = 0` and choose `v`
  have hnonzero : firstOrderMvPoly reflectionRelationSupport
      (reflectionRelationCoeff S (C - 2 * a)) ≠ 0 := by
    obtain ⟨v, hv⟩ : ∃ v : ℂ,
        -v ^ (2 : ℕ) - (C - 2 * a) * ((Polynomial.derivative S).eval 0) ^ (2 : ℕ) ≠ 0 := by
      by_cases hKz : (C - 2 * a) * ((Polynomial.derivative S).eval 0) ^ (2 : ℕ) = 0
      · refine ⟨1, ?_⟩
        rw [hKz]; norm_num
      · refine ⟨0, fun hc => hKz ?_⟩
        linear_combination -hc
    intro h0
    apply hv
    have hev := eval_firstOrderMvPoly reflectionRelationSupport
      (reflectionRelationCoeff S (C - 2 * a)) 0 0 v
    rw [h0, map_zero, reflectionRelation_sum] at hev
    linear_combination -hev
  refine differentiallyAlgebraicOfOrder_one_of_relation hnonzero (fun u => ?_)
  rw [reflectionRelation_sum]
  linear_combination hrel u

/-! ### The nonautonomous `z sin z` example -/

theorem norm_sin_le_exp_norm (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm _) ?_)
    simp
  have h2 : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm _) ?_)
    simp
  have hnum : ‖(Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I‖
      ≤ 2 * Real.exp ‖z‖ := by
    rw [norm_mul, Complex.norm_I, mul_one]
    exact le_trans (norm_sub_le _ _) (by linarith)
  rw [norm_div]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < ‖(2 : ℂ)‖)]
  have : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [this]
  linarith

theorem norm_cos_le_exp_norm (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm _) ?_)
    simp
  have h2 : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm _) ?_)
    simp
  rw [norm_div, div_le_iff₀ (by norm_num : (0:ℝ) < ‖(2 : ℂ)‖)]
  have h3 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h3]
  have := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  linarith

/-- The primitive `sin z - z cos z` of the first-order entire DA function `z ↦ z sin z`. -/
def sinPrimitive (z : ℂ) : ℂ := Complex.sin z - z * Complex.cos z

/-- `sinPrimitive` is a primitive of `z ↦ z sin z`. -/
theorem hasDerivAt_sinPrimitive (z : ℂ) : HasDerivAt sinPrimitive (z * Complex.sin z) z := by
  have h1 : HasDerivAt Complex.sin (Complex.cos z) z := Complex.hasDerivAt_sin z
  have h2 : HasDerivAt (fun w : ℂ => w * Complex.cos w)
      (1 * Complex.cos z + z * (-Complex.sin z)) z :=
    (hasDerivAt_id z).mul (Complex.hasDerivAt_cos z)
  have h3 := h1.sub h2
  have heq : Complex.cos z - (1 * Complex.cos z + z * (-Complex.sin z)) = z * Complex.sin z := by
    ring
  rw [heq] at h3
  exact h3

theorem differentiable_sinPrimitive : Differentiable ℂ sinPrimitive :=
  fun z => (hasDerivAt_sinPrimitive z).differentiableAt

/-- The primitive is odd: it is the reflection law at `b = 0`, `C = 0`. -/
theorem sinPrimitive_reflection (z : ℂ) : sinPrimitive (0 - z) = 0 - sinPrimitive z := by
  simp only [sinPrimitive, zero_sub, Complex.sin_neg, Complex.cos_neg]
  ring

theorem finiteOrderEnvelope_sinPrimitive : FiniteOrderEnvelope sinPrimitive := by
  refine ⟨2, 1, by norm_num, fun z => ?_⟩
  have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hexp : (0 : ℝ) < Real.exp ‖z‖ := Real.exp_pos _
  have hlin : 1 + ‖z‖ ≤ Real.exp ‖z‖ := Real.add_one_le_exp ‖z‖ |>.trans_eq' (by ring)
  calc ‖sinPrimitive z‖ ≤ ‖Complex.sin z‖ + ‖z * Complex.cos z‖ := norm_sub_le _ _
    _ ≤ Real.exp ‖z‖ + ‖z‖ * Real.exp ‖z‖ := by
        refine add_le_add (norm_sin_le_exp_norm z) ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_cos_le_exp_norm z) hz
    _ = (1 + ‖z‖) * Real.exp ‖z‖ := by ring
    _ ≤ Real.exp ‖z‖ * Real.exp ‖z‖ := mul_le_mul_of_nonneg_right hlin hexp.le
    _ = Real.exp (‖z‖ + ‖z‖) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2 * (1 + ‖z‖) ^ (1 : ℕ)) := by
        refine Real.exp_le_exp.mpr ?_
        rw [pow_one]; linarith

/-- **The `z sin z` primitive admits no order-two quadratic inner factor.**  Every entire `g` with
`sin z - z cos z = a + g z ^ (2 : ℕ)` is differentially algebraic of order at most one. -/
theorem sinPrimitive_quadratic_inner_firstOrder {g : ℂ → ℂ} {a : ℂ}
    (hg : Differentiable ℂ g) (hquad : ∀ z, sinPrimitive z = a + g z ^ (2 : ℕ)) :
    DifferentiallyAlgebraicOfOrder g 1 :=
  involutive_reflection_differentiallyAlgebraicOfOrder_one hg finiteOrderEnvelope_sinPrimitive
    sinPrimitive_reflection hquad

end GaloisForLFunctions.HTGeometry
