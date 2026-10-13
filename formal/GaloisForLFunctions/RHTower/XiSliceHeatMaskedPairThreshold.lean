import GaloisForLFunctions.RHTower.XiSliceHeatMixedTripleThreshold

/-!
# WD heat thresholds of an off-line pair behind a critical zero of order `m`

Let `S(t, y) = ξ(½+y+it) ξ(½−y+it)` and `T_n(λ, 0, t)` the heated slice coefficients.  Suppose

  `Ξ(z) = (z − γ)^m ((z − γ)² + b²) g(z)`,   `g` continuous,

so the off-line pair `½ ± b + iγ` sits at the ordinate of a critical zero of order `m`.

**Hermite moments of polynomials** (`integral_poly_mul_hermiteGauss`).  For every real polynomial
`P`, `∫ P(w) g_n(w) dw = ∫ P^{(n)}(w) e^{−w²/2} dw`, by `n` integrations by parts
(`g_n' = −g_{n+1}`, `hasDerivAt_hermiteGauss`).

**Theorem** (`re_xiSliceHeatTransfer_neg_of_masked_pair_order`).  At the ordinate the slice is
`S(γ, y) = y^{2m}(b² − y²)² G(y)`, `G(y) = g(γ − iy) g(γ + iy)` (`xiSliceProduct_eq_masked_mul`), and
`g(γ)` is real (`maskedCofactor_self_im`).  The order-`2j` Hermite moment of `λ^m w^{2m}(b² − λw²)²`
is `√(2π) · maskedPairMoment b λ m j` (`integral_hermiteGauss_mul_maskedPairSlice`).  If the cofactor
deviation is below `−√(2π) · maskedPairMoment b λ m j · g(γ)²`, then `Re T_{2j}(λ, 0, γ) < 0`, and
`λ ≤ λ_WD` (`le_wdHeatThreshold_of_masked_pair_order`).

* Order `2m + 2` (`maskedPairMoment_top`): the moment is `λ^{m+1}(2m+2)!((m+2)(2m+3)λ − 2b²)`, so the
  threshold is `2b²/((m+2)(2m+3))` (`le_wdHeatThreshold_of_masked_pair`); this is `b²/3` for `m = 0`
  (`re_xiSliceHeatTransfer_two_neg_of_offline_zero`) and `2b²/15` for `m = 1`
  (`re_xiSliceHeatTransfer_four_neg_of_mixed_triple`).
* Heat unmasks at lower order (`maskedPairMoment_two_two`,
  `le_wdHeatThreshold_of_double_masked_pair`): for `m = 2` the order-four coefficient at heat `0` is
  `b⁴g(γ)² ≥ 0`, but its moment `24λ²(b⁴ − 30b²λ + 210λ²)` is negative at `λ = b²/12`, above the
  order-six threshold `b²/14`.

At heat `0` the slice coefficients of order below `2m` vanish and the one of order `2m` is
`b⁴g(γ)² ≥ 0`, so order `2m + 2` is the first that sees the pair; positive heat moves detection to
lower orders.
-/

open Complex MeasureTheory Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-! ## Hermite moments of polynomials -/

theorem integrable_poly_mul_hermiteGauss (P : ℝ[X]) (n : ℕ) :
    Integrable (fun x : ℝ => P.eval x * hermiteGauss n x) := by
  have h := integrable_exp_mul_poly_gauss 0 (P * Polynomial.map (Int.castRingHom ℝ) (hermite n))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [zero_mul, Real.exp_zero, one_mul, eval_mul, eval_map, hermiteGauss, aeval_def,
    algebraMap_int_eq]
  ring

/-- One integration by parts: `∫ P g_{n+1} = ∫ P′ g_n`. -/
theorem integral_poly_mul_hermiteGauss_succ (P : ℝ[X]) (n : ℕ) :
    ∫ x : ℝ, P.eval x * hermiteGauss (n + 1) x
      = ∫ x : ℝ, (derivative P).eval x * hermiteGauss n x := by
  have hu : ∀ x ∈ tsupport (hermiteGauss n),
      HasDerivAt (fun y => P.eval y) ((derivative P).eval x) x := fun x _ => P.hasDerivAt x
  have hv : ∀ x ∈ tsupport (fun y => P.eval y),
      HasDerivAt (hermiteGauss n) (-hermiteGauss (n + 1) x) x :=
    fun x _ => hasDerivAt_hermiteGauss n x
  have h1 : Integrable ((fun y => P.eval y) * fun x => -hermiteGauss (n + 1) x) := by
    refine (integrable_poly_mul_hermiteGauss P (n + 1)).neg.congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp [Pi.mul_apply]
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv h1
    (integrable_poly_mul_hermiteGauss (derivative P) n) (integrable_poly_mul_hermiteGauss P n)
  have e1 : ∫ x : ℝ, P.eval x * hermiteGauss (n + 1) x =
      -∫ x : ℝ, P.eval x * -hermiteGauss (n + 1) x := by
    rw [← integral_neg]
    congr 1
    funext x
    ring
  rw [e1, hibp, neg_neg]

/-- **Hermite moments of polynomials.**  `∫ P(w) g_n(w) dw = ∫ P^{(n)}(w) e^{−w²/2} dw`. -/
theorem integral_poly_mul_hermiteGauss (P : ℝ[X]) (n : ℕ) :
    ∫ x : ℝ, P.eval x * hermiteGauss n x
      = ∫ x : ℝ, (derivative^[n] P).eval x * Real.exp (-(x ^ 2 / 2)) := by
  induction n generalizing P with
  | zero => simp [hermiteGauss, hermite_zero]
  | succ n ih => rw [integral_poly_mul_hermiteGauss_succ, ih, Function.iterate_succ_apply]

/-! ## The masked-pair slice polynomial -/

/-- `λ^m w^{2m}(b² − λw²)²` as a polynomial in `w`. -/
def maskedPairPoly (b lam : ℝ) (m : ℕ) : ℝ[X] :=
  C (lam ^ m * b ^ 4) * X ^ (2 * m) - C (2 * b ^ 2 * lam ^ (m + 1)) * X ^ (2 * m + 2)
    + C (lam ^ (m + 2)) * X ^ (2 * m + 4)

theorem eval_maskedPairPoly (b lam : ℝ) (m : ℕ) (w : ℝ) :
    (maskedPairPoly b lam m).eval w = lam ^ m * w ^ (2 * m) * (b ^ 2 - lam * w ^ 2) ^ 2 := by
  simp only [maskedPairPoly, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- `2 · (2m+4)⋯5 · 4 · 3 = (2m+4)!`, in the form `(2m+4)↓(2m+2) = (2m+2)! (2m+3)(m+2)`. -/
theorem descFactorial_two_mul_add_four (m : ℕ) :
    ((2 * m + 4).descFactorial (2 * m + 2) : ℝ) = (2 * m + 2).factorial * ((2 * m + 3) * (m + 2)) := by
  have h := Nat.factorial_mul_descFactorial (show 2 * m + 2 ≤ 2 * m + 4 by omega)
  have hf : (2 * m + 4).factorial = (2 * m + 4) * ((2 * m + 3) * (2 * m + 2).factorial) := by
    have a := Nat.factorial_succ (2 * m + 3)
    have b := Nat.factorial_succ (2 * m + 2)
    rw [show 2 * m + 3 + 1 = 2 * m + 4 by omega] at a
    rw [show 2 * m + 2 + 1 = 2 * m + 3 by omega] at b
    rw [a, b]
  rw [show 2 * m + 4 - (2 * m + 2) = 2 by omega, hf, Nat.factorial_two] at h
  have hR := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at hR
  linear_combination (1 / 2 : ℝ) * hR

/-- `∫ w^{2r} e^{−w²/2} dw = √(2π) (2r)!/(2^r r!)`, without the factor `√(2π)`. -/
def gaussEvenMoment (r : ℕ) : ℝ := (2 * r).factorial * (1 / 2 : ℝ) ^ r / r.factorial

theorem gaussEvenMoment_zero : gaussEvenMoment 0 = 1 := by simp [gaussEvenMoment]

theorem gaussEvenMoment_one : gaussEvenMoment 1 = 1 := by
  norm_num [gaussEvenMoment, Nat.factorial]

/-- The order-`2j` Hermite moment of the masked-pair slice, without the factor `√(2π)`:
`λ^m b⁴ (2m)↓(2j) μ_{m−j} − 2b²λ^{m+1} (2m+2)↓(2j) μ_{m+1−j} + λ^{m+2} (2m+4)↓(2j) μ_{m+2−j}`,
with `μ_r = (2r)!/(2^r r!)` and `k↓i` the falling factorial. -/
def maskedPairMoment (b lam : ℝ) (m j : ℕ) : ℝ :=
  lam ^ m * b ^ 4 * (2 * m).descFactorial (2 * j) * gaussEvenMoment (m - j)
    - 2 * b ^ 2 * lam ^ (m + 1) * (2 * m + 2).descFactorial (2 * j) * gaussEvenMoment (m + 1 - j)
    + lam ^ (m + 2) * (2 * m + 4).descFactorial (2 * j) * gaussEvenMoment (m + 2 - j)

theorem iterate_derivative_maskedPairPoly_eval (b lam : ℝ) (m j : ℕ) (w : ℝ) :
    (derivative^[2 * j] (maskedPairPoly b lam m)).eval w
      = lam ^ m * b ^ 4 * (2 * m).descFactorial (2 * j) * w ^ (2 * (m - j))
        - 2 * b ^ 2 * lam ^ (m + 1) * (2 * m + 2).descFactorial (2 * j) * w ^ (2 * (m + 1 - j))
        + lam ^ (m + 2) * (2 * m + 4).descFactorial (2 * j) * w ^ (2 * (m + 2 - j)) := by
  rw [maskedPairPoly, iterate_map_add, iterate_derivative_sub, iterate_derivative_C_mul,
    iterate_derivative_C_mul, iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
    iterate_derivative_X_pow_eq_C_mul, iterate_derivative_X_pow_eq_C_mul,
    show 2 * m - 2 * j = 2 * (m - j) by omega, show 2 * m + 2 - 2 * j = 2 * (m + 1 - j) by omega,
    show 2 * m + 4 - 2 * j = 2 * (m + 2 - j) by omega]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- **Hermite moments of the masked-pair slice.**
`∫ g_{2j}(w) λ^m w^{2m}(b² − λw²)² dw = √(2π) · maskedPairMoment b λ m j`. -/
theorem integral_hermiteGauss_mul_maskedPairSlice (b lam : ℝ) (m j : ℕ) :
    ∫ w : ℝ, (maskedPairPoly b lam m).eval w * hermiteGauss (2 * j) w
      = Real.sqrt (2 * Real.pi) * maskedPairMoment b lam m j := by
  rw [integral_poly_mul_hermiteGauss]
  set c₀ : ℝ := lam ^ m * b ^ 4 * (2 * m).descFactorial (2 * j) with hc₀
  set c₁ : ℝ := -(2 * b ^ 2 * lam ^ (m + 1) * (2 * m + 2).descFactorial (2 * j)) with hc₁
  set c₂ : ℝ := lam ^ (m + 2) * (2 * m + 4).descFactorial (2 * j) with hc₂
  have e : ∀ w : ℝ, (derivative^[2 * j] (maskedPairPoly b lam m)).eval w * Real.exp (-(w ^ 2 / 2))
      = c₀ * (Real.exp (-(w ^ 2 / 2)) * w ^ (2 * (m - j)))
        + c₁ * (Real.exp (-(w ^ 2 / 2)) * w ^ (2 * (m + 1 - j)))
        + c₂ * (Real.exp (-(w ^ 2 / 2)) * w ^ (2 * (m + 2 - j))) := by
    intro w
    rw [iterate_derivative_maskedPairPoly_eval]
    ring
  simp_rw [e]
  have i₀ := (integrable_exp_neg_sq_half_mul_pow (2 * (m - j))).const_mul c₀
  have i₁ := (integrable_exp_neg_sq_half_mul_pow (2 * (m + 1 - j))).const_mul c₁
  have i₂ := (integrable_exp_neg_sq_half_mul_pow (2 * (m + 2 - j))).const_mul c₂
  have i₀₁ : Integrable fun w : ℝ => c₀ * (Real.exp (-(w ^ 2 / 2)) * w ^ (2 * (m - j)))
      + c₁ * (Real.exp (-(w ^ 2 / 2)) * w ^ (2 * (m + 1 - j))) := i₀.add i₁
  rw [integral_add i₀₁ i₂, integral_add i₀ i₁, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_exp_neg_sq_half_mul_pow_even, integral_exp_neg_sq_half_mul_pow_even,
    integral_exp_neg_sq_half_mul_pow_even, maskedPairMoment, hc₀, hc₁, hc₂]
  simp only [gaussEvenMoment]
  ring

/-- At order `2m + 2` the moment is `λ^{m+1} (2m+2)! ((m+2)(2m+3)λ − 2b²)`. -/
theorem maskedPairMoment_top (b lam : ℝ) (m : ℕ) :
    maskedPairMoment b lam m (m + 1)
      = lam ^ (m + 1) * (2 * m + 2).factorial * ((m + 2) * (2 * m + 3) * lam - 2 * b ^ 2) := by
  have h0 : (2 * m).descFactorial (2 * (m + 1)) = 0 :=
    Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
  rw [maskedPairMoment, h0, show 2 * (m + 1) = 2 * m + 2 by ring, Nat.descFactorial_self,
    descFactorial_two_mul_add_four, show m + 1 - (m + 1) = 0 by omega,
    show m + 2 - (m + 1) = 1 by omega, gaussEvenMoment_zero, gaussEvenMoment_one]
  push_cast
  ring

/-- For a double critical zero (`m = 2`) the order-four moment is `24λ²(b⁴ − 30b²λ + 210λ²)`. -/
theorem maskedPairMoment_two_two (b lam : ℝ) :
    maskedPairMoment b lam 2 2 = 24 * lam ^ 2 * (b ^ 4 - 30 * b ^ 2 * lam + 210 * lam ^ 2) := by
  have d₀ : (2 * 2).descFactorial (2 * 2) = 24 := by decide
  have d₁ : (2 * 2 + 2).descFactorial (2 * 2) = 360 := by decide
  have d₂ : (2 * 2 + 4).descFactorial (2 * 2) = 1680 := by decide
  have μ₂ : gaussEvenMoment 2 = 3 := by norm_num [gaussEvenMoment, Nat.factorial]
  rw [maskedPairMoment, d₀, d₁, d₂, show 2 - 2 = 0 by rfl, show 2 + 1 - 2 = 1 by rfl,
    show 2 + 2 - 2 = 2 by rfl, gaussEvenMoment_zero, gaussEvenMoment_one, μ₂]
  push_cast
  ring

/-! ## The slice at the ordinate -/

/-- At the ordinate of a pair behind a critical zero of order `m` the slice factors as
`S(γ, y) = y^{2m}(b² − y²)² · g(γ − iy) g(γ + iy)`. -/
theorem xiSliceProduct_eq_masked_mul {γ b : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hfac : ∀ z, XiC z = (z - γ) ^ m * ((z - γ) ^ 2 + (b : ℂ) ^ 2) * g z) (y : ℂ) :
    xiSliceProduct γ y = y ^ (2 * m) * ((b : ℂ) ^ 2 - y ^ 2) ^ 2 *
      (g ((γ : ℂ) - y * I) * g ((γ : ℂ) + y * I)) := by
  have h1 : xi (1 / 2 + y + γ * I) = XiC ((γ : ℂ) - y * I) := by
    unfold XiC; congr 1; ring_nf; rw [I_sq]; ring
  have h2 : xi (1 / 2 - y + γ * I) = XiC ((γ : ℂ) + y * I) := by
    unfold XiC; congr 1; ring_nf; rw [I_sq]; ring
  have q1 : ((γ : ℂ) - y * I - γ) ^ 2 + (b : ℂ) ^ 2 = (b : ℂ) ^ 2 - y ^ 2 := by
    linear_combination y ^ 2 * I_sq
  have q2 : ((γ : ℂ) + y * I - γ) ^ 2 + (b : ℂ) ^ 2 = (b : ℂ) ^ 2 - y ^ 2 := by
    linear_combination y ^ 2 * I_sq
  have q3 : ((γ : ℂ) - y * I - γ) ^ m * ((γ : ℂ) + y * I - γ) ^ m = y ^ (2 * m) := by
    rw [← mul_pow, pow_mul]
    congr 1
    linear_combination (-y ^ 2) * I_sq
  unfold xiSliceProduct
  rw [h1, h2, hfac, hfac, q1, q2, ← q3]
  ring

/-- The cofactor is real at the ordinate: `g` is real on `ℝ \ {γ}` because `Ξ` is, and continuous. -/
theorem maskedCofactor_self_im {γ b : ℝ} {m : ℕ} {g : ℂ → ℂ} (hg : Continuous g)
    (hfac : ∀ z, XiC z = (z - γ) ^ m * ((z - γ) ^ 2 + (b : ℂ) ^ 2) * g z) :
    (g γ).im = 0 := by
  have hcont : Continuous fun x : ℝ => (g x).im :=
    Complex.continuous_im.comp (hg.comp Complex.continuous_ofReal)
  have heq : (fun x : ℝ => (g x).im) = fun _ => (0 : ℝ) := by
    refine Continuous.ext_on (dense_compl_singleton γ) hcont continuous_const ?_
    intro x hx
    show (g x).im = 0
    have hxγ : x - γ ≠ 0 := sub_ne_zero.mpr hx
    have hsq : 0 < (x - γ) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hxγ).symm
    set d : ℝ := (x - γ) ^ m * ((x - γ) ^ 2 + b ^ 2) with hd
    have hd0 : d ≠ 0 := mul_ne_zero (pow_ne_zero _ hxγ) (by nlinarith [sq_nonneg b])
    have hreal : (XiC (x : ℂ)).im = 0 := by
      have h' := XiC_conj (x : ℂ)
      rw [Complex.conj_ofReal] at h'
      exact Complex.conj_eq_iff_im.mp h'.symm
    have hdC : ((x : ℂ) - γ) ^ m * (((x : ℂ) - γ) ^ 2 + (b : ℂ) ^ 2) = (d : ℂ) := by
      rw [hd]; push_cast; ring
    have hf := hfac (x : ℂ)
    rw [hdC] at hf
    have him := congrArg Complex.im hf
    rw [Complex.im_ofReal_mul, hreal] at him
    exact (mul_eq_zero.mp him.symm).resolve_left hd0
  exact congrFun heq γ

/-! ## The thresholds -/

/-- **The order-`2j` heated coefficient at the ordinate.**  Let
`Ξ(z) = (z − γ)^m ((z − γ)² + b²) g(z)` with `g` continuous and `λ > 0`.  If the cofactor slice
`G(y) = g(γ − iy) g(γ + iy)` deviates from `g(γ)²` by less than the Hermite budget
`−√(2π) · maskedPairMoment b λ m j · |g(γ)|²` (weighted by `g_{2j}(w) y^{2m}(b² − y²)²` at
`y = √λ w`), then `Re T_{2j}(λ, 0, γ) < 0`. -/
theorem re_xiSliceHeatTransfer_neg_of_masked_pair_order {γ b lam : ℝ} {m j : ℕ} {g : ℂ → ℂ}
    (hlam : 0 < lam) (hg : Continuous g)
    (hfac : ∀ z, XiC z = (z - γ) ^ m * ((z - γ) ^ 2 + (b : ℂ) ^ 2) * g z)
    (hvar : ‖∫ w : ℝ, (hermiteGauss (2 * j) w : ℂ) *
        (((Real.sqrt lam * w : ℝ) : ℂ) ^ (2 * m) *
          ((b : ℂ) ^ 2 - ((Real.sqrt lam * w : ℝ) : ℂ) ^ 2) ^ 2 *
          (g ((γ : ℂ) - ((Real.sqrt lam * w : ℝ) : ℂ) * I) *
            g ((γ : ℂ) + ((Real.sqrt lam * w : ℝ) : ℂ) * I) - g γ ^ 2))‖
      < Real.sqrt (2 * Real.pi) * (-maskedPairMoment b lam m j) * ‖g γ‖ ^ 2) :
    (xiSliceHeatTransfer lam 0 γ (2 * j)).re < 0 := by
  set n := 2 * j with hn
  set sl := Real.sqrt lam with hsl
  have hsl0 : 0 < sl := Real.sqrt_pos.mpr hlam
  have hsl2 : sl ^ 2 = lam := Real.sq_sqrt hlam.le
  set r : ℝ := (g γ).re with hr
  have hgr : g γ = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [maskedCofactor_self_im hg hfac])
  set E : ℂ := ∫ w : ℝ, (hermiteGauss n w : ℂ) *
      (((sl * w : ℝ) : ℂ) ^ (2 * m) * ((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2 *
        (g ((γ : ℂ) - ((sl * w : ℝ) : ℂ) * I) * g ((γ : ℂ) + ((sl * w : ℝ) : ℂ) * I) - g γ ^ 2))
    with hE
  set M : ℝ := ∫ w : ℝ, (maskedPairPoly b lam m).eval w * hermiteGauss n w with hM
  have hMval : M = Real.sqrt (2 * Real.pi) * maskedPairMoment b lam m j :=
    integral_hermiteGauss_mul_maskedPairSlice b lam m j
  -- the main part
  have hP : ∀ w : ℝ, ((sl * w : ℝ) : ℂ) ^ (2 * m) * ((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2
      = (((maskedPairPoly b lam m).eval w : ℝ) : ℂ) := by
    intro w
    have hreal : (sl * w) ^ (2 * m) * (b ^ 2 - (sl * w) ^ 2) ^ 2
        = (maskedPairPoly b lam m).eval w := by
      rw [eval_maskedPairPoly, mul_pow, pow_mul, hsl2, mul_pow, hsl2]
    rw [← hreal]
    push_cast
    ring
  have hmainInt : Integrable (fun w : ℝ => (hermiteGauss n w : ℂ) *
      (((sl * w : ℝ) : ℂ) ^ (2 * m) * ((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2 * g γ ^ 2)) := by
    refine ((integrable_poly_mul_hermiteGauss (maskedPairPoly b lam m) n).ofReal.mul_const
      (g γ ^ 2)).congr (Filter.Eventually.of_forall fun w => ?_)
    show (((maskedPairPoly b lam m).eval w * hermiteGauss n w : ℝ) : ℂ) * g γ ^ 2 = _
    simp only [hP]
    push_cast
    ring
  have hmain : ∫ w : ℝ, (hermiteGauss n w : ℂ) *
      (((sl * w : ℝ) : ℂ) ^ (2 * m) * ((b : ℂ) ^ 2 - ((sl * w : ℝ) : ℂ) ^ 2) ^ 2 * g γ ^ 2)
      = (M : ℂ) * g γ ^ 2 := by
    rw [hM, ← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hP]
    push_cast
    ring
  -- the Hermite representation and the split
  have hH := integral_hermiteGauss_mul_xiSliceProduct hlam.le γ n
  have hSint := integrable_hermiteGauss_mul_xiSliceProduct hlam.le γ n
  have hsplit : ∫ w : ℝ, (hermiteGauss n w : ℂ) * xiSliceProduct γ ((sl * w : ℝ) : ℂ)
      = (M : ℂ) * g γ ^ 2 + E := by
    rw [← hmain, hE, ← integral_add hmainInt]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [xiSliceProduct_eq_masked_mul hfac]
      ring
    · refine (hSint.sub hmainInt).congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.sub_apply, xiSliceProduct_eq_masked_mul hfac]
      ring
  rw [hsplit] at hH
  -- take real parts
  set T := xiSliceHeatTransfer lam 0 γ n with hT
  have hc : (0 : ℝ) < Real.sqrt (2 * Real.pi) * sl ^ n * (Nat.factorial n : ℝ) := by positivity
  have hre := congrArg Complex.re hH
  rw [Complex.re_ofReal_mul, Complex.add_re, hgr] at hre
  have hMr : ((M : ℂ) * (r : ℂ) ^ 2).re = M * r ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hMr] at hre
  have hEle : E.re ≤ ‖E‖ := Complex.re_le_norm E
  have hgn : ‖g γ‖ ^ 2 = r ^ 2 := by rw [hgr, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hgn] at hvar
  have hvar' : ‖E‖ < Real.sqrt (2 * Real.pi) * (-maskedPairMoment b lam m j) * r ^ 2 := by
    simpa [hE, hsl, hn] using hvar
  have hMr2 : M * r ^ 2 = -(Real.sqrt (2 * Real.pi) * (-maskedPairMoment b lam m j) * r ^ 2) := by
    rw [hMval]; ring
  have hsum : M * r ^ 2 + E.re < 0 := by linarith
  by_contra hTnn
  push Not at hTnn
  have : 0 ≤ Real.sqrt (2 * Real.pi) * sl ^ n * (Nat.factorial n : ℝ) * T.re :=
    mul_nonneg hc.le hTnn
  linarith

/-- **The WD threshold at order `2j`.**  Under the hypotheses of
`re_xiSliceHeatTransfer_neg_of_masked_pair_order`, `λ ≤ λ_WD`. -/
theorem le_wdHeatThreshold_of_masked_pair_order {γ b lam : ℝ} {m j : ℕ} {g : ℂ → ℂ}
    (hlam : 0 < lam) (hg : Continuous g)
    (hfac : ∀ z, XiC z = (z - γ) ^ m * ((z - γ) ^ 2 + (b : ℂ) ^ 2) * g z)
    (hvar : ‖∫ w : ℝ, (hermiteGauss (2 * j) w : ℂ) *
        (((Real.sqrt lam * w : ℝ) : ℂ) ^ (2 * m) *
          ((b : ℂ) ^ 2 - ((Real.sqrt lam * w : ℝ) : ℂ) ^ 2) ^ 2 *
          (g ((γ : ℂ) - ((Real.sqrt lam * w : ℝ) : ℂ) * I) *
            g ((γ : ℂ) + ((Real.sqrt lam * w : ℝ) : ℂ) * I) - g γ ^ 2))‖
      < Real.sqrt (2 * Real.pi) * (-maskedPairMoment b lam m j) * ‖g γ‖ ^ 2) :
    lam ≤ wdHeatThreshold := by
  by_contra h
  push Not at h
  have hadm := mem_wdHeatAdmissible_of_lt h γ (2 * j)
  have hneg := re_xiSliceHeatTransfer_neg_of_masked_pair_order hlam hg hfac hvar
  have := (Complex.le_def.mp hadm).1
  simp only [Complex.zero_re] at this
  linarith

/-- **A pair behind a critical zero of order `m` is exposed at order `2m + 2`.**  Under the Hermite
budget `√(2π) λ^{m+1} (2m+2)! (2b² − (m+2)(2m+3)λ) |g(γ)|²` for the cofactor deviation,
`Re T_{2m+2}(λ, 0, γ) < 0`. -/
theorem re_xiSliceHeatTransfer_neg_of_masked_pair {γ b lam : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hlam : 0 < lam) (hg : Continuous g)
    (hfac : ∀ z, XiC z = (z - γ) ^ m * ((z - γ) ^ 2 + (b : ℂ) ^ 2) * g z)
    (hvar : ‖∫ w : ℝ, (hermiteGauss (2 * m + 2) w : ℂ) *
        (((Real.sqrt lam * w : ℝ) : ℂ) ^ (2 * m) *
          ((b : ℂ) ^ 2 - ((Real.sqrt lam * w : ℝ) : ℂ) ^ 2) ^ 2 *
          (g ((γ : ℂ) - ((Real.sqrt lam * w : ℝ) : ℂ) * I) *
            g ((γ : ℂ) + ((Real.sqrt lam * w : ℝ) : ℂ) * I) - g γ ^ 2))‖
      < Real.sqrt (2 * Real.pi) * lam ^ (m + 1) * (2 * m + 2).factorial *
          (2 * b ^ 2 - (m + 2) * (2 * m + 3) * lam) * ‖g γ‖ ^ 2) :
    (xiSliceHeatTransfer lam 0 γ (2 * m + 2)).re < 0 := by
  have h := re_xiSliceHeatTransfer_neg_of_masked_pair_order (j := m + 1) hlam hg hfac (by
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, maskedPairMoment_top]
    calc _ < _ := hvar
      _ = _ := by ring)
  rwa [show 2 * (m + 1) = 2 * m + 2 by ring] at h

/-- **The WD threshold is at least the masked-pair time.**  Under the hypotheses of
`re_xiSliceHeatTransfer_neg_of_masked_pair`, `λ ≤ λ_WD`; for a slowly varying cofactor this is
`λ_WD ≳ 2b²/((m+2)(2m+3))`. -/
theorem le_wdHeatThreshold_of_masked_pair {γ b lam : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hlam : 0 < lam) (hg : Continuous g)
    (hfac : ∀ z, XiC z = (z - γ) ^ m * ((z - γ) ^ 2 + (b : ℂ) ^ 2) * g z)
    (hvar : ‖∫ w : ℝ, (hermiteGauss (2 * m + 2) w : ℂ) *
        (((Real.sqrt lam * w : ℝ) : ℂ) ^ (2 * m) *
          ((b : ℂ) ^ 2 - ((Real.sqrt lam * w : ℝ) : ℂ) ^ 2) ^ 2 *
          (g ((γ : ℂ) - ((Real.sqrt lam * w : ℝ) : ℂ) * I) *
            g ((γ : ℂ) + ((Real.sqrt lam * w : ℝ) : ℂ) * I) - g γ ^ 2))‖
      < Real.sqrt (2 * Real.pi) * lam ^ (m + 1) * (2 * m + 2).factorial *
          (2 * b ^ 2 - (m + 2) * (2 * m + 3) * lam) * ‖g γ‖ ^ 2) :
    lam ≤ wdHeatThreshold := by
  by_contra h
  push Not at h
  have hadm := mem_wdHeatAdmissible_of_lt h γ (2 * m + 2)
  have hneg := re_xiSliceHeatTransfer_neg_of_masked_pair hlam hg hfac hvar
  have := (Complex.le_def.mp hadm).1
  simp only [Complex.zero_re] at this
  linarith

/-- `λ = b²/12` lies in the order-four window of a double critical zero:
`b⁴ − 30b²(b²/12) + 210(b²/12)² = −b⁴/24 < 0`. -/
theorem doubleMaskedWindow_twelfth {b : ℝ} (hb : 0 < b) :
    b ^ 4 - 30 * b ^ 2 * (b ^ 2 / 12) + 210 * (b ^ 2 / 12) ^ 2 < 0 := by
  have e : b ^ 4 - 30 * b ^ 2 * (b ^ 2 / 12) + 210 * (b ^ 2 / 12) ^ 2 = -(b ^ 4 / 24) := by ring
  rw [e]
  have : 0 < b ^ 4 := by positivity
  linarith

/-- **Heat unmasks a pair behind a double critical zero at order four.**  For `m = 2` the order-four
coefficient at heat `0` is `b⁴g(γ)² ≥ 0`.  At heat `λ` the order-four moment is
`24λ²(b⁴ − 30b²λ + 210λ²)`, negative for instance at `λ = b²/12` (`doubleMaskedWindow_twelfth`);
under the corresponding variation bound `λ ≤ λ_WD`, above the order-six threshold `b²/14`. -/
theorem le_wdHeatThreshold_of_double_masked_pair {γ b lam : ℝ} {g : ℂ → ℂ}
    (hlam : 0 < lam) (hg : Continuous g)
    (hfac : ∀ z, XiC z = (z - γ) ^ 2 * ((z - γ) ^ 2 + (b : ℂ) ^ 2) * g z)
    (hvar : ‖∫ w : ℝ, (hermiteGauss (2 * 2) w : ℂ) *
        (((Real.sqrt lam * w : ℝ) : ℂ) ^ (2 * 2) *
          ((b : ℂ) ^ 2 - ((Real.sqrt lam * w : ℝ) : ℂ) ^ 2) ^ 2 *
          (g ((γ : ℂ) - ((Real.sqrt lam * w : ℝ) : ℂ) * I) *
            g ((γ : ℂ) + ((Real.sqrt lam * w : ℝ) : ℂ) * I) - g γ ^ 2))‖
      < Real.sqrt (2 * Real.pi) * (24 * lam ^ 2 * (30 * b ^ 2 * lam - b ^ 4 - 210 * lam ^ 2)) *
          ‖g γ‖ ^ 2) :
    lam ≤ wdHeatThreshold :=
  le_wdHeatThreshold_of_masked_pair_order (m := 2) (j := 2) hlam hg hfac (by
    rw [maskedPairMoment_two_two]
    calc _ < _ := hvar
      _ = _ := by ring)

end

end RHTower.DeBruijn
