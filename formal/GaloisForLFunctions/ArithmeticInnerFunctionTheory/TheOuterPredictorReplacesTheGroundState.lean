import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheSchurParametersOfSpecZ

/-!
# The outer predictor replaces the positive ground state

Allegretto–Piepenbrink: a form with nonpositive couplings is nonnegative iff it has a positive supersolution. The certificate is the Doob
identity `T(x) = Σ (Th)_i/h_i x_i² − ½Σ κ(i−j)h_ih_j(x_i/h_i − x_j/h_j)²` (`toeplitzForm_eq_doob`), and
it dies with frustration: on a triangle with `κ₁²κ₂ > 0` every gauge has a wrong edge (`exists_wrong_edge`).

On a lattice the exact replacement is **causal**. Solve the form only on the past: the predictor `a` of size `n`, with polynomial
`A(z) = 1 + Σ a_k z^{k+1}`, and margin `E`.

**Theorem** (`toeplitzPosDef_iff_exists_outer_predictor`). For an even sequence of any sign pattern, the window of size `n + 1` is
positive definite iff it has a predictor with positive margin and **no zero of `A` in the closed disc**.

Positivity of the ground state is replaced by zero-freeness: *outer* in place of *positive*. Sign changes of the predictor are free, so frustration is no obstruction.

* On nonpositive couplings the certificates agree: the predictor is nonnegative (`predictor_nonneg_of_offDiag_nonpos`), so `(1, a)` is a positive
  supersolution. Allegretto–Piepenbrink is the sign-definite face of the causal certificate.
* The certificate is a sum of squares with the margins as weights (`exists_sum_sq_certificate`).
* **A Riemann hypothesis in every window** (`paraPoly_zero_on_circle`). If `A` is outer, then the self-reciprocal polynomials
  `A ∓ zA^*` have all their zeros on the unit circle. Functional equation (self-reciprocity) plus passivity (outer) is reality of
  the zeros, as in Hermite–Biehler.
* **Spec ℤ** (`riemannHypothesis_iff_exists_outer_predictor`). RH is the existence of an outer predictor with positive margin for every window of every lattice of every nonzero test.

The mechanism is Schur's: `S = A^*/A` is holomorphic on the closed disc and unimodular on the circle, hence contractive. One step of the Levinson
evolution is `A' = A − γzA^*` (`predPoly_snoc`), and its inverse (`stepDown`) needs no invertibility of the smaller window.
-/

open Finset Filter Topology Metric
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GrowingWindowsOfSpecZ ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis

noncomputable section

variable {κ : ℤ → ℝ} {n : ℕ}

/-! ### The predictor polynomial -/

/-- The predictor polynomial `A(z) = 1 + Σ_k a_k z^{k+1}`. -/
def predPoly (a : Fin n → ℝ) (z : ℂ) : ℂ := 1 + ∑ k : Fin n, (a k : ℂ) * z ^ ((k : ℕ) + 1)

/-- The reversed polynomial `A^*(z) = zⁿ + Σ_k a_k z^{n−1−k} = zⁿA(1/z)`. -/
def predRev (a : Fin n → ℝ) (z : ℂ) : ℂ := z ^ n + ∑ k : Fin n, (a k : ℂ) * z ^ ((Fin.rev k : Fin n) : ℕ)

theorem differentiable_predPoly (a : Fin n → ℝ) : Differentiable ℂ (predPoly a) := by
  unfold predPoly
  fun_prop

theorem differentiable_predRev (a : Fin n → ℝ) : Differentiable ℂ (predRev a) := by
  unfold predRev
  fun_prop

theorem predPoly_zero (a : Fin n → ℝ) : predPoly a 0 = 1 := by simp [predPoly]

theorem val_rev_add (k : Fin n) : ((Fin.rev k : Fin n) : ℕ) + ((k : ℕ) + 1) = n := by
  rw [Fin.val_rev]
  have := k.isLt
  omega

theorem rev_cast (k : Fin n) : (((Fin.rev k : Fin n) : ℕ) : ℤ) = (n : ℤ) - 1 - ((k : ℕ) : ℤ) := by
  rw [Fin.val_rev]
  have := k.isLt
  omega

/-- `A^*(z) = zⁿA(1/z)`. -/
theorem predRev_eq_pow_mul (a : Fin n → ℝ) {z : ℂ} (hz : z ≠ 0) :
    predRev a z = z ^ n * predPoly a z⁻¹ := by
  simp only [predRev, predPoly, mul_add, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  have e : z ^ n = z ^ ((Fin.rev k : Fin n) : ℕ) * z ^ ((k : ℕ) + 1) := by
    rw [← pow_add, val_rev_add]
  have h1 : z ^ ((k : ℕ) + 1) * z⁻¹ ^ ((k : ℕ) + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  rw [e]
  linear_combination (-(a k : ℂ) * z ^ ((Fin.rev k : Fin n) : ℕ)) * h1

/-- On the circle `A^*(z) = zⁿ conj A(z)`: the coefficients are real. -/
theorem norm_predRev_eq (a : Fin n → ℝ) {z : ℂ} (hz : ‖z‖ = 1) : ‖predRev a z‖ = ‖predPoly a z‖ := by
  have hzc : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    simp
  have e : predRev a z = z ^ n * conj (predPoly a z) := by
    simp only [predRev, predPoly, map_add, map_one, map_sum, map_mul, map_pow, Complex.conj_ofReal,
      mul_add, mul_one, mul_sum]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    have e : z ^ n = z ^ ((Fin.rev k : Fin n) : ℕ) * z ^ ((k : ℕ) + 1) := by
      rw [← pow_add, val_rev_add]
    have h1 : z ^ ((k : ℕ) + 1) * conj z ^ ((k : ℕ) + 1) = 1 := by
      rw [← mul_pow, hzc, one_pow]
    rw [e]
    linear_combination (-(a k : ℂ) * z ^ ((Fin.rev k : Fin n) : ℕ)) * h1
  rw [e, norm_mul, norm_pow, hz, one_pow, one_mul, RCLike.norm_conj]

/-- **Schur's contraction.** If `A` is outer, `|A^*| ≤ |A|` on the closed disc. -/
theorem norm_predRev_le {a : Fin n → ℝ} (h : ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly a z ≠ 0) {z : ℂ}
    (hz : ‖z‖ ≤ 1) : ‖predRev a z‖ ≤ ‖predPoly a z‖ := by
  have hd : DiffContOnCl ℂ (fun w => predRev a w / predPoly a w) (ball (0 : ℂ) 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    intro w hw
    exact ((differentiable_predRev a w).div (differentiable_predPoly a w)
      (h w (by simpa using hw))).differentiableWithinAt
  have hb : ‖predRev a z / predPoly a z‖ ≤ 1 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
      (fun w hw => by
        rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hw
        rw [norm_div, norm_predRev_eq a hw]
        exact div_self_le_one _)
      (by rw [closure_ball (0 : ℂ) one_ne_zero]; simpa using hz)
  have hpos : 0 < ‖predPoly a z‖ := norm_pos_iff.mpr (h z hz)
  rw [norm_div, div_le_one hpos] at hb
  exact hb

/-! ### The Levinson step -/

/-- One Levinson step on polynomials: `A' = A − γzA^*`. -/
theorem predPoly_snoc (a : Fin n → ℝ) (γ : ℝ) (z : ℂ) :
    predPoly (Fin.snoc (fun k => a k - γ * a (Fin.rev k)) (-γ) : Fin (n + 1) → ℝ) z =
      predPoly a z - γ * z * predRev a z := by
  simp only [predPoly, predRev]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have hr : ∑ k : Fin n, (a (Fin.rev k) : ℂ) * z ^ ((k : ℕ) + 1) =
      (∑ k : Fin n, (a k : ℂ) * z ^ ((Fin.rev k : Fin n) : ℕ)) * z := by
    rw [sum_mul, ← Equiv.sum_comp Fin.revPerm]
    refine sum_congr rfl fun k _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    ring
  have h1 : ∑ k : Fin n, ((a k - γ * a (Fin.rev k) : ℝ) : ℂ) * z ^ ((k : ℕ) + 1) =
      ∑ k : Fin n, (a k : ℂ) * z ^ ((k : ℕ) + 1) -
        γ * ∑ k : Fin n, (a (Fin.rev k) : ℂ) * z ^ ((k : ℕ) + 1) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [h1, hr]
  push_cast
  ring

/-- `A' = A − γzA^*` stays outer for `|γ| < 1`. -/
theorem predPoly_sub_ne_zero {a : Fin n → ℝ} (h : ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly a z ≠ 0) {γ : ℝ}
    (hγ : |γ| < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) : predPoly a z - γ * z * predRev a z ≠ 0 := by
  intro h0
  have hA : predPoly a z = γ * z * predRev a z := sub_eq_zero.mp h0
  have hpos : 0 < ‖predPoly a z‖ := norm_pos_iff.mpr (h z hz)
  have hle : ‖predPoly a z‖ ≤ |γ| * ‖predPoly a z‖ := by
    calc ‖predPoly a z‖ = ‖(γ : ℂ) * z * predRev a z‖ := by rw [← hA]
      _ = |γ| * ‖z‖ * ‖predRev a z‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |γ| * 1 * ‖predPoly a z‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hz (abs_nonneg _)) (norm_predRev_le h hz)
            (norm_nonneg _) (by positivity)
      _ = |γ| * ‖predPoly a z‖ := by ring
  nlinarith

/-- **Positive windows have outer predictors.** -/
theorem predPoly_levinson_ne_zero (hκ : IsEvenSeq κ) :
    ∀ n : ℕ, ToeplitzPosDef κ (n + 1) → ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly (levinsonPred κ n) z ≠ 0
  | 0, _, z, _ => by simp [predPoly]
  | n + 1, h, z, hz => by
    have hlow := (toeplitzForm_posDef_iff hκ (n + 1)).mp h
    have h' : ToeplitzPosDef κ (n + 1) :=
      (toeplitzForm_posDef_iff hκ n).mpr fun k hk => hlow k (by omega)
    have hγ : |reflCoeff κ n| < 1 := by
      have h1 := hlow (n + 1) le_rfl
      have h2 := hlow n (by omega)
      rw [levinsonErr_succ_eq_mul h2.ne'] at h1
      have h3 : 0 < 1 - reflCoeff κ n ^ 2 := (pos_iff_pos_of_mul_pos h1).mp h2
      rw [← sq_lt_one_iff_abs_lt_one]
      linarith
    rw [levinsonPred_succ, predPoly_snoc]
    exact predPoly_sub_ne_zero (predPoly_levinson_ne_zero hκ n h') hγ hz

/-! ### Schur–Cohn: the last coefficient of an outer predictor -/

theorem predRev_zero (b : Fin (n + 1) → ℝ) : predRev b 0 = b (Fin.last n) := by
  simp only [predRev]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.rev_castSucc, Fin.rev_last]

/-- **Schur–Cohn.** The last coefficient of an outer predictor lies in `(−1, 1)`: at the boundary `A^*/A` would be constant by the maximum principle, and `A` would have no zeros in `ℂ`. -/
theorem abs_last_lt_one {b : Fin (n + 1) → ℝ} (h : ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly b z ≠ 0) :
    |b (Fin.last n)| < 1 := by
  have hle : |b (Fin.last n)| ≤ 1 := by
    have h1 := norm_predRev_le h (z := 0) (by simp)
    rw [predRev_zero, predPoly_zero, norm_one, Complex.norm_real, Real.norm_eq_abs] at h1
    exact h1
  refine lt_of_le_of_ne hle fun heq => ?_
  set c : ℂ := (b (Fin.last n) : ℂ) with hc
  have hcn : ‖c‖ = 1 := by rw [hc, Complex.norm_real, Real.norm_eq_abs, heq]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hcn
    exact zero_ne_one hcn
  -- `S = A^*/A` attains its maximum at the centre, so it is the constant `c`
  have hd : DifferentiableOn ℂ (fun w => predRev b w / predPoly b w) (ball (0 : ℂ) 1) := fun w hw =>
    ((differentiable_predRev b w).div (differentiable_predPoly b w)
      (h w (by simpa using (mem_ball_zero_iff.mp hw).le))).differentiableWithinAt
  have hmax : IsMaxOn (norm ∘ fun w => predRev b w / predPoly b w) (ball (0 : ℂ) 1) 0 := by
    intro w hw
    have hw' : ‖w‖ ≤ 1 := by simpa using (mem_ball_zero_iff.mp hw).le
    have h1 := norm_predRev_le h hw'
    have hpos : 0 < ‖predPoly b w‖ := norm_pos_iff.mpr (h w hw')
    change ‖predRev b w / predPoly b w‖ ≤ ‖predRev b 0 / predPoly b 0‖
    rw [predRev_zero, predPoly_zero, div_one, ← hc, hcn, norm_div, div_le_one hpos]
    exact h1
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) 1).isPreconnected
    isOpen_ball hd (mem_ball_self one_pos) hmax
  have hS : ∀ w, ‖w‖ < 1 → predRev b w = c * predPoly b w := by
    intro w hw
    have h1 := hconst (mem_ball_zero_iff.mpr hw)
    simp only [Function.const_apply, predRev_zero, predPoly_zero, div_one] at h1
    have hne := h w hw.le
    rw [div_eq_iff hne] at h1
    exact h1
  -- so `A` has no zeros at all
  have hall : ∀ z : ℂ, predPoly b z ≠ 0 := by
    intro z
    by_cases hz : ‖z‖ ≤ 1
    · exact h z hz
    · push Not at hz
      have hz0 : z ≠ 0 := fun h0 => by
        rw [h0, norm_zero] at hz
        linarith
      have hw : ‖z⁻¹‖ < 1 := by
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hz
      have hw0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
      have e := predRev_eq_pow_mul b hw0
      rw [inv_inv, hS _ hw] at e
      intro h0
      rw [h0, mul_zero] at e
      exact (mul_ne_zero hc0 (h _ hw.le)) e
  -- contradiction with the fundamental theorem of algebra
  let P : Polynomial ℂ := 1 + ∑ k : Fin (n + 1), Polynomial.C (b k : ℂ) * Polynomial.X ^ ((k : ℕ) + 1)
  have hev : ∀ z, P.eval z = predPoly b z := fun z => by
    simp [P, predPoly, Polynomial.eval_finset_sum]
  by_cases hdeg : 0 < P.degree
  · obtain ⟨z, hz⟩ := Complex.exists_root hdeg
    exact hall z (by rw [← hev]; exact hz)
  · have hP := Polynomial.eq_C_of_degree_le_zero (not_lt.mp hdeg)
    have hone : ∀ z, predPoly b z = 1 := fun z => by
      rw [← predPoly_zero b, ← hev, ← hev, hP]
      simp only [Polynomial.eval_C]
    have hw : ‖(2⁻¹ : ℂ)‖ < 1 := by norm_num
    have e := predRev_eq_pow_mul b (z := 2⁻¹) (by norm_num)
    rw [hS _ hw, hone, hone, mul_one, mul_one] at e
    have hn := congrArg norm e
    rw [hcn, norm_pow, norm_inv] at hn
    have h2 : ‖(2 : ℂ)‖⁻¹ = 1 / 2 := by norm_num
    rw [h2] at hn
    have hlt : ((1 : ℝ) / 2) ^ (n + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith

/-! ### The step down -/

/-- The inverse Levinson step: `a_k = (b_k − c b_{n−1−k})/(1 − c²)`, `c = b_n`. -/
def stepDown (b : Fin (n + 1) → ℝ) (k : Fin n) : ℝ :=
  (b k.castSucc - b (Fin.last n) * b (Fin.rev k).castSucc) / (1 - b (Fin.last n) ^ 2)

theorem isPredictor_stepDown (hκ : IsEvenSeq κ) {b : Fin (n + 1) → ℝ} (hb : IsPredictor κ (n + 1) b)
    (hc : 1 - b (Fin.last n) ^ 2 ≠ 0) : IsPredictor κ n (stepDown b) := by
  set c := b (Fin.last n) with hcd
  have hrow : ∀ j : Fin n, ∑ k : Fin n, κ ((j : ℤ) - (k : ℕ)) * b k.castSucc =
      -κ ((j : ℤ) + 1) - κ ((n : ℤ) - j) * c := by
    intro j
    have h := hb j.castSucc
    rw [Fin.sum_univ_castSucc] at h
    simp only [Fin.val_castSucc, Fin.val_last] at h
    have e : κ ((j : ℤ) - n) = κ ((n : ℤ) - j) := by rw [← hκ, neg_sub]
    rw [e] at h
    linarith
  intro j
  have hrev : ∑ k : Fin n, κ ((j : ℤ) - (k : ℕ)) * b (Fin.rev k).castSucc =
      ∑ k : Fin n, κ ((((Fin.rev j : Fin n) : ℕ) : ℤ) - (k : ℕ)) * b k.castSucc := by
    rw [← Equiv.sum_comp Fin.revPerm]
    refine sum_congr rfl fun k _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    congr 1
    rw [← hκ, rev_cast, rev_cast]
    congr 1
    ring
  have hr := hrow (Fin.rev j)
  rw [rev_cast] at hr
  have e1 : (n : ℤ) - 1 - ((j : ℕ) : ℤ) + 1 = (n : ℤ) - j := by ring
  have e2 : κ ((n : ℤ) - ((n : ℤ) - 1 - ((j : ℕ) : ℤ))) = κ ((j : ℤ) + 1) := by
    congr 1
    ring
  rw [e1, e2] at hr
  have hr2 : ∑ k : Fin n, κ (((Fin.rev j : Fin n) : ℕ) - (k : ℕ) : ℤ) * b k.castSucc =
      -κ ((n : ℤ) - j) - κ ((j : ℤ) + 1) * c := by
    rw [← hr]
    refine sum_congr rfl fun k _ => ?_
    rw [rev_cast]
  rw [hr2] at hrev
  have hexp : ∑ k : Fin n, κ ((j : ℤ) - (k : ℕ)) * stepDown b k =
      (∑ k : Fin n, κ ((j : ℤ) - (k : ℕ)) * b k.castSucc -
        c * ∑ k : Fin n, κ ((j : ℤ) - (k : ℕ)) * b (Fin.rev k).castSucc) / (1 - c ^ 2) := by
    rw [mul_sum, ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun k _ => ?_
    simp only [stepDown]
    ring
  rw [hexp, hrow j, hrev, div_eq_iff hc]
  ring

theorem predErr_stepDown (hκ : IsEvenSeq κ) {b : Fin (n + 1) → ℝ} (hb : IsPredictor κ (n + 1) b)
    (hc : 1 - b (Fin.last n) ^ 2 ≠ 0) :
    predErr κ n (stepDown b) = predErr κ (n + 1) b / (1 - b (Fin.last n) ^ 2) := by
  set c := b (Fin.last n) with hcd
  have hrow := hb (Fin.last n)
  rw [Fin.sum_univ_castSucc] at hrow
  simp only [Fin.val_castSucc, Fin.val_last, sub_self] at hrow
  have hrev := sum_rev_eq (κ := κ) (fun k : Fin n => b k.castSucc)
  simp only [predErr]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hexp : ∑ k : Fin n, κ (((k : ℕ) : ℤ) + 1) * stepDown b k =
      (∑ k : Fin n, κ (((k : ℕ) : ℤ) + 1) * b k.castSucc -
        c * ∑ k : Fin n, κ (((k : ℕ) : ℤ) + 1) * b (Fin.rev k).castSucc) / (1 - c ^ 2) := by
    rw [mul_sum, ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun k _ => ?_
    simp only [stepDown]
    ring
  rw [hexp, hrev]
  field_simp
  have hrow' : ∑ k : Fin n, κ ((n : ℤ) - (k : ℕ)) * b k.castSucc = -κ ((n : ℤ) + 1) - κ 0 * c := by
    linarith
  rw [hrow']
  ring

theorem predPoly_stepDown (b : Fin (n + 1) → ℝ) (hc : 1 - b (Fin.last n) ^ 2 ≠ 0) (z : ℂ) :
    predPoly (stepDown b) z =
      (predPoly b z - b (Fin.last n) * predRev b z) / (1 - (b (Fin.last n) : ℂ) ^ 2) := by
  set c := b (Fin.last n) with hcd
  have hcC : (1 - (c : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hc
  rw [eq_div_iff hcC]
  simp only [predPoly, predRev]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.rev_castSucc, Fin.rev_last, Fin.val_succ, Fin.val_zero,
    pow_zero, mul_one]
  have hr : ∑ k : Fin n, (b k.castSucc : ℂ) * z ^ (((Fin.rev k : Fin n) : ℕ) + 1) =
      ∑ k : Fin n, (b (Fin.rev k).castSucc : ℂ) * z ^ ((k : ℕ) + 1) := by
    rw [← Equiv.sum_comp Fin.revPerm]
    refine sum_congr rfl fun k _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]
  have hs : ∑ k : Fin n, ((stepDown b k : ℝ) : ℂ) * z ^ ((k : ℕ) + 1) * (1 - (c : ℂ) ^ 2) =
      ∑ k : Fin n, (b k.castSucc : ℂ) * z ^ ((k : ℕ) + 1) -
        c * ∑ k : Fin n, (b (Fin.rev k).castSucc : ℂ) * z ^ ((k : ℕ) + 1) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [stepDown, ← hcd]
    push_cast
    field_simp
  rw [hr, add_mul, sum_mul, hs, ← hcd]
  ring

/-! ### The certificate -/

/-- **The causal certificate.** For an even sequence of any sign pattern, the window of size `n + 1` is positive definite iff it has
a predictor with positive margin whose polynomial has no zero in the closed disc. -/
theorem toeplitzPosDef_iff_exists_outer_predictor (hκ : IsEvenSeq κ) :
    ∀ n : ℕ, ToeplitzPosDef κ (n + 1) ↔ ∃ a : Fin n → ℝ, IsPredictor κ n a ∧ 0 < predErr κ n a ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly a z ≠ 0 := by
  have hup : ∀ n : ℕ, ToeplitzPosDef κ (n + 1) → ∃ a : Fin n → ℝ, IsPredictor κ n a ∧
      0 < predErr κ n a ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly a z ≠ 0 := by
    intro n h
    have hlow := (toeplitzForm_posDef_iff hκ n).mp h
    have hne : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => (hlow k hk.le).ne'
    refine ⟨levinsonPred κ n, levinson_isPredictor hκ hne, ?_, predPoly_levinson_ne_zero hκ n h⟩
    rw [predErr_levinson hκ hne]
    exact hlow n le_rfl
  intro n
  refine ⟨hup n, ?_⟩
  induction n with
  | zero =>
    rintro ⟨a, ha, hE, -⟩
    refine (posDef_succ_iff hκ ha).mpr ⟨fun x hx => absurd (Subsingleton.elim x 0) hx, hE⟩
  | succ n ih =>
    rintro ⟨b, hb, hE, hz⟩
    have hc := abs_last_lt_one hz
    have hc2 : 0 < 1 - b (Fin.last n) ^ 2 := by
      have := (sq_lt_one_iff_abs_lt_one _).mpr hc
      linarith
    refine (posDef_succ_iff hκ hb).mpr ⟨ih ⟨stepDown b, isPredictor_stepDown hκ hb hc2.ne', ?_, ?_⟩, hE⟩
    · rw [predErr_stepDown hκ hb hc2.ne']
      exact div_pos hE hc2
    · intro z hz1
      rw [predPoly_stepDown b hc2.ne']
      refine div_ne_zero ?_ (by exact_mod_cast hc2.ne')
      have := predPoly_sub_ne_zero (a := b) hz (γ := b (Fin.last n)) hc (z := z)
      intro h0
      have hA : predPoly b z = b (Fin.last n) * predRev b z := sub_eq_zero.mp h0
      have hpos : 0 < ‖predPoly b z‖ := norm_pos_iff.mpr (hz z hz1)
      have hle : ‖predPoly b z‖ ≤ |b (Fin.last n)| * ‖predPoly b z‖ := by
        calc ‖predPoly b z‖ = ‖(b (Fin.last n) : ℂ) * predRev b z‖ := by rw [← hA]
          _ = |b (Fin.last n)| * ‖predRev b z‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ _ := mul_le_mul_of_nonneg_left (norm_predRev_le hz hz1) (abs_nonneg _)
      nlinarith

/-- **RH is the existence of outer predictors.** Every window of every lattice of every nonzero test of `Spec ℤ` has a
predictor with positive margin and no zero in the closed disc. -/
theorem riemannHypothesis_iff_exists_outer_predictor :
    RiemannHypothesis ↔ ∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h → ∀ n : ℕ,
      ∃ a : Fin n → ℝ, IsPredictor (weilSeq φ h) n a ∧ 0 < predErr (weilSeq φ h) n a ∧
        ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly a z ≠ 0 := by
  rw [riemannHypothesis_iff_levinsonErr_pos]
  refine forall_congr' fun φ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun h => forall_congr' fun _ => ?_
  have hκ := weilSeq_isEven φ h
  constructor
  · intro hE n
    exact (toeplitzPosDef_iff_exists_outer_predictor hκ n).mp
      ((toeplitzForm_posDef_iff hκ n).mpr fun k _ => hE k)
  · intro hP n
    exact (toeplitzForm_posDef_iff hκ n).mp
      ((toeplitzPosDef_iff_exists_outer_predictor hκ n).mpr (hP n)) n le_rfl

/-! ### A Riemann hypothesis in every window -/

/-- The self-reciprocal polynomial `A − εzA^*`, `ε = ±1`. -/
def paraPoly (a : Fin n → ℝ) (ε : ℝ) (z : ℂ) : ℂ := predPoly a z - ε * z * predRev a z

/-- Self-reciprocity: `z^{n+1}B(1/z) = −εB(z)`. -/
theorem paraPoly_reciprocal (a : Fin n → ℝ) {ε : ℝ} (hε : ε ^ 2 = 1) {z : ℂ} (hz : z ≠ 0) :
    z ^ (n + 1) * paraPoly a ε z⁻¹ = -ε * paraPoly a ε z := by
  have h1 := predRev_eq_pow_mul a hz
  have h2 := predRev_eq_pow_mul a (inv_ne_zero hz)
  rw [inv_inv] at h2
  have hεC : (ε : ℂ) ^ 2 = 1 := by exact_mod_cast hε
  have h3 : z ^ n * z⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  have h4 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  simp only [paraPoly]
  rw [h2, h1]
  linear_combination (-(ε : ℂ) * predPoly a z * z * z⁻¹) * h3 +
    (-(ε : ℂ) * predPoly a z) * h4 + (-(z * z ^ n) * predPoly a z⁻¹) * hεC

/-- **A Riemann hypothesis in every window.** If `A` is outer, every zero of the self-reciprocal `A ∓ zA^*` lies on the unit circle:
functional equation plus passivity is reality of the zeros. -/
theorem paraPoly_zero_on_circle {a : Fin n → ℝ} (h : ∀ z : ℂ, ‖z‖ ≤ 1 → predPoly a z ≠ 0) {ε : ℝ}
    (hε : ε ^ 2 = 1) {z : ℂ} (hz : paraPoly a ε z = 0) : ‖z‖ = 1 := by
  have hε1 : |ε| = 1 := by
    have h2 : |ε| ^ 2 = 1 := by rw [sq_abs, hε]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg ε) two_ne_zero).mp h2
  have hin : ∀ w : ℂ, ‖w‖ < 1 → paraPoly a ε w ≠ 0 := by
    intro w hw h0
    have hA : predPoly a w = ε * w * predRev a w := sub_eq_zero.mp h0
    have hpos : 0 < ‖predPoly a w‖ := norm_pos_iff.mpr (h w hw.le)
    have hle : ‖predPoly a w‖ ≤ ‖w‖ * ‖predPoly a w‖ := by
      calc ‖predPoly a w‖ = ‖(ε : ℂ) * w * predRev a w‖ := by rw [← hA]
        _ = ‖w‖ * ‖predRev a w‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hε1, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_predRev_le h hw.le) (norm_nonneg _)
    nlinarith
  refine le_antisymm ?_ ?_
  · by_contra hgt
    push Not at hgt
    have hz0 : z ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at hgt
      linarith
    have hw : ‖z⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hgt
    have e := paraPoly_reciprocal a hε hz0
    rw [hz, mul_zero] at e
    exact (mul_ne_zero (pow_ne_zero _ hz0) (hin _ hw)) e
  · by_contra hlt
    push Not at hlt
    exact hin z hlt hz

/-! ### The sign-definite face: Allegretto–Piepenbrink -/

/-- The Doob identity in any gauge without zeros, valid for every sign pattern. -/
theorem toeplitzForm_eq_doob (hκ : IsEvenSeq κ) {h : Fin n → ℝ} (hh : ∀ i, h i ≠ 0) (x : Fin n → ℝ) :
    toeplitzForm κ n x = ∑ i : Fin n, (∑ j : Fin n, κ ((i : ℤ) - j) * h j) / h i * x i ^ 2 -
      (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * (h i * h j) * (x i / h i - x j / h j) ^ 2 := by
  have hsym : ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * (h i / h j) * x j ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * (h j / h i) * x i ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [← hκ, neg_sub]
  have hexp : ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * (h i * h j) * (x i / h i - x j / h j) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * (h j / h i) * x i ^ 2 +
        ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * (h i / h j) * x j ^ 2 -
          2 * toeplitzForm κ n x := by
    simp only [toeplitzForm, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have hi := hh i
    have hj := hh j
    field_simp
    ring
  have hfirst : ∑ i : Fin n, (∑ j : Fin n, κ ((i : ℤ) - j) * h j) / h i * x i ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * (h j / h i) * x i ^ 2 := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_div, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hexp, hsym, hfirst]
  ring

/-- **Allegretto–Piepenbrink on a lattice.** With nonpositive couplings, a positive supersolution certifies nonnegativity. -/
theorem toeplitzForm_nonneg_of_supersolution (hκ : IsEvenSeq κ) (hZ : ∀ d : ℤ, d ≠ 0 → κ d ≤ 0)
    {h : Fin n → ℝ} (hh : ∀ i, 0 < h i) (hs : ∀ i : Fin n, 0 ≤ ∑ j : Fin n, κ ((i : ℤ) - j) * h j)
    (x : Fin n → ℝ) : 0 ≤ toeplitzForm κ n x := by
  rw [toeplitzForm_eq_doob hκ (fun i => (hh i).ne') x]
  have h1 : 0 ≤ ∑ i : Fin n, (∑ j : Fin n, κ ((i : ℤ) - j) * h j) / h i * x i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (div_nonneg (hs i) (hh i).le) (sq_nonneg _)
  have h2 : ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * (h i * h j) * (x i / h i - x j / h j) ^ 2 ≤ 0 := by
    refine sum_nonpos fun i _ => sum_nonpos fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : (i : ℤ) - j ≠ 0 := by
        intro h0
        apply hij
        ext
        omega
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (hZ _ hne) (mul_pos (hh i) (hh j)).le) (sq_nonneg _)
  linarith

/-- **Sign-definite data have positive predictors.** With nonpositive couplings on a positive window, the predictor is nonnegative, so
`(1, a)` is a positive supersolution: the causal certificate specializes to Allegretto–Piepenbrink. -/
theorem predictor_nonneg_of_offDiag_nonpos (hZ : ∀ d : ℤ, d ≠ 0 → κ d ≤ 0) {a : Fin n → ℝ}
    (ha : IsPredictor κ n a) (hpd : ToeplitzPosDef κ n) (k : Fin n) : 0 ≤ a k := by
  set y : Fin n → ℝ := fun k => max (-a k) 0 with hy
  set p : Fin n → ℝ := fun k => max (a k) 0 with hp
  have hy0 : ∀ k, 0 ≤ y k := fun k => le_max_right _ _
  have hp0 : ∀ k, 0 ≤ p k := fun k => le_max_right _ _
  have hsplit : ∀ k, a k = p k - y k := fun k => by
    simp only [hp, hy]
    rcases le_total (a k) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  have hdisj : ∀ k, y k * p k = 0 := fun k => by
    simp only [hp, hy]
    rcases le_total (a k) 0 with h | h
    · rw [max_eq_right h, mul_zero]
    · rw [max_eq_right (by linarith : -a k ≤ 0), zero_mul]
  have hrow : 0 ≤ ∑ j : Fin n, y j * ∑ k : Fin n, κ ((j : ℤ) - k) * a k := by
    refine sum_nonneg fun j _ => ?_
    rw [ha j]
    refine mul_nonneg (hy0 j) ?_
    have hne : ((j : ℕ) : ℤ) + 1 ≠ 0 := by omega
    linarith [hZ _ hne]
  have hexp : ∑ j : Fin n, y j * ∑ k : Fin n, κ ((j : ℤ) - k) * a k =
      ∑ j : Fin n, ∑ k : Fin n, κ ((j : ℤ) - k) * y j * p k - toeplitzForm κ n y := by
    simp only [toeplitzForm, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    rw [hsplit k]
    ring
  have hneg : ∑ j : Fin n, ∑ k : Fin n, κ ((j : ℤ) - k) * y j * p k ≤ 0 := by
    refine sum_nonpos fun j _ => sum_nonpos fun k _ => ?_
    by_cases hjk : j = k
    · subst hjk
      rw [mul_assoc, hdisj, mul_zero]
    · have hne : (j : ℤ) - k ≠ 0 := by
        intro h0
        apply hjk
        ext
        omega
      rw [mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (hZ _ hne) (mul_nonneg (hy0 j) (hp0 k))
  have hT : toeplitzForm κ n y ≤ 0 := by linarith
  have hy_zero : y = 0 := by
    by_contra hne
    exact absurd (hpd y hne) (not_lt.mpr hT)
  have hk : y k = 0 := by rw [hy_zero]; rfl
  have := le_max_left (-a k) 0
  have h2 : -a k ≤ y k := this
  linarith

/-- **Frustration.** On a triangle with `κ₁ ≠ 0`, `κ₂ > 0`, every gauge without zeros has a positive Doob edge, so no gauge makes the
Doob identity a certificate. -/
theorem exists_wrong_edge {κ₁ κ₂ : ℝ} (h1 : κ₁ ≠ 0) (h2 : 0 < κ₂) {h₀ h₁ h₂ : ℝ} (h0 : h₀ ≠ 0)
    (hh1 : h₁ ≠ 0) (hh2 : h₂ ≠ 0) :
    0 < κ₁ * (h₀ * h₁) ∨ 0 < κ₁ * (h₁ * h₂) ∨ 0 < κ₂ * (h₀ * h₂) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h3, h4, h5⟩ := hcon
  have hprod : 0 < (κ₁ * (h₀ * h₁)) * (κ₁ * (h₁ * h₂)) * (κ₂ * (h₀ * h₂)) := by
    have e : (κ₁ * (h₀ * h₁)) * (κ₁ * (h₁ * h₂)) * (κ₂ * (h₀ * h₂)) =
        κ₂ * (κ₁ * (h₀ * h₁ * h₂)) ^ 2 := by ring
    rw [e]
    have : κ₁ * (h₀ * h₁ * h₂) ≠ 0 := mul_ne_zero h1 (mul_ne_zero (mul_ne_zero h0 hh1) hh2)
    positivity
  have hle : (κ₁ * (h₀ * h₁)) * (κ₁ * (h₁ * h₂)) * (κ₂ * (h₀ * h₂)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg_of_nonpos_of_nonpos h3 h4) h5
  linarith

/-- **The certificate is a sum of squares** with the margins as weights. -/
theorem exists_sum_sq_certificate (hκ : IsEvenSeq κ) :
    ∀ n : ℕ, (∀ k < n, levinsonErr κ k ≠ 0) → ∃ v : Fin n → Fin n → ℝ, ∀ x : Fin n → ℝ,
      toeplitzForm κ n x = ∑ m : Fin n, levinsonErr κ m * (∑ i : Fin n, v m i * x i) ^ 2
  | 0, _ => ⟨fun i => i.elim0, fun x => by simp [toeplitzForm]⟩
  | n + 1, h => by
    obtain ⟨v, hv⟩ := exists_sum_sq_certificate hκ n fun k hk => h k (by omega)
    have hne : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => h k (by omega)
    have ha := levinson_isPredictor hκ hne
    have hE := predErr_levinson hκ hne
    set a := levinsonPred κ n with hadef
    refine ⟨Fin.lastCases (Fin.cons 1 0) fun m =>
      Fin.cons (-∑ i : Fin n, v m i * a i) (v m), fun x => ?_⟩
    have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    have hc := toeplitzForm_cons hκ ha (x 0) (Fin.tail x)
    rw [← hx] at hc
    rw [hc, hv, hE, Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last]
    have hlast : ∑ i : Fin (n + 1), (Fin.cons 1 0 : Fin (n + 1) → ℝ) i * x i = x 0 := by
      rw [Fin.sum_univ_succ]
      simp
    have hrow : ∀ m : Fin n, ∑ i : Fin (n + 1),
        (Fin.cons (-∑ i : Fin n, v m i * a i) (v m) : Fin (n + 1) → ℝ) i * x i =
          ∑ i : Fin n, v m i * (Fin.tail x i - x 0 * a i) := fun m => by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
      have e : ∑ i : Fin n, v m i * (x i.succ - x 0 * a i) =
          ∑ i : Fin n, v m i * x i.succ - x 0 * ∑ i : Fin n, v m i * a i := by
        rw [mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun i _ => ?_
        ring
      rw [e]
      ring
    simp only [hlast, hrow]
    ring

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
