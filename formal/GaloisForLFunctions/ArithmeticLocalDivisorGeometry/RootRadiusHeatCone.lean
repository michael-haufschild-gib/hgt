import GaloisForLFunctions.RHTower.DeBruijnPolynomialGaussianAverage
import GaloisForLFunctions.HTGeometry.PolynomialHeatFactorBounds

/-!
# Heat repairs a polynomial with roots in a disc after time `32 r / degree`

Let `q` be a monic real polynomial of degree `N` all of whose complex roots lie in the closed disc
`|ρ| ≤ r`, presented as a product of real linear factors `y − ρ` (`|ρ| ≤ r`) and real quadratic
factors `y² − 2ay + b` (`a² ≤ b ≤ r²`, a conjugate pair of modulus `√b`).

**Theorem** (`coeffNonneg_forwardPolyHeat_expand_of_discFactors`).  For every heat time `s > 0` with
`32 r ≤ s N`, the even polynomial `e^{s∂_x²} q(x²)` has nonnegative Taylor coefficients.

The admissible heat depends only on the root radius and the degree.  The configuration of the
roots is arbitrary: clusters, multiple roots, roots near the positive axis and complex pairs are
all repaired at time `32r/N`.  The order `r/N` is sharp up to the constant: `(y − r)^N` needs heat
of order `r/N`.

**Proof.**  Let `H_l(y) = [w^l] q(y + w)` be the Hasse derivative and `g_s` the Gaussian of
variance `2s`, with moments `μ_m = ∫ g_s u^{2m} = (2m)! s^m/m!`.  Then
`(2l)! s^l/l! · [x^{2l}] e^{s∂²} q(x²) = ∫ g_s(u) u^{2l} H_l(u²) du` (`heatCoeff_mul_eq_integral`).
* For `y ≥ r`, `q(y + w)` dominates `(w + y − r)^N` coefficientwise
  (`coeffDom_taylor_prod`), so `H_l(y) ≥ \binom{N}{l} (y − r)^{N−l}`.
* For real `y`, `|H_l(y)| ≤ \binom{N}{l} (|y| + r)^{N−l}` (`coeffAbsLe_taylor_prod`).
Splitting `y ≥ 2r`, `r ≤ y < 2r`, `y < r` gives, for `y ≥ 0` and `l ≤ N`,
`2^{N−l} y^l H_l(y) ≥ \binom{N}{l} (y^N − (2r)^N − (4r)^{N−l} y^l)` (`pointwise_lower`).
Integrating, the coefficient is nonnegative once `(2r)^N + (4r)^{N−l} μ_l ≤ μ_N`, which holds for
`l < N` because `μ_N/μ_l = ∏_{l ≤ m < N} 2s(2m+1) ≥ (2s)^{N−l} N!/l! ≥ (2sN/e)^{N−l}`
(`moment_numerics`).  For `l ≥ N` the coefficient is a nonnegative combination of `q_N = 1`.
-/

open Polynomial MeasureTheory Finset Filter
open GaloisForLFunctions.HTGeometry
open RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section

/-! ## Factors with roots in a disc -/

/-- A monic real factor whose complex roots lie in the closed disc of radius `r`: a linear factor
`y − ρ` with `|ρ| ≤ r`, or a quadratic `y² − 2ay + b` with `a² ≤ b ≤ r²`. -/
inductive DiscFactor (r : ℝ) : ℝ[X] → Prop
  | lin (ρ : ℝ) (hρ : |ρ| ≤ r) : DiscFactor r (X - C ρ)
  | quad (a b : ℝ) (hab : a ^ 2 ≤ b) (hb : b ≤ r ^ 2) :
      DiscFactor r (X ^ 2 - C (2 * a) * X + C b)

theorem quad_monic (a b : ℝ) : (X ^ 2 - C (2 * a) * X + C b : ℝ[X]).Monic := by
  have h : (X ^ 2 - C (2 * a) * X + C b : ℝ[X]) = X ^ 2 + (C b - C (2 * a) * X) := by ring
  rw [h]
  refine (monic_X_pow 2).add_of_left ?_
  rw [degree_X_pow]
  calc degree (C b - C (2 * a) * X) ≤ 1 := by compute_degree
    _ < 2 := by norm_num

theorem DiscFactor.monic {r : ℝ} {F : ℝ[X]} (hF : DiscFactor r F) : F.Monic := by
  cases hF with
  | lin ρ _ => exact monic_X_sub_C ρ
  | quad a b _ _ => exact quad_monic a b

theorem monic_prod_of_discFactors {r : ℝ} :
    ∀ {L : List ℝ[X]}, (∀ F ∈ L, DiscFactor r F) → L.prod.Monic
  | [], _ => by simp
  | F :: L, hL => by
    rw [List.prod_cons]
    exact (hL F (by simp)).monic.mul (monic_prod_of_discFactors fun G hG => hL G (by simp [hG]))

/-! ## Coefficientwise comparison -/

/-- `B` has nonnegative coefficients bounded by those of `A`. -/
def CoeffDom (A B : ℝ[X]) : Prop := ∀ n, 0 ≤ B.coeff n ∧ B.coeff n ≤ A.coeff n

/-- The coefficients of `A` are bounded in absolute value by those of `B`. -/
def CoeffAbsLe (A B : ℝ[X]) : Prop := ∀ n, |A.coeff n| ≤ B.coeff n

theorem CoeffDom.mul {A₁ A₂ B₁ B₂ : ℝ[X]} (h₁ : CoeffDom A₁ B₁) (h₂ : CoeffDom A₂ B₂) :
    CoeffDom (A₁ * A₂) (B₁ * B₂) := fun n => by
  rw [coeff_mul, coeff_mul]
  refine ⟨sum_nonneg fun x _ => mul_nonneg (h₁ x.1).1 (h₂ x.2).1,
    sum_le_sum fun x _ => mul_le_mul (h₁ x.1).2 (h₂ x.2).2 (h₂ x.2).1
      ((h₁ x.1).1.trans (h₁ x.1).2)⟩

theorem CoeffAbsLe.mul {A₁ A₂ B₁ B₂ : ℝ[X]} (h₁ : CoeffAbsLe A₁ B₁) (h₂ : CoeffAbsLe A₂ B₂) :
    CoeffAbsLe (A₁ * A₂) (B₁ * B₂) := fun n => by
  rw [coeff_mul, coeff_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (h₁ x.1) (h₂ x.2) (abs_nonneg _) ((abs_nonneg _).trans (h₁ x.1))

/-- Coefficients of `y² + αy + β`. -/
theorem coeff_quadForm (α β : ℝ) (n : ℕ) : (X ^ 2 + C α * X + C β : ℝ[X]).coeff n =
    if n = 0 then β else if n = 1 then α else if n = 2 then 1 else 0 := by
  rcases n with _ | _ | _ | n <;> simp [coeff_X, coeff_C, coeff_X_pow]

theorem sq_X_add_C (c : ℝ) : (X + C c) ^ 2 = (X ^ 2 + C (2 * c) * X + C (c ^ 2) : ℝ[X]) := by
  simp only [map_mul, map_pow, map_ofNat]; ring

theorem coeff_linForm (c : ℝ) (n : ℕ) : (X + C c : ℝ[X]).coeff n =
    if n = 0 then c else if n = 1 then 1 else 0 := by
  rcases n with _ | _ | n <;> simp [coeff_X, coeff_C]

theorem taylor_lin (y ρ : ℝ) : taylor y (X - C ρ) = X + C (y - ρ) := by
  rw [taylor_apply, sub_comp, X_comp, C_comp, C_sub]; ring

theorem taylor_quad (y a b : ℝ) : taylor y (X ^ 2 - C (2 * a) * X + C b) =
    X ^ 2 + C (2 * (y - a)) * X + C (y ^ 2 - 2 * a * y + b) := by
  rw [taylor_apply]
  simp only [add_comp, sub_comp, mul_comp, pow_comp, X_comp, C_comp]
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat]
  ring

/-- **Domination of one factor.**  For `y ≥ r`, `F(y + w)` dominates `(w + y − r)^{deg F}`. -/
theorem DiscFactor.coeffDom_taylor {r y : ℝ} (hr : 0 ≤ r) (hy : r ≤ y) {F : ℝ[X]}
    (hF : DiscFactor r F) : CoeffDom (taylor y F) ((X + C (y - r)) ^ F.natDegree) := by
  cases hF with
  | lin ρ hρ =>
    rw [natDegree_X_sub_C, pow_one, taylor_lin]
    have hρ' : ρ ≤ r := (le_abs_self ρ).trans hρ
    intro n
    rw [coeff_linForm, coeff_linForm]
    split_ifs <;> constructor <;> linarith
  | quad a b hab hb =>
    have hdeg : (X ^ 2 - C (2 * a) * X + C b : ℝ[X]).natDegree = 2 := by compute_degree!
    rw [hdeg, sq_X_add_C, taylor_quad]
    have ha : |a| ≤ r := abs_le_of_sq_le_sq (hab.trans hb) hr
    have ha' : a ≤ r := (le_abs_self a).trans ha
    intro n
    rw [coeff_quadForm, coeff_quadForm]
    split_ifs
    · refine ⟨sq_nonneg _, ?_⟩
      nlinarith [mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr ha'), sq_nonneg (a - r),
        abs_mul_abs_self a, abs_nonneg a]
    · constructor <;> linarith
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨le_rfl, le_rfl⟩

/-- **Absolute bound for one factor.**  `|[w^n] F(y + w)| ≤ [w^n] (w + |y| + r)^{deg F}`. -/
theorem DiscFactor.coeffAbsLe_taylor {r : ℝ} (hr : 0 ≤ r) (y : ℝ) {F : ℝ[X]}
    (hF : DiscFactor r F) : CoeffAbsLe (taylor y F) ((X + C (|y| + r)) ^ F.natDegree) := by
  cases hF with
  | lin ρ hρ =>
    rw [natDegree_X_sub_C, pow_one, taylor_lin]
    intro n
    rw [coeff_linForm, coeff_linForm]
    split_ifs
    · exact (abs_sub _ _).trans (by linarith)
    · simp
    · simp
  | quad a b hab hb =>
    have hdeg : (X ^ 2 - C (2 * a) * X + C b : ℝ[X]).natDegree = 2 := by compute_degree!
    rw [hdeg, sq_X_add_C, taylor_quad]
    have ha : |a| ≤ r := abs_le_of_sq_le_sq (hab.trans hb) hr
    have hb' : b ≤ r ^ 2 := hb
    intro n
    rw [coeff_quadForm, coeff_quadForm]
    split_ifs
    · have h0 : 0 ≤ y ^ 2 - 2 * a * y + b := by nlinarith [sq_nonneg (y - a)]
      rw [abs_of_nonneg h0]
      -- `−2ay ≤ 2|a||y| ≤ 2r|y|` and `b ≤ r²`
      have h1 : -(a * y) ≤ |a| * |y| := by rw [← abs_mul]; exact neg_le_abs _
      have h2 : |a| * |y| ≤ r * |y| := mul_le_mul_of_nonneg_right ha (abs_nonneg y)
      have h3 : (|y| + r) ^ 2 = y ^ 2 + 2 * r * |y| + r ^ 2 := by rw [add_sq, sq_abs]; ring
      rw [h3]
      linarith
    · rw [abs_mul, abs_two]
      have := abs_sub y a
      linarith
    · simp
    · simp

theorem coeffDom_taylor_prod {r y : ℝ} (hr : 0 ≤ r) (hy : r ≤ y) :
    ∀ {L : List ℝ[X]}, (∀ F ∈ L, DiscFactor r F) →
      CoeffDom (taylor y L.prod) ((X + C (y - r)) ^ L.prod.natDegree)
  | [], _ => by
    intro n
    simp only [List.prod_nil, taylor_one, natDegree_one, pow_zero, map_one]
    rw [coeff_one]
    split_ifs <;> simp
  | F :: L, hL => by
    have hF := hL F (by simp)
    have hL' : ∀ G ∈ L, DiscFactor r G := fun G hG => hL G (by simp [hG])
    rw [List.prod_cons, taylor_mul, hF.monic.natDegree_mul (monic_prod_of_discFactors hL'), pow_add]
    exact (hF.coeffDom_taylor hr hy).mul (coeffDom_taylor_prod hr hy hL')

theorem coeffAbsLe_taylor_prod {r : ℝ} (hr : 0 ≤ r) (y : ℝ) :
    ∀ {L : List ℝ[X]}, (∀ F ∈ L, DiscFactor r F) →
      CoeffAbsLe (taylor y L.prod) ((X + C (|y| + r)) ^ L.prod.natDegree)
  | [], _ => by
    intro n
    simp only [List.prod_nil, taylor_one, natDegree_one, pow_zero, map_one]
    rw [coeff_one]
    split_ifs <;> simp
  | F :: L, hL => by
    have hF := hL F (by simp)
    have hL' : ∀ G ∈ L, DiscFactor r G := fun G hG => hL G (by simp [hG])
    rw [List.prod_cons, taylor_mul, hF.monic.natDegree_mul (monic_prod_of_discFactors hL'), pow_add]
    exact (hF.coeffAbsLe_taylor hr y).mul (coeffAbsLe_taylor_prod hr y hL')

/-! ## Root estimates for the Hasse derivatives -/

/-- For `y ≥ r`: `H_l(y) ≥ \binom{N}{l} (y − r)^{N−l}`. -/
theorem hasseDeriv_eval_lower {r y : ℝ} (hr : 0 ≤ r) (hy : r ≤ y) {L : List ℝ[X]}
    (hL : ∀ F ∈ L, DiscFactor r F) (l : ℕ) :
    (L.prod.natDegree.choose l : ℝ) * (y - r) ^ (L.prod.natDegree - l) ≤
      (hasseDeriv l L.prod).eval y := by
  rw [← taylor_coeff]
  have h := (coeffDom_taylor_prod hr hy hL l).2
  rwa [coeff_X_add_C_pow, mul_comm] at h

/-- For real `y`: `|H_l(y)| ≤ \binom{N}{l} (|y| + r)^{N−l}`. -/
theorem abs_hasseDeriv_eval_le {r : ℝ} (hr : 0 ≤ r) (y : ℝ) {L : List ℝ[X]}
    (hL : ∀ F ∈ L, DiscFactor r F) (l : ℕ) :
    |(hasseDeriv l L.prod).eval y| ≤
      (L.prod.natDegree.choose l : ℝ) * (|y| + r) ^ (L.prod.natDegree - l) := by
  rw [← taylor_coeff]
  have h := coeffAbsLe_taylor_prod hr y hL l
  rwa [coeff_X_add_C_pow, mul_comm] at h

/-- **Pointwise lower bound.**  For `y ≥ 0` and `l ≤ N`:
`\binom{N}{l} (y^N − (2r)^N − (4r)^{N−l} y^l) ≤ 2^{N−l} y^l H_l(y)`. -/
theorem pointwise_lower {r : ℝ} (hr : 0 ≤ r) {L : List ℝ[X]} (hL : ∀ F ∈ L, DiscFactor r F)
    {l : ℕ} (hl : l ≤ L.prod.natDegree) {y : ℝ} (hy : 0 ≤ y) :
    (L.prod.natDegree.choose l : ℝ) * (y ^ L.prod.natDegree - (2 * r) ^ L.prod.natDegree -
        (4 * r) ^ (L.prod.natDegree - l) * y ^ l) ≤
      2 ^ (L.prod.natDegree - l) * (y ^ l * (hasseDeriv l L.prod).eval y) := by
  set N := L.prod.natDegree with hNdef
  set d := N - l with hd
  have hN : N = l + d := by omega
  set c : ℝ := (N.choose l : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  set H := (hasseDeriv l L.prod).eval y with hH
  have hyl : 0 ≤ y ^ l := pow_nonneg hy l
  have h4 : (4 * r) ^ d = 2 ^ d * (2 * r) ^ d := by rw [← mul_pow]; ring
  have hyN : y ^ N = y ^ l * y ^ d := by rw [hN, pow_add]
  have hpos4 : 0 ≤ (4 * r) ^ d * y ^ l := mul_nonneg (pow_nonneg (by linarith) d) hyl
  rcases le_or_gt r y with hry | hry
  · have hlow : c * (y - r) ^ d ≤ H := hasseDeriv_eval_lower hr hry hL l
    rcases le_or_gt (2 * r) y with h2r | h2r
    · -- far region: `2(y − r) ≥ y`
      have hpow : y ^ d ≤ (2 * (y - r)) ^ d := pow_le_pow_left₀ hy (by linarith) d
      have hpos2 : 0 ≤ (2 * r) ^ N := pow_nonneg (by linarith) N
      calc c * (y ^ N - (2 * r) ^ N - (4 * r) ^ d * y ^ l)
          ≤ c * y ^ N := mul_le_mul_of_nonneg_left (by linarith) hc0
        _ = c * (y ^ l * y ^ d) := by rw [hyN]
        _ ≤ c * (y ^ l * (2 * (y - r)) ^ d) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hyl) hc0
        _ = 2 ^ d * (y ^ l * (c * (y - r) ^ d)) := by rw [mul_pow]; ring
        _ ≤ 2 ^ d * (y ^ l * H) := by gcongr
    · -- middle region: `H ≥ 0`, `y^N ≤ (2r)^N`
      have hH0 : 0 ≤ H := le_trans (mul_nonneg hc0 (pow_nonneg (by linarith) d)) hlow
      have hyN2 : y ^ N ≤ (2 * r) ^ N := pow_le_pow_left₀ hy h2r.le N
      calc c * (y ^ N - (2 * r) ^ N - (4 * r) ^ d * y ^ l) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)
        _ ≤ 2 ^ d * (y ^ l * H) := by positivity
  · -- near region: `|H| ≤ c (2r)^d`
    have hup : |H| ≤ c * (|y| + r) ^ d := abs_hasseDeriv_eval_le hr y hL l
    rw [abs_of_nonneg hy] at hup
    have hup2 : |H| ≤ c * (2 * r) ^ d :=
      hup.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) d) hc0)
    have hHlow : -(c * (2 * r) ^ d) ≤ H := by
      have := neg_abs_le H; linarith
    have hyN2 : y ^ N ≤ (2 * r) ^ N := pow_le_pow_left₀ hy (by linarith) N
    have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
    calc c * (y ^ N - (2 * r) ^ N - (4 * r) ^ d * y ^ l)
        ≤ c * (-((4 * r) ^ d * y ^ l)) := mul_le_mul_of_nonneg_left (by linarith) hc0
      _ = 2 ^ d * (y ^ l * (-(c * (2 * r) ^ d))) := by rw [h4]; ring
      _ ≤ 2 ^ d * (y ^ l * H) := by gcongr

/-! ## Gaussian moments -/

/-- The Gaussian moment `μ_m = ∫ g_s u^{2m} = (2m)! s^m/m!`. -/
def gaussMoment (s : ℝ) (m : ℕ) : ℝ := ((2 * m).factorial : ℝ) * s ^ m / m.factorial

theorem gaussMoment_zero (s : ℝ) : gaussMoment s 0 = 1 := by simp [gaussMoment]

theorem gaussMoment_succ (s : ℝ) (m : ℕ) :
    gaussMoment s (m + 1) = gaussMoment s m * (2 * s * (2 * m + 1)) := by
  unfold gaussMoment
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ]
  have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  push_cast
  field_simp
  ring

theorem gaussMoment_add (s : ℝ) (l d : ℕ) :
    gaussMoment s (l + d) = gaussMoment s l * ∏ i ∈ range d, (2 * s * (2 * ((l + i : ℕ) : ℝ) + 1)) := by
  induction d with
  | zero => simp
  | succ d ih => rw [← add_assoc, gaussMoment_succ, ih, prod_range_succ]; ring

theorem integral_gaussDensity_mul_pow_two_mul {s : ℝ} (hs : 0 < s) (m : ℕ) :
    ∫ u : ℝ, gaussDensity s u * u ^ (2 * m) = gaussMoment s m :=
  integral_gaussDensity_mul_pow_even hs m

/-- `(l + d)^d ≤ e^d (l + d)!/l!`. -/
theorem pow_le_exp_mul_factorial_div (l d : ℕ) :
    ((l + d : ℕ) : ℝ) ^ d ≤ Real.exp d * ((l + d).factorial / l.factorial) := by
  have hl : (0 : ℝ) < l.factorial := by exact_mod_cast Nat.factorial_pos l
  induction d with
  | zero =>
    simp only [add_zero, pow_zero, Nat.cast_zero, Real.exp_zero, one_mul]
    rw [div_self hl.ne']
  | succ d ih =>
    set n : ℕ := l + d with hn
    have hstep : ((n + 1 : ℕ) : ℝ) ^ d ≤ Real.exp 1 * ((n : ℕ) : ℝ) ^ d := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · have hd0 : d = 0 := by omega
        subst hd0
        simp only [pow_zero, mul_one]
        linarith [Real.add_one_le_exp 1]
      · have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos
        have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
        have hratio : ((n + 1 : ℕ) : ℝ) = n * (1 + 1 / n) := by
          push_cast; field_simp
        rw [hratio, mul_pow, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hnpos.le d)
        calc (1 + 1 / (n : ℝ)) ^ d ≤ (1 + 1 / (n : ℝ)) ^ n :=
              pow_le_pow_right₀ (by linarith) (by omega)
          _ ≤ Real.exp (1 / n) ^ n := by
              gcongr
              linarith [Real.add_one_le_exp (1 / (n : ℝ))]
          _ = Real.exp 1 := by
              rw [← Real.exp_nat_mul]; congr 1; field_simp
    have hn1 : l + (d + 1) = n + 1 := by omega
    rw [hn1, pow_succ, Nat.factorial_succ, Nat.cast_mul,
      show ((d + 1 : ℕ) : ℝ) = d + 1 by push_cast; ring, Real.exp_add]
    calc ((n + 1 : ℕ) : ℝ) ^ d * ((n + 1 : ℕ) : ℝ)
        ≤ (Real.exp 1 * (n : ℝ) ^ d) * ((n + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hstep (Nat.cast_nonneg _)
      _ ≤ (Real.exp 1 * (Real.exp d * (n.factorial / l.factorial))) * ((n + 1 : ℕ) : ℝ) := by
          gcongr
      _ = Real.exp d * Real.exp 1 * (((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) / l.factorial) := by
          ring

/-- **Moment ratio.**  For `d ≥ 1`, `N = l + d` and `32 r ≤ s N`:
`2 (4r)^d ≤ ∏_{i<d} 2s(2(l+i)+1)`. -/
theorem prod_moment_ratio_lower {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) {l d : ℕ} (hd : 1 ≤ d)
    (hsN : 32 * r ≤ s * ((l + d : ℕ) : ℝ)) :
    2 * (4 * r) ^ d ≤ ∏ i ∈ range d, (2 * s * (2 * ((l + i : ℕ) : ℝ) + 1)) := by
  have hl : (0 : ℝ) < l.factorial := by exact_mod_cast Nat.factorial_pos l
  -- each factor is at least `2s(l + i + 1)`
  have hge : (2 * s) ^ d * ((l + d).factorial / l.factorial : ℝ) ≤
      ∏ i ∈ range d, (2 * s * (2 * ((l + i : ℕ) : ℝ) + 1)) := by
    have hprod : ((l + d).factorial / l.factorial : ℝ) = ∏ i ∈ range d, ((l + i + 1 : ℕ) : ℝ) := by
      clear hsN hd
      induction d with
      | zero => simp [hl.ne']
      | succ d ih =>
        rw [prod_range_succ, ← ih, show l + (d + 1) = l + d + 1 by omega, Nat.factorial_succ]
        push_cast; field_simp
    rw [hprod, show (2 * s) ^ d = ∏ _i ∈ range d, (2 * s) by rw [prod_const, card_range],
      ← prod_mul_distrib]
    refine prod_le_prod (fun i _ => by positivity) fun i _ => ?_
    push_cast
    nlinarith [hs.le]
  have hexp := pow_le_exp_mul_factorial_div l d
  have hN : (0 : ℝ) < ((l + d : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < l + d)
  have he : Real.exp (d : ℝ) = Real.exp 1 ^ d := by rw [← Real.exp_nat_mul, mul_one]
  have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  -- `(64 r)^d ≤ (2sN)^d ≤ e^d (2s)^d N!/l!`
  have hchain : (64 * r) ^ d ≤ Real.exp 1 ^ d * ((2 * s) ^ d * ((l + d).factorial / l.factorial)) := by
    calc (64 * r) ^ d ≤ (2 * s * ((l + d : ℕ) : ℝ)) ^ d :=
          pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = (2 * s) ^ d * ((l + d : ℕ) : ℝ) ^ d := mul_pow _ _ _
      _ ≤ (2 * s) ^ d * (Real.exp d * ((l + d).factorial / l.factorial)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by rw [he]; ring
  -- `2 (4r)^d ≤ (64 r / e)^d` since `(16/e)^d ≥ 16/3 ≥ 2`
  have h16 : 2 * (4 * r) ^ d * Real.exp 1 ^ d ≤ (64 * r) ^ d := by
    -- `2 e^d ≤ 2^d 3^d = 6^d ≤ 16^d`
    have hbase : 2 * Real.exp 1 ^ d ≤ 16 ^ d := by
      have h2d : (2 : ℝ) ≤ 2 ^ d := le_self_pow₀ (by norm_num) (by omega)
      calc 2 * Real.exp 1 ^ d ≤ 2 ^ d * 3 ^ d :=
            mul_le_mul h2d (pow_le_pow_left₀ he0.le he3.le d) (by positivity) (by positivity)
        _ = 6 ^ d := by rw [← mul_pow]; norm_num
        _ ≤ 16 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    calc 2 * (4 * r) ^ d * Real.exp 1 ^ d = (2 * Real.exp 1 ^ d) * (4 * r) ^ d := by ring
      _ ≤ 16 ^ d * (4 * r) ^ d := mul_le_mul_of_nonneg_right hbase (pow_nonneg (by linarith) d)
      _ = (64 * r) ^ d := by rw [← mul_pow]; ring
  have hed : 0 < Real.exp 1 ^ d := pow_pos he0 d
  have h2 : 2 * (4 * r) ^ d ≤ (2 * s) ^ d * ((l + d).factorial / l.factorial) := by
    refine le_of_mul_le_mul_right ?_ hed
    calc 2 * (4 * r) ^ d * Real.exp 1 ^ d ≤ (64 * r) ^ d := h16
      _ ≤ Real.exp 1 ^ d * ((2 * s) ^ d * ((l + d).factorial / l.factorial)) := hchain
      _ = (2 * s) ^ d * ((l + d).factorial / l.factorial) * Real.exp 1 ^ d := by ring
  exact h2.trans hge

/-- **Moment numerics.**  For `l < N` and `32 r ≤ s N`: `(2r)^N + (4r)^{N−l} μ_l ≤ μ_N`. -/
theorem moment_numerics {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) {l N : ℕ} (hlN : l < N)
    (hsN : 32 * r ≤ s * N) :
    (2 * r) ^ N + (4 * r) ^ (N - l) * gaussMoment s l ≤ gaussMoment s N := by
  have hμl : 0 ≤ gaussMoment s l := by unfold gaussMoment; positivity
  have h1 : 2 * (4 * r) ^ (N - l) * gaussMoment s l ≤ gaussMoment s N := by
    have hN : N = l + (N - l) := by omega
    have hsN' : 32 * r ≤ s * ((l + (N - l) : ℕ) : ℝ) := by rwa [← hN]
    have hp := prod_moment_ratio_lower hr hs (l := l) (d := N - l) (by omega) hsN'
    rw [hN, gaussMoment_add]
    rw [show l + (N - l) - l = N - l by omega]
    have := mul_le_mul_of_nonneg_left hp hμl
    linarith
  have h2 : 2 * (2 * r) ^ N ≤ gaussMoment s N := by
    have hsN' : 32 * r ≤ s * ((0 + N : ℕ) : ℝ) := by simpa using hsN
    have hp := prod_moment_ratio_lower hr hs (l := 0) (d := N) (by omega) hsN'
    have hle : (2 * r) ^ N ≤ (4 * r) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    have e : gaussMoment s N = gaussMoment s (0 + N) := by rw [zero_add]
    rw [e, gaussMoment_add, gaussMoment_zero, one_mul]
    linarith
  linarith

/-! ## The heated coefficient as a Gaussian integral -/

theorem eval_hasse_mul_eq_sum (q : ℝ[X]) (l : ℕ) (u : ℝ) :
    u ^ (2 * l) * (hasseDeriv l q).eval (u ^ 2) =
      ∑ k ∈ range (q.natDegree + 1), ((k + l).choose l : ℝ) * q.coeff (k + l) * u ^ (2 * (l + k)) := by
  have hdeg : (hasseDeriv l q).natDegree < q.natDegree + 1 :=
    lt_of_le_of_lt (natDegree_hasseDeriv_le _ _) (by omega)
  rw [eval_eq_sum_range' hdeg, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [hasseDeriv_coeff, ← pow_mul, show 2 * (l + k) = 2 * l + 2 * k by ring, pow_add]
  ring

theorem integrable_gaussDensity_mul_hasse {s : ℝ} (hs : 0 < s) (q : ℝ[X]) (l : ℕ) :
    Integrable fun u : ℝ => gaussDensity s u * (u ^ (2 * l) * (hasseDeriv l q).eval (u ^ 2)) := by
  simp_rw [eval_hasse_mul_eq_sum, mul_sum]
  exact integrable_finsetSum _ fun k _ =>
    ((integrable_gaussDensity_mul_pow hs (2 * (l + k))).const_mul
      (((k + l).choose l : ℝ) * q.coeff (k + l))).congr (Eventually.of_forall fun u => by ring)

theorem integral_gaussDensity_mul_hasse {s : ℝ} (hs : 0 < s) (q : ℝ[X]) (l : ℕ) :
    ∫ u : ℝ, gaussDensity s u * (u ^ (2 * l) * (hasseDeriv l q).eval (u ^ 2)) =
      ∑ k ∈ range (q.natDegree + 1),
        ((k + l).choose l : ℝ) * q.coeff (k + l) * gaussMoment s (l + k) := by
  simp_rw [eval_hasse_mul_eq_sum, mul_sum]
  rw [integral_finsetSum _ fun k _ =>
    ((integrable_gaussDensity_mul_pow hs (2 * (l + k))).const_mul
      (((k + l).choose l : ℝ) * q.coeff (k + l))).congr (Eventually.of_forall fun u => by ring)]
  refine sum_congr rfl fun k _ => ?_
  rw [← integral_gaussDensity_mul_pow_two_mul hs, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  ring

/-- **The heated coefficient as a Gaussian integral.**
`(2l)! s^l/l! · [x^{2l}] e^{s∂²} q(x²) = ∫ g_s(u) u^{2l} H_l(u²) du`. -/
theorem heatCoeff_mul_eq_integral {s : ℝ} (hs : 0 < s) (q : ℝ[X]) (l : ℕ) :
    ((2 * l).factorial : ℝ) * s ^ l / l.factorial * (forwardPolyHeat s (expand ℝ 2 q)).coeff (2 * l) =
      ∫ u : ℝ, gaussDensity s u * (u ^ (2 * l) * (hasseDeriv l q).eval (u ^ 2)) := by
  rw [integral_gaussDensity_mul_hasse hs, coeff_forwardPolyHeat_expand_two s q l (N := q.natDegree + 1)
    (by omega), mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.cast_choose ℝ (show l ≤ k + l by omega), show k + l - l = k by omega, add_comm k l]
  unfold gaussMoment
  have hl : ((2 * l).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hl' : (l.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hlk : ((l + k).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [show 2 * (l + k) = 2 * l + 2 * k by ring, pow_add]
  field_simp

/-! ## The theorem -/

/-- **Heat repairs every polynomial with roots in a disc after time `32 r / degree`.** -/
theorem coeffNonneg_forwardPolyHeat_expand_of_discFactors {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    {L : List ℝ[X]} (hL : ∀ F ∈ L, DiscFactor r F) (hsN : 32 * r ≤ s * L.prod.natDegree) :
    CoeffNonneg (forwardPolyHeat s (expand ℝ 2 L.prod)) := by
  set q := L.prod with hq
  set N := q.natDegree with hNdef
  have hmon : q.Monic := monic_prod_of_discFactors hL
  intro n
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' n
  · by_cases hlN : l < N
    · have hpos : 0 < ((2 * l).factorial : ℝ) * s ^ l / l.factorial := by positivity
      have hI := heatCoeff_mul_eq_integral hs q l
      set c : ℝ := (N.choose l : ℝ) with hc
      have hc0 : 0 ≤ c := Nat.cast_nonneg _
      have hint1 := integrable_gaussDensity_mul_pow hs (2 * N)
      have hint2 := integrable_gaussDensity_mul_pow hs (2 * l)
      have hint0 : Integrable (fun u : ℝ => gaussDensity s u) := by
        simpa using integrable_gaussDensity_mul_pow hs 0
      have hone : ∫ u : ℝ, gaussDensity s u = 1 := by
        simpa [gaussMoment] using integral_gaussDensity_mul_pow_two_mul hs 0
      -- the lower comparison function and its integral
      have e : (fun u : ℝ => gaussDensity s u * (c * ((u ^ 2) ^ N - (2 * r) ^ N -
          (4 * r) ^ (N - l) * (u ^ 2) ^ l))) = fun u =>
          c * (gaussDensity s u * u ^ (2 * N)) - c * (2 * r) ^ N * gaussDensity s u -
            c * (4 * r) ^ (N - l) * (gaussDensity s u * u ^ (2 * l)) := by
        funext u; rw [← pow_mul, ← pow_mul]; ring
      have hFint : Integrable (fun u : ℝ => gaussDensity s u * (c * ((u ^ 2) ^ N - (2 * r) ^ N -
          (4 * r) ^ (N - l) * (u ^ 2) ^ l))) := by
        rw [e]; exact ((hint1.const_mul _).sub (hint0.const_mul _)).sub (hint2.const_mul _)
      have hFval : ∫ u : ℝ, gaussDensity s u * (c * ((u ^ 2) ^ N - (2 * r) ^ N -
          (4 * r) ^ (N - l) * (u ^ 2) ^ l)) =
          c * (gaussMoment s N - (2 * r) ^ N - (4 * r) ^ (N - l) * gaussMoment s l) := by
        have hAB : Integrable (fun u : ℝ => c * (gaussDensity s u * u ^ (2 * N)) -
            c * (2 * r) ^ N * gaussDensity s u) := (hint1.const_mul c).sub (hint0.const_mul _)
        rw [e, integral_sub hAB (hint2.const_mul _),
          integral_sub (hint1.const_mul c) (hint0.const_mul _), integral_const_mul,
          integral_const_mul, integral_const_mul, hone, integral_gaussDensity_mul_pow_two_mul hs,
          integral_gaussDensity_mul_pow_two_mul hs]
        ring
      have hmono : ∫ u : ℝ, gaussDensity s u * (c * ((u ^ 2) ^ N - (2 * r) ^ N -
          (4 * r) ^ (N - l) * (u ^ 2) ^ l)) ≤
          ∫ u : ℝ, 2 ^ (N - l) * (gaussDensity s u * (u ^ (2 * l) * (hasseDeriv l q).eval (u ^ 2))) := by
        refine integral_mono hFint ((integrable_gaussDensity_mul_hasse hs q l).const_mul _)
          fun u => ?_
        have hg := (gaussDensity_pos hs u).le
        have hp := pointwise_lower hr hL hlN.le (sq_nonneg u)
        rw [← hq, ← hNdef] at hp
        have hul : (u ^ 2) ^ l = u ^ (2 * l) := by rw [← pow_mul]
        rw [hul] at hp
        calc gaussDensity s u * (c * ((u ^ 2) ^ N - (2 * r) ^ N - (4 * r) ^ (N - l) * (u ^ 2) ^ l))
            ≤ gaussDensity s u * (2 ^ (N - l) * (u ^ (2 * l) * (hasseDeriv l q).eval (u ^ 2))) := by
              rw [hul]; exact mul_le_mul_of_nonneg_left hp hg
          _ = 2 ^ (N - l) * (gaussDensity s u * (u ^ (2 * l) * (hasseDeriv l q).eval (u ^ 2))) := by
              ring
      rw [hFval, integral_const_mul] at hmono
      have hnum := moment_numerics hr hs hlN hsN
      have hI0 : 0 ≤ ∫ u : ℝ, gaussDensity s u * (u ^ (2 * l) * (hasseDeriv l q).eval (u ^ 2)) := by
        have h2 : (0 : ℝ) < 2 ^ (N - l) := by positivity
        have hlhs : 0 ≤ c * (gaussMoment s N - (2 * r) ^ N - (4 * r) ^ (N - l) * gaussMoment s l) :=
          mul_nonneg hc0 (by linarith)
        exact (mul_nonneg_iff_of_pos_left h2).mp (hlhs.trans hmono)
      rw [← hI] at hI0
      exact (mul_nonneg_iff_of_pos_left hpos).mp hI0
    · rw [coeff_forwardPolyHeat_expand_two s q l (N := N + 1) (by omega)]
      refine sum_nonneg fun k _ => mul_nonneg (by positivity) ?_
      rcases (show N ≤ l + k by omega).eq_or_lt with h | h
      · rw [← h, hmon.coeff_natDegree]; exact zero_le_one
      · rw [coeff_eq_zero_of_natDegree_lt h]
  · rw [coeff_forwardPolyHeat_expand_two_odd]

end

end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
