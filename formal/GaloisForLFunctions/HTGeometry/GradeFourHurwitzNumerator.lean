import GaloisForLFunctions.HTGeometry.PermutohedralDeletionReflection
import GaloisForLFunctions.HTGeometry.GradeThreeCausalGreenFormation
import GaloisForLFunctions.RHTower.GibbsQuarticStability

/-!
# The grade-four formation numerator and its Hurwitz stability

For four grades with elementary symmetric functions `e_1, …, e_4` the formation numerator is
`P_4 = (2z + e_1) Q_4` with
`Q_4 = 6z⁴ + 12e_1z³ + (8e_1² + 2e_2)z² + (2e_1³ + 2e_1e_2)z + (e_1²e_2 - e_1e_3 + e_4)`
`(GFH.9)`–`(GFH.10)`; it is computed from the deletion law `N_4 = Σ_i (-1)^i N_3(λ̂_i) E_{4,i}` with
`P_3 = 2z + λ_1 + λ_2 + λ_3` and the explicit incidence factors
`E_{4,i} = (z + λ_i) Π_{j ≠ i} (z + λ_i + λ_j) Π_{j ≠ i} (z + e_1 - λ_j)` `(GFH.11)`.

For positive grades all coefficients of `Q_4` are positive (`e_1e_2 > e_3`, `(GFH.14)`), the first
Hurwitz minor is `12e_1(7e_1² + e_2)` `(GFH.17)`, and the decisive minor is
`24e_1²(7e_1⁴ + 2e_1²e_2 + e_2² + 6e_1e_3 - 6e_4) > 0` since `e_2² ≥ 6e_4` `(GFH.18)`.  The quartic
Routh–Hurwitz criterion then places every zero of `P_4` in `Re z < 0` (Theorem 4.1).
-/

open MvPolynomial Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace Permutohedral

/-- The elementary symmetric functions of four grades. -/
def esymm1 {R : Type*} [CommRing R] (l : Fin 4 → R) : R := l 0 + l 1 + l 2 + l 3

def esymm2 {R : Type*} [CommRing R] (l : Fin 4 → R) : R :=
  l 0 * l 1 + l 0 * l 2 + l 0 * l 3 + l 1 * l 2 + l 1 * l 3 + l 2 * l 3

def esymm3 {R : Type*} [CommRing R] (l : Fin 4 → R) : R :=
  l 0 * l 1 * l 2 + l 0 * l 1 * l 3 + l 0 * l 2 * l 3 + l 1 * l 2 * l 3

def esymm4 {R : Type*} [CommRing R] (l : Fin 4 → R) : R := l 0 * l 1 * l 2 * l 3

/-- The quartic factor `Q_4(z)` `(GFH.10)`. -/
def quartic {R : Type*} [CommRing R] (z : R) (l : Fin 4 → R) : R :=
  6 * z ^ 4 + 12 * esymm1 l * z ^ 3 + (8 * esymm1 l ^ 2 + 2 * esymm2 l) * z ^ 2 +
    (2 * esymm1 l ^ 3 + 2 * esymm1 l * esymm2 l) * z +
    (esymm1 l ^ 2 * esymm2 l - esymm1 l * esymm3 l + esymm4 l)

/-- The grade variables of `ℚ[z, λ_1, …, λ_4]`. -/
def lamVar : Fin 4 → Poly 4 := fun i => X (some i)

theorem delta_fin_three {R : Type*} [CommRing R] (v : Fin 3 → R) :
    delta v = (v 0 - v 1) * (v 0 - v 2) * (v 1 - v 2) := by
  rw [delta, Fin.prod_univ_three, show Ioi (0 : Fin 3) = {1, 2} by decide,
    show Ioi (1 : Fin 3) = {2} by decide, show Ioi (2 : Fin 3) = ∅ by decide,
    prod_pair (by decide), prod_singleton, prod_empty, mul_one]

theorem delta_fin_four {R : Type*} [CommRing R] (v : Fin 4 → R) :
    delta v = (v 0 - v 1) * (v 0 - v 2) * (v 0 - v 3) * (v 1 - v 2) * (v 1 - v 3) *
      (v 2 - v 3) := by
  rw [delta, Fin.prod_univ_four, show Ioi (0 : Fin 4) = {1, 2, 3} by decide,
    show Ioi (1 : Fin 4) = {2, 3} by decide, show Ioi (2 : Fin 4) = {3} by decide,
    show Ioi (3 : Fin 4) = ∅ by decide, prod_insert (by decide), prod_pair (by decide),
    prod_pair (by decide), prod_singleton, prod_empty, mul_one]
  ring

variable {K : Type*} [Field K] [Algebra ℚ K]

/-! ### The incidence factors `(GFH.11)` -/

theorem aeval_incidence_four_zero (z : K) (l : Fin 4 → K) :
    aeval (point z l) (incidence (0 : Fin 4)) =
      (z + l 0) * ((z + (l 0 + l 1)) * (z + (l 0 + l 2)) * (z + (l 0 + l 3))) *
      ((z + ((l 0 + l 1 + l 2 + l 3) - l 1)) * (z + ((l 0 + l 1 + l 2 + l 3) - l 2)) *
        (z + ((l 0 + l 1 + l 2 + l 3) - l 3))) := by
  rw [aeval_incidence,
    show incSets (0 : Fin 4) =
      {{0}, {0, 1}, {0, 2}, {0, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}} by decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_singleton,
    sum_singleton, sum_pair (by decide), sum_pair (by decide), sum_pair (by decide),
    sum_insert (by decide), sum_pair (by decide), sum_insert (by decide), sum_pair (by decide),
    sum_insert (by decide), sum_pair (by decide)]
  ring

theorem aeval_incidence_four_one (z : K) (l : Fin 4 → K) :
    aeval (point z l) (incidence (1 : Fin 4)) =
      (z + l 1) * ((z + (l 1 + l 0)) * (z + (l 1 + l 2)) * (z + (l 1 + l 3))) *
      ((z + ((l 0 + l 1 + l 2 + l 3) - l 0)) * (z + ((l 0 + l 1 + l 2 + l 3) - l 2)) *
        (z + ((l 0 + l 1 + l 2 + l 3) - l 3))) := by
  rw [aeval_incidence,
    show incSets (1 : Fin 4) =
      {{1}, {0, 1}, {1, 2}, {1, 3}, {0, 1, 2}, {0, 1, 3}, {1, 2, 3}} by decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_singleton,
    sum_singleton, sum_pair (by decide), sum_pair (by decide), sum_pair (by decide),
    sum_insert (by decide), sum_pair (by decide), sum_insert (by decide), sum_pair (by decide),
    sum_insert (by decide), sum_pair (by decide)]
  ring

theorem aeval_incidence_four_two (z : K) (l : Fin 4 → K) :
    aeval (point z l) (incidence (2 : Fin 4)) =
      (z + l 2) * ((z + (l 2 + l 0)) * (z + (l 2 + l 1)) * (z + (l 2 + l 3))) *
      ((z + ((l 0 + l 1 + l 2 + l 3) - l 0)) * (z + ((l 0 + l 1 + l 2 + l 3) - l 1)) *
        (z + ((l 0 + l 1 + l 2 + l 3) - l 3))) := by
  rw [aeval_incidence,
    show incSets (2 : Fin 4) =
      {{2}, {0, 2}, {1, 2}, {2, 3}, {0, 1, 2}, {0, 2, 3}, {1, 2, 3}} by decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_singleton,
    sum_singleton, sum_pair (by decide), sum_pair (by decide), sum_pair (by decide),
    sum_insert (by decide), sum_pair (by decide), sum_insert (by decide), sum_pair (by decide),
    sum_insert (by decide), sum_pair (by decide)]
  ring

theorem aeval_incidence_four_three (z : K) (l : Fin 4 → K) :
    aeval (point z l) (incidence (3 : Fin 4)) =
      (z + l 3) * ((z + (l 3 + l 0)) * (z + (l 3 + l 1)) * (z + (l 3 + l 2))) *
      ((z + ((l 0 + l 1 + l 2 + l 3) - l 0)) * (z + ((l 0 + l 1 + l 2 + l 3) - l 1)) *
        (z + ((l 0 + l 1 + l 2 + l 3) - l 2))) := by
  rw [aeval_incidence,
    show incSets (3 : Fin 4) =
      {{3}, {0, 3}, {1, 3}, {2, 3}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}} by decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_singleton,
    sum_singleton, sum_pair (by decide), sum_pair (by decide), sum_pair (by decide),
    sum_insert (by decide), sum_pair (by decide), sum_insert (by decide), sum_pair (by decide),
    sum_insert (by decide), sum_pair (by decide)]
  ring

omit [Field K] [Algebra ℚ K] in
theorem comp_succAbove_four (l : Fin 4 → K) :
    l ∘ (0 : Fin 4).succAbove = ![l 1, l 2, l 3] ∧ l ∘ (1 : Fin 4).succAbove = ![l 0, l 2, l 3] ∧
      l ∘ (2 : Fin 4).succAbove = ![l 0, l 1, l 3] ∧
        l ∘ (3 : Fin 4).succAbove = ![l 0, l 1, l 2] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext j <;> fin_cases j <;> rfl

theorem aeval_quartic (z : K) (l : Fin 4 → K) :
    aeval (point z l) (quartic (X none) lamVar) = quartic z l := by
  simp [quartic, esymm1, esymm2, esymm3, esymm4, lamVar, point]

theorem aeval_linear_four (z : K) (l : Fin 4 → K) :
    aeval (point z l) (2 * X none + esymm1 lamVar) = 2 * z + esymm1 l := by
  simp [esymm1, lamVar, point]

/-- **Theorem 3.1, `(GFH.9)`–`(GFH.10)`**: `P_4 = (2z + e_1) Q_4`. -/
theorem formNumer_four :
    formNumer 4 = (2 * X none + esymm1 lamVar) * quartic (X none) lamVar := by
  refine formNumer_unique (MvPolynomial.funext fun x => ?_)
  have e : ∀ p : Poly 4, eval x p = aeval x p := fun p => by rw [← coe_aeval_eq_eval]; rfl
  have hx : point (x none) (fun i => x (some i)) = x := funext fun o => by cases o <;> rfl
  rw [e, e, ← hx]
  set z := x none
  set l : Fin 4 → ℚ := fun i => x (some i)
  obtain ⟨h0, h1, h2, h3⟩ := comp_succAbove_four l
  rw [numer_succ 3, map_sum, Fin.sum_univ_four, map_mul, aeval_deltaPoly, map_mul,
    aeval_linear_four, aeval_quartic, delta_fin_four]
  simp only [map_zsmul, map_mul, aeval_liftDel, h0, h1, h2, h3, numer_eq, aeval_deltaPoly,
    PrimeShiftSource.aeval_formNumer_three, delta_fin_three, aeval_incidence_four_zero,
    aeval_incidence_four_one, aeval_incidence_four_two, aeval_incidence_four_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, quartic, esymm1, esymm2, esymm3, esymm4, zsmul_eq_mul]
  norm_num
  ring

/-! ### Hurwitz stability `(GFH.14)`–`(GFH.18)` -/

theorem esymm_mul_sub_pos {l : Fin 4 → ℝ} (hl : ∀ i, 0 < l i) :
    0 < esymm1 l * esymm2 l - esymm3 l := by
  have h0 := hl 0; have h1 := hl 1; have h2 := hl 2; have h3 := hl 3
  have : esymm1 l * esymm2 l - esymm3 l = 2 * esymm3 l +
      (l 0 ^ 2 * (l 1 + l 2 + l 3) + l 1 ^ 2 * (l 0 + l 2 + l 3) + l 2 ^ 2 * (l 0 + l 1 + l 3) +
        l 3 ^ 2 * (l 0 + l 1 + l 2)) := by
    simp only [esymm1, esymm2, esymm3]; ring
  rw [this]
  simp only [esymm3]
  positivity

theorem six_esymm4_le_sq {l : Fin 4 → ℝ} (hl : ∀ i, 0 < l i) : 6 * esymm4 l ≤ esymm2 l ^ 2 := by
  have h0 := hl 0; have h1 := hl 1; have h2 := hl 2; have h3 := hl 3
  set a := l 0; set b := l 1; set c := l 2; set d := l 3
  have : esymm2 l ^ 2 - 6 * esymm4 l = (a*b)^2 + (a*c)^2 + (a*d)^2 + (b*c)^2 + (b*d)^2 + (c*d)^2 +
      2 * (a*b*(a*c) + a*b*(a*d) + a*b*(b*c) + a*b*(b*d) + a*c*(a*d) + a*c*(b*c) + a*c*(c*d) +
        a*d*(b*d) + a*d*(c*d) + b*c*(b*d) + b*c*(c*d) + b*d*(c*d)) := by
    simp only [esymm2, esymm4]; ring
  have hpos : 0 ≤ esymm2 l ^ 2 - 6 * esymm4 l := by rw [this]; positivity
  linarith

/-- **Theorem 4.1: grade-four causal stability.**  For positive grades every zero of `P_4`
lies in `Re z < 0`. -/
theorem formNumer_four_ne_zero {l : Fin 4 → ℝ} (hl : ∀ i, 0 < l i) {z : ℂ} (hz : 0 ≤ z.re) :
    aeval (point z fun i => (l i : ℂ)) (formNumer 4) ≠ 0 := by
  have h0 := hl 0; have h1 := hl 1; have h2 := hl 2; have h3 := hl 3
  have he1 : 0 < esymm1 l := by simp only [esymm1]; positivity
  have he2 : 0 < esymm2 l := by simp only [esymm2]; positivity
  have he3 : 0 < esymm3 l := by simp only [esymm3]; positivity
  have he4 : 0 < esymm4 l := by simp only [esymm4]; positivity
  have ha0 : 0 < esymm1 l ^ 2 * esymm2 l - esymm1 l * esymm3 l + esymm4 l := by
    have := esymm_mul_sub_pos hl
    nlinarith
  have hsq := six_esymm4_le_sq hl
  have hminor : 6 * (2 * esymm1 l ^ 3 + 2 * esymm1 l * esymm2 l) ^ 2 +
      (12 * esymm1 l) ^ 2 * (esymm1 l ^ 2 * esymm2 l - esymm1 l * esymm3 l + esymm4 l) <
      12 * esymm1 l * (8 * esymm1 l ^ 2 + 2 * esymm2 l) *
        (2 * esymm1 l ^ 3 + 2 * esymm1 l * esymm2 l) := by
    have hid : 12 * esymm1 l * (8 * esymm1 l ^ 2 + 2 * esymm2 l) *
        (2 * esymm1 l ^ 3 + 2 * esymm1 l * esymm2 l) -
        (6 * (2 * esymm1 l ^ 3 + 2 * esymm1 l * esymm2 l) ^ 2 +
          (12 * esymm1 l) ^ 2 * (esymm1 l ^ 2 * esymm2 l - esymm1 l * esymm3 l + esymm4 l)) =
        24 * esymm1 l ^ 2 * (7 * esymm1 l ^ 4 + 2 * esymm1 l ^ 2 * esymm2 l + esymm2 l ^ 2 +
          6 * esymm1 l * esymm3 l - 6 * esymm4 l) := by ring
    have hb : 0 < 7 * esymm1 l ^ 4 + 2 * esymm1 l ^ 2 * esymm2 l + esymm2 l ^ 2 +
        6 * esymm1 l * esymm3 l - 6 * esymm4 l := by nlinarith [pow_pos he1 4]
    have : 0 < 24 * esymm1 l ^ 2 * (7 * esymm1 l ^ 4 + 2 * esymm1 l ^ 2 * esymm2 l +
        esymm2 l ^ 2 + 6 * esymm1 l * esymm3 l - 6 * esymm4 l) := by positivity
    linarith
  have hQ := RHTower.GibbsGas.quartic_no_rhp_root 6 (12 * esymm1 l)
    (8 * esymm1 l ^ 2 + 2 * esymm2 l)
    (2 * esymm1 l ^ 3 + 2 * esymm1 l * esymm2 l)
    (esymm1 l ^ 2 * esymm2 l - esymm1 l * esymm3 l + esymm4 l) (by norm_num) (by positivity)
    (by positivity) (by positivity) ha0 (by simpa using hminor) z hz
  rw [formNumer_four, map_mul, aeval_quartic, aeval_linear_four]
  refine mul_ne_zero ?_ ?_
  · intro h
    have := congrArg Complex.re h
    simp only [esymm1, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.zero_re] at this
    norm_num at this
    linarith [he1, show esymm1 l = l 0 + l 1 + l 2 + l 3 from rfl]
  · intro h
    apply hQ
    rw [← h]
    simp only [quartic, esymm1, esymm2, esymm3, esymm4]
    push_cast
    ring

end Permutohedral

end

end GaloisForLFunctions.HTGeometry
