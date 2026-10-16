import GaloisForLFunctions.RHTower.PoissonDigammaReproduction
import GaloisForLFunctions.HTGeometry.LorentzianCosineIntegral

/-!
# Complex-width integral identities for odd Weil resolvents

The Gauss series gives Poisson–digamma reproduction at a complex width in
the first quadrant. Conjugation supplies the paired lower-quadrant width.
Together with the Lorentzian cosine integral, this evaluates the mixed
odd resolvent density by partial fractions. These are auxiliary identities;
this module does not assert positivity or analytic continuation of a Weil source.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.OddResolvent

def cauchy (a : ℂ) (r : ℝ) : ℂ := (a ^ 2 + (r : ℂ) ^ 2)⁻¹

theorem rotate_sq (a : ℂ) (r : ℝ) :
    (r : ℂ) ^ 2 - (I * a) ^ 2 = a ^ 2 + (r : ℂ) ^ 2 := by
  ring_nf
  rw [I_sq]
  ring

theorem cauchy_ne_zero {a : ℂ} (ha : 0 < a.re) (r : ℝ) :
    a ^ 2 + (r : ℂ) ^ 2 ≠ 0 := by
  have h := sq_sub_sq_ne_zero (w := I * a) (by simpa using ha) r
  rwa [rotate_sq] at h

theorem integrable_cauchy {a : ℂ} (ha : 0 < a.re) : Integrable (cauchy a) := by
  have h := integrable_inv_sq_sub_sq (w := I * a) (by simpa using ha)
  change Integrable (fun r : ℝ => (a ^ 2 + (r : ℂ) ^ 2)⁻¹)
  simpa only [rotate_sq] using h

theorem integral_cauchy {a : ℂ} (ha : 0 < a.re) :
    ∫ r, cauchy a r = Real.pi / a := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have h := integral_cexp_div_sq_sub_sq (w := I * a) (by simpa using ha) 0
  simp only [rotate_sq, ofReal_zero, mul_zero, exp_zero, one_div, abs_zero, mul_one] at h
  rw [show (Real.pi : ℂ) * I / (I * a) = Real.pi / a by field_simp] at h
  exact h

theorem exists_cauchy_poisson_bound {a : ℂ} (ha : 0 < a.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ r, ‖cauchy a r‖ ≤ C * poissonWeight 1 r := by
  obtain ⟨c, hc, hb⟩ := exists_mul_one_add_sq_le_norm_sq_sub
    (w := I * a) (by simpa using ha)
  refine ⟨Real.pi / c, by positivity, fun r => ?_⟩
  have hd : 0 < c * (1 + r ^ 2) := by positivity
  have hnorm := hb r
  rw [rotate_sq] at hnorm
  rw [cauchy, norm_inv]
  calc ‖a ^ 2 + (r : ℂ) ^ 2‖⁻¹ ≤ (c * (1 + r ^ 2))⁻¹ :=
        inv_anti₀ hd hnorm
    _ = Real.pi / c * poissonWeight 1 r := by
        rw [poissonWeight]
        norm_num
        field_simp

theorem cauchy_real (b r : ℝ) :
    cauchy (b : ℂ) r = (((b ^ 2 + r ^ 2)⁻¹ : ℝ) : ℂ) := by
  simp only [cauchy, ofReal_inv, ofReal_add, ofReal_pow]

theorem cauchy_partial_fractions {a : ℂ} {b : ℝ} (ha : 0 < a.re)
    (hb : 0 < b) (hab : (b : ℂ) ^ 2 - a ^ 2 ≠ 0) (r : ℝ) :
    cauchy a r * cauchy (b : ℂ) r =
      ((b : ℂ) ^ 2 - a ^ 2)⁻¹ * (cauchy a r - cauchy (b : ℂ) r) := by
  have h1 := cauchy_ne_zero ha r
  have h2 := cauchy_ne_zero (a := (b : ℂ)) (by simpa using hb) r
  unfold cauchy
  field_simp
  ring

theorem integrable_cauchy_mul {a : ℂ} {b : ℝ} (ha : 0 < a.re)
    (hb : 0 < b) (hab : (b : ℂ) ^ 2 - a ^ 2 ≠ 0) :
    Integrable fun r => cauchy a r * cauchy (b : ℂ) r := by
  simp_rw [cauchy_partial_fractions ha hb hab]
  exact ((integrable_cauchy ha).sub
    (integrable_cauchy (a := (b : ℂ)) (by simpa using hb))).const_mul _

theorem integral_cauchy_mul {a : ℂ} {b : ℝ} (ha : 0 < a.re)
    (hb : 0 < b) (hab : (b : ℂ) ^ 2 - a ^ 2 ≠ 0) :
    (∫ r, cauchy a r * cauchy (b : ℂ) r) =
      Real.pi / (a * b * (a + b)) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hp : a + b ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  simp_rw [cauchy_partial_fractions ha hb hab]
  rw [integral_const_mul, integral_sub (integrable_cauchy ha)
    (integrable_cauchy (a := (b : ℂ)) (by simpa using hb)),
    integral_cauchy ha, integral_cauchy (by simpa using hb : 0 < (b : ℂ).re)]
  field_simp
  ring

theorem integrable_cauchy_weight {a : ℂ} (ha : 0 < a.re) {f : ℝ → ℝ}
    (hf : Continuous f) (hi : Integrable fun r => poissonWeight 1 r * f r) :
    Integrable fun r => cauchy a r * (f r : ℂ) := by
  obtain ⟨C, hC, hbound⟩ := exists_cauchy_poisson_bound ha
  refine (hi.norm.const_mul C).mono' ?_ (Eventually.of_forall fun r => ?_)
  · have hc : Continuous (cauchy a) := by
      unfold cauchy
      exact (by fun_prop : Continuous fun r : ℝ => a ^ 2 + (r : ℂ) ^ 2).inv₀
        (cauchy_ne_zero ha)
    exact (hc.mul (Complex.continuous_ofReal.comp hf)).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (poissonWeight_nonneg (by norm_num : (0 : ℝ) < 1) r)]
    nlinarith [mul_le_mul_of_nonneg_right (hbound r) (abs_nonneg (f r))]

theorem integrable_cauchy_digammaTerm {a : ℂ} (ha : 0 < a.re) {c : ℝ}
    (hc : 0 < c) (n : ℕ) :
    Integrable fun r => cauchy a r * (digammaHalfTerm c n r : ℂ) := by
  apply integrable_cauchy_weight ha
  · change Continuous (fun r => digammaHalfTerm c n r)
    have he : (fun r => digammaHalfTerm c n r) = fun r =>
        1 / ((n : ℝ) + 1) - 2 * (2 * (c + n)) * ((2 * (c + n)) ^ 2 + r ^ 2)⁻¹ :=
      funext (digammaHalfTerm_eq hc n)
    rw [he]
    have hn : 0 < 2 * (c + (n : ℝ)) := by positivity
    fun_prop (disch := intro r; exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hn) (sq_nonneg r)))
  · exact integrable_poissonWeight_mul_digammaHalfTerm (by norm_num) hc n

theorem summable_integral_norm_cauchy_digammaTerm {a : ℂ} (ha : 0 < a.re) {c : ℝ}
    (hc : 0 < c) :
    Summable fun n : ℕ => ∫ r, ‖cauchy a r * (digammaHalfTerm c n r : ℂ)‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_cauchy_poisson_bound ha
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => ?_) ((summable_integral_norm_poissonWeight_digammaHalf (a := 1)
      (by norm_num) hc).mul_left C)
  rw [← integral_const_mul]
  apply integral_mono (integrable_cauchy_digammaTerm ha hc n).norm
    ((integrable_poissonWeight_mul_digammaHalfTerm (a := 1) (by norm_num) hc n).norm.const_mul C)
  intro r
  dsimp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (poissonWeight_nonneg (by norm_num : (0 : ℝ) < 1) r)]
  nlinarith [mul_le_mul_of_nonneg_right (hbound r) (abs_nonneg (digammaHalfTerm c n r))]

theorem integral_cauchy_digammaTerm {a : ℂ} (ha : 0 < a.re) (hai : 0 < a.im)
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (∫ r, cauchy a r * (digammaHalfTerm c n r : ℂ)) =
      Real.pi / a * gaussDigammaSeriesTerm ((c : ℂ) + a / 2) n := by
  let b : ℝ := 2 * (c + n)
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : (b : ℂ) ^ 2 - a ^ 2 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [sub_im, sq, mul_im, ofReal_im, zero_mul, mul_zero, add_zero, zero_im] at hi
    nlinarith [mul_pos ha hai]
  have he : ∀ r, cauchy a r * (digammaHalfTerm c n r : ℂ) =
      (1 / ((n : ℂ) + 1)) * cauchy a r -
        (2 * (b : ℂ)) * (cauchy a r * cauchy (b : ℂ) r) := by
    intro r
    rw [digammaHalfTerm_eq hc, cauchy_real]
    dsimp [b]
    push_cast
    ring
  simp_rw [he]
  rw [integral_sub ((integrable_cauchy ha).const_mul _)
    ((integrable_cauchy_mul ha hb hab).const_mul _), integral_const_mul,
    integral_const_mul, integral_cauchy ha, integral_cauchy_mul ha hb hab]
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hsum : a + b ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hrel : (c : ℂ) + a / 2 + n = (a + b) / 2 := by
    dsimp [b]
    push_cast
    ring
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  unfold gaussDigammaSeriesTerm
  rw [hrel]
  field_simp

/-- Complex-width Poisson reproduction. The width is in the first quadrant,
so every partial fraction used in the Gauss series has distinct poles. -/
theorem integral_cauchy_re_digamma {a : ℂ} (ha : 0 < a.re) (hai : 0 < a.im)
    {c : ℝ} (hc : 0 < c) :
    (∫ r, cauchy a r *
      ((Complex.digamma ((c : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re : ℂ)) =
      Real.pi / a * Complex.digamma ((c : ℂ) + a / 2) := by
  have hint := integrable_cauchy_weight ha (continuous_re_digamma_half hc)
    (integrable_poissonWeight_mul_re_digamma_half (by norm_num : (0 : ℝ) < 1) hc)
  have hsum := integral_tsum_of_summable_integral_norm
    (fun n => integrable_cauchy_digammaTerm ha hc n)
    (summable_integral_norm_cauchy_digammaTerm ha hc)
  have harg : 0 < ((c : ℂ) + a / 2).re := by simp; linarith
  have hseries : (∑' n, gaussDigammaSeriesTerm ((c : ℂ) + a / 2) n) =
      Complex.digamma ((c : ℂ) + a / 2) + Real.eulerMascheroniConstant := by
    rw [digamma_eq_neg_euler_add_tsum_gauss harg]
    ring
  have hintegrand : ∀ r, (∑' n, cauchy a r * (digammaHalfTerm c n r : ℂ)) =
      cauchy a r * ((Complex.digamma ((c : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re : ℂ) +
        (Real.eulerMascheroniConstant : ℂ) * cauchy a r := by
    intro r
    rw [tsum_mul_left, ← Complex.ofReal_tsum, tsum_digammaHalfTerm hc]
    push_cast
    ring
  simp_rw [integral_cauchy_digammaTerm ha hai hc] at hsum
  rw [tsum_mul_left, hseries] at hsum
  simp_rw [hintegrand] at hsum
  rw [integral_add hint ((integrable_cauchy ha).const_mul _), integral_const_mul,
    integral_cauchy ha] at hsum
  linear_combination -hsum

theorem cauchy_conj (a : ℂ) (r : ℝ) : cauchy (conj a) r = conj (cauchy a r) := by
  simp [cauchy]

theorem integral_cauchy_re_digamma_conj {a : ℂ} (ha : 0 < a.re) (hai : 0 < a.im)
    {c : ℝ} (hc : 0 < c) :
    (∫ r, cauchy (conj a) r *
      ((Complex.digamma ((c : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re : ℂ)) =
      conj (Real.pi / a * Complex.digamma ((c : ℂ) + a / 2)) := by
  rw [← integral_cauchy_re_digamma ha hai hc, ← integral_conj]
  congr 1
  funext r
  simp [cauchy_conj]

theorem integrable_cauchy_cos {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    Integrable fun r => cauchy a r * (Real.cos (r * x) : ℂ) := by
  have h := integrable_cos_div_sq_sub_sq (w := I * a) (by simpa using ha) x
  simp only [rotate_sq, div_eq_mul_inv] at h
  simpa only [cauchy, mul_comm] using h

theorem integral_cauchy_cos {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    (∫ r, cauchy a r * (Real.cos (r * x) : ℂ)) =
      Real.pi / a * Complex.exp (-(a * (|x| : ℝ))) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have h := integral_cos_div_sq_sub_sq (w := I * a) (by simpa using ha) x
  simp only [rotate_sq, div_eq_mul_inv] at h
  have he : I * (I * a) * (|x| : ℝ) = -(a * (|x| : ℝ)) := by
    rw [← mul_assoc I I, ← sq, I_sq]
    ring
  rw [he] at h
  have hp : (Real.pi : ℂ) * I * (I * a)⁻¹ = Real.pi / a := by field_simp
  rw [hp] at h
  simpa only [cauchy, mul_comm] using h

theorem oddGram_partial {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hab : a ^ 2 - b ^ 2 ≠ 0) (r : ℝ) :
    (r : ℂ) ^ 2 * cauchy a r * cauchy b r =
      (a ^ 2 - b ^ 2)⁻¹ * (a ^ 2 * cauchy a r - b ^ 2 * cauchy b r) := by
  have h1 := cauchy_ne_zero ha r
  have h2 := cauchy_ne_zero hb r
  unfold cauchy
  field_simp
  ring

theorem integral_oddGram_cos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hab : a ^ 2 - b ^ 2 ≠ 0) (x : ℝ) :
    (∫ r : ℝ, (r : ℂ) ^ 2 * cauchy a r * cauchy b r * (Real.cos (r * x) : ℂ)) =
      Real.pi * (a * Complex.exp (-(a * (|x| : ℝ))) -
        b * Complex.exp (-(b * (|x| : ℝ)))) / (a ^ 2 - b ^ 2) := by
  simp_rw [oddGram_partial ha hb hab, mul_assoc, sub_mul, mul_assoc]
  rw [integral_const_mul,
    integral_sub ((integrable_cauchy_cos ha x).const_mul _)
      ((integrable_cauchy_cos hb x).const_mul _), integral_const_mul, integral_const_mul,
    integral_cauchy_cos ha x, integral_cauchy_cos hb x]
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  field_simp

end RHTower.OddResolvent
