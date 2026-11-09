import Mathlib.Analysis.Complex.Polynomial.Basic
import GaloisForLFunctions.HTGeometry.AddPolynomialInvariance
import Mathlib.Tactic

/-!
# A finite polynomial perturbation preserves long endpoint jets

For an even cluster of positive donor parameters near `A`, subtracting a
small odd monomial from their monic product removes every real root. All
new roots stay within five cluster radii of `-A`. The monomial degree
retains the largest possible jet at the origin for this monic degree.
-/

noncomputable section
set_option autoImplicit false

open Complex Polynomial

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Perturbation size for a cluster of `2k+2` donor pairs. -/
def clusterSurgerySize (k : ℕ) (A w : ℝ) : ℝ :=
  2 * (2 * w) ^ (2 * k + 2) / (A - w) ^ (2 * k + 1)

/-- The odd perturbation preserves every coefficient below degree `2k+1`. -/
def clusterSurgeryPolynomial (k : ℕ) (a : Fin (2 * k + 2) → ℝ) (A w : ℝ) : ℂ[X] :=
  (∏ i, (X + C (a i : ℂ))) - C (clusterSurgerySize k A w : ℂ) * X ^ (2 * k + 1)

@[simp] theorem clusterSurgeryPolynomial_eval (k : ℕ) (a : Fin (2 * k + 2) → ℝ)
    (A w : ℝ) (z : ℂ) :
    (clusterSurgeryPolynomial k a A w).eval z =
      (∏ i, (z + (a i : ℂ))) - (clusterSurgerySize k A w : ℂ) * z ^ (2 * k + 1) := by
  simp [clusterSurgeryPolynomial, Polynomial.eval_prod]

theorem clusterSurgeryPolynomial_monic_degree (k : ℕ) (a : Fin (2 * k + 2) → ℝ)
    (A w : ℝ) :
    (clusterSurgeryPolynomial k a A w).Monic ∧
      (clusterSurgeryPolynomial k a A w).natDegree = 2 * k + 2 := by
  let D : ℂ[X] := ∏ i, (X + C (a i : ℂ))
  have hD : D.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)
  have hdeg : D.natDegree = 2 * k + 2 := by
    dsimp only [D]
    rw [natDegree_prod _ _ (fun i _ => (monic_X_add_C (a i : ℂ)).ne_zero)]
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
  have hsmall : (C (clusterSurgerySize k A w : ℂ) * X ^ (2 * k + 1)).natDegree <
      D.natDegree := by
    apply (natDegree_C_mul_le _ _).trans_lt
    rw [natDegree_X_pow, hdeg]
    omega
  exact ⟨hD.sub_of_left (degree_lt_degree hsmall),
    (natDegree_sub_eq_left_of_natDegree_lt hsmall).trans hdeg⟩

theorem clusterSurgerySize_pos (k : ℕ) {A w : ℝ} (hw : 0 < w) (hA : 7 * w < A) :
    0 < clusterSurgerySize k A w := by
  unfold clusterSurgerySize
  have : 0 < A - w := by linarith only [hw, hA]
  positivity

/-- Beyond five radii, the donor product dominates the perturbing monomial. -/
theorem clusterSurgery_barrier (k : ℕ) {A w r : ℝ}
    (hw : 0 < w) (hA : 7 * w < A) (hr : 5 * w ≤ r) :
    clusterSurgerySize k A w * (r + A) ^ (2 * k + 1) < (r - w) ^ (2 * k + 2) := by
  have hAw : 0 < A - w := by linarith only [hw, hA]
  have hrA : 0 < r + A := by linarith only [hw, hA, hr]
  have hrw : 0 < r - w := by linarith only [hw, hr]
  have hsep : 2 * w * (r + A) < (A - w) * (r - w) := by
    have h₁ := mul_nonneg (show 0 ≤ A - 3 * w by linarith only [hw, hA])
      (show 0 ≤ r - 5 * w by linarith only [hr])
    have h₂ := mul_pos hw (show 0 < A - 7 * w by linarith only [hA])
    nlinarith only [h₁, h₂]
  have hp := pow_lt_pow_left₀ hsep (show 0 ≤ 2 * w * (r + A) by positivity)
    (show 2 * k + 1 ≠ 0 by omega)
  have hs := mul_lt_mul_of_pos_left hp (show 0 < 4 * w by positivity)
  have hu := mul_le_mul_of_nonneg_right
    (show 4 * w ≤ r - w by linarith only [hr])
    (pow_nonneg (mul_nonneg hAw.le hrw.le) (2 * k + 1))
  have hstrict := hs.trans_le hu
  unfold clusterSurgerySize
  rw [div_mul_eq_mul_div, div_lt_iff₀ (pow_pos hAw _)]
  convert hstrict using 1 <;> simp only [mul_pow, pow_succ] <;> ring

/-- A root of the perturbed product lies within five cluster radii. -/
theorem clusterSurgery_root_norm_lt (k : ℕ) {a : Fin (2 * k + 2) → ℝ} {A w : ℝ}
    (hw : 0 < w) (hA : 7 * w < A) (ha : ∀ i, |a i - A| ≤ w) {z : ℂ}
    (hz : ∏ i, (z + (a i : ℂ)) = (clusterSurgerySize k A w : ℂ) * z ^ (2 * k + 1)) :
    ‖z + (A : ℂ)‖ < 5 * w := by
  by_contra hnot
  have hr : 5 * w ≤ ‖z + (A : ℂ)‖ := le_of_not_gt hnot
  have hrw : 0 ≤ ‖z + (A : ℂ)‖ - w := by linarith only [hw, hr]
  have hlower (i : Fin (2 * k + 2)) : ‖z + (A : ℂ)‖ - w ≤ ‖z + (a i : ℂ)‖ := by
    have hs : z + (A : ℂ) = (z + (a i : ℂ)) + ((A - a i : ℝ) : ℂ) := by
      push_cast
      ring
    have h := norm_add_le (z + (a i : ℂ)) ((A - a i : ℝ) : ℂ)
    rw [← hs, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at h
    linarith only [h, ha i]
  have hupper : ‖z‖ ≤ ‖z + (A : ℂ)‖ + A := by
    have h := norm_sub_le (z + (A : ℂ)) (A : ℂ)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < A by linarith only [hw, hA])] at h
    exact h
  have he := congrArg norm hz
  rw [norm_prod, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (clusterSurgerySize_pos k hw hA), norm_pow] at he
  have hprod : (‖z + (A : ℂ)‖ - w) ^ (2 * k + 2) ≤
      clusterSurgerySize k A w * (‖z + (A : ℂ)‖ + A) ^ (2 * k + 1) := by
    calc
      _ = ∏ _i : Fin (2 * k + 2), (‖z + (A : ℂ)‖ - w) := by simp
      _ ≤ ∏ i : Fin (2 * k + 2), ‖z + (a i : ℂ)‖ :=
        Finset.prod_le_prod (fun _ _ => hrw) (fun i _ => hlower i)
      _ = clusterSurgerySize k A w * ‖z‖ ^ (2 * k + 1) := he
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hupper _)
        (clusterSurgerySize_pos k hw hA).le
  exact (not_lt_of_ge hprod) (clusterSurgery_barrier k hw hA hr)

private theorem even_prod_nonneg {k : ℕ} {f : Fin (2 * k + 2) → ℝ}
    (hf : ∀ i, f i ≤ 0) : 0 ≤ ∏ i, f i := by
  have hp : 0 ≤ ∏ i, (-f i) := Finset.prod_nonneg (fun i _ => neg_nonneg.mpr (hf i))
  have he : (∏ i, (-f i)) = ∏ i, f i := by
    calc
      _ = ∏ i, (-1 : ℝ) * f i := by apply Finset.prod_congr rfl; intro i _; ring
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp [pow_add, pow_mul]
  rwa [he] at hp

/-- No real point can be a root of the perturbed even donor product. -/
theorem clusterSurgery_no_real_root (k : ℕ) {a : Fin (2 * k + 2) → ℝ} {A w : ℝ}
    (hw : 0 < w) (hA : 7 * w < A) (ha : ∀ i, |a i - A| ≤ w) (x : ℝ) :
    (∏ i, ((x : ℂ) + (a i : ℂ))) ≠
      (clusterSurgerySize k A w : ℂ) * (x : ℂ) ^ (2 * k + 1) := by
  intro hz
  have hb := clusterSurgery_root_norm_lt k hw hA ha hz
  rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs] at hb
  have hx : x < 0 := by linarith only [le_abs_self (x + A), hb, hA, hw]
  have he : (∏ i, (x + a i)) = clusterSurgerySize k A w * x ^ (2 * k + 1) := by
    exact_mod_cast hz
  have heps := clusterSurgerySize_pos k hw hA
  have hxpow : x ^ (2 * k + 1) < 0 := by
    rw [pow_add, pow_mul, pow_one]
    exact mul_neg_of_pos_of_neg (pow_pos (sq_pos_of_ne_zero hx.ne) k) hx
  have hneg := mul_neg_of_pos_of_neg heps hxpow
  by_cases hleft : x ≤ -A - w
  · have hp : 0 ≤ ∏ i, (x + a i) := even_prod_nonneg (fun i => by
      have hi := (abs_le.mp (ha i)).2
      linarith only [hi, hleft])
    linarith only [hp, he, hneg]
  by_cases hright : -A + w ≤ x
  · have hp : 0 ≤ ∏ i, (x + a i) := Finset.prod_nonneg (fun i _ => by
      have hi := (abs_le.mp (ha i)).1
      linarith only [hi, hright])
    linarith only [hp, he, hneg]
  have hxl : -A - w < x := lt_of_not_ge hleft
  have hxr : x < -A + w := lt_of_not_ge hright
  have hbound (i : Fin (2 * k + 2)) : |x + a i| ≤ 2 * w := by
    obtain ⟨hi₁, hi₂⟩ := abs_le.mp (ha i)
    rw [abs_le]
    constructor <;> linarith only [hxl, hxr, hi₁, hi₂]
  have hp : |∏ i, (x + a i)| ≤ (2 * w) ^ (2 * k + 2) := by
    calc
      _ = ∏ i, |x + a i| := by
        simpa only [Real.norm_eq_abs] using
          (norm_prod Finset.univ (fun i : Fin (2 * k + 2) => x + a i))
      _ ≤ ∏ _i : Fin (2 * k + 2), (2 * w) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hbound i)
      _ = _ := by simp
  have hAw : 0 < A - w := by linarith only [hw, hA]
  have hbig : 2 * (2 * w) ^ (2 * k + 2) ≤
      clusterSurgerySize k A w * (-x) ^ (2 * k + 1) := by
    calc
      _ = clusterSurgerySize k A w * (A - w) ^ (2 * k + 1) := by
        rw [clusterSurgerySize, div_mul_cancel₀ _ (pow_pos hAw _).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hAw.le (by linarith only [hxr]) _) heps.le
  have hpow : x ^ (2 * k + 1) = -(-x) ^ (2 * k + 1) := by
    simp only [pow_add, pow_mul, pow_one, neg_sq]
    ring
  rw [hpow] at he
  have hK : 0 < (2 * w) ^ (2 * k + 2) := pow_pos (by positivity) _
  nlinarith only [hp, hbig, he, hK, neg_abs_le (∏ i, (x + a i))]

/-- Every root is nonreal and stays close to the donor cluster. -/
theorem clusterSurgeryPolynomial_roots (k : ℕ) {a : Fin (2 * k + 2) → ℝ} {A w : ℝ}
    (hw : 0 < w) (hA : 7 * w < A) (ha : ∀ i, |a i - A| ≤ w) {z : ℂ}
    (hz : (clusterSurgeryPolynomial k a A w).eval z = 0) :
    z.im ≠ 0 ∧ ‖z + (A : ℂ)‖ < 5 * w := by
  rw [clusterSurgeryPolynomial_eval, sub_eq_zero] at hz
  refine ⟨?_, clusterSurgery_root_norm_lt k hw hA ha hz⟩
  intro him
  have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
  rw [he] at hz
  exact clusterSurgery_no_real_root k hw hA ha z.re hz

/-- Positive degree guarantees a nonreal root without a root-separation assumption. -/
theorem exists_clusterSurgeryPolynomial_root (k : ℕ) {a : Fin (2 * k + 2) → ℝ} {A w : ℝ}
    (hw : 0 < w) (hA : 7 * w < A) (ha : ∀ i, |a i - A| ≤ w) :
    ∃ z : ℂ, (clusterSurgeryPolynomial k a A w).eval z = 0 ∧
      z.im ≠ 0 ∧ ‖z + (A : ℂ)‖ < 5 * w := by
  have hd : 0 < (clusterSurgeryPolynomial k a A w).natDegree := by
    rw [(clusterSurgeryPolynomial_monic_degree k a A w).2]
    omega
  obtain ⟨z, hz⟩ := Complex.exists_root (natDegree_pos_iff_degree_pos.mp hd)
  exact ⟨z, hz, clusterSurgeryPolynomial_roots k hw hA ha hz⟩

/-- The quadratic coordinate converts root confinement into transverse-depth control. -/
theorem transverse_depth_lt_of_quadratic_distance {H B : ℝ} (hH : 0 < H) (s : ℂ)
    (hb : ‖s * (s - 1) + ((H ^ 2 + 1 / 4 : ℝ) : ℂ)‖ < B) :
    |s.re - 1 / 2| < B / (2 * H) := by
  have hid : ‖s * (s - 1) + ((H ^ 2 + 1 / 4 : ℝ) : ℂ)‖ ^ 2 -
      (2 * H * (s.re - 1 / 2)) ^ 2 =
      ((s.re - 1 / 2) ^ 2 + s.im ^ 2 - H ^ 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq : (2 * H * |s.re - 1 / 2|) ^ 2 ≤
      ‖s * (s - 1) + ((H ^ 2 + 1 / 4 : ℝ) : ℂ)‖ ^ 2 := by
    rw [mul_pow, sq_abs]
    nlinarith only [hid, sq_nonneg ((s.re - 1 / 2) ^ 2 + s.im ^ 2 - H ^ 2)]
  have hlin : 2 * H * |s.re - 1 / 2| ≤
      ‖s * (s - 1) + ((H ^ 2 + 1 / 4 : ℝ) : ℂ)‖ := by
    nlinarith only [hsq, norm_nonneg (s * (s - 1) + ((H ^ 2 + 1 / 4 : ℝ) : ℂ)),
      mul_nonneg (show 0 ≤ 2 * H by positivity) (abs_nonneg (s.re - 1 / 2))]
  rw [lt_div_iff₀ (show 0 < 2 * H by positivity)]
  nlinarith only [hlin, hb]

/-- A monic degree-`n` polynomial is determined by its first `n` derivatives at zero.
Thus a nontrivial monic surgery can retain jets only through order `n-2`. -/
theorem monic_eq_of_endpoint_jets {n : ℕ} {P Q : ℂ[X]}
    (hP : P.Monic) (hQ : Q.Monic) (hPn : P.natDegree = n) (hQn : Q.natDegree = n)
    (hj : ∀ j < n, iteratedDeriv j (fun z => P.eval z) 0 =
      iteratedDeriv j (fun z => Q.eval z) 0) : P = Q := by
  apply Polynomial.ext
  intro j
  rcases lt_trichotomy j n with h | rfl | h
  · have he := hj j h
    simp only [HTGeometry.iteratedDeriv_polynomial_eval,
      ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative,
      zero_add, Nat.descFactorial_self, nsmul_eq_mul] at he
    exact mul_left_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero j)) he
  · simpa only [hPn, hQn] using hP.coeff_natDegree.trans hQ.coeff_natDegree.symm
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.exists_clusterSurgeryPolynomial_root
#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.monic_eq_of_endpoint_jets
