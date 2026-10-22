import GaloisForLFunctions.RHTower.FactorialCriticalWindowHarmonicBounds
import GaloisForLFunctions.RHTower.FactorialCriticalAffineFrequencies
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPatternHarmonicMass

/-! The finite affine harmonic head on a narrow relative scale window.
Only equal integer harmonics retain a slow difference frequency. All remaining
entries decay inversely with the least scale; integer support counting converts
this into a coefficient-square error. -/

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private def affineWindowDifference (F : ℝ → ℝ) (p q : ℝ) (m n : ℕ) : ℝ :=
  ∑ i : Bool, ∑ j : Bool, scaleBranchSign i * scaleBranchSign j *
    (F (p * criticalAffineBranch i m - q * criticalAffineBranch j n) / 2)

private def affineWindowSum (F : ℝ → ℝ) (p q : ℝ) (m n : ℕ) : ℝ :=
  ∑ i : Bool, ∑ j : Bool, scaleBranchSign i * scaleBranchSign j *
    (F (p * criticalAffineBranch i m + q * criticalAffineBranch j n) / 2)

private theorem affine_cos_integrable (a : ℝ) :
    IntegrableOn (fun v => criticalWindowWeight v * Real.cos (2 * Real.pi * a * v))
      (Ioi 1) :=
  integrableOn_criticalWindowWeight.mul_bdd (by fun_prop)
    (Eventually.of_forall fun v => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * Real.pi * a * v))

private theorem affine_product_integrable (a c : ℝ) :
    IntegrableOn (fun v => criticalWindowWeight v *
      (Real.cos (2 * Real.pi * a * v) * Real.cos (2 * Real.pi * c * v))) (Ioi 1) := by
  have h := (affine_cos_integrable a).mul_bdd
    (by fun_prop : AEStronglyMeasurable (fun v => Real.cos (2 * Real.pi * c * v))
      (volume.restrict (Ioi (1 : ℝ))))
    (Eventually.of_forall fun v => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * Real.pi * c * v))
  simpa only [mul_assoc] using h

private theorem affine_layer_branches (S : Finset ℕ) (b : ℕ → ℝ) (p : ℕ) (v : ℝ) :
    realAffineHarmonicLayer S b p v = ∑ m ∈ S, b m * ∑ i : Bool,
      scaleBranchSign i * Real.cos (2 * Real.pi * ((p : ℝ) * criticalAffineBranch i m) * v) := by
  unfold realAffineHarmonicLayer
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Fintype.sum_bool, scaleBranchSign, criticalAffineBranch,
    Bool.false_eq_true, if_false, if_true]
  ring_nf

private theorem affine_integral_eq_matrix (S : Finset ℕ) (b : ℕ → ℝ) (p q : ℕ) :
    (∫ v, realAffineHarmonicLayer S b p v * realAffineHarmonicLayer S b q v
      ∂criticalWindowMeasure) =
      ∑ m ∈ S, ∑ n ∈ S, b m * b n *
        (affineWindowDifference (weightCosineTransform criticalWindowWeight) p q m n +
          affineWindowSum (weightCosineTransform criticalWindowWeight) p q m n) := by
  rw [integral_criticalWindowMeasure_eq_weight]
  have hexp (v : ℝ) : criticalWindowWeight v *
      (realAffineHarmonicLayer S b p v * realAffineHarmonicLayer S b q v) =
      ∑ m ∈ S, ∑ n ∈ S, b m * b n * ∑ i : Bool, ∑ j : Bool,
        scaleBranchSign i * scaleBranchSign j * (criticalWindowWeight v *
          (Real.cos (2 * Real.pi * ((p : ℝ) * criticalAffineBranch i m) * v) *
            Real.cos (2 * Real.pi * ((q : ℝ) * criticalAffineBranch j n) * v))) := by
    rw [affine_layer_branches, affine_layer_branches, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp_rw [Fintype.sum_bool]
    ring
  have hint (i j : Bool) (m n : ℕ) :=
    affine_product_integrable ((p : ℝ) * criticalAffineBranch i m)
      ((q : ℝ) * criticalAffineBranch j n)
  simp_rw [hexp]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint i j m n).const_mul _).const_mul _]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finsetSum _ fun n _ => (integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => (hint i j m n).const_mul _).const_mul _]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_const_mul, integral_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => (hint i j m n).const_mul _]
  congr 1
  unfold affineWindowDifference affineWindowSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ fun j _ => (hint i j m n).const_mul _,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_mul_cos_mul_cos integrableOn_criticalWindowWeight]
  ring

private theorem affine_signed_sum_le (f : Bool → Bool → ℝ) {C : ℝ}
    (h : ∀ i j, |f i j| ≤ C) :
    |∑ i : Bool, ∑ j : Bool, scaleBranchSign i * scaleBranchSign j * (f i j / 2)| ≤
      2 * C := by
  calc _ ≤ ∑ i : Bool, ∑ j : Bool, C / 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        have hs : |scaleBranchSign i * scaleBranchSign j| = 1 := by
          cases i <;> cases j <;> norm_num [scaleBranchSign]
        rw [abs_mul, hs, one_mul, abs_div, abs_two]
        exact div_le_div_of_nonneg_right (h i j) (by norm_num)
    _ = 2 * C := by simp only [Fintype.sum_bool]; ring

private theorem affine_sum_bound {N : ℝ} (hN : 2 ≤ N) {p q m n : ℕ}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hm : N ≤ ((m + 1 : ℕ) : ℝ)) (hn : N ≤ ((n + 1 : ℕ) : ℝ)) :
    |affineWindowSum (weightCosineTransform criticalWindowWeight) p q m n| ≤
      2 * criticalWindowCosineDecay / N := by
  have hN0 : 0 < N := by linarith
  have hf (i j : Bool) := criticalAffineBranch_sum_gap hN0.le hp hq hm hn i j
  have hterm (i j : Bool) :
      |weightCosineTransform criticalWindowWeight
        ((p : ℝ) * criticalAffineBranch i m + q * criticalAffineBranch j n)| ≤
          criticalWindowCosineDecay / N := by
    have hgap : N ≤ |(p : ℝ) * criticalAffineBranch i m + q * criticalAffineBranch j n| :=
      (show N ≤ (p : ℝ) * criticalAffineBranch i m + q * criticalAffineBranch j n by
        linarith [hf i j]).trans (le_abs_self _)
    exact (abs_criticalWindowWeight_cosine_le_inv (by linarith [hgap])).trans
      (div_le_div_of_nonneg_left criticalWindowCosineDecay_nonneg hN0 hgap)
  exact (affine_signed_sum_le _ hterm).trans_eq (by ring)

private theorem affine_difference_bound {N δ : ℝ} (hN : 2 ≤ N) (hδ : 0 ≤ δ)
    {p q m n : ℕ} (hpq : p ≠ q)
    (hsmall : ((p : ℝ) + q) * δ ≤ 1 / 4) (hlarge : (p : ℝ) + q ≤ N)
    (hm : N ≤ ((m + 1 : ℕ) : ℝ) ∧ ((m + 1 : ℕ) : ℝ) ≤ (1 + δ) * N)
    (hn : N ≤ ((n + 1 : ℕ) : ℝ) ∧ ((n + 1 : ℕ) : ℝ) ≤ (1 + δ) * N) :
    |affineWindowDifference (weightCosineTransform criticalWindowWeight) p q m n| ≤
      4 * criticalWindowCosineDecay / N := by
  have hN0 : 0 < N := by linarith
  have hterm (i j : Bool) :
      |weightCosineTransform criticalWindowWeight
        ((p : ℝ) * criticalAffineBranch i m - q * criticalAffineBranch j n)| ≤
          2 * criticalWindowCosineDecay / N := by
    have hgap := criticalAffineBranch_difference_gap hN0 hδ hpq hsmall hlarge hm hn i j
    calc _ ≤ criticalWindowCosineDecay /
          |(p : ℝ) * criticalAffineBranch i m - q * criticalAffineBranch j n| :=
        abs_criticalWindowWeight_cosine_le_inv (by linarith [hgap])
      _ ≤ criticalWindowCosineDecay / (N / 2) :=
        div_le_div_of_nonneg_left criticalWindowCosineDecay_nonneg (by positivity) hgap
      _ = _ := by ring
  exact (affine_signed_sum_le _ hterm).trans_eq (by ring)

private def affineSlowEntry (p m n : ℕ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), criticalWindowWeight v *
    Real.cos (2 * Real.pi * p * ((m : ℝ) - n) * v) *
      (1 - Real.cos (2 * Real.pi * p * v / 12))

private theorem affine_slow_integrable (p m n : ℕ) :
    IntegrableOn (fun v => criticalWindowWeight v *
      Real.cos (2 * Real.pi * p * ((m : ℝ) - n) * v) *
        (1 - Real.cos (2 * Real.pi * p * v / 12))) (Ioi 1) := by
  have hcos : IntegrableOn (fun v => criticalWindowWeight v *
      Real.cos (2 * Real.pi * p * ((m : ℝ) - n) * v)) (Ioi 1) := by
    simpa only [mul_assoc] using affine_cos_integrable ((p : ℝ) * ((m : ℝ) - n))
  apply hcos.mul_bdd (by fun_prop)
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
  linarith [Real.neg_one_le_cos (2 * Real.pi * p * v / 12)]

private theorem affine_difference_resonant (p m n : ℕ) :
    affineWindowDifference (weightCosineTransform criticalWindowWeight) p p m n =
      affineSlowEntry p m n := by
  let f (i j : Bool) (v : ℝ) := scaleBranchSign i * scaleBranchSign j *
    (criticalWindowWeight v * Real.cos (2 * Real.pi *
      ((p : ℝ) * criticalAffineBranch i m - p * criticalAffineBranch j n) * v) / 2)
  have hi (i j : Bool) : IntegrableOn (f i j) (Ioi 1) :=
    ((affine_cos_integrable _).div_const 2).const_mul _
  have he : affineWindowDifference (weightCosineTransform criticalWindowWeight) p p m n =
      ∫ v in Ioi (1 : ℝ), ∑ i : Bool, ∑ j : Bool, f i j v := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
    unfold affineWindowDifference
    apply Finset.sum_congr rfl
    intro i hi'
    rw [integral_finsetSum _ fun j _ => hi i j]
    apply Finset.sum_congr rfl
    intro j hj'
    dsimp only [f]
    rw [integral_const_mul, integral_div]
    rfl
  rw [he]
  unfold affineSlowEntry
  apply integral_congr_ae
  filter_upwards [] with v
  let a := 2 * Real.pi * p * ((m : ℝ) - n) * v
  let c := 2 * Real.pi * p * v / 12
  have hfreq (i j : Bool) : 2 * Real.pi *
      ((p : ℝ) * criticalAffineBranch i m - p * criticalAffineBranch j n) * v =
      a + (if i then c else 0) - (if j then c else 0) := by
    cases i <;> cases j <;> simp only [criticalAffineBranch, Bool.false_eq_true,
      if_false, if_true] <;> dsimp only [a, c] <;> push_cast <;> ring
  dsimp only [f]
  simp_rw [hfreq]
  simp only [Fintype.sum_bool, scaleBranchSign, Bool.false_eq_true, if_false,
    if_true, add_zero, sub_zero, add_sub_cancel_right]
  change _ = criticalWindowWeight v * Real.cos a * (1 - Real.cos c)
  rw [Real.cos_add, Real.cos_sub]
  ring

private theorem affine_slow_matrix_eq_mass (S : Finset ℕ) (b : ℕ → ℝ) (p : ℕ) :
    (∑ m ∈ S, ∑ n ∈ S, b m * b n * affineSlowEntry p m n) =
      factorialCriticalPatternHarmonicMass S b p := by
  let f (m n : ℕ) (v : ℝ) := b m * b n * (criticalWindowWeight v *
    Real.cos (2 * Real.pi * p * ((m : ℝ) - n) * v) *
      (1 - Real.cos (2 * Real.pi * p * v / 12)))
  have hi (m n : ℕ) : IntegrableOn (f m n) (Ioi 1) :=
    (affine_slow_integrable p m n).const_mul _
  have he : (∑ m ∈ S, ∑ n ∈ S, b m * b n * affineSlowEntry p m n) =
      ∫ v in Ioi (1 : ℝ), ∑ m ∈ S, ∑ n ∈ S, f m n v := by
    rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => hi m n]
    apply Finset.sum_congr rfl
    intro m hm
    rw [integral_finsetSum _ fun n _ => hi m n]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [f, affineSlowEntry]
    rw [integral_const_mul]
  rw [he]
  unfold factorialCriticalPatternHarmonicMass
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [factorialCriticalPatternDensity_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [f, criticalWindowWeight]
  rw [show 2 * Real.pi * ((m : ℝ) - n) * ((p : ℝ) * v) =
    2 * Real.pi * p * ((m : ℝ) - n) * v by ring]
  ring

/-- Finite affine harmonic correlations approach the exact pattern mass uniformly
on narrow relative windows, with dimension paid only by the relative width. -/
theorem abs_integral_criticalWindow_affine_sub_mass_le
    {S : Finset ℕ} (b : ℕ → ℝ) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {N δ : ℝ} (hN : 2 ≤ N) (hδ : 0 ≤ δ)
    (hsmall : ((p : ℝ) + q) * δ ≤ 1 / 4) (hlarge : (p : ℝ) + q ≤ N)
    (hS : ∀ n ∈ S, N ≤ ((n + 1 : ℕ) : ℝ) ∧
      ((n + 1 : ℕ) : ℝ) ≤ (1 + δ) * N) :
    |(∫ v, realAffineHarmonicLayer S b p v * realAffineHarmonicLayer S b q v
      ∂criticalWindowMeasure) -
      (if p = q then factorialCriticalPatternHarmonicMass S b p else 0)| ≤
      6 * criticalWindowCosineDecay * (δ + 1 / N) * ∑ n ∈ S, b n ^ 2 := by
  let F := weightCosineTransform criticalWindowWeight
  let K (m n : ℕ) := affineWindowDifference F p q m n + affineWindowSum F p q m n -
    (if p = q then affineSlowEntry p m n else 0)
  let C := 6 * criticalWindowCosineDecay / N
  have hN0 : 0 < N := by linarith
  have hC : 0 ≤ C :=
    div_nonneg (mul_nonneg (by norm_num) criticalWindowCosineDecay_nonneg) hN0.le
  have hK (m : ℕ) (hm : m ∈ S) (n : ℕ) (hn : n ∈ S) : |K m n| ≤ C := by
    have hsum := affine_sum_bound hN hp hq (hS m hm).1 (hS n hn).1
    by_cases he : p = q
    · subst q
      dsimp only [K, F]
      rw [if_pos rfl, affine_difference_resonant, add_sub_cancel_left]
      apply hsum.trans
      dsimp only [C]
      exact div_le_div_of_nonneg_right (by linarith [criticalWindowCosineDecay_nonneg]) hN0.le
    · have hdiff := affine_difference_bound hN hδ he hsmall hlarge (hS m hm) (hS n hn)
      dsimp only [K, F]
      rw [if_neg he, sub_zero]
      exact (abs_add_le _ _).trans ((add_le_add hdiff hsum).trans_eq (by dsimp [C]; ring))
  have hslow : (if p = q then factorialCriticalPatternHarmonicMass S b p else 0) =
      ∑ m ∈ S, ∑ n ∈ S, b m * b n * (if p = q then affineSlowEntry p m n else 0) := by
    by_cases he : p = q
    · simp only [if_pos he]
      exact (affine_slow_matrix_eq_mass S b p).symm
    · simp only [if_neg he, mul_zero, Finset.sum_const_zero]
  rw [affine_integral_eq_matrix, hslow, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  change |∑ m ∈ S, ∑ n ∈ S, b m * b n * K m n| ≤ _
  calc _ ≤ ∑ m ∈ S, ∑ n ∈ S, |b m| * |b n| * C := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        simp only [abs_mul]
        exact mul_le_mul_of_nonneg_left (hK m hm n hn) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = C * (∑ n ∈ S, |b n|) ^ 2 := by
        rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
    _ ≤ C * ((δ * N + 1) * ∑ n ∈ S, b n ^ 2) :=
        mul_le_mul_of_nonneg_left (sq_sum_abs_le_critical_scale_window hN0.le hδ S b hS) hC
    _ = _ := by dsimp only [C]; field_simp [ne_of_gt hN0]; ring

end GaloisForLFunctions.ArithmeticPositivityTheory
