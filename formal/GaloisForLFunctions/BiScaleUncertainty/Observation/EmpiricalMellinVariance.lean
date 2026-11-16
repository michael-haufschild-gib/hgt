import GaloisForLFunctions.HilbertMetric.Optimization.WeightedSimplexResponse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential

/-!
# Empirical Mellin moments under finite product sampling

Independent samples use the positive simplex sampling law. Factorization
of finite sums proves unbiasedness and exact complex covariance. Mellin
characters then give the full mean-square error on every vertical line;
opposite phases attain the reciprocal-sample-size bound on the unit line.
-/

open Complex
open scoped BigOperators
open Finset
open GaloisForLFunctions.HilbertMetric.Optimization
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section
variable {d N : ℕ}

/-- The literal product distribution of independent simplex samples. -/
def independentSamplingWeight (c : Fin (d+1) → ℝ) (N : ℕ) (ω : Fin N → Fin (d+1)) : ℝ :=
  ∏ i, simplexSampling c (ω i)

def finiteSampleExpectation (c : Fin (d+1) → ℝ) (N : ℕ)
    (F : (Fin N → Fin (d+1)) → ℂ) : ℂ :=
  ∑ ω, (independentSamplingWeight c N ω : ℂ) * F ω

def singleSampleExpectation (c : Fin (d+1) → ℝ) (f : Fin (d+1) → ℂ) : ℂ :=
  ∑ x, (simplexSampling c x : ℂ) * f x

lemma singleSampleExpectation_one (c : Fin (d+1) → ℝ) :
    singleSampleExpectation c (fun _ => 1) = 1 := by
  simp only [singleSampleExpectation, mul_one, ← Complex.ofReal_sum,
    simplexSampling_sum, Complex.ofReal_one]

/-- Independence is proved from the finite product, rather than assumed. -/
theorem finiteSampleExpectation_product (c : Fin (d+1) → ℝ)
    (f : Fin N → Fin (d+1) → ℂ) :
    finiteSampleExpectation c N (fun ω => ∏ i, f i (ω i)) =
      ∏ i, singleSampleExpectation c (f i) := by
  simp only [finiteSampleExpectation, independentSamplingWeight, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib, singleSampleExpectation]
  exact (Fintype.prod_sum (fun (i : Fin N) (x : Fin (d+1)) =>
    (simplexSampling c x : ℂ) * f i x)).symm

lemma finiteSampleExpectation_one (c : Fin (d+1) → ℝ) (N : ℕ) :
    finiteSampleExpectation c N (fun _ => 1) = 1 := by
  have h := finiteSampleExpectation_product (N := N) c (fun _ _ => 1)
  simpa only [Finset.prod_const_one, singleSampleExpectation_one] using h

lemma finiteSampleExpectation_add (c : Fin (d+1) → ℝ) (F G : (Fin N → Fin (d+1)) → ℂ) :
    finiteSampleExpectation c N (fun ω => F ω + G ω) =
      finiteSampleExpectation c N F + finiteSampleExpectation c N G := by
  simp only [finiteSampleExpectation, mul_add, Finset.sum_add_distrib]

lemma finiteSampleExpectation_sum {ι : Type*} [Fintype ι] (c : Fin (d+1) → ℝ)
    (F : ι → (Fin N → Fin (d+1)) → ℂ) :
    finiteSampleExpectation c N (fun ω => ∑ i, F i ω) =
      ∑ i, finiteSampleExpectation c N (F i) := by
  simp only [finiteSampleExpectation, Finset.mul_sum]
  exact Finset.sum_comm

lemma finiteSampleExpectation_const_mul (c : Fin (d+1) → ℝ) (a : ℂ)
    (F : (Fin N → Fin (d+1)) → ℂ) :
    finiteSampleExpectation c N (fun ω => a * F ω) = a * finiteSampleExpectation c N F := by
  simp only [finiteSampleExpectation, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma singleSampleExpectation_ite (c : Fin (d+1) → ℝ) (p : Prop) [Decidable p]
    (f g : Fin (d+1) → ℂ) :
    singleSampleExpectation c (fun x => if p then f x else g x) =
      if p then singleSampleExpectation c f else singleSampleExpectation c g := by
  split_ifs <;> rfl

lemma finiteSampleExpectation_coordinate (c : Fin (d+1) → ℝ)
    (f : Fin (d+1) → ℂ) (i : Fin N) :
    finiteSampleExpectation c N (fun ω => f (ω i)) = singleSampleExpectation c f := by
  have h := finiteSampleExpectation_product c (fun j x => if j = i then f x else 1)
  simpa only [singleSampleExpectation_ite, singleSampleExpectation_one,
    Finset.prod_ite_eq', Finset.mem_univ, if_true] using h

lemma finiteSampleExpectation_coordinate_mul (c : Fin (d+1) → ℝ)
    (f g : Fin (d+1) → ℂ) (i j : Fin N) :
    finiteSampleExpectation c N (fun ω => f (ω i) * g (ω j)) =
      if i = j then singleSampleExpectation c (fun x => f x * g x)
      else singleSampleExpectation c f * singleSampleExpectation c g := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact finiteSampleExpectation_coordinate c (fun x => f x * g x) i
  · rw [if_neg hij]
    have h := finiteSampleExpectation_product c
      (fun k x => (if k = i then f x else 1) * (if k = j then g x else 1))
    simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true] at h
    rw [h]
    have he (k : Fin N) : singleSampleExpectation c
        (fun x => (if k = i then f x else 1) * (if k = j then g x else 1)) =
        (if k = i then singleSampleExpectation c f else 1) *
          (if k = j then singleSampleExpectation c g else 1) := by
      by_cases hi : k = i
      · subst k
        simp [hij]
      · by_cases hj : k = j
        · subst k
          simp [hi]
        · simp only [if_neg hi, if_neg hj, one_mul, singleSampleExpectation_one]
    simp only [he, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

lemma singleSampleExpectation_sub_const (c : Fin (d+1) → ℝ) (f : Fin (d+1) → ℂ) (a : ℂ) :
    singleSampleExpectation c (fun x => f x - a) = singleSampleExpectation c f - a := by
  have hp : ∑ x, (simplexSampling c x : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, simplexSampling_sum, Complex.ofReal_one]
  simp only [singleSampleExpectation, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hp, one_mul]

lemma singleSampleExpectation_centered_product (c : Fin (d+1) → ℝ)
    (f g : Fin (d+1) → ℂ) :
    singleSampleExpectation c (fun x =>
      (f x - singleSampleExpectation c f) * (g x - singleSampleExpectation c g)) =
      singleSampleExpectation c (fun x => f x * g x) -
        singleSampleExpectation c f * singleSampleExpectation c g := by
  have hp : ∑ x, (simplexSampling c x : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, simplexSampling_sum, Complex.ofReal_one]
  change (∑ x, (simplexSampling c x : ℂ) *
    ((f x - singleSampleExpectation c f) * (g x - singleSampleExpectation c g))) = _
  have he (x : Fin (d+1)) : (simplexSampling c x : ℂ) *
      ((f x - singleSampleExpectation c f) * (g x - singleSampleExpectation c g)) =
      (simplexSampling c x : ℂ) * (f x * g x) -
        ((simplexSampling c x : ℂ) * f x) * singleSampleExpectation c g -
        singleSampleExpectation c f * ((simplexSampling c x : ℂ) * g x) +
        (simplexSampling c x : ℂ) * (singleSampleExpectation c f * singleSampleExpectation c g) := by
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hp, one_mul]
  change singleSampleExpectation c (fun x => f x * g x) -
    singleSampleExpectation c f * singleSampleExpectation c g -
    singleSampleExpectation c f * singleSampleExpectation c g +
    singleSampleExpectation c f * singleSampleExpectation c g = _
  ring

/-- The covariance of different coordinates vanishes exactly. -/
lemma finiteSampleExpectation_centered_coordinates (c : Fin (d+1) → ℝ)
    (f g : Fin (d+1) → ℂ) (i j : Fin N) :
    finiteSampleExpectation c N (fun ω =>
      (f (ω i) - singleSampleExpectation c f) *
        (g (ω j) - singleSampleExpectation c g)) =
      if i = j then singleSampleExpectation c (fun x => f x * g x) -
        singleSampleExpectation c f * singleSampleExpectation c g else 0 := by
  rw [finiteSampleExpectation_coordinate_mul c
    (fun x => f x - singleSampleExpectation c f)
    (fun x => g x - singleSampleExpectation c g)]
  simp only [singleSampleExpectation_sub_const, sub_self, zero_mul,
    singleSampleExpectation_centered_product]

/-- Product sampling cancels every off-diagonal covariance term. -/
theorem finiteSampleExpectation_centered_sums (c : Fin (d+1) → ℝ)
    (f g : Fin (d+1) → ℂ) (N : ℕ) :
    finiteSampleExpectation c N (fun ω =>
      (∑ i, (f (ω i) - singleSampleExpectation c f)) *
        (∑ j, (g (ω j) - singleSampleExpectation c g))) =
      N * (singleSampleExpectation c (fun x => f x * g x) -
        singleSampleExpectation c f * singleSampleExpectation c g) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [finiteSampleExpectation_sum]
  simp_rw [finiteSampleExpectation_sum, finiteSampleExpectation_centered_coordinates]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Empirical moment from a nonempty sample. -/
def empiricalMoment (f : Fin (d+1) → ℂ) (ω : Fin (N+1) → Fin (d+1)) : ℂ :=
  (∑ i, f (ω i)) / (N+1 : ℂ)

/-- Exact unbiasedness of the empirical moment. -/
theorem empiricalMoment_unbiased (c : Fin (d+1) → ℝ) (f : Fin (d+1) → ℂ) (N : ℕ) :
    finiteSampleExpectation c (N+1) (empiricalMoment f) = singleSampleExpectation c f := by
  unfold empiricalMoment
  simp_rw [div_eq_mul_inv, mul_comm _ (N+1 : ℂ)⁻¹]
  rw [finiteSampleExpectation_const_mul, finiteSampleExpectation_sum]
  simp only [finiteSampleExpectation_coordinate, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero N), one_mul]

lemma empiricalMoment_center (c : Fin (d+1) → ℝ) (f : Fin (d+1) → ℂ)
    (ω : Fin (N+1) → Fin (d+1)) :
    empiricalMoment f ω - singleSampleExpectation c f =
      (N+1 : ℂ)⁻¹ * ∑ i, (f (ω i) - singleSampleExpectation c f) := by
  simp only [empiricalMoment, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp [show (N+1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero N]

/-- Exact covariance at sample size `N+1`, for arbitrary complex observables. -/
theorem empiricalMoment_covariance (c : Fin (d+1) → ℝ) (f g : Fin (d+1) → ℂ) (N : ℕ) :
    finiteSampleExpectation c (N+1) (fun ω =>
      (empiricalMoment f ω - singleSampleExpectation c f) *
        (empiricalMoment g ω - singleSampleExpectation c g)) =
      (singleSampleExpectation c (fun x => f x * g x) -
        singleSampleExpectation c f * singleSampleExpectation c g) / (N+1 : ℂ) := by
  simp_rw [empiricalMoment_center]
  have he (u v : ℂ) : (N+1 : ℂ)⁻¹*u*((N+1 : ℂ)⁻¹*v) =
      (N+1 : ℂ)⁻¹^2*(u*v) := by ring
  simp_rw [he]
  rw [finiteSampleExpectation_const_mul, finiteSampleExpectation_centered_sums]
  push_cast
  field_simp [show (N+1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero N]

lemma singleSampleExpectation_conj (c : Fin (d+1) → ℝ) (f : Fin (d+1) → ℂ) :
    singleSampleExpectation c (fun x => (starRingEnd ℂ) (f x)) = (starRingEnd ℂ) (singleSampleExpectation c f) := by
  simp only [singleSampleExpectation, map_sum, map_mul, Complex.conj_ofReal]

lemma empiricalMoment_conj (f : Fin (d+1) → ℂ) (ω : Fin (N+1) → Fin (d+1)) :
    empiricalMoment (fun x => (starRingEnd ℂ) (f x)) ω = (starRingEnd ℂ) (empiricalMoment f ω) := by
  simp only [empiricalMoment, map_div₀, map_sum, map_add, map_natCast, map_one]

/-- Exact mean-square error of the empirical moment under the constructed product law. -/
theorem empiricalMoment_variance (c : Fin (d+1) → ℝ) (f : Fin (d+1) → ℂ) (N : ℕ) :
    (∑ ω, independentSamplingWeight c (N+1) ω *
      ‖empiricalMoment f ω - singleSampleExpectation c f‖^2) =
      ((∑ x, simplexSampling c x * ‖f x‖^2) - ‖singleSampleExpectation c f‖^2) /
        (N+1 : ℝ) := by
  have h := empiricalMoment_covariance c f (fun x => (starRingEnd ℂ) (f x)) N
  simp_rw [singleSampleExpectation_conj, empiricalMoment_conj, ← map_sub,
    Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  simp only [finiteSampleExpectation, singleSampleExpectation,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- A Mellin character of a positive observation `exp x`. -/
def mellinCharacter (x σ t : ℝ) : ℂ := Complex.exp (((σ : ℂ) + I*t) * x)

lemma mellinCharacter_norm_sq (x σ t : ℝ) :
    ‖mellinCharacter x σ t‖^2 = Real.exp (2*σ*x) := by
  rw [mellinCharacter, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Unbiased empirical Mellin estimation on any vertical line. -/
theorem empiricalMellin_unbiased (c x : Fin (d+1) → ℝ) (σ t : ℝ) (N : ℕ) :
    finiteSampleExpectation c (N+1) (empiricalMoment (fun i => mellinCharacter (x i) σ t)) =
      singleSampleExpectation c (fun i => mellinCharacter (x i) σ t) :=
  empiricalMoment_unbiased c _ N

/-- Mellin estimation error equals the second real moment minus the squared transform, over sample size. -/
theorem empiricalMellin_variance (c x : Fin (d+1) → ℝ) (σ t : ℝ) (N : ℕ) :
    (∑ ω, independentSamplingWeight c (N+1) ω *
      ‖empiricalMoment (fun i => mellinCharacter (x i) σ t) ω -
        singleSampleExpectation c (fun i => mellinCharacter (x i) σ t)‖^2) =
      ((∑ i, simplexSampling c i * Real.exp (2*σ*x i)) -
        ‖singleSampleExpectation c (fun i => mellinCharacter (x i) σ t)‖^2) / (N+1 : ℝ) := by
  rw [empiricalMoment_variance]
  simp only [mellinCharacter_norm_sq]

/-- On the unit-modulus Mellin line, the exact variance is at most reciprocal sample size. -/
theorem empiricalMellin_unit_line_bound (c x : Fin (d+1) → ℝ) (t : ℝ) (N : ℕ) :
    (∑ ω, independentSamplingWeight c (N+1) ω *
      ‖empiricalMoment (fun i => mellinCharacter (x i) 0 t) ω -
        singleSampleExpectation c (fun i => mellinCharacter (x i) 0 t)‖^2) ≤ 1/(N+1 : ℝ) := by
  rw [empiricalMellin_variance]
  simp only [mul_zero, zero_mul, Real.exp_zero, mul_one, simplexSampling_sum]
  exact div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) (by positivity)

/-- The constructed joint weights are nonnegative. -/
theorem independentSamplingWeight_nonneg (c : Fin (d+1) → ℝ) (N : ℕ)
    (ω : Fin N → Fin (d+1)) : 0 ≤ independentSamplingWeight c N ω :=
  Finset.prod_nonneg fun _ _ => (simplexSampling_pos c _).le

/-- The constructed joint weights sum to one. -/
theorem independentSamplingWeight_sum (c : Fin (d+1) → ℝ) (N : ℕ) :
    ∑ ω, independentSamplingWeight c N ω = 1 := by
  have h := finiteSampleExpectation_one c N
  simp only [finiteSampleExpectation, mul_one, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- Opposite unit phases attain the reciprocal-sample-size bound. -/
theorem empiricalMellin_unit_line_sharp (N : ℕ) :
    (∑ ω : Fin (N+1) → Fin 2, independentSamplingWeight (fun _ => 0) (N+1) ω *
      ‖empiricalMoment (fun i => mellinCharacter (![0, Real.pi] i) 0 1) ω -
        singleSampleExpectation (fun _ => 0)
          (fun i => mellinCharacter (![0, Real.pi] i) 0 1)‖^2) = 1/(N+1 : ℝ) := by
  rw [empiricalMellin_variance]
  have hm : singleSampleExpectation (fun _ : Fin 2 => 0)
      (fun i => mellinCharacter (![0, Real.pi] i) 0 1) = 0 := by
    unfold singleSampleExpectation
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [zero_add, add_zero, Matrix.cons_val_zero,
      mellinCharacter, Complex.ofReal_zero,
      Complex.ofReal_one, zero_add, mul_one, mul_zero, Complex.exp_zero]
    change (simplexSampling (fun _ : Fin 2 => 0) 0 : ℂ) +
      (simplexSampling (fun _ : Fin 2 => 0) 1 : ℂ) * Complex.exp (I*Real.pi) = 0
    rw [mul_comm I (Real.pi : ℂ), Complex.exp_pi_mul_I]
    simp [simplexSampling, simplexCompliance, simplexComplianceMass]
  simp only [mul_zero, zero_mul, Real.exp_zero, mul_one, simplexSampling_sum, hm,
    norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), sub_zero]

#print axioms independentSamplingWeight_sum
#print axioms empiricalMellin_unit_line_sharp
#print axioms finiteSampleExpectation_product
#print axioms empiricalMoment_variance
#print axioms empiricalMellin_unbiased
#print axioms empiricalMellin_variance
#print axioms empiricalMellin_unit_line_bound

end
end GaloisForLFunctions.BiScaleUncertainty.Observation
