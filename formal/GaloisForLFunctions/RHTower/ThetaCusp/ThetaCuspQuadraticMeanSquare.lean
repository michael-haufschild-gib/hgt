import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargedBoundaryGrowth
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mean-square bounds for the complete damped quadratic phase sum

An exact oscillatory pair integral, the quadratic frequency gap, and a
summable reciprocal-square row bound give an estimate independent of the
number of source atoms. Dominated convergence keeps the complete series.
At Gaussian scale pi/N^2, the degree-k coefficient energy has order
N^(2k+1), giving N^9 for the degree-four source channel.

This supplies the compact-interval input for the charged-cusp source-energy
limit. It proves no positivity statement for the theta tail kernel.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open scoped BigOperators
namespace RHTower.ThetaCuspBoundaryAudit

def quadraticRowConstant : ℝ := ∑' k : ℤ, 1/(k:ℝ)^2

theorem quadraticRowConstant_nonneg : 0 ≤ quadraticRowConstant := by
  exact tsum_nonneg fun k => by positivity

theorem sq_sub_le_abs_sq_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x-y)^2 ≤ |x^2-y^2| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr ((sq_le_sq₀ hx hy).2 h))]
    nlinarith only [mul_nonneg hx (sub_nonneg.mpr h)]
  · rw [abs_of_nonneg (sub_nonneg.mpr ((sq_le_sq₀ hy hx).2 h))]
    nlinarith only [mul_nonneg hy (sub_nonneg.mpr h)]

theorem quadratic_reciprocal_row_le (s : Finset ℕ) (n : ℕ) :
    (∑ m ∈ s, 1/|(m:ℝ)^2-(n:ℝ)^2|) ≤ quadraticRowConstant := by
  classical
  have hs : Summable (fun k : ℤ => 1/(k:ℝ)^2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hinj : Function.Injective (fun m : ℕ => (m:ℤ)-(n:ℤ)) := by
    intro a b h
    dsimp at h
    omega
  calc
    _ ≤ ∑ m ∈ s, 1/(((m:ℤ)-(n:ℤ):ℤ):ℝ)^2 := by
      apply Finset.sum_le_sum
      intro m hm
      push_cast
      by_cases he : m=n
      · simp [he]
      · have hmn : (m:ℝ)-(n:ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast he)
        exact one_div_le_one_div_of_le (sq_pos_of_ne_zero hmn)
          (sq_sub_le_abs_sq_sub (Nat.cast_nonneg m) (Nat.cast_nonneg n))
    _ = ∑ k ∈ s.image (fun m : ℕ => (m:ℤ)-(n:ℤ)), 1/(k:ℝ)^2 :=
      (Finset.sum_image (f := fun k : ℤ => 1/(k:ℝ)^2) (s := s)
        (fun a _ b _ h => hinj h)).symm
    _ ≤ quadraticRowConstant := hs.sum_le_tsum _ (fun k hk => by positivity)

def dampedQuadraticMode (a b : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((-a:ℂ)+(b:ℂ)*Complex.I)*(n:ℂ)^2*(t:ℂ))

theorem dampedQuadraticMode_norm_le {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : ‖dampedQuadraticMode a b n t‖ ≤ 1 := by
  rw [dampedQuadraticMode, Complex.norm_exp, Real.exp_le_one_iff]
  have hr : (((-a:ℂ)+(b:ℂ)*Complex.I)*(n:ℂ)^2*(t:ℂ)).re = -a*(n:ℝ)^2*t := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
  rw [hr]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _)) ht

theorem norm_integral_damped_exp_le {z : ℂ} (hz : z.re ≤ 0)
    (him : z.im ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in (0:ℝ)..T, Complex.exp (z*(t:ℂ))‖ ≤ 2/|z.im| := by
  have hz0 : z ≠ 0 := by intro h; exact him (by simp [h])
  have hn : ‖Complex.exp (z*(T:ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simpa using mul_nonpos_of_nonpos_of_nonneg hz hT
  rw [integral_exp_mul_complex hz0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, norm_div]
  calc
    _ ≤ (‖Complex.exp (z*(T:ℂ))‖+‖(1:ℂ)‖)/‖z‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 2/‖z‖ := div_le_div_of_nonneg_right
      (by rw [norm_one]; linarith only [hn]) (norm_nonneg z)
    _ ≤ 2/|z.im| := div_le_div_of_nonneg_left (by norm_num) (abs_pos.mpr him)
      (Complex.abs_im_le_norm z)

theorem dampedQuadraticMode_pair (a b : ℝ) (n m : ℕ) (t : ℝ) :
    dampedQuadraticMode a b n t*star (dampedQuadraticMode a b m t) =
      Complex.exp (((-a:ℂ)*((n:ℂ)^2+(m:ℂ)^2)+
        (b:ℂ)*((n:ℂ)^2-(m:ℂ)^2)*Complex.I)*(t:ℂ)) := by
  unfold dampedQuadraticMode
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_add, map_neg, map_pow, Complex.conj_ofReal,
    Complex.conj_natCast, Complex.conj_I]
  ring

theorem norm_integral_dampedQuadraticMode_pair_le {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≠ 0) {n m : ℕ} (hnm : n ≠ m) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in (0:ℝ)..T, dampedQuadraticMode a b n t*star (dampedQuadraticMode a b m t)‖ ≤
      (2/|b|)*(1/|(n:ℝ)^2-(m:ℝ)^2|) := by
  let z : ℂ := (-a:ℂ)*((n:ℂ)^2+(m:ℂ)^2)+
    (b:ℂ)*((n:ℂ)^2-(m:ℂ)^2)*Complex.I
  have hre : z.re = -a*((n:ℝ)^2+(m:ℝ)^2) := by
    simp [z, pow_two, Complex.mul_re, Complex.mul_im]
  have him : z.im = b*((n:ℝ)^2-(m:ℝ)^2) := by
    simp [z, pow_two, Complex.mul_re, Complex.mul_im]
  have hsq : (n:ℝ)^2-(m:ℝ)^2 ≠ 0 := by
    intro h
    have he := (sq_eq_sq₀ (Nat.cast_nonneg n) (Nat.cast_nonneg m)).mp (sub_eq_zero.mp h)
    exact hnm (by exact_mod_cast he)
  simp_rw [dampedQuadraticMode_pair]
  have h := norm_integral_damped_exp_le
    (z := z) (by rw [hre]; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (by positivity))
    (by rw [him]; exact mul_ne_zero hb hsq) hT
  rw [him, abs_mul] at h
  simpa only [div_mul_div_comm, mul_one] using h


private theorem finite_symmetric_row_bound (s : Finset ℕ) (u : ℕ → ℝ)
    (w : ℕ → ℕ → ℝ) (R : ℝ)
    (hw0 : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ w i j)
    (hws : ∀ i ∈ s, ∀ j ∈ s, w i j = w j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, w i j ≤ R) :
    (∑ i ∈ s, ∑ j ∈ s, u i*u j*w i j) ≤ R*∑ i ∈ s, (u i)^2 := by
  have hfirst : (∑ i ∈ s, ∑ j ∈ s, (u i)^2*w i j) ≤ R*∑ i ∈ s, (u i)^2 := by
    calc
      _ = ∑ i ∈ s, (u i)^2*(∑ j ∈ s, w i j) := by simp only [Finset.mul_sum]
      _ ≤ ∑ i ∈ s, (u i)^2*R := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hsecond : (∑ i ∈ s, ∑ j ∈ s, (u j)^2*w i j) =
      ∑ i ∈ s, ∑ j ∈ s, (u i)^2*w i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [hws j hj i hi]
  have hdouble : 2*(∑ i ∈ s, ∑ j ∈ s, u i*u j*w i j) ≤
      (∑ i ∈ s, ∑ j ∈ s, (u i)^2*w i j)+
        ∑ i ∈ s, ∑ j ∈ s, (u j)^2*w i j := by
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, 2*(u i*u j*w i j) := by simp only [Finset.mul_sum]
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ((u i)^2*w i j+(u j)^2*w i j) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have h := mul_le_mul_of_nonneg_right (two_mul_le_add_sq (u i) (u j)) (hw0 i hi j hj)
        simpa only [add_mul, mul_assoc] using h
      _ = _ := by simp only [Finset.sum_add_distrib]
  rw [hsecond] at hdouble
  linarith only [hfirst, hdouble]

private def quadraticMajorant (b T : ℝ) (n m : ℕ) : ℝ :=
  (if n=m then T else 0)+(2/|b|)*(1/|(n:ℝ)^2-(m:ℝ)^2|)

private theorem quadraticMajorant_row (s : Finset ℕ) (b T : ℝ) {n : ℕ} (hn : n ∈ s) :
    (∑ m ∈ s, quadraticMajorant b T n m) ≤ T+(2/|b|)*quadraticRowConstant := by
  classical
  simp only [quadraticMajorant, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hd : (∑ m ∈ s, if n=m then T else 0) = T := by simp [hn]
  rw [hd]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [abs_sub_comm] using quadratic_reciprocal_row_le s n

private theorem integral_pair_majorant {a b T : ℝ} (ha : 0 ≤ a) (hb : b ≠ 0)
    (hT : 0 ≤ T) (n m : ℕ) :
    ‖∫ t in (0:ℝ)..T, dampedQuadraticMode a b n t*star (dampedQuadraticMode a b m t)‖ ≤
      quadraticMajorant b T n m := by
  by_cases hnm : n=m
  · subst m
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := T)
      (C := 1) (f := fun t => dampedQuadraticMode a b n t*star (dampedQuadraticMode a b n t))
      (fun t ht => by
        rw [uIoc_of_le hT] at ht
        rw [norm_mul, norm_star]
        exact mul_le_one₀ (dampedQuadraticMode_norm_le ha b n ht.1.le) (norm_nonneg _)
          (dampedQuadraticMode_norm_le ha b n ht.1.le))
    simpa [quadraticMajorant, abs_of_nonneg hT] using h
  · simpa [quadraticMajorant, hnm] using norm_integral_dampedQuadraticMode_pair_le ha hb hnm hT

def dampedQuadraticSum (s : Finset ℕ) (c : ℕ → ℂ) (a b t : ℝ) : ℂ :=
  ∑ n ∈ s, c n*dampedQuadraticMode a b n t

theorem dampedQuadraticSum_integral_norm_sq_le (s : Finset ℕ) (c : ℕ → ℂ)
    {a b T : ℝ} (ha : 0 ≤ a) (hb : b ≠ 0) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, ‖dampedQuadraticSum s c a b t‖^2) ≤
      (T+(2/|b|)*quadraticRowConstant)*(∑ n ∈ s, ‖c n‖^2) := by
  classical
  have hcont (n m : ℕ) : IntervalIntegrable
      (fun t => (c n*star (c m))*(dampedQuadraticMode a b n t*star (dampedQuadraticMode a b m t)))
      volume 0 T := by
    apply Continuous.intervalIntegrable
    unfold dampedQuadraticMode
    fun_prop
  have hpoint (t : ℝ) : ((‖dampedQuadraticSum s c a b t‖^2:ℝ):ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, (c n*star (c m))*
        (dampedQuadraticMode a b n t*star (dampedQuadraticMode a b m t)) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [dampedQuadraticSum, map_sum, Finset.sum_mul, Finset.mul_sum,
      Complex.star_def, map_mul]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => by ring
  have he : (((∫ t in (0:ℝ)..T, ‖dampedQuadraticSum s c a b t‖^2):ℝ):ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, (c n*star (c m))*
        (∫ t in (0:ℝ)..T, dampedQuadraticMode a b n t*star (dampedQuadraticMode a b m t)) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hpoint]
    rw [intervalIntegral.integral_finsetSum (f := fun n t => ∑ m ∈ s,
      (c n*star (c m))*(dampedQuadraticMode a b n t*star (dampedQuadraticMode a b m t)))
      (fun n hn => by
        apply Continuous.intervalIntegrable
        unfold dampedQuadraticMode
        fun_prop)]
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum (fun m hm => hcont n m)]
    exact Finset.sum_congr rfl fun m hm => intervalIntegral.integral_const_mul _ _
  calc
    _ ≤ ‖(((∫ t in (0:ℝ)..T, ‖dampedQuadraticSum s c a b t‖^2):ℝ):ℂ)‖ := by
      simpa only [Complex.ofReal_re] using Complex.re_le_norm
        (((∫ t in (0:ℝ)..T, ‖dampedQuadraticSum s c a b t‖^2):ℝ):ℂ)
    _ = _ := congrArg norm he
    _ ≤ ∑ n ∈ s, ∑ m ∈ s, ‖c n‖*‖c m‖*quadraticMajorant b T n m := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
      rw [norm_mul, norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (integral_pair_majorant ha hb hT n m) (by positivity)
    _ ≤ _ := finite_symmetric_row_bound s (fun n => ‖c n‖) (quadraticMajorant b T)
      (T+(2/|b|)*quadraticRowConstant)
      (fun i hi j hj => by unfold quadraticMajorant; positivity)
      (fun i hi j hj => by simp only [quadraticMajorant, eq_comm, abs_sub_comm])
      (fun i hi => quadraticMajorant_row s b T hi)


theorem summable_dampedQuadraticMode {c : ℕ → ℂ} (hc : Summable (fun n => ‖c n‖))
    {a : ℝ} (ha : 0 ≤ a) (b : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun n => c n*dampedQuadraticMode a b n t) := by
  apply Summable.of_norm_bounded hc
  intro n
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (dampedQuadraticMode_norm_le ha b n ht) (norm_nonneg (c n))

theorem dampedQuadraticSum_norm_le (s : Finset ℕ) {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖)) {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖dampedQuadraticSum s c a b t‖ ≤ ∑' n, ‖c n‖ := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n hn => ?_).trans
    (hc.sum_le_tsum _ (fun n hn => norm_nonneg _)))
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (dampedQuadraticMode_norm_le ha b n ht) (norm_nonneg (c n))

theorem tsum_dampedQuadraticMode_integral_norm_sq_le {c : ℕ → ℂ}
    (hc : Summable (fun n => ‖c n‖)) (hc2 : Summable (fun n => ‖c n‖^2))
    {a b T : ℝ} (ha : 0 ≤ a) (hb : b ≠ 0) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, ‖∑' n, c n*dampedQuadraticMode a b n t‖^2) ≤
      (T+(2/|b|)*quadraticRowConstant)*(∑' n, ‖c n‖^2) := by
  let C : ℝ := ∑' n, ‖c n‖
  have hC : 0 ≤ C := tsum_nonneg fun n => norm_nonneg _
  have hlim : Tendsto
      (fun M : ℕ => ∫ t in Ioc (0:ℝ) T, ‖dampedQuadraticSum (Finset.range M) c a b t‖^2)
      atTop (𝓝 (∫ t in Ioc (0:ℝ) T, ‖∑' n, c n*dampedQuadraticMode a b n t‖^2)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C^2)
    · intro M
      apply Continuous.aestronglyMeasurable
      unfold dampedQuadraticSum dampedQuadraticMode
      fun_prop
    · exact integrableOn_const (hs := by simp)
    · intro M
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (dampedQuadraticSum_norm_le _ hc ha b ht.1.le) 2
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (summable_dampedQuadraticMode hc ha b ht.1.le).hasSum.tendsto_sum_nat.norm.pow 2
  rw [intervalIntegral.integral_of_le hT]
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro M
  rw [← intervalIntegral.integral_of_le hT]
  refine (dampedQuadraticSum_integral_norm_sq_le _ c ha hb hT).trans ?_
  exact mul_le_mul_of_nonneg_left (hc2.sum_le_tsum _ (fun n hn => sq_nonneg _))
    (add_nonneg hT (mul_nonneg (by positivity) quadraticRowConstant_nonneg))


theorem dampedQuadraticMode_norm (a b : ℝ) (n : ℕ) (t : ℝ) :
    ‖dampedQuadraticMode a b n t‖ = Real.exp (-a*(n:ℝ)^2*t) := by
  rw [dampedQuadraticMode, Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.mul_im]

def gaussianQuadraticCoefficient (a b : ℝ) (k n : ℕ) : ℂ :=
  (n:ℂ)^k*dampedQuadraticMode a b n 1

theorem gaussianQuadraticCoefficient_norm (a b : ℝ) (k n : ℕ) :
    ‖gaussianQuadraticCoefficient a b k n‖ = (n:ℝ)^k*Real.exp (-a*(n:ℝ)^2) := by
  rw [gaussianQuadraticCoefficient, norm_mul, norm_pow, Complex.norm_natCast,
    dampedQuadraticMode_norm, mul_one]

theorem gaussianQuadraticCoefficient_norm_sq (a b : ℝ) (k n : ℕ) :
    ‖gaussianQuadraticCoefficient a b k n‖^2 = (n:ℝ)^(2*k)*Real.exp (-(2*a)*(n:ℝ)^2) := by
  rw [gaussianQuadraticCoefficient_norm, mul_pow, ← Real.exp_nat_mul, ← pow_mul]
  congr 1
  · congr 1; omega
  · congr 1; ring

theorem gaussianQuadraticCoefficient_summable {a : ℝ} (ha : 0<a) (b : ℝ) (k : ℕ) :
    Summable (fun n => ‖gaussianQuadraticCoefficient a b k n‖) := by
  simp_rw [gaussianQuadraticCoefficient_norm]
  exact summable_pow_mul_exp_neg_nat_sq k ha

theorem gaussianQuadraticCoefficient_sq_summable {a : ℝ} (ha : 0<a) (b : ℝ) (k : ℕ) :
    Summable (fun n => ‖gaussianQuadraticCoefficient a b k n‖^2) := by
  simp_rw [gaussianQuadraticCoefficient_norm_sq]
  exact summable_pow_mul_exp_neg_nat_sq (2*k) (by positivity)

theorem gaussian_square_energy_le (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 0<k) :
    thetaGaussianPowerSum (2*Real.pi/(N:ℝ)^2) (2*k) ≤
      (k.factorial:ℝ)/(2*Real.pi^k)*(N:ℝ)^(2*k+1) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have h := gaussian_even_power_sum_le (a := 2*Real.pi/(N:ℝ)^2) (by positivity) hk
  have he : 2/(2*Real.pi/(N:ℝ)^2) = (N:ℝ)^2/Real.pi := by field_simp
  have hs : Real.pi/((2*Real.pi/(N:ℝ)^2)/2) = (N:ℝ)^2 := by field_simp
  rw [he, hs, Real.sqrt_sq hNr.le] at h
  convert h using 1
  rw [pow_succ, pow_mul, div_pow]
  ring

theorem gaussianQuadraticCoefficient_energy_le (N : ℕ) (hN : 0<N)
    (b : ℝ) (k : ℕ) (hk : 0<k) :
    (∑' n, ‖gaussianQuadraticCoefficient (Real.pi/(N:ℝ)^2) b k n‖^2) ≤
      (k.factorial:ℝ)/(2*Real.pi^k)*(N:ℝ)^(2*k+1) := by
  simp_rw [gaussianQuadraticCoefficient_norm_sq]
  change thetaGaussianPowerSum (2*(Real.pi/(N:ℝ)^2)) (2*k) ≤ _
  rw [show 2*(Real.pi/(N:ℝ)^2)=2*Real.pi/(N:ℝ)^2 by ring]
  exact gaussian_square_energy_le N hN k hk

theorem gaussianQuadraticSeries_integral_le (N : ℕ) (hN : 0<N)
    {b T : ℝ} (hb : b ≠ 0) (hT : 0≤T) (k : ℕ) (hk : 0<k) :
    (∫ t in (0:ℝ)..T,
      ‖∑' n, gaussianQuadraticCoefficient (Real.pi/(N:ℝ)^2) b k n*
        dampedQuadraticMode (Real.pi/(N:ℝ)^2) b n t‖^2) ≤
      (T+(2/|b|)*quadraticRowConstant)*
        ((k.factorial:ℝ)/(2*Real.pi^k)*(N:ℝ)^(2*k+1)) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have ha : 0<Real.pi/(N:ℝ)^2 := by positivity
  exact (tsum_dampedQuadraticMode_integral_norm_sq_le
    (gaussianQuadraticCoefficient_summable ha b k)
    (gaussianQuadraticCoefficient_sq_summable ha b k) ha.le hb hT).trans
      (mul_le_mul_of_nonneg_left (gaussianQuadraticCoefficient_energy_le N hN b k hk)
        (add_nonneg hT (mul_nonneg (by positivity) quadraticRowConstant_nonneg)))

end RHTower.ThetaCuspBoundaryAudit
