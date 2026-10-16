import GaloisForLFunctions.HTGeometry.BesselJGeneratingFunction

/-!
# The Klein–Gordon light-cone identity and its entire Bessel kernel

For `w : ℂ` let `B(w) = Σ_k (−w/4)^k/(k!(k+1)!)` (`lightConeBessel`).  It is entire
(`differentiable_lightConeBessel`), `B(0) = 1`, `‖B(w)‖ ≤ e^{‖w‖/4}`, and on the real line it is the
order-one Bessel function divided by its argument: `J₁(x) = (x/2) B(x²)` (`besselJ_one_eq`).

**Beta integrals** (`integral_one_sub_sq_pow_mul_pow`):
`∫_{−1}^{1} (1 − t²)^k t^{2j} dt = 4^{k+1} k! (2j)! (k+j+1)! / (j! (2(k+j)+2)!)`, from
`(1−t²)^{k+1}t^{2j} = (1−t²)^k t^{2j} − (1−t²)^k t^{2j+2}` and induction on `k`.

**Light-cone identity** (`cos_mul_eq_lightCone`): for all complex `z, r, c, w` with `w² = r² + c`,

`cos(z w) = cos(z r) − (c z²/4) ∫_{−1}^{1} B(c z² (1 − t²)) cos(z r t) dt`.

For real time `y` and mass `m = √c` this is the Fourier side of the Klein–Gordon propagator: the
free d'Alembert part `cos(y r)` lives on the light cone `s = ±y`, and the dispersive Bessel tail lives
inside it, `|s| < y`, with density `(m² y/4) B(m²(y² − s²))`.  Both sides are even power series in `z`;
on the right the coefficient of `z^{2n+2}` is a sum over `k + j = n` of products of Bessel coefficients
and Beta integrals, and it collapses to the binomial expansion of
`((r² + c)^{n+1} − r^{2n+2})/(2n+2)!`.
-/

open Complex MeasureTheory Finset
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The entire Bessel kernel -/

/-- The `k`-th term `(−w/4)^k/(k!(k+1)!)` of the light-cone Bessel kernel. -/
def lightConeBesselTerm (w : ℂ) (k : ℕ) : ℂ :=
  (-w / 4) ^ k / ((k ! : ℂ) * ((k + 1)! : ℂ))

/-- The light-cone Bessel kernel `B(w) = Σ_k (−w/4)^k/(k!(k+1)!)`, so that `J₁(x) = (x/2) B(x²)`. -/
def lightConeBessel (w : ℂ) : ℂ := ∑' k : ℕ, lightConeBesselTerm w k

theorem norm_lightConeBesselTerm_le (w : ℂ) (k : ℕ) :
    ‖lightConeBesselTerm w k‖ ≤ (‖w‖ / 4) ^ k / k ! := by
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hk1 : (1 : ℝ) ≤ (k + 1)! := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 1))
  unfold lightConeBesselTerm
  rw [norm_div, norm_pow, norm_div, norm_neg, norm_mul, Complex.norm_natCast, Complex.norm_natCast,
    show ‖(4 : ℂ)‖ = 4 by norm_num]
  exact div_le_div_of_nonneg_left (by positivity) hk (le_mul_of_one_le_right hk.le hk1)

theorem summable_norm_lightConeBesselTerm (w : ℂ) :
    Summable fun k => ‖lightConeBesselTerm w k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_lightConeBesselTerm_le w)
    (Real.summable_pow_div_factorial _)

theorem hasSum_lightConeBessel (w : ℂ) :
    HasSum (lightConeBesselTerm w) (lightConeBessel w) :=
  (summable_norm_lightConeBesselTerm w).of_norm.hasSum

/-- `‖B(w)‖ ≤ e^{‖w‖/4}`. -/
theorem norm_lightConeBessel_le (w : ℂ) : ‖lightConeBessel w‖ ≤ Real.exp (‖w‖ / 4) :=
  tsum_of_norm_bounded (hasSum_real_exp_series (‖w‖ / 4)) (norm_lightConeBesselTerm_le w)

theorem lightConeBessel_zero : lightConeBessel 0 = 1 := by
  rw [lightConeBessel, tsum_eq_single 0 fun k hk => by
    simp [lightConeBesselTerm, zero_pow hk]]
  simp [lightConeBesselTerm]

/-- The light-cone Bessel kernel is entire. -/
theorem differentiable_lightConeBessel : Differentiable ℂ lightConeBessel := by
  intro w₀
  have hU : IsOpen (Metric.ball (0 : ℂ) (‖w₀‖ + 1)) := Metric.isOpen_ball
  have hd : DifferentiableOn ℂ (fun w => ∑' k, lightConeBesselTerm w k)
      (Metric.ball 0 (‖w₀‖ + 1)) := by
    refine differentiableOn_tsum_of_summable_norm
      (Real.summable_pow_div_factorial ((‖w₀‖ + 1) / 4))
      (fun k => (by unfold lightConeBesselTerm; fun_prop :
        Differentiable ℂ fun w => lightConeBesselTerm w k).differentiableOn) hU
      fun k w hw => (norm_lightConeBesselTerm_le w k).trans ?_
    have : ‖w‖ ≤ ‖w₀‖ + 1 := by simpa using (Metric.mem_ball.mp hw).le
    gcongr
  exact hd.differentiableAt (hU.mem_nhds (by simp))

/-- **`J₁(x) = (x/2) B(x²)`** on the real line. -/
theorem besselJ_one_eq (x : ℝ) :
    (besselJ 1 x : ℂ) = ((x : ℂ) / 2) * lightConeBessel ((x : ℂ) ^ 2) := by
  rw [besselJ_eq_mul_tsum, Complex.ofReal_mul, Complex.ofReal_tsum, lightConeBessel]
  congr 1
  · push_cast; ring
  · refine tsum_congr fun j => ?_
    unfold lightConeBesselTerm
    push_cast
    rw [show -(x : ℂ) ^ 2 / 4 = (-1) * ((x : ℂ) / 2) ^ 2 by ring, mul_pow, ← pow_mul]

/-! ## Beta integrals -/

/-- The closed form `4^{k+1} k! (2j)! (k+j+1)!/(j! (2(k+j)+2)!)` of `∫_{−1}^{1}(1−t²)^k t^{2j} dt`. -/
def betaEvenValue (k j : ℕ) : ℝ :=
  4 ^ (k + 1) * (k ! : ℝ) * ((2 * j)! : ℝ) * ((k + j + 1)! : ℝ) /
    ((j ! : ℝ) * ((2 * (k + j) + 2)! : ℝ))

theorem betaEvenValue_zero (j : ℕ) : betaEvenValue 0 j = 2 / (2 * j + 1) := by
  unfold betaEvenValue
  have h1 : (0 + j + 1)! = (j + 1) * j ! := by rw [zero_add]; exact Nat.factorial_succ j
  have h2 : (2 * (0 + j) + 2)! = (2 * j + 2) * ((2 * j + 1) * (2 * j)!) := by
    rw [zero_add, show 2 * j + 2 = (2 * j + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
  rw [h1, h2]
  have hj : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  have h2j : (0 : ℝ) < (2 * j)! := by exact_mod_cast Nat.factorial_pos (2 * j)
  push_cast
  field_simp
  ring

theorem betaEvenValue_succ (k j : ℕ) :
    betaEvenValue (k + 1) j = betaEvenValue k j - betaEvenValue k (j + 1) := by
  unfold betaEvenValue
  have e1 : (k + 1 + j + 1)! = (k + j + 1 + 1) * (k + j + 1)! := by
    rw [show k + 1 + j + 1 = (k + j + 1) + 1 by ring]; exact Nat.factorial_succ _
  have e2 : (2 * (k + 1 + j) + 2)! =
      (2 * (k + j) + 2 + 1 + 1) * ((2 * (k + j) + 2 + 1) * (2 * (k + j) + 2)!) := by
    rw [show 2 * (k + 1 + j) + 2 = (2 * (k + j) + 2 + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
  have e3 : (2 * (j + 1))! = (2 * j + 1 + 1) * ((2 * j + 1) * (2 * j)!) := by
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  have e4 : (k + (j + 1) + 1)! = (k + j + 1 + 1) * (k + j + 1)! := by
    rw [show k + (j + 1) + 1 = (k + j + 1) + 1 by ring]; exact Nat.factorial_succ _
  have e5 : (2 * (k + (j + 1)) + 2)! =
      (2 * (k + j) + 2 + 1 + 1) * ((2 * (k + j) + 2 + 1) * (2 * (k + j) + 2)!) := by
    rw [show 2 * (k + (j + 1)) + 2 = (2 * (k + j) + 2 + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
  rw [e1, e2, e3, e4, e5, Nat.factorial_succ k, Nat.factorial_succ j]
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hj : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  have h2j : (0 : ℝ) < (2 * j)! := by exact_mod_cast Nat.factorial_pos (2 * j)
  have hn : (0 : ℝ) < (k + j + 1)! := by exact_mod_cast Nat.factorial_pos (k + j + 1)
  have hm : (0 : ℝ) < (2 * (k + j) + 2)! := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp
  ring

/-- **Beta integrals**: `∫_{−1}^{1} (1 − t²)^k t^{2j} dt = 4^{k+1} k! (2j)! (k+j+1)!/(j! (2(k+j)+2)!)`. -/
theorem integral_one_sub_sq_pow_mul_pow (k j : ℕ) :
    ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ k * t ^ (2 * j) = betaEvenValue k j := by
  induction k generalizing j with
  | zero =>
    simp only [pow_zero, one_mul, integral_pow, betaEvenValue_zero, one_pow]
    rw [Odd.neg_one_pow ⟨j, rfl⟩]
    push_cast
    ring
  | succ k ih =>
    have hrec : ∀ t : ℝ, (1 - t ^ 2) ^ (k + 1) * t ^ (2 * j) =
        (1 - t ^ 2) ^ k * t ^ (2 * j) - (1 - t ^ 2) ^ k * t ^ (2 * (j + 1)) := fun t => by ring
    simp_rw [hrec]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), ih, ih, betaEvenValue_succ]

/-! ## The light-cone identity -/

theorem summable_norm_cos_term (w : ℂ) :
    Summable fun j : ℕ => ‖(-1 : ℂ) ^ j * w ^ (2 * j) / ((2 * j)! : ℂ)‖ := by
  have h := (Real.summable_pow_div_factorial ‖w‖).comp_injective
    (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0))
  refine h.congr fun j => ?_
  simp [norm_pow]

/-- One Bessel–cosine product term, factored into its coefficient and its Beta integrand. -/
theorem lightConeBesselTerm_mul_cos_term (c z r : ℂ) (t : ℝ) (k j : ℕ) :
    lightConeBesselTerm (c * z ^ 2 * (1 - (t : ℂ) ^ 2)) k *
        ((-1) ^ j * (z * r * t) ^ (2 * j) / ((2 * j)! : ℂ)) =
      ((-c * z ^ 2 / 4) ^ k / ((k ! : ℂ) * ((k + 1)! : ℂ)) *
          ((-1) ^ j * (z * r) ^ (2 * j) / ((2 * j)! : ℂ))) *
        (((1 - t ^ 2) ^ k * t ^ (2 * j) : ℝ) : ℂ) := by
  unfold lightConeBesselTerm
  rw [show -(c * z ^ 2 * (1 - (t : ℂ) ^ 2)) / 4 = (-c * z ^ 2 / 4) * (1 - (t : ℂ) ^ 2) by ring,
    mul_pow, mul_pow (z * r) (t : ℂ)]
  push_cast
  ring

/-- The coefficient of one antidiagonal term after the Beta integral. -/
theorem lightConeCoeff_mul_betaEvenValue (c z r : ℂ) {k j n : ℕ} (h : k + j = n) :
    ((-c * z ^ 2 / 4) ^ k / ((k ! : ℂ) * ((k + 1)! : ℂ)) *
        ((-1) ^ j * (z * r) ^ (2 * j) / ((2 * j)! : ℂ))) * (betaEvenValue k j : ℂ) =
      4 * (-1) ^ n * z ^ (2 * n) / ((2 * n + 2)! : ℂ) *
        (((n + 1).choose (k + 1) : ℂ) * c ^ k * (r ^ 2) ^ j) := by
  subst h
  rw [Nat.cast_choose ℂ (by omega : k + 1 ≤ k + j + 1),
    show k + j + 1 - (k + 1) = j by omega]
  unfold betaEvenValue
  rw [show -c * z ^ 2 / 4 = (-1) * c * z ^ 2 / 4 by ring, div_pow, mul_pow, mul_pow]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : ((k + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + 1)
  have hj : (j ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have h2j : ((2 * j)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * j)
  have hm : ((2 * (k + j) + 2)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

/-- The binomial collapse `c Σ_{k+j=n} C(n+1,k+1) c^k x^j = (x + c)^{n+1} − x^{n+1}`. -/
theorem mul_sum_antidiagonal_choose_succ (n : ℕ) (c x : ℂ) :
    c * ∑ kj ∈ antidiagonal n, ((n + 1).choose (kj.1 + 1) : ℂ) * c ^ kj.1 * x ^ kj.2 =
      (x + c) ^ (n + 1) - x ^ (n + 1) := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k j => ((n + 1).choose (k + 1) : ℂ) * c ^ k * x ^ j), add_comm x c, add_pow,
    Finset.sum_range_succ' _ (n + 1), Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero,
    add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.add_sub_add_right]
  ring

/-- **The Klein–Gordon light-cone identity.**  For all complex `z, r, c, w` with `w² = r² + c`,
`cos(z w) = cos(z r) − (c z²/4) ∫_{−1}^{1} B(c z² (1 − t²)) cos(z r t) dt`. -/
theorem cos_mul_eq_lightCone (z r c w : ℂ) (hw : w ^ 2 = r ^ 2 + c) :
    Complex.cos (z * w) = Complex.cos (z * r) -
      c * z ^ 2 / 4 * ∫ t in (-1 : ℝ)..1,
        lightConeBessel (c * z ^ 2 * (1 - (t : ℂ) ^ 2)) * Complex.cos (z * r * t) := by
  set S : ℕ → ℂ := fun n =>
    ∑ kj ∈ antidiagonal n, ((n + 1).choose (kj.1 + 1) : ℂ) * c ^ kj.1 * (r ^ 2) ^ kj.2 with hS
  set T : ℕ → ℂ := fun n => 4 * (-1) ^ n * z ^ (2 * n) / ((2 * n + 2)! : ℂ) * S n with hT
  -- the product series and its domination on `[-1, 1]`
  set α : ℝ → ℕ → ℂ := fun t k => lightConeBesselTerm (c * z ^ 2 * (1 - (t : ℂ) ^ 2)) k with hα
  set β : ℝ → ℕ → ℂ := fun t j => (-1) ^ j * (z * r * t) ^ (2 * j) / ((2 * j)! : ℂ) with hβ
  set F : ℕ → ℝ → ℂ := fun n t => ∑ kj ∈ antidiagonal n, α t kj.1 * β t kj.2 with hF
  set A : ℕ → ℝ := fun k => (‖c * z ^ 2‖ / 4) ^ k / k ! with hA
  set Bj : ℕ → ℝ := fun j => ‖z * r‖ ^ (2 * j) / ((2 * j)! : ℝ) with hBj
  have hAs : Summable fun k => ‖A k‖ := by
    refine (Real.summable_pow_div_factorial (‖c * z ^ 2‖ / 4)).congr fun k => ?_
    rw [Real.norm_of_nonneg (by positivity)]
  have hBs : Summable fun j => ‖Bj j‖ := by
    refine ((Real.summable_pow_div_factorial ‖z * r‖).comp_injective
      (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0))).congr fun j => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    rfl
  have hbound_sum : Summable fun n => ∑ kj ∈ antidiagonal n, A kj.1 * Bj kj.2 :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hAs hBs).of_norm
  have hαle : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, ∀ k, ‖α t k‖ ≤ A k := by
    intro t ht k
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have ht2 : |1 - t ^ 2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]
    refine (norm_lightConeBesselTerm_le _ k).trans ?_
    have : ‖c * z ^ 2 * (1 - (t : ℂ) ^ 2)‖ ≤ ‖c * z ^ 2‖ := by
      rw [norm_mul, show (1 - (t : ℂ) ^ 2) = ((1 - t ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) ht2
    simp only [hA]
    gcongr
  have hβle : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, ∀ j, ‖β t j‖ ≤ Bj j := by
    intro t ht j
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have h1 : ‖z * r * (t : ℂ)‖ ≤ ‖z * r‖ := by
      rw [norm_mul (z * r), Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) hta
    simp only [hβ, hBj, norm_div, norm_mul ((-1 : ℂ) ^ j), norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Complex.norm_natCast]
    gcongr
  have hFle : ∀ n, ∀ t ∈ Set.uIoc (-1 : ℝ) 1,
      ‖F n t‖ ≤ ∑ kj ∈ antidiagonal n, A kj.1 * Bj kj.2 := by
    intro n t ht
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun kj _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hαle t ht _) (hβle t ht _) (norm_nonneg _) (by positivity)
  have hFlim : ∀ t : ℝ, HasSum (fun n => F n t)
      (lightConeBessel (c * z ^ 2 * (1 - (t : ℂ) ^ 2)) * Complex.cos (z * r * t)) := by
    intro t
    have hα' : Summable fun k => ‖α t k‖ := summable_norm_lightConeBesselTerm _
    have hβ' : Summable fun j => ‖β t j‖ := summable_norm_cos_term _
    have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm hα' hβ').of_norm.hasSum
    rwa [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hα' hβ',
      (Complex.hasSum_cos (z * r * t)).tsum_eq] at h
  have hFc : ∀ n, Continuous (F n) := by
    intro n
    simp only [hF, hα, hβ, lightConeBesselTerm]
    fun_prop
  have hint : HasSum (fun n => ∫ t in (-1 : ℝ)..1, F n t)
      (∫ t in (-1 : ℝ)..1,
        lightConeBessel (c * z ^ 2 * (1 - (t : ℂ) ^ 2)) * Complex.cos (z * r * t)) :=
    intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => ∑ kj ∈ antidiagonal n, A kj.1 * Bj kj.2)
      (fun n => (hFc n).aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall fun t ht => hFle n t ht)
      (Filter.Eventually.of_forall fun _ _ => hbound_sum)
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun t _ => hFlim t)
  have hFint : ∀ n, ∫ t in (-1 : ℝ)..1, F n t = T n := by
    intro n
    simp only [hF]
    rw [intervalIntegral.integral_finsetSum fun kj _ =>
      Continuous.intervalIntegrable (by simp only [hα, hβ, lightConeBesselTerm]; fun_prop) _ _]
    simp only [hT, hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun kj hkj => ?_
    simp only [hα, hβ]
    simp_rw [lightConeBesselTerm_mul_cos_term]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_one_sub_sq_pow_mul_pow,
      lightConeCoeff_mul_betaEvenValue c z r (Finset.HasAntidiagonal.mem_antidiagonal.mp hkj)]
  have hTsum : HasSum T (∫ t in (-1 : ℝ)..1,
      lightConeBessel (c * z ^ 2 * (1 - (t : ℂ) ^ 2)) * Complex.cos (z * r * t)) := by
    simpa only [hFint] using hint
  -- the cosine series and the shift by one
  have hcos := (Complex.hasSum_cos (z * w)).sub (Complex.hasSum_cos (z * r))
  rw [← hasSum_nat_add_iff' 1] at hcos
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, sub_self, sub_zero] at hcos
  have hshift : (fun n : ℕ => (-1) ^ (n + 1) * (z * w) ^ (2 * (n + 1)) / ((2 * (n + 1))! : ℂ) -
      (-1) ^ (n + 1) * (z * r) ^ (2 * (n + 1)) / ((2 * (n + 1))! : ℂ)) =
      fun n => -(c * z ^ 2 / 4) * T n := by
    funext n
    have key := mul_sum_antidiagonal_choose_succ n c (r ^ 2)
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    have e1 : (z * w) ^ (2 * n + 2) = z ^ (2 * n + 2) * (r ^ 2 + c) ^ (n + 1) := by
      rw [mul_pow, show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul w, hw]
    have e2 : (z * r) ^ (2 * n + 2) = z ^ (2 * n + 2) * (r ^ 2) ^ (n + 1) := by
      rw [mul_pow, show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul r]
    rw [e1, e2, show -(c * z ^ 2 / 4) * T n =
        -((-1) ^ n * z ^ (2 * n + 2) / ((2 * n + 2)! : ℂ)) * (c * S n) by
      simp only [hT]; ring, key]
    ring
  rw [hshift] at hcos
  have h := hcos.unique (hTsum.mul_left (-(c * z ^ 2 / 4)))
  linear_combination h

/-! ## The real light-cone identity -/

/-- `B` is real on the real axis. -/
theorem lightConeBessel_ofReal_im (x : ℝ) : (lightConeBessel x).im = 0 := by
  rw [lightConeBessel, Complex.im_tsum (summable_norm_lightConeBesselTerm _).of_norm]
  refine (tsum_congr fun k => ?_).trans tsum_zero
  unfold lightConeBesselTerm
  rw [show (-(x : ℂ) / 4) ^ k / ((k ! : ℂ) * ((k + 1)! : ℂ)) =
      (((-x / 4) ^ k / ((k ! : ℝ) * ((k + 1)! : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_im]

/-- The light-cone Bessel kernel on the real axis, `J₁(x) = (x/2) B(x²)`. -/
def lightConeBesselReal (x : ℝ) : ℝ := (lightConeBessel x).re

theorem ofReal_lightConeBesselReal (x : ℝ) :
    (lightConeBesselReal x : ℂ) = lightConeBessel x :=
  Complex.ext (by simp [lightConeBesselReal]) (by simp [lightConeBessel_ofReal_im])

theorem continuous_lightConeBesselReal : Continuous lightConeBesselReal :=
  Complex.continuous_re.comp
    (differentiable_lightConeBessel.continuous.comp Complex.continuous_ofReal)

theorem lightConeBesselReal_zero : lightConeBesselReal 0 = 1 := by
  simp [lightConeBesselReal, lightConeBessel_zero]

theorem abs_lightConeBesselReal_le (x : ℝ) : |lightConeBesselReal x| ≤ Real.exp (|x| / 4) := by
  have h := norm_lightConeBessel_le (x : ℂ)
  rw [← ofReal_lightConeBesselReal, Complex.norm_real, Complex.norm_real] at h
  exact h

/-- **The real light-cone identity.**  For real `y, r` and `c ≥ 0`,
`cos(y √(r² + c)) = cos(y r) − (c y²/4) ∫_{−1}^{1} B(c y² (1 − t²)) cos(y r t) dt`. -/
theorem cos_mul_sqrt_eq_lightCone (y r c : ℝ) (hc : 0 ≤ c) :
    Real.cos (y * Real.sqrt (r ^ 2 + c)) = Real.cos (y * r) -
      c * y ^ 2 / 4 * ∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (c * y ^ 2 * (1 - t ^ 2)) * Real.cos (y * r * t) := by
  have h := cos_mul_eq_lightCone (y : ℂ) (r : ℂ) (c : ℂ) ((Real.sqrt (r ^ 2 + c) : ℝ) : ℂ)
    (by rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring)
  have hint : (∫ t in (-1 : ℝ)..1,
      lightConeBessel ((c : ℂ) * (y : ℂ) ^ 2 * (1 - (t : ℂ) ^ 2)) *
        Complex.cos ((y : ℂ) * r * t)) =
      ((∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (c * y ^ 2 * (1 - t ^ 2)) * Real.cos (y * r * t) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Complex.ofReal_mul, ofReal_lightConeBesselReal, Complex.ofReal_cos]
    push_cast
    ring_nf
  rw [hint] at h
  apply Complex.ofReal_injective
  push_cast
  exact h
