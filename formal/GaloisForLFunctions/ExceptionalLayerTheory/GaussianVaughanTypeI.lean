import GaloisForLFunctions.ExceptionalLayerTheory.GaussianVaughanBilinearCancellation
import GaloisForLFunctions.RHTower.Sieve.VaughanBlockDecomposition

/-!
# Type-I cancellation for Gaussian prime sums

The logarithmic and quadratic curvatures have the same sign. The second
derivative test therefore applies even across the stationary point.
Abel summation retains the initial Gaussian and abscissa weights.
-/

open Complex Finset RHTower RHTower.Sieve

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Curvature of the Gaussian logarithmic phase, in turns. -/
def gaussianLogCurvature (ξ t x : ℝ) : ℝ := ξ / Real.pi + t / (2 * Real.pi) / x ^ 2

/-- A uniform bound for every prefix of `[P,Q)`. -/
def gaussianTypeIBound (ξ t : ℝ) (P Q : ℕ) : ℝ :=
  min ((Q - P : ℕ) : ℝ)
    (8 * (Q - P : ℕ) * (gaussianLogCurvature ξ t P / gaussianLogCurvature ξ t Q)
      * Real.sqrt (gaussianLogCurvature ξ t Q) +
        12 / Real.sqrt (gaussianLogCurvature ξ t Q))

private theorem gaussianLogCurvature_pos {ξ t x : ℝ}
    (hξ : 0 ≤ ξ) (ht : 0 < t) (hx : 0 < x) : 0 < gaussianLogCurvature ξ t x := by
  unfold gaussianLogCurvature
  positivity

private theorem gaussianLogCurvature_antitone {ξ t x y : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) (hxy : x ≤ y) :
    gaussianLogCurvature ξ t y ≤ gaussianLogCurvature ξ t x := by
  unfold gaussianLogCurvature
  gcongr

private theorem gaussianLogPhase_deriv (ξ t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun v : ℝ => ξ / Real.pi / 2 * v ^ 2 - t / (2 * Real.pi) * Real.log v)
      (ξ / Real.pi * x - t / (2 * Real.pi) / x) x := by
  have h₁ : HasDerivAt (fun v : ℝ => ξ / Real.pi / 2 * v ^ 2)
      (ξ / Real.pi / 2 * (2 * x)) x := by
    simpa using! (hasDerivAt_pow 2 x).const_mul (ξ / Real.pi / 2)
  have h₂ : HasDerivAt (fun v : ℝ => t / (2 * Real.pi) * Real.log v)
      (t / (2 * Real.pi) * x⁻¹) x := by
    simpa using! (Real.hasDerivAt_log hx).const_mul (t / (2 * Real.pi))
  have he : ξ / Real.pi / 2 * (2 * x) - t / (2 * Real.pi) * x⁻¹ =
      ξ / Real.pi * x - t / (2 * Real.pi) / x := by ring
  simpa only [he] using! h₁.sub h₂

private theorem gaussianLogPhase_deriv₂ (ξ t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun v : ℝ => ξ / Real.pi * v - t / (2 * Real.pi) / v)
      (gaussianLogCurvature ξ t x) x := by
  have h₁ : HasDerivAt (fun v : ℝ => ξ / Real.pi * v) (ξ / Real.pi) x :=
    hasDerivAt_const_mul (ξ / Real.pi)
  have h₂ : HasDerivAt (fun v : ℝ => t / (2 * Real.pi) / v)
      (-(t / (2 * Real.pi)) / x ^ 2) x := by
    simpa only [div_eq_mul_inv, mul_neg, neg_mul] using!
      (hasDerivAt_inv hx).const_mul (t / (2 * Real.pi))
  simpa only [gaussianLogCurvature, neg_div, sub_neg_eq_add] using! h₁.sub h₂

private theorem norm_gaussianPrimePhase_zero (ξ t : ℝ) (n : ℕ) :
    ‖gaussianPrimePhase 0 ξ t n‖ = 1 := by
  simp only [gaussianPrimePhase, Complex.ofReal_zero, neg_zero, zero_mul, zero_add,
    Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]

/-- The curvature bound holds uniformly for all prefixes, with no restriction
on how close the phase derivative comes to an integer. -/
theorem norm_sum_gaussianPrimePhase_zero_prefix_le {ξ t : ℝ}
    (hξ : 0 ≤ ξ) (ht : 0 < t) {P Q R : ℕ} (hP : 1 ≤ P) (hPR : P ≤ R) (hRQ : R ≤ Q) :
    ‖∑ n ∈ Ico P R, gaussianPrimePhase 0 ξ t n‖ ≤ gaussianTypeIBound ξ t P Q := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hPQ : (P : ℝ) ≤ Q := by exact_mod_cast (hPR.trans hRQ)
  have hQ0 : (0 : ℝ) < Q := hP0.trans_le hPQ
  have hlam := gaussianLogCurvature_pos hξ ht hQ0
  have hupper := gaussianLogCurvature_antitone (ξ := ξ) ht.le hP0 hPQ
  have hratio : 1 ≤ gaussianLogCurvature ξ t P / gaussianLogCurvature ξ t Q :=
    (le_div_iff₀ hlam).mpr (by simpa using hupper)
  have hcard : ‖∑ n ∈ Ico P R, gaussianPrimePhase 0 ξ t n‖ ≤ ((R - P : ℕ) : ℝ) := by
    refine (norm_sum_le _ _).trans_eq ?_
    simp only [norm_gaussianPrimePhase_zero, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  have hlen : ((R - P : ℕ) : ℝ) ≤ (Q - P : ℕ) := by exact_mod_cast Nat.sub_le_sub_right hRQ P
  unfold gaussianTypeIBound
  refine le_min (hcard.trans hlen) ?_
  by_cases hPR' : P < R
  · by_cases hlam1 : gaussianLogCurvature ξ t Q ≤ 1
    · have hinterval {x : ℝ} (hx : x ∈ Set.Icc (P : ℝ) (P + ((R - P - 1 : ℕ) : ℝ))) :
          0 < x ∧ x ≤ Q := by
        have he : P + (R - P - 1) ≤ Q := by omega
        have he' : (P : ℝ) + ((R - P - 1 : ℕ) : ℝ) ≤ Q := by exact_mod_cast he
        exact ⟨hP0.trans_le hx.1, hx.2.trans he'⟩
      have hb := second_derivative_test'
        (fun v : ℝ => ξ / Real.pi / 2 * v ^ 2 - t / (2 * Real.pi) * Real.log v)
        (fun v => ξ / Real.pi * v - t / (2 * Real.pi) / v)
        (gaussianLogCurvature ξ t) P (R - P) (by omega)
        (hgrow := gaussianLogCurvature ξ t P / gaussianLogCurvature ξ t Q) hlam hlam1
        (fun x hx => gaussianLogPhase_deriv ξ t (hinterval hx).1.ne')
        (fun x hx => gaussianLogPhase_deriv₂ ξ t (hinterval hx).1.ne')
        (fun x hx => gaussianLogCurvature_antitone ht.le (hinterval hx).1 (hinterval hx).2)
        (fun x hx => by
          rw [div_mul_cancel₀ _ hlam.ne']
          exact gaussianLogCurvature_antitone ht.le hP0 hx.1)
      have he : (∑ n ∈ Ico P R, gaussianPrimePhase 0 ξ t n) =
          ∑ n ∈ range (R - P),
            Complex.exp (((2 * Real.pi * (ξ / Real.pi / 2 * ((P : ℝ) + n) ^ 2 -
              t / (2 * Real.pi) * Real.log ((P : ℝ) + n)) : ℝ) : ℂ) * I) := by
        rw [sum_Ico_eq_sum_range]
        apply sum_congr rfl
        intro n _
        simp only [gaussianPrimePhase, Complex.ofReal_zero, neg_zero, zero_mul, zero_add,
          Nat.cast_add]
        congr 2
        push_cast
        field_simp [Real.pi_ne_zero]
      rw [he]
      refine hb.trans ?_
      gcongr
    · have hs : 1 ≤ Real.sqrt (gaussianLogCurvature ξ t Q) :=
        Real.one_le_sqrt.mpr (le_of_not_ge hlam1)
      have hm := mul_le_mul hratio hs (by positivity) (by positivity)
      have hm' := mul_le_mul_of_nonneg_left hm
        (by positivity : 0 ≤ 8 * ((Q - P : ℕ) : ℝ))
      have hi : 0 ≤ 12 / Real.sqrt (gaussianLogCurvature ξ t Q) := by positivity
      have hN : (0 : ℝ) ≤ (Q - P : ℕ) := Nat.cast_nonneg _
      exact (hcard.trans hlen).trans (by nlinarith only [hm', hi, hN])
  · rw [Ico_eq_empty_of_le (by omega), sum_empty, norm_zero]
    positivity

/-- Abel summation costs only the weight at the first integer. -/
def gaussianWeightedTypeIBound (σ α ξ t : ℝ) (P Q : ℕ) : ℝ :=
  gaussianTypeIBound ξ t P Q * ((P : ℝ) ^ (-σ) * Real.exp (-α * (P : ℝ) ^ 2))

private theorem gaussianPrimeWeight_split (σ α ξ t : ℝ) (n : ℕ) :
    gaussianPrimeWeight σ α ξ t n =
      (((n : ℝ) ^ (-σ) * Real.exp (-α * (n : ℝ) ^ 2) : ℝ) : ℂ) *
        gaussianPrimePhase 0 ξ t n := by
  simp only [gaussianPrimeWeight, gaussianPrimePhase, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_zero, neg_zero, zero_mul, zero_add]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  rfl

/-- The weighted bound is uniform over all prefixes of the same interval. -/
theorem norm_sum_gaussianPrimeWeight_prefix_le {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hξ : 0 ≤ ξ) (ht : 0 < t)
    {P Q R : ℕ} (hP : 1 ≤ P) (hPR : P ≤ R) (hRQ : R ≤ Q) :
    ‖∑ n ∈ Ico P R, gaussianPrimeWeight σ α ξ t n‖ ≤
      gaussianWeightedTypeIBound σ α ξ t P Q := by
  simp_rw [gaussianPrimeWeight_split]
  refine abel_block_bound _ (fun n => (n : ℝ) ^ (-σ) * Real.exp (-α * (n : ℝ) ^ 2))
    P R hPR (by positivity) ?_ (gaussianTypeIBound ξ t P Q) ?_
  · intro m hm _
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    apply mul_le_mul
    · exact Real.rpow_le_rpow_of_nonpos hm0 (by norm_cast; omega) (neg_nonpos.mpr hσ)
    · apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hα)
      exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ m) 2
    · positivity
    · positivity
  · intro m hm hmR
    exact norm_sum_gaussianPrimePhase_zero_prefix_le hξ ht hP hm (hmR.trans hRQ)

/-- The logarithmic type-I coefficient costs at most twice the endpoint logarithm. -/
theorem norm_sum_log_gaussianPrimeWeight_le {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hξ : 0 ≤ ξ) (ht : 0 < t)
    {P Q : ℕ} (hP : 1 ≤ P) (hPQ : P ≤ Q) :
    ‖∑ n ∈ Ico P Q, (Real.log n : ℂ) * gaussianPrimeWeight σ α ξ t n‖ ≤
      2 * gaussianWeightedTypeIBound σ α ξ t P Q * Real.log ((Q - 1 : ℕ) : ℝ) := by
  by_cases hlt : P < Q
  · refine norm_sum_Ico_mul_le_of_bounded_partial_mono hlt (fun n => Real.log n)
      (gaussianPrimeWeight σ α ξ t) (Real.log_nonneg (by exact_mod_cast hP)) ?_ ?_
    · intro n hn
      apply Real.log_le_log
      · exact_mod_cast (show 0 < n by omega)
      · exact_mod_cast Nat.le_succ n
    · intro k hk
      exact norm_sum_gaussianPrimeWeight_prefix_le hσ hα hξ ht hP (by omega) (by omega)
  · have he : Q = P := by omega
    subst Q
    simp only [Ico_self, sum_empty, norm_zero]
    have hb : 0 ≤ gaussianWeightedTypeIBound σ α ξ t P P := by
      simpa only [Ico_self, sum_empty, norm_zero] using
        norm_sum_gaussianPrimeWeight_prefix_le hσ hα hξ ht hP le_rfl le_rfl
    have hlog : 0 ≤ Real.log ((P - 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (P - 1) with hz | hz
      · simp [hz]
      · exact Real.log_nonneg (by exact_mod_cast hz)
    positivity

/-- Dilation preserves the phase up to a unit scalar and rescales both Gaussian coefficients. -/
theorem gaussianPrimeWeight_dilate (σ α ξ t : ℝ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gaussianPrimeWeight σ α ξ t (a * b) =
      ((((b : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-t * Real.log b : ℝ) : ℂ) * I)) *
        gaussianPrimeWeight σ (α * (b : ℝ) ^ 2) (ξ * (b : ℝ) ^ 2) t a := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have he : gaussianPrimePhase α ξ t (a * b) =
      Complex.exp (((-t * Real.log b : ℝ) : ℂ) * I) *
        gaussianPrimePhase (α * (b : ℝ) ^ 2) (ξ * (b : ℝ) ^ 2) t a := by
    simp only [gaussianPrimePhase, Nat.cast_mul, Real.log_mul ha0 hb0, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [gaussianPrimeWeight, gaussianPrimeWeight, he, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b), Complex.ofReal_mul]
  ring

/-- The type-I bound on the divisor fibre belonging to `b`. -/
def gaussianTypeIFibreBound (σ α ξ t : ℝ) (A B b : ℕ) : ℝ :=
  (b : ℝ) ^ (-σ) * gaussianWeightedTypeIBound σ (α * (b : ℝ) ^ 2)
    (ξ * (b : ℝ) ^ 2) t ((A - 1) / b + 1) ((B - 1) / b + 1)


private theorem norm_gaussian_dilation_scalar (σ t : ℝ) (b : ℕ) :
    ‖((((b : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-t * Real.log b : ℝ) : ℂ) * I))‖ =
      (b : ℝ) ^ (-σ) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg b) _)]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    Real.exp_zero, mul_one]

/-- The nonlogarithmic Gaussian type-I fibre estimate. -/
theorem norm_sum_gaussianPrimeWeight_fibre_le {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hξ : 0 ≤ ξ) (ht : 0 < t)
    {A B b : ℕ} (hAB : A ≤ B) (hb : 1 ≤ b) :
    ‖∑ a ∈ fibreIco A B b, gaussianPrimeWeight σ α ξ t (a * b)‖ ≤
      gaussianTypeIFibreBound σ α ξ t A B b := by
  have he : (∑ a ∈ fibreIco A B b, gaussianPrimeWeight σ α ξ t (a * b)) =
      ((((b : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-t * Real.log b : ℝ) : ℂ) * I)) *
        ∑ a ∈ fibreIco A B b,
          gaussianPrimeWeight σ (α * (b : ℝ) ^ 2) (ξ * (b : ℝ) ^ 2) t a := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    exact gaussianPrimeWeight_dilate σ α ξ t
      ((Nat.le_add_left 1 _).trans (mem_Ico.mp ha).1) hb
  rw [he, norm_mul, norm_gaussian_dilation_scalar]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg b) _)
  exact norm_sum_gaussianPrimeWeight_prefix_le hσ (by positivity) (by positivity) ht
    (Nat.le_add_left 1 _)
    (Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le_sub_right hAB 1)) 1) le_rfl

/-- The logarithmic Gaussian type-I fibre estimate. -/
theorem norm_sum_log_gaussianPrimeWeight_fibre_le {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hξ : 0 ≤ ξ) (ht : 0 < t)
    {A B b : ℕ} (hAB : A ≤ B) (hb : 1 ≤ b) :
    ‖∑ a ∈ fibreIco A B b, (Real.log a : ℂ) * gaussianPrimeWeight σ α ξ t (a * b)‖ ≤
      2 * gaussianTypeIFibreBound σ α ξ t A B b *
        Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
  have he : (∑ a ∈ fibreIco A B b,
      (Real.log a : ℂ) * gaussianPrimeWeight σ α ξ t (a * b)) =
      ((((b : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-t * Real.log b : ℝ) : ℂ) * I)) *
        ∑ a ∈ fibreIco A B b, (Real.log a : ℂ) *
          gaussianPrimeWeight σ (α * (b : ℝ) ^ 2) (ξ * (b : ℝ) ^ 2) t a := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [gaussianPrimeWeight_dilate σ α ξ t
      ((Nat.le_add_left 1 _).trans (mem_Ico.mp ha).1) hb]
    ring
  rw [he, norm_mul, norm_gaussian_dilation_scalar]
  have h := norm_sum_log_gaussianPrimeWeight_le hσ
    (mul_nonneg hα (sq_nonneg (b : ℝ))) (mul_nonneg hξ (sq_nonneg (b : ℝ))) ht
    (P := (A - 1) / b + 1) (Q := (B - 1) / b + 1) (Nat.le_add_left 1 _)
    (Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le_sub_right hAB 1)) 1)
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (Nat.cast_nonneg b) (-σ))
  simpa only [gaussianTypeIFibreBound, mul_assoc, mul_left_comm, mul_comm] using! hm

/-- A concrete curvature range halves the trivial type-I bound. -/
theorem gaussianTypeIBound_le_half {ξ t : ℝ} {P Q : ℕ}
    (hξ : 0 ≤ ξ) (ht : 0 < t) (hP : 1 ≤ P) (hPQ : P ≤ Q)
    (hsmall : (gaussianLogCurvature ξ t P / gaussianLogCurvature ξ t Q) *
      Real.sqrt (gaussianLogCurvature ξ t Q) ≤ 1 / 32)
    (hlong : 48 ≤ ((Q - P : ℕ) : ℝ) * Real.sqrt (gaussianLogCurvature ξ t Q)) :
    gaussianTypeIBound ξ t P Q ≤ ((Q - P : ℕ) : ℝ) / 2 := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hs := Real.sqrt_pos.mpr (gaussianLogCurvature_pos hξ ht hQ)
  have h₁ := mul_le_mul_of_nonneg_left hsmall
    (by positivity : 0 ≤ 8 * ((Q - P : ℕ) : ℝ))
  have h₂ : 12 / Real.sqrt (gaussianLogCurvature ξ t Q) ≤ ((Q - P : ℕ) : ℝ) / 4 := by
    apply (div_le_iff₀ hs).mpr
    linarith only [hlong]
  exact (min_le_right _ _).trans (by nlinarith only [h₁, h₂])

#print axioms gaussianTypeIBound_le_half
#print axioms norm_sum_gaussianPrimePhase_zero_prefix_le
#print axioms norm_sum_gaussianPrimeWeight_prefix_le
#print axioms norm_sum_log_gaussianPrimeWeight_le
#print axioms gaussianPrimeWeight_dilate
#print axioms norm_sum_gaussianPrimeWeight_fibre_le
#print axioms norm_sum_log_gaussianPrimeWeight_fibre_le

end GaloisForLFunctions.ExceptionalLayerTheory
