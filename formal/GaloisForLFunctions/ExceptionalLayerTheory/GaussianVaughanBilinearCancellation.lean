import GaloisForLFunctions.ExceptionalLayerTheory.ComplexGaussianDamping
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIIEstimate

/-!
# Arithmetic cancellation in Gaussian bilinear sums

The logarithmic height phase cancels from each bilinear correlation.
Constant quadratic curvature and Abel summation then give an explicit
correlation bound retaining the real Gaussian damping.
-/

open Complex Finset RHTower RHTower.Sieve

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The quadratic character, in radians. -/
def quadraticCharacter (u x : ℝ) : ℂ := Complex.exp (((u * x ^ 2 : ℝ) : ℂ) * I)

theorem norm_quadraticCharacter (u x : ℝ) : ‖quadraticCharacter u x‖ = 1 := by
  simp only [quadraticCharacter, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]

/-- The smaller of the trivial bound and the constant-curvature bound.
Zero curvature retains the diagonal exactly. -/
def quadraticSumBound (N : ℕ) (u : ℝ) : ℝ :=
  if u = 0 then N else
    min (N : ℝ) (8 * N * Real.sqrt (|u| / Real.pi) + 12 / Real.sqrt (|u| / Real.pi))

theorem quadraticSumBound_nonneg (N : ℕ) (u : ℝ) : 0 ≤ quadraticSumBound N u := by
  unfold quadraticSumBound
  split_ifs <;> positivity

theorem quadraticSumBound_mono {N M : ℕ} (hNM : N ≤ M) (u : ℝ) :
    quadraticSumBound N u ≤ quadraticSumBound M u := by
  unfold quadraticSumBound
  split_ifs
  · exact_mod_cast hNM
  · have hcast : (N : ℝ) ≤ M := by exact_mod_cast hNM
    gcongr

private theorem norm_sum_quadratic_le_card (u : ℝ) (A B : ℕ) :
    ‖∑ n ∈ Ico A B, quadraticCharacter u n‖ ≤ (B - A : ℕ) := by
  refine (norm_sum_le _ _).trans_eq ?_
  simp only [norm_quadraticCharacter, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]

private theorem norm_sum_quadratic_pos_le {u : ℝ} (hu : 0 < u) (A B : ℕ) :
    ‖∑ n ∈ Ico A B, quadraticCharacter u n‖ ≤
      8 * (B - A : ℕ) * Real.sqrt (u / Real.pi) + 12 / Real.sqrt (u / Real.pi) := by
  have hlam : 0 < u / Real.pi := div_pos hu Real.pi_pos
  by_cases hAB : A < B
  · by_cases hlam1 : u / Real.pi ≤ 1
    · have hd₁ (x : ℝ) : HasDerivAt (fun v : ℝ => u / Real.pi / 2 * v ^ 2)
          (u / Real.pi * x) x := by
        have hh : HasDerivAt (fun v : ℝ => u / Real.pi / 2 * v ^ 2)
            (u / Real.pi / 2 * (2 * x)) x := by
          simpa using! (hasDerivAt_pow 2 x).const_mul (u / Real.pi / 2)
        convert hh using 1
        ring
      have hd₂ (x : ℝ) : HasDerivAt (fun v : ℝ => u / Real.pi * v) (u / Real.pi) x := by
        exact hasDerivAt_const_mul (u / Real.pi)
      have hb := second_derivative_test' (fun v : ℝ => u / Real.pi / 2 * v ^ 2)
        (fun v => u / Real.pi * v) (fun _ => u / Real.pi) A (B - A)
        (by omega) (hgrow := 1) hlam hlam1 (fun x _ => hd₁ x) (fun x _ => hd₂ x)
        (fun _ _ => le_rfl) (fun _ _ => by simp)
      simp only [mul_one] at hb
      rw [sum_Ico_eq_sum_range]
      convert hb using 1
      congr 1
      apply sum_congr rfl
      intro n _
      dsimp only [quadraticCharacter]
      congr 2
      push_cast
      field_simp [Real.pi_ne_zero]
    · have hs : 1 ≤ Real.sqrt (u / Real.pi) :=
        Real.one_le_sqrt.mpr (le_of_not_ge hlam1)
      have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 8 * ((B - A : ℕ) : ℝ))
      exact (norm_sum_quadratic_le_card u A B).trans (by
        have hi : 0 ≤ 12 / Real.sqrt (u / Real.pi) := by positivity
        have hN : (0 : ℝ) ≤ (B - A : ℕ) := Nat.cast_nonneg _
        nlinarith only [hm, hi, hN])
  · rw [Ico_eq_empty_of_le (Nat.le_of_not_gt hAB), sum_empty, norm_zero]
    positivity

/-- A quadratic exponential sum has a curvature saving at every interval,
with no Diophantine or unproved cancellation hypothesis. -/
theorem norm_sum_quadraticCharacter_le (u : ℝ) (A B : ℕ) :
    ‖∑ n ∈ Ico A B, quadraticCharacter u n‖ ≤ quadraticSumBound (B - A) u := by
  by_cases hu : u = 0
  · simpa only [quadraticSumBound, if_pos hu] using norm_sum_quadratic_le_card u A B
  rw [quadraticSumBound, if_neg hu]
  refine le_min (norm_sum_quadratic_le_card u A B) ?_
  rcases lt_or_gt_of_ne hu with hu | hu
  · have he : (∑ n ∈ Ico A B, quadraticCharacter u n) =
        (starRingEnd ℂ) (∑ n ∈ Ico A B, quadraticCharacter (-u) n) := by
      rw [map_sum]
      apply sum_congr rfl
      intro n _
      rw [quadraticCharacter, quadraticCharacter, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [he, Complex.norm_conj, abs_of_neg hu]
    exact norm_sum_quadratic_pos_le (neg_pos.mpr hu) A B
  · rw [abs_of_pos hu]
    exact norm_sum_quadratic_pos_le hu A B

/-- Decreasing Gaussian damping costs only its value at the first point. -/
theorem norm_sum_gaussian_quadratic_le {v : ℝ} (hv : 0 ≤ v) (u : ℝ) (A B : ℕ) :
    ‖∑ n ∈ Ico A B, (Real.exp (-v * (n : ℝ) ^ 2) : ℂ) * quadraticCharacter u n‖ ≤
      quadraticSumBound (B - A) u * Real.exp (-v * (A : ℝ) ^ 2) := by
  by_cases hAB : A ≤ B
  · refine abel_block_bound _ (fun n => Real.exp (-v * (n : ℝ) ^ 2)) A B hAB
      (Real.exp_pos _).le ?_ (quadraticSumBound (B - A) u) ?_
    · intro m _ _
      apply Real.exp_le_exp.mpr
      have hsq : (m : ℝ) ^ 2 ≤ (m + 1 : ℕ) ^ 2 := by
        exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ m) 2
      exact mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hv)
    · intro m _ hmB
      exact (norm_sum_quadraticCharacter_le u A m).trans
        (quadraticSumBound_mono (Nat.sub_le_sub_right hmB A) u)
  · rw [Ico_eq_empty_of_le (Nat.le_of_not_ge hAB), sum_empty, norm_zero]
    exact mul_nonneg (quadraticSumBound_nonneg _ _) (Real.exp_pos _).le

/-- A Gaussian prime phase with real damping `α` and imaginary damping `-ξ`. -/
def gaussianPrimePhase (α ξ t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (-(α : ℂ) * (n : ℂ) ^ 2 +
    ((ξ * (n : ℝ) ^ 2 - t * Real.log n : ℝ) : ℂ) * I)

/-- The height phase becomes a single unit scalar in every correlation. -/
theorem gaussianPrimePhase_correlation (α ξ t : ℝ) {d m₁ m₂ : ℕ}
    (hd : 1 ≤ d) (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) :
    gaussianPrimePhase α ξ t (d * m₁) *
        (starRingEnd ℂ) (gaussianPrimePhase α ξ t (d * m₂)) =
      Complex.exp (((-t * (Real.log m₁ - Real.log m₂) : ℝ) : ℂ) * I) *
        ((Real.exp (-(α * ((m₁ : ℝ) ^ 2 + (m₂ : ℝ) ^ 2)) * (d : ℝ) ^ 2) : ℂ) *
          quadraticCharacter (ξ * ((m₁ : ℝ) ^ 2 - (m₂ : ℝ) ^ 2)) d) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hm₁0 : (m₁ : ℝ) ≠ 0 := by exact_mod_cast (show m₁ ≠ 0 by omega)
  have hm₂0 : (m₂ : ℝ) ≠ 0 := by exact_mod_cast (show m₂ ≠ 0 by omega)
  simp only [gaussianPrimePhase, quadraticCharacter, Nat.cast_mul,
    Real.log_mul hd0 hm₁0, Real.log_mul hd0 hm₂0, ← Complex.exp_conj,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [map_add, map_mul, map_neg, map_pow, Complex.conj_natCast,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The Gaussian pair kernel after the logarithmic phase has canceled. -/
def gaussianPairBound (α ξ : ℝ) (P Q m₁ m₂ : ℕ) : ℝ :=
  quadraticSumBound (Q - P) (ξ * ((m₁ : ℝ) ^ 2 - (m₂ : ℝ) ^ 2)) *
    Real.exp (-(α * ((m₁ : ℝ) ^ 2 + (m₂ : ℝ) ^ 2)) * (P : ℝ) ^ 2)

theorem gaussianPairBound_nonneg (α ξ : ℝ) (P Q m₁ m₂ : ℕ) :
    0 ≤ gaussianPairBound α ξ P Q m₁ m₂ :=
  mul_nonneg (quadraticSumBound_nonneg _ _) (Real.exp_pos _).le

/-- Explicit correlation cancellation, uniform in height and retaining the
real damping. The diagonal and zero imaginary damping use the trivial branch. -/
theorem norm_sum_gaussianPrimePhase_correlation_le {α : ℝ} (hα : 0 ≤ α)
    (ξ t : ℝ) {P Q m₁ m₂ : ℕ} (hP : 1 ≤ P) (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) :
    ‖∑ d ∈ Ico P Q, gaussianPrimePhase α ξ t (d * m₁) *
      (starRingEnd ℂ) (gaussianPrimePhase α ξ t (d * m₂))‖ ≤
        gaussianPairBound α ξ P Q m₁ m₂ := by
  have he := sum_congr (s₁ := Ico P Q) rfl (fun d hd =>
    gaussianPrimePhase_correlation α ξ t (hP.trans (mem_Ico.mp hd).1) hm₁ hm₂)
  rw [he, ← mul_sum, norm_mul]
  have hn : ‖Complex.exp (((-t * (Real.log m₁ - Real.log m₂) : ℝ) : ℂ) * I)‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  rw [hn, one_mul]
  exact norm_sum_gaussian_quadratic_le (by positivity) _ P Q

/-- Product cutoffs preserve a single interval in each correlation. -/
def maskedGaussianPhase (α ξ t : ℝ) (A B d m : ℕ) : ℂ :=
  if d ∈ fibreIco A B m then gaussianPrimePhase α ξ t (d * m) else 0

/-- The explicit pair bound on the intersection of both product fibres. -/
def gaussianBlockPairBound (α ξ : ℝ) (A B P Q m₁ m₂ : ℕ) : ℝ :=
  gaussianPairBound α ξ
    (max P (max ((A - 1) / m₁ + 1) ((A - 1) / m₂ + 1)))
    (min Q (min ((B - 1) / m₁ + 1) ((B - 1) / m₂ + 1))) m₁ m₂

private theorem sum_maskedGaussian_correlation_eq (α ξ t : ℝ) (A B P Q m₁ m₂ : ℕ) :
    (∑ d ∈ Ico P Q, maskedGaussianPhase α ξ t A B d m₁ *
      (starRingEnd ℂ) (maskedGaussianPhase α ξ t A B d m₂)) =
    ∑ d ∈ Ico (max P (max ((A - 1) / m₁ + 1) ((A - 1) / m₂ + 1)))
        (min Q (min ((B - 1) / m₁ + 1) ((B - 1) / m₂ + 1))),
      gaussianPrimePhase α ξ t (d * m₁) * (starRingEnd ℂ) (gaussianPrimePhase α ξ t (d * m₂)) := by
  classical
  have hs : (Ico P Q).filter (fun d => d ∈ fibreIco A B m₁ ∧ d ∈ fibreIco A B m₂) =
      Ico (max P (max ((A - 1) / m₁ + 1) ((A - 1) / m₂ + 1)))
        (min Q (min ((B - 1) / m₁ + 1) ((B - 1) / m₂ + 1))) := by
    ext d
    simp only [mem_filter, fibreIco, mem_Ico, max_le_iff, lt_min_iff]
    tauto
  rw [← hs, sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases h₁ : d ∈ fibreIco A B m₁ <;> by_cases h₂ : d ∈ fibreIco A B m₂ <;>
    simp [maskedGaussianPhase, h₁, h₂]

/-- Bilinear cancellation for the complete Gaussian weight on a product
block. The coefficient norms and the pair kernel are independent of height. -/
theorem norm_maskedGaussian_bilinear_sq_le {α : ℝ} (hα : 0 ≤ α)
    (ξ t : ℝ) (A B P Q : ℕ) (hP : 1 ≤ P) (Ms : Finset ℕ)
    (hMs : ∀ m ∈ Ms, 1 ≤ m) (a b : ℕ → ℂ) :
    ‖∑ d ∈ Ico P Q, a d * ∑ m ∈ Ms, b m * maskedGaussianPhase α ξ t A B d m‖ ^ 2 ≤
      (∑ d ∈ Ico P Q, ‖a d‖ ^ 2) *
        ∑ m₁ ∈ Ms, ∑ m₂ ∈ Ms, ‖b m₁‖ * ‖b m₂‖ *
          gaussianBlockPairBound α ξ A B P Q m₁ m₂ := by
  refine (norm_bilinear_sq_le (Ico P Q) a _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun d _ => sq_nonneg ‖a d‖)
  refine (sum_normSq_inner_le (Ico P Q) Ms b _).trans ?_
  apply sum_le_sum
  intro m₁ hm₁
  apply sum_le_sum
  intro m₂ hm₂
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [sum_maskedGaussian_correlation_eq]
  exact norm_sum_gaussianPrimePhase_correlation_le hα ξ t
    (hP.trans (le_max_left _ _)) (hMs m₁ hm₁) (hMs m₂ hm₂)

/-- The abscissa weight of the literal Gaussian prime sum. -/
def gaussianPrimeWeight (σ α ξ t : ℝ) (n : ℕ) : ℂ :=
  (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * gaussianPrimePhase α ξ t n

/-- The weight is exactly the complex Gaussian Dirichlet summand. -/
theorem gaussianPrimeWeight_eq (σ α ξ t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    gaussianPrimeWeight σ α ξ t n =
      (n : ℂ) ^ (-((σ : ℂ) + t * I)) *
        Complex.exp (-(((α : ℂ) - ξ * I) * (n : ℂ) ^ 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hncast : ((n : ℝ) : ℂ) = (n : ℂ) := by norm_cast
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← hncast, ← Complex.ofReal_log hn0.le]
  rw [gaussianPrimeWeight, gaussianPrimePhase, Real.rpow_def_of_pos hn0,
    Complex.ofReal_exp, Complex.cpow_def_of_ne_zero hnC, hlog,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem gaussianPrimeWeight_mul (σ α ξ t : ℝ) (d m : ℕ) :
    gaussianPrimeWeight σ α ξ t (d * m) =
      (((d : ℝ) ^ (-σ) : ℝ) : ℂ) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ) * gaussianPrimePhase α ξ t (d * m) := by
  rw [gaussianPrimeWeight, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg m), Complex.ofReal_mul]

private theorem gaussian_convolution_eq_masked {A B L : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (σ α ξ t : ℝ) (f g : ArithmeticFunction ℝ) :
    (∑ n ∈ Ico A B, (((f * g) n : ℝ) : ℂ) * gaussianPrimeWeight σ α ξ t n) =
      ∑ d ∈ Icc 1 L, ((f d : ℝ) : ℂ) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ) *
        ∑ m ∈ Icc 1 L, (((g m : ℝ) : ℂ) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ)) *
          maskedGaussianPhase α ξ t A B d m := by
  classical
  have hI : ∀ n ∈ Ico A B, 1 ≤ n ∧ n ≤ L := by
    intro n hn
    have hn' := mem_Ico.mp hn
    constructor <;> omega
  have he : ∀ n ∈ Ico A B, (((f * g) n : ℝ) : ℂ) * gaussianPrimeWeight σ α ξ t n =
      (∑ p ∈ n.divisorsAntidiagonal, ((f p.1 : ℝ) : ℂ) * ((g p.2 : ℝ) : ℂ)) *
        gaussianPrimeWeight σ α ξ t n := by
    intro n _
    rw [coe_mul_apply]
  rw [sum_congr rfl he, sum_conv_mul_eq hI (fun d => ((f d : ℝ) : ℂ))
    (fun m => ((g m : ℝ) : ℂ)) (gaussianPrimeWeight σ α ξ t), sum_filter, sum_product]
  apply sum_congr rfl
  intro d _
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  have hm1 := (mem_Icc.mp hm).1
  have hf : d * m ∈ Ico A B ↔ d ∈ fibreIco A B m := mem_fibre_iff hm1 hA hB d
  by_cases hdm : d * m ∈ Ico A B
  · rw [if_pos hdm, maskedGaussianPhase, if_pos (hf.mp hdm),
      gaussianPrimeWeight_mul σ α ξ t d m]
    ring
  · rw [if_neg hdm, maskedGaussianPhase, if_neg (fun h => hdm (hf.mpr h))]
    ring

/-- The actual type-II Vaughan term has an independent arithmetic energy
bound. No zero location, finite-layer profile or prime estimate is assumed. -/
theorem norm_gaussianVaughan_typeII_sq_le {α : ℝ} (hα : 0 ≤ α)
    (σ ξ t : ℝ) {A B L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (U V : ℕ) :
    ‖∑ n ∈ Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
      gaussianPrimeWeight σ α ξ t n‖ ^ 2 ≤
      (∑ d ∈ Icc 1 L, ‖((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) *
        ∑ m₁ ∈ Icc 1 L, ∑ m₂ ∈ Icc 1 L,
          ‖((typeIIShort V m₁ : ℝ) : ℂ) * (((m₁ : ℝ) ^ (-σ) : ℝ) : ℂ)‖ *
          ‖((typeIIShort V m₂ : ℝ) : ℂ) * (((m₂ : ℝ) ^ (-σ) : ℝ) : ℂ)‖ *
          gaussianBlockPairBound α ξ A B 1 (L + 1) m₁ m₂ := by
  rw [gaussian_convolution_eq_masked hA hB hBL]
  simpa only [Ico_add_one_right_eq_Icc] using
    norm_maskedGaussian_bilinear_sq_le hα ξ t A B 1 (L + 1) le_rfl (Icc 1 L)
      (fun m hm => (mem_Icc.mp hm).1)
      (fun d => ((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ))
      (fun m => ((typeIIShort V m : ℝ) : ℂ) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ))

/-- A concrete nontrivial curvature range halves the trivial correlation
bound. The full Gaussian endpoint factor is retained after Abel summation. -/
theorem quadraticSumBound_le_half {N : ℕ} {u : ℝ} (hu : u ≠ 0)
    (hsmall : |u| / Real.pi ≤ 1 / 1024)
    (hlong : 48 ≤ (N : ℝ) * Real.sqrt (|u| / Real.pi)) :
    quadraticSumBound N u ≤ (N : ℝ) / 2 := by
  have hlam : 0 < |u| / Real.pi := div_pos (abs_pos.mpr hu) Real.pi_pos
  have hs : 0 < Real.sqrt (|u| / Real.pi) := Real.sqrt_pos.mpr hlam
  have hs₁ : Real.sqrt (|u| / Real.pi) ≤ 1 / 32 := by
    nlinarith only [Real.sq_sqrt hlam.le, hs.le, hsmall]
  have h₁ := mul_le_mul_of_nonneg_left hs₁ (by positivity : 0 ≤ 8 * (N : ℝ))
  have h₂ : 12 / Real.sqrt (|u| / Real.pi) ≤ (N : ℝ) / 4 := by
    apply (div_le_iff₀ hs).mpr
    linarith only [hlong]
  rw [quadraticSumBound, if_neg hu]
  exact (min_le_right _ _).trans (by linarith only [h₁, h₂])

/-- The bound applies directly to the complex Gaussian Dirichlet weight of
the rotated prime current, at every interior angle and every height. -/
theorem norm_rotatedGaussianVaughan_typeII_sq_le {y φ : ℝ} (hy : 0 < y)
    (hφ : |φ| < Real.pi / 2) (σ t : ℝ) {A B L : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (U V : ℕ) :
    let ε := complexGaussianDamping y φ
    ‖∑ n ∈ Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
      ((n : ℂ) ^ (-((σ : ℂ) + t * I)) * Complex.exp (-(ε * (n : ℂ) ^ 2)))‖ ^ 2 ≤
      (∑ d ∈ Icc 1 L, ‖((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) *
        ∑ m₁ ∈ Icc 1 L, ∑ m₂ ∈ Icc 1 L,
          ‖((typeIIShort V m₁ : ℝ) : ℂ) * (((m₁ : ℝ) ^ (-σ) : ℝ) : ℂ)‖ *
          ‖((typeIIShort V m₂ : ℝ) : ℂ) * (((m₂ : ℝ) ^ (-σ) : ℝ) : ℂ)‖ *
          gaussianBlockPairBound ε.re (-ε.im) A B 1 (L + 1) m₁ m₂ := by
  dsimp only
  let ε := complexGaussianDamping y φ
  have hε : (ε.re : ℂ) - (-ε.im : ℝ) * I = ε := by
    apply Complex.ext <;> simp
  have hb := norm_gaussianVaughan_typeII_sq_le (complexGaussianDamping_re_pos hy hφ).le
    σ (-ε.im) t hA hB hBL U V
  have hw : ∀ n ∈ Ico A B, gaussianPrimeWeight σ ε.re (-ε.im) t n =
      (n : ℂ) ^ (-((σ : ℂ) + t * I)) * Complex.exp (-(ε * (n : ℂ) ^ 2)) := by
    intro n hn
    rw [gaussianPrimeWeight_eq σ ε.re (-ε.im) t (hA.trans (mem_Ico.mp hn).1), hε]
  have hs : (∑ n ∈ Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
      gaussianPrimeWeight σ ε.re (-ε.im) t n) =
      ∑ n ∈ Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
        ((n : ℂ) ^ (-((σ : ℂ) + t * I)) * Complex.exp (-(ε * (n : ℂ) ^ 2))) :=
    sum_congr rfl (fun n hn => congrArg _ (hw n hn))
  rw [hs] at hb
  exact hb

#print axioms norm_sum_quadraticCharacter_le
#print axioms norm_sum_gaussian_quadratic_le
#print axioms gaussianPrimePhase_correlation
#print axioms norm_sum_gaussianPrimePhase_correlation_le
#print axioms norm_maskedGaussian_bilinear_sq_le
#print axioms gaussianPrimeWeight_eq
#print axioms norm_gaussianVaughan_typeII_sq_le
#print axioms quadraticSumBound_le_half
#print axioms norm_rotatedGaussianVaughan_typeII_sq_le

end GaloisForLFunctions.ExceptionalLayerTheory
