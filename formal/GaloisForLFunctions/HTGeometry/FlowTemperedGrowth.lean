import GaloisForLFunctions.HTGeometry.FlowMultiplicityMeasure
import GaloisForLFunctions.HTGeometry.ExponentialCharacter
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Polynomial growth of the spectral multiplicity measure

Modulating a fixed weight, `φ_x(t) = exp(-i x t) φ₀(t)`, translates its transform by `x` while
inflating its derivative seminorms only polynomially: Leibniz gives
`‖φ_x^{(n)}‖ ≤ (1 + |x|)^n ‖φ₀‖_{C^n}` because the `j`-th derivative of the modulating exponential
has modulus exactly `|x|^j`.

Combined with the spectral counting bound, a seminorm bound on the trace functional therefore
forces the multiplicity measure to grow at most polynomially: `ν([x-ε, x+ε]) ≤ C(1+|x|)^N`.  This
is the temperedness half of clause 5, with the closed-graph continuity of `φ ↦ Tr K_φ` as the
explicit analytic input.

* `iteratedDeriv_cexpLin` : the iterated derivative of `t ↦ exp(c t)`.
* `norm_iteratedFDeriv_modulation` : the modulating exponential has `n`-th derivative of modulus
  `|x|^n`.
* `norm_iteratedFDeriv_modulatedWeight_le` : the Leibniz seminorm estimate.
* `multiplicityMeasure_polynomial_growth` : the counting bound in polynomial form.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal

section Modulation

/-- The exponential with a linear complex exponent. -/
noncomputable def cexpLin (c : ℂ) : ℝ → ℂ := fun t => Complex.exp (c * (t : ℂ))

theorem contDiff_cexpLin (c : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (cexpLin c) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem differentiableAt_cexpLin (c : ℂ) (t : ℝ) : DifferentiableAt ℝ (cexpLin c) t :=
  (hasDerivAt_cexp_const_mul c t).differentiableAt

theorem deriv_cexpLin (c : ℂ) (t : ℝ) : deriv (cexpLin c) t = c * cexpLin c t := by
  have h := (hasDerivAt_cexp_const_mul c t).deriv
  show deriv (fun y : ℝ => Complex.exp (c * (y : ℂ))) t = c * Complex.exp (c * (t : ℂ))
  rw [h]
  ring

/-- The iterated derivative of `t ↦ exp(c t)`. -/
theorem iteratedDeriv_cexpLin (c : ℂ) (n : ℕ) :
    iteratedDeriv n (cexpLin c) = fun t => c ^ n * cexpLin c t := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [deriv_const_mul _ (differentiableAt_cexpLin c t), deriv_cexpLin]
      ring

/-- The modulating exponential `t ↦ exp(-i x t)`. -/
noncomputable def modulation (x : ℝ) : ℝ → ℂ := cexpLin (-(Complex.I * (x : ℂ)))

theorem contDiff_modulation (x : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (modulation x) :=
  contDiff_cexpLin _

theorem norm_modulation (x t : ℝ) : ‖modulation x t‖ = 1 := by
  rw [modulation, cexpLin, Complex.norm_exp]
  have hre : (-(Complex.I * (x : ℂ)) * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

theorem norm_neg_I_mul (x : ℝ) : ‖-(Complex.I * (x : ℂ))‖ = |x| := by
  rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **The modulating exponential has `n`-th derivative of modulus `|x|^n`.** -/
theorem norm_iteratedFDeriv_modulation (x : ℝ) (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n (modulation x) t‖ = |x| ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, modulation, iteratedDeriv_cexpLin]
  rw [norm_mul, norm_pow, norm_neg_I_mul]
  have h1 : ‖cexpLin (-(Complex.I * (x : ℂ))) t‖ = 1 := norm_modulation x t
  rw [h1, mul_one]

/-- The modulated weight `φ_x(t) = exp(-i x t) φ₀(t)`. -/
noncomputable def complexModulatedWeight (phi : ℝ → ℂ) (x : ℝ) : ℝ → ℂ :=
  fun t => modulation x t * phi t

/-- **The Leibniz seminorm estimate for modulations.**  Modulating inflates the `n`-th derivative
seminorm by at most `(1 + |x|)^n`. -/
theorem norm_iteratedFDeriv_modulatedWeight_le {phi : ℝ → ℂ}
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) {M : ℝ} {k : ℕ}
    (hM : ∀ m ≤ k, ∀ s : ℝ, ‖iteratedFDeriv ℝ m phi s‖ ≤ M) {n : ℕ} (hn : n ≤ k) (x t : ℝ) :
    ‖iteratedFDeriv ℝ n (complexModulatedWeight phi x) t‖ ≤ (1 + |x|) ^ n * M := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Nat.zero_le _) t)
  have hleib := norm_iteratedFDeriv_mul_le
    (f := modulation x) (g := phi) (contDiff_modulation x) hphi t (n := n)
    (by exact_mod_cast le_top)
  have hstep : ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (modulation x) t‖
          * ‖iteratedFDeriv ℝ (n - i) phi t‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |x| ^ i * M := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [norm_iteratedFDeriv_modulation]
    have hle : ‖iteratedFDeriv ℝ (n - i) phi t‖ ≤ M :=
      hM (n - i) (le_trans (Nat.sub_le _ _) hn) t
    have hpos : (0 : ℝ) ≤ (n.choose i : ℝ) * |x| ^ i := by positivity
    exact mul_le_mul_of_nonneg_left hle hpos
  have hbinom : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |x| ^ i * M
      = (1 + |x|) ^ n * M := by
    rw [← Finset.sum_mul]
    congr 1
    rw [add_comm (1 : ℝ) |x|, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_one]
    ring
  calc ‖iteratedFDeriv ℝ n (complexModulatedWeight phi x) t‖
      ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (modulation x) t‖
            * ‖iteratedFDeriv ℝ (n - i) phi t‖ := hleib
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |x| ^ i * M := hstep
    _ = (1 + |x|) ^ n * M := hbinom

/-- The uniform form: every derivative up to order `k` of the modulated weight is bounded by
`(1 + |x|)^k` times the corresponding bound for the unmodulated weight. -/
theorem norm_iteratedFDeriv_modulatedWeight_le_pow {phi : ℝ → ℂ}
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) {M : ℝ} {k : ℕ}
    (hM : ∀ m ≤ k, ∀ s : ℝ, ‖iteratedFDeriv ℝ m phi s‖ ≤ M) (x : ℝ) :
    ∀ n ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ n (complexModulatedWeight phi x) t‖ ≤ (1 + |x|) ^ k * M := by
  intro n hn t
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Nat.zero_le _) t)
  have h1 : (1 : ℝ) ≤ 1 + |x| := le_add_of_nonneg_right (abs_nonneg x)
  have hmono : (1 + |x|) ^ n ≤ (1 + |x|) ^ k := pow_le_pow_right₀ h1 hn
  exact le_trans (norm_iteratedFDeriv_modulatedWeight_le hphi hM hn x t)
    (mul_le_mul_of_nonneg_right hmono hM0)

end Modulation

section PolynomialGrowth

variable {ι : Type*} (lam : ι → ℝ)

/-- **Polynomial growth of the multiplicity measure.**  If the symbol of the modulated weight is
bounded below by `c` on the window of radius `ε` around `x`, and its total mass over the spectrum
grows at most polynomially in `x`, then the multiplicity of the window grows at most
polynomially.  This is temperedness of `ν_A`. -/
theorem multiplicityMeasure_polynomial_growth {g : ℝ → ℝ → ℝ} {eps c Cb : ℝ} {N : ℕ}
    (hc : 0 < c)
    (hlow : ∀ x lambda : ℝ, |lambda - x| ≤ eps → c ≤ g x lambda)
    (hsum : ∀ (x : ℝ) (u : Finset ι), ∑ i ∈ u, g x (lam i) ≤ Cb * (1 + |x|) ^ N)
    (x : ℝ) :
    multiplicityMeasure lam (Set.Icc (x - eps) (x + eps))
      ≤ ENNReal.ofReal (Cb * (1 + |x|) ^ N / c) := by
  refine multiplicityMeasure_le_of_forall_sum_le lam measurableSet_Icc hc ?_ (hsum x)
  intro y hy
  refine hlow x y ?_
  rw [abs_le]
  constructor
  · linarith [hy.1]
  · linarith [hy.2]

/-- The window multiplicity is finite and its count grows polynomially. -/
theorem finite_and_card_le_polynomial {g : ℝ → ℝ → ℝ} {eps c Cb : ℝ} {N : ℕ}
    (hc : 0 < c)
    (hlow : ∀ x lambda : ℝ, |lambda - x| ≤ eps → c ≤ g x lambda)
    (hsum : ∀ (x : ℝ) (u : Finset ι), ∑ i ∈ u, g x (lam i) ≤ Cb * (1 + |x|) ^ N)
    (x : ℝ) :
    {i | lam i ∈ Set.Icc (x - eps) (x + eps)}.Finite ∧
      (Nat.card {i // lam i ∈ Set.Icc (x - eps) (x + eps)} : ℝ)
        ≤ Cb * (1 + |x|) ^ N / c := by
  refine finite_and_card_le_of_forall_sum_le lam hc ?_ (hsum x)
  intro y hy
  refine hlow x y ?_
  rw [abs_le]
  constructor
  · linarith [hy.1]
  · linarith [hy.2]

end PolynomialGrowth

section TraceSeminormBound

variable {ι : Type*} (lam : ι → ℝ)

/-- **The temperedness implication.**  Suppose the trace functional obeys a seminorm bound of
order `k` on weights supported in a fixed compact set, the modulated weights all lie in that
class, the trace of the modulated weight is the total symbol mass over the spectrum, and the
symbol stays above `c` on the window of radius `ε` around the modulation frequency.  Then the
multiplicity measure grows at most polynomially, of degree `k`.

The seminorm bound is the closed-graph continuity of `φ ↦ Tr K_φ` from the card's proof; the
Leibniz estimate above is what turns it into the polynomial factor. -/
theorem multiplicityMeasure_tempered_of_traceSeminormBound
    {phi : ℝ → ℂ} (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    {M C c eps : ℝ} {k : ℕ} (hc : 0 < c)
    (hM : ∀ m ≤ k, ∀ s : ℝ, ‖iteratedFDeriv ℝ m phi s‖ ≤ M)
    (trace : (ℝ → ℂ) → ℝ) (g : ℝ → ℝ → ℝ)
    (hbound : ∀ psi : ℝ → ℂ, ∀ B : ℝ,
      (∀ n ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ n psi t‖ ≤ B) → trace psi ≤ C * B)
    (htrace : ∀ (x : ℝ) (u : Finset ι), ∑ i ∈ u, g x (lam i) ≤ trace (complexModulatedWeight phi x))
    (hlow : ∀ x lambda : ℝ, |lambda - x| ≤ eps → c ≤ g x lambda)
    (x : ℝ) :
    multiplicityMeasure lam (Set.Icc (x - eps) (x + eps))
      ≤ ENNReal.ofReal (C * M * (1 + |x|) ^ k / c) := by
  have hsum : ∀ (y : ℝ) (u : Finset ι), ∑ i ∈ u, g y (lam i) ≤ (C * M) * (1 + |y|) ^ k := by
    intro y u
    refine le_trans (htrace y u) ?_
    have hb := hbound (complexModulatedWeight phi y) ((1 + |y|) ^ k * M)
      (norm_iteratedFDeriv_modulatedWeight_le_pow hphi hM y)
    calc trace (complexModulatedWeight phi y) ≤ C * ((1 + |y|) ^ k * M) := hb
      _ = (C * M) * (1 + |y|) ^ k := by ring
  have := multiplicityMeasure_polynomial_growth lam (g := g) (eps := eps) (c := c)
    (Cb := C * M) (N := k) hc hlow hsum x
  exact this

end TraceSeminormBound

end GaloisForLFunctions.HTGeometry
