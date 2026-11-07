import GaloisForLFunctions.ArithmeticPositiveDuality.ADiscreteBeurlingOneOff

/-!
# A Beurling one-off with integer prime norms

Round each discrete prime norm upward to a natural number. Its logarithm changes by at most
its reciprocal, so the difference of the prime sums is holomorphic on `Re s > 0`. Together
with the prime-power remainders this gives a nonvanishing correction on `Re s > 1/2`.
The rounded Euler product therefore retains exactly the prescribed finite zero layer.
-/

set_option autoImplicit false


open Complex Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff

namespace GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

noncomputable section

/-- Logarithm of the upward integer rounding of an exponential. -/
def roundedLog (t : ℝ) : ℝ := Real.log (⌈Real.exp t⌉₊ : ℝ)

/-- Integer rounding changes a logarithmic norm by at most its reciprocal norm. -/
theorem roundedLog_bounds (t : ℝ) :
    t ≤ roundedLog t ∧ roundedLog t ≤ t + Real.exp (-t) := by
  have hp := Real.exp_pos t
  have hq : (0 : ℝ) < ⌈Real.exp t⌉₊ := hp.trans_le (Nat.le_ceil _)
  have hlo : t ≤ roundedLog t := (Real.le_log_iff_exp_le hq).2 (Nat.le_ceil _)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne', Real.log_exp] at hlog
  have hratio : (⌈Real.exp t⌉₊ : ℝ) / Real.exp t ≤ 1 + (Real.exp t)⁻¹ := by
    apply (div_le_iff₀ hp).2
    simpa only [add_mul, one_mul, inv_mul_cancel₀ hp.ne'] using
      (Nat.ceil_lt_add_one hp.le).le
  refine ⟨hlo, ?_⟩
  rw [Real.exp_neg]
  change Real.log (⌈Real.exp t⌉₊ : ℝ) ≤ _
  linarith only [hlog, hratio]

theorem roundedLog_mono : Monotone roundedLog := by
  intro t u htu
  have hp : (0 : ℝ) < ⌈Real.exp t⌉₊ := (Real.exp_pos t).trans_le (Nat.le_ceil _)
  apply Real.log_le_log hp
  exact_mod_cast Nat.ceil_mono (Real.exp_le_exp.mpr htu)

/-- A one-unit increase of a prime norm gains one power in its Mellin transform. -/
theorem norm_primeTerm_sub_le {t u : ℝ} (htu : t ≤ u)
    (hu : u ≤ t + Real.exp (-t)) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖cexp (-(s * u)) - cexp (-(s * t))‖ ≤
      ‖s‖ * Real.exp (-((s.re + 1) * t)) := by
  set d : ℝ := u - t with hd
  have hd0 : 0 ≤ d := sub_nonneg.mpr htu
  have hdle : d ≤ Real.exp (-t) := by dsimp only [d]; linarith only [hu]
  have hf : ∀ r ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun r : ℝ => cexp (-(s * t) + (r : ℂ) * (-(s * d))))
        (cexp (-(s * t) + (r : ℂ) * (-(s * d))) * (-(s * d))) (Icc 0 1) r := by
    intro r _
    have hline := ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (-(s * d))).const_add (-(s * t))
    simpa using hline.cexp.hasDerivWithinAt
  have hb : ∀ r ∈ Ico (0 : ℝ) 1,
      ‖cexp (-(s * t) + (r : ℂ) * (-(s * d))) * (-(s * d))‖ ≤
        ‖s‖ * Real.exp (-(s.re * t)) * d := by
    intro r hr
    have he : ‖cexp (-(s * t) + (r : ℂ) * (-(s * d)))‖ ≤
        Real.exp (-(s.re * t)) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      nlinarith only [mul_nonneg hs (mul_nonneg hr.1 hd0)]
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hd0]
    calc
      _ ≤ Real.exp (-(s.re * t)) * (‖s‖ * d) :=
        mul_le_mul_of_nonneg_right he (mul_nonneg (norm_nonneg _) hd0)
      _ = _ := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hf hb
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_one, one_mul] at h
  have he : -(s * (t : ℂ)) + -(s * (d : ℂ)) = -(s * (u : ℂ)) := by
    rw [hd]
    push_cast
    ring
  rw [he] at h
  refine h.trans ?_
  calc
    ‖s‖ * Real.exp (-(s.re * t)) * d ≤
        ‖s‖ * Real.exp (-(s.re * t)) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_left hdle (by positivity)
    _ = ‖s‖ * Real.exp (-((s.re + 1) * t)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Difference of the prime sums for two sequences of logarithmic norms. -/
def primeCorrection (t u : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' k, (cexp (-(s * u k)) - cexp (-(s * t k)))

/-- Reciprocal-size perturbations of logarithmic prime norms have a holomorphic prime-sum
correction throughout the positive half-plane. -/
theorem differentiableOn_primeCorrection {t u : ℕ → ℝ}
    (ht : ∀ k, 0 < t k) (htu : ∀ k, t k ≤ u k)
    (hu : ∀ k, u k ≤ t k + Real.exp (-(t k)))
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * t k))) :
    DifferentiableOn ℂ (primeCorrection t u) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : 0 < s.re := hs
  set σ₀ : ℝ := s.re / 2
  set M : ℝ := ‖s‖ + 1
  have hσ₀ : 0 < σ₀ := by dsimp only [σ₀]; linarith only [hs0]
  have hM : 0 < M := by dsimp only [M]; positivity
  set U : Set ℂ := {z : ℂ | σ₀ < z.re ∧ ‖z‖ < M}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := by
    constructor
    · dsimp only [σ₀]; linarith only [hs0]
    · dsimp only [M]; linarith
  have hdiff : ∀ k, DifferentiableOn ℂ
      (fun z : ℂ => cexp (-(z * u k)) - cexp (-(z * t k))) U := by
    intro k
    exact (by fun_prop : Differentiable ℂ
      (fun z : ℂ => cexp (-(z * u k)) - cexp (-(z * t k)))).differentiableOn
  have hbound : ∀ k (z : ℂ), z ∈ U →
      ‖cexp (-(z * u k)) - cexp (-(z * t k))‖ ≤
        M * Real.exp (-((σ₀ + 1) * t k)) := by
    intro k z hz
    have hz0 : 0 ≤ z.re := (hσ₀.trans hz.1).le
    refine (norm_primeTerm_sub_le (htu k) (hu k) hz0).trans ?_
    exact mul_le_mul hz.2.le (Real.exp_le_exp.mpr (by nlinarith only [hz.1, ht k]))
      (Real.exp_pos _).le hM.le
  have hsumU : Summable fun k => M * Real.exp (-((σ₀ + 1) * t k)) :=
    (hsum (σ₀ + 1) (by linarith only [hσ₀])).mul_left M
  have hD := differentiableOn_tsum_of_summable_norm hsumU hdiff hU hbound
  exact (hD.differentiableAt (hU.mem_nhds hsU)).differentiableWithinAt

/-- Natural-number norms obtained by rounding the discrete one-off primes upward. -/
def primeNorm (P : Params) (k : ℕ) : ℕ := ⌈Real.exp (P.atom k)⌉₊

def roundedAtom (P : Params) (k : ℕ) : ℝ := Real.log (primeNorm P k)

theorem primeNorm_ge_two (P : Params) (k : ℕ) : 2 ≤ primeNorm P k := by
  have h : (1 : ℝ) < primeNorm P k :=
    (Real.one_lt_exp_iff.mpr (P.atom_pos k)).trans_le (Nat.le_ceil _)
  exact_mod_cast h

theorem atom_le_roundedAtom (P : Params) (k : ℕ) : P.atom k ≤ roundedAtom P k :=
  (roundedLog_bounds (P.atom k)).1

theorem roundedAtom_le (P : Params) (k : ℕ) :
    roundedAtom P k ≤ P.atom k + Real.exp (-(P.atom k)) :=
  (roundedLog_bounds (P.atom k)).2

theorem roundedAtom_pos (P : Params) (k : ℕ) : 0 < roundedAtom P k :=
  (P.atom_pos k).trans_le (atom_le_roundedAtom P k)

theorem roundedAtom_zero_le (P : Params) (k : ℕ) : roundedAtom P 0 ≤ roundedAtom P k :=
  roundedLog_mono (P.atom_zero_le k)

theorem summable_exp_roundedAtom (P : Params) {a : ℝ} (ha : 1 < a) :
    Summable fun k => Real.exp (-(a * roundedAtom P k)) := by
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_)
    (P.summable_exp_atom ha)
  exact Real.exp_le_exp.mpr (by nlinarith only [ha, atom_le_roundedAtom P k])

/-- Euler product of the rounded prime norms, represented by its logarithmic series. -/
def roundedZeta (P : Params) (s : ℂ) : ℂ :=
  cexp (∑' k, -Complex.log (1 - cexp (-(s * roundedAtom P k))))

/-- The old continuation multiplied by the nonvanishing rounding correction. -/
def roundedContinuation (P : Params) (s : ℂ) : ℂ :=
  P.continuation s * cexp (primeCorrection P.atom (roundedAtom P) s +
    primePowerRemainder (roundedAtom P) s - primePowerRemainder P.atom s)

/-- Absolute convergence of the Euler logarithm gives convergence of the Euler product. -/
theorem hasProd_euler {t : ℕ → ℝ} (ht : ∀ k, 0 < t k)
    (hmono : ∀ k, t 0 ≤ t k)
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * t k)))
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun k => (1 - cexp (-(s * t k)))⁻¹)
      (cexp (∑' k, -Complex.log (1 - cexp (-(s * t k))))) := by
  obtain ⟨h1, h2⟩ := summable_neg_log ht hmono hsum hs
  have hlog : Summable fun k => -Complex.log (1 - cexp (-(s * t k))) :=
    (h1.add h2).congr fun k => by ring
  have hne : ∀ k, 1 - cexp (-(s * t k)) ≠ 0 := by
    intro k h
    have hlt : ‖cexp (-(s * t k))‖ < 1 := by
      rw [norm_cexp_neg_mul, Real.exp_lt_one_iff]
      nlinarith only [hs, ht k]
    have he : cexp (-(s * t k)) = 1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hlt
    exact lt_irrefl _ hlt
  have h := (Complex.continuous_exp.tendsto _).comp hlog.hasSum
  change Tendsto (fun J : Finset ℕ => ∏ k ∈ J, (1 - cexp (-(s * t k)))⁻¹)
    atTop (𝓝 _)
  convert h using 1
  · funext J
    dsimp only [Function.comp_def]
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun k _ => by
      rw [Complex.exp_neg (Complex.log (1 - cexp (-(s * t k)))), Complex.exp_log (hne k)]
  · rfl

theorem roundedZeta_eq_continuation (P : Params) {s : ℂ} (hs : 1 < s.re) :
    roundedZeta P s = roundedContinuation P s := by
  obtain ⟨htsum, _⟩ := summable_neg_log P.atom_pos P.atom_zero_le
    (fun a ha => P.summable_exp_atom ha) hs
  obtain ⟨husum, _⟩ := summable_neg_log (roundedAtom_pos P) (roundedAtom_zero_le P)
    (fun a ha => summable_exp_roundedAtom P ha) hs
  have hcorr : primeCorrection P.atom (roundedAtom P) s =
      (∑' k, cexp (-(s * roundedAtom P k))) - ∑' k, cexp (-(s * P.atom k)) :=
    husum.tsum_sub htsum
  rw [roundedZeta, tsum_neg_log_eq (roundedAtom_pos P) (roundedAtom_zero_le P)
    (fun a ha => summable_exp_roundedAtom P ha) hs]
  rw [roundedContinuation, ← P.discreteZeta_eq_continuation hs, Params.discreteZeta,
    Params.eulerLog, tsum_neg_log_eq P.atom_pos P.atom_zero_le
      (fun a ha => P.summable_exp_atom ha) hs, ← Complex.exp_add, hcorr]
  congr 1
  ring

theorem hasProd_roundedContinuation (P : Params) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun k => (1 - cexp (-(s * Real.log (primeNorm P k))))⁻¹)
      (roundedContinuation P s) := by
  rw [← roundedZeta_eq_continuation P hs]
  exact hasProd_euler (roundedAtom_pos P) (roundedAtom_zero_le P)
    (fun a ha => summable_exp_roundedAtom P ha) hs

theorem differentiableOn_roundedContinuation (P : Params) :
    DifferentiableOn ℂ (roundedContinuation P) {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} := by
  rintro s hs
  have hhalf : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hpos : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdomain : IsOpen {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} :=
    hhalf.inter isOpen_compl_singleton
  have hζ := P.differentiableOn_continuation.differentiableAt (hdomain.mem_nhds hs)
  have hC := (differentiableOn_primeCorrection P.atom_pos (atom_le_roundedAtom P)
    (roundedAtom_le P) (fun a ha => P.summable_exp_atom ha)).differentiableAt
      (hpos.mem_nhds (by change 0 < s.re; linarith only [hs.1]))
  have hR := (differentiableOn_primePowerRemainder P.atom_pos P.atom_zero_le
    (fun a ha => P.summable_exp_atom ha)).differentiableAt (hhalf.mem_nhds hs.1)
  have hQ := (differentiableOn_primePowerRemainder (roundedAtom_pos P) (roundedAtom_zero_le P)
    (fun a ha => summable_exp_roundedAtom P ha)).differentiableAt (hhalf.mem_nhds hs.1)
  exact (hζ.mul ((hC.add hQ).sub hR).cexp).differentiableWithinAt

/-- The exponential correction preserves the zero set. -/
theorem roundedContinuation_eq_zero_iff (P : Params) (s : ℂ) :
    roundedContinuation P s = 0 ↔ P.continuation s = 0 := by
  rw [roundedContinuation, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _)]

theorem rounded_zeros_right_of_eq_pair (P : Params) {h : ℝ}
    (hh : h < 1 / 2 - P.μ) (h0 : 0 ≤ h) :
    {s : ℂ | 1 / 2 + h < s.re ∧ s ≠ 1 ∧ roundedContinuation P s = 0} =
      {((1 - P.μ : ℝ) : ℂ) + (P.γ : ℂ) * I, ((1 - P.μ : ℝ) : ℂ) - (P.γ : ℂ) * I} := by
  simp only [roundedContinuation_eq_zero_iff]
  exact P.zeros_right_of_eq_pair hh h0

def fixedParams (γ : ℝ) : Params where
  μ := 2 / 5
  ν := 1 / 10
  γ := γ
  hμ1 := by norm_num
  hμ2 := by norm_num
  hν0 := by norm_num
  hν := by norm_num

/-- At every prescribed ordinate, an Euler product with integer prime norms has exactly
the zero pair `3/5 ± iγ` on `Re s > 1/2` away from `1`. -/
theorem exists_integer_norm_euler_one_off (γ : ℝ) :
    ∃ q : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s)) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} ∧
      {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} =
        {(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} := by
  let P := fixedParams γ
  refine ⟨primeNorm P, primeNorm_ge_two P, roundedContinuation P,
    fun s hs => hasProd_roundedContinuation P hs, differentiableOn_roundedContinuation P, ?_⟩
  have hz := rounded_zeros_right_of_eq_pair P (h := 0) (by norm_num [P, fixedParams]) le_rfl
  norm_num [P, fixedParams] at hz ⊢
  exact hz

end
end GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff.exists_integer_norm_euler_one_off
