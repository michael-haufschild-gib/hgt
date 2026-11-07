import GaloisForLFunctions.ArithmeticPositiveDuality.AnIntegerNormBeurlingOneOff
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSevenTwelfths

/-!
# A finite zero layer in an Euler product over rational primes

Round the discrete Beurling generators to the next rational prime. The prime-gap exponent
`59/100` makes the change of the prime sums holomorphic on `Re s > 59/100`. The resulting
nonvanishing correction preserves the prescribed zero pair at `3/5 ± iγ`.
-/

set_option autoImplicit false

open Complex Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff
open GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

namespace GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff

noncomputable section

/-- The least rational prime at least a given real number. -/
def nextPrime (x : ℝ) : ℕ := Nat.find (Nat.exists_infinite_primes ⌈x⌉₊)

theorem nextPrime_prime (x : ℝ) : (nextPrime x).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes ⌈x⌉₊)).2

theorem le_nextPrime (x : ℝ) : x ≤ nextPrime x :=
  (Nat.le_ceil x).trans (by exact_mod_cast
    (Nat.find_spec (Nat.exists_infinite_primes ⌈x⌉₊)).1)

theorem nextPrime_le {x : ℝ} {p : ℕ} (hp : p.Prime) (hxp : x ≤ p) :
    nextPrime x ≤ p :=
  Nat.find_min' _ ⟨Nat.ceil_le.mpr hxp, hp⟩

theorem nextPrime_mono : Monotone nextPrime := by
  intro x y hxy
  exact nextPrime_le (nextPrime_prime y) (hxy.trans (le_nextPrime y))

def primeNorm (P : Params) (k : ℕ) : ℕ := nextPrime (Real.exp (P.atom k))

def roundedAtom (P : Params) (k : ℕ) : ℝ := Real.log (primeNorm P k)

theorem primeNorm_prime (P : Params) (k : ℕ) : (primeNorm P k).Prime :=
  nextPrime_prime _

theorem atom_le_roundedAtom (P : Params) (k : ℕ) : P.atom k ≤ roundedAtom P k := by
  apply (Real.le_log_iff_exp_le (by exact_mod_cast (primeNorm_prime P k).pos)).2
  exact le_nextPrime _

theorem roundedAtom_pos (P : Params) (k : ℕ) : 0 < roundedAtom P k :=
  (P.atom_pos k).trans_le (atom_le_roundedAtom P k)

theorem roundedAtom_zero_le (P : Params) (k : ℕ) : roundedAtom P 0 ≤ roundedAtom P k := by
  apply Real.log_le_log (by exact_mod_cast (primeNorm_prime P 0).pos)
  exact_mod_cast nextPrime_mono (Real.exp_le_exp.mpr (P.atom_zero_le k))

theorem summable_exp_roundedAtom (P : Params) {a : ℝ} (ha : 1 < a) :
    Summable fun k => Real.exp (-(a * roundedAtom P k)) := by
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_)
    (P.summable_exp_atom ha)
  exact Real.exp_le_exp.mpr (by nlinarith only [ha, atom_le_roundedAtom P k])

/-- The cumulative prime mass at the `k`th atom is `k+1`, so the atoms escape every bound. -/
theorem tendsto_atom (P : Params) : Tendsto P.atom atTop atTop := by
  apply tendsto_atTop.2
  intro b
  refine eventually_atTop.2 ⟨⌈P.W (max b 0)⌉₊ + 1, ?_⟩
  intro k hk
  have hk' : P.W (max b 0) < (k : ℝ) + 1 := by
    have hc := Nat.le_ceil (P.W (max b 0))
    have hn : (⌈P.W (max b 0)⌉₊ : ℝ) + 1 ≤ k := by exact_mod_cast hk
    linarith only [hc, hn]
  have ha : max b 0 < P.atom k := by
    by_contra h
    have := (P.atom_le_iff k (le_max_right b 0)).1 (le_of_not_gt h)
    linarith only [this, hk']
  exact (le_max_left b 0).trans ha.le

/-- Prime gaps give an exponentially small displacement of logarithmic norms. -/
theorem eventually_roundedAtom_sub_le (P : Params) :
    ∀ᶠ k : ℕ in atTop,
      roundedAtom P k - P.atom k ≤ Real.exp (-((41 / 100 : ℝ) * P.atom k)) := by
  have he := (Real.tendsto_exp_atTop.comp (tendsto_atom P)).eventually
    (RHTower.eventually_exists_prime_short_interval_seven_twelfths
      (α := (59 / 100 : ℝ)) (by norm_num) (by norm_num))
  filter_upwards [he] with k hk
  obtain ⟨p, hp, hlow, hhigh⟩ := hk
  have hq : (primeNorm P k : ℝ) ≤ Real.exp (P.atom k) +
      Real.exp (P.atom k) ^ (59 / 100 : ℝ) := by
    have hqp : (primeNorm P k : ℝ) ≤ p := by exact_mod_cast nextPrime_le hp hlow.le
    exact hqp.trans hhigh
  have hp0 : (0 : ℝ) < primeNorm P k := by exact_mod_cast (primeNorm_prime P k).pos
  have ht0 := Real.exp_pos (P.atom k)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp0 ht0)
  rw [Real.log_div hp0.ne' ht0.ne', Real.log_exp] at hlog
  have hratio : (primeNorm P k : ℝ) / Real.exp (P.atom k) - 1 ≤
      Real.exp (P.atom k) ^ (59 / 100 : ℝ) / Real.exp (P.atom k) := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ ht0).2
    simpa only [add_mul, one_mul, div_mul_cancel₀ _ ht0.ne', add_comm] using hq
  have hexp : Real.exp (P.atom k) ^ (59 / 100 : ℝ) / Real.exp (P.atom k) =
      Real.exp (-((41 / 100 : ℝ) * P.atom k)) := by
    rw [Real.rpow_def_of_pos ht0, Real.log_exp, ← Real.exp_sub]
    congr 1
    ring
  exact hlog.trans (hexp ▸ hratio)

/-- Moving a logarithmic prime norm to the right costs its displacement times the derivative. -/
theorem norm_primeTerm_sub_le_displacement {t u : ℝ} (htu : t ≤ u)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖cexp (-(s * u)) - cexp (-(s * t))‖ ≤
      ‖s‖ * Real.exp (-(s.re * t)) * (u - t) := by
  set d : ℝ := u - t with hd
  have hd0 : 0 ≤ d := sub_nonneg.mpr htu
  have hf : ∀ r ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun r : ℝ => cexp (-(s * t) + (r : ℂ) * (-(s * d))))
        (cexp (-(s * t) + (r : ℂ) * (-(s * d))) * (-(s * d))) (Icc 0 1) r := by
    intro r _
    have hline := ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const
      (-(s * d))).const_add (-(s * t))
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
  rwa [he] at h

theorem summable_displacement (P : Params) {a : ℝ} (ha : 59 / 100 < a) :
    Summable fun k => Real.exp (-(a * P.atom k)) * (roundedAtom P k - P.atom k) := by
  apply (P.summable_exp_atom (a := a + 41 / 100) (by linarith only [ha])).of_norm_bounded_eventually_nat
  filter_upwards [eventually_roundedAtom_sub_le P] with k hk
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (sub_nonneg.mpr (atom_le_roundedAtom P k)))]
  calc
    _ ≤ Real.exp (-(a * P.atom k)) * Real.exp (-((41 / 100 : ℝ) * P.atom k)) :=
      mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
    _ = Real.exp (-((a + 41 / 100) * P.atom k)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The prime-sum correction is holomorphic to the left of the prescribed zero pair. -/
theorem differentiableOn_primeCorrection (P : Params) :
    DifferentiableOn ℂ (primeCorrection P.atom (roundedAtom P))
      {s : ℂ | 59 / 100 < s.re} := by
  intro s hs
  change 59 / 100 < s.re at hs
  set σ₀ : ℝ := (s.re + 59 / 100) / 2
  set M : ℝ := ‖s‖ + 1
  have hσ₀ : 59 / 100 < σ₀ := by dsimp only [σ₀]; linarith only [hs]
  have hM : 0 < M := by dsimp only [M]; positivity
  set U : Set ℂ := {z : ℂ | σ₀ < z.re ∧ ‖z‖ < M}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := by
    constructor
    · dsimp only [σ₀]; linarith only [hs]
    · dsimp only [M]; linarith
  have hdiff : ∀ k, DifferentiableOn ℂ
      (fun z : ℂ => cexp (-(z * roundedAtom P k)) - cexp (-(z * P.atom k))) U := by
    intro k
    exact (by fun_prop : Differentiable ℂ
      (fun z : ℂ => cexp (-(z * roundedAtom P k)) - cexp (-(z * P.atom k)))).differentiableOn
  have hbound : ∀ k (z : ℂ), z ∈ U →
      ‖cexp (-(z * roundedAtom P k)) - cexp (-(z * P.atom k))‖ ≤
        M * (Real.exp (-(σ₀ * P.atom k)) * (roundedAtom P k - P.atom k)) := by
    intro k z hz
    have hz0 : 0 ≤ z.re := by linarith only [hσ₀, hz.1]
    refine (norm_primeTerm_sub_le_displacement (atom_le_roundedAtom P k) hz0).trans ?_
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr (atom_le_roundedAtom P k))
    exact mul_le_mul hz.2.le (Real.exp_le_exp.mpr (by
      nlinarith only [hz.1, P.atom_pos k])) (Real.exp_pos _).le hM.le
  have hD := differentiableOn_tsum_of_summable_norm
    ((summable_displacement P hσ₀).mul_left M) hdiff hU hbound
  exact (hD.differentiableAt (hU.mem_nhds hsU)).differentiableWithinAt

/-- The discrete continuation with the nonvanishing prime-rounding correction. -/
def continuation (P : Params) (s : ℂ) : ℂ :=
  P.continuation s * cexp (primeCorrection P.atom (roundedAtom P) s +
    primePowerRemainder (roundedAtom P) s - primePowerRemainder P.atom s)

theorem hasProd_continuation (P : Params) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun k => (1 - cexp (-(s * Real.log (primeNorm P k))))⁻¹)
      (continuation P s) := by
  obtain ⟨htsum, _⟩ := summable_neg_log P.atom_pos P.atom_zero_le
    (fun a ha => P.summable_exp_atom ha) hs
  obtain ⟨husum, _⟩ := summable_neg_log (roundedAtom_pos P) (roundedAtom_zero_le P)
    (fun a ha => summable_exp_roundedAtom P ha) hs
  have hcorr : primeCorrection P.atom (roundedAtom P) s =
      (∑' k, cexp (-(s * roundedAtom P k))) - ∑' k, cexp (-(s * P.atom k)) :=
    husum.tsum_sub htsum
  have he : cexp (∑' k, -Complex.log (1 - cexp (-(s * roundedAtom P k)))) =
      continuation P s := by
    rw [tsum_neg_log_eq (roundedAtom_pos P) (roundedAtom_zero_le P)
      (fun a ha => summable_exp_roundedAtom P ha) hs]
    rw [continuation, ← P.discreteZeta_eq_continuation hs, Params.discreteZeta,
      Params.eulerLog, tsum_neg_log_eq P.atom_pos P.atom_zero_le
        (fun a ha => P.summable_exp_atom ha) hs, ← Complex.exp_add, hcorr]
    congr 1
    ring
  rw [← he]
  exact hasProd_euler (roundedAtom_pos P) (roundedAtom_zero_le P)
    (fun a ha => summable_exp_roundedAtom P ha) hs

theorem differentiableOn_continuation (P : Params) :
    DifferentiableOn ℂ (continuation P) {s : ℂ | 59 / 100 < s.re ∧ s ≠ 1} := by
  rintro s hs
  have hhalf : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hround : IsOpen {s : ℂ | 59 / 100 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdomain : IsOpen {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} :=
    hhalf.inter isOpen_compl_singleton
  have hsHalf : 1 / 2 < s.re := by linarith only [hs.1]
  have hζ := P.differentiableOn_continuation.differentiableAt
    (hdomain.mem_nhds ⟨hsHalf, hs.2⟩)
  have hC := (differentiableOn_primeCorrection P).differentiableAt (hround.mem_nhds hs.1)
  have hR := (differentiableOn_primePowerRemainder P.atom_pos P.atom_zero_le
    (fun a ha => P.summable_exp_atom ha)).differentiableAt (hhalf.mem_nhds hsHalf)
  have hQ := (differentiableOn_primePowerRemainder (roundedAtom_pos P) (roundedAtom_zero_le P)
    (fun a ha => summable_exp_roundedAtom P ha)).differentiableAt (hhalf.mem_nhds hsHalf)
  exact (hζ.mul ((hC.add hQ).sub hR).cexp).differentiableWithinAt

theorem continuation_eq_zero_iff (P : Params) (s : ℂ) :
    continuation P s = 0 ↔ P.continuation s = 0 := by
  rw [continuation, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _)]

/-- Rational-prime Euler factors can have exactly one prescribed conjugate zero pair
on `Re s > 59/100`, away from the pole at `1`. Prime labels may repeat. -/
theorem exists_rational_prime_euler_one_off (γ : ℝ) :
    ∃ q : ℕ → ℕ, (∀ k, (q k).Prime) ∧ ∃ F : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s)) ∧
      DifferentiableOn ℂ F {s : ℂ | 59 / 100 < s.re ∧ s ≠ 1} ∧
      {s : ℂ | 59 / 100 < s.re ∧ s ≠ 1 ∧ F s = 0} =
        {(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} := by
  let P := fixedParams γ
  refine ⟨primeNorm P, primeNorm_prime P, continuation P,
    fun s hs => hasProd_continuation P hs, differentiableOn_continuation P, ?_⟩
  simp only [continuation_eq_zero_iff]
  have hz := P.zeros_right_of_eq_pair (h := (9 / 100 : ℝ))
    (by norm_num [P, fixedParams]) (by norm_num)
  norm_num [P, fixedParams] at hz ⊢
  exact hz

end
end GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff.exists_rational_prime_euler_one_off
