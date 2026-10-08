import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGcdEuler
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPoissonEuler
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticTorusSign
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSummatory

/-!
# The finite Euler density of a multiplicative Weil source

The prime-radius Poisson density has exactly the literal notch Fourier
coefficients. The ordinary gcd limits are proved from the arithmetic
coefficients, including the subtraction at one. Full Weil positivity then
bounds the real part of every finite Euler product. Ordinary harmonic
convergence comes from the source theorem. The strict-profile NotchSmall
obligation is explicit here and is not asserted to follow in this module.
-/

open ArithmeticFunction Complex MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.WeilSingularArithmetic

def primeRadius (p : ℕ) : ℝ := (Real.sqrt (p : ℝ))⁻¹

theorem primeRadius_nonneg (p : ℕ) : 0 ≤ primeRadius p :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem primeRadius_lt_one {p : ℕ} (hp : p.Prime) : primeRadius p < 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  apply (inv_lt_one₀ (Real.sqrt_pos.mpr hp0)).2
  simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hp1

theorem primeRadius_sq (p : ℕ) : primeRadius p ^ 2 = (p : ℝ)⁻¹ := by
  rw [primeRadius, inv_pow, Real.sq_sqrt (Nat.cast_nonneg p)]

private theorem sqrt_pow_nat {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

theorem prod_primeRadius_eq_twistGramWeight (P : Finset ℕ) (g : P → ℤ) :
    (∏ p : P, primeRadius p ^ (g p).natAbs) = WeilAbscissa.twistGramWeight g := by
  unfold WeilAbscissa.twistGramWeight
  rw [WeilAbscissa.vecNum_mul_vecDen_eq_prod, Nat.cast_prod]
  simp only [Nat.cast_pow]
  rw [Real.sqrt_prod _ (fun p _ => pow_nonneg (Nat.cast_nonneg _) _), ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [sqrt_pow_nat (Nat.cast_nonneg _), primeRadius, inv_pow]

private theorem inv_pow_sub_min {z : ℂ} (hz : z ≠ 0) (k j : ℕ) :
    (z⁻¹) ^ (k - min k j) = z ^ min k j / z ^ k := by
  rw [inv_pow]
  apply (eq_div_iff (pow_ne_zero k hz)).2
  have he : z ^ k = z ^ (k - min k j) * z ^ min k j := by
    rw [← pow_add, Nat.sub_add_cancel (min_le_left k j)]
  rw [he, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hz), one_mul]

def localEulerValue (f : ℕ → ℝ) (p : ℕ) : ℝ := ∑' k : ℕ, f (p ^ k) / ((p ^ k : ℕ) : ℝ)

def localGcdEulerValue (f : ℕ → ℝ) (p j : ℕ) : ℝ :=
  ∑' k : ℕ, f (p ^ k) * ((p ^ min k j : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ)

theorem primeRadius_coefficient_tsum (f : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (∑' k : ℕ, (f (p ^ k) : ℂ) * ((primeRadius p : ℂ) ^ 2) ^ (k - min k j)) =
      (localGcdEulerValue f p j : ℂ) := by
  have he : (primeRadius p : ℂ) ^ 2 = (p : ℂ)⁻¹ := by
    simpa only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_natCast] using
      congrArg Complex.ofReal (primeRadius_sq p)
  rw [localGcdEulerValue, Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  rw [he, inv_pow_sub_min (by exact_mod_cast hp.ne_zero)]
  push_cast
  ring

def primeEulerDensity (f : ℕ → ℝ) (H : ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    UnitAddTorus P → ℂ :=
  finitePoissonEulerDensity (fun p k => (f ((p : ℕ) ^ k) : ℂ))
    (fun p => primeRadius p) (fun p => primeRadius_nonneg p)
    (fun p => primeRadius_lt_one (hP p p.2))
    ((H / ∏ p ∈ P, localEulerValue f p : ℝ) : ℂ)

theorem integral_primeEulerDensity_character (f : ℕ → ℝ) (H : ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {C : P → ℝ}
    (hb : ∀ p : P, ∀ k : ℕ, |f ((p : ℕ) ^ k)| ≤ C p) (g : P → ℤ) :
    (∫ x : UnitAddTorus P, primeEulerDensity f H P hP x * UnitAddTorus.mFourier (-g) x) =
      ((WeilAbscissa.twistGramWeight g *
        ((H / ∏ p ∈ P, localEulerValue f p) *
          (∏ p : P, localGcdEulerValue f p (g p).toNat) - 1) : ℝ) : ℂ) := by
  have hc (p : P) (k : ℕ) : ‖(f ((p : ℕ) ^ k) : ℂ)‖ ≤ C p := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb p k
  rw [primeEulerDensity, integral_finitePoissonEulerDensity_character hc]
  simp_rw [primeRadius_coefficient_tsum f (hP _ (Subtype.mem _))]
  have hw : (∏ p : P, (primeRadius p : ℂ) ^ (g p).natAbs) =
      (WeilAbscissa.twistGramWeight g : ℂ) := by
    exact_mod_cast prod_primeRadius_eq_twistGramWeight P g
  rw [hw]
  push_cast
  rfl


theorem tendsto_real_gcdHarmonicSum_of_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {H : ℝ} (hH : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ)) atTop (𝓝 H))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (g : P → ℤ) :
    Tendsto (WeilAbscissa.gcdHarmonicSum P (fun n => f n - if n = 1 then 1 else 0) g)
      atTop (𝓝 ((H / ∏ p ∈ P, localEulerValue f p) *
        (∏ p : P, localGcdEulerValue f p (g p).toNat) - 1)) := by
  let fc : ArithmeticFunction ℂ := ⟨fun n => (f n : ℂ), by simp⟩
  have hfc (n : ℕ) : fc n = (f n : ℂ) := rfl
  have hmult : fc.IsMultiplicative := by
    constructor
    · simp only [hfc, hf.map_one, Complex.ofReal_one]
    · intro m n hmn
      simp only [hfc, hf.map_mul_of_coprime hmn, Complex.ofReal_mul]
  have hbc (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k) : ‖fc (p ^ k)‖ ≤ θ := by
    simpa only [hfc, Complex.norm_real, Real.norm_eq_abs] using hb p hp k hk
  have hHc : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, fc n / (n : ℂ)) atTop (𝓝 (H : ℂ)) := by
    simpa only [Function.comp_def, hfc, Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_natCast]
      using (Complex.continuous_ofReal.tendsto H).comp hH
  have he (p : ℕ) : (∑' k : ℕ, fc (p ^ k) / ((p ^ k : ℕ) : ℂ)) =
      (localEulerValue f p : ℂ) := by
    simp only [localEulerValue, Complex.ofReal_tsum, Complex.ofReal_div,
      Complex.ofReal_natCast, hfc]
  have hg (p : P) : (∑' k : ℕ, fc ((p : ℕ) ^ k) * ((p : ℕ) ^ min k (g p).toNat : ℕ) /
      (((p : ℕ) ^ k : ℕ) : ℂ)) = (localGcdEulerValue f p (g p).toNat : ℂ) := by
    simp only [localGcdEulerValue, Complex.ofReal_tsum, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_natCast, hfc]
  have ht := tendsto_gcdHarmonicSum_of_multiplicative hmult hθ hbc hHc P hP g
  simp only [he, hg] at ht
  simp only [hfc, Complex.ofReal_re] at ht
  simpa only [← Complex.ofReal_prod, ← Complex.ofReal_div, ← Complex.ofReal_mul,
    Complex.ofReal_re] using ht

theorem continuous_primeEulerDensity (f : ℕ → ℝ) (H : ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {C : P → ℝ}
    (hb : ∀ p : P, ∀ k : ℕ, |f ((p : ℕ) ^ k)| ≤ C p) :
    Continuous (primeEulerDensity f H P hP) := by
  apply continuous_finitePoissonEulerDensity
  intro p k
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hb p k

theorem coneDeviation_eq_of_multiplicative_source {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {lam : ℕ → ℝ}
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n) :
    WeilOneSided.coneDeviation lam = fun n => f n - if n = 1 then 1 else 0 := by
  funext n
  by_cases hn : 2 ≤ n
  · simp [WeilOneSided.coneDeviation, hn, hs n hn, show n ≠ 1 by omega]
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> simp [WeilOneSided.coneDeviation, hf.map_one]

theorem exists_harmonic_limit_of_multiplicative_source {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n) :
    ∃ H : ℝ, Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ)) atTop (𝓝 H) := by
  obtain ⟨L, hL⟩ := exists_tendsto_coneDeviation_harmonic hW
  rw [coneDeviation_eq_of_multiplicative_source hf hs] at hL
  refine ⟨L + 1, (hL.add_const 1).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hz : (f 0 - if (0 : ℕ) = 1 then 1 else 0) / ((0 : ℕ) : ℝ) = 0 := by simp
  have herase : (Finset.range (N + 1)).erase 0 = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  have hdelta : (∑ n ∈ Finset.Icc 1 N, (if n = 1 then (1 : ℝ) else 0) / (n : ℝ)) = 1 := by
    have he (n : ℕ) : (if n = 1 then (1 : ℝ) else 0) / (n : ℝ) =
        if n = 1 then 1 else 0 := by
      split_ifs with hn
      · subst n; simp
      · simp
    simp only [he]
    simp [hN]
  change (∑ n ∈ Finset.range (N + 1), (f n - if n = 1 then 1 else 0) / (n : ℝ)) + 1 = _
  rw [← Finset.sum_erase (Finset.range (N + 1)) hz, herase]
  simp only [sub_div, Finset.sum_sub_distrib, hdelta, sub_add_cancel]

theorem re_primeEulerDensity_nonpos_of_weilPositiveFull {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n)
    (hd : PrimeSmallDeviation.NotchSmall (WeilOneSided.coneDeviation lam))
    {H : ℝ} (hH : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ)) atTop (𝓝 H))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ x, (primeEulerDensity f H P hP x).re ≤ 0 := by
  have hbound (p : P) (k : ℕ) : |f ((p : ℕ) ^ k)| ≤ 1 := by
    by_cases hk : k = 0
    · simp [hk, hf.map_one]
    · exact (hb p (hP p p.2) k (by omega)).trans hθ.le
  let Γ (g : P → ℤ) := (H / ∏ p ∈ P, localEulerValue f p) *
    (∏ p : P, localGcdEulerValue f p (g p).toNat) - 1
  have hΓ (g : P → ℤ) : Tendsto
      (WeilAbscissa.gcdHarmonicSum P (WeilOneSided.coneDeviation lam) g) atTop (𝓝 (Γ g)) := by
    rw [coneDeviation_eq_of_multiplicative_source hf hs]
    exact tendsto_real_gcdHarmonicSum_of_multiplicative hf hθ hb hH P hP g
  let U : C(UnitAddTorus P, ℂ) := ⟨primeEulerDensity f H P hP,
    continuous_primeEulerDensity f H P hP hbound⟩
  exact re_density_nonpos_of_weilPositiveFull hW hd P hP Γ hΓ U
    (integral_primeEulerDensity_character f H P hP hbound)


/-- The positive Poisson factor cancels, leaving the finite local Euler bound. -/
theorem finiteEuler_real_bound_of_weilPositiveFull {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n)
    (hd : PrimeSmallDeviation.NotchSmall (WeilOneSided.coneDeviation lam))
    {H : ℝ} (hH : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ)) atTop (𝓝 H))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : UnitAddTorus P) :
    (H / ∏ p ∈ P, localEulerValue f p) *
      (∏ p : P, boundedFun (fun k => (f ((p : ℕ) ^ k) : ℂ))
        ((primeRadius p : ℂ) * fourier 1 (x p))).re ≤ 1 := by
  have hU := re_primeEulerDensity_nonpos_of_weilPositiveFull hf hθ hb hW hs hd hH P hP x
  let K (p : P) : ℝ := additivePoissonKernel
    (realPoissonParameter (primeRadius p) (primeRadius_nonneg p)
      (primeRadius_lt_one (hP p p.2))) (x p)
  have hK : 0 < ∏ p : P, K p := Finset.prod_pos fun p _ => additivePoissonKernel_pos _ _
  have he : (primeEulerDensity f H P hP x).re = (∏ p : P, K p) *
      ((H / ∏ p ∈ P, localEulerValue f p) *
        (∏ p : P, boundedFun (fun k => (f ((p : ℕ) ^ k) : ℂ))
          ((primeRadius p : ℂ) * fourier 1 (x p))).re - 1) := by
    simp [primeEulerDensity, finitePoissonEulerDensity, ← Complex.ofReal_prod, Complex.mul_re, K]
  rw [he] at hU
  nlinarith

/-- The harmonic value is supplied by the source theorem, not assumed to exist.
The remaining strict-profile smallness obligation is displayed explicitly. -/
theorem exists_finiteEuler_bound_of_multiplicative_source {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n)
    (hd : PrimeSmallDeviation.NotchSmall (WeilOneSided.coneDeviation lam)) :
    ∃ H : ℝ,
      Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ)) atTop (𝓝 H) ∧
      ∀ (P : Finset ℕ) (_ : ∀ p ∈ P, p.Prime) (x : UnitAddTorus P),
        (H / ∏ p ∈ P, localEulerValue f p) *
          (∏ p : P, boundedFun (fun k => (f ((p : ℕ) ^ k) : ℂ))
            ((primeRadius p : ℂ) * fourier 1 (x p))).re ≤ 1 := by
  obtain ⟨H, hH⟩ := exists_harmonic_limit_of_multiplicative_source hf hW hs
  exact ⟨H, hH, finiteEuler_real_bound_of_weilPositiveFull hf hθ hb hW hs hd hH⟩

end RHTower.WeilSingularArithmetic
