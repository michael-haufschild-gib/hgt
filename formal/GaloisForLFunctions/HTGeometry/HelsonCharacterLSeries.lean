import Mathlib
import GaloisForLFunctions.HTGeometry.CharacterSource
import GaloisForLFunctions.HTGeometry.HelsonZetaAnalytic

/-!
# The Helson zeta function as a Dirichlet series, and its logarithmic derivative

A family of unimodular prime phases extends to a completely multiplicative function `χ` on the
positive integers.  Its Dirichlet series is the Euler product defining the Helson zeta function, and
the classical convolution identity `Λ ⋆ 1 = log`, twisted by `χ`, identifies the logarithmic
derivative of that series with `-∑ χ(n) Λ(n) n^{-s}`.
-/

noncomputable section

open Complex Filter ArithmeticFunction LSeries

namespace GaloisForLFunctions.HTGeometry

/-- The completely multiplicative extension of a family of prime phases. -/
def phaseChar (u : ℕ → ℂ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun p k => u p ^ k
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, Nat.factorization_mul hm hn,
      Finsupp.prod_add_index' (fun a => by simp) (fun a b₁ b₂ => by rw [pow_add])]

theorem phaseChar_apply_of_ne_zero (u : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    phaseChar u n = n.factorization.prod fun p k => u p ^ k := if_neg hn

theorem phaseChar_zero (u : ℕ → ℂ) : phaseChar u 0 = 0 := rfl

theorem phaseChar_prime (u : ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) : phaseChar u p = u p := by
  rw [phaseChar_apply_of_ne_zero u hp.ne_zero, hp.factorization, Finsupp.prod_single_index (by simp),
    pow_one]

theorem norm_phaseChar_eq_one {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {n : ℕ}
    (hn : n ≠ 0) : ‖phaseChar u n‖ = 1 := by
  rw [phaseChar_apply_of_ne_zero u hn, Finsupp.prod, norm_prod]
  refine Finset.prod_eq_one fun p hp => ?_
  have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by
    rwa [Nat.support_factorization] at hp)
  rw [norm_pow, hu p hprime, one_pow]

theorem norm_phaseChar_le_one {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) (n : ℕ) :
    ‖phaseChar u n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [phaseChar_zero, norm_zero]
    norm_num
  · exact le_of_eq (norm_phaseChar_eq_one hu hn)

/-- The source of the prime phases is the completely multiplicative extension weighted by the von
Mangoldt function. -/
theorem characterSource_eq_phaseChar_mul (u : ℕ → ℂ) (n : ℕ) :
    characterSource u n = phaseChar u n * ((Λ n : ℝ) : ℂ) := by
  by_cases h : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := h
    have hpp : Nat.Prime p := Nat.prime_iff.2 hp
    have hk0 : 0 < k := hk
    have hne : p ^ k ≠ 0 := pow_ne_zero k hpp.ne_zero
    have hminfac : (p ^ k).minFac = p := by
      have hdvd : (p ^ k).minFac ∣ p ^ k := Nat.minFac_dvd _
      have hmfp : Nat.Prime (p ^ k).minFac := Nat.minFac_prime (by
        intro h1
        have : p ^ k ≠ 1 := by
          intro h2
          have := Nat.pow_eq_one.1 h2
          rcases this with h3 | h3
          · exact hpp.one_lt.ne' h3
          · omega
        exact this h1)
      have := (Nat.Prime.dvd_of_dvd_pow hmfp hdvd)
      exact (Nat.prime_dvd_prime_iff_eq hmfp hpp).1 this
    have hfact : (p ^ k).factorization = Finsupp.single p k := hpp.factorization_pow
    rw [characterSource, hminfac, hfact, phaseChar_apply_of_ne_zero u hne, hfact,
      Finsupp.prod_single_index (by simp), Finsupp.single_eq_same]
  · have hΛ : Λ (n) = 0 := by
      rw [vonMangoldt_apply, if_neg h]
    rw [characterSource_of_vonMangoldt_zero hΛ, hΛ]
    simp

/-- The summand `n ↦ χ(n) n^{-s}` of the Dirichlet series, as a completely multiplicative map. -/
def phaseSummandHom (u : ℕ → ℂ) {s : ℂ} (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := phaseChar u n * (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simp_rw [← Complex.ofReal_natCast]
    simpa only [Nat.cast_mul, map_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _] using mul_mul_mul_comm ..

theorem summable_phaseSummand {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {s : ℂ}
    (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖phaseSummandHom u (ne_zero_of_one_lt_re hs) n‖ := by
  simp only [phaseSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  refine (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => by positivity) fun n => ?_
  simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_phaseChar_le_one hu n)

theorem tsum_phaseSummand {u : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, phaseSummandHom u (ne_zero_of_one_lt_re hs) n = LSeries (fun n => phaseChar u n) s := by
  simp only [phaseSummandHom, Complex.cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), div_eq_mul_inv]

/-- **The Euler product of a Helson character is its Dirichlet series.** -/
theorem hasProd_phaseEuler {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {s : ℂ}
    (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeries (fun n => phaseChar u n) s) := by
  have hmain := EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (f := phaseSummandHom u (ne_zero_of_one_lt_re hs)) (summable_phaseSummand hu hs)
  rw [tsum_phaseSummand hs] at hmain
  have hfun : (fun p : Nat.Primes => (1 - phaseSummandHom u (ne_zero_of_one_lt_re hs) (p : ℕ))⁻¹)
      = fun p : Nat.Primes => (1 - u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
    funext p
    show (1 - phaseChar u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹
      = (1 - u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹
    rw [phaseChar_prime u p.2]
  rwa [hfun] at hmain

theorem helsonZetaValue_eq_LSeries {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1)
    {χ : PhaseTorus} (hχ : ∀ p : Nat.Primes, (χ p : ℂ) = u (p : ℕ)) {s : ℂ} (hs : 1 < s.re) :
    helsonZetaValue s χ = LSeries (fun n => phaseChar u n) s := by
  rw [helsonZetaValue]
  have hprod := hasProd_phaseEuler hu hs
  have hfun : (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      = fun p : Nat.Primes => (1 - u (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
    funext p
    rw [hχ p]
  rw [hfun]
  exact hprod.tprod_eq

/-- The `L`-series of the character source is summable past the line. -/
theorem lSeriesSummable_characterSource {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (characterSource u) s := by
  set ε : ℝ := (s.re - 1) / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    linarith
  refine LSeriesSummable_of_isBigO_rpow (x := 1 + ε) (by rw [hεdef]; linarith) ?_
  refine Asymptotics.IsBigO.of_bound (1 / ε) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n : ℝ) := by linarith
  have hlog : Real.log n ≤ (n : ℝ) ^ ε / ε := Real.log_le_rpow_div (le_of_lt hnpos) hε
  have hbound : ‖characterSource u n‖ ≤ Real.log n := norm_characterSource_le hu n
  have hpow : ‖(n : ℝ) ^ ((1 + ε) - 1)‖ = (n : ℝ) ^ ε := by
    have hsimp : (1 + ε) - 1 = ε := by ring
    rw [hsimp, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hnpos) _)]
  rw [hpow]
  calc ‖characterSource u n‖ ≤ Real.log n := hbound
    _ ≤ (n : ℝ) ^ ε / ε := hlog
    _ = 1 / ε * (n : ℝ) ^ ε := by ring

theorem lSeriesSummable_phaseChar {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (fun n => phaseChar u n) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => norm_phaseChar_le_one hu n) hs

/-- The twisted convolution identity `(χΛ) ⋆ χ = χ log`. -/
theorem convolution_characterSource_phaseChar (u : ℕ → ℂ) :
    LSeries.convolution (characterSource u) (fun n => phaseChar u n)
      = LSeries.logMul (fun n => phaseChar u n) := by
  funext n
  simp only [LSeries.convolution_def, LSeries.logMul]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hterm : ∀ p ∈ n.divisorsAntidiagonal,
        characterSource u p.1 * phaseChar u p.2
          = ((Λ p.1 : ℝ) : ℂ) * phaseChar u n := by
      intro p hp
      have hmul : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.1 hp).1
      have hchar : phaseChar u p.1 * phaseChar u p.2 = phaseChar u n := by
        rw [← map_mul, hmul]
      rw [characterSource_eq_phaseChar_mul]
      calc phaseChar u p.1 * ((Λ p.1 : ℝ) : ℂ) * phaseChar u p.2
          = (phaseChar u p.1 * phaseChar u p.2) * ((Λ p.1 : ℝ) : ℂ) := by ring
        _ = phaseChar u n * ((Λ p.1 : ℝ) : ℂ) := by rw [hchar]
        _ = ((Λ p.1 : ℝ) : ℂ) * phaseChar u n := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have hsum : ∑ p ∈ n.divisorsAntidiagonal, ((Λ p.1 : ℝ) : ℂ)
        = ((Real.log n : ℝ) : ℂ) := by
      have hmap := Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
        (f := fun d _ => ((Λ d : ℝ) : ℂ))
      rw [hmap, ← Complex.ofReal_sum, vonMangoldt_sum]
    rw [hsum]
    congr 1
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]

/-- **The logarithmic derivative of the Dirichlet series of a Helson character.** -/
theorem logDeriv_LSeries_phaseChar {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1)
    {χ : PhaseTorus} (hχ : ∀ p : Nat.Primes, (χ p : ℂ) = u (p : ℕ)) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (LSeries (fun n => phaseChar u n)) s = -LSeries (characterSource u) s := by
  have habs : LSeries.abscissaOfAbsConv (fun n => phaseChar u n) ≤ 1 := by
    refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
    refine lSeriesSummable_phaseChar hu ?_
    simpa using hy
  have habs' : LSeries.abscissaOfAbsConv (fun n => phaseChar u n) < (s.re : EReal) := by
    refine lt_of_le_of_lt habs ?_
    exact_mod_cast hs
  have hderiv := LSeries_deriv habs'
  have hconv := LSeries_convolution' (lSeriesSummable_characterSource hu hs)
    (lSeriesSummable_phaseChar hu hs)
  rw [convolution_characterSource_phaseChar] at hconv
  have hne : LSeries (fun n => phaseChar u n) s ≠ 0 := by
    rw [← helsonZetaValue_eq_LSeries hu hχ hs]
    exact helsonZetaValue_ne_zero hs χ
  rw [logDeriv_apply, hderiv, hconv]
  field_simp

/-- **The logarithmic derivative of the Helson zeta function.** -/
theorem logDeriv_helsonZetaValue {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1)
    {χ : PhaseTorus} (hχ : ∀ p : Nat.Primes, (χ p : ℂ) = u (p : ℕ)) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (fun z => helsonZetaValue z χ) s = -LSeries (characterSource u) s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun z => helsonZetaValue z χ) =ᶠ[nhds s] LSeries (fun n => phaseChar u n) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact helsonZetaValue_eq_LSeries hu hχ hz
  rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, ← logDeriv_apply]
  exact logDeriv_LSeries_phaseChar hu hχ hs

end GaloisForLFunctions.HTGeometry

end
