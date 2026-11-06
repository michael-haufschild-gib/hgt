import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheStencilRateReachesVinogradovKorobov

/-!
# The bracket of the best rate

`bestRate K` is the infimum of the rates of producers on alphabets in `[1, K]`: the exact value of
`A(K) − 1`. For every `0 < α < 3/5` and all large `K`,

`c₁ K^{-3/4} ≤ bestRate K ≤ exp(−(log K)^α)`.

The scale of exponents is now complete:

* polynomial rate `K^{-a}` for some `a > 0` ⇔ a zero-free strip;
* a zero-free strip at `Θ` gives the rate `K^{-(1−Θ)/32}`, so the Riemann hypothesis gives `K^{-1/64}`;
* a rate `K^{-a}` gives `Re ρ ≤ 1 − 2a/3`, and rates up to `K^{-3/4}` give the Riemann hypothesis;
* no rate is faster than `K^{-3/4}`.

**Necessary alphabet.** Certifying `ζ(1 + iτ) ≠ 0` through a producer needs `ε ‖s‖ < 1`, hence an
alphabet of size at least `c |τ|^{4/3}`: certificates at height `τ` are long.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The set of rates of producers on an alphabet in `[1, K]`. -/
def rateSet (K : ℕ) : Set ℝ :=
  {ε | ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧ rate c m B = ε}

/-- The best rate at alphabet size `K`: the exact value of `A(K) − 1`. -/
def bestRate (K : ℕ) : ℝ := sInf (rateSet K)

/-- **The bracket of the best rate.** For `0 < α < 3/5` and all large `K`,
`c₁ K^{-3/4} ≤ bestRate K ≤ exp(−(log K)^α)`. -/
theorem exists_bracket_bestRate {α : ℝ} (hα0 : 0 < α) (hα : α < 3 / 5) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ K : ℕ in atTop,
      c₁ * (K : ℝ) ^ (-(3 / 4) : ℝ) ≤ bestRate K ∧
        bestRate K ≤ Real.exp (-(Real.log (K : ℝ) ^ α)) := by
  obtain ⟨c₁, hc₁, hfloor⟩ := exists_three_quarters_floor
  refine ⟨c₁, hc₁, ?_⟩
  filter_upwards [hasRate_vk hα0 hα, eventually_ge_atTop 1] with K hK hK1
  obtain ⟨c, m, B, hP, hKa, hr⟩ := hK
  have hmem : rate c m B ∈ rateSet K := ⟨c, m, B, hP, hKa, rfl⟩
  have hbdd : BddBelow (rateSet K) := by
    refine ⟨0, ?_⟩
    rintro ε ⟨c', m', B', hP', _, rfl⟩
    exact hP'.rate_pos.le
  refine ⟨le_csInf ⟨_, hmem⟩ ?_, (csInf_le hbdd hmem).trans hr⟩
  rintro ε ⟨c', m', B', hP', hKa', rfl⟩
  exact hfloor K c' m' B' hK1 hP' hKa'

/-- **The rate from a zero-free strip.** If `ζ ≠ 0` on `Re s > Θ`, `½ ≤ Θ < 1`, then
`HasRate K^{-(1−Θ)/32}`. -/
theorem hasRate_of_zeroFree {Θ : ℝ} (hΘh : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0) :
    HasRate fun K => (K : ℝ) ^ (-((1 - Θ) / 32)) := by
  set σ : ℝ := (1 - Θ) / 2 with hσ
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hσ1 : σ ≤ 1 := by rw [hσ]; linarith
  obtain ⟨C, hC, hbd⟩ := RHTower.mobiusMertens_subpower_of_zeroFree hΘh hΘ1.le hzf σ hσ0
  have hexp : Θ + σ = 1 - σ := by rw [hσ]; ring
  have hM : ∀ n : ℕ, 1 ≤ n → |RHTower.Sieve.mertensM n| ≤ (C * 2) * (n : ℝ) ^ (1 - σ) := by
    intro n hn
    have hb := hbd n
    rw [RHTower.mobiusMertensPartialSum_eq_sieveMertensM, Complex.norm_real, Real.norm_eq_abs,
      hexp] at hb
    refine hb.trans ?_
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h0 : (0 : ℝ) ≤ 1 - σ := by rw [hσ]; linarith
    have h1 : ((n : ℝ) + 1) ^ (1 - σ) ≤ (2 * (n : ℝ)) ^ (1 - σ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) h0
    have h2 : (2 * (n : ℝ)) ^ (1 - σ) = (2 : ℝ) ^ (1 - σ) * (n : ℝ) ^ (1 - σ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    have h3 : (2 : ℝ) ^ (1 - σ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - σ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have hnp : 0 ≤ (n : ℝ) ^ (1 - σ) := by positivity
    calc C * ((n : ℝ) + 1) ^ (1 - σ) ≤ C * ((2 : ℝ) ^ (1 - σ) * (n : ℝ) ^ (1 - σ)) := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_left h1 hC
      _ ≤ C * (2 * (n : ℝ) ^ (1 - σ)) := by gcongr
      _ = _ := by ring
  have h := hasRate_of_power (C := C * 2) (by positivity) hσ0 hσ1 hM
  have hval : σ / 16 = (1 - Θ) / 32 := by rw [hσ]; ring
  rwa [hval] at h

/-- **The Riemann hypothesis gives a polynomial rate.** Under RH, integer producers have rate
`K^{-1/64}`. -/
theorem hasRate_of_riemannHypothesis (h : RiemannHypothesis) :
    HasRate fun K => (K : ℝ) ^ (-(1 / 64 : ℝ)) := by
  have hzf : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → riemannZeta s ≠ 0 := by
    intro s hs
    by_cases h1 : s.re < 1
    · exact (RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mp h) s hs h1
    · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h1)
  have hr := hasRate_of_zeroFree (Θ := 1 / 2) le_rfl (by norm_num) hzf
  have hval : (1 - (1 / 2 : ℝ)) / 32 = 1 / 64 := by norm_num
  rwa [hval] at hr

/-- **The necessary alphabet of a certificate.** There is an absolute `c > 0` such that a producer on
an alphabet in `[1, K]` with `ε ‖s‖ < 1` has `c ‖s‖ < K^{3/4}`. So certifying `ζ(1 + iτ) ≠ 0` at height
`τ` by a producer needs `K ≫ |τ|^{4/3}`. -/
theorem exists_necessary_alphabet :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : ℕ) (c' : ℕ →₀ ℤ) (m B : ℕ) (x : ℝ), 1 ≤ K → IsProducer c' m B →
      AlphabetLE c' K → 0 < x → rate c' m B * x < 1 → c * x < (K : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨c₁, hc₁, hfloor⟩ := exists_three_quarters_floor
  refine ⟨c₁, hc₁, fun K c' m B x hK hP hal hx hr => ?_⟩
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hf := hfloor K c' m B hK hP hal
  have hrpow : (K : ℝ) ^ (-(3 / 4) : ℝ) * (K : ℝ) ^ (3 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hK0]
    simp
  have hKp : 0 < (K : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hK0 _
  have hstep : c₁ * (K : ℝ) ^ (-(3 / 4) : ℝ) * x ≤ rate c' m B * x :=
    mul_le_mul_of_nonneg_right hf hx.le
  have hlt : c₁ * (K : ℝ) ^ (-(3 / 4) : ℝ) * x < 1 := lt_of_le_of_lt hstep hr
  calc c₁ * x = c₁ * ((K : ℝ) ^ (-(3 / 4) : ℝ) * (K : ℝ) ^ (3 / 4 : ℝ)) * x := by rw [hrpow, mul_one]
    _ = (c₁ * (K : ℝ) ^ (-(3 / 4) : ℝ) * x) * (K : ℝ) ^ (3 / 4 : ℝ) := by ring
    _ < 1 * (K : ℝ) ^ (3 / 4 : ℝ) := mul_lt_mul_of_pos_right hlt hKp
    _ = _ := one_mul _

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
