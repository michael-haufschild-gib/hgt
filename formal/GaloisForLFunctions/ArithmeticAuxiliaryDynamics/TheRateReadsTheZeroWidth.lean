import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheUncertaintyLawOfAProducer
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The rate of a producer family reads the zero width

`HasRate f` says that for all large `K` some producer on an alphabet in `[1, K]` has rate at most
`f(K)`. The rate law turns such a family into a zero-free region, in the only way the two can meet.

* A rate `K^{-a}`, `0 < a ≤ 1`, gives `Re ρ ≤ 1 − a/2` for every zero. So any polynomial rate gives a
  zero-free strip, and rates `K^{-a}` for all `a < 1` give the Riemann hypothesis. The floor of the
  slope stops at `1/(K log K)`, so `a = 1` is the end of the scale.
* A rate `exp(−(log K)^α)`, `0 < α ≤ 1`, gives
  `Re ρ ≤ 1 − c (log ‖ρ‖)^{1 − 1/α}`. At `α = 3/5` this is the Vinogradov–Korobov exponent `2/3`.

Both are one-way: they say what a construction would give, with no construction assumed to exist.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- For all large `K` there is a producer on an alphabet in `[1, K]` of rate at most `f(K)`. -/
def HasRate (f : ℕ → ℝ) : Prop :=
  ∀ᶠ K : ℕ in atTop, ∃ (c : ℕ →₀ ℤ) (m B : ℕ),
    IsProducer c m B ∧ AlphabetLE c K ∧ rate c m B ≤ f K

/-- The law is monotone in the rate. -/
private lemma rate_law_mono {K : ℕ} (hK : 1 ≤ K) {ε f : ℝ} (hε : 0 < ε) (hf : ε ≤ f) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * ε)) ^ (1 - β) * ε ^ β ≤
      (2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * f)) ^ (1 - β) * f ^ β := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog : 0 ≤ Real.log (K : ℝ) := Real.log_natCast_nonneg K
  have hbase : 0 ≤ 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * ε) := by positivity
  have hle : 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * ε) ≤
      2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * f) := by
    gcongr
  have h1 := Real.rpow_le_rpow hbase hle (by linarith : 0 ≤ 1 - β)
  have h2 := Real.rpow_le_rpow hε.le hf hβ0.le
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **A polynomial rate gives a zero-free strip.** A rate `K^{-a}`, `0 < a ≤ 1`, forces
`Re ρ ≤ 1 − a/2` for every zero of `ζ`. -/
theorem re_le_of_hasRate_rpow {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (h : HasRate fun K => (K : ℝ) ^ (-a)) {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    ρ.re ≤ 1 - a / 2 := by
  by_contra hlt
  push Not at hlt
  have hβ1 : ρ.re ≤ 1 := by
    by_contra hgt
    push Not at hgt
    exact riemannZeta_ne_zero_of_one_le_re hgt.le hρ
  have hβ : 1 / 2 ≤ ρ.re := by linarith
  set β := ρ.re with hβdef
  have hβ0 : 0 < β := by linarith
  set δ : ℝ := 2 * β + a - 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hρpos : 0 ≤ ‖ρ‖ := norm_nonneg ρ
  -- The size of the right side at height `K` tends to zero.
  have hlim : Tendsto (fun x : ℝ => (3 + Real.log x) * x ^ (-δ)) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_neg_atTop hδ0
    have h2 := (isLittleO_log_rpow_atTop hδ0).tendsto_div_nhds_zero
    have h3 := (h1.const_mul 3).add h2
    rw [mul_zero, add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_neg hx.le]
    field_simp
  have hlimK : Tendsto (fun K : ℕ => 48 * ‖ρ‖ * ((3 + Real.log (K : ℝ)) * (K : ℝ) ^ (-δ)))
      atTop (𝓝 0) := by
    have := (hlim.comp tendsto_natCast_atTop_atTop).const_mul (48 * ‖ρ‖)
    simpa using this
  have hev := hlimK.eventually (gt_mem_nhds (zero_lt_one))
  obtain ⟨K, hK2, hKlt, c, m, B, hP, hKa, hr⟩ :=
    ((eventually_ge_atTop 2).and (hev.and h)).exists.imp fun K hK => ⟨hK.1, hK.2.1, hK.2.2⟩
      |> fun h' => h'
  have hK1 : 1 ≤ K := by omega
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
  have hpow1 : (K : ℝ) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hKR (by linarith)
  have hr1 : rate c m B ≤ 1 := hr.trans hpow1
  have hεpos := hP.rate_pos
  have hlaw := hP.rate_law hKa hr1 hρ hβ hβ1
  have hmono := rate_law_mono hK1 hεpos hr hβ0 hβ1
  rw [← hβdef] at hlaw
  -- Bound the base of the law.
  set f : ℝ := (K : ℝ) ^ (-a) with hf
  have hfK : ((K : ℝ) + 1) * f ≤ 2 * (K : ℝ) ^ (1 - a) := by
    have hsplit : (K : ℝ) ^ (1 - a) = (K : ℝ) * f := by
      rw [hf, sub_eq_add_neg, Real.rpow_add hK0, Real.rpow_one]
    rw [hsplit]
    have hf0 : 0 ≤ f := by positivity
    nlinarith
  have hK1a : 1 ≤ (K : ℝ) ^ (1 - a) := Real.one_le_rpow hKR (by linarith)
  have hbase : 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * f) ≤
      (2 * (3 + Real.log K)) * (K : ℝ) ^ (2 - a) := by
    have hsplit2 : (K : ℝ) ^ (2 - a) = (K : ℝ) * (K : ℝ) ^ (1 - a) := by
      rw [show (2 : ℝ) - a = 1 + (1 - a) by ring, Real.rpow_add hK0, Real.rpow_one]
    rw [hsplit2]
    have h1 : 1 + Real.log K + ((K : ℝ) + 1) * f ≤ (3 + Real.log K) * (K : ℝ) ^ (1 - a) := by
      nlinarith
    calc 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * f)
        ≤ 2 * (K : ℝ) * ((3 + Real.log K) * (K : ℝ) ^ (1 - a)) := by gcongr
      _ = _ := by ring
  have hbase0 : 0 ≤ 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * f) := by positivity
  have hA1 : 1 ≤ 2 * (3 + Real.log (K : ℝ)) := by linarith
  have hexp : 0 ≤ 1 - β := by linarith
  have hexp1 : 1 - β ≤ 1 := by linarith
  have hAW : (2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * f)) ^ (1 - β) * f ^ β ≤
      (2 * (3 + Real.log (K : ℝ))) * (K : ℝ) ^ (-δ) := by
    have h1 : (2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * f)) ^ (1 - β) ≤
        ((2 * (3 + Real.log (K : ℝ))) * (K : ℝ) ^ (2 - a)) ^ (1 - β) :=
      Real.rpow_le_rpow hbase0 hbase hexp
    have h2 : ((2 * (3 + Real.log (K : ℝ))) * (K : ℝ) ^ (2 - a)) ^ (1 - β) =
        (2 * (3 + Real.log (K : ℝ))) ^ (1 - β) * (K : ℝ) ^ ((2 - a) * (1 - β)) := by
      rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul hK0.le]
    have h3 : (2 * (3 + Real.log (K : ℝ))) ^ (1 - β) ≤ 2 * (3 + Real.log (K : ℝ)) := by
      calc _ ≤ (2 * (3 + Real.log (K : ℝ))) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hA1 hexp1
        _ = _ := Real.rpow_one _
    have h4 : (K : ℝ) ^ ((2 - a) * (1 - β)) * f ^ β = (K : ℝ) ^ (-δ) := by
      rw [hf, ← Real.rpow_mul hK0.le, ← Real.rpow_add hK0, hδ]
      congr 1
      ring
    have hKp : 0 ≤ (K : ℝ) ^ ((2 - a) * (1 - β)) := by positivity
    have hfp : 0 ≤ f ^ β := by positivity
    calc (2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * f)) ^ (1 - β) * f ^ β
        ≤ ((2 * (3 + Real.log (K : ℝ))) ^ (1 - β) * (K : ℝ) ^ ((2 - a) * (1 - β))) * f ^ β := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_right h1 hfp
      _ = (2 * (3 + Real.log (K : ℝ))) ^ (1 - β) * ((K : ℝ) ^ ((2 - a) * (1 - β)) * f ^ β) := by ring
      _ = (2 * (3 + Real.log (K : ℝ))) ^ (1 - β) * (K : ℝ) ^ (-δ) := by rw [h4]
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 (by positivity)
  have hfinal : 1 ≤ 24 * ‖ρ‖ * ((2 * (3 + Real.log (K : ℝ))) * (K : ℝ) ^ (-δ)) :=
    hlaw.trans (mul_le_mul_of_nonneg_left (hmono.trans hAW) (by positivity))
  have hid : 24 * ‖ρ‖ * ((2 * (3 + Real.log (K : ℝ))) * (K : ℝ) ^ (-δ)) =
      48 * ‖ρ‖ * ((3 + Real.log (K : ℝ)) * (K : ℝ) ^ (-δ)) := by ring
  rw [hid] at hfinal
  linarith

/-- **Rates up to the floor give the Riemann hypothesis.** If rates `K^{-a}` exist for every
`a < 1`, every zero of `ζ` in the critical strip has real part at most `1/2`. -/
theorem riemannHypothesis_of_hasRate (h : ∀ a : ℝ, 0 < a → a < 1 → HasRate fun K => (K : ℝ) ^ (-a)) :
    RiemannHypothesis := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro s hs hs1 hzero
  have hb := re_le_of_hasRate_rpow (a := (2 * (1 - s.re) + 1) / 2) (by linarith) (by linarith)
    (h _ (by linarith) (by linarith)) hzero
  linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
