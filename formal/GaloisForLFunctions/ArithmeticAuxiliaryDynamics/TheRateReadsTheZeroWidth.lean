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
  have hpos1 : 0 ≤ ((K : ℝ) + 1) * ε := mul_nonneg (by positivity) hε.le
  have hbase : 0 ≤ 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * ε) :=
    mul_nonneg (by positivity) (by linarith)
  have hle : 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * ε) ≤
      2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * f) := by
    gcongr
  have h1 := Real.rpow_le_rpow hbase hle (by linarith : 0 ≤ 1 - β)
  have h2 := Real.rpow_le_rpow hε.le hf hβ0.le
  exact mul_le_mul h1 h2 (by positivity) (Real.rpow_nonneg (hbase.trans hle) _)

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
  obtain ⟨K, hK2, hKlt, c, m, B, hP, hKa, hr⟩ := ((eventually_ge_atTop 2).and (hev.and h)).exists
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

/-- The size of the law at height `L`: `W ≤ exp (5 + 2L)` when `exp L ≤ K ≤ 2 exp L`, `ε ≤ 1`. -/
private lemma base_le_exp {K : ℕ} {L ε : ℝ} (hL : 1 ≤ L) (hKge : Real.exp L ≤ K)
    (hKle : (K : ℝ) ≤ 2 * Real.exp L) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * ε) ≤ Real.exp (5 + 2 * L) := by
  have hexpL1 : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
  have hKR : (1 : ℝ) ≤ K := hexpL1.trans hKge
  have hK0 : (0 : ℝ) < K := by linarith
  have hlogKle : Real.log (K : ℝ) ≤ K := Real.log_le_self hK0.le
  have h32 : (32 : ℝ) ≤ Real.exp 5 := by
    have h2 := Real.add_one_le_exp (1 : ℝ)
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := by
          gcongr
          linarith
      _ = Real.exp 5 := by
          rw [← Real.exp_nat_mul]
          norm_num
  have h1 : 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * ε) ≤ 8 * (K : ℝ) ^ 2 := by
    have hε : ((K : ℝ) + 1) * ε ≤ (K : ℝ) + 1 := by
      have : 0 ≤ (K : ℝ) + 1 := by linarith
      nlinarith
    have hsum : 1 + Real.log K + ((K : ℝ) + 1) * ε ≤ 4 * (K : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * (K : ℝ))
    nlinarith
  have h2 : (K : ℝ) ^ 2 ≤ 4 * Real.exp (2 * L) := by
    have hsq : (K : ℝ) ^ 2 ≤ (2 * Real.exp L) ^ 2 := by gcongr
    have hexp2 : Real.exp (2 * L) = Real.exp L ^ 2 := by
      rw [two_mul, Real.exp_add]; ring
    rw [hexp2]
    nlinarith
  have h4 : 32 * Real.exp (2 * L) ≤ Real.exp 5 * Real.exp (2 * L) :=
    mul_le_mul_of_nonneg_right h32 (Real.exp_pos _).le
  rw [Real.exp_add]
  linarith

/-- The law turned into a linear inequality in the logarithms. -/
private lemma log_ineq_of_law {Λ L β ε W : ℝ} (hΛ1 : 1 ≤ Λ) (hL : 1 ≤ L) (hβ : 1 / 2 ≤ β)
    (hβ1 : β ≤ 1) (hε0 : 0 < ε) (hεle : ε ≤ Real.exp (-(4 * Λ))) (hW0 : 0 ≤ W)
    (hWle : W ≤ Real.exp (5 + 2 * L)) (hlaw : 1 ≤ Real.exp Λ * (W ^ (1 - β) * ε ^ β)) :
    Λ ≤ 7 * L * (1 - β) := by
  have hβ0 : 0 < β := by linarith
  have h1β : 0 ≤ 1 - β := by linarith
  have hpow1 : W ^ (1 - β) ≤ Real.exp ((5 + 2 * L) * (1 - β)) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow hW0 hWle h1β
  have hpow2 : ε ^ β ≤ Real.exp (-(2 * Λ)) := by
    have h1 : ε ^ β ≤ Real.exp (-(4 * Λ)) ^ β := Real.rpow_le_rpow hε0.le hεle hβ0.le
    rw [← Real.exp_mul] at h1
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  have hchain : 1 ≤ Real.exp (Λ + (5 + 2 * L) * (1 - β) + -(2 * Λ)) := by
    rw [Real.exp_add, Real.exp_add, mul_assoc]
    refine hlaw.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    exact mul_le_mul hpow1 hpow2 (by positivity) (Real.exp_pos _).le
  have hineq : Λ ≤ (5 + 2 * L) * (1 - β) := by
    have := (Real.one_le_exp_iff).mp hchain
    linarith
  nlinarith

/-- The algebra of the exponent. -/
private lemma coef_le_of_ineq {α Λ β : ℝ} (hΛ0 : 0 < Λ)
    (h : Λ ≤ 7 * (4 * Λ) ^ (1 / α) * (1 - β)) :
    (1 / (7 * (4 : ℝ) ^ (1 / α))) * Λ ^ (1 - 1 / α) ≤ 1 - β := by
  have hΛpos : 0 < Λ ^ (1 / α) := Real.rpow_pos_of_pos hΛ0 _
  have h4pos : 0 < (4 : ℝ) ^ (1 / α) := by positivity
  rw [Real.mul_rpow (by norm_num) hΛ0.le] at h
  rw [Real.rpow_sub hΛ0, Real.rpow_one]
  generalize Λ ^ (1 / α) = P at *
  generalize (4 : ℝ) ^ (1 / α) = A at *
  have hid : 1 / (7 * A) * (Λ / P) = Λ / (7 * (A * P)) := by field_simp
  rw [hid, div_le_iff₀ (by positivity)]
  linarith

/-- Trivial range of the region: the coefficient is at most `1/2`. -/
private lemma coef_le_half {α Λ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hΛ1 : 1 ≤ Λ) :
    (1 / (7 * (4 : ℝ) ^ (1 / α))) * Λ ^ (1 - 1 / α) ≤ 1 / 2 := by
  have hinv : 1 ≤ 1 / α := by rw [le_div_iff₀ hα0]; linarith
  have h4pow : 1 ≤ (4 : ℝ) ^ (1 / α) := Real.one_le_rpow (by norm_num) (by linarith)
  have hΛpow : Λ ^ (1 - 1 / α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΛ1 (by linarith)
  have hΛpow0 : 0 ≤ Λ ^ (1 - 1 / α) := by positivity
  have h1 : 1 / (7 * (4 : ℝ) ^ (1 / α)) ≤ 1 / 7 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  calc _ ≤ 1 / 7 * 1 := mul_le_mul h1 hΛpow hΛpow0 (by norm_num)
    _ ≤ 1 / 2 := by norm_num

/-- **A subpolynomial rate gives a zero-free region of Vinogradov–Korobov shape.** A rate
`exp(−(log K)^α)`, `0 < α ≤ 1`, forces `Re ρ ≤ 1 − c Λ^{1 − 1/α}` with `Λ = log (24 ‖ρ‖)`, for zeros
of large modulus. At `α = 3/5` the exponent is `−2/3`. -/
theorem exists_re_le_of_hasRate_exp {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (h : HasRate fun K => Real.exp (-(Real.log K) ^ α)) :
    ∃ T₀ : ℝ, ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ ‖ρ‖ →
      ρ.re ≤ 1 - (1 / (7 * (4 : ℝ) ^ (1 / α))) * Real.log (24 * ‖ρ‖) ^ (1 - 1 / α) := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp h
  refine ⟨Real.exp (max 1 (K₀ : ℝ)) / 24, fun ρ hρ hT => ?_⟩
  have hexp_pos := Real.exp_pos (max 1 (K₀ : ℝ))
  have h24 : Real.exp (max 1 (K₀ : ℝ)) ≤ 24 * ‖ρ‖ := by
    rw [div_le_iff₀ (by norm_num)] at hT
    linarith
  have h24pos : 0 < 24 * ‖ρ‖ := lt_of_lt_of_le hexp_pos h24
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = Real.log (24 * ‖ρ‖) := ⟨_, rfl⟩
  rw [← hΛ]
  have hΛmax : max 1 (K₀ : ℝ) ≤ Λ := by
    rw [hΛ, Real.le_log_iff_exp_le h24pos]
    exact h24
  have hΛ1 : 1 ≤ Λ := (le_max_left _ _).trans hΛmax
  have hΛK : (K₀ : ℝ) ≤ Λ := (le_max_right _ _).trans hΛmax
  have hΛ0 : 0 < Λ := by linarith
  have hexpΛ : Real.exp Λ = 24 * ‖ρ‖ := by rw [hΛ]; exact Real.exp_log h24pos
  by_cases hβ : ρ.re < 1 / 2
  · linarith [coef_le_half (Λ := Λ) hα0 hα1 hΛ1]
  push Not at hβ
  have hβ1 : ρ.re ≤ 1 := by
    by_contra hgt
    push Not at hgt
    exact riemannZeta_ne_zero_of_one_le_re hgt.le hρ
  have hinv : 1 ≤ 1 / α := by rw [le_div_iff₀ hα0]; linarith
  have h4Λ : 1 ≤ 4 * Λ := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = (4 * Λ) ^ (1 / α) := ⟨_, rfl⟩
  have hLα : L ^ α = 4 * Λ := by
    rw [hL, ← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hα0.ne', Real.rpow_one]
  have hLge : 4 * Λ ≤ L := by
    rw [hL]
    calc 4 * Λ = (4 * Λ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h4Λ hinv
  have hL1 : 1 ≤ L := by linarith
  have hexpL1 : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
  obtain ⟨K, hK⟩ : ∃ K, K = ⌈Real.exp L⌉₊ := ⟨_, rfl⟩
  have hKge : Real.exp L ≤ K := hK ▸ Nat.le_ceil _
  have hKle : (K : ℝ) ≤ 2 * Real.exp L := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Real.exp L by linarith)
    rw [hK]
    linarith
  have hKR : (1 : ℝ) ≤ K := hexpL1.trans hKge
  have hK0 : (0 : ℝ) < K := by linarith
  have hexpgeL : L + 1 ≤ Real.exp L := Real.add_one_le_exp L
  have hK₀K : K₀ ≤ K := by
    have : (K₀ : ℝ) ≤ K := by linarith
    exact_mod_cast this
  obtain ⟨c, m, B, hP, hKa, hr⟩ := hK₀ K hK₀K
  have hlogK : L ≤ Real.log K := by
    rw [Real.le_log_iff_exp_le hK0]
    exact hKge
  have hrate : rate c m B ≤ Real.exp (-(4 * Λ)) := by
    refine hr.trans (Real.exp_le_exp.mpr ?_)
    have : (4 * Λ) ≤ Real.log (K : ℝ) ^ α := by
      rw [← hLα]
      exact Real.rpow_le_rpow (by linarith) hlogK hα0.le
    linarith
  have hr1 : rate c m B ≤ 1 := hrate.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hεpos := hP.rate_pos
  have hlaw := hP.rate_law hKa hr1 hρ hβ hβ1
  have hW0 : 0 ≤ 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * rate c m B) := by
    have hlogK0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
    have h1 : 0 ≤ ((K : ℝ) + 1) * rate c m B := mul_nonneg (by linarith) hεpos.le
    exact mul_nonneg (by positivity) (by linarith)
  have hineq := log_ineq_of_law hΛ1 hL1 hβ hβ1 hεpos hrate hW0
    (base_le_exp hL1 hKge hKle hεpos.le hr1) (by rw [hexpΛ]; exact hlaw)
  rw [hL] at hineq
  linarith [coef_le_of_ineq (α := α) hΛ0 hineq]

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
