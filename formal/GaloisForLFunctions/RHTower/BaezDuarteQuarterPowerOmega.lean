import GaloisForLFunctions.RHTower.BaezDuarteRieszPoissonCriterion
import GaloisForLFunctions.RHTower.RieszFunctionQuarterPowerOmega

/-!
# The Báez--Duarte coefficients are `Ω±(k^{-3/4})`

Poissonization `R(x) = e^{-x} Σ_k c_k x^k/k!` has nonnegative weights, so it transfers one-sided
bounds: `ηc_k ≤ C(k+1)^{-β}` for `k ≥ k₀` gives
`ηR(x) ≤ 2C x^{-β} + Z Σ_{k<k₀} e^{-x}x^k/k!`, and the finite tail times `x` vanishes at infinity.
With `β = 3/4` this is an eventual one-sided bound `ηF(x) ≤ (2C + δ)x^{1/4}` for the Riesz function,
so the Riesz quarter-power boundary applies: a one-sided `ηc_k ≤ C(k+1)^{-3/4}` implies RH and
simplicity of the critical zeros, and `F = Ω±(x^{1/4})` forces `c_k = Ω±(k^{-3/4})`.
-/

open Filter Finset Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- The finitely many Poisson weights below `k₀`, times `x`, vanish at infinity. -/
theorem tendsto_mul_sum_poissonProbWeight_zero (k₀ : ℕ) :
    Tendsto (fun x : ℝ => x * ∑ k ∈ range k₀, poissonProbWeight x k) atTop (𝓝 0) := by
  have h : ∀ k ∈ range k₀, Tendsto (fun x : ℝ => x * poissonProbWeight x k) atTop (𝓝 0) := by
    intro k _
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (k + 1)).mul_const
      ((k.factorial : ℝ)⁻¹)
    rw [zero_mul] at this
    refine this.congr fun x => ?_
    unfold poissonProbWeight
    rw [pow_succ]
    ring
  have := tendsto_finsetSum (range k₀) h
  simp only [sum_const_zero] at this
  refine this.congr fun x => ?_
  rw [mul_sum]

/-- **One-sided Poisson transfer.**  If `ηc_k ≤ C(k+1)^{-β}` for `k ≥ k₀` (`C ≥ 0`,
`0 ≤ β ≤ 1`), then `ηR(x) ≤ 2C x^{-β} + Z Σ_{k<k₀} e^{-x}x^k/k!`, `Z = Σ n^{-2}`. -/
theorem mul_rieszSeries_le_of_bdReal_le {η C β : ℝ} {k₀ : ℕ} (hη : |η| = 1) (hC : 0 ≤ C)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h : ∀ k : ℕ, k₀ ≤ k → η * bdReal k ≤ C * ((k : ℝ) + 1) ^ (-β)) {x : ℝ} (hx : 0 < x) :
    η * rieszSeries x ≤ 2 * C * x ^ (-β) +
      (∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) * ∑ k ∈ range k₀, poissonProbWeight x k := by
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹
  have hZ : 0 ≤ Z := tsum_nonneg fun n => by positivity
  have hw0 := poissonProbWeight_nonneg hx.le
  set g : ℕ → ℝ := fun k => C * ((k : ℝ) + 1) ^ (-β) + if k < k₀ then Z else 0 with hg
  have hle : ∀ k, η * bdReal k ≤ g k := by
    intro k
    simp only [hg]
    by_cases hk : k < k₀
    · rw [if_pos hk]
      have h1 : η * bdReal k ≤ Z := by
        calc η * bdReal k ≤ |η * bdReal k| := le_abs_self _
          _ = |bdReal k| := by rw [abs_mul, hη, one_mul]
          _ ≤ Z := abs_bdReal_le k
      have : 0 ≤ C * ((k : ℝ) + 1) ^ (-β) := mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
      linarith
    · rw [if_neg hk, add_zero]
      exact h k (not_lt.mp hk)
  have hS := summable_poissonProbWeight x
  have hsumL : Summable fun k => poissonProbWeight x k * (η * bdReal k) := by
    refine (hS.mul_right Z).of_norm_bounded_eventually ?_
    exact Eventually.of_forall fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 k), abs_mul, hη, one_mul]
      exact mul_le_mul_of_nonneg_left (abs_bdReal_le k) (hw0 k)
  have hsumP : Summable fun k : ℕ => poissonProbWeight x k * ((k : ℝ) + 1) ^ (-β) :=
    hS.of_nonneg_of_le (fun k => mul_nonneg (hw0 k) (Real.rpow_nonneg (by positivity) _))
      fun k => mul_le_of_le_one_right (hw0 k) (Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]) (by linarith))
  have hsumF : Summable fun k : ℕ => poissonProbWeight x k * (if k < k₀ then Z else 0) := by
    refine summable_of_ne_finset_zero (s := range k₀) fun k hk => ?_
    rw [mem_range] at hk
    rw [if_neg hk, mul_zero]
  have hsumR : Summable fun k => poissonProbWeight x k * g k := by
    have := (hsumP.mul_left C).add hsumF
    refine this.congr fun k => ?_
    simp only [hg]; ring
  have hfin : ∑' k : ℕ, poissonProbWeight x k * (if k < k₀ then Z else 0) =
      Z * ∑ k ∈ range k₀, poissonProbWeight x k := by
    rw [tsum_eq_sum (s := range k₀) fun k hk => by
      rw [mem_range] at hk; rw [if_neg hk, mul_zero], mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [if_pos hk]; ring
  rw [rieszSeries_eq_tsum_poissonProbWeight_mul_bdReal, ← tsum_mul_left]
  calc ∑' k : ℕ, η * (poissonProbWeight x k * bdReal k)
      = ∑' k : ℕ, poissonProbWeight x k * (η * bdReal k) := tsum_congr fun k => by ring
    _ ≤ ∑' k : ℕ, poissonProbWeight x k * g k :=
        hsumL.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hle k) (hw0 k)) hsumR
    _ = C * ∑' k : ℕ, poissonProbWeight x k * ((k : ℝ) + 1) ^ (-β) +
          ∑' k : ℕ, poissonProbWeight x k * (if k < k₀ then Z else 0) := by
        rw [← tsum_mul_left, ← (hsumP.mul_left C).tsum_add hsumF]
        refine tsum_congr fun k => ?_
        simp only [hg]; ring
    _ ≤ C * (2 * x ^ (-β)) + Z * ∑ k ∈ range k₀, poissonProbWeight x k := by
        rw [hfin]
        gcongr
        exact tsum_poissonProbWeight_mul_rpow_le hx hβ0 hβ1
    _ = 2 * C * x ^ (-β) + Z * ∑ k ∈ range k₀, poissonProbWeight x k := by ring

/-- An eventual one-sided quarter-power bound for `c_k` gives one for `F` with twice the constant
plus any `δ > 0`. -/
theorem eventually_mul_rieszFunction_le_of_bdReal_le {η c δ : ℝ} {k₀ : ℕ} (hη : |η| = 1)
    (hc : 0 ≤ c) (hδ : 0 < δ)
    (h : ∀ k : ℕ, k₀ ≤ k → η * bdReal k ≤ c * ((k : ℝ) + 1) ^ (-(3 / 4 : ℝ))) :
    ∀ᶠ x : ℝ in atTop, η * rieszFunction x ≤ (2 * c + δ) * x ^ (1 / 4 : ℝ) := by
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹
  have hZ : 0 ≤ Z := tsum_nonneg fun n => by positivity
  have htend := (tendsto_mul_sum_poissonProbWeight_zero k₀).const_mul Z
  rw [mul_zero] at htend
  filter_upwards [htend.eventually (ge_mem_nhds hδ), eventually_ge_atTop 1] with x hsmall hx1
  have hx : 0 < x := by linarith
  have hR := mul_rieszSeries_le_of_bdReal_le hη hc (by norm_num) (by norm_num) h hx
  have hq : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hpow : x * x ^ (-(3 / 4 : ℝ)) = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_one_add' hx.le (by norm_num)]; norm_num
  have hF : η * rieszFunction x = x * (η * rieszSeries x) := by rw [rieszFunction]; ring
  rw [hF]
  calc x * (η * rieszSeries x)
      ≤ x * (2 * c * x ^ (-(3 / 4 : ℝ)) + Z * ∑ k ∈ range k₀, poissonProbWeight x k) :=
        mul_le_mul_of_nonneg_left hR hx.le
    _ = 2 * c * x ^ (1 / 4 : ℝ) + Z * (x * ∑ k ∈ range k₀, poissonProbWeight x k) := by
        rw [← hpow]; ring
    _ ≤ 2 * c * x ^ (1 / 4 : ℝ) + δ * x ^ (1 / 4 : ℝ) := by
        have : Z * (x * ∑ k ∈ range k₀, poissonProbWeight x k) ≤ δ := hsmall
        nlinarith
    _ = (2 * c + δ) * x ^ (1 / 4 : ℝ) := by ring

/-- **A one-sided bound `ηc_k ≤ c(k+1)^{-3/4}` for the Báez--Duarte coefficients implies the
Riemann hypothesis**, and makes every zero on the critical line simple. -/
theorem riemannHypothesis_of_bdReal_oneSided {η c : ℝ} {k₀ : ℕ} (hη : |η| = 1) (hc : 0 ≤ c)
    (h : ∀ k : ℕ, k₀ ≤ k → η * bdReal k ≤ c * ((k : ℝ) + 1) ^ (-(3 / 4 : ℝ))) :
    RiemannHypothesis :=
  riemannHypothesis_of_rieszFunction_oneSided hη (by linarith : 0 ≤ 2 * c + 1)
    (eventually_mul_rieszFunction_le_of_bdReal_le hη hc one_pos h)

theorem deriv_zetaResidueUnit_ne_zero_of_bdReal_oneSided {η c : ℝ} {k₀ : ℕ} (hη : |η| = 1)
    (hc : 0 ≤ c) (h : ∀ k : ℕ, k₀ ≤ k → η * bdReal k ≤ c * ((k : ℝ) + 1) ^ (-(3 / 4 : ℝ)))
    {ρ : ℂ} (hρre : ρ.re = 1 / 2) (hρim : ρ.im ≠ 0) (hρ0 : zetaResidueUnit ρ = 0) :
    deriv zetaResidueUnit ρ ≠ 0 :=
  deriv_zetaResidueUnit_ne_zero_of_rieszFunction_oneSided hη (by linarith : 0 ≤ 2 * c + 1)
    (eventually_mul_rieszFunction_le_of_bdReal_le hη hc one_pos h) hρre hρim hρ0

/-- **The Báez--Duarte coefficients are `Ω±(k^{-3/4})`.** -/
theorem bdReal_omega_pm :
    ∃ c : ℝ, 0 < c ∧ (∃ᶠ k : ℕ in atTop, c * ((k : ℝ) + 1) ^ (-(3 / 4 : ℝ)) < bdReal k)
      ∧ ∃ᶠ k : ℕ in atTop, bdReal k < -(c * ((k : ℝ) + 1) ^ (-(3 / 4 : ℝ))) := by
  obtain ⟨cF, hcF, hup, hdown⟩ := rieszFunction_omega_pm_quarter
  refine ⟨cF / 4, by positivity, ?_, ?_⟩
  · by_contra hno
    rw [Filter.not_frequently] at hno
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hno
    have hev := eventually_mul_rieszFunction_le_of_bdReal_le (η := 1) (c := cF / 4)
      (δ := cF / 2) (k₀ := k₀) (by simp) (by positivity) (by positivity)
      fun k hk => by rw [one_mul]; exact not_lt.mp (hk₀ k hk)
    obtain ⟨x, hx1, hx2⟩ := (hup.and_eventually hev).exists
    rw [one_mul] at hx2
    linarith
  · by_contra hno
    rw [Filter.not_frequently] at hno
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hno
    have hev := eventually_mul_rieszFunction_le_of_bdReal_le (η := -1) (c := cF / 4)
      (δ := cF / 2) (k₀ := k₀) (by simp) (by positivity) (by positivity)
      fun k hk => by have := not_lt.mp (hk₀ k hk); linarith
    obtain ⟨x, hx1, hx2⟩ := (hdown.and_eventually hev).exists
    linarith

/-- The Báez--Duarte coefficients are not `o(k^{-3/4})`. -/
theorem not_bdReal_isLittleO :
    ¬ (fun k : ℕ => bdReal k) =o[atTop] fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 4 : ℝ)) := by
  intro h
  obtain ⟨c, hc, hfr, -⟩ := bdReal_omega_pm
  have hb := h.bound hc
  obtain ⟨k, hk1, hk2⟩ := (hfr.and_eventually hb).exists
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
    at hk2
  linarith [le_abs_self (bdReal k)]

end

end RHTower
