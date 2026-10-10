import GaloisForLFunctions.RHTower.LiEvenCrossActualClockNegativeResponse
import GaloisForLFunctions.RHTower.LiCayleyWindowLaw

/-!
# The growth law of the actual Li clock response

The literal completed-source response of route LI is `R(t) = Re Σ_q w_q sin(t w_q)` over the zero
copies, with `w_q = 1/a_q` and `a_q = -i(ρ - 1/2)` the spectral point. Its imaginary frequencies
`b_q = |Im w_q| = |β - 1/2|/(γ² + (β - 1/2)²)` vanish exactly on the critical line.

**Theorem** (`growthRate_le_iff_liEvenCrossActualClock_lower`). For `r ≥ 0`, every zero has
`b_q ≤ r` iff for every `r' > r` some `C` gives `R(t) ≥ -C e^{r' t}` eventually.

* `r = 0` is RH (`riemannHypothesis_iff_liEvenCrossActualClock_subexp_lower`). The receiver
  "eventually `R ≥ 0`" (`riemannHypothesis_of_liEvenCrossActualClock_eventually_nonneg`) therefore
  only needs a subexponential lower bound.
* Every off-line zero has `γ² ≥ 431/2`, so every `b_q ≤ 1/431`. Unconditionally,
  `R(t) ≥ -C e^{r' t}` eventually for every `r' > 1/431`
  (`exists_liEvenCrossActualClock_lower_of_431_lt`).

Since `b_q ≍ |β - 1/2|/γ²`, a fixed rate `r` is RH in the lens below height `≍ r^{-1/2}`. The clock
response follows the same window law as the Li coefficients.
-/

open scoped BigOperators Topology
open Filter
namespace RHTower
noncomputable section

private theorem actualResponse_split' (Q : Set XiZeroCopy) [Fintype Q]
    [DecidablePred (· ∈ Q)] (t : ℝ) :
    liEvenCrossActualClockResponse t =
      (∑ q : Q, (liEvenCrossActualClockSineAtom t q.val).re) +
        (∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockSineAtom t q).re := by
  classical
  rw [liEvenCrossActualClockResponse_eq_re_tsum_sine,
    ← (summable_liEvenCrossActualClockSineAtom t).tsum_subtype_add_tsum_subtype_compl Q,
    Complex.add_re, tsum_fintype]
  congr 1
  · exact map_sum Complex.reAddGroupHom _ _
  · congr 1
    rw [tsum_subtype]
    apply tsum_congr
    intro q
    by_cases hq : q ∈ Q <;> simp [Set.indicator, hq]

/-- **The negative limit at the top frequency.** Off the line, the response normalized at the
largest frequency `b` has a negative limit along cofinal clocks, and `b` dominates every
frequency. -/
theorem exists_top_negative_normalized_limit_of_not_rh (hnot : ¬RiemannHypothesis) :
    ∃ b : ℝ, 0 < b ∧ (∀ q, liEvenCrossActualClockReciprocalGrowthRate q ≤ b) ∧ ∃ L : ℝ, L < 0 ∧
      ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
        Tendsto (fun n => Real.exp (-b * t n) * liEvenCrossActualClockResponse (t n))
          atTop (𝓝 L) := by
  classical
  obtain ⟨b, hb, hQfin, hQnonempty, hmax, β, hβ0, hgap, hβ⟩ :=
    exists_liEvenCrossActualClockTopPacket_of_not_rh hnot
  let Q := liEvenCrossActualClockTopPacket b
  letI : Fintype Q := hQfin.fintype
  letI : Nonempty Q := hQnonempty.to_subtype
  let w : Q → ℂ := fun q => (xiSpectralPoint q.val)⁻¹
  have hw (q : Q) : |(w q).im| = b := q.property
  obtain ⟨t, -, htcofinal, htop⟩ :=
    exists_liClockFiniteTopSinePacket_negative_limit w hb hw
  have hcompl :=
    (liEvenCrossActualClock_tendsto_normalized_complement_zero Q hβ0 hβ hgap).comp htcofinal
  have htail : Tendsto (fun n => Real.exp (-b * t n) *
      (∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockSineAtom (t n) q).re)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hcompl
  have hcard : 0 < (Fintype.card Q : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨b, hb, hmax, -b * (Fintype.card Q : ℝ) / 2, by nlinarith [mul_pos hb hcard], t,
    htcofinal, ?_⟩
  have hsum := htop.add htail
  have heq (n : ℕ) :
      Real.exp (-b * t n) * liEvenCrossActualClockResponse (t n) =
        Real.exp (-b * t n) * (∑ q : Q, (w q * Complex.sin ((t n : ℂ) * w q)).re) +
          Real.exp (-b * t n) *
            (∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockSineAtom (t n) q).re := by
    rw [actualResponse_split' Q (t n)]
    simp only [liEvenCrossActualClockSineAtom, w, mul_add]
  simpa only [← heq, add_zero] using hsum

/-- Under RH every frequency vanishes. -/
theorem growthRate_eq_zero_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    liEvenCrossActualClockReciprocalGrowthRate q = 0 := by
  have hre : ((q.1 : ℂ)).re = 1 / 2 :=
    (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) _ (xi_eq_zero_of_mem_divisor_support q.1)
  have hreal : xiSpectralPoint q = ((((q.1 : ℂ)).im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [xiSpectralPoint, hre]
  rw [liEvenCrossActualClockReciprocalGrowthRate, hreal, ← Complex.ofReal_inv, Complex.ofReal_im,
    abs_zero]

/-- **The growth law.** -/
theorem growthRate_le_iff_liEvenCrossActualClock_lower {r : ℝ} (hr : 0 ≤ r) :
    (∀ q, liEvenCrossActualClockReciprocalGrowthRate q ≤ r) ↔
      ∀ r' : ℝ, r < r' → ∃ C : ℝ, ∀ᶠ t : ℝ in atTop,
        -(C * Real.exp (r' * t)) ≤ liEvenCrossActualClockResponse t := by
  constructor
  · intro h r' hrr
    set M : ℝ := ∑' q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖ ^ 2 with hM
    have hM0 : 0 ≤ M := tsum_nonneg fun _ => sq_nonneg _
    -- `t e^{rt} ≤ K e^{r't}`
    have hlim : Tendsto (fun t : ℝ => t * Real.exp (-(r' - r) * t)) atTop (𝓝 0) := by
      have hδ : 0 < r' - r := sub_pos.mpr hrr
      have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop hδ)
      have heq : (fun t : ℝ => (1 / (r' - r)) * (((r' - r) * t) ^ 1 * Real.exp (-((r' - r) * t))))
          = fun t : ℝ => t * Real.exp (-(r' - r) * t) := by
        funext t; rw [pow_one, neg_mul]; field_simp
      simpa only [heq, mul_zero, Function.comp_def, id] using hbase.const_mul (1 / (r' - r))
    obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds one_pos))
    refine ⟨M, ?_⟩
    filter_upwards [eventually_ge_atTop (max T 0)] with t ht
    have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
    have hbd := liEvenCrossActualClock_norm_complement_le (∅ : Set XiZeroCopy) hr
      (fun q _ => h q) ht0
    simp only [Set.mem_empty_iff_false, if_false] at hbd
    have hre : -‖∑' q : XiZeroCopy, liEvenCrossActualClockSineAtom t q‖ ≤
        liEvenCrossActualClockResponse t := by
      rw [liEvenCrossActualClockResponse_eq_re_tsum_sine]
      exact neg_le_of_abs_le (Complex.abs_re_le_norm _)
    have hTt := hT t (le_trans (le_max_left _ _) ht)
    have hexp : t * Real.exp (r * t) ≤ Real.exp (r' * t) := by
      have h1 : t * Real.exp (-(r' - r) * t) * Real.exp (r' * t) = t * Real.exp (r * t) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      rw [← h1]
      exact mul_le_of_le_one_left (Real.exp_pos _).le hTt.le
    have : M * t * Real.exp (r * t) ≤ M * Real.exp (r' * t) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hexp hM0
    linarith
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨q₀, hq₀⟩ := hcon
    have hnot : ¬RiemannHypothesis := fun hRH => by
      rw [growthRate_eq_zero_of_rh hRH q₀] at hq₀; linarith
    obtain ⟨b, hb, hmax, L, hL, t, htcofinal, hlimit⟩ :=
      exists_top_negative_normalized_limit_of_not_rh hnot
    have hrb : r < b := lt_of_lt_of_le hq₀ (hmax q₀)
    obtain ⟨C, hC⟩ := h ((r + b) / 2) (by linarith)
    have hdecay : Tendsto (fun n => -(C * Real.exp (-((b - r) / 2) * t n))) atTop (𝓝 0) := by
      have hδ : 0 < (b - r) / 2 := by linarith
      have h1 := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (htcofinal.const_mul_atTop hδ))
      simpa only [Function.comp_def, neg_mul, mul_zero, neg_zero] using
        (h1.const_mul C).neg
    have hlow : ∀ᶠ n in atTop, -(C * Real.exp (-((b - r) / 2) * t n)) ≤
        Real.exp (-b * t n) * liEvenCrossActualClockResponse (t n) := by
      filter_upwards [htcofinal.eventually hC] with n hn
      have hpos : 0 < Real.exp (-b * t n) := Real.exp_pos _
      have h2 := mul_le_mul_of_nonneg_left hn hpos.le
      have h3 : Real.exp (-b * t n) * -(C * Real.exp ((r + b) / 2 * t n)) =
          -(C * Real.exp (-((b - r) / 2) * t n)) := by
        rw [mul_neg, ← mul_assoc, mul_comm (Real.exp _) C, mul_assoc, ← Real.exp_add]
        congr 3; ring
      rw [h3] at h2
      exact h2
    have := le_of_tendsto_of_tendsto hdecay hlimit hlow
    linarith

/-- **RH needs only a subexponential lower bound for the clock response.** -/
theorem riemannHypothesis_iff_liEvenCrossActualClock_subexp_lower :
    RiemannHypothesis ↔
      ∀ r' : ℝ, 0 < r' → ∃ C : ℝ, ∀ᶠ t : ℝ in atTop,
        -(C * Real.exp (r' * t)) ≤ liEvenCrossActualClockResponse t := by
  rw [← growthRate_le_iff_liEvenCrossActualClock_lower le_rfl]
  constructor
  · intro hRH q; exact (growthRate_eq_zero_of_rh hRH q).le
  · intro h
    by_contra hnot
    obtain ⟨b, hb, -, -⟩ := exists_top_negative_normalized_limit_of_not_rh hnot
    obtain ⟨q, hq⟩ := exists_liEvenCrossActualClockReciprocalGrowthRate_pos_of_not_rh hnot
    linarith [h q]

/-- Every frequency is at most `1/431`, because off-line zeros have `γ² ≥ 431/2`. -/
theorem growthRate_le_one_div_431 (q : XiZeroCopy) :
    liEvenCrossActualClockReciprocalGrowthRate q ≤ 1 / 431 := by
  set ρ : ℂ := (q.1 : ℂ) with hρ
  have hz : xi ρ = 0 := xi_eq_zero_of_mem_divisor_support q.1
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  set δ := ρ.re - 1 / 2 with hδ
  set γ := ρ.im with hγ
  have ha : xiSpectralPoint q = (γ : ℂ) - (δ : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [xiSpectralPoint, hρ, hδ, hγ]
  have hden : 0 < γ ^ 2 + δ ^ 2 := by
    have h := xiSpectralPoint_ne_zero q
    rw [ha] at h
    by_contra hle
    push Not at hle
    have hγ0 : γ = 0 := by nlinarith [sq_nonneg γ, sq_nonneg δ]
    have hδ0 : δ = 0 := by nlinarith [sq_nonneg γ, sq_nonneg δ]
    exact h (by rw [hγ0, hδ0]; simp)
  have him : ((xiSpectralPoint q)⁻¹).im = δ / (γ ^ 2 + δ ^ 2) := by
    have hre' : ((γ : ℂ) - (δ : ℂ) * Complex.I).re = γ := by simp
    have him' : ((γ : ℂ) - (δ : ℂ) * Complex.I).im = -δ := by simp
    rw [ha, Complex.inv_im, Complex.normSq_apply, hre', him',
      show γ * γ + -δ * -δ = γ ^ 2 + δ ^ 2 by ring, neg_neg]
  rw [liEvenCrossActualClockReciprocalGrowthRate, him, abs_div, abs_of_pos hden]
  by_cases hoff : ρ.re = 1 / 2
  · have : δ = 0 := by rw [hδ, hoff]; ring
    rw [this, abs_zero, zero_div]; norm_num
  · have hγ2 := im_sq_ge_of_xi_eq_zero_of_re_ne_half hz hoff
    have hδ1 : |δ| ≤ 1 / 2 := abs_le.mpr ⟨by rw [hδ]; linarith [hstrip.1],
      by rw [hδ]; linarith [hstrip.2]⟩
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith [sq_nonneg δ, abs_nonneg δ]

/-- **An unconditional subexponential bound for the clock response at every rate above
`1/431`.** -/
theorem exists_liEvenCrossActualClock_lower_of_431_lt {r' : ℝ} (hr' : 1 / 431 < r') :
    ∃ C : ℝ, ∀ᶠ t : ℝ in atTop,
      -(C * Real.exp (r' * t)) ≤ liEvenCrossActualClockResponse t :=
  (growthRate_le_iff_liEvenCrossActualClock_lower (by norm_num)).mp growthRate_le_one_div_431 r' hr'

end
end RHTower
