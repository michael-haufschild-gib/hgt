import GaloisForLFunctions.RHTower.JointAncestryDiagonalBochnerLevel

/-!
# Signed window means of the prime lags are a zero-free half-plane

With `a_p = Φ(log p)`, the signed mean over the primes of the Huxley window `(x, x + x^θ]`,
`7/12 < θ < 1`, controls `Φ` pointwise up to the coherence error.

**Theorem** (`abs_re_sub_half_le_of_primeWindowMean`).  If
`|Σ_{x < p ≤ x + x^θ} Φ(log p)| ≤ C x^c · #{x < p ≤ x + x^θ}` for all large `x`, then every zero
satisfies `|Re ρ − ½| ≤ max(0, c)`.  The converse is immediate from `|Φ(L)| ≤ C' e^{αL}` under the
half-plane `α`, so power-saving signed window means are exactly zero-free half-planes, and
`O(x^ε)` window means for every `ε > 0` are RH (`riemannHypothesis_iff_forall_primeWindowMean`).

Proof.  Each `p` in the window has `log p ∈ (u, u + x^{θ−1}]` with `u = log x`, so
`|Φ(log p) − Φ(u)| ≤ e^{αu}·O((1 + u) x^{−(1−θ)/2})` by coherence.  Hence
`|Φ(u)| ≤ C e^{cu} + O((1 + u) e^{(α−(1−θ)/2)u})`, and the growth criterion gives
`α ≤ max(c, α − (1−θ)/4)`, i.e. `α ≤ c`.
-/

open Filter

namespace RHTower

noncomputable section

/-- `|Φ(log p) − Φ(u)| ≤ e^{αu}·diagCoherence δ u` for `log p ∈ [u, u + e^{−δu}]`. -/
theorem abs_weilLagFunctionReal_log_sub_le {α δ u L : ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) (hδ0 : 0 < δ) (hu : 0 ≤ u)
    (hL : u ≤ L ∧ L ≤ u + Real.exp (-(δ * u))) :
    |weilLagFunctionReal L - weilLagFunctionReal u| ≤ Real.exp (α * u) * diagCoherence δ u := by
  have hh1 : Real.exp (-(δ * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hT : 1 ≤ Real.exp (δ * u / 2) := Real.one_le_exp (by positivity)
  have := abs_weilLagFunctionReal_add_sub_le hα hu (sub_nonneg.mpr hL.1) (by linarith) hT
    (y := L - u)
  rw [show u + (L - u) = L by ring] at this
  refine this.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  unfold diagCoherence
  have hW := lagWeightTotal_nonneg
  have he := Real.exp_pos (1 / 2 : ℝ)
  gcongr
  linarith

/-- Arithmetic: `C e^{cu} + e^{αu}·(coherence bound) ≤ M e^{au}` with `a = max(c, α − δ/4)`. -/
theorem windowMean_bound_le_exp {α δ c a W C D u : ℝ} (hδ0 : 0 < δ) (hu : 0 ≤ u) (hW : 0 ≤ W)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hca : c ≤ a) (hm : α - δ / 4 ≤ a) :
    C * Real.exp (c * u) + Real.exp (α * u) * (2 * Real.exp (1 / 2) * (3 / 2 * W +
        80 * (D + 2 + u)) * Real.exp (-(δ * u / 2))) ≤
      (C + 2 * Real.exp (1 / 2) * (3 / 2 * W + 80 * (D + 2) + 80 * (4 / δ))) *
        Real.exp (a * u) := by
  have t1 : Real.exp (c * u) ≤ Real.exp (a * u) := Real.exp_le_exp.mpr (by nlinarith)
  have t4 : Real.exp ((α - δ / 4) * u) ≤ Real.exp (a * u) := Real.exp_le_exp.mpr (by nlinarith)
  have e1 : Real.exp (α * u) * Real.exp (-(δ * u / 2)) =
      Real.exp ((α - δ / 4) * u) * Real.exp (-(δ * u / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h5 : Real.exp (δ * u / 4) * Real.exp (-(δ * u / 4)) = 1 := by rw [← Real.exp_add]; simp
  have h7 : Real.exp (-(δ * u / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hlin : u ≤ 4 / δ * Real.exp (δ * u / 4) := by
    have := Real.add_one_le_exp (δ * u / 4)
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
    nlinarith
  have h8 : u * Real.exp (-(δ * u / 4)) ≤ 4 / δ := by
    have := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-(δ * u / 4))).le
    rwa [mul_assoc, h5, mul_one] at this
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (3 / 2 * W + 80 * (D + 2 + u)) * Real.exp (-(δ * u / 4)) := ⟨_, rfl⟩
  have hQb : Q ≤ 3 / 2 * W + 80 * (D + 2) + 80 * (4 / δ) := by
    have h9 : 0 ≤ 3 / 2 * W + 80 * (D + 2) := by positivity
    have := mul_le_mul_of_nonneg_left h7 h9
    rw [hQ]
    nlinarith [Real.exp_pos (-(δ * u / 4))]
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have e2 : Real.exp (α * u) * (2 * Real.exp (1 / 2) * (3 / 2 * W + 80 * (D + 2 + u)) *
      Real.exp (-(δ * u / 2))) = 2 * Real.exp (1 / 2) * Q * Real.exp ((α - δ / 4) * u) := by
    rw [hQ]
    linear_combination (2 * Real.exp (1 / 2) * (3 / 2 * W + 80 * (D + 2 + u))) * e1
  rw [e2]
  have he := Real.exp_pos (1 / 2 : ℝ)
  have k1 : 2 * Real.exp (1 / 2) * Q * Real.exp ((α - δ / 4) * u) ≤
      2 * Real.exp (1 / 2) * (3 / 2 * W + 80 * (D + 2) + 80 * (4 / δ)) * Real.exp (a * u) := by
    gcongr
  have k2 := mul_le_mul_of_nonneg_left t1 hC
  nlinarith

/-- **Signed window means give the half-plane.** -/
theorem abs_re_sub_half_le_of_primeWindowMean {c θ C : ℝ} (hθ : 7 / 12 < θ) (hθ1 : θ < 1)
    (hC : 0 ≤ C)
    (h : ∀ᶠ x : ℝ in atTop, |∑ p ∈ jasIntervalPrimes x (Real.exp (θ * Real.log x)),
      weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))| ≤
        C * Real.exp (c * Real.log x) * (jasIntervalPrimes x (Real.exp (θ * Real.log x))).card)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = zeroReSup - 1 / 2 := ⟨_, rfl⟩
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q', rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := re_le_zeroReSup q'
    rw [hαdef]; linarith
  have hαall : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hαh : α ≤ 1 / 2 := by
    have := zeroReSup_le (fun q : XiZeroCopy => (xiZeroCopy_re_lt_one q).le)
    rw [hαdef]; linarith
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = max 0 c := ⟨_, rfl⟩
  rw [← hc']
  by_cases hbig : 1 / 2 ≤ c'
  · exact (hαall q).trans (by linarith)
  push Not at hbig
  have hc'0 : 0 ≤ c' := hc' ▸ le_max_left _ _
  have hcc' : c ≤ c' := hc' ▸ le_max_right _ _
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 - θ := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδ : δ < 5 / 12 := by rw [hδdef]; linarith
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = max c' (α - δ / 4) := ⟨_, rfl⟩
  have hca : c' ≤ a := hadef ▸ le_max_left _ _
  have hm : α - δ / 4 ≤ a := hadef ▸ le_max_right _ _
  have ha0 : 0 ≤ a := by linarith
  have ha : a < 1 / 2 := by rw [hadef]; exact max_lt hbig (by linarith)
  -- windows exist and are nonempty at large scales
  obtain ⟨X₀, -, hX₀⟩ := exists_theta_window_lower_seven_twelfths
    (α := (7 / 12 + (1 - δ)) / 2) (by linarith) (by linarith)
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp ((eventually_diagWindow_conditions 0 (σ := 0) (δ := δ)
    (c := 1 / 2) (α' := (7 / 12 + (1 - δ)) / 2) (X₀ := X₀) (by linarith) (by linarith)
    (by norm_num)).and (Real.tendsto_exp_atTop.eventually h))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C + 2 * Real.exp (1 / 2) * (3 / 2 * lagWeightTotal +
      80 * (|xiLineTwoLogDerivConstant| + 2) + 80 * (4 / δ)) := ⟨_, rfl⟩
  have hW := lagWeightTotal_nonneg
  have hM : ∀ L, 0 ≤ L → |weilLagFunctionReal L| ≤
      max K (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L) := by
    intro L hL
    rcases le_or_gt u₀ L with hLu | hLu
    · obtain ⟨⟨hE1, hE1', hE2, hE3, -, hu1⟩, hmean⟩ := hu₀ L hLu
      obtain ⟨P, hPdef, hlogP, hMass⟩ := exists_window (X := 0) (σ := 0) (c := 1 / 2) le_rfl hδ0
        (by linarith) (by linarith) hX₀ hu1 hE1 hE1' hE2 hE3
      have hθL : Real.exp (θ * Real.log (Real.exp L)) = Real.exp ((1 - δ) * L) := by
        rw [Real.log_exp, hδdef]; ring_nf
      rw [hθL, ← hPdef, Real.log_exp] at hmean
      have hcard : (0 : ℝ) < P.card := by
        have h1 : ∑ p ∈ P, Real.exp (-0 * Real.log ((p : ℕ) : ℝ)) = P.card := by simp
        rw [h1] at hMass
        exact lt_of_lt_of_le (Real.exp_pos _) hMass
      have hcoh : ∀ p ∈ P, |weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) - weilLagFunctionReal L| ≤
          Real.exp (α * L) * diagCoherence δ L := fun p hp =>
        abs_weilLagFunctionReal_log_sub_le hαall hδ0 hL (hlogP p hp)
      have hsplit : (P.card : ℝ) * |weilLagFunctionReal L| ≤
          |∑ p ∈ P, weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))| +
            P.card * (Real.exp (α * L) * diagCoherence δ L) := by
        have e : (P.card : ℝ) * weilLagFunctionReal L =
            ∑ p ∈ P, weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) -
              ∑ p ∈ P, (weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) - weilLagFunctionReal L) := by
          rw [Finset.sum_sub_distrib]; simp
        rw [← abs_of_pos hcard, ← abs_mul, e]
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [abs_of_pos hcard]
        have := Finset.sum_le_sum hcoh
        simpa [Finset.sum_const, nsmul_eq_mul] using this
      have hΦL : |weilLagFunctionReal L| ≤ C * Real.exp (c * L) +
          Real.exp (α * L) * diagCoherence δ L := by
        have h1 : (P.card : ℝ) * |weilLagFunctionReal L| ≤ P.card * (C * Real.exp (c * L) +
            Real.exp (α * L) * diagCoherence δ L) := by
          refine hsplit.trans ?_
          linarith [hmean]
        exact le_of_mul_le_mul_left h1 hcard
      have hcohb := diagCoherence_le hδ0 (by linarith) hL
      have hcc : C * Real.exp (c * L) ≤ C * Real.exp (c' * L) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
      have hw := windowMean_bound_le_exp (α := α) (c := c') (W := lagWeightTotal) (C := C)
        (D := |xiLineTwoLogDerivConstant|) (u := L) hδ0 hL hW hC (abs_nonneg _) hca hm
      rw [← hK] at hw
      have hfin := hΦL.trans (add_le_add hcc (mul_le_mul_of_nonneg_left hcohb (Real.exp_pos _).le))
      exact (hfin.trans hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · have h1 := abs_weilLagFunctionReal_le L
      rw [abs_of_nonneg hL] at h1
      have h2 : Real.exp (L / 2) ≤ Real.exp (|u₀| / 2) :=
        Real.exp_le_exp.mpr (by linarith [le_abs_self u₀])
      have h3 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
      have h4 : |weilLagFunctionReal L| ≤ Real.exp (|u₀| / 2) * lagWeightTotal :=
        h1.trans (mul_le_mul_of_nonneg_right h2 hW)
      have h5 : 0 ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) :=
        le_trans (by positivity) (le_max_right _ _)
      calc |weilLagFunctionReal L| ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) :=
            h4.trans (le_max_right _ _)
        _ ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L) :=
            le_mul_of_one_le_right h5 h3
  have hg : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + a := fun q =>
    re_le_half_add_of_weilLagFunctionReal_le_exp ha0 ha
      (fun L hL => (le_abs_self _).trans (hM L hL)) q
  have hsup := zeroReSup_le hg
  have hΘ : zeroReSup = α + 1 / 2 := by rw [hαdef]; ring
  have hle : α ≤ a := by linarith
  have hαc : α ≤ c' := by
    by_contra hlt
    push Not at hlt
    rcases le_total c' (α - δ / 4) with h1 | h1
    · rw [hadef, max_eq_right h1] at hle; linarith
    · rw [hadef, max_eq_left h1] at hle; linarith
  exact (hαall q).trans hαc

/-! ## The converse and the capstones -/

/-- **Half-planes bound the window means.**  Under `Re ρ ≤ ½ + α` (`α ≥ 0`), for every `x ≥ 1` and
`θ ≤ 1`, `|Σ_{x<p≤x+x^θ} Φ(log p)| ≤ 2^α M x^α · #(window)`, with `M = Σ|w_ρ|`-type mass. -/
theorem abs_sum_primeWindow_le_of_xiZeroHalfPlaneBound {α θ : ℝ} (hXi : XiZeroHalfPlaneBound α)
    (hα : 0 ≤ α) (hθ1 : θ ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ jasIntervalPrimes x (Real.exp (θ * Real.log x)),
      weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))| ≤
        (Real.exp (α * Real.log 2) * jasLagAbsMass) * Real.exp (α * Real.log x) *
          (jasIntervalPrimes x (Real.exp (θ * Real.log x))).card := by
  have hx0 : 0 < x := by linarith
  have hwin : Real.exp (θ * Real.log x) ≤ x := by
    calc Real.exp (θ * Real.log x) ≤ Real.exp (Real.log x) :=
          Real.exp_le_exp.mpr (by nlinarith [Real.log_nonneg hx])
      _ = x := Real.exp_log hx0
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ p ∈ jasIntervalPrimes x (Real.exp (θ * Real.log x)),
      |weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))| ≤
        (Real.exp (α * Real.log 2) * jasLagAbsMass) * Real.exp (α * Real.log x) := by
    intro p hp
    have hp' : (p : ℕ) ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + Real.exp (θ * Real.log x)⌋₊).filter Nat.Prime :=
      Finset.mem_subtype.mp hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp'
    have hp1 : x < ((p : ℕ) : ℝ) := (Nat.floor_lt hx0.le).mp hp'.1.1
    have hp2 : ((p : ℕ) : ℝ) ≤ 2 * x := le_trans (by exact_mod_cast hp'.1.2)
      ((Nat.floor_le (by positivity)).trans (by linarith))
    have hlogp0 : 0 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_nonneg (by linarith)
    have hb := abs_weilLagFunctionReal_le_of_xiZeroHalfPlaneBound hXi hlogp0
    have hlog2 : Real.log ((p : ℕ) : ℝ) ≤ Real.log 2 + Real.log x := by
      rw [← Real.log_mul (by norm_num) hx0.ne']; exact Real.log_le_log (by linarith) hp2
    have hM0 : 0 ≤ jasLagAbsMass :=
      le_trans (abs_nonneg _) (abs_weilLagFunctionReal_le_of_xiZeroHalfPlaneBound hXi le_rfl |>.trans
        (by simp))
    calc |weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))|
        ≤ Real.exp (α * Real.log ((p : ℕ) : ℝ)) * jasLagAbsMass := hb
      _ ≤ Real.exp (α * (Real.log 2 + Real.log x)) * jasLagAbsMass :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) hM0
      _ = (Real.exp (α * Real.log 2) * jasLagAbsMass) * Real.exp (α * Real.log x) := by
          rw [mul_add, Real.exp_add]; ring
  have := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at this
  linarith

/-- **RH ⟺ subpower signed window means.**  For `7/12 < θ < 1`: RH holds iff for every `ε > 0` the
signed means of `Φ(log p)` over the Huxley windows `(x, x + x^θ]` are `O(x^ε)`. -/
theorem riemannHypothesis_iff_forall_primeWindowMean {θ : ℝ} (hθ : 7 / 12 < θ) (hθ1 : θ < 1) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |∑ p ∈ jasIntervalPrimes x (Real.exp (θ * Real.log x)),
        weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))| ≤
        C * Real.exp (ε * Real.log x) * (jasIntervalPrimes x (Real.exp (θ * Real.log x))).card := by
  constructor
  · intro hRH ε hε
    have hXi : XiZeroHalfPlaneBound 0 := riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mp hRH
    have hM0 : 0 ≤ jasLagAbsMass :=
      le_trans (abs_nonneg _) (abs_weilLagFunctionReal_le_of_xiZeroHalfPlaneBound hXi le_rfl |>.trans
        (by simp))
    refine ⟨jasLagAbsMass, hM0, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have h := abs_sum_primeWindow_le_of_xiZeroHalfPlaneBound (θ := θ) hXi le_rfl hθ1.le hx
    simp only [zero_mul, Real.exp_zero, one_mul] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    have : 1 ≤ Real.exp (ε * Real.log x) := Real.one_le_exp (mul_nonneg hε.le (Real.log_nonneg hx))
    nlinarith
  · intro h
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, hC, hev⟩ := h ε hε
    have := abs_re_sub_half_le_of_primeWindowMean hθ hθ1 hC hev q
    rw [max_eq_right hε.le] at this
    linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- **Quasi-RH ⟺ power-saving signed window means.** -/
theorem exists_halfPlane_lt_half_iff_exists_primeWindowMean {θ : ℝ} (hθ : 7 / 12 < θ)
    (hθ1 : θ < 1) :
    (∃ α : ℝ, α < 1 / 2 ∧ XiZeroHalfPlaneBound α) ↔ ∃ c : ℝ, c < 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x : ℝ in atTop, |∑ p ∈ jasIntervalPrimes x (Real.exp (θ * Real.log x)),
        weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))| ≤
        C * Real.exp (c * Real.log x) * (jasIntervalPrimes x (Real.exp (θ * Real.log x))).card := by
  constructor
  · rintro ⟨α, hα, hXi⟩
    obtain ⟨α', hα'def⟩ : ∃ α' : ℝ, α' = max α 0 := ⟨_, rfl⟩
    have hXi' : XiZeroHalfPlaneBound α' := fun ρ hρ => by
      have := hXi ρ hρ; rw [hα'def]; linarith [le_max_left α 0]
    have hα'0 : 0 ≤ α' := hα'def ▸ le_max_right _ _
    have hM0 : 0 ≤ jasLagAbsMass :=
      le_trans (abs_nonneg _) (abs_weilLagFunctionReal_le_of_xiZeroHalfPlaneBound hXi' le_rfl |>.trans
        (by simp))
    refine ⟨α', by rw [hα'def]; exact max_lt hα (by norm_num),
      Real.exp (α' * Real.log 2) * jasLagAbsMass, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact abs_sum_primeWindow_le_of_xiZeroHalfPlaneBound hXi' hα'0 hθ1.le hx
  · rintro ⟨c, hc, C, hC, hev⟩
    refine ⟨max 0 c, max_lt (by norm_num) hc, fun ρ hρ => ?_⟩
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := abs_re_sub_half_le_of_primeWindowMean hθ hθ1 hC hev q
    linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

end

end RHTower
