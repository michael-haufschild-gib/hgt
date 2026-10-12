import GaloisForLFunctions.RHTower.PrimeLagLandauPowerSaving
import GaloisForLFunctions.RHTower.PrimeLagLowerBoundRH
import GaloisForLFunctions.RHTower.VonMangoldtMinusOneAbscissa

/-!
# The power-saving prime-lag criterion from below

If the lag values `a_p = Φ(log p)` satisfy `a_p ≥ -M p^σ` on the primes `p > X`, with `0 ≤ σ < ½`,
then every zero satisfies `Re ρ ≤ ½ + σ` (`re_le_half_add_of_primeLag_ge_rpow`).  The case `σ = 0`
is `riemannHypothesis_of_primeLag_ge`.

**Proof.**  The lag primitive transfers a lower bound at `log p` to `L ≥ log p` with loss
`e^{L/2}(L − log p) sup |g|`, where `g(s) = (e^s − ψ(e^s))e^{−s}`.  A prime with
`L − 2e^{−2L/5} ≤ log p ≤ L` exists for large `L`.
* With `|g| ≤ log 4 + 4` the loss is `O(e^{L/10})`, so `Φ(L) ≥ −K e^{max(σ, 1/10) L}`, and the lower
  growth criterion gives `Re ρ ≤ ½ + max(σ, 1/10)`.  This settles `σ ≥ 1/10`.
* For `σ < 1/10` the first step gives `Re ρ ≤ 3/5`, hence `|g(s)| ≤ C e^{−7s/20}`; the loss is then
  `O(e^{−L/4})`, so `Φ(L) ≥ −K e^{σL}`.

Together with `re_le_half_add_of_primeLag_le_rpow'`, each one-sided power-saving bound on the prime
lags is exactly a zero-free half-plane.  For the JAS single-prime test at level `σ` this means that
the single test vector `z = 1` (or the single test vector `z = −1`) already gives the half-plane
`Re ρ ≤ ½ + σ` (`xiZeroHalfPlaneBound_of_jasSinglePrime_plus`,
`xiZeroHalfPlaneBound_of_jasSinglePrime_minus`).
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- One transfer step: a lower bound `−M e^{σ log p}` at a prime close below `e^L` gives a lower
bound at `L`, with the loss controlled by `|g| ≤ A` on `[log p, L]`. -/
theorem weilLagFunctionReal_ge_of_prime_near {M σ A L : ℝ} {p : ℕ} (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hp : p.Prime) (h1 : L - 2 * Real.exp (-(2 / 5) * L) ≤ Real.log p) (h2 : Real.log p ≤ L)
    (h3 : L - 1 ≤ Real.log p) (hA : ∀ s ∈ Icc (Real.log p) L, |mertensLagDensity s| ≤ A)
    (hlow : -(M * Real.exp (σ * Real.log p)) ≤ weilLagFunctionReal (Real.log p)) :
    -(2 * M * Real.exp (σ * L) + 2 * A * Real.exp (1 / 10 * L) + 2) ≤ weilLagFunctionReal L := by
  have hT₂ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have htr := weilLagFunctionReal_ge_of_transfer hT₂ h2 hA hlow
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA (Real.log p) ⟨le_rfl, h2⟩)
  have he1 : Real.exp ((L - Real.log p) / 2) ≤ 2 := by
    have : Real.exp ((L - Real.log p) / 2) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith [exp_one_half_le_two_lag]
  have hσp : Real.exp (σ * Real.log p) ≤ Real.exp (σ * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h2 hσ)
  have hM2 : M * Real.exp (σ * Real.log p) * Real.exp ((L - Real.log p) / 2) ≤
      2 * M * Real.exp (σ * L) := by
    have h4 : M * Real.exp (σ * Real.log p) ≤ M * Real.exp (σ * L) :=
      mul_le_mul_of_nonneg_left hσp hM
    have h5 : 0 ≤ M * Real.exp (σ * Real.log p) := by positivity
    calc M * Real.exp (σ * Real.log p) * Real.exp ((L - Real.log p) / 2)
        ≤ M * Real.exp (σ * Real.log p) * 2 := mul_le_mul_of_nonneg_left he1 h5
      _ ≤ 2 * M * Real.exp (σ * L) := by linarith
  have he2 : A * (L - Real.log p) * Real.exp (L / 2) ≤ 2 * A * Real.exp (1 / 10 * L) := by
    have hd : L - Real.log p ≤ 2 * Real.exp (-(2 / 5) * L) := by linarith
    have h4 : (L - Real.log p) * Real.exp (L / 2)
        ≤ 2 * Real.exp (-(2 / 5) * L) * Real.exp (L / 2) :=
      mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
    have h5 : Real.exp (-(2 / 5) * L) * Real.exp (L / 2) = Real.exp (1 / 10 * L) := by
      rw [← Real.exp_add]; ring_nf
    have := mul_le_mul_of_nonneg_left h4 hA0
    nlinarith
  linarith

/-- **The power-saving prime-lag criterion from below.**  If `a_p ≥ −M p^σ` on the primes `p > X`
with `0 ≤ σ < ½`, every zero satisfies `Re ρ ≤ ½ + σ`. -/
theorem re_le_half_add_of_primeLag_ge_rpow {X : ℕ} {M σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2)
    (hM : ∀ p : ℕ, p.Prime → X < p → -(M * Real.exp (σ * Real.log p)) ≤ integerLag p)
    (q : XiZeroCopy) : (q.1 : ℂ).re ≤ 1 / 2 + σ := by
  obtain ⟨M', hM'0, hM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ M ≤ M' := ⟨max M 0, le_max_right _ _, le_max_left _ _⟩
  have hlow : ∀ p : ℕ, p.Prime → ((X + 1 : ℕ) : ℝ) ≤ p →
      -(M' * Real.exp (σ * Real.log p)) ≤ weilLagFunctionReal (Real.log p) := by
    intro p hp hpX
    have hXp : X < p := by exact_mod_cast (show ((X : ℝ) + 1) ≤ p by exact_mod_cast hpX)
    have := hM p hp hXp
    unfold integerLag at this
    have : M * Real.exp (σ * Real.log p) ≤ M' * Real.exp (σ * Real.log p) :=
      mul_le_mul_of_nonneg_right hM' (Real.exp_pos _).le
    linarith
  -- primes just below `e^L`, beyond `X`
  have hnear : ∀ᶠ L : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ ((X + 1 : ℕ) : ℝ) ≤ p ∧
      L - 2 * Real.exp (-(2 / 5) * L) ≤ Real.log p ∧ Real.log p ≤ L ∧ L - 1 ≤ Real.log p := by
    have hsm : ∀ᶠ L : ℝ in atTop, 2 * Real.exp (-(2 / 5) * L) ≤ 1 := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (show -(2 / 5 : ℝ) < 0 by norm_num))).eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by
          norm_num))
      filter_upwards [this] with L hL
      simp only [Function.comp, id] at hL
      linarith
    filter_upwards [eventually_exists_prime_log_near, hsm,
      eventually_ge_atTop (Real.log (max ((X + 1 : ℕ) : ℝ) 1) + 1)] with L ⟨p, hp, h1, h2⟩ hL hLP
    refine ⟨p, hp, ?_, h1, h2, by linarith⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have : Real.log (max ((X + 1 : ℕ) : ℝ) 1) ≤ Real.log p := by linarith
    have h3 : max ((X + 1 : ℕ) : ℝ) 1 ≤ p :=
      (Real.log_le_log_iff (lt_of_lt_of_le one_pos (le_max_right _ _)) hp0).mp this
    exact le_trans (le_max_left _ _) h3
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hnear
  -- Step 1: `Φ(L) ≥ −K e^{max(σ, 1/10) L}`
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Real.log 4 + 4 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; have := Real.log_pos (show (1 : ℝ) < 4 by norm_num); linarith
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = max σ (1 / 10) := ⟨_, rfl⟩
  have haσ : σ ≤ a := hadef ▸ le_max_left _ _
  have ha10 : 1 / 10 ≤ a := hadef ▸ le_max_right _ _
  have ha : a < 1 / 2 := hadef ▸ max_lt hσ (by norm_num)
  have hstep1 : ∀ L, max L₁ 1 ≤ L →
      -((2 * M' + 2 * A + 2) * Real.exp (a * L)) ≤ weilLagFunctionReal L := by
    intro L hL
    obtain ⟨p, hp, hpX, h1, h2, h3⟩ := hL₁ L (le_trans (le_max_left _ _) hL)
    have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
    have hb := weilLagFunctionReal_ge_of_prime_near hM'0 hσ0 hp h1 h2 h3
      (fun s _ => hAdef ▸ abs_mertensLagDensity_le s) (hlow p hp hpX)
    have e1 : Real.exp (σ * L) ≤ Real.exp (a * L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right haσ (by linarith))
    have e2 : Real.exp (1 / 10 * L) ≤ Real.exp (a * L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha10 (by linarith))
    have e3 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (by nlinarith)
    have := mul_le_mul_of_nonneg_left e1 hM'0
    have := mul_le_mul_of_nonneg_left e2 hA0
    nlinarith
  have hre1 := re_le_half_add_of_neg_exp_le_weilLagFunctionReal (by linarith) ha
    (weilLagFunctionReal_lower_of_eventually (by linarith) (by positivity) hstep1)
  rcases le_or_gt (1 / 10) σ with h10 | h10
  · have : a = σ := by rw [hadef]; exact max_eq_left h10
    rw [← this]
    exact hre1 q
  -- Step 2 (`σ < 1/10`): every zero has real part `≤ 3/5`, so the loss decays
  have ha' : a = 1 / 10 := by rw [hadef]; exact max_eq_right h10.le
  have hΘ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 3 / 5 := fun q => by
    have := hre1 q; rw [ha'] at this; linarith
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  have hΘ35 : zeroReSup ≤ 3 / 5 := zeroReSup_le_of_forall_re_le hΘ
  obtain ⟨C, hC0, hC⟩ := exists_abs_mertensLagDensity_le_exp (b := 13 / 20) (by linarith)
  have hdecay : ∀ᶠ L : ℝ in atTop, 2 * C * Real.exp (7 / 20) * Real.exp (-(1 / 4) * L) ≤ 1 := by
    have := ((Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
      (show -(1 / 4 : ℝ) < 0 by norm_num))).const_mul (2 * C * Real.exp (7 / 20))).eventually
        (ge_mem_nhds (show (2 * C * Real.exp (7 / 20)) * 0 < 1 by norm_num))
    filter_upwards [this] with L hL
    simpa [Function.comp] using hL
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.mp hdecay
  have hstep2 : ∀ L, max (max L₁ 1) L₂ ≤ L →
      -((2 * M' + 3) * Real.exp (σ * L)) ≤ weilLagFunctionReal L := by
    intro L hL
    have hLa : max L₁ 1 ≤ L := le_trans (le_max_left _ _) hL
    obtain ⟨p, hp, hpX, h1, h2, h3⟩ := hL₁ L (le_trans (le_max_left _ _) hLa)
    have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLa
    have hT₂ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    obtain ⟨A', hA'⟩ : ∃ A', A' = C * Real.exp ((13 / 20 - 1) * (L - 1)) := ⟨_, rfl⟩
    have hA'b : ∀ s ∈ Icc (Real.log p) L, |mertensLagDensity s| ≤ A' := by
      intro s hs
      have hs0 : 0 ≤ s := le_trans hT₂.le hs.1
      rw [hA']
      refine (hC s hs0).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
      nlinarith [hs.1]
    have htr := weilLagFunctionReal_ge_of_transfer hT₂ h2 hA'b (hlow p hp hpX)
    have hd : L - Real.log p ≤ 2 * Real.exp (-(2 / 5) * L) := by linarith
    have he1 : Real.exp ((L - Real.log p) / 2) ≤ 2 := by
      have : Real.exp ((L - Real.log p) / 2) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith [exp_one_half_le_two_lag]
    have hA'0 : 0 ≤ A' := by rw [hA']; positivity
    have he2 : A' * (L - Real.log p) * Real.exp (L / 2) ≤ 1 := by
      have h4 : (L - Real.log p) * Real.exp (L / 2)
          ≤ 2 * Real.exp (-(2 / 5) * L) * Real.exp (L / 2) :=
        mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
      have h5 : Real.exp ((13 / 20 - 1) * (L - 1)) * (Real.exp (-(2 / 5) * L) * Real.exp (L / 2))
          = Real.exp (7 / 20) * Real.exp (-(1 / 4) * L) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
      have h6 := hL₂ L (le_trans (le_max_right _ _) hL)
      calc A' * (L - Real.log p) * Real.exp (L / 2)
          ≤ A' * (2 * Real.exp (-(2 / 5) * L) * Real.exp (L / 2)) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h4 hA'0
        _ = 2 * C * (Real.exp ((13 / 20 - 1) * (L - 1))
              * (Real.exp (-(2 / 5) * L) * Real.exp (L / 2))) := by rw [hA']; ring
        _ = 2 * C * Real.exp (7 / 20) * Real.exp (-(1 / 4) * L) := by rw [h5]; ring
        _ ≤ 1 := h6
    have hσp : Real.exp (σ * Real.log p) ≤ Real.exp (σ * L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h2 hσ0)
    have hM2 : M' * Real.exp (σ * Real.log p) * Real.exp ((L - Real.log p) / 2) ≤
        2 * M' * Real.exp (σ * L) := by
      have h4 : M' * Real.exp (σ * Real.log p) ≤ M' * Real.exp (σ * L) :=
        mul_le_mul_of_nonneg_left hσp hM'0
      have h5 : 0 ≤ M' * Real.exp (σ * Real.log p) := by positivity
      calc M' * Real.exp (σ * Real.log p) * Real.exp ((L - Real.log p) / 2)
          ≤ M' * Real.exp (σ * Real.log p) * 2 := mul_le_mul_of_nonneg_left he1 h5
        _ ≤ 2 * M' * Real.exp (σ * L) := by linarith
    have e3 : 1 ≤ Real.exp (σ * L) := Real.one_le_exp (by nlinarith)
    nlinarith
  exact re_le_half_add_of_neg_exp_le_weilLagFunctionReal hσ0 hσ
    (weilLagFunctionReal_lower_of_eventually hσ0 (by positivity) hstep2) q

/-! ## The two one-sided JAS single-prime tests -/

/-- **The test vector `z = 1` alone gives the half-plane.**  If the single-prime JAS aggregate is
nonnegative at `z = 1` for every prime `p > X`, at a level `0 ≤ σ < ½`, then `Re ρ ≤ ½ + σ`. -/
theorem xiZeroHalfPlaneBound_of_jasSinglePrime_plus {X : ℕ} {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2)
    (h : ∀ p : Nat.Primes, X < (p : ℕ) →
      0 ≤ (∑' q : XiZeroCopy, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re) :
    XiZeroHalfPlaneBound σ := by
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  refine re_le_half_add_of_primeLag_ge_rpow (X := X) (M := poleSharpConstant) hσ0 hσ
    (fun p hp hpX => ?_) q
  have h1 := h ⟨p, hp⟩ hpX
  rw [re_jasSinglePrimeAggregate] at h1
  simp only [norm_one, one_pow, Complex.one_re] at h1
  have hEE : Real.exp (-σ * Real.log p) * Real.exp (σ * Real.log p) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hE : 0 < Real.exp (σ * Real.log p) := Real.exp_pos _
  unfold integerLag
  have key : 0 ≤ (poleSharpConstant + Real.exp (-σ * Real.log p) *
      weilLagFunctionReal (Real.log p)) * Real.exp (σ * Real.log p) :=
    mul_nonneg (by linarith) hE.le
  have e : (poleSharpConstant + Real.exp (-σ * Real.log p) * weilLagFunctionReal (Real.log p)) *
      Real.exp (σ * Real.log p) = poleSharpConstant * Real.exp (σ * Real.log p) +
        weilLagFunctionReal (Real.log p) := by
    rw [add_mul, mul_comm (Real.exp (-σ * Real.log p)), mul_assoc, hEE, mul_one]
  linarith

/-- **The test vector `z = −1` alone gives the half-plane.**  If the single-prime JAS aggregate is
nonnegative at `z = −1` for every prime `p > X`, at a level `0 ≤ σ < ½`, then `Re ρ ≤ ½ + σ`. -/
theorem xiZeroHalfPlaneBound_of_jasSinglePrime_minus {X : ℕ} {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ < 1 / 2)
    (h : ∀ p : Nat.Primes, X < (p : ℕ) →
      0 ≤ (∑' q : XiZeroCopy, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (-1) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re) :
    XiZeroHalfPlaneBound σ := by
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  refine re_le_half_add_of_primeLag_le_rpow' (X := X) (M := poleSharpConstant) hσ0 hσ
    (fun p hp hpX => ?_) q
  have h1 := h ⟨p, hp⟩ hpX
  rw [re_jasSinglePrimeAggregate] at h1
  simp only [norm_neg, norm_one, one_pow, Complex.neg_re, Complex.one_re] at h1
  have hEE : Real.exp (-σ * Real.log p) * Real.exp (σ * Real.log p) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hE : 0 < Real.exp (σ * Real.log p) := Real.exp_pos _
  have key : 0 ≤ (poleSharpConstant - Real.exp (-σ * Real.log p) *
      weilLagFunctionReal (Real.log p)) * Real.exp (σ * Real.log p) :=
    mul_nonneg (by linarith) hE.le
  have e : (poleSharpConstant - Real.exp (-σ * Real.log p) * weilLagFunctionReal (Real.log p)) *
      Real.exp (σ * Real.log p) = poleSharpConstant * Real.exp (σ * Real.log p) -
        weilLagFunctionReal (Real.log p) := by
    rw [sub_mul, mul_comm (Real.exp (-σ * Real.log p)), mul_assoc, hEE, mul_one]
  unfold integerLag
  linarith

/-- **RH from one test vector.**  RH holds iff, for some `X`, the single-prime JAS aggregate at
level `0` is nonnegative at `z = 1` for every prime `p > X`. -/
theorem riemannHypothesis_iff_exists_jasSinglePrime_plus_zero :
    RiemannHypothesis ↔ ∃ X : ℕ, ∀ p : Nat.Primes, X < (p : ℕ) →
      0 ≤ (∑' q : XiZeroCopy, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + ((0 : ℝ) - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - ((0 : ℝ) - 1 / 2 : ℝ)) p) 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  constructor
  · intro hRH
    obtain ⟨X, hX⟩ := (riemannHypothesis_iff_exists_jasSinglePrimePositiveAbove_zero).mp hRH
    exact ⟨X, fun p hp => hX p hp 1⟩
  · rintro ⟨X, hX⟩
    exact riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr
      (xiZeroHalfPlaneBound_of_jasSinglePrime_plus le_rfl (by norm_num) hX)

end

end RHTower
