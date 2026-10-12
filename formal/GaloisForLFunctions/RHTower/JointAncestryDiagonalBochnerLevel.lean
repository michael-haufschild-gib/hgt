import GaloisForLFunctions.RHTower.JointAncestryDiagonalBochner
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSevenTwelfths
import GaloisForLFunctions.RHTower.JointAncestryZeroTailBound

/-!
# Product positivity at level `σ` forces the half-plane `|Re ρ − ½| ≤ max(0, σ − 1)`

**Theorem** (`abs_re_sub_half_le_of_jasIntervalProductPositive`).  If the JAS product tests with a
constant vector `z` are positive on the primes of every interval `(y, y + L]`, `y ≥ X + 1`, at a
level `σ ≥ 0`, then every zero satisfies `|Re ρ − ½| ≤ max(0, σ − 1)`.  In particular
`RH ⟺ ∃X, JasIntervalProductPositive X 1` (`riemannHypothesis_iff_exists_jasIntervalProductPositive_one`)
and `RH ⟺ ∃X, JasProductPositiveAbove X 1` (`riemannHypothesis_iff_exists_jasProductPositiveAbove_one`).

**Proof.**  Let `α = sup |Re ρ − ½|`.  For large `u` take the primes in the Huxley window
`(e^u, e^u + e^{(1−δ)u}]` and weights with total `≍ e^{−cu}`, `c > max(0, σ − 1 + δ)`.
* The diagonal Bochner bound (`abs_sum_weilLagFunctionReal_le_of_jasProductPositiveAbove`) bounds
  the weighted window average of `Φ(log p)` by `Φ(0) + O(e^{−2cu}(1 + e^{αu}))`.
* The coherence estimate (`abs_weilLagFunctionReal_add_sub_le`, from the weight tail of the zeros)
  replaces `Φ(log p)` by `Φ(u)` at cost `O(u e^{(α − δ/2)u})`.

So `|Φ(u)| = O(e^{cu} + e^{(α−c)u} + u e^{(α−δ/2)u})`.  The growth criterion then gives
`α ≤ max(c, α − min(c, δ/4))`, i.e. `α ≤ c`.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-! ## Coherence of the lag function on short windows -/

theorem norm_cexp_sub_one_le_min {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    ‖Complex.exp z - 1‖ ≤ 2 * Real.exp (1 / 2) * min 1 ‖z‖ := by
  have he : 1 ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)
  rcases le_or_gt ‖z‖ 1 with h | h
  · rw [min_eq_right h]
    have := Complex.norm_exp_sub_one_le h
    nlinarith [norm_nonneg z]
  · rw [min_eq_left h.le, mul_one]
    calc ‖Complex.exp z - 1‖ ≤ ‖Complex.exp z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = Real.exp z.re + 1 := by rw [Complex.norm_exp, norm_one]
      _ ≤ Real.exp (1 / 2) + Real.exp (1 / 2) := by
          gcongr
          · exact (le_abs_self _).trans hz
      _ = 2 * Real.exp (1 / 2) := by ring

/-- **Coherence.**  For `0 ≤ y ≤ 1` and `T ≥ 1`,
`|Φ(u + y) − Φ(u)| ≤ e^{αu} · 2e^{½}((½ + T) y W + 80(C + log(3T + 4))/T)`. -/
theorem abs_weilLagFunctionReal_add_sub_le {α : ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) {u y T : ℝ} (hu : 0 ≤ u) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hT : 1 ≤ T) :
    |weilLagFunctionReal (u + y) - weilLagFunctionReal u| ≤
      Real.exp (α * u) * (2 * Real.exp (1 / 2) * ((1 / 2 + T) * y * lagWeightTotal +
        80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T)) := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, ← weilLagFunction_eq_ofReal,
    ← weilLagFunction_eq_ofReal]
  unfold weilLagFunction
  rw [← (summable_weilLagTerm (u + y)).tsum_sub (summable_weilLagTerm u)]
  -- the terms
  obtain ⟨g, hgdef⟩ : ∃ g : XiZeroCopy → ℝ, g = fun q =>
      2 * Real.exp (1 / 2) * ((1 / 2 + T) * y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ +
        {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
          (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q) := ⟨_, rfl⟩
  have hterm : ∀ q : XiZeroCopy,
      ‖Complex.exp (((u + y : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) -
        Complex.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
        Real.exp (α * u) * g q := by
    intro q
    have hab := hα q
    have hb : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
    have e : Complex.exp (((u + y : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) -
        Complex.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
        Complex.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)) *
          (Complex.exp ((y : ℂ) * ((q.1 : ℂ) - 1 / 2)) - 1) *
            (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
      rw [← sub_div, show ((u + y : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2) =
        (u : ℂ) * ((q.1 : ℂ) - 1 / 2) + (y : ℂ) * ((q.1 : ℂ) - 1 / 2) by push_cast; ring,
        Complex.exp_add]
      ring
    rw [e, norm_mul, norm_mul, Complex.norm_exp]
    have hre1 : ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = u * ((q.1 : ℂ).re - 1 / 2) := by
      simp [Complex.mul_re]
    have hre2 : ((y : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = y * ((q.1 : ℂ).re - 1 / 2) := by
      simp [Complex.mul_re]
    have h1 : Real.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)).re ≤ Real.exp (α * u) := by
      rw [hre1]
      apply Real.exp_le_exp.mpr
      have := abs_le.mp hab
      nlinarith
    have hz : |((y : ℂ) * ((q.1 : ℂ) - 1 / 2)).re| ≤ 1 / 2 := by
      rw [hre2, abs_mul, abs_of_nonneg hy0]
      nlinarith [abs_nonneg ((q.1 : ℂ).re - 1 / 2)]
    have h2 := norm_cexp_sub_one_le_min hz
    have hw := norm_nonneg (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))
    have hmin : min 1 ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
        (1 / 2 + T) * y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ +
          {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
            (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q := by
      by_cases hq : T < |(q.1 : ℂ).im|
      · rw [Set.indicator_of_mem (show q ∈ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from hq)]
        have : min 1 ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖ ≤ 1 := min_le_left _ _
        have h0 : 0 ≤ (1 / 2 + T) * y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by positivity
        nlinarith
      · rw [Set.indicator_of_notMem (show q ∉ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from hq),
          add_zero]
        push Not at hq
        have hnz : ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖ ≤ (1 / 2 + T) * y := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]
          have hn := Complex.norm_le_abs_re_add_abs_im ((q.1 : ℂ) - 1 / 2)
          simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
            Complex.div_ofNat_re, Complex.div_ofNat_im, zero_div, sub_zero] at hn
          nlinarith [abs_nonneg ((q.1 : ℂ).im)]
        have := (min_le_right 1 ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖).trans hnz
        exact mul_le_mul_of_nonneg_right this hw
    rw [hgdef]
    calc Real.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)).re *
          ‖Complex.exp ((y : ℂ) * ((q.1 : ℂ) - 1 / 2)) - 1‖ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
        ≤ Real.exp (α * u) * (2 * Real.exp (1 / 2) * min 1 ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖) *
            ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by gcongr
      _ = Real.exp (α * u) * (2 * Real.exp (1 / 2) *
            (min 1 ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)) := by ring
      _ ≤ _ := by beta_reduce; gcongr
  have hgs : Summable g := by
    rw [hgdef]
    exact ((summable_inv_mul_one_sub.norm.mul_left _).add
      (summable_inv_mul_one_sub.norm.indicator _)).mul_left _
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_norm_bounded (hgs.mul_left _) fun q => by
      rw [norm_norm]; exact hterm q
  refine (Summable.tsum_le_tsum hterm ?_ (hgs.mul_left _)).trans ?_
  · exact Summable.of_norm_bounded (hgs.mul_left _) fun q => by
      rw [norm_norm]; exact hterm q
  rw [tsum_mul_left, hgdef, tsum_mul_left, (summable_inv_mul_one_sub.norm.mul_left _).tsum_add
    (summable_inv_mul_one_sub.norm.indicator _), tsum_mul_left]
  have htail := tsum_indicator_abs_im_gt_weight_le hT
  have hW : ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ = lagWeightTotal := rfl
  rw [hW]
  have hexp := Real.exp_pos (α * u)
  have he2 := Real.exp_pos (1 / 2 : ℝ)
  gcongr

/-! ## The window -/

/-- `∏(1 + x_i) − 1 − Σ x_i ≤ (Σ x_i)²` for `x_i ≥ 0` with `Σ x_i ≤ 1`. -/
theorem prod_one_add_sub_le_sq {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (h1 : ∑ i ∈ s, x i ≤ 1) :
    (∏ i ∈ s, (1 + x i)) - 1 - ∑ i ∈ s, x i ≤ (∑ i ∈ s, x i) ^ 2 := by
  have hp : ∏ i ∈ s, (1 + x i) ≤ Real.exp (∑ i ∈ s, x i) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun i hi => by linarith [hx i hi]) fun i _ => by
      linarith [Real.add_one_le_exp (x i)]
  have h0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx
  have he := Real.abs_exp_sub_one_sub_id_le (x := ∑ i ∈ s, x i) (by rw [abs_of_nonneg h0]; exact h1)
  linarith [le_abs_self (Real.exp (∑ i ∈ s, x i) - 1 - ∑ i ∈ s, x i)]

/-- The coherence constant at scale `u`: `2e^{½}((½ + e^{δu/2}) e^{−δu} W + 80(C + log(3e^{δu/2} + 4)) e^{−δu/2})`. -/
def diagCoherence (δ u : ℝ) : ℝ :=
  2 * Real.exp (1 / 2) * ((1 / 2 + Real.exp (δ * u / 2)) * Real.exp (-(δ * u)) * lagWeightTotal +
    80 * (xiLineTwoLogDerivConstant + Real.log (3 * Real.exp (δ * u / 2) + 4)) /
      Real.exp (δ * u / 2))

/-- The primes in the interval `(y, y + L]`. -/
def jasIntervalPrimes (y L : ℝ) : Finset Nat.Primes :=
  ((Finset.Ioc ⌊y⌋₊ ⌊y + L⌋₊).filter Nat.Prime).subtype Nat.Prime

/-- **Interval product positivity.**  The product tests with a constant vector `z` are positive on
the primes of every interval `(y, y + L]` with `y ≥ X + 1`. -/
def JasIntervalProductPositive (X : ℕ) (σ : ℝ) : Prop :=
  ∀ y L : ℝ, (X : ℝ) + 1 ≤ y → 0 ≤ L → JasConstProductPositiveOn (jasIntervalPrimes y L) σ

theorem JasProductPositiveAbove.intervalPositive {X : ℕ} {σ : ℝ} (h : JasProductPositiveAbove X σ) :
    JasIntervalProductPositive X σ := by
  intro y L hy _
  refine h.constOn fun p hp => ?_
  have hp' : (p : ℕ) ∈ (Finset.Ioc ⌊y⌋₊ ⌊y + L⌋₊).filter Nat.Prime := Finset.mem_subtype.mp hp
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp'
  have h1 : y < ((p : ℕ) : ℝ) := (Nat.floor_lt (by linarith [Nat.cast_nonneg (α := ℝ) X])).mp hp'.1.1
  have : (X : ℝ) < ((p : ℕ) : ℝ) := by linarith
  exact_mod_cast this

/-- **A Huxley window with weight.**  Under explicit largeness conditions on `u` there is a set of
primes `p > X` with `log p ∈ [u, u + e^{−δu}]` and `Σ p^{−σ} ≥ e^{−cu}`. -/
theorem exists_window {X : ℕ} {σ δ c α' X₀ u : ℝ} (hσ : 0 ≤ σ) (hδ0 : 0 < δ) (hα'0 : 0 ≤ α')
    (hα'1 : α' ≤ 1)
    (hX₀ : ∀ y L : ℝ, X₀ ≤ y → 0 ≤ L →
      (L - (y + L) ^ α') / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y)
    (hu1 : 1 ≤ u) (hE1 : X₀ ≤ Real.exp u) (hE1' : (X : ℝ) + 1 ≤ Real.exp u)
    (hE2 : 2 * Real.exp (α' * u) ≤ Real.exp ((1 - δ) * u) / 2)
    (hE3 : 4 * Real.exp σ * (u + 1) * Real.exp (-(c * u)) ≤ Real.exp ((1 - δ - σ) * u)) :
    ∃ P : Finset Nat.Primes, P = jasIntervalPrimes (Real.exp u) (Real.exp ((1 - δ) * u)) ∧
      (∀ p ∈ P, u ≤ Real.log ((p : ℕ) : ℝ) ∧ Real.log ((p : ℕ) : ℝ) ≤ u + Real.exp (-(δ * u))) ∧
      Real.exp (-(c * u)) ≤ ∑ p ∈ P, Real.exp (-σ * Real.log ((p : ℕ) : ℝ)) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.exp u := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.exp ((1 - δ) * u) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = Real.exp (-(δ * u)) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by linarith
  have hy0 : 0 < y := by rw [hy]; exact Real.exp_pos _
  have hL0 : 0 < L := by rw [hL]; exact Real.exp_pos _
  have hLy : L = y * h := by rw [hL, hy, hh, ← Real.exp_add]; ring_nf
  have hh0 : 0 < h := by rw [hh]; exact Real.exp_pos _
  have hh1 : h ≤ 1 := by rw [hh]; exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hLley : L ≤ y := by rw [hLy]; nlinarith
  obtain ⟨Pn, hPn⟩ : ∃ Pn : Finset ℕ, Pn = (Finset.Ioc ⌊y⌋₊ ⌊y + L⌋₊).filter Nat.Prime := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Finset Nat.Primes, P = Pn.subtype Nat.Prime := ⟨_, rfl⟩
  have hmemP : ∀ p ∈ P, y < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ y + L := by
    intro p hp
    rw [hPdef] at hp
    have hp' : (p : ℕ) ∈ Pn := Finset.mem_subtype.mp hp
    rw [hPn, Finset.mem_filter, Finset.mem_Ioc] at hp'
    have hp := hp'
    exact ⟨(Nat.floor_lt hy0.le).mp hp.1.1,
      le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le (by linarith))⟩
  have hlogP : ∀ p ∈ P, u ≤ Real.log ((p : ℕ) : ℝ) ∧ Real.log ((p : ℕ) : ℝ) ≤ u + h := by
    intro p hp
    obtain ⟨h1, h2⟩ := hmemP p hp
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    constructor
    · rw [show u = Real.log y by rw [hy, Real.log_exp]]
      exact Real.log_le_log hy0 h1.le
    · have : Real.log ((p : ℕ) : ℝ) ≤ Real.log (y + L) := Real.log_le_log hp0 h2
      have e : Real.log (y + L) = u + Real.log (1 + h) := by
        rw [show y + L = y * (1 + h) by rw [hLy]; ring, Real.log_mul hy0.ne' (by linarith), hy,
          Real.log_exp]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + h by linarith)
      linarith
  have hXP : ∀ p ∈ P, X < (p : ℕ) := by
    intro p hp
    have := (hmemP p hp).1
    have : (X : ℝ) < ((p : ℕ) : ℝ) := by rw [hy] at this; linarith
    exact_mod_cast this
  -- the window mass
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∑ p ∈ P, Real.exp (-σ * Real.log ((p : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hMass : Real.exp (-(c * u)) ≤ M := by
    have hθ := hX₀ y L (by rw [hy]; exact hE1) hL0.le
    rw [Sieve.theta_sub_eq_sum_Ioc (by linarith), ← hPn] at hθ
    have hpow : (y + L) ^ α' ≤ 2 * Real.exp (α' * u) := by
      calc (y + L) ^ α' ≤ (2 * y) ^ α' := Real.rpow_le_rpow (by linarith) (by linarith) hα'0
        _ = 2 ^ α' * y ^ α' := Real.mul_rpow (by norm_num) hy0.le
        _ ≤ 2 * Real.exp (α' * u) := by
            have h2 : (2 : ℝ) ^ α' ≤ 2 := by
              calc (2 : ℝ) ^ α' ≤ 2 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hα'1
                _ = 2 := Real.rpow_one 2
            have h3 : y ^ α' = Real.exp (α' * u) := by
              rw [Real.rpow_def_of_pos hy0, hy, Real.log_exp, mul_comm]
            rw [h3]
            exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    have hθL : L / 4 ≤ ∑ n ∈ Pn, Real.log n := by rw [← hL] at hE2; linarith
    have hlogn : ∀ n ∈ Pn, Real.log n ≤ u + 1 := by
      intro n hn
      rw [hPn, Finset.mem_filter, Finset.mem_Ioc] at hn
      have hn1 : (n : ℝ) ≤ y + L := le_trans (by exact_mod_cast hn.1.2) (Nat.floor_le (by linarith))
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.2.pos
      have h1 : Real.log n ≤ Real.log (2 * y) := Real.log_le_log hn0 (by linarith)
      rw [Real.log_mul (by norm_num) hy0.ne', hy, Real.log_exp] at h1
      linarith [Real.log_two_lt_d9]
    have hcard : L / 4 ≤ Pn.card * (u + 1) := by
      refine hθL.trans ?_
      have := Finset.sum_le_sum hlogn
      simp only [Finset.sum_const, nsmul_eq_mul] at this
      linarith
    have hMeq : M = ∑ n ∈ Pn, Real.exp (-σ * Real.log n) := by
      rw [hMdef, hPdef]
      change (∑ p ∈ Finset.subtype Nat.Prime Pn,
        (fun n : ℕ => Real.exp (-σ * Real.log n)) (p : ℕ)) = _
      rw [Finset.sum_subtype_eq_sum_filter (fun n : ℕ => Real.exp (-σ * Real.log n))]
      congr 1
      rw [hPn, Finset.filter_filter]
      simp
    have hMlow : Pn.card * Real.exp (-σ * (u + 1)) ≤ M := by
      rw [hMeq]
      have := Finset.sum_le_sum fun n (hn : n ∈ Pn) =>
        (Real.exp_le_exp.mpr (show -σ * (u + 1) ≤ -σ * Real.log n by nlinarith [hlogn n hn]))
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    have hE3' : Real.exp (-(c * u)) * (4 * (u + 1)) ≤ L * Real.exp (-σ * (u + 1)) := by
      have e : L * Real.exp (-σ * (u + 1)) = Real.exp ((1 - δ - σ) * u) / Real.exp σ := by
        rw [hL, ← Real.exp_add, ← Real.exp_sub]; ring_nf
      rw [e, le_div_iff₀ (Real.exp_pos _)]
      linarith
    have hcard' : L * Real.exp (-σ * (u + 1)) ≤ 4 * (u + 1) * M := by
      have hep := Real.exp_pos (-σ * (u + 1))
      nlinarith
    have hu2 : (0 : ℝ) < 4 * (u + 1) := by linarith
    nlinarith
  refine ⟨P, by rw [hPdef, hPn, hy, hL]; rfl, fun p hp => ?_, by rw [← hMdef]; exact hMass⟩
  rw [← hh]; exact hlogP p hp

/-- **The window bound at one scale.**  Given a set of primes `p > X` with
`log p ∈ [u, u + e^{−δu}]` and `Σ p^{−σ} ≥ e^{−cu}`, positivity of the product tests at level `σ`
gives `|Φ(u)| ≤ 2Φ(0)e^{cu} + 32W(e^{−cu} + e^{(α−c)u}) + e^{αu}·diagCoherence δ u`. -/
theorem abs_weilLagFunctionReal_le_of_window {σ : ℝ}
    {α δ c u : ℝ} (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α)
    (hδ0 : 0 < δ) (hu1 : 1 ≤ u) (hE4 : 4 * Real.exp (-(c * u)) ≤ 1)
    (P : Finset Nat.Primes) (hpos : JasConstProductPositiveOn P σ)
    (hlogP' : ∀ p ∈ P, u ≤ Real.log ((p : ℕ) : ℝ) ∧ Real.log ((p : ℕ) : ℝ) ≤ u + Real.exp (-(δ * u)))
    (hMass : Real.exp (-(c * u)) ≤ ∑ p ∈ P, Real.exp (-σ * Real.log ((p : ℕ) : ℝ))) :
    |weilLagFunctionReal u| ≤ 2 * poleSharpConstant * Real.exp (c * u) +
      32 * lagWeightTotal * (Real.exp (-(c * u)) + Real.exp ((α - c) * u)) +
        Real.exp (α * u) * diagCoherence δ u := by
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = Real.exp (-(δ * u)) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by linarith
  have hh0 : 0 < h := by rw [hh]; exact Real.exp_pos _
  have hh1 : h ≤ 1 := by rw [hh]; exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hlogP : ∀ p ∈ P, u ≤ Real.log ((p : ℕ) : ℝ) ∧ Real.log ((p : ℕ) : ℝ) ≤ u + h := by
    rw [hh]; exact hlogP'
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∑ p ∈ P, Real.exp (-σ * Real.log ((p : ℕ) : ℝ)) := ⟨_, rfl⟩
  rw [← hMdef] at hMass
  have hM0 : 0 < M := lt_of_lt_of_le (Real.exp_pos _) hMass
  -- the weights
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.exp (-(c * u)) / M := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; exact div_pos (Real.exp_pos _) hM0
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hM0]; exact hMass
  have hS : ∑ p ∈ P, diagA σ r p = r / (1 + r ^ 2) * M := by
    rw [hMdef, Finset.mul_sum]; rfl
  have hrM : r * M = Real.exp (-(c * u)) := by rw [hrdef]; field_simp
  have hSlow : Real.exp (-(c * u)) / 2 ≤ ∑ p ∈ P, diagA σ r p := by
    rw [hS, ← hrM]
    have h1 : 1 + r ^ 2 ≤ 2 := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hSup : ∑ p ∈ P, diagA σ r p ≤ Real.exp (-(c * u)) := by
    rw [hS, ← hrM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hr0.le hM0.le) (sq_nonneg r)]
  -- the Bochner bound
  have hstar := abs_sum_weilLagFunctionReal_le_of_constPositive hα hu0 hr0.le P hpos hlogP
  have hK : ∑ p ∈ P, 2 * (diagA σ r p * Real.exp (h / 2)) ≤ 4 * Real.exp (-(c * u)) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have he : Real.exp (h / 2) ≤ 2 :=
      (Real.exp_le_exp.mpr (by linarith)).trans exp_one_half_le_two_lag
    have hS0 : 0 ≤ ∑ p ∈ P, diagA σ r p := Finset.sum_nonneg fun p _ => diagA_nonneg hr0.le p
    have := mul_le_mul hSup he (Real.exp_pos _).le (Real.exp_pos _).le
    linarith
  obtain ⟨x, hxdef⟩ : ∃ x : Nat.Primes → ℝ, x = fun p => 2 * (diagA σ r p * Real.exp (h / 2)) :=
    ⟨_, rfl⟩
  have hx0 : ∀ p ∈ P, 0 ≤ x p := fun p _ => by
    rw [hxdef]; exact mul_nonneg (by norm_num) (mul_nonneg (diagA_nonneg hr0.le p) (Real.exp_pos _).le)
  have hxs : ∑ p ∈ P, x p ≤ 4 * Real.exp (-(c * u)) := by rw [hxdef]; exact hK
  have hR : (∏ p ∈ P, (1 + 2 * (diagA σ r p * Real.exp (h / 2)))) - 1 -
      2 * ∑ p ∈ P, diagA σ r p * Real.exp (h / 2) ≤ 16 * Real.exp (-(c * u)) ^ 2 := by
    have h1 := prod_one_add_sub_le_sq P x hx0 (hxs.trans hE4)
    have e1 : ∏ p ∈ P, (1 + 2 * (diagA σ r p * Real.exp (h / 2))) = ∏ p ∈ P, (1 + x p) := by
      rw [hxdef]
    have e2 : 2 * ∑ p ∈ P, diagA σ r p * Real.exp (h / 2) = ∑ p ∈ P, x p := by
      rw [hxdef, Finset.mul_sum]
    rw [e1, e2]
    have hx00 : 0 ≤ ∑ p ∈ P, x p := Finset.sum_nonneg hx0
    have h2 : (∑ p ∈ P, x p) ^ 2 ≤ (4 * Real.exp (-(c * u))) ^ 2 := pow_le_pow_left₀ hx00 hxs 2
    calc (∏ p ∈ P, (1 + x p)) - 1 - ∑ p ∈ P, x p ≤ (∑ p ∈ P, x p) ^ 2 := h1
      _ ≤ (4 * Real.exp (-(c * u))) ^ 2 := h2
      _ = 16 * Real.exp (-(c * u)) ^ 2 := by ring
  -- coherence
  have hcoh : ∀ p ∈ P, |weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) - weilLagFunctionReal u| ≤
      Real.exp (α * u) * diagCoherence δ u := by
    intro p hp
    obtain ⟨h1, h2⟩ := hlogP p hp
    have hT : 1 ≤ Real.exp (δ * u / 2) := Real.one_le_exp (by positivity)
    have := abs_weilLagFunctionReal_add_sub_le hα hu0 (sub_nonneg.mpr h1) (by linarith) hT
      (y := Real.log ((p : ℕ) : ℝ) - u)
    rw [show u + (Real.log ((p : ℕ) : ℝ) - u) = Real.log ((p : ℕ) : ℝ) by ring] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    unfold diagCoherence
    have hW := lagWeightTotal_nonneg
    have he := Real.exp_pos (1 / 2 : ℝ)
    gcongr
    rw [← hh]
    linarith
  -- assemble
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ p ∈ P, diagA σ r p := ⟨_, rfl⟩
  rw [← hSdef] at hSlow hSup
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hSlow
  have hsplit : S * |weilLagFunctionReal u| ≤
      |∑ p ∈ P, diagA σ r p * weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))| +
        S * (Real.exp (α * u) * diagCoherence δ u) := by
    have e : S * weilLagFunctionReal u = ∑ p ∈ P, diagA σ r p * weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) -
        ∑ p ∈ P, diagA σ r p * (weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) - weilLagFunctionReal u) := by
      rw [hSdef, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [← abs_of_pos hS0, ← abs_mul, e]
    refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [abs_of_pos hS0, hSdef, Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [abs_mul, abs_of_nonneg (diagA_nonneg hr0.le p)]
    exact mul_le_mul_of_nonneg_left (hcoh p hp) (diagA_nonneg hr0.le p)
  have hA0 : 0 ≤ poleSharpConstant + lagWeightTotal * (16 * Real.exp (-(c * u)) ^ 2) *
      (1 + Real.exp (α * u)) := by
    have := poleSharpConstant_pos; have := lagWeightTotal_nonneg; positivity
  have hstar' : |∑ p ∈ P, diagA σ r p * weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))| ≤
      poleSharpConstant + lagWeightTotal * (16 * Real.exp (-(c * u)) ^ 2) *
        (1 + Real.exp (α * u)) := by
    refine hstar.trans ?_
    have := lagWeightTotal_nonneg
    have := Real.exp_pos (α * u)
    gcongr
  have hdiv : |weilLagFunctionReal u| ≤ (poleSharpConstant + lagWeightTotal *
      (16 * Real.exp (-(c * u)) ^ 2) * (1 + Real.exp (α * u))) / S +
        Real.exp (α * u) * diagCoherence δ u := by
    rw [div_add' _ _ _ hS0.ne', le_div_iff₀ hS0]
    linarith [hsplit, hstar']
  have hinv : 1 / S ≤ 2 * Real.exp (c * u) := by
    rw [div_le_iff₀ hS0]
    have h1 : Real.exp (c * u) * Real.exp (-(c * u)) = 1 := by rw [← Real.exp_add]; simp
    have h2 := mul_le_mul_of_nonneg_left hSlow (by positivity : (0 : ℝ) ≤ 2 * Real.exp (c * u))
    linarith
  have hfin : (poleSharpConstant + lagWeightTotal * (16 * Real.exp (-(c * u)) ^ 2) *
      (1 + Real.exp (α * u))) / S ≤ 2 * poleSharpConstant * Real.exp (c * u) +
        32 * lagWeightTotal * (Real.exp (-(c * u)) + Real.exp ((α - c) * u)) := by
    rw [div_eq_mul_one_div]
    refine (mul_le_mul_of_nonneg_left hinv hA0).trans (le_of_eq ?_)
    have e1 : Real.exp (-(c * u)) ^ 2 * Real.exp (c * u) = Real.exp (-(c * u)) := by
      rw [sq, mul_assoc, ← Real.exp_add]; simp
    have e2 : Real.exp (-(c * u)) ^ 2 * Real.exp (c * u) * Real.exp (α * u) =
        Real.exp ((α - c) * u) := by
      rw [e1, ← Real.exp_add]; ring_nf
    linear_combination (32 * lagWeightTotal) * e1 + (32 * lagWeightTotal) * e2
  linarith

/-! ## Exponential growth of `Φ` -/

theorem diagCoherence_le {δ u : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hu : 0 ≤ u) :
    diagCoherence δ u ≤ 2 * Real.exp (1 / 2) * (3 / 2 * lagWeightTotal +
      80 * (|xiLineTwoLogDerivConstant| + 2 + u)) * Real.exp (-(δ * u / 2)) := by
  unfold diagCoherence
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.exp (δ * u / 2) := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hT]; exact Real.one_le_exp (by positivity)
  have hT0 : 0 < T := by linarith
  have hTi : Real.exp (-(δ * u / 2)) = T⁻¹ := by rw [hT, Real.exp_neg]
  have hT2 : Real.exp (-(δ * u)) = T⁻¹ * T⁻¹ := by
    rw [← hTi, ← Real.exp_add]; ring_nf
  rw [← hT, hT2, hTi]
  have hW := lagWeightTotal_nonneg
  have hlog : Real.log (3 * T + 4) ≤ 2 + u := by
    have h1 : Real.log (3 * T + 4) ≤ Real.log (7 * T) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) hT0.ne', hT, Real.log_exp] at h1
    have h7 : Real.log 7 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e2]
      nlinarith [Real.exp_one_gt_d9]
    have hδu : δ * u ≤ u := by nlinarith
    rw [hT]
    linarith
  have hC := le_abs_self xiLineTwoLogDerivConstant
  have he := Real.exp_pos (1 / 2 : ℝ)
  have hTinv : 0 < T⁻¹ := inv_pos.mpr hT0
  have h1 : (1 / 2 + T) * (T⁻¹ * T⁻¹) * lagWeightTotal ≤ 3 / 2 * lagWeightTotal * T⁻¹ := by
    have : (1 / 2 + T) * (T⁻¹ * T⁻¹) ≤ 3 / 2 * T⁻¹ := by
      have e : (1 / 2 + T) * (T⁻¹ * T⁻¹) = (1 / 2) * T⁻¹ * T⁻¹ + T⁻¹ := by field_simp
      rw [e]
      have : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT1
      nlinarith
    nlinarith
  have h2 : 80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T ≤
      80 * (|xiLineTwoLogDerivConstant| + 2 + u) * T⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) hTinv.le
  have := add_le_add h1 h2
  calc 2 * Real.exp (1 / 2) * ((1 / 2 + T) * (T⁻¹ * T⁻¹) * lagWeightTotal +
        80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T)
      ≤ 2 * Real.exp (1 / 2) * (3 / 2 * lagWeightTotal * T⁻¹ +
          80 * (|xiLineTwoLogDerivConstant| + 2 + u) * T⁻¹) := by gcongr
    _ = _ := by ring

/-- The largeness conditions of the window, for all large `u`. -/
theorem eventually_diagWindow_conditions (X : ℕ) {σ δ c α' X₀ : ℝ} (hα' : α' < 1 - δ)
    (hκ : 0 < 1 - δ - σ + c) (hc0 : 0 < c) :
    ∀ᶠ u : ℝ in atTop, X₀ ≤ Real.exp u ∧ (X : ℝ) + 1 ≤ Real.exp u ∧
      2 * Real.exp (α' * u) ≤ Real.exp ((1 - δ) * u) / 2 ∧
      4 * Real.exp σ * (u + 1) * Real.exp (-(c * u)) ≤ Real.exp ((1 - δ - σ) * u) ∧
      4 * Real.exp (-(c * u)) ≤ 1 ∧ 1 ≤ u := by
  have ev1 : ∀ᶠ u : ℝ in atTop, X₀ ≤ Real.exp u := Real.tendsto_exp_atTop.eventually_ge_atTop X₀
  have ev1' : ∀ᶠ u : ℝ in atTop, (X : ℝ) + 1 ≤ Real.exp u :=
    Real.tendsto_exp_atTop.eventually_ge_atTop _
  have ev2 : ∀ᶠ u : ℝ in atTop, 2 * Real.exp (α' * u) ≤ Real.exp ((1 - δ) * u) / 2 := by
    have ht : Tendsto (fun u : ℝ => Real.exp (((1 - δ) - α') * u)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
    filter_upwards [ht.eventually_ge_atTop 4] with u hu
    have e : Real.exp ((1 - δ) * u) = Real.exp (((1 - δ) - α') * u) * Real.exp (α' * u) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have := Real.exp_pos (α' * u)
    nlinarith
  have ev3 : ∀ᶠ u : ℝ in atTop, 4 * Real.exp σ * (u + 1) * Real.exp (-(c * u)) ≤
      Real.exp ((1 - δ - σ) * u) := by
    have ht := (Real.tendsto_exp_div_pow_atTop 1).comp (tendsto_id.const_mul_atTop hκ)
    filter_upwards [ht.eventually_ge_atTop (8 * Real.exp σ / (1 - δ - σ + c)),
      eventually_ge_atTop (1 : ℝ)] with u hu hu1
    simp only [Function.comp, id, pow_one] at hu
    have hκu : 0 < (1 - δ - σ + c) * u := by positivity
    rw [le_div_iff₀ hκu] at hu
    have h8 : 8 * Real.exp σ / (1 - δ - σ + c) * ((1 - δ - σ + c) * u) = 8 * Real.exp σ * u := by
      field_simp
    rw [h8] at hu
    have e : Real.exp ((1 - δ - σ) * u) = Real.exp ((1 - δ - σ + c) * u) * Real.exp (-(c * u)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have hes := Real.exp_pos σ
    have h1 : 4 * Real.exp σ * (u + 1) ≤ Real.exp ((1 - δ - σ + c) * u) := by nlinarith
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have ev4 : ∀ᶠ u : ℝ in atTop, 4 * Real.exp (-(c * u)) ≤ 1 := by
    have ht : Tendsto (fun u : ℝ => Real.exp (-(c * u))) atTop (nhds 0) := by
      have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (show -c < 0 by linarith))
      refine this.congr fun u => ?_
      simp [Function.comp]
    filter_upwards [ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))] with u hu
    linarith
  exact ev1.and (ev1'.and (ev2.and (ev3.and (ev4.and (eventually_ge_atTop (1 : ℝ))))))

/-- Arithmetic: the window bound is `O(e^{aL})`. -/
theorem window_bound_le_exp {α δ c a W Φ0 C L : ℝ} (hδ0 : 0 < δ) (hc0 : 0 < c) (hL : 0 ≤ L)
    (hW : 0 ≤ W) (hΦ0 : 0 ≤ Φ0) (hC : 0 ≤ C) (hca : c ≤ a)
    (hm : α - min c (δ / 4) ≤ a) :
    2 * Φ0 * Real.exp (c * L) + 32 * W * (Real.exp (-(c * L)) + Real.exp ((α - c) * L)) +
        Real.exp (α * L) * (2 * Real.exp (1 / 2) * (3 / 2 * W + 80 * (C + 2 + L)) *
          Real.exp (-(δ * L / 2))) ≤
      (2 * Φ0 + 64 * W + 2 * Real.exp (1 / 2) * (3 / 2 * W + 80 * (C + 2) + 80 * (4 / δ))) *
        Real.exp (a * L) := by
  have hmc : min c (δ / 4) ≤ c := min_le_left _ _
  have hmd : min c (δ / 4) ≤ δ / 4 := min_le_right _ _
  have t1 : Real.exp (c * L) ≤ Real.exp (a * L) := Real.exp_le_exp.mpr (by nlinarith)
  have t2 : Real.exp (-(c * L)) ≤ Real.exp (a * L) := Real.exp_le_exp.mpr (by nlinarith)
  have t3 : Real.exp ((α - c) * L) ≤ Real.exp (a * L) := Real.exp_le_exp.mpr (by nlinarith)
  have t4 : Real.exp ((α - δ / 4) * L) ≤ Real.exp (a * L) := Real.exp_le_exp.mpr (by nlinarith)
  have e1 : Real.exp (α * L) * Real.exp (-(δ * L / 2)) =
      Real.exp ((α - δ / 4) * L) * Real.exp (-(δ * L / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h5 : Real.exp (δ * L / 4) * Real.exp (-(δ * L / 4)) = 1 := by rw [← Real.exp_add]; simp
  have h7 : Real.exp (-(δ * L / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hlin : L ≤ 4 / δ * Real.exp (δ * L / 4) := by
    have := Real.add_one_le_exp (δ * L / 4)
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
    nlinarith
  have h8 : L * Real.exp (-(δ * L / 4)) ≤ 4 / δ := by
    have := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-(δ * L / 4))).le
    rwa [mul_assoc, h5, mul_one] at this
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (3 / 2 * W + 80 * (C + 2 + L)) * Real.exp (-(δ * L / 4)) := ⟨_, rfl⟩
  have hQb : Q ≤ 3 / 2 * W + 80 * (C + 2) + 80 * (4 / δ) := by
    have h9 : 0 ≤ 3 / 2 * W + 80 * (C + 2) := by positivity
    have := mul_le_mul_of_nonneg_left h7 h9
    rw [hQ]
    nlinarith [Real.exp_pos (-(δ * L / 4))]
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have e2 : Real.exp (α * L) * (2 * Real.exp (1 / 2) * (3 / 2 * W + 80 * (C + 2 + L)) *
      Real.exp (-(δ * L / 2))) = 2 * Real.exp (1 / 2) * Q * Real.exp ((α - δ / 4) * L) := by
    rw [hQ]
    linear_combination (2 * Real.exp (1 / 2) * (3 / 2 * W + 80 * (C + 2 + L))) * e1
  rw [e2]
  have he := Real.exp_pos (1 / 2 : ℝ)
  have k1 : 2 * Real.exp (1 / 2) * Q * Real.exp ((α - δ / 4) * L) ≤
      2 * Real.exp (1 / 2) * (3 / 2 * W + 80 * (C + 2) + 80 * (4 / δ)) * Real.exp (a * L) := by
    gcongr
  have k2 := mul_le_mul_of_nonneg_left t1 (by positivity : (0 : ℝ) ≤ 2 * Φ0)
  have k3 := mul_le_mul_of_nonneg_left (add_le_add t2 t3) (by positivity : (0 : ℝ) ≤ 32 * W)
  nlinarith

/-- Positive windows at scale `u`: a set of primes with `log p ∈ [u, u + e^{−δu}]`, weight
`Σ p^{−σ} ≥ e^{−cu}`, on which the constant-vector product tests are positive. -/
def JasPositiveWindow (σ δ c u : ℝ) : Prop :=
  ∃ P : Finset Nat.Primes, JasConstProductPositiveOn P σ ∧
    (∀ p ∈ P, u ≤ Real.log ((p : ℕ) : ℝ) ∧ Real.log ((p : ℕ) : ℝ) ≤ u + Real.exp (-(δ * u))) ∧
    Real.exp (-(c * u)) ≤ ∑ p ∈ P, Real.exp (-σ * Real.log ((p : ℕ) : ℝ))

/-- **Exponential growth of the lag function from positive windows.**  If positive windows exist
at all large scales, with `0 < δ ≤ 1` and `c > 0`, and `|Re ρ − ½| ≤ α`, then `|Φ(L)| ≤ M e^{aL}`
for all `L ≥ 0`, where `a = max(c, α − min(c, δ/4))`. -/
theorem exists_abs_weilLagFunctionReal_le_exp_of_windows {σ α δ c : ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hc0 : 0 < c)
    (hW : ∀ᶠ u : ℝ in atTop, JasPositiveWindow σ δ c u) :
    ∃ M : ℝ, ∀ L, 0 ≤ L →
      |weilLagFunctionReal L| ≤ M * Real.exp (max c (α - min c (δ / 4)) * L) := by
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = max c (α - min c (δ / 4)) := ⟨_, rfl⟩
  rw [← hadef]
  have hca : c ≤ a := hadef ▸ le_max_left _ _
  have hm : α - min c (δ / 4) ≤ a := hadef ▸ le_max_right _ _
  have ha0 : 0 ≤ a := by linarith
  have ev4 : ∀ᶠ u : ℝ in atTop, 4 * Real.exp (-(c * u)) ≤ 1 := by
    have ht : Tendsto (fun u : ℝ => Real.exp (-(c * u))) atTop (nhds 0) := by
      have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (show -c < 0 by linarith))
      refine this.congr fun u => ?_
      simp [Function.comp]
    filter_upwards [ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))] with u hu
    linarith
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (hW.and (ev4.and (eventually_ge_atTop (1 : ℝ))))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * poleSharpConstant + 64 * lagWeightTotal +
      2 * Real.exp (1 / 2) * (3 / 2 * lagWeightTotal + 80 * (|xiLineTwoLogDerivConstant| + 2) +
        80 * (4 / δ)) := ⟨_, rfl⟩
  have hW0 := lagWeightTotal_nonneg
  refine ⟨max K (Real.exp (|u₀| / 2) * lagWeightTotal), fun L hL => ?_⟩
  rcases le_or_gt u₀ L with hLu | hLu
  · obtain ⟨⟨P, hposP, hlogP, hMass⟩, hE4, hu1⟩ := hu₀ L hLu
    have hb := abs_weilLagFunctionReal_le_of_window hα hδ0 hu1 hE4 P hposP hlogP hMass
    have hcoh := diagCoherence_le hδ0 hδ1 hL
    have hb2 := hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcoh (Real.exp_pos _).le))
    have hw := window_bound_le_exp (α := α) (W := lagWeightTotal) (Φ0 := poleSharpConstant)
      (C := |xiLineTwoLogDerivConstant|) hδ0 hc0 hL hW0 poleSharpConstant_pos.le (abs_nonneg _)
      hca hm
    rw [← hK] at hw
    exact (hb2.trans hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have h1 := abs_weilLagFunctionReal_le L
    rw [abs_of_nonneg hL] at h1
    have h2 : Real.exp (L / 2) ≤ Real.exp (|u₀| / 2) :=
      Real.exp_le_exp.mpr (by linarith [le_abs_self u₀])
    have h3 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
    have h4 : |weilLagFunctionReal L| ≤ Real.exp (|u₀| / 2) * lagWeightTotal :=
      h1.trans (mul_le_mul_of_nonneg_right h2 hW0)
    have h5 : 0 ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) :=
      le_trans (by positivity) (le_max_right _ _)
    calc |weilLagFunctionReal L| ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) :=
          h4.trans (le_max_right _ _)
      _ ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L) :=
          le_mul_of_one_le_right h5 h3

/-- **Positive windows give the half-plane.**  If for every `0 < δ < 5/12` and every
`c₀ + δ < c < ½`, `c > 0`, positive windows exist at all large scales, then every zero satisfies
`|Re ρ − ½| ≤ max(0, c₀)`. -/
theorem abs_re_sub_half_le_of_windows {σ c₀ : ℝ}
    (hW : ∀ δ c : ℝ, 0 < δ → δ < 5 / 12 → 0 < c → c₀ + δ < c → c < 1 / 2 →
      ∀ᶠ u : ℝ in atTop, JasPositiveWindow σ δ c u) (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c₀ := by
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
  have key : ∀ δ c : ℝ, 0 < δ → δ < 5 / 12 → 0 < c → c₀ + δ < c → c < 1 / 2 → α ≤ c := by
    intro δ c hδ0 hδ hc0 hc hch
    obtain ⟨M, hM⟩ := exists_abs_weilLagFunctionReal_le_exp_of_windows hαall hδ0 (by linarith)
      hc0 (hW δ c hδ0 hδ hc0 hc hch)
    have hm0 : 0 < min c (δ / 4) := lt_min hc0 (by linarith)
    have ha0 : 0 ≤ max c (α - min c (δ / 4)) := le_trans hc0.le (le_max_left _ _)
    have ha : max c (α - min c (δ / 4)) < 1 / 2 := max_lt hch (by linarith)
    have hg : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + max c (α - min c (δ / 4)) := fun q =>
      re_le_half_add_of_weilLagFunctionReal_le_exp ha0 ha
        (fun L hL => (le_abs_self _).trans (hM L hL)) q
    have hsup := zeroReSup_le hg
    have hΘ : zeroReSup = α + 1 / 2 := by rw [hαdef]; ring
    have hle : α ≤ max c (α - min c (δ / 4)) := by linarith
    by_contra hlt
    push Not at hlt
    rcases le_total c (α - min c (δ / 4)) with h | h
    · rw [max_eq_right h] at hle; linarith
    · rw [max_eq_left h] at hle; linarith
  have hfin : α ≤ max 0 c₀ := by
    by_cases ht : 1 / 2 ≤ max 0 c₀
    · linarith
    · push Not at ht
      refine le_of_forall_pos_le_add fun ε hε => ?_
      rcases le_or_gt (1 / 2 - max 0 c₀) ε with hε' | hε'
      · linarith
      · have h1 := le_max_left 0 c₀
        have h2 := le_max_right 0 c₀
        have h3 := min_le_left (ε / 2) (1 / 4)
        have h4 := min_le_right (ε / 2) (1 / 4)
        exact key (min (ε / 2) (1 / 4)) (max 0 c₀ + ε) (lt_min (by linarith) (by norm_num))
          (by linarith) (by linarith) (by linarith) (by linarith)
  exact (hαall q).trans hfin

/-- Interval positivity supplies positive windows (the Huxley windows themselves). -/
theorem eventually_jasPositiveWindow_of_jasIntervalProductPositive {X : ℕ} {σ : ℝ}
    (hpos : JasIntervalProductPositive X σ) (hσ : 0 ≤ σ) {δ c : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < 5 / 12) (hc0 : 0 < c) (hc : σ - 1 + δ < c) :
    ∀ᶠ u : ℝ in atTop, JasPositiveWindow σ δ c u := by
  obtain ⟨X₀, -, hX₀⟩ := exists_theta_window_lower_seven_twelfths
    (α := (7 / 12 + (1 - δ)) / 2) (by linarith) (by linarith)
  filter_upwards [eventually_diagWindow_conditions X (σ := σ) (δ := δ) (c := c)
    (α' := (7 / 12 + (1 - δ)) / 2) (X₀ := X₀) (by linarith) (by linarith) hc0]
    with u hu
  obtain ⟨hE1, hE1', hE2, hE3, -, hu1⟩ := hu
  obtain ⟨P, hPdef, hlogP, hMass⟩ := exists_window (X := X) (c := c) hσ hδ0 (by linarith)
    (by linarith) hX₀ hu1 hE1 hE1' hE2 hE3
  refine ⟨P, ?_, hlogP, hMass⟩
  rw [hPdef]; exact hpos _ _ hE1' (Real.exp_pos _).le

/-- **Interval product positivity at level `σ` forces `|Re ρ − ½| ≤ max(0, σ − 1)`.** -/
theorem abs_re_sub_half_le_of_jasIntervalProductPositive {X : ℕ} {σ : ℝ}
    (hpos : JasIntervalProductPositive X σ) (hσ : 0 ≤ σ) (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 (σ - 1) :=
  abs_re_sub_half_le_of_windows (fun _ _ hδ0 hδ hc0 hc _ =>
    eventually_jasPositiveWindow_of_jasIntervalProductPositive hpos hσ hδ0 hδ hc0 hc) q

theorem abs_re_sub_half_le_of_jasProductPositiveAbove {X : ℕ} {σ : ℝ}
    (hpos : JasProductPositiveAbove X σ) (hσ : 0 ≤ σ) (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 (σ - 1) :=
  abs_re_sub_half_le_of_jasIntervalProductPositive hpos.intervalPositive hσ q

/-- **Interval product positivity at a level `σ ≤ 1` implies RH.** -/
theorem riemannHypothesis_of_jasIntervalProductPositive {X : ℕ} {σ : ℝ}
    (hpos : JasIntervalProductPositive X σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) : RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have := abs_re_sub_half_le_of_jasIntervalProductPositive hpos hσ0 q
  rw [max_eq_left (by linarith)] at this
  linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- **RH ⟺ interval product positivity at level `1`.**  RH holds iff, for some `X`, the aggregate
`Re Σ_ρ w_ρ ∏_{y < p ≤ y + L} (1 + z p^{−(ρ+½)} + z̄ p^{−(3/2−ρ)} + |z|²)` is nonnegative for every
interval `(y, y + L]` with `y ≥ X + 1` and every constant `z ∈ ℂ`. -/
theorem riemannHypothesis_iff_exists_jasIntervalProductPositive_one :
    RiemannHypothesis ↔ ∃ X : ℕ, JasIntervalProductPositive X 1 := by
  constructor
  · intro hRH
    obtain ⟨X, σ, hσ0, hσ, h⟩ := riemannHypothesis_iff_exists_jasProductPositiveAbove_lt_half.mp hRH
    exact ⟨X, (h.mono_level (by linarith)).intervalPositive⟩
  · rintro ⟨X, h⟩
    exact riemannHypothesis_of_jasIntervalProductPositive h (by norm_num) le_rfl

/-- **Level-one product positivity implies the Riemann hypothesis.**  More generally, product
positivity on the primes `p > X` at any level `0 ≤ σ ≤ 1` implies RH. -/
theorem riemannHypothesis_of_jasProductPositiveAbove {X : ℕ} {σ : ℝ}
    (hpos : JasProductPositiveAbove X σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) : RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have := abs_re_sub_half_le_of_jasProductPositiveAbove hpos hσ0 q
  rw [max_eq_left (by linarith)] at this
  linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- **RH ⟺ level-one product positivity**, with no zero-free-region hypothesis. -/
theorem riemannHypothesis_iff_exists_jasProductPositiveAbove_one :
    RiemannHypothesis ↔ ∃ X : ℕ, JasProductPositiveAbove X 1 := by
  constructor
  · intro hRH
    obtain ⟨X, σ, hσ0, hσ, h⟩ := riemannHypothesis_iff_exists_jasProductPositiveAbove_lt_half.mp hRH
    exact ⟨X, h.mono_level (by linarith)⟩
  · rintro ⟨X, h⟩
    exact riemannHypothesis_of_jasProductPositiveAbove h (by norm_num) le_rfl

/-- **The product abscissa law.**  Product positivity at a level `1 ≤ σ` forces every zero into
`|Re ρ − ½| ≤ σ − 1`, i.e. `sup Re ρ ≤ σ − ½`. -/
theorem xiZeroHalfPlaneBound_of_jasProductPositiveAbove {X : ℕ} {σ : ℝ}
    (hpos : JasProductPositiveAbove X σ) (hσ : 1 ≤ σ) : XiZeroHalfPlaneBound (σ - 1) := by
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have := abs_re_sub_half_le_of_jasProductPositiveAbove hpos (by linarith) q
  rw [max_eq_right (by linarith)] at this
  linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

end

end RHTower
