import GaloisForLFunctions.RHTower.RVCumulantAverage

/-!
# The cumulant limit

The card's `(12)`:

`(1/d_X) ∑_{p ≤ X} log I₀(λ d_X a_{p,X}) → Λ_α(λ)`.

The head is bounded by `log I₀(x) ≤ x`, which converts it into the ratio of two prime Karamata
sums; the body is compared shell by shell with the Riemann sums of the antitone integrand
`v ↦ log I₀(λ w_α(v))`, the shell counts being supplied by `tendsto_shell_card_ratio` and the
normalized weights by `rvNormReal_bounds`.
-/

open MeasureTheory Filter Topology HTGeometry

namespace RHTower

noncomputable section

/-- The decomposition of the prime average into head and shells. -/
theorem rvCumulantAverage_decomp {α : ℝ} {L : ℝ → ℝ} {lam : ℝ} {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hv₀1 : v₀ < 1) {N : ℕ} (hN : 0 < N) {X : ℝ} (hX : 0 < X) :
    primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 X
      = primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 (v₀ * X)
        + ∑ j ∈ Finset.range N, primeCountSum
            (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
            (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X) := by
  set x : ℕ → ℝ := fun k => if k = 0 then 0 else karamataNode v₀ N (k - 1) * X with hx
  have hx0 : x 0 = 0 := by simp [hx]
  have hxsucc : ∀ k : ℕ, x (k + 1) = karamataNode v₀ N k * X := by
    intro k
    simp [hx]
  have hmono : ∀ k, ⌊x k⌋₊ ≤ ⌊x (k + 1)⌋₊ := by
    intro k
    refine Nat.floor_mono ?_
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [hx0, hxsucc]
      have := karamataNode_pos hv₀ hv₀1 N 0
      positivity
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      rw [hxsucc, hxsucc]
      have hnode := karamataNode_mono (v₀ := v₀) (N := N) hv₀1 (Nat.le_succ m)
      nlinarith [hnode, hX.le]
  have hchain := primeCountSum_chain
    (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) x hmono (N + 1)
  rw [hx0, hxsucc, karamataNode_last hN, one_mul] at hchain
  rw [← hchain, Finset.sum_range_succ']
  have hfirst : primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
      (x 0) (x (0 + 1))
      = primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 (v₀ * X) := by
    rw [hx0, hxsucc, karamataNode_zero]
  have hrest : ∀ k ∈ Finset.range N,
      primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
          (x (k + 1)) (x (k + 1 + 1))
      = primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
          (karamataNode v₀ N k * X) (karamataNode v₀ N (k + 1) * X) := by
    intro k _
    rw [hxsucc, hxsucc]
  rw [Finset.sum_congr rfl hrest, hfirst]
  ring


theorem weightProfile_antitone {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {u v : ℝ} (hu : 0 < u)
    (huv : u ≤ v) : weightProfile α v ≤ weightProfile α u := by
  have hα' : (0 : ℝ) < 1 - α := by linarith
  have hpow : v ^ (-α) ≤ u ^ (-α) := Real.rpow_le_rpow_of_nonpos hu huv (by linarith)
  rw [weightProfile, weightProfile]
  exact mul_le_mul_of_nonneg_left hpow hα'.le

/-- The distorted upper Riemann sum. -/
def rvUpSum (α : ℝ) (lam v₀ : ℝ) (N : ℕ) (c : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    steinhausLogLaplace (lam * (1 + c) ^ 4 * weightProfile α (karamataNode v₀ N j))
      * ((1 - v₀) / N + c)

/-- The distorted lower Riemann sum. -/
def rvLoSum (α : ℝ) (lam v₀ : ℝ) (N : ℕ) (c : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    steinhausLogLaplace (lam * (1 - c) ^ 4 * weightProfile α (karamataNode v₀ N (j + 1)))
      * ((1 - v₀) / N - c)

theorem continuous_rvUpSum (α lam v₀ : ℝ) (N : ℕ) : Continuous (rvUpSum α lam v₀ N) := by
  refine continuous_finset_sum _ fun j _ => ?_
  exact (continuous_steinhausLogLaplace.comp
    (((continuous_const.mul ((continuous_const.add continuous_id).pow 4)).mul
      continuous_const))).mul (continuous_const.add continuous_id)

theorem continuous_rvLoSum (α lam v₀ : ℝ) (N : ℕ) : Continuous (rvLoSum α lam v₀ N) := by
  refine continuous_finset_sum _ fun j _ => ?_
  exact (continuous_steinhausLogLaplace.comp
    (((continuous_const.mul ((continuous_const.sub continuous_id).pow 4)).mul
      continuous_const))).mul (continuous_const.sub continuous_id)

theorem rvUpSum_zero (α lam v₀ : ℝ) (N : ℕ) :
    rvUpSum α lam v₀ N 0
      = (∑ j ∈ Finset.range N, rvProfileCumulant α lam (karamataNode v₀ N j)) * ((1 - v₀) / N) := by
  rw [rvUpSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [rvProfileCumulant]

theorem rvLoSum_zero (α lam v₀ : ℝ) (N : ℕ) :
    rvLoSum α lam v₀ N 0
      = (∑ j ∈ Finset.range N, rvProfileCumulant α lam (karamataNode v₀ N (j + 1)))
        * ((1 - v₀) / N) := by
  rw [rvLoSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [rvProfileCumulant]

/-- The Darboux gap telescopes. -/
theorem rvDarboux_gap {α lam v₀ : ℝ} {N : ℕ} (hN : 0 < N) :
    (∑ j ∈ Finset.range N, rvProfileCumulant α lam (karamataNode v₀ N j))
      - ∑ j ∈ Finset.range N, rvProfileCumulant α lam (karamataNode v₀ N (j + 1))
      = rvProfileCumulant α lam v₀ - rvProfileCumulant α lam 1 := by
  rw [← Finset.sum_sub_distrib]
  have := Finset.sum_range_sub'
    (fun j : ℕ => rvProfileCumulant α lam (karamataNode v₀ N j)) N
  rw [this, karamataNode_zero, karamataNode_last hN]


/-- **The shell totals of the prime average.** -/
theorem rvCumulantAverage_shell_bounds {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) {lam : ℝ} (hlam : 0 ≤ lam) {v₀ : ℝ} (hv₀ : 0 < v₀) (hv₀1 : v₀ < 1)
    {N : ℕ} (hN : 0 < N) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∀ᶠ X in atTop,
      (∑ j ∈ Finset.range N, primeCountSum
          (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
          (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X)) / rvPrimeCount X
        ≤ rvUpSum α lam v₀ N c
      ∧ rvLoSum α lam v₀ N c ≤
        (∑ j ∈ Finset.range N, primeCountSum
          (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
          (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X)) / rvPrimeCount X := by
  have hnodepos : ∀ j : ℕ, 0 < karamataNode v₀ N j := fun j => karamataNode_pos hv₀ hv₀1 N j
  have hall : ∀ j ∈ Finset.range N, ∀ᶠ X in atTop,
      (∀ t : ℝ, karamataNode v₀ N j * X < t → t ≤ karamataNode v₀ N (j + 1) * X →
        (1 - c) ^ 4 * weightProfile α (t / X) ≤ rvNormReal α L X t
          ∧ rvNormReal α L X t ≤ (1 + c) ^ 4 * weightProfile α (t / X))
      ∧ |(primeShellCard (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X) : ℝ)
            / rvPrimeCount X - (karamataNode v₀ N (j + 1) - karamataNode v₀ N j)| ≤ c
      ∧ 1 < karamataNode v₀ N j * X := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 := rvNormReal_bounds hα0 hα1 hL (hnodepos j)
      (karamataNode_mono hv₀1 (Nat.le_succ j)) (karamataNode_le_one hv₀1 hN hj) hc0 hc1
    have h2 := (tendsto_shell_card_ratio (hnodepos j)
      (karamataNode_mono (v₀ := v₀) (N := N) hv₀1 (Nat.le_succ j))).eventually
      (Metric.closedBall_mem_nhds _ hc0)
    have h3 : ∀ᶠ X in atTop, 1 < karamataNode v₀ N j * X :=
      (tendsto_const_mul_atTop_of_pos (hnodepos j)).eventually_gt_atTop 1
    filter_upwards [h1, h2, h3] with X hX1 hX2 hX3
    exact ⟨hX1, by rw [Real.dist_eq] at hX2; exact hX2, hX3⟩
  rw [← Filter.eventually_all_finset] at hall
  have hd : ∀ᶠ X in atTop, 0 < rvPrimeCount X := by
    have := tendsto_rvPrimeCount_ratio_inv
    have hev : ∀ᶠ X in atTop, (2 : ℝ) ≤ X := eventually_ge_atTop 2
    filter_upwards [hev] with X hX
    have h2 : (2 : ℕ) ≤ ⌊X⌋₊ := Nat.le_floor (by push_cast; linarith)
    have : 0 < Nat.primeCounting ⌊X⌋₊ := by
      have hmono := Nat.monotone_primeCounting h2
      have : 0 < Nat.primeCounting 2 := by decide
      omega
    rw [rvPrimeCount]
    exact_mod_cast this
  have hW : ∀ᶠ X in atTop, 0 < rvWeightSum α L X := by
    have hα' : (0 : ℝ) < 1 - α := by linarith
    have hlim := (tendsto_rvWeightSum hα0 hα1 hL).eventually_const_lt
      (show (0 : ℝ) < 1 / (1 - α) by positivity)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with X hX hX1
    have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
    have hLX : 0 < L X := hL.pos _ hX0
    have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
    have hden : (0 : ℝ) < X ^ (1 - α) * L X := mul_pos hXpow hLX
    rw [lt_div_iff₀ hden, zero_mul] at hX
    exact hX
  filter_upwards [hall, hd, hW, eventually_gt_atTop (0 : ℝ)] with X hX hdX hWX hX0
  have hshell : ∀ j ∈ Finset.range N,
      primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
          (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X) / rvPrimeCount X
        ≤ steinhausLogLaplace (lam * (1 + c) ^ 4 * weightProfile α (karamataNode v₀ N j))
            * ((1 - v₀) / N + c)
      ∧ steinhausLogLaplace (lam * (1 - c) ^ 4
            * weightProfile α (karamataNode v₀ N (j + 1))) * ((1 - v₀) / N - c)
        ≤ primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
            (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X) / rvPrimeCount X := by
    intro j hj
    obtain ⟨hnorm, hcard, hone⟩ := hX j hj
    have hjr := Finset.mem_range.1 hj
    have hab : karamataNode v₀ N j * X ≤ karamataNode v₀ N (j + 1) * X :=
      mul_le_mul_of_nonneg_right (karamataNode_mono hv₀1 (Nat.le_succ j)) hX0.le
    have hMnn : 0 ≤ steinhausLogLaplace
        (lam * (1 + c) ^ 4 * weightProfile α (karamataNode v₀ N j)) :=
      steinhausLogLaplace_nonneg _
    have hmnn : 0 ≤ steinhausLogLaplace
        (lam * (1 - c) ^ 4 * weightProfile α (karamataNode v₀ N (j + 1))) :=
      steinhausLogLaplace_nonneg _
    rw [abs_le] at hcard
    rw [karamataNode_diff] at hcard
    constructor
    · have hup := primeCountSum_le (f := fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
        hone hab hMnn ?_
      · rw [div_le_iff₀ hdX]
        have hcards : (primeShellCard (karamataNode v₀ N j * X)
            (karamataNode v₀ N (j + 1) * X) : ℝ)
            ≤ ((1 - v₀) / N + c) * rvPrimeCount X := by
          rw [← div_le_iff₀ hdX] at *
          linarith [hcard.2]
        calc primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
              (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X)
            ≤ (primeShellCard (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X) : ℝ)
              * steinhausLogLaplace
                (lam * (1 + c) ^ 4 * weightProfile α (karamataNode v₀ N j)) := hup
          _ ≤ (((1 - v₀) / N + c) * rvPrimeCount X) * steinhausLogLaplace
                (lam * (1 + c) ^ 4 * weightProfile α (karamataNode v₀ N j)) :=
              mul_le_mul_of_nonneg_right hcards hMnn
          _ = steinhausLogLaplace
                (lam * (1 + c) ^ 4 * weightProfile α (karamataNode v₀ N j))
              * ((1 - v₀) / N + c) * rvPrimeCount X := by ring
      · intro p hprime h1 h2
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_lt.le
        obtain ⟨-, hub⟩ := hnorm (p : ℝ) h1 h2
        have hvp : karamataNode v₀ N j ≤ (p : ℝ) / X := by
          rw [le_div_iff₀ hX0]; linarith [h1]
        have hwle : weightProfile α ((p : ℝ) / X) ≤ weightProfile α (karamataNode v₀ N j) :=
          weightProfile_antitone hα0 hα1 (hnodepos j) hvp
        have hnn : 0 ≤ lam * rvNormReal α L X (p : ℝ) :=
          mul_nonneg hlam (rvNormReal_nonneg hL hWX hp1)
        refine steinhausLogLaplace_mono hnn ?_
        have hc4 : (0 : ℝ) ≤ (1 + c) ^ 4 := by positivity
        have hstep : rvNormReal α L X (p : ℝ) ≤ (1 + c) ^ 4 * weightProfile α (karamataNode v₀ N j) :=
          le_trans hub (mul_le_mul_of_nonneg_left hwle hc4)
        nlinarith only [hstep, hlam]
    · have hlow := le_primeCountSum (f := fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
        hone hab ?_
      · rw [le_div_iff₀ hdX]
        have hcards : ((1 - v₀) / N - c) * rvPrimeCount X
            ≤ (primeShellCard (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X) : ℝ) := by
          rw [← le_div_iff₀ hdX]
          linarith [hcard.1]
        calc steinhausLogLaplace
              (lam * (1 - c) ^ 4 * weightProfile α (karamataNode v₀ N (j + 1)))
            * ((1 - v₀) / N - c) * rvPrimeCount X
            = (((1 - v₀) / N - c) * rvPrimeCount X) * steinhausLogLaplace
                (lam * (1 - c) ^ 4 * weightProfile α (karamataNode v₀ N (j + 1))) := by ring
          _ ≤ (primeShellCard (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X) : ℝ)
              * steinhausLogLaplace
                (lam * (1 - c) ^ 4 * weightProfile α (karamataNode v₀ N (j + 1))) :=
              mul_le_mul_of_nonneg_right hcards hmnn
          _ ≤ primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
              (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X) := hlow
      · intro p hprime h1 h2
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_lt.le
        obtain ⟨hlb, -⟩ := hnorm (p : ℝ) h1 h2
        have hvp : (p : ℝ) / X ≤ karamataNode v₀ N (j + 1) := by
          rw [div_le_iff₀ hX0]; linarith [h2]
        have hwge : weightProfile α (karamataNode v₀ N (j + 1)) ≤ weightProfile α ((p : ℝ) / X) :=
          weightProfile_antitone hα0 hα1 (by positivity) hvp
        have hc4 : (0 : ℝ) ≤ (1 - c) ^ 4 := by positivity
        have hstep : (1 - c) ^ 4 * weightProfile α (karamataNode v₀ N (j + 1))
            ≤ rvNormReal α L X (p : ℝ) :=
          le_trans (mul_le_mul_of_nonneg_left hwge hc4) hlb
        have hwnn : 0 ≤ weightProfile α (karamataNode v₀ N (j + 1)) :=
          weightProfile_nonneg hα1 (hnodepos (j + 1)).le
        refine steinhausLogLaplace_mono (by positivity) ?_
        nlinarith only [hstep, hlam]
  rw [Finset.sum_div]
  constructor
  · exact Finset.sum_le_sum fun j hj => (hshell j hj).1
  · exact Finset.sum_le_sum fun j hj => (hshell j hj).2

end

end RHTower
