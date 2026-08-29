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
  refine continuous_finsetSum _ fun j _ => ?_
  exact (continuous_steinhausLogLaplace.comp
    (((continuous_const.mul ((continuous_const.add continuous_id).pow 4)).mul
      continuous_const))).mul (continuous_const.add continuous_id)

theorem continuous_rvLoSum (α lam v₀ : ℝ) (N : ℕ) : Continuous (rvLoSum α lam v₀ N) := by
  refine continuous_finsetSum _ fun j _ => ?_
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
        (m := steinhausLogLaplace
          (lam * (1 - c) ^ 4 * weightProfile α (karamataNode v₀ N (j + 1)))) hone hab ?_
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


/-- **The card's `(12)`.** -/
theorem tendsto_rvCumulantAverage {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun X : ℝ => rvCumulantAverage α L lam X) atTop (𝓝 (rvCumulant α lam)) := by
  have hα' : (0 : ℝ) < 1 - α := by linarith
  rw [Metric.tendsto_nhds]
  intro η hη
  set εh : ℝ := (η / 8) / (2 * (1 - α) * (lam + 1)) with hεh
  have hεh0 : 0 < εh := by rw [hεh]; positivity
  obtain ⟨w, hw0, hw1, hwb⟩ := exists_karamata_head_bound hα0 hα1 hL hεh0
  obtain ⟨u, hu0, hu1, hub⟩ : ∃ u : ℝ, 0 < u ∧ u < 1 ∧ lam * u ^ (1 - α) ≤ η / 8 := by
    have hc : ContinuousAt (fun v : ℝ => v ^ (1 - α)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr hα'.le)
    have h0 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rw [Real.zero_rpow hα'.ne'] at h0
    have hlim := h0.const_mul lam
    rw [mul_zero] at hlim
    have hev := hlim.eventually_le_const (show (0 : ℝ) < η / 8 by linarith)
    obtain ⟨v, ⟨hv1, hv2⟩⟩ := ((hev.and self_mem_nhdsWithin).and
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)).exists
    exact ⟨v, hv1.2, hv2, hv1.1⟩
  set v₀ : ℝ := min w u with hv₀def
  have hv₀0 : 0 < v₀ := lt_min hw0 hu0
  have hv₀1 : v₀ < 1 := lt_of_le_of_lt (min_le_left _ _) hw1
  have hv₀w : v₀ ≤ w := min_le_left _ _
  have hv₀u : v₀ ≤ u := min_le_right _ _
  have htail : lam * v₀ ^ (1 - α) ≤ η / 8 := by
    have hmono : v₀ ^ (1 - α) ≤ u ^ (1 - α) := Real.rpow_le_rpow hv₀0.le hv₀u hα'.le
    nlinarith only [hmono, hub, hlam]
  -- the block count
  set Gap : ℝ := rvProfileCumulant α lam v₀ - rvProfileCumulant α lam 1 with hGap
  obtain ⟨N, hN0, hNb⟩ : ∃ N : ℕ, 0 < N ∧ Gap * ((1 - v₀) / N) ≤ η / 8 := by
    have hGap0 : 0 ≤ Gap := by
      rw [hGap]
      have := antitoneOn_rvProfileCumulant hα0 hα1 hlam hv₀0
        (Set.left_mem_Icc.2 hv₀1.le) (Set.right_mem_Icc.2 hv₀1.le) hv₀1.le
      linarith
    obtain ⟨M, hM⟩ := exists_nat_gt (Gap * (1 - v₀) / (η / 8))
    refine ⟨M + 1, Nat.succ_pos _, ?_⟩
    have hMR : (0 : ℝ) < ((M : ℝ) + 1) := by positivity
    have hM' : Gap * (1 - v₀) / (η / 8) < (M : ℝ) + 1 := by linarith [hM]
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < η / 8)] at hM'
    have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    rw [hcast, mul_div_assoc', div_le_iff₀ hMR]
    nlinarith only [hM']
  -- the tilt tolerance
  obtain ⟨c, hc0, hc1, hcU, hcL⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      rvUpSum α lam v₀ N c ≤ rvUpSum α lam v₀ N 0 + η / 8
      ∧ rvLoSum α lam v₀ N 0 - η / 8 ≤ rvLoSum α lam v₀ N c := by
    have hU := (continuous_rvUpSum α lam v₀ N).continuousAt.tendsto.eventually
      (eventually_lt_nhds (show rvUpSum α lam v₀ N 0 < rvUpSum α lam v₀ N 0 + η / 8 by linarith))
    have hL' := (continuous_rvLoSum α lam v₀ N).continuousAt.tendsto.eventually
      (eventually_gt_nhds (show rvLoSum α lam v₀ N 0 - η / 8 < rvLoSum α lam v₀ N 0 by linarith))
    have hpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), (0 : ℝ) < x := self_mem_nhdsWithin
    have hlt1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    obtain ⟨x, ⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ :=
      (((hU.filter_mono nhdsWithin_le_nhds).and
        (hL'.filter_mono nhdsWithin_le_nhds)).and hpos).and hlt1 |>.exists
    exact ⟨x, hx3, hx4, hx1.le, hx2.le⟩
  -- the Darboux data
  have hanti := antitoneOn_rvProfileCumulant hα0 hα1 hlam hv₀0
  obtain ⟨hdarL, hdarU⟩ := antitone_darboux hv₀0 hv₀1 hN0 hanti
  have hsplit := integral_rvProfileCumulant_split hα1 lam hv₀0.le hv₀1.le
  have hheadint := integral_rvProfileCumulant_head_le hα1 hlam hv₀0.le hv₀1.le
  have hheadnn : 0 ≤ ∫ v in (0 : ℝ)..v₀, rvProfileCumulant α lam v := by
    refine intervalIntegral.integral_nonneg hv₀0.le fun v _ => ?_
    exact steinhausLogLaplace_nonneg _
  have hgapid := rvDarboux_gap (α := α) (lam := lam) (v₀ := v₀) hN0
  -- the numeric Darboux comparison
  have hUp0 : rvUpSum α lam v₀ N 0 ≤ rvCumulant α lam + η / 8 := by
    rw [rvUpSum_zero]
    have hdiff : (∑ j ∈ Finset.range N, rvProfileCumulant α lam (karamataNode v₀ N j))
        * ((1 - v₀) / N)
        - (∑ j ∈ Finset.range N, rvProfileCumulant α lam (karamataNode v₀ N (j + 1)))
          * ((1 - v₀) / N) = Gap * ((1 - v₀) / N) := by
      rw [← sub_mul, hgapid, hGap]
    linarith [hdarL, hsplit, hheadnn, hNb, hdiff]
  have hLo0 : rvCumulant α lam - η / 4 ≤ rvLoSum α lam v₀ N 0 := by
    rw [rvLoSum_zero]
    have hdiff : (∑ j ∈ Finset.range N, rvProfileCumulant α lam (karamataNode v₀ N j))
        * ((1 - v₀) / N)
        - (∑ j ∈ Finset.range N, rvProfileCumulant α lam (karamataNode v₀ N (j + 1)))
          * ((1 - v₀) / N) = Gap * ((1 - v₀) / N) := by
      rw [← sub_mul, hgapid, hGap]
    linarith [hdarU, hsplit, hheadint, htail, hNb, hdiff]
  -- eventually in X
  have hshells := rvCumulantAverage_shell_bounds hα0 hα1 hL hlam hv₀0 hv₀1 hN0 hc0 hc1
  have hWlow : ∀ᶠ X in atTop, (1 / (2 * (1 - α))) * (X ^ (1 - α) * L X) < rvWeightSum α L X := by
    have hlim := (tendsto_rvWeightSum hα0 hα1 hL).eventually_const_lt
      (show (1 : ℝ) / (2 * (1 - α)) < 1 / (1 - α) by
        rw [div_lt_div_iff₀ (by positivity) hα']
        linarith)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with X hX hX1
    have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
    have hLX : 0 < L X := hL.pos _ hX0
    have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
    have hden : (0 : ℝ) < X ^ (1 - α) * L X := mul_pos hXpow hLX
    rw [lt_div_iff₀ hden] at hX
    linarith [hX]
  have hdpos : ∀ᶠ X in atTop, 0 < rvPrimeCount X := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    have h2 : (2 : ℕ) ≤ ⌊X⌋₊ := Nat.le_floor (by push_cast; linarith)
    have hpc : 0 < Nat.primeCounting ⌊X⌋₊ := by
      have hmono := Nat.monotone_primeCounting h2
      have h1 : 0 < Nat.primeCounting 2 := by decide
      omega
    rw [rvPrimeCount]
    exact_mod_cast hpc
  filter_upwards [hshells, hwb, hWlow, hdpos, eventually_gt_atTop (1 : ℝ)] with
    X hXsh hXhead hXW hXd hX1
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
  have hLX : 0 < L X := hL.pos _ hX0
  have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
  have hden : (0 : ℝ) < X ^ (1 - α) * L X := mul_pos hXpow hLX
  have hWpos : 0 < rvWeightSum α L X := by
    have : (0 : ℝ) < (1 / (2 * (1 - α))) * (X ^ (1 - α) * L X) := by positivity
    linarith [hXW]
  -- the head of the average
  have hheadv : primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 (v₀ * X)
      / rvPrimeCount X ≤ η / 8 := by
    have h1 := rvCumulantAverage_head_le (α := α) hL (lam := lam) (X := X) (Y := v₀ * X)
      hlam hWpos
    have h2 : primeLogSum (rvPrimeWeight α L) 0 (v₀ * X) ≤ εh * (X ^ (1 - α) * L X) := by
      refine le_trans (primeLogSum_head_mono hL (by positivity)
        (mul_le_mul_of_nonneg_right hv₀w hX0.le)) hXhead
    have h3 : lam * rvPrimeCount X * primeLogSum (rvPrimeWeight α L) 0 (v₀ * X)
        / rvWeightSum α L X / rvPrimeCount X ≤ η / 8 := by
      rw [div_div, div_le_iff₀ (by positivity)]
      have hnum : lam * rvPrimeCount X * primeLogSum (rvPrimeWeight α L) 0 (v₀ * X)
          ≤ lam * rvPrimeCount X * (εh * (X ^ (1 - α) * L X)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have hW2 : lam * rvPrimeCount X * (εh * (X ^ (1 - α) * L X))
          ≤ η / 8 * (rvWeightSum α L X * rvPrimeCount X) := by
        have hkey : εh * (2 * (1 - α)) * (lam + 1) = η / 8 := by
          rw [hεh]; field_simp
        have hden2 : X ^ (1 - α) * L X ≤ 2 * (1 - α) * rvWeightSum α L X := by
          have hmul := mul_le_mul_of_nonneg_left hXW.le
            (show (0:ℝ) ≤ 2 * (1 - α) by positivity)
          have hid : 2 * (1 - α) * (1 / (2 * (1 - α)) * (X ^ (1 - α) * L X))
              = X ^ (1 - α) * L X := by field_simp
          linarith [hmul, hid.le, hid.ge]
        have e1 : lam * rvPrimeCount X * (εh * (X ^ (1 - α) * L X))
            ≤ (lam + 1) * εh * (rvPrimeCount X * (X ^ (1 - α) * L X)) := by
          have hnn : (0 : ℝ) ≤ εh * (rvPrimeCount X * (X ^ (1 - α) * L X)) := by positivity
          nlinarith only [hnn]
        have e2 : (lam + 1) * εh * (rvPrimeCount X * (X ^ (1 - α) * L X))
            ≤ (lam + 1) * εh * (rvPrimeCount X * (2 * (1 - α) * rvWeightSum α L X)) := by
          have hnn : (0 : ℝ) ≤ (lam + 1) * εh * rvPrimeCount X := by positivity
          nlinarith only [hden2, hnn]
        have e3 : (lam + 1) * εh * (rvPrimeCount X * (2 * (1 - α) * rvWeightSum α L X))
            = η / 8 * (rvWeightSum α L X * rvPrimeCount X) := by
          rw [← hkey]; ring
        linarith [e1, e2, e3.le, e3.ge]
      linarith [hnum, hW2]
    calc primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 (v₀ * X)
        / rvPrimeCount X
        ≤ lam * rvPrimeCount X * primeLogSum (rvPrimeWeight α L) 0 (v₀ * X)
          / rvWeightSum α L X / rvPrimeCount X := by
          exact div_le_div_of_nonneg_right h1 hXd.le
      _ ≤ η / 8 := h3
  have hheadnn' : 0 ≤ primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t))
      0 (v₀ * X) / rvPrimeCount X := by
    refine div_nonneg ?_ hXd.le
    refine Finset.sum_nonneg fun p _ => ?_
    exact steinhausLogLaplace_nonneg _
  have hdec := rvCumulantAverage_decomp (α := α) (L := L) (lam := lam) hv₀0 hv₀1 hN0 hX0
  rw [Real.dist_eq, abs_lt]
  rw [rvCumulantAverage, hdec, add_div]
  constructor
  · linarith [hXsh.2, hcL, hLo0, hheadnn']
  · linarith [hXsh.1, hcU, hUp0, hheadv]

end

end RHTower
