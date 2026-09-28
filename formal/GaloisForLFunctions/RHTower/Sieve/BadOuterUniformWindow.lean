import GaloisForLFunctions.RHTower.Sieve.MoebiusAveragedMeanSquareAllLengths
import GaloisForLFunctions.RHTower.Sieve.ScaledBadStart

/-!
# The exceptional outer factors, uniformly in the window

Step 1 of the reciprocal-marker argument holds along every window profile `ℓ(y)` squeezed between
`(log y)⁴` and `√y/log y`.  A diagonal argument over profiles turns this into a statement uniform in
the window: for every `ε > 0`, eventually in `y`, *every* window `L` in that range has at most
`1024 ε √y/ϱ² + √y/(log y)²` exceptional outer factors.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **From every profile to uniformity.**  A two-variable property that holds eventually along
every profile `ℓ` with `lo ≤ ℓ ≤ hi` holds eventually, uniformly in `lo x ≤ L ≤ hi x`. -/
theorem eventually_forall_of_forall_profile {P : ℝ → ℝ → Prop} {lo hi : ℝ → ℝ}
    (hle : ∀ᶠ x in atTop, lo x ≤ hi x)
    (h : ∀ ℓ : ℝ → ℝ, (∀ᶠ x in atTop, lo x ≤ ℓ x ∧ ℓ x ≤ hi x) → ∀ᶠ x in atTop, P x (ℓ x)) :
    ∀ᶠ x in atTop, ∀ L, lo x ≤ L → L ≤ hi x → P x L := by
  classical
  by_contra hne
  rw [Filter.not_eventually] at hne
  have hfreq : ∀ a : ℝ, ∃ x, a ≤ x ∧ ∃ L, lo x ≤ L ∧ L ≤ hi x ∧ ¬ P x L := by
    intro a
    obtain ⟨x, hx, hnx⟩ := (Filter.frequently_atTop.1 hne) a
    push Not at hnx
    obtain ⟨L, h1, h2, h3⟩ := hnx
    exact ⟨x, hx, L, h1, h2, h3⟩
  choose xf hxf Lf hLf1 hLf2 hLf3 using hfreq
  -- the thresholds of a strictly increasing sequence of failures
  let a : ℕ → ℝ := fun n => Nat.rec 0 (fun _ y => xf y + 1) n
  have ha_succ : ∀ n, a (n + 1) = xf (a n) + 1 := fun n => rfl
  set xs : ℕ → ℝ := fun n => xf (a n) with hxs
  have hstep : ∀ n, xs n + 1 ≤ xs (n + 1) := by
    intro n
    have := hxf (a (n + 1))
    rw [ha_succ] at this
    simpa [hxs, ha_succ] using this
  have hmono : StrictMono xs := strictMono_nat_of_lt_succ fun n => by linarith [hstep n]
  have hlin : ∀ n : ℕ, xs 0 + n ≤ xs n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => push_cast; linarith [hstep n]
  have htend : Tendsto xs atTop atTop := by
    refine tendsto_atTop_mono hlin ?_
    exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  -- the profile through the failures
  let ℓ : ℝ → ℝ := fun x => if hx : ∃ n, xs n = x then Lf (a (Nat.find hx)) else lo x
  have hℓxs : ∀ n, ℓ (xs n) = Lf (a n) := by
    intro n
    have hx : ∃ k, xs k = xs n := ⟨n, rfl⟩
    have hfind : Nat.find hx = n := hmono.injective (Nat.find_spec hx)
    simp only [ℓ, dif_pos hx, hfind]
  have hprof : ∀ᶠ x in atTop, lo x ≤ ℓ x ∧ ℓ x ≤ hi x := by
    filter_upwards [hle] with x hx
    by_cases hex : ∃ n, xs n = x
    · obtain ⟨n, rfl⟩ := hex
      rw [hℓxs]
      exact ⟨hLf1 (a n), hLf2 (a n)⟩
    · simp only [ℓ, dif_neg hex]
      exact ⟨le_rfl, hx⟩
  obtain ⟨n, hn⟩ := (htend.eventually (h ℓ hprof)).exists
  rw [hℓxs] at hn
  exact hLf3 (a n) hn

/-- The window range is eventually nonempty: `(log y)⁴ ≤ √y/log y`. -/
theorem eventually_logPow_four_le_sqrt_div_log :
    ∀ᶠ y : ℝ in atTop, (Real.log y) ^ (4 : ℕ) ≤ Real.sqrt y / Real.log y := by
  have hlo : (fun y : ℝ => Real.log y ^ (5 : ℝ)) =o[atTop] fun y : ℝ => y ^ ((1 : ℝ) / 2) :=
    isLittleO_log_rpow_rpow_atTop 5 (by norm_num)
  filter_upwards [hlo.bound (show (0 : ℝ) < 1 by norm_num), eventually_ge_atTop (3 : ℝ)]
    with y hy hy3
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog : (1 : ℝ) < Real.log y := by
    rw [Real.lt_log_iff_exp_lt hy0]
    linarith [Real.exp_one_lt_d9]
  have hpow : Real.log y ^ (5 : ℝ) = (Real.log y) ^ (5 : ℕ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsq : y ^ ((1 : ℝ) / 2) = Real.sqrt y := by rw [Real.sqrt_eq_rpow]
  rw [hpow, hsq, one_mul, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hy
  rw [le_div_iff₀ (by linarith)]
  calc (Real.log y) ^ (4 : ℕ) * Real.log y = (Real.log y) ^ (5 : ℕ) := by ring
    _ ≤ Real.sqrt y := hy

open ArithmeticFunction in
/-- **The exceptional outer factors, uniformly in the window.** -/
theorem eventually_card_badOuter_le_uniform {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, ∀ L : ℝ, (Real.log y) ^ (4 : ℕ) ≤ L → L ≤ Real.sqrt y / Real.log y →
      ((badOuter y L).card : ℝ)
        ≤ 1024 * ε * Real.sqrt y / squarefreeDensity ^ (2 : ℕ)
          + Real.sqrt y / (Real.log y) ^ (2 : ℕ) := by
  classical
  refine eventually_forall_of_forall_profile
    (P := fun y L => ((badOuter y L).card : ℝ)
        ≤ 1024 * ε * Real.sqrt y / squarefreeDensity ^ (2 : ℕ)
          + Real.sqrt y / (Real.log y) ^ (2 : ℕ))
    eventually_logPow_four_le_sqrt_div_log ?_
  intro ℓ hℓ
  have hlog : Tendsto (fun y : ℝ => Real.log y) atTop atTop := Real.tendsto_log_atTop
  have hlog1 : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y := hlog.eventually_ge_atTop 1
  have hgrow : Tendsto ℓ atTop atTop := by
    have hpow : Tendsto (fun y : ℝ => (Real.log y) ^ (4 : ℕ)) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp hlog
    refine tendsto_atTop_mono' atTop ?_ hpow
    filter_upwards [hℓ] with y hy using hy.1
  have hsq : ∀ᶠ y : ℝ in atTop, ℓ y ≤ Real.sqrt y := by
    filter_upwards [hℓ, hlog1] with y hy hy1
    exact le_trans hy.2 (div_le_self (Real.sqrt_nonneg _) hy1)
  have hms := averagedMeanSquare_moebius_of_tendsto hgrow hsq
  have hinv : Tendsto (fun y : ℝ => 1 / Real.log y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hratio : Tendsto (fun y : ℝ => ℓ y / Real.sqrt y) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hinv
    · filter_upwards [hℓ, eventually_gt_atTop (0 : ℝ)] with y hy hy0
      have : 0 ≤ ℓ y := le_trans (by positivity) hy.1
      positivity
    · filter_upwards [hℓ, hlog1, eventually_gt_atTop (0 : ℝ)] with y hy hy1 hy0
      have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
      rw [div_le_iff₀ hs0]
      calc ℓ y ≤ Real.sqrt y / Real.log y := hy.2
        _ = 1 / Real.log y * Real.sqrt y := by ring
  have hpoly : Tendsto (fun y : ℝ => (Real.log y) ^ (3 : ℝ) / ℓ y) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hinv
    · filter_upwards [hℓ, hlog1] with y hy hy1
      have : 0 < ℓ y := lt_of_lt_of_le (by positivity) hy.1
      positivity
    · filter_upwards [hℓ, hlog1] with y hy hy1
      have hL0 : (0 : ℝ) < Real.log y := by linarith
      have hℓ0 : 0 < ℓ y := lt_of_lt_of_le (by positivity) hy.1
      have hr3 : (Real.log y) ^ (3 : ℝ) = (Real.log y) ^ (3 : ℕ) := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hr3, div_le_div_iff₀ hℓ0 hL0]
      calc (Real.log y) ^ (3 : ℕ) * Real.log y = (Real.log y) ^ (4 : ℕ) := by ring
        _ ≤ ℓ y := hy.1
        _ = 1 * ℓ y := by ring
  filter_upwards [eventually_fibre_step_one_growing_gen hms hgrow hratio hpoly hε] with y hy
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := outerBlock y (ℓ y)) (p := fun a => goodFibre y (ℓ y) a)
  have hcast : (((outerBlock y (ℓ y)).filter (fun a => goodFibre y (ℓ y) a)).card : ℝ)
      + ((badOuter y (ℓ y)).card : ℝ) = ((outerBlock y (ℓ y)).card : ℝ) := by
    rw [badOuter]
    exact_mod_cast hsplit
  have hgoodeq : ((outerBlock y (ℓ y)).filter (fun a => goodFibre y (ℓ y) a))
      = ((outerBlock y (ℓ y)).filter (fun a =>
          (3 / 16) * squarefreeDensity * (fibreLen y (ℓ y) a : ℝ)
              ≤ (((Finset.Ioc (fibreStartIdx y a)
                  (fibreStartIdx y a + fibreLen y (ℓ y) a)).filter
                  (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * squarefreeDensity * (fibreLen y (ℓ y) a : ℝ)
              ≤ (((Finset.Ioc (fibreStartIdx y a)
                  (fibreStartIdx y a + fibreLen y (ℓ y) a)).filter
                  (fun n => moebius n = -1)).card : ℝ))) := by
    refine Finset.filter_congr fun a _ => ?_
    rw [goodFibre]
  rw [hgoodeq] at hcast
  show ((badOuter y (ℓ y)).card : ℝ) ≤ _
  linarith [hy, hcast]

end RHTower.Sieve
