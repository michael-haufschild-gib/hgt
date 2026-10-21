import GaloisForLFunctions.TransHorizonIncidenceMechanics.FiniteKernelsRepairAPositiveDriftOnlyAtItsPole

/-!
# Critical Wiener kernels repair a positive drift only at its pole

The pole law of finite kernels extends to the whole critical Wiener algebra
`Σ_j |k(j)| j^{-1/2} < ∞`. For such `k` and a nonnegative drift weight `q`
(`n Σ_{(n,2n]} q(d)/d ≥ κ n^{1−ε}`, `0 < ε ≤ 1/2`):

* the Mellin pairings obey `Φ_{k⋆q}(σ) = K(σ) Φ_q(σ) + m_q Φ_k(σ)` with `K(σ) = Σ_j k(j) j^{-σ}`: the
  double series `Σ_n Σ_j k(j) A_q(⌊n/j⌋) Δ_n(σ)` converges absolutely (`|A_q(m)| ≤ C m^{1−ε}`), and each
  dilation `k ↦ jk` contributes `j^{-σ} Φ_q(σ)`;
* the prefix of the kernel itself has pronic norm at most `(√2 + 1) Σ_j |k(j)| j^{-1/2}`, so
  `|Φ_k(σ)| = O((σ − 1/2)^{-1/2})`, as is `|Φ_{k⋆q}(σ)|` when the receiver of `k ⋆ q` is bounded;
* `Φ_q(1 − ε + δ) ≍ −δ^{-1}`, and `K(σ) → K(1 − ε)` by dominated convergence.

Hence **if `K(1 − ε) ≠ 0`, the receiver of `k ⋆ q` is unbounded**: no kernel of the critical Wiener
algebra pays a positive drift unless its Dirichlet series vanishes at the pole.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- A sequence of bounded pronic energy pairs absolutely with the Mellin cells for `σ > 1/2`. -/
theorem summable_mul_mellinCell_of_energy {σ E : ℝ} (hσ : 1 / 2 < σ) {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hE : ∀ T, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) :
    Summable (fun n => f n * mellinCell σ n) := by
  have hσ0 : 0 < σ := by linarith
  have hE0 : 0 ≤ E := by simpa using hE 0
  set B := 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))
  have hZ := Real.summable_nat_rpow.mpr (show -(2 * σ) < -1 by linarith)
  have hcells : ∀ T, ∑ n ∈ Icc 1 T, mellinCell σ n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) ≤ B := by
    intro T
    calc ∑ n ∈ Icc 1 T, mellinCell σ n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ Icc 1 T, 2 * σ ^ 2 * (n : ℝ) ^ (-(2 * σ)) :=
          sum_le_sum fun n hn => mellinCell_sq_mul_pronic_le hσ0 (mem_Icc.mp hn).1
      _ = 2 * σ ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * σ)) := by rw [mul_sum]
      _ ≤ B := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (hZ.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _).trans
            (RHTower.Sieve.tsum_nat_rpow_neg_le (by linarith))
  refine Summable.of_abs (summable_of_sum_range_le (c := Real.sqrt E * Real.sqrt B)
    (fun n => abs_nonneg _) fun T => ?_)
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp; positivity
  obtain ⟨T, rfl⟩ : ∃ m, T = m + 1 := ⟨T - 1, by omega⟩
  rw [dampedSign_sum_range_succ_eq_add_Icc, hf0, zero_mul, abs_zero, zero_add,
    ← Real.sqrt_mul hE0]
  refine Real.le_sqrt_of_sq_le ?_
  set w : ℕ → ℝ := fun n => (n : ℝ) * ((n : ℝ) + 1)
  have hw : ∀ n ∈ Icc 1 T, 0 < w n := fun n hn => by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [w]; positivity
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 T) (fun n => |f n| / Real.sqrt (w n))
    (fun n => |mellinCell σ n| * Real.sqrt (w n))
  have h1 : ∑ n ∈ Icc 1 T, |f n| / Real.sqrt (w n) * (|mellinCell σ n| * Real.sqrt (w n)) =
      ∑ n ∈ Icc 1 T, |f n * mellinCell σ n| := sum_congr rfl fun n hn => by
    have := (Real.sqrt_pos.mpr (hw n hn)).ne'
    rw [abs_mul]; field_simp
  have h2 : ∑ n ∈ Icc 1 T, (|f n| / Real.sqrt (w n)) ^ 2 =
      ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := sum_congr rfl fun n hn => by
    rw [div_pow, sq_abs, Real.sq_sqrt (hw n hn).le]
  have h3 : ∑ n ∈ Icc 1 T, (|mellinCell σ n| * Real.sqrt (w n)) ^ 2 =
      ∑ n ∈ Icc 1 T, mellinCell σ n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) := sum_congr rfl fun n hn => by
    rw [mul_pow, sq_abs, Real.sq_sqrt (hw n hn).le]
  rw [h1, h2, h3] at hcs
  exact hcs.trans (mul_le_mul (hE T) (hcells T) (sum_nonneg fun n _ => by positivity) hE0)

/-- The prefix of a critical Wiener kernel has pronic energies at most `((√2 + 1) W)²`. -/
theorem energy_weightCenteredPrefix_critical_le {k : ℕ → ℝ} (hk : CriticalWiener k) (T : ℕ) :
    ∑ n ∈ Icc 1 T, weightCenteredPrefix k (∑' j : ℕ, k j / j) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      ((Real.sqrt 2 + 1) * ∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
  have h := pronicNorm_weightCenteredPrefix_le_critical hk T
  rw [pronicNorm, Real.sqrt_le_iff] at h
  exact h.2

/-- **Critical Wiener kernels repair a positive drift only at its pole.** Let `0 < ε ≤ 1/2`, let
`q ≥ 0` lie in the damped class with drift `n Σ_{(n,2n]} q(d)/d ≥ κ n^{1−ε}` eventually, and let
`k` lie in the critical Wiener algebra. If `Σ_j k(j) j^{-(1−ε)} ≠ 0`, the receiver of `k ⋆ q` is
unbounded. -/
theorem not_receiverBounded_dirichletConv_of_drift_critical {K ε κ : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) {q : ℕ → ℝ} (hq : ∀ d, 0 ≤ q d) (hclass : DampedClass K ε q) (hκ : 0 < κ)
    (hdrift : ∀ᶠ n : ℕ in atTop, κ * (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), q d / d)
    {k : ℕ → ℝ} (hk : CriticalWiener k) (hK : ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε)) ≠ 0) :
    ¬ ReceiverBounded (RHTower.dirichletConv k q) := by
  rintro ⟨E, hE⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hdrift
  set N₀ := max N₁ 1
  have hN₀ : 1 ≤ N₀ := le_max_right _ _
  have hdrift' : ∀ n, N₀ ≤ n → κ * (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), q d / d :=
    fun n hn => hN₁ n ((le_max_left _ _).trans hn)
  have hK0 := nonneg_of_dampedClass hclass
  -- the means
  have hqs : Summable (fun d : ℕ => q d / d) := summable_div_of_dampedClass hε hclass
  set mq := ∑' d : ℕ, q d / d
  set mk := ∑' j : ℕ, k j / j
  have hmean : ∑' n : ℕ, RHTower.dirichletConv k q n / n = mk * mq :=
    (hasSum_dirichletConv_div hk.summable_abs_div.of_abs.hasSum hqs.hasSum hk.summable_abs_div
      hqs.abs).tsum_eq
  have hE' : ∀ T, ∑ n ∈ Icc 1 T, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)) ≤ E := fun T => by
    have := hE T; rwa [hmean] at this
  -- the prefixes
  set A := weightCenteredPrefix q mq
  set Ak := weightCenteredPrefix k mk
  set W := ∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))
  have hW : 0 ≤ W := tsum_nonneg fun j => by positivity
  set Cq := K * (1 + 1 / (1 - ε) + 1 / ε)
  have hCq : 0 ≤ Cq := by
    have : 0 < 1 - ε := by linarith
    positivity
  have hA0 : A 0 = 0 := weightCenteredPrefix_zero _ _
  have hAk0 : Ak 0 = 0 := weightCenteredPrefix_zero _ _
  have hAbound : ∀ n, 1 ≤ n → |A n| ≤ Cq * (n : ℝ) ^ (1 - ε) := fun n hn =>
    abs_weightCenteredPrefix_le_of_dampedClass hε (by linarith) hclass hn
  -- `|A_q(⌊n/j⌋)| ≤ C n^{1−ε} j^{-(1−ε)}`
  have hAdiv : ∀ n j, |A (n / j)| ≤ Cq * ((n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε))) := by
    intro n j
    rcases Nat.eq_zero_or_pos (n / j) with h0 | h1
    · rw [h0, hA0, abs_zero]
      exact mul_nonneg hCq (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    · have hj : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
      refine (hAbound _ h1).trans (mul_le_mul_of_nonneg_left ?_ hCq)
      calc (((n / j : ℕ) : ℝ)) ^ (1 - ε) ≤ ((n : ℝ) / j) ^ (1 - ε) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le (by linarith)
        _ = (n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε)) := by
            rw [Real.div_rpow (Nat.cast_nonneg _) hj0.le, Real.rpow_neg hj0.le, div_eq_mul_inv]
  have hconv : ∀ n, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n =
      ∑' j : ℕ, k j * A (n / j) + mq * Ak n := fun n => by
    rw [weightCenteredPrefix_dirichletConv, tsum_eq_sum (s := Icc 1 n) fun j hj => ?_]
    rw [mem_Icc, not_and_or] at hj
    rcases hj with hj | hj
    · rw [show j = 0 by omega, Nat.div_zero, hA0, mul_zero]
    · rw [Nat.div_eq_of_lt (by omega), hA0, mul_zero]
  -- the dominating weights of the kernel
  have hkσ : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 - ε))) := by
    refine hk.of_nonneg_of_le (fun j => by positivity) fun j => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [Nat.cast_zero, Real.zero_rpow (show -(1 - ε) ≠ 0 by linarith),
        Real.zero_rpow (show -(1 / 2 : ℝ) ≠ 0 by norm_num), mul_zero, le_refl]
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)
  set Kσ : ℝ → ℝ := fun δ => ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε + δ))
  set M := |mq| * ((Real.sqrt 2 + 1) * W)
  have hkey : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      |Kσ δ| * (κ * (1 - ε + δ) / 2 * ((N₀ : ℝ) + 1) ^ (-δ)) ≤
        (Real.sqrt E + M) * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) := by
    intro δ hδ hδ2
    set σ := 1 - ε + δ
    have hσ : 1 / 2 < σ := by simp only [σ]; linarith
    have hσ0 : 0 < σ := by linarith
    have hsA : Summable (fun n => A n * mellinCell σ n) :=
      summable_mul_mellinCell hσ0 (show 1 - ε < σ by simp only [σ]; linarith) hA0 hAbound
    have hsAk : Summable (fun n => Ak n * mellinCell σ n) :=
      summable_mul_mellinCell_of_energy hσ hAk0 (energy_weightCenteredPrefix_critical_le hk)
    -- the double series
    set F : ℕ → ℕ → ℝ := fun j n => k j * (A (n / j) * mellinCell σ n)
    have hZn := Real.summable_nat_rpow.mpr (show -(ε + σ) < -1 by simp only [σ]; linarith)
    have hFbound : ∀ j n, |F j n| ≤ (|k j| * (j : ℝ) ^ (-(1 - ε))) *
        (Cq * σ * (n : ℝ) ^ (-(ε + σ))) := by
      intro j n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [F, Nat.zero_div, hA0, zero_mul, mul_zero, abs_zero]
        exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have hb := (mellinCell_bounds hσ0 hn).2
      have hΔ := mellinCell_nonneg hσ0 hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [F]
      rw [abs_mul, abs_mul, abs_of_nonneg hΔ]
      have hexp : (n : ℝ) ^ (1 - ε) * (n : ℝ) ^ (-σ - 1) = (n : ℝ) ^ (-(ε + σ)) := by
        rw [← Real.rpow_add hn0]; congr 1; ring
      calc |k j| * (|A (n / j)| * mellinCell σ n)
          ≤ |k j| * (Cq * ((n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε))) * (σ * (n : ℝ) ^ (-σ - 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hAdiv n j) hb hΔ (by positivity))
              (abs_nonneg _)
        _ = (|k j| * (j : ℝ) ^ (-(1 - ε))) * (Cq * σ * ((n : ℝ) ^ (1 - ε) * (n : ℝ) ^ (-σ - 1))) := by
            ring
        _ = _ := by rw [hexp]
    have hFsum : Summable (Function.uncurry F) := by
      refine Summable.of_norm_bounded ((hkσ.mul_of_nonneg (hZn.mul_left (Cq * σ))
        (fun j => by positivity) (fun n => by positivity))) fun x => ?_
      rw [Real.norm_eq_abs]; exact hFbound x.1 x.2
    have hFj : ∀ j, Summable (F j) := fun j =>
      Summable.of_norm_bounded ((hZn.mul_left (Cq * σ)).mul_left (|k j| * (j : ℝ) ^ (-(1 - ε))))
        fun n => by rw [Real.norm_eq_abs]; exact hFbound j n
    have hFn : ∀ n, Summable (fun j => F j n) := fun n =>
      Summable.of_norm_bounded (hkσ.mul_right (Cq * σ * (n : ℝ) ^ (-(ε + σ))))
        fun j => by rw [Real.norm_eq_abs]; exact hFbound j n
    have hFnsum : Summable (fun n => ∑' j, F j n) := by
      refine Summable.of_norm_bounded ((hZn.mul_left (Cq * σ)).mul_left
        (∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 - ε)))) fun n => ?_
      rw [Real.norm_eq_abs]
      have h := tsum_of_norm_bounded ((hkσ.mul_right (Cq * σ * (n : ℝ) ^ (-(ε + σ)))).hasSum)
        fun j => by rw [Real.norm_eq_abs]; exact hFbound j n
      rw [Real.norm_eq_abs, tsum_mul_right] at h
      linarith
    have hsplit : ∀ n, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n *
        mellinCell σ n = ∑' j, F j n + mq * (Ak n * mellinCell σ n) := fun n => by
      rw [hconv, add_mul, ← tsum_mul_right]
      congr 1
      · exact tsum_congr fun j => by simp only [F]; ring
      · ring
    have hsc : Summable (fun n =>
        weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n * mellinCell σ n) := by
      simp_rw [hsplit]; exact hFnsum.add (hsAk.mul_left _)
    have hlaw : ∑' n, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n * mellinCell σ n =
        Kσ δ * ∑' n, A n * mellinCell σ n + mq * ∑' n, Ak n * mellinCell σ n := by
      simp_rw [hsplit]
      rw [hFnsum.tsum_add (hsAk.mul_left _), tsum_mul_left, hFsum.tsum_comm' hFj hFn]
      congr 1
      simp only [Kσ, F]
      rw [← tsum_mul_right]
      refine tsum_congr fun j => ?_
      rw [tsum_mul_left]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp only [Nat.div_zero, hA0, zero_mul, tsum_zero, mul_zero, Nat.cast_zero,
          Real.zero_rpow (show -(1 - ε + δ) ≠ 0 by linarith), zero_mul]
      · have hsAj : Summable (fun n => A (n / j) * mellinCell σ n) := by
          have := (hFj j)
          rcases eq_or_ne (k j) 0 with hk0 | hk0
          · refine Summable.of_norm_bounded ((hZn.mul_left (Cq * σ)).mul_left ((j : ℝ) ^ (-(1 - ε))))
              fun n => ?_
            rcases Nat.eq_zero_or_pos n with rfl | hn
            · simp [hA0]; positivity
            have hb := (mellinCell_bounds hσ0 hn).2
            have hΔ := mellinCell_nonneg hσ0 hn
            have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hΔ]
            have hexp : (n : ℝ) ^ (1 - ε) * (n : ℝ) ^ (-σ - 1) = (n : ℝ) ^ (-(ε + σ)) := by
              rw [← Real.rpow_add hn0]; congr 1; ring
            calc |A (n / j)| * mellinCell σ n
                ≤ Cq * ((n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε))) * (σ * (n : ℝ) ^ (-σ - 1)) :=
                  mul_le_mul (hAdiv n j) hb hΔ (by positivity)
              _ = (j : ℝ) ^ (-(1 - ε)) * (Cq * σ * ((n : ℝ) ^ (1 - ε) * (n : ℝ) ^ (-σ - 1))) := by
                  ring
              _ = _ := by rw [hexp]
          · exact (this.mul_left (k j)⁻¹).congr fun n => by simp only [F]; field_simp
        rw [tsum_comp_div_mul_mellinCell hA0 hj hsA hsAj]
        ring
    -- the three bounds
    have hcs := abs_tsum_mul_mellinCell_le hσ (weightCenteredPrefix_zero _ _) hsc hE'
    have hPk := abs_tsum_mul_mellinCell_le hσ hAk0 hsAk (energy_weightCenteredPrefix_critical_le hk)
    rw [Real.sqrt_sq (by positivity)] at hPk
    have hdrift'' := tsum_mul_mellinCell_le_of_drift hq hqs.hasSum hκ.le hε.le (by linarith) hδ
      hN₀ hdrift' hsA
    -- assemble
    set Φ := ∑' n, A n * mellinCell σ n
    set Bσ := Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)))
    have hΦ : (κ * σ / 2) * (((N₀ : ℝ) + 1) ^ (-δ) / δ) ≤ |Φ| := by
      have := neg_le_abs Φ; linarith
    have h2σ0 : 0 < 2 * σ - 1 := by linarith
    have hBnn : 0 ≤ 1 + 1 / (2 * σ - 1) := by positivity
    have hB : Bσ * δ ≤ Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) := by
      rw [show Bσ * δ = Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)) * δ ^ 2) by
        rw [Real.sqrt_mul (x := 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) (by positivity) (δ ^ 2),
          Real.sqrt_sq hδ.le]]
      refine Real.sqrt_le_sqrt ?_
      have h2σ : 2 * δ ≤ 2 * σ - 1 := by simp only [σ]; linarith
      have hinv : 1 / (2 * σ - 1) ≤ 1 / (2 * δ) := one_div_le_one_div_of_le (by positivity) h2σ
      have hσ2 : σ ^ 2 ≤ 9 / 4 := by
        have : σ ≤ 3 / 2 := by simp only [σ]; linarith
        nlinarith
      calc 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)) * δ ^ 2 ≤ 2 * (9 / 4) * (1 + 1 / (2 * δ)) * δ ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul (by linarith) (by linarith) hBnn (by norm_num)
        _ = 9 / 2 * (δ ^ 2 + δ / 2) := by field_simp; ring
    have habs : |Kσ δ| * |Φ| ≤ (Real.sqrt E + M) * Bσ := by
      rw [← abs_mul, show Kσ δ * Φ = (Kσ δ * Φ + mq * ∑' n, Ak n * mellinCell σ n) -
        mq * ∑' n, Ak n * mellinCell σ n by ring, ← hlaw]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul (mq)]
      calc |∑' n, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n * mellinCell σ n| +
            |mq| * |∑' n, Ak n * mellinCell σ n|
          ≤ Real.sqrt E * Bσ + |mq| * ((Real.sqrt 2 + 1) * W * Bσ) :=
            add_le_add hcs (mul_le_mul_of_nonneg_left hPk (abs_nonneg _))
        _ = (Real.sqrt E + M) * Bσ := by simp only [M]; ring
    have hKabs := abs_nonneg (Kσ δ)
    have hM : 0 ≤ Real.sqrt E + M := by positivity
    calc |Kσ δ| * (κ * (1 - ε + δ) / 2 * ((N₀ : ℝ) + 1) ^ (-δ))
        = δ * (|Kσ δ| * ((κ * σ / 2) * (((N₀ : ℝ) + 1) ^ (-δ) / δ))) := by
          simp only [σ]; field_simp
      _ ≤ δ * (|Kσ δ| * |Φ|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦ hKabs) hδ.le
      _ ≤ δ * ((Real.sqrt E + M) * Bσ) := mul_le_mul_of_nonneg_left habs hδ.le
      _ = (Real.sqrt E + M) * (Bσ * δ) := by ring
      _ ≤ (Real.sqrt E + M) * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) :=
          mul_le_mul_of_nonneg_left hB hM
  -- the limit `δ → 0⁺`
  have hKlim : Tendsto Kσ (𝓝[>] 0) (𝓝 (∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε)))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun j => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)))
      hk (fun j => ?_) ?_
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0, k 0 * ((0 : ℕ) : ℝ) ^ (-(1 - ε + δ)) =
            k 0 * ((0 : ℕ) : ℝ) ^ (-(1 - ε)) := by
          filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
          rw [Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
        exact tendsto_const_nhds.congr' (EventuallyEq.symm hev)
      · have hj0 : (j : ℝ) ≠ 0 := by positivity
        have hc : Continuous (fun δ : ℝ => (j : ℝ) ^ (-(1 - ε + δ))) :=
          continuous_const.rpow (by fun_prop) fun _ => Or.inl hj0
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        simpa using this.const_mul (k j)
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) j
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp only [Nat.cast_zero, Real.zero_rpow (show -(1 - ε + δ) ≠ 0 by linarith),
          Real.zero_rpow (show -(1 / 2 : ℝ) ≠ 0 by norm_num), abs_zero, le_refl]
      · rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)
  have hN0 : ((N₀ : ℝ) + 1) ≠ 0 := by positivity
  have hPlim : Tendsto (fun δ : ℝ => ((N₀ : ℝ) + 1) ^ (-δ)) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun δ : ℝ => ((N₀ : ℝ) + 1) ^ (-δ)) :=
      continuous_const.rpow (by fun_prop) fun _ => Or.inl hN0
    simpa using hc.tendsto 0
  set L₀ := |∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε))| * (κ * (1 - ε + 0) / 2 * 1)
  have hL₀ : 0 < L₀ := by
    have : 0 < 1 - ε := by linarith
    simp only [L₀]; positivity
  have hLHS : Tendsto (fun δ : ℝ => |Kσ δ| * (κ * (1 - ε + δ) / 2 * ((N₀ : ℝ) + 1) ^ (-δ)))
      (𝓝[>] 0) (𝓝 L₀) :=
    (continuous_abs.tendsto _ |>.comp hKlim).mul (tendsto_nhdsWithin_of_tendsto_nhds
      ((((tendsto_const_nhds.add tendsto_id).const_mul κ).div_const 2).mul hPlim))
  have hRHS : Tendsto (fun δ : ℝ => (Real.sqrt E + M) * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)))
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun δ : ℝ => (Real.sqrt E + M) * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2))) := by
      fun_prop
    simpa using hc.tendsto 0
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), L₀ / 2 < |Kσ δ| * (κ * (1 - ε + δ) / 2 * ((N₀ : ℝ) + 1) ^ (-δ)) ∧
      (Real.sqrt E + M) * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) < L₀ / 2 ∧ 0 < δ ∧ δ ≤ 1 / 2 := by
    refine (hLHS.eventually (lt_mem_nhds (by linarith))).and
      ((tendsto_nhdsWithin_of_tendsto_nhds hRHS |>.eventually (gt_mem_nhds (by linarith))).and
      ((eventually_nhdsWithin_of_forall fun δ hδ => hδ).and ?_))
    exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨δ, h1, h2, hδ, hδ2⟩ := hev.exists
  linarith [hkey δ hδ hδ2]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
