import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheHyperplaneGapIsTheSelectiveMargin

/-!
# A margin needs harmonic correlation

The prime forms `P_N(x)` and `P_N(ωx)` of a sign gauge `ω² = 1` are unitarily equivalent; their
tops point along the pole `b_n = n^{−1/2}` and along `ω_n b_n`. The pole hyperplane cuts off the
first. It cuts off the second only as far as the two directions correlate, and that correlation
is the harmonic sum `S_N(ω) = Σ_{n ≤ N} ω(n)/n` against `H_N = Σ_{n ≤ N} 1/n`.

* **The ceiling witness** (`eventually_exists_gauge_ceiling_witness`): if `S_N(ω)² = o(log N)`,
  then for every `ε > 0`, eventually, the projection of `ωb` onto the pole hyperplane has
  `P_N(ωx) ≥ (log N − γ − ε)|x|²`. The cost of the projection is `O(S_N² + 1)`, read off the
  ground-state identity polarized at the pole (RenormalizedArithmeticPotentialTheory).
* **No margin without correlation** (`not_hasHyperplaneGap_of_harmonicSum_small`): such a gauge has
  no positive hyperplane gap. Bounded harmonic sums suffice
  (`not_hasHyperplaneGap_of_abs_harmonicSum_le`), which recovers the Liouville twin.
* **Contrapositive** (`frequently_harmonicSum_sq_ge_of_hasHyperplaneGap`): a sign gauge with a
  positive margin has `S_N(ω)² ≥ c log N` for some `c > 0` and infinitely many `N`.

So the margin `2 log 2` of `ζ` (`S_N = H_N`) is carried by its correlation with the pole, and every
sign gauge that decorrelates from it faster than `√log N` is at the ceiling.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

theorem abs_eq_one_of_mul_self_eq_one {a : ℝ} (h : a * a = 1) : |a| = 1 := by
  have h2 : |a| * |a| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg a]

/-- **The ceiling witness.** If `S_N(ω)²/log N → 0`, then for every `ε > 0`, eventually in `N`,
some nonzero `x` on the pole hyperplane has `P_N(ωx) ≥ (log N − γ − ε)|x|²`. The witness is the
gauge's top `ω_n n^{−1/2}` projected onto the hyperplane. -/
theorem eventually_exists_gauge_ceiling_witness {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hS : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ω n / n) ^ 2 / Real.log N) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧
      0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
      (Real.log N - γ - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ atomicWeilForm N (fun n => ω n * x n) := by
  obtain ⟨N₂, hN₂⟩ := eventually_atomicWeilForm_truncPole_ge (show 0 < ε / 2 by positivity)
  set C₀ := Real.log 4 + 4
  set B := Real.log 4 + 4 + Real.log 2 + γ
  have hC₀ : 0 ≤ C₀ := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hB : 0 ≤ B := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  set κ := 4 + C₀ + 2 * γ
  have hκ : 0 < κ := by positivity
  set η := ε / (4 * κ)
  have hη : 0 < η := by positivity
  have hηκ : η * κ = ε / 4 := by simp only [η]; field_simp
  -- eventually `S_N² ≤ η log N`
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp (hS.eventually (Iic_mem_nhds hη))
  -- eventually `log N` exceeds what the projection costs
  obtain ⟨N₃, hN₃⟩ : ∃ N₃ : ℕ, ∀ N, N₃ ≤ N → γ + ε ≤ Real.log N ∧ 4 * B ^ 2 / ε ≤ Real.log N ∧
      3 + η ≤ Real.log N := by
    obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop |>.eventually_ge_atTop
        (max (γ + ε) (max (4 * B ^ 2 / ε) (3 + η))))
    exact ⟨N₃, fun N hN => by
      have := hN₃ N hN
      simp only [Function.comp] at this
      exact ⟨(le_max_left _ _).trans this, ((le_max_left _ _).trans (le_max_right _ _)).trans this,
        ((le_max_right _ _).trans (le_max_right _ _)).trans this⟩⟩
  refine ⟨max N₂ (max N₃ N₄), fun N hN => ?_⟩
  have hN2 : N₂ ≤ N := le_of_max_le_left hN
  have hN3 : N₃ ≤ N := (le_max_left _ _).trans (le_of_max_le_right hN)
  have hN4 : N₄ ≤ N := (le_max_right _ _).trans (le_of_max_le_right hN)
  obtain ⟨hLγ, hLB, hL3⟩ := hN₃ N hN3
  have hηL : 0 < Real.log N := by linarith
  have hN1 : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    rw [this, Nat.cast_zero, Real.log_zero] at hηL
    linarith
  -- the pole, its harmonic mass and the harmonic sum of the gauge
  set b := truncPole N
  set H := ∑ n ∈ Icc 1 N, (1 : ℝ) / n
  set S := ∑ n ∈ Icc 1 N, ω n / n
  set L := Real.log N
  have hSL : S ^ 2 ≤ η * L := by
    have h := hN₄ N hN4
    rw [Set.mem_Iic, div_le_iff₀ hηL] at h
    exact h
  have hb2 : ∀ n ∈ Icc 1 N, b n ^ 2 = 1 / n := fun n hn => by
    simp only [b, truncPole, if_pos (mem_Icc.mp hn).2, poleVector_sq]
  have hbsq : ∑ n ∈ Icc 1 N, b n ^ 2 = H := sum_congr rfl hb2
  have hbs : ∀ n ∈ Icc 1 N, b n / Real.sqrt n = 1 / n := fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [b, truncPole, if_pos (mem_Icc.mp hn).2, poleVector]
    rw [div_div, Real.mul_self_sqrt hn0.le]
  have hHL : L ≤ H := by
    have h := log_add_one_le_harmonic N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    have : L ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log (by exact_mod_cast hN1) (by linarith)
    simp only [H, one_div]
    linarith
  have hH3 : 3 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  set s := S / H
  -- the witness: the gauge's top projected onto the pole hyperplane
  set x : ℕ → ℝ := fun n => (ω n - s) * b n
  have horth : ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 := by
    have : ∀ n ∈ Icc 1 N, x n / Real.sqrt n = ω n / n - s * (1 / n) := fun n hn => by
      rw [show x n / Real.sqrt n = (ω n - s) * (b n / Real.sqrt n) by simp only [x]; ring,
        hbs n hn]
      ring
    rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum]
    show S - s * H = 0
    rw [div_mul_cancel₀ S hH0.ne', sub_self]
  have hxsq : ∑ n ∈ Icc 1 N, x n ^ 2 = H - S ^ 2 / H := by
    have : ∀ n ∈ Icc 1 N, x n ^ 2 = 1 / n - 2 * s * (ω n / n) + s ^ 2 * (1 / n) :=
      fun n hn => by
        have hl := hω n
        simp only [x]
        rw [mul_pow, hb2 n hn]
        have : (ω n - s) ^ 2 = 1 - 2 * s * ω n + s ^ 2 := by linear_combination hl
        rw [this]
        ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
    simp only [s]
    field_simp
    ring
  have hSH : S ^ 2 / H < H := by
    rw [div_lt_iff₀ hH0]
    nlinarith [mul_lt_mul_of_pos_right (show η < L by linarith) hηL,
      mul_le_mul hHL hHL hηL.le hH0.le]
  have hxpos : 0 < ∑ n ∈ Icc 1 N, x n ^ 2 := by rw [hxsq]; linarith
  refine ⟨x, horth, hxpos, ?_⟩
  -- the gauge of the witness is the pole minus `s` times the gauge's top
  set u : ℕ → ℝ := fun n => -s * (ω n * b n)
  have hlx : (fun n => ω n * x n) = fun n => b n + u n := by
    funext n
    have hl := hω n
    simp only [x, u]
    linear_combination b n * hl
  rw [hlx, atomicWeilForm_truncPole_add N u]
  -- the three pieces
  have hPb : (L - γ - ε / 2) * H ≤ atomicWeilForm N b := by
    have := hN₂ N hN2
    rwa [hbsq] at this
  have hlb2 : ∑ n ∈ Icc 1 N, (ω n * b n) ^ 2 = H := by
    rw [← hbsq]
    exact sum_congr rfl fun n _ => by rw [mul_pow, show ω n ^ 2 = 1 by rw [sq, hω], one_mul]
  have hPu : -(s ^ 2 * ((L + C₀) * H)) ≤ atomicWeilForm N u := by
    have hu : u = fun n => (-s) * (ω n * b n) := rfl
    rw [hu, atomicWeilForm_smul, neg_sq]
    have hbot := fixedPoint_bottom_ge (κ := -1) (by norm_num) N (fun n => ω n * b n)
    rw [hlb2] at hbot
    have e : ((-1 : ℝ) - 1 / -1) = 0 := by norm_num
    rw [e, zero_mul, zero_add] at hbot
    have : -((L + C₀) * H) ≤ atomicWeilForm N (fun n => ω n * b n) := by
      simp only [L, C₀] at hbot ⊢; linarith
    have := mul_le_mul_of_nonneg_left this (sq_nonneg s)
    linarith
  have hcross : |∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * b n * u n| ≤
      |s| * ((L + γ) * |S| + B * H) := by
    have e : ∀ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * b n * u n =
        -s * ((L - γ) * (ω n / n) +
          (mertensSum (N / n) + Real.log n - (L - γ)) * (ω n * (1 / n))) := by
      intro n hn
      simp only [u]
      have : b n * b n = 1 / n := by rw [← sq, hb2 n hn]
      have : (mertensSum (N / n) + Real.log n) * b n * (-s * (ω n * b n)) =
          -s * ((mertensSum (N / n) + Real.log n) * ω n * (b n * b n)) := by ring
      rw [this, ‹b n * b n = 1 / n›]
      ring
    rw [sum_congr rfl e, ← mul_sum, abs_mul, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
    rw [sum_add_distrib, ← mul_sum]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      have : |L - γ| ≤ L + γ := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    · refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [show B * H = ∑ n ∈ Icc 1 N, B * (1 / (n : ℝ)) by rw [← mul_sum]]
      refine sum_le_sum fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [abs_mul, abs_mul, abs_eq_one_of_mul_self_eq_one (hω n), one_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
      exact mul_le_mul_of_nonneg_right (abs_row_sub_le hn) (by positivity)
  -- assemble: the projection costs at most `κ S² + B² ≤ ε L / 2`
  have hT1 : s ^ 2 * ((L + C₀) * H) ≤ S ^ 2 * (1 + C₀) := by
    have e : s ^ 2 * ((L + C₀) * H) = S ^ 2 * ((L + C₀) / H) := by
      simp only [s]; field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg S)
    rw [div_le_iff₀ hH0]
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ H by linarith) hC₀]
  have hT2 : 2 * (|s| * ((L + γ) * |S| + B * H)) ≤ S ^ 2 * (3 + 2 * γ) + B ^ 2 := by
    have habs : |s| = |S| / H := by rw [abs_div, abs_of_pos hH0]
    have e : |s| * ((L + γ) * |S| + B * H) = S ^ 2 * ((L + γ) / H) + B * |S| := by
      rw [habs, ← sq_abs S]; field_simp; ring
    rw [e]
    have h1 : (L + γ) / H ≤ 1 + γ := by
      rw [div_le_iff₀ hH0]
      nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ H by linarith) hγ.le]
    have h2 : S ^ 2 * ((L + γ) / H) ≤ S ^ 2 * (1 + γ) := mul_le_mul_of_nonneg_left h1 (sq_nonneg S)
    have h3 : 2 * (B * |S|) ≤ S ^ 2 + B ^ 2 := by
      nlinarith [sq_nonneg (B - |S|), sq_abs S]
    linarith
  have hκS : S ^ 2 * κ ≤ ε / 4 * L := by
    have := mul_le_mul_of_nonneg_right hSL hκ.le
    rw [mul_right_comm, hηκ] at this
    linarith
  have hB2 : B ^ 2 ≤ ε / 4 * L := by
    rw [div_le_iff₀ hε] at hLB
    linarith
  have hxH : ∑ n ∈ Icc 1 N, x n ^ 2 ≤ H := by
    rw [hxsq]
    have : 0 ≤ S ^ 2 / H := div_nonneg (sq_nonneg _) hH0.le
    linarith
  have hcoef : 0 ≤ L - γ - ε := by linarith
  have hcr := (abs_le.mp hcross).1
  have hεL : ε / 2 * L ≤ ε / 2 * H := mul_le_mul_of_nonneg_left hHL (by positivity)
  calc (L - γ - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ (L - γ - ε) * H :=
        mul_le_mul_of_nonneg_left hxH hcoef
    _ ≤ atomicWeilForm N b + atomicWeilForm N u +
        2 * ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * b n * u n := by
        simp only [κ] at hκS
        linarith

/-- **No margin without harmonic correlation**: a sign gauge with `S_N(ω)²/log N → 0` has no
positive hyperplane gap. -/
theorem not_hasHyperplaneGap_of_harmonicSum_small {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hS : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ω n / n) ^ 2 / Real.log N) atTop (𝓝 0))
    {g : ℝ} (hg : 0 < g) : ¬ HasHyperplaneGap ω g := by
  intro h
  set ε := g / 4
  have hε : 0 < ε := by positivity
  obtain ⟨N₁, hN₁⟩ := h ε hε
  obtain ⟨N₂, hN₂⟩ := eventually_exists_gauge_ceiling_witness hω hS hε
  obtain ⟨x, hx, hmass, hge⟩ := hN₂ (max N₁ N₂) (le_max_right _ _)
  have hle := hN₁ (max N₁ N₂) (le_max_left _ _) x hx
  have h2 := le_of_mul_le_mul_right (hge.trans hle) hmass
  simp only [ε] at h2
  linarith

/-- Bounded harmonic sums are `o(√log N)`. -/
theorem tendsto_harmonicSum_sq_div_log_of_abs_le {ω : ℕ → ℝ} {M : ℝ}
    (hM : ∀ N, |∑ n ∈ Icc 1 N, ω n / n| ≤ M) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ω n / n) ^ 2 / Real.log N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun N : ℕ => M ^ 2 / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun N => div_nonneg (sq_nonneg _) (Real.log_natCast_nonneg N)) (fun N => ?_)
  refine div_le_div_of_nonneg_right ?_ (Real.log_natCast_nonneg N)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hM N) 2

/-- A sign gauge with bounded harmonic sums has no positive hyperplane gap. -/
theorem not_hasHyperplaneGap_of_abs_harmonicSum_le {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1) {M : ℝ}
    (hM : ∀ N, |∑ n ∈ Icc 1 N, ω n / n| ≤ M) {g : ℝ} (hg : 0 < g) : ¬ HasHyperplaneGap ω g :=
  not_hasHyperplaneGap_of_harmonicSum_small hω (tendsto_harmonicSum_sq_div_log_of_abs_le hM) hg

/-- The Liouville twin, recovered: `|Σ_{n ≤ N} λ(n)/n| ≤ 2`. -/
theorem not_liouville_hasHyperplaneGap' {g : ℝ} (hg : 0 < g) :
    ¬ HasHyperplaneGap liouvilleSign g :=
  not_hasHyperplaneGap_of_abs_harmonicSum_le liouvilleSign_mul_self abs_sum_liouvilleSign_div_le hg

/-- **A positive margin forces harmonic correlation**: if a sign gauge has a positive hyperplane
gap, then `S_N(ω)² ≥ c log N` for some `c > 0` and infinitely many `N`. -/
theorem frequently_harmonicSum_sq_ge_of_hasHyperplaneGap {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    {g : ℝ} (hg : 0 < g) (h : HasHyperplaneGap ω g) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ N : ℕ in atTop,
      c * Real.log N ≤ (∑ n ∈ Icc 1 N, ω n / n) ^ 2 := by
  by_contra hne
  simp only [not_exists, not_and, not_frequently, not_le] at hne
  refine not_hasHyperplaneGap_of_harmonicSum_small hω ?_ hg h
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hne (δ / 2) (by positivity)).and
    (eventually_gt_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hlt, h1⟩ := hN₀ N hN
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast h1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (sq_nonneg _) hL.le), div_lt_iff₀ hL]
  linarith

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
