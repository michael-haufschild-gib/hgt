import GaloisForLFunctions.RHTower.JointAncestryPrimeSumComparison

/-!
# Twisted reciprocal prime sums at exponent one

For `Δ ≠ 0` there is `κ < 1` with `‖Σ_{p ≤ N} p^{−1+iΔ}‖ ≤ κ Σ_{p ≤ N} p^{−1}` for all large `N`
(`exists_twisted_jasPrimeRpowSum_one_le`).  Together with the case `0 < α < 1` this gives the
twisted comparison for every `0 < α ≤ 1` (`exists_twisted_jasPrimeRpowSum_le_of_le_one`).

Abel summation against `g(k) = k^{−1/2}` writes both sums through the prime sums at exponent `½`:
`Σ_{k ≤ N} a_k g(k) = A(N) g(N) + Σ_{k < N} A(k)(g(k) − g(k+1))`.  The asymptotics
`Σ_{p ≤ k} p^{−s} = k^{1−s}/((1−s) log k) + o(k^{1/2}/log k)` at `s = ½ − iΔ` and at `s = ½`
bound the twisted partial sums above by `(m + ε) k^{1/2}/log k` with `m = 1/|½ + iΔ| < 2`.  They
bound the untwisted ones below by `(2 − ε) k^{1/2}/log k`.  So both sums are compared through the
same weights `ω_k = (g(k) − g(k+1)) k^{1/2}/log k`, whose sum diverges because `Σ_{p ≤ N} p^{−1}`
does.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- **Abel summation.** -/
theorem sum_range_mul_eq_abel {R : Type*} [CommRing R] (f g : ℕ → R) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), f k * g k =
      (∑ j ∈ Finset.range (N + 1), f j) * g N +
        ∑ k ∈ Finset.range N, (∑ j ∈ Finset.range (k + 1), f j) * (g k - g (k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 : ∑ j ∈ Finset.range (N + 1 + 1), f j = (∑ j ∈ Finset.range (N + 1), f j) + f (N + 1) :=
      Finset.sum_range_succ _ _
    have h2 : ∑ k ∈ Finset.range (N + 1), (∑ j ∈ Finset.range (k + 1), f j) * (g k - g (k + 1)) =
        ∑ k ∈ Finset.range N, (∑ j ∈ Finset.range (k + 1), f j) * (g k - g (k + 1)) +
          (∑ j ∈ Finset.range (N + 1), f j) * (g N - g (N + 1)) :=
      Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ (fun k => f k * g k) (N + 1), ih, h1, h2]
    ring

/-- The Abel weight `g(k) = k^{−1/2}`. -/
def jasHalfWeight (k : ℕ) : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))

theorem jasHalfWeight_nonneg (k : ℕ) : 0 ≤ jasHalfWeight k :=
  Real.rpow_nonneg (Nat.cast_nonneg k) _

theorem jasHalfWeight_succ_le {k : ℕ} (hk : 1 ≤ k) : jasHalfWeight (k + 1) ≤ jasHalfWeight k := by
  unfold jasHalfWeight
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hk) (by push_cast; linarith) (by norm_num)

theorem jasHalfWeight_mul_rpow {k : ℕ} (hk : 1 ≤ k) :
    jasHalfWeight k * (k : ℝ) ^ (1 / 2 : ℝ) = 1 := by
  unfold jasHalfWeight
  rw [← Real.rpow_add (by exact_mod_cast hk)]
  norm_num

/-- The twisted exponent `s = ½ − iΔ`. -/
def jasHalfTwist (Δ : ℝ) : ℂ := 1 / 2 - (Δ : ℂ) * I

theorem jasHalfTwist_re (Δ : ℝ) : (jasHalfTwist Δ).re = 1 / 2 := by simp [jasHalfTwist]

theorem norm_one_sub_jasHalfTwist_gt {Δ : ℝ} (hΔ : Δ ≠ 0) : 1 / 2 < ‖1 - jasHalfTwist Δ‖ := by
  have h : 1 - jasHalfTwist Δ = ((1 / 2 : ℝ) : ℂ) + (Δ : ℂ) * I := by
    simp [jasHalfTwist]; ring
  rw [h, Complex.norm_add_mul_I]
  have hΔ2 : 0 < Δ ^ 2 := by positivity
  rw [show (1 / 2 : ℝ) = Real.sqrt ((1 / 2) ^ 2) by
    rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by positivity) (by linarith)

/-- The twisted prime coefficients `1_P(k) k^{−s}`. -/
def jasTwistCoeff (Δ : ℝ) (k : ℕ) : ℂ := if k.Prime then (k : ℂ) ^ (-jasHalfTwist Δ) else 0

/-- The untwisted prime coefficients `1_P(k) k^{−1/2}`. -/
def jasHalfCoeff (k : ℕ) : ℝ := if k.Prime then (k : ℝ) ^ (-(1 / 2 : ℝ)) else 0

theorem sum_range_jasTwistCoeff (Δ : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), jasTwistCoeff Δ j =
      ∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-jasHalfTwist Δ) := by
  unfold jasTwistCoeff
  rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]

theorem sum_range_jasHalfCoeff (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), jasHalfCoeff j =
      ∑ p ∈ Nat.primesLE k, (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold jasHalfCoeff
  rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]

theorem jasHalfCoeff_nonneg (k : ℕ) : 0 ≤ jasHalfCoeff k := by
  unfold jasHalfCoeff
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg k) _
  · exact le_rfl

/-- `k^{−s} k^{−1/2} = k^{−1} k^{iΔ}`. -/
theorem cpow_jasHalfTwist_mul_jasHalfWeight (Δ : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℂ) ^ (-jasHalfTwist Δ) * (jasHalfWeight n : ℂ) =
      (Real.exp (-1 * Real.log n) : ℂ) * cexp (((Δ * Real.log n : ℝ) : ℂ) * I) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn'.le]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), hlog, jasHalfWeight,
    Real.rpow_def_of_pos hn', Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  simp only [jasHalfTwist]
  push_cast
  ring

theorem rpow_mul_jasHalfWeight {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) * jasHalfWeight n = Real.exp (-1 * Real.log n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [jasHalfWeight, ← Real.rpow_add hn', Real.rpow_def_of_pos hn']
  congr 1
  ring

theorem twisted_sum_eq_abel (Δ : ℝ) (N : ℕ) :
    ∑ p ∈ jasPrimesUpTo N, (Real.exp (-1 * Real.log p) : ℂ) * cexp (((Δ * Real.log p : ℝ) : ℂ) * I) =
      ∑ k ∈ Finset.range (N + 1), jasTwistCoeff Δ k * (jasHalfWeight k : ℂ) := by
  rw [sum_jasPrimesUpTo (fun n : ℕ => (Real.exp (-1 * Real.log n) : ℂ) *
    cexp (((Δ * Real.log n : ℝ) : ℂ) * I)) N, Nat.primesLE, Nat.primesBelow, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold jasTwistCoeff
  split_ifs with hk
  · exact (cpow_jasHalfTwist_mul_jasHalfWeight Δ hk.pos).symm
  · exact (zero_mul _).symm

theorem jasPrimeRpowSum_one_eq_abel (N : ℕ) :
    jasPrimeRpowSum 1 N = ∑ k ∈ Finset.range (N + 1), jasHalfCoeff k * jasHalfWeight k := by
  rw [jasPrimeRpowSum, sum_jasPrimesUpTo (fun n : ℕ => Real.exp (-1 * Real.log n)) N, Nat.primesLE,
    Nat.primesBelow, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold jasHalfCoeff
  split_ifs with hk
  · exact (rpow_mul_jasHalfWeight hk.pos).symm
  · exact (zero_mul _).symm

/-- The twisted partial sums at exponent `½` are eventually `≤ (1/|1 − s| + ε) k^{1/2}/log k`. -/
theorem eventually_norm_sum_primesLE_jasHalfTwist_le (Δ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ‖∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-jasHalfTwist Δ)‖ ≤
      (1 / ‖1 - jasHalfTwist Δ‖ + ε) * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k) := by
  have hre := jasHalfTwist_re Δ
  have h := tendsto_sum_primesLE_cpow_sub_main (s := jasHalfTwist Δ) (by rw [hre]; norm_num)
    (by rw [hre]; norm_num)
  have hs0 : 1 - jasHalfTwist Δ ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp [hre] at this
    norm_num at this
  filter_upwards [h.eventually (ge_mem_nhds hε), eventually_ge_atTop 2] with k hk hk2
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hlog : 0 < Real.log k := Real.log_pos (by linarith)
  have hpow : 0 < (k : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [hre, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, mul_div_assoc] at hk
  have hdiff : ‖∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-jasHalfTwist Δ) -
      ((k : ℝ) : ℂ) ^ (1 - jasHalfTwist Δ) / ((1 - jasHalfTwist Δ) * (Real.log k : ℂ))‖ ≤
        ε * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k) := by
    calc _ = (‖∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-jasHalfTwist Δ) -
          ((k : ℝ) : ℂ) ^ (1 - jasHalfTwist Δ) / ((1 - jasHalfTwist Δ) * (Real.log k : ℂ))‖ *
            (Real.log k / (k : ℝ) ^ (1 / 2 : ℝ))) * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k) := by
          field_simp
      _ ≤ ε * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k) :=
          mul_le_mul_of_nonneg_right hk (by positivity)
  have hmain : ‖((k : ℝ) : ℂ) ^ (1 - jasHalfTwist Δ) / ((1 - jasHalfTwist Δ) * (Real.log k : ℂ))‖ =
      1 / ‖1 - jasHalfTwist Δ‖ * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k) := by
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.norm_real,
      Real.norm_of_nonneg hlog.le]
    have : (1 - jasHalfTwist Δ).re = 1 / 2 := by
      rw [Complex.sub_re, Complex.one_re, hre]; norm_num
    rw [this]
    field_simp
  calc ‖∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-jasHalfTwist Δ)‖
      ≤ ‖((k : ℝ) : ℂ) ^ (1 - jasHalfTwist Δ) / ((1 - jasHalfTwist Δ) * (Real.log k : ℂ))‖ +
          ‖∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-jasHalfTwist Δ) -
            ((k : ℝ) : ℂ) ^ (1 - jasHalfTwist Δ) / ((1 - jasHalfTwist Δ) * (Real.log k : ℂ))‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ _ := by rw [hmain]; linarith

/-- The untwisted partial sums at exponent `½` are eventually within `ε k^{1/2}/log k` of
`2 k^{1/2}/log k`. -/
theorem eventually_abs_sum_primesLE_half_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, |∑ p ∈ Nat.primesLE k, (p : ℝ) ^ (-(1 / 2 : ℝ)) -
      2 * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k)| ≤ ε * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k) := by
  have h0 := tendsto_sum_primesLE_cpow_sub_main (s := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
  filter_upwards [h0.eventually (ge_mem_nhds hε), eventually_ge_atTop 2] with k hk hk2
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hlog : 0 < Real.log k := Real.log_pos (by linarith)
  have hpow : 0 < (k : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hsum : ∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((∑ p ∈ Nat.primesLE k, (p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.ofReal_cpow (Nat.cast_nonneg p)]
    push_cast
    rfl
  have hmain : ((k : ℝ) : ℂ) ^ (1 - (1 / 2 : ℂ)) / ((1 - (1 / 2 : ℂ)) * (Real.log k : ℂ)) =
      ((2 * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - 1 / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (Nat.cast_nonneg k)]
    push_cast
    field_simp
  rw [hsum, hmain, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hk
  have h3 : 0 < Real.log k / (k : ℝ) ^ (1 / 2 : ℝ) := by positivity
  rw [mul_div_assoc, ← le_div_iff₀ h3] at hk
  rw [div_div_eq_mul_div] at hk
  calc _ ≤ ε * (k : ℝ) ^ (1 / 2 : ℝ) / Real.log k := hk
    _ = ε * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k) := by ring

theorem sum_primesLE_zero_rpow : ∑ p ∈ Nat.primesLE 0, (p : ℝ) ^ (-(1 / 2 : ℝ)) = 0 := by
  rw [show Nat.primesLE 0 = ∅ by decide]
  rfl

/-- **Twisted reciprocal prime sums.**  For `Δ ≠ 0` there is `κ < 1` with
`‖Σ_{p ≤ N} p^{−1} p^{iΔ}‖ ≤ κ Σ_{p ≤ N} p^{−1}` for all large `N`. -/
theorem exists_twisted_jasPrimeRpowSum_one_le {Δ : ℝ} (hΔ : Δ ≠ 0) :
    ∃ κ : ℝ, κ < 1 ∧ ∀ᶠ N in atTop,
      ‖∑ p ∈ jasPrimesUpTo N, (Real.exp (-1 * Real.log p) : ℂ) *
          cexp (((Δ * Real.log p : ℝ) : ℂ) * I)‖ ≤ κ * jasPrimeRpowSum 1 N := by
  have hn := norm_one_sub_jasHalfTwist_gt hΔ
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = 1 / ‖1 - jasHalfTwist Δ‖ := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact one_div_pos.mpr (by linarith)
  have hm2 : m < 2 := by
    rw [hm, div_lt_iff₀ (by linarith)]; linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (2 - m) / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  have h2ε : 0 < 2 - ε := by rw [hε]; linarith
  obtain ⟨κ₁, hκ₁⟩ : ∃ κ₁ : ℝ, κ₁ = (m + ε) / (2 - ε) := ⟨_, rfl⟩
  have hκ₁0 : 0 ≤ κ₁ := by rw [hκ₁]; exact div_nonneg (by linarith) h2ε.le
  have hκ₁1 : κ₁ < 1 := by rw [hκ₁, div_lt_one h2ε, hε]; linarith
  have hκ₁e : κ₁ * (2 - ε) = m + ε := by rw [hκ₁]; field_simp
  refine ⟨(κ₁ + 1) / 2, by linarith, ?_⟩
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp
    ((eventually_norm_sum_primesLE_jasHalfTwist_le Δ hε0).and
      ((eventually_abs_sum_primesLE_half_sub_le hε0).and (eventually_ge_atTop 3)))
  rw [← hm] at hk₀
  -- the comparison weights
  obtain ⟨ω, hω⟩ : ∃ ω : ℕ → ℝ, ∀ k, ω k =
      (jasHalfWeight k - jasHalfWeight (k + 1)) * ((k : ℝ) ^ (1 / 2 : ℝ) / Real.log k) :=
    ⟨_, fun _ => rfl⟩
  have hdec : ∀ k, k₀ ≤ k → 0 ≤ jasHalfWeight k - jasHalfWeight (k + 1) := fun k hk =>
    sub_nonneg.mpr (jasHalfWeight_succ_le (by linarith [(hk₀ k hk).2.2]))
  have hlogk : ∀ k, k₀ ≤ k → 1 ≤ Real.log k := fun k hk => by
    have h3 : (3 : ℝ) ≤ k := by exact_mod_cast (hk₀ k hk).2.2
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hω0 : ∀ k, k₀ ≤ k → 0 ≤ ω k := fun k hk => by
    rw [hω]
    have := hlogk k hk
    exact mul_nonneg (hdec k hk) (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) (by linarith))
  -- the small-index constants
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = ∑ k ∈ Finset.range k₀,
      ‖∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-jasHalfTwist Δ)‖ *
        |jasHalfWeight k - jasHalfWeight (k + 1)| := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = ∑ k ∈ Finset.range k₀,
      (∑ p ∈ Nat.primesLE k, (p : ℝ) ^ (-(1 / 2 : ℝ))) *
        (jasHalfWeight k - jasHalfWeight (k + 1)) := ⟨_, rfl⟩
  have hRA0 : ∀ k, 0 ≤ ∑ p ∈ Nat.primesLE k, (p : ℝ) ^ (-(1 / 2 : ℝ)) := fun k =>
    Finset.sum_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    refine Finset.sum_nonneg fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [sum_primesLE_zero_rpow, zero_mul]
    · exact mul_nonneg (hRA0 k) (sub_nonneg.mpr (jasHalfWeight_succ_le hk))
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = (2 - ε) * (1 - κ₁) / 2 := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ']; exact div_pos (mul_pos h2ε (by linarith)) two_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((m + ε) + C₀) / δ' := ⟨_, rfl⟩
  filter_upwards [eventually_ge_atTop k₀,
    (tendsto_jasPrimeRpowSum_atTop le_rfl).eventually_ge_atTop ((2 + ε) + C₁ + (2 + ε) * B)]
    with N hN hS
  have hsplit : ∀ F : ℕ → ℝ, ∑ k ∈ Finset.range N, F k =
      ∑ k ∈ Finset.range k₀, F k + ∑ k ∈ Finset.Ico k₀ N, F k := fun F =>
    (Finset.sum_range_add_sum_Ico F hN).symm
  -- the twisted sum
  have hTabel := sum_range_mul_eq_abel (jasTwistCoeff Δ) (fun k => (jasHalfWeight k : ℂ)) N
  simp only [sum_range_jasTwistCoeff] at hTabel
  have hT : ‖∑ k ∈ Finset.range (N + 1), jasTwistCoeff Δ k * (jasHalfWeight k : ℂ)‖ ≤
      (m + ε) + C₀ + (m + ε) * ∑ k ∈ Finset.Ico k₀ N, ω k := by
    rw [hTabel]
    refine (norm_add_le _ _).trans ?_
    have hfirst : ‖(∑ p ∈ Nat.primesLE N, (p : ℂ) ^ (-jasHalfTwist Δ)) * (jasHalfWeight N : ℂ)‖ ≤
        m + ε := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (jasHalfWeight_nonneg N)]
      have h1 := (hk₀ N hN).1
      have hl := hlogk N hN
      have hw := jasHalfWeight_mul_rpow (by linarith [(hk₀ N hN).2.2] : 1 ≤ N)
      calc _ ≤ (m + ε) * ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log N) * jasHalfWeight N :=
            mul_le_mul_of_nonneg_right h1 (jasHalfWeight_nonneg N)
        _ = (m + ε) / Real.log N := by
            have e : (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N * jasHalfWeight N = 1 / Real.log N := by
              rw [div_mul_eq_mul_div, mul_comm ((N : ℝ) ^ (1 / 2 : ℝ)), hw]
            rw [mul_assoc, e]; ring
        _ ≤ m + ε := div_le_self (by linarith) hl
    have hsecond : ‖∑ k ∈ Finset.range N, (∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-jasHalfTwist Δ)) *
        ((jasHalfWeight k : ℂ) - (jasHalfWeight (k + 1) : ℂ))‖ ≤
          C₀ + (m + ε) * ∑ k ∈ Finset.Ico k₀ N, ω k := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ k, ‖(∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-jasHalfTwist Δ)) *
          ((jasHalfWeight k : ℂ) - (jasHalfWeight (k + 1) : ℂ))‖ =
            ‖∑ p ∈ Nat.primesLE k, (p : ℂ) ^ (-jasHalfTwist Δ)‖ *
              |jasHalfWeight k - jasHalfWeight (k + 1)| := fun k => by
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simp_rw [hterm]
      rw [hsplit, ← hC₀, Finset.mul_sum]
      refine add_le_add le_rfl (Finset.sum_le_sum fun k hk => ?_)
      have hk' : k₀ ≤ k := (Finset.mem_Ico.mp hk).1
      rw [abs_of_nonneg (hdec k hk'), hω, mul_comm (jasHalfWeight k - _), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hk₀ k hk').1 (hdec k hk')
    linarith
  -- the untwisted sum
  have hRabel := sum_range_mul_eq_abel jasHalfCoeff jasHalfWeight N
  simp only [sum_range_jasHalfCoeff] at hRabel
  have hR : jasPrimeRpowSum 1 N = (∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(1 / 2 : ℝ))) *
      jasHalfWeight N + C₁ + ∑ k ∈ Finset.Ico k₀ N,
        (∑ p ∈ Nat.primesLE k, (p : ℝ) ^ (-(1 / 2 : ℝ))) *
          (jasHalfWeight k - jasHalfWeight (k + 1)) := by
    rw [jasPrimeRpowSum_one_eq_abel, hRabel, hsplit, ← hC₁]; ring
  have hlow : ∀ k ∈ Finset.Ico k₀ N, (2 - ε) * ω k ≤
      (∑ p ∈ Nat.primesLE k, (p : ℝ) ^ (-(1 / 2 : ℝ))) *
        (jasHalfWeight k - jasHalfWeight (k + 1)) := by
    intro k hk
    have hk' : k₀ ≤ k := (Finset.mem_Ico.mp hk).1
    have h2 := (abs_le.mp (hk₀ k hk').2.1).1
    rw [hω, mul_comm (jasHalfWeight k - _), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (hdec k hk')
  have hup : ∀ k ∈ Finset.Ico k₀ N,
      (∑ p ∈ Nat.primesLE k, (p : ℝ) ^ (-(1 / 2 : ℝ))) *
        (jasHalfWeight k - jasHalfWeight (k + 1)) ≤ (2 + ε) * ω k := by
    intro k hk
    have hk' : k₀ ≤ k := (Finset.mem_Ico.mp hk).1
    have h2 := (abs_le.mp (hk₀ k hk').2.1).2
    rw [hω, mul_comm (jasHalfWeight k - _), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (hdec k hk')
  have hfirstR : (∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(1 / 2 : ℝ))) * jasHalfWeight N ≤ 2 + ε := by
    have h2 := (abs_le.mp (hk₀ N hN).2.1).2
    have hl := hlogk N hN
    have hw := jasHalfWeight_mul_rpow (by linarith [(hk₀ N hN).2.2] : 1 ≤ N)
    calc _ ≤ (2 + ε) * ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log N) * jasHalfWeight N :=
          mul_le_mul_of_nonneg_right (by linarith) (jasHalfWeight_nonneg N)
      _ = (2 + ε) / Real.log N := by
          have e : (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N * jasHalfWeight N = 1 / Real.log N := by
            rw [div_mul_eq_mul_div, mul_comm ((N : ℝ) ^ (1 / 2 : ℝ)), hw]
          rw [mul_assoc, e]; ring
      _ ≤ 2 + ε := div_le_self (by linarith) hl
  have hfirstR0 : 0 ≤ (∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(1 / 2 : ℝ))) * jasHalfWeight N :=
    mul_nonneg (hRA0 N) (jasHalfWeight_nonneg N)
  have hSlow : (2 - ε) * ∑ k ∈ Finset.Ico k₀ N, ω k ≤ jasPrimeRpowSum 1 N := by
    rw [hR, Finset.mul_sum]
    linarith [Finset.sum_le_sum hlow]
  have hSup : jasPrimeRpowSum 1 N ≤ (2 + ε) + C₁ + (2 + ε) * ∑ k ∈ Finset.Ico k₀ N, ω k := by
    rw [hR, Finset.mul_sum]
    linarith [Finset.sum_le_sum hup]
  have hΩB : B ≤ ∑ k ∈ Finset.Ico k₀ N, ω k := by
    have : (2 + ε) * B ≤ (2 + ε) * ∑ k ∈ Finset.Ico k₀ N, ω k := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  have hBδ : (m + ε) + C₀ ≤ δ' * ∑ k ∈ Finset.Ico k₀ N, ω k := by
    rw [hB, div_le_iff₀ hδ'0] at hΩB; linarith
  rw [twisted_sum_eq_abel]
  have hκS : ((κ₁ + 1) / 2) * ((2 - ε) * ∑ k ∈ Finset.Ico k₀ N, ω k) ≤
      ((κ₁ + 1) / 2) * jasPrimeRpowSum 1 N :=
    mul_le_mul_of_nonneg_left hSlow (by linarith)
  have hid : ((κ₁ + 1) / 2) * ((2 - ε) * ∑ k ∈ Finset.Ico k₀ N, ω k) =
      δ' * ∑ k ∈ Finset.Ico k₀ N, ω k + (m + ε) * ∑ k ∈ Finset.Ico k₀ N, ω k := by
    rw [hδ', ← hκ₁e]; ring
  linarith

/-- **The twisted comparison for `0 < α ≤ 1`.** -/
theorem exists_twisted_jasPrimeRpowSum_le_of_le_one {α Δ : ℝ} (h0 : 0 < α) (h1 : α ≤ 1)
    (hΔ : Δ ≠ 0) :
    ∃ κ : ℝ, κ < 1 ∧ ∀ᶠ N in atTop,
      ‖∑ p ∈ jasPrimesUpTo N, (Real.exp (-α * Real.log p) : ℂ) *
          cexp (((Δ * Real.log p : ℝ) : ℂ) * I)‖ ≤ κ * jasPrimeRpowSum α N := by
  rcases h1.lt_or_eq with h | rfl
  · exact exists_twisted_jasPrimeRpowSum_le h0 h hΔ
  · exact exists_twisted_jasPrimeRpowSum_one_le hΔ

end

end RHTower
