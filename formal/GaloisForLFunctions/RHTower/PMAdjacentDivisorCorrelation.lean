import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSecondMoment
import GaloisForLFunctions.RHTower.EulerDeletionTruncatedDivisorPairCorrelation
import GaloisForLFunctions.RHTower.Sieve.RamarePhaseError

/-!
# Adjacent power-damped divisor correlations

The adjacent correlation is evaluated by two successive dominated limits. Positivity of the
divisor field controls the outer limit even when its Möbius coefficients are not summable.
-/

open Filter Topology Finset ArithmeticFunction

noncomputable section
namespace RHTower

private theorem pm_nat_quotient_mean (q : ℕ) :
    Tendsto (fun N : ℕ => ((N / q : ℕ) : ℝ) / N) atTop (𝓝 (1 / (q : ℝ))) := by
  by_cases hq : q = 0
  · subst q
    simp
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_mod_div_atTop_nhds_zero_nat (Nat.pos_of_ne_zero hq))).div_const (q : ℝ)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have he : ((N % q : ℕ) : ℝ) + q * (N / q : ℕ) = N := by
    exact_mod_cast Nat.mod_add_div N q
  field_simp
  nlinarith

private theorem pm_residue_count_mean {q : ℕ} (hq : 0 < q) (r : ℕ) :
    Tendsto (fun N : ℕ =>
      ((#{n ∈ Icc 1 N | n ≡ r [MOD q]} : ℕ) : ℝ) / N)
      atTop (𝓝 (1 / (q : ℝ))) := by
  let e : ℕ → ℝ := fun N =>
    (if r % q < (N + 1) % q then 1 else 0) - (if 0 ≡ r [MOD q] then 1 else 0)
  have he (N : ℕ) : |e N| ≤ 1 := by
    dsimp only [e]
    split_ifs <;> norm_num
  have hcount (N : ℕ) :
      ((#{n ∈ Icc 1 N | n ≡ r [MOD q]} : ℕ) : ℝ) =
        (( (N + 1) / q : ℕ) : ℝ) + e N := by
    have hset : range (N + 1) = insert 0 (Icc 1 N) := by
      ext n
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    have hc := Nat.count_modEq_card (N + 1) hq r
    rw [Nat.count_eq_card_filter_range, hset] at hc
    simp only [filter_insert] at hc
    have hzero : 0 ∉ {n ∈ Icc 1 N | n ≡ r [MOD q]} := by simp
    dsimp only [e]
    split_ifs at hc ⊢
    all_goals
      have hcR := congrArg (fun n : ℕ => (n : ℝ)) hc
      simp only [card_insert_of_notMem hzero, Nat.cast_add, Nat.cast_one,
        Nat.cast_zero] at hcR
      linarith
  have herr : Tendsto (fun N : ℕ => e N / N) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    rw [norm_div, Real.norm_eq_abs, Real.norm_natCast]
    exact div_le_div_of_nonneg_right (he N) (Nat.cast_nonneg N)
  have hqmean := (pm_nat_quotient_mean q).comp (tendsto_add_atTop_nat 1)
  have hscale : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have hmain : Tendsto (fun N : ℕ => (((N + 1) / q : ℕ) : ℝ) / N)
      atTop (𝓝 (1 / (q : ℝ))) := by
    simpa only [mul_one] using (hqmean.mul hscale).congr (fun N => by
      dsimp only [Function.comp_def]
      push_cast
      have hN : (N : ℝ) + 1 ≠ 0 := by positivity
      field_simp)
  simpa only [add_zero] using (hmain.add herr).congr (fun N => by
    rw [hcount, add_div])

/-- The density of simultaneous divisibility at adjacent integers is the coprime CRT density. -/
theorem pm_adjacent_divisibility_mean (a d : ℕ) :
    Tendsto (fun N : ℕ =>
      ((#{n ∈ Icc 1 N | d ∣ n ∧ a ∣ n + 1} : ℕ) : ℝ) / N)
      atTop (𝓝 (if a.Coprime d then 1 / ((a : ℝ) * d) else 0)) := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hd : d = 0
  · subst d
    have hz (N : ℕ) : {n ∈ Icc 1 N | 0 ∣ n ∧ a ∣ n + 1} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hn, h0, _⟩ := mem_filter.mp hn
      have hpos := (mem_Icc.mp hn).1
      have hn0 := zero_dvd_iff.mp h0
      omega
    simp only [hz, card_empty, Nat.cast_zero, zero_div, mul_zero, div_zero, ite_self]
    exact tendsto_const_nhds
  by_cases hc : a.Coprime d
  · obtain ⟨r, _, hr⟩ := exists_lcm_residueClass_of_gcd_dvd_shift
      (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero ha)
      (show Nat.gcd d a ∣ 1 by simp [hc.symm.gcd_eq_one])
    have hf (N : ℕ) : {n ∈ Icc 1 N | d ∣ n ∧ a ∣ n + 1} =
        {n ∈ Icc 1 N | n ≡ r [MOD Nat.lcm d a]} := by
      ext n
      simp only [mem_filter, hr]
    simpa only [hf, if_pos hc, hc.symm.lcm_eq_mul, Nat.cast_mul, mul_comm] using
      pm_residue_count_mean (Nat.lcm_pos (Nat.pos_of_ne_zero hd)
        (Nat.pos_of_ne_zero ha)) r
  · have hz (N : ℕ) : {n ∈ Icc 1 N | d ∣ n ∧ a ∣ n + 1} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨_, hn⟩ := mem_filter.mp hn
      have hg := gcd_dvd_shift_of_joint_divisibility hn.1 hn.2
      exact hc (Nat.coprime_iff_gcd_eq_one.mpr
        (by simpa only [Nat.gcd_comm] using Nat.dvd_one.mp hg))
    simp only [hz, card_empty, Nat.cast_zero, zero_div, if_neg hc]
    exact tendsto_const_nhds

private theorem pm_adjacent_count_le (a d N : ℕ) :
    #{n ∈ Icc 1 N | d ∣ n ∧ a ∣ n + 1} ≤ (N + 1) / a := by
  rw [← Sieve.card_Icc_filter_dvd (N + 1) a]
  apply Finset.card_le_card_of_injOn (fun n => n + 1)
  · intro n hn
    obtain ⟨hn, _, ha⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.succ_pos n,
      Nat.add_le_add_right (mem_Icc.mp hn).2 1⟩, ha⟩
  · intro m _ n _ h
    exact Nat.add_right_cancel h

private theorem pm_adjacent_average_eq_tsum (c : ℕ → ℝ) (d N : ℕ) :
    (∑ n ∈ Icc 1 N, if d ∣ n then ∑ a ∈ (n + 1).divisors, c a else 0) / (N : ℝ) =
      ∑' a : ℕ, c a *
        (((#{n ∈ Icc 1 N | d ∣ n ∧ a ∣ n + 1} : ℕ) : ℝ) / N) := by
  have hz (a : ℕ) (ha : a ∉ Icc 1 (N + 1)) :
      {n ∈ Icc 1 N | d ∣ n ∧ a ∣ n + 1} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hn, _, had⟩ := mem_filter.mp hn
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos had (by omega)
    have han := Nat.le_of_dvd (by omega : 0 < n + 1) had
    exact ha (mem_Icc.mpr ⟨ha0, by have := (mem_Icc.mp hn).2; omega⟩)
  rw [tsum_eq_sum (s := Icc 1 (N + 1)) (fun a ha => by simp [hz a ha])]
  have hexpand (n : ℕ) (hn : n ∈ Icc 1 N) :
      (if d ∣ n then ∑ a ∈ (n + 1).divisors, c a else 0) =
        ∑ a ∈ Icc 1 (N + 1), if d ∣ n ∧ a ∣ n + 1 then c a else 0 := by
    by_cases hd : d ∣ n
    · rw [if_pos hd]
      have hsub : (n + 1).divisors ⊆ Icc 1 (N + 1) := by
        intro a ha
        obtain ⟨had, _⟩ := Nat.mem_divisors.mp ha
        exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos had (by omega),
          (Nat.le_of_dvd (by omega : 0 < n + 1) had).trans
            (Nat.add_le_add_right (mem_Icc.mp hn).2 1)⟩
      rw [← Finset.sum_subset hsub]
      · apply sum_congr rfl
        intro a ha
        simp [hd, (Nat.mem_divisors.mp ha).1]
      · intro a _ ha
        have hnot : ¬a ∣ n + 1 := fun h => ha (Nat.mem_divisors.mpr ⟨h, by omega⟩)
        simp [hnot]
    · simp [hd]
  rw [sum_congr rfl hexpand, sum_comm, sum_div]
  apply sum_congr rfl
  intro a _
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  ring

/-- A shifted divisor sum on one divisibility progression has its exact coprime density. -/
theorem pm_divisor_progression_mean {c : ℕ → ℝ}
    (hc : Summable (fun a : ℕ => c a / (a : ℝ))) (d : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, if d ∣ n then ∑ a ∈ (n + 1).divisors, c a else 0) / (N : ℝ))
      atTop (𝓝 (∑' a : ℕ, c a *
        (if a.Coprime d then 1 / ((a : ℝ) * d) else 0))) := by
  let F : ℕ → ℕ → ℝ := fun N a => c a *
    (((#{n ∈ Icc 1 N | d ∣ n ∧ a ∣ n + 1} : ℕ) : ℝ) / N)
  have hlim (a : ℕ) := (pm_adjacent_divisibility_mean a d).const_mul (c a)
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ a : ℕ,
      ‖F N a‖ ≤ 2 * ‖c a / (a : ℝ)‖ := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro a
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hcount :
        ((#{n ∈ Icc 1 N | d ∣ n ∧ a ∣ n + 1} : ℕ) : ℝ) / N ≤ 2 / (a : ℝ) := by
      by_cases ha : a = 0
      · subst a
        simp
      have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
      have hb : ((#{n ∈ Icc 1 N | d ∣ n ∧ a ∣ n + 1} : ℕ) : ℝ) ≤
          ((N : ℝ) + 1) / a := by
        exact (Nat.cast_le.mpr (pm_adjacent_count_le a d N)).trans
          (by exact_mod_cast (Nat.cast_div_le (m := N + 1) (n := a) (α := ℝ)))
      apply (div_le_iff₀ hNR).mpr
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      calc
        _ ≤ ((N : ℝ) + 1) / a := hb
        _ ≤ (2 * N) / a := div_le_div_of_nonneg_right (by linarith) haR.le
        _ = _ := by ring
    dsimp only [F]
    rw [norm_mul, norm_div, Real.norm_natCast, Real.norm_natCast,
      norm_div, Real.norm_natCast]
    calc
      _ ≤ ‖c a‖ * (2 / (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hcount (norm_nonneg (c a))
      _ = _ := by ring
  have h := tendsto_tsum_of_dominated_convergence (hc.norm.mul_left (2 : ℝ)) hlim hbound
  exact h.congr fun N => (pm_adjacent_average_eq_tsum c d N).symm

private theorem pm_weighted_divisor_average_eq_tsum (c f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f (n + 1) * ∑ d ∈ n.divisors, c d) / (N : ℝ) =
      ∑' d : ℕ, c d *
        ((∑ n ∈ Icc 1 N, if d ∣ n then f (n + 1) else 0) / N) := by
  have hz (d : ℕ) (hd : d ∉ Icc 1 N) (n : ℕ) (hn : n ∈ Icc 1 N) : ¬d ∣ n := by
    intro hdn
    have hn0 := (mem_Icc.mp hn).1
    exact hd (mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdn hn0,
      (Nat.le_of_dvd hn0 hdn).trans (mem_Icc.mp hn).2⟩)
  rw [tsum_eq_sum (s := Icc 1 N) (fun d hd => by
    have hsum : (∑ n ∈ Icc 1 N, if d ∣ n then f (n + 1) else 0) = 0 :=
      sum_eq_zero fun n hn => if_neg (hz d hd n hn)
    rw [hsum, zero_div, mul_zero])]
  have hexpand (n : ℕ) (hn : n ∈ Icc 1 N) :
      f (n + 1) * (∑ d ∈ n.divisors, c d) =
        ∑ d ∈ Icc 1 N, c d * (if d ∣ n then f (n + 1) else 0) := by
    have hn0 := (mem_Icc.mp hn).1
    have hsub : n.divisors ⊆ Icc 1 N := by
      intro d hd
      obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hd
      exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdn hn0,
        (Nat.le_of_dvd hn0 hdn).trans (mem_Icc.mp hn).2⟩
    rw [mul_sum, ← Finset.sum_subset hsub]
    · apply sum_congr rfl
      intro d hd
      rw [if_pos (Nat.mem_divisors.mp hd).1, mul_comm]
    · intro d _ hd
      have hdn : ¬d ∣ n := fun h => hd (Nat.mem_divisors.mpr ⟨h, by omega⟩)
      simp [hdn]
  rw [sum_congr rfl hexpand, sum_comm, sum_div]
  apply sum_congr rfl
  intro d _
  rw [← mul_sum]
  ring

/-- Absolute reciprocal summability of the real power-damped Möbius coefficients. -/
theorem pm_summable_real_mobius_reciprocal {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => ((moebius n : ℝ) * (n : ℝ) ^ (-ε)) / n) := by
  apply (RCLike.summable_ofReal (𝕜 := ℂ)).mp
  change Summable (fun n : ℕ => (((moebius n : ℝ) * (n : ℝ) ^ (-ε) / n : ℝ) : ℂ))
  simpa only [pmPowerDampedMobiusCoeff, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_intCast, Complex.ofReal_natCast] using
      summable_pmPowerDampedDivisorDensity_terms hε

/-- The absolutely convergent coprime double series for adjacent divisor fields. -/
def pmAdjacentDivisorDensity (ε η : ℝ) : ℝ :=
  ∑' d : ℕ, ((moebius d : ℝ) * (d : ℝ) ^ (-η)) *
    ∑' a : ℕ, ((moebius a : ℝ) * (a : ℝ) ^ (-ε)) *
      (if a.Coprime d then 1 / ((a : ℝ) * d) else 0)

/-- The adjacent Cesàro correlation exists for every pair of positive damping parameters. -/
theorem tendsto_pm_adjacent_divisor_mean {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, pmPowerDampedDivisorCoeff ε (n + 1) *
        pmPowerDampedDivisorCoeff η n) / (N : ℝ))
      atTop (𝓝 (pmAdjacentDivisorDensity ε η)) := by
  let c : ℕ → ℝ := fun d => (moebius d : ℝ) * (d : ℝ) ^ (-η)
  let F : ℕ → ℕ → ℝ := fun N d => c d *
    ((∑ n ∈ Icc 1 N, if d ∣ n then pmPowerDampedDivisorCoeff ε (n + 1) else 0) / N)
  have hlim (d : ℕ) := (pm_divisor_progression_mean
    (pm_summable_real_mobius_reciprocal hε) d).const_mul (c d)
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, ‖F N d‖ ≤ ‖c d / (d : ℝ)‖ := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro d
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    let B : ℝ := ∑ n ∈ Icc 1 N,
      if d ∣ n then pmPowerDampedDivisorCoeff ε (n + 1) else 0
    have hB0 : 0 ≤ B := sum_nonneg fun n _ => by
      split_ifs
      · exact pmPowerDampedDivisorCoeff_nonneg hε.le _
      · rfl
    have hB : B ≤ ((N / d : ℕ) : ℝ) := by
      calc
        B ≤ ∑ n ∈ Icc 1 N, if d ∣ n then (1 : ℝ) else 0 := by
          apply sum_le_sum
          intro n _
          split_ifs
          · exact pmPowerDampedDivisorCoeff_le_one hε.le _
          · rfl
        _ = _ := by
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, Sieve.card_Icc_filter_dvd]
    have hb : B / (N : ℝ) ≤ 1 / (d : ℝ) := by
      apply (div_le_iff₀ hNR).mpr
      calc
        B ≤ ((N / d : ℕ) : ℝ) := hB
        _ ≤ (N : ℝ) / d := Nat.cast_div_le
        _ = _ := by ring
    change ‖c d * (B / (N : ℝ))‖ ≤ ‖c d / (d : ℝ)‖
    rw [norm_mul, norm_div, Real.norm_of_nonneg hB0,
      Real.norm_natCast, norm_div, Real.norm_natCast]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hb (norm_nonneg (c d))
  have h := tendsto_tsum_of_dominated_convergence
    (pm_summable_real_mobius_reciprocal hη).norm hlim hbound
  exact h.congr fun N =>
    (pm_weighted_divisor_average_eq_tsum c (pmPowerDampedDivisorCoeff ε) N).symm

end RHTower
