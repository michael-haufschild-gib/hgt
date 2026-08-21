import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientSpatialBridge

open Complex

namespace RHTower.Sieve

noncomputable section

/-- Spatial Mellin `L²` with the actual coefficient energy.  This is the weighted form hidden by
the earlier uniform-envelope/cardinality corollary. -/
theorem integral_norm_sq_maynardDiscreteMellinPacket_le_energy
    {x c : ℝ} {N : ℕ} (hx : 0 < x) (hc : 0 ≤ c)
    (S : Finset ℕ) (hS : S ⊆ Finset.range N) (a : ℕ → ℂ) :
    (∫ y : ℝ in x..(2 * x), ‖maynardDiscreteMellinPacket S a c y‖ ^ 2) ≤
      4 * (2 * x) ^ (2 * c + 1) *
        (1 + 2 * (1 + Real.log N)) *
          ∑ m ∈ S, ‖a m‖ ^ 2 := by
  classical
  let K : ℝ := 4 * (2 * x) ^ (2 * c + 1)
  let H : ℝ := 1 + 2 * (1 + Real.log N)
  let Q : ℕ → ℕ → ℝ := fun m n => 1 / (1 + |(n : ℝ) - (m : ℝ)|)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hQ : ∀ m n, 0 ≤ Q m n := by
    intro m n
    dsimp only [Q]
    positivity
  have hQsymm : ∀ m n, Q m n = Q n m := by
    intro m n
    dsimp only [Q]
    rw [abs_sub_comm]
  have hrow : ∀ m ∈ S, ∑ n ∈ S, Q m n ≤ H := by
    intro m hm
    simpa only [Q, H] using sum_subset_one_div_one_add_abs_int_dist_le hS hm
  have hamgm : ∀ m n : ℕ,
      ‖a m‖ * ‖a n‖ * Q m n ≤
        (‖a m‖ ^ 2 / 2 + ‖a n‖ ^ 2 / 2) * Q m n := by
    intro m n
    refine mul_le_mul_of_nonneg_right ?_ (hQ m n)
    nlinarith [sq_nonneg (‖a m‖ - ‖a n‖)]
  have hbound :
      (∑ m ∈ S, ∑ n ∈ S, ‖a m‖ * ‖a n‖ * Q m n) ≤
        ∑ m ∈ S, ∑ n ∈ S,
          (‖a m‖ ^ 2 / 2 + ‖a n‖ ^ 2 / 2) * Q m n := by
    exact Finset.sum_le_sum fun m _ =>
      Finset.sum_le_sum fun n _ => hamgm m n
  have hsplit :
      (∑ m ∈ S, ∑ n ∈ S,
          (‖a m‖ ^ 2 / 2 + ‖a n‖ ^ 2 / 2) * Q m n) =
        (∑ m ∈ S, ‖a m‖ ^ 2 / 2 * ∑ n ∈ S, Q m n) +
          ∑ m ∈ S, ∑ n ∈ S, ‖a n‖ ^ 2 / 2 * Q m n := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hswap :
      (∑ m ∈ S, ∑ n ∈ S, ‖a n‖ ^ 2 / 2 * Q m n) =
        ∑ n ∈ S, ‖a n‖ ^ 2 / 2 * ∑ m ∈ S, Q n m := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hQsymm m n]
  have hhalf1 :
      (∑ m ∈ S, ‖a m‖ ^ 2 / 2 * ∑ n ∈ S, Q m n) ≤
        H / 2 * ∑ m ∈ S, ‖a m‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    calc
      ‖a m‖ ^ 2 / 2 * ∑ n ∈ S, Q m n ≤ ‖a m‖ ^ 2 / 2 * H :=
        mul_le_mul_of_nonneg_left (hrow m hm) (by positivity)
      _ = H / 2 * ‖a m‖ ^ 2 := by ring
  have hhalf2 :
      (∑ n ∈ S, ‖a n‖ ^ 2 / 2 * ∑ m ∈ S, Q n m) ≤
        H / 2 * ∑ n ∈ S, ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    calc
      ‖a n‖ ^ 2 / 2 * ∑ m ∈ S, Q n m ≤ ‖a n‖ ^ 2 / 2 * H :=
        mul_le_mul_of_nonneg_left (hrow n hn) (by positivity)
      _ = H / 2 * ‖a n‖ ^ 2 := by ring
  have hschur :
      (∑ m ∈ S, ∑ n ∈ S, ‖a m‖ * ‖a n‖ * Q m n) ≤
        H * ∑ m ∈ S, ‖a m‖ ^ 2 := by
    calc
      (∑ m ∈ S, ∑ n ∈ S, ‖a m‖ * ‖a n‖ * Q m n) ≤
          ∑ m ∈ S, ∑ n ∈ S,
            (‖a m‖ ^ 2 / 2 + ‖a n‖ ^ 2 / 2) * Q m n := hbound
      _ = (∑ m ∈ S, ‖a m‖ ^ 2 / 2 * ∑ n ∈ S, Q m n) +
          ∑ m ∈ S, ∑ n ∈ S, ‖a n‖ ^ 2 / 2 * Q m n := hsplit
      _ = (∑ m ∈ S, ‖a m‖ ^ 2 / 2 * ∑ n ∈ S, Q m n) +
          ∑ n ∈ S, ‖a n‖ ^ 2 / 2 * ∑ m ∈ S, Q n m := by rw [hswap]
      _ ≤ H / 2 * (∑ m ∈ S, ‖a m‖ ^ 2) +
          H / 2 * ∑ n ∈ S, ‖a n‖ ^ 2 := add_le_add hhalf1 hhalf2
      _ = H * ∑ m ∈ S, ‖a m‖ ^ 2 := by ring
  have hbase := integral_norm_sq_maynardDiscreteMellinPacket_le_gram hx hc S a
  calc
    (∫ y : ℝ in x..(2 * x), ‖maynardDiscreteMellinPacket S a c y‖ ^ 2) ≤
        ∑ m ∈ S, ∑ n ∈ S,
          ‖a m‖ * ‖a n‖ *
            (K / (1 + |(m : ℝ) - (n : ℝ)|)) := by
      simpa only [K] using hbase
    _ = K * (∑ m ∈ S, ∑ n ∈ S, ‖a m‖ * ‖a n‖ * Q m n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [Q]
      rw [abs_sub_comm]
      ring
    _ ≤ K * (H * ∑ m ∈ S, ‖a m‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hschur hK
    _ = 4 * (2 * x) ^ (2 * c + 1) *
        (1 + 2 * (1 + Real.log N)) *
          ∑ m ∈ S, ‖a m‖ ^ 2 := by
      dsimp only [K, H]
      ring

theorem integral_norm_sq_maynardDiscreteMellinPacket_le_weighted_envelope
    {x c : ℝ} {N : ℕ} (hx : 0 < x) (hc : 0 ≤ c)
    (S : Finset ℕ) (hS : S ⊆ Finset.range N) (a : ℕ → ℂ)
    (A : ℕ → ℝ) (hA : ∀ m ∈ S, 0 ≤ A m)
    (ha : ∀ m ∈ S, ‖a m‖ ≤ A m) :
    (∫ y : ℝ in x..(2 * x), ‖maynardDiscreteMellinPacket S a c y‖ ^ 2) ≤
      4 * (2 * x) ^ (2 * c + 1) *
        (1 + 2 * (1 + Real.log N)) *
          ∑ m ∈ S, (A m) ^ 2 := by
  by_cases hSem : S = ∅
  · subst S
    simp [maynardDiscreteMellinPacket]
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSem
  obtain ⟨m0, hm0⟩ := hSne
  have hm0N := hS hm0
  have hN : 1 ≤ N := by
    simp only [Finset.mem_range] at hm0N
    omega
  have henergy : (∑ m ∈ S, ‖a m‖ ^ 2) ≤ ∑ m ∈ S, (A m) ^ 2 := by
    apply Finset.sum_le_sum
    intro m hm
    exact pow_le_pow_left₀ (norm_nonneg _) (ha m hm) 2
  have hfactor : 0 ≤
      4 * (2 * x) ^ (2 * c + 1) * (1 + 2 * (1 + Real.log N)) := by
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    positivity
  exact (integral_norm_sq_maynardDiscreteMellinPacket_le_energy hx hc S hS a).trans
    (mul_le_mul_of_nonneg_left henergy hfactor)

/-- Continuous unit-cell packet bound with a separate envelope on every selected cell. -/
theorem integral_norm_sq_maynardUnitCellMellinPacket_le_weighted_envelope
    {x c : ℝ} {N : ℕ} (hx : 1 ≤ x) (hc : 0 ≤ c)
    (S : Finset ℕ) (hS : S ⊆ Finset.range N) (b : ℕ → ℝ → ℂ)
    (hb : ∀ m ∈ S, Continuous (b m))
    (A : ℕ → ℝ) (hA : ∀ m ∈ S, 0 ≤ A m)
    (hbnd : ∀ m ∈ S, ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖b m v‖ ≤ A m) :
    (∫ y : ℝ in x..(2 * x), ‖maynardUnitCellMellinPacket S b c y‖ ^ 2) ≤
      4 * (2 * x) ^ (2 * c + 1) *
        (1 + 2 * (1 + Real.log N)) *
          ∑ m ∈ S, (A m) ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let Q : ℝ → ℝ → ℂ := fun v y =>
    maynardUnitCellMellinIntegrandPosExtension S b c v y
  let P : ℝ → ℂ := maynardUnitCellMellinPacketPosExtension S b c
  let F : ℝ → ℝ → ℝ := fun y v => ‖Q v y‖ ^ 2
  let C : ℝ := 4 * (2 * x) ^ (2 * c + 1) *
    (1 + 2 * (1 + Real.log N)) * ∑ m ∈ S, (A m) ^ 2
  have hQ : Continuous fun p : ℝ × ℝ => Q p.1 p.2 :=
    continuous_maynardUnitCellMellinIntegrandPosExtension S b c hb
  have hP : Continuous P :=
    continuous_maynardUnitCellMellinPacketPosExtension S b c hb
  have hF : Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
    dsimp only [F]
    exact (hQ.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hleft :
      (∫ y : ℝ in x..(2 * x), ‖maynardUnitCellMellinPacket S b c y‖ ^ 2) =
        ∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hy
    have hy1 : 1 ≤ y := hx.trans hy.1
    change ‖maynardUnitCellMellinPacket S b c y‖ ^ 2 =
      ‖maynardUnitCellMellinPacketPosExtension S b c y‖ ^ 2
    rw [maynardUnitCellMellinPacketPosExtension_eq hy1]
  have hpoint : ∀ y ∈ Set.Icc x (2 * x),
      ‖P y‖ ^ 2 ≤ ∫ v : ℝ in (0 : ℝ)..1, F y v := by
    intro y hy
    have hy1 : 1 ≤ y := hx.trans hy.1
    have hj := norm_sq_maynardUnitCellMellinPacket_le_integral_discrete
      hy1 S b c hb
    calc
      ‖P y‖ ^ 2 = ‖maynardUnitCellMellinPacket S b c y‖ ^ 2 := by
        change ‖maynardUnitCellMellinPacketPosExtension S b c y‖ ^ 2 = _
        rw [maynardUnitCellMellinPacketPosExtension_eq hy1]
      _ ≤ ∫ v : ℝ in (0 : ℝ)..1,
          ‖maynardDiscreteMellinPacket S (fun m => b m v) c y‖ ^ 2 := hj
      _ = ∫ v : ℝ in (0 : ℝ)..1, F y v := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only [F, Q]
        rw [maynardUnitCellMellinIntegrandPosExtension_eq hy1,
          norm_maynardUnitCellMellinIntegrand_eq_discrete
            (lt_of_lt_of_le zero_lt_one hy1)]
  have hinnerContinuous : Continuous fun y => ∫ v : ℝ in (0 : ℝ)..1, F y v :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1
  have hmono :
      (∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2) ≤
        ∫ y : ℝ in x..(2 * x), ∫ v : ℝ in (0 : ℝ)..1, F y v := by
    exact intervalIntegral.integral_mono_on (by linarith)
      (hP.norm.pow 2 |>.intervalIntegrable x (2 * x))
      (hinnerContinuous.intervalIntegrable x (2 * x)) hpoint
  have hswap :
      (∫ y : ℝ in x..(2 * x), ∫ v : ℝ in (0 : ℝ)..1, F y v) =
        ∫ v : ℝ in (0 : ℝ)..1, ∫ y : ℝ in x..(2 * x), F y v :=
    intervalIntegral_swap_of_continuous_maynard hF x (2 * x) 0 1
  have houterContinuous : Continuous fun v => ∫ y : ℝ in x..(2 * x), F y v := by
    change Continuous fun v => ∫ y : ℝ in x..(2 * x), ‖Q v y‖ ^ 2
    have hFswap : Continuous fun p : ℝ × ℝ => ‖Q p.1 p.2‖ ^ 2 := hQ.norm.pow 2
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hFswap x (2 * x)
  have houterPoint : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (∫ y : ℝ in x..(2 * x), F y v) ≤ C := by
    intro v hv
    have heq :
        (∫ y : ℝ in x..(2 * x), F y v) =
          ∫ y : ℝ in x..(2 * x),
            ‖maynardDiscreteMellinPacket S (fun m => b m v) c y‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hy
      have hy1 : 1 ≤ y := hx.trans hy.1
      dsimp only [F, Q]
      rw [maynardUnitCellMellinIntegrandPosExtension_eq hy1,
        norm_maynardUnitCellMellinIntegrand_eq_discrete
          (lt_of_lt_of_le zero_lt_one hy1)]
    rw [heq]
    have hd := integral_norm_sq_maynardDiscreteMellinPacket_le_weighted_envelope
      hxpos hc S hS (fun m => b m v) A hA (fun m hm => hbnd m hm v hv)
    simpa only [C] using hd
  have houter :
      (∫ v : ℝ in (0 : ℝ)..1, ∫ y : ℝ in x..(2 * x), F y v) ≤ C := by
    have hcst : IntervalIntegrable (fun _v : ℝ => C) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hle := intervalIntegral.integral_mono_on zero_le_one
      (houterContinuous.intervalIntegrable 0 1) hcst houterPoint
    simpa using hle
  calc
    (∫ y : ℝ in x..(2 * x), ‖maynardUnitCellMellinPacket S b c y‖ ^ 2) =
        ∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2 := hleft
    _ ≤ ∫ y : ℝ in x..(2 * x), ∫ v : ℝ in (0 : ℝ)..1, F y v := hmono
    _ = ∫ v : ℝ in (0 : ℝ)..1, ∫ y : ℝ in x..(2 * x), F y v := hswap
    _ ≤ C := houter
    _ = 4 * (2 * x) ^ (2 * c + 1) *
        (1 + 2 * (1 + Real.log N)) *
          ∑ m ∈ S, (A m) ^ 2 := rfl

/-- Weighted fixed-ambient equation-(111): spatial energy pays the sum of actual squared cell
envelopes, not the maximum envelope times cell count. -/
theorem integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_weighted_envelope
    {x sigma N R H : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hsigma : 1 ≤ sigma)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount) (a : ℝ → ℂ)
    (ha : Continuous a) (A : ℕ → ℝ)
    (hA : ∀ m ∈ S, 0 ≤ A m)
    (hbnd : ∀ m ∈ S, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient a N R H sigma m v‖ ≤ A m) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket
          S a lambda N R H sigma‖ ^ 2) ≤
      4 * (2 * x) ^ (2 * (sigma - 1) + 1) *
        (1 + 2 * (1 + Real.log cellCount)) *
          ∑ m ∈ S, (A m) ^ 2 := by
  have hb : ∀ m ∈ S,
      Continuous (maynardFixedAmbientDefectCellCoefficient a N R H sigma m) := by
    intro m hm
    exact continuous_maynardFixedAmbientDefectCellCoefficient ha hN hR hH
      (lt_of_lt_of_le zero_lt_one hsigma) m
  have hL2 := integral_norm_sq_maynardUnitCellMellinPacket_le_weighted_envelope
    hx (sub_nonneg.mpr hsigma) S hS
      (maynardFixedAmbientDefectCellCoefficient a N R H sigma) hb A hA hbnd
  calc
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H sigma‖ ^ 2) =
        ∫ lambda : ℝ in x..(2 * x),
          ‖maynardUnitCellMellinPacket S
            (maynardFixedAmbientDefectCellCoefficient a N R H sigma)
            (sigma - 1) lambda‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro lambda hlambda
      rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hlambda
      change ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H sigma‖ ^ 2 =
        ‖maynardUnitCellMellinPacket S
          (maynardFixedAmbientDefectCellCoefficient a N R H sigma)
          (sigma - 1) lambda‖ ^ 2
      rw [maynardFixedAmbientPhysicalDefectPacket_eq_mellinPacket
        S a lambda N R H sigma
          (lt_of_lt_of_le zero_lt_one (hx.trans hlambda.1)) hR hH]
    _ ≤ 4 * (2 * x) ^ (2 * (sigma - 1) + 1) *
        (1 + 2 * (1 + Real.log cellCount)) *
          ∑ m ∈ S, (A m) ^ 2 := hL2


+theorem integral_norm_sq_fixedSource_lowRange_le_cube
    (L X k K : ℕ) (hX : 1 ≤ X) (T0 t M x N H R : ℝ)
    (hM : 0 < M) (hx : 1 ≤ x) (hN : 0 < N)
    (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hsmall : (K : ℝ) * (2 * R / N) ≤ 1) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket (Finset.range K)
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda N R H 1‖ ^ 2) ≤
      4 * (2 * x) * (1 + 2 * (1 + Real.log K)) *
        (8 * heathBrownWindowRelevantFixedPolylogBound L X k M 1 * (R / N)) ^ 2 *
          (K : ℝ) ^ 3 := by
  let source : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k M 1
  let A : ℕ → ℝ := fun m => 8 * P * (R / N) * ((m : ℝ) + 1)
  have hsource : ∀ y : ℝ, ‖source y‖ ≤ P := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t M 1 y hM (by norm_num)
  have hP : 0 ≤ P := (norm_nonneg (source 0)).trans (hsource 0)
  have hsourceCont : Continuous source :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line L X k T0 t M 1
  have hA : ∀ m ∈ Finset.range K, 0 ≤ A m := by
    intro m hm
    dsimp only [A]
    positivity
  have hcell : ∀ m ∈ Finset.range K, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient source N R H 1 m v‖ ≤ A m := by
    intro m hm v hv
    have hmK : m < K := Finset.mem_range.mp hm
    have hmKreal : (m : ℝ) + 1 ≤ (K : ℝ) := by
      exact_mod_cast (show m + 1 ≤ K by omega)
    let y : ℝ := (m : ℝ) + v
    have hy0 : 0 ≤ y := by dsimp only [y]; linarith [hv.1]
    have hym : y ≤ (m : ℝ) + 1 := by dsimp only [y]; linarith [hv.2]
    have hyK : y ≤ K := hym.trans hmKreal
    let s : ℂ := (1 : ℂ) + (y : ℝ) * Complex.I
    have hsre : 0 < s.re := by simp [s]
    have hsnorm : ‖s - 1‖ = y := by
      rw [show s - 1 = (y : ℝ) * Complex.I by dsimp only [s]; ring]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0,
        Complex.norm_I, mul_one]
    have hsmallY : ‖s - 1‖ * (2 * R / N) ≤ 1 := by
      rw [hsnorm]
      exact (mul_le_mul_of_nonneg_right hyK (by positivity : 0 ≤ 2 * R / N)).trans hsmall
    have hkernel := norm_routeTNormalizedSmoothWindowMellin_sub_le_reference
      hN hH hR hHR hsre hsmallY
    have hkernel' :
        ‖routeTNormalizedSmoothWindowMellin N R s -
            routeTNormalizedSmoothWindowMellin N H s‖ ≤
          8 * ((m : ℝ) + 1) * (R / N) := by
      rw [show s.re = 1 by simp [s], sub_self, Real.rpow_zero, mul_one, hsnorm] at hkernel
      exact hkernel.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hym (by norm_num : (0 : ℝ) ≤ 8))
        (by positivity))
    rw [maynardFixedAmbientDefectCellCoefficient, norm_mul]
    change ‖source y‖ *
        ‖routeTNormalizedSmoothWindowMellin N R s -
          routeTNormalizedSmoothWindowMellin N H s‖ ≤ A m
    calc
      ‖source y‖ *
          ‖routeTNormalizedSmoothWindowMellin N R s -
            routeTNormalizedSmoothWindowMellin N H s‖ ≤
          P * (8 * ((m : ℝ) + 1) * (R / N)) :=
        mul_le_mul (hsource y) hkernel' (norm_nonneg _) hP
      _ = A m := by dsimp only [A]; ring
  have hL2 := integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_weighted_envelope
    (cellCount := K)
    hx (by norm_num : (1 : ℝ) ≤ 1) hN hR hH
      (Finset.range K) (by simp) source hsourceCont A hA hcell
  have hsumBase :
      (∑ m ∈ Finset.range K, ((m : ℝ) + 1) ^ 2) ≤ (K : ℝ) ^ 3 := by
    calc
      (∑ m ∈ Finset.range K, ((m : ℝ) + 1) ^ 2) ≤
          ∑ _m ∈ Finset.range K, (K : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        have hmKnat : m < K := Finset.mem_range.mp hm
        have hmK : (m : ℝ) + 1 ≤ (K : ℝ) := by
          exact_mod_cast (show m + 1 ≤ K by omega)
        exact pow_le_pow_left₀ (by positivity) hmK 2
      _ = (K : ℝ) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have hsumA :
      (∑ m ∈ Finset.range K, (A m) ^ 2) ≤
        (8 * P * (R / N)) ^ 2 * (K : ℝ) ^ 3 := by
    calc
      (∑ m ∈ Finset.range K, (A m) ^ 2) =
          (8 * P * (R / N)) ^ 2 *
            ∑ m ∈ Finset.range K, ((m : ℝ) + 1) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        dsimp only [A]
        ring
      _ ≤ (8 * P * (R / N)) ^ 2 * (K : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hsumBase (sq_nonneg _)
  have hfactor : 0 ≤ 4 * (2 * x) * (1 + 2 * (1 + Real.log K)) := by
    by_cases hK0 : K = 0
    · subst K
      norm_num
      exact zero_le_one.trans hx
    · have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK0
      have hlog : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK1)
      positivity
  have hweighted := mul_le_mul_of_nonneg_left hsumA hfactor
  dsimp only [source, A, P] at hL2 hweighted ⊢
  calc
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket (Finset.range K)
          (fun y : ℝ => heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
            ((1 : ℂ) + (y : ℝ) * Complex.I)) lambda N R H 1‖ ^ 2) ≤
      4 * (2 * x) ^ (2 * (1 - 1) + 1) *
        (1 + 2 * (1 + Real.log K)) *
          ∑ m ∈ Finset.range K,
            (8 * heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
              (R / N) * ((m : ℝ) + 1)) ^ 2 := hL2
    _ ≤ 4 * (2 * x) * (1 + 2 * (1 + Real.log K)) *
        (8 * heathBrownWindowRelevantFixedPolylogBound L X k M 1 * (R / N)) ^ 2 *
          (K : ℝ) ^ 3 := by
      norm_num at hweighted ⊢
      simpa only [mul_assoc] using hweighted

end

end RHTower.Sieve
