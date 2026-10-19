import GaloisForLFunctions.BiScaleUncertainty.FiniteGridNullCorrector
import GaloisForLFunctions.BiScaleUncertainty.EnergyControlledClosedCycleRecovery


/-!
# Fixed-energy full-grid ambiguity at every finite closed-cycle order

One singular-energy ceiling contains actual smooth compact sources that vanish
simultaneously at every positive integer-log node and agree in every normalized
closed product through any prescribed finite order, yet have different signed
correlations. A finite-null cross corrector enforces the entire grid; independent
source shapes retain the energy bound while their distant cross packets change sign.

The packet-charge mechanism is existing/classical. The theorem couples it to the
full logarithmic grid and one fixed source-energy ceiling. Its positive companions
are `EnergyControlledClosedCycleRecovery` and `ClosedCycleAmbiguityDecay`.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.ThreePacketParity
noncomputable section
set_option autoImplicit false

def profile (H C : ℝ → ℝ) (T x : ℝ) : ℝ := H x + C (x - T) + C (-x - T)

def packetIndex (D T x : ℝ) : ℤ := if |x| ≤ D then 0 else if |x - T| ≤ D then 1 else -1

def charge (D T : ℝ) (l : List ℝ) : ℤ := (l.map (packetIndex D T)).sum

def raw (H C : ℝ → ℝ) (T : ℝ) (l : List ℝ) : ℝ := (l.map (profile H C T)).prod

theorem profile_sign {H C : ℝ → ℝ} {D T : ℝ}
    (hH : ∀ x, D < |x| → H x = 0) (hC : ∀ x, D < |x| → C x = 0)
    (hT : 2 * D < T) (x : ℝ) :
    profile H (fun y => -C y) T x = (-1 : ℝ) ^ packetIndex D T x * profile H C T x := by
  by_cases hx : |x| ≤ D
  · have hb := abs_le.mp hx
    have hl := hC (x - T) (by have ha := neg_le_abs (x - T); linarith only [hb.2, hT, ha])
    have hr := hC (-x - T) (by have ha := neg_le_abs (-x - T); linarith only [hb.1, hT, ha])
    simp [profile, packetIndex, hx, hl, hr]
  · have hz := hH x (lt_of_not_ge hx)
    by_cases hy : |x - T| ≤ D <;> simp [profile, packetIndex, hx, hy, hz] <;> ring

private theorem packet_distance {H C : ℝ → ℝ} {D T : ℝ}
    (hH : ∀ x, D < |x| → H x = 0) (hC : ∀ x, D < |x| → C x = 0)
    {x : ℝ} (hp : profile H C T x ≠ 0) :
    |x - (packetIndex D T x : ℝ) * T| ≤ D := by
  by_cases hx : |x| ≤ D
  · simp [packetIndex, hx]
  · by_cases hy : |x - T| ≤ D
    · simp [packetIndex, hx, hy]
    · have hz : |x + T| ≤ D := by
        by_contra hz
        have hneg : D < |-x - T| := by
          rw [show -x - T = -(x + T) by ring, abs_neg]
          exact lt_of_not_ge hz
        apply hp
        simp only [profile, hH x (lt_of_not_ge hx), hC (x - T) (lt_of_not_ge hy),
          hC (-x - T) hneg, add_zero]
      simpa [packetIndex, hx, hy] using hz

theorem raw_sign {H C : ℝ → ℝ} {D T : ℝ}
    (hH : ∀ x, D < |x| → H x = 0) (hC : ∀ x, D < |x| → C x = 0)
    (hT : 2 * D < T) (l : List ℝ) :
    raw H (fun y => -C y) T l = (-1 : ℝ) ^ charge D T l * raw H C T l := by
  induction l with
  | nil => simp [raw, charge]
  | cons x l ih =>
    change profile H (fun y => -C y) T x * raw H (fun y => -C y) T l =
      (-1 : ℝ) ^ (packetIndex D T x + charge D T l) *
        (profile H C T x * raw H C T l)
    rw [profile_sign hH hC hT, ih, zpow_add₀ (by norm_num)]
    ring

private theorem sum_error_bound (D T : ℝ) (l : List ℝ)
    (h : ∀ x ∈ l, |x - (packetIndex D T x : ℝ) * T| ≤ D) :
    |l.sum - (charge D T l : ℝ) * T| ≤ (l.length : ℝ) * D := by
  induction l with
  | nil => simp [charge]
  | cons x l ih =>
    have hx := h x (by simp)
    have hl := ih (fun y hy => h y (by simp [hy]))
    have he : (x :: l).sum - (charge D T (x :: l) : ℝ) * T =
        (x - (packetIndex D T x : ℝ) * T) + (l.sum - (charge D T l : ℝ) * T) := by
      simp only [charge, List.map_cons, List.sum_cons, Int.cast_add]
      ring
    rw [he]
    calc
      _ ≤ |x - (packetIndex D T x : ℝ) * T| + |l.sum - (charge D T l : ℝ) * T| := abs_add_le _ _
      _ ≤ D + (l.length : ℝ) * D := add_le_add hx hl
      _ = ((x :: l).length : ℝ) * D := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- Closed products whose accumulated support width is below the separation
cannot detect side-packet sign reversal. The central and side shapes may differ. -/
theorem closed_products_eq {H C : ℝ → ℝ} {D T : ℝ} (hD : 0 ≤ D)
    (hH : ∀ x, D < |x| → H x = 0) (hC : ∀ x, D < |x| → C x = 0)
    (hT : 2 * D < T) (l : List ℝ) (hs : l.sum = 0)
    (hshort : (l.length : ℝ) * D < T) :
    raw H (fun y => -C y) T l = raw H C T l := by
  rw [raw_sign hH hC hT]
  by_cases hp : raw H C T l = 0
  · simp only [hp, mul_zero]
  have hT0 : 0 < T := by linarith only [hD, hT]
  have hb := sum_error_bound D T l (by
    intro x hx
    apply packet_distance hH hC
    intro hz
    apply hp
    exact List.prod_eq_zero_iff.mpr (List.mem_map.mpr ⟨x, hx, hz⟩))
  rw [hs, zero_sub, abs_neg] at hb
  have hbounds := abs_lt.mp (hb.trans_lt hshort)
  have hq : charge D T l = 0 := by
    by_contra hn
    have hi : charge D T l ≤ -1 ∨ 1 ≤ charge D T l := by omega
    rcases hi with hi | hi
    · have hir : (charge D T l : ℝ) ≤ -1 := by exact_mod_cast hi
      have hm := mul_le_mul_of_nonneg_right hir hT0.le
      linarith only [hm, hbounds.1]
    · have hir : (1 : ℝ) ≤ charge D T l := by exact_mod_cast hi
      have hm := mul_le_mul_of_nonneg_right hir hT0.le
      linarith only [hm, hbounds.2]
  rw [hq, zpow_zero, one_mul]

end
end GaloisForLFunctions.BiScaleUncertainty.ThreePacketParity

namespace GaloisForLFunctions.BiScaleUncertainty.GridCycleAmbiguity
noncomputable section
set_option autoImplicit false
open FiniteNullCorrector


/-- A single actual corrector annihilates the entire shifted integer-log grid.
The support radius is independent of the shift and of the number of constraints. -/
theorem exists_full_grid_cross_null_source {f : ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hR : 0 < autocorr f 0) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ u, r < |u| → f u = 0) (T : ℝ) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧ HasCompactSupport v ∧
      (∀ u, 2 * r < |u| → v u = 0) ∧
      (∀ n : ℕ, cross f v (Real.log n - T) = 0) ∧ ∃ x, cross f v x ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (T + 3 * r))
  obtain ⟨v, hv, hvc, hvs, hz, hnonzero⟩ := exists_smooth_corrector hf hfc hR hr hsupp N
    (fun i => Real.log (i : ℕ) - T)
  refine ⟨v, hv, hvc, hvs, ?_, hnonzero⟩
  intro n
  by_cases hn : n < N
  · exact hz ⟨n, hn⟩
  · have hle : (N : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_not_gt hn)
    have hexp : Real.exp (T + 3 * r) < (n : ℝ) := hN.trans_le hle
    have hl := Real.log_lt_log (Real.exp_pos (T + 3 * r)) hexp
    rw [Real.log_exp] at hl
    apply SeparatedSourcePair.cross_eq_zero_of_source_radii hsupp hvs
    have ha := le_abs_self (Real.log n - T)
    linarith only [hl, ha]


/-- A fixed singular-energy ceiling and simultaneous zeros on the entire
integer-log grid do not give any uniform exact closed-cycle detection order.
The witnesses are actual smooth compactly supported sources. -/
theorem exists_full_grid_bounded_energy_cycle_aliases :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, ∃ p q : LevyEnergySource K,
      (ContDiff ℝ (↑(⊤ : ℕ∞)) (p.source : ℝ → ℝ) ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) (q.source : ℝ → ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n → p.correlation (Real.log n) = 0 ∧ q.correlation (Real.log n) = 0) ∧
      (∀ l : List ℝ, l.length ≤ m → EnergyCycle.value p l = EnergyCycle.value q l) ∧
      ∃ x : ℝ, p.correlation x ≠ q.correlation x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let r := Real.log 2 / 8
  have hr : 0 < r := by dsimp only [r]; positivity
  have hsmall : 4 * r < Real.log 2 := by dsimp only [r]; linarith only [hlog2]
  obtain ⟨u, hu, huc, huR, hus⟩ := exists_smooth_source_in_radius hr
  have huE := biScaleLevyEnergy_nonneg huc hu.continuous
  let K := 2 * (biScaleLevyEnergy u + 1) / autocorr u 0
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro m
  let D := 4 * r
  have hD : 0 < D := by dsimp only [D]; positivity
  let T := ((m : ℝ) + 2) * D + 1
  have hT : 2 * D < T := by
    have hm := mul_nonneg (Nat.cast_nonneg m) hD.le
    dsimp only [T]
    nlinarith only [hm]
  have hmT : (m : ℝ) * D < T := by dsimp only [T]; nlinarith only [hD]
  obtain ⟨v, hv, hvc, hvs, hzgrid, hznonzero⟩ :=
    exists_full_grid_cross_null_source hu huc huR hr hus T
  have hvE := biScaleLevyEnergy_nonneg hvc hv.continuous
  let a := 1 / (1 + biScaleLevyEnergy v)
  have ha : 0 < a := by dsimp only [a]; positivity
  have haE : a ^ 2 * biScaleLevyEnergy v ≤ 1 := by
    have he : a ^ 2 * biScaleLevyEnergy v =
        biScaleLevyEnergy v / (1 + biScaleLevyEnergy v) ^ 2 := by
      dsimp only [a]
      rw [div_pow, one_pow]
      ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith only [hvE] : 0 < 1 + biScaleLevyEnergy v))).mpr
    nlinarith only [hvE, sq_nonneg (biScaleLevyEnergy v)]
  have hlevel : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hup := SeparatedSourcePair.source_smooth hu hv a T
  have hum := SeparatedSourcePair.source_smooth hu hv (-a) T
  let Fp : C_c(ℝ, ℝ) :=
    ⟨⟨SeparatedSourcePair.source u v a T, hup.continuous⟩,
      SeparatedSourcePair.source_compact huc hvc a T⟩
  let Fm : C_c(ℝ, ℝ) :=
    ⟨⟨SeparatedSourcePair.source u v (-a) T, hum.continuous⟩,
      SeparatedSourcePair.source_compact huc hvc (-a) T⟩
  let M := autocorr u 0 + a ^ 2 * autocorr v 0
  have hMR : autocorr u 0 ≤ M := by
    have hnonneg := mul_nonneg (sq_nonneg a) (autocorr_zero_nonneg v)
    dsimp only [M]
    linarith only [hnonneg]
  have hM : 0 < M := huR.trans_le hMR
  have hzT : cross u v (-T) = 0 := by
    simpa only [Nat.cast_zero, Real.log_zero, zero_sub] using hzgrid 0
  have hmass (b : ℝ) : autocorr (SeparatedSourcePair.source u v b T) 0 =
      autocorr u 0 + b ^ 2 * autocorr v 0 := by
    rw [SeparatedSourcePair.source_correlation hu.continuous hv.continuous huc hvc]
    simp only [zero_sub, neg_zero, hzT, mul_zero, add_zero]
  have hMp : autocorr Fp 0 = M := hmass a
  have hMm : autocorr Fm 0 = M := by
    change autocorr (SeparatedSourcePair.source u v (-a) T) 0 =
      autocorr u 0 + a ^ 2 * autocorr v 0
    simpa only [neg_sq] using hmass (-a)
  have hEp : 0 ≤ biScaleLevyEnergy Fp := biScaleLevyEnergy_nonneg Fp.hasCompactSupport Fp.continuous
  have hEm : 0 ≤ biScaleLevyEnergy Fm := biScaleLevyEnergy_nonneg Fm.hasCompactSupport Fm.continuous
  have hpair : biScaleLevyEnergy Fp + biScaleLevyEnergy Fm =
      2 * (biScaleLevyEnergy u + a ^ 2 * biScaleLevyEnergy v) :=
    SeparatedSourcePair.source_energy_pair (hu.of_le hlevel) (hv.of_le hlevel) huc hvc a T
  have hEpbound : biScaleLevyEnergy Fp ≤ 2 * (biScaleLevyEnergy u + 1) := by
    nlinarith only [hpair, hEm, haE]
  have hEmbound : biScaleLevyEnergy Fm ≤ 2 * (biScaleLevyEnergy u + 1) := by
    nlinarith only [hpair, hEp, haE]
  have hcap : 0 ≤ 2 * (biScaleLevyEnergy u + 1) := by positivity
  have hnorm (F : C_c(ℝ, ℝ)) (hMF : autocorr F 0 = M)
      (hEF : biScaleLevyEnergy F ≤ 2 * (biScaleLevyEnergy u + 1)) :
      normalizedArchEnergy F ≤ K := by
    change biScaleLevyEnergy F / autocorr F 0 ≤ 2 * (biScaleLevyEnergy u + 1) / autocorr u 0
    rw [hMF]
    apply (div_le_div_iff₀ hM huR).mpr
    exact (mul_le_mul_of_nonneg_right hEF huR.le).trans (mul_le_mul_of_nonneg_left hMR hcap)
  let p : LevyEnergySource K :=
    ⟨Fp, hup.of_le hlevel, by rw [hMp]; exact hM, hnorm Fp hMp hEpbound⟩
  let q : LevyEnergySource K :=
    ⟨Fm, hum.of_le hlevel, by rw [hMm]; exact hM, hnorm Fm hMm hEmbound⟩
  let H : ℝ → ℝ := fun x => autocorr u x + a ^ 2 * autocorr v x
  let C : ℝ → ℝ := fun x => a * cross u v x
  have hHp (x : ℝ) (hx : D < |x|) : H x = 0 := by
    have hux : autocorr u x = 0 := autocorr_eq_zero_of_source_radius hus (by
      dsimp only [D] at hx
      linarith only [hx, hr])
    have hvx : autocorr v x = 0 := autocorr_eq_zero_of_source_radius hvs (by
      dsimp only [D] at hx
      linarith only [hx])
    simp only [H, hux, hvx, mul_zero, add_zero]
  have hCp (x : ℝ) (hx : D < |x|) : C x = 0 := by
    have hz := SeparatedSourcePair.cross_eq_zero_of_source_radii hus hvs (x := x) (by
      dsimp only [D] at hx
      linarith only [hx, hr])
    simp only [C, hz, mul_zero]
  have hFp : autocorr Fp = ThreePacketParity.profile H C T := by
    funext x
    exact SeparatedSourcePair.source_correlation hu.continuous hv.continuous huc hvc a T x
  have hFm : autocorr Fm = ThreePacketParity.profile H (fun x => -C x) T := by
    funext x
    change autocorr (SeparatedSourcePair.source u v (-a) T) x = _
    rw [SeparatedSourcePair.source_correlation hu.continuous hv.continuous huc hvc]
    dsimp only [ThreePacketParity.profile, H, C]
    ring
  refine ⟨p, q, ⟨hup, hum⟩, ?_, ?_, ?_⟩
  · intro n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : D < Real.log n :=
      hsmall.trans_le (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnR)
    have hHz := hHp (Real.log n) (hlog.trans_le (le_abs_self _))
    have hCz : C (Real.log n - T) = 0 := by simp only [C, hzgrid n, mul_zero]
    have hCneg : C (-Real.log n - T) = 0 := by
      apply hCp
      have hb := neg_le_abs (-Real.log n - T)
      linarith only [hb, hlog, hT, hD]
    have hpz : autocorr Fp (Real.log n) = 0 := by
      rw [hFp]
      simp only [ThreePacketParity.profile, hHz, hCz, hCneg, add_zero]
    have hqz : autocorr Fm (Real.log n) = 0 := by
      rw [hFm]
      simp only [ThreePacketParity.profile, hHz, hCz, hCneg, neg_zero, add_zero]
    constructor
    · change autocorr Fp (Real.log n) / autocorr Fp 0 = 0
      rw [hpz, zero_div]
    · change autocorr Fm (Real.log n) / autocorr Fm 0 = 0
      rw [hqz, zero_div]
  · intro l hl
    have hclosed : SeparatedCycle.closedProduct Fp l = SeparatedCycle.closedProduct Fm l := by
      unfold SeparatedCycle.closedProduct
      split_ifs with hs
      · have hlR : (l.length : ℝ) ≤ m := by exact_mod_cast hl
        have hshort := (mul_le_mul_of_nonneg_right hlR hD.le).trans_lt hmT
        have he := ThreePacketParity.closed_products_eq hD.le hHp hCp hT l hs hshort
        change (l.map (autocorr Fp)).prod = (l.map (autocorr Fm)).prod
        rw [hFp, hFm]
        exact he.symm
      · rfl
    rw [EnergyCycle.value_eq_normalized, EnergyCycle.value_eq_normalized]
    change SeparatedCycle.closedProduct Fp l / autocorr Fp 0 ^ l.length =
      SeparatedCycle.closedProduct Fm l / autocorr Fm 0 ^ l.length
    rw [hMp, hMm, hclosed]
  · obtain ⟨z, hz⟩ := hznonzero
    have hCz : C z ≠ 0 := mul_ne_zero ha.ne' hz
    have hzD : |z| ≤ D := le_of_not_gt (fun h => hCz (hCp z h))
    have hremote : C (-(T + z) - T) = 0 := by
      apply hCp
      have hb := neg_le_abs (-(T + z) - T)
      have hzlo := (abs_le.mp hzD).1
      linarith only [hb, hzlo, hT, hD]
    have hraw : autocorr Fp (T + z) ≠ autocorr Fm (T + z) := by
      intro he
      rw [hFp, hFm] at he
      dsimp only [ThreePacketParity.profile] at he
      simp only [show T + z - T = z by ring, hremote] at he
      apply hCz
      linarith only [he]
    refine ⟨T + z, ?_⟩
    intro he
    change autocorr Fp (T + z) / autocorr Fp 0 = autocorr Fm (T + z) / autocorr Fm 0 at he
    rw [hMp, hMm] at he
    field_simp [hM.ne'] at he
    exact hraw he

end
end GaloisForLFunctions.BiScaleUncertainty.GridCycleAmbiguity
