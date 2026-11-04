import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsReadTheNonpolarCenter
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheUpwardPrimeWindowsCarryTheShellCorrection
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompletedShellEnergyIsAPositiveFourierIntegral
import GaloisForLFunctions.RHTower.ThetaIntegerCutoffMovingPacket

/-!
# Terminal upward shells have their polar mean

The polar shell is a dilated Riemann sum. The nonpolar shell consists
of two shifted mean-zero periodic sequences. Both descriptions retain
uniform errors when the shell centre stays in a terminal interval.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- A compact Lipschitz kernel has a uniform dilated right-endpoint sum estimate. -/
theorem abs_sum_terminal_shell_sub_integral_le
    {K : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hKL : ∀ x y, |K x - K y| ≤ L * |x - y|)
    (hzero : ∀ x, 1 ≤ x → K x = 0)
    {r : ℝ} (hr : 0 < r) {H : ℕ} (hrH : r ≤ H) :
    |(∑ j ∈ Icc 1 H, K ((j : ℝ) / r)) - r * ∫ x in (0 : ℝ)..1, K x| ≤
      L * H / r := by
  let L' : NNReal := ⟨L, hL⟩
  have hLip : LipschitzWith L' K := LipschitzWith.of_dist_le_mul fun x y => by
    change |K x - K y| ≤ L * |x - y|
    exact hKL x y
  have htop : 1 ≤ (H : ℝ) * (1 / r) := by
    rw [mul_one_div, le_div_iff₀ hr, one_mul]
    exact hrH
  have hi : (∫ x in (0 : ℝ)..(H : ℝ) * (1 / r), K x) = ∫ x in (0 : ℝ)..1, K x := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hLip.continuous.intervalIntegrable 0 1 : IntervalIntegrable K volume 0 1)
      (hLip.continuous.intervalIntegrable 1 ((H : ℝ) * (1 / r)) :
        IntervalIntegrable K volume 1 ((H : ℝ) * (1 / r)))
    have hz : (∫ x in (1 : ℝ)..(H : ℝ) * (1 / r), K x) = 0 := by
      rw [intervalIntegral.integral_of_le htop]
      exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => hzero x hx.1.le
    rw [hz, add_zero] at hadd
    exact hadd.symm
  have hb := _root_.RHTower.abs_riemannSum_sub_integral_le
    hLip.lipschitzOnWith hLip.continuous.continuousOn H (one_div_nonneg.mpr hr.le) le_rfl
  rw [hi] at hb
  have hs : (∑ j ∈ Icc 1 H, K ((j : ℝ) / r)) =
      ∑ i ∈ range H, K (((i : ℝ) + 1) * (1 / r)) := by
    rw [_root_.RHTower.sum_Icc_one_eq_sum_range_succ]
    exact sum_congr rfl fun i _ => by rw [Nat.cast_add, Nat.cast_one]; congr 1; ring
  rw [hs]
  have he : (∑ i ∈ range H, K (((i : ℝ) + 1) * (1 / r))) -
      r * ∫ x in (0 : ℝ)..1, K x =
      r * ((1 / r) * (∑ i ∈ range H, K (((i : ℝ) + 1) * (1 / r))) -
        ∫ x in (0 : ℝ)..1, K x) := by field_simp [hr.ne'] <;> ring
  rw [he, abs_mul, abs_of_pos hr]
  exact (mul_le_mul_of_nonneg_left hb hr.le).trans_eq (by
    change r * (L * (H : ℝ) * (1 / r) ^ 2) = L * H / r
    field_simp [hr.ne'] <;> ring)

/-- Truncation at a prime-multiple horizon costs at most one Riemann cell. -/
theorem abs_terminal_truncated_riemannSum_sub_integral_le
    {F : ℝ → ℝ} {B L : ℝ} (hF : ∀ x, |F x| ≤ B) (hL : 0 ≤ L)
    (hFL : ∀ x y, |F x - F y| ≤ L * |x - y|)
    {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    |(∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N)) / N -
      ∫ x in (0 : ℝ)..1 / k, F x| ≤ (L + B) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hB : 0 ≤ B := (abs_nonneg _).trans (hF 0)
  let J : ℕ := N / k
  let t : ℝ := J / N
  have hJlo : (J : ℝ) ≤ (N : ℝ) / k := by
    rw [show J = ⌊(N : ℝ) / k⌋₊ by rw [Nat.floor_div_eq_div]]
    exact Nat.floor_le (div_nonneg hN0.le hk0.le)
  have hJhi : (N : ℝ) / k < (J : ℝ) + 1 := by
    rw [show J = ⌊(N : ℝ) / k⌋₊ by rw [Nat.floor_div_eq_div]]
    exact Nat.lt_floor_add_one _
  have hcancel : ((N : ℝ) / k) / N = 1 / k := by field_simp [hN0.ne', hk0.ne']
  have ht : t ≤ 1 / k := by
    have hh := div_le_div_of_nonneg_right hJlo hN0.le
    rwa [hcancel] at hh
  have hgap : 1 / k - t ≤ 1 / N := by
    have hh := (div_lt_div_iff_of_pos_right hN0).mpr hJhi
    rw [hcancel, add_div] at hh
    change 1 / (k : ℝ) < t + 1 / N at hh
    linarith only [hh]
  let L' : NNReal := ⟨L, hL⟩
  have hLip : LipschitzWith L' F := LipschitzWith.of_dist_le_mul fun x y => by
    change |F x - F y| ≤ L * |x - y|
    exact hFL x y
  have hriemann := _root_.RHTower.abs_riemannSum_sub_integral_le
    hLip.lipschitzOnWith hLip.continuous.continuousOn J
    (one_div_nonneg.mpr hN0.le) (show (J : ℝ) * (1 / N) ≤ 1 / k by simpa only [mul_one_div] using ht)
  have hs : (1 / (N : ℝ)) * (∑ i ∈ range J, F (((i : ℝ) + 1) * (1 / N))) =
      (∑ n ∈ Icc 1 J, F ((n : ℝ) / N)) / N := by
    rw [_root_.RHTower.sum_Icc_one_eq_sum_range_succ, sum_div, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [Nat.cast_add, Nat.cast_one]
    rw [show (((i : ℝ) + 1) * (1 / N)) = ((i : ℝ) + 1) / N by ring]
    ring
  rw [hs, mul_one_div] at hriemann
  have hmean : |(∑ n ∈ Icc 1 J, F ((n : ℝ) / N)) / N - ∫ x in (0 : ℝ)..t, F x| ≤ L / N := by
    apply hriemann.trans
    change L * J * (1 / (N : ℝ)) ^ 2 ≤ L / N
    have hJN : (J : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N k
    calc
      _ ≤ L * N * (1 / (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJN hL) (sq_nonneg _)
      _ = _ := by field_simp [hN0.ne']
  have htail : |∫ x in t..1 / (k : ℝ), F x| ≤ B / N := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := 1 / (k : ℝ)) (C := B) (f := F)
      (fun x _ => by simpa only [Real.norm_eq_abs] using hF x)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht)] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hgap hB).trans_eq (by ring))
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hLip.continuous.intervalIntegrable 0 t : IntervalIntegrable F volume 0 t)
    (hLip.continuous.intervalIntegrable t (1 / (k : ℝ)) : IntervalIntegrable F volume t (1 / (k : ℝ)))
  change |(∑ n ∈ Icc 1 J, F ((n : ℝ) / N)) / N - ∫ x in (0 : ℝ)..1 / k, F x| ≤ _
  rw [← hadd, sub_add_eq_sub_sub]
  exact ((abs_sub _ _).trans (add_le_add hmean htail)).trans_eq (by ring)

/-- The polar affine shell has its integral mean, with the literal Riemann error. -/
theorem abs_upwardShellModel_one_sub_mean_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hGL : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ L * |x - y|)
    {N H p : ℕ} (hp : 1 ≤ p) (hpN : p ≤ N) (hH : c ≤ H) :
    |upwardShellModel φ c N 1 H p -
      ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) * (c * p / N)| ≤
        2 * L * H / ((∫ u, φ u ^ 2) * (c * p / N)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (hp.trans hpN)
  let r : ℝ := c * p / N
  have hr : 0 < r := div_pos (mul_pos hc hp0) hN0
  have hrH : r ≤ H := by
    apply le_trans _ hH
    apply (div_le_iff₀ hN0).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpN) hc.le
  have hb := abs_sum_terminal_shell_sub_integral_le hL hGL
    (fun x hx => shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (hx.trans (le_abs_self x))) hr hrH
  have he : upwardShellModel φ c N 1 H p =
      (2 / (∫ u, φ u ^ 2)) * ∑ j ∈ Icc 1 H, shellAutocorr φ ((j : ℝ) / r) := by
    unfold upwardShellModel
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [ramanujanLagCoefficient_one, ramanujanLagCoefficient_one]
    have hx : (j : ℝ) * N / (c * p) = (j : ℝ) / r := by
      dsimp only [r]
      field_simp [hc.ne', hp0.ne', hN0.ne']
    rw [hx]
    ring
  have hmean : ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) * r =
      (2 / (∫ u, φ u ^ 2)) * (r * ∫ x in (0 : ℝ)..1, shellAutocorr φ x) := by
    rw [← two_mul_integral_shellAutocorr hφ hsupp]
    ring
  change |upwardShellModel φ c N 1 H p - ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) * r| ≤ _
  rw [he, hmean, ← mul_sub, abs_mul, abs_of_pos (div_pos two_pos hM)]
  exact (mul_le_mul_of_nonneg_left hb (div_nonneg two_pos.le hM.le)).trans_eq (by
    dsimp only [r]; ring)

/-- Reflection changes the descending affine shell into an ordinary shifted Ramanujan sequence. -/
theorem ramanujanLagCoefficient_reflected_affine {m : ℕ} (hm : 1 ≤ m) (p j : ℕ) :
    ramanujanLagCoefficient m (p + (m - 1) * j) =
      ramanujanLagCoefficient m ((m - 1) * p + j) := by
  unfold ramanujanLagCoefficient
  apply sum_congr rfl
  intro d hd
  have hsum : d ∣ (p + (m - 1) * j) + ((m - 1) * p + j) := by
    have he : (p + (m - 1) * j) + ((m - 1) * p + j) = m * (p + j) := by
      calc
        _ = ((m - 1) + 1) * (p + j) := by ring
        _ = _ := by rw [Nat.sub_add_cancel hm]
    rw [he]
    exact (Nat.dvd_of_mem_divisors hd).mul_right _
  have he : d ∣ p + (m - 1) * j ↔ d ∣ (m - 1) * p + j :=
    ⟨fun h => (Nat.dvd_add_right h).mp hsum, fun h => (Nat.dvd_add_left h).mp hsum⟩
  simp only [he]

/-- A nonpolar affine shell has a bounded periodic error and no linear mean. -/
theorem abs_upwardShellModel_nonpolar_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hGL : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ L * |x - y|)
    {N H p m : ℕ} (hN : 1 ≤ N) (hH : 1 ≤ H) (hp : 1 ≤ p) (hm : 2 ≤ m) :
    |upwardShellModel φ c N m H p| ≤
      4 * m * m.totient * (1 + L * H / ((∫ u, φ u ^ 2) * (c * p / N))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  let r : ℝ := c * p / N
  have hr : 0 < r := div_pos (mul_pos hc hp0) hN0
  let G : ℝ → ℝ := fun x => shellAutocorr φ ((H : ℝ) * x / r) / (∫ u, φ u ^ 2)
  let LG : ℝ := L * H / ((∫ u, φ u ^ 2) * r)
  have hLG : 0 ≤ LG := by dsimp only [LG]; positivity
  have hGb : ∀ x, |G x| ≤ 1 := by
    intro x
    dsimp only [G]
    rw [abs_div, abs_of_pos hM]
    exact (div_le_one hM).mpr (abs_shellAutocorr_le hφ hsupp _)
  have hGl : ∀ x y, |G x - G y| ≤ LG * |x - y| := by
    intro x y
    dsimp only [G]
    rw [← sub_div, abs_div, abs_of_pos hM]
    calc
      _ ≤ L * |(H : ℝ) * x / r - (H : ℝ) * y / r| / (∫ u, φ u ^ 2) :=
        div_le_div_of_nonneg_right (hGL _ _) hM.le
      _ = LG * |x - y| := by
        rw [show (H : ℝ) * x / r - (H : ℝ) * y / r = ((H : ℝ) / r) * (x - y) by ring,
          abs_mul, abs_of_nonneg (div_nonneg hH0.le hr.le)]
        dsimp only [LG]
        ring
  have hperiod : ∀ n, ramanujanLagCoefficient m (n + m) = ramanujanLagCoefficient m n :=
    fun n => by simpa only [mul_one] using ramanujanLagCoefficient_add_mul m n 1
  have hmean : periodicMean (ramanujanLagCoefficient m) m = 0 := by
    rw [periodicMean, sum_range_ramanujanLagCoefficient (by omega), if_neg (by omega), zero_div]
  have h₁ := abs_terminal_shifted_periodic_zero_mean_le hGb hLG hGl
    (by omega : 0 < m) hperiod hmean
    (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m) hH le_rfl 0 p
  have h₂ := abs_terminal_shifted_periodic_zero_mean_le hGb hLG hGl
    (by omega : 0 < m) hperiod hmean
    (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m)
    hH le_rfl 0 ((m - 1) * p)
  simp only [Nat.add_zero] at h₁ h₂
  have he : upwardShellModel φ c N m H p =
      (∑ j ∈ Icc 1 H, G ((j : ℝ) / H) * ramanujanLagCoefficient m (j + p)) +
      ∑ j ∈ Icc 1 H, G ((j : ℝ) / H) * ramanujanLagCoefficient m (j + (m - 1) * p) := by
    unfold upwardShellModel
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rw [ramanujanLagCoefficient_reflected_affine (by omega : 1 ≤ m)]
    have hG : G ((j : ℝ) / H) = shellAutocorr φ ((j : ℝ) * N / (c * p)) / (∫ u, φ u ^ 2) := by
      dsimp only [G]
      congr 1
      congr 1
      dsimp only [r]
      field_simp [hH0.ne', hc.ne', hp0.ne', hN0.ne']
    rw [hG, Nat.add_comm p j, Nat.add_comm ((m - 1) * p) j]
    ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by dsimp only [LG, r]; ring)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_upwardShellModel_one_sub_mean_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_truncated_riemannSum_sub_integral_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ramanujanLagCoefficient_reflected_affine
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_upwardShellModel_nonpolar_le
