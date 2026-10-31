import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorMoments
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.FullShellRows
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.NonpolarJointCancellation

/-!
# Mixed Ramanujan–polar top-band cancellation

The mean of the logarithmic divisor jet cancels the harmonic Ramanujan
pole moment exactly. The remaining two periodic shell rows and the lattice
quadrature error have bounded top-band harmonic mass. Thus every nonpolar
Ramanujan base with a constant top-band partner has joint coefficient
`Oφ(m (sqrt(φ(m))+V_m) G (1+log N))`, uniformly for `1≤c≤N/4`.
-/

open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics CriticalArithmeticCorrelationTheory
  BezoutValuationIncidence ArithmeticFunction
noncomputable section

/-- The full smooth shell row, including its ratio diagonal. -/
def fullShellReading (g : ℝ → ℝ) (N : ℕ) (w : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  poleVector n * ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)), shellPartnerKernel g n ℓ * a ℓ

theorem fullShellReading_log (g : ℝ → ℝ) (N : ℕ) (w : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    fullShellReading g N w (fun ℓ => Real.log ℓ * a ℓ) n =
      poleVector n * ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)), rowIntegrand g n ℓ * a ℓ := by
  rw [fullShellReading]
  congr 1
  apply sum_congr rfl
  intro ℓ _
  rw [shellPartnerKernel, rowIntegrand]
  ring

theorem abs_sum_topBand_le_of_reciprocal {w C : ℝ} (hw : 0 ≤ w) (hC : 0 ≤ C)
    (N : ℕ) (F : ℕ → ℝ) (hF : ∀ n ∈ topBand N w, |F n| ≤ C / (n : ℝ)) :
    |∑ n ∈ topBand N w, F n| ≤ 2 * C := by
  calc
    _ ≤ ∑ n ∈ topBand N w, |F n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ topBand N w, C / (n : ℝ) := sum_le_sum hF
    _ = C * ∑ n ∈ topBand N w, 1 / (n : ℝ) := by rw [mul_sum]; simp only [mul_one_div]
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left (sum_topBand_inv_le_two hw N) hC
    _ = _ := mul_comm _ _

theorem shellTopCoefficient_eq_fullShellReading {g : ℝ → ℝ} {w : ℝ} (hw : 0 ≤ w)
    (a ψ : ℕ → ℝ) (N : ℕ) :
    shellTopCoefficient g a ψ N w =
      (∑ n ∈ topBand N w, ψ n * fullShellReading g N w (horizonDivisorCoefficient a N) n) -
      (∫ u, g u ^ 2) * ∑ n ∈ topBand N w, ψ n * horizonDivisorCoefficient a N n / (n : ℝ) := by
  have hkernel (ℓ n : ℕ) :
      poleVector ℓ * shellPartnerKernel g ℓ n = poleVector n * shellPartnerKernel g n ℓ := by
    have he : bumpCorr g (Real.log n - Real.log ℓ) = bumpCorr g (Real.log ℓ - Real.log n) := by
      rw [← bumpCorr_neg (g := g) (Real.log n - Real.log ℓ), neg_sub]
    rw [shellPartnerKernel, shellPartnerKernel, he]
    unfold poleVector
    ring
  rw [shellTopCoefficient_eq_product_sum hw]
  congr 1
  simp only [fullShellReading, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro ℓ _
  calc
    _ = horizonDivisorCoefficient a N ℓ *
        (poleVector ℓ * shellPartnerKernel g ℓ n) * ψ n := by ring
    _ = _ := by rw [hkernel]; ring

theorem fullShellReading_horizon_ramanujan {m N : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {w : ℝ} (hL : Nat.ceil ((N : ℝ) * Real.exp w) ≤ 2 * N) (n : ℕ) :
    fullShellReading g N w (horizonDivisorCoefficient (normalizedRamanujanMode m) N) n =
      fullShellReading g N w (fun ℓ => Real.log ℓ * normalizedRamanujanMode m ℓ) n -
        fullShellReading g N w (centeredRamanujanJet m) n -
        (vonMangoldt m / Real.sqrt (m.totient : ℝ)) *
          fullShellReading g N w (fun _ => 1) n := by
  have he (ℓ : ℕ) (hℓ : ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w))) :
      horizonDivisorCoefficient (normalizedRamanujanMode m) N ℓ =
        Real.log ℓ * normalizedRamanujanMode m ℓ - centeredRamanujanJet m ℓ -
          vonMangoldt m / Real.sqrt (m.totient : ℝ) := by
    rw [horizonDivisorCoefficient_ramanujan_eq hm (mem_Icc.mp hℓ).1
      ((mem_Icc.mp hℓ).2.trans hL), centeredRamanujanJet]
    ring
  rw [fullShellReading]
  have hs := sum_congr rfl (fun (ℓ : ℕ) hℓ => congrArg
    (fun t => shellPartnerKernel g n ℓ * t) (he ℓ hℓ))
  rw [hs]
  simp only [fullShellReading, mul_sub, sum_sub_distrib, mul_one, ← sum_mul]
  ring

/-- The divisor-jet mean and the harmonic pole occur with opposite signs in the literal block. -/
theorem jointTopCoefficient_ramanujan_const_eq {m N : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {w : ℝ} (hw : 0 ≤ w)
    (hL : Nat.ceil ((N : ℝ) * Real.exp w) ≤ 2 * N) :
    jointTopCoefficient g (normalizedRamanujanMode m) (fun _ => 1) N w =
      (poleWeightMinus g * poleWeightPlus g) *
        (((∑ n ∈ Icc 1 N, normalizedRamanujanMode m n / (n : ℝ)) +
            vonMangoldt m / Real.sqrt (m.totient : ℝ)) * (topBand N w).card +
          (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n) * (∑ n ∈ topBand N w, 1 / (n : ℝ))) -
      (∑ n ∈ topBand N w,
        fullShellReading g N w (fun ℓ => Real.log ℓ * normalizedRamanujanMode m ℓ) n) +
      (∑ n ∈ topBand N w, fullShellReading g N w (centeredRamanujanJet m) n) +
      (vonMangoldt m / Real.sqrt (m.totient : ℝ)) *
        (∑ n ∈ topBand N w,
          (fullShellReading g N w (fun _ => 1) n - poleWeightMinus g * poleWeightPlus g)) +
      (∫ u, g u ^ 2) *
        (∑ n ∈ topBand N w, horizonDivisorCoefficient (normalizedRamanujanMode m) N n / (n : ℝ)) := by
  rw [jointTopCoefficient, shellTopCoefficient_eq_fullShellReading hw]
  simp only [one_mul]
  simp_rw [fullShellReading_horizon_ramanujan hm hL]
  simp only [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one]
  ring

/-- After subtracting the exact Mangoldt mean, the two polar terms have bounded total mass. -/
theorem abs_ramanujan_centered_polar_coefficient_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {m : ℕ} (hm : 2 ≤ m) {w : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4) (N : ℕ) :
    |(poleWeightMinus (atomDilate φ w) * poleWeightPlus (atomDilate φ w)) *
        (((∑ n ∈ Icc 1 N, normalizedRamanujanMode m n / (n : ℝ)) +
            vonMangoldt m / Real.sqrt (m.totient : ℝ)) * (topBand N w).card +
          (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n) * (∑ n ∈ topBand N w, 1 / (n : ℝ)))| ≤
      6 * m * Real.sqrt (m.totient : ℝ) * (∫ u, atomDilate φ w u ^ 2) := by
  have hm0 : 0 < m := by omega
  set U := Real.sqrt (m.totient : ℝ)
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hcard : ((topBand N w).card : ℝ) ≤ (N : ℝ) + 1 := by
    have h : (topBand N w).card ≤ N := by
      have hsub : topBand N w ⊆ Icc 1 N := fun n hn => (mem_topBand.mp hn).1
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
    have hR : ((topBand N w).card : ℝ) ≤ N := by exact_mod_cast h
    linarith only [hR]
  have htail := abs_normalizedRamanujan_harmonic_add_vonMangoldt_le hm N
  have hordinary : |∑ n ∈ Icc 1 N, normalizedRamanujanMode m n| ≤ 2 * m * U := by
    simpa only [Ico_add_one_right_eq_Icc] using
      abs_sum_Ico_periodic_mean_zero_le (by omega : 1 ≤ m) (normalizedRamanujanMode m)
        (normalizedRamanujanMode_periodic hm0) (sum_range_normalizedRamanujanMode hm)
        (SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm0) 1 (N + 1)
  have hST : |∑ n ∈ topBand N w, 1 / (n : ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (sum_nonneg fun n _ => by positivity)]
    exact sum_topBand_inv_le_two hw.le N
  have hfirst :
      |((∑ n ∈ Icc 1 N, normalizedRamanujanMode m n / (n : ℝ)) +
          vonMangoldt m / Real.sqrt (m.totient : ℝ)) * (topBand N w).card| ≤ 2 * m * U := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ ((topBand N w).card : ℝ) from Nat.cast_nonneg _)]
    have h := mul_le_mul htail hcard (Nat.cast_nonneg _) (by positivity)
    exact h.trans_eq (by rw [div_mul_cancel₀ _ (by positivity : (N : ℝ) + 1 ≠ 0)])
  have hsecond :
      |(∑ n ∈ Icc 1 N, normalizedRamanujanMode m n) *
        (∑ n ∈ topBand N w, 1 / (n : ℝ))| ≤ 4 * m * U := by
    rw [abs_mul]
    exact (mul_le_mul hordinary hST (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hbracket := (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  rw [abs_mul]
  have hG : 0 ≤ ∫ u, atomDilate φ w u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have h := mul_le_mul (abs_poleWeight_product_le_mass hφ hsupp hw hw4) hbracket
    (abs_nonneg _) hG
  exact h.trans_eq (by dsimp only [U]; ring)

/-- Every nonpolar base cancels the constant top-band partner with a finite conductor cost. -/
theorem exists_abs_ramanujan_polar_jointTopCoefficient_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ (c : ℝ) (N : ℕ),
      1 ≤ c → 8 ≤ N → 4 * c ≤ N →
      |jointTopCoefficient (atomDilate φ (c / N)) (normalizedRamanujanMode m) (fun _ => 1) N (c / N)| ≤
        K * m * (Real.sqrt (m.totient : ℝ) + ramanujanJetAmplitude m) *
          (∫ u, atomDilate φ (c / N) u ^ 2) * (1 + Real.log N) := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := exists_abs_deriv_shellAutocorr_le hφ hsupp
  set r := (1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2)
  set C₀ := 2 + 28 * r
  have hr : 0 ≤ r := add_nonneg (by norm_num) (div_nonneg hA₁0 hM.le)
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  refine ⟨8 + 8 * C₀, by positivity, fun m hm c N hc hN hNc => ?_⟩
  set w := c / (N : ℝ)
  set g := atomDilate φ w
  set G := ∫ u, g u ^ 2
  set U := Real.sqrt (m.totient : ℝ)
  set V := ramanujanJetAmplitude m
  set H := vonMangoldt m / Real.sqrt (m.totient : ℝ)
  set P := poleWeightMinus g * poleWeightPlus g
  set L := 1 + Real.log N
  have hm0 : 0 < m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hNR : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hNR]
  have hw : 0 < w := div_pos (zero_lt_one.trans_le hc) hN0
  have hw4 : w ≤ 1 / 4 := by
    dsimp only [w]
    rw [div_le_iff₀ hN0]
    linarith only [hNc]
  have hwN : 1 ≤ w * N := by dsimp only [w]; rwa [div_mul_cancel₀ c hN0.ne']
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hJ : 0 ≤ ramanujanJetBound m := sum_nonneg fun _ _ => abs_nonneg _
  have hV : 0 ≤ V := div_nonneg (add_nonneg hJ vonMangoldt_nonneg) (Real.sqrt_nonneg _)
  have hH : 0 ≤ H := div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hHV : H ≤ V := div_le_div_of_nonneg_right
    (le_add_of_nonneg_left hJ) (Real.sqrt_nonneg _)
  have hHmV : H ≤ m * V := hHV.trans (le_mul_of_one_le_left hV hmR)
  have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hlog]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hem : 3 / 4 ≤ Real.exp (-w) := by
    have h := Real.add_one_le_exp (-w)
    linarith only [h, hw4]
  have hep : Real.exp w ≤ 4 / 3 := by
    have h : Real.exp w * Real.exp (-w) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith only [h, hem, Real.exp_pos w]
  have hcut : Nat.ceil ((N : ℝ) * Real.exp w) ≤ 2 * N := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) * Real.exp w by positivity)
    exact_mod_cast (by nlinarith only [h, hep, hNR] :
      (Nat.ceil ((N : ℝ) * Real.exp w) : ℝ) ≤ 2 * N)
  have hfacts (n : ℕ) (hn : n ∈ topBand N w) :
      4 ≤ n ∧ n ≤ N ∧ 1 / 2 ≤ w * n := by
    have hnI := mem_Icc.mp (mem_topBand.mp hn).1
    have ht := (mem_topBand.mp hn).2
    have hNexp : (N : ℝ) ≤ N * Real.exp w :=
      le_mul_of_one_le_right hN0.le (Real.one_le_exp_iff.mpr hw.le)
    have hlarge : (N : ℝ) < 2 * n := hNexp.trans_lt ht
    refine ⟨?_, hnI.2, ?_⟩
    · exact_mod_cast (by linarith only [hlarge, hNR] : (4 : ℝ) ≤ n)
    · nlinarith only [hw, hwN, hlarge]
  have hlogn (n : ℕ) (hn : n ∈ topBand N w) : 1 + Real.log (2 * n) ≤ 2 * L := by
    have hnI := mem_Icc.mp (mem_topBand.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hnI.1
    have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnI.2
    have h := Real.log_le_log (show (0 : ℝ) < 2 * n by positivity)
      (mul_le_mul_of_nonneg_left hnNR zero_le_two)
    rw [Real.log_mul two_ne_zero hN0.ne'] at h
    have htwo := Real.log_two_lt_d9
    dsimp only [L]
    linarith only [h, htwo, hlog]
  have hmode : ∀ n, |normalizedRamanujanMode m n| ≤ U :=
    SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm0
  have hfirst :
      |∑ n ∈ topBand N w,
        fullShellReading g N w (fun ℓ => Real.log ℓ * normalizedRamanujanMode m ℓ) n| ≤
        8 * C₀ * m * U * G * L := by
    have hpoint (n : ℕ) (hn : n ∈ topBand N w) :
        |fullShellReading g N w (fun ℓ => Real.log ℓ * normalizedRamanujanMode m ℓ) n| ≤
          (4 * C₀ * m * U * G * L) / n := by
      obtain ⟨hn4, hnN, hwn⟩ := hfacts n hn
      rw [fullShellReading_log]
      have hrow := abs_full_periodic_rowIntegrand_sum_le hφ hsupp hM (by omega : 1 ≤ m)
        (normalizedRamanujanMode m) (normalizedRamanujanMode_periodic hm0)
        (sum_range_normalizedRamanujanMode hm) hmode hw hw4 hA₁0 hA₁ hn4 hnN hwn
      have hconst : 0 ≤ (4 + 56 * r) * m * U * G := by positivity
      have hbound := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hlogn n hn) hconst) (Nat.cast_nonneg n)
      exact hrow.trans (hbound.trans_eq (by dsimp only [C₀]; ring))
    have h := abs_sum_topBand_le_of_reciprocal hw.le (by positivity) N _ hpoint
    exact h.trans_eq (by ring)
  have hsecond : |∑ n ∈ topBand N w, fullShellReading g N w (centeredRamanujanJet m) n| ≤
      4 * C₀ * m * V * G := by
    have hpoint (n : ℕ) (hn : n ∈ topBand N w) :
        |fullShellReading g N w (centeredRamanujanJet m) n| ≤ (2 * C₀ * m * V * G) / n := by
      obtain ⟨hn4, hnN, hwn⟩ := hfacts n hn
      have hrow := abs_full_periodic_shellPartnerKernel_sum_le hφ hsupp hM (by omega : 1 ≤ m)
        (centeredRamanujanJet m) (centeredRamanujanJet_periodic m)
        (sum_range_centeredRamanujanJet hm0) (abs_centeredRamanujanJet_le m)
        hw hw4 hA₁0 hA₁ hn4 hnN hwn
      exact hrow.trans_eq (by dsimp only [C₀, r, V, G, g]; ring)
    have h := abs_sum_topBand_le_of_reciprocal hw.le (by positivity) N _ hpoint
    exact h.trans_eq (by ring)
  have hthird :
      |H * (∑ n ∈ topBand N w, (fullShellReading g N w (fun _ => 1) n - P))| ≤ 2 * C₀ * H * G := by
    have hpoint (n : ℕ) (hn : n ∈ topBand N w) :
        |fullShellReading g N w (fun _ => 1) n - P| ≤ (C₀ * G) / n := by
      obtain ⟨hn4, hnN, hwn⟩ := hfacts n hn
      have hrow := abs_full_shellPartnerKernel_sum_sub_integral_le hφ hsupp hM hw hw4
        hA₁0 hA₁ hn4 hnN hwn
      obtain ⟨hg, _, hgc⟩ := atomDilate_facts hφ hsupp hw
      have hP : (∫ u, Real.exp (u / 2) * bumpCorr g u) = P :=
        integral_exp_half_mul_bumpCorr hg.continuous hgc
      rw [hP] at hrow
      simpa only [fullShellReading, mul_one] using hrow
    have hsum := abs_sum_topBand_le_of_reciprocal hw.le (by positivity) N _ hpoint
    rw [abs_mul, abs_of_nonneg hH]
    exact (mul_le_mul_of_nonneg_left hsum hH).trans_eq (by ring)
  have hdiag :
      |G * ∑ n ∈ topBand N w, horizonDivisorCoefficient (normalizedRamanujanMode m) N n / (n : ℝ)| ≤
        2 * U * G * Real.log N := by
    have h := abs_shellTop_diagonal_le (B := U) (U := 1)
      (normalizedRamanujanMode m) (fun _ => 1) hmode (fun _ => by norm_num) hw.le N
    simp only [one_mul, mul_one] at h
    rw [abs_mul, abs_of_nonneg hG]
    exact (mul_le_mul_of_nonneg_left h hG).trans_eq (by ring)
  have hpole := abs_ramanujan_centered_polar_coefficient_le hφ hsupp hm hw hw4 N
  rw [jointTopCoefficient_ramanujan_const_eq hm0 hw.le hcut]
  have htotal :
      |P * (((∑ n ∈ Icc 1 N, normalizedRamanujanMode m n / (n : ℝ)) + H) * (topBand N w).card +
          (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n) * (∑ n ∈ topBand N w, 1 / (n : ℝ))) -
        (∑ n ∈ topBand N w, fullShellReading g N w (fun ℓ => Real.log ℓ * normalizedRamanujanMode m ℓ) n) +
        (∑ n ∈ topBand N w, fullShellReading g N w (centeredRamanujanJet m) n) +
        H * (∑ n ∈ topBand N w, (fullShellReading g N w (fun _ => 1) n - P)) +
        G * (∑ n ∈ topBand N w, horizonDivisorCoefficient (normalizedRamanujanMode m) N n / (n : ℝ))| ≤
        6 * m * U * G + 8 * C₀ * m * U * G * L + 4 * C₀ * m * V * G +
          2 * C₀ * H * G + 2 * U * G * Real.log N := by
    apply (abs_add_le _ _).trans
    apply add_le_add _ hdiag
    apply (abs_add_le _ _).trans
    apply add_le_add _ hthird
    apply (abs_add_le _ _).trans
    apply add_le_add _ hsecond
    exact (abs_sub _ _).trans (add_le_add hpole hfirst)
  refine htotal.trans ?_
  have hP' : 6 * m * U * G ≤ 6 * m * U * G * L :=
    le_mul_of_one_le_right (by positivity) hL
  have hB' : 4 * C₀ * m * V * G ≤ 4 * C₀ * m * V * G * L :=
    le_mul_of_one_le_right (by positivity) hL
  have hE' : 2 * C₀ * H * G ≤ 2 * C₀ * m * V * G * L := by
    have h := mul_le_mul_of_nonneg_left hHmV (show 0 ≤ 2 * C₀ * G by positivity)
    have h' := le_mul_of_one_le_right (show 0 ≤ 2 * C₀ * m * V * G by positivity) hL
    nlinarith only [h, h']
  have hD' : 2 * U * G * Real.log N ≤ 2 * m * U * G * L := by
    have h1 := mul_le_mul_of_nonneg_left (show Real.log N ≤ L by dsimp only [L]; linarith only)
      (show 0 ≤ 2 * U * G by positivity)
    have h2 := mul_le_mul_of_nonneg_right hmR (show 0 ≤ 2 * U * G * L by positivity)
    nlinarith only [h1, h2]
  have hrest : 0 ≤ (8 + 2 * C₀) * m * V * G * L := by positivity
  nlinarith only [hP', hB', hE', hD', hrest]

#print axioms jointTopCoefficient_ramanujan_const_eq
#print axioms abs_ramanujan_centered_polar_coefficient_le
#print axioms exists_abs_ramanujan_polar_jointTopCoefficient_le
end
end GaloisForLFunctions.SuccessorShellArithmetic
