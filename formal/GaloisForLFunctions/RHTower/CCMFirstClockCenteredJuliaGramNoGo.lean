import GaloisForLFunctions.RHTower.CCMFirstClockSourceFusionSuperselectionNoGo

/-!
# Moving-block no-go for the centered first-clock Julia Gram

Centering the bad source vector removes the constant rank-one mode of the Julia Gram.  Fixed-packet
convergence is not enough for Route J because the hard prime packet moves with aperture.  The
macroscopic block nevertheless has uniformly bounded logarithmic diameter.  Continuity of the
normalized Julia kernel at zero therefore gives one zero-scale neighborhood on which every moving
block Gram is uniformly close to the constant matrix.

For nonnegative masses with total `B`, centered coefficients have `ℓ¹` norm at most `2B`.  If a
kernel is within `δ` of the constant kernel, its centered energy has absolute value at most
`4δB²`.  Taking `δ < 1/8` proves that the actual centered Julia energy is strictly smaller than
the squared pure-bad block mass, simultaneously for every certified block.  Hence every scale
schedule tending to zero eventually fails domination.

No kernel Taylor expansion, convergence rate, prime gap, zero, or RH hypothesis is used.
-/

open Set Finset Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Finite real kernel energy against arbitrary coefficients. -/
def finsetRealKernelEnergy
    {ι : Type*} (packet : Finset ι) (kernel : ι → ι → ℝ)
    (coefficient : ι → ℝ) : ℝ :=
  ∑ i ∈ packet, ∑ j ∈ packet,
    coefficient i * kernel i j * coefficient j

/-- A centered finite kernel energy only sees the deviation from the constant Gram. -/
theorem finsetRealKernelEnergy_eq_sub_one_of_sum_eq_zero
    {ι : Type*} (packet : Finset ι) (kernel : ι → ι → ℝ)
    (coefficient : ι → ℝ)
    (hcenter : ∑ i ∈ packet, coefficient i = 0) :
    finsetRealKernelEnergy packet kernel coefficient =
      ∑ i ∈ packet, ∑ j ∈ packet,
        coefficient i * (kernel i j - 1) * coefficient j := by
  unfold finsetRealKernelEnergy
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j ∈ packet, coefficient i * kernel i j * coefficient j) =
        ∑ j ∈ packet,
          (coefficient i * (kernel i j - 1) * coefficient j +
            coefficient i * coefficient j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j ∈ packet,
          coefficient i * (kernel i j - 1) * coefficient j) +
        ∑ j ∈ packet, coefficient i * coefficient j := by
      rw [Finset.sum_add_distrib]
    _ = (∑ j ∈ packet,
          coefficient i * (kernel i j - 1) * coefficient j) +
        coefficient i * (∑ j ∈ packet, coefficient j) := by
      rw [Finset.mul_sum]
    _ = ∑ j ∈ packet,
          coefficient i * (kernel i j - 1) * coefficient j := by
      rw [hcenter, mul_zero, add_zero]

/-- A kernel uniformly `δ`-close to the constant Gram has centered energy at most `δ` times the
square of the coefficient `ℓ¹` norm. -/
theorem abs_finsetRealKernelEnergy_le_of_sum_eq_zero
    {ι : Type*} (packet : Finset ι) (kernel : ι → ι → ℝ)
    (coefficient : ι → ℝ) (δ : ℝ)
    (_hδ : 0 ≤ δ)
    (hcenter : ∑ i ∈ packet, coefficient i = 0)
    (hclose : ∀ i ∈ packet, ∀ j ∈ packet,
      |kernel i j - 1| ≤ δ) :
    |finsetRealKernelEnergy packet kernel coefficient| ≤
      δ * (∑ i ∈ packet, |coefficient i|) ^ (2 : ℕ) := by
  rw [finsetRealKernelEnergy_eq_sub_one_of_sum_eq_zero
    packet kernel coefficient hcenter]
  calc
    |∑ i ∈ packet, ∑ j ∈ packet,
        coefficient i * (kernel i j - 1) * coefficient j| ≤
        ∑ i ∈ packet,
          |∑ j ∈ packet,
            coefficient i * (kernel i j - 1) * coefficient j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ packet, ∑ j ∈ packet,
          |coefficient i * (kernel i j - 1) * coefficient j| := by
      exact Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ packet, ∑ j ∈ packet,
          δ * (|coefficient i| * |coefficient j|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      have hci : 0 ≤ |coefficient i| := abs_nonneg _
      have hcj : 0 ≤ |coefficient j| := abs_nonneg _
      calc
        |coefficient i| * |kernel i j - 1| * |coefficient j| ≤
            |coefficient i| * δ * |coefficient j| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hclose i hi j hj) hci) hcj
        _ = δ * (|coefficient i| * |coefficient j|) := by ring
    _ = δ * (∑ i ∈ packet, |coefficient i|) ^ (2 : ℕ) := by
      calc
        (∑ i ∈ packet, ∑ j ∈ packet,
            δ * (|coefficient i| * |coefficient j|)) =
            δ * (∑ i ∈ packet, ∑ j ∈ packet,
              |coefficient i| * |coefficient j|) := by
          symm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = δ * ((∑ i ∈ packet, |coefficient i|) *
            (∑ j ∈ packet, |coefficient j|)) := by
          rw [Finset.sum_mul_sum]
        _ = δ * (∑ i ∈ packet, |coefficient i|) ^ (2 : ℕ) := by ring

/-- Centering nonnegative masses gives a zero-sum coefficient vector. -/
theorem sum_sub_finsetMean_eq_zero
    {ι : Type*} (packet : Finset ι) (mass : ι → ℝ)
    (hpacket : packet.Nonempty) :
    (∑ i ∈ packet,
      (mass i - (∑ j ∈ packet, mass j) / (packet.card : ℝ))) = 0 := by
  have hcardNat : packet.card ≠ 0 := Finset.card_ne_zero.mpr hpacket
  have hcardReal : (packet.card : ℝ) ≠ 0 := by exact_mod_cast hcardNat
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

/-- Centered nonnegative masses have `ℓ¹` norm at most twice their total mass. -/
theorem sum_abs_sub_finsetMean_le_two_mul_sum
    {ι : Type*} (packet : Finset ι) (mass : ι → ℝ)
    (hpacket : packet.Nonempty)
    (hmass : ∀ i ∈ packet, 0 ≤ mass i) :
    (∑ i ∈ packet,
      |mass i - (∑ j ∈ packet, mass j) / (packet.card : ℝ)|) ≤
      2 * ∑ i ∈ packet, mass i := by
  let total := ∑ i ∈ packet, mass i
  let mean := total / (packet.card : ℝ)
  have hcardPos : (0 : ℝ) < (packet.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hpacket
  have htotal : 0 ≤ total := Finset.sum_nonneg hmass
  have hmean : 0 ≤ mean := div_nonneg htotal hcardPos.le
  have hpoint :
      ∀ i ∈ packet, |mass i - mean| ≤ mass i + mean := by
    intro i hi
    calc
      |mass i - mean| = |mass i + -mean| := by ring_nf
      _ ≤ |mass i| + |-mean| := abs_add_le _ _
      _ = mass i + mean := by
        rw [abs_of_nonneg (hmass i hi), abs_neg, abs_of_nonneg hmean]
  have hcardMean : (packet.card : ℝ) * mean = total := by
    dsimp only [mean]
    field_simp
  change (∑ i ∈ packet, |mass i - mean|) ≤ 2 * total
  calc
    (∑ i ∈ packet, |mass i - mean|) ≤
        ∑ i ∈ packet, (mass i + mean) :=
      Finset.sum_le_sum hpoint
    _ = total + (packet.card : ℝ) * mean := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ = 2 * total := by rw [hcardMean]; ring

/-- Centered Julia Gram energy of the actual pure-bad first-clock block. -/
def ccmFirstClockJuliaSixthPowerBlockCenteredKernelEnergy
    (x : ℝ) (m : ℕ) : ℝ :=
  let block := suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ))
  let bad :=
    ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m)
  let mean := (∑ p ∈ block, bad p) / (block.card : ℝ)
  finsetRealKernelEnergy block
    (fun p q =>
      HTGeometry.juliaDefectAttenuationKernel
        (x * (Real.log (q : ℝ) - Real.log (p : ℝ))))
    (fun p => bad p - mean)

/-- In one zero-scale neighborhood, every Julia kernel entry on every sixth-power moving block is
within `1/8` of the constant Gram. -/
theorem eventually_juliaKernel_sub_one_abs_lt_eighth_on_every_sixthPowerBlock :
    ∀ᶠ x : ℝ in 𝓝 0, ∀ m : ℕ, 25 ≤ m →
      ∀ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
      ∀ q ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
        |HTGeometry.juliaDefectAttenuationKernel
          (x * (Real.log (q : ℝ) - Real.log (p : ℝ))) - 1| < 1 / 8 := by
  have hkernelLimit := HTGeometry.tendsto_juliaDefectAttenuationKernel_zero
  have hlower : ∀ᶠ y : ℝ in 𝓝 0,
      (7 / 8 : ℝ) < HTGeometry.juliaDefectAttenuationKernel y :=
    (tendsto_order.1 hkernelLimit).1 (7 / 8) (by norm_num)
  have hupper : ∀ᶠ y : ℝ in 𝓝 0,
      HTGeometry.juliaDefectAttenuationKernel y < (9 / 8 : ℝ) :=
    (tendsto_order.1 hkernelLimit).2 (9 / 8) (by norm_num)
  have habs : ∀ᶠ y : ℝ in 𝓝 0,
      |HTGeometry.juliaDefectAttenuationKernel y - 1| < 1 / 8 := by
    filter_upwards [hlower, hupper] with y hyLower hyUpper
    rw [abs_lt]
    constructor <;> linarith
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp habs
  have hxBall : Metric.ball (0 : ℝ) (epsilon / 2) ∈ 𝓝 0 :=
    Metric.ball_mem_nhds 0 (half_pos hepsilon)
  filter_upwards [hxBall] with x hx
  intro m hm p hp q hq
  have hdiff :=
    abs_log_sub_log_le_two_of_mem_suzukiMangoldtFivePrimeBlock_fourthPower
      hm hp hq
  have hxAbs : |x| < epsilon / 2 := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    exact hx
  have hargAbs :
      |x * (Real.log (q : ℝ) - Real.log (p : ℝ))| < epsilon := by
    rw [abs_mul]
    calc
      |x| * |Real.log (q : ℝ) - Real.log (p : ℝ)| ≤ |x| * 2 :=
        mul_le_mul_of_nonneg_left hdiff (abs_nonneg x)
      _ < (epsilon / 2) * 2 :=
        mul_lt_mul_of_pos_right hxAbs (by norm_num)
      _ = epsilon := by ring
  exact hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hargAbs)

/-- Uniform moving-block theorem: sufficiently source-faithful centered Julia energy is less than
half the squared pure-bad block mass, simultaneously on every certified block. -/
theorem eventually_ccmFirstClockJuliaSixthPowerBlockCenteredKernelEnergy_le_half_badMass_sq :
    ∀ᶠ x : ℝ in 𝓝 0, ∀ m : ℕ, 25 ≤ m →
      Real.exp 20 ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ) →
      ccmFirstClockJuliaSixthPowerBlockCenteredKernelEnergy x m ≤
        (1 / 2 : ℝ) *
          (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
            ccmFirstClockReducedBadNatTerm
              (ccmFirstClockJuliaSixthPowerAperture m) p) ^ (2 : ℕ) := by
  filter_upwards
    [eventually_juliaKernel_sub_one_abs_lt_eighth_on_every_sixthPowerBlock]
      with x hx
  intro m hm hmCheb
  let block := suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ))
  let bad :=
    ccmFirstClockReducedBadNatTerm (ccmFirstClockJuliaSixthPowerAperture m)
  let total := ∑ p ∈ block, bad p
  let mean := total / (block.card : ℝ)
  let centered := fun p => bad p - mean
  have hpacket : block.Nonempty := by
    simpa only [block] using
      suzukiMangoldtFivePrimeBlock_fourthPower_nonempty hm hmCheb
  have hbad : ∀ p ∈ block, 0 ≤ bad p := by
    intro p hp
    have hpPrime := (mem_suzukiMangoldtFivePrimeBlock.mp hp).1
    dsimp only [bad]
    rw [ccmFirstClockReducedBadNatTerm_of_prime _ hpPrime]
    exact (ccmFirstClockJuliaSixthPower_block_badTerm_pos hm hp).le
  have hcenter :
      ∑ p ∈ block, centered p = 0 := by
    simpa only [centered, mean, total] using
      sum_sub_finsetMean_eq_zero block bad hpacket
  have hl1 :
      (∑ p ∈ block, |centered p|) ≤ 2 * total := by
    simpa only [centered, mean, total] using
      sum_abs_sub_finsetMean_le_two_mul_sum block bad hpacket hbad
  have htotalNonneg : 0 ≤ total := Finset.sum_nonneg hbad
  have hclose :
      ∀ p ∈ block, ∀ q ∈ block,
        |HTGeometry.juliaDefectAttenuationKernel
          (x * (Real.log (q : ℝ) - Real.log (p : ℝ))) - 1| ≤
            (1 / 8 : ℝ) :=
    fun p hp q hq => (hx m hm p hp q hq).le
  have habs :=
    abs_finsetRealKernelEnergy_le_of_sum_eq_zero block
      (fun p q =>
        HTGeometry.juliaDefectAttenuationKernel
          (x * (Real.log (q : ℝ) - Real.log (p : ℝ))))
      centered (1 / 8) (by norm_num) hcenter hclose
  have hl1Sq :
      (∑ p ∈ block, |centered p|) ^ (2 : ℕ) ≤ (2 * total) ^ (2 : ℕ) :=
    (sq_le_sq₀
      (Finset.sum_nonneg fun p _ => abs_nonneg (centered p))
      (mul_nonneg (by norm_num) htotalNonneg)).2 hl1
  have henergyAbs :
      |finsetRealKernelEnergy block
        (fun p q =>
          HTGeometry.juliaDefectAttenuationKernel
            (x * (Real.log (q : ℝ) - Real.log (p : ℝ))))
        centered| ≤ (1 / 2 : ℝ) * total ^ (2 : ℕ) := by
    calc
      |finsetRealKernelEnergy block
          (fun p q =>
            HTGeometry.juliaDefectAttenuationKernel
              (x * (Real.log (q : ℝ) - Real.log (p : ℝ))))
          centered| ≤
          (1 / 8 : ℝ) * (∑ p ∈ block, |centered p|) ^ (2 : ℕ) := habs
      _ ≤ (1 / 8 : ℝ) * (2 * total) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hl1Sq (by norm_num)
      _ = (1 / 2 : ℝ) * total ^ (2 : ℕ) := by ring
  unfold ccmFirstClockJuliaSixthPowerBlockCenteredKernelEnergy
  dsimp only
  change finsetRealKernelEnergy block
      (fun p q =>
        HTGeometry.juliaDefectAttenuationKernel
          (x * (Real.log (q : ℝ) - Real.log (p : ℝ))))
      centered ≤ (1 / 2 : ℝ) * total ^ (2 : ℕ)
  exact (le_abs_self _).trans henergyAbs

/-- Every zero-scale schedule eventually makes the centered Julia Gram fail pure-bad domination. -/
theorem eventually_ccmFirstClockJuliaSixthPowerBlockCenteredKernelEnergy_lt_badMass_sq
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop (𝓝 0)) :
    ∀ᶠ m : ℕ in atTop,
      25 ≤ m →
      Real.exp 20 ≤ ((m ^ (4 : ℕ) : ℕ) : ℝ) →
      ccmFirstClockJuliaSixthPowerBlockCenteredKernelEnergy (scale m) m <
        (∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
          ccmFirstClockReducedBadNatTerm
            (ccmFirstClockJuliaSixthPowerAperture m) p) ^ (2 : ℕ) := by
  have hnear :=
    hscale.eventually
      eventually_ccmFirstClockJuliaSixthPowerBlockCenteredKernelEnergy_le_half_badMass_sq
  filter_upwards [hnear] with m hmNear
  intro hm hmCheb
  have hhalf := hmNear m hm hmCheb
  have hmass :=
    ccmFirstClockJuliaSixthPower_block_badMass_lower hm hmCheb
  have htotalPos :
      0 < ∑ p ∈ suzukiMangoldtFivePrimeBlock (m ^ (4 : ℕ)),
        ccmFirstClockReducedBadNatTerm
          (ccmFirstClockJuliaSixthPowerAperture m) p := by
    have hmPos : (0 : ℝ) < m := by positivity
    have hlowerPos : 0 < (m : ℝ) ^ (2 : ℕ) / 24 := by positivity
    exact hlowerPos.trans_le hmass
  nlinarith [sq_pos_of_pos htotalPos]

end RHTower
