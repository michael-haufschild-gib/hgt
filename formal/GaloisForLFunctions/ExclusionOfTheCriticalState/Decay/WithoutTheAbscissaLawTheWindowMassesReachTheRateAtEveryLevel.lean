import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.WithoutTheAbscissaLawTheWindowMassesHaveTheRateOfTheZeros

/-!
# Without the abscissa law the window masses reach the rate of the zeros at every level

Without the asymptotic abscissa law the zeros have an isolated finite top on `Re ρ = Θ`. At a base
`ℓ > 0` let `m_ν = ∫_{−(ν+1)ℓ}^{−νℓ} |F| e^{−8u}` be the window masses of the critical state.

A smooth test `ψ₀` on `(−ℓ, 0)` whose transform is `1` at one top centred zero `z₀` and `0` at the
other top centred zeros (`exists_bump_isolating_centredZero`) turns the pairing of `e^{−8u}F` with
`ψ₀(· + νℓ)` into the level sum `Σ_z L F(z) ψ̂₀(z) e^{νℓz}` of the tower. Its top part is the single
mode `m L F(z₀) e^{νℓ z₀}` (`m` the multiplicity of `z₀` in the top), of modulus
`m |L F(z₀)| e^{(Θ−½)νℓ}` at every level, and `L F(z₀) ≠ 0` because the transform of the state has no
zero on `Re w ≥ 0`. The rest is `O(e^{(Θ₂−½)νℓ})` with `Θ₂ < Θ`.

* **Every level** (`criticalState_windowMass_ge_of_not_asymptoticAbscissaLaw`):
  `m_ν ≥ c e^{(Θ−½)νℓ}` for every large `ν`, with `c = m |L F(z₀)| / (2a(B + 1))`, `B = sup |ψ₀|`.
  The excursions need no window of consecutive levels and no Turán-type bound: the isolating test
  leaves one mode at the top.
* **Two-sided rate** (`criticalState_windowMass_two_sided_of_not_asymptoticAbscissaLaw`): with
  `criticalState_windowMass_le`, `c e^{(Θ−½)νℓ} ≤ m_ν ≤ C_ε e^{(Θ−½+ε)νℓ}`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology Finset
open scoped ContDiff

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower
open GaloisForLFunctions.InfiniteRankWeilTheory

/-- **An isolating test.** For a finite set `S` of zero copies and `q₀`, a smooth test supported in
`(−ℓ, 0)` whose transform at the centred zeros of `S` is `1` at `z₀ = centredZero q₀` and `0`
elsewhere. -/
theorem exists_bump_isolating_centredZero {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset XiZeroCopy)
    (q₀ : XiZeroCopy) :
    ∃ (ψ₀ : ℝ → ℂ) (B : ℝ), ContDiff ℝ ∞ ψ₀ ∧ HasCompactSupport ψ₀ ∧
      (∀ v, v ∉ Ioo (-ℓ) 0 → ψ₀ v = 0) ∧ 0 ≤ B ∧ (∀ v, ‖ψ₀ v‖ ≤ B) ∧
      ∀ q ∈ S, laplaceTest ψ₀ (centredZero q) =
        if centredZero q = centredZero q₀ then 1 else 0 := by
  classical
  let P : Finset ℂ := S.image centredZero
  let e : Fin P.card ≃ P := P.equivFin.symm
  have hinj : Function.Injective (fun k : Fin P.card => (e k : ℂ)) := fun i j hij =>
    e.injective (Subtype.ext hij)
  let target : Fin P.card → ℂ := fun k => if (e k : ℂ) = centredZero q₀ then 1 else 0
  obtain ⟨ψ₀, hψ₀, hs₀, hsupp₀, hinterp⟩ :=
    exists_smooth_negInterval_interpolating hℓ (fun k => (e k : ℂ)) hinj target
  obtain ⟨B₀, hB₀⟩ := hs₀.exists_bound_of_continuous hψ₀.continuous
  refine ⟨ψ₀, max B₀ 0, hψ₀, hs₀, hsupp₀, le_max_right _ _,
    fun v => (hB₀ v).trans (le_max_left _ _), fun q hq => ?_⟩
  have hmem : centredZero q ∈ P := mem_image_of_mem centredZero hq
  let k : Fin P.card := e.symm ⟨centredZero q, hmem⟩
  have hk : (e k : ℂ) = centredZero q := by simp [k]
  simpa [target, hk] using hinterp k

/-- **E-M18: without the abscissa law the window masses reach the rate of the zeros at every
level.** At every base `ℓ > 0` there is `c > 0` with `c e^{(Θ−½)νℓ} ≤ ∫_{−(ν+1)ℓ}^{−νℓ} |F| e^{−8u}`
for all large `ν`. -/
theorem criticalState_windowMass_ge_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ c : ℝ, 0 < c ∧ ∃ ν₀ : ℕ, ∀ ν : ℕ, ν₀ ≤ ν →
      c * Real.exp ((zetaZeroAbscissa - 1 / 2) * ν * ℓ) ≤
        ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
          |F u| * Real.exp (-(8 * u)) := by
  classical
  rw [asymptoticAbscissaLaw_zetaConfig_iff, not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨S, Θ, Θ₂, hSne, hΘ, hΘ₂, hS, hrest⟩ := hnot
  have habs := zetaZeroAbscissa_eq_of_isolatedTop hSne hΘ hΘ₂ hS hrest
  rw [habs]
  obtain ⟨q₀, hq₀⟩ := hSne
  obtain ⟨ψ₀, B, hψ₀, hs₀, hsupp₀, hB0, hbound, hval⟩ :=
    exists_bump_isolating_centredZero hℓ S q₀
  have h0 : ∀ x, 0 < x → ψ₀ x = 0 := fun x hx =>
    hsupp₀ x fun hm => lt_irrefl (0 : ℝ) (hx.trans hm.2)
  set b : XiZeroCopy → ℂ := fun q =>
    negativeHalfLineLaplace (cx F) (centredZero q) * laplaceTest ψ₀ (centredZero q)
  have hb : Summable fun q => ‖b q‖ :=
    (criticalState_hasSum_zeroSeries_test_left hW hthreshold hF hψ₀ hs₀ h0).summable.norm
  obtain ⟨htop_norm, hlow_norm, hlt_norm⟩ := frobTower_isolatedTop hℓ hΘ₂ hS hrest
  set Rr : ℝ := Real.exp (ℓ * (Θ - 1 / 2))
  set rr : ℝ := Real.exp (ℓ * (Θ₂ - 1 / 2))
  have hRr : 0 < Rr := Real.exp_pos _
  have hrr : 0 < rr := Real.exp_pos _
  have haW : 0 < criticalAliasCoefficient W₀ := criticalAliasCoefficient_positive hW
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  set m : ℕ := (S.filter fun q => centredZero q = centredZero q₀).card
  have hm : 0 < m := Finset.card_pos.2 ⟨q₀, mem_filter.2 ⟨hq₀, rfl⟩⟩
  set L₀ : ℂ := negativeHalfLineLaplace (cx F) (centredZero q₀)
  have hL₀ : L₀ ≠ 0 := by
    have hre : 0 ≤ (centredZero q₀).re := by
      have := hS q₀ hq₀
      change ((q₀.1 : ℂ)).re = Θ at this
      simp only [centredZero, Complex.sub_re, this]
      norm_num; linarith
    exact criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF hre
  set κ : ℝ := (m : ℝ) * ‖L₀‖
  have hκ : 0 < κ := mul_pos (by exact_mod_cast hm) (norm_pos_iff.2 hL₀)
  set M : ℝ := ∑' q, ‖b q‖
  -- eventually the modes below the top are at most half of the top mode
  have hq1 : rr / Rr < 1 := (div_lt_one hRr).2 hlt_norm
  have hlim : Tendsto (fun n : ℕ => M * (rr / Rr) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hrr.le hRr.le) hq1).const_mul M
  obtain ⟨ν₀, hν₀⟩ := (hlim.eventually (gt_mem_nhds (half_pos hκ))).exists_forall_of_atTop
  set K : ℝ := criticalAliasCoefficient W₀ * (B + 1)
  have hK : 0 < K := by positivity
  refine ⟨κ / 2 / K, by positivity, ν₀, fun ν hν => ?_⟩
  set f : XiZeroCopy → ℂ := fun q => b q * frobTower ℓ zetaConfig q ^ (ν : ℤ)
  have hzle : ∀ q, ‖frobTower ℓ zetaConfig q‖ ≤ Rr := fun q => by
    by_cases hq : q ∈ S
    · exact (htop_norm q hq).le
    · exact (hlow_norm q hq).trans hlt_norm.le
  have hfs : Summable fun q => ‖f q‖ := by
    refine (hb.mul_right (Rr ^ ν)).of_nonneg_of_le (fun q => norm_nonneg _) fun q => ?_
    simp only [f]
    rw [norm_mul, zpow_natCast, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hzle q) ν) (norm_nonneg _)
  -- the top part is the single mode of the isolated zero
  have htop : ∑ q ∈ S, f q = (m : ℂ) * L₀ * frobTower ℓ zetaConfig q₀ ^ (ν : ℤ) := by
    have h1 : ∀ q ∈ S, f q = if centredZero q = centredZero q₀ then
        L₀ * frobTower ℓ zetaConfig q₀ ^ (ν : ℤ) else 0 := by
      intro q hq
      simp only [f, b, hval q hq]
      split_ifs with hz
      · have hcfg : zetaConfig q = zetaConfig q₀ := by
          change (q.1 : ℂ) = (q₀.1 : ℂ)
          change (q.1 : ℂ) - 1 / 2 = (q₀.1 : ℂ) - 1 / 2 at hz
          linear_combination hz
        have hzq : frobTower ℓ zetaConfig q = frobTower ℓ zetaConfig q₀ := by
          simp [frobTower, hcfg]
        rw [hz, hzq, mul_one]
      · rw [mul_zero, zero_mul]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    ring
  have htop_n : ‖∑ q ∈ S, f q‖ = κ * Rr ^ ν := by
    rw [htop, norm_mul, norm_mul, zpow_natCast, norm_pow, htop_norm q₀ hq₀, Complex.norm_natCast]
  -- the modes below the top
  set g : XiZeroCopy → ℂ := fun q => if q ∈ S then 0 else f q
  have hS0 : HasSum (fun q => if q ∈ S then f q else 0) (∑ q ∈ S, f q) := by
    have h : HasSum (fun q : XiZeroCopy => if q ∈ S then f q else 0)
        (∑ q ∈ S, (if q ∈ S then f q else 0)) :=
      hasSum_sum_of_ne_finset_zero fun q hq => by simp [hq]
    have e : (∑ q ∈ S, (if q ∈ S then f q else 0)) = ∑ q ∈ S, f q :=
      Finset.sum_congr rfl fun q hq => if_pos hq
    rwa [e] at h
  have hg : HasSum g ((∑' q, f q) - ∑ q ∈ S, f q) := by
    have h := hfs.of_norm.hasSum.sub hS0
    refine h.congr_fun fun q => ?_
    by_cases hq : q ∈ S <;> simp [g, hq]
  have hgb : ∀ q, ‖g q‖ ≤ ‖b q‖ * rr ^ ν := by
    intro q
    by_cases hq : q ∈ S
    · simp only [g, hq, if_true, norm_zero]; positivity
    · simp only [g, hq, if_false, f]
      rw [norm_mul, zpow_natCast, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hlow_norm q hq) ν)
        (norm_nonneg _)
  have hgs : Summable fun q => ‖g q‖ :=
    (hb.mul_right (rr ^ ν)).of_nonneg_of_le (fun q => norm_nonneg _) hgb
  have hrest_le : ‖(∑' q, f q) - ∑ q ∈ S, f q‖ ≤ M * rr ^ ν := by
    rw [← hg.tsum_eq, show M * rr ^ ν = ∑' q, ‖b q‖ * rr ^ ν from tsum_mul_right.symm]
    exact (norm_tsum_le_tsum_norm hgs).trans (Summable.tsum_le_tsum hgb hgs (hb.mul_right _))
  -- the level sum is the window pairing of the state
  have hls : levelSum (frobTower ℓ zetaConfig) b ν = ∑' q, f q := rfl
  have hid := criticalState_levelSum_laplaceTest hW hthreshold hF hψ₀ hs₀ h0 hℓ.le ν
  have hp := norm_statePairing_shift_le hd hB0 hbound hsupp₀ ν
  set mν := ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)), |F u| * Real.exp (-(8 * u))
  have hmν : 0 ≤ mν := setIntegral_nonneg measurableSet_Icc fun u _ => by positivity
  have hnormLS : ‖∑' q, f q‖ ≤ K * mν := by
    rw [← hls, hid, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg haW.le]
    calc criticalAliasCoefficient W₀ * ‖statePairing F (fun u => ψ₀ (u + ν * ℓ))‖
        ≤ criticalAliasCoefficient W₀ * (B * mν) := mul_le_mul_of_nonneg_left hp haW.le
      _ ≤ K * mν := by simp only [K]; nlinarith [mul_nonneg haW.le hmν]
  have htri : κ * Rr ^ ν ≤ K * mν + M * rr ^ ν := by
    rw [← htop_n]
    calc ‖∑ q ∈ S, f q‖ = ‖(∑' q, f q) - ((∑' q, f q) - ∑ q ∈ S, f q)‖ := by
          rw [sub_sub_cancel]
      _ ≤ ‖∑' q, f q‖ + ‖(∑' q, f q) - ∑ q ∈ S, f q‖ := norm_sub_le _ _
      _ ≤ K * mν + M * rr ^ ν := add_le_add hnormLS hrest_le
  have hsmall : M * rr ^ ν ≤ κ / 2 * Rr ^ ν := by
    have h := (hν₀ ν hν).le
    have e : M * rr ^ ν = M * (rr / Rr) ^ ν * Rr ^ ν := by
      rw [div_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hRr.ne')]
    rw [e]
    exact mul_le_mul_of_nonneg_right h (pow_nonneg hRr.le _)
  have hRν : Rr ^ ν = Real.exp ((Θ - 1 / 2) * ν * ℓ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [← hRν, div_mul_eq_mul_div, div_le_iff₀ hK]
  linarith

/-- **Two-sided rate without the abscissa law.** At every base `ℓ > 0` the window masses satisfy
`c e^{(Θ−½)νℓ} ≤ m_ν` for all large `ν`, and `m_ν ≤ C_ε e^{(Θ−½+ε)νℓ}` at every level for every
`ε > 0`. -/
theorem criticalState_windowMass_two_sided_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∃ c : ℝ, 0 < c ∧ ∃ ν₀ : ℕ, ∀ ν : ℕ, ν₀ ≤ ν →
      c * Real.exp ((zetaZeroAbscissa - 1 / 2) * ν * ℓ) ≤
        ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)), |F u| * Real.exp (-(8 * u))) ∧
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ ν : ℕ,
      (∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)), |F u| * Real.exp (-(8 * u))) ≤
        C * Real.exp ((zetaZeroAbscissa - 1 / 2 + ε) * ν * ℓ) :=
  ⟨criticalState_windowMass_ge_of_not_asymptoticAbscissaLaw hnot hW hthreshold hF hℓ,
    fun _ hε => criticalState_windowMass_le hW hthreshold hF hℓ (by linarith)⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
