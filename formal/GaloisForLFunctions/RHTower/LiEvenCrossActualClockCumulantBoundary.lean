import GaloisForLFunctions.RHTower.LiEvenCrossActualClockThirdLahBracket
import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniThetaCumulantContact
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoalescingXiSourceRate

/-!
# Signed tilted cumulants and the Lah recurrence of the integrated clock

With `κ_k = (d/dz)^k log Φ`:

* `κ₁` is the theta Esscher mean `flux/partition`, so on `0 < z < 1` the corpus moment recursion
  identifies `κ₂, κ₃, κ₄` with the shifted reciprocal-moment formulas
  `κ₃(z) = -6z Re m₁(z²) + 8z³ Re m₂(z²)` and
  `κ₄(z) = -6 Re m₁(z²) + 48z² Re m₂(z²) - 48z⁴ Re m₃(z²)`;
* since `m_n(y) → M_n` as `y → 0⁺`: `κ₃(z)/z → -6M₁`, `κ₃(0) = 0`,
  `κ₄(0) = -6M₁ = ν₂ - 3ν₁² < 0`, and `κ₃ < 0` on a punctured right neighbourhood of `0`;
* the Lah sums `L_n(z) = Σ_k L(n,k) z^k κ_k(z) = z^{-n} (-1)^n H^{(n)}(1/z)` satisfy
  `L_{n+1} = n L_n + z L_n'`, with `L₁, L₂ > 0` on `z > 0` and `L₃ > 0` on `0 < z < 300`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "Φ" => liClockThetaGeneratorReal
local notation "L" => liClockThetaLogGenerator

/-! ## The Esscher identification -/

/-- `κ₁ = flux/partition`, the theta Esscher mean. -/
theorem deriv_liClockThetaLogGenerator_eq_esscherMean :
    deriv L = thetaCuspCassiniEsscherMean := by
  funext t
  rw [(hasDerivAt_liClockThetaLogGenerator t).deriv]
  have hR := thetaCuspRawEvenMoment_pos 0
  have hΦ := one_le_liClockThetaGeneratorReal t
  rw [liClockThetaGeneratorReal_eq_integral] at hΦ
  have hI : 0 < ∫ y in Ioi (0 : ℝ), Real.cosh (t * y) * thetaCuspFullSource y := by
    by_contra h
    push Not at h
    have : 2 / thetaCuspRawEvenMoment 0 *
        ∫ y in Ioi (0 : ℝ), Real.cosh (t * y) * thetaCuspFullSource y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  rw [liClockThetaGeneratorReal_eq_integral, liClockThetaGeneratorRealDeriv_eq_integral]
  unfold thetaCuspCassiniEsscherMean thetaCuspHyperbolicFlux thetaCuspHyperbolicPartition
  field_simp
  congr 1
  funext y
  rw [mul_comm y t]

theorem iteratedDeriv_two_liClockThetaLogGenerator_eq {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    iteratedDeriv 2 L t = thetaCuspCassiniEsscherVariance t := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_liClockThetaLogGenerator_eq_esscherMean,
    (hasDerivAt_thetaCuspCassiniEsscherMean ht0 ht1).deriv]

theorem iteratedDeriv_three_liClockThetaLogGenerator_eq {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    iteratedDeriv 3 L t = thetaCuspCassiniEsscherThirdCumulant t := by
  have hev : iteratedDeriv 2 L =ᶠ[𝓝 t] thetaCuspCassiniEsscherVariance := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs
    exact iteratedDeriv_two_liClockThetaLogGenerator_eq hs.1 hs.2
  rw [iteratedDeriv_succ, hev.deriv_eq, (hasDerivAt_thetaCuspCassiniEsscherVariance ht0).deriv]

theorem iteratedDeriv_four_liClockThetaLogGenerator_eq {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    iteratedDeriv 4 L t = thetaCuspCassiniEsscherFourthCumulant t := by
  have hev : iteratedDeriv 3 L =ᶠ[𝓝 t] thetaCuspCassiniEsscherThirdCumulant := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs
    exact iteratedDeriv_three_liClockThetaLogGenerator_eq hs.1 hs.2
  rw [iteratedDeriv_succ, hev.deriv_eq, (hasDerivAt_thetaCuspCassiniEsscherThirdCumulant ht0).deriv]

/-! ## The central fourth cumulant and the sign of `κ₃` -/

private theorem tendsto_sq_nhdsGT : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝[≥] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun t => sq_nonneg t⟩
  have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa using this

private theorem tendsto_re_moment (n : ℕ) :
    Tendsto (fun t : ℝ => (xiShiftedReciprocalMoment (t ^ 2) n).re) (𝓝[>] 0)
      (𝓝 (normalizedPrimeArchMoment n)) := by
  have h := (Complex.continuous_re.tendsto _).comp
    ((tendsto_xiShiftedReciprocalMoment_nhdsGE_zero n).comp tendsto_sq_nhdsGT)
  simpa [Function.comp_def] using h

/-- `κ₃(z)/z → -6M₁` as `z → 0⁺`. -/
theorem tendsto_iteratedDeriv_three_liClockThetaLogGenerator_div :
    Tendsto (fun t => iteratedDeriv 3 L t / t) (𝓝[>] 0)
      (𝓝 (-6 * normalizedPrimeArchMoment 1)) := by
  have h1 := tendsto_re_moment 1
  have h2 := tendsto_re_moment 2
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) :=
    tendsto_sq_nhdsGT.mono_right nhdsWithin_le_nhds
  have hlim := (h1.const_mul (-6)).add ((hsq.mul h2).const_mul 8)
  rw [zero_mul, mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  rw [iteratedDeriv_three_liClockThetaLogGenerator_eq ht.1 ht.2]
  unfold thetaCuspCassiniEsscherThirdCumulant
  field_simp [ht.1.ne']

/-- **Signed tilted cumulant (C5).**  `κ₃ < 0` on a punctured right neighbourhood of `0`. -/
theorem exists_iteratedDeriv_three_liClockThetaLogGenerator_neg :
    ∃ ε > 0, ∀ t ∈ Ioo (0 : ℝ) ε, iteratedDeriv 3 L t < 0 := by
  have hM := normalizedPrimeArchMoment_one_pos
  have hev := tendsto_iteratedDeriv_three_liClockThetaLogGenerator_div.eventually
    (gt_mem_nhds (show -6 * normalizedPrimeArchMoment 1 < 0 by linarith))
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨ε, hε, fun t ht => ?_⟩
  have h : iteratedDeriv 3 L t / t < 0 := hsub ht
  have ht0 : 0 < t := ht.1
  have := mul_neg_of_neg_of_pos h ht0
  rwa [div_mul_cancel₀ _ ht0.ne'] at this

theorem continuous_iteratedDeriv_liClockThetaLogGenerator (k : ℕ) :
    Continuous (iteratedDeriv k L) :=
  (differentiable_iteratedDeriv_liClockThetaLogGenerator k).continuous

/-- `κ₃(0) = 0`. -/
theorem iteratedDeriv_three_liClockThetaLogGenerator_zero : iteratedDeriv 3 L 0 = 0 := by
  have h1 : Tendsto (iteratedDeriv 3 L) (𝓝[>] 0) (𝓝 (iteratedDeriv 3 L 0)) :=
    ((continuous_iteratedDeriv_liClockThetaLogGenerator 3).tendsto 0).mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  have h2 := hid.mul tendsto_iteratedDeriv_three_liClockThetaLogGenerator_div
  rw [zero_mul] at h2
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (t : ℝ) ≠ 0 := (show (0 : ℝ) < t from ht).ne'
  field_simp

/-- **Central fourth cumulant (C5).**  `κ₄(0) = -6M₁ = ν₂ - 3ν₁² < 0`. -/
theorem iteratedDeriv_four_liClockThetaLogGenerator_zero :
    iteratedDeriv 4 L 0 = -6 * normalizedPrimeArchMoment 1 ∧
      iteratedDeriv 4 L 0 = thetaCuspNormalizedEvenMoment 2 - 3 * thetaCuspNormalizedEvenMoment 1 ^ 2 ∧
        iteratedDeriv 4 L 0 < 0 := by
  have h1 : Tendsto (iteratedDeriv 4 L) (𝓝[>] 0) (𝓝 (iteratedDeriv 4 L 0)) :=
    ((continuous_iteratedDeriv_liClockThetaLogGenerator 4).tendsto 0).mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) :=
    tendsto_sq_nhdsGT.mono_right nhdsWithin_le_nhds
  have hsq4 : Tendsto (fun t : ℝ => t ^ 4) (𝓝[>] 0) (𝓝 0) := by
    have := hsq.mul hsq
    rw [zero_mul] at this
    exact this.congr fun t => by ring
  have hlim := (((tendsto_re_moment 1).const_mul (-6)).add
    ((hsq.mul (tendsto_re_moment 2)).const_mul 48)).sub ((hsq4.mul (tendsto_re_moment 3)).const_mul 48)
  rw [zero_mul, mul_zero, add_zero, zero_mul, mul_zero, sub_zero] at hlim
  have h4 : iteratedDeriv 4 L 0 = -6 * normalizedPrimeArchMoment 1 := by
    refine tendsto_nhds_unique h1 (hlim.congr' ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [iteratedDeriv_four_liClockThetaLogGenerator_eq ht.1 ht.2]
    unfold thetaCuspCassiniEsscherFourthCumulant
    ring
  refine ⟨h4, ?_, ?_⟩
  · rw [h4, normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment]; ring
  · rw [h4]; linarith [normalizedPrimeArchMoment_one_pos]

/-! ## The Lah recurrence -/

/-- `(-1)^n H^{(n)}(1/z) = z^n L_n(z)` for `z > 0`. -/
theorem neg_one_pow_mul_iteratedDeriv_log_inv_eq_lahCumulantSum (n : ℕ) {z : ℝ} (hz : 0 < z) :
    (-1) ^ n * iteratedDeriv n (fun q => Real.log (Φ q⁻¹)) z⁻¹ = z ^ n * lahCumulantSum L n z := by
  rw [log_liClockThetaGeneratorReal_inv_eq_comp,
    neg_one_pow_mul_iteratedDeriv_comp_inv differentiable_iteratedDeriv_liClockThetaLogGenerator n
      (inv_pos.2 hz), lahInverseSum_inv_eq]

/-- **Lah recurrence (C6).**  `L_{n+1} = n L_n + z L_n'`. -/
theorem lahCumulantSum_liClockThetaLogGenerator_succ (n : ℕ) (z : ℝ) :
    lahCumulantSum L (n + 1) z = n * lahCumulantSum L n z + z * deriv (lahCumulantSum L n) z :=
  lahCumulantSum_succ differentiable_iteratedDeriv_liClockThetaLogGenerator n z

theorem lahCumulantSum_one (z : ℝ) : lahCumulantSum L 1 z = z * iteratedDeriv 1 L z := by
  simp [lahCumulantSum, Finset.sum_range_succ, show lahNumber 1 1 = 1 from rfl]

theorem lahCumulantSum_two (z : ℝ) :
    lahCumulantSum L 2 z = 2 * z * iteratedDeriv 1 L z + z ^ 2 * iteratedDeriv 2 L z := by
  simp [lahCumulantSum, Finset.sum_range_succ, show lahNumber 2 1 = 2 from rfl,
    show lahNumber 2 2 = 1 from rfl]

theorem lahCumulantSum_three (z : ℝ) :
    lahCumulantSum L 3 z = z * (6 * iteratedDeriv 1 L z + 6 * z * iteratedDeriv 2 L z +
      z ^ 2 * iteratedDeriv 3 L z) := by
  simp [lahCumulantSum, Finset.sum_range_succ, show lahNumber 3 1 = 6 from rfl,
    show lahNumber 3 2 = 6 from rfl, show lahNumber 3 3 = 1 from rfl]
  ring

theorem lahCumulantSum_one_pos {z : ℝ} (hz : 0 < z) : 0 < lahCumulantSum L 1 z := by
  rw [lahCumulantSum_one]
  exact mul_pos hz (iteratedDeriv_one_liClockThetaLogGenerator_pos hz)

theorem lahCumulantSum_two_pos {z : ℝ} (hz : 0 < z) : 0 < lahCumulantSum L 2 z := by
  rw [lahCumulantSum_two]
  have h1 := iteratedDeriv_one_liClockThetaLogGenerator_pos hz
  have h2 := iteratedDeriv_two_liClockThetaLogGenerator_nonneg z
  have : 0 ≤ z ^ 2 * iteratedDeriv 2 L z := mul_nonneg (sq_nonneg z) h2
  nlinarith [mul_pos (mul_pos two_pos hz) h1]

theorem lahCumulantSum_three_pos {z : ℝ} (hz : 0 < z) (hz300 : z < 300) :
    0 < lahCumulantSum L 3 z := by
  rw [lahCumulantSum_three]
  exact mul_pos hz (thirdLahBracket_pos hz hz300)

end RHTower
