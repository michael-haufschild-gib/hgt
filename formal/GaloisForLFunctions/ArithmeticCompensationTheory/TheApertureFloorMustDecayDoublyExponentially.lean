import GaloisForLFunctions.ArithmeticCriticalityTheory.GaussianCriticalityRestrictedWeilGroundEnergy
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFloorTransportFromTheCertifiedEndpoint

/-!
# The aperture floor must decay doubly exponentially

The restricted Weil ground energy has the unconditional Gaussian ceiling
`μ(A) ≤ K exp((11/2)A − π e^{2(A−2)})` for `A ≥ 3`
(`ArithmeticCriticalityTheory.exists_ccmRestrictedWeilGroundEnergy_le_doubleExp`). Without RH it
says nothing about the sign of `μ`; it does say how fast any *positive* floor must die.

* `tendsto_apertureCeilingExponent_atBot`, `eventually_groundEnergy_lt`: the ceiling tends to `0`,
  so below every fixed level `c > 0` the ground energy drops at all large apertures.
* `not_exists_positive_floor_along`: no positive floor holds along any unbounded aperture sequence —
  regardless of RH.
* `not_relative_step_transport`: hence the half-summable relative-loss transport of
  `ArithmeticContinuationAndCriticalEnergy.groundEnergy_ge_of_relative_step`, which produces the
  fixed floor `1/10000`, can never hold along an unbounded sequence. That implication is valid and
  vacuous on the actual source: it cannot be the producer.
* `le_floorLoss_of_floor` — **the positive information**: a floor `μ(A) ≥ m₀ e^{−B(A)}` forces the
  loss rate `B(A) ≥ π e^{2(A−2)} − (11/2)A + log(m₀/K)`; and a transported product of step factors
  must itself be below the ceiling, `∏_{i<J}(1 − c_i) ≤ (K/μ₀) exp((11/2)A_J − π e^{2(A_J−2)})`
  (`prod_le_ceiling_of_relative_step`).
* `exists_groundEnergy_lt_harmonic_transport`: even the harmonic product `1/(J+1)`, which is not
  summable, is far too large along linearly growing apertures.

So a positive aperture transport must lose at a doubly exponential rate in the aperture; positive
step factors may do so while staying positive at every finite stage, and a graded *negative* floor
is the weaker target that the zero-width dictionaries actually need.
-/

open Filter Topology Finset RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-- The exponent of the Gaussian ceiling, `(11/2)A − π e^{2(A−2)}`. -/
def apertureCeilingExponent (A : ℝ) : ℝ := 11 / 2 * A - Real.pi * Real.exp (2 * (A - 2))

/-- The ceiling with a strictly positive constant. -/
theorem exists_pos_groundEnergy_ceiling :
    ∃ K : ℝ, 0 < K ∧ ∀ A : SuzukiPositiveAperture, 3 ≤ A.1 →
      ccmRestrictedWeilGroundEnergy A ≤ K * Real.exp (apertureCeilingExponent A.1) := by
  obtain ⟨K, hK, h⟩ := exists_ccmRestrictedWeilGroundEnergy_le_doubleExp
  refine ⟨K + 1, by linarith, fun A hA => (h A hA).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- The ceiling exponent is at most `(11/2)A − 2π(A − 2)²` for `A ≥ 2`. -/
theorem apertureCeilingExponent_le {A : ℝ} (hA : 2 ≤ A) :
    apertureCeilingExponent A ≤ 11 / 2 * A - 2 * Real.pi * (A - 2) ^ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (A - 2))
  have hπ := Real.pi_pos
  unfold apertureCeilingExponent
  nlinarith [mul_le_mul_of_nonneg_left h hπ.le, sq_nonneg (A - 2)]

/-- The ceiling exponent decreases on `[3, ∞)`. -/
theorem apertureCeilingExponent_antitone {A B : ℝ} (hA : 3 ≤ A) (hAB : A ≤ B) :
    apertureCeilingExponent B ≤ apertureCeilingExponent A := by
  have hexp : Real.exp (2 * (A - 2)) * (2 * (B - A) + 1) ≤ Real.exp (2 * (B - 2)) := by
    have h := Real.add_one_le_exp (2 * (B - A))
    calc Real.exp (2 * (A - 2)) * (2 * (B - A) + 1)
        ≤ Real.exp (2 * (A - 2)) * Real.exp (2 * (B - A)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = Real.exp (2 * (B - 2)) := by rw [← Real.exp_add]; ring_nf
  have he2 : 1 + 2 * (A - 2) ≤ Real.exp (2 * (A - 2)) := by
    linarith [Real.add_one_le_exp (2 * (A - 2))]
  have hπ : 3 < Real.pi := Real.pi_gt_three
  set eA := Real.exp (2 * (A - 2))
  set eB := Real.exp (2 * (B - 2))
  have h1 : 2 * (B - A) * eA ≤ eB - eA := by linarith [hexp]
  have h2 : 3 ≤ eA := by linarith
  have h3 : 6 * (B - A) ≤ 2 * (B - A) * eA := by
    have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * (B - A))
    linarith
  have h4 : 3 * (6 * (B - A)) ≤ Real.pi * (eB - eA) :=
    mul_le_mul hπ.le (h3.trans h1) (by linarith) Real.pi_pos.le
  unfold apertureCeilingExponent
  linarith

theorem tendsto_apertureCeilingExponent_atBot :
    Tendsto apertureCeilingExponent atTop atBot := by
  refine tendsto_atBot_mono' atTop ?_ (f₁ := fun A => 11 / 2 * A - 2 * Real.pi * (A - 2) ^ 2) ?_
  · filter_upwards [eventually_ge_atTop 2] with A hA
    exact apertureCeilingExponent_le hA
  · refine tendsto_atBot.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (|b| + 10)] with A hA
    have hπ : 3 < Real.pi := Real.pi_gt_three
    have hb := le_abs_self b
    have hb' := neg_abs_le b
    nlinarith [sq_nonneg (A - 2), mul_le_mul_of_nonneg_left
      (show (A - 2) * 8 ≤ (A - 2) ^ 2 by nlinarith) (by linarith : (0 : ℝ) ≤ 2 * Real.pi)]

/-- The Gaussian ceiling tends to `0`. -/
theorem tendsto_ceiling_zero (K : ℝ) :
    Tendsto (fun A => K * Real.exp (apertureCeilingExponent A)) atTop (𝓝 0) := by
  simpa using (Real.tendsto_exp_atBot.comp tendsto_apertureCeilingExponent_atBot).const_mul K

/-- **Below every positive level eventually.** For every `c > 0` the ground energy is below `c` at
all large apertures. -/
theorem eventually_groundEnergy_lt {c : ℝ} (hc : 0 < c) :
    ∃ A₀ : ℝ, ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 → ccmRestrictedWeilGroundEnergy A < c := by
  obtain ⟨K, _, hK⟩ := exists_pos_groundEnergy_ceiling
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp ((tendsto_ceiling_zero K).eventually (gt_mem_nhds hc))
  exact ⟨max A₁ 3, fun A hA =>
    (hK A ((le_max_right _ _).trans hA)).trans_lt (hA₁ _ ((le_max_left _ _).trans hA))⟩

/-- **No positive floor along an unbounded aperture sequence**, regardless of RH. -/
theorem not_exists_positive_floor_along {A : ℕ → SuzukiPositiveAperture}
    (hA : Tendsto (fun j => (A j).1) atTop atTop) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ ccmRestrictedWeilGroundEnergy (A j) := by
  rintro ⟨c, hc, hfloor⟩
  obtain ⟨A₀, hA₀⟩ := eventually_groundEnergy_lt hc
  obtain ⟨j, hj⟩ := (hA.eventually_ge_atTop A₀).exists
  exact absurd (hfloor j) (not_le.mpr (hA₀ _ hj))

/-- **The half-summable transport premise is impossible along unbounded apertures.** Its
conclusion would be the fixed floor `1/10000`. -/
theorem not_relative_step_transport {A : ℕ → SuzukiPositiveAperture} {c : ℕ → ℝ}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) (hcsum : ∀ J, ∑ i ∈ range J, c i ≤ 1 / 2) :
    ¬ ∀ j, (1 - c j) * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1)) := fun hstep =>
  not_exists_positive_floor_along hAtop
    ⟨1 / 10000, by norm_num, groundEnergy_ge_of_relative_step hA0 hc0 hc1 hcsum hstep⟩

/-- **The forced loss rate.** There is `K > 0` such that every floor `μ(A) ≥ m₀ e^{−B}` at an
aperture `A ≥ 3` has `B ≥ π e^{2(A−2)} − (11/2)A + log(m₀/K)`. -/
theorem exists_le_floorLoss_of_floor :
    ∃ K : ℝ, 0 < K ∧ ∀ A : SuzukiPositiveAperture, 3 ≤ A.1 → ∀ m₀ B : ℝ, 0 < m₀ →
      m₀ * Real.exp (-B) ≤ ccmRestrictedWeilGroundEnergy A →
      Real.pi * Real.exp (2 * (A.1 - 2)) - 11 / 2 * A.1 + Real.log (m₀ / K) ≤ B := by
  obtain ⟨K, hK, hceil⟩ := exists_pos_groundEnergy_ceiling
  refine ⟨K, hK, fun A hA m₀ B hm₀ hfloor => ?_⟩
  have h := hfloor.trans (hceil A hA)
  have hlog := Real.log_le_log (by positivity) h
  rw [Real.log_mul hm₀.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [Real.log_div hm₀.ne' hK.ne']
  unfold apertureCeilingExponent at hlog
  linarith

/-- **A transported product lies below the ceiling.** If the floor at `A_J ≥ 3` is at least
`μ₀ ∏_{i<J} q_i` with `μ₀ > 0`, the product is at most `(K/μ₀) e^{(11/2)A_J − π e^{2(A_J−2)}}`. -/
theorem prod_le_ceiling_of_relative_step :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : ℕ → SuzukiPositiveAperture) (q : ℕ → ℝ), (∀ j, 0 ≤ q j) →
      (∀ j, q j * ccmRestrictedWeilGroundEnergy (A j) ≤ ccmRestrictedWeilGroundEnergy (A (j + 1))) →
      0 < ccmRestrictedWeilGroundEnergy (A 0) → ∀ J, 3 ≤ (A J).1 →
      ∏ i ∈ range J, q i ≤
        K / ccmRestrictedWeilGroundEnergy (A 0) * Real.exp (apertureCeilingExponent (A J).1) := by
  obtain ⟨K, hK, hceil⟩ := exists_pos_groundEnergy_ceiling
  refine ⟨K, hK, fun A q hq hstep hμ0 J hJ => ?_⟩
  have h := (mul_prod_le_of_relative_step (μ := fun j => ccmRestrictedWeilGroundEnergy (A j))
    hq hstep J).trans (hceil (A J) hJ)
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ0]
  linarith

/-- **The harmonic product is far too large.** Along apertures growing at least linearly, the
harmonic transport `μ(A_J) ≥ μ₀/(J + 1)` fails at some stage, for every `μ₀ > 0`. -/
theorem exists_groundEnergy_lt_harmonic_transport {a μ₀ : ℝ} (ha : 0 < a) (hμ₀ : 0 < μ₀)
    {A : ℕ → SuzukiPositiveAperture} (hA : ∀ J : ℕ, a * J ≤ (A J).1) :
    ∃ J : ℕ, ccmRestrictedWeilGroundEnergy (A J) < μ₀ / ((J : ℝ) + 1) := by
  obtain ⟨K, hK, hceil⟩ := exists_pos_groundEnergy_ceiling
  -- `K e^{E(aJ)} (J + 1) → 0`, since `E(aJ) ≤ (11/2)aJ − 2π(aJ − 2)²` is quadratic in `J`
  have hlin : Tendsto (fun J : ℕ => a * (J : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have hquad : Tendsto (fun J : ℕ => apertureCeilingExponent (a * J) + Real.log ((J : ℝ) + 1))
      atTop atBot := by
    have hE : ∀ᶠ J : ℕ in atTop, apertureCeilingExponent (a * J) + Real.log ((J : ℝ) + 1) ≤
        11 / 2 * (a * J) - 2 * Real.pi * (a * J - 2) ^ 2 + (J : ℝ) := by
      filter_upwards [hlin.eventually_ge_atTop 2] with J hJ
      have hlog : Real.log ((J : ℝ) + 1) ≤ J := by
        have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (J : ℝ) + 1)
        linarith
      linarith [apertureCeilingExponent_le hJ]
    refine tendsto_atBot_mono' atTop hE (tendsto_atBot.mpr fun b => ?_)
    set ia := 1 / a with hia
    have hia0 : 0 < ia := by rw [hia]; positivity
    filter_upwards [hlin.eventually_ge_atTop (|b| + 3 * (11 / 2 + ia) + 3)] with J hJ
    have hπ : 3 < Real.pi := Real.pi_gt_three
    have hb := neg_abs_le b
    have hab := abs_nonneg b
    have hJx : (J : ℝ) = ia * (a * J) := by rw [hia]; field_simp
    obtain ⟨x, hxdef⟩ : ∃ x, x = a * (J : ℝ) := ⟨_, rfl⟩
    rw [← hxdef] at hJ hJx ⊢
    have hQ0 : 0 ≤ 11 / 2 + ia := by linarith
    have hy0 : 0 ≤ x - 2 := by linarith
    have hsq : (x - 2) * (11 / 2 + ia + 1) ≤ (x - 2) ^ 2 := by nlinarith
    have hπy : 6 * (x - 2) ^ 2 ≤ 2 * Real.pi * (x - 2) ^ 2 := by nlinarith [sq_nonneg (x - 2)]
    rw [hJx]
    nlinarith [mul_nonneg hQ0 hy0, hsq, hπy]
  have hzero : Tendsto (fun J : ℕ => K * Real.exp (apertureCeilingExponent (a * J) +
      Real.log ((J : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hquad).const_mul K
  obtain ⟨J, hJ⟩ := ((hzero.eventually (gt_mem_nhds hμ₀)).and
    ((hlin.eventually_ge_atTop 3))).exists
  refine ⟨J, ?_⟩
  have hJ3 : 3 ≤ (A J).1 := hJ.2.trans (hA J)
  have hmono := apertureCeilingExponent_antitone hJ.2 (hA J)
  have hpos : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  rw [lt_div_iff₀ hpos]
  calc ccmRestrictedWeilGroundEnergy (A J) * ((J : ℝ) + 1)
      ≤ K * Real.exp (apertureCeilingExponent (A J).1) * ((J : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (hceil _ hJ3) hpos.le
    _ ≤ K * Real.exp (apertureCeilingExponent (a * J)) * ((J : ℝ) + 1) := by
        gcongr
    _ = K * Real.exp (apertureCeilingExponent (a * J) + Real.log ((J : ℝ) + 1)) := by
        rw [Real.exp_add, Real.exp_log hpos]; ring
    _ < μ₀ := hJ.1

end GaloisForLFunctions.ArithmeticCompensationTheory
