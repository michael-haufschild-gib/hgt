import GaloisForLFunctions.RHTower.XiPrimeSeamPairVariance
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# Cofinal asymptotics of the Xi prime-seam pair energy

The canonical FE--Schwarz seam has finite reciprocal-prime one-particle square energy and an
absolutely convergent reciprocal-prime mean throughout the open critical strip.  Combining these
facts with the exact finite weighted-variance identity shows that pair energy grows, after division
by reciprocal-prime mass, to twice the one-particle square energy.  That limit is strictly positive
at every off-critical strip point.

The proof uses the existing logarithmically weighted Dirichlet summability theorem from
`EulerFisherCurvature.lean`; it uses no Xi zero-location information.
-/

set_option maxHeartbeats 4000000

open scoped BigOperators

namespace RHTower

noncomputable section

/-- A summable square-energy majorant for the canonical prime seam on the open strip. -/
def primeSeamSquareMajorant (rho : ℂ) (p : Nat.Primes) : ℝ :=
  2 * |Real.log (p : ℝ)| ^ 2 * (p : ℝ) ^ (-(1 + 2 * rho.re)) +
    2 * |Real.log (p : ℝ)| ^ 2 * (p : ℝ) ^ (-(3 - 2 * rho.re))

theorem summable_primeSeamSquareMajorant
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Summable (primeSeamSquareMajorant rho) := by
  have hleftNat := summable_abs_log_natCast_pow_mul_rpow_neg
    2 (1 + 2 * rho.re) (by linarith)
  have hrightNat := summable_abs_log_natCast_pow_mul_rpow_neg
    2 (3 - 2 * rho.re) (by linarith)
  have hleft : Summable (fun p : Nat.Primes =>
      |Real.log (p : ℝ)| ^ 2 * (p : ℝ) ^ (-(1 + 2 * rho.re))) := by
    exact hleftNat.comp_injective Subtype.coe_injective
  have hright : Summable (fun p : Nat.Primes =>
      |Real.log (p : ℝ)| ^ 2 * (p : ℝ) ^ (-(3 - 2 * rho.re))) := by
    exact hrightNat.comp_injective Subtype.coe_injective
  refine ((hleft.mul_left 2).add (hright.mul_left 2)).congr (fun p => ?_)
  dsimp only [primeSeamSquareMajorant]
  ring

theorem orbitwiseNatPrimeSeamCharge_weighted_norm_sq_le_majorant
    (rho : ℂ) (p : Nat.Primes) :
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 / (p : ℝ) ≤
      primeSeamSquareMajorant rho p := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  let P : ℝ := (p : ℝ)
  let x : ℂ := (P : ℂ) ^ (-(starRingEnd ℂ) rho)
  let y : ℂ := (P : ℂ) ^ (-(1 - rho))
  have hx : ‖x‖ = (p : ℝ) ^ (-rho.re) := by
    dsimp [x, P]
    change ‖(((p : ℕ) : ℝ) : ℂ) ^ (-(starRingEnd ℂ) rho)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp
  have hy : ‖y‖ = (p : ℝ) ^ (-(1 - rho.re)) := by
    dsimp [y, P]
    change ‖(((p : ℕ) : ℝ) : ℂ) ^ (-(1 - rho))‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp
  have hnorm : ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ≤
      |Real.log (p : ℝ)| * (‖x‖ + ‖y‖) := by
    dsimp [orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge, x, y, P]
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
  have hsq : ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 ≤
      |Real.log (p : ℝ)| ^ 2 * (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) := by
    have h0 : 0 ≤ |Real.log (p : ℝ)| * (‖x‖ + ‖y‖) := by positivity
    have hs := (sq_le_sq₀ (norm_nonneg _) h0).mpr hnorm
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  rw [hx, hy] at hsq
  rw [primeSeamSquareMajorant]
  have hdiv := (div_le_div_iff_of_pos_right hp).mpr hsq
  have hsquareLeft : ((p : ℝ) ^ (-rho.re)) ^ (2 : ℕ) =
      (p : ℝ) ^ (-2 * rho.re) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp.le]
    congr 1
    ring
  have hsquareRight : ((p : ℝ) ^ (-(1 - rho.re))) ^ (2 : ℕ) =
      (p : ℝ) ^ (-2 * (1 - rho.re)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp.le]
    congr 1
    ring
  calc
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 / (p : ℝ)
        ≤ |Real.log (p : ℝ)| ^ 2 *
            (2 * ((p : ℝ) ^ (-rho.re)) ^ (2 : ℕ) +
              2 * ((p : ℝ) ^ (-(1 - rho.re))) ^ (2 : ℕ)) / (p : ℝ) := hdiv
    _ = 2 * |Real.log (p : ℝ)| ^ 2 * (p : ℝ) ^ (-(1 + 2 * rho.re)) +
        2 * |Real.log (p : ℝ)| ^ 2 * (p : ℝ) ^ (-(3 - 2 * rho.re)) := by
      rw [hsquareLeft, hsquareRight]
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      have hmulLeft :
          (p : ℝ) ^ (-2 * rho.re) * (p : ℝ) ^ (-1 : ℝ) =
            (p : ℝ) ^ (-(1 + 2 * rho.re)) := by
        rw [← Real.rpow_add hp]
        congr 1
        ring
      have hmulRight :
          (p : ℝ) ^ (-2 * (1 - rho.re)) * (p : ℝ) ^ (-1 : ℝ) =
            (p : ℝ) ^ (-(3 - 2 * rho.re)) := by
        rw [← Real.rpow_add hp]
        congr 1
        ring
      calc
        |Real.log (p : ℝ)| ^ 2 *
              (2 * (p : ℝ) ^ (-2 * rho.re) +
                2 * (p : ℝ) ^ (-2 * (1 - rho.re))) * (p : ℝ) ^ (-1 : ℝ) =
            2 * |Real.log (p : ℝ)| ^ 2 *
                ((p : ℝ) ^ (-2 * rho.re) * (p : ℝ) ^ (-1 : ℝ)) +
              2 * |Real.log (p : ℝ)| ^ 2 *
                ((p : ℝ) ^ (-2 * (1 - rho.re)) * (p : ℝ) ^ (-1 : ℝ)) := by ring
        _ = _ := by rw [hmulLeft, hmulRight]

/-- The canonical seam has finite reciprocal-prime one-particle square energy at every open-strip
point. -/
theorem summable_orbitwisePrimeSeam_weighted_norm_sq
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Summable (fun p : Nat.Primes =>
      ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 / (p : ℝ)) := by
  apply Summable.of_nonneg_of_le
  · intro p
    exact div_nonneg (sq_nonneg _) (by exact_mod_cast p.prop.pos.le)
  · exact orbitwiseNatPrimeSeamCharge_weighted_norm_sq_le_majorant rho
  · exact summable_primeSeamSquareMajorant hstrip

/-- A summable absolute majorant for the reciprocal-prime mean of the canonical seam. -/
def primeSeamMeanMajorant (rho : ℂ) (p : Nat.Primes) : ℝ :=
  |Real.log (p : ℝ)| * (p : ℝ) ^ (-(1 + rho.re)) +
    |Real.log (p : ℝ)| * (p : ℝ) ^ (-(2 - rho.re))

theorem summable_primeSeamMeanMajorant
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Summable (primeSeamMeanMajorant rho) := by
  have hleftNat := summable_abs_log_natCast_pow_mul_rpow_neg
    1 (1 + rho.re) (by linarith)
  have hrightNat := summable_abs_log_natCast_pow_mul_rpow_neg
    1 (2 - rho.re) (by linarith)
  have hleft : Summable (fun p : Nat.Primes =>
      |Real.log (p : ℝ)| * (p : ℝ) ^ (-(1 + rho.re))) := by
    simpa only [pow_one] using
      hleftNat.comp_injective Subtype.coe_injective
  have hright : Summable (fun p : Nat.Primes =>
      |Real.log (p : ℝ)| * (p : ℝ) ^ (-(2 - rho.re))) := by
    simpa only [pow_one] using
      hrightNat.comp_injective Subtype.coe_injective
  exact hleft.add hright

theorem orbitwiseNatPrimeSeamCharge_weighted_norm_le_meanMajorant
    (rho : ℂ) (p : Nat.Primes) :
    ‖(((1 / (p : ℝ) : ℝ) : ℂ) *
        orbitwiseNatPrimeSeamCharge (p : ℕ) rho)‖ ≤
      primeSeamMeanMajorant rho p := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  let P : ℝ := (p : ℝ)
  let x : ℂ := (P : ℂ) ^ (-(starRingEnd ℂ) rho)
  let y : ℂ := (P : ℂ) ^ (-(1 - rho))
  have hx : ‖x‖ = (p : ℝ) ^ (-rho.re) := by
    dsimp [x, P]
    change ‖(((p : ℕ) : ℝ) : ℂ) ^ (-(starRingEnd ℂ) rho)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp
  have hy : ‖y‖ = (p : ℝ) ^ (-(1 - rho.re)) := by
    dsimp [y, P]
    change ‖(((p : ℕ) : ℝ) : ℂ) ^ (-(1 - rho))‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp
  have hnorm : ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ≤
      |Real.log (p : ℝ)| * (‖x‖ + ‖y‖) := by
    dsimp [orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge, x, y, P]
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hx, hy] at hnorm
  rw [primeSeamMeanMajorant]
  calc
    (1 / (p : ℝ)) * ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖
        ≤ (1 / (p : ℝ)) *
            (|Real.log (p : ℝ)| *
              ((p : ℝ) ^ (-rho.re) + (p : ℝ) ^ (-(1 - rho.re)))) := by
          exact mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = |Real.log (p : ℝ)| * (p : ℝ) ^ (-(1 + rho.re)) +
        |Real.log (p : ℝ)| * (p : ℝ) ^ (-(2 - rho.re)) := by
      rw [one_div, ← Real.rpow_neg_one]
      have hmulLeft :
          (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-rho.re) =
            (p : ℝ) ^ (-(1 + rho.re)) := by
        rw [← Real.rpow_add hp]
        congr 1
        ring
      have hmulRight :
          (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-(1 - rho.re)) =
            (p : ℝ) ^ (-(2 - rho.re)) := by
        rw [← Real.rpow_add hp]
        congr 1
        ring
      calc
        (p : ℝ) ^ (-1 : ℝ) *
              (|Real.log (p : ℝ)| *
                ((p : ℝ) ^ (-rho.re) + (p : ℝ) ^ (-(1 - rho.re)))) =
            |Real.log (p : ℝ)| *
                ((p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-rho.re)) +
              |Real.log (p : ℝ)| *
                ((p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-(1 - rho.re))) := by ring
        _ = _ := by rw [hmulLeft, hmulRight]

theorem summable_norm_orbitwisePrimeSeam_weightedMean
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Summable (fun p : Nat.Primes =>
      ‖(((1 / (p : ℝ) : ℝ) : ℂ) *
        orbitwiseNatPrimeSeamCharge (p : ℕ) rho)‖) := by
  apply Summable.of_nonneg_of_le
  · intro p
    exact norm_nonneg _
  · exact orbitwiseNatPrimeSeamCharge_weighted_norm_le_meanMajorant rho
  · exact summable_primeSeamMeanMajorant hstrip

/-- The reciprocal-prime weighted canonical seam mean is absolutely summable. -/
theorem summable_orbitwisePrimeSeam_weightedMean
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Summable (fun p : Nat.Primes =>
      (((1 / (p : ℝ) : ℝ) : ℂ) *
        orbitwiseNatPrimeSeamCharge (p : ℕ) rho)) :=
  (summable_norm_orbitwisePrimeSeam_weightedMean hstrip).of_norm

/-- Infinite reciprocal-prime mass as a directed net over all finite prime sets. -/
theorem tendsto_primeReciprocalMass_atTop :
    Filter.Tendsto primeReciprocalMass Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  obtain ⟨s, hs⟩ := exists_finset_primes_sum_one_div_gt B
  refine ⟨s, ?_⟩
  intro t hst
  exact (le_of_lt hs).trans (by
    unfold primeReciprocalMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (by
      intro p hpt hps
      positivity))

/-- The limiting one-particle reciprocal-prime square energy of the canonical seam. -/
def orbitwisePrimeSeamWeightedNormSq (rho : ℂ) : ℝ :=
  ∑' p : Nat.Primes,
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho‖ ^ 2 / (p : ℝ)

/-- **Quantitative cofinal seam law.**  Finite canonical pair energy divided by reciprocal-prime
mass converges to twice the full one-particle seam square energy. -/
theorem tendsto_orbitwisePrimeSeamPairEnergy_div_mass
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Filter.Tendsto
      (fun s : Finset Nat.Primes =>
        primePairDifferenceEnergy
          (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s /
            primeReciprocalMass s)
      Filter.atTop (nhds (2 * orbitwisePrimeSeamWeightedNormSq rho)) := by
  let a : Nat.Primes → ℂ :=
    fun p => orbitwiseNatPrimeSeamCharge (p : ℕ) rho
  have hSsum : Summable (fun p : Nat.Primes => ‖a p‖ ^ 2 / (p : ℝ)) := by
    simpa only [a] using summable_orbitwisePrimeSeam_weighted_norm_sq hstrip
  have hS : Filter.Tendsto (fun s : Finset Nat.Primes =>
      primePairWeightedNormSq a s) Filter.atTop
      (nhds (orbitwisePrimeSeamWeightedNormSq rho)) := by
    have hShas := hSsum.hasSum
    change Filter.Tendsto
      (fun s : Finset Nat.Primes => ∑ p ∈ s, ‖a p‖ ^ 2 / (p : ℝ))
      Filter.atTop (nhds (∑' p : Nat.Primes, ‖a p‖ ^ 2 / (p : ℝ))) at hShas
    convert hShas using 1
    · ext s
      unfold primePairWeightedNormSq
      apply Finset.sum_congr rfl
      intro p hp
      ring
  have hAsum : Summable (fun p : Nat.Primes =>
      (((1 / (p : ℝ) : ℝ) : ℂ) * a p)) := by
    simpa only [a] using summable_orbitwisePrimeSeam_weightedMean hstrip
  have hA : Filter.Tendsto (fun s : Finset Nat.Primes =>
      primePairWeightedMean a s) Filter.atTop
      (nhds (∑' p : Nat.Primes, (((1 / (p : ℝ) : ℝ) : ℂ) * a p))) := by
    simpa only [primePairWeightedMean] using hAsum.hasSum
  have hAdiv : Filter.Tendsto (fun s : Finset Nat.Primes =>
      ‖primePairWeightedMean a s‖ ^ 2 / primeReciprocalMass s)
      Filter.atTop (nhds 0) :=
    (hA.norm.pow 2).div_atTop tendsto_primeReciprocalMass_atTop
  have hmain : Filter.Tendsto (fun s : Finset Nat.Primes =>
      2 * primePairWeightedNormSq a s -
        2 * (‖primePairWeightedMean a s‖ ^ 2 / primeReciprocalMass s))
      Filter.atTop (nhds (2 * orbitwisePrimeSeamWeightedNormSq rho)) := by
    convert ((tendsto_const_nhds.mul hS).sub
      (tendsto_const_nhds.mul hAdiv)) using 1
    all_goals ring
  apply hmain.congr'
  filter_upwards [Filter.eventually_ge_atTop ({⟨2, by norm_num⟩} : Finset Nat.Primes)]
    with s hs
  have hmass : 0 < primeReciprocalMass s := by
    have htwo : (⟨2, by norm_num⟩ : Nat.Primes) ∈ s := hs (by simp)
    unfold primeReciprocalMass
    have hsingle := Finset.single_le_sum
      (s := s) (f := fun p : Nat.Primes => 1 / (p : ℝ)) (by
        intro p hp
        positivity) htwo
    norm_num at hsingle ⊢
    linarith
  rw [orbitwisePrimeSeamPairEnergy_eq_weightedVariance]
  dsimp only [a]
  field_simp [hmass.ne']

/-- The limiting one-particle seam energy is strictly positive at every off-critical open-strip
point. -/
theorem orbitwisePrimeSeamWeightedNormSq_pos_of_re_ne_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ 1 / 2) :
    0 < orbitwisePrimeSeamWeightedNormSq rho := by
  have hsum := summable_orbitwisePrimeSeam_weighted_norm_sq hstrip
  apply hsum.tsum_pos
    (fun p => div_nonneg (sq_nonneg _) (by exact_mod_cast p.prop.pos.le))
    (⟨2, by norm_num⟩ : Nat.Primes)
  have hne : orbitwiseNatPrimeSeamCharge 2 rho ≠ 0 := by
      rw [orbitwiseNatPrimeSeamCharge_two_eq_firstPrime]
      exact (orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).not.mpr hoff
  have hnorm : 0 < ‖orbitwiseNatPrimeSeamCharge 2 rho‖ := norm_pos_iff.mpr hne
  exact div_pos (sq_pos_of_pos hnorm) (by norm_num)

/-- The genuinely weaker top-down source interface: canonical pair energy is sublinear in the
reciprocal-prime mass.  Uniform boundedness implies this condition, but is not required. -/
def OrbitwisePrimeSeamPairEnergySubmass (rho : ℂ) : Prop :=
  Filter.Tendsto
    (fun s : Finset Nat.Primes =>
      primePairDifferenceEnergy
        (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s /
          primeReciprocalMass s)
    Filter.atTop (nhds 0)

/-- Sublinear reciprocal-prime pair energy forces the critical-line equation.  This is the
top-down consequence of the positive off-line asymptotic coefficient. -/
theorem re_eq_half_of_orbitwisePrimeSeamPairEnergySubmass
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hsub : OrbitwisePrimeSeamPairEnergySubmass rho) :
    rho.re = 1 / 2 := by
  by_contra hoff
  have hpos := orbitwisePrimeSeamWeightedNormSq_pos_of_re_ne_half hstrip hoff
  have heq : (0 : ℝ) = 2 * orbitwisePrimeSeamWeightedNormSq rho :=
    tendsto_nhds_unique hsub
      (tendsto_orbitwisePrimeSeamPairEnergy_div_mass hstrip)
  nlinarith

theorem orbitwisePrimeSeamPairEnergySubmass_of_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hre : rho.re = 1 / 2) :
    OrbitwisePrimeSeamPairEnergySubmass rho := by
  have hcoh : OrbitwisePrimeSeamChargesCoherent rho :=
    (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half hstrip).mpr hre
  have htwo : orbitwiseNatPrimeSeamCharge 2 rho = 0 := by
    rw [orbitwiseNatPrimeSeamCharge_two_eq_firstPrime]
    exact (orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).mpr hre
  have hzero : ∀ p : Nat.Primes,
      orbitwiseNatPrimeSeamCharge (p : ℕ) rho = 0 := by
    intro p
    exact (hcoh (p : ℕ) 2 p.prop (by norm_num)).trans htwo
  simpa [OrbitwisePrimeSeamPairEnergySubmass, primePairDifferenceEnergy,
    primePairDifferenceRow, hzero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : Finset Nat.Primes => (0 : ℝ))
        Filter.atTop (nhds 0))

/-- Exact fiberwise endpoint of the weakened source interface. -/
theorem orbitwisePrimeSeamPairEnergySubmass_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    OrbitwisePrimeSeamPairEnergySubmass rho ↔ rho.re = 1 / 2 := by
  exact ⟨re_eq_half_of_orbitwisePrimeSeamPairEnergySubmass hstrip,
    orbitwisePrimeSeamPairEnergySubmass_of_re_eq_half hstrip⟩

/-- Submass growth on every actual Xi divisor fibre. -/
def XiPrimeSeamPairEnergySubmass : Prop :=
  ∀ rho : XiDivisorSupport, OrbitwisePrimeSeamPairEnergySubmass (rho : ℂ)

/-- Global top-down chain: sublinear reciprocal-prime pair energy on every Xi fibre is equivalent
to RH.  The unresolved source problem is to obtain this growth estimate from the actual Sonin
finite sections without using Xi zero locations. -/
theorem xiPrimeSeamPairEnergySubmass_iff_riemannHypothesis :
    XiPrimeSeamPairEnergySubmass ↔ RiemannHypothesis := by
  constructor
  · intro hsub
    apply riemannHypothesis_of_xiPrimeSeamChargesCoherent
    intro rho
    apply (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact re_eq_half_of_orbitwisePrimeSeamPairEnergySubmass
      (xi_divisor_support_re_mem_open_unit rho) (hsub rho)
  · intro hRH rho
    apply orbitwisePrimeSeamPairEnergySubmass_of_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)
    exact (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mp
        (xiPrimeSeamChargesCoherent_iff_riemannHypothesis.mpr hRH rho)

end

end RHTower
