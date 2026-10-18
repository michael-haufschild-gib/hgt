import GaloisForLFunctions.RHTower.PMAdjacentDivisorEuler
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSmallDampingVariance
import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-!
# Small-damping adjacent correlations

Equal exponents have adjacent density `o(ε)`. Shifting one exponent by one leaves an arithmetic
Euler constant at order `ε`; its two- and three-prime factors already force it below `1/2`.
-/

open Filter Topology Finset ArithmeticFunction

noncomputable section
namespace RHTower

private theorem pm_unit_product_bounds {ι : Type*} {f : ι → ℝ} {L : ℝ}
    (hprod : HasProd f L) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (S : Finset ι) :
    0 ≤ L ∧ L ≤ ∏ i ∈ S, f i := by
  constructor
  · exact le_of_tendsto hprod (Filter.Eventually.of_forall fun T =>
      Finset.prod_nonneg fun i _ => hf0 i)
  · apply le_of_tendsto hprod
    filter_upwards [eventually_ge_atTop S] with T hT
    exact Finset.prod_le_prod_of_subset_of_le_one hT (fun i _ => hf0 i)
      (fun i _ _ => hf1 i)

private theorem pm_adjacent_ratio_factor_bounds {ε η : ℝ}
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (p : Nat.Primes) :
    0 ≤ 1 - (p : ℝ) ^ (-η) / ((p : ℝ) - (p : ℝ) ^ (-ε)) ∧
      1 - (p : ℝ) ^ (-η) / ((p : ℝ) - (p : ℝ) ^ (-ε)) ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have he : (p : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have ht : (p : ℝ) ^ (-η) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hd : 0 < (p : ℝ) - (p : ℝ) ^ (-ε) := by linarith
  constructor
  · exact sub_nonneg.mpr ((div_le_one hd).mpr (by linarith))
  · exact sub_le_self _ (div_nonneg (Real.rpow_nonneg (by linarith) _) hd.le)

/-- Dividing by the one-point density isolates the adjacent exclusion factors. -/
theorem pmAdjacentDivisorDensity_ratio_hasProd {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    HasProd (fun p : Nat.Primes =>
      1 - (p : ℝ) ^ (-η) / ((p : ℝ) - (p : ℝ) ^ (-ε)))
      (pmAdjacentDivisorDensity ε η / (pmPowerDampedDivisorDensity ε).re) := by
  have hnum : Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S,
      (1 - ((p : ℝ) ^ (-ε) + (p : ℝ) ^ (-η)) / p)) atTop
      (𝓝 (pmAdjacentDivisorDensity ε η)) := pmAdjacentDivisorDensity_hasProd hε hη
  have hden : Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S,
      (1 - (p : ℝ) ^ (-ε) / p)) atTop
      (𝓝 (pmPowerDampedDivisorDensity ε).re) := pmPowerDampedDivisorDensity_hasProd_real hε
  change Tendsto _ atTop _
  apply (hnum.div hden (pmPowerDampedDivisorDensity_re_ne_zero hε)).congr
  intro S
  rw [← Finset.prod_div_distrib]
  apply prod_congr rfl
  intro p _
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have he : (p : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ) - (p : ℝ) ^ (-ε) ≠ 0 := by linarith
  have hf : 1 - (p : ℝ) ^ (-ε) / p ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  field_simp
  <;> ring

/-- The equal-exponent adjacent density vanishes faster than the damping parameter. -/
theorem tendsto_pmAdjacentDivisorDensity_self_div_parameter :
    Tendsto (fun ε : ℝ => pmAdjacentDivisorDensity ε ε / ε) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun ε : ℝ => (2 : ℝ) ^ (-ε)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp
      continuous_neg).tendsto 0).mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun ε : ℝ => 1 - (2 : ℝ) ^ (-ε) / (2 - (2 : ℝ) ^ (-ε)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (hp.div ((tendsto_const_nhds (x := (2 : ℝ))).sub hp) (by norm_num))
  have hr : Tendsto (fun ε : ℝ =>
      pmAdjacentDivisorDensity ε ε / (pmPowerDampedDivisorDensity ε).re)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hu
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (pm_unit_product_bounds (pmAdjacentDivisorDensity_ratio_hasProd hε hε)
        (fun p => (pm_adjacent_ratio_factor_bounds hε.le hε.le p).1)
        (fun p => (pm_adjacent_ratio_factor_bounds hε.le hε.le p).2) ∅).1
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa using (pm_unit_product_bounds (pmAdjacentDivisorDensity_ratio_hasProd hε hε)
        (fun p => (pm_adjacent_ratio_factor_bounds hε.le hε.le p).1)
        (fun p => (pm_adjacent_ratio_factor_bounds hε.le hε.le p).2)
        {⟨2, Nat.prime_two⟩}).2
  have h := hr.mul tendsto_pmPowerDampedDivisorDensity_re_div_parameter
  simpa only [zero_mul] using h.congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    field_simp [pmPowerDampedDivisorDensity_re_ne_zero hε])

/-- The prime deficit remaining after one adjacent exponent has been shifted by one. -/
def pmAdjacentShiftedPrimeDeficit (ε : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-ε) / ((p : ℝ) * ((p : ℝ) - (p : ℝ) ^ (-ε)))

theorem pmAdjacentShiftedPrimeDeficit_bounds {ε : ℝ} (hε : 0 ≤ ε) (p : Nat.Primes) :
    0 ≤ pmAdjacentShiftedPrimeDeficit ε p ∧
      pmAdjacentShiftedPrimeDeficit ε p ≤ 1 / 2 ∧
        pmAdjacentShiftedPrimeDeficit ε p ≤ 4 / (p : ℝ) ^ 2 := by
  let q := (p : ℝ) ^ (-ε)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by linarith) _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hd : 0 < (p : ℝ) * ((p : ℝ) - q) := mul_pos (by linarith) (by linarith)
  change 0 ≤ q / ((p : ℝ) * ((p : ℝ) - q)) ∧
    q / ((p : ℝ) * ((p : ℝ) - q)) ≤ 1 / 2 ∧
      q / ((p : ℝ) * ((p : ℝ) - q)) ≤ 4 / (p : ℝ) ^ 2
  refine ⟨div_nonneg hq0 hd.le, (div_le_iff₀ hd).mpr ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hp2) (sub_nonneg.mpr hq1)]
  · apply (div_le_div_iff₀ hd (sq_pos_of_pos (by linarith : (0 : ℝ) < p))).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hp2) (sub_nonneg.mpr hq1),
      mul_nonneg (sq_nonneg (p : ℝ)) (sub_nonneg.mpr hq1)]

/-- The arithmetic constant governing the mixed adjacent density. -/
def pmAdjacentArtinConstant : ℝ :=
  ∏' p : Nat.Primes, (1 - 1 / ((p : ℝ) * ((p : ℝ) - 1)))

theorem pmAdjacentArtinConstant_pos_le :
    0 < pmAdjacentArtinConstant ∧ pmAdjacentArtinConstant ≤ 5 / 12 := by
  let d : Nat.Primes → ℝ := fun p => 1 / ((p : ℝ) * ((p : ℝ) - 1))
  have hd (p : Nat.Primes) : 0 ≤ d p ∧ d p ≤ 1 / 2 ∧ d p ≤ 4 / (p : ℝ) ^ 2 := by
    simpa [d, pmAdjacentShiftedPrimeDeficit] using
      pmAdjacentShiftedPrimeDeficit_bounds (by norm_num : (0 : ℝ) ≤ 0) p
  have hs : Summable d := Summable.of_nonneg_of_le (fun p => (hd p).1)
    (fun p => (hd p).2.2) summable_pm_variance_prime_majorant
  have hf (p : Nat.Primes) : 0 < 1 - d p := by linarith [(hd p).2.1]
  have hlog := Real.summable_log_one_add_of_summable hs.neg
  have he : Real.exp (∑' p : Nat.Primes, Real.log (1 - d p)) = pmAdjacentArtinConstant := by
    simpa [pmAdjacentArtinConstant, d, sub_eq_add_neg] using
      Real.rexp_tsum_eq_tprod hf (by simpa only [sub_eq_add_neg] using hlog)
  have hp : HasProd (fun p => 1 - d p) pmAdjacentArtinConstant := by
    simpa only [he] using Real.hasProd_of_hasSum_log hf
      (show Summable (fun p => Real.log (1 - d p)) by
        simpa only [sub_eq_add_neg] using hlog).hasSum
  refine ⟨he ▸ Real.exp_pos _, ?_⟩
  have hb := (pm_unit_product_bounds hp (fun p => (hf p).le)
    (fun p => sub_le_self _ (hd p).1)
    {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩}).2
  norm_num [d] at hb
  exact hb

private theorem pmAdjacentShiftedPrimeDeficit_limit (p : Nat.Primes) :
    Tendsto (fun ε : ℝ => pmAdjacentShiftedPrimeDeficit ε p) (𝓝[>] 0)
      (𝓝 (1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hq : Tendsto (fun ε : ℝ => (p : ℝ) ^ (-ε)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (((Real.continuous_const_rpow hp0).comp continuous_neg).tendsto 0).mono_left
      nhdsWithin_le_nhds
  exact hq.div ((tendsto_const_nhds (x := (p : ℝ))).mul
    ((tendsto_const_nhds (x := (p : ℝ))).sub hq))
    (mul_ne_zero hp0 (by linarith))

private theorem pmAdjacentShifted_ratio_hasProd {ε : ℝ} (hε : 0 < ε) :
    HasProd (fun p : Nat.Primes => 1 - pmAdjacentShiftedPrimeDeficit ε p)
      (pmAdjacentDivisorDensity ε (1 + ε) / (pmPowerDampedDivisorDensity ε).re) := by
  apply (pmAdjacentDivisorDensity_ratio_hasProd hε (by linarith : 0 < 1 + ε)).congr_fun
  intro p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  rw [show -(1 + ε) = -ε + (-1) by ring, Real.rpow_add hp0, Real.rpow_neg_one]
  dsimp only [pmAdjacentShiftedPrimeDeficit]
  ring

/-- The mixed adjacent density has the arithmetic Euler constant as its exact linear rate. -/
theorem tendsto_pmAdjacentDivisorDensity_shifted_div_parameter :
    Tendsto (fun ε : ℝ => pmAdjacentDivisorDensity ε (1 + ε) / ε)
      (𝓝[>] 0) (𝓝 pmAdjacentArtinConstant) := by
  have hprod := tendsto_tprod_one_add_of_dominated_convergence
    summable_pm_variance_prime_majorant
    (fun p => (pmAdjacentShiftedPrimeDeficit_limit p).neg)
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ p : Nat.Primes,
      ‖-pmAdjacentShiftedPrimeDeficit ε p‖ ≤ 4 / (p : ℝ) ^ 2 from by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      intro p
      rw [norm_neg, Real.norm_of_nonneg (pmAdjacentShiftedPrimeDeficit_bounds hε.le p).1]
      exact (pmAdjacentShiftedPrimeDeficit_bounds hε.le p).2.2)
  have hr : Tendsto (fun ε : ℝ =>
      pmAdjacentDivisorDensity ε (1 + ε) / (pmPowerDampedDivisorDensity ε).re)
      (𝓝[>] 0) (𝓝 pmAdjacentArtinConstant) := by
    change Tendsto _ _ (𝓝 (∏' p : Nat.Primes, 1 - 1 / ((p : ℝ) * ((p : ℝ) - 1))))
    have h := hprod.congr' (show ∀ᶠ ε : ℝ in 𝓝[>] 0,
        (∏' p : Nat.Primes, 1 + -pmAdjacentShiftedPrimeDeficit ε p) =
          pmAdjacentDivisorDensity ε (1 + ε) / (pmPowerDampedDivisorDensity ε).re from by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa only [sub_eq_add_neg] using (pmAdjacentShifted_ratio_hasProd hε).tprod_eq)
    simpa only [sub_eq_add_neg] using h
  have h := hr.mul tendsto_pmPowerDampedDivisorDensity_re_div_parameter
  simpa only [mul_one] using h.congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    field_simp [pmPowerDampedDivisorDensity_re_ne_zero hε])

end RHTower
