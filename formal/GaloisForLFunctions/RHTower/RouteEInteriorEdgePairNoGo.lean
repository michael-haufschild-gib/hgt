import GaloisForLFunctions.RHTower.RouteEUpperBoundaryEdgePair

/-!
# Interior sign classification for compensated Route E edge rays

The upper-boundary two-edge cancellation does not persist uniformly through
all cofactor scales. The fixed quotient `11` leaves a negative logarithmic
ray, but this is harmless for the one-sided Route E upper ceiling. The
composite quotient `22` leaves a *positive* logarithmic ray after the same
compensation. Thus this edge pairing cannot bound each quotient separately;
the positive interior channel needs cancellation from other source channels.
The failure persists along an explicit exponent schedule approaching the
Route E critical boundary from above.
-/

open Finset ArithmeticFunction Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem eleven_pair_eq {d : ℕ} (hd : 1 ≤ d)
    (hcop : d.Coprime 22) (hsf : Squarefree d) :
    routeEUpperBoundaryEdgePair 11 d = -(1 / (78 * (d : ℝ))) := by
  have hodd : Odd d := Nat.coprime_two_right.mp
    (hcop.coprime_dvd_right (by norm_num : 2 ∣ 22))
  have hcop11 : d.Coprime 11 :=
    hcop.coprime_dvd_right (by norm_num : 11 ∣ 22)
  have hμd : mobiusRealCoefficient d ^ 2 = 1 := by
    have hne : moebius d ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsf
    rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;>
      simp [mobiusRealCoefficient, hm]
  have hμ11 : moebius 11 = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)
  have hμ11d : mobiusRealCoefficient (11 * d) =
      -mobiusRealCoefficient d := by
    unfold mobiusRealCoefficient
    rw [Sieve.moebius_mul_of_coprime hcop11.symm, hμ11]
    norm_num
  have hμ2d : mobiusRealCoefficient (2 * d) = -mobiusRealCoefficient d := by
    have hm2 : moebius 2 = -1 := by
      simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
    unfold mobiusRealCoefficient
    rw [Sieve.moebius_mul_of_coprime hodd.coprime_two_left, hm2]
    norm_num
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  unfold routeEUpperBoundaryEdgePair
  rw [hμ11d, hμ2d]
  have hden1 : (((d + 11 * d : ℕ) : ℝ)) = 12 * (d : ℝ) := by
    push_cast; ring
  have hden2 : (((2 * d + 11 * d : ℕ) : ℝ)) = 13 * (d : ℝ) := by
    push_cast; ring
  rw [hden1, hden2]
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  field_simp
  nlinarith [hμd]

/-- The full interior compensated 1:11 and 2:11 ray. -/
def elevenCompensatedRay (M : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d.Coprime 22 ∧ Squarefree d),
    routeEUpperBoundaryEdgePair 11 d

theorem elevenCompensatedRay_eq (M : ℕ) :
    elevenCompensatedRay M =
      -(1 / 78 : ℝ) *
        ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d.Coprime 22 ∧ Squarefree d),
          1 / (d : ℝ) := by
  unfold elevenCompensatedRay
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdi, hcop, hsf⟩ := Finset.mem_filter.mp hd
  rw [eleven_pair_eq (Finset.mem_Icc.mp hdi).1 hcop hsf]
  ring

theorem elevenCompensatedRay_le_log (M : ℕ) (hM : 1 ≤ M) :
    elevenCompensatedRay M ≤
      -(1 / 624 : ℝ) * Real.log (M : ℝ) + 7 / 624 := by
  have hpf : Nat.primeFactors 22 = {2, 11} := by
    rw [show (22 : ℕ) = 2 * 11 by norm_num,
      Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0)
        (by norm_num : (11 : ℕ) ≠ 0),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 11)]
    rfl
  have hQsum : ∑ p ∈ Nat.primeFactors 22, (1 : ℝ) / p ≤ 5 / 8 := by
    rw [hpf]
    norm_num
  have hmass := Sieve.sum_inv_coprime_squarefree_ge
    (M := M) (Q := 22) (by norm_num) (by norm_num) hM hQsum
  rw [elevenCompensatedRay_eq]
  nlinarith


private theorem twentyTwo_pair_eq {d : ℕ} (hd : 1 ≤ d)
    (hcop : d.Coprime 22) (hsf : Squarefree d) :
    routeEUpperBoundaryEdgePair 22 d = 1 / (276 * (d : ℝ)) := by
  have hodd : Odd d := Nat.coprime_two_right.mp
    (hcop.coprime_dvd_right (by norm_num : 2 ∣ 22))
  have hμd : mobiusRealCoefficient d ^ 2 = 1 := by
    have hne : moebius d ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsf
    rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;>
      simp [mobiusRealCoefficient, hm]
  have hμ22 : moebius 22 = 1 := by
    have hcop2 : Nat.Coprime 2 11 := by norm_num
    have hμ2 : moebius 2 = -1 := by
      simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
    have hμ11 : moebius 11 = -1 := by
      simpa using ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)
    rw [show (22 : ℕ) = 2 * 11 by norm_num,
      Sieve.moebius_mul_of_coprime hcop2, hμ2, hμ11]
    norm_num
  have hμ22d : mobiusRealCoefficient (22 * d) =
      mobiusRealCoefficient d := by
    unfold mobiusRealCoefficient
    rw [Sieve.moebius_mul_of_coprime hcop.symm, hμ22]
    norm_num
  have hμ2d : mobiusRealCoefficient (2 * d) = -mobiusRealCoefficient d := by
    have hm2 : moebius 2 = -1 := by
      simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
    unfold mobiusRealCoefficient
    rw [Sieve.moebius_mul_of_coprime hodd.coprime_two_left, hm2]
    norm_num
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  unfold routeEUpperBoundaryEdgePair
  rw [hμ22d, hμ2d]
  have hden1 : (((d + 22 * d : ℕ) : ℝ)) = 23 * (d : ℝ) := by
    push_cast; ring
  have hden2 : (((2 * d + 22 * d : ℕ) : ℝ)) = 24 * (d : ℝ) := by
    push_cast; ring
  rw [hden1, hden2]
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  field_simp
  nlinarith [hμd]

/-- A positive residual after exact 2-edge compensation. -/
def twentyTwoCompensatedRay (M : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d.Coprime 22 ∧ Squarefree d),
    routeEUpperBoundaryEdgePair 22 d

theorem twentyTwoCompensatedRay_eq (M : ℕ) :
    twentyTwoCompensatedRay M =
      (1 / 276 : ℝ) *
        ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d.Coprime 22 ∧ Squarefree d),
          1 / (d : ℝ) := by
  unfold twentyTwoCompensatedRay
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdi, hcop, hsf⟩ := Finset.mem_filter.mp hd
  rw [twentyTwo_pair_eq (Finset.mem_Icc.mp hdi).1 hcop hsf]
  ring

theorem twentyTwoCompensatedRay_ge_log (M : ℕ) (hM : 1 ≤ M) :
    (1 / 2208 : ℝ) * Real.log (M : ℝ) - 7 / 2208 ≤
      twentyTwoCompensatedRay M := by
  have hpf : Nat.primeFactors 22 = {2, 11} := by
    rw [show (22 : ℕ) = 2 * 11 by norm_num,
      Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0)
        (by norm_num : (11 : ℕ) ≠ 0),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 11)]
    rfl
  have hQsum : ∑ p ∈ Nat.primeFactors 22, (1 : ℝ) / p ≤ 5 / 8 := by
    rw [hpf]
    norm_num
  have hmass := Sieve.sum_inv_coprime_squarefree_ge
    (M := M) (Q := 22) (by norm_num) (by norm_num) hM hQsum
  rw [twentyTwoCompensatedRay_eq]
  nlinarith


/-- Same literal compensated ray at a moving Gamma--Hankel exponent. -/
def twentyTwoCompensatedRayR (M : ℕ) (r : ℝ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d.Coprime 22 ∧ Squarefree d),
    (2 * mobiusRealCoefficient d * mobiusRealCoefficient (22 * d) /
        (((d + 22 * d : ℕ) : ℝ) ^ r) +
      2 * mobiusRealCoefficient (2 * d) * mobiusRealCoefficient (22 * d) /
        (((2 * d + 22 * d : ℕ) : ℝ) ^ r))

theorem twentyTwoCompensatedRayR_one (M : ℕ) :
    twentyTwoCompensatedRayR M 1 = twentyTwoCompensatedRay M := by
  unfold twentyTwoCompensatedRayR twentyTwoCompensatedRay
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Real.rpow_one, routeEUpperBoundaryEdgePair]

theorem continuousAt_twentyTwoCompensatedRayR_one (M : ℕ) :
    ContinuousAt (twentyTwoCompensatedRayR M) 1 := by
  unfold twentyTwoCompensatedRayR
  apply Continuous.continuousAt
  apply continuous_finsetSum
  intro d hd
  have hdpos : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  have hden1 : (0 : ℝ) < (((d + 22 * d : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 0 < d + 22 * d)
  have hden2 : (0 : ℝ) < (((2 * d + 22 * d : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 0 < 2 * d + 22 * d)
  have hc1 : Continuous (fun r : ℝ => (((d + 22 * d : ℕ) : ℝ)) ^ r) :=
    Real.continuous_const_rpow hden1.ne'
  have hc2 : Continuous (fun r : ℝ => (((2 * d + 22 * d : ℕ) : ℝ)) ^ r) :=
    Real.continuous_const_rpow hden2.ne'
  have hfirst : Continuous (fun r : ℝ =>
      2 * mobiusRealCoefficient d * mobiusRealCoefficient (22 * d) /
        (((d + 22 * d : ℕ) : ℝ) ^ r)) :=
    continuous_const.div hc1 (fun r => (Real.rpow_pos_of_pos hden1 r).ne')
  have hsecond : Continuous (fun r : ℝ =>
      2 * mobiusRealCoefficient (2 * d) * mobiusRealCoefficient (22 * d) /
        (((2 * d + 22 * d : ℕ) : ℝ) ^ r)) :=
    continuous_const.div hc2 (fun r => (Real.rpow_pos_of_pos hden2 r).ne')
  exact hfirst.add hsecond

/-- No uniform per-ray ceiling survives as the exponent approaches one. -/
theorem twentyTwoCompensatedRayR_not_uniform_upper :
    ¬ ∃ C : ℝ, ∀ (M : ℕ) (r : ℝ), 1 < r →
      twentyTwoCompensatedRayR M r ≤ C := by
  rintro ⟨C, hC⟩
  have hlogTop : Filter.Tendsto (fun M : ℕ => Real.log (M : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM, hlog⟩ :=
    ((Filter.eventually_ge_atTop (1 : ℕ)).and
      (hlogTop.eventually_gt_atTop (2208 * (C + 1) + 7))).exists
  have hlarge : C < twentyTwoCompensatedRay M := by
    have hbound := twentyTwoCompensatedRay_ge_log M hM
    nlinarith
  have hnear : ∀ᶠ r : ℝ in nhds (1 : ℝ),
      C < twentyTwoCompensatedRayR M r :=
    (continuousAt_twentyTwoCompensatedRayR_one M).eventually
      (eventually_gt_nhds (by rw [twentyTwoCompensatedRayR_one]; exact hlarge))
  have hright : ∀ᶠ r : ℝ in 𝓝[>] (1 : ℝ),
      C < twentyTwoCompensatedRayR M r :=
    hnear.filter_mono nhdsWithin_le_nhds
  obtain ⟨r, hrC, hr1⟩ := (hright.and self_mem_nhdsWithin).exists
  exact (not_le.mpr hrC) (hC M r hr1)

/-- The same failure holds on the explicit cofinal exponent schedule. -/
theorem twentyTwoCompensatedRayR_not_canonical_upper :
    ¬ ∃ C : ℝ, ∀ (M k : ℕ),
      twentyTwoCompensatedRayR M (1 + 1 / ((k : ℝ) + 1)) ≤ C := by
  rintro ⟨C, hC⟩
  have hlogTop : Filter.Tendsto (fun M : ℕ => Real.log (M : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM, hlog⟩ :=
    ((Filter.eventually_ge_atTop (1 : ℕ)).and
      (hlogTop.eventually_gt_atTop (2208 * (C + 1) + 7))).exists
  have hlarge : C < twentyTwoCompensatedRay M := by
    have hbound := twentyTwoCompensatedRay_ge_log M hM
    nlinarith
  have hscale : Filter.Tendsto
      (fun k : ℕ => (1 : ℝ) + 1 / ((k : ℝ) + 1))
      Filter.atTop (nhds (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Filter.Tendsto
      (fun k : ℕ => twentyTwoCompensatedRayR M (1 + 1 / ((k : ℝ) + 1)))
      Filter.atTop (nhds (twentyTwoCompensatedRay M)) := by
    simpa only [Function.comp_def, twentyTwoCompensatedRayR_one] using
      (continuousAt_twentyTwoCompensatedRayR_one M).tendsto.comp hscale
  obtain ⟨k, hk⟩ :=
    (hlim.eventually (eventually_gt_nhds hlarge)).exists
  exact (not_le.mpr hk) (hC M k)

end
end RHTower
