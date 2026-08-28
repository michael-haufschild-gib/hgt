import GaloisForLFunctions.RHTower.XiGammaSixFilteredBoundaryControl

/-!
# Gamma-six filtered boundary: exact harmonic residue and confluent wall jump

The filtered Gamma-six second boundary jet was previously known to sit between positive harmonic
bounds and to be summable exactly at horizontal neutrality. This file computes its full principal
class. For depth `m ≥ 1`, the literal prime coefficient has the coefficient-exact decomposition

`J_p(t) = R_m(t) / p - D_p(t)`,

where `D_p(t) ≥ 0` and `∑ₚ D_p(t) < ∞`, while

`R_m(0) = 0`, `R_m(t) = log 2 / m²` for `t ≠ 0`.

Thus `R_m(t)` is the unique scalar prime-harmonic counterterm modulo `ℓ¹`. Its jump at the neutral
wall rules out every grade-continuous confluent diagonal renormalizer. The result is sharper than
the earlier harmonic comparison: it identifies the entire nonsummable quotient class and proves
the remaining prime--Gamma source loss is absolutely summable.
-/

open Complex Set Filter Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Harmonic-scale interpolation of the factorized Gamma-six second boundary jet. -/
def gammaSixFilteredBoundaryHarmonicProfile
    (m : ℕ) (t x : ℝ) : ℝ :=
  Real.log 2 / (m : ℝ) ^ 2 *
    (1 - x⁻¹) ^ (2 * m) *
    (1 - x ^ (-(m : ℝ))) ^ 2 *
    (1 / (1 + x⁻¹) ^ 2) *
    (1 - x ^ (-|t|)) ^ 2

/-- Exact coefficientwise harmonic residue: zero at neutral charge, universal off it. -/
def gammaSixFilteredBoundaryAsymptoticResidue
    (m : ℕ) (t : ℝ) : ℝ :=
  if t = 0 then 0 else Real.log 2 / (m : ℝ) ^ 2

theorem gammaSixFilteredBoundarySecondJet_harmonic_scale_eq_profile
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    (p : ℝ) * gammaSixFilteredBoundarySecondJet m q p =
      gammaSixFilteredBoundaryHarmonicProfile m
        (primeDepthBVWoldXiCenteredRate q.1) (p : ℝ) := by
  let P : ℝ := p
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact_mod_cast p.2.ne_zero
  have hP1 : P + 1 ≠ 0 := by
    dsimp [P]
    positivity
  rw [gammaSixFilteredBoundarySecondJet_eq_factorized hm q p,
    gaussLocalFactorWeight, primeActivationOccupancyFisherDensity_eq,
    gammaSixFilteredBoundaryHarmonicProfile]
  change P *
      (Real.log 2 / (m : ℝ) ^ 2 * ((P - 1) / P) ^ (2 * m) *
        (1 - P ^ (-(m : ℝ))) ^ 2 * (P / (P + 1) ^ 2) *
          (1 - P ^ (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2) = _
  have hlocal : (P - 1) / P = 1 - P⁻¹ := by
    field_simp [hP0]
  have hFisher : P * (P / (P + 1) ^ 2) = 1 / (1 + P⁻¹) ^ 2 := by
    field_simp [hP0, hP1]
  rw [hlocal]
  rw [← hFisher]
  ring

private theorem tendsto_real_rpow_neg_atTop_zero
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun x : ℝ => x ^ (-u)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ u) atTop atTop :=
    tendsto_rpow_atTop hu
  have hinv : Tendsto (fun x : ℝ => (x ^ u)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le]

theorem tendsto_gammaSixFilteredBoundaryHarmonicProfile
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    Tendsto (gammaSixFilteredBoundaryHarmonicProfile m t) atTop
      (𝓝 (gammaSixFilteredBoundaryAsymptoticResidue m t)) := by
  by_cases ht : t = 0
  · subst t
    rw [gammaSixFilteredBoundaryAsymptoticResidue, if_pos rfl]
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)) using 1
    funext x
    simp [gammaSixFilteredBoundaryHarmonicProfile]
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hlocal : Tendsto (fun x : ℝ => (1 - x⁻¹) ^ (2 * m)) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).pow (2 * m)
  have hmgap : Tendsto (fun x : ℝ => (1 - x ^ (-(m : ℝ))) ^ 2)
      atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_real_rpow_neg_atTop_zero hmpos)).pow 2
  have hFisher : Tendsto (fun x : ℝ => 1 / (1 + x⁻¹) ^ 2)
      atTop (𝓝 1) := by
    have hden : Tendsto (fun x : ℝ => (1 + x⁻¹) ^ 2) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).pow 2
    have hdiv : Tendsto (fun x : ℝ => (1 : ℝ) / (1 + x⁻¹) ^ 2)
        atTop (𝓝 ((1 : ℝ) / 1)) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div hden
        (by norm_num : (1 : ℝ) ≠ 0)
    simpa using hdiv
  have htgap : Tendsto (fun x : ℝ => (1 - x ^ (-|t|)) ^ 2)
      atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_real_rpow_neg_atTop_zero htpos)).pow 2
  rw [gammaSixFilteredBoundaryAsymptoticResidue, if_neg ht]
  change Tendsto (fun x : ℝ =>
    Real.log 2 / (m : ℝ) ^ 2 *
      (1 - x⁻¹) ^ (2 * m) *
      (1 - x ^ (-(m : ℝ))) ^ 2 *
      (1 / (1 + x⁻¹) ^ 2) *
      (1 - x ^ (-|t|)) ^ 2) atTop
        (𝓝 (Real.log 2 / (m : ℝ) ^ 2))
  simpa only [one_mul, mul_one, one_pow] using
    (((((tendsto_const_nhds (x := Real.log 2 / (m : ℝ) ^ 2)).mul hlocal).mul hmgap).mul hFisher).mul htgap)

/-- A canonical cofinal enumeration used only to state the literal prime-coefficient residue. -/
def gammaSixFilteredBoundaryNthPrime (n : ℕ) : Nat.Primes :=
  ⟨Nat.nth Nat.Prime n, Nat.prime_nth_prime n⟩

private theorem tendsto_gammaSixFilteredBoundaryNthPrime_cast_atTop :
    Tendsto (fun n : ℕ => ((gammaSixFilteredBoundaryNthPrime n).1 : ℝ))
      atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop N] with n hn
  calc
    b ≤ (N : ℝ) := hN
    _ ≤ n := by exact_mod_cast hn
    _ ≤ Nat.nth Nat.Prime n := by
      exact_mod_cast (show n ≤ Nat.nth Nat.Prime n by
        exact (by omega : n ≤ n + 2).trans (Nat.add_two_le_nth_prime n))

/-- The literal second boundary jet has the discontinuous harmonic residue along the prime end. -/
theorem tendsto_gammaSixFilteredBoundarySecondJet_harmonic_residue
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Tendsto (fun n : ℕ =>
      ((gammaSixFilteredBoundaryNthPrime n).1 : ℝ) *
        gammaSixFilteredBoundarySecondJet m q
          (gammaSixFilteredBoundaryNthPrime n)) atTop
      (𝓝 (gammaSixFilteredBoundaryAsymptoticResidue m
        (primeDepthBVWoldXiCenteredRate q.1))) := by
  have hlim := (tendsto_gammaSixFilteredBoundaryHarmonicProfile hm
    (primeDepthBVWoldXiCenteredRate q.1)).comp
      tendsto_gammaSixFilteredBoundaryNthPrime_cast_atTop
  convert hlim using 1
  funext n
  exact gammaSixFilteredBoundarySecondJet_harmonic_scale_eq_profile hm q
    (gammaSixFilteredBoundaryNthPrime n)

private theorem one_sub_mul_le_one_sub_add_one_sub
    {a b : ℝ} (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    1 - a * b ≤ (1 - a) + (1 - b) := by
  calc
    1 - a * b = (1 - a) + a * (1 - b) := by ring
    _ ≤ (1 - a) + 1 * (1 - b) := by gcongr
    _ = (1 - a) + (1 - b) := by ring

private theorem one_sub_four_mul_le_sum_defects
    {a b c d : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hd1 : d ≤ 1) :
    1 - a * b * c * d ≤
      (1 - a) + (1 - b) + (1 - c) + (1 - d) := by
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hab1 : a * b ≤ 1 := (mul_le_mul ha1 hb1 hb0 (by norm_num)).trans_eq (by ring)
  have habc0 : 0 ≤ a * b * c := mul_nonneg hab0 hc0
  have habc1 : a * b * c ≤ 1 :=
    (mul_le_mul hab1 hc1 hc0 (by norm_num)).trans_eq (by ring)
  calc
    1 - a * b * c * d ≤ (1 - a * b * c) + (1 - d) :=
      one_sub_mul_le_one_sub_add_one_sub habc1 hd1
    _ ≤ ((1 - a * b) + (1 - c)) + (1 - d) := by
      gcongr
      exact one_sub_mul_le_one_sub_add_one_sub hab1 hc1
    _ ≤ (((1 - a) + (1 - b)) + (1 - c)) + (1 - d) := by
      gcongr
      exact one_sub_mul_le_one_sub_add_one_sub ha1 hb1
    _ = (1 - a) + (1 - b) + (1 - c) + (1 - d) := by ring

/-- Positive finite part left after subtracting the exact Gamma-six harmonic residue. -/
def gammaSixFilteredBoundaryHarmonicDefect
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  gammaSixFilteredBoundaryAsymptoticResidue m
      (primeDepthBVWoldXiCenteredRate q.1) / (p : ℝ) -
    gammaSixFilteredBoundarySecondJet m q p

theorem gammaSixFilteredBoundaryHarmonicDefect_nonneg
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ gammaSixFilteredBoundaryHarmonicDefect m q p := by
  rw [gammaSixFilteredBoundaryHarmonicDefect]
  by_cases ht : primeDepthBVWoldXiCenteredRate q.1 = 0
  · rw [gammaSixFilteredBoundaryAsymptoticResidue, if_pos ht,
      gammaSixFilteredBoundarySecondJet_eq_factorized hm q p, ht]
    simp
  · rw [gammaSixFilteredBoundaryAsymptoticResidue, if_neg ht]
    exact sub_nonneg.mpr (by
      simpa [div_eq_mul_inv] using
        (gammaSixFilteredBoundarySecondJet_le_harmonic hm q p))

set_option maxHeartbeats 800000 in
theorem gammaSixFilteredBoundaryHarmonicDefect_le
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy)
    (ht : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) (p : Nat.Primes) :
    gammaSixFilteredBoundaryHarmonicDefect m q p ≤
      (Real.log 2 / (m : ℝ) ^ 2) *
        (((2 * m : ℕ) : ℝ) + 5) * (p : ℝ)⁻¹ ^ 2 +
      (Real.log 2 / (m : ℝ) ^ 2) * 2 *
        ((p : ℝ)⁻¹ * (p : ℝ) ^
          (-|primeDepthBVWoldXiCenteredRate q.1|)) := by
  let P : ℝ := p
  let z : ℝ := P⁻¹
  let u : ℝ := |primeDepthBVWoldXiCenteredRate q.1|
  let a : ℝ := (1 - z) ^ (2 * m)
  let b : ℝ := (1 - P ^ (-(m : ℝ))) ^ 2
  let c : ℝ := 1 / (1 + z) ^ 2
  let d : ℝ := (1 - P ^ (-u)) ^ 2
  let C : ℝ := Real.log 2 / (m : ℝ) ^ 2
  have hP2 : (2 : ℝ) ≤ P := by dsimp [P]; exact_mod_cast p.2.two_le
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP2
  have hP1 : 1 ≤ P := by linarith
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hzh : z ≤ 1 / 2 := by
    dsimp [z]
    simpa only [one_div] using
      (inv_le_inv₀ hP0 (by norm_num : (0 : ℝ) < 2)).2 hP2
  have hz1 : z ≤ 1 := hzh.trans (by norm_num)
  have hbase0 : 0 ≤ 1 - z := by linarith
  have hbase1 : 1 - z ≤ 1 := by linarith
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact pow_le_one₀ hbase0 hbase1
  have hadefect : 1 - a ≤ (((2 * m : ℕ) : ℝ)) * z := by
    have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -z by linarith) (2 * m)
    have hbern' : 1 - (((2 * m : ℕ) : ℝ)) * z ≤ a := by
      simpa [a, sub_eq_add_neg] using hbern
    linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hv0 : 0 ≤ P ^ (-(m : ℝ)) := Real.rpow_nonneg hP0.le _
  have hv1 : P ^ (-(m : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hP1
      (neg_nonpos.mpr (Nat.cast_nonneg m))
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]
    nlinarith [mul_nonneg hv0 (by linarith : 0 ≤ 2 - P ^ (-(m : ℝ)))]
  have hbdefect : 1 - b ≤ 2 * z := by
    have hvmz : P ^ (-(m : ℝ)) ≤ z := by
      dsimp [z]
      rw [← Real.rpow_neg_one]
      apply Real.rpow_le_rpow_of_exponent_le hP1
      have hmcast : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    dsimp [b]
    nlinarith [sq_nonneg (P ^ (-(m : ℝ)))]
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have hden : 1 ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
    exact (div_le_one (by positivity : 0 < (1 + z) ^ 2)).2 hden
  have hcdefect : 1 - c ≤ 3 * z := by
    have hF := (primeActivationOccupancyFisherDensity_harmonic_difference_bounds p).2
    have hcEq : c = P * primeActivationOccupancyFisherDensity p := by
      rw [primeActivationOccupancyFisherDensity_eq]
      dsimp only [c, z]
      change 1 / (1 + P⁻¹) ^ 2 = P * (P / (P + 1) ^ 2)
      field_simp [hP0.ne']
    rw [hcEq]
    change 1 / P - primeActivationOccupancyFisherDensity p ≤ 3 / P ^ 2 at hF
    have hmul := mul_le_mul_of_nonneg_left hF hP0.le
    change 1 - P * primeActivationOccupancyFisherDensity p ≤ 3 * P⁻¹
    calc
      1 - P * primeActivationOccupancyFisherDensity p =
          P * (1 / P - primeActivationOccupancyFisherDensity p) := by
        field_simp [hP0.ne']
      _ ≤ P * (3 / P ^ 2) := hmul
      _ = 3 * P⁻¹ := by field_simp [hP0.ne']
  have hu : 0 < u := by dsimp [u]; exact abs_pos.mpr ht
  have hw0 : 0 ≤ P ^ (-u) := Real.rpow_nonneg hP0.le _
  have hw1 : P ^ (-u) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hP1 (neg_nonpos.mpr hu.le)
  have hd1 : d ≤ 1 := by
    dsimp [d]
    nlinarith [mul_nonneg hw0 (by linarith : 0 ≤ 2 - P ^ (-u))]
  have hddefect : 1 - d ≤ 2 * P ^ (-u) := by
    dsimp [d]
    nlinarith [sq_nonneg (P ^ (-u))]
  have hprod : 1 - a * b * c * d ≤
      ((((2 * m : ℕ) : ℝ)) + 5) * z + 2 * P ^ (-u) := by
    calc
      1 - a * b * c * d ≤
          (1 - a) + (1 - b) + (1 - c) + (1 - d) :=
        one_sub_four_mul_le_sum_defects ha0 ha1 hb0 hb1 hc0 hc1 hd1
      _ ≤ (((2 * m : ℕ) : ℝ)) * z + 2 * z + 3 * z + 2 * P ^ (-u) := by
        gcongr
      _ = ((((2 * m : ℕ) : ℝ)) + 5) * z + 2 * P ^ (-u) := by ring
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hdefectEq : gammaSixFilteredBoundaryHarmonicDefect m q p =
      C * z * (1 - a * b * c * d) := by
    have hbridge := gammaSixFilteredBoundarySecondJet_harmonic_scale_eq_profile hm q p
    have hjet : gammaSixFilteredBoundarySecondJet m q p =
        z * gammaSixFilteredBoundaryHarmonicProfile m
          (primeDepthBVWoldXiCenteredRate q.1) P := by
      calc
        gammaSixFilteredBoundarySecondJet m q p =
            z * (P * gammaSixFilteredBoundarySecondJet m q p) := by
          dsimp [z]
          field_simp [hP0.ne']
        _ = _ := by rw [hbridge]
    rw [gammaSixFilteredBoundaryHarmonicDefect,
      gammaSixFilteredBoundaryAsymptoticResidue, if_neg ht, hjet,
      gammaSixFilteredBoundaryHarmonicProfile]
    dsimp only [P, z, u, a, b, c, d, C]
    ring
  rw [hdefectEq]
  change C * z * (1 - a * b * c * d) ≤
    C * ((((2 * m : ℕ) : ℝ)) + 5) * z ^ 2 +
      C * 2 * (z * P ^ (-u))
  calc
    C * z * (1 - a * b * c * d) ≤
        C * z * (((((2 * m : ℕ) : ℝ)) + 5) * z + 2 * P ^ (-u)) := by
      gcongr
    _ = _ := by ring

/-- The exact Gamma-six boundary jet is its universal harmonic atom modulo an absolutely
summable positive finite part. -/
theorem summable_gammaSixFilteredBoundaryHarmonicDefect
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Summable (gammaSixFilteredBoundaryHarmonicDefect m q) := by
  by_cases ht : primeDepthBVWoldXiCenteredRate q.1 = 0
  · have hzero : gammaSixFilteredBoundaryHarmonicDefect m q = 0 := by
      funext p
      rw [gammaSixFilteredBoundaryHarmonicDefect,
        gammaSixFilteredBoundaryAsymptoticResidue, if_pos ht,
        gammaSixFilteredBoundarySecondJet_eq_factorized hm q p, ht]
      simp
    rw [hzero]
    exact summable_zero
  let u : ℝ := |primeDepthBVWoldXiCenteredRate q.1|
  let C : ℝ := Real.log 2 / (m : ℝ) ^ 2
  let A : ℝ := (((2 * m : ℕ) : ℝ)) + 5
  have hu : 0 < u := by dsimp [u]; exact abs_pos.mpr ht
  have hsq : Summable (fun p : Nat.Primes => (p : ℝ)⁻¹ ^ 2) := by
    have h := summable_prime_rpow_neg (show (1 : ℝ) < 2 by norm_num)
    refine h.congr fun p => ?_
    rw [← Real.rpow_neg_one, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : 0 ≤ (p : ℝ))]
    norm_num
  have htail : Summable (fun p : Nat.Primes =>
      (p : ℝ)⁻¹ * (p : ℝ) ^ (-u)) := by
    have h := summable_prime_rpow_neg (show (1 : ℝ) < 1 + u by linarith)
    refine h.congr fun p => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    rw [← Real.rpow_neg_one, ← Real.rpow_add hp0]
    congr 1
    ring
  have hmajor : Summable (fun p : Nat.Primes =>
      C * A * (p : ℝ)⁻¹ ^ 2 + C * 2 *
        ((p : ℝ)⁻¹ * (p : ℝ) ^ (-u))) :=
    ((hsq.mul_left (C * A)).congr (fun p => by ring)).add
      ((htail.mul_left (C * 2)).congr (fun p => by ring))
  apply Summable.of_nonneg_of_le
    (gammaSixFilteredBoundaryHarmonicDefect_nonneg hm q)
    (fun p => ?_) hmajor
  simpa only [u, C, A] using gammaSixFilteredBoundaryHarmonicDefect_le hm q ht p

/-- Coefficient-exact positive decomposition into the sole nonsummable atom and finite part. -/
theorem gammaSixFilteredBoundarySecondJet_eq_harmonic_sub_defect
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundarySecondJet m q p =
      gammaSixFilteredBoundaryAsymptoticResidue m
          (primeDepthBVWoldXiCenteredRate q.1) / (p : ℝ) -
        gammaSixFilteredBoundaryHarmonicDefect m q p := by
  rw [gammaSixFilteredBoundaryHarmonicDefect]
  ring

/-- Subtraction of a scalar prime-harmonic atom from the literal second boundary jet. -/
def gammaSixFilteredBoundaryPrincipalCorrection
    (m : ℕ) (q : XiZeroCopy) (c : ℝ) (p : Nat.Primes) : ℝ :=
  gammaSixFilteredBoundarySecondJet m q p - c / (p : ℝ)

/-- Exact `ℓ¹` principal-class classification: the asymptotic residue is the unique scalar
harmonic coefficient whose subtraction leaves an absolutely summable prime--Gamma source. -/
theorem summable_gammaSixFilteredBoundaryPrincipalCorrection_iff
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (c : ℝ) :
    Summable (gammaSixFilteredBoundaryPrincipalCorrection m q c) ↔
      c = gammaSixFilteredBoundaryAsymptoticResidue m
        (primeDepthBVWoldXiCenteredRate q.1) := by
  let r : ℝ := gammaSixFilteredBoundaryAsymptoticResidue m
    (primeDepthBVWoldXiCenteredRate q.1)
  constructor
  · intro hsum
    have hclass : Summable (fun p : Nat.Primes =>
        (r - c) * (1 / (p : ℝ))) := by
      have hadd := hsum.add (summable_gammaSixFilteredBoundaryHarmonicDefect hm q)
      refine hadd.congr fun p => ?_
      rw [gammaSixFilteredBoundaryPrincipalCorrection,
        gammaSixFilteredBoundarySecondJet_eq_harmonic_sub_defect]
      dsimp only [r]
      ring
    by_contra hne
    have hrc : r - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
      (summable_mul_left_iff hrc).mp hclass
    exact Nat.Primes.not_summable_one_div hharmonic
  · intro hc
    have hneg := (summable_gammaSixFilteredBoundaryHarmonicDefect hm q).neg
    refine hneg.congr fun p => ?_
    rw [gammaSixFilteredBoundaryPrincipalCorrection,
      gammaSixFilteredBoundarySecondJet_eq_harmonic_sub_defect, hc]
    ring

theorem gammaSixFilteredBoundaryAsymptoticResidue_ne_zero
    {m : ℕ} (hm : 1 ≤ m) :
    Real.log 2 / (m : ℝ) ^ 2 ≠ 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  exact div_ne_zero (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))
    (pow_ne_zero 2 hm0)

theorem not_continuousAt_gammaSixFilteredBoundaryAsymptoticResidue
    {m : ℕ} (hm : 1 ≤ m) :
    ¬ ContinuousAt (gammaSixFilteredBoundaryAsymptoticResidue m) 0 := by
  intro hcont
  let u : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have hcast : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop := by
    simpa [Function.comp_def] using
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1) :
        Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop)
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa [u, Function.comp_def] using
      (RHTower.Sieve.tendsto_one_div_atTop.comp hcast)
  have hthrough := hcont.tendsto.comp hu
  have hconst : Tendsto (fun _ : ℕ => Real.log 2 / (m : ℝ) ^ 2)
      atTop (𝓝 (Real.log 2 / (m : ℝ) ^ 2)) := tendsto_const_nhds
  have hprofile : (fun n => gammaSixFilteredBoundaryAsymptoticResidue m (u n)) =
      fun _ : ℕ => Real.log 2 / (m : ℝ) ^ 2 := by
    funext n
    rw [gammaSixFilteredBoundaryAsymptoticResidue, if_neg]
    dsimp [u]
    positivity
  change Tendsto (fun n => gammaSixFilteredBoundaryAsymptoticResidue m (u n))
    atTop (𝓝 (gammaSixFilteredBoundaryAsymptoticResidue m 0)) at hthrough
  rw [hprofile] at hthrough
  have heq := tendsto_nhds_unique hthrough hconst
  simp [gammaSixFilteredBoundaryAsymptoticResidue] at heq
  exact gammaSixFilteredBoundaryAsymptoticResidue_ne_zero hm heq.symm

/-- A harmonic counterterm cancels the scaled second boundary jet to little-oh order on every
horizontal fibre. -/
def IsGammaSixFilteredBoundaryHarmonicCounterterm
    (m : ℕ) (r : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, Tendsto
    (fun x => gammaSixFilteredBoundaryHarmonicProfile m t x - r t)
    atTop (𝓝 0)

/-- The discontinuous residue is the unique coefficient-exact harmonic counterterm. -/
theorem isGammaSixFilteredBoundaryHarmonicCounterterm_iff
    {m : ℕ} (hm : 1 ≤ m) (r : ℝ → ℝ) :
    IsGammaSixFilteredBoundaryHarmonicCounterterm m r ↔
      r = gammaSixFilteredBoundaryAsymptoticResidue m := by
  constructor
  · intro hr
    funext t
    have hlim := (tendsto_gammaSixFilteredBoundaryHarmonicProfile hm t).sub_const (r t)
    have heq := tendsto_nhds_unique hlim (hr t)
    linarith
  · rintro rfl t
    simpa using (tendsto_gammaSixFilteredBoundaryHarmonicProfile hm t).sub_const
      (gammaSixFilteredBoundaryAsymptoticResidue m t)

/-- A continuous confluent counterterm would have to be a harmonic counterterm. -/
def IsGammaSixFilteredBoundaryConfluentRenormalizer
    (m : ℕ) (r : ℝ → ℝ) : Prop :=
  ContinuousAt r 0 ∧ IsGammaSixFilteredBoundaryHarmonicCounterterm m r

/-- No continuous confluent source counterterm cancels the Gamma-six harmonic second-jet
residue on every horizontal fibre. -/
theorem not_exists_gammaSixFilteredBoundaryConfluentRenormalizer
    {m : ℕ} (hm : 1 ≤ m) :
    ¬ ∃ r : ℝ → ℝ, IsGammaSixFilteredBoundaryConfluentRenormalizer m r := by
  rintro ⟨r, hrcont, hr⟩
  have hre := (isGammaSixFilteredBoundaryHarmonicCounterterm_iff hm r).1 hr
  apply not_continuousAt_gammaSixFilteredBoundaryAsymptoticResidue hm
  simpa [← hre] using hrcont

end

end RHTower
