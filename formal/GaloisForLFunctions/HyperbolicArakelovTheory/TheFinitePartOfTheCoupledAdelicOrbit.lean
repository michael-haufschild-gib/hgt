import GaloisForLFunctions.HyperbolicArakelovTheory.TheCriticalAdelicOrbitRequiresGlobalRenormalization
import GaloisForLFunctions.HTGeometry.MonotoneRiemannSum
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheShellsRepayEveryConductor
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex
import GaloisForLFunctions.RHTower.EstermannRightEdgeExplicit

/-!
# A finite part for the coupled rational orbit

The collision pole is removed before summing the primitive height rows.
The remaining smooth profile has a fixed integral mean. Möbius inversion
transfers the bounded quadrature error of ordinary rows to primitive rows;
the divisor majorant is summable with the critical height weight.
-/

noncomputable section
open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.CompletedShell

namespace GaloisForLFunctions.HyperbolicArakelovTheory.CoupledOrbit

/-- Integral mean of the smooth remainder fixed by the local Green profile. -/
def regularMean : ℝ := ∫ r in (0 : ℝ)..1, regularProfile r

/-- The smooth density has a fixed elementary normalization. -/
theorem regularMean_eq : regularMean = Real.log 2 / 4 + Real.pi / 8 := by
  have hc : ContinuousOn regularProfile (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply ContinuousOn.add
    · apply continuousOn_const.div (continuousOn_const.mul (continuousOn_const.add continuousOn_id))
      intro x hx
      have hx0 := hx.1
      change 4 * (1 + x) ≠ 0
      positivity
    · apply continuousOn_const.div
        (continuousOn_const.mul (continuousOn_const.add (continuousOn_id.pow 2)))
      intro x hx
      change 2 * (1 + x ^ 2) ≠ 0
      positivity
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => Real.log (1 + r) / 4 + Real.arctan r / 2)
        (regularProfile x) x := by
    intro x hx
    have hx0 : 0 ≤ x := (Set.mem_Icc.mp
      (by simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)).1
    have hlog := ((hasDerivAt_id x).const_add 1).log (by positivity)
    have he : (1 / (1 + x)) / 4 + (1 / (1 + x ^ 2)) / 2 = regularProfile x := by
      simp only [regularProfile, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [← he]
    apply HasDerivAt.add
    · exact hlog.div_const 4
    · exact (Real.hasDerivAt_arctan x).div_const 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  norm_num only [add_zero, Real.log_one, Real.arctan_zero,
    zero_div, sub_zero, Real.arctan_one, one_add_one_eq_two] at h
  unfold regularMean
  convert h using 1
  ring

/-- The right-endpoint row, including its endpoint for divisor reindexing. -/
def smoothRow (n : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 n, regularProfile ((a : ℝ) / n)

/-- Primitive right-endpoint row. The endpoint survives only at height one. -/
def primitiveSmoothRow (n : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 n, if Nat.Coprime n a then regularProfile ((a : ℝ) / n) else 0

def rowError (n : ℕ) : ℝ := smoothRow n - (n : ℝ) * regularMean

def primitiveRowError (n : ℕ) : ℝ :=
  primitiveSmoothRow n - (n.totient : ℝ) * regularMean

private theorem regularProfile_antitone : AntitoneOn regularProfile (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hx0 := hx.1
  unfold regularProfile
  apply add_le_add
  · exact one_div_le_one_div_of_le (by positivity) (by linarith only [hxy])
  · apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [sq_le_sq₀ hx.1 hy.1 |>.mpr hxy]

private theorem regularProfile_endpoints : regularProfile 0 = 3 / 4 ∧
    regularProfile 1 = 3 / 8 := by norm_num [regularProfile]

private theorem smoothRow_eq_range {n : ℕ} (hn : 0 < n) :
    smoothRow n = (∑ a ∈ range n, regularProfile ((a : ℝ) / n)) +
      regularProfile 1 - regularProfile 0 := by
  rw [smoothRow, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have ht := sum_range_sub (fun a : ℕ => regularProfile ((a : ℝ) / n)) n
  rw [sum_sub_distrib] at ht
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Nat.cast_zero, zero_div, div_self hnR] at ht
  simp only [Nat.add_comm 1]
  linarith only [ht]

/-- Monotone quadrature controls the unweighted row error uniformly in its height. -/
theorem abs_rowError_le (n : ℕ) : |rowError n| ≤ 3 / 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [rowError, smoothRow]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := _root_.HTGeometry.abs_sum_sub_integral_le_of_antitoneOn_scaled
    (g := regularProfile) (c := 0) (k := (n : ℝ)) (n := n) hnR
    (by simpa only [div_self hnR.ne', zero_add] using regularProfile_antitone)
  simp only [zero_add, div_self hnR.ne'] at hr
  change |(1 / (n : ℝ)) * (∑ a ∈ range n, regularProfile ((a : ℝ) / n)) - regularMean| ≤
    (1 / (n : ℝ)) * (regularProfile 0 - regularProfile 1) at hr
  have hmul := mul_le_mul_of_nonneg_left hr hnR.le
  have he : (n : ℝ) * ((1 / (n : ℝ)) *
      (∑ a ∈ range n, regularProfile ((a : ℝ) / n)) - regularMean) =
      (∑ a ∈ range n, regularProfile ((a : ℝ) / n)) - (n : ℝ) * regularMean := by
    field_simp
  have habs : (n : ℝ) * |(1 / (n : ℝ)) *
      (∑ a ∈ range n, regularProfile ((a : ℝ) / n)) - regularMean| =
      |(n : ℝ) * ((1 / (n : ℝ)) *
        (∑ a ∈ range n, regularProfile ((a : ℝ) / n)) - regularMean)| := by
    rw [abs_mul, abs_of_pos hnR]
  rw [habs, he] at hmul
  have he' : (n : ℝ) * ((1 / (n : ℝ)) * (regularProfile 0 - regularProfile 1)) =
      regularProfile 0 - regularProfile 1 := by field_simp
  rw [he'] at hmul
  rw [rowError, smoothRow_eq_range hn]
  rw [regularProfile_endpoints.1, regularProfile_endpoints.2] at hmul ⊢
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp hmul).1]
  · linarith only [(abs_le.mp hmul).2]

/-- Primitive quadrature is the exact Möbius transform of ordinary quadrature. -/
theorem primitiveSmoothRow_moebius {n : ℕ} (hn : 0 < n) :
    primitiveSmoothRow n =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * smoothRow (n / d) := by
  classical
  have hind (a : ℕ) :
      (if Nat.Coprime n a then regularProfile ((a : ℝ) / n) else 0) =
        ∑ d ∈ n.divisors, if d ∣ a then
          (ArithmeticFunction.moebius d : ℝ) * regularProfile ((a : ℝ) / n) else 0 := by
    have hi := sum_divisors_moebius_filter_dvd (k := a) hn
    have hm := congrArg (fun x : ℝ => x * regularProfile ((a : ℝ) / n)) hi
    rw [sum_mul, sum_filter] at hm
    simpa only [ite_mul, zero_mul, one_mul] using hm.symm
  rw [primitiveSmoothRow, sum_congr rfl (fun a _ => hind a), sum_comm]
  apply sum_congr rfl
  intro d hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  rw [← sum_filter, _root_.RHTower.Sieve.sum_filter_dvd_eq_sum_scaled hd0,
    smoothRow, mul_sum]
  apply sum_congr rfl
  intro k hk
  congr 2
  have he : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  have heR : (d : ℝ) * (n / d : ℕ) = n := by exact_mod_cast he
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [Nat.cast_mul, ← heR]
  field_simp

/-- The primitive density is forced by the same divisor transformation. -/
theorem primitiveRowError_moebius {n : ℕ} (hn : 0 < n) :
    primitiveRowError n =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * rowError (n / d) := by
  have ht : (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) * (n / d : ℕ)) = n.totient := by
    rw [← Nat.sum_div_divisors n (fun d => (ArithmeticFunction.moebius d : ℝ) * (n / d : ℕ))]
    have heq : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) *
        (n / (n / d) : ℕ)) =
        ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) * (d : ℝ) := by
      apply sum_congr rfl
      intro d hd
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hq : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) (Nat.pos_of_mem_divisors hd)
      have hqq : n / (n / d) = d := by
        calc
          n / (n / d) = ((n / d) * d) / (n / d) :=
            congrArg (fun x : ℕ => x / (n / d)) (Nat.div_mul_cancel hdvd).symm
          _ = d := Nat.mul_div_cancel_left d hq
      rw [hqq]
    rw [heq]
    exact sum_divisors_moebius_div_mul n
  rw [primitiveRowError, primitiveSmoothRow_moebius hn]
  simp only [rowError, mul_sub, sum_sub_distrib, ← mul_assoc, ← sum_mul, ht]

/-- Primitive quadrature costs only the number of divisors of the height. -/
theorem abs_primitiveRowError_le (n : ℕ) :
    |primitiveRowError n| ≤ (3 / 4 : ℝ) * n.divisors.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [primitiveRowError, primitiveSmoothRow]
  rw [primitiveRowError_moebius hn]
  calc
    _ ≤ ∑ d ∈ n.divisors, |(ArithmeticFunction.moebius d : ℝ) * rowError (n / d)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (3 / 4 : ℝ) := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      have hm : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      simpa only [one_mul] using mul_le_mul hm (abs_rowError_le (n / d))
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

/-- The primitive remainder has an absolutely convergent critical height sum. -/
theorem summable_primitiveRowError_div_sq :
    Summable (fun n : ℕ => primitiveRowError n / (n : ℝ) ^ 2) := by
  apply Summable.of_norm_bounded
    (_root_.RHTower.summable_divisorSquareMass.mul_left (3 / 4 : ℝ))
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_sq]
  calc
    |primitiveRowError n| / (n : ℝ) ^ 2 ≤
        ((3 / 4 : ℝ) * n.divisors.card) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (abs_primitiveRowError_le n) (sq_nonneg _)
    _ = _ := by ring

/-- A nonidentity primitive height row of the critical product profile. -/
def geometricRow (n : ℕ) : ℝ :=
  if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ * ∑ a ∈ Icc 1 n,
    if Nat.Coprime n a then 1 / (1 - ((a : ℝ) / n) ^ 4) else 0 else 0

/-- The height row is a sum of products of the archimedean and finite Green profiles. -/
theorem geometricRow_eq_localGreenSum {n : ℕ} (hn : 2 ≤ n) :
    geometricRow n = ∑ a ∈ Icc 1 n, if Nat.Coprime n a then
      SurfaceOfSpecZ.archProfile (2 * Real.log ((n : ℝ) / a)) * finiteFactor a * finiteFactor n
      else 0 := by
  rw [geometricRow, if_pos hn, mul_sum]
  apply sum_congr rfl
  intro a ha
  by_cases hc : Nat.Coprime n a
  · have hapos : 0 < a := (mem_Icc.mp ha).1
    have hlt : a < n := by
      have hal := (mem_Icc.mp ha).2
      have hne : a ≠ n := by
        intro he
        subst a
        have h1 : n = 1 := by simpa only [Nat.coprime_self] using hc
        omega
      exact lt_of_le_of_ne hal hne
    rw [if_pos hc, if_pos hc]
    have h := term_two_eq_local_product (⟨(a, n), hapos, hlt, hc.symm⟩ : Primitive)
    simpa only [term, Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two,
      div_eq_mul_inv, one_mul] using h
  · simp only [if_neg hc, mul_zero]

/-- The rational collision pole extracted from the same local profile. -/
def collisionRow (n : ℕ) : ℝ :=
  if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ * ∑ a ∈ Icc 1 n,
    if Nat.Coprime n a then 1 / (4 * (1 - (a : ℝ) / n)) else 0 else 0

/-- The primitive density counterterm, normalized by the integral mean. -/
def densityRow (n : ℕ) : ℝ :=
  if 2 ≤ n then (n.totient : ℝ) * regularMean / (n : ℝ) ^ 2 else 0

def renormalizedRow (n : ℕ) : ℝ := geometricRow n - collisionRow n - densityRow n

/-- Both counterterms leave exactly the primitive quadrature error. -/
theorem renormalizedRow_eq (n : ℕ) :
    renormalizedRow n = if 2 ≤ n then primitiveRowError n / (n : ℝ) ^ 2 else 0 := by
  by_cases hn : 2 ≤ n
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hterm : ∀ a ∈ Icc 1 n,
        (if Nat.Coprime n a then 1 / (1 - ((a : ℝ) / n) ^ 4) else 0) =
          (if Nat.Coprime n a then 1 / (4 * (1 - (a : ℝ) / n)) else 0) +
          (if Nat.Coprime n a then regularProfile ((a : ℝ) / n) else 0) := by
      intro a ha
      by_cases hc : Nat.Coprime n a
      · have haN : a < n := by
          have hal := (mem_Icc.mp ha).2
          have hne : a ≠ n := by
            intro he
            subst a
            have h1 : n = 1 := by simpa only [Nat.coprime_self] using hc
            omega
          exact lt_of_le_of_ne hal hne
        rw [if_pos hc, if_pos hc, if_pos hc]
        exact profile_split (div_nonneg (Nat.cast_nonneg a) hnR.le)
          ((div_lt_one hnR).mpr (by exact_mod_cast haN))
      · simp only [if_neg hc, zero_add]
    rw [renormalizedRow, geometricRow, collisionRow, densityRow, if_pos hn,
      if_pos hn, if_pos hn, if_pos hn, sum_congr rfl hterm, sum_add_distrib,
      primitiveRowError, primitiveSmoothRow]
    ring
  · simp only [renormalizedRow, geometricRow, collisionRow, densityRow, if_neg hn,
      sub_zero]

/-- The prescribed global subtraction has an absolutely convergent remainder. -/
theorem summable_renormalizedRow : Summable renormalizedRow := by
  have h := summable_primitiveRowError_div_sq.indicator {n : ℕ | 2 ≤ n}
  exact h.congr fun n => by simp only [Set.indicator_apply, Set.mem_setOf_eq, renormalizedRow_eq]

/-- The orbit finite part is fixed by the collision pole and the smooth density mean. -/
def orbitFinitePart : ℝ := ∑' n : ℕ, renormalizedRow n

/-- An independently specified finite part of the primitive critical orbit exists. -/
theorem tendsto_orbit_finitePart :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, geometricRow n) -
      (∑ n ∈ range N, collisionRow n) - (∑ n ∈ range N, densityRow n)) atTop
      (𝓝 orbitFinitePart) := by
  have h := summable_renormalizedRow.hasSum.tendsto_sum_nat
  exact h.congr fun N => by simp only [renormalizedRow, sum_sub_distrib]

#print axioms primitiveSmoothRow_moebius
#print axioms regularMean_eq
#print axioms abs_rowError_le
#print axioms geometricRow_eq_localGreenSum
#print axioms summable_renormalizedRow
#print axioms tendsto_orbit_finitePart

end GaloisForLFunctions.HyperbolicArakelovTheory.CoupledOrbit
