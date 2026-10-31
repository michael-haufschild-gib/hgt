import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.AffineShellConductorSelection
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorHeadBoundary

/-!
# A logarithmic packet bound for every centered prime head

Affine conductor selection makes the mixed period means nonnegative.
Their partial prime sums increase to the torsion pairing, while diagonal
corrections decrease to twice the negative tame different. The absolute
torsion bound controls every signed packet uniformly in the head length.
-/

open Filter Topology Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory
  ArithmeticEffectivityTheory ArithmeticIntersectionTheory ArithmeticElectrostatics
noncomputable section

private theorem lagQuotient_dilate {l : ℕ} (hl : 0 < l) (k n : ℕ) :
    l / Nat.gcd l (k * n) = (l / Nat.gcd l k) / Nat.gcd (l / Nat.gcd l k) n := by
  let g := Nat.gcd l k
  let q := l / g
  let u := k / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left k hl
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hl (Nat.gcd_dvd_left l k)) hg
  have hgl : g * q = l := Nat.mul_div_cancel' (Nat.gcd_dvd_left l k)
  have hgk : g * u = k := Nat.mul_div_cancel' (Nat.gcd_dvd_right l k)
  have hqu : q.Coprime u := Nat.coprime_div_gcd_div_gcd hg
  have hsmall : Nat.gcd q (u * n) = Nat.gcd q n := by
    rw [Nat.mul_comm u n, hqu.symm.gcd_mul_right_cancel_right]
  have hlarge : Nat.gcd l (k * n) = g * Nat.gcd q n := by
    rw [← hgl, ← hgk, Nat.mul_assoc, Nat.gcd_mul_left, hsmall]
  have hmul : l = (g * Nat.gcd q n) * (q / Nat.gcd q n) := by
    calc
      l = g * q := hgl.symm
      _ = g * ((q / Nat.gcd q n) * Nat.gcd q n) := by
        rw [Nat.div_mul_cancel (Nat.gcd_dvd_left q n)]
      _ = _ := by ring
  change l / Nat.gcd l (k * n) = q / Nat.gcd q n
  rw [hlarge, hmul, Nat.mul_div_cancel_left _
    (Nat.mul_pos hg (Nat.gcd_pos_of_pos_left n hq))]

/-- Dilation reduces the whole Ramanujan coefficient to one conductor, with its exact totient weight. -/
theorem ramanujanLagCoefficient_dilate_reduced {l : ℕ} (hl : 0 < l) (k n : ℕ) :
    (((l / Nat.gcd l k).totient : ℕ) : ℝ) * ramanujanLagCoefficient l (k * n) =
      (l.totient : ℝ) * ramanujanLagCoefficient (l / Nat.gcd l k) n := by
  have hs : sieveLagMultiplier l (k * n) = sieveLagMultiplier (l / Nat.gcd l k) n := by
    rw [sieveLagMultiplier_eq_moebius_totient_quotient,
      sieveLagMultiplier_eq_moebius_totient_quotient, lagQuotient_dilate hl k n]
  rw [ramanujanLagCoefficient_eq_totient_mul, ramanujanLagCoefficient_eq_totient_mul, hs]
  ring

/-- In normalized conductor coordinates, the dilation weight is the square-root totient ratio. -/
theorem normalizedRamanujanMode_dilate_reduced {l : ℕ} (hl : 0 < l) (k n : ℕ) :
    normalizedRamanujanMode l (k * n) =
      (Real.sqrt (l.totient : ℝ) / Real.sqrt ((l / Nat.gcd l k).totient : ℝ)) *
        normalizedRamanujanMode (l / Nat.gcd l k) n := by
  have hq : 0 < l / Nat.gcd l k := Nat.div_pos
    (Nat.le_of_dvd hl (Nat.gcd_dvd_left l k)) (Nat.gcd_pos_of_pos_left k hl)
  have ha : Real.sqrt (l.totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hl)).ne'
  have hb : Real.sqrt ((l / Nat.gcd l k).totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hq)).ne'
  have h : Real.sqrt ((l / Nat.gcd l k).totient : ℝ) ^ 2 * ramanujanLagCoefficient l (k * n) =
      Real.sqrt (l.totient : ℝ) ^ 2 * ramanujanLagCoefficient (l / Nat.gcd l k) n := by
    simpa only [Real.sq_sqrt (Nat.cast_nonneg (l / Nat.gcd l k).totient),
      Real.sq_sqrt (Nat.cast_nonneg l.totient)] using ramanujanLagCoefficient_dilate_reduced hl k n
  simp only [normalizedRamanujanMode_eq_coefficient hl, normalizedRamanujanMode_eq_coefficient hq]
  field_simp [ha, hb]
  linear_combination h

/-- The literal head is an exact sum of harmonic Grams at reduced conductors and quotient horizons. -/
theorem primeConductorHeadPairing_eq_reducedGram {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (K N : ℕ) :
    primeConductorHeadPairing m l K N =
      ∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
        ((Real.sqrt (l.totient : ℝ) / Real.sqrt ((l / Nat.gcd l k).totient : ℝ) *
            (∑ n ∈ Icc 1 (N / k), normalizedRamanujanMode m n *
              normalizedRamanujanMode (l / Nat.gcd l k) n / (n : ℝ)) +
          Real.sqrt (m.totient : ℝ) / Real.sqrt ((m / Nat.gcd m k).totient : ℝ) *
            (∑ n ∈ Icc 1 (N / k), normalizedRamanujanMode l n *
              normalizedRamanujanMode (m / Nat.gcd m k) n / (n : ℝ))) / Real.log N) := by
  rw [primeConductorHeadPairing]
  apply sum_congr rfl
  intro k _
  apply congrArg (fun x : ℝ => vonMangoldt k / (k : ℝ) * (x / Real.log N))
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  rw [normalizedRamanujanMode_dilate_reduced hl k n, normalizedRamanujanMode_dilate_reduced hm k n]
  ring

/-- The symmetrized complete-period head after its diagonal Mertens term is removed. -/
def centeredPrimeConductorHead (m l K : ℕ) : ℝ :=
  ∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
    (primeConductorDilationMean m l k + primeConductorDilationMean l m k -
      (if m = l then 2 else 0))

/-- A complete-period dilation selects exactly the reduced partner conductor. -/
theorem primeConductorDilationMean_eq_reduced {m l : ℕ} (hm : 0 < m) (hl : 0 < l) (k : ℕ) :
    primeConductorDilationMean m l k =
      if m = l / Nat.gcd l k then
        (l.totient : ℝ) / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) else 0 := by
  have hzero : ramanujanLagCoefficient l 0 = (l.totient : ℝ) := by
    rw [ramanujanLagCoefficient_eq_totient_mul, sieveLagMultiplier_eq_moebius_totient_quotient,
      Nat.gcd_zero_right, Nat.div_self hl]
    simp [moebiusReal]
  have hsum := sum_range_ramanujanLagCoefficient_mul_affine hm hl
    (dvd_mul_right m l) (dvd_mul_left l m) k 0
  simp only [Nat.add_zero, hzero] at hsum
  rw [primeConductorDilationMean, hsum]
  split_ifs
  · have hq : ((m * l : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hm hl).ne'
    rw [mul_div_cancel_left₀ _ hq]
  · simp only [zero_div]

/-- Every mixed dilation mean is nonnegative. -/
theorem primeConductorDilationMean_nonneg {m l : ℕ} (hm : 0 < m) (hl : 0 < l) (k : ℕ) :
    0 ≤ primeConductorDilationMean m l k := by
  rw [primeConductorDilationMean_eq_reduced hm hl]
  split_ifs
  · positivity
  · exact le_rfl

/-- A diagonal dilation mean never exceeds its undilated value. -/
theorem primeConductorDilationMean_self_le_one {m : ℕ} (hm : 0 < m) (k : ℕ) :
    primeConductorDilationMean m m k ≤ 1 := by
  rw [primeConductorDilationMean_eq_reduced hm hm]
  split_ifs
  · rw [← sq, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
    apply le_of_eq
    exact div_self (by exact_mod_cast (Nat.totient_pos.mpr hm).ne')
  · norm_num

/-- Distinct-conductor head means increase inside the exact torsion interval. -/
theorem centeredPrimeConductorHead_offDiagonal_bounds {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hml : m ≠ l) (K : ℕ) :
    0 ≤ centeredPrimeConductorHead m l K ∧
      centeredPrimeConductorHead m l K ≤
        orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) := by
  have hterm (k : ℕ) : 0 ≤ vonMangoldt k / (k : ℝ) *
      (primeConductorDilationMean m l k + primeConductorDilationMean l m k -
        (if m = l then 2 else 0)) := by
    rw [if_neg hml, sub_zero]
    exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
      (add_nonneg (primeConductorDilationMean_nonneg hm hl k) (primeConductorDilationMean_nonneg hl hm k))
  have hlim := tendsto_primeConductorHeadMean_finitePart hm hl
  simp only [if_neg hml, sub_zero] at hlim
  refine ⟨sum_nonneg fun k _ => hterm k, ?_⟩
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop K] with T hKT
  change (∑ k ∈ range K, _) ≤ _
  simp only [if_neg hml, sub_zero]
  apply sum_le_sum_of_subset_of_nonneg (range_mono hKT)
  intro k _ _
  simpa only [if_neg hml, sub_zero] using hterm k

/-- Every diagonal centered head lies between its tame-different limit and zero. -/
theorem centeredPrimeConductorHead_diagonal_bounds {m : ℕ}
    (hm : 0 < m) (K : ℕ) :
    -2 * tameDifferent m ≤ centeredPrimeConductorHead m m K ∧
      centeredPrimeConductorHead m m K ≤ 0 := by
  have hterm (k : ℕ) : vonMangoldt k / (k : ℝ) *
      (primeConductorDilationMean m m k + primeConductorDilationMean m m k - (2 : ℝ)) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
    linarith only [primeConductorDilationMean_self_le_one hm k]
  have hlim := tendsto_primeConductorHeadMean_finitePart hm hm
  simp only [ite_true] at hlim
  have hval : orbitIntersection m m / (Real.sqrt (m.totient : ℝ) * Real.sqrt (m.totient : ℝ)) -
      (Real.log m + tameDifferent m) = -2 * tameDifferent m := by
    rw [orbitIntersection_self_eq hm, localCorrection_eq_totient_mul_tameDifferent,
      ← sq, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
    have hphi : (m.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hm).ne'
    field_simp [hphi]
    ring
  rw [hval] at hlim
  constructor
  · apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop K] with T hKT
    have h := sum_le_sum_of_subset_of_nonneg (s := range K) (t := range T)
      (f := fun k => -(vonMangoldt k / (k : ℝ) *
        (primeConductorDilationMean m m k + primeConductorDilationMean m m k - 2)))
      (range_mono hKT) (fun k _ _ => neg_nonneg.mpr (hterm k))
    simp only [sum_neg_distrib, neg_le_neg_iff] at h
    simpa only [centeredPrimeConductorHead, ite_true] using h
  · simpa only [centeredPrimeConductorHead, ite_true] using sum_nonpos fun k (_ : k ∈ range K) => hterm k

private theorem normalizedTorsion_nonneg {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    0 ≤ orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) := by
  apply div_nonneg _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  by_cases hml : m = l
  · subst l
    rw [orbitIntersection_self_eq hm, localCorrection_eq_totient_mul_tameDifferent]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left (tameDifferent_le_log hm) (Nat.cast_nonneg _))
  · exact orbitIntersection_nonneg_of_ne hm hl hml

private theorem abs_centeredHead_entry_le {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (K : ℕ) :
    |centeredPrimeConductorHead m l K| ≤
      orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) +
        (if m = l then 2 * tameDifferent m else 0) := by
  by_cases hml : m = l
  · subst l
    have h := centeredPrimeConductorHead_diagonal_bounds hm K
    rw [if_pos rfl, abs_of_nonpos h.2]
    linarith only [h.1, normalizedTorsion_nonneg hm hm]
  · have h := centeredPrimeConductorHead_offDiagonal_bounds hm hl hml K
    rw [if_neg hml, add_zero, abs_of_nonneg h.1]
    exact h.2

private theorem normalized_abs_selfMass (Q : ℕ) (a : ℕ → ℝ) :
    selfMass Q (fun m => |a m| / Real.sqrt (m.totient : ℝ)) = ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  unfold selfMass
  apply sum_congr rfl
  intro m hm
  have hphi : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hm).1).ne'
  rw [div_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)]
  field_simp [hphi]

/-- Every centered prime head has logarithmic conductor-packet norm, uniformly in its length. -/
theorem abs_centeredPrimeConductorHeadPacket_le_log (Q K : ℕ) (a : ℕ → ℝ) :
    |∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, a m * a l * centeredPrimeConductorHead m l K| ≤
      (6 * Real.log Q + (Real.log 4 + 4)) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let f : ℕ → ℝ := fun m => |a m| / Real.sqrt (m.totient : ℝ)
  have hmass : selfMass Q f = ∑ m ∈ Icc 1 Q, a m ^ 2 := normalized_abs_selfMass Q a
  have htor := abs_torsionPairing_le_log Q f
  rw [hmass] at htor
  have hentry (m l : ℕ) (hm : m ∈ Icc 1 Q) (hl : l ∈ Icc 1 Q) :
      |a m * a l * centeredPrimeConductorHead m l K| ≤
      f m * f l * orbitIntersection m l +
        (if m = l then a m ^ 2 * (2 * tameDifferent m) else 0) := by
    rw [abs_mul, abs_mul]
    have h := mul_le_mul_of_nonneg_left (abs_centeredHead_entry_le (mem_Icc.mp hm).1 (mem_Icc.mp hl).1 K)
      (mul_nonneg (abs_nonneg (a m)) (abs_nonneg (a l)))
    calc
      _ ≤ _ := h
      _ = _ := by
        dsimp only [f]
        by_cases hml : m = l
        · subst l
          simp only [ite_true, ← sq, div_pow, sq_abs]
          ring
        · simp only [if_neg hml, add_zero]
          ring
  have hdiag : (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
      if m = l then a m ^ 2 * (2 * tameDifferent m) else 0) ≤
      2 * Real.log Q * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
    simp only [sum_ite_eq, mem_Icc]
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    rw [if_pos (mem_Icc.mp hm)]
    have hlog : Real.log (m : ℝ) ≤ Real.log Q :=
      Real.log_le_log (by exact_mod_cast (mem_Icc.mp hm).1) (by exact_mod_cast (mem_Icc.mp hm).2)
    have ht := (tameDifferent_le_log (mem_Icc.mp hm).1).trans hlog
    nlinarith only [mul_le_mul_of_nonneg_right ht (sq_nonneg (a m))]
  calc
    _ ≤ ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, |a m * a l * centeredPrimeConductorHead m l K| := by
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
        (f m * f l * orbitIntersection m l +
          (if m = l then a m ^ 2 * (2 * tameDifferent m) else 0)) :=
      sum_le_sum fun m hm => sum_le_sum fun l hl => hentry m l hm hl
    _ = torsionPairing Q f + ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
        if m = l then a m ^ 2 * (2 * tameDifferent m) else 0 := by
      simp only [sum_add_distrib, torsionPairing]
    _ ≤ (4 * Real.log Q + (Real.log 4 + 4)) * (∑ m ∈ Icc 1 Q, a m ^ 2) +
        2 * Real.log Q * (∑ m ∈ Icc 1 Q, a m ^ 2) :=
      add_le_add ((le_abs_self _).trans htor) hdiag
    _ = _ := by ring

#print axioms centeredPrimeConductorHead_offDiagonal_bounds
#print axioms centeredPrimeConductorHead_diagonal_bounds
#print axioms abs_centeredPrimeConductorHeadPacket_le_log
#print axioms ramanujanLagCoefficient_dilate_reduced
#print axioms normalizedRamanujanMode_dilate_reduced
#print axioms primeConductorHeadPairing_eq_reducedGram
#print axioms primeConductorDilationMean_eq_reduced
#print axioms primeConductorDilationMean_nonneg
#print axioms primeConductorDilationMean_self_le_one

end
end GaloisForLFunctions.SuccessorShellArithmetic
