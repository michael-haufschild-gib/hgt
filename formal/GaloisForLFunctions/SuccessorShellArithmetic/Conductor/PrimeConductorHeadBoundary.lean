import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorFinitePart
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTwistedCompleteWeilFormHasAPeriodicLimit

/-!
# The torsion boundary between fixed prime heads and the full prime form

Complete-period averaging of the centered prime rows retains a positive
torsion intersection. Harmonic averaging of each fixed dilation gives the
same head coefficient. The full prime cutoff has the opposite torsion
finite part, so its complementary boundary retains minus twice the
intersection.
-/

open Filter Topology Finset ArithmeticFunction
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory
  RenormalizedBiarithmeticGeometry CriticalArithmeticCorrelationTheory
  ArithmeticEffectivityTheory ArithmeticIntersectionTheory ArithmeticElectrostatics
noncomputable section

private theorem lag_periodic_of_dvd {m q : ℕ} (hmq : m ∣ q) :
    Function.Periodic (ramanujanLagCoefficient m) q := by
  intro n
  unfold ramanujanLagCoefficient
  apply sum_congr rfl
  intro d hd
  simp only [Nat.dvd_add_left ((Nat.dvd_of_mem_divisors hd).trans hmq)]

private theorem jet_periodic_of_dvd {m q : ℕ} (hmq : m ∣ q) :
    Function.Periodic (ramanujanLogDivisorJet m) q := by
  intro n
  unfold ramanujanLogDivisorJet
  apply sum_congr rfl
  intro d hd
  simp only [Nat.dvd_add_left ((Nat.dvd_of_mem_divisors hd).trans hmq)]

private theorem lag_dilate_product_periodic {m l q : ℕ}
    (hmq : m ∣ q) (hlq : l ∣ q) (k : ℕ) :
    Function.Periodic (fun n => ramanujanLagCoefficient m n *
      ramanujanLagCoefficient l (k * n)) q := by
  have hm := lag_periodic_of_dvd hmq
  have hl := (lag_periodic_of_dvd hlq).nat_mul k
  intro n
  simp only [Nat.cast_id] at hl
  change ramanujanLagCoefficient m (n + q) * ramanujanLagCoefficient l (k * (n + q)) = _
  rw [hm, Nat.mul_add, hl]

private theorem sum_lag_mul_jet {m l q : ℕ} (hm : 0 < m) (hl : 0 < l)
    (hmq : m ∣ q) (hlq : l ∣ q) :
    (∑ n ∈ range q, ramanujanLagCoefficient m n * ramanujanLogDivisorJet l n) =
      if m ∣ l then (q : ℝ) * m.totient * ramanujanJetConductorWeight l m else 0 := by
  simp_rw [ramanujanLogDivisorJet_eq_weighted_conductors hl, mul_sum]
  rw [sum_comm]
  have hterm (d : ℕ) (hd : d ∈ l.divisors) :
      (∑ n ∈ range q, ramanujanLagCoefficient m n *
        (ramanujanJetConductorWeight l d * ramanujanLagCoefficient d n)) =
      if d = m then (q : ℝ) * m.totient * ramanujanJetConductorWeight l m else 0 := by
    calc
      _ = ramanujanJetConductorWeight l d *
          ∑ n ∈ range q, ramanujanLagCoefficient m n * ramanujanLagCoefficient d n := by
        rw [mul_sum]
        exact sum_congr rfl fun n _ => by ring
      _ = _ := by
        rw [sum_range_ramanujanLagCoefficient_mul hm (Nat.pos_of_mem_divisors hd)
          hmq ((Nat.dvd_of_mem_divisors hd).trans hlq)]
        by_cases hdm : d = m
        · subst d
          simp only [ite_true]
          ring
        · simp only [if_neg hdm, if_neg (Ne.symm hdm), mul_zero]
  rw [sum_congr rfl hterm, sum_ite_eq']
  by_cases hml : m ∣ l
  · rw [if_pos (Nat.mem_divisors.mpr ⟨hml, hl.ne'⟩), if_pos hml]
  · rw [if_neg (fun h => hml (Nat.dvd_of_mem_divisors h)), if_neg hml]

/-- The complete-period mean of a conductor against one multiplicative dilation. -/
def primeConductorDilationMean (m l k : ℕ) : ℝ :=
  (∑ n ∈ range (m * l), ramanujanLagCoefficient m n * ramanujanLagCoefficient l (k * n)) /
    (m * l : ℕ) / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))

private theorem tendsto_centered_primePeriodPairing {m l q : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hmq : m ∣ q) (hlq : l ∣ q) :
    Tendsto (fun K : ℕ =>
      ∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
        ((∑ n ∈ range q, ramanujanLagCoefficient m n * ramanujanLagCoefficient l (k * n)) -
          (if m = l then (q : ℝ) * m.totient else 0))) atTop
      (𝓝 ((q : ℝ) * ((if m ∣ l then (m.totient : ℝ) * vonMangoldt (l / m) else 0) -
        (if m = l then (m.totient : ℝ) * tameDifferent m else 0)))) := by
  have hrow (n : ℕ) :
      Tendsto (fun K : ℕ => ∑ k ∈ range K,
        ramanujanLagCoefficient m (n + 1) * ramanujanUpCorrectionTerm l (n + 1) k) atTop
      (𝓝 (ramanujanLagCoefficient m (n + 1) *
        (-(Real.log l + tameDifferent l) * ramanujanLagCoefficient l (n + 1) +
          ramanujanLogDivisorJet l (n + 1)))) := by
    have h := ((hasSum_ramanujan_correction l hl (n + 1) (by omega)).mul_left
      (ramanujanLagCoefficient m (n + 1))).tendsto_sum_nat
    rw [ramanujanDownCorrection_eq_neg_logDivisorJet l (by omega), sub_neg_eq_add] at h
    exact h
  have hlim := tendsto_finsetSum (range q) fun n _ => hrow n
  have hgram : (∑ n ∈ range q, ramanujanLagCoefficient m n * ramanujanLagCoefficient l n) =
      if m = l then (q : ℝ) * m.totient else 0 := by
    rw [sum_range_ramanujanLagCoefficient_mul hm hl hmq hlq]
    by_cases hml : m = l
    · subst l
      rfl
    · simp only [if_neg hml]
  have hshift (k : ℕ) :
      (∑ n ∈ range q, ramanujanLagCoefficient m (n + 1) *
        ramanujanLagCoefficient l (k * (n + 1))) =
      ∑ n ∈ range q, ramanujanLagCoefficient m n * ramanujanLagCoefficient l (k * n) := by
    simpa only [Nat.add_comm] using
      RenormalizedBiarithmeticGeometry.sum_range_shift_of_periodic
        (p := fun n => ramanujanLagCoefficient m n * ramanujanLagCoefficient l (k * n))
        (q := q) (fun n => lag_dilate_product_periodic hmq hlq k n) 1
  have hshiftGram :
      (∑ n ∈ range q, ramanujanLagCoefficient m (n + 1) * ramanujanLagCoefficient l (n + 1)) =
      if m = l then (q : ℝ) * m.totient else 0 := by
    simpa only [Nat.one_mul] using (hshift 1).trans (by simpa only [Nat.one_mul] using hgram)
  have hshiftJet :
      (∑ n ∈ range q, ramanujanLagCoefficient m (n + 1) * ramanujanLogDivisorJet l (n + 1)) =
      if m ∣ l then (q : ℝ) * m.totient * ramanujanJetConductorWeight l m else 0 := by
    have hp : Function.Periodic (fun n => ramanujanLagCoefficient m n * ramanujanLogDivisorJet l n) q := by
      intro n
      exact congrArg₂ (· * ·) (lag_periodic_of_dvd hmq n) (jet_periodic_of_dvd hlq n)
    have hs := RenormalizedBiarithmeticGeometry.sum_range_shift_of_periodic
      (p := fun n => ramanujanLagCoefficient m n * ramanujanLogDivisorJet l n)
      (q := q) (fun n => hp n) 1
    calc
      _ = ∑ n ∈ range q, ramanujanLagCoefficient m n * ramanujanLogDivisorJet l n := by
        simpa only [Nat.add_comm] using hs
      _ = _ := sum_lag_mul_jet hm hl hmq hlq
  have hfun (K : ℕ) :
      (∑ n ∈ range q, ∑ k ∈ range K,
        ramanujanLagCoefficient m (n + 1) * ramanujanUpCorrectionTerm l (n + 1) k) =
      ∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
        ((∑ n ∈ range q, ramanujanLagCoefficient m n * ramanujanLagCoefficient l (k * n)) -
          (if m = l then (q : ℝ) * m.totient else 0)) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    calc
      _ = vonMangoldt k / (k : ℝ) *
          ((∑ n ∈ range q, ramanujanLagCoefficient m (n + 1) * ramanujanLagCoefficient l (k * (n + 1))) -
            ∑ n ∈ range q, ramanujanLagCoefficient m (n + 1) * ramanujanLagCoefficient l (n + 1)) := by
        rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro n _
        rw [ramanujanUpCorrectionTerm, Nat.mul_comm (n + 1) k]
        ring
      _ = _ := by rw [hshift, hshiftGram]
  have hval :
      (∑ n ∈ range q, ramanujanLagCoefficient m (n + 1) *
        (-(Real.log l + tameDifferent l) * ramanujanLagCoefficient l (n + 1) +
          ramanujanLogDivisorJet l (n + 1))) =
      (q : ℝ) * ((if m ∣ l then (m.totient : ℝ) * vonMangoldt (l / m) else 0) -
        (if m = l then (m.totient : ℝ) * tameDifferent m else 0)) := by
    calc
      _ = -(Real.log l + tameDifferent l) *
          (∑ n ∈ range q, ramanujanLagCoefficient m (n + 1) * ramanujanLagCoefficient l (n + 1)) +
          ∑ n ∈ range q, ramanujanLagCoefficient m (n + 1) * ramanujanLogDivisorJet l (n + 1) := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun n _ => by ring
      _ = _ := by
        rw [hshiftGram, hshiftJet]
        by_cases hml : m = l
        · subst l
          simp only [ite_true, dvd_refl, ramanujanJetConductorWeight, Nat.div_self hm,
            vonMangoldt_apply_one, add_zero]
          ring
        · simp only [ramanujanJetConductorWeight, if_neg hml, mul_zero,
            zero_add, sub_zero]
          split_ifs <;> ring
  rw [hval] at hlim
  exact hlim.congr' (Filter.Eventually.of_forall hfun)


private theorem tendsto_centered_primeConductorDilationMean {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun K : ℕ => ∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
      (primeConductorDilationMean m l k - (if m = l then 1 else 0))) atTop
      (𝓝 (((if m ∣ l then (m.totient : ℝ) * vonMangoldt (l / m) else 0) -
        (if m = l then (m.totient : ℝ) * tameDifferent m else 0)) /
          (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)))) := by
  let q := m * l
  let d := Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hm hl).ne'
  have hd : d ≠ 0 := mul_ne_zero
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hm)).ne'
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hl)).ne'
  have hdiag : (if m = l then (q : ℝ) * m.totient else 0) / ((q : ℝ) * d) =
      if m = l then 1 else 0 := by
    by_cases hml : m = l
    · subst l
      simp only [ite_true, d, ← sq, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
      exact div_self (mul_ne_zero hq (by exact_mod_cast (Nat.totient_pos.mpr hm).ne'))
    · simp only [if_neg hml, zero_div]
  have h := (tendsto_centered_primePeriodPairing hm hl
    (dvd_mul_right m l) (dvd_mul_left l m)).div_const ((q : ℝ) * d)
  have hval : ((q : ℝ) * ((if m ∣ l then (m.totient : ℝ) * vonMangoldt (l / m) else 0) -
      (if m = l then (m.totient : ℝ) * tameDifferent m else 0))) / ((q : ℝ) * d) =
      ((if m ∣ l then (m.totient : ℝ) * vonMangoldt (l / m) else 0) -
      (if m = l then (m.totient : ℝ) * tameDifferent m else 0)) / d := by
    field_simp [hq, hd]
  change Tendsto _ atTop (𝓝 _) at h
  rw [hval] at h
  refine h.congr fun K => ?_
  rw [sum_div]
  apply sum_congr rfl
  intro k _
  rw [mul_div_assoc, sub_div, hdiag]
  simp only [primeConductorDilationMean, q, d, div_div]

/-- Both centered prime orientations have the positive torsion finite part. -/
theorem tendsto_primeConductorHeadMean_finitePart {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun K : ℕ => ∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
      (primeConductorDilationMean m l k + primeConductorDilationMean l m k -
        (if m = l then 2 else 0))) atTop
      (𝓝 (orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m else 0))) := by
  have h := (tendsto_centered_primeConductorDilationMean hm hl).add
    (tendsto_centered_primeConductorDilationMean hl hm)
  have hfun (K : ℕ) :
      (∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
        (primeConductorDilationMean m l k - (if m = l then 1 else 0))) +
      (∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
        (primeConductorDilationMean l m k - (if l = m then 1 else 0))) =
      ∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
        (primeConductorDilationMean m l k + primeConductorDilationMean l m k -
          (if m = l then 2 else 0)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    by_cases hml : m = l
    · subst l
      simp only [ite_true]
      ring
    · simp only [if_neg hml, if_neg (Ne.symm hml)]
      ring
  have hval :
      (((if m ∣ l then (m.totient : ℝ) * vonMangoldt (l / m) else 0) -
        (if m = l then (m.totient : ℝ) * tameDifferent m else 0)) /
          (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))) +
      (((if l ∣ m then (l.totient : ℝ) * vonMangoldt (m / l) else 0) -
        (if l = m then (l.totient : ℝ) * tameDifferent l else 0)) /
          (Real.sqrt (l.totient : ℝ) * Real.sqrt (m.totient : ℝ))) =
      orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m else 0) := by
    by_cases hml : m = l
    · subst l
      rw [orbitIntersection_self_eq hm, localCorrection_eq_totient_mul_tameDifferent]
      simp only [ite_true, dvd_refl, Nat.div_self hm, vonMangoldt_apply_one, mul_zero,
        zero_sub, ← sq, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
      have hphi : (m.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hm).ne'
      field_simp
      ring
    · rw [orbitIntersection_eq hm hl hml]
      simp only [if_neg hml, if_neg (Ne.symm hml), sub_zero]
      by_cases hmlD : m ∣ l
      · have hlmD : ¬ l ∣ m := fun hd => hml (Nat.dvd_antisymm hmlD hd)
        simp only [if_pos hmlD, if_neg hlmD, zero_div, add_zero]
      · by_cases hlmD : l ∣ m
        · simp only [if_neg hmlD, if_pos hlmD, zero_div, zero_add]
          ring
        · simp only [if_neg hmlD, if_neg hlmD, zero_div, zero_add]
  rw [hval] at h
  exact h.congr' (Filter.Eventually.of_forall hfun)

/-- The fixed prime head, retaining both orientations and the exact ratio cutoff. -/
def primeConductorHeadPairing (m l K N : ℕ) : ℝ :=
  ∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
    ((∑ n ∈ Icc 1 (N / k),
      (normalizedRamanujanMode m n * normalizedRamanujanMode l (k * n) +
        normalizedRamanujanMode l n * normalizedRamanujanMode m (k * n)) / (n : ℝ)) /
          Real.log N)

/-- The complete-period reading of the fixed prime head. -/
def primeConductorHeadMean (m l K : ℕ) : ℝ :=
  ∑ k ∈ range K, vonMangoldt k / (k : ℝ) *
    (primeConductorDilationMean m l k + primeConductorDilationMean l m k)

private theorem fullPrimeMatrix_inner_normalized (m l N : ℕ) :
    ⟪normalizedRamanujanHorizonVector m N,
      Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector l N)⟫ =
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        ramanujanPoleProfile m n * ramanujanPoleProfile l j * weilPrimeKernel n j) / Real.log N := by
  have hraw : ⟪ramanujanHorizonVector m N,
      Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector l N)⟫ =
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        ramanujanPoleProfile m n * ramanujanPoleProfile l j * weilPrimeKernel n j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ n : PrimeHorizonIndex N,
      (Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector l N)) n *
        ramanujanPoleProfile m n) = _
    simp_rw [fullPrimeMatrix_apply_ramanujanHorizonVector]
    rw [sum_coe_sort (Icc 1 N) (fun n =>
      (∑ j ∈ Icc 1 N, weilPrimeKernel n j * ramanujanPoleProfile l j) * ramanujanPoleProfile m n)]
    apply sum_congr rfl
    intro n _
    rw [sum_mul]
    exact sum_congr rfl fun j _ => by ring
  rw [normalizedRamanujanHorizonVector, normalizedRamanujanHorizonVector, map_smul,
    real_inner_smul_left, real_inner_smul_right, hraw]
  have hs : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← mul_assoc, hs]
  ring

private theorem sum_prime_pair_eq_edges (N : ℕ) (x y : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * y j * weilPrimeKernel n j) =
      ∑ k ∈ Icc 1 N, ∑ n ∈ Icc 1 (N / k), vonMangoldt k / Real.sqrt k *
        (x n * y (k * n) + y n * x (k * n)) := by
  have hup (a b : ℕ → ℝ) :
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, a n * b j * upKernel n j) =
      ∑ k ∈ Icc 1 N, ∑ n ∈ Icc 1 (N / k), vonMangoldt k / Real.sqrt k * (a n * b (k * n)) := by
    have hrow (n : ℕ) (hn : n ∈ Icc 1 N) :
        (∑ j ∈ Icc 1 N, a n * b j * upKernel n j) =
        ∑ k ∈ Icc 1 (N / n), vonMangoldt k / Real.sqrt k * (a n * b (k * n)) := by
      have hn0 := (mem_Icc.mp hn).1
      have h := sum_up_eq_of_self (N := N) hn0
        (fun j => a n * b j * (vonMangoldt (j / n) / Real.sqrt ((j / n : ℕ) : ℝ)))
        (by simp only [Nat.div_self hn0, vonMangoldt_apply_one, zero_div, mul_zero])
      have he : (∑ j ∈ Icc 1 N, a n * b j * upKernel n j) =
          ∑ j ∈ Icc 1 N, if n ∣ j ∧ n ≠ j then
            a n * b j * (vonMangoldt (j / n) / Real.sqrt ((j / n : ℕ) : ℝ)) else 0 := by
        apply sum_congr rfl
        intro j _
        unfold upKernel
        split_ifs <;> simp only [mul_zero]
      rw [he, h]
      apply sum_congr rfl
      intro k _
      rw [Nat.mul_div_cancel_left k hn0, Nat.mul_comm n k]
      ring
    rw [sum_congr rfl hrow]
    apply sum_comm'
    intro n k
    simp only [mem_Icc]
    constructor
    · rintro ⟨⟨hn, _⟩, hk, hkN⟩
      rw [Nat.le_div_iff_mul_le hn] at hkN
      refine ⟨⟨hn, ?_⟩, hk, ?_⟩
      · rw [Nat.le_div_iff_mul_le hk]
        simpa only [Nat.mul_comm] using hkN
      · nlinarith only [hkN, hn]
    · rintro ⟨⟨hn, hnN⟩, hk, _⟩
      rw [Nat.le_div_iff_mul_le hk] at hnN
      refine ⟨⟨hn, ?_⟩, hk, ?_⟩
      · nlinarith only [hnN, hk]
      · rw [Nat.le_div_iff_mul_le hn]
        simpa only [Nat.mul_comm] using hnN
  have hswap : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * y j * upKernel j n) =
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, y n * x j * upKernel n j := by
    rw [sum_comm]
    exact sum_congr rfl fun n _ => sum_congr rfl fun j _ => by ring
  simp_rw [weilPrimeKernel_eq_up_add, mul_add]
  simp only [sum_add_distrib]
  rw [hswap, hup, hup]

private theorem prime_pole_edge (m l k n : ℕ) :
    vonMangoldt k / Real.sqrt k * (ramanujanPoleProfile m n * ramanujanPoleProfile l (k * n)) =
      vonMangoldt k / (k : ℝ) *
        (normalizedRamanujanMode m n * normalizedRamanujanMode l (k * n) / (n : ℝ)) := by
  rw [ramanujanPoleProfile, ramanujanPoleProfile, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg k)]
  calc
    _ = vonMangoldt k * (normalizedRamanujanMode m n * normalizedRamanujanMode l (k * n)) /
        (Real.sqrt (k : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 2) := by ring
    _ = _ := by
      rw [Real.sq_sqrt (Nat.cast_nonneg k), Real.sq_sqrt (Nat.cast_nonneg n)]
      ring

/-- A head containing every possible dilation is exactly the literal full prime matrix. -/
theorem primeConductorHeadPairing_horizon (m l N : ℕ) :
    primeConductorHeadPairing m l (N + 1) N =
      ⟪normalizedRamanujanHorizonVector m N,
        Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector l N)⟫ := by
  have hset : range (N + 1) = insert 0 (Icc 1 N) := by
    ext k
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [primeConductorHeadPairing, hset, sum_insert (by simp)]
  simp only [Nat.cast_zero, div_zero, zero_mul, zero_add]
  rw [fullPrimeMatrix_inner_normalized, sum_prime_pair_eq_edges, sum_div]
  apply sum_congr rfl
  intro k _
  simp only [mul_add, prime_pole_edge]
  simp only [← mul_add, ← add_div]
  rw [← mul_sum, mul_div_assoc]

/-- One fixed dilation has its complete-period mean at the hyperbolic harmonic cutoff. -/
theorem tendsto_primeConductorHarmonicDilationMean {m l k : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hk : 0 < k) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 (N / k), normalizedRamanujanMode m n *
        normalizedRamanujanMode l (k * n) / (n : ℝ)) / Real.log N) atTop
      (𝓝 (primeConductorDilationMean m l k)) := by
  have hp : Function.Periodic (fun n => normalizedRamanujanMode m n *
      normalizedRamanujanMode l (k * n)) (m * l) := by
    intro n
    simp only [normalizedRamanujanMode_eq_coefficient hm,
      normalizedRamanujanMode_eq_coefficient hl, div_mul_div_comm]
    exact congrArg (fun x : ℝ => x /
      (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)))
      (lag_dilate_product_periodic (dvd_mul_right m l) (dvd_mul_left l m) k n)
  have hmean : periodMean (fun n => normalizedRamanujanMode m n *
      normalizedRamanujanMode l (k * n)) (m * l) = primeConductorDilationMean m l k := by
    simp only [periodMean, primeConductorDilationMean,
      normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hl,
      div_mul_div_comm, ← sum_div]
    ring
  simpa only [hmean] using tendsto_harmonic_mean_div (Nat.mul_pos hm hl) hp hk

/-- The actual logarithmic head has exactly its complete-period limit. -/
theorem tendsto_primeConductorHeadPairing {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (K : ℕ) :
    Tendsto (primeConductorHeadPairing m l K) atTop (𝓝 (primeConductorHeadMean m l K)) := by
  unfold primeConductorHeadPairing primeConductorHeadMean
  apply tendsto_finsetSum (range K)
  intro k _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, div_zero, zero_mul]
    exact tendsto_const_nhds
  · simpa only [add_div, sum_add_distrib] using
      ((tendsto_primeConductorHarmonicDilationMean hm hl hk).add
        (tendsto_primeConductorHarmonicDilationMean hl hm hk)).const_mul
          (vonMangoldt k / (k : ℝ))

/-- Subtracting the exact diagonal head divergence exposes the torsion finite part. -/
theorem tendsto_primeConductorHeadMean_sub_scalar {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun K : ℕ => primeConductorHeadMean m l K -
      (if m = l then 2 * ∑ k ∈ range K, vonMangoldt k / (k : ℝ) else 0)) atTop
      (𝓝 (orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m else 0))) := by
  apply (tendsto_primeConductorHeadMean_finitePart hm hl).congr
  intro K
  simp only [mul_sub, sum_sub_distrib, primeConductorHeadMean]
  congr 1
  by_cases hml : m = l
  · simp only [if_pos hml, ← sum_mul]
    ring
  · simp only [if_neg hml, mul_zero, sum_const_zero]

/-- The finite part left after subtracting the fixed prime head from the full prime form. -/
def primeConductorBoundaryFinitePart (m l K : ℕ) : ℝ :=
  -orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
    (if m = l then Real.log m + tameDifferent m else 0) -
      (primeConductorHeadMean m l K -
        (if m = l then 2 * ∑ k ∈ range K, vonMangoldt k / (k : ℝ) else 0))

/-- The complementary prime boundary has an exact inner limit at every fixed head. -/
theorem tendsto_primeConductorBoundaryPairing {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (K : ℕ) :
    Tendsto (fun N : ℕ =>
      ⟪normalizedRamanujanHorizonVector m N,
        Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector l N)⟫ -
      primeConductorHeadPairing m l K N -
      (if m = l then Real.log N - 2 * ∑ k ∈ range K, vonMangoldt k / (k : ℝ) else 0)) atTop
      (𝓝 (primeConductorBoundaryFinitePart m l K)) := by
  have h := (tendsto_primeConductorPairing_finitePart hm hl).sub
    ((tendsto_primeConductorHeadPairing hm hl K).sub_const
      (if m = l then 2 * ∑ k ∈ range K, vonMangoldt k / (k : ℝ) else 0))
  change Tendsto _ atTop (𝓝 (primeConductorBoundaryFinitePart m l K)) at h
  apply h.congr
  intro N
  split_ifs <;> ring

/-- Removing the full head leaves exactly minus twice the normalized torsion intersection. -/
theorem tendsto_primeConductorBoundaryFinitePart {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) :
    Tendsto (primeConductorBoundaryFinitePart m l) atTop
      (𝓝 (-2 * orbitIntersection m l /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)))) := by
  have h := (tendsto_primeConductorHeadMean_sub_scalar hm hl).const_sub
    (-orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
      (if m = l then Real.log m + tameDifferent m else 0))
  convert h using 1
  congr 1
  ring

#print axioms tendsto_primeConductorHeadMean_finitePart
#print axioms primeConductorHeadPairing_horizon
#print axioms tendsto_primeConductorHarmonicDilationMean
#print axioms tendsto_primeConductorHeadPairing
#print axioms tendsto_primeConductorHeadMean_sub_scalar
#print axioms tendsto_primeConductorBoundaryPairing
#print axioms tendsto_primeConductorBoundaryFinitePart

end
end GaloisForLFunctions.SuccessorShellArithmetic
