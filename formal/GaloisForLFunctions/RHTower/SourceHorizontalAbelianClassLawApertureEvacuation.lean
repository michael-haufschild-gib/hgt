import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ClassLaw
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential

/-!
# Exact abelian-class realization and unavoidable aperture evacuation

Two fixed convergent abelian zeta class laws realize the reflected adaptive horizontal prime
occupations exactly.  The realization uses the canonical pair

`A_N = (Z/pZ)^(N+1)` and `B_N = Z/p^(2N)Z`.

The coefficient problem is therefore closed for two-class events.  The price is exponential source
mass evacuation: the admitted two-class aperture tends to zero in both orientations.  A final
classification proves that the canonical pair has the smallest possible order/socle statistics
among prime-primary two-class realizations of the same two log-odds equations.

This is a positive survivor of the failed uniformly-admitted observer conjecture.  It uses no RH
premise and does not assert a source renewal that replenishes the lost aperture.
-/

open Real Set MeasureTheory Filter Topology
open scoped ENNReal

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Canonical source laws and prime-primary classes -/

/-- Forward convergent class law with horizontal displacement stored in the socle exponent. -/
def sourceHorizontalAbelianForwardParameters
    (a : ℝ) (_ha0 : 0 ≤ a) (ha1 : a < 1) : AbelianZetaConvergentParameters where
  sigma := 1
  tau := 1 - a
  sigma_pos := by norm_num
  tau_nonneg := by linarith
  firstDepth := by linarith

/-- Reflected convergent class law. -/
def sourceHorizontalAbelianReverseParameters
    (a : ℝ) (ha0 : 0 ≤ a) : AbelianZetaConvergentParameters where
  sigma := 1
  tau := 1 + a
  sigma_pos := by norm_num
  tau_nonneg := by linarith
  firstDepth := by linarith

/-- Elementary abelian success class `(Z/pZ)^(N+1)`. -/
def sourceHorizontalAbelianElementaryClass
    (p : Nat.Primes) (N : ℕ) : AbelianZetaGroupClass :=
  Finsupp.single (p, 0) (N + 1)

/-- Cyclic comparison class `Z/p^(2N)Z`.  Its intended range is `N >= 1`. -/
def sourceHorizontalAbelianCyclicClass
    (p : Nat.Primes) (N : ℕ) : AbelianZetaGroupClass :=
  Finsupp.single (p, 2 * N - 1) 1

theorem sourceHorizontalAbelianElementaryClass_order
    (p : Nat.Primes) (N : ℕ) :
    (sourceHorizontalAbelianElementaryClass p N).order = p ^ (N + 1) := by
  unfold sourceHorizontalAbelianElementaryClass AbelianZetaGroupClass.order
  rw [Finsupp.prod_single_index]
  · simp [AbelianZetaMode.depth]
  · simp

theorem sourceHorizontalAbelianElementaryClass_socleOrder
    (p : Nat.Primes) (N : ℕ) :
    (sourceHorizontalAbelianElementaryClass p N).socleOrder = p ^ (N + 1) := by
  unfold sourceHorizontalAbelianElementaryClass AbelianZetaGroupClass.socleOrder
  rw [Finsupp.prod_single_index]
  simp

theorem sourceHorizontalAbelianCyclicClass_order
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N) :
    (sourceHorizontalAbelianCyclicClass p N).order = p ^ (2 * N) := by
  have hdepth : AbelianZetaMode.depth (p, 2 * N - 1) = 2 * N := by
    simp [AbelianZetaMode.depth]
    omega
  unfold sourceHorizontalAbelianCyclicClass AbelianZetaGroupClass.order
  rw [Finsupp.prod_single_index]
  · simp [hdepth]
  · simp

theorem sourceHorizontalAbelianCyclicClass_socleOrder
    (p : Nat.Primes) (N : ℕ) :
    (sourceHorizontalAbelianCyclicClass p N).socleOrder = p := by
  unfold sourceHorizontalAbelianCyclicClass AbelianZetaGroupClass.socleOrder
  rw [Finsupp.prod_single_index] <;> simp

private lemma sourceHorizontal_cast_pow_rpow
    (p : Nat.Primes) (n : ℕ) (x : ℝ) :
    (((p : ℕ) ^ n : ℕ) : ℝ) ^ x = (p : ℝ) ^ ((n : ℝ) * x) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  exact (Real.rpow_mul (by positivity : (0 : ℝ) ≤ p) n x).symm

/-! ## Exact two-observable source weights -/

theorem sourceHorizontalAbelianForwardWeight_elementary
    (p : Nat.Primes) (N : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    abelianZetaTwoObservableWeight
        (sourceHorizontalAbelianForwardParameters a ha0 ha1).toAbelianZetaParameters
        (sourceHorizontalAbelianElementaryClass p N) =
      (p : ℝ) ^ ((a - 2) * (N + 1)) := by
  rw [abelianZetaTwoObservableWeight,
    sourceHorizontalAbelianElementaryClass_order,
    sourceHorizontalAbelianElementaryClass_socleOrder]
  simp only [sourceHorizontalAbelianForwardParameters]
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [sourceHorizontal_cast_pow_rpow, sourceHorizontal_cast_pow_rpow,
    ← Real.rpow_add hp]
  congr 1
  push_cast
  ring

theorem sourceHorizontalAbelianForwardWeight_cyclic
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    abelianZetaTwoObservableWeight
        (sourceHorizontalAbelianForwardParameters a ha0 ha1).toAbelianZetaParameters
        (sourceHorizontalAbelianCyclicClass p N) =
      (p : ℝ) ^ (-2 * N - 1 + a) := by
  rw [abelianZetaTwoObservableWeight,
    sourceHorizontalAbelianCyclicClass_order p N hN,
    sourceHorizontalAbelianCyclicClass_socleOrder]
  simp only [sourceHorizontalAbelianForwardParameters]
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [sourceHorizontal_cast_pow_rpow]
  change (p : ℝ) ^ ((2 * N : ℕ) * (-1 : ℝ)) *
      (p : ℝ) ^ (-(1 - a)) = _
  rw [← Real.rpow_add hp]
  congr 1
  push_cast
  ring

theorem sourceHorizontalAbelianReverseWeight_elementary
    (p : Nat.Primes) (N : ℕ) {a : ℝ} (ha0 : 0 ≤ a) :
    abelianZetaTwoObservableWeight
        (sourceHorizontalAbelianReverseParameters a ha0).toAbelianZetaParameters
        (sourceHorizontalAbelianElementaryClass p N) =
      (p : ℝ) ^ (-(a + 2) * (N + 1)) := by
  rw [abelianZetaTwoObservableWeight,
    sourceHorizontalAbelianElementaryClass_order,
    sourceHorizontalAbelianElementaryClass_socleOrder]
  simp only [sourceHorizontalAbelianReverseParameters]
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [sourceHorizontal_cast_pow_rpow, sourceHorizontal_cast_pow_rpow,
    ← Real.rpow_add hp]
  congr 1
  push_cast
  ring

theorem sourceHorizontalAbelianReverseWeight_cyclic
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N) {a : ℝ} (ha0 : 0 ≤ a) :
    abelianZetaTwoObservableWeight
        (sourceHorizontalAbelianReverseParameters a ha0).toAbelianZetaParameters
        (sourceHorizontalAbelianCyclicClass p N) =
      (p : ℝ) ^ (-2 * N - 1 - a) := by
  rw [abelianZetaTwoObservableWeight,
    sourceHorizontalAbelianCyclicClass_order p N hN,
    sourceHorizontalAbelianCyclicClass_socleOrder]
  simp only [sourceHorizontalAbelianReverseParameters]
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [sourceHorizontal_cast_pow_rpow]
  change (p : ℝ) ^ ((2 * N : ℕ) * (-1 : ℝ)) *
      (p : ℝ) ^ (-(1 + a)) = _
  rw [← Real.rpow_add hp]
  congr 1
  push_cast
  ring

/-! ## Actual class-law conditional probabilities -/

private theorem sourceHorizontalAbelianClassAtomMass
    (theta : AbelianZetaConvergentParameters) (A : AbelianZetaGroupClass) :
    (classLaw theta.toAbelianZetaParameters {A}).toReal =
      theta.ennNormalizer.toReal *
        abelianZetaTwoObservableWeight theta.toAbelianZetaParameters A := by
  rw [classLaw_singleton, theta.classMass_eq_ennNormalizer_mul_twoObservableWeight,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  exact AbelianZetaConvergentParameters.twoObservableWeight_nonneg
    theta.toAbelianZetaParameters A

/-- Success probability of the elementary class conditional on the canonical two-class aperture. -/
def sourceHorizontalAbelianTwoClassConditional
    (theta : AbelianZetaConvergentParameters) (p : Nat.Primes) (N : ℕ) : ℝ :=
  (classLaw theta.toAbelianZetaParameters
      {sourceHorizontalAbelianElementaryClass p N}).toReal /
    ((classLaw theta.toAbelianZetaParameters
        {sourceHorizontalAbelianElementaryClass p N}).toReal +
      (classLaw theta.toAbelianZetaParameters
        {sourceHorizontalAbelianCyclicClass p N}).toReal)

/-- Total probability mass of the canonical two-class aperture. -/
def sourceHorizontalAbelianTwoClassAdmission
    (theta : AbelianZetaConvergentParameters) (p : Nat.Primes) (N : ℕ) : ℝ :=
  (classLaw theta.toAbelianZetaParameters
      {sourceHorizontalAbelianElementaryClass p N}).toReal +
    (classLaw theta.toAbelianZetaParameters
      {sourceHorizontalAbelianCyclicClass p N}).toReal

private theorem sourceHorizontalAbelianForwardConditional_formula
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    sourceHorizontalAbelianTwoClassConditional
        (sourceHorizontalAbelianForwardParameters a ha0 ha1) p N =
      (p : ℝ) ^ (N * a) / ((p : ℝ) + (p : ℝ) ^ (N * a)) := by
  unfold sourceHorizontalAbelianTwoClassConditional
  rw [sourceHorizontalAbelianClassAtomMass, sourceHorizontalAbelianClassAtomMass,
    sourceHorizontalAbelianForwardWeight_elementary,
    sourceHorizontalAbelianForwardWeight_cyclic p N hN]
  have hc : 0 <
      ((sourceHorizontalAbelianForwardParameters a ha0 ha1).ennNormalizer).toReal :=
    ENNReal.toReal_pos
      (AbelianZetaConvergentParameters.ennNormalizer_ne_zero _)
      (ennNormalizer_ne_top _)
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hx : 0 < (p : ℝ) ^ ((a - 2) * (N + 1)) := Real.rpow_pos_of_pos hp _
  have hy : 0 < (p : ℝ) ^ (-2 * N - 1 + a) := Real.rpow_pos_of_pos hp _
  have hu : 0 < (p : ℝ) ^ (N * a) := Real.rpow_pos_of_pos hp _
  have hfactor :
      (p : ℝ) ^ ((a - 2) * (N + 1)) =
        (p : ℝ) ^ (-2 * N - 1 + a) * (p : ℝ) ^ (N * a - 1) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  rw [hfactor]
  field_simp
  rw [Real.rpow_sub hp, Real.rpow_one]
  field_simp
  ring

private theorem sourceHorizontalAbelianReverseConditional_formula
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N)
    {a : ℝ} (ha0 : 0 ≤ a) :
    sourceHorizontalAbelianTwoClassConditional
        (sourceHorizontalAbelianReverseParameters a ha0) p N =
      (p : ℝ) ^ (-(N * a)) / ((p : ℝ) + (p : ℝ) ^ (-(N * a))) := by
  unfold sourceHorizontalAbelianTwoClassConditional
  rw [sourceHorizontalAbelianClassAtomMass, sourceHorizontalAbelianClassAtomMass,
    sourceHorizontalAbelianReverseWeight_elementary,
    sourceHorizontalAbelianReverseWeight_cyclic p N hN]
  have hc : 0 <
      ((sourceHorizontalAbelianReverseParameters a ha0).ennNormalizer).toReal :=
    ENNReal.toReal_pos
      (AbelianZetaConvergentParameters.ennNormalizer_ne_zero _)
      (ennNormalizer_ne_top _)
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hx : 0 < (p : ℝ) ^ (-(a + 2) * (N + 1)) := Real.rpow_pos_of_pos hp _
  have hy : 0 < (p : ℝ) ^ (-2 * N - 1 - a) := Real.rpow_pos_of_pos hp _
  have hu : 0 < (p : ℝ) ^ (-(N * a)) := Real.rpow_pos_of_pos hp _
  have hfactor :
      (p : ℝ) ^ (-(a + 2) * (N + 1)) =
        (p : ℝ) ^ (-2 * N - 1 - a) * (p : ℝ) ^ (-(N * a) - 1) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  rw [hfactor]
  field_simp
  rw [Real.rpow_sub hp, Real.rpow_one]
  field_simp
  ring

/-- **Exact reflected adaptive realization.**  Two fixed class laws and one canonical pair of
prime-primary classes realize both adaptive orientations, with prime label unchanged. -/
theorem sourceHorizontalAbelianTwoClassConditionals_eq_adaptivePair
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    sourceHorizontalAbelianTwoClassConditional
          (sourceHorizontalAbelianForwardParameters a ha0 ha1) p N =
        (p : ℝ) ^ (N * a) / ((p : ℝ) + (p : ℝ) ^ (N * a)) ∧
      sourceHorizontalAbelianTwoClassConditional
          (sourceHorizontalAbelianReverseParameters a ha0) p N =
        (p : ℝ) ^ (-(N * a)) / ((p : ℝ) + (p : ℝ) ^ (-(N * a))) := by
  exact ⟨sourceHorizontalAbelianForwardConditional_formula p N hN ha0 ha1,
    sourceHorizontalAbelianReverseConditional_formula p N hN ha0⟩

/-! ## Exponential aperture evacuation -/

theorem sourceHorizontalAbelianForwardAdmission_eq
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    sourceHorizontalAbelianTwoClassAdmission
        (sourceHorizontalAbelianForwardParameters a ha0 ha1) p N =
      ((sourceHorizontalAbelianForwardParameters a ha0 ha1).ennNormalizer).toReal *
        ((p : ℝ) ^ ((a - 2) * (N + 1)) +
          (p : ℝ) ^ (-2 * N - 1 + a)) := by
  unfold sourceHorizontalAbelianTwoClassAdmission
  rw [sourceHorizontalAbelianClassAtomMass, sourceHorizontalAbelianClassAtomMass,
    sourceHorizontalAbelianForwardWeight_elementary,
    sourceHorizontalAbelianForwardWeight_cyclic p N hN]
  ring

theorem sourceHorizontalAbelianReverseAdmission_eq
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N)
    {a : ℝ} (ha0 : 0 ≤ a) :
    sourceHorizontalAbelianTwoClassAdmission
        (sourceHorizontalAbelianReverseParameters a ha0) p N =
      ((sourceHorizontalAbelianReverseParameters a ha0).ennNormalizer).toReal *
        ((p : ℝ) ^ (-(a + 2) * (N + 1)) +
          (p : ℝ) ^ (-2 * N - 1 - a)) := by
  unfold sourceHorizontalAbelianTwoClassAdmission
  rw [sourceHorizontalAbelianClassAtomMass, sourceHorizontalAbelianClassAtomMass,
    sourceHorizontalAbelianReverseWeight_elementary,
    sourceHorizontalAbelianReverseWeight_cyclic p N hN]
  ring

theorem sourceHorizontalAbelianForwardUnnormalizedAdmission_le
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N)
    {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a < 1) :
    (p : ℝ) ^ ((a - 2) * (N + 1)) + (p : ℝ) ^ (-2 * N - 1 + a) ≤
      2 * (p : ℝ) ^ (-(N + 1 : ℝ)) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  have hAexp : (a - 2) * ((N : ℝ) + 1) ≤ -((N : ℝ) + 1) := by
    nlinarith
  have hBexp : -2 * (N : ℝ) - 1 + a ≤ -((N : ℝ) + 1) := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hA := Real.rpow_le_rpow_of_exponent_le hp hAexp
  have hB := Real.rpow_le_rpow_of_exponent_le hp hBexp
  linarith

theorem sourceHorizontalAbelianReverseUnnormalizedAdmission_le
    (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N) {a : ℝ} (ha0 : 0 ≤ a) :
    (p : ℝ) ^ (-(a + 2) * (N + 1)) + (p : ℝ) ^ (-2 * N - 1 - a) ≤
      2 * (p : ℝ) ^ (-(N + 1 : ℝ)) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  have hAexp : -(a + 2) * ((N : ℝ) + 1) ≤ -((N : ℝ) + 1) := by
    nlinarith
  have hBexp : -2 * (N : ℝ) - 1 - a ≤ -((N : ℝ) + 1) := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hA := Real.rpow_le_rpow_of_exponent_le hp hAexp
  have hB := Real.rpow_le_rpow_of_exponent_le hp hBexp
  linarith

private theorem sourceHorizontal_rpow_neg_nat_tendsto_zero (p : Nat.Primes) :
    Tendsto (fun N : ℕ => (p : ℝ) ^ (-(N + 1 : ℝ))) atTop (nhds 0) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hinv0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp.le
  have hinv1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp).2 hp1
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hinv0 hinv1
  convert hpow.mul_const (p : ℝ)⁻¹ using 1
  · funext N
    rw [show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hp.le, Real.rpow_natCast, pow_succ, mul_inv, ← inv_pow]
  · simp

/-- The forward actual class-law aperture vanishes exponentially. -/
theorem tendsto_sourceHorizontalAbelianForwardAdmission_zero
    (p : Nat.Primes) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ =>
      sourceHorizontalAbelianTwoClassAdmission
        (sourceHorizontalAbelianForwardParameters a ha0 ha1) p (N + 1))
      atTop (nhds 0) := by
  let c := ((sourceHorizontalAbelianForwardParameters a ha0 ha1).ennNormalizer).toReal
  have hbase := sourceHorizontal_rpow_neg_nat_tendsto_zero p
  have hshift : Tendsto
      (fun N : ℕ => (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1)))
      atTop (nhds 0) := by
    convert hbase.comp (tendsto_add_atTop_nat 1) using 1
    funext N
    dsimp only [Function.comp_apply]
  have hupper : Tendsto
      (fun N : ℕ => c * (2 * (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1))))
      atTop (nhds 0) := by
    convert hshift.const_mul (2 * c) using 1 <;> ring_nf
  have hnonneg : ∀ N : ℕ, 0 ≤
      sourceHorizontalAbelianTwoClassAdmission
        (sourceHorizontalAbelianForwardParameters a ha0 ha1) p (N + 1) := by
    intro N
    unfold sourceHorizontalAbelianTwoClassAdmission
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hle : ∀ N : ℕ,
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianForwardParameters a ha0 ha1) p (N + 1) ≤
        c * (2 * (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1))) := by
    intro N
    rw [sourceHorizontalAbelianForwardAdmission_eq p (N + 1) (by omega) ha0 ha1]
    change c * _ ≤ c * _
    exact mul_le_mul_of_nonneg_left
      (sourceHorizontalAbelianForwardUnnormalizedAdmission_le
        p (N + 1) (by omega) ha0 ha1)
      ENNReal.toReal_nonneg
  exact squeeze_zero hnonneg hle hupper

/-- The reflected actual class-law aperture vanishes exponentially as well. -/
theorem tendsto_sourceHorizontalAbelianReverseAdmission_zero
    (p : Nat.Primes) {a : ℝ} (ha0 : 0 ≤ a) :
    Tendsto (fun N : ℕ =>
      sourceHorizontalAbelianTwoClassAdmission
        (sourceHorizontalAbelianReverseParameters a ha0) p (N + 1))
      atTop (nhds 0) := by
  let c := ((sourceHorizontalAbelianReverseParameters a ha0).ennNormalizer).toReal
  have hbase := sourceHorizontal_rpow_neg_nat_tendsto_zero p
  have hshift : Tendsto
      (fun N : ℕ => (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1)))
      atTop (nhds 0) := by
    convert hbase.comp (tendsto_add_atTop_nat 1) using 1
    funext N
    dsimp only [Function.comp_apply]
  have hupper : Tendsto
      (fun N : ℕ => c * (2 * (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1))))
      atTop (nhds 0) := by
    convert hshift.const_mul (2 * c) using 1 <;> ring_nf
  have hnonneg : ∀ N : ℕ, 0 ≤
      sourceHorizontalAbelianTwoClassAdmission
        (sourceHorizontalAbelianReverseParameters a ha0) p (N + 1) := by
    intro N
    unfold sourceHorizontalAbelianTwoClassAdmission
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hle : ∀ N : ℕ,
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianReverseParameters a ha0) p (N + 1) ≤
        c * (2 * (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1))) := by
    intro N
    rw [sourceHorizontalAbelianReverseAdmission_eq p (N + 1) (by omega) ha0]
    change c * _ ≤ c * _
    exact mul_le_mul_of_nonneg_left
      (sourceHorizontalAbelianReverseUnnormalizedAdmission_le
        p (N + 1) (by omega) ha0)
      ENNReal.toReal_nonneg
  exact squeeze_zero hnonneg hle hupper

/-! ## Sharp statistic classification -/

/-- The two reflected log-odds equations uniquely force the differences of order and socle
exponents.  This is the algebraic core of two-class aperture optimality. -/
theorem sourceHorizontalAbelianTwoClassStatistics_forced
    {a : ℝ} {N oA sA oB sB : ℕ} (ha : 0 < a)
    (hforward :
      -((oA : ℝ) - oB) - (1 - a) * ((sA : ℝ) - sB) = (N : ℝ) * a - 1)
    (hreverse :
      -((oA : ℝ) - oB) - (1 + a) * ((sA : ℝ) - sB) = -(N : ℝ) * a - 1) :
    sA = sB + N ∧ oB + 1 = oA + N := by
  have hsreal : (sA : ℝ) = (sB : ℝ) + N := by
    nlinarith
  have horeal : (oB : ℝ) + 1 = (oA : ℝ) + N := by
    nlinarith
  constructor
  · exact_mod_cast hsreal
  · exact_mod_cast horeal

/-- **Two-class statistic minimality.**  For prime-primary classes (`s <= o`, with zero socle
exponent only for the trivial class), exact reflected adaptive odds force the canonical lower
bounds. -/
theorem sourceHorizontalAbelianTwoClassStatistics_minimal
    {a : ℝ} {N oA sA oB sB : ℕ} (ha : 0 < a) (hN : 1 ≤ N)
    (hsAoA : sA ≤ oA) (_hsBoB : sB ≤ oB) (hBtrivial : sB = 0 ↔ oB = 0)
    (hforward :
      -((oA : ℝ) - oB) - (1 - a) * ((sA : ℝ) - sB) = (N : ℝ) * a - 1)
    (hreverse :
      -((oA : ℝ) - oB) - (1 + a) * ((sA : ℝ) - sB) = -(N : ℝ) * a - 1) :
    1 ≤ sB ∧ N + 1 ≤ sA ∧ N + 1 ≤ oA ∧ 2 * N ≤ oB := by
  obtain ⟨hs, ho⟩ :=
    sourceHorizontalAbelianTwoClassStatistics_forced ha hforward hreverse
  have hsB : 1 ≤ sB := by
    by_contra h
    have hsB0 : sB = 0 := by omega
    have hoB0 : oB = 0 := hBtrivial.mp hsB0
    omega
  omega

/-! ## Multiplicity-resolved Xi specialization -/

theorem sourceHorizontalXiCenteredRate_abs_lt_one (q : XiZeroCopy) :
    |primeDepthBVWoldXiCenteredRate q.1| < 1 := by
  obtain ⟨h0, h1⟩ :=
    xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)
  rw [primeDepthBVWoldXiCenteredRate, abs_lt]
  constructor <;> linarith

/-- Every Xi divisor copy has an exact two-class reflected adaptive realization.  The copy is an
argument, so analytic multiplicity is retained rather than quotiented to support. -/
theorem sourceHorizontalXiAbelianTwoClassConditionals_eq_adaptivePair
    (q : XiZeroCopy) (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N) :
    let a := |primeDepthBVWoldXiCenteredRate q.1|
    sourceHorizontalAbelianTwoClassConditional
          (sourceHorizontalAbelianForwardParameters a (abs_nonneg _) 
            (sourceHorizontalXiCenteredRate_abs_lt_one q)) p N =
        (p : ℝ) ^ (N * a) / ((p : ℝ) + (p : ℝ) ^ (N * a)) ∧
      sourceHorizontalAbelianTwoClassConditional
          (sourceHorizontalAbelianReverseParameters a (abs_nonneg _)) p N =
        (p : ℝ) ^ (-(N * a)) / ((p : ℝ) + (p : ℝ) ^ (-(N * a))) := by
  dsimp only
  exact sourceHorizontalAbelianTwoClassConditionals_eq_adaptivePair p N hN
    (abs_nonneg _) (sourceHorizontalXiCenteredRate_abs_lt_one q)

end

end RHTower
