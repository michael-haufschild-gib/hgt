import GaloisForLFunctions.RHTower.CCMPrimePoleUniversalPolynomialBoundary
import GaloisForLFunctions.RHTower.GelfondSchneider
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Prime-complete transverse Frostman profile for CCM local factors

For the Connes--Consani prime-local Frostman shift at target scale `q`, this
module evaluates the normalized model-kernel defect along the distinguished
pole orbit of a source prime `p`.  The defect is an explicit Poisson profile.

For distinct primes the logarithmic clock ratio is irrational, so the marked
orbit is dense.  Its lower and upper envelopes are therefore sharp, and the
lower envelope recovers `q` exactly.  The capstone theorem contrasts that
recovery with the unmarked all-prime polynomial Calkin character, which takes
the same value `1` on every prime generator.
-/

open Set Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower

def ccmFrostmanTransverseValue (q θ : ℝ) : ℂ :=
  (Real.sqrt q : ℂ) * (1 - Complex.exp ((θ : ℂ) * Complex.I)) /
    ((q : ℂ) - Complex.exp ((θ : ℂ) * Complex.I))

def ccmFrostmanTransverseDefect (q θ : ℝ) : ℝ :=
  1 - ‖ccmFrostmanTransverseValue q θ‖ ^ 2

def ccmFrostmanPoissonProfile (q θ : ℝ) : ℝ :=
  (q - 1) ^ 2 / (q ^ 2 - 2 * q * Real.cos θ + 1)

lemma ccmFrostman_denominator_pos {q θ : ℝ} (hq : 1 < q) :
    0 < q ^ 2 - 2 * q * Real.cos θ + 1 := by
  have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
  nlinarith [sq_nonneg (q - 1)]

lemma ccmFrostman_complex_denominator_ne {q θ : ℝ} (hq : 1 < q) :
    ((q : ℂ) - Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
  intro h
  have heq : (q : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) := sub_eq_zero.mp h
  have hn := congrArg norm heq
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq.le
  simp [Complex.norm_real, abs_of_nonneg hq0] at hn
  linarith

lemma normSq_one_sub_exp_I_mul (θ : ℝ) :
    Complex.normSq (1 - Complex.exp ((θ : ℂ) * Complex.I)) = 2 - 2 * Real.cos θ := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.sub_im, Complex.one_im, Complex.add_im, mul_one,
    add_zero]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma normSq_real_sub_exp_I_mul (q θ : ℝ) :
    Complex.normSq ((q : ℂ) - Complex.exp ((θ : ℂ) * Complex.I)) =
      q ^ 2 - 2 * q * Real.cos θ + 1 := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.sub_im, Complex.add_im, mul_one, add_zero]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma norm_sq_ccmFrostmanTransverseValue {q θ : ℝ} (hq : 1 < q) :
    ‖ccmFrostmanTransverseValue q θ‖ ^ 2 =
      q * (2 - 2 * Real.cos θ) /
        (q ^ 2 - 2 * q * Real.cos θ + 1) := by
  rw [Complex.sq_norm, ccmFrostmanTransverseValue, map_div₀, map_mul]
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by linarith : 0 ≤ q)]
  rw [normSq_one_sub_exp_I_mul, normSq_real_sub_exp_I_mul]

/-- Exact normalized model-kernel diagonal of the prime-local Frostman shift. -/
theorem ccmFrostmanTransverseDefect_eq_poisson {q θ : ℝ} (hq : 1 < q) :
    ccmFrostmanTransverseDefect q θ = ccmFrostmanPoissonProfile q θ := by
  rw [ccmFrostmanTransverseDefect, ccmFrostmanPoissonProfile,
    norm_sq_ccmFrostmanTransverseValue hq]
  have hden := (ccmFrostman_denominator_pos hq :
    0 < q ^ 2 - 2 * q * Real.cos θ + 1).ne'
  rw [one_sub_div hden]
  congr 1
  ring

end RHTower

namespace RHTower

def ccmFrostmanProfileFloor (q : ℝ) : ℝ := (q - 1) ^ 2 / (q + 1) ^ 2

lemma ccmFrostmanProfileFloor_le {q θ : ℝ} (hq : 1 < q) :
    ccmFrostmanProfileFloor q ≤ ccmFrostmanPoissonProfile q θ := by
  have hD : 0 < q ^ 2 - 2 * q * Real.cos θ + 1 := ccmFrostman_denominator_pos hq
  have hQ : 0 < (q + 1) ^ 2 := sq_pos_of_pos (by linarith)
  rw [ccmFrostmanProfileFloor, ccmFrostmanPoissonProfile]
  rw [div_le_div_iff₀ hQ hD]
  have hc := Real.neg_one_le_cos θ
  have hnum : 0 ≤ (q - 1) ^ 2 := sq_nonneg _
  have hdenle : q ^ 2 - 2 * q * Real.cos θ + 1 ≤ (q + 1) ^ 2 := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hdenle hnum

lemma ccmFrostmanPoissonProfile_le_one {q θ : ℝ} (hq : 1 < q) :
    ccmFrostmanPoissonProfile q θ ≤ 1 := by
  have hD : 0 < q ^ 2 - 2 * q * Real.cos θ + 1 := ccmFrostman_denominator_pos hq
  rw [ccmFrostmanPoissonProfile, div_le_one hD]
  have hc := Real.cos_le_one θ
  nlinarith

@[simp] theorem ccmFrostmanPoissonProfile_zero {q : ℝ} (hq : 1 < q) :
    ccmFrostmanPoissonProfile q 0 = 1 := by
  rw [ccmFrostmanPoissonProfile, Real.cos_zero]
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq.ne'
  have hden : q ^ 2 - 2 * q * 1 + 1 = (q - 1) ^ 2 := by ring
  rw [hden, div_self (pow_ne_zero 2 hq1)]

@[simp] theorem ccmFrostmanPoissonProfile_pi {q : ℝ} (_hq : 1 < q) :
    ccmFrostmanPoissonProfile q Real.pi = ccmFrostmanProfileFloor q := by
  rw [ccmFrostmanPoissonProfile, ccmFrostmanProfileFloor, Real.cos_pi]
  ring_nf

/-- Distinct prime clocks have irrational conversion ratio. -/
theorem irrational_log_div_log_of_distinct_primes {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational (Real.log q / Real.log p) := by
  exact GaloisForLFunctions.RHTower.irrational_log_ratio hp hq hpq

end RHTower

namespace RHTower

def ccmFrostmanAngleProfile (q : ℝ) (θ : Real.Angle) : ℝ :=
  (q - 1) ^ 2 / (q ^ 2 - 2 * q * θ.cos + 1)

lemma continuous_ccmFrostmanAngleProfile {q : ℝ} (hq : 1 < q) :
    Continuous (ccmFrostmanAngleProfile q) := by
  apply Continuous.div continuous_const
  · exact (continuous_const.sub
      (continuous_const.mul Real.Angle.continuous_cos)).add continuous_const
  · intro θ
    have hc : -1 ≤ θ.cos := by
      induction θ using Real.Angle.induction_on with
      | _ θ => simpa using Real.neg_one_le_cos θ
    have hc' : θ.cos ≤ 1 := by
      induction θ using Real.Angle.induction_on with
      | _ θ => simpa using Real.cos_le_one θ
    nlinarith [sq_pos_of_pos (sub_pos.mpr hq)]

lemma ccmFrostmanAngleProfile_floor_le {q : ℝ} (hq : 1 < q) (θ : Real.Angle) :
    ccmFrostmanProfileFloor q ≤ ccmFrostmanAngleProfile q θ := by
  induction θ using Real.Angle.induction_on with
  | _ θ =>
      simpa [ccmFrostmanAngleProfile, ccmFrostmanPoissonProfile] using
        ccmFrostmanProfileFloor_le (q := q) (θ := θ) hq

lemma ccmFrostmanAngleProfile_le_one {q : ℝ} (hq : 1 < q) (θ : Real.Angle) :
    ccmFrostmanAngleProfile q θ ≤ 1 := by
  induction θ using Real.Angle.induction_on with
  | _ θ =>
      simpa [ccmFrostmanAngleProfile, ccmFrostmanPoissonProfile] using
        ccmFrostmanPoissonProfile_le_one (q := q) (θ := θ) hq

@[simp] theorem ccmFrostmanAngleProfile_zero {q : ℝ} (hq : 1 < q) :
    ccmFrostmanAngleProfile q 0 = 1 := by
  simpa [ccmFrostmanAngleProfile, ccmFrostmanPoissonProfile] using
    ccmFrostmanPoissonProfile_zero (q := q) hq

@[simp] theorem ccmFrostmanAngleProfile_pi {q : ℝ} (hq : 1 < q) :
    ccmFrostmanAngleProfile q (Real.pi : Real.Angle) = ccmFrostmanProfileFloor q := by
  simpa [ccmFrostmanAngleProfile, ccmFrostmanPoissonProfile] using
    ccmFrostmanPoissonProfile_pi (q := q) hq

def ccmPrimePoleOrbitAngle (p q : ℕ) (n : ℤ) : Real.Angle :=
  n • ((2 * Real.pi * (Real.log q / Real.log p) : ℝ) : Real.Angle)

/-- The transverse pole orbit of two distinct primes is dense in the angle circle. -/
theorem denseRange_ccmPrimePoleOrbitAngle {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    DenseRange (ccmPrimePoleOrbitAngle p q) := by
  change DenseRange (fun n : ℤ =>
    n • ((2 * Real.pi * (Real.log q / Real.log p) : ℝ) : Real.Angle))
  apply AddCircle.denseRange_zsmul_coe_iff.mpr
  have hirr := irrational_log_div_log_of_distinct_primes hp hq hpq
  convert hirr using 1
  field_simp [Real.pi_ne_zero]

/-- The prime-marked Frostman profile on the distinguished source pole orbit. -/
def ccmPrimeTransverseFrostmanProfile (p q : ℕ) (n : ℤ) : ℝ :=
  ccmFrostmanAngleProfile q (ccmPrimePoleOrbitAngle p q n)

theorem ccmPrimeTransverseFrostmanProfile_floor_le {p q : ℕ}
    (hq : q.Prime) (n : ℤ) :
    ccmFrostmanProfileFloor q ≤ ccmPrimeTransverseFrostmanProfile p q n := by
  exact ccmFrostmanAngleProfile_floor_le (by exact_mod_cast hq.one_lt)
    (ccmPrimePoleOrbitAngle p q n)

theorem ccmPrimeTransverseFrostmanProfile_le_one {p q : ℕ}
    (hq : q.Prime) (n : ℤ) :
    ccmPrimeTransverseFrostmanProfile p q n ≤ 1 := by
  exact ccmFrostmanAngleProfile_le_one (by exact_mod_cast hq.one_lt)
    (ccmPrimePoleOrbitAngle p q n)

/-- Sharpness of the lower envelope along every distinct-prime pole orbit. -/
theorem exists_ccmPrimeTransverseFrostmanProfile_lt_floor_add
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℤ, ccmPrimeTransverseFrostmanProfile p q n <
      ccmFrostmanProfileFloor q + ε := by
  let U : Set Real.Angle :=
    {θ | ccmFrostmanAngleProfile q θ < ccmFrostmanProfileFloor q + ε}
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hopen : IsOpen U :=
    isOpen_Iio.preimage (continuous_ccmFrostmanAngleProfile hqR)
  have hmem : (Real.pi : Real.Angle) ∈ U := by
    change ccmFrostmanAngleProfile q (Real.pi : Real.Angle) <
      ccmFrostmanProfileFloor q + ε
    rw [show ccmFrostmanAngleProfile q (Real.pi : Real.Angle) =
      ccmFrostmanProfileFloor q from ccmFrostmanAngleProfile_pi hqR]
    exact lt_add_of_pos_right _ hε
  obtain ⟨n, hn⟩ := (denseRange_ccmPrimePoleOrbitAngle hp hq hpq).exists_mem_open
    hopen ⟨_, hmem⟩
  exact ⟨n, hn⟩

/-- Sharpness of the upper envelope along every distinct-prime pole orbit. -/
theorem exists_one_sub_lt_ccmPrimeTransverseFrostmanProfile
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℤ, 1 - ε < ccmPrimeTransverseFrostmanProfile p q n := by
  let U : Set Real.Angle :=
    {θ | 1 - ε < ccmFrostmanAngleProfile q θ}
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hopen : IsOpen U :=
    isOpen_Ioi.preimage (continuous_ccmFrostmanAngleProfile hqR)
  have hmem : (0 : Real.Angle) ∈ U := by
    change 1 - ε < ccmFrostmanAngleProfile q (0 : Real.Angle)
    rw [show ccmFrostmanAngleProfile q (0 : Real.Angle) = 1 from
      ccmFrostmanAngleProfile_zero hqR]
    linarith
  obtain ⟨n, hn⟩ := (denseRange_ccmPrimePoleOrbitAngle hp hq hpq).exists_mem_open
    hopen ⟨_, hmem⟩
  exact ⟨n, hn⟩

end RHTower

namespace RHTower

/-- Cosine converts an integral angle multiple back to real multiplication. -/
lemma ccmAngle_cos_zsmul (n : ℤ) (x : ℝ) :
    Real.Angle.cos (n • (x : Real.Angle)) = Real.cos ((n : ℝ) * x) := by
  calc
    Real.Angle.cos (n • (x : Real.Angle)) =
        Real.Angle.cos ((n • x : ℝ) : Real.Angle) := by
          rw [Real.Angle.coe_zsmul]
    _ = Real.cos (n • x : ℝ) := Real.Angle.cos_coe _
    _ = Real.cos ((n : ℝ) * x) := by rw [zsmul_eq_mul]

/-- The angular definition is exactly the real Poisson profile on the pole orbit. -/
theorem ccmPrimeTransverseFrostmanProfile_eq_poisson (p q : ℕ) (n : ℤ) :
    ccmPrimeTransverseFrostmanProfile p q n =
      ccmFrostmanPoissonProfile q
        (2 * Real.pi * (n : ℝ) * (Real.log q / Real.log p)) := by
  simp [ccmPrimeTransverseFrostmanProfile, ccmPrimePoleOrbitAngle,
    ccmFrostmanAngleProfile, ccmFrostmanPoissonProfile, ccmAngle_cos_zsmul]
  congr 2
  ring

/-- The prime-dependent lower envelope has an elementary square root. -/
theorem sqrt_ccmFrostmanProfileFloor {q : ℝ} (hq : 1 < q) :
    Real.sqrt (ccmFrostmanProfileFloor q) = (q - 1) / (q + 1) := by
  have hq1 : 0 < q - 1 := sub_pos.mpr hq
  have hqp : 0 < q + 1 := by linarith
  rw [ccmFrostmanProfileFloor]
  have hsq : (q - 1) ^ 2 / (q + 1) ^ 2 = ((q - 1) / (q + 1)) ^ 2 := by
    field_simp
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hq1 hqp)]

/-- Exact target-scale recovery from the sharp lower envelope. -/
theorem ccmFrostmanProfileFloor_recovers_scale {q : ℝ} (hq : 1 < q) :
    (1 + Real.sqrt (ccmFrostmanProfileFloor q)) /
        (1 - Real.sqrt (ccmFrostmanProfileFloor q)) = q := by
  rw [sqrt_ccmFrostmanProfileFloor hq]
  have hqp : q + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The lower envelope is the greatest lower bound of every distinct-prime profile. -/
theorem isGLB_range_ccmPrimeTransverseFrostmanProfile
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsGLB (Set.range (ccmPrimeTransverseFrostmanProfile p q))
      (ccmFrostmanProfileFloor q) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    exact ccmPrimeTransverseFrostmanProfile_floor_le hq n
  · intro b hb
    by_contra hnot
    have hlt : ccmFrostmanProfileFloor q < b := lt_of_not_ge hnot
    have hε : 0 < (b - ccmFrostmanProfileFloor q) / 2 := by linarith
    obtain ⟨n, hn⟩ :=
      exists_ccmPrimeTransverseFrostmanProfile_lt_floor_add hp hq hpq hε
    have hbn : b ≤ ccmPrimeTransverseFrostmanProfile p q n := hb ⟨n, rfl⟩
    linarith

/-- The upper envelope is the least upper bound of every distinct-prime profile. -/
theorem isLUB_range_ccmPrimeTransverseFrostmanProfile
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsLUB (Set.range (ccmPrimeTransverseFrostmanProfile p q)) 1 := by
  constructor
  · rintro _ ⟨n, rfl⟩
    exact ccmPrimeTransverseFrostmanProfile_le_one hq n
  · intro b hb
    by_contra hnot
    have hlt : b < 1 := lt_of_not_ge hnot
    have hε : 0 < (1 - b) / 2 := by linarith
    obtain ⟨n, hn⟩ :=
      exists_one_sub_lt_ccmPrimeTransverseFrostmanProfile hp hq hpq hε
    have hnb : ccmPrimeTransverseFrostmanProfile p q n ≤ b := hb ⟨n, rfl⟩
    linarith

/-- **Marked recovery versus unmarked collapse.**  The all-prime polynomial
Calkin character identifies every prime generator with the same scalar `1`,
while the cross-prime pole-orbit profile has a sharp lower envelope that
recovers the target prime exactly. -/
theorem ccmAllPrime_unmarked_character_marked_profile_recovery
    (p q : CCMPrimeIndex) (hpq : p ≠ q) :
    ccmAllPrimePolePolynomialCalkinCharacter
        (Ideal.Quotient.mk
          (ccmPrimePoleFamilyPolynomialCompactIdeal
            ccmAllPrimeLogScale ccmAllPrimeLogScale_pos)
          (FreeAlgebra.ι ℂ q)) = 1 ∧
      IsGLB (Set.range
        (ccmPrimeTransverseFrostmanProfile (p : ℕ) (q : ℕ)))
        (ccmFrostmanProfileFloor (q : ℕ)) ∧
      IsLUB (Set.range
        (ccmPrimeTransverseFrostmanProfile (p : ℕ) (q : ℕ))) 1 ∧
      (1 + Real.sqrt (ccmFrostmanProfileFloor (q : ℕ))) /
          (1 - Real.sqrt (ccmFrostmanProfileFloor (q : ℕ))) = (q : ℕ) := by
  have hpqN : (p : ℕ) ≠ (q : ℕ) := by
    intro h
    exact hpq (Subtype.ext h)
  refine ⟨ccmAllPrimePolePolynomialCalkinCharacter_generator q,
    isGLB_range_ccmPrimeTransverseFrostmanProfile p.property q.property hpqN,
    isLUB_range_ccmPrimeTransverseFrostmanProfile p.property q.property hpqN, ?_⟩
  exact ccmFrostmanProfileFloor_recovers_scale (by exact_mod_cast q.property.one_lt)

end RHTower
