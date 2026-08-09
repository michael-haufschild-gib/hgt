import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# q-Pochhammer analytic infrastructure

Mathlib currently has no general q-Pochhammer function.  This module supplies the source-level
infrastructure needed by the Euler q-Gamma process: finite and infinite products, absolute defect
summability, multipliability, the exact one-step shift, and nonvanishing in the bidisc.

Analytic domain conditions are carried by structures, so exported theorems are closed and have no
external convergence hypotheses.
-/

open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A complex nome strictly inside the open unit disc. -/
structure EulerNome where
  val : ℂ
  norm_lt_one : ‖val‖ < 1

namespace EulerNome

instance : Coe EulerNome ℂ := ⟨EulerNome.val⟩

@[simp]
theorem coe_mk (q : ℂ) (hq : ‖q‖ < 1) : ((⟨q, hq⟩ : EulerNome) : ℂ) = q :=
  rfl

end EulerNome

/-- A q-Pochhammer parameter and nome both lying in the open unit disc. -/
structure EulerPochhammerDatum where
  a : ℂ
  q : EulerNome
  a_norm_lt_one : ‖a‖ < 1

/-- Finite q-Pochhammer symbol `(a;q)_n`. -/
def qPochhammer (a : ℂ) (q : EulerNome) (n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, (1 - a * (q : ℂ) ^ j)

/-- Infinite q-Pochhammer symbol `(a;q)_∞`, using Mathlib's topological product. -/
def qPochhammerInf (a : ℂ) (q : EulerNome) : ℂ :=
  ∏' j : ℕ, (1 - a * (q : ℂ) ^ j)

/-- The q-Pochhammer multiplicative defect is absolutely summable for every open-disc nome. -/
theorem qPochhammer_summable_defect (a : ℂ) (q : EulerNome) :
    Summable (fun j : ℕ ↦ -(a * (q : ℂ) ^ j)) := by
  simpa only [neg_mul] using
    Summable.mul_left (-a) (summable_geometric_of_norm_lt_one q.norm_lt_one)

/-- Infinite q-Pochhammer products are multipliable throughout the nome disc. -/
theorem qPochhammer_multipliable (a : ℂ) (q : EulerNome) :
    Multipliable (fun j : ℕ ↦ 1 - a * (q : ℂ) ^ j) := by
  simpa only [sub_eq_add_neg] using
    Complex.multipliable_one_add_of_summable (qPochhammer_summable_defect a q)

/-- Finite successor equation `(a;q)_(n+1) = (a;q)_n (1-aq^n)`. -/
theorem qPochhammer_succ (a : ℂ) (q : EulerNome) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * (q : ℂ) ^ n) := by
  simp [qPochhammer, Finset.prod_range_succ]

set_option maxHeartbeats 800000 in
/-- **Infinite q-Pochhammer shift.** `(a;q)_∞ = (1-a)(aq;q)_∞`. -/
theorem qPochhammerInf_shift (a : ℂ) (q : EulerNome) :
    qPochhammerInf a q = (1 - a) * qPochhammerInf (a * (q : ℂ)) q := by
  change (∏' j : ℕ, (1 - a * (q : ℂ) ^ j)) =
    (1 - a) * ∏' j : ℕ, (1 - (a * (q : ℂ)) * (q : ℂ) ^ j)
  have htail : Multipliable
      (fun j : ℕ ↦ 1 - a * (q : ℂ) ^ (j + 1)) := by
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      qPochhammer_multipliable (a * (q : ℂ)) q
  rw [tprod_eq_zero_mul' htail]
  simp only [pow_zero, mul_one]
  congr 1
  apply tprod_congr
  intro j
  simp only [pow_succ, mul_assoc, mul_comm]

/-- Every factor of a bidisc q-Pochhammer datum is nonzero. -/
theorem EulerPochhammerDatum.factor_ne_zero (d : EulerPochhammerDatum) (n : ℕ) :
    1 - d.a * (d.q : ℂ) ^ n ≠ 0 := by
  intro hzero
  have hone : ‖d.a * (d.q : ℂ) ^ n‖ = 1 := by
    rw [(sub_eq_zero.mp hzero).symm]
    norm_num
  have hlt : ‖d.a * (d.q : ℂ) ^ n‖ < 1 := by
    calc
      ‖d.a * (d.q : ℂ) ^ n‖ = ‖d.a‖ * ‖(d.q : ℂ)‖ ^ n := by
        rw [norm_mul, norm_pow]
      _ ≤ ‖d.a‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) d.q.norm_lt_one.le
      _ = ‖d.a‖ := mul_one _
      _ < 1 := d.a_norm_lt_one
  linarith

/-- Infinite q-Pochhammer products have no zeros on the open bidisc. -/
theorem qPochhammerInf_ne_zero (d : EulerPochhammerDatum) :
    qPochhammerInf d.a d.q ≠ 0 := by
  change (∏' j : ℕ, (1 + -(d.a * (d.q : ℂ) ^ j))) ≠ 0
  apply tprod_one_add_ne_zero_of_summable
  · intro n
    simpa only [sub_eq_add_neg] using d.factor_ne_zero n
  · simpa only [norm_neg] using (qPochhammer_summable_defect d.a d.q).norm

/-- The finite products converge to the infinite q-Pochhammer value. -/
theorem qPochhammer_tendsto (a : ℂ) (q : EulerNome) :
    Filter.Tendsto (fun n : ℕ ↦ qPochhammer a q n) Filter.atTop
      (nhds (qPochhammerInf a q)) := by
  simpa [qPochhammer, qPochhammerInf] using
    (qPochhammer_multipliable a q).tendsto_prod_tprod_nat

/-! ## Local q-Gamma core -/

/-- Positive real nome `0 < q < 1`. -/
structure RealEulerNome where
  val : ℝ
  pos : 0 < val
  lt_one : val < 1

namespace RealEulerNome

instance : Coe RealEulerNome ℝ := ⟨RealEulerNome.val⟩

/-- Forget positivity while retaining the complex open-disc nome. -/
def toEulerNome (q : RealEulerNome) : EulerNome where
  val := (q.val : ℂ)
  norm_lt_one := by
    simpa [Real.norm_eq_abs, abs_of_pos q.pos] using q.lt_one

@[simp]
theorem toEulerNome_coe (q : RealEulerNome) : ((q.toEulerNome : EulerNome) : ℂ) = q.val :=
  rfl

theorem complex_ne_zero (q : RealEulerNome) : (q.val : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr q.pos.ne'

end RealEulerNome

/-- Right-half-plane q-Gamma input. -/
structure EulerQGammaPoint where
  q : RealEulerNome
  z : ℂ
  re_pos : 0 < z.re

namespace EulerQGammaPoint

/-- Translation by one preserves the right half-plane. -/
def shift (x : EulerQGammaPoint) : EulerQGammaPoint where
  q := x.q
  z := x.z + 1
  re_pos := by simpa using add_pos_of_pos_of_nonneg x.re_pos zero_le_one

@[simp]
theorem shift_q (x : EulerQGammaPoint) : x.shift.q = x.q :=
  rfl

@[simp]
theorem shift_z (x : EulerQGammaPoint) : x.shift.z = x.z + 1 :=
  rfl

/-- Canonical input `z=1`. -/
def one (q : RealEulerNome) : EulerQGammaPoint where
  q := q
  z := 1
  re_pos := by norm_num

@[simp]
theorem one_q (q : RealEulerNome) : (one q).q = q :=
  rfl

@[simp]
theorem one_z (q : RealEulerNome) : (one q).z = 1 :=
  rfl

/-- The denominator parameter `q^z` lies in the open unit disc. -/
def denominatorDatum (x : EulerQGammaPoint) : EulerPochhammerDatum where
  a := (x.q.val : ℂ) ^ x.z
  q := x.q.toEulerNome
  a_norm_lt_one := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos x.q.pos]
    exact Real.rpow_lt_one x.q.pos.le x.q.lt_one x.re_pos

/-- The fixed numerator parameter `q` lies in the open unit disc. -/
def numeratorDatum (q : RealEulerNome) : EulerPochhammerDatum where
  a := q.val
  q := q.toEulerNome
  a_norm_lt_one := by
    simpa [Real.norm_eq_abs, abs_of_pos q.pos] using q.lt_one

end EulerQGammaPoint

/-- q-Gamma quotient before the elementary `(1-q)^(1-z)` normalization. -/
def qGammaCore (x : EulerQGammaPoint) : ℂ :=
  qPochhammerInf x.q.val x.q.toEulerNome /
    qPochhammerInf ((x.q.val : ℂ) ^ x.z) x.q.toEulerNome

/-- The local q-Gamma core is nonzero throughout its encoded domain. -/
theorem qGammaCore_ne_zero : ∀ x : EulerQGammaPoint, qGammaCore x ≠ 0 := by
  intro x
  apply div_ne_zero
  · exact qPochhammerInf_ne_zero (EulerQGammaPoint.numeratorDatum x.q)
  · exact qPochhammerInf_ne_zero x.denominatorDatum

/-- Complex exponent translation for a positive real nome. -/
theorem realEulerNome_cpow_add_one (x : EulerQGammaPoint) :
    (x.q.val : ℂ) ^ (x.z + 1) = (x.q.val : ℂ) ^ x.z * x.q.val := by
  rw [Complex.cpow_add _ _ x.q.complex_ne_zero, Complex.cpow_one]

/-- **Exact local translation law.** The unnormalized q-Gamma core acquires precisely the first
q-Pochhammer factor under translation. -/
theorem qGammaCore_shift (x : EulerQGammaPoint) :
    qGammaCore x.shift = (1 - (x.q.val : ℂ) ^ x.z) * qGammaCore x := by
  have hden :
      qPochhammerInf ((x.q.val : ℂ) ^ x.z) x.q.toEulerNome =
        (1 - (x.q.val : ℂ) ^ x.z) *
          qPochhammerInf ((x.q.val : ℂ) ^ (x.z + 1)) x.q.toEulerNome := by
    rw [realEulerNome_cpow_add_one]
    exact qPochhammerInf_shift ((x.q.val : ℂ) ^ x.z) x.q.toEulerNome
  have hden0 :
      qPochhammerInf ((x.q.val : ℂ) ^ x.z) x.q.toEulerNome ≠ 0 :=
    qPochhammerInf_ne_zero x.denominatorDatum
  have hden10 :
      qPochhammerInf ((x.q.val : ℂ) ^ (x.z + 1)) x.q.toEulerNome ≠ 0 := by
    simpa [EulerQGammaPoint.denominatorDatum, EulerQGammaPoint.shift] using
      qPochhammerInf_ne_zero x.shift.denominatorDatum
  unfold qGammaCore
  simp only [EulerQGammaPoint.shift_q, EulerQGammaPoint.shift_z]
  field_simp [hden0, hden10]
  rw [hden]
  ring

/-- Standard q-Gamma normalization on the encoded right half-plane. -/
def qGamma (x : EulerQGammaPoint) : ℂ :=
  ((1 - x.q.val : ℝ) : ℂ) ^ (1 - x.z) * qGammaCore x

/-- The positive normalization base `1-q` is nonzero. -/
theorem RealEulerNome.one_sub_complex_ne_zero (q : RealEulerNome) :
    (((1 - q.val : ℝ) : ℂ)) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr q.lt_one).ne'

/-- **Normalized q-Gamma translation law.** -/
theorem qGamma_shift (x : EulerQGammaPoint) :
    qGamma x.shift =
      ((1 - (x.q.val : ℂ) ^ x.z) / ((1 - x.q.val : ℝ) : ℂ)) * qGamma x := by
  let b : ℂ := ((1 - x.q.val : ℝ) : ℂ)
  have hb : b ≠ 0 := x.q.one_sub_complex_ne_zero
  have hpow : b ^ (1 - x.z) = b ^ (1 - (x.z + 1)) * b := by
    rw [show 1 - x.z = (1 - (x.z + 1)) + 1 by ring,
      Complex.cpow_add _ _ hb, Complex.cpow_one]
  unfold qGamma
  simp only [EulerQGammaPoint.shift_q, EulerQGammaPoint.shift_z]
  rw [qGammaCore_shift]
  change b ^ (1 - (x.z + 1)) * ((1 - (x.q.val : ℂ) ^ x.z) * qGammaCore x) =
    ((1 - (x.q.val : ℂ) ^ x.z) / b) * (b ^ (1 - x.z) * qGammaCore x)
  field_simp [hb]
  rw [hpow]
  ring

/-- q-Gamma is normalized at one. -/
theorem qGamma_one : ∀ q : RealEulerNome, qGamma (EulerQGammaPoint.one q) = 1 := by
  intro q
  unfold qGamma qGammaCore
  simp only [EulerQGammaPoint.one_q, EulerQGammaPoint.one_z, sub_self, Complex.cpow_zero,
    one_mul, Complex.cpow_one]
  exact div_self (qPochhammerInf_ne_zero (EulerQGammaPoint.numeratorDatum q))

/-- q-Gamma is also normalized at two, forced by its translation law. -/
theorem qGamma_two : ∀ q : RealEulerNome,
    qGamma (EulerQGammaPoint.one q).shift = 1 := by
  intro q
  rw [qGamma_shift, qGamma_one]
  simp only [EulerQGammaPoint.one_q, EulerQGammaPoint.one_z, Complex.cpow_one, mul_one]
  rw [show (((1 - q.val : ℝ) : ℂ)) = 1 - (q.val : ℂ) by norm_cast]
  exact div_self (by simpa using q.one_sub_complex_ne_zero)

/-! ## Positive local law and exact normalization -/

/-- Real q-factorial `(q;q)_n`. -/
def realQFactorial (q : RealEulerNome) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (1 - q.val ^ (j + 1))

/-- Real infinite q-factorial `(q;q)_∞`. -/
def realQFactorialInf (q : RealEulerNome) : ℝ :=
  ∏' j : ℕ, (1 - q.val ^ (j + 1))

/-- Every positive q-factorial factor is strictly positive. -/
theorem realQFactorial_factor_pos (q : RealEulerNome) (j : ℕ) :
    0 < 1 - q.val ^ (j + 1) := by
  exact sub_pos.mpr (pow_lt_one₀ q.pos.le q.lt_one (by omega))

/-- Finite q-factorials are strictly positive. -/
theorem realQFactorial_pos (q : RealEulerNome) (n : ℕ) :
    0 < realQFactorial q n := by
  apply Finset.prod_pos
  intro j hj
  exact realQFactorial_factor_pos q j

/-- Finite real q-factorial successor equation. -/
theorem realQFactorial_succ (q : RealEulerNome) (n : ℕ) :
    realQFactorial q (n + 1) =
      realQFactorial q n * (1 - q.val ^ (n + 1)) := by
  simp [realQFactorial, Finset.prod_range_succ]

/-- The real q-factorial defect series is summable. -/
theorem realQFactorial_summable_defect (q : RealEulerNome) :
    Summable (fun n : ℕ ↦ -(q.val ^ (n + 1))) := by
  exact ((summable_nat_add_iff 1).2
    (summable_geometric_of_lt_one q.pos.le q.lt_one)).neg

/-- Real q-factorial product is multipliable. -/
theorem realQFactorial_multipliable (q : RealEulerNome) :
    Multipliable (fun n : ℕ ↦ 1 - q.val ^ (n + 1)) := by
  simpa only [sub_eq_add_neg] using
    Real.multipliable_one_add_of_summable (realQFactorial_summable_defect q)

/-- The real infinite q-factorial is nonzero. -/
theorem realQFactorialInf_ne_zero (q : RealEulerNome) :
    realQFactorialInf q ≠ 0 := by
  change (∏' n : ℕ, (1 + -(q.val ^ (n + 1)))) ≠ 0
  apply tprod_one_add_ne_zero_of_summable
  · intro n
    simpa only [sub_eq_add_neg] using (realQFactorial_factor_pos q n).ne'
  · simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg q.pos.le _)] using
      (realQFactorial_summable_defect q).norm

/-- Finite real q-factorials converge to their infinite product. -/
theorem realQFactorial_tendsto (q : RealEulerNome) :
    Filter.Tendsto (realQFactorial q) Filter.atTop (nhds (realQFactorialInf q)) := by
  change Filter.Tendsto
    (fun n : ℕ ↦ ∏ j ∈ Finset.range n, (1 - q.val ^ (j + 1))) Filter.atTop
      (nhds (∏' j : ℕ, (1 - q.val ^ (j + 1))))
  exact (realQFactorial_multipliable q).tendsto_prod_tprod_nat

/-- Local q-geometric coefficient before multiplication by the normalizing infinite product. -/
def qGeometricCoefficient (q : RealEulerNome) (n : ℕ) : ℝ :=
  q.val ^ n / realQFactorial q n

/-- Local q-geometric coefficients are nonnegative. -/
theorem qGeometricCoefficient_nonneg (q : RealEulerNome) (n : ℕ) :
    0 ≤ qGeometricCoefficient q n := by
  exact div_nonneg (pow_nonneg q.pos.le n) (realQFactorial_pos q n).le

/-- **Finite q-binomial normalization telescope at `z=q`.** -/
theorem qGeometricCoefficient_sum_finite (q : RealEulerNome) :
    ∀ N : ℕ,
      (∑ n ∈ Finset.range (N + 1), qGeometricCoefficient q n) =
        1 / realQFactorial q N := by
  intro N
  induction N with
  | zero => simp [qGeometricCoefficient, realQFactorial]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      change 1 / realQFactorial q N + q.val ^ (N + 1) / realQFactorial q (N + 1) =
        1 / realQFactorial q (N + 1)
      have hfac : realQFactorial q N ≠ 0 := (realQFactorial_pos q N).ne'
      have hstep : 1 - q.val ^ (N + 1) ≠ 0 := (realQFactorial_factor_pos q N).ne'
      rw [realQFactorial_succ]
      field_simp [hfac, hstep]
      ring

/-- **Infinite local normalization.** -/
theorem qGeometricCoefficient_hasSum (q : RealEulerNome) :
    HasSum (qGeometricCoefficient q) (realQFactorialInf q)⁻¹ := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (qGeometricCoefficient_nonneg q)
    (realQFactorialInf q)⁻¹).2
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  have hinv := (realQFactorial_tendsto q).inv₀ (realQFactorialInf_ne_zero q)
  convert hinv using 1
  funext N
  simpa [one_div] using qGeometricCoefficient_sum_finite q N

/-- Normalized local q-Gamma weights. -/
def qGammaWeight (q : RealEulerNome) (n : ℕ) : ℝ :=
  realQFactorialInf q * qGeometricCoefficient q n

/-- Every normalized local q-Gamma weight is nonnegative. -/
theorem qGammaWeight_nonneg (q : RealEulerNome) (n : ℕ) :
    0 ≤ qGammaWeight q n := by
  unfold qGammaWeight
  have hinf : 0 ≤ realQFactorialInf q := by
    exact ge_of_tendsto' (realQFactorial_tendsto q) (fun n ↦ (realQFactorial_pos q n).le)
  exact mul_nonneg hinf (qGeometricCoefficient_nonneg q n)

/-- The normalized local weights have total mass one. -/
theorem qGammaWeight_hasSum_one (q : RealEulerNome) :
    HasSum (qGammaWeight q) 1 := by
  change HasSum
    (fun n ↦ realQFactorialInf q * qGeometricCoefficient q n) 1
  have h := (qGeometricCoefficient_hasSum q).mul_left (realQFactorialInf q)
  have hprod : realQFactorialInf q * (realQFactorialInf q)⁻¹ = 1 :=
    mul_inv_cancel₀ (realQFactorialInf_ne_zero q)
  rw [hprod] at h
  exact h

/-! ## Integer intervention transform

The full complex q-binomial transform will be built on top of this core.  The theorem below already
closes every nonnegative integral intervention exactly.  It is enough to certify the normalized
unit tilt and its whole discrete response ladder without importing an unproved special-function
identity.
-/

/-- q-geometric coefficient evaluated at the integral nome power `q^k`. -/
def qGeometricCoefficientAt (q : RealEulerNome) (k n : ℕ) : ℝ :=
  q.val ^ (k * n) / realQFactorial q n

/-- One coefficient-level q-binomial difference. -/
theorem qGeometricCoefficientAt_succ_difference (q : RealEulerNome) (k n : ℕ) :
    qGeometricCoefficientAt q (k + 1) (n + 1) =
      qGeometricCoefficientAt q k (n + 1) -
        q.val ^ k * qGeometricCoefficientAt q k n := by
  unfold qGeometricCoefficientAt
  rw [realQFactorial_succ]
  have hfac : realQFactorial q n ≠ 0 := (realQFactorial_pos q n).ne'
  have hstep : 1 - q.val ^ (n + 1) ≠ 0 := (realQFactorial_factor_pos q n).ne'
  field_simp [hfac, hstep]
  ring

/-- A convergent integral q-binomial series advances by multiplication with `1-q^k`. -/
theorem qGeometricCoefficientAt_hasSum_succ (q : RealEulerNome) (k : ℕ) (S : ℝ)
    (hS : HasSum (qGeometricCoefficientAt q k) S) :
    HasSum (qGeometricCoefficientAt q (k + 1)) ((1 - q.val ^ k) * S) := by
  apply (hasSum_nat_add_iff' 1).mp
  convert ((hasSum_nat_add_iff' 1).mpr hS).sub (hS.mul_left (q.val ^ k)) using 1
  · funext n
    exact qGeometricCoefficientAt_succ_difference q k n
  · simp [qGeometricCoefficientAt]
    ring

/-- **Integral q-binomial theorem.** For every `r≥0`, the series at `q^(r+1)` sums to the
finite q-factorial ratio `(q;q)_r/(q;q)_∞`. -/
theorem qGeometricCoefficientAt_hasSum (q : RealEulerNome) :
    ∀ r : ℕ,
      HasSum (qGeometricCoefficientAt q (r + 1))
        (realQFactorial q r / realQFactorialInf q) := by
  intro r
  induction r with
  | zero =>
      convert qGeometricCoefficient_hasSum q using 1
      · funext n
        simp [qGeometricCoefficientAt, qGeometricCoefficient]
      · simp [realQFactorial, one_div]
  | succ r ih =>
      have h := qGeometricCoefficientAt_hasSum_succ q (r + 1)
        (realQFactorial q r / realQFactorialInf q) ih
      convert h using 1
      rw [realQFactorial_succ]
      ring

/-- Algebraic normalized observable `q^n/(1-q)` raised to an integral intervention power. -/
def qGammaIntegerMomentTerm (q : RealEulerNome) (r n : ℕ) : ℝ :=
  qGammaWeight q n * (q.val ^ n / (1 - q.val)) ^ r

/-- Closed integral response of the local positive q-Gamma law. -/
def qGammaIntegerResponse (q : RealEulerNome) (r : ℕ) : ℝ :=
  realQFactorial q r / (1 - q.val) ^ r

/-- Coefficient identity connecting the positive moment term to the integral q-binomial series. -/
theorem qGammaIntegerMomentTerm_eq (q : RealEulerNome) (r n : ℕ) :
    qGammaIntegerMomentTerm q r n =
      (realQFactorialInf q / (1 - q.val) ^ r) *
        qGeometricCoefficientAt q (r + 1) n := by
  unfold qGammaIntegerMomentTerm qGammaWeight qGeometricCoefficient
    qGeometricCoefficientAt
  have hfac : realQFactorial q n ≠ 0 := (realQFactorial_pos q n).ne'
  have hbase : 1 - q.val ≠ 0 := (sub_pos.mpr q.lt_one).ne'
  rw [div_pow, pow_mul]
  field_simp [hfac, hbase]
  rw [← pow_mul, ← pow_mul]
  calc
    realQFactorialInf q * q.val ^ n * q.val ^ (n * r) =
        realQFactorialInf q * (q.val ^ n * q.val ^ (n * r)) := by ring
    _ = realQFactorialInf q * q.val ^ (n + n * r) := by rw [pow_add]
    _ = realQFactorialInf q * q.val ^ ((r + 1) * n) := by
      congr 2
      ring

/-- Scalar identity closing the normalized integral response. -/
theorem qGammaIntegerResponse_eq (q : RealEulerNome) (r : ℕ) :
    qGammaIntegerResponse q r =
      (realQFactorialInf q / (1 - q.val) ^ r) *
        (realQFactorial q r / realQFactorialInf q) := by
  unfold qGammaIntegerResponse
  have hinf := realQFactorialInf_ne_zero q
  field_simp [hinf]

/-- **Exact local positive transform.** Every nonnegative integral intervention moment equals the
q-Gamma factorial response. -/
theorem qGammaIntegerMoment_hasSum (q : RealEulerNome) (r : ℕ) :
    HasSum (qGammaIntegerMomentTerm q r) (qGammaIntegerResponse q r) := by
  have h := (qGeometricCoefficientAt_hasSum q r).mul_left
    (realQFactorialInf q / (1 - q.val) ^ r)
  rw [qGammaIntegerResponse_eq]
  rw [show qGammaIntegerMomentTerm q r =
      fun n ↦ (realQFactorialInf q / (1 - q.val) ^ r) *
        qGeometricCoefficientAt q (r + 1) n by
    funext n
    exact qGammaIntegerMomentTerm_eq q r n]
  exact h

/-- The unit intervention is normalized. -/
theorem qGammaIntegerResponse_one (q : RealEulerNome) :
    qGammaIntegerResponse q 1 = 1 := by
  unfold qGammaIntegerResponse
  rw [show realQFactorial q 1 = 1 - q.val by simp [realQFactorial]]
  simpa only [pow_one] using div_self (sub_pos.mpr q.lt_one).ne'

end

end GaloisForLFunctions.HTGeometry
