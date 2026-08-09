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

end

end GaloisForLFunctions.HTGeometry
