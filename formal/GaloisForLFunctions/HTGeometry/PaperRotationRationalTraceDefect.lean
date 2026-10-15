import GaloisForLFunctions.HTGeometry.PaperRotationPolynomialTraceIntegrality
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Rational inversion exposes an exact trace defect

Norm-convergent geometric series construct both bounded resolvents of the
actual rotation generator off its unit circle. The canonical trace of its
logarithmic resolvent is one inside and zero outside. In the constructed
quantum Laurent division ring the same rational expression has trace zero
for every nonzero scalar parameter, by its positive formal Laurent order.

The resulting relative trace defect is exactly one inside and zero
outside. Thus the finite-Weyl trace comparison cannot be extended across
all rational inverses. The defect is a source invariant to retain in an
arithmetic transgression; no projective-class trace identity is assumed.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped Classical
local notation "RotOp" => PaperRotationHilbert →L[ℂ] PaperRotationHilbert

theorem paperRotationModulation_mul (s t : ℝ) :
    paperRotationModulation s * paperRotationModulation t = paperRotationModulation (s + t) :=
  paperRotationModulation_comp s t

theorem paperRotationModulation_pow (t : ℝ) (n : ℕ) :
    paperRotationModulation t ^ n = paperRotationModulation ((n : ℝ) * t) := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, paperRotationModulation_zero]; rfl
  | succ n hn =>
    rw [pow_succ, hn, paperRotationModulation_mul]
    congr 1
    push_cast
    ring

theorem paperRotationModulation_opNorm_le_one (t : ℝ) : ‖paperRotationModulation t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp

private theorem scaled_modulation_norm_lt_one (t : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖z • paperRotationModulation t‖ < 1 := by
  rw [norm_smul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg z)
    (paperRotationModulation_opNorm_le_one t)) hz

theorem paperRotationTrace_modulation (t : ℝ) :
    paperRotationTrace (paperRotationModulation t) = if paperRotationPhase t = 1 then 1 else 0 := by
  simpa only [paperRotationWord, paperRotationShift_zero, ContinuousLinearMap.comp_id,
    eq_self, true_and] using paperRotationTrace_word 0 t

def paperRotationGeometricInverse (t : ℝ) (z : ℂ) : RotOp :=
  ∑' n : ℕ, (z • paperRotationModulation t) ^ n

theorem paperRotationGeometricInverse_left (t : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    (1 - z • paperRotationModulation t) * paperRotationGeometricInverse t z = 1 :=
  mul_neg_geom_series _ (scaled_modulation_norm_lt_one t hz)

theorem paperRotationGeometricInverse_right (t : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    paperRotationGeometricInverse t z * (1 - z • paperRotationModulation t) = 1 :=
  geom_series_mul_neg _ (scaled_modulation_norm_lt_one t hz)

theorem paperRotationGeometricInverse_trace (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (z : ℂ) (hz : ‖z‖ < 1) :
    paperRotationTrace (paperRotationGeometricInverse t z) = 1 := by
  have hs := summable_geometric_of_norm_lt_one (scaled_modulation_norm_lt_one t hz)
  rw [paperRotationGeometricInverse, paperRotationTrace.map_tsum hs]
  have hterm : ∀ n : ℕ, paperRotationTrace ((z • paperRotationModulation t) ^ n) =
      if n = 0 then 1 else 0 := by
    intro n
    rw [smul_pow, map_smul, paperRotationModulation_pow, paperRotationTrace_modulation]
    have hh : paperRotationPhase ((n : ℝ) * t) = 1 ↔ n = 0 := by
      simpa only [Int.cast_natCast, Nat.cast_eq_zero] using ht (n : ℤ)
    simp only [hh]
    split_ifs with hn
    · subst n; simp
    · simp
  simp_rw [hterm]
  simp

private theorem infinite_clock_neg {t : ℝ}
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0) :
    ∀ b : ℤ, paperRotationPhase ((b : ℝ) * -t) = 1 ↔ b = 0 := by
  intro b
  simpa only [Int.cast_neg, neg_mul, mul_neg, neg_eq_zero] using ht (-b)

private theorem modulation_mul_neg (t : ℝ) :
    paperRotationModulation t * paperRotationModulation (-t) = 1 := by
  rw [paperRotationModulation_mul, add_neg_cancel, paperRotationModulation_zero]
  rfl

private theorem modulation_neg_mul (t : ℝ) :
    paperRotationModulation (-t) * paperRotationModulation t = 1 := by
  rw [paperRotationModulation_mul, neg_add_cancel, paperRotationModulation_zero]
  rfl

private theorem modulation_commutes_geometric (t s : ℝ) (z : ℂ) :
    Commute (paperRotationModulation t) (paperRotationGeometricInverse s z) := by
  apply Commute.tsum_right
  intro n
  apply Commute.pow_right
  change paperRotationModulation t * (z • paperRotationModulation s) =
    (z • paperRotationModulation s) * paperRotationModulation t
  rw [mul_smul_comm, smul_mul_assoc, paperRotationModulation_mul, paperRotationModulation_mul,
    add_comm t s]

/-- Actual bounded inverse of V-z for the inside component of its resolvent set. -/
def paperRotationInsideResolvent (t : ℝ) (z : ℂ) : RotOp :=
  paperRotationModulation (-t) * paperRotationGeometricInverse (-t) z

theorem paperRotationInsideResolvent_mul (t : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    (paperRotationModulation t - z • (1 : RotOp)) * paperRotationInsideResolvent t z = 1 := by
  rw [paperRotationInsideResolvent, ← mul_assoc, sub_mul, modulation_mul_neg,
    smul_mul_assoc, one_mul]
  exact paperRotationGeometricInverse_left (-t) z hz

theorem paperRotationInsideResolvent_mul_reverse (t : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    paperRotationInsideResolvent t z * (paperRotationModulation t - z • (1 : RotOp)) = 1 := by
  rw [paperRotationInsideResolvent, mul_sub, mul_assoc,
    ← (modulation_commutes_geometric t (-t) z).eq, ← mul_assoc, modulation_neg_mul,
    one_mul, mul_smul_comm, mul_one]
  have h := paperRotationGeometricInverse_left (-t) z hz
  simpa only [sub_mul, one_mul, smul_mul_assoc] using h

theorem paperRotationInsideResolvent_logarithmicTrace (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (z : ℂ) (hz : ‖z‖ < 1) :
    paperRotationTrace (paperRotationModulation t * paperRotationInsideResolvent t z) = 1 := by
  rw [paperRotationInsideResolvent, ← mul_assoc, modulation_mul_neg, one_mul]
  exact paperRotationGeometricInverse_trace (-t) (infinite_clock_neg ht) z hz

/-- The same logarithmic resolvent has zero constant coefficient in the fixed formal chamber. -/
theorem hahnLaurent_logarithmicResolvent_constant (z : ℂ) (hz : z ≠ 0) :
    ((HahnSeries.single (1 : ℤ) (1 : ℂ)) *
      (HahnSeries.single (1 : ℤ) (1 : ℂ) - HahnSeries.single 0 z)⁻¹).coeff 0 = 0 := by
  let v : HahnSeries ℤ ℂ := HahnSeries.single 1 1
  let f : HahnSeries ℤ ℂ := v - HahnSeries.single 0 z
  have hv : v ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have hf : f ≠ 0 := by
    intro h
    have := congrArg (fun x : HahnSeries ℤ ℂ => x.coeff 0) h
    simp [f, v, hz] at this
  have htop : f.orderTop = 0 := by
    have ho := HahnSeries.orderTop_sub (x := HahnSeries.single (0 : ℤ) z) (y := v)
      (by rw [HahnSeries.orderTop_single hz, HahnSeries.orderTop_single one_ne_zero]; norm_num)
    rw [HahnSeries.orderTop_single hz] at ho
    have he : f = -(HahnSeries.single 0 z - v) := by dsimp [f]; abel
    rw [he, HahnSeries.orderTop_neg, ho, WithTop.coe_zero]
  have hf0 : f.order = 0 := by
    have h := HahnSeries.orderTop_of_ne_zero hf
    rw [htop] at h
    simpa only [HahnSeries.order, dif_neg hf] using WithTop.coe_injective h.symm
  have hi0 : f⁻¹.order = 0 := by
    have h := HahnSeries.order_mul hf (inv_ne_zero hf)
    rw [mul_inv_cancel₀ hf, HahnSeries.order_one, hf0, zero_add] at h
    exact h.symm
  apply HahnSeries.coeff_eq_zero_of_lt_order
  change (0 : ℤ) < (v * f⁻¹).order
  rw [HahnSeries.order_mul hv (inv_ne_zero hf), HahnSeries.order_single one_ne_zero, hi0]
  norm_num

/-- Exact trace mismatch: a rational inverse cannot preserve the finite-word trace comparison. -/
theorem paperRotationInsideResolvent_trace_discrepancy (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    paperRotationTrace (paperRotationModulation t * paperRotationInsideResolvent t z) -
      ((HahnSeries.single (1 : ℤ) (1 : ℂ)) *
        (HahnSeries.single (1 : ℤ) (1 : ℂ) - HahnSeries.single 0 z)⁻¹).coeff 0 = 1 := by
  rw [paperRotationInsideResolvent_logarithmicTrace t ht z hz,
    hahnLaurent_logarithmicResolvent_constant z hz0, sub_zero]

/-- The rational logarithmic derivative in the actual quantum division ring. -/
def quantumLaurentLogarithmicResolvent (c : ℂˣ) (z : ℂ) : QuantumLaurentDivisionRing c :=
  quantumLaurentWord c 0 1 * (quantumLaurentWord c 0 1 - z • 1)⁻¹

theorem quantumLaurentLogarithmicResolvent_trace (c : ℂˣ) (z : ℂ) (hz : z ≠ 0) :
    quantumLaurentTrace c (quantumLaurentLogarithmicResolvent c z) = 0 := by
  let C := skewLaurentConstant (quantumLaurentScaleAut c)
  have hc : C (HahnSeries.single (0 : ℤ) z) = z • (1 : QuantumLaurentDivisionRing c) := by
    change quantumLaurentScalar c z = z • (1 : QuantumLaurentDivisionRing c)
    rw [quantumLaurentScalar_eq_algebraMap, Algebra.algebraMap_eq_smul_one]
  have hv : C (HahnSeries.single (1 : ℤ) (1 : ℂ)) = quantumLaurentWord c 0 1 := rfl
  rw [quantumLaurentLogarithmicResolvent, ← hv, ← hc, ← map_sub, ← map_inv₀, ← map_mul]
  change quantumLaurentInnerTrace (skewLaurentScalarCoefficient _ 0 (C _)) = 0
  rw [skewLaurentScalarCoefficient_constant]
  exact hahnLaurent_logarithmicResolvent_constant z hz

/-- The proved finite-Weyl trace comparison fails on this actual rational inverse. -/
theorem paperRotationInsideResolvent_quantumTrace_discrepancy (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    paperRotationTrace (paperRotationModulation t * paperRotationInsideResolvent t z) -
      quantumLaurentTrace (paperRotationQuantumUnit t)
        (quantumLaurentLogarithmicResolvent (paperRotationQuantumUnit t) z) = 1 := by
  rw [paperRotationInsideResolvent_logarithmicTrace t ht z hz,
    quantumLaurentLogarithmicResolvent_trace _ z hz0, sub_zero]

/-- Outside the circle, the analytic inverse uses the same formal expansion chamber. -/
def paperRotationOutsideResolvent (t : ℝ) (z : ℂ) : RotOp :=
  -(z⁻¹ • paperRotationGeometricInverse t z⁻¹)

theorem paperRotationOutsideResolvent_mul (t : ℝ) (z : ℂ) (hz : 1 < ‖z‖) :
    (paperRotationModulation t - z • (1 : RotOp)) * paperRotationOutsideResolvent t z = 1 := by
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  have hi : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have h := paperRotationGeometricInverse_left t z⁻¹ hi
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  rw [paperRotationOutsideResolvent, mul_neg, mul_smul_comm, sub_mul, smul_mul_assoc,
    one_mul, smul_sub, smul_smul, inv_mul_cancel₀ hz0, one_smul, neg_sub]
  exact h

theorem paperRotationOutsideResolvent_mul_reverse (t : ℝ) (z : ℂ) (hz : 1 < ‖z‖) :
    paperRotationOutsideResolvent t z * (paperRotationModulation t - z • (1 : RotOp)) = 1 := by
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  have hi : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have h := paperRotationGeometricInverse_right t z⁻¹ hi
  rw [mul_sub, mul_one, mul_smul_comm] at h
  rw [paperRotationOutsideResolvent, neg_mul, smul_mul_assoc, mul_sub, mul_smul_comm,
    mul_one, smul_sub, smul_smul, inv_mul_cancel₀ hz0, one_smul, neg_sub]
  exact h

theorem paperRotationOutsideResolvent_logarithmicTrace (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (z : ℂ) (hz : 1 < ‖z‖) :
    paperRotationTrace (paperRotationModulation t * paperRotationOutsideResolvent t z) = 0 := by
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  have hi : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have h := congrArg paperRotationTrace (paperRotationOutsideResolvent_mul t z hz)
  rw [sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul, paperRotationTrace_one,
    paperRotationOutsideResolvent, map_neg, map_smul,
    paperRotationGeometricInverse_trace t ht z⁻¹ hi] at h
  simp only [smul_eq_mul, mul_one, mul_neg, mul_inv_cancel₀ hz0, sub_neg_eq_add] at h
  simpa only [paperRotationOutsideResolvent, mul_neg] using
    add_right_cancel (h.trans (zero_add (1 : ℂ)).symm)

theorem paperRotationOutsideResolvent_quantumTrace_discrepancy (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (z : ℂ) (hz : 1 < ‖z‖) :
    paperRotationTrace (paperRotationModulation t * paperRotationOutsideResolvent t z) -
      quantumLaurentTrace (paperRotationQuantumUnit t)
        (quantumLaurentLogarithmicResolvent (paperRotationQuantumUnit t) z) = 0 := by
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  rw [paperRotationOutsideResolvent_logarithmicTrace t ht z hz,
    quantumLaurentLogarithmicResolvent_trace _ z hz0, sub_self]

theorem paperRotationInsideResolvent_eq_inverse (t : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    Ring.inverse (paperRotationModulation t - z • (1 : RotOp)) =
      paperRotationInsideResolvent t z := by
  let u : RotOpˣ := ⟨_, paperRotationInsideResolvent t z,
    paperRotationInsideResolvent_mul t z hz, paperRotationInsideResolvent_mul_reverse t z hz⟩
  exact Ring.inverse_unit u

theorem paperRotationOutsideResolvent_eq_inverse (t : ℝ) (z : ℂ) (hz : 1 < ‖z‖) :
    Ring.inverse (paperRotationModulation t - z • (1 : RotOp)) =
      paperRotationOutsideResolvent t z := by
  let u : RotOpˣ := ⟨_, paperRotationOutsideResolvent t z,
    paperRotationOutsideResolvent_mul t z hz, paperRotationOutsideResolvent_mul_reverse t z hz⟩
  exact Ring.inverse_unit u

/-- The actual operator inverse and fixed formal inverse, compared using their constructed traces. -/
def paperRotationRationalTraceDefect (t : ℝ) (z : ℂ) : ℂ :=
  paperRotationTrace (paperRotationModulation t *
    Ring.inverse (paperRotationModulation t - z • (1 : RotOp))) -
  quantumLaurentTrace (paperRotationQuantumUnit t)
    (quantumLaurentLogarithmicResolvent (paperRotationQuantumUnit t) z)

theorem paperRotationRationalTraceDefect_inside (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) : paperRotationRationalTraceDefect t z = 1 := by
  rw [paperRotationRationalTraceDefect, paperRotationInsideResolvent_eq_inverse t z hz]
  exact paperRotationInsideResolvent_quantumTrace_discrepancy t ht z hz0 hz

theorem paperRotationRationalTraceDefect_outside (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (z : ℂ) (hz : 1 < ‖z‖) : paperRotationRationalTraceDefect t z = 0 := by
  rw [paperRotationRationalTraceDefect, paperRotationOutsideResolvent_eq_inverse t z hz]
  exact paperRotationOutsideResolvent_quantumTrace_discrepancy t ht z hz

theorem paperRotationModulation_mem_algebra (t : ℝ) (b : ℤ) :
    paperRotationModulation ((b : ℝ) * t) ∈ paperRotationAlgebra t := by
  simpa only [paperRotationWord, paperRotationShift_zero, ContinuousLinearMap.comp_id] using
    paperRotationWord_mem_algebra t 0 b

/-- The norm sums belong to the actual closed rotation algebra. -/
theorem paperRotationGeometricInverse_mem_algebra (t : ℝ) (b : ℤ) (z : ℂ) :
    paperRotationGeometricInverse ((b : ℝ) * t) z ∈ paperRotationAlgebra t := by
  apply tsum_mem (StarSubalgebra.isClosed_topologicalClosure _)
  intro n
  exact pow_mem ((paperRotationAlgebra t).smul_mem (paperRotationModulation_mem_algebra t b) z) n

theorem paperRotationInsideResolvent_mem_algebra (t : ℝ) (z : ℂ) :
    paperRotationInsideResolvent t z ∈ paperRotationAlgebra t := by
  have hm := paperRotationModulation_mem_algebra t (-1)
  have hs := paperRotationGeometricInverse_mem_algebra t (-1) z
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at hm hs
  exact (paperRotationAlgebra t).mul_mem hm hs

theorem paperRotationOutsideResolvent_mem_algebra (t : ℝ) (z : ℂ) :
    paperRotationOutsideResolvent t z ∈ paperRotationAlgebra t := by
  have hs := paperRotationGeometricInverse_mem_algebra t 1 z⁻¹
  simp only [Int.cast_one, one_mul] at hs
  exact (paperRotationAlgebra t).neg_mem ((paperRotationAlgebra t).smul_mem hs z⁻¹)

end
end GaloisForLFunctions.HTGeometry
