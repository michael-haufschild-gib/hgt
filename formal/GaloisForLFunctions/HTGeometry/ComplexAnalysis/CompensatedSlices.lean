import GaloisForLFunctions.HTGeometry.DbarSeveral

/-!
# Holomorphic compensation of complex-line restrictions

Multiplication by a holomorphic function commutes with `∂̄`. In particular, the factor `w^m`
in a compensated slice contributes no differentiated term to `∂̄`, although it does contribute
to `∂`. The squared norm acquires exactly the factor `‖w‖^(2*m)`, which is the polar Jacobian
when the ambient complex dimension is `m+1`.

The real-linear case records the complete decomposition on every complex line, including its
antiholomorphic defect. These identities are the differential and pointwise norm ingredients
of compensated slicing; they do not assert a Sobolev or unique continuation estimate.
-/

open Complex
open scoped ComplexConjugate

namespace HTGeometry

/-- The antiholomorphic derivative obeys the pointwise Leibniz rule. -/
theorem dzbar_mul_at {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dzbar (fun w => f w * g w) z = f z * dzbar g z + g z * dzbar f z := by
  have h : HasFDerivAt (fun w => f w * g w)
      (f z • fderiv ℝ g z + g z • fderiv ℝ f z) z :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [dzbar, h.fderiv, wirtingerAntihol_add,
    wirtingerAntihol_smul, wirtingerAntihol_smul]
  rfl

/-- A holomorphic multiplier commutes with `∂̄`. -/
theorem dzbar_holomorphic_mul {h f : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z) (hf : DifferentiableAt ℝ f z) :
    dzbar (fun w => h w * f w) z = h z * dzbar f z := by
  rw [dzbar_mul_at (hh.restrictScalars ℝ) hf,
    (dzbar_eq_zero_of_differentiableAt hh).1, mul_zero, add_zero]

/-- The monomial degree does not occur in the antiholomorphic derivative. -/
theorem dzbar_pow_mul {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (m : ℕ) :
    dzbar (fun w => w ^ m * f w) z = z ^ m * dzbar f z :=
  dzbar_holomorphic_mul (differentiableAt_id.pow m) hf

/-- A function on a complex vector space restricted to a line and multiplied by `w^m`. -/
def compensatedSlice {E : Type*} [AddCommGroup E] [Module ℂ E]
    (m : ℕ) (f : E → ℂ) (v : E) (w : ℂ) : ℂ := w ^ m * f (w • v)

/-- The squared norm of the holomorphic compensator equals the polar power weight. -/
theorem norm_compensatedSlice_sq {E : Type*} [AddCommGroup E] [Module ℂ E]
    (m : ℕ) (f : E → ℂ) (v : E) (w : ℂ) :
    ‖compensatedSlice m f v w‖ ^ 2 = ‖w‖ ^ (2 * m) * ‖f (w • v)‖ ^ 2 := by
  simp only [compensatedSlice, norm_mul, norm_pow, mul_pow, ← pow_mul]
  rw [Nat.mul_comm m 2]

/-- Restriction of a real-linear functional to a complex line. -/
noncomputable def realLinearSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℝ] ℂ) (v : E) : ℂ →L[ℝ] ℂ :=
  A.comp (((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ)

@[simp] theorem realLinearSlice_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (A : E →L[ℝ] ℂ) (v : E) (w : ℂ) :
    realLinearSlice A v w = A (w • v) := rfl

/-- On a complex line, a real-linear functional has exactly one holomorphic and one
antiholomorphic coefficient. -/
theorem realLinearSlice_decomp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℝ] ℂ) (v : E) (w : ℂ) :
    A (w • v) = wirtingerHol (realLinearSlice A v) * w +
      wirtingerAntihol (realLinearSlice A v) * conj w :=
  wirtinger_decomp (realLinearSlice A v) w

/-- Compensated restriction of a real-linear functional has an exact antiholomorphic defect. -/
theorem dzbar_compensatedSlice_realLinear {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (A : E →L[ℝ] ℂ) (v : E) (m : ℕ) (w : ℂ) :
    dzbar (compensatedSlice m A v) w =
      w ^ m * wirtingerAntihol (realLinearSlice A v) := by
  change dzbar (fun z => z ^ m * realLinearSlice A v z) w = _
  rw [dzbar_pow_mul (realLinearSlice A v).differentiableAt,
    dzbar_eq_of_hasFDerivAt (realLinearSlice A v).hasFDerivAt]

/-- The compensator's degree changes the amplitude but not the relative squared `∂̄` defect. -/
theorem norm_dzbar_compensatedSlice_realLinear_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (A : E →L[ℝ] ℂ) (v : E) (m : ℕ) (w : ℂ) :
    ‖dzbar (compensatedSlice m A v) w‖ ^ 2 =
      ‖w‖ ^ (2 * m) * ‖wirtingerAntihol (realLinearSlice A v)‖ ^ 2 := by
  rw [dzbar_compensatedSlice_realLinear, norm_mul, norm_pow, mul_pow, ← pow_mul,
    Nat.mul_comm m 2]

/-- At every point where a slice is real differentiable, its compensator commutes with `∂̄`. -/
theorem dzbar_compensatedSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (v : E) (m : ℕ) {w : ℂ} (hf : DifferentiableAt ℝ f (w • v)) :
    dzbar (compensatedSlice m f v) w =
      w ^ m * wirtingerAntihol (realLinearSlice (fderiv ℝ f (w • v)) v) := by
  have hline := (((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ).hasFDerivAt (x := w)
  have h : HasFDerivAt (fun z : ℂ => f (z • v))
      (realLinearSlice (fderiv ℝ f (w • v)) v) w :=
    hf.hasFDerivAt.comp w hline
  change dzbar (fun z => z ^ m * f (z • v)) w = _
  rw [dzbar_pow_mul h.differentiableAt, dzbar_eq_of_hasFDerivAt h]

/-- The antiholomorphic derivative on a complex line is the contraction of the coordinate
antiholomorphic derivatives with the conjugate direction. -/
theorem wirtingerAntihol_realLinearSlice_pi {n : ℕ}
    (A : (Fin n → ℂ) →L[ℝ] ℂ) (v : Fin n → ℂ) :
    wirtingerAntihol (realLinearSlice A v) =
      ∑ j, conj (v j) * wirtingerAntihol
        (A.comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)) := by
  have hs (u : Fin n → ℂ) : A u = ∑ j, A (Pi.single j (u j)) := by
    rw [← map_sum]
    congr 1
    ext j
    simp
  change (A ((1 : ℂ) • v) + Complex.I * A (Complex.I • v)) / 2 = _
  rw [one_smul]
  rw [hs v, hs (Complex.I • v), Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  let B := A.comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)
  change (B (v j) + Complex.I * B (Complex.I * v j)) / 2 =
    conj (v j) * wirtingerAntihol B
  rw [wirtinger_decomp B (v j), wirtinger_decomp B (Complex.I * v j),
    map_mul, Complex.conj_I]
  linear_combination (wirtingerHol B * v j / 2 -
    wirtingerAntihol B * conj (v j) / 2) * Complex.I_sq

/-- The exact coordinate formula for the compensated slice. -/
theorem dzbar_compensatedSlice_pi {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : Differentiable ℝ f) (v : Fin n → ℂ) (m : ℕ) (w : ℂ) :
    dzbar (compensatedSlice m f v) w =
      w ^ m * ∑ j, conj (v j) * dzbarAt f j (w • v) := by
  rw [dzbar_compensatedSlice v m (hf _), wirtingerAntihol_realLinearSlice_pi]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [dzbarAt_eq_wirtingerAntihol hf]

end HTGeometry
