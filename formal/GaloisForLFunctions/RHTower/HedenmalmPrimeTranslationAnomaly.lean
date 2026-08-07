import GaloisForLFunctions.RHTower.HedenmalmQuantileRootMode

/-!
# The prime-translation rank-one anomaly

The source-core operator `B = V P` with

`P f = f - (∫f / M) k`,  `V g (x) = i ∫_{-∞}^x g`

commutes with every translation up to a rank-one source channel: the commutator with `S_a` is the
functional `∫f / M` times the fixed vector `V(S_a k - k)`.  For the normalized integer shifts
`T_n f (x) = n^{-1/2} f(x + log n)` the same statement holds with the fixed vector
`V(T_n k - n^{-1/2} k)`.

On the conormal side the Fourier-Laplace evaluation `ℓ_z(f) = ∫ f(x) e^{i z x} dx` transforms under
`T_n` by the literal Dirichlet character `n^{-s(z)}` with `s(z) = 1/2 + i z`, and its jets obey the
exact triangular law with logarithmic prime coefficients.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmPrimeTranslation

open HedenmalmQuantile

variable (S : PositiveDensitySource)

/-! ### The source core -/

/-- Real translation `(S_a f)(x) = f (x - a)`. -/
def sourceShift (a : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := f (x - a)

/-- The normalized integer shift `T_n f (x) = n^{-1/2} f (x + log n)`. -/
def integerShift (n : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (x + Real.log n)

/-- The total-mass functional `ℓ(f) = ∫ f`. -/
def sourceFunctional (f : ℝ → ℂ) : ℂ := ∫ x, f x

/-- The two-ended primitive `V g (x) = i ∫_{-∞}^x g`. -/
def sourcePrimitive (g : ℝ → ℂ) (x : ℝ) : ℂ := Complex.I * ∫ y in Iic x, g y

/-- The rank-one anomaly vector `r_a = V(S_a k - k)`. -/
def shiftAnomaly (a : ℝ) (x : ℝ) : ℂ :=
  sourcePrimitive (fun y => (S.k (y - a) : ℂ) - (S.k y : ℂ)) x

/-- The rank-one anomaly vector of the normalized integer shift. -/
def integerAnomaly (n : ℕ) (x : ℝ) : ℂ :=
  sourcePrimitive (fun y => integerShift n (fun w => (S.k w : ℂ)) y
    - (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (S.k y : ℂ)) x

/-! ### Translation of half-line integrals -/

theorem setIntegral_Iic_comp_sub (f : ℝ → ℂ) (a x : ℝ) :
    ∫ y in Iic x, f (y - a) = ∫ y in Iic (x - a), f y := by
  have h1 : ∫ y in Iic x, f (y - a) = ∫ y, (Iic x).indicator (fun y => f (y - a)) y := by
    rw [integral_indicator measurableSet_Iic]
  have h2 : ∫ y in Iic (x - a), f y = ∫ y, (Iic (x - a)).indicator f y := by
    rw [integral_indicator measurableSet_Iic]
  rw [h1, h2, ← MeasureTheory.integral_add_right_eq_self
    (fun y => (Iic x).indicator (fun y => f (y - a)) y) a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (Iic x).indicator (fun y => f (y - a)) (u + a) = (Iic (x - a)).indicator f u
  by_cases hu : u ∈ Iic (x - a)
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show u + a ∈ Iic x by
      simp only [mem_Iic] at hu ⊢; linarith)]
    simp
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (show u + a ∉ Iic x by
      simp only [mem_Iic] at hu ⊢; intro h; exact hu (by linarith))]

theorem setIntegral_Iic_comp_add (f : ℝ → ℂ) (a x : ℝ) :
    ∫ y in Iic x, f (y + a) = ∫ y in Iic (x + a), f y := by
  have := setIntegral_Iic_comp_sub f (-a) x
  simpa using this

theorem sourceFunctional_sourceShift (f : ℝ → ℂ) (a : ℝ) :
    sourceFunctional (sourceShift a f) = sourceFunctional f := by
  show (∫ x, f (x - a)) = ∫ x, f x
  exact MeasureTheory.integral_sub_right_eq_self f a

theorem sourceFunctional_integerShift (f : ℝ → ℂ) (n : ℕ) :
    sourceFunctional (integerShift n f)
      = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * sourceFunctional f := by
  show (∫ x, (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (x + Real.log n))
    = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∫ x, f x
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_add_right_eq_self f (Real.log n)

/-! ### The rank-one commutator -/

theorem sourceInverse_sourceShift (f : ℝ → ℂ) (hf : Integrable f) (a x : ℝ) :
    sourceInverse S (sourceShift a f) x - sourceInverse S f (x - a)
      = (sourceFunctional f / (S.mass : ℂ)) * shiftAnomaly S a x := by
  have hkC : Integrable (fun y => (S.k y : ℂ)) (volume : Measure ℝ) := S.integrable_k.ofReal
  have hsh : Integrable (sourceShift a f) := by
    unfold sourceShift
    exact hf.comp_sub_right a
  have hkshift : Integrable (fun y => (S.k (y - a) : ℂ)) := by
    simpa using hkC.comp_sub_right a
  have hsplit : ∀ (g : ℝ → ℂ) (hg : Integrable g) (c : ℂ) (t : ℝ),
      Complex.I * ∫ y in Iic t, (g y - c * (S.k y : ℂ))
        = Complex.I * ((∫ y in Iic t, g y) - c * ∫ y in Iic t, (S.k y : ℂ)) := by
    intro g hg c t
    rw [MeasureTheory.integral_sub hg.integrableOn ((hkC.const_mul c).integrableOn),
      MeasureTheory.integral_const_mul]
  rw [HedenmalmQuantile.sourceInverse, HedenmalmQuantile.sourceInverse, shiftAnomaly, sourcePrimitive,
    MeasureTheory.integral_sub hkshift.integrableOn hkC.integrableOn,
    setIntegral_Iic_comp_sub (fun y => (S.k y : ℂ)) a x]
  rw [show (∫ z, sourceShift a f z) = ∫ z, f z from sourceFunctional_sourceShift f a]
  rw [MeasureTheory.integral_sub (hsh.integrableOn) ((hkC.const_mul _).integrableOn),
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub (hf.integrableOn) ((hkC.const_mul _).integrableOn),
    MeasureTheory.integral_const_mul]
  have hshiftInt : (∫ y in Iic x, sourceShift a f y) = ∫ y in Iic (x - a), f y :=
    setIntegral_Iic_comp_sub f a x
  rw [hshiftInt]
  show _ = (∫ z, f z) / (S.mass : ℂ) * _
  ring

theorem sourceInverse_integerShift (f : ℝ → ℂ) (hf : Integrable f) (n : ℕ) (x : ℝ) :
    sourceInverse S (integerShift n f) x
        - (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * sourceInverse S f (x + Real.log n)
      = (sourceFunctional f / (S.mass : ℂ)) * integerAnomaly S n x := by
  have hkC : Integrable (fun y => (S.k y : ℂ)) (volume : Measure ℝ) := S.integrable_k.ofReal
  have hshbase : Integrable (fun y : ℝ => f (y + Real.log n)) (volume : Measure ℝ) :=
    hf.comp_add_right (Real.log n)
  have hkbase : Integrable (fun y : ℝ => (S.k (y + Real.log n) : ℂ)) (volume : Measure ℝ) :=
    hkC.comp_add_right (Real.log n)
  have hsh : Integrable (integerShift n f) (volume : Measure ℝ) :=
    hshbase.const_mul _
  have hkshift : Integrable (fun y => integerShift n (fun w => (S.k w : ℂ)) y)
      (volume : Measure ℝ) := hkbase.const_mul _
  set c : ℂ := (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hc
  rw [HedenmalmQuantile.sourceInverse, HedenmalmQuantile.sourceInverse, integerAnomaly, sourcePrimitive,
    MeasureTheory.integral_sub hkshift.integrableOn ((hkC.const_mul c).integrableOn),
    MeasureTheory.integral_const_mul]
  rw [show (∫ z, integerShift n f z) = c * ∫ z, f z from sourceFunctional_integerShift f n]
  rw [MeasureTheory.integral_sub hsh.integrableOn ((hkC.const_mul _).integrableOn),
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub hf.integrableOn ((hkC.const_mul _).integrableOn),
    MeasureTheory.integral_const_mul]
  have hshiftInt : (∫ y in Iic x, integerShift n f y) = c * ∫ y in Iic (x + Real.log n), f y := by
    show (∫ y in Iic x, c * f (y + Real.log n)) = _
    rw [MeasureTheory.integral_const_mul, setIntegral_Iic_comp_add f]
  have hkshift' : (∫ y in Iic x, integerShift n (fun w => (S.k w : ℂ)) y)
      = c * ∫ y in Iic (x + Real.log n), (S.k y : ℂ) := by
    show (∫ y in Iic x, c * (S.k (y + Real.log n) : ℂ)) = _
    rw [MeasureTheory.integral_const_mul, setIntegral_Iic_comp_add (fun y => (S.k y : ℂ))]
  rw [hshiftInt, hkshift']
  show _ = (∫ z, f z) / (S.mass : ℂ) * _
  ring

/-! ### The fibrewise Dirichlet character -/

/-- The Fourier--Laplace evaluation `ℓ_z(f) = ∫ f(x) e^{i z x} dx`. -/
def sourceEvaluation (z : ℂ) (f : ℝ → ℂ) : ℂ := ∫ x, f x * HedenmalmQuantile.sourceChar z x

/-- The centered Dirichlet exponent `s(z) = 1/2 + i z`. -/
def dirichletExponent (z : ℂ) : ℂ := 1 / 2 + Complex.I * z

theorem sourceChar_sub (z : ℂ) (x a : ℝ) :
    HedenmalmQuantile.sourceChar z (x - a)
      = HedenmalmQuantile.sourceChar z x * Complex.exp (-(Complex.I * z) * (a : ℂ)) := by
  rw [HedenmalmQuantile.sourceChar, HedenmalmQuantile.sourceChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The literal ordinary-integer character.**  The evaluation transforms under the normalized
integer shift by `n^{-s(z)}`. -/
theorem sourceEvaluation_integerShift (z : ℂ) (f : ℝ → ℂ) {n : ℕ} (hn : 0 < n) :
    sourceEvaluation z (integerShift n f)
      = ((n : ℂ) ^ (-(dirichletExponent z))) * sourceEvaluation z f := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have htrans : ∫ x, f (x + Real.log n) * HedenmalmQuantile.sourceChar z x
      = Complex.exp (-(Complex.I * z) * ((Real.log n : ℝ) : ℂ))
        * ∫ y, f y * HedenmalmQuantile.sourceChar z y := by
    have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y => f y * HedenmalmQuantile.sourceChar z (y - Real.log n)) (Real.log n)
    simp only [add_sub_cancel_right] at h
    rw [h, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show f y * HedenmalmQuantile.sourceChar z (y - Real.log n)
      = Complex.exp (-(Complex.I * z) * ((Real.log n : ℝ) : ℂ))
        * (f y * HedenmalmQuantile.sourceChar z y)
    rw [sourceChar_sub]
    ring
  show (∫ x, (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (x + Real.log n)
      * HedenmalmQuantile.sourceChar z x) = _
  rw [show (fun x => (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (x + Real.log n)
        * HedenmalmQuantile.sourceChar z x)
      = fun x => (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * (f (x + Real.log n) * HedenmalmQuantile.sourceChar z x) from
    funext fun x => by ring]
  rw [MeasureTheory.integral_const_mul, htrans, ← mul_assoc]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hnne, dirichletExponent]
  have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_log hnpos.le).symm
  rw [hlog, show ((Real.log n : ℝ) : ℂ) * -(1 / 2 + Complex.I * z)
      = ((-(1 / 2 : ℝ) * Real.log n : ℝ) : ℂ) + -(Complex.I * z) * ((Real.log n : ℝ) : ℂ) by
    push_cast
    ring, Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  rw [Real.rpow_def_of_pos hnpos]
  ring_nf

end HedenmalmPrimeTranslation

end

end RHTower
