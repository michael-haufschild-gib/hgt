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


/-! ### The anomaly vectors are nonzero -/

theorem shiftAnomaly_eq (a x : ℝ) :
    shiftAnomaly S a x
      = Complex.I * (((S.mass * (S.cdfFun (x - a) - S.cdfFun x) : ℝ)) : ℂ) := by
  have hkC : Integrable (fun y => (S.k y : ℂ)) (volume : Measure ℝ) := S.integrable_k.ofReal
  have hkshift : Integrable (fun y => (S.k (y - a) : ℂ)) (volume : Measure ℝ) := by
    have := hkC.comp_sub_right a
    exact this
  rw [shiftAnomaly, sourcePrimitive,
    MeasureTheory.integral_sub hkshift.integrableOn hkC.integrableOn,
    setIntegral_Iic_comp_sub (fun y => (S.k y : ℂ)) a x]
  congr 1
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_sub]
  congr 1
  have hM : S.mass ≠ 0 := S.mass_ne_zero
  show (∫ y in Iic (x - a), S.k y) - ∫ y in Iic x, S.k y
    = S.mass * ((∫ y in Iic (x - a), S.k y) / S.mass - (∫ y in Iic x, S.k y) / S.mass)
  field_simp

/-- **The real-translation anomaly vanishes only for the trivial shift.** -/
theorem shiftAnomaly_eq_zero_iff (a : ℝ) :
    (∀ x, shiftAnomaly S a x = 0) ↔ a = 0 := by
  constructor
  · intro h
    by_contra hne
    have h0 := h 0
    rw [shiftAnomaly_eq] at h0
    have hzero : S.cdfFun (0 - a) - S.cdfFun 0 = 0 := by
      have : ((S.mass * (S.cdfFun (0 - a) - S.cdfFun 0) : ℝ) : ℂ) = 0 := by
        simpa [Complex.I_ne_zero] using h0
      have hr : S.mass * (S.cdfFun (0 - a) - S.cdfFun 0) = 0 := by exact_mod_cast this
      rcases mul_eq_zero.mp hr with hm | hc
      · exact absurd hm S.mass_ne_zero
      · exact hc
    have heq : S.cdfFun (0 - a) = S.cdfFun 0 := by linarith
    exact hne (by
      have := S.strictMono_cdfFun.injective heq
      linarith)
  · rintro rfl
    intro x
    rw [shiftAnomaly_eq]
    simp

theorem integerAnomaly_eq (n : ℕ) (x : ℝ) :
    integerAnomaly S n x
      = Complex.I * ((((n : ℝ) ^ (-(1 / 2 : ℝ))) * S.mass
          * (S.cdfFun (x + Real.log n) - S.cdfFun x) : ℝ) : ℂ) := by
  have hkC : Integrable (fun y => (S.k y : ℂ)) (volume : Measure ℝ) := S.integrable_k.ofReal
  have hkbase : Integrable (fun y : ℝ => (S.k (y + Real.log n) : ℂ)) (volume : Measure ℝ) :=
    hkC.comp_add_right (Real.log n)
  set c : ℂ := (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hc
  have hkshift : Integrable (fun y => integerShift n (fun w => (S.k w : ℂ)) y)
      (volume : Measure ℝ) := hkbase.const_mul _
  rw [integerAnomaly, sourcePrimitive,
    MeasureTheory.integral_sub hkshift.integrableOn ((hkC.const_mul c).integrableOn),
    MeasureTheory.integral_const_mul]
  have hkshift' : (∫ y in Iic x, integerShift n (fun w => (S.k w : ℂ)) y)
      = c * ∫ y in Iic (x + Real.log n), (S.k y : ℂ) := by
    show (∫ y in Iic x, c * (S.k (y + Real.log n) : ℂ)) = _
    rw [MeasureTheory.integral_const_mul, setIntegral_Iic_comp_add (fun y => (S.k y : ℂ))]
  rw [hkshift']
  congr 1
  rw [integral_complex_ofReal, integral_complex_ofReal, hc, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  congr 1
  have hM : S.mass ≠ 0 := S.mass_ne_zero
  show (n : ℝ) ^ (-(1 / 2 : ℝ)) * (∫ y in Iic (x + Real.log n), S.k y)
      - (n : ℝ) ^ (-(1 / 2 : ℝ)) * ∫ y in Iic x, S.k y
    = (n : ℝ) ^ (-(1 / 2 : ℝ)) * S.mass
      * ((∫ y in Iic (x + Real.log n), S.k y) / S.mass - (∫ y in Iic x, S.k y) / S.mass)
  field_simp

/-- **The integer-shift anomaly vanishes only for `n = 1`.** -/
theorem integerAnomaly_eq_zero_iff {n : ℕ} (hn : 0 < n) :
    (∀ x, integerAnomaly S n x = 0) ↔ n = 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow : (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  constructor
  · intro h
    have h0 := h 0
    rw [integerAnomaly_eq] at h0
    have hr : (n : ℝ) ^ (-(1 / 2 : ℝ)) * S.mass
        * (S.cdfFun (0 + Real.log n) - S.cdfFun 0) = 0 := by
      have : (((n : ℝ) ^ (-(1 / 2 : ℝ)) * S.mass
          * (S.cdfFun (0 + Real.log n) - S.cdfFun 0) : ℝ) : ℂ) = 0 := by
        simpa [Complex.I_ne_zero] using h0
      exact_mod_cast this
    have hcdf : S.cdfFun (0 + Real.log n) = S.cdfFun 0 := by
      rcases mul_eq_zero.mp hr with hpm | hc
      · rcases mul_eq_zero.mp hpm with hp | hm
        · exact absurd hp hpow.ne'
        · exact absurd hm S.mass_ne_zero
      · linarith
    have hlog : Real.log n = 0 := by
      have := S.strictMono_cdfFun.injective hcdf
      linarith
    have hone : (n : ℝ) = 1 := by
      have := Real.exp_log hnpos
      rw [hlog, Real.exp_zero] at this
      exact this.symm
    exact_mod_cast hone
  · rintro rfl
    intro x
    rw [integerAnomaly_eq]
    simp

/-! ### The conormal jets and the triangular prime law -/

theorem cpow_neg_dirichletExponent (z : ℂ) {n : ℕ} (hn : 0 < n) :
    ((n : ℂ) ^ (-(dirichletExponent z)))
      = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * z) * ((Real.log n : ℝ) : ℂ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
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

/-- The `j`-th Fourier--Laplace jet `ℓ_z^{[j]}(f) = ∫ (i x)^j f(x) e^{i z x} dx`. -/
def sourceEvaluationJet (z : ℂ) (j : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, (Complex.I * (x : ℂ)) ^ j * f x * HedenmalmQuantile.sourceChar z x

theorem sourceEvaluationJet_zero (z : ℂ) (f : ℝ → ℂ) :
    sourceEvaluationJet z 0 f = sourceEvaluation z f := by
  rw [sourceEvaluationJet, sourceEvaluation]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (Complex.I * (x : ℂ)) ^ 0 * f x * HedenmalmQuantile.sourceChar z x
    = f x * HedenmalmQuantile.sourceChar z x
  rw [pow_zero, one_mul]

/-- **The triangular prime law for the conormal jets.**  The `j`-th jet transforms under the
normalized integer shift by the Dirichlet character times a triangular combination of the lower
jets whose coefficients are powers of the logarithmic prime. -/
theorem sourceEvaluationJet_integerShift (z : ℂ) (j : ℕ) (f : ℝ → ℂ) {n : ℕ} (hn : 0 < n)
    (hint : ∀ r ∈ Finset.range (j + 1),
      Integrable (fun y : ℝ => (Complex.I * (y : ℂ)) ^ r * f y * HedenmalmQuantile.sourceChar z y)
        (volume : Measure ℝ)) :
    sourceEvaluationJet z j (integerShift n f)
      = ((n : ℂ) ^ (-(dirichletExponent z))) *
        ∑ r ∈ Finset.range (j + 1), sourceEvaluationJet z r f
          * (-(Complex.I * ((Real.log n : ℝ) : ℂ))) ^ (j - r) * (j.choose r : ℂ) := by
  set L : ℝ := Real.log n with hL
  set c : ℂ := (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hc
  set e : ℂ := Complex.exp (-(Complex.I * z) * ((L : ℝ) : ℂ)) with he
  have hpull : sourceEvaluationJet z j (integerShift n f)
      = c * ∫ x : ℝ, (Complex.I * (x : ℂ)) ^ j * f (x + L)
          * HedenmalmQuantile.sourceChar z x := by
    rw [sourceEvaluationJet, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (Complex.I * (x : ℂ)) ^ j * (c * f (x + L)) * HedenmalmQuantile.sourceChar z x = _
    ring
  have hshift : (∫ x : ℝ, (Complex.I * (x : ℂ)) ^ j * f (x + L)
        * HedenmalmQuantile.sourceChar z x)
      = ∫ y : ℝ, (Complex.I * ((y : ℂ) - (L : ℂ))) ^ j * f y
        * HedenmalmQuantile.sourceChar z (y - L) := by
    have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ => (Complex.I * ((y : ℂ) - (L : ℂ))) ^ j * f y
        * HedenmalmQuantile.sourceChar z (y - L)) L
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (Complex.I * (x : ℂ)) ^ j * f (x + L) * HedenmalmQuantile.sourceChar z x
      = (Complex.I * ((((x + L : ℝ)) : ℂ) - (L : ℂ))) ^ j * f (x + L)
        * HedenmalmQuantile.sourceChar z ((x + L) - L)
    congr 2
    · push_cast
      ring
    · norm_num
  have hexpand : (∫ y : ℝ, (Complex.I * ((y : ℂ) - (L : ℂ))) ^ j * f y
        * HedenmalmQuantile.sourceChar z (y - L))
      = e * ∑ r ∈ Finset.range (j + 1), sourceEvaluationJet z r f
          * (-(Complex.I * ((L : ℝ) : ℂ))) ^ (j - r) * (j.choose r : ℂ) := by
    have hsum : ∀ y : ℝ, (Complex.I * ((y : ℂ) - (L : ℂ))) ^ j * f y
        * HedenmalmQuantile.sourceChar z (y - L)
        = ∑ r ∈ Finset.range (j + 1),
          e * ((Complex.I * (y : ℂ)) ^ r * f y * HedenmalmQuantile.sourceChar z y
            * (-(Complex.I * ((L : ℝ) : ℂ))) ^ (j - r) * (j.choose r : ℂ)) := by
      intro y
      have hchar : HedenmalmQuantile.sourceChar z (y - L)
          = HedenmalmQuantile.sourceChar z y * e := sourceChar_sub z y L
      have hbin : (Complex.I * ((y : ℂ) - (L : ℂ))) ^ j
          = ∑ r ∈ Finset.range (j + 1), (Complex.I * (y : ℂ)) ^ r
            * (-(Complex.I * ((L : ℝ) : ℂ))) ^ (j - r) * (j.choose r : ℂ) := by
        rw [show Complex.I * ((y : ℂ) - (L : ℂ))
            = Complex.I * (y : ℂ) + -(Complex.I * ((L : ℝ) : ℂ)) by ring]
        exact add_pow _ _ j
      rw [hchar, hbin, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsum)]
    rw [MeasureTheory.integral_finsetSum _ (fun r hr =>
      (((hint r hr).mul_const ((-(Complex.I * ((L : ℝ) : ℂ))) ^ (j - r))).mul_const
        ((j.choose r : ℂ))).const_mul e)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [show (fun a : ℝ => e * ((Complex.I * (a : ℂ)) ^ r * f a
          * HedenmalmQuantile.sourceChar z a
          * (-(Complex.I * ((L : ℝ) : ℂ))) ^ (j - r) * (j.choose r : ℂ)))
        = fun a : ℝ => (e * ((-(Complex.I * ((L : ℝ) : ℂ))) ^ (j - r) * (j.choose r : ℂ)))
          * ((Complex.I * (a : ℂ)) ^ r * f a * HedenmalmQuantile.sourceChar z a) from
      funext fun a => by ring]
    rw [MeasureTheory.integral_const_mul, sourceEvaluationJet]
    ring
  rw [hpull, hshift, hexpand, cpow_neg_dirichletExponent z hn, ← hc, ← he, ← mul_assoc]


/-! ### The explicit source-normalized right mode -/

theorem hasDerivAt_setIntegral_Iic {g : ℝ → ℂ} (hg : Continuous g) (hgi : Integrable g)
    (x : ℝ) : HasDerivAt (fun t => ∫ y in Iic t, g y) (g x) x := by
  have hsplit : ∀ t : ℝ, (∫ y in Iic t, g y)
      = (∫ y in Iic (0 : ℝ), g y) + ∫ y in (0 : ℝ)..t, g y := by
    intro t
    rcases le_total (0 : ℝ) t with ht | ht
    · rw [intervalIntegral.integral_of_le ht, ← MeasureTheory.setIntegral_union
        (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hgi.integrableOn hgi.integrableOn,
        Iic_union_Ioc_eq_Iic ht]
    · rw [intervalIntegral.integral_of_ge ht]
      have hs : (∫ y in Iic (0 : ℝ), g y) = (∫ y in Iic t, g y) + ∫ y in Ioc t (0 : ℝ), g y := by
        rw [← MeasureTheory.setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
          hgi.integrableOn hgi.integrableOn, Iic_union_Ioc_eq_Iic ht]
      rw [hs]
      ring
  have h : HasDerivAt (fun t => ∫ y in (0 : ℝ)..t, g y) (g x) x :=
    (hg.integral_hasStrictDerivAt 0 x).hasDerivAt
  refine (h.const_add (∫ y in Iic (0 : ℝ), g y)).congr_of_eventuallyEq ?_
  filter_upwards with t
  exact hsplit t

/-- The source primitive `I_z(x) = ∫_{-∞}^x k(y) e^{i z y} dy`. -/
def sourceModeI (z : ℂ) (x : ℝ) : ℂ :=
  ∫ y in Iic x, (S.k y : ℂ) * HedenmalmQuantile.sourceChar z y

/-- The source-pointed mode `u_z(x) = -i e^{-i z x} I_z(x)`. -/
def sourceModeU (z : ℂ) (x : ℝ) : ℂ :=
  -Complex.I * Complex.exp (-(Complex.I * z) * (x : ℂ)) * sourceModeI S z x

/-- The right mode `f_z = -z u_z`. -/
def sourceModeF (z : ℂ) (x : ℝ) : ℂ := -z * sourceModeU S z x

theorem hasDerivAt_sourceModeI {z : ℂ} (hz : HedenmalmQuantile.HasShiftedTail S z) (x : ℝ) :
    HasDerivAt (sourceModeI S z) ((S.k x : ℂ) * HedenmalmQuantile.sourceChar z x) x := by
  refine hasDerivAt_setIntegral_Iic ?_ (HedenmalmQuantile.integrable_k_sourceChar S hz) x
  exact (Complex.continuous_ofReal.comp S.continuous_k).mul
    (HedenmalmQuantile.continuous_sourceChar z)

/-- **The source-pointed mode solves the Hedenmalm equation** `(-i ∂ + z) u_z = -k`. -/
theorem hasDerivAt_sourceModeU {z : ℂ} (hz : HedenmalmQuantile.HasShiftedTail S z) (x : ℝ) :
    HasDerivAt (sourceModeU S z)
      (-(Complex.I * z) * sourceModeU S z x - Complex.I * (S.k x : ℂ)) x := by
  have hI := hasDerivAt_sourceModeI S hz x
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(Complex.I * z) * (t : ℂ)))
      (-(Complex.I * z) * Complex.exp (-(Complex.I * z) * (x : ℂ))) x := by
    have hlin : HasDerivAt (fun t : ℝ => -(Complex.I * z) * ((t : ℝ) : ℂ))
        (-(Complex.I * z)) x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_mul (-(Complex.I * z))
    have := hlin.cexp
    refine this.congr_deriv ?_
    ring
  have hprod := ((hE.mul hI).const_mul (-Complex.I))
  have hfun : (fun y : ℝ => -Complex.I *
      ((fun t : ℝ => Complex.exp (-(Complex.I * z) * (t : ℂ))) * sourceModeI S z) y)
      = sourceModeU S z := by
    funext y
    show -Complex.I * (Complex.exp (-(Complex.I * z) * (y : ℂ)) * sourceModeI S z y) = _
    rw [sourceModeU]
    ring
  rw [hfun] at hprod
  refine hprod.congr_deriv ?_
  have hEχ : Complex.exp (-(Complex.I * z) * (x : ℂ)) * HedenmalmQuantile.sourceChar z x = 1 := by
    rw [HedenmalmQuantile.sourceChar, ← Complex.exp_add]
    simp
  rw [sourceModeU]
  have hrw : -Complex.I * (-(Complex.I * z) * Complex.exp (-(Complex.I * z) * (x : ℂ))
        * sourceModeI S z x
      + Complex.exp (-(Complex.I * z) * (x : ℂ)) * ((S.k x : ℂ)
        * HedenmalmQuantile.sourceChar z x))
      = -(Complex.I * z) * (-Complex.I * Complex.exp (-(Complex.I * z) * (x : ℂ))
        * sourceModeI S z x)
        - Complex.I * ((S.k x : ℂ)
          * (Complex.exp (-(Complex.I * z) * (x : ℂ)) * HedenmalmQuantile.sourceChar z x)) := by
    ring
  rw [hrw, hEχ, mul_one]

/-- **The Hedenmalm source equation** in the form `(A + z) u_z = -k`. -/
theorem sourceModeU_equation (z : ℂ) (x : ℝ) :
    -Complex.I * (-(Complex.I * z) * sourceModeU S z x - Complex.I * (S.k x : ℂ))
        + z * sourceModeU S z x
      = -(S.k x : ℂ) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (sourceModeU S z x * z + (S.k x : ℂ)) * hI

/-- **The eigen-relation of the right mode**, `(I + z B) f_z = 0` in pointwise form:
`f_z = -z u_z` and `u_z` is the value of the source inverse on `f_z` whenever the mode vanishes at
both ends. -/
theorem sourceModeF_eq {z : ℂ} (x : ℝ) : sourceModeF S z x = -z * sourceModeU S z x := rfl



/-- The derivative field of the source-pointed mode. -/
def sourceModeD (z : ℂ) (y : ℝ) : ℂ :=
  -(Complex.I * z) * sourceModeU S z y - Complex.I * (S.k y : ℂ)

theorem sourceModeF_eq_neg_I_mul_D (z : ℂ) (y : ℝ) :
    sourceModeF S z y = -Complex.I * sourceModeD S z y + (S.k y : ℂ) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [sourceModeF, sourceModeD]
  linear_combination (-(sourceModeU S z y * z) - (S.k y : ℂ)) * hI

theorem sourceModeD_eq (z : ℂ) (y : ℝ) :
    sourceModeD S z y = Complex.I * (sourceModeF S z y - (S.k y : ℂ)) := by
  rw [sourceModeF, sourceModeD]
  ring

/-- **The eigen-relation of the explicit right mode.**  When the mode vanishes at `-∞` and carries
the full source mass, the source inverse acts on `f_z` by `-z⁻¹`. -/
theorem sourceInverse_sourceModeF {z : ℂ} (hz : HedenmalmQuantile.HasShiftedTail S z)
    (hint : Integrable (sourceModeF S z) (volume : Measure ℝ))
    (hbot : Filter.Tendsto (sourceModeU S z) Filter.atBot (nhds 0))
    (hmass : (∫ x, sourceModeF S z x) = (S.mass : ℂ)) (x : ℝ) :
    HedenmalmQuantile.sourceInverse S (sourceModeF S z) x = sourceModeU S z x := by
  have hkC : Integrable (fun y => (S.k y : ℂ)) (volume : Measure ℝ) := S.integrable_k.ofReal
  have hMne : ((S.mass : ℝ) : ℂ) ≠ 0 := by exact_mod_cast S.mass_ne_zero
  have hD : Integrable (sourceModeD S z) (volume : Measure ℝ) := by
    refine ((hint.sub hkC).const_mul Complex.I).congr ?_
    filter_upwards with y
    exact (sourceModeD_eq S z y).symm
  have hderiv : ∀ y ∈ Iic x, HasDerivAt (sourceModeU S z) (sourceModeD S z y) y :=
    fun y _ => hasDerivAt_sourceModeU S hz y
  have hftc : (∫ y in Iic x, sourceModeD S z y) = sourceModeU S z x - 0 :=
    MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto' hderiv hD.integrableOn hbot
  have hsplit : (∫ y in Iic x, sourceModeF S z y)
      = -Complex.I * (∫ y in Iic x, sourceModeD S z y) + ∫ y in Iic x, (S.k y : ℂ) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add
      ((hD.const_mul (-Complex.I)).integrableOn) hkC.integrableOn]
    refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
    exact sourceModeF_eq_neg_I_mul_D S z y
  rw [HedenmalmQuantile.sourceInverse,
    MeasureTheory.integral_sub hint.integrableOn ((hkC.const_mul _).integrableOn),
    MeasureTheory.integral_const_mul, hmass, hsplit, hftc]
  field_simp
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(sourceModeU S z x)) * hI



/-! ### Reflection and conjugation of the source mode -/

theorem setIntegral_Iic_comp_neg (g : ℝ → ℂ) (x : ℝ) :
    ∫ y in Iic (-x), g y = ∫ u in Ici x, g (-u) := by
  have h1 : ∫ y in Iic (-x), g y = ∫ y, (Iic (-x)).indicator g y := by
    rw [integral_indicator measurableSet_Iic]
  have h2 : ∫ u in Ici x, g (-u) = ∫ u, (Ici x).indicator (fun u => g (-u)) u := by
    rw [integral_indicator measurableSet_Ici]
  rw [h1, h2, ← integral_neg_eq_self (fun y => (Iic (-x)).indicator g y) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (Iic (-x)).indicator g (-u) = (Ici x).indicator (fun u => g (-u)) u
  by_cases hu : u ∈ Ici x
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show -u ∈ Iic (-x) by
      simp only [mem_Ici] at hu; simp only [mem_Iic]; linarith)]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (show -u ∉ Iic (-x) by
      simp only [mem_Ici] at hu
      simp only [mem_Iic]
      intro h
      exact hu (by linarith))]

theorem setIntegral_Ici_eq_sub {g : ℝ → ℂ} (hg : Integrable g (volume : Measure ℝ)) (x : ℝ) :
    (∫ u in Ici x, g u) = (∫ u, g u) - ∫ u in Iic x, g u := by
  have hIci : (∫ u in Ici x, g u) = ∫ u in Ioi x, g u :=
    setIntegral_congr_set (Filter.EventuallyEq.symm Ioi_ae_eq_Ici)
  have h : (∫ y in Iic x, g y) + ∫ y in Ioi x, g y = ∫ y, g y := by
    rw [← MeasureTheory.setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hg.integrableOn hg.integrableOn, Iic_union_Ioi, setIntegral_univ]
  rw [hIci]
  linear_combination h

/-- **Reflection of the source primitive.**  Evenness of the source turns the reflected primitive
into the complementary tail. -/
theorem sourceModeI_neg (hk : ∀ x, S.k (-x) = S.k x) {z : ℂ}
    (hz : HedenmalmQuantile.HasShiftedTail S z) (x : ℝ) :
    sourceModeI S (-z) (-x) = HedenmalmQuantile.xiC S z - sourceModeI S z x := by
  have hint := HedenmalmQuantile.integrable_k_sourceChar S hz
  rw [sourceModeI, setIntegral_Iic_comp_neg]
  have hpt : ∀ u : ℝ, (S.k (-u) : ℂ) * HedenmalmQuantile.sourceChar (-z) (-u)
      = (S.k u : ℂ) * HedenmalmQuantile.sourceChar z u := by
    intro u
    rw [hk u, HedenmalmQuantile.sourceChar, HedenmalmQuantile.sourceChar]
    congr 2
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ici (fun u _ => hpt u),
    setIntegral_Ici_eq_sub hint x, HedenmalmQuantile.xiC, sourceModeI]

/-- **Reflection of the source-pointed mode** at a zero of the source transform. -/
theorem sourceModeU_neg (hk : ∀ x, S.k (-x) = S.k x) {z : ℂ}
    (hz : HedenmalmQuantile.HasShiftedTail S z) (hzero : HedenmalmQuantile.xiC S z = 0) (x : ℝ) :
    sourceModeU S (-z) (-x) = -sourceModeU S z x := by
  rw [sourceModeU, sourceModeU, sourceModeI_neg S hk hz x, hzero]
  have hexp : Complex.exp (-(Complex.I * -z) * ((-x : ℝ) : ℂ))
      = Complex.exp (-(Complex.I * z) * (x : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- **The reflection package `R f_z = f_{-z}`** at a zero of the source transform. -/
theorem sourceModeF_neg (hk : ∀ x, S.k (-x) = S.k x) {z : ℂ}
    (hz : HedenmalmQuantile.HasShiftedTail S z) (hzero : HedenmalmQuantile.xiC S z = 0) (x : ℝ) :
    sourceModeF S (-z) (-x) = sourceModeF S z x := by
  rw [sourceModeF, sourceModeF, sourceModeU_neg S hk hz hzero x]
  ring

/-- **Conjugation of the source primitive.**  The source is real, so conjugation reflects the
spectral parameter through the imaginary axis. -/
theorem conj_sourceModeI (z : ℂ) (x : ℝ) :
    (starRingEnd ℂ) (sourceModeI S z x) = sourceModeI S (-(starRingEnd ℂ) z) x := by
  rw [sourceModeI, sourceModeI, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
  rw [map_mul, Complex.conj_ofReal, HedenmalmQuantile.sourceChar, HedenmalmQuantile.sourceChar,
    ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **Conjugation of the source-pointed mode.** -/
theorem conj_sourceModeU (z : ℂ) (x : ℝ) :
    (starRingEnd ℂ) (sourceModeU S z x) = -sourceModeU S (-(starRingEnd ℂ) z) x := by
  rw [sourceModeU, sourceModeU, map_mul, map_mul, ← Complex.exp_conj, conj_sourceModeI]
  have hexp : (starRingEnd ℂ) (-(Complex.I * z) * (x : ℂ))
      = -(Complex.I * -(starRingEnd ℂ) z) * (x : ℂ) := by
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hexp]
  simp only [map_neg, Complex.conj_I]
  ring

/-- **Conjugation of the right mode**, `conj f_z = f_{-conj z}`. -/
theorem conj_sourceModeF (z : ℂ) (x : ℝ) :
    (starRingEnd ℂ) (sourceModeF S z x) = sourceModeF S (-(starRingEnd ℂ) z) x := by
  rw [sourceModeF, sourceModeF, map_mul, map_neg, conj_sourceModeU]
  ring



/-! ### Geometric multiplicity one -/

/-- **Uniqueness for the source equation.**  Two solutions of the same inhomogeneous Hedenmalm
equation whose tilted difference vanishes at one end coincide.  This is the geometric
multiplicity-one statement: the eigenspace of the source inverse at a divisor point is a line. -/
theorem eq_of_sourceEquation {z c : ℂ} {u v u' v' : ℝ → ℂ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (heu : ∀ x, -Complex.I * u' x + z * u x = c * (S.k x : ℂ))
    (hev : ∀ x, -Complex.I * v' x + z * v x = c * (S.k x : ℂ))
    (hbot : Filter.Tendsto (fun x => (u x - v x) * HedenmalmQuantile.sourceChar z x)
      Filter.atBot (nhds 0)) :
    ∀ x, u x = v x := by
  have hchar : ∀ x : ℝ, HasDerivAt (HedenmalmQuantile.sourceChar z)
      (Complex.I * z * HedenmalmQuantile.sourceChar z x) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => Complex.I * z * ((t : ℝ) : ℂ)) (Complex.I * z) x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * z)
    have := hlin.cexp
    refine this.congr_deriv ?_
    rw [HedenmalmQuantile.sourceChar]
    ring
  have hzero : ∀ x : ℝ,
      HasDerivAt (fun t => (u t - v t) * HedenmalmQuantile.sourceChar z t) 0 x := by
    intro x
    have h := ((hu x).sub (hv x)).mul (hchar x)
    refine h.congr_deriv ?_
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hx : -Complex.I * (u' x - v' x) + z * (u x - v x) = 0 := by
      have h1 := heu x
      have h2 := hev x
      linear_combination h1 - h2
    simp only [Pi.sub_apply]
    linear_combination (Complex.I * HedenmalmQuantile.sourceChar z x) * hx
      + (HedenmalmQuantile.sourceChar z x * (u' x - v' x)) * hI
  have hdiff : Differentiable ℝ (fun t => (u t - v t) * HedenmalmQuantile.sourceChar z t) :=
    fun x => (hzero x).differentiableAt
  have hconst : ∀ x y : ℝ, (u x - v x) * HedenmalmQuantile.sourceChar z x
      = (u y - v y) * HedenmalmQuantile.sourceChar z y :=
    is_const_of_deriv_eq_zero hdiff (fun x => (hzero x).deriv)
  have hallzero : ∀ x : ℝ, (u x - v x) * HedenmalmQuantile.sourceChar z x = 0 := by
    intro x
    have hc : Filter.Tendsto
        (fun _ : ℝ => (u x - v x) * HedenmalmQuantile.sourceChar z x) Filter.atBot
        (nhds ((u x - v x) * HedenmalmQuantile.sourceChar z x)) := tendsto_const_nhds
    have hc' := hbot.congr (fun y => hconst y x)
    exact tendsto_nhds_unique hc hc'
  intro x
  have hne : HedenmalmQuantile.sourceChar z x ≠ 0 := Complex.exp_ne_zero _
  have := hallzero x
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hne


end HedenmalmPrimeTranslation

end

end RHTower
