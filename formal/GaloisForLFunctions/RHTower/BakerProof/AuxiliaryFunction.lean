import GaloisForLFunctions.RHTower.BakerProof.AuxiliaryMatrix
import GaloisForLFunctions.Hurwitz.ExpIndependence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The analytic face of the Baker auxiliary construction

The Siegel-kernel coefficients define an exponential polynomial.  Normalizing the assumed
logarithmic relation rewrites every frequency in the non-pivot directions.  The matrix kernel kills
each multinomial coefficient separately, so all derivatives of order below the row cutoff vanish at
every selected integer sample.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerProof

noncomputable def Relation.frequency (R : Relation) {L : ℕ} (m : R.Column L) : ℂ :=
  ∑ i, ((m i : ℕ) : ℂ) * ((Real.log (R.p i) : ℝ) : ℂ)

/-- Distinct exponent vectors have distinct logarithmic frequencies.  A collision would give an
integer linear relation among the logarithms of the distinct primes in `R`, contradicting the
unconditional integer fragment of Baker's statement. -/
theorem Relation.frequency_injective (R : Relation) {L : ℕ} :
    Function.Injective (R.frequency (L := L)) := by
  intro m₁ m₂ hfrequency
  have hrelC :
      ∑ i, (((m₁ i : ℕ) : ℤ) - ((m₂ i : ℕ) : ℤ) : ℂ) *
        ((Real.log (R.p i) : ℝ) : ℂ) = 0 := by
    calc
      _ = ∑ i, (((m₁ i : ℕ) : ℂ) * ((Real.log (R.p i) : ℝ) : ℂ) -
          ((m₂ i : ℕ) : ℂ) * ((Real.log (R.p i) : ℝ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        push_cast
        ring
      _ = R.frequency m₁ - R.frequency m₂ := by
        rw [Finset.sum_sub_distrib]
        rfl
      _ = 0 := sub_eq_zero.mpr hfrequency
  have hrelR :
      ∑ i, ((((m₁ i : ℕ) : ℤ) - ((m₂ i : ℕ) : ℤ) : ℤ) : ℝ) *
        Real.log (R.p i) = 0 := by
    apply Complex.ofReal_injective
    simpa using hrelC
  have hcoord := baker_intFragment_unconditional R.p R.p_injective R.p_prime
    (fun i => ((m₁ i : ℕ) : ℤ) - ((m₂ i : ℕ) : ℤ)) hrelR
  funext i
  apply Fin.ext
  have hi : ((m₁ i : ℕ) : ℤ) = ((m₂ i : ℕ) : ℤ) := sub_eq_zero.mp (hcoord i)
  exact_mod_cast hi

@[simp] theorem Relation.coeffEmbedding_scaledCoeff (R : Relation) (c : ℤ) (i : Fin R.n) :
    R.coeffEmbedding (R.scaledCoeff c i) = (c : ℂ) * R.coeff i := by
  simp [Relation.scaledCoeff]

@[simp] theorem Relation.coeffEmbedding_scaledDirection (R : Relation) (c : ℤ)
    (pivot : Fin R.n) {L : ℕ} (m : R.Column L) (i : Fin R.n) :
    R.coeffEmbedding (R.scaledDirection c pivot m i) =
      (c : ℂ) * R.coeff pivot * (m i : ℕ) -
        (m pivot : ℕ) * ((c : ℂ) * R.coeff i) := by
  simp [Relation.scaledDirection]

private theorem sum_nonPivot_eq_sum_erase (R : Relation) (pivot : Fin R.n)
    (f : Fin R.n → ℂ) :
    (∑ i : R.NonPivot pivot, f i) = ∑ i ∈ Finset.univ.erase pivot, f i := by
  exact (Finset.sum_subtype (Finset.univ.erase pivot) (by simp) f).symm

/-- Multiplying a frequency by the scaled pivot coefficient rewrites it as a linear combination in
the non-pivot algebraic directions. -/
theorem Relation.scaled_frequency_eq (R : Relation) (c : ℤ) (pivot : Fin R.n)
    {L : ℕ} (m : R.Column L) :
    R.coeffEmbedding (R.scaledCoeff c pivot) * R.frequency m =
      ∑ i : R.NonPivot pivot,
        R.coeffEmbedding (R.scaledDirection c pivot m i) *
          ((Real.log (R.p i) : ℝ) : ℂ) := by
  let logp : Fin R.n → ℂ := fun i => ((Real.log (R.p i) : ℝ) : ℂ)
  have hpivot := R.pivot_log_eq pivot
  change logp pivot = -∑ i ∈ Finset.univ.erase pivot,
    R.coeffEmbedding (R.normalizedCoeff pivot i) * logp i at hpivot
  rw [sum_nonPivot_eq_sum_erase R pivot (fun i =>
    R.coeffEmbedding (R.scaledDirection c pivot m i) * logp i)]
  simp only [Relation.frequency, Relation.coeffEmbedding_scaledCoeff,
    Relation.coeffEmbedding_scaledDirection]
  rw [show (∑ i, ((m i : ℕ) : ℂ) * logp i) =
      (∑ i ∈ Finset.univ.erase pivot, ((m i : ℕ) : ℂ) * logp i) +
        ((m pivot : ℕ) : ℂ) * logp pivot by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]]
  rw [hpivot]
  simp only [mul_add, mul_neg, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [R.coeffEmbedding_normalizedCoeff]
  field_simp [R.coeff_ne_zero pivot]
  ring

noncomputable def Relation.integralCoeffEmbedding (R : Relation) :
    𝓞 R.CoefficientField →+* ℂ :=
  R.coeffEmbedding.comp (algebraMap (𝓞 R.CoefficientField) R.CoefficientField)

/-- The finite exponential polynomial attached to a Siegel-kernel coefficient vector. -/
noncomputable def Relation.auxiliaryFunction (R : Relation) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (z : ℂ) : ℂ :=
  ∑ m, R.integralCoeffEmbedding (η m) * Complex.exp (R.frequency m * z)

/-- A nonzero Siegel-kernel vector gives a genuinely nonzero auxiliary exponential polynomial.
This is the Vandermonde independence of exponentials, after `frequency_injective` rules out
colliding frequencies. -/
theorem Relation.auxiliaryFunction_ne_zero (R : Relation) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (hη : η ≠ 0) :
    R.auxiliaryFunction η ≠ 0 := by
  let e : Fin (Fintype.card (R.Column L)) ≃ R.Column L := (Fintype.equivFin _).symm
  have hfreq : Function.Injective (fun k => R.frequency (e k)) :=
    R.frequency_injective.comp e.injective
  have hLI := HurwitzExp.expLin_linearIndependent hfreq
  have hsum : ∑ k, R.integralCoeffEmbedding (η (e k)) •
      (fun z : ℂ => Complex.exp (R.frequency (e k) * z)) ≠ 0 := by
    intro hzero
    have hcoeff := Fintype.linearIndependent_iff.mp hLI
      (fun k => R.integralCoeffEmbedding (η (e k))) hzero
    apply hη
    funext m
    let k := e.symm m
    have hk := hcoeff k
    have he : e k = m := e.apply_symm_apply m
    change R.integralCoeffEmbedding (η (e k)) = 0 at hk
    rw [he] at hk
    have hkK : algebraMap (𝓞 R.CoefficientField) R.CoefficientField (η m) = 0 := by
      apply R.coeffEmbedding.injective
      simpa [Relation.integralCoeffEmbedding] using hk
    apply Subtype.ext
    exact hkK
  intro haux
  apply hsum
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  have hz := congrFun haux z
  change (∑ m, R.integralCoeffEmbedding (η m) *
    Complex.exp (R.frequency m * z)) = 0 at hz
  change (∑ k, R.integralCoeffEmbedding (η (e k)) *
    Complex.exp (R.frequency (e k) * z)) = 0
  calc
    _ = ∑ m, R.integralCoeffEmbedding (η m) *
        Complex.exp (R.frequency m * z) :=
      e.sum_comp (fun m => R.integralCoeffEmbedding (η m) *
        Complex.exp (R.frequency m * z))
    _ = 0 := hz

theorem Relation.iteratedDeriv_auxiliaryFunction (R : Relation) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (R.auxiliaryFunction η) z =
      ∑ m, R.integralCoeffEmbedding (η m) *
        R.frequency m ^ k * Complex.exp (R.frequency m * z) := by
  unfold Relation.auxiliaryFunction
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [iteratedDeriv_const_mul_field]
    rw [congrFun (iteratedDeriv_cexp_const_mul k (R.frequency m)) z]
    ring
  · intro m hm
    fun_prop

@[simp] theorem Relation.coeffEmbedding_sampleFactor (R : Relation) {L S : ℕ}
    (sample : Fin S) (m : R.Column L) :
    R.coeffEmbedding (R.sampleFactor sample m) =
      ∏ i, ((R.p i : ℕ) : ℂ) ^ ((m i : ℕ) * (sample : ℕ)) := by
  simp [Relation.sampleFactor]

theorem Relation.exp_frequency_nat (R : Relation) {L S : ℕ}
    (sample : Fin S) (m : R.Column L) :
    Complex.exp (R.frequency m * (sample : ℕ)) =
      ∏ i, ((R.p i : ℕ) : ℂ) ^ ((m i : ℕ) * (sample : ℕ)) := by
  rw [Relation.frequency, Finset.sum_mul, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [show ((m i : ℕ) : ℂ) * ((Real.log (R.p i) : ℝ) : ℂ) * (sample : ℕ) =
      (((m i : ℕ) * (sample : ℕ) : ℕ) : ℂ) * Complex.log (R.p i) by
    rw [← Complex.natCast_log]
    push_cast
    ring]
  rw [Complex.exp_nat_mul, Complex.exp_log]
  exact_mod_cast (R.p_prime i).ne_zero

@[simp] theorem Relation.coeffEmbedding_auxiliaryEntry (R : Relation) (c : ℤ)
    (pivot : Fin R.n) {L S T : ℕ} (row : R.Row pivot S T) (m : R.Column L) :
    R.coeffEmbedding (R.auxiliaryEntry c pivot row m) =
      (∏ i : R.NonPivot pivot,
        R.coeffEmbedding (R.scaledDirection c pivot m i) ^ (row.2 i : ℕ)) *
        Complex.exp (R.frequency m * (row.1 : ℕ)) := by
  rw [Relation.auxiliaryEntry, map_mul, map_prod, R.coeffEmbedding_sampleFactor,
    R.exp_frequency_nat]
  simp

theorem Relation.mapped_auxiliary_kernel (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (row : R.Row pivot S T) :
    ∑ m, R.coeffEmbedding (R.auxiliaryEntry c pivot row m) *
      R.integralCoeffEmbedding (η m) = 0 := by
  have hrow := congrFun hker row
  apply_fun R.integralCoeffEmbedding at hrow
  simpa [Matrix.mulVec, dotProduct, Relation.integralCoeffEmbedding,
    Relation.auxiliaryMatrix, map_sum, map_mul] using hrow

theorem Relation.auxiliary_kernel_row_eq (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (row : R.Row pivot S T) :
    ∑ m, (∏ i : R.NonPivot pivot,
      R.coeffEmbedding (R.scaledDirection c pivot m i) ^ (row.2 i : ℕ)) *
      R.integralCoeffEmbedding (η m) *
      Complex.exp (R.frequency m * (row.1 : ℕ)) = 0 := by
  have h := R.mapped_auxiliary_kernel c hint pivot η hker row
  simpa [R.coeffEmbedding_auxiliaryEntry, mul_assoc, mul_left_comm, mul_comm] using h

theorem Relation.auxiliary_kernel_multiIndex_eq (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (sample : Fin S) (k : ℕ) (hk : k < T)
    (ν : R.NonPivot pivot → ℕ) (hν : ν ∈ Finset.piAntidiag Finset.univ k) :
    ∑ m, (∏ i : R.NonPivot pivot,
      R.coeffEmbedding (R.scaledDirection c pivot m i) ^ ν i) *
      R.integralCoeffEmbedding (η m) *
      Complex.exp (R.frequency m * (sample : ℕ)) = 0 := by
  have hνsum : ∑ i, ν i = k := (Finset.mem_piAntidiag.mp hν).1
  have hνlt : ∀ i, ν i < T := by
    intro i
    apply lt_of_le_of_lt _ hk
    rw [← hνsum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let row : R.Row pivot S T := ⟨sample, fun i => ⟨ν i, hνlt i⟩⟩
  have hrow := R.auxiliary_kernel_row_eq c hint pivot η hker row
  simpa [row] using hrow

/-- **High-order vanishing bridge.**  Every derivative below the cutoff `T` of the auxiliary
exponential polynomial vanishes at every selected integer sample. -/
theorem Relation.auxiliaryFunction_iteratedDeriv_eq_zero (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (sample : Fin S) (k : ℕ) (hk : k < T) :
    iteratedDeriv k (R.auxiliaryFunction η) (sample : ℕ) = 0 := by
  let a : ℂ := R.coeffEmbedding (R.scaledCoeff c pivot)
  let D : R.Column L → R.NonPivot pivot → ℂ := fun m i =>
    R.coeffEmbedding (R.scaledDirection c pivot m i)
  let logp : R.NonPivot pivot → ℂ := fun i => ((Real.log (R.p i) : ℝ) : ℂ)
  have ha : a ≠ 0 := by
    simp only [a, R.coeffEmbedding_scaledCoeff]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hc) (R.coeff_ne_zero pivot)
  apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero k ha)
  rw [R.iteratedDeriv_auxiliaryFunction, Finset.mul_sum]
  calc
    ∑ m, a ^ k * (R.integralCoeffEmbedding (η m) * R.frequency m ^ k *
        Complex.exp (R.frequency m * (sample : ℕ))) =
        ∑ m, R.integralCoeffEmbedding (η m) *
          (∑ i : R.NonPivot pivot, D m i * logp i) ^ k *
          Complex.exp (R.frequency m * (sample : ℕ)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [← R.scaled_frequency_eq c pivot m]
      simp only [a]
      ring
    _ = ∑ m, R.integralCoeffEmbedding (η m) *
          (∑ ν ∈ Finset.piAntidiag (Finset.univ : Finset (R.NonPivot pivot)) k,
            (Nat.multinomial Finset.univ ν : ℂ) *
              ∏ i, (D m i * logp i) ^ ν i) *
          Complex.exp (R.frequency m * (sample : ℕ)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_pow_eq_sum_piAntidiag]
    _ = ∑ ν ∈ Finset.piAntidiag (Finset.univ : Finset (R.NonPivot pivot)) k,
          (Nat.multinomial Finset.univ ν : ℂ) * (∏ i, logp i ^ ν i) *
            (∑ m, (∏ i, D m i ^ ν i) * R.integralCoeffEmbedding (η m) *
              Complex.exp (R.frequency m * (sample : ℕ))) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ν hν
      apply Finset.sum_congr rfl
      intro m hm
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib]
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro ν hν
      rw [R.auxiliary_kernel_multiIndex_eq c hint pivot η hker sample k hk ν hν]
      ring

end GaloisForLFunctions.RHTower.BakerProof
