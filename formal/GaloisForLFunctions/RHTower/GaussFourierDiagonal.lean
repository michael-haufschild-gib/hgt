import GaloisForLFunctions.RHTower.GaussIterateInner
import GaloisForLFunctions.RHTower.GaussComponentAmplitude

/-!
# The Fourier diagonal of the quasi-inner block is the principal diagonal model

The diagonal block of the source reduction carries the full vertical Gauss component, whose modulus
is the archimedean prefactor times the modulus of the Gamma ratio.  Scaling the diagonal by that
prefactor scales the quasi-inner block by its square, hence its `m`-th power by the archimedean
constant, which is exactly the constant relating the sampled value to the sampled energy.

Together with the reflection symmetry of the lattice — the sampled value conjugates and the sampled
phase is unchanged — the two-sided Fourier diagonal of `G^m` is asymptotically the principal
diagonal model whose exact logarithmic mean is already known.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

/-! ## The archimedean prefactor -/

/-- The archimedean prefactor `(π/m)^{1/(2m)}` of a Gauss component. -/
def gaussArchScale (m : ℕ) : ℝ := (Real.pi / (m : ℝ)) ^ gaussComponentDelta m

theorem gaussArchScale_pos {m : ℕ} (hm : 1 ≤ m) : 0 < gaussArchScale m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hbase : (0 : ℝ) < Real.pi / (m : ℝ) := by positivity
  exact Real.rpow_pos_of_pos hbase _

theorem gaussArchScale_pow (m : ℕ) : gaussArchScale m ^ (2 * m) = gaussArchConst m := rfl

/-! ## The diagonal with the full component symbol -/

/-- The diagonal block whose symbol is the full vertical Gauss component. -/
def gaussDiagonalBlockFull {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ((gaussArchScale m : ℝ) : ℂ) • gaussDiagonalBlock hm k p

/-- The conjugate of the full diagonal block. -/
def gaussDiagonalBlockFullStar {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ((gaussArchScale m : ℝ) : ℂ) • gaussDiagonalBlockStar hm k p

/-- The exponential monomials are eigenvectors of the full diagonal block, with the full sampled
component as eigenvalue. -/
theorem gaussDiagonalBlockFull_fourierLp {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (j : ℤ) :
    gaussDiagonalBlockFull hm k p (fourierLp 2 j)
      = (((gaussArchScale m : ℝ) : ℂ) * gaussSampleValue k p j) • fourierLp 2 j := by
  rw [gaussDiagonalBlockFull, smul_apply,
    gaussDiagonalBlock_fourierLp, smul_smul]

/-- The modulus of the full sampled component is the sampled magnitude. -/
theorem norm_gaussSampleValueFull_pow {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {i : ℤ} (hi : i ≠ 0) :
    gaussArchScale m ^ (2 * m) * ‖gaussSampleValue k p i‖ ^ (2 * m)
      = gaussComponentPrimeMagnitudeEnergy k p (i.natAbs - 1) := by
  rw [gaussArchScale_pow]
  exact norm_gaussSampleValue_pow_eq hm k p hi

/-! ## The card's quasi-inner block -/

/-- `G = p B D B^{-2} D* B` with the full diagonal. -/
def gaussQuasiInnerGFull {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ((p : ℝ) : ℂ) •
    (gaussPrimeScaleBlock (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt) ∘L
      gaussDiagonalBlockFull hm k p ∘L
        gaussPrimeScaleInvSqBlock (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt) ∘L
          gaussDiagonalBlockFullStar hm k p ∘L
            gaussPrimeScaleBlock (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt))

/-- Scaling the diagonal scales the quasi-inner block by the square of the scale. -/
theorem gaussQuasiInnerGFull_eq {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    gaussQuasiInnerGFull hm k p
      = ((gaussArchScale m ^ 2 : ℝ) : ℂ) • gaussQuasiInnerG hm k p := by
  rw [gaussQuasiInnerGFull, gaussQuasiInnerG, gaussDiagonalBlockFull,
    gaussDiagonalBlockFullStar]
  simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, smul_smul]
  congr 1
  push_cast
  ring

theorem gaussQuasiInnerGFull_pow {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (r : ℕ) :
    gaussQuasiInnerGFull hm k p ^ r
      = ((gaussArchScale m ^ (2 * r) : ℝ) : ℂ) • gaussQuasiInnerG hm k p ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, ih, gaussQuasiInnerGFull_eq, pow_succ (gaussQuasiInnerG hm k p),
        smul_mul_smul_comm]
      congr 1
      push_cast
      ring

theorem inner_gaussQuasiInnerGFull_pow {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (r : ℕ) (i : ℤ) :
    (inner ℂ (fourierLp 2 i) ((gaussQuasiInnerGFull hm k p ^ r) (fourierLp 2 i)) : ℂ)
      = ((gaussArchScale m ^ (2 * r) : ℝ) : ℂ) *
        inner ℂ (fourierLp 2 i) ((gaussQuasiInnerG hm k p ^ r) (fourierLp 2 i)) := by
  rw [gaussQuasiInnerGFull_pow, smul_apply, inner_smul_right]

/-! ## The amplitude and phase bridges -/

theorem gaussAmplitudeCircle_apply_coe (p : ℝ) (m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    gaussAmplitudeCircle p m ((x : ℝ) : AddCircle (1 : ℝ)) = gaussAmplitudeSegment p m x := by
  simp only [gaussAmplitudeCircle, ContinuousMap.coe_mk]
  exact AddCircle.liftIoc_coe_apply hx

theorem gaussAmplitudeCircle_coe (p : ℝ) (m : ℕ) (s : ℝ) :
    gaussAmplitudeCircle p m ((s : ℝ) : AddCircle (1 : ℝ))
      = gaussAmplitudeSegment p m (Int.fract s) := by
  by_cases h0 : Int.fract s = 0
  · have hcoe : ((s : ℝ) : AddCircle (1 : ℝ)) = ((1 : ℝ) : AddCircle (1 : ℝ)) := by
      rw [← coe_fract_eq s, h0]
      have hper : ((0 + 1 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) :=
        AddCircle.coe_add_period 1 0
      rw [← hper]
      norm_num
    rw [hcoe, h0, gaussAmplitudeSegment_zero]
    rw [gaussAmplitudeCircle_apply_coe p m (by norm_num : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) (0 + 1)),
      gaussAmplitudeSegment_one]
  · have hmem : Int.fract s ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
      constructor
      · exact lt_of_le_of_ne (Int.fract_nonneg s) (Ne.symm h0)
      · simpa using (Int.fract_lt_one s).le
    rw [← coe_fract_eq s]
    exact gaussAmplitudeCircle_apply_coe p m hmem

theorem gaussComponentPhasePoint_eq (m : ℕ) (p : Nat.Primes) (n : ℕ) :
    gaussComponentPhasePoint m p n
      = ((gaussSamplePhase m p ((n : ℤ) + 1) : ℝ) : AddCircle (1 : ℝ)) := by
  rw [gaussComponentPhasePoint, gaussSamplePhase_natSucc]

/-! ## The two-sided Fourier diagonal -/

theorem gaussStepScalar_pow_eq {m : ℕ} (k : Fin m) (p : Nat.Primes) (i : ℤ) (r : ℕ) :
    ((((p : ℝ) : ℂ) *
        (starRingEnd ℂ (gaussSampleValue k p i) * gaussSampleValue k p i)) ^ r)
      = (((p : ℝ) ^ r * ‖gaussSampleValue k p i‖ ^ (2 * r) : ℝ) : ℂ) := by
  have hconj : starRingEnd ℂ (gaussSampleValue k p i) * gaussSampleValue k p i
      = ((‖gaussSampleValue k p i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [hconj, ← Complex.ofReal_mul, ← Complex.ofReal_pow]
  congr 1
  rw [mul_pow, ← pow_mul]

/-- **The principal diagonal model is the doubled scaled step scalar times the amplitude
average.**  Both frequencies `±(n+1)` contribute the same value. -/
theorem gaussPrincipalDiagonalTerm_eq {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (n : ℕ) :
    ((gaussArchScale m ^ (2 * m) : ℝ) : ℂ) *
        ((((p : ℝ) : ℂ) * (starRingEnd ℂ (gaussSampleValue k p ((n : ℤ) + 1)) *
              gaussSampleValue k p ((n : ℤ) + 1))) ^ m *
            ((gaussAmplitudeSegment (p : ℝ) m
              (Int.fract (gaussSamplePhase m p ((n : ℤ) + 1))) : ℝ) : ℂ) +
          (((p : ℝ) : ℂ) * (starRingEnd ℂ (gaussSampleValue k p ((n : ℤ) + 1)) *
              gaussSampleValue k p ((n : ℤ) + 1))) ^ m *
            ((gaussAmplitudeSegment (p : ℝ) m
              (Int.fract (gaussSamplePhase m p ((n : ℤ) + 1))) : ℝ) : ℂ))
      = gaussPrincipalDiagonalTerm k p n := by
  have hine : ((n : ℤ) + 1) ≠ 0 := by omega
  have henergy : gaussArchScale m ^ (2 * m) *
      ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m)
      = gaussComponentPrimeMagnitudeEnergy k p n := by
    have h := norm_gaussSampleValueFull_pow hm k p hine
    rwa [show ((n : ℤ) + 1).natAbs - 1 = n by omega] at h
  have hamp : gaussAmplitudeCircleComplex (p : ℝ) m (gaussComponentPhasePoint m p n)
      = ((gaussAmplitudeSegment (p : ℝ) m
          (Int.fract (gaussSamplePhase m p ((n : ℤ) + 1))) : ℝ) : ℂ) := by
    rw [gaussAmplitudeCircleComplex_apply, gaussComponentPhasePoint_eq,
      gaussAmplitudeCircle_coe]
  rw [gaussPrincipalDiagonalTerm, hamp, gaussStepScalar_pow_eq, ← henergy]
  push_cast
  ring

/-- **The Fourier diagonal of the iterated quasi-inner block is the principal diagonal model.**
Summing the two frequencies `±(n+1)` produces exactly the two-sided principal diagonal term. -/
theorem tendsto_gaussFourierDiagonal {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun n : ℕ =>
      ((inner ℂ (fourierLp 2 ((n : ℤ) + 1))
            ((gaussQuasiInnerGFull hm k p ^ m) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
          inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
            ((gaussQuasiInnerGFull hm k p ^ m) (fourierLp 2 (-((n : ℤ) + 1))))) -
        gaussPrincipalDiagonalTerm k p n) atTop (nhds 0) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hιp : Tendsto (fun n : ℕ => (((n : ℤ) + 1)).natAbs) atTop atTop := by
    refine (Filter.tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have hιm : Tendsto (fun n : ℕ => ((-((n : ℤ) + 1))).natAbs) atTop atTop := by
    refine (Filter.tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have h1 := tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_gaussIterateInner hm k p hp hιp m)
  have h2 := tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_gaussIterateInner hm k p hp hιm m)
  have hsum := (h1.add h2).const_mul ((gaussArchScale m ^ (2 * m) : ℝ) : ℂ)
  rw [add_zero, mul_zero] at hsum
  refine hsum.congr fun n => ?_
  set i : ℤ := (n : ℤ) + 1 with hi
  have hine : i ≠ 0 := by omega
  set σ : ℂ := ((p : ℝ) : ℂ) *
    (starRingEnd ℂ (gaussSampleValue k p i) * gaussSampleValue k p i) with hσ
  set S : ℝ := gaussAmplitudeSegment (p : ℝ) m (Int.fract (gaussSamplePhase m p i)) with hS
  -- the negative frequency has the same scalar and the same phase
  have hvalneg : ‖gaussSampleValue k p (-i)‖ = ‖gaussSampleValue k p i‖ := by
    rw [gaussSampleValue_neg, RCLike.norm_conj]
  have hscalneg : ((((p : ℝ) : ℂ) *
      (starRingEnd ℂ (gaussSampleValue k p (-i)) * gaussSampleValue k p (-i))) ^ m)
      = σ ^ m := by
    rw [hσ, gaussStepScalar_pow_eq, gaussStepScalar_pow_eq, hvalneg]
  have hphaseneg : gaussSamplePhase m p (-i) = gaussSamplePhase m p i :=
    gaussSamplePhase_neg m p i
  -- the two limits sum to the principal diagonal term
  have hpdt : ((gaussArchScale m ^ (2 * m) : ℝ) : ℂ) * (σ ^ m * ((S : ℝ) : ℂ) +
      σ ^ m * ((S : ℝ) : ℂ)) = gaussPrincipalDiagonalTerm k p n := by
    rw [hσ, hS, hi]
    exact gaussPrincipalDiagonalTerm_eq hm k p n
  rw [inner_gaussQuasiInnerGFull_pow, inner_gaussQuasiInnerGFull_pow, ← hpdt,
    hscalneg, hphaseneg]
  ring

end

end RHTower
