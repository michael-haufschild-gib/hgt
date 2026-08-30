import GaloisForLFunctions.RHTower.CCMSqrtTwoDyadicCyclotomicIntersection

/-!
# Finite determinant closure of the CCM dyadic cyclotomic ring

The coefficientwise part of Connes--Consani--Moscovici Theorem 5.6 places
the literal Lambert entries in `ℤ^cyc[1/2]`.  The finite determinant step in
the same theorem must preserve that coefficient ring before the distinct
source-specific `ℚ(√2)`-similarity is invoked.

This file makes that finite algebraic step unconditional.  It realizes
`ℤ^cyc[1/2]` as a literal subring of `ℂ`, lifts a coefficientwise-contained
power series matrix to that subring, and descends its determinant.  The final
bridge applies this to finite packets of the literal CCM Lambert system.

It constructs the unconditional finite equation-(53) parity-block `q`-matrix
using its source-selected nonnegative real square roots.  The distinct paper identity identifying it with
the parity restrictions of `𝒟ₙ(0)⁻¹𝓔ₙ(q)` over `ℚ(√2)` remains a separate
source-specific obligation.
-/

namespace RHTower

noncomputable section

open QuantumAlg.QubitTwoDesign

theorem CCMDyadicCyclotomicInteger.zero : CCMDyadicCyclotomicInteger (0 : ℂ) :=
  ⟨0, by simpa using CCMCyclotomicInteger.zero⟩

theorem CCMDyadicCyclotomicInteger.one : CCMDyadicCyclotomicInteger (1 : ℂ) :=
  ⟨0, by simpa using CCMCyclotomicInteger.one⟩

theorem CCMDyadicCyclotomicInteger.neg {z : ℂ}
    (hz : CCMDyadicCyclotomicInteger z) : CCMDyadicCyclotomicInteger (-z) := by
  rcases hz with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  rw [mul_neg]
  exact hd.neg

theorem CCMDyadicCyclotomicInteger.mul {x y : ℂ}
    (hx : CCMDyadicCyclotomicInteger x) (hy : CCMDyadicCyclotomicInteger y) :
    CCMDyadicCyclotomicInteger (x * y) := by
  rcases hx with ⟨d, hd⟩
  rcases hy with ⟨e, he⟩
  refine ⟨d + e, ?_⟩
  rw [pow_add]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hd.mul he

/-- The concrete dyadically localized cyclotomic integer ring. -/
def ccmDyadicCyclotomicSubring : Subring ℂ where
  carrier := {z | CCMDyadicCyclotomicInteger z}
  zero_mem' := CCMDyadicCyclotomicInteger.zero
  one_mem' := CCMDyadicCyclotomicInteger.one
  add_mem' := CCMDyadicCyclotomicInteger.add
  mul_mem' := CCMDyadicCyclotomicInteger.mul
  neg_mem' := CCMDyadicCyclotomicInteger.neg

/-- Inclusion of the literal dyadic cyclotomic subring in `ℂ`. -/
def ccmDyadicCyclotomicInclusion : ccmDyadicCyclotomicSubring →+* ℂ :=
  SubringClass.subtype ccmDyadicCyclotomicSubring

/-- Lift a power series whose coefficients lie in the dyadic cyclotomic ring. -/
def ccmDyadicCyclotomicSeriesLift (f : PowerSeries ℂ)
    (hf : ∀ n, CCMDyadicCyclotomicInteger (f.coeff n)) :
    PowerSeries ccmDyadicCyclotomicSubring :=
  PowerSeries.mk fun n => ⟨f.coeff n, hf n⟩

theorem ccmDyadicCyclotomicSeriesLift_map (f : PowerSeries ℂ)
    (hf : ∀ n, CCMDyadicCyclotomicInteger (f.coeff n)) :
    PowerSeries.map ccmDyadicCyclotomicInclusion
      (ccmDyadicCyclotomicSeriesLift f hf) = f := by
  ext n
  rw [PowerSeries.coeff_map]
  simp [ccmDyadicCyclotomicInclusion, ccmDyadicCyclotomicSeriesLift]

/-- Every coefficient of a finite determinant of dyadic-cyclotomic power
series entries is again dyadic-cyclotomic. -/
theorem ccmDyadicCyclotomic_det_coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (PowerSeries ℂ))
    (hM : ∀ i j n, CCMDyadicCyclotomicInteger ((M i j).coeff n)) (n : ℕ) :
    CCMDyadicCyclotomicInteger (M.det.coeff n) := by
  let M' : Matrix ι ι (PowerSeries ccmDyadicCyclotomicSubring) := fun i j =>
    ccmDyadicCyclotomicSeriesLift (M i j) (hM i j)
  have hmap : M'.map (PowerSeries.map ccmDyadicCyclotomicInclusion) = M := by
    ext i j n
    change (PowerSeries.map ccmDyadicCyclotomicInclusion (M' i j)).coeff n =
      (M i j).coeff n
    rw [PowerSeries.coeff_map]
    simp [M', ccmDyadicCyclotomicInclusion, ccmDyadicCyclotomicSeriesLift]
  have hdet : PowerSeries.map ccmDyadicCyclotomicInclusion M'.det = M.det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det hmap
  rw [← hdet]
  change CCMDyadicCyclotomicInteger
    (ccmDyadicCyclotomicInclusion (M'.det.coeff n))
  exact (M'.det.coeff n).property

/-- The source-selected nonnegative square root in CCM equation (53). -/
def ccmLambertCanonicalRadical (ell i j : ℕ) : ℂ :=
  (Real.sqrt (ccmLambertRadicand ell i j) : ℂ)

theorem ccmLambertCanonicalRadical_sq (ell i j : ℕ) :
    (ccmLambertCanonicalRadical ell i j) ^ 2 = (ccmLambertRadicand ell i j : ℂ) := by
  have hrad : 0 ≤ (ccmLambertRadicand ell i j : ℝ) := by
    exact_mod_cast mul_nonneg (ccmFiniteSemilocalSigma_nonneg ell i)
      (ccmFiniteSemilocalSigma_nonneg ell j)
  rw [ccmLambertCanonicalRadical, ← Complex.ofReal_pow, Real.sq_sqrt hrad]
  norm_cast

/-- The literal finite CCM `q`-matrix at depth `N`: equation (53) on each
parity block, and zero across the two blocks.  Thus it is the concrete finite
presentation of `𝒜_n⁺(q) ⊕ 𝒜_n⁻(q)` used in Theorem 5.6. -/
def ccmLambertFiniteMatrix (N : ℕ) (rad : ℕ → ℕ → ℕ → ℂ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℂ) :=
  fun i j => if (i : ℕ) % 2 = (j : ℕ) % 2 then
    ccmLambertEntrySeries i j (rad i j) else 0

theorem ccmLambertFiniteMatrix_coeff_literal_dyadicCyclotomic (N : ℕ)
    (rad : ℕ → ℕ → ℕ → ℂ)
    (hrad : ∀ i j ell, (rad i j ell) ^ 2 = (ccmLambertRadicand ell i j : ℂ))
    (i j : Fin N) (n : ℕ) :
    CCMDyadicCyclotomicInteger ((ccmLambertFiniteMatrix N rad i j).coeff n) := by
  unfold ccmLambertFiniteMatrix
  split_ifs with hpar
  · exact ccmLambertEntrySeries_coeff_literal_dyadicCyclotomic i j n (rad i j)
      (hrad i j)
  · exact CCMDyadicCyclotomicInteger.zero

/-- The finite determinant of literal CCM Lambert entries satisfies the
coefficientwise `ℤ^cyc[1/2]` containment. -/
theorem ccmLambertFiniteMatrix_det_coeff_literal_dyadicCyclotomic (N : ℕ)
    (rad : ℕ → ℕ → ℕ → ℂ)
    (hrad : ∀ i j ell, (rad i j ell) ^ 2 = (ccmLambertRadicand ell i j : ℂ)) (n : ℕ) :
    CCMDyadicCyclotomicInteger ((ccmLambertFiniteMatrix N rad).det.coeff n) := by
  apply ccmDyadicCyclotomic_det_coeff
  intro i j k
  exact ccmLambertFiniteMatrix_coeff_literal_dyadicCyclotomic N rad hrad i j k

/-- The unconditional finite CCM `q`-matrix obtained with its source-selected
nonnegative radicals. -/
def ccmActualFiniteQMatrix (N : ℕ) : Matrix (Fin N) (Fin N) (PowerSeries ℂ) :=
  ccmLambertFiniteMatrix N (fun i j ell => ccmLambertCanonicalRadical ell i j)

theorem ccmActualFiniteQMatrix_coeff_dyadicCyclotomic (N : ℕ)
    (i j : Fin N) (n : ℕ) :
    CCMDyadicCyclotomicInteger ((ccmActualFiniteQMatrix N i j).coeff n) := by
  exact ccmLambertFiniteMatrix_coeff_literal_dyadicCyclotomic N
    (fun i j ell => ccmLambertCanonicalRadical ell i j)
    (fun i j ell => ccmLambertCanonicalRadical_sq ell i j) i j n

theorem ccmActualFiniteQMatrix_det_coeff_dyadicCyclotomic (N n : ℕ) :
    CCMDyadicCyclotomicInteger ((ccmActualFiniteQMatrix N).det.coeff n) := by
  exact ccmLambertFiniteMatrix_det_coeff_literal_dyadicCyclotomic N
    (fun i j ell => ccmLambertCanonicalRadical ell i j)
    (fun i j ell => ccmLambertCanonicalRadical_sq ell i j) n

/-- The literal CCM `q`-matrix has no constant term. -/
theorem ccmActualFiniteQMatrix_coeff_zero (N : ℕ) (i j : Fin N) :
    (ccmActualFiniteQMatrix N i j).coeff 0 = 0 := by
  unfold ccmActualFiniteQMatrix ccmLambertFiniteMatrix
  split_ifs with hpar
  · exact ccmLambertEntrySeries_coeff_zero i j _
  · rfl

/-- The finite determinant `det(I + 𝒜ₙ(q))` of CCM Lemma 5.1.  This is the
generating determinant for the exterior traces; its identification with the
normalized moment determinant is a separate source theorem. -/
def ccmActualFiniteQNormalizedDeterminant (N : ℕ) : PowerSeries ℂ :=
  ((1 : Matrix (Fin N) (Fin N) (PowerSeries ℂ)) + ccmActualFiniteQMatrix N).det

theorem ccmActualFiniteQNormalizedDeterminant_coeff_dyadicCyclotomic (N n : ℕ) :
    CCMDyadicCyclotomicInteger
      ((ccmActualFiniteQNormalizedDeterminant N).coeff n) := by
  unfold ccmActualFiniteQNormalizedDeterminant
  apply ccmDyadicCyclotomic_det_coeff
  intro i j k
  rw [Matrix.add_apply, map_add]
  apply CCMDyadicCyclotomicInteger.add
  · by_cases hij : i = j
    · subst j
      by_cases hk : k = 0
      · subst k
        simpa using CCMDyadicCyclotomicInteger.one
      · simpa [hk] using CCMDyadicCyclotomicInteger.zero
    · simpa [Matrix.one_apply, hij] using CCMDyadicCyclotomicInteger.zero
  · exact ccmActualFiniteQMatrix_coeff_dyadicCyclotomic N i j k

/-- The literal finite CCM normalized determinant has constant coefficient
one, as required by the Lambert deformation. -/
theorem ccmActualFiniteQNormalizedDeterminant_coeff_zero (N : ℕ) :
    (ccmActualFiniteQNormalizedDeterminant N).coeff 0 = 1 := by
  have hdet : PowerSeries.constantCoeff (ccmActualFiniteQNormalizedDeterminant N) = 1 := by
    unfold ccmActualFiniteQNormalizedDeterminant
    rw [RingHom.map_det]
    have hzero : PowerSeries.constantCoeff.mapMatrix
        (1 + ccmActualFiniteQMatrix N) = 1 := by
      ext i j
      change PowerSeries.constantCoeff
        ((1 : Matrix (Fin N) (Fin N) (PowerSeries ℂ)) i j +
          ccmActualFiniteQMatrix N i j) = (1 : Matrix (Fin N) (Fin N) ℂ) i j
      rw [map_add]
      have hA : PowerSeries.constantCoeff (ccmActualFiniteQMatrix N i j) = 0 := by
        simpa only [← PowerSeries.coeff_zero_eq_constantCoeff] using
          ccmActualFiniteQMatrix_coeff_zero N i j
      simp [Matrix.one_apply, hA]
    rw [hzero, Matrix.det_one]
  simpa only [← PowerSeries.coeff_zero_eq_constantCoeff] using hdet

/-- The exact interface to the concrete quadratic intersection: any literal
finite CCM determinant coefficient which is represented in `ℚ(√2)` belongs
to `ℤ[√2][1/2]`. -/
theorem ccmSqrtTwoDyadicInteger_of_complex_eq_ccmLambertFiniteMatrix_det_coeff
    {N : ℕ} (rad : ℕ → ℕ → ℕ → ℂ)
    (hrad : ∀ i j ell, (rad i j ell) ^ 2 = (ccmLambertRadicand ell i j : ℂ))
    {x : SqrtTwoRat} {n : ℕ}
    (hx : ccmSqrtTwoRatComplexEmbedding x =
      (ccmLambertFiniteMatrix N rad).det.coeff n) :
    ccmSqrtTwoDyadicInteger x := by
  apply (ccm_sqrtTwoDyadicInteger_iff_complex_dyadicCyclotomic x).mpr
  rw [hx]
  exact ccmLambertFiniteMatrix_det_coeff_literal_dyadicCyclotomic N rad hrad n

end
end RHTower
