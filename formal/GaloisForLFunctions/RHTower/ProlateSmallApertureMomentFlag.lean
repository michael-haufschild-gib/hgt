import GaloisForLFunctions.HTGeometry.ApertureExponentialL2Expansion
import GaloisForLFunctions.HTGeometry.IntervalL2Density
import GaloisForLFunctions.RHTower.LeastSquaresProjection

/-!
# Small-aperture moment flag for every prolate rung

The small-aperture finite-Fourier character has a polynomial moment flag that can
be exposed without choosing an eigenvector.  At rung `k`, orthogonal projection
removes every monomial of degree strictly below `k`.  The surviving degree-`k`
residual is nonzero, and the rescaled projected Fourier character converges to
that residual with its exact Taylor coefficient.

Taking `k = 2 * n` supplies the missing all-rung even seed for the small-aperture
prolate problem.  This module deliberately stops before identifying that seed
with the `n`th indexed Slepian eigenline: that spectral lifting is the next
ordering step, not an assumption hidden in the construction.
-/

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem apertureMeasure_one_eq :
    apertureMeasure 1 = volume.restrict (Icc (-1 : ℝ) 1) := by
  rw [apertureMeasure, restrict_Ioo_eq_restrict_Icc]

theorem memLp_apertureCpoly (a : ℝ) (P : Polynomial ℂ) :
    MemLp (fun x : ℝ => Polynomial.eval (x : ℂ) P) 2 (apertureMeasure a) := by
  rw [apertureMeasure, restrict_Ioo_eq_restrict_Icc]
  exact memLp_two_of_continuous a (continuous_cpoly P)

/-- Polynomial evaluation on the aperture interval, regarded as an `L²` vector. -/
def apertureCpolyToL2 (a : ℝ) :
    Polynomial ℂ →ₗ[ℂ] Lp ℂ 2 (apertureMeasure a) where
  toFun P := (memLp_apertureCpoly a P).toLp _
  map_add' P Q := by
    rw [← MemLp.toLp_add]
    congr 1
    funext x
    simp
  map_smul' c P := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    congr 1
    funext x
    simp

/-- A polynomial vanishing as an aperture `L²` vector is the zero polynomial. -/
theorem apertureCpolyToL2_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective (apertureCpolyToL2 a) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro P hP
  by_contra hne
  have hzero : ((apertureCpolyToL2 a P : Lp ℂ 2 (apertureMeasure a)) : ℝ → ℂ)
      =ᵐ[apertureMeasure a] 0 := by
    rw [hP]
    exact Lp.coeFn_zero ℂ 2 _
  have hfun : (fun x : ℝ => Polynomial.eval (x : ℂ) P)
      =ᵐ[apertureMeasure a] 0 :=
    ((memLp_apertureCpoly a P).coeFn_toLp).symm.trans hzero
  have hae := ae_iff.mp hfun
  have hsub : {x : ℝ | ¬ Polynomial.eval (x : ℂ) P = (0 : ℝ → ℂ) x}
      ⊇ {x : ℝ | ¬ Polynomial.IsRoot P (x : ℂ)} := by
    intro x hx
    simpa [Polynomial.IsRoot] using hx
  have hroot : Set.Finite {z : ℂ | Polynomial.IsRoot P z} :=
    Polynomial.finite_setOf_isRoot hne
  have hrootReal : Set.Finite {x : ℝ | Polynomial.IsRoot P (x : ℂ)} := by
    refine Set.Finite.ofFinset (hroot.toFinset.preimage (fun x : ℝ => (x : ℂ))
      (Set.injOn_of_injective Complex.ofReal_injective)) ?_
    intro x
    simp [Set.Finite.mem_toFinset]
  have huniv : apertureMeasure a Set.univ = 0 := by
    have h1 : apertureMeasure a {x : ℝ | Polynomial.IsRoot P (x : ℂ)} = 0 := by
      rw [apertureMeasure]
      apply le_antisymm
      · exact (Measure.restrict_le_self (μ := volume) (s := Ioo (-a) a)) _
          |>.trans (le_of_eq (hrootReal.measure_zero volume))
      · exact bot_le
    have h2 : apertureMeasure a {x : ℝ | ¬ Polynomial.IsRoot P (x : ℂ)} = 0 :=
      measure_mono_null hsub hae
    have hle := measure_union_le (μ := apertureMeasure a)
      {x : ℝ | Polynomial.IsRoot P (x : ℂ)} {x : ℝ | ¬ Polynomial.IsRoot P (x : ℂ)}
    rw [h1, h2] at hle
    simp only [add_zero, nonpos_iff_eq_zero] at hle
    have hsetu : {x : ℝ | Polynomial.IsRoot P (x : ℂ)}
        ∪ {x : ℝ | ¬ Polynomial.IsRoot P (x : ℂ)} = Set.univ := by
      ext x
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      tauto
    rwa [hsetu] at hle
  rw [apertureMeasure, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.ofReal_eq_zero] at huniv
  linarith

theorem apertureCpolyToL2_X_pow (a : ℝ) (n : ℕ) :
    apertureCpolyToL2 a (Polynomial.X ^ n) = apertureComplexMonomialL2 a n := by
  unfold apertureCpolyToL2 apertureComplexMonomialL2
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  funext x
  simp

/-- Complex monomials are linearly independent in unit-aperture `L²`. -/
theorem linearIndependent_apertureComplexMonomialL2_one :
    LinearIndependent ℂ (apertureComplexMonomialL2 1) := by
  have hX : LinearIndependent ℂ (fun n : ℕ => (Polynomial.X : Polynomial ℂ) ^ n) := by
    have hb := (Polynomial.basisMonomials ℂ).linearIndependent
    rw [Polynomial.coe_basisMonomials] at hb
    simpa [Polynomial.X_pow_eq_monomial] using hb
  have hmap := hX.map' (apertureCpolyToL2 1)
    (LinearMap.ker_eq_bot.mpr (apertureCpolyToL2_injective one_pos))
  have hcomp : (⇑(apertureCpolyToL2 1) ∘ fun n : ℕ =>
      (Polynomial.X : Polynomial ℂ) ^ n) = apertureComplexMonomialL2 1 := by
    funext n
    exact apertureCpolyToL2_X_pow 1 n
  rwa [hcomp] at hmap

abbrev UnitApertureL2 := Lp ℂ 2 (apertureMeasure 1)

/-- Span of aperture monomials of degrees strictly below `k`. -/
def apertureMomentSpan (k : ℕ) : Submodule ℂ UnitApertureL2 :=
  Submodule.span ℂ (Set.range fun i : Fin k => apertureComplexMonomialL2 1 (i : ℕ))

noncomputable instance apertureMomentSpan_hasOrthogonalProjection (k : ℕ) :
    (apertureMomentSpan k).HasOrthogonalProjection := by
  exact hasOrthogonalProjection_span
    (fun i : Fin k => apertureComplexMonomialL2 1 (i : ℕ))

/-- Orthogonal residual after removing every aperture moment below degree `k`. -/
noncomputable def apertureMomentResidual (k : ℕ) :
    UnitApertureL2 →L[ℂ] UnitApertureL2 :=
  ContinuousLinearMap.id ℂ UnitApertureL2 -
    (apertureMomentSpan k).subtypeL.comp (apertureMomentSpan k).orthogonalProjectionOnto

theorem apertureMomentResidual_apply (k : ℕ) (f : UnitApertureL2) :
    apertureMomentResidual k f = f - (apertureMomentSpan k).starProjection f := rfl

theorem apertureComplexMonomial_mem_momentSpan {j k : ℕ} (hjk : j < k) :
    apertureComplexMonomialL2 1 j ∈ apertureMomentSpan k := by
  apply Submodule.subset_span
  exact ⟨⟨j, hjk⟩, rfl⟩

theorem apertureMomentResidual_monomial_eq_zero {j k : ℕ} (hjk : j < k) :
    apertureMomentResidual k (apertureComplexMonomialL2 1 j) = 0 := by
  rw [apertureMomentResidual_apply]
  have hmem := apertureComplexMonomial_mem_momentSpan hjk
  have hproj := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨apertureComplexMonomialL2 1 j, hmem⟩ : apertureMomentSpan k)
  change apertureComplexMonomialL2 1 j -
    ((apertureMomentSpan k).orthogonalProjectionOnto
      (apertureComplexMonomialL2 1 j) : UnitApertureL2) = 0
  rw [hproj]
  exact sub_self _

/-- Degree `k` is outside span of all strictly lower aperture moments. -/
theorem apertureComplexMonomial_not_mem_momentSpan (k : ℕ) :
    apertureComplexMonomialL2 1 k ∉ apertureMomentSpan k := by
  have hnot := linearIndependent_apertureComplexMonomialL2_one.notMem_span k
  intro hmem
  apply hnot
  refine Submodule.span_mono ?_ hmem
  rintro x ⟨i, rfl⟩
  exact ⟨i, by simpa using (show (i : ℕ) ≠ k by omega), rfl⟩

/-- The first moment surviving the degree-`k` deflation is nonzero. -/
theorem apertureMomentResidual_monomial_ne_zero (k : ℕ) :
    apertureMomentResidual k (apertureComplexMonomialL2 1 k) ≠ 0 := by
  intro hzero
  apply apertureComplexMonomial_not_mem_momentSpan k
  rw [apertureMomentResidual_apply, sub_eq_zero] at hzero
  rw [hzero]
  exact (apertureMomentSpan k).orthogonalProjectionOnto
    (apertureComplexMonomialL2 1 k) |>.property

/--
After deleting moments below `k`, the finite-Fourier character has exact leading
order `k`; its limiting direction is the nonzero degree-`k` moment residual.
-/
theorem tendsto_apertureMomentResidual_fourier (k : ℕ) :
    Tendsto (fun x : ℝ => (x ^ k)⁻¹ • apertureMomentResidual k (apertureFourierL2 1 x))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (fourierGroundVector 1 (apertureMomentResidual k) k)) :=
  tendsto_smul_inv_pow_apertureFourier zero_le_one (apertureMomentResidual k)
    (fun _j hj => apertureMomentResidual_monomial_eq_zero hj)

theorem fourierGroundVector_apertureMomentResidual_ne_zero (k : ℕ) :
    fourierGroundVector 1 (apertureMomentResidual k) k ≠ 0 := by
  rw [fourierGroundVector]
  exact smul_ne_zero (by
    exact div_ne_zero (pow_ne_zero k (neg_ne_zero.mpr Complex.I_ne_zero))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)))
    (apertureMomentResidual_monomial_ne_zero k)

/-- The normalized projected character converges projectively to rung `k`. -/
theorem tendsto_groundOverlap_apertureMomentResidual_fourier (k : ℕ) :
    Tendsto (fun x : ℝ =>
        groundOverlap (((Nat.factorial k : ℂ))⁻¹ •
            apertureMomentResidual k (apertureComplexMonomialL2 1 k))
          (apertureMomentResidual k (apertureFourierL2 1 x)))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) :=
  tendsto_groundOverlap_apertureFourier zero_le_one (apertureMomentResidual k)
    (fun _j hj => apertureMomentResidual_monomial_eq_zero hj)
    (apertureMomentResidual_monomial_ne_zero k)

/-- All-rung even specialization used by the small-aperture prolate ladder. -/
theorem tendsto_evenRung_apertureMomentResidual_fourier (n : ℕ) :
    Tendsto (fun x : ℝ => (x ^ (2 * n))⁻¹ •
        apertureMomentResidual (2 * n) (apertureFourierL2 1 x))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (fourierGroundVector 1 (apertureMomentResidual (2 * n)) (2 * n))) :=
  tendsto_apertureMomentResidual_fourier (2 * n)

end RHTower
