/-
# The spectral discriminant of a Hermitian family is a homogeneous polynomial

For a finite family `P₁, …, P_N` of Hermitian matrices the Hamiltonian `H(θ) = ∑ θ_a P_a` has a
real spectrum, and the product of the squared eigenvalue differences

  `Disc(θ) = ∏_{i<j} (E_i(θ) − E_j(θ))²`

is a polynomial in `θ`, homogeneous of degree `D(D−1)`.  The construction avoids the discriminant
of the characteristic polynomial: the Hankel matrix of the power traces `Tr H(θ)^{i+j}` is
`VᵀV` for the Vandermonde matrix `V` of the spectrum, so its determinant is `(det V)²`, which is
the product of the squared differences, while each entry is visibly a polynomial in `θ` of degree
`i + j` — making the determinant homogeneous of degree `∑_i (σ(i) + i) = D(D−1)`, the same for
every permutation.

Reality of the coefficients comes from Hermiticity: conjugating the coefficients of the generic
matrix transposes it, so every power trace, and hence the determinant, is fixed by coefficientwise
conjugation.

Combined with the sphere sublevel bound this gives the shell estimate the transversality tail
needs: as soon as one member of the family has simple spectrum, the degeneracy locus is a
polynomial sublevel set and its shell mass is `O(ε^{1/(D(D−1))})`.

Main results:
* `spectralDiscriminantPoly` — the discriminant as a real multivariate polynomial.
* `isHomogeneous_spectralDiscriminantPoly` — homogeneous of degree `2∑ i = D(D−1)`.
* `eval_spectralDiscriminantPoly` — it evaluates to the product of squared eigenvalue differences.
* `spectralDiscriminantPoly_ne_zero` — nonzero as soon as one member has simple spectrum.
* `exists_toSphere_spectralDiscriminant_sublevel_le` — the shell sublevel bound.
-/
import GaloisForLFunctions.HTGeometry.RankEnergyPowerSum
import GaloisForLFunctions.HTGeometry.PolynomialSublevelSphere
import Mathlib.LinearAlgebra.Vandermonde

open MvPolynomial Matrix Finset MeasureTheory Metric

open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-! ## Real polynomials inside complex ones -/

section RealPart

variable {σ : Type*}

/-- The real polynomial whose coefficients are the real parts of a complex one. -/
noncomputable def realCoeffPart (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  ∑ s ∈ p.support, MvPolynomial.monomial s (p.coeff s).re

theorem coeff_realCoeffPart (p : MvPolynomial σ ℂ) (t : σ →₀ ℕ) :
    (realCoeffPart p).coeff t = (p.coeff t).re := by
  classical
  rw [realCoeffPart, MvPolynomial.coeff_sum]
  by_cases ht : t ∈ p.support
  · have hone := Finset.sum_eq_single (s := p.support)
      (f := fun b => MvPolynomial.coeff t (MvPolynomial.monomial b (p.coeff b).re)) t
      (fun b _ hb => by rw [MvPolynomial.coeff_monomial, if_neg hb])
      (fun h => absurd ht h)
    rw [hone, MvPolynomial.coeff_monomial, if_pos rfl]
  · have h0 : p.coeff t = 0 := by simpa [MvPolynomial.mem_support_iff] using ht
    rw [h0, Complex.zero_re]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    rintro rfl
    exact ht hb

/-- A polynomial fixed by coefficientwise conjugation is the image of its real part. -/
theorem map_realCoeffPart {p : MvPolynomial σ ℂ}
    (h : MvPolynomial.map (starRingEnd ℂ) p = p) :
    MvPolynomial.map (algebraMap ℝ ℂ) (realCoeffPart p) = p := by
  ext t
  rw [MvPolynomial.coeff_map, coeff_realCoeffPart]
  have hc : (starRingEnd ℂ) (p.coeff t) = p.coeff t := by
    have := congrArg (fun q => MvPolynomial.coeff t q) h
    rwa [MvPolynomial.coeff_map] at this
  have him : (p.coeff t).im = 0 := by
    have := Complex.conj_eq_iff_im.mp hc
    exact this
  refine Complex.ext ?_ ?_
  · simp
  · simp [him]

/-- Homogeneity descends along an injective coefficient map. -/
theorem isHomogeneous_of_map {p : MvPolynomial σ ℂ} {q : MvPolynomial σ ℝ} {d : ℕ}
    (hq : MvPolynomial.map (algebraMap ℝ ℂ) q = p) (h : p.IsHomogeneous d) :
    q.IsHomogeneous d := by
  intro t ht
  refine h ?_
  rw [← hq, MvPolynomial.coeff_map]
  simpa using ht

/-- The real evaluation of a real polynomial is the complex evaluation of its image. -/
theorem ofReal_eval_eq_eval_map (q : MvPolynomial σ ℝ) (θ : σ → ℝ) :
    ((MvPolynomial.eval θ q : ℝ) : ℂ)
      = MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ)) (MvPolynomial.map (algebraMap ℝ ℂ) q) := by
  rw [MvPolynomial.eval_map]
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p a hp => simp [hp]

end RealPart

/-! ## The generic Hamiltonian of a Hermitian family -/

section Ensemble

variable {N D : ℕ}

/-- The Hamiltonian of the family at a real coefficient vector. -/
noncomputable def spectralEnsembleMatrix (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (θ : Fin N → ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ a, (θ a : ℂ) • P a

theorem isHermitian_spectralEnsembleMatrix {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) :
    (spectralEnsembleMatrix P θ).IsHermitian := by
  show (spectralEnsembleMatrix P θ)ᴴ = spectralEnsembleMatrix P θ
  ext i j
  simp only [Matrix.conjTranspose_apply, spectralEnsembleMatrix, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hentry : star (P a j i) = P a i j := by
    have := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M i j) (hP a)
    simpa [Matrix.conjTranspose_apply] using this
  rw [star_mul']
  rw [hentry, Complex.star_def, Complex.conj_ofReal]

/-- The Hamiltonian of the family over the polynomial ring in its coefficients. -/
noncomputable def spectralGenericMatrix (P : Fin N → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) (MvPolynomial (Fin N) ℂ) :=
  fun i j => ∑ a, MvPolynomial.X a * MvPolynomial.C (P a i j)

theorem trace_mapMatrix {R S : Type*} [CommRing R] [CommRing S] {n : Type*} [Fintype n]
    [DecidableEq n] (f : R →+* S) (M : Matrix n n R) : (f.mapMatrix M).trace = f M.trace := by
  simp [Matrix.trace, Matrix.diag, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum]

theorem mapMatrix_spectralGenericMatrix (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (θ : Fin N → ℝ) :
    (MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ))).mapMatrix (spectralGenericMatrix P)
      = spectralEnsembleMatrix P θ := by
  refine Matrix.ext fun i j => ?_
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, spectralGenericMatrix,
    spectralEnsembleMatrix, Matrix.sum_apply, Matrix.smul_apply]

theorem mapMatrix_conj_spectralGenericMatrix {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) :
    (MvPolynomial.map (starRingEnd ℂ)).mapMatrix (spectralGenericMatrix P)
      = (spectralGenericMatrix P)ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    spectralGenericMatrix, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  have hentry : star (P a i j) = P a j i := by
    have := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M j i) (hP a)
    simpa [Matrix.conjTranspose_apply] using this
  simpa [Complex.star_def] using hentry

/-- The Hankel matrix of the power traces of the generic Hamiltonian. -/
noncomputable def spectralTraceHankel (P : Fin N → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) (MvPolynomial (Fin N) ℂ) :=
  fun i j => ((spectralGenericMatrix P) ^ ((i : ℕ) + (j : ℕ))).trace

/-- The spectral discriminant, over the complex coefficients. -/
noncomputable def spectralDiscriminantC (P : Fin N → Matrix (Fin D) (Fin D) ℂ) :
    MvPolynomial (Fin N) ℂ := (spectralTraceHankel P).det

/-- The degree of the spectral discriminant of a `D`-dimensional family, namely `D(D−1)`. -/
def spectralDiscriminantDegree (D : ℕ) : ℕ := 2 * ∑ i : Fin D, (i : ℕ)

/-! ## Homogeneity -/

theorem isHomogeneous_spectralGenericMatrix (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin D) : (spectralGenericMatrix P i j).IsHomogeneous 1 := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => ?_
  simpa using (MvPolynomial.isHomogeneous_X ℂ a).mul (MvPolynomial.isHomogeneous_C (Fin N) (P a i j))

theorem isHomogeneous_spectralGenericMatrix_pow (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (k : ℕ) :
    ∀ i j : Fin D, ((spectralGenericMatrix P ^ k) i j).IsHomogeneous k := by
  induction k with
  | zero =>
      intro i j
      simp only [pow_zero, Matrix.one_apply]
      split
      · exact MvPolynomial.isHomogeneous_one _ _
      · exact MvPolynomial.isHomogeneous_zero _ _ _
  | succ k ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun p _ => ?_
      exact (ih i p).mul (isHomogeneous_spectralGenericMatrix P p j)

theorem isHomogeneous_spectralTraceHankel (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    (spectralTraceHankel P i j).IsHomogeneous ((i : ℕ) + (j : ℕ)) := by
  rw [spectralTraceHankel, Matrix.trace]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun p _ => ?_
  exact isHomogeneous_spectralGenericMatrix_pow P _ p p

theorem isHomogeneous_spectralDiscriminantC (P : Fin N → Matrix (Fin D) (Fin D) ℂ) :
    (spectralDiscriminantC P).IsHomogeneous (spectralDiscriminantDegree D) := by
  rw [spectralDiscriminantC, Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s _ => ?_
  have hprod : (∏ i, spectralTraceHankel P (s i) i).IsHomogeneous
      (∑ i : Fin D, ((s i : ℕ) + (i : ℕ))) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_spectralTraceHankel P (s i) i
  have hsum : ∑ i : Fin D, ((s i : ℕ) + (i : ℕ)) = spectralDiscriminantDegree D := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp s (fun i : Fin D => (i : ℕ)),
      spectralDiscriminantDegree, two_mul]
  rw [hsum] at hprod
  have hCast : ((Equiv.Perm.sign s : ℤ) : MvPolynomial (Fin N) ℂ)
      = MvPolynomial.C ((Equiv.Perm.sign s : ℤ) : ℂ) :=
    (map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin N) ℂ) _).symm
  rw [hCast]
  simpa using (MvPolynomial.isHomogeneous_C (Fin N) (((Equiv.Perm.sign s : ℤ) : ℂ))).mul hprod

/-! ## Reality -/

theorem map_conj_spectralDiscriminantC {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) :
    MvPolynomial.map (starRingEnd ℂ) (spectralDiscriminantC P) = spectralDiscriminantC P := by
  rw [spectralDiscriminantC, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  show (MvPolynomial.map (starRingEnd ℂ)) (spectralTraceHankel P i j) = spectralTraceHankel P i j
  rw [spectralTraceHankel, ← trace_mapMatrix, map_pow, mapMatrix_conj_spectralGenericMatrix hP,
    ← Matrix.transpose_pow, Matrix.trace_transpose]

/-- The spectral discriminant as a real multivariate polynomial in the coefficients. -/
noncomputable def spectralDiscriminantPoly (P : Fin N → Matrix (Fin D) (Fin D) ℂ) :
    MvPolynomial (Fin N) ℝ := realCoeffPart (spectralDiscriminantC P)

theorem map_spectralDiscriminantPoly {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) :
    MvPolynomial.map (algebraMap ℝ ℂ) (spectralDiscriminantPoly P) = spectralDiscriminantC P :=
  map_realCoeffPart (map_conj_spectralDiscriminantC hP)

theorem isHomogeneous_spectralDiscriminantPoly {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) :
    (spectralDiscriminantPoly P).IsHomogeneous (spectralDiscriminantDegree D) :=
  isHomogeneous_of_map (map_spectralDiscriminantPoly hP) (isHomogeneous_spectralDiscriminantC P)

/-! ## The value: the product of squared eigenvalue differences -/

theorem det_powerSum_hankel (v : Fin D → ℂ) :
    (Matrix.of fun i j : Fin D => ∑ k, v k ^ ((i : ℕ) + (j : ℕ))).det
      = (∏ i, ∏ j ∈ Finset.Ioi i, (v j - v i)) ^ 2 := by
  have hEq : (Matrix.of fun i j : Fin D => ∑ k, v k ^ ((i : ℕ) + (j : ℕ)))
      = (Matrix.vandermonde v)ᵀ * (Matrix.vandermonde v) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vandermonde_apply, pow_add]
  rw [hEq, Matrix.det_mul, Matrix.det_transpose, Matrix.det_vandermonde, sq]

theorem eval_spectralDiscriminantC {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) :
    MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ)) (spectralDiscriminantC P)
      = (∏ i, ∏ j ∈ Finset.Ioi i,
          (((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues j : ℂ)
            - ((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i : ℂ))) ^ 2 := by
  rw [spectralDiscriminantC, RingHom.map_det]
  have hentry : (MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ))).mapMatrix (spectralTraceHankel P)
      = Matrix.of fun i j : Fin D =>
          ∑ k, (((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues k : ℂ))
            ^ ((i : ℕ) + (j : ℕ)) := by
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    show (MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ))) (spectralTraceHankel P i j) = _
    rw [spectralTraceHankel, ← trace_mapMatrix, map_pow, mapMatrix_spectralGenericMatrix]
    exact trace_pow_eq_sum_eigenvalues_pow (isHermitian_spectralEnsembleMatrix hP θ) _
  rw [hentry, det_powerSum_hankel]

theorem eval_spectralDiscriminantPoly {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) :
    MvPolynomial.eval θ (spectralDiscriminantPoly P)
      = (∏ i, ∏ j ∈ Finset.Ioi i,
          ((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues j
            - (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i)) ^ 2 := by
  have hcast := ofReal_eval_eq_eval_map (spectralDiscriminantPoly P) θ
  rw [map_spectralDiscriminantPoly hP, eval_spectralDiscriminantC hP θ] at hcast
  have hpush : ((∏ i, ∏ j ∈ Finset.Ioi i,
        (((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues j : ℂ)
          - ((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i : ℂ))) ^ 2)
      = (((∏ i, ∏ j ∈ Finset.Ioi i,
        ((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues j
          - (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i)) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hpush] at hcast
  exact_mod_cast hcast

theorem spectralDiscriminantPoly_nonneg {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) :
    0 ≤ MvPolynomial.eval θ (spectralDiscriminantPoly P) := by
  rw [eval_spectralDiscriminantPoly hP θ]
  exact sq_nonneg _

/-- **The discriminant is a nonzero polynomial** as soon as one member of the family has simple
spectrum. -/
theorem spectralDiscriminantPoly_ne_zero {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) {θ₀ : Fin N → ℝ}
    (hinj : Function.Injective (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues) :
    spectralDiscriminantPoly P ≠ 0 := by
  intro hzero
  have hval : MvPolynomial.eval θ₀ (spectralDiscriminantPoly P) = 0 := by rw [hzero]; simp
  rw [eval_spectralDiscriminantPoly hP θ₀, sq_eq_zero_iff, Finset.prod_eq_zero_iff] at hval
  obtain ⟨i, -, hi⟩ := hval
  rw [Finset.prod_eq_zero_iff] at hi
  obtain ⟨j, hj, hij⟩ := hi
  have hne : i ≠ j := (Finset.mem_Ioi.mp hj).ne
  have heq : (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues j
      = (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues i := sub_eq_zero.mp hij
  exact hne (hinj heq).symm

end Ensemble

/-! ## The shell sublevel bound -/

theorem spectralDiscriminantDegree_pos {D : ℕ} (hD : 2 ≤ D) : 0 < spectralDiscriminantDegree D := by
  rw [spectralDiscriminantDegree]
  have hmem : (⟨1, by omega⟩ : Fin D) ∈ (Finset.univ : Finset (Fin D)) := Finset.mem_univ _
  have hle : (1 : ℕ) ≤ ∑ i : Fin D, (i : ℕ) :=
    le_trans (by norm_num) (Finset.single_le_sum (f := fun i : Fin D => (i : ℕ))
      (fun i _ => Nat.zero_le _) hmem)
  omega

/-- **The transversality tail of the degeneracy locus.**  For a Hermitian family on `m+1`
coefficients with at least one simple-spectrum member, the shell mass of the set where the spectral
discriminant is at most `ε` is at most a finite constant times `ε^{1/(D(D−1))}`. -/
theorem exists_toSphere_spectralDiscriminant_sublevel_le {m D : ℕ} (hD : 2 ≤ D)
    {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    {θ₀ : Fin (m + 1) → ℝ}
    (hinj : Function.Injective (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ε : ℝ, 0 ≤ ε →
      volume.toSphere {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
          MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1))))
            (spectralDiscriminantPoly P) ≤ ε}
        ≤ C * ENNReal.ofReal (ε ^ ((1 : ℝ) / spectralDiscriminantDegree D)) := by
  obtain ⟨C, hCtop, hbound⟩ := exists_toSphere_sublevel_le (spectralDiscriminantDegree_pos hD)
    (spectralDiscriminantPoly P) (isHomogeneous_spectralDiscriminantPoly hP)
    (spectralDiscriminantPoly_ne_zero hP hinj)
  refine ⟨C, hCtop, fun ε hε => ?_⟩
  have hset : {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
      MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1))))
        (spectralDiscriminantPoly P) ≤ ε}
      = {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
        |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1))))
          (spectralDiscriminantPoly P)| ≤ ε} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [abs_of_nonneg (spectralDiscriminantPoly_nonneg hP _)]
  rw [hset]
  exact hbound ε hε

end GaloisForLFunctions.HTGeometry
