import GaloisForLFunctions.HTGeometry.LocalExponentialTestClosure

/-!
# The block-Hankel sign cone of a bounded Hermitian matrix density

A bounded Hermitian matrix field `J` on a source `μ` has entrywise moments `M_n(J)` and order-`N`
block Hankel sections `H_N(J)`.  The load-bearing identity is that the block-Hankel quadratic form
at a block coefficient family is exactly the integrated multiplier form of `J` against the
associated vector polynomial.  Positivity of the density therefore forces positivity of every
block section.
-/

namespace HTGeometry

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Matrix ComplexOrder

section MatrixSignCone

variable {d : ℕ} {μ : Measure ℝ}

/-- Entrywise matrix moment of a matrix density. -/
noncomputable def matrixMoment (μ : Measure ℝ) (J : ℝ → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun k l => ∫ x : ℝ, (x : ℂ) ^ n * J x k l ∂μ

/-- The order-`N` block Hankel section of a matrix density. -/
noncomputable def blockHankel (μ : Measure ℝ) (J : ℝ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ :=
  Matrix.of fun p q => matrixMoment μ J ((p.1 : ℕ) + (q.1 : ℕ)) p.2 q.2

/-- The vector polynomial attached to a block coefficient family. -/
noncomputable def vectorPoly {N : ℕ} (v : Fin N × Fin d → ℂ) (x : ℝ) (k : Fin d) : ℂ :=
  ∑ i : Fin N, (x : ℂ) ^ (i : ℕ) * v (i, k)

/-- The Hermitian quadratic form of a matrix at a vector. -/
noncomputable def matQuad {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) : ℂ :=
  ∑ k, ∑ l, (starRingEnd ℂ) (v k) * M k l * v l

/-- The integrated multiplier form of a matrix density against a vector field. -/
noncomputable def multiplierForm (μ : Measure ℝ) (J : ℝ → Matrix (Fin d) (Fin d) ℂ)
    (p : ℝ → Fin d → ℂ) : ℂ :=
  ∫ x : ℝ, matQuad (J x) (p x) ∂μ

theorem conj_vectorPoly {N : ℕ} (v : Fin N × Fin d → ℂ) (x : ℝ) (k : Fin d) :
    (starRingEnd ℂ) (vectorPoly v x k)
      = ∑ i : Fin N, (x : ℂ) ^ (i : ℕ) * (starRingEnd ℂ) (v (i, k)) := by
  rw [vectorPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← Complex.ofReal_pow, Complex.conj_ofReal, Complex.ofReal_pow]

/-! ## Integrability in the exponential window -/

/-- Every absolute monomial is integrable against a measure with an exponential window. -/
theorem integrable_abs_pow {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) μ := by
  refine Integrable.mono (hexp.const_mul ((n.factorial : ℝ) / a ^ n)) (by fun_prop) ?_
  filter_upwards with x
  have hb := abs_pow_le_const_mul_exp ha n x
  have hnn : (0 : ℝ) ≤ (n.factorial : ℝ) / a ^ n * Real.exp (a * |x|) := by
    have := (Real.exp_pos (a * |x|)).le
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ |x| ^ n)]
  exact hb

/-- Every entrywise moment integrand of a bounded matrix density is integrable. -/
theorem integrable_pow_mul_entry {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C) (n : ℕ) (k l : Fin d) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * J x k l) μ := by
  refine Integrable.mono ((integrable_abs_pow ha hexp n).const_mul C) ?_ ?_
  · exact (Complex.continuous_ofReal.aestronglyMeasurable.pow n).mul (hmeas k l)
  · filter_upwards [hbdd] with x hx
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ C * |x| ^ n)]
    calc |x| ^ n * ‖J x k l‖ ≤ |x| ^ n * C :=
          mul_le_mul_of_nonneg_left (hx k l) (by positivity)
      _ = C * |x| ^ n := by ring

/-! ## The exact block-Hankel / multiplier identity -/

/-- **(LEF.9).**  The block-Hankel quadratic form is the integrated multiplier form of the
associated vector polynomial. -/
theorem matQuad_blockHankel_eq_multiplierForm {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    (N : ℕ) (v : Fin N × Fin d → ℂ) :
    matQuad (blockHankel μ J N) v = multiplierForm μ J (vectorPoly v) := by
  set F : Fin N × Fin d → Fin N × Fin d → ℝ → ℂ := fun p q x =>
    (starRingEnd ℂ) (v p) * ((x : ℂ) ^ ((p.1 : ℕ) + (q.1 : ℕ)) * J x p.2 q.2) * v q with hF
  have hint : ∀ p q, Integrable (F p q) μ := fun p q =>
    ((integrable_pow_mul_entry ha hexp hC hmeas hbdd _ p.2 q.2).const_mul _).mul_const _
  have hterm : ∀ p q, (starRingEnd ℂ) (v p) * blockHankel μ J N p q * v q = ∫ x, F p q x ∂μ := by
    intro p q
    simp only [blockHankel, matrixMoment, Matrix.of_apply, hF]
    rw [integral_mul_const, integral_const_mul]
  simp only [matQuad, multiplierForm]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hterm p q]
  have hswap : ∀ p : Fin N × Fin d, ∑ q, ∫ x, F p q x ∂μ = ∫ x, ∑ q, F p q x ∂μ := fun p =>
    (integral_finsetSum _ fun q _ => hint p q).symm
  rw [Finset.sum_congr rfl fun p _ => hswap p,
    ← integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hRHS : ∀ k l : Fin d,
      (starRingEnd ℂ) (vectorPoly v x k) * J x k l * vectorPoly v x l
        = ∑ i : Fin N, ∑ j : Fin N,
            (starRingEnd ℂ) (v (i, k)) * ((x : ℂ) ^ ((i : ℕ) + (j : ℕ)) * J x k l) * v (j, l) := by
    intro k l
    rw [conj_vectorPoly, vectorPoly, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  have perm : ∀ G : Fin N → Fin d → Fin N → Fin d → ℂ,
      (∑ i, ∑ k, ∑ j, ∑ l, G i k j l) = ∑ k, ∑ l, ∑ i, ∑ j, G i k j l := by
    intro G
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : ∀ i : Fin N, (∑ j, ∑ l, G i k j l) = ∑ l, ∑ j, G i k j l :=
      fun i => Finset.sum_comm
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  simp only [hF, Fintype.sum_prod_type]
  rw [perm fun i k j l =>
    (starRingEnd ℂ) (v (i, k)) * ((x : ℂ) ^ ((i : ℕ) + (j : ℕ)) * J x k l) * v (j, l)]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => (hRHS k l).symm

/-! ## Forward direction of the sign cone -/

/-- The Hermitian quadratic form is the standard vector-matrix-vector pairing. -/
theorem matQuad_eq_dotProduct {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    matQuad M v = star v ⬝ᵥ (M *ᵥ v) := by
  simp only [matQuad, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc,
    RCLike.star_def]


theorem integrable_matQuad_vectorPoly {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    {N : ℕ} (v : Fin N × Fin d → ℂ) :
    Integrable (fun x : ℝ => matQuad (J x) (vectorPoly v x)) μ := by
  refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ?_
  have hpt : ∀ x : ℝ, (starRingEnd ℂ) (vectorPoly v x k) * J x k l * vectorPoly v x l
      = ∑ i : Fin N, ∑ j : Fin N,
          (starRingEnd ℂ) (v (i, k)) * ((x : ℂ) ^ ((i : ℕ) + (j : ℕ)) * J x k l) * v (j, l) := by
    intro x
    rw [conj_vectorPoly, vectorPoly, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  simp only [hpt]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((integrable_pow_mul_entry ha hexp hC hmeas hbdd ((i : ℕ) + (j : ℕ)) k l).const_mul
      ((starRingEnd ℂ) (v (i, k)))).mul_const (v (j, l))

/-- **Theorem 3.1, forward direction.**  A positive semidefinite matrix density has positive
semidefinite block Hankel sections. -/
theorem re_matQuad_blockHankel_nonneg {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    (hpos : ∀ᵐ x ∂μ, (J x).PosSemidef)
    (N : ℕ) (v : Fin N × Fin d → ℂ) :
    0 ≤ (matQuad (blockHankel μ J N) v).re := by
  rw [matQuad_blockHankel_eq_multiplierForm ha hexp hC hmeas hbdd N v, multiplierForm]
  have hint := integrable_matQuad_vectorPoly ha hexp hC hmeas hbdd v
  have hre : (∫ x : ℝ, matQuad (J x) (vectorPoly v x) ∂μ).re
      = ∫ x : ℝ, (matQuad (J x) (vectorPoly v x)).re ∂μ := (integral_re hint).symm
  rw [hre]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hpos] with x hx
  rw [matQuad_eq_dotProduct]
  exact hx.re_dotProduct_nonneg _

/-! ## Rank-one reduction to a scalar density -/

theorem conj_mul_self (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq z

theorem matQuad_smul_vector {n : Type*} [Fintype n] (M : Matrix n n ℂ) (z : ℂ) (u : n → ℂ) :
    matQuad M (fun k => z * u k) = ((starRingEnd ℂ) z * z) * matQuad M u := by
  simp only [matQuad, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem vectorPoly_rankOne {N : ℕ} {P : Polynomial ℂ} (hN : P.natDegree < N) (u : Fin d → ℂ)
    (x : ℝ) (k : Fin d) :
    vectorPoly (fun p : Fin N × Fin d => P.coeff (p.1 : ℕ) * u p.2) x k
      = Polynomial.eval (x : ℂ) P * u k := by
  rw [vectorPoly, Polynomial.eval_eq_sum_range' hN, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range
    (fun i => P.coeff i * (x : ℂ) ^ i * u k) N]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Rank-one test.**  Positivity of every block Hankel section forces the squared-modulus
polynomial pairing of every scalar direction `u* J u` to be nonnegative. -/
theorem integral_normSq_poly_mul_matQuad_nonneg {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    (hH : ∀ (N : ℕ) (v : Fin N × Fin d → ℂ), 0 ≤ (matQuad (blockHankel μ J N) v).re)
    (P : Polynomial ℂ) (u : Fin d → ℂ) :
    0 ≤ ∫ x : ℝ, ‖Polynomial.eval (x : ℂ) P‖ ^ 2 * (matQuad (J x) u).re ∂μ := by
  set N := P.natDegree + 1 with hNdef
  set v : Fin N × Fin d → ℂ := fun p => P.coeff (p.1 : ℕ) * u p.2 with hv
  have hN : P.natDegree < N := by omega
  have hkey := hH N v
  rw [matQuad_blockHankel_eq_multiplierForm ha hexp hC hmeas hbdd N v, multiplierForm] at hkey
  have hpt : ∀ x : ℝ, matQuad (J x) (vectorPoly v x)
      = ((‖Polynomial.eval (x : ℂ) P‖ ^ 2 : ℝ) : ℂ) * matQuad (J x) u := by
    intro x
    have hvp : vectorPoly v x = fun k => Polynomial.eval (x : ℂ) P * u k := by
      funext k
      exact vectorPoly_rankOne hN u x k
    rw [hvp, matQuad_smul_vector, conj_mul_self]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at hkey
  have hint : Integrable (fun x : ℝ =>
      ((‖Polynomial.eval (x : ℂ) P‖ ^ 2 : ℝ) : ℂ) * matQuad (J x) u) μ := by
    refine Integrable.congr (integrable_matQuad_vectorPoly ha hexp hC hmeas hbdd v)
      (Filter.Eventually.of_forall hpt)
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre] at hkey
  refine le_trans hkey (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)))
  simp [Complex.mul_re, -Complex.ofReal_pow]

end MatrixSignCone

end HTGeometry
