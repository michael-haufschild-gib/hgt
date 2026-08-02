import GaloisForLFunctions.RHTower.ArithmeticDilationProjectiveLimit
import GaloisForLFunctions.RHTower.FredholmDeterminantZeta
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.RHTower.SuzukiDiagonalResolventInstantiation
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Trace-class realization of absolutely projective arithmetic matrices

An absolutely summable matrix on `ℕ × ℕ` is realized on `ℓ²(ℕ)` by its canonical
rank-one matrix-unit expansion.  Its Schatten-1 norm is bounded by the entrywise projective norm.
Consequently the arithmetic projective convergence proved in
`ArithmeticDilationProjectiveLimit` is genuine trace-norm convergence of trace-class operators.
-/

noncomputable section

open Filter
open ContinuousLinearMap
open scoped InnerProductSpace

namespace RHTower

/-- The Hilbert carrier of the arithmetic dilation matrix. -/
abbrev ArithmeticDilationHilbert := lp (fun _ : ℕ => ℂ) 2

/-- One matrix entry as a rank-one matrix unit on `ℓ²(ℕ)`. -/
noncomputable def absoluteMatrixRankOneTerm
    (M : ℕ × ℕ → ℂ) (p : ℕ × ℕ) :
    ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert :=
  M p • InnerProductSpace.rankOne ℂ
    (HilbertSchmidt.lpBasis ℕ p.1) (HilbertSchmidt.lpBasis ℕ p.2)

theorem absoluteMatrixRankOneTerm_hasRankLE
    (M : ℕ × ℕ → ℂ) (p : ℕ × ℕ) :
    HasRankLE (absoluteMatrixRankOneTerm M p) 1 := by
  apply hasRankLE_smul
  simpa [absoluteMatrixRankOneTerm] using hasRankLE_sum_range_rankOne
    (fun _ : ℕ => HilbertSchmidt.lpBasis ℕ p.1)
    (fun _ : ℕ => HilbertSchmidt.lpBasis ℕ p.2) 1

@[simp] theorem norm_absoluteMatrixRankOneTerm
    (M : ℕ × ℕ → ℂ) (p : ℕ × ℕ) :
    ‖absoluteMatrixRankOneTerm M p‖ = ‖M p‖ := by
  rw [absoluteMatrixRankOneTerm, norm_smul, InnerProductSpace.norm_rankOne,
    (HilbertSchmidt.lpBasis ℕ).orthonormal.norm_eq_one,
    (HilbertSchmidt.lpBasis ℕ).orthonormal.norm_eq_one]
  ring

/-- Canonical operator represented by an absolutely projective matrix.  The definition is total;
the trace-class theorems below require the mathematically relevant absolute summability input. -/
noncomputable def absoluteMatrixOperator (M : ℕ × ℕ → ℂ) :
    ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert :=
  ∑' p : ℕ × ℕ, absoluteMatrixRankOneTerm M p

theorem summable_absoluteMatrixRankOneTerm {M : ℕ × ℕ → ℂ}
    (hM : Summable fun p => ‖M p‖) :
    Summable (absoluteMatrixRankOneTerm M) := by
  apply Summable.of_norm
  simpa using hM

theorem absoluteMatrixOperator_memSchattenClass_one {M : ℕ × ℕ → ℂ}
    (hM : Summable fun p => ‖M p‖) :
    MemSchattenClass 1 (absoluteMatrixOperator M) := by
  exact memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    (absoluteMatrixRankOneTerm M)
    (absoluteMatrixRankOneTerm_hasRankLE M) (by simpa using hM)

private theorem approxNumber_le_norm_sub_add_matrix
    (T S : ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert) (n : ℕ) :
    approxNumber T n ≤ ‖T - S‖ + approxNumber S n := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F, hF, hFlt⟩ := exists_hasRankLE_norm_sub_lt S n
    (lt_add_of_pos_right _ hε)
  calc
    approxNumber T n ≤ ‖T - F‖ := approxNumber_le T n F hF
    _ = ‖(T - S) + (S - F)‖ := by congr 1; abel
    _ ≤ ‖T - S‖ + ‖S - F‖ := norm_add_le _ _
    _ ≤ ‖T - S‖ + approxNumber S n + ε := by linarith

/-- Trace norm of an absolutely convergent rank-one expansion is at most its nuclear budget. -/
theorem traceNorm_tsum_rankOneTerms_le_tsum_norm
    {A : ℕ × ℕ → ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert}
    (hA : ∀ p, HasRankLE (A p) 1) (hnorm : Summable fun p => ‖A p‖) :
    traceNorm ArithmeticDilationHilbert (∑' p, A p) ≤ ∑' p, ‖A p‖ := by
  classical
  have hsum : Summable A := Summable.of_norm hnorm
  rw [traceNorm]
  apply Real.tsum_le_of_sum_le (fun n => approxNumber_nonneg _ n)
  intro s
  apply le_of_forall_pos_le_add
  intro ε hε
  let c : ℝ := s.card
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  obtain ⟨u, hu⟩ : ∃ u : Finset (ℕ × ℕ),
      c * ‖(∑' p, A p) - ∑ p ∈ u, A p‖ < ε := by
    by_cases hc : c = 0
    · exact ⟨∅, by simp [hc, hε]⟩
    · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
      have htend : Tendsto (fun u : Finset (ℕ × ℕ) => ∑ p ∈ u, A p) atTop
          (nhds (∑' p, A p)) := hsum.hasSum
      have hevent : ∀ᶠ u : Finset (ℕ × ℕ) in atTop,
          ‖(∑' p, A p) - ∑ p ∈ u, A p‖ < ε / c := by
        have hball := htend.eventually
          (Metric.ball_mem_nhds _ (div_pos hε hcpos))
        filter_upwards [hball] with u hu'
        rw [dist_eq_norm] at hu'
        simpa only [norm_sub_rev] using hu'
      obtain ⟨u, htail⟩ := hevent.exists
      exact ⟨u, by
        have heq : c * (ε / c) = ε := by field_simp [hc]
        nlinarith⟩
  let S : ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert := ∑ p ∈ u, A p
  have hpoint : ∀ n, approxNumber (∑' p, A p) n ≤
      ‖(∑' p, A p) - S‖ + approxNumber S n :=
    fun n => approxNumber_le_norm_sub_add_matrix _ _ _
  calc
    ∑ n ∈ s, approxNumber (∑' p, A p) n ≤
        ∑ n ∈ s, (‖(∑' p, A p) - S‖ + approxNumber S n) :=
      Finset.sum_le_sum fun n _ => hpoint n
    _ = c * ‖(∑' p, A p) - S‖ + ∑ n ∈ s, approxNumber S n := by
      simp [c, Finset.sum_add_distrib]
    _ ≤ c * ‖(∑' p, A p) - S‖ + traceNorm ArithmeticDilationHilbert S := by
      gcongr
      exact Summable.sum_le_tsum s (fun n _ => approxNumber_nonneg S n)
        ((memSchattenClass_of_hasRankLE one_pos
          (hasRankLE_sum_finset_of_rankOne A hA u)).congr
            (fun n => Real.rpow_one _))
    _ ≤ c * ‖(∑' p, A p) - S‖ + ∑ p ∈ u, ‖A p‖ := by
      gcongr
      exact traceNorm_sum_le_sum_norm_of_rankOneTerms A hA u
    _ ≤ c * ‖(∑' p, A p) - S‖ + ∑' p, ‖A p‖ := by
      gcongr
      exact hnorm.sum_le_tsum u (fun p _ => norm_nonneg _)
    _ ≤ ∑' p, ‖A p‖ + ε := by dsimp [S] at hu ⊢; linarith

/-- The entrywise projective norm dominates the operator trace norm. -/
theorem traceNorm_absoluteMatrixOperator_le {M : ℕ × ℕ → ℂ}
    (hM : Summable fun p => ‖M p‖) :
    traceNorm ArithmeticDilationHilbert (absoluteMatrixOperator M) ≤ ∑' p, ‖M p‖ := by
  rw [absoluteMatrixOperator]
  simpa using traceNorm_tsum_rankOneTerms_le_tsum_norm
    (absoluteMatrixRankOneTerm_hasRankLE M) (by simpa using hM)

theorem absoluteMatrixOperator_sub {M N : ℕ × ℕ → ℂ}
    (hM : Summable fun p => ‖M p‖) (hN : Summable fun p => ‖N p‖) :
    absoluteMatrixOperator (fun p => M p - N p) =
      absoluteMatrixOperator M - absoluteMatrixOperator N := by
  have hMs := summable_absoluteMatrixRankOneTerm hM
  have hNs := summable_absoluteMatrixRankOneTerm hN
  rw [absoluteMatrixOperator, absoluteMatrixOperator, absoluteMatrixOperator,
    ← hMs.tsum_sub hNs]
  apply tsum_congr
  intro p
  simp [absoluteMatrixRankOneTerm, sub_smul]

/-- Entrywise `ℓ¹` convergence gives Schatten trace-norm convergence of represented operators. -/
theorem absoluteMatrixOperator_traceNorm_tendsto
    {α : Type*} {l : Filter α} {M : α → ℕ × ℕ → ℂ} {N : ℕ × ℕ → ℂ}
    (hM : ∀ x, Summable fun p => ‖M x p‖) (hN : Summable fun p => ‖N p‖)
    (hMN : ∀ x, Summable fun p => ‖M x p - N p‖)
    (htend : Tendsto (fun x => ∑' p, ‖M x p - N p‖) l (nhds 0)) :
    Tendsto (fun x => traceNorm ArithmeticDilationHilbert
      (absoluteMatrixOperator (M x) - absoluteMatrixOperator N)) l (nhds 0) := by
  refine squeeze_zero (fun x => traceNorm_nonneg _) (fun x => ?_) htend
  rw [← absoluteMatrixOperator_sub (hM x) hN]
  exact traceNorm_absoluteMatrixOperator_le (hMN x)

/-! ## Diagonal realization and determinant -/

theorem summable_norm_diagMul_of_summable_norm {g : ℕ → ℂ}
    (hg : Summable fun n => ‖g n‖) :
    Summable fun p : ℕ × ℕ => ‖HilbertSchmidt.diagMul g p‖ := by
  have heq : (fun p : ℕ × ℕ => ‖HilbertSchmidt.diagMul g p‖) =
      diagMatrix (fun n => ‖g n‖) := by
    funext p
    by_cases h : p.1 = p.2 <;>
      simp [HilbertSchmidt.diagMul, diagMatrix, h]
  rw [heq]
  exact summable_diagMatrix hg

theorem absoluteMatrixRankOneTerm_diagMul_apply
    (g : ℕ → ℂ) (p : ℕ × ℕ) (j : ℕ) :
    absoluteMatrixRankOneTerm (HilbertSchmidt.diagMul g) p
        (HilbertSchmidt.lpBasis ℕ j) =
      if p = (j, j) then g j • HilbertSchmidt.lpBasis ℕ j else 0 := by
  have hbinner := (orthonormal_iff_ite.mp
    (HilbertSchmidt.lpBasis ℕ).orthonormal) p.2 j
  simp only [absoluteMatrixRankOneTerm, smul_apply,
    InnerProductSpace.rankOne_apply, hbinner]
  by_cases hdiag : p.1 = p.2
  · rw [HilbertSchmidt.diagMul, if_pos hdiag]
    by_cases hj : p.2 = j
    · have hp : p = (j, j) := Prod.ext (hdiag.trans hj) hj
      subst p
      simp
    · have hpne : p ≠ (j, j) := fun h => hj (congrArg Prod.snd h)
      simp [hj, hpne]
  · rw [HilbertSchmidt.diagMul, if_neg hdiag]
    have hpne : p ≠ (j, j) := fun h =>
      hdiag ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)
    simp [hpne]

/-- The canonical nuclear matrix operator has the advertised diagonal eigenbasis. -/
theorem absoluteMatrixOperator_diagMul_apply_basis
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) (j : ℕ) :
    absoluteMatrixOperator (HilbertSchmidt.diagMul g)
        (HilbertSchmidt.lpBasis ℕ j) =
      g j • HilbertSchmidt.lpBasis ℕ j := by
  rw [absoluteMatrixOperator]
  have hterms : Summable (absoluteMatrixRankOneTerm (HilbertSchmidt.diagMul g)) :=
    summable_absoluteMatrixRankOneTerm (summable_norm_diagMul_of_summable_norm hg)
  change (ContinuousLinearMap.apply ℂ ArithmeticDilationHilbert
    (HilbertSchmidt.lpBasis ℕ j))
      (∑' p, absoluteMatrixRankOneTerm (HilbertSchmidt.diagMul g) p) = _
  rw [(ContinuousLinearMap.apply ℂ ArithmeticDilationHilbert
    (HilbertSchmidt.lpBasis ℕ j)).map_tsum hterms]
  rw [tsum_eq_single (j, j)]
  · simpa using absoluteMatrixRankOneTerm_diagMul_apply g (j, j) j
  · intro p hp
    change absoluteMatrixRankOneTerm (HilbertSchmidt.diagMul g) p
      (HilbertSchmidt.lpBasis ℕ j) = 0
    rw [absoluteMatrixRankOneTerm_diagMul_apply, if_neg hp]

/-- Summable diagonal entries are square-summable, hence define the existing Hilbert--Schmidt
kernel determinant. -/
theorem summable_norm_sq_of_summable_norm {ι : Type*} {g : ι → ℂ}
    (hg : Summable fun i => ‖g i‖) : Summable fun i => ‖g i‖ ^ 2 := by
  let C : ℝ := ∑' i, ‖g i‖
  have hC0 : 0 ≤ C := tsum_nonneg fun i => norm_nonneg (g i)
  have hle : ∀ i, ‖g i‖ ≤ C := fun i =>
    hg.le_tsum i (fun j _ => norm_nonneg (g j))
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg ‖g i‖) (fun i => ?_)
    (hg.mul_left C)
  simpa [pow_two] using mul_le_mul_of_nonneg_right (hle i) (norm_nonneg (g i))

theorem toOperator_diagMul_apply_basis
    (g : ℕ → ℂ) (hs : Summable fun n => ‖g n‖ ^ 2) (j : ℕ) :
    HilbertSchmidt.toOperator (HilbertSchmidt.isHS_diagMul_infinite g hs)
        (HilbertSchmidt.lpBasis ℕ j) =
      g j • HilbertSchmidt.lpBasis ℕ j := by
  apply lp.ext
  funext i
  rw [HilbertSchmidt.lpBasis_apply,
    HilbertSchmidt.toOperator_single (HilbertSchmidt.isHS_diagMul_infinite g hs) i j]
  by_cases h : i = j
  · subst i
    simp [HilbertSchmidt.diagMul]
  · simp [HilbertSchmidt.diagMul, h]

/-- The nuclear matrix-unit sum and the Hilbert--Schmidt kernel realization are the same diagonal
operator, so its matrix spectrum and Fredholm determinant refer to one literal operator. -/
theorem absoluteMatrixOperator_diagMul_eq_toOperator
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) :
    absoluteMatrixOperator (HilbertSchmidt.diagMul g) =
      HilbertSchmidt.toOperator
        (HilbertSchmidt.isHS_diagMul_infinite g
          (summable_norm_sq_of_summable_norm hg)) := by
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (HilbertSchmidt.lpBasis ℕ).dense_span) ?_
  rintro x ⟨j, rfl⟩
  rw [absoluteMatrixOperator_diagMul_apply_basis g hg j,
    toOperator_diagMul_apply_basis g (summable_norm_sq_of_summable_norm hg) j]

/-- The nuclear diagonal matrix is exactly the corpus's bounded diagonal multiplier. -/
theorem norm_le_tsum_of_summable_norm
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) (n : ℕ) :
    ‖g n‖ ≤ ∑' j : ℕ, ‖g j‖ :=
  hg.le_tsum n (fun _ _ => norm_nonneg _)

theorem absoluteMatrixOperator_diagMul_eq_diagonalOperator
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) :
    absoluteMatrixOperator (HilbertSchmidt.diagMul g) =
      _root_.RHTower.diagonalOperator (C := ∑' j : ℕ, ‖g j‖) g
        (by intro n; exact Summable.le_tsum hg n (fun _ _ => norm_nonneg _)) := by
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (HilbertSchmidt.lpBasis ℕ).dense_span) ?_
  rintro x ⟨n, rfl⟩
  rw [absoluteMatrixOperator_diagMul_apply_basis g hg n,
    GaloisForLFunctions.RHTower.diagonalOperator_lpBasis]

/-- A summable nonnegative real diagonal gives a positive nuclear operator. -/
theorem absoluteMatrixOperator_diagMul_isPositive_ofReal
    (r : ℕ → ℝ) (hrsum : Summable fun n => ‖((r n : ℝ) : ℂ)‖)
    (hr0 : ∀ n, 0 ≤ r n) :
    (absoluteMatrixOperator (HilbertSchmidt.diagMul fun n => (r n : ℂ))).IsPositive := by
  rw [absoluteMatrixOperator_diagMul_eq_diagonalOperator _ hrsum]
  exact GaloisForLFunctions.RHTower.isPositive_diagonalOperator_ofReal r
    (norm_le_tsum_of_summable_norm _ hrsum) hr0

/-- Bare trace-class Fredholm product `det(I + z·diag(g))`. -/
noncomputable def arithmeticDiagonalFredholmDeterminant (g : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, (1 + z * g n)

theorem multipliable_arithmeticDiagonalFredholmDeterminant
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) (z : ℂ) :
    Multipliable fun n : ℕ => 1 + z * g n := by
  apply multipliable_one_add_of_summable
  simpa [norm_mul] using hg.mul_left ‖z‖

/-- The limiting determinant product converges uniformly on every compact subset of `ℂ`. -/
theorem hasProdUniformlyOn_arithmeticDiagonalFredholmDeterminant
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖)
    (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun n z => 1 + z * g n)
      (arithmeticDiagonalFredholmDeterminant g) K := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  apply Summable.hasProdUniformlyOn_one_add hK (hg.mul_left R)
  · exact Filter.Eventually.of_forall fun n z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (by simpa using hR z hz) (norm_nonneg (g n))
  · intro n
    exact (continuous_id.mul continuous_const).continuousOn

/-- Near the origin the global bare product agrees with the corpus's kernel Fredholm determinant
`det₁(I - wK)`, evaluated at `w = -z`. -/
theorem arithmeticDiagonalFredholmDeterminant_eq_fredholmDet1
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖)
    (r : ℝ)
    (hr : r * HilbertSchmidt.hsNorm (HilbertSchmidt.diagMul g) < 1)
    (z : ℂ) (hz : -z ∈ Metric.ball (0 : ℂ) r) :
    arithmeticDiagonalFredholmDeterminant g z =
      HilbertSchmidt.fredholmDet1 (HilbertSchmidt.diagMul g) (-z) := by
  rw [arithmeticDiagonalFredholmDeterminant,
    HilbertSchmidt.fredholmDet1_tprod_diagMul g
      (summable_norm_sq_of_summable_norm hg) (Summable.of_norm hg) r hr (-z) hz]
  apply tprod_congr
  intro n
  ring

/-! ## Arithmetic dilation specialization -/

/-- Symmetrized finite-aperture arithmetic matrix from the projective error `E`. -/
def arithmeticDilationComplexMatrix
    {α : Type*} (a : α → ℕ → ℝ) (E : α → ℕ → ℕ → ℝ)
    (w : ℕ → ℝ) (x : α) (p : ℕ × ℕ) : ℂ :=
  ((a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p) : ℝ)

/-- Limiting positive diagonal arithmetic matrix `κ k = 2 L k w k`. -/
def arithmeticDilationLimitComplexMatrix (L w : ℕ → ℝ) (p : ℕ × ℕ) : ℂ :=
  (diagMatrix (fun k => 2 * L k * w k) p : ℝ)

/-- **Arithmetic trace-class operator limit.**  Under exactly the weighted projective hypothesis
and divisor trap of the paper card, every arithmetic matrix and its limiting diagonal define
Schatten-1 operators, and the former converge to the latter in genuine trace norm. -/
theorem arithmeticDilation_traceClass_traceNorm_limit
    {α : Type*} {l : Filter α} {E : α → ℕ → ℕ → ℝ}
    {w L Ω : ℕ → ℝ} {a : α → ℕ → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hΩ : ∀ k, L k ≤ Ω k)
    (ha0 : ∀ x k, 0 ≤ a x k) (haL : ∀ x k, a x k ≤ L k)
    (haev : ∀ k, ∀ᶠ x in l, a x k = L k)
    (hLw : Summable fun k => L k * w k)
    (hEsum : ∀ x, Summable fun p : ℕ × ℕ =>
      (Ω p.1 + Ω p.2) * |E x p.1 p.2|)
    (hE : Tendsto (fun x => ∑' p : ℕ × ℕ,
      (Ω p.1 + Ω p.2) * |E x p.1 p.2|) l (nhds 0)) :
    (∀ x, MemSchattenClass 1
        (absoluteMatrixOperator (arithmeticDilationComplexMatrix a E w x))) ∧
      MemSchattenClass 1
        (absoluteMatrixOperator (arithmeticDilationLimitComplexMatrix L w)) ∧
      Tendsto (fun x => traceNorm ArithmeticDilationHilbert
        (absoluteMatrixOperator (arithmeticDilationComplexMatrix a E w x) -
          absoluteMatrixOperator (arithmeticDilationLimitComplexMatrix L w))) l (nhds 0) := by
  have hbound := arithmeticDilation_abs_le (E := E) hw hΩ ha0 haL
  have hdef0 : ∀ x k, 0 ≤ 2 * (L k - a x k) * w k := fun x k =>
    mul_nonneg (by linarith [haL x k]) (hw k)
  have hdefle : ∀ x k, 2 * (L k - a x k) * w k ≤ 2 * (L k * w k) := fun x k => by
    nlinarith [hw k, ha0 x k, mul_nonneg (ha0 x k) (hw k)]
  have hdefsum : Summable fun k => 2 * (L k * w k) := hLw.mul_left 2
  have hBsum : ∀ x, Summable (fun p : ℕ × ℕ =>
      (Ω p.1 + Ω p.2) * |E x p.1 p.2| +
        diagMatrix (fun k => 2 * (L k - a x k) * w k) p) := fun x =>
    (hEsum x).add (summable_diagMatrix
      (hdefsum.of_nonneg_of_le (fun k => hdef0 x k) (fun k => hdefle x k)))
  have hDabs : ∀ x, Summable (fun p : ℕ × ℕ =>
      |(a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p) -
        diagMatrix (fun k => 2 * L k * w k) p|) := fun x =>
    (hBsum x).of_nonneg_of_le (fun p => abs_nonneg _) (fun p => hbound x p)
  have hentryNorm : ∀ x p,
      ‖arithmeticDilationComplexMatrix a E w x p -
        arithmeticDilationLimitComplexMatrix L w p‖ =
      |(a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p) -
        diagMatrix (fun k => 2 * L k * w k) p| := by
    intro x p
    rw [arithmeticDilationComplexMatrix, arithmeticDilationLimitComplexMatrix]
    norm_cast
  have hdiff : ∀ x, Summable (fun p =>
      ‖arithmeticDilationComplexMatrix a E w x p -
        arithmeticDilationLimitComplexMatrix L w p‖) := fun x => by
    simpa only [hentryNorm] using hDabs x
  have hlimitNorm : Summable (fun p =>
      ‖arithmeticDilationLimitComplexMatrix L w p‖) := by
    have hdiag : Summable (diagMatrix (fun k => 2 * L k * w k)) :=
      summable_diagMatrix (by simpa [mul_assoc] using hdefsum)
    simpa [arithmeticDilationLimitComplexMatrix, Complex.norm_real, Real.norm_eq_abs,
      diagMatrix] using hdiag.norm
  have hstageNorm : ∀ x, Summable (fun p =>
      ‖arithmeticDilationComplexMatrix a E w x p‖) := fun x => by
    refine (hdiff x).add hlimitNorm |>.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    calc
      ‖arithmeticDilationComplexMatrix a E w x p‖ =
          ‖(arithmeticDilationComplexMatrix a E w x p -
              arithmeticDilationLimitComplexMatrix L w p) +
            arithmeticDilationLimitComplexMatrix L w p‖ := by ring_nf
      _ ≤ ‖arithmeticDilationComplexMatrix a E w x p -
              arithmeticDilationLimitComplexMatrix L w p‖ +
            ‖arithmeticDilationLimitComplexMatrix L w p‖ := norm_add_le _ _
  have hproj : Tendsto (fun x => ∑' p,
      ‖arithmeticDilationComplexMatrix a E w x p -
        arithmeticDilationLimitComplexMatrix L w p‖) l (nhds 0) := by
    simpa only [hentryNorm] using
      arithmeticDilation_projective_tendsto hw hΩ ha0 haL haev hLw hEsum hE
  exact ⟨fun x => absoluteMatrixOperator_memSchattenClass_one (hstageNorm x),
    absoluteMatrixOperator_memSchattenClass_one hlimitNorm,
    absoluteMatrixOperator_traceNorm_tendsto hstageNorm hlimitNorm hdiff hproj⟩

/-! ## Exact constrained-prolate arithmetic operator -/

/-- Absolute summability of the explicit positive constrained-prolate spectrum after casting to
the complex scalar field of the Hilbert space. -/
theorem summable_norm_constrainedProlateArithmeticEigenvalue_complex :
    Summable fun n : ℕ =>
      ‖((GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℝ) : ℂ)‖ := by
  convert GaloisForLFunctions.summable_constrainedProlateArithmeticEigenvalue using 1
  funext n
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_nonneg n)]

/-- Canonical positive arithmetic limit operator of the constrained-prolate card.  It is the
literal nuclear matrix-unit realization used by the projective convergence theorem. -/
noncomputable def constrainedProlateArithmeticLimitOperator :
    ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert :=
  absoluteMatrixOperator (HilbertSchmidt.diagMul fun n =>
    (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ))

theorem constrainedProlateArithmeticLimitOperator_memSchattenClass_one :
    MemSchattenClass 1 constrainedProlateArithmeticLimitOperator := by
  exact absoluteMatrixOperator_memSchattenClass_one
    (summable_norm_diagMul_of_summable_norm
      summable_norm_constrainedProlateArithmeticEigenvalue_complex)

/-- Every advertised arithmetic eigenvalue acts on its literal coordinate vector. -/
theorem constrainedProlateArithmeticLimitOperator_apply_basis (n : ℕ) :
    constrainedProlateArithmeticLimitOperator (HilbertSchmidt.lpBasis ℕ n) =
      (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ) •
        HilbertSchmidt.lpBasis ℕ n := by
  exact absoluteMatrixOperator_diagMul_apply_basis _
    summable_norm_constrainedProlateArithmeticEigenvalue_complex n

theorem norm_constrainedProlateArithmeticEigenvalue_le_tsum (n : ℕ) :
    ‖((GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℝ) : ℂ)‖ ≤
      ∑' j : ℕ,
        ‖((GaloisForLFunctions.constrainedProlateArithmeticEigenvalue j : ℝ) : ℂ)‖ :=
  summable_norm_constrainedProlateArithmeticEigenvalue_complex.le_tsum n
    (fun _ _ => norm_nonneg _)

/-- The nuclear matrix realization is exactly the corpus's bounded diagonal multiplier. -/
theorem constrainedProlateArithmeticLimitOperator_eq_diagonalOperator :
    constrainedProlateArithmeticLimitOperator =
      _root_.RHTower.diagonalOperator
        (fun n => (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ))
        norm_constrainedProlateArithmeticEigenvalue_le_tsum :=
  absoluteMatrixOperator_diagMul_eq_diagonalOperator _
    summable_norm_constrainedProlateArithmeticEigenvalue_complex

/-- The limiting arithmetic operator is positive, not merely entrywise positive. -/
theorem constrainedProlateArithmeticLimitOperator_isPositive :
    constrainedProlateArithmeticLimitOperator.IsPositive := by
  rw [constrainedProlateArithmeticLimitOperator_eq_diagonalOperator]
  exact GaloisForLFunctions.RHTower.isPositive_diagonalOperator_ofReal
    GaloisForLFunctions.constrainedProlateArithmeticEigenvalue
    norm_constrainedProlateArithmeticEigenvalue_le_tsum
    GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_nonneg

theorem constrainedProlateArithmeticLimitOperator_isSelfAdjoint :
    IsSelfAdjoint constrainedProlateArithmeticLimitOperator :=
  constrainedProlateArithmeticLimitOperator_isPositive.isSelfAdjoint

/-- Ordinary operator trace of a Schatten-1 operator is its diagonal sum in any Hilbert basis. -/
theorem opTrace_eq_tsum_basis_of_memSchattenClass_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T)
    {ι : Type*} (b : HilbertBasis ι ℂ H) :
    ContinuousLinearMap.opTrace T = ∑' i, inner ℂ (b i) (T (b i)) := by
  obtain ⟨A, B, hA, hB, hfac⟩ := hT.one_isTraceClass
  rw [hfac]
  exact ContinuousLinearMap.opTrace_comp_eq_tsum_basis hA hB b

/-- Exact trace of the canonical arithmetic operator. -/
theorem opTrace_constrainedProlateArithmeticLimitOperator :
    ContinuousLinearMap.opTrace constrainedProlateArithmeticLimitOperator =
      ((∑' n : ℕ,
        GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℝ) : ℂ) := by
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one
    constrainedProlateArithmeticLimitOperator_memSchattenClass_one
    (HilbertSchmidt.lpBasis ℕ)]
  calc
    (∑' n : ℕ, inner ℂ (HilbertSchmidt.lpBasis ℕ n)
        (constrainedProlateArithmeticLimitOperator (HilbertSchmidt.lpBasis ℕ n))) =
        ∑' n : ℕ,
          (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ) := by
      apply tsum_congr
      intro n
      rw [constrainedProlateArithmeticLimitOperator_apply_basis]
      simp [(HilbertSchmidt.lpBasis ℕ).orthonormal.norm_eq_one]
    _ = ((∑' n : ℕ,
        GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℝ) : ℂ) :=
      (Complex.ofReal_tsum _).symm

/-- The full raw radial prime charge is the negative operator trace, with the exact normalization
already established by the scalar arithmetic spectrum. -/
theorem opTrace_constrainedProlateArithmeticLimitOperator_eq_neg_primeConstant :
    ContinuousLinearMap.opTrace constrainedProlateArithmeticLimitOperator =
      (-GaloisForLFunctions.constrainedProlatePrimeConstant : ℂ) := by
  rw [opTrace_constrainedProlateArithmeticLimitOperator,
    GaloisForLFunctions.tsum_constrainedProlateArithmeticEigenvalue]
  norm_cast

/-- Global characteristic product of the constrained-prolate arithmetic spectrum. -/
noncomputable def constrainedProlateArithmeticFredholmDeterminant (z : ℂ) : ℂ :=
  arithmeticDiagonalFredholmDeterminant
    (fun n => (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)) z

theorem hasProdUniformlyOn_constrainedProlateArithmeticFredholmDeterminant
    (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn
      (fun n z => 1 + z *
        (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ))
      constrainedProlateArithmeticFredholmDeterminant K := by
  exact hasProdUniformlyOn_arithmeticDiagonalFredholmDeterminant _
    summable_norm_constrainedProlateArithmeticEigenvalue_complex K hK

theorem constrainedProlateArithmeticFredholmDeterminant_eq_fredholmDet1
    (r : ℝ)
    (hr : r * HilbertSchmidt.hsNorm (HilbertSchmidt.diagMul fun n =>
      (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)) < 1)
    (z : ℂ) (hz : -z ∈ Metric.ball (0 : ℂ) r) :
    constrainedProlateArithmeticFredholmDeterminant z =
      HilbertSchmidt.fredholmDet1 (HilbertSchmidt.diagMul fun n =>
        (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)) (-z) := by
  exact arithmeticDiagonalFredholmDeterminant_eq_fredholmDet1 _
    summable_norm_constrainedProlateArithmeticEigenvalue_complex r hr z hz

/-- Every reciprocal arithmetic eigenvalue is a zero of the global determinant product. -/
theorem constrainedProlateArithmeticFredholmDeterminant_neg_inv_eq_zero (n : ℕ) :
    constrainedProlateArithmeticFredholmDeterminant
      (-(GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)⁻¹) = 0 := by
  rw [constrainedProlateArithmeticFredholmDeterminant,
    arithmeticDiagonalFredholmDeterminant]
  apply tprod_of_exists_eq_zero
  refine ⟨n, ?_⟩
  have hn : (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_pos n)
  field_simp
  ring

end RHTower
