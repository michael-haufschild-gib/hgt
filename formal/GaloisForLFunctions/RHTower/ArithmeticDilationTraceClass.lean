import GaloisForLFunctions.RHTower.ArithmeticDilationProjectiveLimit
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

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

end RHTower
