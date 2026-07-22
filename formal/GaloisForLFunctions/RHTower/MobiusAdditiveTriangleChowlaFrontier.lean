import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangleSubpower

/-!
# Binary-Chowla decomposition of the additive Möbius triangle

The cumulative additive triangle splits exactly into its diagonal squarefree mass and twice one
strict off-diagonal half.  The diagonal is only linear, so the unresolved `N^(1+o(1))` source is
precisely a one-sided square-root-scale bound for the aggregated binary Möbius correlations.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Equal-coordinate part of one additive Möbius antidiagonal. -/
def mobiusAdditiveDiagonalConvolution (k : ℕ) : ℂ :=
  ∑ mn ∈ (Finset.antidiagonal k).filter (fun mn => mn.1 = mn.2),
    mobiusComplexCoefficient mn.1 * mobiusComplexCoefficient mn.2

/-- One strict-order half of one additive Möbius antidiagonal. -/
def mobiusAdditiveStrictOffDiagonalConvolution (k : ℕ) : ℂ :=
  ∑ mn ∈ (Finset.antidiagonal k).filter (fun mn => mn.1 < mn.2),
    mobiusComplexCoefficient mn.1 * mobiusComplexCoefficient mn.2

/-- The two strict-order halves have equal sums by coordinate exchange. -/
theorem sum_mobiusAdditiveConvolution_gt_eq_strictOffDiagonal (k : ℕ) :
    (∑ mn ∈ (Finset.antidiagonal k).filter (fun mn => mn.2 < mn.1),
      mobiusComplexCoefficient mn.1 * mobiusComplexCoefficient mn.2) =
        mobiusAdditiveStrictOffDiagonalConvolution k := by
  rw [mobiusAdditiveStrictOffDiagonalConvolution]
  apply Finset.sum_equiv (Equiv.prodComm ℕ ℕ)
  · intro mn
    constructor
    · intro h
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at h ⊢
      exact ⟨by simpa [add_comm] using h.1, h.2⟩
    · intro h
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at h ⊢
      exact ⟨by simpa [add_comm] using h.1, h.2⟩
  · intro mn _hmn
    rcases mn with ⟨m, n⟩
    change mobiusComplexCoefficient m * mobiusComplexCoefficient n =
      mobiusComplexCoefficient n * mobiusComplexCoefficient m
    ring

/-- Exact diagonal/off-diagonal split of one additive convolution coefficient. -/
theorem mobiusAdditiveConvolution_eq_diagonal_add_two_mul_strictOffDiagonal (k : ℕ) :
    mobiusAdditiveConvolution k =
      mobiusAdditiveDiagonalConvolution k +
        2 * mobiusAdditiveStrictOffDiagonalConvolution k := by
  let A := Finset.antidiagonal k
  let f : ℕ × ℕ → ℂ := fun mn =>
    mobiusComplexCoefficient mn.1 * mobiusComplexCoefficient mn.2
  have hfirst := Finset.sum_filter_add_sum_filter_not A (fun mn => mn.1 < mn.2) f
  have hsecond := Finset.sum_filter_add_sum_filter_not
    (A.filter fun mn => ¬ mn.1 < mn.2) (fun mn => mn.1 = mn.2) f
  have hEq :
      (A.filter fun mn => ¬ mn.1 < mn.2).filter (fun mn => mn.1 = mn.2) =
        A.filter (fun mn => mn.1 = mn.2) := by
    ext mn
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hA, _hnot⟩, heq⟩
      exact ⟨hA, heq⟩
    · rintro ⟨hA, heq⟩
      exact ⟨⟨hA, by omega⟩, heq⟩
  have hGt :
      (A.filter fun mn => ¬ mn.1 < mn.2).filter (fun mn => ¬ mn.1 = mn.2) =
        A.filter (fun mn => mn.2 < mn.1) := by
    ext mn
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hA, hnotLt⟩, hne⟩
      exact ⟨hA, by omega⟩
    · rintro ⟨hA, hgt⟩
      exact ⟨⟨hA, by omega⟩, by omega⟩
  rw [hEq, hGt] at hsecond
  have hpartition :
      ∑ mn ∈ A, f mn =
        (∑ mn ∈ A.filter (fun mn => mn.1 < mn.2), f mn) +
        (∑ mn ∈ A.filter (fun mn => mn.1 = mn.2), f mn) +
        (∑ mn ∈ A.filter (fun mn => mn.2 < mn.1), f mn) := by
    rw [← hfirst, ← hsecond]
    ring
  rw [mobiusAdditiveConvolution]
  change (∑ mn ∈ A, f mn) = _
  rw [hpartition]
  rw [show (∑ mn ∈ A.filter (fun mn => mn.2 < mn.1), f mn) =
      mobiusAdditiveStrictOffDiagonalConvolution k by
    simpa [A, f] using sum_mobiusAdditiveConvolution_gt_eq_strictOffDiagonal k]
  simp only [mobiusAdditiveDiagonalConvolution,
    mobiusAdditiveStrictOffDiagonalConvolution, A, f]
  ring

/-- Cumulative diagonal mass in the additive triangle. -/
def mobiusAdditiveDiagonalTriangle (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), mobiusAdditiveDiagonalConvolution k

/-- Cumulative strict off-diagonal half of the additive triangle. -/
def mobiusAdditiveStrictOffDiagonalTriangle (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), mobiusAdditiveStrictOffDiagonalConvolution k

/-- Exact cumulative decomposition: diagonal squarefree mass plus twice one off-diagonal half. -/
theorem mobiusAdditiveTriangle_eq_diagonal_add_two_mul_strictOffDiagonal (N : ℕ) :
    mobiusAdditiveTriangle N =
      mobiusAdditiveDiagonalTriangle N +
        2 * mobiusAdditiveStrictOffDiagonalTriangle N := by
  rw [mobiusAdditiveTriangle, mobiusAdditiveDiagonalTriangle,
    mobiusAdditiveStrictOffDiagonalTriangle]
  simp_rw [mobiusAdditiveConvolution_eq_diagonal_add_two_mul_strictOffDiagonal]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]

/-- Each antidiagonal contains at most one diagonal pair, whose Möbius-square norm is at most one. -/
theorem norm_mobiusAdditiveDiagonalConvolution_le_one (k : ℕ) :
    ‖mobiusAdditiveDiagonalConvolution k‖ ≤ 1 := by
  let D := (Finset.antidiagonal k).filter (fun mn => mn.1 = mn.2)
  have hcard : D.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    dsimp [D] at ha hb
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha hb
    apply Prod.ext
    · omega
    · omega
  rw [mobiusAdditiveDiagonalConvolution]
  change ‖∑ mn ∈ D, mobiusComplexCoefficient mn.1 * mobiusComplexCoefficient mn.2‖ ≤ 1
  calc
    ‖∑ mn ∈ D, mobiusComplexCoefficient mn.1 * mobiusComplexCoefficient mn.2‖ ≤
        ∑ mn ∈ D, ‖mobiusComplexCoefficient mn.1 * mobiusComplexCoefficient mn.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _mn ∈ D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro mn _hmn
      rw [norm_mul]
      nlinarith [norm_mobiusComplexCoefficient_le_one mn.1,
        norm_mobiusComplexCoefficient_le_one mn.2,
        norm_nonneg (mobiusComplexCoefficient mn.1),
        norm_nonneg (mobiusComplexCoefficient mn.2)]
    _ = D.card := by simp
    _ ≤ 1 := by exact_mod_cast hcard

/-- The full diagonal contribution is unconditionally at most linear. -/
theorem norm_mobiusAdditiveDiagonalTriangle_le (N : ℕ) :
    ‖mobiusAdditiveDiagonalTriangle N‖ ≤ (N : ℝ) + 1 := by
  rw [mobiusAdditiveDiagonalTriangle]
  calc
    ‖∑ k ∈ Finset.range (N + 1), mobiusAdditiveDiagonalConvolution k‖ ≤
        ∑ k ∈ Finset.range (N + 1), ‖mobiusAdditiveDiagonalConvolution k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (N + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact norm_mobiusAdditiveDiagonalConvolution_le_one k
    _ = (N : ℝ) + 1 := by simp

/-- Fixed-degree quantitative version of the one-sided off-diagonal binary-Chowla source. -/
def MobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound (q : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (mobiusAdditiveStrictOffDiagonalTriangle N).re ≤
      C * ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ (2 * q)

/-- A fixed-degree off-diagonal bound gives the full additive-triangle bound of the same degree;
the diagonal is absorbed using the positive constant `log(2)^(-2q)`. -/
theorem
    mobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound_implies_triangleLinearPolylogUpperBound
    {q : ℕ} (hoff : MobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound q) :
    MobiusAdditiveTriangleLinearPolylogUpperBound q := by
  obtain ⟨C, hC, hOff⟩ := hoff
  let L : ℝ := Real.log 2 ^ (2 * q)
  let K : ℝ := L⁻¹ + 2 * C
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro N
  let y : ℝ := (N : ℝ) + 1
  let P : ℝ := Real.log ((N : ℝ) + 2) ^ (2 * q)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have harg : (2 : ℝ) ≤ (N : ℝ) + 2 := by linarith
  have hlogLe : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact hN.trans_lt (by linarith)
    · exact harg
  have hP : L ≤ P := by
    dsimp [L, P]
    exact pow_le_pow_left₀ hlogTwo.le hlogLe _
  have hOne : 1 ≤ L⁻¹ * P := by
    calc
      1 = L⁻¹ * L := (inv_mul_cancel₀ hL.ne').symm
      _ ≤ L⁻¹ * P := mul_le_mul_of_nonneg_left hP (inv_nonneg.mpr hL.le)
  have hDiag : (mobiusAdditiveDiagonalTriangle N).re ≤ y := by
    exact (Complex.re_le_norm _).trans
      (by simpa only [y] using norm_mobiusAdditiveDiagonalTriangle_le N)
  have hSplit := congrArg Complex.re
    (mobiusAdditiveTriangle_eq_diagonal_add_two_mul_strictOffDiagonal N)
  norm_num [Complex.add_re, Complex.mul_re] at hSplit
  have hOff' : (mobiusAdditiveStrictOffDiagonalTriangle N).re ≤ C * y * P := by
    simpa only [y, P] using hOff N
  calc
    (mobiusAdditiveTriangle N).re =
        (mobiusAdditiveDiagonalTriangle N).re +
          2 * (mobiusAdditiveStrictOffDiagonalTriangle N).re := hSplit
    _ ≤ y + 2 * (C * y * P) := by gcongr
    _ ≤ (L⁻¹ * P) * y + 2 * (C * y * P) := by
      nlinarith [mul_le_mul_of_nonneg_right hOne hy]
    _ = K * ((N : ℝ) + 1) * Real.log ((N : ℝ) + 2) ^ (2 * q) := by
      dsimp [K, y, P]
      ring

/-- Quantitative aggregated binary-Chowla cancellation of degree `2q` implies RH and caps every
critical-line zeta-zero multiplicity by `q+1`. -/
theorem mobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound_implies_RH_and_multiplicityCap
    {q : ℕ} (hoff : MobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound q) :
    RiemannHypothesis ∧
      ∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
        (analyticOrderAt riemannZeta rho).toNat ≤ q + 1 :=
  mobiusAdditiveTriangleLinearPolylogUpperBound_implies_RH_and_multiplicityCap
    (mobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound_implies_triangleLinearPolylogUpperBound
      hoff)

/-- One-sided square-root-scale control of the aggregated strict off-diagonal binary Möbius
correlations. -/
def MobiusAdditiveStrictOffDiagonalSubpowerUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (mobiusAdditiveStrictOffDiagonalTriangle N).re ≤
      C * ((N : ℝ) + 1) ^ (1 + ε)

/-- Off-diagonal subpower control is exactly sufficient after paying the harmless linear diagonal. -/
theorem mobiusAdditiveStrictOffDiagonalSubpowerUpperBound_implies_triangleSubpowerUpperBound
    (hoff : MobiusAdditiveStrictOffDiagonalSubpowerUpperBound) :
    MobiusAdditiveTriangleSubpowerUpperBound := by
  intro ε hε
  obtain ⟨C, hC, hOff⟩ := hoff ε hε
  refine ⟨1 + 2 * C, by positivity, ?_⟩
  intro N
  let y : ℝ := (N : ℝ) + 1
  have hy : 1 ≤ y := by
    dsimp [y]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hyPos : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hyPow : y ≤ y ^ (1 + ε) := by
    rw [Real.rpow_add hyPos, Real.rpow_one]
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hy hε.le)
  have hDiag : (mobiusAdditiveDiagonalTriangle N).re ≤ y := by
    exact (Complex.re_le_norm _).trans
      (by simpa only [y] using norm_mobiusAdditiveDiagonalTriangle_le N)
  have hSplit := congrArg Complex.re
    (mobiusAdditiveTriangle_eq_diagonal_add_two_mul_strictOffDiagonal N)
  norm_num [Complex.add_re, Complex.mul_re] at hSplit
  calc
    (mobiusAdditiveTriangle N).re =
        (mobiusAdditiveDiagonalTriangle N).re +
          2 * (mobiusAdditiveStrictOffDiagonalTriangle N).re := hSplit
    _ ≤ y + 2 * (C * y ^ (1 + ε)) := by
      gcongr
      simpa only [y] using hOff N
    _ ≤ y ^ (1 + ε) + 2 * (C * y ^ (1 + ε)) := by linarith
    _ = (1 + 2 * C) * ((N : ℝ) + 1) ^ (1 + ε) := by
      dsimp [y]
      ring

/-- **Binary-Chowla frontier criterion for RH.** The one-sided optimal-scale aggregate of strict
off-diagonal Möbius pairs implies RH. -/
theorem mobiusAdditiveStrictOffDiagonalSubpowerUpperBound_implies_riemannHypothesis
    (hoff : MobiusAdditiveStrictOffDiagonalSubpowerUpperBound) :
    RiemannHypothesis :=
  mobiusAdditiveTriangleSubpowerUpperBound_implies_riemannHypothesis
    (mobiusAdditiveStrictOffDiagonalSubpowerUpperBound_implies_triangleSubpowerUpperBound hoff)

end

end RHTower
