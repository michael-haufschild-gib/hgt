import GaloisForLFunctions.HTGeometry.FiniteRankDeterminantCompletion
import GaloisForLFunctions.HTGeometry.FiniteRankTracePrescriptionInfinite

/-!
# Nonreal finite divisors are dense in traceless Hilbert--Schmidt approximations

Finite support, exact diagonal-trace cancellation, and arbitrarily accurate Hilbert--Schmidt
approximation do not select real ordinary Fredholm divisors, even near a fixed nonzero target.

Given any Hilbert--Schmidt kernel, first approximate it by a traceless finite-support kernel. Two
fresh coordinates then carry an isolated diagonal pair `ir,-ir`. Its trace is zero, its norm can be
made arbitrarily small, and the first fresh column of the ordinary pencil vanishes at `z=-i/r`.
Thus spectrally bad traceless finite stages are dense around every Hilbert--Schmidt source.
-/

open Complex Matrix

namespace HilbertSchmidt

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Isolated traceless pair with eigenvalues `ir` and `-ir` on two chosen coordinates. -/
def imaginaryPairBlock (a b : ι) (r : ℝ) : ι × ι → ℂ :=
  fun p => if p = (a, a) then (r : ℂ) * I
    else if p = (b, b) then -((r : ℂ) * I) else 0

theorem imaginaryPairBlock_eq_zero_of_notMem {a b : ι} (r : ℝ) {p : ι × ι}
    (hp : p ∉ ({a, b} : Finset ι) ×ˢ ({a, b} : Finset ι)) :
    imaginaryPairBlock a b r p = 0 := by
  rw [imaginaryPairBlock]
  split_ifs with hpa hpb
  · subst p
    exact absurd (Finset.mem_product.mpr (by simp)) hp
  · subst p
    exact absurd (Finset.mem_product.mpr (by simp)) hp
  · rfl

theorem isHS_imaginaryPairBlock (a b : ι) (r : ℝ) :
    IsHS (imaginaryPairBlock a b r) := by
  refine isHS_of_support_subset (({a, b} : Finset ι) ×ˢ ({a, b} : Finset ι)) ?_
  exact fun p hp => imaginaryPairBlock_eq_zero_of_notMem r hp

theorem hsNormSq_imaginaryPairBlock {a b : ι} (hab : a ≠ b) (r : ℝ) :
    hsNormSq (imaginaryPairBlock a b r) = 2 * r ^ (2 : ℕ) := by
  rw [hsNormSq, tsum_eq_sum
    (s := ({(a, a), (b, b)} : Finset (ι × ι))) (fun p hp => ?_)]
  · simp [imaginaryPairBlock, hab, Ne.symm hab, Complex.norm_real]
    ring
  · rw [imaginaryPairBlock]
    split_ifs with hpa hpb
    · subst p
      exact (hp (by simp)).elim
    · subst p
      exact (hp (by simp)).elim
    · simp

theorem hsTraceDiag_imaginaryPairBlock {a b : ι} (hab : a ≠ b) (r : ℝ) :
    hsTraceDiag (imaginaryPairBlock a b r) = 0 := by
  rw [hsTraceDiag, tsum_eq_sum (s := ({a, b} : Finset ι)) (fun i hi => ?_)]
  · simp [imaginaryPairBlock, hab, Ne.symm hab]
  · rw [imaginaryPairBlock]
    split_ifs with hia hib
    · have hai : i = a := congrArg Prod.fst hia
      exact (hi (by simp [hai])).elim
    · have hbi : i = b := congrArg Prod.fst hib
      exact (hi (by simp [hbi])).elim
    · rfl

omit [DecidableEq ι] in
private theorem exists_fresh [Infinite ι] (s : Finset ι) : ∃ a, a ∉ s := by
  by_contra h
  push Not at h
  exact Set.infinite_univ (s.finite_toSet.subset (by
    intro x _
    exact h x))

/-- A matrix with one identically zero column has zero determinant. -/
theorem det_eq_zero_of_column_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (a : n) (h : ∀ i, M i a = 0) : M.det = 0 := by
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  rw [Finset.prod_eq_zero (Finset.mem_univ a)]
  · simp
  · exact h (σ a)

/-- Traceless finite-support kernels having a nonreal ordinary Fredholm divisor are dense around
every Hilbert--Schmidt kernel on an infinite coordinate carrier. -/
theorem exists_finiteSupport_traceZero_nonrealDivisor_close
    [Infinite ι] {K : ι × ι → ℂ} (hK : IsHS K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ι) (K' : ι × ι → ℂ) (z : ℂ),
      (∀ p, p ∉ s ×ˢ s → K' p = 0) ∧
      IsHS K' ∧
      hsNorm (K' - K) < ε ∧
      hsTraceDiag K' = 0 ∧
      ((1 : Matrix ↥s ↥s ℂ) - z • blockMatrix K' s).det = 0 ∧
      z.im ≠ 0 := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨s, T, hTsupp, hTHS, hTclose, hTtrace⟩ :=
    exists_finiteSupport_hsNorm_sub_lt_and_hsTraceDiag_eq_of_infinite
      hK (0 : ℂ) hhalf
  obtain ⟨a, ha⟩ := exists_fresh s
  obtain ⟨b, hb⟩ := exists_fresh (insert a s)
  simp only [Finset.mem_insert, not_or] at hb
  rcases hb with ⟨hba, hbs⟩
  let r : ℝ := ε / 8
  let B : ι × ι → ℂ := imaginaryPairBlock a b r
  let s' : Finset ι := insert a (insert b s)
  let K' : ι × ι → ℂ := T + B
  let z : ℂ := -(I : ℂ) / (r : ℂ)
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨s', K', z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hps : p ∉ s ×ˢ s := by
      intro hmem
      rcases Finset.mem_product.mp hmem with ⟨h1, h2⟩
      exact hp (Finset.mem_product.mpr (by simp [s', h1, h2]))
    have hpab : p ∉ ({a, b} : Finset ι) ×ˢ ({a, b} : Finset ι) := by
      intro hmem
      rcases Finset.mem_product.mp hmem with ⟨h1, h2⟩
      exact hp (Finset.mem_product.mpr (by
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 ⊢
        aesop))
    change T p + imaginaryPairBlock a b r p = 0
    rw [hTsupp p hps, imaginaryPairBlock_eq_zero_of_notMem r hpab, add_zero]
  · exact isHS_add hTHS (isHS_imaginaryPairBlock a b r)
  · have hsplit : K' - K = (T - K) + B := by
      funext p
      simp [K', B]
      ring
    rw [hsplit]
    have hB : hsNorm B < ε / 2 := by
      rw [show B = imaginaryPairBlock a b r from rfl, hsNorm,
        hsNormSq_imaginaryPairBlock (Ne.symm hba)]
      have hsqrt : Real.sqrt (2 * r ^ (2 : ℕ)) ≤ 2 * r := by
        apply (Real.sqrt_le_iff).2
        constructor
        · positivity
        · nlinarith
      calc
        Real.sqrt (2 * r ^ (2 : ℕ)) ≤ 2 * r := hsqrt
        _ < ε / 2 := by dsimp [r]; linarith
    have hadd := hsNorm_add_le (isHS_sub hTHS hK)
      (isHS_imaginaryPairBlock a b r)
    linarith
  · have hsumT : Summable fun i : ι => T (i, i) :=
      summable_diag_of_finset_support (s := s) fun i hi =>
        hTsupp (i, i) (fun hmem => hi (Finset.mem_product.mp hmem).1)
    have hsumB : Summable fun i : ι => B (i, i) := by
      apply summable_diag_of_finset_support (s := ({a, b} : Finset ι))
      intro i hi
      change imaginaryPairBlock a b r (i, i) = 0
      exact imaginaryPairBlock_eq_zero_of_notMem r (by simp [hi])
    change hsTraceDiag (T + B) = 0
    rw [hsTraceDiag]
    change (∑' i : ι, (fun j => T (j, j) + B (j, j)) i) = 0
    rw [hsumT.tsum_add hsumB]
    change hsTraceDiag T + hsTraceDiag B = 0
    rw [hTtrace, show hsTraceDiag B = 0 by
      exact hsTraceDiag_imaginaryPairBlock (Ne.symm hba) r]
    simp
  · let aa : ↥s' := ⟨a, by simp [s']⟩
    apply det_eq_zero_of_column_eq_zero _ aa
    intro i
    by_cases hia : (i : ι) = a
    · have hi_eq : i = aa := Subtype.ext hia
      subst i
      have hTaa : T (a, a) = 0 := by
        apply hTsupp
        intro hmem
        exact ha (Finset.mem_product.mp hmem).1
      have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      simp [blockMatrix, K', B, imaginaryPairBlock, z, aa, hTaa]
      field_simp [hrc]
      simp [Complex.I_sq]
    · have hTa : T ((i : ι), a) = 0 := by
        apply hTsupp
        intro hmem
        exact ha (Finset.mem_product.mp hmem).2
      have hiaa : i ≠ aa := by
        intro h
        exact hia (congrArg Subtype.val h)
      simp [blockMatrix, K', B, imaginaryPairBlock, z, aa, hia, hiaa, hTa,
        Ne.symm hba]
  · change (-(I : ℂ) / (r : ℂ)).im ≠ 0
    simp [hr.ne']

end

end HilbertSchmidt
