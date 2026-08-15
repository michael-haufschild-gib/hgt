import GaloisForLFunctions.HTGeometry.ExponentialPolynomialModes

/-!
# The characteristic Evans boundary state has infinite rank

Three exact mechanisms of the card are formalized.

*The exterior trace is a Hankel kernel.*  With `s = x - a` and `t = a - y` one has `x - y = s + t`
exactly, so the columns of the exterior trace map are precisely the **translates** of the kernel.

*Finite rank forces an exponential polynomial.*  If every Hankel column lies in one
finite-dimensional space, the translation span of the kernel is finite-dimensional, and the
Anselone–Korevaar equivalence of `AnseloneKorevaarTranslationRank` — the continuous form of
Kronecker's finite-rank Hankel theorem — makes the kernel an exponential polynomial.  It then has
finitely many frequencies and extends to an **entire** function.  Contrapositively, a kernel with no
entire extension has infinite exterior rank.

*The Gamma pole lattice is infinite.*  The digamma arguments `1/4 ± i z/2` hit a nonpositive integer
exactly on `z = ± i(2n + 1/2)`; that lattice is infinite, so it is not the zero set of any nonzero
polynomial and the corrected symbol is not rational.

The analytic ingredients — the distribution kernel of `c_a(D)`, the meromorphic continuation of the
Gamma symbol and the identification of the Laplace transform of the kernel with a half-plane branch
of `c_a` — are cited parents and stay outside the Lean statement.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The exterior trace is a Hankel kernel -/

/-- **Equation (5) → (6).**  The exterior displacement splits exactly into the two boundary
coordinates `s = x - a` and `t = a - y`. -/
theorem exterior_displacement_split (a x y : ℝ) : x - y = (x - a) + (a - y) := by ring

/-- The `s`-th column of the Hankel kernel `k(s+t)`. -/
def hankelColumn (k : ℝ → ℂ) (s : ℝ) : ℝ → ℂ := fun t => k (s + t)

/-- **Equation (6).**  The Hankel columns are exactly the translates of the kernel. -/
theorem hankelColumn_eq_realTranslate (k : ℝ → ℂ) (s : ℝ) :
    hankelColumn k s = realTranslate (-s) k := by
  funext t
  simp only [hankelColumn, realTranslate, sub_neg_eq_add]
  rw [add_comm]

/-! ## Finite rank forces an exponential polynomial -/

/-- **Section 3, Kronecker step.**  If every Hankel column lies in one finite-dimensional space,
the kernel is an exponential polynomial. -/
theorem mem_expPolySpace_of_hankelColumns {k : ℝ → ℂ} (hk : Continuous k)
    {V : Submodule ℂ (ℝ → ℂ)} [FiniteDimensional ℂ V]
    (hcol : ∀ s : ℝ, hankelColumn k s ∈ V) : k ∈ expPolySpace := by
  refine (mem_expPolySpace_iff_finiteDimensional_translationSpan hk).mpr ?_
  have hle : translationSpan k ≤ V := by
    rw [translationSpan, Submodule.span_le]
    rintro u ⟨a, rfl⟩
    have hmem := hcol (-a)
    rw [hankelColumn_eq_realTranslate, neg_neg] at hmem
    exact hmem
  exact Submodule.finiteDimensional_of_le hle

/-- **Equation (7).**  A finite-rank Hankel kernel is a finite sum of blocks: finitely many
frequencies, each with a polynomial factor. -/
theorem exists_finite_frequencies {k : ℝ → ℂ} (hk : k ∈ expPolySpace) :
    ∃ (S : Finset ℂ) (P : ℂ → Polynomial ℂ), k = ∑ μ ∈ S, polyExp (P μ) μ := by
  obtain ⟨N, S, hmem⟩ := exists_expMonomialSpace_of_mem_expPolySpace hk
  obtain ⟨P, hP⟩ := expMonomialSpace_le_blockSpan N S hmem
  exact ⟨S, P, hP⟩

/-- **Section 3, regularity step.**  A finite-rank Hankel kernel extends to an entire function: an
exponential polynomial has no singularity at all. -/
theorem exists_entire_extension_of_hankelColumns {k : ℝ → ℂ} (hk : Continuous k)
    {V : Submodule ℂ (ℝ → ℂ)} [FiniteDimensional ℂ V]
    (hcol : ∀ s : ℝ, hankelColumn k s ∈ V) :
    ∃ K : ℂ → ℂ, AnalyticOnNhd ℂ K (Set.univ : Set ℂ) ∧ ∀ x : ℝ, K (x : ℂ) = k x := by
  obtain ⟨K, hKmem, hKeq⟩ := exists_entire_extension (mem_expPolySpace_of_hankelColumns hk hcol)
  exact ⟨K, analyticOnNhd_of_mem_expPolySpaceC hKmem, hKeq⟩

/-- **The infinite-rank theorem.**  A continuous kernel admitting no entire extension has no
finite-dimensional space containing all of its Hankel columns: the exterior trace map has infinite
rank. -/
theorem not_hankelColumns_finiteDimensional {k : ℝ → ℂ} (hk : Continuous k)
    (hno : ∀ K : ℂ → ℂ, (∀ x : ℝ, K (x : ℂ) = k x) → ¬ AnalyticOnNhd ℂ K (Set.univ : Set ℂ))
    (V : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ V] :
    ¬ (∀ s : ℝ, hankelColumn k s ∈ V) := by
  intro hcol
  obtain ⟨K, hKan, hKeq⟩ := exists_entire_extension_of_hankelColumns hk hcol
  exact hno K hKeq hKan

/-! ## The infinite Gamma pole lattice -/

/-- **Equation (4), right branch.**  The first digamma argument is a nonpositive integer exactly on
the upper lattice point. -/
theorem digammaArgument_eq_neg_natCast_iff (z : ℂ) (n : ℕ) :
    (1 : ℂ) / 4 + Complex.I * z / 2 = -(n : ℂ)
      ↔ z = Complex.I * (2 * (n : ℂ) + 1 / 2) := by
  constructor
  · intro h
    have hI : Complex.I * (Complex.I * z) = -z := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    have h2 : Complex.I * z = -2 * (n : ℂ) - 1 / 2 := by linear_combination 2 * h
    have h3 : Complex.I * (Complex.I * z) = Complex.I * (-2 * (n : ℂ) - 1 / 2) := by rw [h2]
    rw [hI] at h3
    linear_combination -h3
  · intro h
    rw [h]
    have hI : Complex.I * (Complex.I * (2 * (n : ℂ) + 1 / 2)) = -(2 * (n : ℂ) + 1 / 2) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    linear_combination hI / 2

/-- **Equation (4), left branch.** -/
theorem digammaArgumentNeg_eq_neg_natCast_iff (z : ℂ) (n : ℕ) :
    (1 : ℂ) / 4 - Complex.I * z / 2 = -(n : ℂ)
      ↔ z = -(Complex.I * (2 * (n : ℂ) + 1 / 2)) := by
  constructor
  · intro h
    have hI : Complex.I * (Complex.I * z) = -z := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    have h2 : Complex.I * z = 2 * (n : ℂ) + 1 / 2 := by linear_combination -2 * h
    have h3 : Complex.I * (Complex.I * z) = Complex.I * (2 * (n : ℂ) + 1 / 2) := by rw [h2]
    rw [hI] at h3
    linear_combination -h3
  · intro h
    rw [h]
    have hI : Complex.I * (Complex.I * (2 * (n : ℂ) + 1 / 2)) = -(2 * (n : ℂ) + 1 / 2) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    linear_combination hI / 2

/-- The Gamma pole lattice `(4)`. -/
def gammaPoleLattice : Set ℂ :=
  {z : ℂ | ∃ n : ℕ, z = Complex.I * (2 * (n : ℂ) + 1 / 2)}

/-- **Equation (4), infiniteness.** -/
theorem gammaPoleLattice_infinite : gammaPoleLattice.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => Complex.I * (2 * (n : ℂ) + 1 / 2)) ?_ ?_
  · intro m n hmn
    have h := mul_left_cancel₀ Complex.I_ne_zero hmn
    have h2 : (m : ℂ) = (n : ℂ) := by linear_combination h / 2
    exact_mod_cast h2
  · intro n
    exact ⟨n, rfl⟩

/-- **Section 1, conclusion.**  The pole lattice is not the zero set of any nonzero polynomial, so
the corrected symbol is not rational. -/
theorem not_subset_rootSet_of_gammaPoleLattice {q : Polynomial ℂ} (hq : q ≠ 0) :
    ¬ (gammaPoleLattice ⊆ {z : ℂ | q.eval z = 0}) := by
  intro hsub
  exact hq (Polynomial.eq_zero_of_infinite_isRoot q
    (Set.Infinite.mono hsub gammaPoleLattice_infinite))

end GaloisForLFunctions.RHTower

end
