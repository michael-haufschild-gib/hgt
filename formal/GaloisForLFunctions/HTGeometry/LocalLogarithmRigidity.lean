import GaloisForLFunctions.HTGeometry.PhaseBandwidthInfimum
import GaloisForLFunctions.HTGeometry.HistogramCentralizerDimension

/-!
# Rigidity of exact local logarithms

If a real number `r` makes every anchored spectral gap an integer multiple of `2π/r`, then all the
gaps lie on a single rational line, so their rational span is at most one-dimensional.  Two-gap
irrationality therefore forces `r = 0`: the only exact local logarithm has the physical slope.

Once the slope is fixed, the residual constants are all equal, so the logarithm differs from
physical time by a scalar, and a scalar shift does not change the spectral diameter.  The collision
case is separate arithmetic: two real numbers with the same exponential differ by `2π`, so a strict
diameter bound below `2π` forces them to be equal.
-/

open Module

namespace GaloisForLFunctions.HTGeometry

/-! ## Commensurable gaps span one rational line -/

/-- If `r` scales every gap into `2πℤ`, every gap is a rational multiple of `2π/r`. -/
theorem span_le_of_commensurable {ι : Type*} (g : ι → ℝ) {r : ℝ} (hr : r ≠ 0) {m : ι → ℤ}
    (h : ∀ j, r * g j = 2 * Real.pi * (m j : ℝ)) :
    Submodule.span ℚ (Set.range g) ≤ Submodule.span ℚ ({2 * Real.pi / r} : Set ℝ) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hgj : g j = ((m j : ℚ) : ℝ) * (2 * Real.pi / r) := by
    have hrj := h j
    field_simp
    push_cast
    linarith [hrj]
  rw [hgj]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- **Two-gap irrationality forces the physical slope.**  If the anchored gaps span a rational space
of dimension at least two, no nonzero `r` can push every gap into `2πℤ`. -/
theorem eq_zero_of_two_dim_span {ι : Type*} (g : ι → ℝ) {r : ℝ} {m : ι → ℤ}
    (h : ∀ j, r * g j = 2 * Real.pi * (m j : ℝ))
    (hdim : 2 ≤ finrank ℚ (Submodule.span ℚ (Set.range g))) : r = 0 := by
  by_contra hr
  have hle := span_le_of_commensurable g hr h
  have hfin : FiniteDimensional ℚ (Submodule.span ℚ ({2 * Real.pi / r} : Set ℝ)) := by
    rw [show ({2 * Real.pi / r} : Set ℝ) = {(2 * Real.pi / r : ℝ)} from rfl]
    exact Module.Finite.span_singleton ℚ _
  have hmono := Submodule.finrank_mono hle
  have hone : finrank ℚ (Submodule.span ℚ ({2 * Real.pi / r} : Set ℝ)) ≤ 1 := by
    have hcard := finrank_span_le_card (R := ℚ) ({2 * Real.pi / r} : Set ℝ)
    simpa using hcard
  omega

/-! ## The residual constant -/

/-- Once the slope is physical, all the winding integers coincide. -/
theorem winding_const {ι : Type*} [Nonempty ι] {b φ : ℝ} {m : ι → ℤ}
    (h : ∀ j, b + φ = 2 * Real.pi * (m j : ℝ)) (j k : ι) : m j = m k := by
  have hj := h j
  have hk := h k
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have : (2 * Real.pi) * (m j : ℝ) = (2 * Real.pi) * (m k : ℝ) := by linarith
  have hcast : ((m j : ℤ) : ℝ) = ((m k : ℤ) : ℝ) :=
    mul_left_cancel₀ (ne_of_gt hpi) this
  exact_mod_cast hcast

/-! ## Scalar shifts do not change the spectral diameter -/

section Diameter

variable {ι : Type*} [Fintype ι] (hne : (Finset.univ : Finset ι).Nonempty)

theorem sup'_affine_of_nonneg (E : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    (Finset.univ.sup' hne fun j => t * E j + c) = t * (Finset.univ.sup' hne E) + c := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun j _ => ?_
    have hj := Finset.le_sup' E (Finset.mem_univ j)
    nlinarith [hj, ht]
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hne E
    rw [hjeq]
    exact Finset.le_sup' (fun j => t * E j + c) hj

theorem inf'_affine_of_nonneg (E : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    (Finset.univ.inf' hne fun j => t * E j + c) = t * (Finset.univ.inf' hne E) + c := by
  refine le_antisymm ?_ ?_
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hne E
    rw [hjeq]
    exact Finset.inf'_le (fun j => t * E j + c) hj
  · refine Finset.le_inf' _ _ fun j _ => ?_
    have hj := Finset.inf'_le E (Finset.mem_univ j)
    nlinarith [hj, ht]

theorem sup'_affine_of_nonpos (E : ι → ℝ) {t : ℝ} (ht : t ≤ 0) (c : ℝ) :
    (Finset.univ.sup' hne fun j => t * E j + c) = t * (Finset.univ.inf' hne E) + c := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun j _ => ?_
    have hj := Finset.inf'_le E (Finset.mem_univ j)
    nlinarith [hj, ht]
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hne E
    rw [hjeq]
    exact Finset.le_sup' (fun j => t * E j + c) hj

theorem inf'_affine_of_nonpos (E : ι → ℝ) {t : ℝ} (ht : t ≤ 0) (c : ℝ) :
    (Finset.univ.inf' hne fun j => t * E j + c) = t * (Finset.univ.sup' hne E) + c := by
  refine le_antisymm ?_ ?_
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hne E
    rw [hjeq]
    exact Finset.inf'_le (fun j => t * E j + c) hj
  · refine Finset.le_inf' _ _ fun j _ => ?_
    have hj := Finset.le_sup' E (Finset.mem_univ j)
    nlinarith [hj, ht]

/-- **`(10)`: the spectral diameter of `tH + cI` is `|t|` times that of `H`.** -/
theorem diam_affine (E : ι → ℝ) (t c : ℝ) :
    (Finset.univ.sup' hne fun j => t * E j + c) - (Finset.univ.inf' hne fun j => t * E j + c)
      = |t| * ((Finset.univ.sup' hne E) - (Finset.univ.inf' hne E)) := by
  rcases le_total 0 t with ht | ht
  · rw [sup'_affine_of_nonneg hne E ht c, inf'_affine_of_nonneg hne E ht c, abs_of_nonneg ht]
    ring
  · rw [sup'_affine_of_nonpos hne E ht c, inf'_affine_of_nonpos hne E ht c, abs_of_nonpos ht]
    ring

end Diameter

/-! ## The collision case -/

/-- Two real phases with the same exponential differ by a multiple of `2π`. -/
theorem exists_int_of_expI_eq {x y : ℝ}
    (hexp : Complex.exp (-(x : ℂ) * Complex.I) = Complex.exp (-(y : ℂ) * Complex.I)) :
    ∃ k : ℤ, x - y = -((k : ℝ) * (2 * Real.pi)) := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hdiv : (-(x : ℂ)) = (-(y : ℂ)) + (k : ℂ) * (2 * (Real.pi : ℂ)) := by
    refine mul_right_cancel₀ Complex.I_ne_zero ?_
    rw [add_mul]
    linear_combination hk
  have hreal : -x = -y + (k : ℝ) * (2 * Real.pi) := by exact_mod_cast hdiv
  exact ⟨k, by linarith⟩

/-- **Two real numbers with the same exponential and separation below `2π` are equal.**  This is the
strict diameter step of the collision-complete dichotomy. -/
theorem eq_of_exp_eq_of_abs_sub_lt {x y : ℝ}
    (hexp : Complex.exp (-(x : ℂ) * Complex.I) = Complex.exp (-(y : ℂ) * Complex.I))
    (hlt : |x - y| < 2 * Real.pi) : x = y := by
  obtain ⟨k, hxy⟩ := exists_int_of_expI_eq hexp
  rcases eq_or_ne k 0 with hk0 | hk0
  · rw [hk0] at hxy
    push_cast at hxy
    linarith
  · exfalso
    have hone : (1 : ℝ) ≤ |(k : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |(k : ℝ)| := by push_cast [Int.cast_abs]; rfl
    rw [hxy, abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hlt
    nlinarith [hone, Real.pi_pos, hlt]

/-! ## The orbit resolves the spectrum -/

section OrbitResolution

open _root_.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- **`(7)` makes the orbit phases distinct.** -/
theorem orbitPhase_injective {E : n → ℝ} {t : ℝ}
    (h7 : ∀ j k : n, j ≠ k → ∀ m : ℤ, t * (E j - E k) ≠ 2 * Real.pi * (m : ℝ)) :
    Function.Injective fun j => Complex.exp (-((t * E j : ℝ) : ℂ) * Complex.I) := by
  intro j k hjk
  by_contra hne
  obtain ⟨m, hm⟩ := exists_int_of_expI_eq hjk
  exact h7 j k hne (-m) (by push_cast at hm ⊢; nlinarith [hm])

/-- **`(11)` upgrades to `[K₀, H] = 0`.**  A matrix commuting with the orbit, whose phases `(7)`
makes distinct, has no off-diagonal entries and therefore commutes with the Hamiltonian. -/
theorem commutes_diagonal_of_commutes_orbit {E : n → ℝ} {t : ℝ}
    (h7 : ∀ j k : n, j ≠ k → ∀ m : ℤ, t * (E j - E k) ≠ 2 * Real.pi * (m : ℝ))
    {X : Matrix n n ℂ}
    (hcomm : Matrix.diagonal (fun j => Complex.exp (-((t * E j : ℝ) : ℂ) * Complex.I)) * X
      = X * Matrix.diagonal (fun j => Complex.exp (-((t * E j : ℝ) : ℂ) * Complex.I))) :
    Matrix.diagonal (fun j => ((E j : ℝ) : ℂ)) * X
      = X * Matrix.diagonal (fun j => ((E j : ℝ) : ℂ)) := by
  have hinj := orbitPhase_injective h7
  have hoff : ∀ i j : n, i ≠ j → X i j = 0 := by
    intro i j hij
    exact (mem_commutantSubmodule_diagonal.mp (mem_commutantSubmodule.mpr hcomm)) i j
      (fun h => hij (hinj h))
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : i = j
  · subst hij
    ring
  · rw [hoff i j hij]
    ring

end OrbitResolution


/-! ## Theorem A: the only local exact logarithm is physical time -/

section TheoremA

variable {n : Type*}

/-- **`(13)`: diagonalizing `(8)` gives the winding equations.** -/
theorem exists_int_winding {E : n → ℝ} {a b t φ : ℝ}
    (h : ∀ j, Complex.exp (-((a * E j + b : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp (-((t * E j : ℝ) : ℂ) * Complex.I)) :
    ∃ m : n → ℤ, ∀ j, (a - t) * E j + b + φ = 2 * Real.pi * (m j : ℝ) := by
  classical
  have hstep : ∀ j : n, ∃ k : ℤ,
      (a * E j + b) - (t * E j - φ) = -((k : ℝ) * (2 * Real.pi)) := by
    intro j
    refine exists_int_of_expI_eq ?_
    rw [h j]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  choose k hk using hstep
  refine ⟨fun j => -k j, fun j => ?_⟩
  have := hk j
  push_cast
  linarith [this]

/-- **Theorem A.**  If the anchored gaps have rational dimension at least two, the only exact local
logarithm of `e^{iφ}U_H(t)` inside the centralizer line is physical time up to a scalar phase. -/
theorem localLogarithm_eq_physical {E : n → ℝ} {a b t φ : ℝ} (j₁ : n)
    (h : ∀ j, Complex.exp (-((a * E j + b : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp (-((t * E j : ℝ) : ℂ) * Complex.I))
    (hdim : 2 ≤ finrank ℚ (Submodule.span ℚ (Set.range fun j => E j - E j₁))) :
    a = t ∧ ∃ m : ℤ, b = 2 * Real.pi * (m : ℝ) - φ := by
  obtain ⟨m, hm⟩ := exists_int_winding h
  have hanchored : ∀ j : n,
      (a - t) * (E j - E j₁) = 2 * Real.pi * ((m j - m j₁ : ℤ) : ℝ) := by
    intro j
    have hj := hm j
    have hj₁ := hm j₁
    push_cast
    nlinarith [hj, hj₁]
  have hslope : a - t = 0 := eq_zero_of_two_dim_span _ hanchored hdim
  refine ⟨by linarith [hslope], ⟨m j₁, ?_⟩⟩
  have hj₁ := hm j₁
  rw [hslope, zero_mul] at hj₁
  linarith [hj₁]

end TheoremA


/-! ## The matrix form of Theorem A -/

section MatrixForm

open _root_.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exponential of a diagonal matrix is the diagonal of the scalar exponentials. -/
theorem exp_diagonal_entries (v : n → ℂ) :
    NormedSpace.exp (Matrix.diagonal v) = Matrix.diagonal fun j => Complex.exp (v j) := by
  rw [Matrix.exp_diagonal]
  congr 1
  funext j
  rw [Pi.coe_exp]
  exact (congrFun Complex.exp_eq_exp_ℂ (v j)).symm

omit [Fintype n] in
/-- **`(12)` in the eigenbasis.**  An element of the centralizer line is the diagonal of its
affine energy values. -/
theorem centralizerLine_diagonal (E : n → ℝ) (a b : ℝ) :
    ((a : ℝ) : ℂ) • Matrix.diagonal (fun j => ((E j : ℝ) : ℂ))
        + ((b : ℝ) : ℂ) • (1 : Matrix n n ℂ)
      = Matrix.diagonal fun j => ((a * E j + b : ℝ) : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
    push_cast
    ring
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- **Theorem A at the matrix level.**  In the eigenbasis of `H`, an exact logarithm on the
centralizer line is physical time up to a scalar phase. -/
theorem localLogarithm_eq_physical_matrix {E : n → ℝ} {a b t φ : ℝ} (j₁ : n)
    (h : NormedSpace.exp (Matrix.diagonal fun j => -((a * E j + b : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((φ : ℂ) * Complex.I)
          • NormedSpace.exp (Matrix.diagonal fun j => -((t * E j : ℝ) : ℂ) * Complex.I))
    (hdim : 2 ≤ finrank ℚ (Submodule.span ℚ (Set.range fun j => E j - E j₁))) :
    a = t ∧ ∃ m : ℤ, b = 2 * Real.pi * (m : ℝ) - φ := by
  rw [exp_diagonal_entries, exp_diagonal_entries, ← Matrix.diagonal_smul] at h
  refine localLogarithm_eq_physical j₁ (fun j => ?_) hdim
  have hj := congrFun (congrFun h j) j
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at hj
  simpa using hj

end MatrixForm


/-! ## Theorem A.1: the collision case -/

section Collision

open _root_.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A spectrum of diameter below `2π` separates no two of its values by `2π`. -/
theorem abs_sub_lt_of_diam_lt (hne : (Finset.univ : Finset n).Nonempty) (κ : n → ℝ)
    (hdiam : (Finset.univ.sup' hne κ) - (Finset.univ.inf' hne κ) < 2 * Real.pi) (i j : n) :
    |κ i - κ j| < 2 * Real.pi := by
  have hi := Finset.le_sup' κ (Finset.mem_univ i)
  have hj := Finset.le_sup' κ (Finset.mem_univ j)
  have hi' := Finset.inf'_le κ (Finset.mem_univ i)
  have hj' := Finset.inf'_le κ (Finset.mem_univ j)
  rw [abs_lt]
  constructor <;> linarith

omit [DecidableEq n] in
/-- **Scalarity on the phase fibres.**  Below diameter `2π`, equal exponentials force equal
eigenvalues, so an exact logarithm is scalar on every eigenspace of its exponential. -/
theorem eigenvalue_eq_of_exp_eq_of_diam_lt (hne : (Finset.univ : Finset n).Nonempty) (κ : n → ℝ)
    (hdiam : (Finset.univ.sup' hne κ) - (Finset.univ.inf' hne κ) < 2 * Real.pi) {i j : n}
    (h : Complex.exp (-((κ i : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-((κ j : ℝ) : ℂ) * Complex.I)) :
    κ i = κ j :=
  eq_of_exp_eq_of_abs_sub_lt h (abs_sub_lt_of_diam_lt hne κ hdiam i j)

/-- **`[K₀, H] = 0` even at a phase collision.**  If the Hamiltonian commutes with the exponential
and the logarithm is scalar on each of its phase fibres, the logarithm commutes with the
Hamiltonian. -/
theorem commutes_of_scalar_on_fiber {κ : n → ℝ} {H : Matrix n n ℂ}
    (hcomm : Matrix.diagonal (fun j => Complex.exp (-((κ j : ℝ) : ℂ) * Complex.I)) * H
      = H * Matrix.diagonal (fun j => Complex.exp (-((κ j : ℝ) : ℂ) * Complex.I)))
    (hscal : ∀ i j : n, Complex.exp (-((κ i : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-((κ j : ℝ) : ℂ) * Complex.I) → κ i = κ j) :
    Matrix.diagonal (fun j => ((κ j : ℝ) : ℂ)) * H
      = H * Matrix.diagonal (fun j => ((κ j : ℝ) : ℂ)) := by
  have hoff := mem_commutantSubmodule_diagonal.mp (mem_commutantSubmodule.mpr hcomm)
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hexp : Complex.exp (-((κ i : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-((κ j : ℝ) : ℂ) * Complex.I)
  · rw [hscal i j hexp]
    ring
  · rw [hoff i j hexp]
    ring

end Collision


end GaloisForLFunctions.HTGeometry
