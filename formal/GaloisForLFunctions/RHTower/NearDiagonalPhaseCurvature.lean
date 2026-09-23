import GaloisForLFunctions.RHTower.Sieve.SecondDerivativeTest

/-!
# The near-diagonal phase and its curvature

The phase produced by writing `2n = m + r` is `F_r(u) = (T/2π) log(1 + r/u)`, differentiated in the
actual summation variable `u = m`.  Its second derivative

`F_r''(u) = (T/2π) · r (2u + r) / (u² (u+r)²)`

is positive, and on a dyadic block `M ≤ u ≤ 2M` with `r ≤ M/2` it is pinned to `T r / M³` within an
absolute ratio, which is exactly the input of the van der Corput second-derivative test.
-/

namespace RHTower

noncomputable section

/-- The near-diagonal phase `F_r(u) = (T/2π) log(1 + r/u)`. -/
def nearDiagonalPhase (T r u : ℝ) : ℝ := T / (2 * Real.pi) * Real.log (1 + r / u)

/-- Its first derivative in the summation variable. -/
def nearDiagonalPhaseD1 (T r u : ℝ) : ℝ := -(T / (2 * Real.pi)) * (r / (u * (u + r)))

/-- Its second derivative in the summation variable. -/
def nearDiagonalPhaseD2 (T r u : ℝ) : ℝ :=
  T / (2 * Real.pi) * (r * (2 * u + r) / (u ^ (2 : ℕ) * (u + r) ^ (2 : ℕ)))

theorem hasDerivAt_nearDiagonalPhase (T : ℝ) {r u : ℝ} (hr : 0 ≤ r) (hu : 0 < u) :
    HasDerivAt (nearDiagonalPhase T r) (nearDiagonalPhaseD1 T r u) u := by
  have hune : u ≠ 0 := ne_of_gt hu
  have hpos : (0 : ℝ) < 1 + r / u := by positivity
  have hinner : HasDerivAt (fun x : ℝ => 1 + r / x) (-(r / u ^ (2 : ℕ))) u := by
    have h := (hasDerivAt_const u r).div (hasDerivAt_id u) hune
    have h2 := h.const_add (1 : ℝ)
    refine h2.congr_deriv ?_
    simp only [id_eq]
    field_simp
    ring
  have h := hinner.log (ne_of_gt hpos)
  have hd := h.const_mul (T / (2 * Real.pi))
  refine hd.congr_deriv ?_
  rw [nearDiagonalPhaseD1]
  have huu : u + r ≠ 0 := by positivity
  field_simp

theorem hasDerivAt_nearDiagonalPhaseD1 (T : ℝ) {r u : ℝ} (hr : 0 ≤ r) (hu : 0 < u) :
    HasDerivAt (nearDiagonalPhaseD1 T r) (nearDiagonalPhaseD2 T r u) u := by
  have hune : u ≠ 0 := ne_of_gt hu
  have huu : (0 : ℝ) < u + r := by positivity
  have hden : HasDerivAt (fun x : ℝ => x * (x + r)) (1 * (u + r) + u * 1) u :=
    (hasDerivAt_id u).mul ((hasDerivAt_id u).add_const r)
  have hinv : HasDerivAt (fun x : ℝ => r / (x * (x + r)))
      ((0 * (u * (u + r)) - r * (1 * (u + r) + u * 1)) / (u * (u + r)) ^ (2 : ℕ)) u :=
    (hasDerivAt_const u r).div hden (by positivity)
  have h := hinv.const_mul (-(T / (2 * Real.pi)))
  refine h.congr_deriv ?_
  rw [nearDiagonalPhaseD2]
  field_simp
  ring

theorem nearDiagonalPhaseD2_pos {T r u : ℝ} (hT : 0 < T) (hr : 0 < r) (hu : 0 < u) :
    0 < nearDiagonalPhaseD2 T r u := by
  rw [nearDiagonalPhaseD2]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

/-- The dyadic curvature scale `λ = T r / (36 π M³)`. -/
def nearDiagonalLambda (T r M : ℝ) : ℝ := T * r / (36 * Real.pi * M ^ (3 : ℕ))

theorem nearDiagonalLambda_pos {T r M : ℝ} (hT : 0 < T) (hr : 0 < r) (hM : 0 < M) :
    0 < nearDiagonalLambda T r M := by
  rw [nearDiagonalLambda]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

/-- Lower curvature bound on a dyadic block. -/
theorem nearDiagonalLambda_le_D2 {T r M u : ℝ} (hT : 0 < T) (hr : 0 < r) (hM : 0 < M)
    (hrM : r ≤ M) (hu1 : M ≤ u) (hu2 : u ≤ 2 * M) :
    nearDiagonalLambda T r M ≤ nearDiagonalPhaseD2 T r u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hM hu1
  have hur : (0 : ℝ) < u + r := by linarith
  have hkey : u ^ (2 : ℕ) * (u + r) ^ (2 : ℕ) ≤ 18 * M ^ (3 : ℕ) * (2 * u + r) := by
    have h1 : u ^ (2 : ℕ) ≤ 4 * M ^ (2 : ℕ) := by nlinarith
    have h2 : (u + r) ^ (2 : ℕ) ≤ 9 * M ^ (2 : ℕ) := by nlinarith
    have h3 : (2 : ℝ) * M ≤ 2 * u + r := by linarith
    have hA : u ^ (2 : ℕ) * (u + r) ^ (2 : ℕ) ≤ (4 * M ^ (2 : ℕ)) * (9 * M ^ (2 : ℕ)) :=
      mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    have hB : 18 * M ^ (3 : ℕ) * (2 * M) ≤ 18 * M ^ (3 : ℕ) * (2 * u + r) := by
      have hM3 : (0 : ℝ) ≤ 18 * M ^ (3 : ℕ) := by positivity
      nlinarith
    nlinarith [hA, hB]
  have hfrac : nearDiagonalPhaseD2 T r u - nearDiagonalLambda T r M
      = T * r * (18 * M ^ (3 : ℕ) * (2 * u + r) - u ^ (2 : ℕ) * (u + r) ^ (2 : ℕ))
        / (36 * Real.pi * M ^ (3 : ℕ) * (u ^ (2 : ℕ) * (u + r) ^ (2 : ℕ))) := by
    rw [nearDiagonalPhaseD2, nearDiagonalLambda]
    field_simp
    ring
  have hnn : 0 ≤ nearDiagonalPhaseD2 T r u - nearDiagonalLambda T r M := by
    rw [hfrac]
    apply div_nonneg
    · nlinarith [mul_pos hT hr]
    · positivity
  linarith

/-- Upper curvature bound on a dyadic block. -/
theorem D2_le_nearDiagonalLambda {T r M u : ℝ} (hT : 0 < T) (hr : 0 < r) (hM : 0 < M)
    (hrM : r ≤ M) (hu1 : M ≤ u) (hu2 : u ≤ 2 * M) :
    nearDiagonalPhaseD2 T r u ≤ 90 * nearDiagonalLambda T r M := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hM hu1
  have hur : (0 : ℝ) < u + r := by linarith
  have hkey : M ^ (3 : ℕ) * (2 * u + r) ≤ 5 * (u ^ (2 : ℕ) * (u + r) ^ (2 : ℕ)) := by
    have h1 : M ^ (2 : ℕ) ≤ u ^ (2 : ℕ) := by nlinarith
    have h2 : M ^ (2 : ℕ) ≤ (u + r) ^ (2 : ℕ) := by nlinarith
    have h3 : 2 * u + r ≤ 5 * M := by linarith
    have hA : M ^ (3 : ℕ) * (2 * u + r) ≤ M ^ (3 : ℕ) * (5 * M) := by
      have hM3 : (0 : ℝ) ≤ M ^ (3 : ℕ) := by positivity
      nlinarith
    have hB : (M ^ (2 : ℕ)) * (M ^ (2 : ℕ)) ≤ u ^ (2 : ℕ) * (u + r) ^ (2 : ℕ) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith [hA, hB]
  have hfrac : 90 * nearDiagonalLambda T r M - nearDiagonalPhaseD2 T r u
      = T * r * (5 * (u ^ (2 : ℕ) * (u + r) ^ (2 : ℕ)) - M ^ (3 : ℕ) * (2 * u + r))
        / (2 * Real.pi * M ^ (3 : ℕ) * (u ^ (2 : ℕ) * (u + r) ^ (2 : ℕ))) := by
    rw [nearDiagonalPhaseD2, nearDiagonalLambda]
    field_simp
    ring
  have hnn : 0 ≤ 90 * nearDiagonalLambda T r M - nearDiagonalPhaseD2 T r u := by
    rw [hfrac]
    apply div_nonneg
    · nlinarith [mul_pos hT hr]
    · positivity
  linarith

/-- **The dyadic block bound.**  Van der Corput's second-derivative test applied to the
near-diagonal phase on a block of unit-spaced sample points inside `[M, 2M]`. -/
theorem norm_nearDiagonalBlock_le {T r M : ℝ} (hT : 0 < T) (hr : 0 < r) (hM : 0 < M)
    (hrM : r ≤ M) {N : ℕ} (hN : 1 ≤ N) (hspan : ((N : ℕ) - 1 : ℕ) ≤ M)
    (hlam1 : nearDiagonalLambda T r M ≤ 1) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * nearDiagonalPhase T r (M + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ (2 * (N : ℝ) * 90 * nearDiagonalLambda T r M + 3)
          * (3 / Real.sqrt (nearDiagonalLambda T r M) + 1) := by
  have hlam0 : 0 < nearDiagonalLambda T r M := nearDiagonalLambda_pos hT hr hM
  have hmemsub : ∀ x ∈ Set.Icc M (M + (((N : ℕ) - 1 : ℕ) : ℝ)), M ≤ x ∧ x ≤ 2 * M := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    exact ⟨hx1, by linarith⟩
  refine RHTower.Sieve.second_derivative_test (nearDiagonalPhase T r) (nearDiagonalPhaseD1 T r)
    (nearDiagonalPhaseD2 T r) M N hN hlam0 hlam1 ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, -⟩ := hmemsub x hx
    exact hasDerivAt_nearDiagonalPhase T hr.le (lt_of_lt_of_le hM hx1)
  · intro x hx
    obtain ⟨hx1, -⟩ := hmemsub x hx
    exact hasDerivAt_nearDiagonalPhaseD1 T hr.le (lt_of_lt_of_le hM hx1)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hmemsub x hx
    exact nearDiagonalLambda_le_D2 hT hr hM hrM hx1 hx2
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hmemsub x hx
    exact D2_le_nearDiagonalLambda hT hr hM hrM hx1 hx2

end

end RHTower
