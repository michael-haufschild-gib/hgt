import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceJacobiEnergy
import GaloisForLFunctions.HTGeometry.StieltjesMomentProblem

/-!
# Degree-centered orthogonal source as causal Jacobi history

Centering Euler transport at admitted degree changes the adaptive orthogonal source from

`(X Pₙ) X (X Pₙ' + Pₙ)`

to

`(X Pₙ) X (X Pₙ' - n Pₙ)`.

The subtraction cancels the complete current/future Jacobi shell: `βₙ`, `βₙ₊₁`, and the local
`αₙ²` contribution.  Its moment is therefore current norm times the causal prefix-history

`∑_{j<n} (αⱼ² + αₙ αⱼ + 2 βⱼ)`.

This is a source-first, admission-sensitive law.  No observation map, orientation character,
reflection aggregate, or post hoc reporter enters.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

noncomputable section

/-- Degree-centered bilinear source attached to the actual monic orthogonal admission. -/
noncomputable def degreeCenteredOrthoSourcePolynomial
    (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  (X * monicOrtho s n) *
    (X * (X * (monicOrtho s n).derivative - (n : ℝ) • monicOrtho s n))

/-- Causal Jacobi history retained after degree-centering cancels the current/future shell. -/
noncomputable def degreeCenteredOrthoJacobiHistory
    (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
    monicOrthoAlpha s n *
      (∑ j ∈ Finset.range n, monicOrthoAlpha s j) +
    2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j)

/-- The polynomial `nextCoeff` API agrees with the Jacobi first-coefficient coordinate. -/
theorem monicOrtho_nextCoeff_eq_firstCoeff
    (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (monicOrtho s n).nextCoeff = monicOrthoFirstCoeff s n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Polynomial.nextCoeff_of_natDegree_pos]
  · simp [natDegree_monicOrtho, monicOrthoFirstCoeff]
  · rw [natDegree_monicOrtho]
    omega

/-- Centered source equals adaptive source minus its degree-weighted coordinate square. -/
theorem degreeCenteredOrthoSourcePolynomial_eq_adaptive_sub_square
    (s : ℕ → ℝ) (n : ℕ) :
    degreeCenteredOrthoSourcePolynomial s n =
      adaptiveOrthoSourcePolynomial s n -
        ((n : ℝ) + 1) • ((X * monicOrtho s n) ^ (2 : ℕ)) := by
  simp only [degreeCenteredOrthoSourcePolynomial, adaptiveOrthoSourcePolynomial,
    Polynomial.smul_eq_C_mul]
  rw [map_add, map_one]
  ring

/-- Consecutive norm ratio cancels its denominator unconditionally under positive moment form. -/
theorem monicOrthoNormSq_mul_beta_succ
    {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    monicOrthoNormSq s n * monicOrthoBeta s (n + 1) =
      monicOrthoNormSq s (n + 1) := by
  have hn : monicOrthoNormSq s n ≠ 0 := ne_of_gt (monicOrthoNormSq_pos h n)
  simp only [monicOrthoBeta]
  exact mul_div_cancel₀ _ hn

/-- Exact Jacobi shell energy of the coordinate-multiplied admitted amplitude. -/
theorem momentFunctional_X_mul_monicOrtho_sq_eq_jacobiShell
    {s : ℕ → ℝ} (h : PositiveMomentForm s) {n : ℕ} (hn : 0 < n) :
    momentFunctional s ((X * monicOrtho s n) ^ (2 : ℕ)) =
      monicOrthoNormSq s n *
        (monicOrthoBeta s (n + 1) + monicOrthoAlpha s n ^ (2 : ℕ) +
          monicOrthoBeta s n) := by
  have hnormne : monicOrthoNormSq s n ≠ 0 :=
    ne_of_gt (monicOrthoNormSq_pos h n)
  have hdiag :
      momentInner s (monicOrtho s n) (X * monicOrtho s n) =
        monicOrthoAlpha s n * monicOrthoNormSq s n := by
    rw [momentInner_comm]
    unfold monicOrthoAlpha monicOrthoNormSq
    rw [div_mul_cancel₀]
    exact hnormne
  have hup :
      momentInner s (monicOrtho s (n + 1)) (X * monicOrtho s n) =
        monicOrthoNormSq s (n + 1) := by
    rw [momentInner_monicOrtho_succ_X_mul h n]
    rfl
  have hdown :
      momentInner s (monicOrtho s (n - 1)) (X * monicOrtho s n) =
        monicOrthoNormSq s n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [Nat.succ_sub_one, ← momentInner_X_mul, momentInner_comm,
      momentInner_monicOrtho_succ_X_mul h k]
    rfl
  calc
    momentFunctional s ((X * monicOrtho s n) ^ (2 : ℕ)) =
        momentInner s (X * monicOrtho s n) (X * monicOrtho s n) :=
      (momentInner_self s (X * monicOrtho s n)).symm
    _ = momentInner s
          (monicOrtho s (n + 1) + monicOrthoAlpha s n • monicOrtho s n +
            monicOrthoBeta s n • monicOrtho s (n - 1))
          (X * monicOrtho s n) := by
      exact congrArg (fun p => momentInner s p (X * monicOrtho s n))
        (X_mul_monicOrtho h n)
    _ = monicOrthoNormSq s (n + 1) +
          monicOrthoAlpha s n *
            (monicOrthoAlpha s n * monicOrthoNormSq s n) +
          monicOrthoBeta s n * monicOrthoNormSq s n := by
      rw [momentInner_add_left, momentInner_add_left,
        momentInner_smul_left, momentInner_smul_left, hup, hdiag, hdown]
    _ = monicOrthoNormSq s n *
          (monicOrthoBeta s (n + 1) + monicOrthoAlpha s n ^ (2 : ℕ) +
            monicOrthoBeta s n) := by
      rw [← monicOrthoNormSq_mul_beta_succ h]
      ring

/-- Algebraic cancellation of adaptive shell by exact degree-centering. -/
theorem degreeCenteredOrthoJacobiHistory_eq_adaptive_sub_shell
    {s : ℕ → ℝ} (n : ℕ) :
    degreeCenteredOrthoJacobiHistory s n =
      adaptiveOrthoJacobiEnergy s n -
        (n + 1 : ℝ) *
          (monicOrthoBeta s (n + 1) + monicOrthoAlpha s n ^ (2 : ℕ) +
            monicOrthoBeta s n) := by
  simp only [degreeCenteredOrthoJacobiHistory, adaptiveOrthoJacobiEnergy]
  have hsquares :
      (∑ j ∈ Finset.range n,
          (monicOrthoAlpha s j + monicOrthoAlpha s n / 2) ^ (2 : ℕ)) =
        (∑ j ∈ Finset.range n,
          (monicOrthoAlpha s j ^ (2 : ℕ) +
            monicOrthoAlpha s n * monicOrthoAlpha s j +
            monicOrthoAlpha s n ^ (2 : ℕ) / 4)) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsquares]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Pointwise prefix-history form of the centered Jacobi invariant. -/
theorem degreeCenteredOrthoJacobiHistory_eq_sum
    (s : ℕ → ℝ) (n : ℕ) :
    degreeCenteredOrthoJacobiHistory s n =
      ∑ j ∈ Finset.range n,
        (monicOrthoAlpha s j ^ (2 : ℕ) +
          monicOrthoAlpha s n * monicOrthoAlpha s j +
          2 * monicOrthoBeta s j) := by
  simp only [degreeCenteredOrthoJacobiHistory, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- Division-free compactification of causal history.  The potentially singular current diagonal
coefficient appears only through its unnormalized odd current. -/
theorem monicOrthoNormSq_mul_degreeCenteredOrthoJacobiHistory_eq_bulk_add_current
    {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    monicOrthoNormSq s n * degreeCenteredOrthoJacobiHistory s n =
      monicOrthoNormSq s n *
          ((∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
            2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j)) +
        (∑ j ∈ Finset.range n, monicOrthoAlpha s j) *
          momentInner s (monicOrtho s n) (X * monicOrtho s n) := by
  have hnormne : monicOrthoNormSq s n ≠ 0 :=
    ne_of_gt (monicOrthoNormSq_pos h n)
  have hdiag : momentInner s (monicOrtho s n) (X * monicOrtho s n) =
      monicOrthoAlpha s n * monicOrthoNormSq s n := by
    rw [momentInner_comm]
    unfold monicOrthoAlpha monicOrthoNormSq
    rw [div_mul_cancel₀]
    exact hnormne
  rw [degreeCenteredOrthoJacobiHistory, hdiag]
  ring

/-- **Degree-centered arithmetic source law.**  Literal source equals admitted norm times causal
Jacobi history; all current/future shell coordinates have disappeared before observation. -/
theorem momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_jacobiHistory
    {s : ℕ → ℝ} (h : PositiveMomentForm s) {n : ℕ} (hn : 0 < n) :
    momentFunctional s (degreeCenteredOrthoSourcePolynomial s n) =
      monicOrthoNormSq s n * degreeCenteredOrthoJacobiHistory s n := by
  rw [degreeCenteredOrthoSourcePolynomial_eq_adaptive_sub_square,
    momentFunctional_sub, momentFunctional_smul,
    momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy h hn,
    momentFunctional_X_mul_monicOrtho_sq_eq_jacobiShell h hn,
    degreeCenteredOrthoJacobiHistory_eq_adaptive_sub_shell]
  ring

/-- Division-free source law: positive lower Jacobi bulk plus cumulative trace times current odd
moment.  This is the chamber-side expression whose flat-face compactification retains only the
second term. -/
theorem momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_bulk_add_current
    {s : ℕ → ℝ} (h : PositiveMomentForm s) {n : ℕ} (hn : 0 < n) :
    momentFunctional s (degreeCenteredOrthoSourcePolynomial s n) =
      monicOrthoNormSq s n *
          ((∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
            2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j)) +
        (∑ j ∈ Finset.range n, monicOrthoAlpha s j) *
          momentInner s (monicOrtho s n) (X * monicOrtho s n) := by
  rw [momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_jacobiHistory h hn,
    monicOrthoNormSq_mul_degreeCenteredOrthoJacobiHistory_eq_bulk_add_current h]

/-! ## Riccati completion -/

/-- Degree-centered source completed by the square of the admitted trace.  The correction has
degree `2n`, so it disappears on a flat degree-`n` null face while changing chamber coercivity. -/
noncomputable def riccatiCompletedDegreeCenteredOrthoSourcePolynomial
    (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  degreeCenteredOrthoSourcePolynomial s n +
    (2 * monicOrthoFirstCoeff s n ^ (2 : ℕ)) • (monicOrtho s n) ^ (2 : ℕ)

/-- Jacobi history of the Riccati-completed centered source. -/
noncomputable def riccatiCompletedDegreeCenteredOrthoJacobiHistory
    (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  degreeCenteredOrthoJacobiHistory s n + 2 * monicOrthoFirstCoeff s n ^ (2 : ℕ)

/-- Nondegenerate null-flag completion.  The odd unit channel fixes the surviving top coefficient
at one; the lower even channel completes its chamber contribution to `alpha^(2 : ℕ) + 1`.  Both
corrections remain inside the adaptive polynomial before any moment functional is applied. -/
noncomputable def nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial
    (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  riccatiCompletedDegreeCenteredOrthoSourcePolynomial s n +
    (1 + monicOrthoFirstCoeff s n) • (X * (monicOrtho s n) ^ (2 : ℕ)) +
    (monicOrthoAlpha s n ^ (2 : ℕ) - monicOrthoAlpha s n + 1) •
      (monicOrtho s n) ^ (2 : ℕ)

/-- Manifestly positive chamber history of the nondegenerate null-flag completion. -/
noncomputable def nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
    (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
    2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) +
    2 * monicOrthoFirstCoeff s n ^ (2 : ℕ) + monicOrthoAlpha s n ^ (2 : ℕ) + 1

/-- The completion converts the only indefinite cross term into admitted trace times cumulative
Riccati flux. -/
theorem riccatiCompletedDegreeCenteredOrthoJacobiHistory_eq_bulk_add_flux
    {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    riccatiCompletedDegreeCenteredOrthoJacobiHistory s n =
      (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
        2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) +
        (-monicOrthoFirstCoeff s n) *
          (-2 * monicOrthoFirstCoeff s n + monicOrthoAlpha s n) := by
  rw [riccatiCompletedDegreeCenteredOrthoJacobiHistory,
    degreeCenteredOrthoJacobiHistory, monicOrthoFirstCoeff_eq_neg_sum h]
  ring

/-- Exact source law after Riccati completion. -/
theorem momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_eq_history
    {s : ℕ → ℝ} (h : PositiveMomentForm s) {n : ℕ} (hn : 0 < n) :
    momentFunctional s (riccatiCompletedDegreeCenteredOrthoSourcePolynomial s n) =
      monicOrthoNormSq s n *
        riccatiCompletedDegreeCenteredOrthoJacobiHistory s n := by
  have hcorr := momentFunctional_smul s
    (2 * monicOrthoFirstCoeff s n ^ (2 : ℕ)) ((monicOrtho s n) ^ (2 : ℕ))
  rw [riccatiCompletedDegreeCenteredOrthoSourcePolynomial,
    momentFunctional_add, hcorr,
    momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_jacobiHistory h hn,
    ← momentInner_self]
  change monicOrthoNormSq s n * degreeCenteredOrthoJacobiHistory s n +
      2 * monicOrthoFirstCoeff s n ^ (2 : ℕ) * monicOrthoNormSq s n = _
  rw [riccatiCompletedDegreeCenteredOrthoJacobiHistory]
  ring

/-- Negative admitted first coefficient and positive cumulative Riccati flux force strict
positivity of completed causal history.  No asymptotic or degree-dependent margin is used. -/
theorem riccatiCompletedDegreeCenteredOrthoJacobiHistory_pos
    {s : ℕ → ℝ} (h : PositiveMomentForm s) {n : ℕ}
    (hfirst : monicOrthoFirstCoeff s n < 0)
    (hflux : 0 < -2 * monicOrthoFirstCoeff s n + monicOrthoAlpha s n) :
    0 < riccatiCompletedDegreeCenteredOrthoJacobiHistory s n := by
  rw [riccatiCompletedDegreeCenteredOrthoJacobiHistory_eq_bulk_add_flux h]
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoBeta s j :=
    Finset.sum_nonneg fun j _ => monicOrthoBeta_nonneg h j
  have htrace : 0 < (-monicOrthoFirstCoeff s n) *
      (-2 * monicOrthoFirstCoeff s n + monicOrthoAlpha s n) :=
    mul_pos (neg_pos.mpr hfirst) hflux
  positivity

/-- Riccati completion is a strictly positive source throughout every chamber with negative
admitted trace and positive cumulative flux. -/
theorem momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_pos
    {s : ℕ → ℝ} (h : PositiveMomentForm s) {n : ℕ} (hn : 0 < n)
    (hfirst : monicOrthoFirstCoeff s n < 0)
    (hflux : 0 < -2 * monicOrthoFirstCoeff s n + monicOrthoAlpha s n) :
    0 < momentFunctional s
      (riccatiCompletedDegreeCenteredOrthoSourcePolynomial s n) := by
  rw [momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_eq_history h hn]
  exact mul_pos (monicOrthoNormSq_pos h n)
    (riccatiCompletedDegreeCenteredOrthoJacobiHistory_pos h hfirst hflux)

/-! ### Finite positive-chamber localization -/

theorem monicOrthoNormSq_mul_beta_succ_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hnN : n + 1 ≤ N) :
    monicOrthoNormSq s n * monicOrthoBeta s (n + 1) =
      monicOrthoNormSq s (n + 1) := by
  have hn : monicOrthoNormSq s n ≠ 0 :=
    ne_of_gt (monicOrthoNorm_pos_below h (by omega))
  simp only [monicOrthoBeta]
  exact mul_div_cancel₀ _ hn

theorem momentFunctional_X_mul_monicOrtho_sq_eq_jacobiShell_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 1 ≤ N) :
    momentFunctional s ((X * monicOrtho s n) ^ (2 : ℕ)) =
      monicOrthoNormSq s n *
        (monicOrthoBeta s (n + 1) + monicOrthoAlpha s n ^ (2 : ℕ) +
          monicOrthoBeta s n) := by
  have hnormne : monicOrthoNormSq s n ≠ 0 :=
    ne_of_gt (monicOrthoNorm_pos_below h (by omega))
  have hdiag :
      momentInner s (monicOrtho s n) (X * monicOrtho s n) =
        monicOrthoAlpha s n * monicOrthoNormSq s n := by
    rw [momentInner_comm]
    unfold monicOrthoAlpha monicOrthoNormSq
    rw [div_mul_cancel₀]
    exact hnormne
  have hup :
      momentInner s (monicOrtho s (n + 1)) (X * monicOrtho s n) =
        monicOrthoNormSq s (n + 1) := by
    rw [momentInner_monicOrtho_succ_X_mul_below h hnN]
    rfl
  have hdown :
      momentInner s (monicOrtho s (n - 1)) (X * monicOrtho s n) =
        monicOrthoNormSq s n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [Nat.succ_sub_one, ← momentInner_X_mul, momentInner_comm,
      momentInner_monicOrtho_succ_X_mul_below h (by omega)]
    rfl
  calc
    momentFunctional s ((X * monicOrtho s n) ^ (2 : ℕ)) =
        momentInner s (X * monicOrtho s n) (X * monicOrtho s n) :=
      (momentInner_self s (X * monicOrtho s n)).symm
    _ = momentInner s
          (monicOrtho s (n + 1) + monicOrthoAlpha s n • monicOrtho s n +
            monicOrthoBeta s n • monicOrtho s (n - 1))
          (X * monicOrtho s n) := by
      exact congrArg (fun p => momentInner s p (X * monicOrtho s n))
        (X_mul_monicOrtho_below h hnN)
    _ = monicOrthoNormSq s (n + 1) +
          monicOrthoAlpha s n *
            (monicOrthoAlpha s n * monicOrthoNormSq s n) +
          monicOrthoBeta s n * monicOrthoNormSq s n := by
      rw [momentInner_add_left, momentInner_add_left,
        momentInner_smul_left, momentInner_smul_left, hup, hdiag, hdown]
    _ = monicOrthoNormSq s n *
          (monicOrthoBeta s (n + 1) + monicOrthoAlpha s n ^ (2 : ℕ) +
            monicOrthoBeta s n) := by
      rw [← monicOrthoNormSq_mul_beta_succ_below h hnN]
      ring

theorem momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_jacobiHistory_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    momentFunctional s (degreeCenteredOrthoSourcePolynomial s n) =
      monicOrthoNormSq s n * degreeCenteredOrthoJacobiHistory s n := by
  rw [degreeCenteredOrthoSourcePolynomial_eq_adaptive_sub_square,
    momentFunctional_sub, momentFunctional_smul,
    momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below h hn hnN,
    momentFunctional_X_mul_monicOrtho_sq_eq_jacobiShell_below h hn (by omega),
    degreeCenteredOrthoJacobiHistory_eq_adaptive_sub_shell]
  ring

theorem riccatiCompletedDegreeCenteredOrthoJacobiHistory_eq_bulk_add_flux_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N) (hnN : n ≤ N) :
    riccatiCompletedDegreeCenteredOrthoJacobiHistory s n =
      (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
        2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) +
        (-monicOrthoFirstCoeff s n) *
          (-2 * monicOrthoFirstCoeff s n + monicOrthoAlpha s n) := by
  rw [riccatiCompletedDegreeCenteredOrthoJacobiHistory,
    degreeCenteredOrthoJacobiHistory,
    monicOrthoFirstCoeff_eq_neg_sum_below h hnN]
  ring

/-- The cumulative Riccati flux is not an independent coordinate: after the adjacent monic
recurrence it is the negative sum of two neighboring admitted first coefficients.  Consequently
the completed history couples adjacent traces before any scalar observation. -/
theorem riccatiCompletedDegreeCenteredOrthoJacobiHistory_eq_bulk_add_adjacentTrace_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hnN : n + 1 ≤ N) :
    riccatiCompletedDegreeCenteredOrthoJacobiHistory s n =
      (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
        2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) +
        monicOrthoFirstCoeff s n *
          (monicOrthoFirstCoeff s n + monicOrthoFirstCoeff s (n + 1)) := by
  rw [riccatiCompletedDegreeCenteredOrthoJacobiHistory_eq_bulk_add_flux_below
    h (by omega)]
  have hsucc := monicOrthoFirstCoeff_succ_below h hnN
  rw [hsucc]
  ring

/-- Two negative neighboring admission traces force strict completed-history positivity.  This
eliminates the separately stated Riccati-flux sign from the chamber criterion. -/
theorem riccatiCompletedDegreeCenteredOrthoJacobiHistory_pos_of_adjacentTrace_neg_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hnN : n + 1 ≤ N)
    (hcurrent : monicOrthoFirstCoeff s n < 0)
    (hnext : monicOrthoFirstCoeff s (n + 1) < 0) :
    0 < riccatiCompletedDegreeCenteredOrthoJacobiHistory s n := by
  rw [riccatiCompletedDegreeCenteredOrthoJacobiHistory_eq_bulk_add_adjacentTrace_below h hnN]
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [monicOrthoBeta]
    · exact (monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hsum : monicOrthoFirstCoeff s n + monicOrthoFirstCoeff s (n + 1) < 0 :=
    add_neg hcurrent hnext
  have htrace : 0 < monicOrthoFirstCoeff s n *
      (monicOrthoFirstCoeff s n + monicOrthoFirstCoeff s (n + 1)) :=
    mul_pos_of_neg_of_neg hcurrent hsum
  positivity

theorem momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    momentFunctional s (riccatiCompletedDegreeCenteredOrthoSourcePolynomial s n) =
      monicOrthoNormSq s n *
        riccatiCompletedDegreeCenteredOrthoJacobiHistory s n := by
  have hcorr := momentFunctional_smul s
    (2 * monicOrthoFirstCoeff s n ^ (2 : ℕ)) ((monicOrtho s n) ^ (2 : ℕ))
  rw [riccatiCompletedDegreeCenteredOrthoSourcePolynomial,
    momentFunctional_add, hcorr,
    momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_jacobiHistory_below h hn hnN,
    ← momentInner_self]
  change monicOrthoNormSq s n * degreeCenteredOrthoJacobiHistory s n +
      2 * monicOrthoFirstCoeff s n ^ (2 : ℕ) * monicOrthoNormSq s n = _
  rw [riccatiCompletedDegreeCenteredOrthoJacobiHistory]
  ring

/-- **Nondegenerate chamber source law.**  Adjacent completion converts the Riccati cross term
into two squares plus a unit reserve.  This theorem is finite-block local and needs no global
moment-form hypothesis. -/
theorem momentFunctional_nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    momentFunctional s
        (nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial s n) =
      monicOrthoNormSq s n *
        nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s n := by
  have hnormne : monicOrthoNormSq s n ≠ 0 :=
    ne_of_gt (monicOrthoNorm_pos_below h (by omega))
  have hodd :
      momentFunctional s (X * (monicOrtho s n) ^ (2 : ℕ)) =
        monicOrthoAlpha s n * monicOrthoNormSq s n := by
    calc
      momentFunctional s (X * (monicOrtho s n) ^ (2 : ℕ)) =
          momentInner s (monicOrtho s n) (X * monicOrtho s n) := by
        rw [momentInner_def]
        congr 1
        ring
      _ = monicOrthoAlpha s n * monicOrthoNormSq s n := by
        rw [momentInner_comm]
        unfold monicOrthoAlpha monicOrthoNormSq
        rw [div_mul_cancel₀]
        exact hnormne
  have hsquare :
      momentFunctional s ((monicOrtho s n) ^ (2 : ℕ)) = monicOrthoNormSq s n := by
    rw [← momentInner_self]
    rfl
  rw [nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial,
    momentFunctional_add, momentFunctional_add, momentFunctional_smul,
    momentFunctional_smul,
    momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
      h hn hnN,
    hodd, hsquare,
    nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory,
    riccatiCompletedDegreeCenteredOrthoJacobiHistory_eq_bulk_add_flux_below h (by omega)]
  ring

/-- Unit reserve makes the completed source strictly positive on every finite positive chamber,
without any trace or flux sign premise. -/
theorem momentFunctional_nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial_pos_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    0 < momentFunctional s
      (nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial s n) := by
  rw [momentFunctional_nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
    h hn hnN]
  apply mul_pos (monicOrthoNorm_pos_below h (by omega))
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [monicOrthoBeta]
    · exact (monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  rw [nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory]
  positivity

/-- **Odd-current coercivity of the nondegenerate completion.**  Multiplying the completed
source by the admitted norm exposes the square of the current odd channel.  This is the
division-free boundary-layer law behind the adjacent completion: any chamber path on which the
norm collapses while the odd current stays nonzero must make the completed source unbounded. -/
theorem sq_momentInner_monicOrtho_X_le_norm_mul_nondegenerateSource_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    momentInner s (monicOrtho s n) (X * monicOrtho s n) ^ (2 : ℕ) ≤
      monicOrthoNormSq s n *
        momentFunctional s
          (nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial s n) := by
  have hnorm : 0 < monicOrthoNormSq s n :=
    monicOrthoNorm_pos_below h (by omega)
  have hdiag :
      momentInner s (monicOrtho s n) (X * monicOrtho s n) =
        monicOrthoAlpha s n * monicOrthoNormSq s n := by
    rw [momentInner_comm]
    unfold monicOrthoAlpha monicOrthoNormSq
    rw [div_mul_cancel₀]
    exact ne_of_gt hnorm
  have hhistory :
      monicOrthoAlpha s n ^ (2 : ℕ) ≤
        nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s n := by
    have hsquares : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ) :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hbetas : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoBeta s j := by
      apply Finset.sum_nonneg
      intro j hj
      rcases j with _ | j
      · simp [monicOrthoBeta]
      · exact (monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
          have hjn := Finset.mem_range.mp hj
          omega)).le
    unfold nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
    nlinarith [sq_nonneg (monicOrthoFirstCoeff s n)]
  rw [hdiag,
    momentFunctional_nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
      h hn hnN]
  have hmul :=
    mul_le_mul_of_nonneg_left hhistory (sq_nonneg (monicOrthoNormSq s n))
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- **Exact projective boundary-layer identity.**  After multiplying by admitted norm, the
nondegenerate completed source splits into the square of the odd current and a regular history
carrying a second norm factor.  Thus the projective boundary value is the odd-current square,
not its orientation. -/
theorem norm_mul_momentFunctional_nondegenerateSource_eq_odd_sq_add_regular_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    monicOrthoNormSq s n *
        momentFunctional s
          (nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial s n) =
      momentInner s (monicOrtho s n) (X * monicOrtho s n) ^ (2 : ℕ) +
        monicOrthoNormSq s n ^ (2 : ℕ) *
          ((∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
            2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) +
            2 * monicOrthoFirstCoeff s n ^ (2 : ℕ) + 1) := by
  have hnorm : 0 < monicOrthoNormSq s n :=
    monicOrthoNorm_pos_below h (by omega)
  have hdiag :
      momentInner s (monicOrtho s n) (X * monicOrtho s n) =
        monicOrthoAlpha s n * monicOrthoNormSq s n := by
    rw [momentInner_comm]
    unfold monicOrthoAlpha monicOrthoNormSq
    rw [div_mul_cancel₀]
    exact ne_of_gt hnorm
  rw [momentFunctional_nondegenerateNullFlagCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
      h hn hnN,
    nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory, hdiag]
  ring

theorem riccatiCompletedDegreeCenteredOrthoJacobiHistory_pos_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hnN : n ≤ N) (hfirst : monicOrthoFirstCoeff s n < 0)
    (hflux : 0 < -2 * monicOrthoFirstCoeff s n + monicOrthoAlpha s n) :
    0 < riccatiCompletedDegreeCenteredOrthoJacobiHistory s n := by
  rw [riccatiCompletedDegreeCenteredOrthoJacobiHistory_eq_bulk_add_flux_below h hnN]
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [monicOrthoBeta]
    · exact (monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have htrace : 0 < (-monicOrthoFirstCoeff s n) *
      (-2 * monicOrthoFirstCoeff s n + monicOrthoAlpha s n) :=
    mul_pos (neg_pos.mpr hfirst) hflux
  positivity

theorem momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_pos_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N)
    (hfirst : monicOrthoFirstCoeff s n < 0)
    (hflux : 0 < -2 * monicOrthoFirstCoeff s n + monicOrthoAlpha s n) :
    0 < momentFunctional s
      (riccatiCompletedDegreeCenteredOrthoSourcePolynomial s n) := by
  rw [momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
    h hn hnN]
  exact mul_pos (monicOrthoNorm_pos_below h (by omega))
    (riccatiCompletedDegreeCenteredOrthoJacobiHistory_pos_below
      h (by omega) hfirst hflux)

/-- Source-level adjacent-trace criterion.  Admission, trace coupling, and completion all occur
inside the moment functional; no fixed reporter or post-formation orientation is used. -/
theorem momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_pos_of_adjacentTrace_neg_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N)
    (hcurrent : monicOrthoFirstCoeff s n < 0)
    (hnext : monicOrthoFirstCoeff s (n + 1) < 0) :
    0 < momentFunctional s
      (riccatiCompletedDegreeCenteredOrthoSourcePolynomial s n) := by
  rw [momentFunctional_riccatiCompletedDegreeCenteredOrthoSourcePolynomial_eq_history_below
    h hn hnN]
  exact mul_pos (monicOrthoNorm_pos_below h (by omega))
    (riccatiCompletedDegreeCenteredOrthoJacobiHistory_pos_of_adjacentTrace_neg_below
      h (by omega) hcurrent hnext)

/-- The cumulative degree-`n` Jacobi dissipation minus the degree-`n` trace velocity is exactly
the next trace-velocity energy and is strictly positive.  Written generically here, this law does
not unfold any arithmetic realization. -/
theorem adjacentTraceDissipationGap_pos_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    0 <
      (2 * (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
          monicOrthoAlpha s n ^ (2 : ℕ) +
          4 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) +
          2 * (n + 1 : ℝ) *
            (monicOrthoBeta s n + monicOrthoBeta s (n + 1))) -
        ((∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ)) +
          2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) +
          2 * (n : ℝ) * monicOrthoBeta s n) := by
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbetas : 0 ≤ ∑ j ∈ Finset.range n, monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [monicOrthoBeta]
    · exact (monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hbeta : 0 < monicOrthoBeta s n :=
    monicOrthoBeta_pos_below h hn (by omega)
  have hbetaNext : 0 < monicOrthoBeta s (n + 1) :=
    monicOrthoBeta_pos_below h (by omega) (by omega)
  have hnextTerm : 0 < 2 * (n + 1 : ℝ) * monicOrthoBeta s (n + 1) := by
    positivity
  nlinarith [sq_nonneg (monicOrthoAlpha s n)]

end
end HTGeometry
