import GaloisForLFunctions.HTGeometry.ChristoffelDarboux

/-!
# Second-kind polynomials and the Wronskian

The associated (second-kind) polynomials of a moment sequence obey the *same* three-term recurrence
as the orthogonal polynomials, with the shifted initial data `R₀ = 0`, `R₁ = 1`.  They are the
second solution of the recurrence, and the pair `(Qₙ, Rₙ)` spans its solution space.

The structural fact is that the Wronskian

`Qₙ₊₁ Rₙ - Qₙ Rₙ₊₁`

is a *constant polynomial*, equal to `-hₙ / h₀`.  Constancy in `z` is what makes the ratio
`Rₙ / Qₙ` a genuine Nevanlinna-type fraction, and the explicit value is the normalization that
appears in the determinant identity `AD - BC = 1` of the Nevanlinna matrix.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Diagonal coefficient of the three-term recurrence. -/
noncomputable def recurDiag (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentInner s (Polynomial.X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
    momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))

/-- Off-diagonal coefficient of the three-term recurrence: the ratio of consecutive moment norms. -/
noncomputable def recurOff (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
    momentInner s (monicOrtho s n) (monicOrtho s n)

theorem recurOff_mul (h : PositiveMomentForm s) (n : ℕ) :
    recurOff s n * momentInner s (monicOrtho s n) (monicOrtho s n) =
      momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) := by
  rw [recurOff, div_mul_cancel₀ _ (h.self_ne_zero (monicOrtho_ne_zero s n))]

/-- The recurrence in solved form: `Qₙ₊₂ = (X - aₙ) Qₙ₊₁ - bₙ Qₙ`. -/
theorem monicOrtho_succ_succ (h : PositiveMomentForm s) (n : ℕ) :
    monicOrtho s (n + 2) =
      (Polynomial.X - Polynomial.C (recurDiag s n)) * monicOrtho s (n + 1)
        - Polynomial.C (recurOff s n) * monicOrtho s n := by
  have hrec := monicOrtho_three_term h n
  rw [recurDiag, recurOff]
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul] at hrec
  linear_combination -hrec

/-- The **second-kind polynomials**: the same recurrence with initial data `R₀ = 0`, `R₁ = 1`. -/
noncomputable def secondKind (s : ℕ → ℝ) : ℕ → Polynomial ℝ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (Polynomial.X - Polynomial.C (recurDiag s n)) * secondKind s (n + 1)
      - Polynomial.C (recurOff s n) * secondKind s n

@[simp] theorem secondKind_zero (s : ℕ → ℝ) : secondKind s 0 = 0 := rfl

@[simp] theorem secondKind_one (s : ℕ → ℝ) : secondKind s 1 = 1 := rfl

theorem secondKind_succ_succ (s : ℕ → ℝ) (n : ℕ) :
    secondKind s (n + 2) =
      (Polynomial.X - Polynomial.C (recurDiag s n)) * secondKind s (n + 1)
        - Polynomial.C (recurOff s n) * secondKind s n := rfl

/-- The Wronskian of the two solutions. -/
noncomputable def momentWronskian (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  monicOrtho s (n + 1) * secondKind s n - monicOrtho s n * secondKind s (n + 1)

/-- The Wronskian scales by the off-diagonal coefficient: the diagonal coefficient cancels because
both families obey the same recurrence. -/
theorem momentWronskian_succ (h : PositiveMomentForm s) (n : ℕ) :
    momentWronskian s (n + 1) = Polynomial.C (recurOff s n) * momentWronskian s n := by
  rw [momentWronskian, momentWronskian, monicOrtho_succ_succ h n, secondKind_succ_succ s n]
  ring

/-- **The Wronskian is a constant polynomial with an explicit value.** -/
theorem momentWronskian_eq (h : PositiveMomentForm s) (n : ℕ) :
    momentWronskian s n =
      Polynomial.C (-(momentInner s (monicOrtho s n) (monicOrtho s n) /
        momentInner s (monicOrtho s 0) (monicOrtho s 0))) := by
  induction n with
  | zero =>
      have h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s 0)
      rw [monicOrtho_zero] at h0
      rw [momentWronskian, secondKind_zero, secondKind_one, monicOrtho_zero, div_self h0]
      simp
  | succ n ih =>
      have h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s 0)
      rw [momentWronskian_succ h n, ih, ← Polynomial.C_mul]
      congr 1
      have hb := recurOff_mul h n
      field_simp
      linear_combination -hb

/-- The Wronskian never vanishes: the two solutions are genuinely independent. -/
theorem momentWronskian_ne_zero (h : PositiveMomentForm s) (n : ℕ) :
    momentWronskian s n ≠ 0 := by
  rw [momentWronskian_eq h n, Ne, Polynomial.C_eq_zero, neg_eq_zero, div_eq_zero_iff]
  rintro (hA | hB)
  · exact h.self_ne_zero (monicOrtho_ne_zero s n) hA
  · exact h.self_ne_zero (monicOrtho_ne_zero s 0) hB

/-! ## Exact degree of the second-kind family -/

/-- `Rₙ₊₁` is monic of exact degree `n`: the second solution lags the first by one degree.  Both
statements are proved together, since the two-step recurrence needs both at each stage. -/
theorem secondKind_succ_monic_degree (s : ℕ → ℝ) (n : ℕ) :
    (secondKind s (n + 1)).Monic ∧ (secondKind s (n + 1)).degree = (n : WithBot ℕ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 =>
          refine ⟨?_, ?_⟩
          · rw [secondKind_one]; exact Polynomial.monic_one
          · rw [secondKind_one]; simp
      | 1 =>
          have hrec : secondKind s 2 =
              (Polynomial.X - Polynomial.C (recurDiag s 0)) * secondKind s 1
                - Polynomial.C (recurOff s 0) * secondKind s 0 := secondKind_succ_succ s 0
          rw [secondKind_one, secondKind_zero, mul_zero, sub_zero, mul_one] at hrec
          refine ⟨?_, ?_⟩
          · rw [hrec]; exact Polynomial.monic_X_sub_C _
          · rw [hrec]; simp
      | (m + 2) =>
          obtain ⟨hmon, hdeg⟩ := ih (m + 1) (by omega)
          obtain ⟨_, hdeg0⟩ := ih m (by omega)
          have hrec : secondKind s (m + 3) =
              (Polynomial.X - Polynomial.C (recurDiag s (m + 1))) * secondKind s (m + 2)
                - Polynomial.C (recurOff s (m + 1)) * secondKind s (m + 1) :=
            secondKind_succ_succ s (m + 1)
          have hmulmon : ((Polynomial.X - Polynomial.C (recurDiag s (m + 1))) *
              secondKind s (m + 2)).Monic := (Polynomial.monic_X_sub_C _).mul hmon
          have hmuldeg : ((Polynomial.X - Polynomial.C (recurDiag s (m + 1))) *
              secondKind s (m + 2)).degree = ((m + 2 : ℕ) : WithBot ℕ) := by
            rw [Polynomial.degree_mul, Polynomial.degree_X_sub_C, hdeg]
            push_cast
            ring
          have hlow : (Polynomial.C (recurOff s (m + 1)) * secondKind s (m + 1)).degree
              < ((Polynomial.X - Polynomial.C (recurDiag s (m + 1))) *
                secondKind s (m + 2)).degree := by
            rw [hmuldeg]
            have hle : (Polynomial.C (recurOff s (m + 1)) * secondKind s (m + 1)).degree
                ≤ ((m : ℕ) : WithBot ℕ) := by
              refine le_trans (Polynomial.degree_mul_le _ _) ?_
              rw [hdeg0]
              have hC : (Polynomial.C (recurOff s (m + 1))).degree ≤ (0 : WithBot ℕ) :=
                Polynomial.degree_C_le
              calc (Polynomial.C (recurOff s (m + 1))).degree + ((m : ℕ) : WithBot ℕ)
                  ≤ 0 + ((m : ℕ) : WithBot ℕ) := by gcongr
                _ = ((m : ℕ) : WithBot ℕ) := zero_add _
            refine lt_of_le_of_lt hle ?_
            exact_mod_cast (by omega : m < m + 2)
          refine ⟨?_, ?_⟩
          · rw [hrec]; exact hmulmon.sub_of_left hlow
          · rw [hrec, Polynomial.degree_sub_eq_left_of_degree_lt hlow, hmuldeg]

theorem secondKind_succ_ne_zero (s : ℕ → ℝ) (n : ℕ) : secondKind s (n + 1) ≠ 0 :=
  (secondKind_succ_monic_degree s n).1.ne_zero

/-- The second-kind family lags the first by exactly one degree. -/
theorem secondKind_degree_succ_eq (s : ℕ → ℝ) (n : ℕ) :
    (secondKind s (n + 1)).degree + 1 = (monicOrtho s (n + 1)).degree := by
  rw [(secondKind_succ_monic_degree s n).2, monicOrtho_degree]
  push_cast
  ring

/-! ## Mixed Christoffel--Darboux

Pairing the first-kind family at one point against the second-kind family at another.  The
telescoping is the same as for `christoffelDarboux`, but the boundary term at `n = 0` no longer
vanishes: `R₀ = 0` and `R₁ = 1` leave the constant `1 / h₀`.  That constant is the normalization
which becomes the determinant identity of the Nevanlinna matrix. -/

theorem monicOrtho_succ_succ_eval (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    (monicOrtho s (n + 2)).eval x =
      (x - recurDiag s n) * (monicOrtho s (n + 1)).eval x
        - recurOff s n * (monicOrtho s n).eval x := by
  have hev := congrArg (Polynomial.eval x) (monicOrtho_succ_succ h n)
  simpa using hev

theorem secondKind_succ_succ_eval (s : ℕ → ℝ) (n : ℕ) (y : ℝ) :
    (secondKind s (n + 2)).eval y =
      (y - recurDiag s n) * (secondKind s (n + 1)).eval y
        - recurOff s n * (secondKind s n).eval y := by
  have hev := congrArg (Polynomial.eval y) (secondKind_succ_succ s n)
  simpa using hev

/-- **Mixed Christoffel--Darboux.** -/
theorem mixedChristoffelDarboux (h : PositiveMomentForm s) (n : ℕ) (x y : ℝ) :
    (x - y) * ∑ k ∈ Finset.range (n + 1),
        (monicOrtho s k).eval x * (secondKind s k).eval y /
          momentInner s (monicOrtho s k) (monicOrtho s k)
      = ((monicOrtho s (n + 1)).eval x * (secondKind s n).eval y -
          (monicOrtho s n).eval x * (secondKind s (n + 1)).eval y) /
          momentInner s (monicOrtho s n) (monicOrtho s n)
        + 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
  induction n with
  | zero =>
      have h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s 0)
      have hx0 : (monicOrtho s 0).eval x = 1 := by simp
      simp only [Nat.zero_add, Finset.sum_range_one, secondKind_zero, secondKind_one,
        Polynomial.eval_zero, Polynomial.eval_one, hx0, mul_zero, zero_div, mul_one, mul_zero,
        zero_sub]
      field_simp
      ring
  | succ n ih =>
      have hn : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s n)
      have hn1 : momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s (n + 1))
      have hQ := monicOrtho_succ_succ_eval h n x
      have hR := secondKind_succ_succ_eval s n y
      simp only [recurOff] at hQ hR
      rw [Finset.sum_range_succ, mul_add, ih, hQ, hR]
      field_simp
      ring

/-- **Second-kind Christoffel--Darboux.**  Pairing the second-kind family against itself.  Here the
`n = 0` boundary term vanishes (`R₀ = 0`), so unlike `mixedChristoffelDarboux` no constant survives.
Together with `christoffelDarboux` and `mixedChristoffelDarboux` this completes the trio of
bilinear identities carried by the recurrence. -/
theorem secondKindChristoffelDarboux (h : PositiveMomentForm s) (n : ℕ) (x y : ℝ) :
    (x - y) * ∑ k ∈ Finset.range (n + 1),
        (secondKind s k).eval x * (secondKind s k).eval y /
          momentInner s (monicOrtho s k) (monicOrtho s k)
      = ((secondKind s (n + 1)).eval x * (secondKind s n).eval y -
          (secondKind s n).eval x * (secondKind s (n + 1)).eval y) /
        momentInner s (monicOrtho s n) (monicOrtho s n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s n)
      have hn1 : momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) ≠ 0 :=
        h.self_ne_zero (monicOrtho_ne_zero s (n + 1))
      have hRx := secondKind_succ_succ_eval s n x
      have hRy := secondKind_succ_succ_eval s n y
      simp only [recurOff] at hRx hRy
      rw [Finset.sum_range_succ, mul_add, ih, hRx, hRy]
      field_simp
      ring

/-! ## The transfer matrix

Packaging the two solutions as a `2 × 2` matrix over `ℝ[X]`.  Its determinant is the Wronskian,
hence a *nonzero constant*, hence a unit of `ℝ[X]` — so the transfer matrix is invertible over the
polynomial ring itself, not merely over the fraction field.  This is the finite, polynomial-level
form of the determinant condition carried by a Nevanlinna matrix. -/

/-- The transfer matrix of the recurrence, with rows indexed by consecutive levels. -/
noncomputable def momentTransfer (s : ℕ → ℝ) (n : ℕ) : Matrix (Fin 2) (Fin 2) (Polynomial ℝ) :=
  !![monicOrtho s (n + 1), secondKind s (n + 1); monicOrtho s n, secondKind s n]

/-- The determinant of the transfer matrix is the Wronskian. -/
theorem momentTransfer_det_eq_wronskian (s : ℕ → ℝ) (n : ℕ) :
    (momentTransfer s n).det = momentWronskian s n := by
  rw [momentTransfer, Matrix.det_fin_two_of, momentWronskian]
  ring

/-- The determinant is the explicit nonzero constant `-hₙ / h₀`. -/
theorem momentTransfer_det (h : PositiveMomentForm s) (n : ℕ) :
    (momentTransfer s n).det =
      Polynomial.C (-(momentInner s (monicOrtho s n) (monicOrtho s n) /
        momentInner s (monicOrtho s 0) (monicOrtho s 0))) := by
  rw [momentTransfer_det_eq_wronskian, momentWronskian_eq h n]

/-- The determinant is a unit of `ℝ[X]`: it is a nonzero constant polynomial. -/
theorem momentTransfer_det_isUnit (h : PositiveMomentForm s) (n : ℕ) :
    IsUnit (momentTransfer s n).det := by
  rw [momentTransfer_det h n, Polynomial.isUnit_C]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [neg_ne_zero, div_ne_zero_iff]
  exact ⟨h.self_ne_zero (monicOrtho_ne_zero s n), h.self_ne_zero (monicOrtho_ne_zero s 0)⟩

/-- **The transfer matrix is invertible over `ℝ[X]`.**  The two solutions of the recurrence are
independent in the strongest polynomial sense. -/
theorem momentTransfer_isUnit (h : PositiveMomentForm s) (n : ℕ) :
    IsUnit (momentTransfer s n) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (momentTransfer_det_isUnit h n)

/-! ## The Duhamel comparison formula

Comparing the orthogonal polynomials at two points.  This is the discrete variation-of-constants
formula, and it needs no separate induction: `christoffelDarboux` supplies one partial sum in closed
form, `mixedChristoffelDarboux` the other (contributing the `1/h₀` term), and on substitution the
`Rₙ(z)` contributions cancel, leaving `Qₙ(w)` after one use of the constant Wronskian. -/

theorem monicOrtho_duhamel (h : PositiveMomentForm s) (n : ℕ) (z w : ℝ) :
    (monicOrtho s n).eval w
      = (monicOrtho s n).eval z
        - (w - z) * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          ((monicOrtho s n).eval z *
              (∑ j ∈ Finset.range (n + 1), (monicOrtho s j).eval w * (secondKind s j).eval z /
                momentInner s (monicOrtho s j) (monicOrtho s j))
            - (secondKind s n).eval z *
              (∑ j ∈ Finset.range (n + 1), (monicOrtho s j).eval w * (monicOrtho s j).eval z /
                momentInner s (monicOrtho s j) (monicOrtho s j))) := by
  have h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
    h.self_ne_zero (monicOrtho_ne_zero s 0)
  have hn : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
    h.self_ne_zero (monicOrtho_ne_zero s n)
  have hCD := christoffelDarboux h n w z
  have hMix := mixedChristoffelDarboux h n w z
  have hWz : (monicOrtho s (n + 1)).eval z * (secondKind s n).eval z
      - (monicOrtho s n).eval z * (secondKind s (n + 1)).eval z
      = -(momentInner s (monicOrtho s n) (monicOrtho s n) /
          momentInner s (monicOrtho s 0) (monicOrtho s 0)) := by
    have hev := congrArg (Polynomial.eval z) (momentWronskian_eq h n)
    simpa [momentWronskian] using hev
  -- the numerator identity, with no denominators in sight
  have hnum : (monicOrtho s n).eval z *
        ((monicOrtho s (n + 1)).eval w * (secondKind s n).eval z -
          (monicOrtho s n).eval w * (secondKind s (n + 1)).eval z)
      - (secondKind s n).eval z *
        ((monicOrtho s (n + 1)).eval w * (monicOrtho s n).eval z -
          (monicOrtho s n).eval w * (monicOrtho s (n + 1)).eval z)
      = -((monicOrtho s n).eval w * momentInner s (monicOrtho s n) (monicOrtho s n) /
          momentInner s (monicOrtho s 0) (monicOrtho s 0)) := by
    have hb : (monicOrtho s n).eval z *
          ((monicOrtho s (n + 1)).eval w * (secondKind s n).eval z -
            (monicOrtho s n).eval w * (secondKind s (n + 1)).eval z)
        - (secondKind s n).eval z *
          ((monicOrtho s (n + 1)).eval w * (monicOrtho s n).eval z -
            (monicOrtho s n).eval w * (monicOrtho s (n + 1)).eval z)
        = (monicOrtho s n).eval w *
          ((monicOrtho s (n + 1)).eval z * (secondKind s n).eval z -
            (monicOrtho s n).eval z * (secondKind s (n + 1)).eval z) := by
      ring
    rw [hb, hWz]
    ring
  have key : (w - z) * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
      ((monicOrtho s n).eval z *
          (∑ j ∈ Finset.range (n + 1), (monicOrtho s j).eval w * (secondKind s j).eval z /
            momentInner s (monicOrtho s j) (monicOrtho s j))
        - (secondKind s n).eval z *
          (∑ j ∈ Finset.range (n + 1), (monicOrtho s j).eval w * (monicOrtho s j).eval z /
            momentInner s (monicOrtho s j) (monicOrtho s j)))
      = (monicOrtho s n).eval z - (monicOrtho s n).eval w := by
    calc (w - z) * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          ((monicOrtho s n).eval z *
              (∑ j ∈ Finset.range (n + 1), (monicOrtho s j).eval w * (secondKind s j).eval z /
                momentInner s (monicOrtho s j) (monicOrtho s j))
            - (secondKind s n).eval z *
              (∑ j ∈ Finset.range (n + 1), (monicOrtho s j).eval w * (monicOrtho s j).eval z /
                momentInner s (monicOrtho s j) (monicOrtho s j)))
        = momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            ((monicOrtho s n).eval z *
                ((w - z) * ∑ j ∈ Finset.range (n + 1),
                  (monicOrtho s j).eval w * (secondKind s j).eval z /
                    momentInner s (monicOrtho s j) (monicOrtho s j))
              - (secondKind s n).eval z *
                ((w - z) * ∑ j ∈ Finset.range (n + 1),
                  (monicOrtho s j).eval w * (monicOrtho s j).eval z /
                    momentInner s (monicOrtho s j) (monicOrtho s j))) := by
          ring
      _ = momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            ((monicOrtho s n).eval z *
                (((monicOrtho s (n + 1)).eval w * (secondKind s n).eval z -
                    (monicOrtho s n).eval w * (secondKind s (n + 1)).eval z) /
                  momentInner s (monicOrtho s n) (monicOrtho s n)
                  + 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0))
              - (secondKind s n).eval z *
                (((monicOrtho s (n + 1)).eval w * (monicOrtho s n).eval z -
                    (monicOrtho s n).eval w * (monicOrtho s (n + 1)).eval z) /
                  momentInner s (monicOrtho s n) (monicOrtho s n))) := by
          rw [hMix, hCD]
      _ = momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            ((monicOrtho s n).eval z *
                ((monicOrtho s (n + 1)).eval w * (secondKind s n).eval z -
                  (monicOrtho s n).eval w * (secondKind s (n + 1)).eval z)
              - (secondKind s n).eval z *
                ((monicOrtho s (n + 1)).eval w * (monicOrtho s n).eval z -
                  (monicOrtho s n).eval w * (monicOrtho s (n + 1)).eval z)) /
              momentInner s (monicOrtho s n) (monicOrtho s n)
            + (monicOrtho s n).eval z := by
          field_simp [h0, hn]
          ring
      _ = momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            (-((monicOrtho s n).eval w * momentInner s (monicOrtho s n) (monicOrtho s n) /
              momentInner s (monicOrtho s 0) (monicOrtho s 0))) /
              momentInner s (monicOrtho s n) (monicOrtho s n)
            + (monicOrtho s n).eval z := by
          rw [hnum]
      _ = (monicOrtho s n).eval z - (monicOrtho s n).eval w := by
          field_simp [h0, hn]
          ring
  linear_combination key

end HTGeometry
