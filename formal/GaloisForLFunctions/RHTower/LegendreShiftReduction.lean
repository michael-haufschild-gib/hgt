import GaloisForLFunctions.RHTower.LegendreGeneratingFunction

/-!
# Legendre polynomials at `4k + j` through `P_{4k+3}` and `P_{4k+4}`

The three-term recurrence expresses every `P_{4k+j}(s)`, `j ∈ {0, 1, 2, 5, 6, 7, 8}`, as
`A_j(k, s) P_{4k+3}(s) + B_j(k, s) P_{4k+4}(s)` with explicit rational coefficients.  This is the
exact "two-index reduction" used for the uniform law of the Route J residual: all cancellations
between the five Legendre values of the residual are performed here, algebraically.
-/

open Finset

namespace RHTower
namespace LegendreBoost

theorem legendre_rec_up (n : ℕ) (s : ℝ) :
    legendre (n + 2) s =
      ((2 * (n : ℝ) + 3) * s * legendre (n + 1) s - ((n : ℝ) + 1) * legendre n s) / ((n : ℝ) + 2) := by
  have h := legendre_recurrence n s
  have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
  rw [eq_div_iff hne]
  linear_combination h

theorem legendre_rec_down (n : ℕ) (s : ℝ) :
    legendre n s =
      ((2 * (n : ℝ) + 3) * s * legendre (n + 1) s - ((n : ℝ) + 2) * legendre (n + 2) s) / ((n : ℝ) + 1) := by
  have h := legendre_recurrence n s
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff hne]
  linear_combination h

/-! ## The shift coefficients -/

noncomputable def shA0 (k s : ℝ) : ℝ :=
  s * (8 * k + 5) * (64 * k ^ (2 : ℕ) * s ^ (2 : ℕ) - 32 * k ^ (2 : ℕ) + 80 * k * s ^ (2 : ℕ) - 40 * k + 21 * s ^ (2 : ℕ) - 11) /
    (2 * (2 * k + 1) * (4 * k + 1) * (4 * k + 3))
noncomputable def shB0 (k s : ℝ) : ℝ :=
  -2 * (k + 1) * (64 * k ^ (2 : ℕ) * s ^ (2 : ℕ) - 16 * k ^ (2 : ℕ) + 64 * k * s ^ (2 : ℕ) - 16 * k + 15 * s ^ (2 : ℕ) - 4) /
    ((2 * k + 1) * (4 * k + 1) * (4 * k + 3))
noncomputable def shA1 (k s : ℝ) : ℝ :=
  (64 * k ^ (2 : ℕ) * s ^ (2 : ℕ) - 16 * k ^ (2 : ℕ) + 96 * k * s ^ (2 : ℕ) - 24 * k + 35 * s ^ (2 : ℕ) - 9) /
    (2 * (2 * k + 1) * (4 * k + 3))
noncomputable def shB1 (k s : ℝ) : ℝ := -2 * s * (k + 1) * (8 * k + 5) / ((2 * k + 1) * (4 * k + 3))
noncomputable def shA2 (k s : ℝ) : ℝ := s * (8 * k + 7) / (4 * k + 3)
noncomputable def shB2 (k s : ℝ) : ℝ := -4 * (k + 1) / (4 * k + 3)
noncomputable def shA5 (k s : ℝ) : ℝ := -4 * (k + 1) / (4 * k + 5)
noncomputable def shB5 (k s : ℝ) : ℝ := s * (8 * k + 9) / (4 * k + 5)
noncomputable def shA6 (k s : ℝ) : ℝ := -2 * s * (k + 1) * (8 * k + 11) / ((2 * k + 3) * (4 * k + 5))
noncomputable def shB6 (k s : ℝ) : ℝ :=
  (64 * k ^ (2 : ℕ) * s ^ (2 : ℕ) - 16 * k ^ (2 : ℕ) + 160 * k * s ^ (2 : ℕ) - 40 * k + 99 * s ^ (2 : ℕ) - 25) /
    (2 * (2 * k + 3) * (4 * k + 5))
noncomputable def shA7 (k s : ℝ) : ℝ :=
  -2 * (k + 1) * (64 * k ^ (2 : ℕ) * s ^ (2 : ℕ) - 16 * k ^ (2 : ℕ) + 192 * k * s ^ (2 : ℕ) - 48 * k + 143 * s ^ (2 : ℕ) - 36) /
    ((2 * k + 3) * (4 * k + 5) * (4 * k + 7))
noncomputable def shB7 (k s : ℝ) : ℝ :=
  s * (8 * k + 11) * (64 * k ^ (2 : ℕ) * s ^ (2 : ℕ) - 32 * k ^ (2 : ℕ) + 176 * k * s ^ (2 : ℕ) - 88 * k + 117 * s ^ (2 : ℕ) - 59) /
    (2 * (2 * k + 3) * (4 * k + 5) * (4 * k + 7))
noncomputable def shA8 (k s : ℝ) : ℝ :=
  -s * (k + 1) * (8 * k + 13) *
      (64 * k ^ (2 : ℕ) * s ^ (2 : ℕ) - 32 * k ^ (2 : ℕ) + 208 * k * s ^ (2 : ℕ) - 104 * k + 165 * s ^ (2 : ℕ) - 83) /
    (2 * (k + 2) * (2 * k + 3) * (4 * k + 5) * (4 * k + 7))
noncomputable def shB8 (k s : ℝ) : ℝ :=
  (4096 * k ^ (4 : ℕ) * s ^ (4 : ℕ) - 3072 * k ^ (4 : ℕ) * s ^ (2 : ℕ) + 256 * k ^ (4 : ℕ) + 24576 * k ^ (3 : ℕ) * s ^ (4 : ℕ) -
      18432 * k ^ (3 : ℕ) * s ^ (2 : ℕ) + 1536 * k ^ (3 : ℕ) + 54656 * k ^ (2 : ℕ) * s ^ (4 : ℕ) - 41040 * k ^ (2 : ℕ) * s ^ (2 : ℕ) +
      3424 * k ^ (2 : ℕ) + 53376 * k * s ^ (4 : ℕ) - 40176 * k * s ^ (2 : ℕ) + 3360 * k + 19305 * s ^ (4 : ℕ) -
      14586 * s ^ (2 : ℕ) + 1225) /
    (8 * (k + 2) * (2 * k + 3) * (4 * k + 5) * (4 * k + 7))

/-! ## Upward shifts -/

theorem legendre_shift5 (k : ℕ) (s : ℝ) :
    legendre (4 * k + 5) s = shA5 k s * legendre (4 * k + 3) s + shB5 k s * legendre (4 * k + 4) s := by
  rw [show 4 * k + 5 = 4 * k + 3 + 2 from rfl, legendre_rec_up, show 4 * k + 3 + 1 = 4 * k + 4 from rfl]
  unfold shA5 shB5
  push_cast
  have h1 : (0 : ℝ) < 4 * k + 3 + 2 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 5 := by positivity
  field_simp
  ring

theorem legendre_shift6 (k : ℕ) (s : ℝ) :
    legendre (4 * k + 6) s = shA6 k s * legendre (4 * k + 3) s + shB6 k s * legendre (4 * k + 4) s := by
  rw [show 4 * k + 6 = 4 * k + 4 + 2 from rfl, legendre_rec_up, show 4 * k + 4 + 1 = 4 * k + 5 from rfl,
    legendre_shift5]
  unfold shA5 shB5 shA6 shB6
  push_cast
  have h1 : (0 : ℝ) < 4 * k + 4 + 2 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 5 := by positivity
  have h3 : (0 : ℝ) < 2 * k + 3 := by positivity
  field_simp
  ring

theorem legendre_shift7 (k : ℕ) (s : ℝ) :
    legendre (4 * k + 7) s = shA7 k s * legendre (4 * k + 3) s + shB7 k s * legendre (4 * k + 4) s := by
  rw [show 4 * k + 7 = 4 * k + 5 + 2 from rfl, legendre_rec_up, show 4 * k + 5 + 1 = 4 * k + 6 from rfl,
    legendre_shift6, legendre_shift5]
  unfold shA5 shB5 shA6 shB6 shA7 shB7
  push_cast
  have h1 : (0 : ℝ) < 4 * k + 5 + 2 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 5 := by positivity
  have h3 : (0 : ℝ) < 2 * k + 3 := by positivity
  have h4 : (0 : ℝ) < 4 * k + 7 := by positivity
  field_simp
  ring

theorem legendre_shift8 (k : ℕ) (s : ℝ) :
    legendre (4 * k + 8) s = shA8 k s * legendre (4 * k + 3) s + shB8 k s * legendre (4 * k + 4) s := by
  rw [show 4 * k + 8 = 4 * k + 6 + 2 from rfl, legendre_rec_up, show 4 * k + 6 + 1 = 4 * k + 7 from rfl,
    legendre_shift7, legendre_shift6]
  unfold shA6 shB6 shA7 shB7 shA8 shB8
  push_cast
  have h1 : (0 : ℝ) < 4 * k + 6 + 2 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 5 := by positivity
  have h3 : (0 : ℝ) < 2 * k + 3 := by positivity
  have h4 : (0 : ℝ) < 4 * k + 7 := by positivity
  have h5 : (0 : ℝ) < k + 2 := by positivity
  field_simp
  ring

/-! ## Downward shifts -/

theorem legendre_shift2 (k : ℕ) (s : ℝ) :
    legendre (4 * k + 2) s = shA2 k s * legendre (4 * k + 3) s + shB2 k s * legendre (4 * k + 4) s := by
  rw [legendre_rec_down (4 * k + 2) s, show 4 * k + 2 + 1 = 4 * k + 3 from rfl,
    show 4 * k + 2 + 2 = 4 * k + 4 from rfl]
  unfold shA2 shB2
  push_cast
  have h1 : (0 : ℝ) < 4 * k + 2 + 1 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 3 := by positivity
  field_simp
  ring

theorem legendre_shift1 (k : ℕ) (s : ℝ) :
    legendre (4 * k + 1) s = shA1 k s * legendre (4 * k + 3) s + shB1 k s * legendre (4 * k + 4) s := by
  rw [legendre_rec_down (4 * k + 1) s, show 4 * k + 1 + 1 = 4 * k + 2 from rfl,
    show 4 * k + 1 + 2 = 4 * k + 3 from rfl, legendre_shift2]
  unfold shA1 shB1 shA2 shB2
  push_cast
  have h1 : (0 : ℝ) < 4 * k + 1 + 1 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 3 := by positivity
  have h3 : (0 : ℝ) < 2 * k + 1 := by positivity
  field_simp
  ring

theorem legendre_shift0 (k : ℕ) (s : ℝ) :
    legendre (4 * k) s = shA0 k s * legendre (4 * k + 3) s + shB0 k s * legendre (4 * k + 4) s := by
  rw [legendre_rec_down (4 * k) s, legendre_shift1, legendre_shift2]
  unfold shA0 shB0 shA1 shB1 shA2 shB2
  push_cast
  have h1 : (0 : ℝ) < 4 * k + 1 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 3 := by positivity
  have h3 : (0 : ℝ) < 2 * k + 1 := by positivity
  field_simp
  ring

end LegendreBoost
end RHTower
