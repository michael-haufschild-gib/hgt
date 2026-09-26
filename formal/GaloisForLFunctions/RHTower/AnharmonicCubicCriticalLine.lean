import GaloisForLFunctions.RHTower.AnharmonicChebyshevOrientationCasimir

open Complex

namespace RHTower

noncomputable section

/-- Critical-line quotient coordinate in the cubic descent. -/
def chebyshevCriticalLineCoordinate (t : ℝ) : ℝ :=
  t * (4 * t ^ 2 + 9) / (4 * t ^ 2 + 1)

theorem chebyshevCriticalLineCoordinate_odd (t : ℝ) :
    chebyshevCriticalLineCoordinate (-t) =
      -chebyshevCriticalLineCoordinate t := by
  simp [chebyshevCriticalLineCoordinate, neg_div]

theorem chebyshevAnharmonicQ_criticalLine (t : ℝ) :
    chebyshevAnharmonicQ ((1 / 2 : ℂ) + (t : ℂ) * I) =
      I * (chebyshevCriticalLineCoordinate t : ℂ) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hdenR : (4 * t ^ 2 + 1 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hden : ((4 * t ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hdenR
  have hd : 2 * s * (s - 1) = -(((4 * t ^ 2 + 1 : ℝ) : ℂ)) / 2 := by
    dsimp [s]
    push_cast
    ring_nf
    simp
    ring
  have hn : (s - 2) * (s + 1) * (2 * s - 1) =
      -I * (t : ℂ) * (((4 * t ^ 2 + 9 : ℝ) : ℂ)) / 2 := by
    dsimp [s]
    push_cast
    ring_nf
    simp
    ring
  rw [chebyshevAnharmonicQ, ← show s = (1 / 2 : ℂ) + (t : ℂ) * I from rfl,
    hd, hn]
  simp only [chebyshevCriticalLineCoordinate, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  field_simp [hden]

theorem chebyshevAnharmonicQ_criticalLine_sq (t : ℝ) :
    chebyshevAnharmonicQ ((1 / 2 : ℂ) + (t : ℂ) * I) ^ 2 =
      ((-chebyshevCriticalLineCoordinate t ^ 2 : ℝ) : ℂ) := by
  rw [chebyshevAnharmonicQ_criticalLine, mul_pow, I_sq]
  push_cast
  ring

theorem chebyshevAnharmonicQ_criticalLine_sq_nonpos (t : ℝ) :
    ∃ x : ℝ, x ≤ 0 ∧
      chebyshevAnharmonicQ ((1 / 2 : ℂ) + (t : ℂ) * I) ^ 2 = (x : ℂ) := by
  refine ⟨-chebyshevCriticalLineCoordinate t ^ 2, ?_,
    chebyshevAnharmonicQ_criticalLine_sq t⟩
  exact neg_nonpos.mpr (sq_nonneg _)

end

end RHTower
